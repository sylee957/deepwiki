import DeepWiki.Refine.Basic
import Lean

/-! # The transfer resolver — the Lean analog of Trocq's Elpi engine

A `MetaM` metaprogram that automates relational transfer over the `Refine` kernel. Given a goal
`Refines R c ?a` (functional relation `R = DenoteRel denote`), it decomposes `c` by head symbol,
looks up `@[refines]` witnesses, and composes them via `Refines.app` — synthesizing the abstract term
`?a` and its proof. It is `isDefEq`-driven (the higher-order beta-match `c =?= F ?xs` that typeclass
synthesis refuses), *not* `simp`-driven. -/

open Lean Meta Elab

namespace DeepWiki.Refine

/-- Env extension collecting `@[refines]`-tagged witness declaration names. -/
initialize refinesExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrs => arrs.foldl Array.append #[] }

initialize registerBuiltinAttribute {
    name := `refines
    descr := "A refinement witness `Refines (R ⟹ … ⟹ R) F G` for the transfer resolver."
    add := fun decl _stx _kind => modifyEnv fun env => refinesExt.addEntry env decl }

/-- The arity of a witness = the number of nested respectful arrows `⟹` in its relation. -/
partial def arityOf (rel : Expr) : Nat :=
  match rel.getAppFnArgs with
  | (``Respectful, args) => if args.size ≥ 1 then 1 + arityOf args[args.size - 1]! else 0
  | _ => 0

/-- Extract `denote` from a functional relation `R` definitionally equal to `DenoteRel denote`,
δ-unfolding the relation head one step at a time. -/
partial def getDenote (rel : Expr) : MetaM Expr := do
  match rel.getAppFnArgs with
  | (``DenoteRel, #[_, _, denote]) => return denote
  | _ =>
    match ← unfoldDefinition? rel with
    | some rel' => getDenote rel'
    | none => throwError "refine_transfer: relation is not a `DenoteRel`"

/-- Resolve `c` to `(abstract, proof)` with `proof : Refines (DenoteRel denote) c abstract`, by
matching registered witnesses (recursively) and falling back to the denotation leaf. -/
partial def resolve (denote : Expr) (c : Expr) : MetaM (Expr × Expr) := do
  for w in refinesExt.getState (← getEnv) do
    let s ← saveState
    let wConst ← mkConstWithFreshMVarLevels w
    let (params, bis, concl) ← forallMetaTelescopeReducing (← inferType wConst)
    match concl.getAppFnArgs with
    | (``Refines, #[_, _, rel, fExpr, gExpr]) =>
      let arity := arityOf rel
      if arity > 0 then
        let argMvars ← (List.replicate arity ()).mapM fun _ => mkFreshExprMVar none
        let lhs := fExpr.beta argMvars.toArray
        -- cheap pre-filter: only run `isDefEq` when head symbols agree
        if lhs.getAppFn.constName? != c.getAppFn.constName? || lhs.getAppFn.constName?.isNone then
          s.restore
        else if ← isDefEq c lhs then
          for i in [0:params.size] do
            if bis[i]!.isInstImplicit then
              let m := params[i]!.mvarId!
              unless ← m.isAssigned do
                try m.assign (← synthInstance (← m.getType)) catch _ => pure ()
          let mut absArgs := #[]
          let mut proof := mkAppN wConst params
          for x in argMvars do
            let (xAbs, xPf) ← resolve denote (← instantiateMVars x)
            absArgs := absArgs.push xAbs
            proof ← mkAppM ``Refines.app #[proof, xPf]
          return (mkAppN gExpr absArgs, proof)
        else s.restore
      else s.restore
    | _ => s.restore
  -- leaf: `c` refines its denotation
  return (mkApp denote c, ← mkAppM ``refines_denote #[denote, c])

open Lean.Elab.Tactic in
/-- `refine_transfer`: close a goal `Refines R c ?a` (or check `Refines R c a`) by synthesizing the
abstract `?a` and its proof via the relational resolver — no `simp`. -/
elab "refine_transfer" : tactic => withMainContext do
  let goal ← getMainGoal
  match (← goal.getType).getAppFnArgs with
  | (``Refines, #[_, _, rel, c, a]) =>
    let denote ← getDenote rel
    let (absTerm, proof) ← resolve denote (← instantiateMVars c)
    unless ← isDefEq a absTerm do
      throwError "refine_transfer: computed abstract term{indentExpr absTerm}\ndoes not match the goal"
    goal.assign proof
  | _ => throwError "refine_transfer: goal is not `Refines _ _ _`"

end DeepWiki.Refine
