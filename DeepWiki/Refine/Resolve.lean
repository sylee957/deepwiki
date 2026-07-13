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

/-- Decompose a witness relation `R₁ ⟹ … ⟹ Rₖ ⟹ Rout` into the argument relations `[R₁,…,Rₖ]` and
the output relation `Rout`. This is what lets the resolver thread a *different* relation on the output
than on the inputs (e.g. `gcd`: equality inputs, up-to-unit output). -/
partial def decomposeArrow (rel : Expr) : List Expr × Expr :=
  match rel.getAppFnArgs with
  | (``Respectful, args) =>
    if args.size ≥ 6 then
      let (rest, out) := decomposeArrow args[args.size - 1]!
      (args[args.size - 2]! :: rest, out)
    else ([], rel)
  | _ => ([], rel)

/-- Extract `denote` from a functional relation `R` definitionally equal to `DenoteRel denote`,
δ-unfolding the relation head one step at a time. -/
partial def getDenote (rel : Expr) : MetaM Expr := do
  match rel.getAppFnArgs with
  | (``DenoteRel, #[_, _, denote]) => return denote
  | _ =>
    match ← unfoldDefinition? rel with
    | some rel' => getDenote rel'
    | none => throwError "refine_transfer: relation is not a `DenoteRel`"

/-- Resolve `c` at target relation `R` to `(abstract, proof)` with `proof : Refines R c abstract`. A
witness matches when its **head symbol** and its **output relation** agree with `c` and `R`; each
argument is then resolved at the relation named by the witness's arrow (so a functional-input /
up-to-unit-output op like `gcd` composes). Leaves close via the functional denotation of `R`. -/
partial def resolve (R : Expr) (c : Expr) : MetaM (Expr × Expr) := do
  for w in refinesExt.getState (← getEnv) do
    let s ← saveState
    let wConst ← mkConstWithFreshMVarLevels w
    let (params, bis, concl) ← forallMetaTelescopeReducing (← inferType wConst)
    match concl.getAppFnArgs with
    | (``Refines, #[_, _, rel, fExpr, gExpr]) =>
      let (argRels, outRel) := decomposeArrow rel
      if argRels.length > 0 then
        let argMvars ← argRels.mapM fun _ => mkFreshExprMVar none
        let lhs := fExpr.beta argMvars.toArray
        -- cheap head pre-filter, then the output-relation and term matches
        if lhs.getAppFn.constName? != c.getAppFn.constName? || lhs.getAppFn.constName?.isNone then
          s.restore
        else if !(← isDefEq R outRel) then s.restore
        else if ← isDefEq c lhs then
          for i in [0:params.size] do
            if bis[i]!.isInstImplicit then
              let m := params[i]!.mvarId!
              unless ← m.isAssigned do
                try m.assign (← synthInstance (← m.getType)) catch _ => pure ()
          let mut absArgs := #[]
          let mut proof := mkAppN wConst params
          for (x, Ri) in argMvars.zip argRels do
            let (xAbs, xPf) ← resolve (← instantiateMVars Ri) (← instantiateMVars x)
            absArgs := absArgs.push xAbs
            proof ← mkAppM ``Refines.app #[proof, xPf]
          return (mkAppN (← instantiateMVars gExpr) absArgs, proof)
        else s.restore
      else s.restore
    | _ => s.restore
  -- leaf: `c` refines its denotation (functional relation)
  let denote ← getDenote R
  return (mkApp denote c, ← mkAppM ``refines_denote #[denote, c])

open Lean.Elab.Tactic in
/-- `refine_transfer`: close a goal `Refines R c ?a` (or check `Refines R c a`) by synthesizing the
abstract `?a` and its proof via the relational resolver — no `simp`. -/
elab "refine_transfer" : tactic => withMainContext do
  let goal ← getMainGoal
  match (← goal.getType).getAppFnArgs with
  | (``Refines, #[_, _, rel, c, a]) =>
    let (absTerm, proof) ← resolve rel (← instantiateMVars c)
    unless ← isDefEq a absTerm do
      throwError "refine_transfer: computed abstract term{indentExpr absTerm}\ndoes not match the goal"
    goal.assign proof
  | _ => throwError "refine_transfer: goal is not `Refines _ _ _`"

end DeepWiki.Refine
