import DeepWiki.SymbolicIntegration.Computable.GenericPolyEngine

/-! # `DenoteHom` parametricity classes and the `derive_denote_hom` generator

`DenoteHom₁`/`DenoteHom₂` carry the denotation square of a computable operation (its `op` an
`outParam`), the CoqEAL-style parametricity instances consumed by `RefinesPolyG.hom₁`/`hom₂`.

`derive_denote_hom sq` reads a denotation-square lemma `sq : ∀ …, toPolyG (cop …) = op (toPolyG …) …`
and *generates* the matching `DenoteHom` instance — the Lean slice of Coq's `param` translation, so an
operation author writes only the square. Supports the clean unary/binary case with no extra scalar
arguments (parameterized ops such as `cscaleG c` keep explicit instances).
-/

open Polynomial Lean Meta Elab Command

namespace DeepWiki.SymbolicIntegration

open CPolyG

/-- A unary computable operation `cop` denotes the abstract unary `op` through `toPolyG`. -/
class DenoteHom₁ {α : Type*} [CField α] [CFieldSpec α]
    (cop : CPolyG α → CPolyG α) (op : outParam ((CFieldSpec.K α)[X] → (CFieldSpec.K α)[X])) : Prop where
  /-- The denotation square: `cop` commutes with `op` along `toPolyG`. -/
  square : ∀ p, toPolyG (cop p) = op (toPolyG p)

/-- A binary computable operation `cop` denotes the abstract binary `op` through `toPolyG`. -/
class DenoteHom₂ {α : Type*} [CField α] [CFieldSpec α]
    (cop : CPolyG α → CPolyG α → CPolyG α)
    (op : outParam ((CFieldSpec.K α)[X] → (CFieldSpec.K α)[X] → (CFieldSpec.K α)[X])) : Prop where
  /-- The denotation square: `cop` commutes with `op` along `toPolyG`. -/
  square : ∀ p q, toPolyG (cop p q) = op (toPolyG p) (toPolyG q)

/-- `derive_denote_hom sq` generates the `DenoteHom₁`/`DenoteHom₂` instance from the denotation
square `sq`. Extracts `cop` (the computable head) and `op` (the abstract operation, by abstracting
`toPolyG` of the polynomial arguments from the square's RHS), then registers the instance. -/
elab "derive_denote_hom " sq:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo sq
  liftTermElabM do
    let info ← getConstInfo name
    let lvls := info.levelParams.map Level.param
    forallTelescopeReducing info.type fun args body => do
      let some (_, lhs, rhs) := body.eq?
        | throwError "derive_denote_hom: `{name}` is not an equality"
      -- lhs must be `toPolyG innerL`; recover the `toPolyG` head with its implicit args.
      let toPolyGFn := lhs.getAppFn
      let lhsArgs := lhs.getAppArgs
      unless lhsArgs.size ≥ 1 do throwError "derive_denote_hom: LHS is not a `toPolyG` application"
      let innerL := lhsArgs.back!
      let tpImplicits := lhsArgs.pop  -- the `@toPolyG α inst inst` prefix
      let tpHead := mkAppN toPolyGFn tpImplicits  -- `toPolyG` awaiting its polynomial argument
      let tpOf (x : Expr) : Expr := mkApp tpHead x
      -- Polynomial args are those explicit args whose `toPolyG` occurs in the RHS.
      let polyArgs ← args.filterM fun x => do
        pure <| (rhs.find? (· == tpOf x)).isSome
      -- Any explicit (default-binder) arg that is not a polynomial arg is an unsupported parameter.
      for x in args do
        let d ← x.fvarId!.getDecl
        if d.binderInfo == .default && !polyArgs.contains x then
          throwError "derive_denote_hom: `{name}` has extra argument `{d.userName}`; keep an explicit instance"
      let n := polyArgs.size
      unless n == 1 || n == 2 do
        throwError "derive_denote_hom: expected 1 or 2 polynomial arguments, got {n}"
      -- `cop := fun polyArgs => innerL`
      let cop ← mkLambdaFVars polyArgs innerL
      -- `op := rhs` with each `toPolyG polyArgᵢ` abstracted to a fresh `K[X]` binder.
      let kx ← inferType (tpOf polyArgs[0]!)  -- `(CFieldSpec.K α)[X]`
      let op ← withLocalDeclsD (polyArgs.mapIdx fun i _ => (s!"y{i}".toName, fun _ => pure kx)) fun ys => do
        let mut body := rhs
        for pa in polyArgs, y in ys do
          body := body.replace fun e => if e == tpOf pa then some y else none
        mkLambdaFVars ys body
      -- Outer binders: everything that is not a polynomial argument (α, instances).
      let outer := args.filter (!polyArgs.contains ·)
      let clsName := if n == 1 then ``DenoteHom₁ else ``DenoteHom₂
      let mkName := if n == 1 then ``DenoteHom₁.mk else ``DenoteHom₂.mk
      let instType ← mkForallFVars outer (mkAppN (mkConst clsName lvls) (tpImplicits ++ #[cop, op]))
      -- field proof: `fun polyArgs => sq (all original args)` — defeq to the class field.
      let field ← mkLambdaFVars polyArgs (mkAppN (mkConst name lvls) args)
      let instVal ← mkLambdaFVars outer (mkAppN (mkConst mkName lvls) (tpImplicits ++ #[cop, op, field]))
      let instName := name ++ `denoteHom
      addDecl <| .defnDecl {
        name := instName, levelParams := info.levelParams, type := instType, value := instVal,
        hints := .abbrev, safety := .safe }
      setReducibleAttribute instName
      addInstance instName .global 1000

end DeepWiki.SymbolicIntegration

