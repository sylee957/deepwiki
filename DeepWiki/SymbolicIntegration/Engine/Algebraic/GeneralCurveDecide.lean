import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralLogSoundness
import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralWellFounded
import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralDivisorOrder

/-! # `cIntegrateGeneralCurveDecide`: elementarity decision over an arbitrary plane curve

The self-determining elementary-integration decision over `K(x)[y]/(f)`, returning
`some F` when the integral is elementary (no log part, principal `1·log u`, or torsion
`(1/m)·log g`) and `none` when the residue divisor is non-torsion. Sound, complete, and a
decision procedure modulo the isolated `GeneralPicTorsionFrontier`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential
open DensePoly

/-! ## Result type and decision statement -/

/-- The general-curve integral `∫ = v + Σ cᵢ log uᵢ`: rational part `ratPart : DensePoly (DenseFrac ℚ)`
over `K(x)[y]/(f)` plus `logTerms` of `(cᵢ ∈ ℚ(x), uᵢ ∈ K(x)[y]/(f))`; the output of
`cIntegrateGeneralCurveDecide`. -/
structure GeneralCurveIntegralResult where
  /-- The rational part `v` of `∫ = v + Σ cᵢ log uᵢ` (a carrier element of `K(x)[y]/(f)`). -/
  ratPart : DensePoly (DenseFrac ℚ)
  /-- The log terms `[(c₁, u₁), …]`: each a coefficient `cᵢ ∈ ℚ(x)` and an argument `uᵢ ∈ K(x)[y]/(f)`. -/
  logTerms : List (DenseFrac ℚ × DensePoly (DenseFrac ℚ))

/-! ### The residual data: the torsion-branch inputs `GeneralCurveTorsionInputs` -/

/-- The torsion-branch inputs: the residue `divisor : GenDivisor` of the integrand, and the
principal-generator oracle `genGen : ℕ → DensePoly (DenseFrac ℚ)` giving, for order `m`, a `g` with
`div(g) = m·δ`. The data side of `GeneralPicTorsionFrontier`. -/
structure GeneralCurveTorsionInputs where
  /-- The residue divisor `δ : GenDivisor` of the integrand (a fractional `O`-ideal over the integral basis). -/
  divisor : GenDivisor
  /-- The principal-generator oracle: given the torsion order `m`, the function `g` with `div(g) = m·δ`. -/
  genGen : ℕ → DensePoly (DenseFrac ℚ)

/-! ### The torsion log term `genCurveTorsionLogTerm` -/

/-- The torsion log term: `genDivisorOrder fuel f basis tin.divisor` yields `some m` ⟹
`some (1/m, tin.genGen m)` (the `(1/m)·log g` term for the `m`-torsion residue divisor); `none`
(non-torsion within fuel) ⟹ `none`. -/
def genCurveTorsionLogTerm [CLinearSolve (DenseFrac ℚ)]
    (fuel : ℕ) (f : DensePoly (DenseFrac ℚ)) (basis : List (DensePoly (DenseFrac ℚ)))
    (tin : GeneralCurveTorsionInputs) : Option (DenseFrac ℚ × DensePoly (DenseFrac ℚ)) :=
  match genDivisorOrder fuel f basis tin.divisor with
  | none => none
  | some m => some (CField.div (CCommRing.one : DenseFrac ℚ) (CFrac.ofScalar (m : ℚ)), tin.genGen m)

/-! ### The decision integrator `cIntegrateGeneralCurveDecide` -/

section SelectedLinearSolve

variable [CLinearSolve ℚ] [CLinearSolve (DenseFrac ℚ)]

/-- The elementarity-deciding integrator over `K(x)[y]/(f)`, `Option GeneralCurveIntegralResult`:
compute the rational part `v = afRationalSolveWf …` (fail ⟹ `none`); if `hasLogPart = false` ⟹
`some ⟨v, []⟩`; else principal `afLogArgSolveWf … = some u` ⟹ `some ⟨v, [(1, u)]⟩`; else the torsion
decision `genCurveTorsionLogTerm` ⟹ `some ⟨v, [(1/m, g)]⟩` (torsion) or `none` (non-torsion). -/
def cIntegrateGeneralCurveDecide (fuel : ℕ) (f : DensePoly (DenseFrac ℚ)) (basis : List (DensePoly (DenseFrac ℚ)))
    (degBound : ℕ) (ratIntegrand logIntegrand : DensePoly (DenseFrac ℚ))
    (tin : GeneralCurveTorsionInputs) (hasLogPart : Bool) :
    Option GeneralCurveIntegralResult :=
  match afRationalSolveWf f basis degBound ratIntegrand with
  | none => none
  | some v =>
    if hasLogPart = false then
      some ⟨v, []⟩
    else
      match afLogArgSolveWf f basis degBound logIntegrand with
      | some u => some ⟨v, [(CCommRing.one, u)]⟩
      | none =>
        match genCurveTorsionLogTerm fuel f basis tin with
        | some term => some ⟨v, [term]⟩
        | none => none

/-! ## Branch structure of `some` and `none` results -/

/-- A `none` output means the rational solve failed, or (log part present, principal solve failed,
and) the torsion decision returned `none`: `afRationalSolveWf … = none ∨ (afLogArgSolveWf …
isNone ∧ genCurveTorsionLogTerm … isNone)`. -/
theorem genCurveTorsionLogTerm_none_of_decide_none (fuel : ℕ) (f : DensePoly (DenseFrac ℚ))
    (basis : List (DensePoly (DenseFrac ℚ))) (degBound : ℕ) (ratIntegrand logIntegrand : DensePoly (DenseFrac ℚ))
    (tin : GeneralCurveTorsionInputs) (hasLogPart : Bool)
    (hnone : cIntegrateGeneralCurveDecide fuel f basis degBound ratIntegrand logIntegrand tin hasLogPart
      = none) :
    afRationalSolveWf f basis degBound ratIntegrand = none
      ∨ ((afLogArgSolveWf f basis degBound logIntegrand).isNone = true
          ∧ (genCurveTorsionLogTerm fuel f basis tin).isNone = true) := by
  unfold cIntegrateGeneralCurveDecide at hnone
  cases hv : afRationalSolveWf f basis degBound ratIntegrand with
  | none => exact Or.inl rfl
  | some v =>
    simp only [hv] at hnone
    by_cases hlp : hasLogPart = false
    · rw [if_pos hlp] at hnone; simp at hnone
    · rw [if_neg hlp] at hnone
      cases hu : afLogArgSolveWf f basis degBound logIntegrand with
      | some u => rw [hu] at hnone; simp at hnone
      | none =>
        rw [hu] at hnone
        cases hT : genCurveTorsionLogTerm fuel f basis tin with
        | some term => rw [hT] at hnone; simp at hnone
        | none => exact Or.inr ⟨by simp, by simp⟩

/-! ## Soundness `some F → D(F) = integrand` -/

section Soundness

variable (fuel : ℕ) (f : DensePoly (DenseFrac ℚ)) (basis : List (DensePoly (DenseFrac ℚ))) (degBound : ℕ)
variable (ratIntegrand logIntegrand : DensePoly (DenseFrac ℚ)) (tin : GeneralCurveTorsionInputs)
variable (hasLogPart : Bool) (integrand commonDenomQ : DensePoly (DenseFrac ℚ))
variable (cofs : List (DensePoly (DenseFrac ℚ)))

/-- The soundness residual: the per-branch instances turning each `some F` branch into
`IsGeneralAlgebraicIntegralWf f integrand F.ratPart commonDenomQ F.logTerms cofs` (the cross-multiplied
`D(v + Σ cᵢ log uᵢ) = integrand` in `K[X] ⧸ afIdeal f`) — clauses `hnolog`, `hprincipal`, `htorsion`
for the three `some` branches. -/
structure GeneralCurveDecideSoundnessResidual : Prop where
  /-- No-log branch: `D(⟨v, []⟩) = integrand` (rational part is the whole answer). -/
  hnolog : ∀ v, afRationalSolveWf f basis degBound ratIntegrand = some v →
    DensePoly.IsGeneralAlgebraicIntegralWf f integrand
      (GeneralCurveIntegralResult.mk v []).ratPart commonDenomQ
      (GeneralCurveIntegralResult.mk v []).logTerms cofs
  /-- Principal branch: `D(⟨v, [(1, u)]⟩) = integrand`. -/
  hprincipal : ∀ v u, afRationalSolveWf f basis degBound ratIntegrand = some v →
    afLogArgSolveWf f basis degBound logIntegrand = some u →
    DensePoly.IsGeneralAlgebraicIntegralWf f integrand
      (GeneralCurveIntegralResult.mk v [(CCommRing.one, u)]).ratPart commonDenomQ
      (GeneralCurveIntegralResult.mk v [(CCommRing.one, u)]).logTerms cofs
  /-- Torsion branch: `D(⟨v, [term]⟩) = integrand`. -/
  htorsion : ∀ v term, afRationalSolveWf f basis degBound ratIntegrand = some v →
    genCurveTorsionLogTerm fuel f basis tin = some term →
    DensePoly.IsGeneralAlgebraicIntegralWf f integrand
      (GeneralCurveIntegralResult.mk v [term]).ratPart commonDenomQ
      (GeneralCurveIntegralResult.mk v [term]).logTerms cofs

/-- Soundness: under the soundness residual, `cIntegrateGeneralCurveDecide … = some F` gives
`IsGeneralAlgebraicIntegralWf f integrand F.ratPart commonDenomQ F.logTerms cofs`, i.e.
`D(v + Σ cᵢ log uᵢ) = integrand` in `K[X] ⧸ afIdeal f`. -/
theorem cIntegrateGeneralCurveDecide_sound
    (hres : GeneralCurveDecideSoundnessResidual fuel f basis degBound ratIntegrand logIntegrand tin
      integrand commonDenomQ cofs)
    (F : GeneralCurveIntegralResult)
    (hsome : cIntegrateGeneralCurveDecide fuel f basis degBound ratIntegrand logIntegrand tin hasLogPart
      = some F) :
    DensePoly.IsGeneralAlgebraicIntegralWf f integrand F.ratPart commonDenomQ F.logTerms cofs := by
  unfold cIntegrateGeneralCurveDecide at hsome
  cases hv : afRationalSolveWf f basis degBound ratIntegrand with
  | none => rw [hv] at hsome; simp at hsome
  | some v =>
    simp only [hv] at hsome
    by_cases hlp : hasLogPart = false
    · -- no-log branch: F = ⟨v, []⟩
      rw [if_pos hlp, Option.some.injEq] at hsome
      rw [← hsome]
      exact hres.hnolog v hv
    · -- has-log branch
      rw [if_neg hlp] at hsome
      cases hu : afLogArgSolveWf f basis degBound logIntegrand with
      | some u =>
        -- principal branch: F = ⟨v, [(1, u)]⟩
        rw [hu, Option.some.injEq] at hsome
        rw [← hsome]
        exact hres.hprincipal v u hv hu
      | none =>
        -- torsion branch: F = ⟨v, [term]⟩, or none
        rw [hu] at hsome
        cases hT : genCurveTorsionLogTerm fuel f basis tin with
        | some term =>
          rw [hT, Option.some.injEq] at hsome
          rw [← hsome]
          exact hres.htorsion v term hv hT
        | none =>
          rw [hT] at hsome
          exact absurd hsome (by simp)

end Soundness

end SelectedLinearSolve

/-! ## The isolated torsion frontier `GeneralPicTorsionFrontier` -/

section PicTorsion

variable [CLinearSolve (DenseFrac ℚ)]
variable (fuel : ℕ) (f : DensePoly (DenseFrac ℚ)) (basis : List (DensePoly (DenseFrac ℚ)))
variable (tin : GeneralCurveTorsionInputs)

/-- The torsion term fires iff the order test succeeds: `(genCurveTorsionLogTerm fuel f basis
tin).isSome = true ↔ ∃ m, genDivisorOrder fuel f basis tin.divisor = some m`. -/
theorem genCurveTorsionLogTerm_isSome_iff :
    (genCurveTorsionLogTerm fuel f basis tin).isSome = true
      ↔ ∃ m, genDivisorOrder fuel f basis tin.divisor = some m := by
  unfold genCurveTorsionLogTerm
  cases hm : genDivisorOrder fuel f basis tin.divisor with
  | none => simp
  | some m => simp

/-- The torsion frontier for `isTorsion` (the residue divisor class `δ = tin.divisor` is torsion) and
`elem` (elementarity): clause `htorsion` = order test succeeds ⟺ `isTorsion`, clause `hcriterion` =
`isTorsion ↔ elem` (the log-part criterion). The isolated deep residual the decision is proven modulo. -/
structure GeneralPicTorsionFrontier (isTorsion : Prop) (elem : Prop) : Prop where
  /-- Torsion-decision correctness: `genDivisorOrder` succeeds ⟺ `δ` is torsion. -/
  htorsion : (∃ m, genDivisorOrder fuel f basis tin.divisor = some m) ↔ isTorsion
  /-- The log-part criterion: the integrand is elementary ⟺ `δ` is torsion. -/
  hcriterion : isTorsion ↔ elem

/-- Completeness modulo the frontier: under `GeneralPicTorsionFrontier`, the torsion branch fires iff
the integrand is elementary — `(genCurveTorsionLogTerm fuel f basis tin).isSome = true ↔ elem`. -/
theorem genCurveTorsionLogTerm_complete_of_frontier {isTorsion elem : Prop}
    (hres : GeneralPicTorsionFrontier fuel f basis tin isTorsion elem) :
    (genCurveTorsionLogTerm fuel f basis tin).isSome = true ↔ elem := by
  rw [genCurveTorsionLogTerm_isSome_iff, hres.htorsion, hres.hcriterion]

end PicTorsion

/-! ## Completeness `none → ¬ elementary` -/

section SelectedLinearSolve

variable [CLinearSolve ℚ] [CLinearSolve (DenseFrac ℚ)]

section Completeness

variable (fuel : ℕ) (f : DensePoly (DenseFrac ℚ)) (basis : List (DensePoly (DenseFrac ℚ))) (degBound : ℕ)
variable (ratIntegrand logIntegrand : DensePoly (DenseFrac ℚ)) (tin : GeneralCurveTorsionInputs)

/-- Completeness: on the non-principal log path (`afRationalSolveWf = some v`, `hasLogPart = true`,
`afLogArgSolveWf = none`), under `GeneralPicTorsionFrontier`, a `none` output gives `¬ elem`. -/
theorem cIntegrateGeneralCurveDecide_complete {isTorsion elem : Prop} (v : DensePoly (DenseFrac ℚ))
    (hres : GeneralPicTorsionFrontier fuel f basis tin isTorsion elem)
    (hv : afRationalSolveWf f basis degBound ratIntegrand = some v)
    (_hlog : afLogArgSolveWf f basis degBound logIntegrand = none)
    (hnone : cIntegrateGeneralCurveDecide fuel f basis degBound ratIntegrand logIntegrand tin true
      = none) :
    ¬ elem := by
  -- the `none` output (on this path) forces the torsion branch to `none` (non-torsion verdict)
  have hcases := genCurveTorsionLogTerm_none_of_decide_none fuel f basis degBound ratIntegrand
    logIntegrand tin true hnone
  have hT : (genCurveTorsionLogTerm fuel f basis tin).isNone = true := by
    rcases hcases with hrat | ⟨_, hT⟩
    · rw [hv] at hrat; simp at hrat
    · exact hT
  -- contrapositive of the completeness equivalence: if `elem` held, the log term would be emitted
  intro hcon
  have hsome : (genCurveTorsionLogTerm fuel f basis tin).isSome = true :=
    (genCurveTorsionLogTerm_complete_of_frontier fuel f basis tin hres).mpr hcon
  rw [Option.isNone_iff_eq_none] at hT
  rw [hT] at hsome
  simp at hsome

end Completeness

/-! ## Decision-procedure criterion `(∃ F, … = some F) ⟺ elementary` -/

section Decides

variable (fuel : ℕ) (f : DensePoly (DenseFrac ℚ)) (basis : List (DensePoly (DenseFrac ℚ))) (degBound : ℕ)
variable (ratIntegrand logIntegrand : DensePoly (DenseFrac ℚ)) (tin : GeneralCurveTorsionInputs)

/-- On the non-principal log path (`afRationalSolveWf = some v`, `hasLogPart = true`, `afLogArgSolveWf
= none`), `cIntegrateGeneralCurveDecide … isSome ↔ genCurveTorsionLogTerm … isSome`. -/
theorem decide_isSome_iff_genTorsion_isSome (v : DensePoly (DenseFrac ℚ))
    (hv : afRationalSolveWf f basis degBound ratIntegrand = some v)
    (hlog : afLogArgSolveWf f basis degBound logIntegrand = none) :
    (cIntegrateGeneralCurveDecide fuel f basis degBound ratIntegrand logIntegrand tin true).isSome = true
      ↔ (genCurveTorsionLogTerm fuel f basis tin).isSome = true := by
  unfold cIntegrateGeneralCurveDecide
  simp only [hv, hlog, Bool.true_eq_false, if_false]
  cases hT : genCurveTorsionLogTerm fuel f basis tin with
  | none => simp
  | some term => simp

/-- The decision-procedure capstone: on the non-principal log path, under `GeneralPicTorsionFrontier`,
`(∃ F, cIntegrateGeneralCurveDecide … true = some F) ↔ elem`. -/
theorem cIntegrateGeneralCurveDecide_decides {isTorsion elem : Prop} (v : DensePoly (DenseFrac ℚ))
    (hres : GeneralPicTorsionFrontier fuel f basis tin isTorsion elem)
    (hv : afRationalSolveWf f basis degBound ratIntegrand = some v)
    (hlog : afLogArgSolveWf f basis degBound logIntegrand = none) :
    (∃ F, cIntegrateGeneralCurveDecide fuel f basis degBound ratIntegrand logIntegrand tin true = some F)
      ↔ elem := by
  rw [← Option.isSome_iff_exists,
    decide_isSome_iff_genTorsion_isSome fuel f basis degBound ratIntegrand logIntegrand tin v hv hlog]
  exact genCurveTorsionLogTerm_complete_of_frontier fuel f basis tin hres

end Decides

end SelectedLinearSolve

/-! ## End-to-end `native_decide` witnesses -/

open DensePoly

/-! ### Witness A — the torsion divisor `div(y)` on the cuspidal cubic `y³ = x²` -/

/-- Torsion inputs on `y³ = x²`: residue divisor `gdDivY = div(y)` (order 1) with generator oracle
returning `gcuspCubicY`. -/
def genCurveWitnessTorsionInputs : GeneralCurveTorsionInputs :=
  ⟨gdDivY, fun _ => gcuspCubicY⟩

/-- The decision run on the cuspidal-cubic torsion divisor: `hasLogPart = true`, `ratIntegrand = 0`,
`logIntegrand = 1`, fuel `8`; expected `some ⟨v, [(1/1, y)]⟩`. -/
def genCurveWitnessTorsion : Option GeneralCurveIntegralResult :=
  cIntegrateGeneralCurveDecide 8 gcuspCubicF gcuspCubicBasis 2
    ([] : DensePoly (DenseFrac ℚ)) ([CCommRing.one] : DensePoly (DenseFrac ℚ)) genCurveWitnessTorsionInputs true

/-- The decision returns `some` with one `(1/1)·log` term on `y³ = x²`: `(isSome, logTerms.length,
coefficient = 1/1) = (true, some 1, some true)`. -/
theorem genCurveWitnessTorsion_some :
    (genCurveWitnessTorsion.isSome,
     (genCurveWitnessTorsion.map fun F => F.logTerms.length),
     (genCurveWitnessTorsion.bind fun F =>
        F.logTerms.head?.map fun t => CCommRing.isZero
          (CField.sub t.1 (CField.div CCommRing.one (CFrac.ofScalar (1 : ℚ))))))
      = (true, some 1, some true) := by native_decide

/-! ### Witness B — the order-3 divisor on `y² = x³ + 1`, search starved to fuel 2 -/

/-- Non-torsion-within-fuel inputs: residue divisor `hcubeTorsionDiv = P = (x, y − 1)·O` (order 3) on
`y² = x³ + 1`, with an irrelevant generator oracle. -/
def genCurveWitnessNonTorsionInputs : GeneralCurveTorsionInputs :=
  ⟨hcubeTorsionDiv, fun _ => gcuspCubicY⟩

/-- The decision run on the order-3 divisor with fuel `2 < 3`: `hasLogPart = true`, `ratIntegrand =
0`, `logIntegrand = 1`; expected `none`. -/
def genCurveWitnessNonTorsion : Option GeneralCurveIntegralResult :=
  cIntegrateGeneralCurveDecide 2 hcubeF hcubeBasis 2
    ([] : DensePoly (DenseFrac ℚ)) ([CCommRing.one] : DensePoly (DenseFrac ℚ)) genCurveWitnessNonTorsionInputs true

/-- The decision returns `none` on the order-3 divisor with fuel `2 < 3`: `genCurveWitnessNonTorsion =
none`. -/
theorem genCurveWitnessNonTorsion_none : genCurveWitnessNonTorsion = none := by native_decide

/-! ## Combined decision witness -/

/-- Both verdicts through `cIntegrateGeneralCurveDecide`: on `y³ = x²` the divisor `div(y)` gives
`some` with a `(1/1)·log y` term, and on `y² = x³ + 1` the order-3 divisor with fuel 2 gives `none`. -/
theorem self_determining_general_curve_decision_validates :
    (genCurveWitnessTorsion.isSome,
     (genCurveWitnessTorsion.map fun F => F.logTerms.length),
     (genCurveWitnessTorsion.bind fun F =>
        F.logTerms.head?.map fun t => CCommRing.isZero
          (CField.sub t.1 (CField.div CCommRing.one (CFrac.ofScalar (1 : ℚ))))))
      = (true, some 1, some true)
    ∧ genCurveWitnessNonTorsion = none := by native_decide


/-! ### Axiom audit

The decision, soundness, completeness, and criterion theorems are axiom-clean
(`[propext, Classical.choice, Quot.sound]`); the witnesses use `native_decide` (`Lean.ofReduceBool`). -/


end DeepWiki.SymbolicIntegration
