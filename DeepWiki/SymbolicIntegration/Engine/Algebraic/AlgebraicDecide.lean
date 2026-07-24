import DeepWiki.SymbolicIntegration.Engine.Algebraic.AlgebraicWfSoundness
import DeepWiki.SymbolicIntegration.Engine.Algebraic.AlgebraicCompleteness

/-! # The self-determining algebraic integrator `cIntegrateAlgebraicDecide`

Turns the total `cIntegrateAlgebraicWf` (over `y² = ρ`) into a decision procedure by wiring in the
torsion decision: it returns `some ⟨v, logs⟩` when the integral is elementary (no log part, principal
`1·log u`, or torsion `(1/m)·log g`) and `none` when the residue divisor is non-torsion (not
elementary). The wrapper states soundness, completeness, and the decision criterion in terms of the
residual hypotheses supplied by the algebraic log and torsion layers, with computed witnesses on
both verdicts. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential
open RadElem DensePoly
open DeepWiki.SymbolicIntegration.AlgebraicCompleteness

/-! ## Decision Integrator -/

/-- The self-determining algebraic integrator `cIntegrateAlgebraicDecide` over `y² = ρ`, returning
`Option (AlgIntegralResult (DenseFrac ℚ))`: computes the rational part `v`, then `some ⟨v, []⟩` if `hasLogPart =
false`, `some ⟨v, [(c, N/D)]⟩` on a principal `radLogArgSolve = some N`, `some ⟨v, [(1/m, g)]⟩` when
the residue divisor `Dm` is torsion, and `none` when it is non-torsion. -/
def cIntegrateAlgebraicDecide (p : ℕ) [Fact p.Prime]
    (ρ : DenseFrac ℚ) (R B : DensePoly ℚ)
    (residual : RadElem (DenseFrac ℚ)) (c : DenseFrac ℚ) (D : DensePoly ℚ) (degBound : ℕ)
    (ρq : DensePoly ℚ) (gen : ℕ) (Dm : DensePoly.MumfordDivisor ℚ) (hasLogPart : Bool) :
    Option (AlgIntegralResult (DenseFrac ℚ)) :=
  let ρpoly : DensePoly ℚ := CFrac.num ρ
  let runs := DensePoly.radIntegrateRationalWf ρpoly R B
  let v := radAssembleRatPart ρ runs
  if hasLogPart = false then
    some ⟨v, []⟩
  else
    match radLogArgSolve ρ residual D degBound with
    | some N =>
      let Dq : DenseFrac ℚ := CFrac.ofPoly D
      let u : RadElem (DenseFrac ℚ) := N.map (fun z => CField.div z Dq)
      some ⟨v, [(c, u)]⟩
    | none =>
      match torsionLogTerm p ρ ρq gen Dm with
      | some term => some ⟨v, [term]⟩
      | none => none

/-- On the principal branch, `cIntegrateAlgebraicDecide … = some (cIntegrateAlgebraicWf …)`: the
decision integrator returns the total integrator's `AlgIntegralResult (DenseFrac ℚ)` wrapped in `some`. -/
theorem cIntegrateAlgebraicDecide_principal_eq (p : ℕ) [Fact p.Prime]
    (ρ : DenseFrac ℚ) (R B : DensePoly ℚ)
    (residual : RadElem (DenseFrac ℚ)) (c : DenseFrac ℚ) (D : DensePoly ℚ) (degBound : ℕ)
    (ρq : DensePoly ℚ) (gen : ℕ) (Dm : DensePoly.MumfordDivisor ℚ)
    (hlog : (radLogArgSolve ρ residual D degBound).isSome = true) :
    cIntegrateAlgebraicDecide p ρ R B residual c D degBound ρq gen Dm true
      = some (cIntegrateAlgebraicWf ρ R B residual c D degBound) := by
  unfold cIntegrateAlgebraicDecide cIntegrateAlgebraicWf
  simp only [Bool.true_eq_false, if_false]
  cases hN : radLogArgSolve ρ residual D degBound with
  | none => rw [hN] at hlog; simp at hlog
  | some N => rfl

/-! ## Soundness -/

section Soundness

variable (p : ℕ) [Fact p.Prime]
variable (ρ : DenseFrac ℚ) (R B : DensePoly ℚ)
variable (residual : RadElem (DenseFrac ℚ)) (c : DenseFrac ℚ) (D : DensePoly ℚ) (degBound : ℕ)
variable (ρq : DensePoly ℚ) (gen : ℕ) (Dm : DensePoly.MumfordDivisor ℚ) (hasLogPart : Bool)
variable (integrand : RadElem (DenseFrac ℚ))

/-- The soundness residual `AlgebraicDecideSoundnessResidual …`: bundles the three branch
hypotheses (`hnolog`, `hprincipal`, `htorsion`) turning each `some F` branch of
`cIntegrateAlgebraicDecide` into `toPoly (algDeriv ρ F) = toPoly integrand`. -/
structure AlgebraicDecideSoundnessResidual : Prop where
  /-- No-log branch (rational-part exhaustiveness): `D(⟨v, []⟩) = integrand`. -/
  hnolog :
    DensePoly.toPoly (algDeriv ρ
        ⟨radAssembleRatPart ρ (DensePoly.radIntegrateRationalWf (CFrac.num ρ) R B), []⟩)
      = DensePoly.toPoly integrand
  /-- Principal branch (`cIntegrateAlgebraicWf_sound` discharge): `D(cIntegrateAlgebraicWf …) = integrand`. -/
  hprincipal :
    DensePoly.toPoly (algDeriv ρ (cIntegrateAlgebraicWf ρ R B residual c D degBound))
      = DensePoly.toPoly integrand
  /-- Torsion branch (`isTorsionDivisor`/`principalGenerator` correctness): for the constructed log term
  `term`, `D(⟨v, [term]⟩) = integrand`. -/
  htorsion : ∀ term,
    torsionLogTerm p ρ ρq gen Dm = some term →
    DensePoly.toPoly (algDeriv ρ
        ⟨radAssembleRatPart ρ (DensePoly.radIntegrateRationalWf (CFrac.num ρ) R B), [term]⟩)
      = DensePoly.toPoly integrand

/-- Soundness of `cIntegrateAlgebraicDecide`: under the soundness residual, `… = some F` implies
`toPoly (algDeriv ρ F) = toPoly integrand`. Checker-free (no round-trip hypothesis). -/
theorem cIntegrateAlgebraicDecide_sound
    (hres : AlgebraicDecideSoundnessResidual p ρ R B residual c D degBound ρq gen Dm integrand)
    (F : AlgIntegralResult (DenseFrac ℚ))
    (hsome : cIntegrateAlgebraicDecide p ρ R B residual c D degBound ρq gen Dm hasLogPart
      = some F) :
    DensePoly.toPoly (algDeriv ρ F) = DensePoly.toPoly integrand := by
  unfold cIntegrateAlgebraicDecide at hsome
  -- split the `hasLogPart` discriminator, then the principal log solve, then the torsion decision
  by_cases hlp : hasLogPart = false
  · -- no-log branch: F = ⟨v, []⟩
    rw [hlp, if_pos rfl, Option.some.injEq] at hsome
    rw [← hsome]
    exact hres.hnolog
  · -- has-log branch
    rw [if_neg hlp] at hsome
    cases hN : radLogArgSolve ρ residual D degBound with
    | some N =>
      -- principal branch: F = the `cIntegrateAlgebraicWf` output
      rw [hN, Option.some.injEq] at hsome
      rw [← hsome]
      -- the literal output equals `cIntegrateAlgebraicWf …` (same parts, same log term)
      have heq : (⟨radAssembleRatPart ρ (DensePoly.radIntegrateRationalWf (CFrac.num ρ) R B),
          [(c, N.map (fun z => CField.div z (CFrac.ofPoly D)))]⟩ : AlgIntegralResult (DenseFrac ℚ))
          = cIntegrateAlgebraicWf ρ R B residual c D degBound := by
        unfold cIntegrateAlgebraicWf
        rw [hN]
      rw [heq]
      exact hres.hprincipal
    | none =>
      -- torsion branch: F = ⟨v, [term]⟩ from `torsionLogTerm`, or `none`
      rw [hN] at hsome
      cases hT : torsionLogTerm p ρ ρq gen Dm with
      | some term =>
        rw [hT, Option.some.injEq] at hsome
        rw [← hsome]
        exact hres.htorsion term hT
      | none =>
        rw [hT] at hsome
        exact absurd hsome (by simp)

end Soundness

/-! ## Completeness -/

section Completeness

variable (p : ℕ) [Fact p.Prime]
variable (ρ : DenseFrac ℚ) (R B : DensePoly ℚ)
variable (residual : RadElem (DenseFrac ℚ)) (c : DenseFrac ℚ) (D : DensePoly ℚ) (degBound : ℕ)
variable (ρq : DensePoly ℚ) (gen : ℕ) (Dm : DensePoly.MumfordDivisor ℚ) (hasLogPart : Bool)

/-- A `none` output of `cIntegrateAlgebraicDecide` forces `(torsionLogTerm p ρ ρq gen Dm).isNone`:
the torsion branch fired and returned `none` (non-torsion divisor). -/
theorem torsionLogTerm_none_of_decide_none
    (hnone : cIntegrateAlgebraicDecide p ρ R B residual c D degBound ρq gen Dm hasLogPart
      = none) :
    (torsionLogTerm p ρ ρq gen Dm).isNone = true := by
  unfold cIntegrateAlgebraicDecide at hnone
  by_cases hlp : hasLogPart = false
  · rw [hlp] at hnone; simp at hnone
  · rw [if_neg hlp] at hnone
    cases hN : radLogArgSolve ρ residual D degBound with
    | some N => rw [hN] at hnone; simp at hnone
    | none =>
      rw [hN] at hnone
      cases hT : torsionLogTerm p ρ ρq gen Dm with
      | some term => rw [hT] at hnone; simp at hnone
      | none => simp

/-- Completeness of `cIntegrateAlgebraicDecide`: under `AlgebraicCompletenessResidual` on `Dm`, a
`none` output certifies `¬ elem` (the integrand is not elementary). -/
theorem cIntegrateAlgebraicDecide_complete {isTorsion : Prop} {elem : Prop}
    (hres : AlgebraicCompletenessResidual ρq gen Dm p isTorsion elem)
    (hnone : cIntegrateAlgebraicDecide p ρ R B residual c D degBound ρq gen Dm hasLogPart
      = none) :
    ¬ elem := by
  -- the `none` output forces the torsion branch to `none` (non-torsion verdict)
  have hT : (torsionLogTerm p ρ ρq gen Dm).isNone = true :=
    torsionLogTerm_none_of_decide_none p ρ R B residual c D degBound ρq gen Dm hasLogPart hnone
  -- contrapositive of the completeness equivalence: if `elem` held, the log term would be emitted
  intro hcon
  have hsome : (torsionLogTerm p ρ ρq gen Dm).isSome = true :=
    (cIntegrateAlgebraicWf_complete_of_residual ρ ρq gen Dm p hres).mpr hcon
  rw [Option.isNone_iff_eq_none] at hT
  rw [hT] at hsome
  simp at hsome

end Completeness

/-! ## Decision Criterion -/

section Decides

variable (p : ℕ) [Fact p.Prime]
variable (ρ : DenseFrac ℚ) (R B : DensePoly ℚ)
variable (residual : RadElem (DenseFrac ℚ)) (c : DenseFrac ℚ) (D : DensePoly ℚ) (degBound : ℕ)
variable (ρq : DensePoly ℚ) (gen : ℕ) (Dm : DensePoly.MumfordDivisor ℚ)

/-- On the non-principal log path (`hasLogPart = true`, `radLogArgSolve = none`),
`(cIntegrateAlgebraicDecide …).isSome ↔ (torsionLogTerm p ρ ρq gen Dm).isSome`. -/
theorem decide_isSome_iff_torsion_isSome
    (hlog : radLogArgSolve ρ residual D degBound = none) :
    (cIntegrateAlgebraicDecide p ρ R B residual c D degBound ρq gen Dm true).isSome = true
      ↔ (torsionLogTerm p ρ ρq gen Dm).isSome = true := by
  unfold cIntegrateAlgebraicDecide
  simp only [Bool.true_eq_false, if_false, hlog]
  cases hT : torsionLogTerm p ρ ρq gen Dm with
  | none => simp
  | some term => simp

/-- The decision-procedure capstone: on the non-principal log path (`hasLogPart = true`,
`radLogArgSolve = none`), under `AlgebraicCompletenessResidual`,
`(∃ F, cIntegrateAlgebraicDecide … true = some F) ↔ elem`. -/
theorem cIntegrateAlgebraicDecide_decides {isTorsion : Prop} {elem : Prop}
    (hres : AlgebraicCompletenessResidual ρq gen Dm p isTorsion elem)
    (hlog : radLogArgSolve ρ residual D degBound = none) :
    (∃ F, cIntegrateAlgebraicDecide p ρ R B residual c D degBound ρq gen Dm true = some F)
      ↔ elem := by
  rw [← Option.isSome_iff_exists,
    decide_isSome_iff_torsion_isSome p ρ R B residual c D degBound ρq gen Dm hlog]
  exact cIntegrateAlgebraicWf_complete_of_residual ρ ρq gen Dm p hres

end Decides

/-! ## End-To-End Witnesses -/

/-! ### Non-torsion witness -/

/-- A non-principal log residual `decideNonPrincipalResidual`: the double-pole integrand
`[0, 1/(x²·(x²+1))]` for which `radLogArgSolve … [0,0,1] 1 = none`, forcing the torsion decision to
govern the verdict. -/
def decideNonPrincipalResidual : RadElem (DenseFrac ℚ) :=
  radInvYLift (CFrac.ofPoly [0, 0, 1, 0, 1]) CCommRing.one

/-- `cIntegrateAlgebraicDecide` on the non-torsion `(3,5)` of `y² = x³ − 2`: a log-part input whose
principal solve fails and whose residue divisor is non-torsion, expected to return `none`. -/
def decideWitnessNonTorsion : Option (AlgIntegralResult (DenseFrac ℚ)) :=
  cIntegrateAlgebraicDecide 5 tltRhoX3m2 [1] [1] decideNonPrincipalResidual CCommRing.one [0, 0, 1] 1
    hypRhoX3m2 1 hypPt35 true

/-- `cIntegrateAlgebraicDecide` returns `none` on the non-torsion `(3,5)` of `y² = x³ − 2`: the
integrand is not elementary. -/
theorem decideWitnessNonTorsion_none : decideWitnessNonTorsion = none := by native_decide

/-! ### Torsion witness -/

/-- `cIntegrateAlgebraicDecide` on the order-3 torsion flex `(0,1)` of `y² = x³ + 1`: a log-part
input whose principal solve fails, expected to return `some ⟨v, [(1/3, y − 1)]⟩`. -/
def decideWitnessTorsion : Option (AlgIntegralResult (DenseFrac ℚ)) :=
  cIntegrateAlgebraicDecide 5 tltRhoX3p1 [1] [1] decideNonPrincipalResidual CCommRing.one [0, 0, 1] 1
    hypRhoX3p1 1 hypPt01 true

/-- `cIntegrateAlgebraicDecide` returns `some F` with one `(1/3)·log` term on the torsion `(0,1)` of
`y² = x³ + 1`, checked on `(isSome, logTerms.length, coefficient = 1/3)`. -/
theorem decideWitnessTorsion_some :
    (decideWitnessTorsion.isSome,
     (decideWitnessTorsion.map fun F => F.logTerms.length),
     (decideWitnessTorsion.bind fun F => F.logTerms.head?.map fun t =>
       CFrac.eq t.1 (CField.div CCommRing.one (CFrac.ofScalar (3 : ℚ)))))
      = (true, some 1, some true) := by native_decide

/-! ### Principal witness -/

/-- `cIntegrateAlgebraicDecide` on a principal-log example (`y² = x² + 1`, the `arcsinh` solve): with
a principal `radLogArgSolve = some N`, expected to return `some` with a `1·log(N/D)` term. -/
def decideWitnessPrincipal : Option (AlgIntegralResult (DenseFrac ℚ)) :=
  cIntegrateAlgebraicDecide 5 rtRatRho [1] [1]
    (radInvYLift rtRatRho CCommRing.one) CCommRing.one [1] 1
    (CFrac.num rtRatRho) 1 hypPt35 true

/-- `cIntegrateAlgebraicDecide` returns `some F` with one principal log term on the `∫ 1/√(x²+1)`
example: `(isSome, logTerms.length) = (true, some 1)`. -/
theorem decideWitnessPrincipal_some :
    (decideWitnessPrincipal.isSome, decideWitnessPrincipal.map fun F => F.logTerms.length)
      = (true, some 1) := by native_decide

/-! ## Self-determining algebraic decision validation -/

/-- End-to-end validation that `cIntegrateAlgebraicDecide` decides elementarity: `none` on the
non-torsion `(3,5)` of `y² = x³ − 2`, `some` with a `(1/3)·log` term on the torsion `(0,1)` of
`y² = x³ + 1`, and `some` with a principal log term on `∫ 1/√(x²+1)`. -/
theorem self_determining_algebraic_decision_validates :
    decideWitnessNonTorsion = none
    ∧ (decideWitnessTorsion.isSome,
       (decideWitnessTorsion.map fun F => F.logTerms.length),
       (decideWitnessTorsion.bind fun F => F.logTerms.head?.map fun t =>
         CFrac.eq t.1 (CField.div CCommRing.one (CFrac.ofScalar (3 : ℚ)))))
        = (true, some 1, some true)
    ∧ (decideWitnessPrincipal.isSome, decideWitnessPrincipal.map fun F => F.logTerms.length)
        = (true, some 1) := by native_decide


/-! ### Axiom audit -/

#print axioms cIntegrateAlgebraicDecide_sound
#print axioms cIntegrateAlgebraicDecide_complete
#print axioms cIntegrateAlgebraicDecide_decides
#print axioms decideWitnessNonTorsion_none
#print axioms decideWitnessTorsion_some
#print axioms self_determining_algebraic_decision_validates

end DeepWiki.SymbolicIntegration
