import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalWellFounded
import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralWellFounded
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalLogSoundness
import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralLogSoundness
import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralIntegralSoundness

/-! # Fuel-free soundness of the algebraic integrator: `some F → D(F) = integrand`

Full soundness for the fuel-free algebraic drivers `cIntegrateAlgebraicWf` (radical, `y² = ρ`) and
`afIntegrateAlgebraicWf` (general curve, `K(x)[y]/(f)`), unconditional in the part hypotheses and gated
only on the engine's own round-trip certificate. Delivers each in two forms: the cross-multiplied
`IsAlgebraicIntegral` / `IsGeneralAlgebraicIntegralWf` (composing the proven telescoping + partial
fraction with the round-trip split) and the clean un-cross-multiplied `D(F) = integrand`. Axiom-clean
(`[propext, Classical.choice, Quot.sound]`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential
open RadElem CPoly

/-! ## Task 1 — the radical integrator `cIntegrateAlgebraicWf` -/

/-- The radical integrator's output satisfies the cross-multiplied `IsAlgebraicIntegral`: given the
proven `hrat` (rational-part telescoping), `hlog` (log-part residue match), and the round-trip
`hsplit`, `IsAlgebraicIntegral 2 ρ f F.ratPart commonDenomQ F.logTerms cofs` holds for the literal
output `F`. -/
theorem cIntegrateAlgebraicWf_isAlgebraicIntegral
    (ρ : QFunNZ ℚ) (R B : CPoly ℚ) (residual : RadElem (QFunNZ ℚ))
    (c : QFunNZ ℚ) (D : CPoly ℚ) (degBound : ℕ)
    (f ratPart logPart commonDenomQ : RadElem (QFunNZ ℚ)) (cofs : List (RadElem (QFunNZ ℚ)))
    (hrat : Ideal.Quotient.mk (radIdeal 2 ρ)
          (CPoly.toPoly (radMul 2 ρ
            (radDeriv 2 ρ (cIntegrateAlgebraicWf ρ R B residual c D degBound).ratPart) commonDenomQ))
        = Ideal.Quotient.mk (radIdeal 2 ρ) (CPoly.toPoly (radMul 2 ρ ratPart commonDenomQ)))
    (hlog : RadElem.IsRadicalLogIntegral 2 ρ logPart commonDenomQ
      (cIntegrateAlgebraicWf ρ R B residual c D degBound).logTerms cofs)
    (hsplit : Ideal.Quotient.mk (radIdeal 2 ρ) (CPoly.toPoly (radMul 2 ρ ratPart commonDenomQ))
        + Ideal.Quotient.mk (radIdeal 2 ρ) (CPoly.toPoly (radMul 2 ρ logPart commonDenomQ))
      = Ideal.Quotient.mk (radIdeal 2 ρ) (CPoly.toPoly (radMul 2 ρ f commonDenomQ))) :
    RadElem.IsAlgebraicIntegral 2 ρ f
      (cIntegrateAlgebraicWf ρ R B residual c D degBound).ratPart commonDenomQ
      (cIntegrateAlgebraicWf ρ R B residual c D degBound).logTerms cofs :=
  RadElem.isAlgebraicIntegral_of_parts 2 ρ f _ ratPart logPart commonDenomQ _ cofs hrat hlog hsplit

/-- The radical capstone `cIntegrateAlgebraicWf_sound`: from the engine round-trip certificate
`radIsZero (radSub (algDeriv ρ F) integrand) = true` alone, `toPoly (algDeriv ρ F) = toPoly
integrand` — the un-cross-multiplied `D(v + Σ cᵢ log uᵢ) = f`. -/
theorem cIntegrateAlgebraicWf_sound
    (ρ : QFunNZ ℚ) (R B : CPoly ℚ) (residual : RadElem (QFunNZ ℚ))
    (c : QFunNZ ℚ) (D : CPoly ℚ) (degBound : ℕ) (integrand : RadElem (QFunNZ ℚ))
    (hrt : RadElem.radIsZero
      (RadElem.radSub (algDeriv ρ (cIntegrateAlgebraicWf ρ R B residual c D degBound)) integrand)
      = true) :
    CPoly.toPoly (algDeriv ρ (cIntegrateAlgebraicWf ρ R B residual c D degBound))
      = CPoly.toPoly integrand :=
  toPolyG_algDeriv_eq_of_roundtrip ρ (cIntegrateAlgebraicWf ρ R B residual c D degBound) integrand hrt

/-! ## Task 2 — the general-curve integrator `afIntegrateAlgebraicWf` -/

/-- The general integrator's `some (v, u)` output satisfies the cross-multiplied
`IsGeneralAlgebraicIntegralWf`: given the proven `hrat`, `hlog`, and the round-trip `hsplit`,
`IsGeneralAlgebraicIntegralWf f g v commonDenomQ [(c, u)] cofs` holds for the literal output. -/
theorem afIntegrateAlgebraicWf_isGeneralAlgebraicIntegralWf
    (f : CPoly (QFunNZ ℚ)) (basis : List (CPoly (QFunNZ ℚ))) (degBound : ℕ)
    (ratIntegrand logIntegrand : CPoly (QFunNZ ℚ)) (p : CPoly (QFunNZ ℚ) × CPoly (QFunNZ ℚ))
    (g ratPart logPart commonDenomQ : CPoly (QFunNZ ℚ)) (c : QFunNZ ℚ)
    (cofs : List (CPoly (QFunNZ ℚ)))
    (hrun : afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand = some p)
    (hrat : Ideal.Quotient.mk (afIdeal f)
          (CPoly.toPoly (afMul f (afDerivWf f p.1) commonDenomQ))
        = Ideal.Quotient.mk (afIdeal f) (CPoly.toPoly (afMul f ratPart commonDenomQ)))
    (hlog : CPoly.IsGeneralLogIntegralWf f logPart commonDenomQ [(c, p.2)] cofs)
    (hsplit : Ideal.Quotient.mk (afIdeal f) (CPoly.toPoly (afMul f ratPart commonDenomQ))
        + Ideal.Quotient.mk (afIdeal f) (CPoly.toPoly (afMul f logPart commonDenomQ))
      = Ideal.Quotient.mk (afIdeal f) (CPoly.toPoly (afMul f g commonDenomQ))) :
    CPoly.IsGeneralAlgebraicIntegralWf f g
      ((afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand).get
        (by rw [hrun]; exact rfl)).1
      commonDenomQ
      [(c, ((afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand).get
        (by rw [hrun]; exact rfl)).2)] cofs := by
  -- the literal output's components ARE `p` (via `hrun`), so the conclusion is genuinely about the engine
  have hget : (afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand).get
      (by rw [hrun]; exact rfl) = p := by rw [Option.get_of_mem _ hrun]
  rw [hget]
  exact CPoly.isGeneralAlgebraicIntegralWf_of_parts f g p.1 ratPart logPart commonDenomQ _ cofs
    hrat hlog hsplit

/-- The general capstone `afIntegrateAlgebraicWf_sound`: from the engine round-trip check `cisZero
(csub (afDerivWf f v) ratIntegrand) = true` alone, `toPoly (afDerivWf f v) = toPoly ratIntegrand` —
the faithful `D(v) = ratIntegrand` for the general rational part. -/
theorem afIntegrateAlgebraicWf_sound
    (f : CPoly (QFunNZ ℚ)) (basis : List (CPoly (QFunNZ ℚ))) (degBound : ℕ)
    (ratIntegrand logIntegrand : CPoly (QFunNZ ℚ))
    (p : CPoly (QFunNZ ℚ) × CPoly (QFunNZ ℚ))
    (hrun : afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand = some p)
    (hcheck : CPoly.cisZero (CPoly.csub (afDerivWf f p.1) ratIntegrand) = true) :
    CPoly.toPoly (afDerivWf f
        ((afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand).get
          (by rw [hrun]; exact rfl)).1)
      = CPoly.toPoly ratIntegrand := by
  -- the literal output's rational part IS `p.1` (via `hrun`), so this is `D(v) = ratIntegrand` for the engine
  have hget : (afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand).get
      (by rw [hrun]; exact rfl) = p := by rw [Option.get_of_mem _ hrun]
  rw [hget]
  exact CPoly.toPolyG_afDerivWf_eq_of_roundtrip f p.1 ratIntegrand hcheck

/-- The fuel-free general driver output satisfies `IsGeneralRationalIntegralWf`. -/
theorem afIntegrateAlgebraicWf_isGeneralRationalIntegralWf
    (f : CPoly (QFunNZ ℚ)) (basis : List (CPoly (QFunNZ ℚ))) (degBound : ℕ)
    (ratIntegrand logIntegrand : CPoly (QFunNZ ℚ))
    (p : CPoly (QFunNZ ℚ) × CPoly (QFunNZ ℚ))
    (hrun : afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand = some p)
    (hcheck : CPoly.cisZero (CPoly.csub (afDerivWf f p.1) ratIntegrand) = true) :
    CPoly.IsGeneralRationalIntegralWf f ratIntegrand
      ((afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand).get
        (by rw [hrun]; exact rfl)).1 := by
  have hget : (afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand).get
      (by rw [hrun]; exact rfl) = p := by rw [Option.get_of_mem _ hrun]
  rw [hget]
  exact CPoly.isGeneralRationalIntegralWf_of_roundtrip f p.1 ratIntegrand hcheck

/-! ## Restatements and axiom audit -/

/-! ### Restatements (anonymous `example`s) -/

-- ★ RADICAL CAPSTONE (fuel-free, unconditional modulo round-trip): the fuel-free radical integrator's output
-- differentiates to the integrand — `D(F) = integrand` in `K[X]`, from the engine round-trip certificate.
example (ρ : QFunNZ ℚ) (R B : CPoly ℚ) (residual : RadElem (QFunNZ ℚ))
    (c : QFunNZ ℚ) (D : CPoly ℚ) (degBound : ℕ) (integrand : RadElem (QFunNZ ℚ))
    (hrt : RadElem.radIsZero
      (RadElem.radSub (algDeriv ρ (cIntegrateAlgebraicWf ρ R B residual c D degBound)) integrand)
      = true) :
    CPoly.toPoly (algDeriv ρ (cIntegrateAlgebraicWf ρ R B residual c D degBound))
      = CPoly.toPoly integrand :=
  cIntegrateAlgebraicWf_sound ρ R B residual c D degBound integrand hrt

-- ★ GENERAL CAPSTONE (fuel-free, unconditional modulo round-trip): the fuel-free general integrator's
-- rational part differentiates to the rational integrand — `D(v) = ratIntegrand`, from the engine check.
example (f : CPoly (QFunNZ ℚ)) (basis : List (CPoly (QFunNZ ℚ))) (degBound : ℕ)
    (ratIntegrand logIntegrand : CPoly (QFunNZ ℚ))
    (p : CPoly (QFunNZ ℚ) × CPoly (QFunNZ ℚ))
    (hrun : afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand = some p)
    (hcheck : CPoly.cisZero (CPoly.csub (afDerivWf f p.1) ratIntegrand) = true) :
    CPoly.toPoly (afDerivWf f
        ((afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand).get
          (by rw [hrun]; exact rfl)).1)
      = CPoly.toPoly ratIntegrand :=
  afIntegrateAlgebraicWf_sound f basis degBound ratIntegrand logIntegrand p hrun hcheck

-- ★ GENERAL CAPSTONE predicate form: the fuel-free general integrator's rational part is an
-- `IsGeneralRationalIntegralWf` witness.
example (f : CPoly (QFunNZ ℚ)) (basis : List (CPoly (QFunNZ ℚ))) (degBound : ℕ)
    (ratIntegrand logIntegrand : CPoly (QFunNZ ℚ))
    (p : CPoly (QFunNZ ℚ) × CPoly (QFunNZ ℚ))
    (hrun : afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand = some p)
    (hcheck : CPoly.cisZero (CPoly.csub (afDerivWf f p.1) ratIntegrand) = true) :
    CPoly.IsGeneralRationalIntegralWf f ratIntegrand
      ((afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand).get
        (by rw [hrun]; exact rfl)).1 :=
  afIntegrateAlgebraicWf_isGeneralRationalIntegralWf f basis degBound ratIntegrand logIntegrand p hrun hcheck

-- The cross-multiplied radical `IsAlgebraicIntegral` for the literal output (Form A): the proven
-- telescoping + partial fraction, the split from the round-trip.
example (ρ : QFunNZ ℚ) (R B : CPoly ℚ) (residual : RadElem (QFunNZ ℚ))
    (c : QFunNZ ℚ) (D : CPoly ℚ) (degBound : ℕ)
    (f ratPart logPart commonDenomQ : RadElem (QFunNZ ℚ)) (cofs : List (RadElem (QFunNZ ℚ)))
    (hrat : Ideal.Quotient.mk (radIdeal 2 ρ)
          (CPoly.toPoly (radMul 2 ρ
            (radDeriv 2 ρ (cIntegrateAlgebraicWf ρ R B residual c D degBound).ratPart) commonDenomQ))
        = Ideal.Quotient.mk (radIdeal 2 ρ) (CPoly.toPoly (radMul 2 ρ ratPart commonDenomQ)))
    (hlog : RadElem.IsRadicalLogIntegral 2 ρ logPart commonDenomQ
      (cIntegrateAlgebraicWf ρ R B residual c D degBound).logTerms cofs)
    (hsplit : Ideal.Quotient.mk (radIdeal 2 ρ) (CPoly.toPoly (radMul 2 ρ ratPart commonDenomQ))
        + Ideal.Quotient.mk (radIdeal 2 ρ) (CPoly.toPoly (radMul 2 ρ logPart commonDenomQ))
      = Ideal.Quotient.mk (radIdeal 2 ρ) (CPoly.toPoly (radMul 2 ρ f commonDenomQ))) :
    RadElem.IsAlgebraicIntegral 2 ρ f
      (cIntegrateAlgebraicWf ρ R B residual c D degBound).ratPart commonDenomQ
      (cIntegrateAlgebraicWf ρ R B residual c D degBound).logTerms cofs :=
  cIntegrateAlgebraicWf_isAlgebraicIntegral ρ R B residual c D degBound f ratPart logPart commonDenomQ cofs
    hrat hlog hsplit

/-! ### Axiom audit -/

-- ★★ THE RADICAL CAPSTONE (fuel-free, unconditional modulo round-trip): `some F → D(F) = integrand`:
#print axioms cIntegrateAlgebraicWf_sound
-- ★★ THE GENERAL CAPSTONE (fuel-free, unconditional modulo round-trip): `some (v, u) → D(v) = ratIntegrand`:
#print axioms afIntegrateAlgebraicWf_sound
-- Predicate-shaped version of the same fuel-free general rational-part soundness:
#print axioms afIntegrateAlgebraicWf_isGeneralRationalIntegralWf
-- ★ Form A radical — the cross-multiplied `IsAlgebraicIntegral` for the literal output:
#print axioms cIntegrateAlgebraicWf_isAlgebraicIntegral
-- ★ Form A general — the cross-multiplied `IsGeneralAlgebraicIntegralWf` for the literal output:
#print axioms afIntegrateAlgebraicWf_isGeneralAlgebraicIntegralWf

end DeepWiki.SymbolicIntegration
