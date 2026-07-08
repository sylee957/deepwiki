import DeepWiki.SymbolicIntegration.Compute.Diophantine
import DeepWiki.SymbolicIntegration.Compute.HermitePower
import DeepWiki.SymbolicIntegration.Compute.RationalFunction
import DeepWiki.SymbolicIntegration.RationalFunctionDerivative

/-! # Correctness of the computable Hermite inner loop
Proves the one-factor Hermite inner loop in `RatFunc ℚ`, from the local Bezout step through the
public `hermiteInner_spec_of` theorem. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### The `hermiteInner` step identity and inner-loop invariant -/

open scoped Differential in
/-- The `hermiteInner` step identity in `RatFunc ℚ`. -/
theorem hermiteInner_step_ratFunc (A B C U V : ℚ[X]) (hU : U ≠ 0) (hV : V ≠ 0) (j : ℕ)
    (hrel : B * (U * derivative V) + C * V = -A * Polynomial.C (((j : ℚ) + 1)⁻¹)) :
    algebraMap ℚ[X] (RatFunc ℚ) A
        / (algebraMap ℚ[X] (RatFunc ℚ) U * algebraMap ℚ[X] (RatFunc ℚ) V ^ (j + 2))
      = (algebraMap ℚ[X] (RatFunc ℚ) B / algebraMap ℚ[X] (RatFunc ℚ) V ^ (j + 1))′
        + algebraMap ℚ[X] (RatFunc ℚ) (-(Polynomial.C ((j : ℚ) + 1)) * C - U * derivative B)
          / (algebraMap ℚ[X] (RatFunc ℚ) U * algebraMap ℚ[X] (RatFunc ℚ) V ^ (j + 1)) := by
  have hinj := RatFunc.algebraMap_injective (K := ℚ)
  set am := algebraMap ℚ[X] (RatFunc ℚ) with hamdef
  have hu : am U ≠ 0 := (map_ne_zero_iff _ hinj).mpr hU
  have hv : am V ≠ 0 := (map_ne_zero_iff _ hinj).mpr hV
  have hvp : am V ^ (j + 1) ≠ 0 := pow_ne_zero _ hv
  have hn1 : ((j : ℚ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero j
  have e1 : ∀ k : ℚ, am (Polynomial.C k) = algebraMap ℚ (RatFunc ℚ) k := fun k => by
    rw [hamdef, ← Polynomial.algebraMap_eq]
    exact (IsScalarTower.algebraMap_apply ℚ ℚ[X] (RatFunc ℚ) k).symm
  have hc1 : am (Polynomial.C ((j : ℚ) + 1)) = (j : RatFunc ℚ) + 1 := by
    rw [e1, map_add, map_natCast, map_one]
  have hκ : ((j : RatFunc ℚ) + 1) * am (Polynomial.C (((j : ℚ) + 1)⁻¹)) = 1 := by
    rw [e1, ← hc1, e1, ← map_mul, mul_inv_cancel₀ hn1, map_one]
  have hdB : (am B)′ = am (derivative B) := ratFuncDeriv_algebraMap B
  have hdV : (am V)′ = am (derivative V) := ratFuncDeriv_algebraMap V
  have hbez : am B * (am U * am (derivative V)) + am C * am V
      = -am A * am (Polynomial.C (((j : ℚ) + 1)⁻¹)) := by
    have h := congrArg am hrel
    rw [map_add, map_mul, map_mul, map_mul, map_mul, map_neg] at h
    exact h
  have hbez2 : ((j : RatFunc ℚ) + 1) * (am B * (am U * am (derivative V)) + am C * am V) = -am A := by
    rw [hbez]; linear_combination (-am A) * hκ
  have hderiv : (am B / am V ^ (j + 1))′
      = (am V ^ (j + 1) * am (derivative B)
          - am B * ((j + 1 : RatFunc ℚ) * am V ^ j * am (derivative V))) / (am V ^ (j + 1)) ^ 2 := by
    rw [deriv_div, hdB, deriv_pow, hdV, Nat.add_sub_cancel]
    push_cast; ring_nf
  rw [hderiv, map_sub, map_mul, map_mul, map_neg, hc1]
  have hA : am A = -((j : RatFunc ℚ) + 1) * (am B * (am U * am (derivative V)) + am C * am V) := by
    linear_combination hbez2
  rw [hA, pow_succ]
  field_simp
  ring

/-- The per-step Bezout relation of `hermiteInner` at counter `j'` with numerator `A'`. -/
private def hbezPred (fuel : ℕ) (V U : CPoly) (j' : ℕ) (A' : CPoly) : Prop :=
  toPoly (cdiophantine fuel (cmul U (cderiv V)) V (cscale (-((j' : ℚ) + 1)⁻¹) A')).1
      * (toPoly U * derivative (toPoly V))
    + toPoly (cdiophantine fuel (cmul U (cderiv V)) V (cscale (-((j' : ℚ) + 1)⁻¹) A')).2
      * toPoly V
    = -toPoly A' * Polynomial.C (((j' : ℚ) + 1)⁻¹)

/-- The Hermite-inner Bezout call has a nonzero denominator and constant gcd. -/
structure IsHermiteInnerBezoutInput (fuel : ℕ) (V U : CPoly) : Prop where
  /-- The inner denominator is nonzero. -/
  den_ne : cnorm V ≠ []
  /-- The computed gcd reads as its leading constant. -/
  gcd_const : toPoly (cgcdExt fuel (cmul U (cderiv V)) V).1
    = Polynomial.C (clead (cgcdExt fuel (cmul U (cderiv V)) V).1)
  /-- The leading coefficient of the computed gcd is nonzero. -/
  gcd_lead_ne : clead (cgcdExt fuel (cmul U (cderiv V)) V).1 ≠ 0

open scoped Differential in
/-- `hermiteInner` loop invariant, generalized over an accumulator. -/
theorem hermiteInner_spec_acc (fuel : ℕ) (V U : CPoly) (hU : toPoly U ≠ 0) (hV : toPoly V ≠ 0)
    (hbez : ∀ (j' : ℕ) (A' : CPoly), hbezPred fuel V U j' A') :
    ∀ (j : ℕ) (A : CPoly) (g : QFun), toPoly g.2 ≠ 0 →
      algebraMap ℚ[X] (RatFunc ℚ) (toPoly A)
          / (algebraMap ℚ[X] (RatFunc ℚ) (toPoly U)
              * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V) ^ (j + 1))
        + (toQFun g)′
        = (toQFun (hermiteInner fuel V U j A g).1)′
          + algebraMap ℚ[X] (RatFunc ℚ) (toPoly (hermiteInner fuel V U j A g).2)
            / (algebraMap ℚ[X] (RatFunc ℚ) (toPoly U) * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V)) := by
  set am := algebraMap ℚ[X] (RatFunc ℚ) with hamdef
  intro j
  induction j with
  | zero =>
    intro A g hg
    simp only [hermiteInner]
    rw [pow_one]; ring
  | succ j ih =>
    intro A g hg
    rw [hermiteInner]
    rcases hBC : cdiophantine fuel (cmul U (cderiv V)) V (cscale (-((j : ℚ) + 1)⁻¹) A)
      with ⟨B, C⟩
    simp only []
    set Vpow := (List.range (j + 1)).foldl (fun acc _ => cmul acc V) [1] with hVpowdef
    set A' := csub (cscale (-((j : ℚ) + 1)) C) (cmul U (cderiv B)) with hA'def
    have hVpow : toPoly Vpow = toPoly V ^ (j + 1) := toPoly_hermiteInner_Vpow V j
    have hVpow0 : toPoly Vpow ≠ 0 := by rw [hVpow]; exact pow_ne_zero _ hV
    have hqadd : toQFun (qadd g (B, Vpow)) = toQFun g + toQFun (B, Vpow) :=
      toQFun_qadd g (B, Vpow) hg hVpow0
    have hgnew : toPoly (qadd g (B, Vpow)).2 ≠ 0 := by
      show toPoly (cmul g.2 Vpow) ≠ 0
      rw [toPoly_cmul]; exact mul_ne_zero hg hVpow0
    have hcdB : toPoly (cderiv B) = derivative (toPoly B) := toPoly_cderiv B
    have hb : hbezPred fuel V U j A := hbez j A
    rw [hbezPred, hBC] at hb
    have hstep := hermiteInner_step_ratFunc (toPoly A) (toPoly B) (toPoly C) (toPoly U) (toPoly V)
      hU hV j ?_
    · have ihA := ih A' (qadd g (B, Vpow)) hgnew
      have hBVpow : toQFun (B, Vpow) = am (toPoly B) / am (toPoly V) ^ (j + 1) := by
        rw [toQFun, hVpow, map_pow]
      have hA'eq : toPoly A'
          = -(Polynomial.C ((j : ℚ) + 1)) * toPoly C - toPoly U * derivative (toPoly B) := by
        rw [hA'def, toPoly_csub, toPoly_cscale, toPoly_cmul, hcdB, map_neg]
      rw [hqadd, map_add, hBVpow, hA'eq] at ihA
      rw [show (j + 1 + 1) = (j + 2) from rfl]
      linear_combination hstep + ihA
    · exact hb

open scoped Differential in
/-- Public `qzero`-start correctness of the `hermiteInner` loop. -/
theorem hermiteInner_spec (fuel : ℕ) (V U : CPoly) (hU : toPoly U ≠ 0) (hV : toPoly V ≠ 0)
    (hbez : ∀ (j' : ℕ) (A' : CPoly), hbezPred fuel V U j' A') (j : ℕ) (A : CPoly) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A)
        / (algebraMap ℚ[X] (RatFunc ℚ) (toPoly U)
            * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V) ^ (j + 1))
      = (toQFun (hermiteInner fuel V U j A qzero).1)′
        + algebraMap ℚ[X] (RatFunc ℚ) (toPoly (hermiteInner fuel V U j A qzero).2)
          / (algebraMap ℚ[X] (RatFunc ℚ) (toPoly U) * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V)) := by
  have h := hermiteInner_spec_acc fuel V U hU hV hbez j A qzero (by simp [qzero, toPoly_cons])
  rw [toQFun_qzero, map_zero, add_zero] at h
  simpa using h

/-- The per-step Bezout relation follows from the computable constant-gcd certificate. -/
theorem hermiteInner_bezout_of (fuel : ℕ) (V U : CPoly) (j' : ℕ) (A' : CPoly)
    (hbez : IsHermiteInnerBezoutInput fuel V U) :
    hbezPred fuel V U j' A' := by
  obtain ⟨hq, hg, hgc⟩ := hbez
  rw [hbezPred]
  have h := toPoly_cdiophantine fuel (cmul U (cderiv V)) V
    (cscale (-((j' : ℚ) + 1)⁻¹) A') hq hg hgc
  rw [toPoly_cmul, toPoly_cderiv, toPoly_cscale] at h
  rw [h]
  rw [show Polynomial.C (-((j' : ℚ) + 1)⁻¹) = -Polynomial.C (((j' : ℚ) + 1)⁻¹) from by rw [map_neg]]
  ring

open scoped Differential in
/-- `hermiteInner` correctness from the computable engine, with the Bezout premise discharged. -/
theorem hermiteInner_spec_of (fuel : ℕ) (V U : CPoly) (hU : toPoly U ≠ 0) (hV : toPoly V ≠ 0)
    (hbez : IsHermiteInnerBezoutInput fuel V U) (j : ℕ) (A : CPoly) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A)
        / (algebraMap ℚ[X] (RatFunc ℚ) (toPoly U)
            * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V) ^ (j + 1))
      = (toQFun (hermiteInner fuel V U j A qzero).1)′
        + algebraMap ℚ[X] (RatFunc ℚ) (toPoly (hermiteInner fuel V U j A qzero).2)
          / (algebraMap ℚ[X] (RatFunc ℚ) (toPoly U) * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V)) :=
  hermiteInner_spec fuel V U hU hV
    (fun j' A' => hermiteInner_bezout_of fuel V U j' A' hbez) j A

open scoped Differential in
example (fuel : ℕ) (V U : CPoly) (hU : toPoly U ≠ 0) (hV : toPoly V ≠ 0) (hq : cnorm V ≠ [])
    (hg : toPoly (cgcdExt fuel (cmul U (cderiv V)) V).1
      = Polynomial.C (clead (cgcdExt fuel (cmul U (cderiv V)) V).1))
    (hgc : clead (cgcdExt fuel (cmul U (cderiv V)) V).1 ≠ 0) (j : ℕ) (A : CPoly) :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly A)
        / (algebraMap ℚ[X] (RatFunc ℚ) (toPoly U)
            * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V) ^ (j + 1))
      = (toQFun (hermiteInner fuel V U j A qzero).1)′
        + algebraMap ℚ[X] (RatFunc ℚ) (toPoly (hermiteInner fuel V U j A qzero).2)
          / (algebraMap ℚ[X] (RatFunc ℚ) (toPoly U) * algebraMap ℚ[X] (RatFunc ℚ) (toPoly V)) :=
  hermiteInner_spec_of fuel V U hU hV ⟨hq, hg, hgc⟩ j A

end DeepWiki.SymbolicIntegration.Compute
