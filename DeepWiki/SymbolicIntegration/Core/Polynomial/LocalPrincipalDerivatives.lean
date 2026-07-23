import DeepWiki.SymbolicIntegration.Core.Polynomial.LocalPrincipalParts
import DeepWiki.Algebra.RatFuncEvaluation
import DeepWiki.SymbolicIntegration.DifferentialAlgebra.RationalFunctionDerivative
import DeepWiki.ComputableAlgebra.PolySquarefreeTheory

/-! # Derivative readings of local principal coefficients

Connects the `(X - C α)`-adic digits of a local approximant with iterated
polynomial and rational-function derivatives.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ## Local coefficients as derivative values -/

/-- `(ratFuncKDeriv^[d]) (algebraMap p) = algebraMap (derivative^[d] p)`. -/
theorem iterate_ratFuncKDeriv_algebraMap (p : K[X]) (d : ℕ) :
    (ratFuncKDeriv^[d]) (algebraMap K[X] (RatFunc K) p)
      = algebraMap K[X] (RatFunc K) (derivative^[d] p) := by
  induction d generalizing p with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      show ratFuncKDeriv (algebraMap K[X] (RatFunc K) p) = algebraMap K[X] (RatFunc K) (derivative p)
        from ratFuncDeriv_algebraMap p, ih]

/-- Evaluation of iterated `ratFuncKDeriv` on a polynomial image. -/
theorem eval_iterate_ratFuncKDeriv_algebraMap (W : K[X]) (α : K) (d : ℕ) :
    RatFunc.eval (RingHom.id K) α ((ratFuncKDeriv^[d]) (algebraMap K[X] (RatFunc K) W))
      = (derivative^[d] W).eval α := by
  rw [iterate_ratFuncKDeriv_algebraMap]
  have h := eval_algebraMap_div α (derivative^[d] W) 1 (by simp)
  rwa [map_one, div_one, Polynomial.eval_one, div_one] at h

/-- The Hasse-derivative identity `(derivative^[d] W).eval α = d!·(taylor α W).coeff d`. -/
theorem eval_iterate_derivative_eq_factorial_taylor_coeff (W : K[X]) (α : K) (d : ℕ) :
    (derivative^[d] W).eval α = (d.factorial : K) * (taylor α W).coeff d := by
  have hhasse : derivative^[d] W = d.factorial • hasseDeriv d W := by
    have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := K) (k := d)) W
    simpa using h.symm
  rw [hhasse, Polynomial.taylor_coeff, Polynomial.eval_smul, nsmul_eq_mul]

/-- The derivative value of `localApprox` is `d!` times `localCoeff`. -/
theorem eval_iterate_ratFuncKDeriv_algebraMap_eq_localCoeff (A M : K[X]) (α : K) (i d : ℕ) :
    RatFunc.eval (RingHom.id K) α
        ((ratFuncKDeriv^[d]) (algebraMap K[X] (RatFunc K) (localApprox A M α i)))
      = (d.factorial : K) * localCoeff A M α i d := by
  rw [eval_iterate_ratFuncKDeriv_algebraMap, eval_iterate_derivative_eq_factorial_taylor_coeff,
    localCoeff]

/-- Iterated derivatives of `p/M` preserve a controlled residual zero at `α`. -/
theorem exists_iterate_ratFuncKDeriv_div (p M : K[X]) {α : K} (i : ℕ) (hM : M.eval α ≠ 0)
    (hdvd : (Polynomial.X - Polynomial.C α) ^ i ∣ p) :
    ∀ d, d ≤ i → ∃ (Pd Qd : K[X]), Qd.eval α ≠ 0 ∧ (Polynomial.X - Polynomial.C α) ^ (i - d) ∣ Pd ∧
      (ratFuncKDeriv^[d]) (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) M)
        = algebraMap K[X] (RatFunc K) Pd / algebraMap K[X] (RatFunc K) Qd := by
  intro d
  induction d with
  | zero =>
    intro _
    exact ⟨p, M, hM, by simpa using hdvd, by rw [Function.iterate_zero_apply]⟩
  | succ n ih =>
    intro hsucc
    obtain ⟨Pn, Qn, hQn, hdvdn, heqn⟩ := ih (Nat.le_of_succ_le hsucc)
    refine ⟨derivative Pn * Qn - Pn * derivative Qn, Qn ^ 2, ?_, ?_, ?_⟩
    · rw [Polynomial.eval_pow]; exact pow_ne_zero 2 hQn
    · have hd1 : (Polynomial.X - Polynomial.C α) ^ (i - n - 1) ∣ derivative Pn :=
        pow_sub_one_dvd_derivative_of_pow_dvd hdvdn
      have hd2 : (Polynomial.X - Polynomial.C α) ^ (i - n - 1) ∣ Pn :=
        dvd_trans (pow_dvd_pow _ (by omega)) hdvdn
      rw [show i - (n + 1) = i - n - 1 from by omega]
      exact dvd_sub (Dvd.dvd.mul_right hd1 Qn) (Dvd.dvd.mul_right hd2 (derivative Qn))
    · rw [Function.iterate_succ_apply', heqn]
      have hQn0 : algebraMap K[X] (RatFunc K) Qn ≠ 0 :=
        (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
          (fun h => hQn (by rw [h, Polynomial.eval_zero]))
      rw [Derivation.leibniz_div,
        show ratFuncKDeriv (algebraMap K[X] (RatFunc K) Pn) = algebraMap K[X] (RatFunc K) (derivative Pn)
          from ratFuncDeriv_algebraMap Pn,
        show ratFuncKDeriv (algebraMap K[X] (RatFunc K) Qn) = algebraMap K[X] (RatFunc K) (derivative Qn)
          from ratFuncDeriv_algebraMap Qn]
      rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, map_sub, map_mul, map_mul, map_pow]
      rw [inv_pow, ← div_eq_inv_mul, div_eq_div_iff (pow_ne_zero 2 hQn0) (pow_ne_zero 2 hQn0)]
      ring

/-- If `p` has a zero of order `i`, then the first `i` derivatives of `p/M` vanish at `α`. -/
theorem eval_iterate_ratFuncKDeriv_div_eq_zero (p M : K[X]) {α : K} (i d : ℕ) (hM : M.eval α ≠ 0)
    (hdvd : (Polynomial.X - Polynomial.C α) ^ i ∣ p) (hd : d < i) :
    RatFunc.eval (RingHom.id K) α
        ((ratFuncKDeriv^[d]) (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) M)) = 0 := by
  obtain ⟨Pd, Qd, hQd, hdvdd, heqd⟩ :=
    exists_iterate_ratFuncKDeriv_div p M i hM hdvd d (Nat.le_of_lt hd)
  rw [heqd, eval_algebraMap_div α Pd Qd hQd]
  obtain ⟨s, hs⟩ := hdvdd
  have hPd0 : Pd.eval α = 0 := by
    rw [hs, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_self, zero_pow (by omega), zero_mul]
  rw [hPd0, zero_div]

/-- `A/M − W = (A − M·W)/M` in `K(x)` for `W = localApprox A M α i`. -/
theorem hFrac_sub_localApprox (A M : K[X]) (α : K) (i : ℕ) (hM : M.eval α ≠ 0) :
    algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) M
        - algebraMap K[X] (RatFunc K) (localApprox A M α i)
      = algebraMap K[X] (RatFunc K) (A - M * localApprox A M α i)
          / algebraMap K[X] (RatFunc K) M := by
  have hM0 : algebraMap K[X] (RatFunc K) M ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (fun h => hM (by rw [h, Polynomial.eval_zero]))
  rw [map_sub, map_mul]
  field_simp

/-- `(ratFuncKDeriv^[d])` is additive. -/
theorem iterate_ratFuncKDeriv_add (x y : RatFunc K) (d : ℕ) :
    (ratFuncKDeriv^[d]) (x + y) = (ratFuncKDeriv^[d]) x + (ratFuncKDeriv^[d]) y := by
  induction d generalizing x y with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      map_add, ih]

/-- `localCoeff` is the Taylor coefficient of the regular fraction `A/M` at `α`. -/
theorem localCoeff_eq_taylor_coeff [CharZero K] (A M : K[X]) {α : K} (i d : ℕ) (hM : M.eval α ≠ 0)
    (hd : d < i) :
    localCoeff A M α i d
      = (((d.factorial : K))⁻¹)
          * RatFunc.eval (RingHom.id K) α
              ((ratFuncKDeriv^[d])
                (algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) M)) := by
  set W := localApprox A M α i with hWdef
  obtain ⟨Pd, Qd, hQd, hdvdd, heqd⟩ :=
    exists_iterate_ratFuncKDeriv_div (A - M * W) M i hM (localApprox_spec A M i hM) d
      (Nat.le_of_lt hd)
  have hPd0 : Pd.eval α = 0 := by
    obtain ⟨s, hs⟩ := hdvdd
    rw [hs, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_self, zero_pow (by omega), zero_mul]
  have hsplit : algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) M
      = algebraMap K[X] (RatFunc K) W
        + (algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) M
            - algebraMap K[X] (RatFunc K) W) := by ring
  rw [hsplit, iterate_ratFuncKDeriv_add, iterate_ratFuncKDeriv_algebraMap,
    hFrac_sub_localApprox A M α i hM, ← hWdef, heqd]
  have hQd0 : algebraMap K[X] (RatFunc K) Qd ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (fun h => hQd (by rw [h, Polynomial.eval_zero]))
  have hcomb : algebraMap K[X] (RatFunc K) (derivative^[d] W)
        + algebraMap K[X] (RatFunc K) Pd / algebraMap K[X] (RatFunc K) Qd
      = algebraMap K[X] (RatFunc K) (derivative^[d] W * Qd + Pd) / algebraMap K[X] (RatFunc K) Qd := by
    rw [map_add, map_mul, add_div, mul_div_assoc, div_self hQd0, mul_one]
  rw [hcomb, eval_algebraMap_div α _ _ hQd]
  rw [Polynomial.eval_add, Polynomial.eval_mul, hPd0, add_zero,
    eval_iterate_derivative_eq_factorial_taylor_coeff, localCoeff, ← hWdef]
  have hfac : (d.factorial : K) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero (R := K)).mpr (Nat.factorial_ne_zero d)
  field_simp

end DeepWiki.SymbolicIntegration
