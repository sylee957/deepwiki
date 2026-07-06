import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # Evaluating polynomial fractions

Small API for evaluating `RatFunc K` values presented as fractions of polynomial
images at points where the denominator does not vanish.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- If `g ∣ h` and `h(α) ≠ 0`, then `g(α) ≠ 0`. -/
theorem eval_ne_zero_of_dvd {α : K} {g h : K[X]} (hdvd : g ∣ h) (hh : h.eval α ≠ 0) :
    g.eval α ≠ 0 := by
  obtain ⟨c, rfl⟩ := hdvd
  rw [eval_mul] at hh
  exact left_ne_zero_of_mul hh

/-- Evaluation of a rational function presented as a quotient of polynomial images. -/
theorem eval_algebraMap_div (α : K) (g h : K[X]) (hh : h.eval α ≠ 0) :
    RatFunc.eval (RingHom.id K) α (algebraMap K[X] (RatFunc K) g / algebraMap K[X] (RatFunc K) h)
      = g.eval α / h.eval α := by
  set x : RatFunc K := algebraMap K[X] (RatFunc K) g / algebraMap K[X] (RatFunc K) h with hx
  have hh0 : h ≠ 0 := fun h0 => hh (by rw [h0, eval_zero])
  have hdenom : (RatFunc.denom x).eval α ≠ 0 :=
    eval_ne_zero_of_dvd (RatFunc.denom_div_dvd g h) hh
  have hcross : RatFunc.num x * h = g * RatFunc.denom x := by
    have hd := RatFunc.denom_ne_zero x
    have heq : algebraMap K[X] (RatFunc K) (RatFunc.num x)
          / algebraMap K[X] (RatFunc K) (RatFunc.denom x)
        = algebraMap K[X] (RatFunc K) g / algebraMap K[X] (RatFunc K) h :=
      (RatFunc.num_div_denom x).trans hx
    rw [div_eq_div_iff
      ((map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hd)
      ((map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hh0),
      ← map_mul, ← map_mul] at heq
    exact RatFunc.algebraMap_injective K heq
  have heval : (RatFunc.num x).eval α * h.eval α = g.eval α * (RatFunc.denom x).eval α := by
    simpa only [eval_mul] using congrArg (Polynomial.eval α) hcross
  rw [RatFunc.eval, Polynomial.eval₂_id, Polynomial.eval₂_id, div_eq_div_iff hdenom hh]
  exact heval

end DeepWiki.SymbolicIntegration
