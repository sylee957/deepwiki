import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-! # Polynomial normalization over fields

Small normalization identities for univariate polynomials over fields.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Classical in
/-- `p = C p.leadingCoeff * normalize p` over a field. -/
theorem self_eq_C_leadingCoeff_mul_normalize {K : Type*} [Field K] (p : K[X]) (hp : p ≠ 0) :
    p = Polynomial.C p.leadingCoeff * normalize p := by
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hcn : ((normUnit p.leadingCoeff : K) : K) = p.leadingCoeff⁻¹ := by
    simp [normUnit, hlc]
  rw [normalize_apply, Polynomial.coe_normUnit, hcn]
  rw [show Polynomial.C p.leadingCoeff * (p * Polynomial.C p.leadingCoeff⁻¹)
        = (Polynomial.C p.leadingCoeff * Polynomial.C p.leadingCoeff⁻¹) * p from by ring,
    ← map_mul, mul_inv_cancel₀ hlc, map_one, one_mul]

end DeepWiki.SymbolicIntegration
