import DeepWiki.SymbolicIntegration.Core.Polynomial.RatFuncEvaluation
import DeepWiki.SymbolicIntegration.LaurentCoefficients.RootEvaluation

/-! # Laurent Taylor coefficient bridge

Taylor-coefficient interpretation of the Laurent engine at regular roots. -/

open Polynomial MvPolynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ## `Hᵢⱼ(α)` is the order-`(i−j)` Taylor coefficient of `hᵢ,α` -/

/-- `(lDenomα Ei Diα i d).eval α ≠ 0` when `Ei(α), Diα(α) ≠ 0`. -/
theorem eval_lDenomα_ne_zero {Ei Diα : K[X]} {α : K} (i d : ℕ) (hEi : Ei.eval α ≠ 0)
    (hDiα : Diα.eval α ≠ 0) : (lDenomα Ei Diα i d).eval α ≠ 0 := by
  unfold lDenomα
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_pow]
  exact mul_ne_zero (pow_ne_zero _ hDiα) (pow_ne_zero _ hEi)

/-- Eval of `lFracα` at `α`:
`RatFunc.eval id α (lFracα A Ei Diα i d) = (diffSubst Diα (laurentNum …)).eval α / (lDenomα …).eval α`. -/
theorem eval_lFracα {A Ei Diα : K[X]} {α : K} (i d : ℕ) (hEi : Ei.eval α ≠ 0)
    (hDiα : Diα.eval α ≠ 0) :
    RatFunc.eval (RingHom.id K) α (lFracα A Ei Diα i d)
      = (diffSubst Diα (laurentNum A Ei i d)).eval α / (lDenomα Ei Diα i d).eval α := by
  rw [lFracα, eval_algebraMap_div α _ _ (eval_lDenomα_ne_zero i d hEi hDiα)]

/-- Eval of a `K`-scaled `lFracα` at `α`:
`RatFunc.eval id α (c • lFracα A Ei Diα i d) = c · ((diffSubst Diα (laurentNum …)).eval α / (lDenomα …).eval α)`. -/
theorem eval_smul_lFracα {A Ei Diα : K[X]} {α : K} (c : K) (i d : ℕ) (hEi : Ei.eval α ≠ 0)
    (hDiα : Diα.eval α ≠ 0) :
    RatFunc.eval (RingHom.id K) α (c • lFracα A Ei Diα i d)
      = c * ((diffSubst Diα (laurentNum A Ei i d)).eval α / (lDenomα Ei Diα i d).eval α) := by
  have hsmul : c • lFracα A Ei Diα i d
      = algebraMap K[X] (RatFunc K) (Polynomial.C c * diffSubst Diα (laurentNum A Ei i d))
        / algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i d) := by
    rw [lFracα, RatFunc.smul_eq_C_mul, ← RatFunc.algebraMap_C, map_mul, mul_div_assoc]
  rw [hsmul, eval_algebraMap_div α _ _ (eval_lDenomα_ne_zero i d hEi hDiα),
    Polynomial.eval_mul, Polynomial.eval_C, mul_div_assoc]

/-- The specialized invariant evaluated at the root `α`:
`RatFunc.eval id α ((ratFuncKDeriv^[d]) (hFracα A Ei Diα i)) = d!·(diffSubst Diα (laurentNum …)).eval α / (lDenomα …).eval α`,
for `0 < i`, `Ei(α), Diα(α) ≠ 0`. -/
theorem eval_ratFuncKDeriv_iterate_hFracα_at_root [CharZero K] {A Ei Diα : K[X]} {α : K} (i : ℕ)
    (hi : 0 < i) (hEi0 : Ei ≠ 0) (hDiα0 : Diα ≠ 0) (hEi : Ei.eval α ≠ 0) (hDiα : Diα.eval α ≠ 0)
    (d : ℕ) :
    RatFunc.eval (RingHom.id K) α ((ratFuncKDeriv^[d]) (hFracα A Ei Diα i))
      = (d.factorial : K) * (diffSubst Diα (laurentNum A Ei i d)).eval α
          / (lDenomα Ei Diα i d).eval α := by
  rw [iterate_ratFuncKDeriv_hFracα A Ei Diα i hi hEi0 hDiα0 d,
    eval_smul_lFracα _ i d hEi hDiα, mul_div_assoc]

/-- A regular root setup for the Laurent coefficient engine at multiplicity `i`. -/
structure IsLaurentRegularRoot (D Di Diα : K[X]) (α : K) (i : ℕ) : Prop where
  /-- `Di` is monic. -/
  monic : Di.Monic
  /-- `α` is a root of `Di`. -/
  root : Di.eval α = 0
  /-- `Di` factors as `(X - C α) * Diα`. -/
  factor : Di = (Polynomial.X - Polynomial.C α) * Diα
  /-- The complementary factor `Eᵢ` is coprime to `Di`. -/
  coprime_laurentE : IsCoprime (laurentE D Di i) Di
  /-- The derivative `Di'` is coprime to `Di`. -/
  coprime_derivative : IsCoprime (derivative Di) Di
  /-- The complementary factor `Eᵢ` does not vanish at `α`. -/
  laurentE_eval_ne : (laurentE D Di i).eval α ≠ 0
  /-- The linear cofactor `Diα` does not vanish at `α`. -/
  cofactor_eval_ne : Diα.eval α ≠ 0

/-- `Hᵢⱼ(α)` is the order-`(i−j)` Taylor coefficient of `hᵢ,α = (A/D)(x−α)ⁱ`:
`(laurentH A D Di i j).eval α = ((i−j)!)⁻¹ · RatFunc.eval id α ((ratFuncKDeriv^[i−j]) (hFracα A Eᵢ Diα i))`,
for `Dᵢ = (x−α)·Dᵢ,α` monic, `j ≤ i`, `Eᵢ(α), Dᵢ,α(α) ≠ 0`. -/
theorem eval_laurentH_eq_taylor_coeff [CharZero K] {A D Di Diα : K[X]} {α : K} (i j : ℕ)
    (hi : 0 < i) (hji : j ≤ i) (hroot : IsLaurentRegularRoot D Di Diα α i) :
    (laurentH A D Di i j).eval α
      = (((i - j).factorial : K))⁻¹
          * RatFunc.eval (RingHom.id K) α
              ((ratFuncKDeriv^[i - j]) (hFracα A (laurentE D Di i) Diα i)) := by
  set Ei := laurentE D Di i with hEidef
  have hEi0 : Ei ≠ 0 := fun h => hroot.laurentE_eval_ne (by rw [← hEidef, h, Polynomial.eval_zero])
  have hDiα0 : Diα ≠ 0 := fun h => hroot.cofactor_eval_ne (by rw [h, Polynomial.eval_zero])
  rw [eval_ratFuncKDeriv_iterate_hFracα_at_root i hi hEi0 hDiα0
    hroot.laurentE_eval_ne hroot.cofactor_eval_ne (i - j)]
  rw [eval_laurentH_eq_diffSubst_laurentNum i j hroot.monic hroot.root hroot.factor
    hroot.coprime_laurentE hroot.coprime_derivative, ← hEidef]
  rw [eval_derivative_of_X_sub_C_mul hroot.factor]
  unfold lDenomα
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_pow]
  have hidx : i + (i - j) = 2 * i - j := by omega
  rw [hidx]
  set N := (diffSubst Diα (laurentNum A Ei i (i - j))).eval α with hN
  set e := Ei.eval α with he
  set g := Diα.eval α with hg
  have hfact : ((i - j).factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (i - j)
  rw [one_div, one_div, inv_pow, inv_pow]
  field_simp

end DeepWiki.SymbolicIntegration
