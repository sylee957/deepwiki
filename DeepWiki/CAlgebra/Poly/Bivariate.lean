import Mathlib.RingTheory.Polynomial.Resultant.Basic
import DeepWiki.CAlgebra.Poly.Operations

/-! # The bivariate polynomial bridge

`toPolynomial₂` reads a dense bivariate polynomial (`x` outermost, coefficients an inner
`DensePoly`) as Mathlib's `(R[X])[X]`: the outer `toPolynomial` followed by mapping every
coefficient through the ring equivalence. The bundled `toPolynomial₂Hom` makes every
ring-operation transport a `map_*` fact; satellites keep the coefficient/constant/degree
readings and the boundary size measure. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [CommRing R] [DecidableEq R]

/-- The bivariate bridge: read `DensePoly (DensePoly R)` as `Polynomial (Polynomial R)`. -/
noncomputable def toPolynomial₂ (p : DensePoly (DensePoly R)) : Polynomial (Polynomial R) :=
  (toPolynomial p).map (equiv (R := R)).toRingHom

/-- The bivariate bridge, bundled: every ring-operation transport is a `map_*` fact. -/
noncomputable def toPolynomial₂Hom : DensePoly (DensePoly R) →+* Polynomial (Polynomial R) :=
  (Polynomial.mapRingHom (equiv (R := R)).toRingHom).comp
    ((equiv (R := DensePoly R)) : DensePoly (DensePoly R) →+* Polynomial (DensePoly R))

@[simp] theorem toPolynomial₂Hom_apply (p : DensePoly (DensePoly R)) :
    toPolynomial₂Hom p = toPolynomial₂ p := rfl

/-- Coefficient reading: the `i`-th coefficient is the bridged inner polynomial. -/
@[simp] theorem toPolynomial₂_coeff (p : DensePoly (DensePoly R)) (i : ℕ) :
    (toPolynomial₂ p).coeff i = toPolynomial (p.coeff i) := by
  rw [toPolynomial₂, Polynomial.coeff_map, coeff_toPolynomial]
  rfl

/-- The bivariate bridge is injective. -/
theorem toPolynomial₂_injective : Function.Injective (toPolynomial₂ (R := R)) :=
  fun _ _ h => toPolynomial_injective
    (Polynomial.map_injective _ (RingEquiv.injective _) h)

@[simp] theorem toPolynomial₂_zero : toPolynomial₂ (0 : DensePoly (DensePoly R)) = 0 :=
  map_zero toPolynomial₂Hom

@[simp] theorem toPolynomial₂_one : toPolynomial₂ (1 : DensePoly (DensePoly R)) = 1 :=
  map_one toPolynomial₂Hom

@[simp] theorem toPolynomial₂_add (p q : DensePoly (DensePoly R)) :
    toPolynomial₂ (p + q) = toPolynomial₂ p + toPolynomial₂ q :=
  map_add toPolynomial₂Hom p q

@[simp] theorem toPolynomial₂_sub (p q : DensePoly (DensePoly R)) :
    toPolynomial₂ (p - q) = toPolynomial₂ p - toPolynomial₂ q :=
  map_sub toPolynomial₂Hom p q

@[simp] theorem toPolynomial₂_mul (p q : DensePoly (DensePoly R)) :
    toPolynomial₂ (p * q) = toPolynomial₂ p * toPolynomial₂ q :=
  map_mul toPolynomial₂Hom p q

/-- The bridge sends inner-polynomial constants to `Polynomial.C` of the bridged inner
polynomial. -/
@[simp] theorem toPolynomial₂_C (c : DensePoly R) :
    toPolynomial₂ (C c : DensePoly (DensePoly R)) = Polynomial.C (toPolynomial c) := by
  rw [toPolynomial₂, toPolynomial_C, Polynomial.map_C]
  rfl

/-- The bridge preserves the (outer) degree. -/
theorem toPolynomial₂_natDegree (p : DensePoly (DensePoly R)) :
    (toPolynomial₂ p).natDegree = (toPolynomial p).natDegree :=
  Polynomial.natDegree_map_eq_of_injective (RingEquiv.injective _) _

/-- The boundary measure: the bridged outer degree is the size minus one. -/
theorem natDegree₂_eq_size_sub_one (p : DensePoly (DensePoly R)) :
    (toPolynomial₂ p).natDegree = p.size - 1 := by
  rw [toPolynomial₂_natDegree, natDegree_toPolynomial_eq_size_sub_one]

/-- The bridge transports outer resultants: reading a resultant over `DensePoly R` through
`toPolynomial` computes the resultant of the bridged bivariate polynomials. -/
theorem toPolynomial_resultant₂ (p q : DensePoly (DensePoly R)) (m n : ℕ) :
    toPolynomial (Polynomial.resultant (toPolynomial p) (toPolynomial q) m n)
      = Polynomial.resultant (toPolynomial₂ p) (toPolynomial₂ q) m n := by
  rw [toPolynomial₂, toPolynomial₂, Polynomial.resultant_map_map]
  rfl

/-- The bridge reflects zero. -/
theorem toPolynomial₂_ne_zero {p : DensePoly (DensePoly R)} (hp : p ≠ 0) :
    toPolynomial₂ p ≠ 0 :=
  fun h => hp (toPolynomial₂_injective (by rw [h, toPolynomial₂_zero]))

/-- List members are bounded by the max fold. -/
private theorem le_foldr_max (l : List ℕ) : ∀ x ∈ l, x ≤ l.foldr max 0 := by
  induction l with
  | nil => intro x hx; exact absurd hx List.not_mem_nil
  | cons a t ih =>
      intro x hx
      rw [List.foldr_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_max_left _ _
      · exact le_trans (ih x hx) (le_max_right _ _)

/-- Transpose a bivariate polynomial between its outer-`x` and outer-`z` representations. -/
def zSwap (S : DensePoly (DensePoly R)) : DensePoly (DensePoly R) :=
  DensePoly.ofList ((List.range ((S.coeffs.map DensePoly.size).foldr max 0)).map
    fun j => DensePoly.ofList (S.coeffs.map (fun c => c.coeff j)))

/-- Coefficient characterization of the bivariate transpose: `zSwap` swaps the two
coefficient indices. -/
theorem coeff_coeff_zSwap (S : DensePoly (DensePoly R)) (i j : ℕ) :
    ((zSwap S).coeff i).coeff j = (S.coeff j).coeff i := by
  set B := (S.coeffs.map DensePoly.size).foldr max 0 with hB
  rw [zSwap, coeff_ofList, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hi : i < (List.range B).length
  · rw [List.getElem?_eq_getElem hi, List.getElem_range, Option.map_some, Option.getD_some]
    rw [coeff_ofList, List.getD_eq_getElem?_getD, List.getElem?_map]
    by_cases hj : j < S.coeffs.length
    · rw [List.getElem?_eq_getElem hj]
      show S.coeffs[j].coeff i = _
      congr 1
      rw [DensePoly.coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
        Option.getD_some]
    · rw [List.getElem?_eq_none (by omega)]
      show (0 : R) = _
      rw [DensePoly.coeff_eq_zero_of_size_le S (by show S.coeffs.length ≤ j; omega)]
      rfl
  · rw [List.length_range] at hi
    rw [List.getElem?_eq_none (by rw [List.length_range, ← hB]; omega)]
    show (0 : DensePoly R).coeff j = _
    by_cases hj : j < S.coeffs.length
    · have hsz : (S.coeff j).size ≤ i := by
        have hmem : (S.coeff j).size ∈ S.coeffs.map DensePoly.size := by
          rw [List.mem_map]
          refine ⟨S.coeffs[j], List.getElem_mem hj, ?_⟩
          congr 1
          rw [DensePoly.coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
            Option.getD_some]
        have := le_foldr_max _ _ hmem
        omega
      rw [show (0 : DensePoly R).coeff j = 0 from rfl,
        DensePoly.coeff_eq_zero_of_size_le (S.coeff j) hsz]
    · rw [DensePoly.coeff_eq_zero_of_size_le S (by show S.coeffs.length ≤ j; omega),
        DensePoly.coeff_zero, DensePoly.coeff_zero]

end DensePoly

variable {R : Type u} [CommRing R] [DecidableEq R]

/-- Evaluate the `z`-coefficients of a bivariate polynomial: `S(z, x) ↦ S(α, x)`. -/
def zEval (α : R) (S : DensePoly (DensePoly R)) : DensePoly R :=
  DensePoly.ofList (S.coeffs.map (evalAt α))

/-- Coefficient reading of the coefficient evaluation. -/
@[simp] theorem coeff_zEval (α : R) (S : DensePoly (DensePoly R)) (j : ℕ) :
    (zEval α S).coeff j = evalAt α (S.coeff j) := by
  rw [zEval, DensePoly.coeff_ofList, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hj : j < S.coeffs.length
  · rw [List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]
    congr 1
    rw [DensePoly.coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      Option.getD_some]
  · rw [List.getElem?_eq_none (by omega)]
    show (0 : R) = _
    rw [DensePoly.coeff_eq_zero_of_size_le S (by show S.coeffs.length ≤ j; omega),
      evalAt_eq, toPolynomial_zero, Polynomial.eval_zero]

/-- `zEval` computes the bridged coefficient evaluation. -/
theorem toPolynomial_zEval (α : R) (S : DensePoly (DensePoly R)) :
    toPolynomial (zEval α S) = (DensePoly.toPolynomial₂ S).map (Polynomial.evalRingHom α) := by
  refine Polynomial.ext fun n => ?_
  rw [coeff_toPolynomial, coeff_zEval, evalAt_eq, Polynomial.coeff_map,
    DensePoly.toPolynomial₂_coeff]
  rfl

/-- Evaluating the outer variable of the transpose at a constant is the coefficient
evaluation: `(zSwap S)(C α) = S(α, ·)`. -/
theorem toPolynomial₂_zSwap_eval (S : DensePoly (DensePoly R)) (α : R) :
    (DensePoly.toPolynomial₂ (DensePoly.zSwap S)).eval (Polynomial.C α)
      = toPolynomial (zEval α S) := by
  refine Polynomial.ext fun j => ?_
  have hple : (toPolynomial (S.coeff j)).natDegree
      ≤ (DensePoly.toPolynomial₂ (DensePoly.zSwap S)).natDegree := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
    have h0 : (DensePoly.toPolynomial₂ (DensePoly.zSwap S)).coeff m = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt hm
    rw [DensePoly.toPolynomial₂_coeff] at h0
    rw [coeff_toPolynomial, ← DensePoly.coeff_coeff_zSwap,
      show (DensePoly.zSwap S).coeff m = 0 from
        toPolynomial_injective (h0.trans toPolynomial_zero.symm),
      DensePoly.coeff_zero]
  rw [coeff_toPolynomial, coeff_zEval, evalAt_eq,
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hple),
    Polynomial.eval_eq_sum_range, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Polynomial.C_pow, Polynomial.coeff_mul_C, DensePoly.toPolynomial₂_coeff,
    coeff_toPolynomial, DensePoly.coeff_coeff_zSwap, coeff_toPolynomial]

end DeepWiki.CAlgebra
