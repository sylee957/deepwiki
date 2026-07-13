import DeepWiki.CAlgebra.Poly.Operations
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! # Mathlib bridge: `DensePoly R ≃+* Polynomial R`

`toPolynomial`/`ofPolynomial` convert between the normalized dense representation and Mathlib's
`Polynomial`, agreeing coefficientwise. Because the representation is canonical (`ext_coeff`), the
two conversions are mutually inverse, so the bridge bundles into a ring *isomorphism* `equiv`. This
is the linchpin of the rewrite: completeness (reflection of divisibility, gcd) follows by
transporting properties backward along `equiv`, rather than by hand-proving each reflection. -/

open Polynomial

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [CommRing R] [DecidableEq R]

noncomputable section

/-- Denotation into Mathlib: sum the stored coefficients as monomials. -/
def toPolynomial (p : DensePoly R) : Polynomial R :=
  ∑ i ∈ Finset.range p.size, Polynomial.monomial i (p.coeff i)

/-- Rebuild a dense polynomial from a Mathlib polynomial by reading off its coefficients. -/
def ofPolynomial (q : Polynomial R) : DensePoly R :=
  DensePoly.ofList ((List.range (q.natDegree + 1)).map q.coeff)

/-- `toPolynomial` agrees with the dense coefficient function at every index. -/
@[simp] theorem coeff_toPolynomial (p : DensePoly R) (n : Nat) :
    (toPolynomial p).coeff n = p.coeff n := by
  rw [toPolynomial, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range p.size) n p.coeff]
  by_cases h : n < p.size
  · rw [if_pos (Finset.mem_range.mpr h)]
  · rw [if_neg (by simpa [Finset.mem_range] using h)]
    exact (DensePoly.coeff_eq_zero_of_size_le p (Nat.not_lt.mp h)).symm

/-- `ofPolynomial` agrees with the Mathlib coefficient function at every index. -/
@[simp] theorem coeff_ofPolynomial (q : Polynomial R) (n : Nat) :
    (ofPolynomial q).coeff n = q.coeff n := by
  rw [ofPolynomial, DensePoly.coeff_ofList_map_range]
  by_cases h : n < q.natDegree + 1
  · rw [if_pos h]
  · rw [if_neg h]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- Round trip `ofPolynomial ∘ toPolynomial = id` (left inverse). -/
@[simp] theorem ofPolynomial_toPolynomial (p : DensePoly R) :
    ofPolynomial (toPolynomial p) = p := by
  ext i; rw [coeff_ofPolynomial, coeff_toPolynomial]

/-- Round trip `toPolynomial ∘ ofPolynomial = id` (right inverse). -/
@[simp] theorem toPolynomial_ofPolynomial (q : Polynomial R) :
    toPolynomial (ofPolynomial q) = q := by
  ext n; rw [coeff_toPolynomial, coeff_ofPolynomial]

/-- `toPolynomial` is injective (it has a left inverse). -/
theorem toPolynomial_injective : Function.Injective (toPolynomial (R := R)) :=
  Function.LeftInverse.injective ofPolynomial_toPolynomial

/-! ### Homomorphism squares -/

@[simp] theorem toPolynomial_zero : toPolynomial (0 : DensePoly R) = 0 := by
  ext n; simp

@[simp] theorem toPolynomial_one : toPolynomial (1 : DensePoly R) = 1 := by
  ext n; rw [coeff_toPolynomial, DensePoly.coeff_one, Polynomial.coeff_one]

@[simp] theorem toPolynomial_C (c : R) : toPolynomial (DensePoly.C c) = Polynomial.C c := by
  ext n; rw [coeff_toPolynomial, DensePoly.coeff_C, Polynomial.coeff_C]

@[simp] theorem toPolynomial_monomial (n : ℕ) (c : R) :
    toPolynomial (DensePoly.monomial n c) = Polynomial.monomial n c := by
  ext k
  rw [coeff_toPolynomial, DensePoly.coeff_monomial, Polynomial.coeff_monomial]
  by_cases h : k = n
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]

/-- `toPolynomial` transports the executable degree (`degree?`, defaulting the zero polynomial to `0`)
to Mathlib's `natDegree`. -/
theorem natDegree_toPolynomial (p : DensePoly R) :
    (toPolynomial p).natDegree = p.degree?.getD 0 := by
  by_cases hsize : p.size = 0
  · have hp0 : toPolynomial p = 0 := by
      ext n
      rw [coeff_toPolynomial, Polynomial.coeff_zero, DensePoly.coeff_eq_zero_of_size_le p (by omega)]
    rw [hp0, Polynomial.natDegree_zero, DensePoly.degree?]
    simp [hsize]
  · have hpos : 0 < p.size := Nat.pos_of_ne_zero hsize
    rw [DensePoly.degree?, if_neg hsize, Option.getD_some]
    apply le_antisymm
    · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro N hN
      rw [coeff_toPolynomial]
      exact DensePoly.coeff_eq_zero_of_size_le p (by omega)
    · apply Polynomial.le_natDegree_of_ne_zero
      rw [coeff_toPolynomial]
      exact DensePoly.coeff_last_ne_zero_of_pos_size p hpos

@[simp] theorem toPolynomial_add (p q : DensePoly R) :
    toPolynomial (p + q) = toPolynomial p + toPolynomial q := by
  ext n; simp [Polynomial.coeff_add]

@[simp] theorem toPolynomial_neg (p : DensePoly R) :
    toPolynomial (-p) = - toPolynomial p := by
  ext n; simp [Polynomial.coeff_neg]

@[simp] theorem toPolynomial_mul (p q : DensePoly R) :
    toPolynomial (p * q) = toPolynomial p * toPolynomial q := by
  ext n
  rw [coeff_toPolynomial, DensePoly.coeff_mul, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [coeff_toPolynomial, coeff_toPolynomial]

/-- The normalized dense representation is ring-equivalent to Mathlib polynomials. This is the
canonical-representation payoff: a bijection preserving `+` and `*`, from which reflection
(completeness) transports backward. -/
def equiv : DensePoly R ≃+* Polynomial R where
  toFun := toPolynomial
  invFun := ofPolynomial
  left_inv := ofPolynomial_toPolynomial
  right_inv := toPolynomial_ofPolynomial
  map_mul' := toPolynomial_mul
  map_add' := toPolynomial_add

@[simp] theorem equiv_apply (p : DensePoly R) : equiv p = toPolynomial p := rfl

@[simp] theorem equiv_symm_apply (q : Polynomial R) : equiv.symm q = ofPolynomial q := rfl

/-! ### Validation: the bridge is a bona fide ring isomorphism, so properties transport both ways. -/

/-- `equiv` preserves multiplication (soundness of the product denotation). -/
example (p q : DensePoly R) : equiv (p * q) = equiv p * equiv q := map_mul equiv p q

/-- `equiv` preserves addition. -/
example (p q : DensePoly R) : equiv (p + q) = equiv p + equiv q := map_add equiv p q

/-- `equiv` is a bijection: every Mathlib polynomial is the image of a unique dense one — the
reverse direction that will carry completeness (reflection) in later phases. -/
example : Function.Bijective (equiv (R := R)) := equiv.bijective

/-- The reverse map recovers the polynomial exactly. -/
example (q : Polynomial R) : toPolynomial (ofPolynomial q) = q := by simp

end

end DeepWiki.CAlgebra
