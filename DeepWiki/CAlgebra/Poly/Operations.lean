import DeepWiki.CAlgebra.Poly.Dense
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Basic

/-! # Arithmetic on normalized dense polynomials

`one`, `monomial`, `add`, `neg`, `mul` on `DensePoly R` over a `CommRing R`, each defined through the
uniform `ofList ((List.range m).map f)` shape so the coefficient laws (`coeff_add`, `coeff_neg`,
`coeff_mul`, …) all reduce to one helper. These coefficient laws are the homomorphism squares the
Mathlib `RingEquiv` bridge transports. -/

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [CommRing R] [DecidableEq R]

namespace DensePoly

/-- Reading a coefficient of `ofList ((range m).map f)`: it is `f n` inside range, `0` past it. -/
theorem coeff_ofList_map_range (m : Nat) (f : Nat → R) (n : Nat) :
    (ofList ((List.range m).map f)).coeff n = if n < m then f n else 0 := by
  rw [coeff_ofList, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : n < m
  · rw [List.getElem?_range h]; simp [h]
  · rw [List.getElem?_eq_none (by rw [List.length_range]; exact Nat.not_lt.mp h)]; simp [h]

/-! ### One and monomial -/

/-- The constant polynomial `1`. -/
instance : One (DensePoly R) where one := C 1

theorem one_def : (1 : DensePoly R) = C 1 := rfl

@[simp] theorem coeff_one (n : Nat) : (1 : DensePoly R).coeff n = if n = 0 then 1 else 0 := by
  rw [one_def, coeff_C]

/-- The monomial `c · xⁿ` (collapses to `0` when `c = 0`). -/
def monomial (n : Nat) (c : R) : DensePoly R :=
  ofList ((List.range n).map (fun _ => (0 : R)) ++ [c])

@[simp] theorem coeff_monomial (n : Nat) (c : R) (i : Nat) :
    (monomial n c).coeff i = if i = n then c else 0 := by
  rw [monomial, coeff_ofList, List.getD_eq_getElem?_getD, List.getElem?_append,
      List.length_map, List.length_range]
  rcases lt_trichotomy i n with h | h | h
  · rw [if_pos h, List.getElem?_map, List.getElem?_range h]
    simp [Nat.ne_of_lt h]
  · subst h
    rw [if_neg (lt_irrefl _), Nat.sub_self]
    simp
  · rw [if_neg (Nat.not_lt.mpr (le_of_lt h))]
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (show i - n ≠ 0 by omega)
    rw [hk]
    simp [Nat.ne_of_gt h]

/-! ### Addition -/

/-- Dense polynomial addition (coefficientwise, then normalized). -/
def add (p q : DensePoly R) : DensePoly R :=
  ofList ((List.range (max p.size q.size)).map (fun n => p.coeff n + q.coeff n))

instance : Add (DensePoly R) where add := add

theorem add_def (p q : DensePoly R) :
    p + q = ofList ((List.range (max p.size q.size)).map (fun n => p.coeff n + q.coeff n)) := rfl

@[simp] theorem coeff_add (p q : DensePoly R) (n : Nat) :
    (p + q).coeff n = p.coeff n + q.coeff n := by
  rw [add_def, coeff_ofList_map_range]
  by_cases h : n < max p.size q.size
  · simp [h]
  · rw [if_neg h]
    have h' : max p.size q.size ≤ n := Nat.not_lt.mp h
    rw [coeff_eq_zero_of_size_le p (le_trans (le_max_left _ _) h'),
      coeff_eq_zero_of_size_le q (le_trans (le_max_right _ _) h'), add_zero]

/-! ### Negation -/

/-- Dense polynomial negation. -/
def neg (p : DensePoly R) : DensePoly R :=
  ofList ((List.range p.size).map (fun n => - p.coeff n))

instance : Neg (DensePoly R) where neg := neg

theorem neg_def (p : DensePoly R) :
    -p = ofList ((List.range p.size).map (fun n => - p.coeff n)) := rfl

@[simp] theorem coeff_neg (p : DensePoly R) (n : Nat) : (-p).coeff n = - p.coeff n := by
  rw [neg_def, coeff_ofList_map_range]
  by_cases h : n < p.size
  · simp [h]
  · rw [if_neg h]
    rw [coeff_eq_zero_of_size_le p (Nat.not_lt.mp h), neg_zero]

/-! ### Multiplication -/

/-- Dense polynomial multiplication via the Cauchy convolution, then normalized. -/
def mul (p q : DensePoly R) : DensePoly R :=
  ofList ((List.range (p.size + q.size)).map
    (fun n => ∑ i ∈ Finset.range (n + 1), p.coeff i * q.coeff (n - i)))

instance : Mul (DensePoly R) where mul := mul

theorem mul_def (p q : DensePoly R) :
    p * q = ofList ((List.range (p.size + q.size)).map
      (fun n => ∑ i ∈ Finset.range (n + 1), p.coeff i * q.coeff (n - i))) := rfl

@[simp] theorem coeff_mul (p q : DensePoly R) (n : Nat) :
    (p * q).coeff n = ∑ i ∈ Finset.range (n + 1), p.coeff i * q.coeff (n - i) := by
  rw [mul_def, coeff_ofList_map_range]
  by_cases h : n < p.size + q.size
  · simp [h]
  · rw [if_neg h]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hip : p.size ≤ i
    · rw [coeff_eq_zero_of_size_le p hip, zero_mul]
    · have hn : p.size + q.size ≤ n := Nat.not_lt.mp h
      have hi' : i < p.size := Nat.not_le.mp hip
      rw [coeff_eq_zero_of_size_le q (by omega), mul_zero]

end DensePoly

end DeepWiki.CAlgebra
