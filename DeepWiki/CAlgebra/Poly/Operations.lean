import DeepWiki.CAlgebra.Poly.Dense
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! # `DensePoly R` as a computable commutative ring identified with `Polynomial R`

Arithmetic (`one`/`monomial`/`add`/`neg`/`sub`/`mul`) with its coefficient laws, the Mathlib
denotation `toPolynomial`/`ofPolynomial` and the ring isomorphism `equiv : DensePoly R ≃+* Polynomial
R`, and the hand-built **computable** `CommRing (DensePoly R)` (arithmetic = the computable ops here,
axioms by transport, `nsmul`/`npow`/casts at Lean's computable defaults — nothing noncomputable is
bundled). Everything about `DensePoly` as a polynomial lives here. -/

open Polynomial

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [CommRing R] [DecidableEq R]

namespace DensePoly

/-! ### Arithmetic -/

/-- Reading a coefficient of `ofList ((range m).map f)`: it is `f n` inside range, `0` past it. -/
theorem coeff_ofList_map_range (m : Nat) (f : Nat → R) (n : Nat) :
    (ofList ((List.range m).map f)).coeff n = if n < m then f n else 0 := by
  rw [coeff_ofList, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : n < m
  · rw [List.getElem?_range h]; simp [h]
  · rw [List.getElem?_eq_none (by rw [List.length_range]; exact Nat.not_lt.mp h)]; simp [h]

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

/-- Dense polynomial subtraction `a - b := a + (-b)`. -/
instance : Sub (DensePoly R) where sub a b := a + (-b)

theorem sub_def (p q : DensePoly R) : p - q = p + (-q) := rfl

@[simp] theorem coeff_sub (p q : DensePoly R) (n : Nat) :
    (p - q).coeff n = p.coeff n - q.coeff n := by
  rw [sub_def, coeff_add, coeff_neg, sub_eq_add_neg]

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

/-- Coefficient of `monomial k c * q`: a `k`-shifted, `c`-scaled read of `q`. -/
theorem coeff_monomial_mul (k : Nat) (c : R) (q : DensePoly R) (n : Nat) :
    (monomial k c * q).coeff n = if k ≤ n then c * q.coeff (n - k) else 0 := by
  rw [coeff_mul]
  simp only [coeff_monomial, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' (Finset.range (n + 1)) k (fun i => c * q.coeff (n - i))]
  simp [Finset.mem_range]

/-- Coefficient of `C c * p`: a `c`-scaled read of `p`. -/
theorem coeff_C_mul (c : R) (p : DensePoly R) (n : Nat) :
    (C c * p).coeff n = c * p.coeff n := by
  rw [coeff_mul]
  simp only [coeff_C, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' (Finset.range (n + 1)) 0 (fun i => c * p.coeff (n - i))]
  simp

/-- `C` is multiplicative: `C (a * b) = C a * C b`. -/
theorem C_mul (a b : R) : (C (a * b) : DensePoly R) = C a * C b := by
  ext n; rw [coeff_C, coeff_C_mul, coeff_C, mul_ite, mul_zero]

/-- Constant multiplication never increases the stored size. -/
theorem size_C_mul_le (c : R) (p : DensePoly R) : (C c * p).size ≤ p.size :=
  size_le_of_coeff_zero fun j hj => by
    rw [coeff_C_mul, coeff_eq_zero_of_size_le p hj, mul_zero]

end DensePoly

/-! ### Mathlib denotation and the ring isomorphism `equiv` -/

/-- Denotation into Mathlib: sum the stored coefficients as monomials. -/
noncomputable def toPolynomial (p : DensePoly R) : Polynomial R :=
  ∑ i ∈ Finset.range p.size, Polynomial.monomial i (p.coeff i)

/-- Rebuild a dense polynomial from a Mathlib polynomial by reading off its coefficients. -/
noncomputable def ofPolynomial (q : Polynomial R) : DensePoly R :=
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

/-- `toPolynomial` transports the executable degree to Mathlib's `natDegree`. -/
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

/-- `toPolynomial` intertwines subtraction. -/
@[simp] theorem toPolynomial_sub (p q : DensePoly R) :
    toPolynomial (p - q) = toPolynomial p - toPolynomial q := by
  ext n; simp [Polynomial.coeff_sub, DensePoly.coeff_sub]

/-- The normalized dense representation is ring-equivalent to Mathlib polynomials. -/
noncomputable def equiv : DensePoly R ≃+* Polynomial R where
  toFun := toPolynomial
  invFun := ofPolynomial
  left_inv := ofPolynomial_toPolynomial
  right_inv := toPolynomial_ofPolynomial
  map_mul' := toPolynomial_mul
  map_add' := toPolynomial_add

@[simp] theorem equiv_apply (p : DensePoly R) : equiv p = toPolynomial p := rfl

@[simp] theorem equiv_symm_apply (q : Polynomial R) : equiv.symm q = ofPolynomial q := rfl

/-! ### The computable commutative ring, and divisibility reflection -/

/-- The commutative ring structure on dense polynomials — hand-built and computable. Arithmetic
fields are the computable ops above; axioms are proved by transport through `toPolynomial`;
`nsmul`/`zsmul` = `nsmulRec`/`zsmulRec`, `npow`/`natCast`/`intCast` at Lean's computable defaults —
deliberately NOT `Function.Injective.commRing` (noncomputable). -/
instance : CommRing (DensePoly R) where
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  sub := (· - ·)
  zero := 0
  one := 1
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc a b c := toPolynomial_injective (by simp only [toPolynomial_add]; ring)
  zero_add a := toPolynomial_injective (by simp)
  add_zero a := toPolynomial_injective (by simp)
  add_comm a b := toPolynomial_injective (by simp only [toPolynomial_add]; ring)
  mul_assoc a b c := toPolynomial_injective (by simp only [toPolynomial_mul]; ring)
  one_mul a := toPolynomial_injective (by simp)
  mul_one a := toPolynomial_injective (by simp)
  left_distrib a b c := toPolynomial_injective (by simp only [toPolynomial_add, toPolynomial_mul]; ring)
  right_distrib a b c := toPolynomial_injective (by simp only [toPolynomial_add, toPolynomial_mul]; ring)
  mul_comm a b := toPolynomial_injective (by simp only [toPolynomial_mul]; ring)
  neg_add_cancel a :=
    toPolynomial_injective (by simp only [toPolynomial_add, toPolynomial_neg, toPolynomial_zero]; ring)
  zero_mul a := toPolynomial_injective (by simp)
  mul_zero a := toPolynomial_injective (by simp)
  sub_eq_add_neg a b := rfl

/-- Divisibility is preserved by `toPolynomial` (soundness direction). -/
theorem toPolynomial_dvd {p q : DensePoly R} (h : p ∣ q) : toPolynomial p ∣ toPolynomial q := by
  rcases h with ⟨r, rfl⟩; exact ⟨toPolynomial r, by rw [toPolynomial_mul]⟩

/-- Divisibility is reflected by `toPolynomial` (completeness direction, via reverse transport). -/
theorem dvd_of_toPolynomial_dvd {p q : DensePoly R}
    (h : toPolynomial p ∣ toPolynomial q) : p ∣ q := by
  rcases h with ⟨s, hs⟩
  refine ⟨ofPolynomial s, toPolynomial_injective ?_⟩
  rw [toPolynomial_mul, toPolynomial_ofPolynomial, hs]

/-- `toPolynomial` both preserves and reflects divisibility. -/
@[simp] theorem toPolynomial_dvd_iff {p q : DensePoly R} :
    toPolynomial p ∣ toPolynomial q ↔ p ∣ q :=
  ⟨dvd_of_toPolynomial_dvd, toPolynomial_dvd⟩

/-! ### Structure classes transported through the bridge -/

/-- `DensePoly R` is nontrivial when `R` is (transported through `equiv`). -/
instance [Nontrivial R] : Nontrivial (DensePoly R) :=
  (equiv (R := R)).toEquiv.nontrivial

/-- `DensePoly R` has no zero divisors when `R` is a domain (transported through `toPolynomial`). -/
instance [IsDomain R] : NoZeroDivisors (DensePoly R) where
  eq_zero_or_eq_zero_of_mul_eq_zero {p q} h := by
    have hpq : toPolynomial p * toPolynomial q = 0 := by
      rw [← toPolynomial_mul, h, toPolynomial_zero]
    rcases mul_eq_zero.mp hpq with hp | hq
    · exact Or.inl (toPolynomial_injective (by rw [hp, toPolynomial_zero]))
    · exact Or.inr (toPolynomial_injective (by rw [hq, toPolynomial_zero]))

/-- `DensePoly R` is an integral domain when `R` is. -/
instance [IsDomain R] : IsDomain (DensePoly R) :=
  NoZeroDivisors.to_isDomain _

end DeepWiki.CAlgebra
