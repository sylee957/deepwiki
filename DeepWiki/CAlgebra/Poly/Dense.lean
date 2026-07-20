import Mathlib.Data.List.Basic
import Mathlib.Algebra.GroupWithZero.Defs

/-! # Normalized dense polynomials (Hex-style canonical representation)

`DensePoly R` stores coefficients in a `List R` (index `i` = coefficient of `xⁱ`, low to high)
together with a proof of `Normalized`: the list is empty or its last entry is nonzero. Bundling the
no-trailing-zeros invariant into the type makes structural equality coincide with semantic equality,
so the coefficient function determines the polynomial (`ext_coeff`) and the bridge to Mathlib's
`Polynomial` is a ring *isomorphism* rather than a one-directional homomorphism. -/

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [Zero R] [DecidableEq R]

/-- A coefficient list is normalized when it is empty or its last entry is nonzero. -/
def Normalized (coeffs : List R) : Prop :=
  coeffs = [] ∨ coeffs.getLast? ≠ some (0 : R)

/-- Remove trailing zeros from a coefficient list without disturbing the remaining order. -/
def trimTrailingZeros : List R → List R
  | [] => []
  | a :: as =>
      let trimmed := trimTrailingZeros as
      if trimmed = [] ∧ a = (0 : R) then [] else a :: trimmed

/-- Trimming preserves the value at every index (out-of-range indices default to `0` on both sides). -/
theorem trimTrailingZeros_getD (coeffs : List R) (n : Nat) :
    (trimTrailingZeros coeffs).getD n (0 : R) = coeffs.getD n (0 : R) := by
  induction coeffs generalizing n with
  | nil => simp [trimTrailingZeros]
  | cons a as ih =>
      cases n with
      | zero =>
          by_cases htrim : trimTrailingZeros as = [] ∧ a = (0 : R)
          · simp [trimTrailingZeros, htrim]
          · simp [trimTrailingZeros, htrim]
      | succ n =>
          by_cases htrim : trimTrailingZeros as = [] ∧ a = (0 : R)
          · have hstep : trimTrailingZeros (a :: as) = [] := by
              simp only [trimTrailingZeros]; rw [if_pos htrim]
            have hn := ih n
            rw [htrim.1] at hn
            rw [hstep]
            simpa [List.getD_cons_succ] using hn
          · simpa [trimTrailingZeros, htrim] using ih n

/-- Trimming trailing zeros never increases the coefficient-list length. -/
theorem trimTrailingZeros_length_le (coeffs : List R) :
    (trimTrailingZeros coeffs).length ≤ coeffs.length := by
  induction coeffs with
  | nil => simp [trimTrailingZeros]
  | cons a as ih =>
      by_cases htrim : trimTrailingZeros as = [] ∧ a = (0 : R)
      · simp [trimTrailingZeros, htrim]
      · simp only [trimTrailingZeros, htrim, if_false, List.length_cons]; omega

/-- Trimming leaves the list empty or with a nonzero last entry: the `Normalized` invariant. -/
theorem trimTrailingZeros_normalized (coeffs : List R) :
    Normalized (trimTrailingZeros coeffs) := by
  induction coeffs with
  | nil => left; rfl
  | cons a as ih =>
      by_cases htrim : trimTrailingZeros as = [] ∧ a = (0 : R)
      · left; simp [trimTrailingZeros, htrim]
      · right
        have hstep : trimTrailingZeros (a :: as) = a :: trimTrailingZeros as := by
          simp only [trimTrailingZeros]; rw [if_neg htrim]
        cases htail : trimTrailingZeros as with
        | nil =>
            intro hlast
            have ha_ne : a ≠ (0 : R) := fun ha => htrim ⟨htail, ha⟩
            rw [hstep, htail] at hlast
            simp only [List.getLast?_singleton, Option.some.injEq] at hlast
            exact ha_ne hlast
        | cons b bs =>
            intro hlast
            rw [hstep, htail, List.getLast?_cons_cons] at hlast
            rcases ih with has_empty | has_last
            · rw [htail] at has_empty; exact absurd has_empty (by simp)
            · rw [htail] at has_last; exact has_last hlast

/-- Normalized dense polynomial: coefficients low-to-high with no trailing zeros. -/
structure DensePoly (R : Type u) [Zero R] [DecidableEq R] where
  /-- The stored coefficients in ascending degree order. -/
  coeffs : List R
  /-- Proof that `coeffs` carries no trailing zeros. -/
  normalized : Normalized coeffs

namespace DensePoly

/-- Structural equality of dense polynomials is decidable (the proof field is irrelevant). -/
instance : DecidableEq (DensePoly R) := fun a b =>
  match decEq a.coeffs b.coeffs with
  | isTrue h => isTrue (by cases a; cases b; cases h; rfl)
  | isFalse h => isFalse (fun hab => h (congrArg DensePoly.coeffs hab))

/-- Build a dense polynomial from a raw coefficient list by normalizing away trailing zeros. -/
def ofList (coeffs : List R) : DensePoly R :=
  ⟨trimTrailingZeros coeffs, trimTrailingZeros_normalized coeffs⟩

/-- The zero polynomial. -/
def zero : DensePoly R := ⟨[], Or.inl rfl⟩

instance : Zero (DensePoly R) where
  zero := zero

/-- The constant polynomial with value `c` (collapses to zero when `c = 0`). -/
def C (c : R) : DensePoly R := ofList [c]

/-- The number of stored coefficients: `1 + degree` for a nonzero polynomial, `0` for zero. -/
def size (p : DensePoly R) : Nat := p.coeffs.length

/-- `true` exactly when the polynomial is zero. -/
def isZero (p : DensePoly R) : Bool := p.coeffs.isEmpty

/-- The coefficient of `xⁿ`, defaulting to `0` when `n` is out of range. -/
def coeff (p : DensePoly R) (n : Nat) : R := p.coeffs.getD n (0 : R)

@[simp] theorem coeff_mk (coeffs : List R) (h : Normalized coeffs) (n : Nat) :
    (DensePoly.mk coeffs h).coeff n = coeffs.getD n (0 : R) := rfl

/-- `coeff (ofList l) n = l.getD n 0`: normalization does not change the value at any index. -/
@[simp] theorem coeff_ofList (coeffs : List R) (n : Nat) :
    (ofList coeffs).coeff n = coeffs.getD n (0 : R) := by
  simp only [coeff, ofList, trimTrailingZeros_getD]

/-- The coefficients of the zero polynomial are all zero. -/
@[simp] theorem coeff_zero (n : Nat) : (0 : DensePoly R).coeff n = (0 : R) := by
  show ([] : List R).getD n (0 : R) = 0
  simp

/-- The constant polynomial has coefficient `c` at degree `0` and zero elsewhere. -/
@[simp] theorem coeff_C (c : R) (n : Nat) :
    (C c).coeff n = if n = 0 then c else (0 : R) := by
  rw [C, coeff_ofList]
  cases n with
  | zero => simp
  | succ n => simp

/-- Coefficients past the stored support are zero. -/
theorem coeff_eq_zero_of_size_le (p : DensePoly R) {i : Nat} (h : p.size ≤ i) :
    p.coeff i = (0 : R) := by
  simp only [coeff, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by simpa [size] using h)]; rfl

/-- The last stored coefficient of a nonzero normalized polynomial is nonzero. -/
theorem coeff_last_ne_zero_of_pos_size (p : DensePoly R) (hpos : 0 < p.size) :
    p.coeff (p.size - 1) ≠ (0 : R) := by
  have hne : p.coeffs ≠ [] := fun h => by simp [size, h] at hpos
  have hlen : p.coeffs.length - 1 < p.coeffs.length := by
    have : 0 < p.coeffs.length := by simpa [size] using hpos
    omega
  have hget : p.coeff (p.size - 1) = p.coeffs.getLast hne := by
    simp only [coeff, size, List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hlen, Option.getD_some]
  rw [hget]
  intro hc
  rcases p.normalized with hzero | hlast
  · exact hne hzero
  · exact hlast (by rw [List.getLast?_eq_some_getLast hne, hc])

/-- The leading (top-degree) coefficient; `0` for the zero polynomial. -/
def leadingCoeff (p : DensePoly R) : R := p.coeff (p.size - 1)

/-- A nonzero polynomial has nonzero leading coefficient. -/
theorem leadingCoeff_ne_zero {p : DensePoly R} (hp : p.size ≠ 0) : leadingCoeff p ≠ 0 :=
  coeff_last_ne_zero_of_pos_size p (Nat.pos_of_ne_zero hp)

/-- The zero polynomial has leading coefficient `0`. -/
@[simp] theorem leadingCoeff_zero : (0 : DensePoly R).leadingCoeff = 0 := by
  simp [leadingCoeff, coeff]
  rfl

/-- If every coefficient from index `n` upward vanishes, the size is at most `n`. -/
theorem size_le_of_coeff_zero {p : DensePoly R} {n : Nat} (h : ∀ j, n ≤ j → p.coeff j = 0) :
    p.size ≤ n := by
  by_contra hlt
  have hpos : 0 < p.size := by omega
  exact coeff_last_ne_zero_of_pos_size p hpos (h (p.size - 1) (by omega))

/-- Coefficientwise equality of normalized polynomials forces equal stored sizes. -/
theorem size_eq_of_coeff_eq {p q : DensePoly R} (hcoeff : ∀ i, p.coeff i = q.coeff i) :
    p.size = q.size := by
  rcases Nat.lt_trichotomy p.size q.size with hpq | hpq | hqp
  · have hp_zero := coeff_eq_zero_of_size_le p (i := q.size - 1) (by omega)
    have hq_ne := coeff_last_ne_zero_of_pos_size q (by omega)
    exact absurd ((hcoeff (q.size - 1)).symm.trans hp_zero) hq_ne
  · exact hpq
  · have hq_zero := coeff_eq_zero_of_size_le q (i := p.size - 1) (by omega)
    have hp_ne := coeff_last_ne_zero_of_pos_size p (by omega)
    exact absurd ((hcoeff (p.size - 1)).trans hq_zero) hp_ne

/-- Extensionality: normalized dense polynomials are determined by their coefficient functions.
This is the keystone property the normalization invariant buys. -/
@[ext] theorem ext_coeff {p q : DensePoly R} (hcoeff : ∀ i, p.coeff i = q.coeff i) : p = q := by
  have hsize : p.size = q.size := size_eq_of_coeff_eq hcoeff
  cases p with
  | mk pc _ =>
    cases q with
    | mk qc _ =>
      congr 1
      apply List.ext_getElem (by simpa [size] using hsize)
      intro i h₁ h₂
      have := hcoeff i
      simpa only [coeff_mk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁,
        List.getElem?_eq_getElem h₂, Option.getD_some] using this

/-- A size-zero polynomial is the zero polynomial. -/
theorem eq_zero_of_size_zero {p : DensePoly R} (h : p.size = 0) : p = 0 := by
  ext i; rw [coeff_zero]; exact coeff_eq_zero_of_size_le p (by omega)

/-- A nonzero constant has size `1`. -/
theorem size_C {c : R} (hc : c ≠ 0) : (C c).size = 1 := by
  simp [C, ofList, size, trimTrailingZeros, hc]

/-- A polynomial of size `1` is the constant on its `0`-th coefficient. -/
theorem eq_C_of_size_eq_one {p : DensePoly R} (h : p.size = 1) : p = C (p.coeff 0) := by
  ext i
  rw [coeff_C]
  cases i with
  | zero => rw [if_pos rfl]
  | succ n =>
      rw [if_neg (Nat.succ_ne_zero n)]
      exact coeff_eq_zero_of_size_le p (by omega)

/-- The largest exponent with a stored coefficient, or `none` for the zero polynomial. -/
def degree? (p : DensePoly R) : Option Nat :=
  if p.size = 0 then none else some (p.size - 1)

@[simp] theorem size_zero : (0 : DensePoly R).size = 0 := rfl

@[simp] theorem degree?_zero : (0 : DensePoly R).degree? = none := by
  simp [degree?]

/-- `isZero` is `true` iff the polynomial equals `0`. -/
theorem isZero_iff (p : DensePoly R) : p.isZero = true ↔ p = 0 := by
  constructor
  · intro h
    have : p.coeffs = [] := List.isEmpty_iff.mp h
    ext i; rw [coeff_zero]; simp [coeff, this]
  · intro h; subst h; rfl

end DensePoly

end DeepWiki.CAlgebra
