import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.Polynomial.Basic
import DeepWiki.Transfer.Denote

/-! # A generic computable field, and a polynomial engine over it

`CField α`: computable field operations (`zero`/`one`/`add`/`mul`/`neg`/`inv`, zero test) that
reduce, with meaning supplied by a companion `CFieldSpec` homomorphism `toK : α → K` into a Mathlib
`Field K`. Over any `CField`, a dense polynomial engine `CPolyG α := List α` with computable
arithmetic and a Horner bridge `toPolyG : CPolyG α → (CFieldSpec.K α)[X]`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### The `CField` typeclass (computable operations only)

`CField α`: the computable field operations plus zero test, bridge-free so instances stay
computable; correctness proofs add `[CFieldSpec α]`. -/

/-- Computable field operations: `zero`/`one`/`add`/`mul`/`neg`/`inv` and a zero test `isZero`;
bridge-free, so instances stay computable. -/
class CField (α : Type*) where
  /-- Computable zero. -/
  zero : α
  /-- Computable one. -/
  one : α
  /-- Computable addition. -/
  add : α → α → α
  /-- Computable multiplication. -/
  mul : α → α → α
  /-- Computable negation. -/
  neg : α → α
  /-- Computable inverse (`0⁻¹ = 0`). -/
  inv : α → α
  /-- Computable zero test. -/
  isZero : α → Bool

namespace CField

/-- Computable subtraction `a - b := a + (-b)`, derived from `add`/`neg`. -/
def sub {α : Type*} [CField α] (a b : α) : α := add a (neg b)

/-- Computable division `a / b := a * b⁻¹`, derived from `mul`/`inv`. -/
def div {α : Type*} [CField α] (a b : α) : α := mul a (inv b)

end CField

/-! ### The `CFieldSpec` typeclass (the field-homomorphism bridge)

`CFieldSpec α`: the noncomputable bridge `toK : α → K` into a Mathlib `Field K` intertwining the
`CField` operations, with `isZero_iff` certifying the zero test; `toK` need not be injective. -/

/-- Computable-field specification: the bridge `toK : α → K` into a Mathlib `Field K` intertwining
`zero`/`one`/`add`/`mul`/`neg`/`inv`, plus `isZero_iff` certifying `CField.isZero`. -/
class CFieldSpec (α : Type*) [CField α] where
  /-- The genuine Mathlib field the bridge lands in. -/
  K : Type*
  /-- `K` is a field. -/
  [instField : Field K]
  /-- The bridge to the genuine field. -/
  toK : α → K
  /-- `toK` sends `zero` to `0`. -/
  toK_zero : toK CField.zero = 0
  /-- `toK` sends `one` to `1`. -/
  toK_one : toK CField.one = 1
  /-- `toK` intertwines `add` with `+`. -/
  toK_add : ∀ a b, toK (CField.add a b) = toK a + toK b
  /-- `toK` intertwines `mul` with `*`. -/
  toK_mul : ∀ a b, toK (CField.mul a b) = toK a * toK b
  /-- `toK` intertwines `neg` with `-`. -/
  toK_neg : ∀ a, toK (CField.neg a) = - toK a
  /-- `toK` intertwines `inv` with `⁻¹`. -/
  toK_inv : ∀ a, toK (CField.inv a) = (toK a)⁻¹
  /-- `isZero a` is `true` iff `toK a = 0`. -/
  isZero_iff : ∀ a, CField.isZero a = true ↔ toK a = 0

/-- Expose `Field (CFieldSpec.K α)` as an instance so the genuine field structure resolves. -/
instance instFieldK (α : Type*) [CField α] [CFieldSpec α] : Field (CFieldSpec.K α) :=
  CFieldSpec.instField

-- The base `toK` homomorphism laws are the leaf denotation squares.
attribute [denote] CFieldSpec.toK_zero CFieldSpec.toK_one CFieldSpec.toK_add
  CFieldSpec.toK_mul CFieldSpec.toK_neg CFieldSpec.toK_inv

namespace CFieldSpec

/-- `toK` intertwines derived `sub` with `-`. -/
@[denote] theorem toK_sub {α : Type*} [CField α] [CFieldSpec α] (a b : α) :
    toK (CField.sub a b) = toK a - toK b := by
  rw [CField.sub, toK_add, toK_neg, sub_eq_add_neg]

/-- `toK` intertwines derived `div` with `/`. -/
@[denote] theorem toK_div {α : Type*} [CField α] [CFieldSpec α] (a b : α) :
    toK (CField.div a b) = toK a / toK b := by
  rw [CField.div, toK_mul, toK_inv, div_eq_mul_inv]

end CFieldSpec

/-! ### Instances: `CField ℚ` and `CFieldSpec ℚ`

`ℚ` as a computable field over itself: `ℚ`'s own operations, `isZero` by decidable equality, bridge
`K = ℚ`, `toK = id`. -/

/-- `CField ℚ`: rationals as a computable field with `ℚ`'s own operations and
`isZero a := decide (a = 0)`. -/
instance : CField ℚ where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  inv := (·⁻¹)
  isZero a := decide (a = 0)

/-- `CFieldSpec ℚ`: the trivial bridge `K = ℚ`, `toK = id`; all homomorphism laws are `rfl` and
`isZero_iff` is decidable-equality. -/
instance : CFieldSpec ℚ where
  K := ℚ
  toK := id
  toK_zero := rfl
  toK_one := rfl
  toK_add _ _ := rfl
  toK_mul _ _ := rfl
  toK_neg _ := rfl
  toK_inv _ := rfl
  isZero_iff a := by show decide (a = 0) = true ↔ id a = 0; simp

/-! ### The polynomial engine `CPolyG α := List α`

Dense-coefficient lists (index = degree, low to high) over `[CField α]`, with arithmetic built from
the `CField` operations and a Horner bridge `toPolyG` into `(CFieldSpec.K α)[X]`. -/

/-- Generic dense coefficient list over a computable field `α` (index = degree, low to high).
A reducible `abbrev` for `List α` so the `List` instances (`BEq`/`DecidableEq`/…) transfer and the
ℚ-specialization `CPoly := CPolyG ℚ` stays defeq to `List ℚ`. -/
abbrev CPolyG (α : Type*) := List α

namespace CPolyG

/-- Normalize a `CPolyG` by stripping trailing (high-degree) zero coefficients (`isZero`-tested),
so `cnormG` is a canonical form (the zero polynomial becomes `[]`). -/
def cnormG {α : Type*} [CField α] : CPolyG α → CPolyG α
  | [] => []
  | a :: as => match cnormG as with
    | [] => if CField.isZero a then [] else [a]
    | r => a :: r

/-- Coefficientwise addition of two `CPolyG`s (the shorter is zero-extended implicitly). -/
def caddG {α : Type*} [CField α] : CPolyG α → CPolyG α → CPolyG α
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => CField.add a b :: caddG as bs

/-- Negation of a `CPolyG`, coefficientwise. -/
def cnegG {α : Type*} [CField α] (p : CPolyG α) : CPolyG α := (p : List α).map CField.neg

/-- Subtraction of `CPolyG`s, `p − q := p + (−q)`. -/
def csubG {α : Type*} [CField α] (p q : CPolyG α) : CPolyG α := caddG p (cnegG q)

/-- Scalar multiplication of a `CPolyG` by `c : α`, coefficientwise. -/
def cscaleG {α : Type*} [CField α] (c : α) (p : CPolyG α) : CPolyG α := (p : List α).map (CField.mul c)

/-- Degree shift `cshiftG k p = x^k · p`: prepend `k` zero coefficients. -/
def cshiftG {α : Type*} [CField α] : ℕ → CPolyG α → CPolyG α
  | 0, p => p
  | n + 1, p => CField.zero :: cshiftG n p

/-- Polynomial multiplication of `CPolyG`s (schoolbook convolution via `cshiftG`/`cscaleG`). -/
def cmulG {α : Type*} [CField α] : CPolyG α → CPolyG α → CPolyG α
  | [], _ => []
  | a :: as, q => caddG (cscaleG a q) (CField.zero :: cmulG as q)

/-- Power of a `CPolyG` by `ℕ`-recursion (`[1]` at `0`). -/
def cpowG {α : Type*} [CField α] (p : CPolyG α) : ℕ → CPolyG α
  | 0 => [CField.one]
  | n + 1 => cmulG p (cpowG p n)

/-- Leading coefficient of a `CPolyG` (top nonzero coefficient; `zero` for the zero polynomial). -/
def cleadG {α : Type*} [CField α] (p : CPolyG α) : α := ((cnormG p : List α).getLast?.getD CField.zero)

/-- Degree of a `CPolyG` as a `ℕ`: `(length of normalized p) − 1`, with `cdegG 0 = 0`. -/
def cdegG {α : Type*} [CField α] (p : CPolyG α) : ℕ := (cnormG p : List α).length - 1

/-- Zero test for a `CPolyG`: `true` iff it normalizes to `[]`. -/
def cisZeroG {α : Type*} [CField α] (p : CPolyG α) : Bool := (cnormG p : List α).isEmpty

/-- Make a `CPolyG` monic (lead coefficient `1`) by scaling by `(clead)⁻¹`; the zero polynomial
stays `[]`. -/
def cmonicG {α : Type*} [CField α] (p : CPolyG α) : CPolyG α :=
  let p := cnormG p
  if cisZeroG p then [] else cscaleG (CField.inv (cleadG p)) p

/-! ### The generic Horner bridge `toPolyG` and its homomorphism lemmas

From here on the bridge `[CFieldSpec α]` is in scope: `toPolyG` and every correctness lemma carry the
extra binder, while the engine ops above need only `[CField α]`. -/

/-- Generic bridge to `(CFieldSpec.K α)[X]`: `toPolyG p` reads a `CPolyG` coefficient list (index =
degree, low to high) as a `Polynomial (CFieldSpec.K α)` in Horner form `p₀ + x·(p₁ + x·(p₂ + …))`,
each coefficient embedded via `toK`. -/
noncomputable def toPolyG {α : Type*} [CField α] [CFieldSpec α] : CPolyG α → (CFieldSpec.K α)[X]
  | [] => 0
  | a :: p => Polynomial.C (CFieldSpec.toK a) + X * toPolyG p

/-- `toPolyG [] = 0`: the empty coefficient list is the zero polynomial. -/
@[simp, denote] theorem toPolyG_nil {α : Type*} [CField α] [CFieldSpec α] :
    toPolyG ([] : CPolyG α) = 0 := rfl

/-- `toPolyG`'s leading recursion (Horner): `toPolyG (a :: p) = C (toK a) + X · toPolyG p`. -/
@[simp, denote] theorem toPolyG_cons {α : Type*} [CField α] [CFieldSpec α] (a : α) (p : CPolyG α) :
    toPolyG (a :: p) = Polynomial.C (CFieldSpec.toK a) + X * toPolyG p := rfl

/-- `toPolyG [CField.one] = 1`: the singleton coefficient list `[1]` reads as the polynomial `1`. -/
@[denote] theorem toPolyG_one_singleton {α : Type*} [CField α] [CFieldSpec α] :
    toPolyG ([CField.one] : CPolyG α) = 1 := by
  rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]

/-- `toPolyG [CField.one] ≠ 0`: the singleton coefficient list `[1]` reads nontrivially. -/
theorem toPolyG_one_singleton_ne_zero {α : Type*} [CField α] [CFieldSpec α] :
    toPolyG ([CField.one] : CPolyG α) ≠ 0 := by
  rw [toPolyG_one_singleton]
  exact one_ne_zero

/-- `toPolyG` is additive: `caddG` realizes `(CFieldSpec.K α)[X]` addition under the Horner bridge. -/
@[simp, denote] theorem toPolyG_caddG {α : Type*} [CField α] [CFieldSpec α] (p q : CPolyG α) :
    toPolyG (caddG p q) = toPolyG p + toPolyG q := by
  induction p generalizing q with
  | nil => simp [caddG]
  | cons a as ih =>
    cases q with
    | nil => simp [caddG]
    | cons b bs =>
      simp only [caddG, ih bs, denote, map_add]
      ring

/-- `toPolyG` commutes with negation: `toPolyG (cnegG p) = − toPolyG p`. -/
@[simp, denote] theorem toPolyG_cnegG {α : Type*} [CField α] [CFieldSpec α] (p : CPolyG α) :
    toPolyG (cnegG p) = - toPolyG p := by
  induction p with
  | nil => simp [cnegG]
  | cons a as ih =>
    show toPolyG (CField.neg a :: cnegG as) = -toPolyG (a :: as)
    simp only [denote, ih, map_neg]; ring

/-- `toPolyG` realizes subtraction: `toPolyG (csubG p q) = toPolyG p − toPolyG q`. -/
@[simp, denote] theorem toPolyG_csubG {α : Type*} [CField α] [CFieldSpec α] (p q : CPolyG α) :
    toPolyG (csubG p q) = toPolyG p - toPolyG q := by
  rw [csubG, toPolyG_caddG, toPolyG_cnegG, sub_eq_add_neg]

/-- `toPolyG` realizes scalar multiplication: `toPolyG (cscaleG c p) = C (toK c) · toPolyG p`. -/
@[simp, denote] theorem toPolyG_cscaleG {α : Type*} [CField α] [CFieldSpec α] (c : α) (p : CPolyG α) :
    toPolyG (cscaleG c p) = Polynomial.C (CFieldSpec.toK c) * toPolyG p := by
  induction p with
  | nil => simp [cscaleG]
  | cons a as ih =>
    show toPolyG (CField.mul c a :: cscaleG c as) = Polynomial.C (CFieldSpec.toK c) * toPolyG (a :: as)
    simp only [denote, ih, map_mul]; ring

/-- `toPolyG` realizes the degree shift: `toPolyG (cshiftG k p) = X^k · toPolyG p`. -/
@[simp, denote] theorem toPolyG_cshiftG {α : Type*} [CField α] [CFieldSpec α] (k : ℕ) (p : CPolyG α) :
    toPolyG (cshiftG k p) = X ^ k * toPolyG p := by
  induction k with
  | zero => simp [cshiftG]
  | succ n ih =>
    show toPolyG (CField.zero :: cshiftG n p) = X ^ (n + 1) * toPolyG p
    simp only [denote, ih, map_zero]; ring

/-- `toPolyG` is multiplicative: `cmulG` realizes `(CFieldSpec.K α)[X]` multiplication. -/
@[simp, denote] theorem toPolyG_cmulG {α : Type*} [CField α] [CFieldSpec α] (p q : CPolyG α) :
    toPolyG (cmulG p q) = toPolyG p * toPolyG q := by
  induction p with
  | nil => simp [cmulG]
  | cons a as ih =>
    show toPolyG (caddG (cscaleG a q) (CField.zero :: cmulG as q)) = toPolyG (a :: as) * toPolyG q
    simp only [denote, ih, map_zero]; ring

/-- `toPolyG` realizes the `ℕ`-power: `toPolyG (cpowG p n) = (toPolyG p) ^ n`. -/
@[simp, denote] theorem toPolyG_cpowG {α : Type*} [CField α] [CFieldSpec α] (p : CPolyG α) (n : ℕ) :
    toPolyG (cpowG p n) = (toPolyG p) ^ n := by
  induction n with
  | zero => simp [cpowG, denote]
  | succ n ih => rw [cpowG, toPolyG_cmulG, ih, pow_succ, mul_comm]

/-! ### Normalization, degree, leading coefficient — generic correctness -/

/-- `cnormG [] = []`. -/
@[simp] theorem cnormG_nil {α : Type*} [CField α] : cnormG ([] : CPolyG α) = [] := rfl

/-- `cnormG` on a cons cell, unfolded to its defining `match` (definitional). -/
theorem cnormG_cons_eq {α : Type*} [CField α] (a : α) (as : CPolyG α) :
    cnormG (a :: as)
      = (match cnormG as with | [] => if CField.isZero a then [] else [a] | r => a :: r) := rfl

/-- `cnormG` is idempotent: stripping trailing zeros twice is the same as once. -/
@[simp] theorem cnormG_idem {α : Type*} [CField α] (p : CPolyG α) : cnormG (cnormG p) = cnormG p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [cnormG_cons_eq]
    cases h : cnormG as with
    | nil => cases ha : CField.isZero a <;> simp [cnormG_cons_eq, ha]
    | cons b bs =>
      rw [h] at ih
      simp only [cnormG_cons_eq, ih]

/-- `toPolyG` ignores normalization: `toPolyG (cnormG p) = toPolyG p` — stripping trailing zeros
does not change the polynomial (the dropped coefficients are zero, via `isZero_iff`). -/
@[simp, denote] theorem toPolyG_cnormG {α : Type*} [CField α] [CFieldSpec α] (p : CPolyG α) :
    toPolyG (cnormG p) = toPolyG p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [cnormG_cons_eq]
    cases h : cnormG as with
    | nil =>
      rw [h] at ih
      simp only [toPolyG_nil] at ih
      have has : toPolyG as = 0 := ih.symm
      cases ha : CField.isZero a with
      | true =>
        have ha0 : CFieldSpec.toK a = 0 := (CFieldSpec.isZero_iff a).mp ha
        rw [if_pos rfl, toPolyG_nil, toPolyG_cons, has, mul_zero, add_zero, ha0, map_zero]
      | false =>
        rw [if_neg (by simp), toPolyG_cons, toPolyG_nil, mul_zero, add_zero, toPolyG_cons, has,
          mul_zero, add_zero]
    | cons b bs =>
      rw [h] at ih
      simp only [toPolyG_cons, ih]

/-- Coefficient read: the `i`-th coefficient of `toPolyG p` is `toK` of the `i`-th list entry
(`0` past the end). The Horner bridge realizes the dense coefficient list exactly. -/
theorem toPolyG_coeff {α : Type*} [CField α] [CFieldSpec α] (p : CPolyG α) (i : ℕ) :
    (toPolyG p).coeff i = CFieldSpec.toK ((p : List α).getD i CField.zero) := by
  induction p generalizing i with
  | nil => simp [CFieldSpec.toK_zero]
  | cons a as ih =>
    rw [toPolyG_cons]
    cases i with
    | zero => simp [coeff_C]
    | succ n => simp [coeff_X_mul, ih]

/-- `toK` reads a normalized coefficient as the corresponding coefficient of `toPolyG p`. -/
theorem toK_cnormG_getD {α : Type*} [CField α] [CFieldSpec α] (p : CPolyG α) (k : ℕ) :
    CFieldSpec.toK ((cnormG p : List α).getD k CField.zero) = (toPolyG p).coeff k := by
  rw [← toPolyG_coeff, toPolyG_cnormG]

/-- `cnormG` has no trailing zero: `(cnormG p).getLast?` is never a zero coefficient. -/
theorem cnormG_getLast?_ne_some_zero {α : Type*} [CField α] (p : CPolyG α) :
    ∀ v, (cnormG p : List α).getLast? = some v → CField.isZero v = false := by
  induction p with
  | nil => simp
  | cons a as ih =>
    rw [cnormG_cons_eq]
    cases h : cnormG as with
    | nil =>
      cases ha : CField.isZero a with
      | true => rw [if_pos rfl]; simp
      | false =>
        intro v hv
        rw [if_neg (by simp), List.getLast?_singleton, Option.some.injEq] at hv
        rwa [← hv]
    | cons b bs =>
      rw [h] at ih
      intro v hv
      rw [List.getLast?_cons_cons] at hv
      exact ih v hv

/-- For a normalized nonzero `CPolyG`, the leading coefficient `cleadG` is nonzero (in `K`). -/
theorem toK_cleadG_ne_zero {α : Type*} [CField α] [CFieldSpec α] {p : CPolyG α} (h : cnormG p ≠ []) :
    CFieldSpec.toK (cleadG p) ≠ 0 := by
  rw [cleadG]
  rcases hl : (cnormG p : List α).getLast? with _ | v
  · exact absurd (List.getLast?_eq_none_iff.mp hl) h
  · simp only [Option.getD_some]
    intro hv
    have := cnormG_getLast?_ne_some_zero p v hl
    rw [(CFieldSpec.isZero_iff v).mpr hv] at this
    exact absurd this (by simp)

/-- `cleadG` is the coefficient at the top index: `toK (cleadG p) = (toPolyG p).coeff (cdegG p)`. -/
theorem toK_cleadG_eq_coeff {α : Type*} [CField α] [CFieldSpec α] (p : CPolyG α) :
    CFieldSpec.toK (cleadG p) = (toPolyG p).coeff (cdegG p) := by
  rw [cleadG, cdegG, ← toPolyG_cnormG, toPolyG_coeff, List.getD_eq_getElem?_getD,
    ← List.getLast?_eq_getElem?]

/-- Degree bound: `natDegree (toPolyG p) ≤ (cnormG p).length − 1`. -/
theorem natDegree_toPolyG_le {α : Type*} [CField α] [CFieldSpec α] (p : CPolyG α) :
    (toPolyG p).natDegree ≤ (cnormG p : List α).length - 1 := by
  rw [← toPolyG_cnormG]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [toPolyG_coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none,
    CFieldSpec.toK_zero]

/-- `cdegG` is the honest `natDegree`: `cdegG p = (toPolyG p).natDegree`. -/
theorem cdegG_eq_natDegree {α : Type*} [CField α] [CFieldSpec α] (p : CPolyG α) :
    cdegG p = (toPolyG p).natDegree := by
  rcases eq_or_ne (cnormG p) [] with h | h
  · have h0 : toPolyG p = 0 := by rw [← toPolyG_cnormG, h, toPolyG_nil]
    rw [cdegG, h, h0]; simp
  · refine le_antisymm ?_ (natDegree_toPolyG_le p)
    apply Polynomial.le_natDegree_of_ne_zero
    rw [← toK_cleadG_eq_coeff]
    exact toK_cleadG_ne_zero h

/-- `toK (cleadG p)` is the honest `leadingCoeff`: `toK (cleadG p) = (toPolyG p).leadingCoeff`. -/
theorem toK_cleadG_eq_leadingCoeff {α : Type*} [CField α] [CFieldSpec α] (p : CPolyG α) :
    CFieldSpec.toK (cleadG p) = (toPolyG p).leadingCoeff := by
  rw [Polynomial.leadingCoeff, ← cdegG_eq_natDegree, ← toK_cleadG_eq_coeff]

/-- `cnormG p = []` iff `toPolyG p = 0` (the list normalizes to empty exactly for the zero
polynomial). -/
theorem cnormG_eq_nil_iff {α : Type*} [CField α] [CFieldSpec α] (p : CPolyG α) :
    cnormG p = [] ↔ toPolyG p = 0 := by
  constructor
  · intro h; rw [← toPolyG_cnormG, h, toPolyG_nil]
  · intro h
    by_contra hne
    have hcl := toK_cleadG_ne_zero hne
    rw [toK_cleadG_eq_leadingCoeff, h, Polynomial.leadingCoeff_zero] at hcl
    exact hcl rfl

/-- `length (cnormG p) < length (cnormG q)` (with `cnormG q ≠ []`) gives
`deg (toPolyG p) < deg (toPolyG q)`. -/
theorem toPolyG_degree_lt_of_length_lt {α : Type*} [CField α] [CFieldSpec α] (p q : CPolyG α)
    (hq : cnormG q ≠ []) (hlen : (cnormG p : List α).length < (cnormG q : List α).length) :
    (toPolyG p).degree < (toPolyG q).degree := by
  have hq0 : toPolyG q ≠ 0 := fun h => hq ((cnormG_eq_nil_iff q).mpr h)
  rcases eq_or_ne (cnormG p) [] with hp | hp
  · rw [(cnormG_eq_nil_iff p).mp hp, Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr (by rwa [Ne, Polynomial.degree_eq_bot])
  · have hp0 : toPolyG p ≠ 0 := fun h => hp ((cnormG_eq_nil_iff p).mpr h)
    rw [Polynomial.degree_eq_natDegree hp0, Polynomial.degree_eq_natDegree hq0, Nat.cast_lt,
      ← cdegG_eq_natDegree, ← cdegG_eq_natDegree, cdegG, cdegG]
    have hplen : 1 ≤ (cnormG p : List α).length := List.length_pos_iff.mpr hp
    have hqlen : 1 ≤ (cnormG q : List α).length := List.length_pos_iff.mpr hq
    omega

/-- `cisZeroG` reads as `toPolyG = 0`: `cisZeroG p = true ↔ toPolyG p = 0`. -/
theorem cisZeroG_iff {α : Type*} [CField α] [CFieldSpec α] (p : CPolyG α) :
    cisZeroG p = true ↔ toPolyG p = 0 := by
  rw [cisZeroG, ← cnormG_eq_nil_iff]
  exact (List.isEmpty_iff (l := (cnormG p : List α)))

/-- `cisZeroG p = false` gives `toPolyG p ≠ 0`. -/
theorem toPolyG_ne_zero_of_cisZeroG_false {α : Type*} [CField α] [CFieldSpec α] {p : CPolyG α}
    (h : cisZeroG p = false) :
    toPolyG p ≠ 0 := by
  rw [Bool.eq_false_iff, Ne, cisZeroG_iff] at h
  exact h

/-- `toPolyG (cmonicG p)` is monic for `toPolyG p ≠ 0`. -/
theorem monic_toPolyG_cmonicG {α : Type*} [CField α] [CFieldSpec α] (p : CPolyG α)
    (hp : toPolyG p ≠ 0) :
    (toPolyG (cmonicG p)).Monic := by
  have hz : cisZeroG (cnormG p) = false := by
    rw [← Bool.not_eq_true, cisZeroG_iff, toPolyG_cnormG]
    exact hp
  have hcform : toPolyG (cmonicG p)
      = Polynomial.C (CFieldSpec.toK (CField.inv (cleadG (cnormG p)))) * toPolyG p := by
    rw [cmonicG, if_neg (by rw [hz]; decide), toPolyG_cscaleG, toPolyG_cnormG]
  rw [hcform]
  refine monic_C_mul_of_mul_leadingCoeff_eq_one ?_
  rw [CFieldSpec.toK_inv, toK_cleadG_eq_leadingCoeff, toPolyG_cnormG,
    inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hp)]

end CPolyG

end DeepWiki.SymbolicIntegration
