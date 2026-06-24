import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.Polynomial.Basic

/-! # Generic computable field + polynomial engine (the differential-field-tower base)
The Risch algorithm needs the **same** polynomial engine over a *tower* of differential fields
ℚ ⊂ ℚ(x) ⊂ ℚ(x)(t) ⊂ …, so this file abstracts the carrier into a `CField` typeclass: a type `α` of
computable field elements with a bridge `toK : α → K` to a genuine Mathlib `Field K` that intertwines
the computable `zero`/`one`/`add`/`mul`/`neg`/`inv` with the field operations. The generic polynomial
engine `CPolyG α := List α` (dense coefficients, index = degree) mirrors a `cadd`/`cmul`/… arithmetic
over any `CField`, with a generic Horner bridge `toPolyG : CPolyG α → (CFieldSpec.K α)[X]` proven to
realize `(CFieldSpec.K α)[X]` arithmetic. This file is **standalone** (imports only Mathlib): the
coherence with the concrete `CPoly := List ℚ` engine lives downstream in `ComputableField`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### The `CField` typeclass (computable operations only)

`CField α` packages just the **computable** field operations on `α`: `zero`/`one`/`add`/`mul`/`neg`/
`inv` and the computable zero test `isZero`, plus derived `sub`/`div`. It is deliberately bridge-free,
so an instance like `CField QFunNZ` whose operations are honest list computations stays *computable*
even though its companion `CFieldSpec` (the field-homomorphism bridge) is noncomputable. The generic
polynomial **engine** (`caddG`/`cmulG`/`cdivmodG`/`cgcdExtG`/`cderivG`) needs only `[CField α]`, so it
reduces (`#eval`/`native_decide`); the **correctness proofs** add `[CFieldSpec α]`. -/

/-- **Computable field operations**: a type `α` with computable `zero`/`one`/`add`/`mul`/`neg`/`inv`
and a computable zero test `isZero`. Bridge-free, so instances built from honest computations stay
computable; the field-homomorphism bridge lives in the companion `CFieldSpec`. The base of the
differential-field tower the Risch algorithm runs the polynomial engine over. -/
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

/-- **Computable subtraction** `a - b := a + (-b)`, derived from `add`/`neg`. -/
def sub {α : Type*} [CField α] (a b : α) : α := add a (neg b)

/-- **Computable division** `a / b := a * b⁻¹`, derived from `mul`/`inv`. -/
def div {α : Type*} [CField α] (a b : α) : α := mul a (inv b)

end CField

/-! ### The `CFieldSpec` typeclass (the field-homomorphism bridge)

`CFieldSpec α` (over `[CField α]`) carries the noncomputable bridge `toK : α → K` into a genuine
Mathlib `Field K` that intertwines the `CField` operations, plus the certification `isZero_iff` of the
computable zero test against `toK a = 0`. `toK` need NOT be injective — the engine operates on
representations and tests `K`-equality through `isZero`, so multiple representations of one field
element are fine (e.g. unreduced rational functions). Keeping this separate from `CField` is what lets
the engine compute while only the *correctness layer* depends on the bridge. -/

/-- **Computable-field specification**: the field-homomorphism bridge for `[CField α]`. Carries
`toK : α → K` into a Mathlib `Field K` intertwining `zero`/`one`/`add`/`mul`/`neg`/`inv`, plus the
certification `isZero_iff` of `CField.isZero` against `toK a = 0`. Noncomputable in general; required
only by the correctness proofs, not by the engine. -/
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

namespace CFieldSpec

/-- `toK` intertwines derived `sub` with `-`. -/
theorem toK_sub {α : Type*} [CField α] [CFieldSpec α] (a b : α) :
    toK (CField.sub a b) = toK a - toK b := by
  rw [CField.sub, toK_add, toK_neg, sub_eq_add_neg]

/-- `toK` intertwines derived `div` with `/`. -/
theorem toK_div {α : Type*} [CField α] [CFieldSpec α] (a b : α) :
    toK (CField.div a b) = toK a / toK b := by
  rw [CField.div, toK_mul, toK_inv, div_eq_mul_inv]

end CFieldSpec

/-! ### Instances: `CField ℚ` and `CFieldSpec ℚ`

`ℚ` is trivially a computable field over itself: the operations are `ℚ`'s own, `isZero` by decidable
equality, and the bridge is `K = ℚ`, `toK = id` with every law `rfl`. The simplest instance — and the
one that validates the whole abstraction. -/

/-- **`CField ℚ`**: rationals as a computable field with `ℚ`'s own operations and
`isZero a := decide (a = 0)`. -/
instance : CField ℚ where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  inv := (·⁻¹)
  isZero a := decide (a = 0)

/-- **`CFieldSpec ℚ`**: the trivial bridge `K = ℚ`, `toK = id`; all homomorphism laws are `rfl` and
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

/-! ### Generic polynomial engine `CPolyG α := List α`

Over any `[CField α]` the dense-coefficient list `CPolyG α` (index = degree, low to high) carries the
same arithmetic as the concrete `CPoly = List ℚ`, with `ℚ` operations replaced by `CField.add`/`mul`/
`neg`/`isZero`. The generic Horner bridge `toPolyG : CPolyG α → (CFieldSpec.K α)[X]` embeds via `toK`
(so it additionally needs `[CFieldSpec α]`). -/

/-- **Generic dense coefficient list** over a computable field `α` (index = degree, low to high).
A reducible `abbrev` for `List α` so the `List` instances (`BEq`/`DecidableEq`/…) transfer and the
ℚ-specialization `CPoly := CPolyG ℚ` stays defeq to `List ℚ`. -/
abbrev CPolyG (α : Type*) := List α

namespace CPolyG

variable {α : Type*} [CField α]

/-- **Normalize** a `CPolyG` by stripping trailing (high-degree) zero coefficients (`isZero`-tested),
so `cnormG` is a canonical form (the zero polynomial becomes `[]`). -/
def cnormG : CPolyG α → CPolyG α
  | [] => []
  | a :: as => match cnormG as with
    | [] => if CField.isZero a then [] else [a]
    | r => a :: r

/-- **Coefficientwise addition** of two `CPolyG`s (the shorter is zero-extended implicitly). -/
def caddG : CPolyG α → CPolyG α → CPolyG α
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => CField.add a b :: caddG as bs

/-- **Negation** of a `CPolyG`, coefficientwise. -/
def cnegG (p : CPolyG α) : CPolyG α := (p : List α).map CField.neg

/-- **Subtraction** of `CPolyG`s, `p − q := p + (−q)`. -/
def csubG (p q : CPolyG α) : CPolyG α := caddG p (cnegG q)

/-- **Scalar multiplication** of a `CPolyG` by `c : α`, coefficientwise. -/
def cscaleG (c : α) (p : CPolyG α) : CPolyG α := (p : List α).map (CField.mul c)

/-- **Degree shift** `cshiftG k p = x^k · p`: prepend `k` zero coefficients. -/
def cshiftG : ℕ → CPolyG α → CPolyG α
  | 0, p => p
  | n + 1, p => CField.zero :: cshiftG n p

/-- **Polynomial multiplication** of `CPolyG`s (schoolbook convolution via `cshiftG`/`cscaleG`). -/
def cmulG : CPolyG α → CPolyG α → CPolyG α
  | [], _ => []
  | a :: as, q => caddG (cscaleG a q) (CField.zero :: cmulG as q)

/-- **Power** of a `CPolyG` by `ℕ`-recursion (`[1]` at `0`). -/
def cpowG (p : CPolyG α) : ℕ → CPolyG α
  | 0 => [CField.one]
  | n + 1 => cmulG p (cpowG p n)

/-- **Leading coefficient** of a `CPolyG` (top nonzero coefficient; `zero` for the zero polynomial). -/
def cleadG (p : CPolyG α) : α := ((cnormG p : List α).getLast?.getD CField.zero)

/-- **Degree** of a `CPolyG` as a `ℕ`: `(length of normalized p) − 1`, with `cdegG 0 = 0`. -/
def cdegG (p : CPolyG α) : ℕ := (cnormG p : List α).length - 1

/-- **Zero test** for a `CPolyG`: `true` iff it normalizes to `[]`. -/
def cisZeroG (p : CPolyG α) : Bool := (cnormG p : List α).isEmpty

/-- **Make a `CPolyG` monic** (lead coefficient `1`) by scaling by `(clead)⁻¹`; the zero polynomial
stays `[]`. -/
def cmonicG (p : CPolyG α) : CPolyG α :=
  let p := cnormG p
  if cisZeroG p then [] else cscaleG (CField.inv (cleadG p)) p

/-! ### Generic Euclidean division and extended Euclidean algorithm (engine, `[CField α]`-only)

`cdivmodG`/`cdivG`/`cmodG`/`cdvdG`/`cgcdExtG` mirror `Compute.cdivmod`/… over any `[CField α]`
(ℚ-division `clead p / clead q` becomes `CField.div`); only the engine `[CField α]` operations are
used, so they reduce (`#eval`/`native_decide`). Their correctness (Euclidean identity, Bézout, gcd
divisibility) lives downstream in `ComputableFieldGcd` where `[CFieldSpec α]` is in scope. -/

/-- **Generic Euclidean division** of `CPolyG`s, fuel-bounded: `cdivmodG fuel p q = (quotient,
remainder)` with `p = quotient · q + remainder` over the field `K` (`q ≠ 0`; one step per degree drop). -/
def cdivmodG : ℕ → CPolyG α → CPolyG α → CPolyG α × CPolyG α
  | 0, p, _ => ([], cnormG p)
  | fuel + 1, p, q =>
    let p := cnormG p
    let q := cnormG q
    if cisZeroG q then ([], [])
    else if (p : List α).length < (q : List α).length then ([], p)
    else
      let c := CField.div (cleadG p) (cleadG q)
      let k := (p : List α).length - (q : List α).length
      let term := cshiftG k [c]
      let p' := cnormG (csubG p (cmulG term q))
      let (quo, rem) := cdivmodG fuel p' q
      (caddG term quo, rem)

/-- **Quotient** of generic Euclidean division (`cdivmodG`'s first component). -/
def cdivG (fuel : ℕ) (p q : CPolyG α) : CPolyG α := (cdivmodG fuel p q).1

/-- **Remainder** of generic Euclidean division (`cdivmodG`'s second component). -/
def cmodG (fuel : ℕ) (p q : CPolyG α) : CPolyG α := (cdivmodG fuel p q).2

/-- **Generic divisibility test** `cdvdG fuel q p`: `true` iff `q ∣ p` (remainder of `p` by `q` is
zero). -/
def cdvdG (fuel : ℕ) (q p : CPolyG α) : Bool := cisZeroG (cmodG fuel p q)

/-- **Generic extended Euclidean algorithm** on `CPolyG`s, fuel-bounded: `cgcdExtG fuel a b =
(g, s, t)` with `s · a + t · b = g` and `g = gcd(a, b)` over `K`. -/
def cgcdExtG : ℕ → CPolyG α → CPolyG α → CPolyG α × CPolyG α × CPolyG α
  | 0, a, _ => (cnormG a, [CField.one], [])
  | fuel + 1, a, b =>
    if cisZeroG b then (cnormG a, [CField.one], [])
    else
      let (q, _) := cdivmodG (fuel + 1) a b
      let (g, s, t) := cgcdExtG fuel b (cmodG (fuel + 1) a b)
      (g, t, csubG s (cmulG t q))

/-! ### The generic Horner bridge `toPolyG` and its homomorphism lemmas

From here on the bridge `[CFieldSpec α]` is in scope: `toPolyG` and every correctness lemma reference
`CFieldSpec.toK`/`CFieldSpec.K` and so carry the extra binder, while the engine ops above need only
`[CField α]`. -/

variable [CFieldSpec α]

/-- **Generic bridge to `(CFieldSpec.K α)[X]`**: `toPolyG p` reads a `CPolyG` coefficient list (index =
degree, low to high) as a `Polynomial (CFieldSpec.K α)` in **Horner form** `p₀ + x·(p₁ + x·(p₂ + …))`,
each coefficient embedded via `toK`. -/
noncomputable def toPolyG : CPolyG α → (CFieldSpec.K α)[X]
  | [] => 0
  | a :: p => Polynomial.C (CFieldSpec.toK a) + X * toPolyG p

/-- `toPolyG [] = 0`: the empty coefficient list is the zero polynomial. -/
@[simp] theorem toPolyG_nil : toPolyG ([] : CPolyG α) = 0 := rfl

/-- `toPolyG`'s leading recursion (Horner): `toPolyG (a :: p) = C (toK a) + X · toPolyG p`. -/
@[simp] theorem toPolyG_cons (a : α) (p : CPolyG α) :
    toPolyG (a :: p) = Polynomial.C (CFieldSpec.toK a) + X * toPolyG p := rfl

/-- `toPolyG` is **additive**: `caddG` realizes `(CFieldSpec.K α)[X]` addition under the Horner bridge. -/
theorem toPolyG_caddG (p q : CPolyG α) : toPolyG (caddG p q) = toPolyG p + toPolyG q := by
  induction p generalizing q with
  | nil => simp [caddG]
  | cons a as ih =>
    cases q with
    | nil => simp [caddG]
    | cons b bs =>
      simp only [caddG, toPolyG_cons, ih bs, CFieldSpec.toK_add, map_add]
      ring

/-- `toPolyG` commutes with **negation**: `toPolyG (cnegG p) = − toPolyG p`. -/
theorem toPolyG_cnegG (p : CPolyG α) : toPolyG (cnegG p) = - toPolyG p := by
  induction p with
  | nil => simp [cnegG]
  | cons a as ih =>
    show toPolyG (CField.neg a :: cnegG as) = -toPolyG (a :: as)
    rw [toPolyG_cons, toPolyG_cons, ih, CFieldSpec.toK_neg, map_neg]; ring

/-- `toPolyG` realizes **subtraction**: `toPolyG (csubG p q) = toPolyG p − toPolyG q`. -/
theorem toPolyG_csubG (p q : CPolyG α) : toPolyG (csubG p q) = toPolyG p - toPolyG q := by
  rw [csubG, toPolyG_caddG, toPolyG_cnegG, sub_eq_add_neg]

/-- `toPolyG` realizes **scalar multiplication**: `toPolyG (cscaleG c p) = C (toK c) · toPolyG p`. -/
theorem toPolyG_cscaleG (c : α) (p : CPolyG α) :
    toPolyG (cscaleG c p) = Polynomial.C (CFieldSpec.toK c) * toPolyG p := by
  induction p with
  | nil => simp [cscaleG]
  | cons a as ih =>
    show toPolyG (CField.mul c a :: cscaleG c as) = Polynomial.C (CFieldSpec.toK c) * toPolyG (a :: as)
    rw [toPolyG_cons, toPolyG_cons, ih, CFieldSpec.toK_mul, map_mul]; ring

/-- `toPolyG` realizes the **degree shift**: `toPolyG (cshiftG k p) = X^k · toPolyG p`. -/
theorem toPolyG_cshiftG (k : ℕ) (p : CPolyG α) : toPolyG (cshiftG k p) = X ^ k * toPolyG p := by
  induction k with
  | zero => simp [cshiftG]
  | succ n ih =>
    show toPolyG (CField.zero :: cshiftG n p) = X ^ (n + 1) * toPolyG p
    rw [toPolyG_cons, ih, CFieldSpec.toK_zero, map_zero]; ring

/-- `toPolyG` is **multiplicative**: `cmulG` realizes `(CFieldSpec.K α)[X]` multiplication. -/
theorem toPolyG_cmulG (p q : CPolyG α) : toPolyG (cmulG p q) = toPolyG p * toPolyG q := by
  induction p with
  | nil => simp [cmulG]
  | cons a as ih =>
    show toPolyG (caddG (cscaleG a q) (CField.zero :: cmulG as q)) = toPolyG (a :: as) * toPolyG q
    rw [toPolyG_caddG, toPolyG_cscaleG, toPolyG_cons, toPolyG_cons, ih, CFieldSpec.toK_zero,
      map_zero]; ring

/-- `toPolyG` realizes the **`ℕ`-power**: `toPolyG (cpowG p n) = (toPolyG p) ^ n`. -/
theorem toPolyG_cpowG (p : CPolyG α) (n : ℕ) : toPolyG (cpowG p n) = (toPolyG p) ^ n := by
  induction n with
  | zero => simp [cpowG, toPolyG_cons, CFieldSpec.toK_one]
  | succ n ih => rw [cpowG, toPolyG_cmulG, ih, pow_succ, mul_comm]

/-! ### Normalization, degree, leading coefficient — generic correctness -/

omit [CFieldSpec α] in
/-- `cnormG [] = []`. -/
@[simp] theorem cnormG_nil : cnormG ([] : CPolyG α) = [] := rfl

omit [CFieldSpec α] in
/-- `cnormG` on a cons cell, unfolded to its defining `match` (definitional). -/
theorem cnormG_cons_eq (a : α) (as : CPolyG α) :
    cnormG (a :: as)
      = (match cnormG as with | [] => if CField.isZero a then [] else [a] | r => a :: r) := rfl

omit [CFieldSpec α] in
/-- `cnormG` is **idempotent**: stripping trailing zeros twice is the same as once. -/
@[simp] theorem cnormG_idem (p : CPolyG α) : cnormG (cnormG p) = cnormG p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [cnormG_cons_eq]
    cases h : cnormG as with
    | nil => cases ha : CField.isZero a <;> simp [cnormG_cons_eq, ha]
    | cons b bs =>
      rw [h] at ih
      simp only [cnormG_cons_eq, ih]

/-- **`toPolyG` ignores normalization**: `toPolyG (cnormG p) = toPolyG p` — stripping trailing zeros
does not change the polynomial (the dropped coefficients are zero, via `isZero_iff`). -/
@[simp] theorem toPolyG_cnormG (p : CPolyG α) : toPolyG (cnormG p) = toPolyG p := by
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

/-- **Coefficient read**: the `i`-th coefficient of `toPolyG p` is `toK` of the `i`-th list entry
(`0` past the end). The Horner bridge realizes the dense coefficient list exactly. -/
theorem toPolyG_coeff (p : CPolyG α) (i : ℕ) :
    (toPolyG p).coeff i = CFieldSpec.toK ((p : List α).getD i CField.zero) := by
  induction p generalizing i with
  | nil => simp [CFieldSpec.toK_zero]
  | cons a as ih =>
    rw [toPolyG_cons]
    cases i with
    | zero => simp [coeff_C]
    | succ n => simp [coeff_X_mul, ih]

omit [CFieldSpec α] in
/-- `cnormG` has **no trailing zero**: `(cnormG p).getLast?` is never a zero coefficient. -/
theorem cnormG_getLast?_ne_some_zero (p : CPolyG α) :
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
theorem toK_cleadG_ne_zero {p : CPolyG α} (h : cnormG p ≠ []) : CFieldSpec.toK (cleadG p) ≠ 0 := by
  rw [cleadG]
  rcases hl : (cnormG p : List α).getLast? with _ | v
  · exact absurd (List.getLast?_eq_none_iff.mp hl) h
  · simp only [Option.getD_some]
    intro hv
    have := cnormG_getLast?_ne_some_zero p v hl
    rw [(CFieldSpec.isZero_iff v).mpr hv] at this
    exact absurd this (by simp)

/-- **`cleadG` is the coefficient at the top index**: `toK (cleadG p) = (toPolyG p).coeff (cdegG p)`. -/
theorem toK_cleadG_eq_coeff (p : CPolyG α) :
    CFieldSpec.toK (cleadG p) = (toPolyG p).coeff (cdegG p) := by
  rw [cleadG, cdegG, ← toPolyG_cnormG, toPolyG_coeff, List.getD_eq_getElem?_getD,
    ← List.getLast?_eq_getElem?]

/-- **Degree bound**: `natDegree (toPolyG p) ≤ (cnormG p).length − 1`. -/
theorem natDegree_toPolyG_le (p : CPolyG α) : (toPolyG p).natDegree ≤ (cnormG p : List α).length - 1 := by
  rw [← toPolyG_cnormG]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [toPolyG_coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none,
    CFieldSpec.toK_zero]

/-- **`cdegG` is the honest `natDegree`**: `cdegG p = (toPolyG p).natDegree`. -/
theorem cdegG_eq_natDegree (p : CPolyG α) : cdegG p = (toPolyG p).natDegree := by
  rcases eq_or_ne (cnormG p) [] with h | h
  · have h0 : toPolyG p = 0 := by rw [← toPolyG_cnormG, h, toPolyG_nil]
    rw [cdegG, h, h0]; simp
  · refine le_antisymm ?_ (natDegree_toPolyG_le p)
    apply Polynomial.le_natDegree_of_ne_zero
    rw [← toK_cleadG_eq_coeff]
    exact toK_cleadG_ne_zero h

/-- **`toK (cleadG p)` is the honest `leadingCoeff`**: `toK (cleadG p) = (toPolyG p).leadingCoeff`. -/
theorem toK_cleadG_eq_leadingCoeff (p : CPolyG α) :
    CFieldSpec.toK (cleadG p) = (toPolyG p).leadingCoeff := by
  rw [Polynomial.leadingCoeff, ← cdegG_eq_natDegree, ← toK_cleadG_eq_coeff]

/-- `cnormG p = []` iff `toPolyG p = 0` (the list normalizes to empty exactly for the zero
polynomial). -/
theorem cnormG_eq_nil_iff (p : CPolyG α) : cnormG p = [] ↔ toPolyG p = 0 := by
  constructor
  · intro h; rw [← toPolyG_cnormG, h, toPolyG_nil]
  · intro h
    by_contra hne
    have hcl := toK_cleadG_ne_zero hne
    rw [toK_cleadG_eq_leadingCoeff, h, Polynomial.leadingCoeff_zero] at hcl
    exact hcl rfl

/-- **`cisZeroG` reads as `toPolyG = 0`**: `cisZeroG p = true ↔ toPolyG p = 0`. -/
theorem cisZeroG_iff (p : CPolyG α) : cisZeroG p = true ↔ toPolyG p = 0 := by
  rw [cisZeroG, ← cnormG_eq_nil_iff]
  exact (List.isEmpty_iff (l := (cnormG p : List α)))

end CPolyG

end DeepWiki.SymbolicIntegration
