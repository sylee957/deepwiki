import DeepWiki.SymbolicIntegration.LogToAtanCompute
import DeepWiki.SymbolicIntegration.ComputeCorrectness
import DeepWiki.SymbolicIntegration.RationalFunctionCompute

/-! # Generic computable field + polynomial engine (the differential-field-tower base)
The concrete `CPoly := List ℚ` engine (`LogToAtanCompute`, `ComputeCorrectness`) and the computable
ℚ(x) field `QFun` (`RationalFunctionCompute`) are each specialized to one carrier. The Risch
algorithm needs the **same** polynomial engine over a *tower* of differential fields ℚ ⊂ ℚ(x) ⊂
ℚ(x)(t) ⊂ …, so this file abstracts the carrier into a `CField` typeclass: a type `α` of computable
field elements with a bridge `toK : α → K` to a genuine Mathlib `Field K` that intertwines the
computable `zero`/`one`/`add`/`mul`/`neg`/`inv` with the field operations. The generic polynomial
engine `CPolyG α := List α` (dense coefficients, index = degree) mirrors the concrete `cadd`/`cmul`/…
over any `CField`, with a generic Horner bridge `toPolyG : CPolyG α → (CField.K α)[X]` proven to
realize `(CField.K α)[X]` arithmetic. The coherence lemmas (`caddG (α := ℚ) = cadd`, `toPolyG
(α := ℚ) = toPoly`) show the generic engine specializes back to the concrete one, so a later stage
can migrate `CPoly := CPolyG ℚ` without breaking consumers. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### The `CField` typeclass

`CField α` packages computable field operations on `α` together with an injective bridge `toK : α → K`
into a genuine Mathlib `Field K` that intertwines them. The `isZero` predicate is the computable zero
test, certified by `isZero_iff` against `toK a = 0`. `sub`/`div` are derived (default-field-defined). -/

/-- **Computable field**: a type `α` of computable field elements with an injective field-homomorphism
bridge `toK : α → K` into a Mathlib `Field K` intertwining `zero`/`one`/`add`/`mul`/`neg`/`inv`, plus a
certified computable zero test `isZero`. The base of the differential-field tower the Risch algorithm
runs the polynomial engine over. -/
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
  /-- The genuine Mathlib field the bridge lands in. -/
  K : Type*
  /-- `K` is a field. -/
  [instField : Field K]
  /-- The bridge to the genuine field. -/
  toK : α → K
  /-- `toK` sends `zero` to `0`. -/
  toK_zero : toK zero = 0
  /-- `toK` sends `one` to `1`. -/
  toK_one : toK one = 1
  /-- `toK` intertwines `add` with `+`. -/
  toK_add : ∀ a b, toK (add a b) = toK a + toK b
  /-- `toK` intertwines `mul` with `*`. -/
  toK_mul : ∀ a b, toK (mul a b) = toK a * toK b
  /-- `toK` intertwines `neg` with `-`. -/
  toK_neg : ∀ a, toK (neg a) = - toK a
  /-- `toK` intertwines `inv` with `⁻¹`. -/
  toK_inv : ∀ a, toK (inv a) = (toK a)⁻¹
  /-- `toK` is injective (the computable carrier faithfully represents `K`'s reachable elements). -/
  toK_injective : Function.Injective toK
  /-- `isZero a` is `true` iff `toK a = 0`. -/
  isZero_iff : ∀ a, isZero a = true ↔ toK a = 0

/-- Expose `Field (CField.K α)` as an instance so the genuine field structure resolves. -/
instance instFieldK (α : Type*) [CField α] : Field (CField.K α) := CField.instField

namespace CField

/-- **Computable subtraction** `a - b := a + (-b)`, derived from `add`/`neg`. -/
def sub {α : Type*} [CField α] (a b : α) : α := add a (neg b)

/-- **Computable division** `a / b := a * b⁻¹`, derived from `mul`/`inv`. -/
def div {α : Type*} [CField α] (a b : α) : α := mul a (inv b)

/-- `toK` intertwines derived `sub` with `-`. -/
theorem toK_sub {α : Type*} [CField α] (a b : α) : toK (sub a b) = toK a - toK b := by
  rw [sub, toK_add, toK_neg, sub_eq_add_neg]

/-- `toK` intertwines derived `div` with `/`. -/
theorem toK_div {α : Type*} [CField α] (a b : α) : toK (div a b) = toK a / toK b := by
  rw [div, toK_mul, toK_inv, div_eq_mul_inv]

end CField

/-! ### Instance: `CField ℚ`

`ℚ` is trivially a computable field over itself: `K = ℚ`, `toK = id`, every law `rfl`, `isZero` by
decidable equality. The simplest instance — and the one that validates the whole abstraction. -/

/-- **`CField ℚ`**: rationals as a computable field over `K = ℚ` with `toK = id`; all bridge laws are
`rfl` and `isZero a := decide (a = 0)`. -/
instance : CField ℚ where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  inv := (·⁻¹)
  isZero a := decide (a = 0)
  K := ℚ
  toK := id
  toK_zero := rfl
  toK_one := rfl
  toK_add _ _ := rfl
  toK_mul _ _ := rfl
  toK_neg _ := rfl
  toK_inv _ := rfl
  toK_injective := fun _ _ h => h
  isZero_iff a := by simp [id]

/-! ### Generic polynomial engine `CPolyG α := List α`

Over any `[CField α]` the dense-coefficient list `CPolyG α` (index = degree, low to high) carries the
same arithmetic as the concrete `CPoly = List ℚ`, with `ℚ` operations replaced by `CField.add`/`mul`/
`neg`/`isZero`. The generic Horner bridge `toPolyG : CPolyG α → (CField.K α)[X]` embeds via `toK`. -/

/-- **Generic dense coefficient list** over a computable field `α` (index = degree, low to high). -/
def CPolyG (α : Type*) := List α

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

/-! ### The generic Horner bridge `toPolyG` and its homomorphism lemmas -/

/-- **Generic bridge to `(CField.K α)[X]`**: `toPolyG p` reads a `CPolyG` coefficient list (index =
degree, low to high) as a `Polynomial (CField.K α)` in **Horner form** `p₀ + x·(p₁ + x·(p₂ + …))`,
each coefficient embedded via `toK`. -/
noncomputable def toPolyG : CPolyG α → (CField.K α)[X]
  | [] => 0
  | a :: p => Polynomial.C (CField.toK a) + X * toPolyG p

/-- `toPolyG [] = 0`: the empty coefficient list is the zero polynomial. -/
@[simp] theorem toPolyG_nil : toPolyG ([] : CPolyG α) = 0 := rfl

/-- `toPolyG`'s leading recursion (Horner): `toPolyG (a :: p) = C (toK a) + X · toPolyG p`. -/
@[simp] theorem toPolyG_cons (a : α) (p : CPolyG α) :
    toPolyG (a :: p) = Polynomial.C (CField.toK a) + X * toPolyG p := rfl

/-- `toPolyG` is **additive**: `caddG` realizes `(CField.K α)[X]` addition under the Horner bridge. -/
theorem toPolyG_caddG (p q : CPolyG α) : toPolyG (caddG p q) = toPolyG p + toPolyG q := by
  induction p generalizing q with
  | nil => simp [caddG]
  | cons a as ih =>
    cases q with
    | nil => simp [caddG]
    | cons b bs =>
      simp only [caddG, toPolyG_cons, ih bs, CField.toK_add, map_add]
      ring

/-- `toPolyG` commutes with **negation**: `toPolyG (cnegG p) = − toPolyG p`. -/
theorem toPolyG_cnegG (p : CPolyG α) : toPolyG (cnegG p) = - toPolyG p := by
  induction p with
  | nil => simp [cnegG]
  | cons a as ih =>
    show toPolyG (CField.neg a :: cnegG as) = -toPolyG (a :: as)
    rw [toPolyG_cons, toPolyG_cons, ih, CField.toK_neg, map_neg]; ring

/-- `toPolyG` realizes **subtraction**: `toPolyG (csubG p q) = toPolyG p − toPolyG q`. -/
theorem toPolyG_csubG (p q : CPolyG α) : toPolyG (csubG p q) = toPolyG p - toPolyG q := by
  rw [csubG, toPolyG_caddG, toPolyG_cnegG, sub_eq_add_neg]

/-- `toPolyG` realizes **scalar multiplication**: `toPolyG (cscaleG c p) = C (toK c) · toPolyG p`. -/
theorem toPolyG_cscaleG (c : α) (p : CPolyG α) :
    toPolyG (cscaleG c p) = Polynomial.C (CField.toK c) * toPolyG p := by
  induction p with
  | nil => simp [cscaleG]
  | cons a as ih =>
    show toPolyG (CField.mul c a :: cscaleG c as) = Polynomial.C (CField.toK c) * toPolyG (a :: as)
    rw [toPolyG_cons, toPolyG_cons, ih, CField.toK_mul, map_mul]; ring

/-- `toPolyG` realizes the **degree shift**: `toPolyG (cshiftG k p) = X^k · toPolyG p`. -/
theorem toPolyG_cshiftG (k : ℕ) (p : CPolyG α) : toPolyG (cshiftG k p) = X ^ k * toPolyG p := by
  induction k with
  | zero => simp [cshiftG]
  | succ n ih =>
    show toPolyG (CField.zero :: cshiftG n p) = X ^ (n + 1) * toPolyG p
    rw [toPolyG_cons, ih, CField.toK_zero, map_zero]; ring

/-- `toPolyG` is **multiplicative**: `cmulG` realizes `(CField.K α)[X]` multiplication. -/
theorem toPolyG_cmulG (p q : CPolyG α) : toPolyG (cmulG p q) = toPolyG p * toPolyG q := by
  induction p with
  | nil => simp [cmulG]
  | cons a as ih =>
    show toPolyG (caddG (cscaleG a q) (CField.zero :: cmulG as q)) = toPolyG (a :: as) * toPolyG q
    rw [toPolyG_caddG, toPolyG_cscaleG, toPolyG_cons, toPolyG_cons, ih, CField.toK_zero,
      map_zero]; ring

/-- `toPolyG` realizes the **`ℕ`-power**: `toPolyG (cpowG p n) = (toPolyG p) ^ n`. -/
theorem toPolyG_cpowG (p : CPolyG α) (n : ℕ) : toPolyG (cpowG p n) = (toPolyG p) ^ n := by
  induction n with
  | zero => simp [cpowG, toPolyG_cons, CField.toK_one]
  | succ n ih => rw [cpowG, toPolyG_cmulG, ih, pow_succ, mul_comm]

end CPolyG

end DeepWiki.SymbolicIntegration
