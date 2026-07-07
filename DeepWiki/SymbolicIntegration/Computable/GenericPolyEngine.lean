import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
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

/-- `toK` intertwines a `CField.add` fold with the corresponding field addition fold. -/
theorem toK_foldl_add {α : Type*} [CField α] [CFieldSpec α] (z : α) (L : List α) :
    toK (L.foldl CField.add z) = (L.map toK).foldl (· + ·) (toK z) := by
  induction L generalizing z with
  | nil => simp
  | cons a t ih => simp only [List.foldl_cons, List.map_cons, ih, CFieldSpec.toK_add]

/-- `toK` reads a `CField.zero`-defaulted list lookup through `List.map toK`. -/
theorem getD_map_toK {α : Type*} [CField α] [CFieldSpec α] (l : List α) (j : ℕ) :
    (l.map toK).getD j 0 = toK (l.getD j CField.zero) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[j]? with
  | none => simp [CFieldSpec.toK_zero]
  | some a => simp

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

/-- Pad a `CPolyG` on the high-degree end with zeros up to length `n`; no-op if length is already
at least `n`. -/
def cpadG {α : Type*} [CField α] (n : ℕ) (p : CPolyG α) : CPolyG α :=
  (p : List α) ++ List.replicate (n - (p : List α).length) CField.zero

/-- Reverse coefficients after zero-padding to degree bound `k`: `creverseDegG k p` represents
`X^k * p(X⁻¹)` when `k` bounds the degree of `p`. -/
def creverseDegG {α : Type*} [CField α] (k : ℕ) (p : CPolyG α) : CPolyG α :=
  (cpadG (k + 1) p).reverse

/-- Monomial `c * X^n` as a `CPolyG`: `n` low-degree zeros followed by coefficient `c`. -/
def cMonomialG {α : Type*} [CField α] (c : α) (n : ℕ) : CPolyG α :=
  (List.replicate n CField.zero ++ [c] : List α)

/-- The generic denominator fold `∏ acc·(zk − zⱼ)` reads through `toK` as
`toK init · ∏ (toK zk − toK zⱼ)`. -/
theorem toK_foldl_csub_mul {α : Type*} [CField α] [CFieldSpec α]
    (zk : α) (others : List α) (init : α) :
    CFieldSpec.toK (others.foldl (fun acc zj => CField.mul acc (CField.sub zk zj)) init)
      = CFieldSpec.toK init
        * (others.map (fun zj => CFieldSpec.toK zk - CFieldSpec.toK zj)).prod := by
  induction others generalizing init with
  | nil => simp
  | cons z zs ih =>
    rw [List.foldl_cons, ih, CFieldSpec.toK_mul, CFieldSpec.toK_sub, List.map_cons, List.prod_cons]
    ring

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

/-- `(cshiftG k p).length = k + p.length`. -/
theorem cshiftG_length {α : Type*} [CField α] (k : ℕ) (p : CPolyG α) :
    (cshiftG k p : List α).length = k + (p : List α).length := by
  induction k with
  | zero => simp [cshiftG]
  | succ m ih => rw [cshiftG]; simp only [List.length_cons, ih]; omega

/-- Polynomial multiplication of `CPolyG`s (schoolbook convolution via `cshiftG`/`cscaleG`). -/
def cmulG {α : Type*} [CField α] : CPolyG α → CPolyG α → CPolyG α
  | [], _ => []
  | a :: as, q => caddG (cscaleG a q) (CField.zero :: cmulG as q)

/-- Product of a list of `CPolyG`s, folding `cmulG` from `[1]`. -/
def cprodG {α : Type*} [CField α] (ps : List (CPolyG α)) : CPolyG α :=
  ps.foldl (fun acc p => cmulG acc p) [CField.one]

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

/-- Monic test for a `CPolyG`: `true` iff `cmonicG p = p` as normalized lists. -/
def cisMonicG {α : Type*} [CField α] (p : CPolyG α) : Bool := cisZeroG (csubG (cmonicG p) p)

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

/-! ### Generic formal derivative `cderivG` over a `CField` -/

/-- Generic `ℕ`-scaling `nsmulG k a = a + a + … + a` (`k` times), built from `CField.add`. -/
def nsmulG {α : Type*} [CField α] : ℕ → α → α
  | 0, _ => CField.zero
  | k + 1, a => CField.add a (nsmulG k a)

/-- `toK (nsmulG k a) = k • toK a` in `K`. -/
@[denote] theorem toK_nsmulG {α : Type*} [CField α] [CFieldSpec α] (k : ℕ) (a : α) :
    CFieldSpec.toK (nsmulG k a) = k • CFieldSpec.toK a := by
  induction k with
  | zero => rw [nsmulG, CFieldSpec.toK_zero, zero_smul]
  | succ n ih => rw [nsmulG, CFieldSpec.toK_add, ih, succ_nsmul']

/-- Generic formal derivative `cderivG [a₀,a₁,a₂,…] = [1·a₁, 2·a₂, 3·a₃, …]`. -/
def cderivG {α : Type*} [CField α] : CPolyG α → CPolyG α
  | [] => []
  | _ :: as => go 1 as
where
  /-- Auxiliary: from degree `k`, emit `nsmulG k a` for each coefficient `a` (the derivative tail). -/
  go : ℕ → CPolyG α → CPolyG α
  | _, [] => []
  | k, a :: as => nsmulG k a :: go (k + 1) as

/-- `cderivG` realizes the `K[X]` derivative: `toPolyG (cderivG p) = Polynomial.derivative (toPolyG p)`. -/
@[denote] theorem toPolyG_cderivG {α : Type*} [CField α] [CFieldSpec α] (p : CPolyG α) :
    toPolyG (cderivG p) = Polynomial.derivative (toPolyG p) := by
  suffices h : ∀ (as : CPolyG α) (k : ℕ),
      toPolyG (cderivG.go k as)
        = (k : (CFieldSpec.K α)[X]) * toPolyG as + X * Polynomial.derivative (toPolyG as) by
    cases p with
    | nil => simp [cderivG]
    | cons a as =>
      show toPolyG (cderivG.go 1 as) = Polynomial.derivative (toPolyG (a :: as))
      rw [h as 1, toPolyG_cons, derivative_add, derivative_C, derivative_mul, derivative_X]
      push_cast; ring
  intro as
  induction as with
  | nil => intro k; simp [cderivG.go]
  | cons b bs ih =>
    intro k
    show toPolyG (nsmulG k b :: cderivG.go (k + 1) bs) = _
    rw [toPolyG_cons, ih (k + 1), toPolyG_cons, derivative_add, derivative_C, derivative_mul,
      derivative_X]
    have hk : Polynomial.C (CFieldSpec.toK (nsmulG k b)) = (k : (CFieldSpec.K α)[X]) * Polynomial.C (CFieldSpec.toK b) := by
      rw [toK_nsmulG, nsmul_eq_mul, map_mul, map_natCast]
    rw [hk]; push_cast; ring

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

/-- `cleadG` is invariant under `cnormG`: `cleadG (cnormG p) = cleadG p`. -/
theorem cleadG_cnormG {α : Type*} [CField α] (p : CPolyG α) : cleadG (cnormG p) = cleadG p := by
  simp only [cleadG, cnormG_idem]

/-- `cisZeroG` is invariant under `cnormG`. -/
theorem cisZeroG_cnormG {α : Type*} [CField α] (q : CPolyG α) : cisZeroG (cnormG q) = cisZeroG q := by
  simp only [cisZeroG, cnormG_idem]

/-- `cdegG` is invariant under `cnormG`. -/
theorem cdegG_cnormG {α : Type*} [CField α] (p : CPolyG α) : cdegG (cnormG p) = cdegG p := by
  simp only [cdegG, cnormG_idem]

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

/-- `toPolyG` of a coefficient list is its dense polynomial `∑ i, C(toK cᵢ) * X^i`. -/
theorem toPolyG_eq_sum_range {α : Type*} [CField α] [CFieldSpec α] (l : CPolyG α) :
    toPolyG l =
      ∑ i ∈ Finset.range l.length, C (CFieldSpec.toK ((l : List α).getD i CField.zero)) * X ^ i := by
  induction l with
  | nil => simp
  | cons a p ih =>
    rw [toPolyG_cons, List.length_cons, Finset.sum_range_succ', ih, Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

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

/-- For a nonzero generic polynomial, the normalized list length is `natDegree + 1`. -/
theorem length_cnormG_of_ne {α : Type*} [CField α] [CFieldSpec α] (p : CPolyG α)
    (h : cnormG p ≠ []) :
    (cnormG p : List α).length = (toPolyG p).natDegree + 1 := by
  have hd := cdegG_eq_natDegree p
  rw [cdegG] at hd
  have hlen : 1 ≤ (cnormG p : List α).length := List.length_pos_iff.mpr h
  omega

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

/-- Monic-normalization is a unit-scaling: `toPolyG (cmonicG p)` is associated to `toPolyG p` in `K[X]`. -/
theorem associated_toPolyG_cmonicG {α : Type*} [CField α] [CFieldSpec α] (p : CPolyG α) :
    Associated (toPolyG (cmonicG p)) (toPolyG p) := by
  rw [cmonicG]
  split_ifs with h
  · rw [toPolyG_nil]
    have hz : toPolyG p = 0 := (cisZeroG_iff p).mp (by rwa [cisZeroG_cnormG] at h)
    rw [hz]
  · rw [toPolyG_cscaleG, toPolyG_cnormG]
    have hne : cnormG (cnormG p) ≠ [] := by
      rw [cnormG_idem]; intro he
      exact h (by rw [cisZeroG_cnormG, cisZeroG_iff, ← toPolyG_cnormG, he, toPolyG_nil])
    exact associated_unit_mul_left _ _
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr
        (by rw [CFieldSpec.toK_inv]; exact inv_ne_zero (toK_cleadG_ne_zero hne))))

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
