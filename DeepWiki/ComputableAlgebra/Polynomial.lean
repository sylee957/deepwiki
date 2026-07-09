import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.Polynomial.Basic
import DeepWiki.Transfer.Denote

/-! # A generic computable field, and a polynomial engine over it

`CField α`: computable field operations (`zero`/`one`/`add`/`mul`/`neg`/`inv`, zero test) that
reduce, with meaning supplied by a companion `CFieldSpec` homomorphism `toK : α → K` into a Mathlib
`Field K`. Over any `CField`, generic scalar powers and a dense polynomial engine
`CPoly α := List α` provide computable arithmetic with a Horner bridge
`toPoly : CPoly α → (CFieldSpec.K α)[X]`. -/

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

/-! ### The `CCommRing` typeclass (computable commutative-ring operations)

`CCommRing α` is the ring fragment of `CField` (no `inv`): the coefficient constraint the ring-generic
polynomial engine actually needs (20 of the 21 core `c*` ops use only these). Every `CField` is a
`CCommRing` (bridge instance below), and a `CPoly` over a `CCommRing` is itself a `CCommRing`, so
bivariate polynomials are just `CPoly (CPoly _)`. See `docs/ring-generalization-plan.md`. -/

/-- Computable commutative-ring operations: `zero`/`one`/`add`/`mul`/`neg` and a zero test `isZero`;
bridge-free, so instances reduce in the native compiler (`native_decide`). -/
class CCommRing (α : Type*) where
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
  /-- Computable zero test. -/
  isZero : α → Bool

namespace CCommRing

/-- Computable subtraction `a - b := a + (-b)`, derived from `add`/`neg`. -/
def sub {α : Type*} [CCommRing α] (a b : α) : α := add a (neg b)

end CCommRing

/-- Every computable field is a computable commutative ring (forget `inv`). Bridge instance: makes
`[CCommRing α]` available at every `[CField α]` type, so ring-generic engine ops resolve on field
coefficients unchanged. -/
instance (priority := 100) instCCommRingOfCField {α : Type*} [CField α] : CCommRing α where
  zero := CField.zero
  one := CField.one
  add := CField.add
  mul := CField.mul
  neg := CField.neg
  isZero := CField.isZero

/-- Computable-commutative-ring specification: the bridge `toR : α → R` into a Mathlib `CommRing R`
intertwining `zero`/`one`/`add`/`mul`/`neg`, plus `isZero_iff`. The ring analogue of `CFieldSpec`; the
ring-generic denotation `toPoly : CPoly α → (CRingSpec.R α)[X]` lands in this `CommRing`. -/
class CRingSpec (α : Type*) [CCommRing α] where
  /-- The genuine Mathlib commutative ring the bridge lands in. -/
  R : Type*
  /-- `R` is a commutative ring. -/
  [instCommRing : CommRing R]
  /-- The bridge to the genuine ring. -/
  toR : α → R
  /-- `toR` sends `zero` to `0`. -/
  toR_zero : toR CCommRing.zero = 0
  /-- `toR` sends `one` to `1`. -/
  toR_one : toR CCommRing.one = 1
  /-- `toR` intertwines `add` with `+`. -/
  toR_add : ∀ a b, toR (CCommRing.add a b) = toR a + toR b
  /-- `toR` intertwines `mul` with `*`. -/
  toR_mul : ∀ a b, toR (CCommRing.mul a b) = toR a * toR b
  /-- `toR` intertwines `neg` with `-`. -/
  toR_neg : ∀ a, toR (CCommRing.neg a) = - toR a
  /-- `isZero a` is `true` iff `toR a = 0`. -/
  isZero_iff : ∀ a, CCommRing.isZero a = true ↔ toR a = 0

/-- Expose `CommRing (CRingSpec.R α)` so the polynomial ring `(CRingSpec.R α)[X]` resolves. -/
instance (priority := 50) instCommRingR (α : Type*) [CCommRing α] [CRingSpec α] :
    CommRing (CRingSpec.R α) :=
  CRingSpec.instCommRing

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

/-- Every `[CFieldSpec α]` is a `CRingSpec α`: the field bridge is a ring bridge with `R := K`. The hom
laws transfer by defeq through the `CField ⇒ CCommRing` bridge, so `CRingSpec.R α = CFieldSpec.K α` and
ring-level denotation squares (over `CRingSpec.R`) agree with field-level ones (over `CFieldSpec.K`) on
field coefficients. -/
instance (priority := 100) instCRingSpecOfCFieldSpec {α : Type*} [CField α] [CFieldSpec α] :
    CRingSpec α where
  R := CFieldSpec.K α
  toR := CFieldSpec.toK
  toR_zero := CFieldSpec.toK_zero
  toR_one := CFieldSpec.toK_one
  toR_add := CFieldSpec.toK_add
  toR_mul := CFieldSpec.toK_mul
  toR_neg := CFieldSpec.toK_neg
  isZero_iff := CFieldSpec.isZero_iff

/-- On a field coefficient the ring bridge IS the field bridge (`R = K`, `toR = toK`), by defeq. -/
@[simp, denote] theorem toR_eq_toK {α : Type*} [CField α] [CFieldSpec α] (a : α) :
    CRingSpec.toR a = CFieldSpec.toK a := rfl

/-! ### Field-path element normalizers
The ring-generic engine ops emit `CCommRing.zero`/`one`/… (from the weakened `[CCommRing]` definitions);
on a field coefficient these are defeq to the `CField` operations, so these `@[simp]` lemmas normalize
them back to the `CField` head that field-path call sites and their satellite lemmas are phrased in. -/

/-- Field-path: `CCommRing.zero = CField.zero`. -/
@[simp] theorem ccrZero_eq_cfield {α : Type*} [CField α] : (CCommRing.zero : α) = CField.zero := rfl
/-- Field-path: `CCommRing.one = CField.one`. -/
@[simp] theorem ccrOne_eq_cfield {α : Type*} [CField α] : (CCommRing.one : α) = CField.one := rfl
/-- Field-path: `CCommRing.add = CField.add`. -/
@[simp] theorem ccrAdd_eq_cfield {α : Type*} [CField α] (a b : α) :
    CCommRing.add a b = CField.add a b := rfl
/-- Field-path: `CCommRing.mul = CField.mul`. -/
@[simp] theorem ccrMul_eq_cfield {α : Type*} [CField α] (a b : α) :
    CCommRing.mul a b = CField.mul a b := rfl
/-- Field-path: `CCommRing.neg = CField.neg`. -/
@[simp] theorem ccrNeg_eq_cfield {α : Type*} [CField α] (a : α) :
    CCommRing.neg a = CField.neg a := rfl

/-- `CRingSpec.R α = CFieldSpec.K α`, a `Field`, so field-level squares over the ring-generic
`toPoly : CPoly α → (CRingSpec.R α)[X]` find `⁻¹`/`GroupWithZero` on the field path. -/
instance (priority := 100) instFieldROfCFieldSpec {α : Type*} [CField α] [CFieldSpec α] :
    Field (CRingSpec.R α) := instFieldK α

-- The base `toK` homomorphism laws are the leaf denotation squares.
attribute [denote] CFieldSpec.toK_zero CFieldSpec.toK_one CFieldSpec.toK_add
  CFieldSpec.toK_mul CFieldSpec.toK_neg CFieldSpec.toK_inv
attribute [denote] CRingSpec.toR_zero CRingSpec.toR_one CRingSpec.toR_add
  CRingSpec.toR_mul CRingSpec.toR_neg

/-! ### `toK` homomorphism laws through the `CField ⇒ CCommRing` bridge
Ring-generic engine ops (`cadd`/`cmul`/… weakened to `[CCommRing]`) put `CCommRing.add`/… in goals; on a
field coefficient that is defeq to `CField.add`/…, so these `@[denote]` lemmas let the denotation squares
fire on the ring-op head. -/
@[denote] theorem toK_ccrZero {α : Type*} [CField α] [CFieldSpec α] :
    CFieldSpec.toK (CCommRing.zero : α) = 0 := CFieldSpec.toK_zero
@[denote] theorem toK_ccrOne {α : Type*} [CField α] [CFieldSpec α] :
    CFieldSpec.toK (CCommRing.one : α) = 1 := CFieldSpec.toK_one
@[denote] theorem toK_ccrAdd {α : Type*} [CField α] [CFieldSpec α] (a b : α) :
    CFieldSpec.toK (CCommRing.add a b) = CFieldSpec.toK a + CFieldSpec.toK b := CFieldSpec.toK_add a b
@[denote] theorem toK_ccrMul {α : Type*} [CField α] [CFieldSpec α] (a b : α) :
    CFieldSpec.toK (CCommRing.mul a b) = CFieldSpec.toK a * CFieldSpec.toK b := CFieldSpec.toK_mul a b
@[denote] theorem toK_ccrNeg {α : Type*} [CField α] [CFieldSpec α] (a : α) :
    CFieldSpec.toK (CCommRing.neg a) = - CFieldSpec.toK a := CFieldSpec.toK_neg a

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
@[denote] theorem toK_foldl_add {α : Type*} [CField α] [CFieldSpec α] (z : α) (L : List α) :
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

/-! ### The polynomial engine `CPoly α := List α`

Dense-coefficient lists (index = degree, low to high) over `[CField α]`, with arithmetic built from
the `CField` operations and a Horner bridge `toPoly` into `(CFieldSpec.K α)[X]`. -/

/-- Generic dense coefficient list over a computable field `α` (index = degree, low to high).
A reducible `abbrev` for `List α` so the `List` instances (`BEq`/`DecidableEq`/…) transfer and the
ℚ-specialization `CPoly ℚ := CPoly ℚ` stays defeq to `List ℚ`. -/
abbrev CPoly (α : Type*) := List α

namespace CPoly

/-- Pad a `CPoly` on the high-degree end with zeros up to length `n`; no-op if length is already
at least `n`. -/
def cpad {α : Type*} [CField α] (n : ℕ) (p : CPoly α) : CPoly α :=
  (p : List α) ++ List.replicate (n - (p : List α).length) CField.zero

/-- Reverse coefficients after zero-padding to degree bound `k`: `creverseDeg k p` represents
`X^k * p(X⁻¹)` when `k` bounds the degree of `p`. -/
def creverseDeg {α : Type*} [CField α] (k : ℕ) (p : CPoly α) : CPoly α :=
  (cpad (k + 1) p).reverse

/-- Monomial `c * X^n` as a `CPoly`: `n` low-degree zeros followed by coefficient `c`. -/
def cMonomial {α : Type*} [CField α] (c : α) (n : ℕ) : CPoly α :=
  (List.replicate n CField.zero ++ [c] : List α)

/-- Generic power of a field element: `cfpow c n = cⁿ` over `[CField α]` by `ℕ`-recursion. -/
def cfpow {α : Type*} [CField α] (c : α) : ℕ → α
  | 0 => CField.one
  | n + 1 => CField.mul c (cfpow c n)

/-- Horner evaluation `ceval p c = p(c)` for a dense coefficient list, low degree first. -/
def ceval {α : Type*} [CField α] (p : CPoly α) (c : α) : α :=
  (p : List α).foldr (fun coeff acc => CField.add coeff (CField.mul c acc)) CField.zero

/-- `toK (cfpow c n) = (toK c) ^ n`: generic constant power realizes the `K`-power. -/
@[denote] theorem toK_cfpow {α : Type*} [CField α] [CFieldSpec α] (c : α) (n : ℕ) :
    CFieldSpec.toK (cfpow c n) = (CFieldSpec.toK c) ^ n := by
  induction n with
  | zero => simp [cfpow, CFieldSpec.toK_one]
  | succ n ih => rw [cfpow, CFieldSpec.toK_mul, ih, pow_succ']

/-- The generic denominator fold `∏ acc·(zk − zⱼ)` reads through `toK` as
`toK init · ∏ (toK zk − toK zⱼ)`. -/
@[denote] theorem toK_foldl_csub_mul {α : Type*} [CField α] [CFieldSpec α]
    (zk : α) (others : List α) (init : α) :
    CFieldSpec.toK (others.foldl (fun acc zj => CField.mul acc (CField.sub zk zj)) init)
      = CFieldSpec.toK init
        * (others.map (fun zj => CFieldSpec.toK zk - CFieldSpec.toK zj)).prod := by
  induction others generalizing init with
  | nil => simp
  | cons z zs ih =>
    rw [List.foldl_cons, ih, CFieldSpec.toK_mul, CFieldSpec.toK_sub, List.map_cons, List.prod_cons]
    ring

/-- The product `∏_{zⱼ ∈ others}(toK zk − toK zⱼ)` is nonzero when every `toK zⱼ ≠ toK zk`. -/
theorem prodG_sub_ne_zero {α : Type*} [CField α] [CFieldSpec α] {zk : α} {others : List α}
    (hne : ∀ zj ∈ others, CFieldSpec.toK zj ≠ CFieldSpec.toK zk) :
    (others.map (fun zj => CFieldSpec.toK zk - CFieldSpec.toK zj)).prod ≠ 0 := by
  rw [Ne, List.prod_eq_zero_iff]
  intro hy
  rw [List.mem_map] at hy
  obtain ⟨zj, hzj, hzeq⟩ := hy
  exact hne zj hzj (sub_eq_zero.mp hzeq).symm

/-- Normalize a `CPoly` by stripping trailing (high-degree) zero coefficients (`isZero`-tested),
so `cnorm` is a canonical form (the zero polynomial becomes `[]`). -/
def cnorm {α : Type*} [CCommRing α] : CPoly α → CPoly α
  | [] => []
  | a :: as => match cnorm as with
    | [] => if CCommRing.isZero a then [] else [a]
    | r => a :: r

/-- Coefficientwise addition of two `CPoly`s (the shorter is zero-extended implicitly). -/
def cadd {α : Type*} [CCommRing α] : CPoly α → CPoly α → CPoly α
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => CCommRing.add a b :: cadd as bs

/-- Negation of a `CPoly`, coefficientwise. -/
def cneg {α : Type*} [CCommRing α] (p : CPoly α) : CPoly α := (p : List α).map CCommRing.neg

/-- Subtraction of `CPoly`s, `p − q := p + (−q)`. -/
def csub {α : Type*} [CCommRing α] (p q : CPoly α) : CPoly α := cadd p (cneg q)

/-- Scalar multiplication of a `CPoly` by `c : α`, coefficientwise. -/
def cscale {α : Type*} [CCommRing α] (c : α) (p : CPoly α) : CPoly α := (p : List α).map (CCommRing.mul c)

/-- Degree shift `cshift k p = x^k · p`: prepend `k` zero coefficients. -/
def cshift {α : Type*} [CCommRing α] : ℕ → CPoly α → CPoly α
  | 0, p => p
  | n + 1, p => CCommRing.zero :: cshift n p

/-- `(cshift k p).length = k + p.length`. -/
theorem cshiftG_length {α : Type*} [CField α] (k : ℕ) (p : CPoly α) :
    (cshift k p : List α).length = k + (p : List α).length := by
  induction k with
  | zero => simp [cshift]
  | succ m ih => rw [cshift]; simp only [List.length_cons, ih]; omega

/-- Polynomial multiplication of `CPoly`s (schoolbook convolution via `cshift`/`cscale`). -/
def cmul {α : Type*} [CCommRing α] : CPoly α → CPoly α → CPoly α
  | [], _ => []
  | a :: as, q => cadd (cscale a q) (CCommRing.zero :: cmul as q)

/-- Product of a list of `CPoly`s, folding `cmul` from `[1]`. -/
def cprod {α : Type*} [CCommRing α] (ps : List (CPoly α)) : CPoly α :=
  ps.foldl (fun acc p => cmul acc p) [CCommRing.one]

/-- Power of a `CPoly` by `ℕ`-recursion (`[1]` at `0`). -/
def cpow {α : Type*} [CCommRing α] (p : CPoly α) : ℕ → CPoly α
  | 0 => [CCommRing.one]
  | n + 1 => cmul p (cpow p n)

/-- Leading coefficient of a `CPoly` (top nonzero coefficient; `zero` for the zero polynomial). -/
def clead {α : Type*} [CCommRing α] (p : CPoly α) : α := ((cnorm p : List α).getLast?.getD CCommRing.zero)

/-- Degree of a `CPoly` as a `ℕ`: `(length of normalized p) − 1`, with `cdeg 0 = 0`. -/
def cdeg {α : Type*} [CCommRing α] (p : CPoly α) : ℕ := (cnorm p : List α).length - 1

/-- Zero test for a `CPoly`: `true` iff it normalizes to `[]`. -/
def cisZero {α : Type*} [CCommRing α] (p : CPoly α) : Bool := (cnorm p : List α).isEmpty

/-- **Keystone instance.** A `CPoly` over a computable commutative ring is itself a computable commutative
ring (`add := cadd`, `mul := cmul`, `neg := cneg`, `zero := []`, `one := [one]`, `isZero := cisZero`) — so
`CPoly (CPoly _)` is a valid coefficient tower and bivariate polynomials need no separate definition. All
ops reduce, so the tower stays `native_decide`-executable. See `docs/ring-generalization-plan.md`. -/
instance instCCommRingCPoly {α : Type*} [CCommRing α] : CCommRing (CPoly α) where
  zero := []
  one := [CCommRing.one]
  add := cadd
  mul := cmul
  neg := cneg
  isZero := cisZero

/-- Make a `CPoly` monic (lead coefficient `1`) by scaling by `(clead)⁻¹`; the zero polynomial
stays `[]`. -/
def cmonic {α : Type*} [CField α] (p : CPoly α) : CPoly α :=
  let p := cnorm p
  if cisZero p then [] else cscale (CField.inv (clead p)) p

/-- Monic test for a `CPoly`: `true` iff `cmonic p = p` as normalized lists. -/
def cisMonic {α : Type*} [CField α] (p : CPoly α) : Bool := cisZero (csub (cmonic p) p)

/-! ### The generic Horner bridge `toPoly` and its homomorphism lemmas

From here on the bridge `[CFieldSpec α]` is in scope: `toPoly` and every correctness lemma carry the
extra binder, while the engine ops above need only `[CField α]`. -/

/-- Generic bridge to `(CFieldSpec.K α)[X]`: `toPoly p` reads a `CPoly` coefficient list (index =
degree, low to high) as a `Polynomial (CFieldSpec.K α)` in Horner form `p₀ + x·(p₁ + x·(p₂ + …))`,
each coefficient embedded via `toK`. -/
noncomputable def toPoly {α : Type*} [CCommRing α] [CRingSpec α] : CPoly α → (CRingSpec.R α)[X]
  | [] => 0
  | a :: p => Polynomial.C (CRingSpec.toR a) + X * toPoly p

/-- `toPoly [] = 0`: the empty coefficient list is the zero polynomial. -/
@[simp, denote] theorem toPolyG_nil {α : Type*} [CCommRing α] [CRingSpec α] :
    toPoly ([] : CPoly α) = 0 := rfl

/-- `toPoly`'s leading recursion (Horner): `toPoly (a :: p) = C (toK a) + X · toPoly p`. -/
@[simp, denote] theorem toPolyG_cons {α : Type*} [CCommRing α] [CRingSpec α] (a : α) (p : CPoly α) :
    toPoly (a :: p) = Polynomial.C (CRingSpec.toR a) + X * toPoly p := rfl

/-- `toPoly [CField.one] = 1`: the singleton coefficient list `[1]` reads as the polynomial `1`. -/
@[denote] theorem toPolyG_one_singleton {α : Type*} [CCommRing α] [CRingSpec α] :
    toPoly ([CCommRing.one] : CPoly α) = 1 := by
  rw [toPolyG_cons, toPolyG_nil, mul_zero, add_zero, CRingSpec.toR_one, map_one]

/-- `toPoly [CField.one] ≠ 0`: the singleton coefficient list `[1]` reads nontrivially. -/
theorem toPolyG_one_singleton_ne_zero {α : Type*} [CField α] [CFieldSpec α] :
    toPoly ([CField.one] : CPoly α) ≠ 0 := by
  simp only [denote, map_one, mul_zero, add_zero]
  exact (one_ne_zero : (1 : Polynomial (CFieldSpec.K α)) ≠ 0)

/-- `toPoly` is additive: `cadd` realizes `(CFieldSpec.K α)[X]` addition under the Horner bridge. -/
@[simp, denote] theorem toPolyG_caddG {α : Type*} [CCommRing α] [CRingSpec α] (p q : CPoly α) :
    toPoly (cadd p q) = toPoly p + toPoly q := by
  induction p generalizing q with
  | nil => simp [cadd]
  | cons a as ih =>
    cases q with
    | nil => simp [cadd]
    | cons b bs =>
      simp only [cadd, ih bs, denote, map_add]
      ring

/-- `toPoly` of a `cadd` fold is the running sum of the term images. -/
@[denote] theorem toPolyG_foldl_caddG {α : Type*} [CCommRing α] [CRingSpec α]
    (f : α × α → CPoly α) (pts : List (α × α)) (init : CPoly α) :
    toPoly (pts.foldl (fun acc p => cadd acc (f p)) init)
      = toPoly init + (pts.map (fun p => toPoly (f p))).sum := by
  induction pts generalizing init with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons, ih]
    simp only [denote, List.map_cons, List.sum_cons]
    ring

/-- `toPoly` commutes with negation: `toPoly (cneg p) = − toPoly p`. -/
@[simp, denote] theorem toPolyG_cnegG {α : Type*} [CCommRing α] [CRingSpec α] (p : CPoly α) :
    toPoly (cneg p) = - toPoly p := by
  induction p with
  | nil => simp [cneg]
  | cons a as ih =>
    show toPoly (CCommRing.neg a :: cneg as) = -toPoly (a :: as)
    simp only [denote, ih, map_neg]; ring

/-- `toPoly` realizes subtraction: `toPoly (csub p q) = toPoly p − toPoly q`. -/
@[simp, denote] theorem toPolyG_csubG {α : Type*} [CCommRing α] [CRingSpec α] (p q : CPoly α) :
    toPoly (csub p q) = toPoly p - toPoly q := by
  rw [csub]
  simp only [denote, sub_eq_add_neg]

/-- `toPoly` realizes scalar multiplication: `toPoly (cscale c p) = C (toK c) · toPoly p`. -/
@[simp, denote] theorem toPolyG_cscaleG {α : Type*} [CCommRing α] [CRingSpec α] (c : α) (p : CPoly α) :
    toPoly (cscale c p) = Polynomial.C (CRingSpec.toR c) * toPoly p := by
  induction p with
  | nil => simp [cscale]
  | cons a as ih =>
    show toPoly (CCommRing.mul c a :: cscale c as) = Polynomial.C (CRingSpec.toR c) * toPoly (a :: as)
    simp only [denote, ih, map_mul]; ring

/-- `toPoly` realizes the degree shift: `toPoly (cshift k p) = X^k · toPoly p`. -/
@[simp, denote] theorem toPolyG_cshiftG {α : Type*} [CCommRing α] [CRingSpec α] (k : ℕ) (p : CPoly α) :
    toPoly (cshift k p) = X ^ k * toPoly p := by
  induction k with
  | zero => simp [cshift]
  | succ n ih =>
    show toPoly (CCommRing.zero :: cshift n p) = X ^ (n + 1) * toPoly p
    simp only [denote, ih, map_zero]; ring

/-- `toPoly` is multiplicative: `cmul` realizes `(CFieldSpec.K α)[X]` multiplication. -/
@[simp, denote] theorem toPolyG_cmulG {α : Type*} [CCommRing α] [CRingSpec α] (p q : CPoly α) :
    toPoly (cmul p q) = toPoly p * toPoly q := by
  induction p with
  | nil => simp [cmul]
  | cons a as ih =>
    show toPoly (cadd (cscale a q) (CCommRing.zero :: cmul as q)) = toPoly (a :: as) * toPoly q
    simp only [denote, ih, map_zero]; ring

/-- `toPoly` realizes the `ℕ`-power: `toPoly (cpow p n) = (toPoly p) ^ n`. -/
@[simp, denote] theorem toPolyG_cpowG {α : Type*} [CCommRing α] [CRingSpec α] (p : CPoly α) (n : ℕ) :
    toPoly (cpow p n) = (toPoly p) ^ n := by
  induction n with
  | zero => simp [cpow, denote]
  | succ n ih =>
    rw [cpow]
    simp only [denote, ih, pow_succ, mul_comm]

/-! ### Generic formal derivative `cderiv` over a `CField` -/

/-- Generic `ℕ`-scaling `cnsmul k a = a + a + … + a` (`k` times), built from `CField.add`. -/
def cnsmul {α : Type*} [CField α] : ℕ → α → α
  | 0, _ => CField.zero
  | k + 1, a => CField.add a (cnsmul k a)

/-- `toK (cnsmul k a) = k • toK a` in `K`. -/
@[denote] theorem toK_nsmulG {α : Type*} [CField α] [CFieldSpec α] (k : ℕ) (a : α) :
    CFieldSpec.toK (cnsmul k a) = k • CFieldSpec.toK a := by
  induction k with
  | zero => rw [cnsmul, CFieldSpec.toK_zero, zero_smul]
  | succ n ih => rw [cnsmul, CFieldSpec.toK_add, ih, succ_nsmul']

/-- Generic formal derivative `cderiv [a₀,a₁,a₂,…] = [1·a₁, 2·a₂, 3·a₃, …]`. -/
def cderiv {α : Type*} [CField α] : CPoly α → CPoly α
  | [] => []
  | _ :: as => go 1 as
where
  /-- Auxiliary: from degree `k`, emit `cnsmul k a` for each coefficient `a` (the derivative tail). -/
  go : ℕ → CPoly α → CPoly α
  | _, [] => []
  | k, a :: as => cnsmul k a :: go (k + 1) as

/-- `cderiv` realizes the `K[X]` derivative: `toPoly (cderiv p) = Polynomial.derivative (toPoly p)`. -/
@[denote] theorem toPolyG_cderivG {α : Type*} [CField α] [CFieldSpec α] (p : CPoly α) :
    toPoly (cderiv p) = Polynomial.derivative (toPoly p) := by
  suffices h : ∀ (as : CPoly α) (k : ℕ),
      toPoly (cderiv.go k as)
        = (k : (CFieldSpec.K α)[X]) * toPoly as + X * Polynomial.derivative (toPoly as) by
    cases p with
    | nil => simp [cderiv]
    | cons a as =>
      show toPoly (cderiv.go 1 as) = Polynomial.derivative (toPoly (a :: as))
      rw [h as 1, toPolyG_cons, derivative_add, derivative_C, derivative_mul, derivative_X]
      push_cast; ring
  intro as
  induction as with
  | nil => intro k; simp [cderiv.go]
  | cons b bs ih =>
    intro k
    show toPoly (cnsmul k b :: cderiv.go (k + 1) bs) = _
    rw [toPolyG_cons, ih (k + 1), toPolyG_cons, derivative_add, derivative_C, derivative_mul,
      derivative_X]
    simp only [toR_eq_toK]
    have hk : Polynomial.C (CFieldSpec.toK (cnsmul k b)) = (k : (CFieldSpec.K α)[X]) * Polynomial.C (CFieldSpec.toK b) := by
      rw [toK_nsmulG, nsmul_eq_mul, map_mul, map_natCast]
    rw [hk]; push_cast; ring

/-! ### Normalization, degree, leading coefficient — generic correctness -/

/-- `cnorm [] = []`. -/
@[simp] theorem cnormG_nil {α : Type*} [CCommRing α] : cnorm ([] : CPoly α) = [] := rfl

/-- `cnorm` on a cons cell, unfolded to its defining `match` (definitional). -/
theorem cnormG_cons_eq {α : Type*} [CCommRing α] (a : α) (as : CPoly α) :
    cnorm (a :: as)
      = (match cnorm as with | [] => if CCommRing.isZero a then [] else [a] | r => a :: r) := rfl

/-- `cnorm` is idempotent: stripping trailing zeros twice is the same as once. -/
@[simp] theorem cnormG_idem {α : Type*} [CCommRing α] (p : CPoly α) : cnorm (cnorm p) = cnorm p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [cnormG_cons_eq]
    cases h : cnorm as with
    | nil => cases ha : CCommRing.isZero a <;> simp [cnormG_cons_eq, ha]
    | cons b bs =>
      rw [h] at ih
      simp only [cnormG_cons_eq, ih]

/-- `clead` is invariant under `cnorm`: `clead (cnorm p) = clead p`. -/
theorem cleadG_cnormG {α : Type*} [CCommRing α] (p : CPoly α) : clead (cnorm p) = clead p := by
  simp only [clead, cnormG_idem]

/-- `cisZero` is invariant under `cnorm`. -/
theorem cisZeroG_cnormG {α : Type*} [CCommRing α] (q : CPoly α) : cisZero (cnorm q) = cisZero q := by
  simp only [cisZero, cnormG_idem]

/-- `cdeg` is invariant under `cnorm`. -/
theorem cdegG_cnormG {α : Type*} [CCommRing α] (p : CPoly α) : cdeg (cnorm p) = cdeg p := by
  simp only [cdeg, cnormG_idem]

/-- `toPoly` ignores normalization: `toPoly (cnorm p) = toPoly p` — stripping trailing zeros
does not change the polynomial (the dropped coefficients are zero, via `isZero_iff`). -/
@[simp, denote] theorem toPolyG_cnormG {α : Type*} [CCommRing α] [CRingSpec α] (p : CPoly α) :
    toPoly (cnorm p) = toPoly p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [cnormG_cons_eq]
    cases h : cnorm as with
    | nil =>
      rw [h] at ih
      simp only [toPolyG_nil] at ih
      have has : toPoly as = 0 := ih.symm
      cases ha : CCommRing.isZero a with
      | true =>
        have ha0 : CRingSpec.toR a = 0 := (CRingSpec.isZero_iff a).mp ha
        rw [if_pos rfl, toPolyG_nil, toPolyG_cons, has, mul_zero, add_zero, ha0, map_zero]
      | false =>
        rw [if_neg (by simp), toPolyG_cons, toPolyG_nil, mul_zero, add_zero, toPolyG_cons, has,
          mul_zero, add_zero]
    | cons b bs =>
      rw [h] at ih
      simp only [toPolyG_cons, ih]

/-- Coefficient read: the `i`-th coefficient of `toPoly p` is `toK` of the `i`-th list entry
(`0` past the end). The Horner bridge realizes the dense coefficient list exactly. -/
theorem toPolyG_coeff {α : Type*} [CCommRing α] [CRingSpec α] (p : CPoly α) (i : ℕ) :
    (toPoly p).coeff i = CRingSpec.toR ((p : List α).getD i CCommRing.zero) := by
  induction p generalizing i with
  | nil => simp [CRingSpec.toR_zero]
  | cons a as ih =>
    rw [toPolyG_cons]
    cases i with
    | zero => simp [coeff_C]
    | succ n => simp [coeff_X_mul, ih]

/-- `toPoly` of a coefficient list is its dense polynomial `∑ i, C(toK cᵢ) * X^i`. -/
theorem toPolyG_eq_sum_range {α : Type*} [CCommRing α] [CRingSpec α] (l : CPoly α) :
    toPoly l =
      ∑ i ∈ Finset.range l.length, C (CRingSpec.toR ((l : List α).getD i CCommRing.zero)) * X ^ i := by
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

/-- `toK` reads a normalized coefficient as the corresponding coefficient of `toPoly p`. -/
theorem toR_cnormG_getD {α : Type*} [CCommRing α] [CRingSpec α] (p : CPoly α) (k : ℕ) :
    CRingSpec.toR ((cnorm p : List α).getD k CCommRing.zero) = (toPoly p).coeff k := by
  rw [← toPolyG_coeff, toPolyG_cnormG]

/-- `cnorm` has no trailing zero: `(cnorm p).getLast?` is never a zero coefficient. -/
theorem cnormG_getLast?_ne_some_zero {α : Type*} [CCommRing α] (p : CPoly α) :
    ∀ v, (cnorm p : List α).getLast? = some v → CCommRing.isZero v = false := by
  induction p with
  | nil => simp
  | cons a as ih =>
    rw [cnormG_cons_eq]
    cases h : cnorm as with
    | nil =>
      cases ha : CCommRing.isZero a with
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

/-- For a normalized nonzero `CPoly`, the leading coefficient `clead` is nonzero (in `K`). -/
theorem toR_cleadG_ne_zero {α : Type*} [CCommRing α] [CRingSpec α] {p : CPoly α} (h : cnorm p ≠ []) :
    CRingSpec.toR (clead p) ≠ 0 := by
  rw [clead]
  rcases hl : (cnorm p : List α).getLast? with _ | v
  · exact absurd (List.getLast?_eq_none_iff.mp hl) h
  · simp only [Option.getD_some]
    intro hv
    have := cnormG_getLast?_ne_some_zero p v hl
    rw [(CRingSpec.isZero_iff v).mpr hv] at this
    exact absurd this (by simp)

/-- `clead` is the coefficient at the top index: `toK (clead p) = (toPoly p).coeff (cdeg p)`. -/
theorem toR_cleadG_eq_coeff {α : Type*} [CCommRing α] [CRingSpec α] (p : CPoly α) :
    CRingSpec.toR (clead p) = (toPoly p).coeff (cdeg p) := by
  rw [clead, cdeg, ← toPolyG_cnormG, toPolyG_coeff, List.getD_eq_getElem?_getD,
    ← List.getLast?_eq_getElem?]

/-- Degree bound: `natDegree (toPoly p) ≤ (cnorm p).length − 1`. -/
theorem natDegree_toPolyG_le {α : Type*} [CCommRing α] [CRingSpec α] (p : CPoly α) :
    (toPoly p).natDegree ≤ (cnorm p : List α).length - 1 := by
  rw [← toPolyG_cnormG]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [toPolyG_coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none,
    CRingSpec.toR_zero]

/-- `cdeg` is the honest `natDegree`: `cdeg p = (toPoly p).natDegree`. -/
theorem cdegG_eq_natDegree {α : Type*} [CCommRing α] [CRingSpec α] (p : CPoly α) :
    cdeg p = (toPoly p).natDegree := by
  rcases eq_or_ne (cnorm p) [] with h | h
  · have h0 : toPoly p = 0 := by rw [← toPolyG_cnormG, h, toPolyG_nil]
    rw [cdeg, h, h0]; simp
  · refine le_antisymm ?_ (natDegree_toPolyG_le p)
    apply Polynomial.le_natDegree_of_ne_zero
    rw [← toR_cleadG_eq_coeff]
    exact toR_cleadG_ne_zero h

/-- For a nonzero generic polynomial, the normalized list length is `natDegree + 1`. -/
theorem length_cnormG_of_ne {α : Type*} [CCommRing α] [CRingSpec α] (p : CPoly α)
    (h : cnorm p ≠ []) :
    (cnorm p : List α).length = (toPoly p).natDegree + 1 := by
  have hd := cdegG_eq_natDegree p
  rw [cdeg] at hd
  have hlen : 1 ≤ (cnorm p : List α).length := List.length_pos_iff.mpr h
  omega

/-- `toK (clead p)` is the honest `leadingCoeff`: `toK (clead p) = (toPoly p).leadingCoeff`. -/
theorem toR_cleadG_eq_leadingCoeff {α : Type*} [CCommRing α] [CRingSpec α] (p : CPoly α) :
    CRingSpec.toR (clead p) = (toPoly p).leadingCoeff := by
  rw [Polynomial.leadingCoeff, ← cdegG_eq_natDegree, ← toR_cleadG_eq_coeff]

/-! ### Field-path `toK` aliases of the `toR` clead/coeff readings
On a field coefficient the ring bridge is the field bridge (`toR = toK`, by defeq), so these expose the
same readings phrased with `CFieldSpec.toK` for the field-only call sites. -/

/-- Field-path alias: `toK` reads a normalized coefficient as the corresponding `toPoly` coefficient. -/
theorem toK_cnormG_getD {α : Type*} [CField α] [CFieldSpec α] (p : CPoly α) (k : ℕ) :
    CFieldSpec.toK ((cnorm p : List α).getD k CField.zero) = (toPoly p).coeff k :=
  toR_cnormG_getD p k

/-- Field-path alias: `toK (clead p) = (toPoly p).coeff (cdeg p)`. -/
theorem toK_cleadG_eq_coeff {α : Type*} [CField α] [CFieldSpec α] (p : CPoly α) :
    CFieldSpec.toK (clead p) = (toPoly p).coeff (cdeg p) :=
  toR_cleadG_eq_coeff p

/-- Field-path alias: `toK (clead p) = (toPoly p).leadingCoeff`. -/
theorem toK_cleadG_eq_leadingCoeff {α : Type*} [CField α] [CFieldSpec α] (p : CPoly α) :
    CFieldSpec.toK (clead p) = (toPoly p).leadingCoeff :=
  toR_cleadG_eq_leadingCoeff p

/-- `cnorm p = []` iff `toPoly p = 0` (the list normalizes to empty exactly for the zero
polynomial). -/
theorem cnormG_eq_nil_iff {α : Type*} [CCommRing α] [CRingSpec α] (p : CPoly α) :
    cnorm p = [] ↔ toPoly p = 0 := by
  constructor
  · intro h; rw [← toPolyG_cnormG, h, toPolyG_nil]
  · intro h
    by_contra hne
    have hcl := toR_cleadG_ne_zero hne
    rw [toR_cleadG_eq_leadingCoeff, h, Polynomial.leadingCoeff_zero] at hcl
    exact hcl rfl

/-- `length (cnorm p) < length (cnorm q)` (with `cnorm q ≠ []`) gives
`deg (toPoly p) < deg (toPoly q)`. -/
theorem toPolyG_degree_lt_of_length_lt {α : Type*} [CCommRing α] [CRingSpec α] (p q : CPoly α)
    (hq : cnorm q ≠ []) (hlen : (cnorm p : List α).length < (cnorm q : List α).length) :
    (toPoly p).degree < (toPoly q).degree := by
  have hq0 : toPoly q ≠ 0 := fun h => hq ((cnormG_eq_nil_iff q).mpr h)
  rcases eq_or_ne (cnorm p) [] with hp | hp
  · rw [(cnormG_eq_nil_iff p).mp hp, Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr (by rwa [Ne, Polynomial.degree_eq_bot])
  · have hp0 : toPoly p ≠ 0 := fun h => hp ((cnormG_eq_nil_iff p).mpr h)
    rw [Polynomial.degree_eq_natDegree hp0, Polynomial.degree_eq_natDegree hq0, Nat.cast_lt,
      ← cdegG_eq_natDegree, ← cdegG_eq_natDegree, cdeg, cdeg]
    have hplen : 1 ≤ (cnorm p : List α).length := List.length_pos_iff.mpr hp
    have hqlen : 1 ≤ (cnorm q : List α).length := List.length_pos_iff.mpr hq
    omega

/-- `cisZero` reads as `toPoly = 0`: `cisZero p = true ↔ toPoly p = 0`. -/
theorem cisZeroG_iff {α : Type*} [CCommRing α] [CRingSpec α] (p : CPoly α) :
    cisZero p = true ↔ toPoly p = 0 := by
  rw [cisZero, ← cnormG_eq_nil_iff]
  exact (List.isEmpty_iff (l := (cnorm p : List α)))

/-- `cisZero p = false` gives `toPoly p ≠ 0`. -/
theorem toPolyG_ne_zero_of_cisZeroG_false {α : Type*} [CCommRing α] [CRingSpec α] {p : CPoly α}
    (h : cisZero p = false) :
    toPoly p ≠ 0 := by
  rw [Bool.eq_false_iff, Ne, cisZeroG_iff] at h
  exact h

/-- **Denotational keystone.** A `CPoly` over `[CCommRing α] [CRingSpec α]` is a `CRingSpec` with
`R := (CRingSpec.R α)[X]` and `toR := toPoly`, the Horner ring homomorphism (its hom laws are the
`toPolyG_*` squares). Together with `instCCommRingCPoly` this makes `CPoly (CPoly _)` a fully
denotable ring coefficient — bivariate polynomials denote into the iterated polynomial ring
`(R α)[X][X]` with no separate development. See `docs/ring-generalization-plan.md`. -/
noncomputable instance instCRingSpecCPoly {α : Type*} [CCommRing α] [CRingSpec α] :
    CRingSpec (CPoly α) where
  R := (CRingSpec.R α)[X]
  toR := toPoly
  toR_zero := toPolyG_nil
  toR_one := toPolyG_one_singleton
  toR_add := toPolyG_caddG
  toR_mul := toPolyG_cmulG
  toR_neg := toPolyG_cnegG
  isZero_iff := cisZeroG_iff

/-- Monic-normalization is a unit-scaling: `toPoly (cmonic p)` is associated to `toPoly p` in `K[X]`. -/
theorem associated_toPolyG_cmonicG {α : Type*} [CField α] [CFieldSpec α] (p : CPoly α) :
    Associated (toPoly (cmonic p)) (toPoly p) := by
  rw [cmonic]
  split_ifs with h
  · rw [toPolyG_nil]
    have hz : toPoly p = 0 := (cisZeroG_iff p).mp (by rwa [cisZeroG_cnormG] at h)
    rw [hz]
  · rw [toPolyG_cscaleG, toPolyG_cnormG]
    have hne : cnorm (cnorm p) ≠ [] := by
      rw [cnormG_idem]; intro he
      exact h (by rw [cisZeroG_cnormG, cisZeroG_iff, ← toPolyG_cnormG, he, toPolyG_nil])
    exact associated_unit_mul_left _ _
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr
        (by rw [toR_eq_toK, CFieldSpec.toK_inv]; exact inv_ne_zero (toR_cleadG_ne_zero hne))))

/-- `toPoly (cmonic p)` is monic for `toPoly p ≠ 0`. -/
theorem monic_toPolyG_cmonicG {α : Type*} [CField α] [CFieldSpec α] (p : CPoly α)
    (hp : toPoly p ≠ 0) :
    (toPoly (cmonic p)).Monic := by
  have hz : cisZero (cnorm p) = false := by
    rw [← Bool.not_eq_true, cisZeroG_iff, toPolyG_cnormG]
    exact hp
  have hcform : toPoly (cmonic p)
      = Polynomial.C (CRingSpec.toR (CField.inv (clead (cnorm p)))) * toPoly p := by
    rw [cmonic, if_neg (by rw [hz]; decide), toPolyG_cscaleG, toPolyG_cnormG]
  rw [hcform]
  refine monic_C_mul_of_mul_leadingCoeff_eq_one ?_
  rw [toR_eq_toK, CFieldSpec.toK_inv, ← toR_eq_toK, toR_cleadG_eq_leadingCoeff, toPolyG_cnormG,
    inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hp)]

end CPoly

end DeepWiki.SymbolicIntegration
