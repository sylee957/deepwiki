import DeepWiki.ComputableAlgebra.PolyRepr
import DeepWiki.ComputableAlgebra.Field
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.Polynomial.Basic

/-! # The dense computable-polynomial representation and engine

`DensePoly α := List α` is the dense coefficient-list carrier. It supplies both the representation-
independent `CPoly` instance and the concrete dense arithmetic engine with its Horner denotation
`DensePoly.toPoly : DensePoly α → (CRingSpec.R α)[X]`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u

/-- Generic dense coefficient list over a computable ring `α` (index = degree, low to high).
A reducible `abbrev` for `List α` so the `List` instances (`BEq`/`DecidableEq`/…) transfer and the
ℚ-specialization stays definitionally equal to `List ℚ`. -/
abbrev DensePoly (α : Type u) := List α

namespace CPoly

/-! ### The representation-independent dense-list instance -/

/-- Dense-coefficient-list representation (index = degree, low to high). -/
instance instList : CPoly DensePoly where
  coeff p i := (p : List _).getD i CCommRing.zero
  degBound p := (p : List _).length
  ofFn n f := (List.range n).map f
  coeff_ofFn n f i := by
    show ((List.range n).map f).getD i CCommRing.zero = if i < n then f i else CCommRing.zero
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    rcases Nat.lt_or_ge i n with h | h
    · rw [List.getElem?_range h, Option.map_some, Option.getD_some, if_pos h]
    · rw [List.getElem?_eq_none (by simpa using h), Option.map_none, Option.getD_none,
        if_neg (by simpa using h)]
  coeff_ge p i h := by
    show (p : List _).getD i CCommRing.zero = CCommRing.zero
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

/-- Generic coefficient lookup on the dense representation is exactly list lookup with a zero default. -/
@[simp] theorem coeff_dense_eq {α : Type u} [CCommRing α] (p : DensePoly α) (i : ℕ) :
    CPoly.coeff p i = (p : List α).getD i CCommRing.zero := rfl

/-- Generic construction on the dense representation is the low-to-high `List.range` map. -/
@[simp] theorem ofFn_dense_eq {α : Type u} [CCommRing α] (n : ℕ) (f : ℕ → α) :
    CPoly.ofFn (P := DensePoly) n f = (List.range n).map f := rfl

/-! ### The generic arithmetic reduces on the dense representation -/

/-- Generic `add` reduces under `native_decide` at the dense instance. -/
example : (add ([1, 2, 3] : DensePoly ℚ) [10, 20]) = [11, 22, 3] := by native_decide

/-- Generic `neg` reduces under `native_decide` at the dense instance. -/
example : (neg ([1, -2, 3] : DensePoly ℚ)) = [-1, 2, -3] := by native_decide

/-- Generic `scale` reduces under `native_decide` at the dense instance. -/
example : (scale (2 : ℚ) ([1, -2, 3] : DensePoly ℚ)) = [2, -4, 6] := by native_decide

/-- Generic `mul` reduces on the dense representation, retaining its degree-bound trailing zero. -/
example : (mul ([1, 2] : DensePoly ℚ) [3, 4]) = [3, 10, 8, 0] := by native_decide

end CPoly

/-! ### The polynomial engine on `DensePoly`

Dense-coefficient lists (index = degree, low to high) over `[CField α]`, with arithmetic built from
the `CField` operations and a Horner bridge `toPoly` into `(CFieldSpec.K α)[X]`. -/

namespace DensePoly

/-- Pad a `DensePoly` on the high-degree end with zeros up to length `n`; no-op if length is already
at least `n`. -/
def cpad {α : Type*} [CField α] (n : ℕ) (p : DensePoly α) : DensePoly α :=
  (p : List α) ++ List.replicate (n - (p : List α).length) CCommRing.zero

/-- Reverse coefficients after zero-padding to degree bound `k`: `creverseDeg k p` represents
`X^k * p(X⁻¹)` when `k` bounds the degree of `p`. -/
def creverseDeg {α : Type*} [CField α] (k : ℕ) (p : DensePoly α) : DensePoly α :=
  (cpad (k + 1) p).reverse

/-- Monomial `c * X^n` as a `DensePoly`: `n` low-degree zeros followed by coefficient `c`. -/
def cMonomial {α : Type*} [CField α] (c : α) (n : ℕ) : DensePoly α :=
  (List.replicate n CCommRing.zero ++ [c] : List α)

/-- Generic power of a field element: `cfpow c n = cⁿ` over `[CField α]` by `ℕ`-recursion. -/
def cfpow {α : Type*} [CField α] (c : α) : ℕ → α
  | 0 => CCommRing.one
  | n + 1 => CCommRing.mul c (cfpow c n)

/-- Polynomial antiderivative `cIntegratePoly c = q` with zero constant coefficient: termwise
`∫ Σ cᵢXⁱ = Σ (cᵢ/(i+1))X^(i+1)`, using the computable natural cast in the coefficient field. -/
def cIntegratePoly {α : Type*} [CField α] (c : DensePoly α) : DensePoly α :=
  CCommRing.zero :: ((c : List α).zipIdx.map (fun (a, i) => CField.div a (cnatCast (i + 1))))

/-- Horner evaluation `ceval p c = p(c)` for a dense coefficient list, low degree first. -/
def ceval {α : Type*} [CCommRing α] (p : DensePoly α) (c : α) : α :=
  (p : List α).foldr (fun coeff acc => CCommRing.add coeff (CCommRing.mul c acc)) CCommRing.zero

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
    CFieldSpec.toK (others.foldl (fun acc zj => CCommRing.mul acc (CField.sub zk zj)) init)
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

/-- Normalize a `DensePoly` by stripping trailing (high-degree) zero coefficients (`isZero`-tested),
so `cnorm` is a canonical form (the zero polynomial becomes `[]`). -/
def cnorm {α : Type*} [CCommRing α] : DensePoly α → DensePoly α
  | [] => []
  | a :: as => match cnorm as with
    | [] => if CCommRing.isZero a then [] else [a]
    | r => a :: r

/-- Coefficientwise addition of two `DensePoly`s (the shorter is zero-extended implicitly). -/
def cadd {α : Type*} [CCommRing α] : DensePoly α → DensePoly α → DensePoly α
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => CCommRing.add a b :: cadd as bs

/-- `(cadd p q).length = max p.length q.length`: addition zero-extends the shorter input. -/
theorem caddG_length {α : Type*} [CCommRing α] (p q : DensePoly α) :
    (cadd p q : List α).length = max (p : List α).length (q : List α).length := by
  induction p generalizing q with
  | nil => simp [cadd]
  | cons a as ih =>
    cases q with
    | nil => simp [cadd]
    | cons b bs => simp only [cadd, List.length_cons, ih bs]; omega

/-- Negation of a `DensePoly`, coefficientwise. -/
def cneg {α : Type*} [CCommRing α] (p : DensePoly α) : DensePoly α := (p : List α).map CCommRing.neg

/-- Subtraction of `DensePoly`s, `p − q := p + (−q)`. -/
def csub {α : Type*} [CCommRing α] (p q : DensePoly α) : DensePoly α := cadd p (cneg q)

/-- Scalar multiplication of a `DensePoly` by `c : α`, coefficientwise. -/
def cscale {α : Type*} [CCommRing α] (c : α) (p : DensePoly α) : DensePoly α := (p : List α).map (CCommRing.mul c)

/-- Degree shift `cshift k p = x^k · p`: prepend `k` zero coefficients. -/
def cshift {α : Type*} [CCommRing α] : ℕ → DensePoly α → DensePoly α
  | 0, p => p
  | n + 1, p => CCommRing.zero :: cshift n p

/-- `(cshift k p).length = k + p.length`. -/
theorem cshiftG_length {α : Type*} [CField α] (k : ℕ) (p : DensePoly α) :
    (cshift k p : List α).length = k + (p : List α).length := by
  induction k with
  | zero => simp [cshift]
  | succ m ih => rw [cshift]; simp only [List.length_cons, ih]; omega

/-- Polynomial multiplication of `DensePoly`s (schoolbook convolution via `cshift`/`cscale`). -/
def cmul {α : Type*} [CCommRing α] : DensePoly α → DensePoly α → DensePoly α
  | [], _ => []
  | a :: as, q => cadd (cscale a q) (CCommRing.zero :: cmul as q)

/-- Product of a list of `DensePoly`s, folding `cmul` from `[1]`. -/
def cprod {α : Type*} [CCommRing α] (ps : List (DensePoly α)) : DensePoly α :=
  ps.foldl (fun acc p => cmul acc p) [CCommRing.one]

/-- Power of a `DensePoly` by `ℕ`-recursion (`[1]` at `0`). -/
def cpow {α : Type*} [CCommRing α] (p : DensePoly α) : ℕ → DensePoly α
  | 0 => [CCommRing.one]
  | n + 1 => cmul p (cpow p n)

/-- Leading coefficient of a `DensePoly` (top nonzero coefficient; `zero` for the zero polynomial). -/
def clead {α : Type*} [CCommRing α] (p : DensePoly α) : α := ((cnorm p : List α).getLast?.getD CCommRing.zero)

/-- Degree of a `DensePoly` as a `ℕ`: `(length of normalized p) − 1`, with `cdeg 0 = 0`. -/
def cdeg {α : Type*} [CCommRing α] (p : DensePoly α) : ℕ := (cnorm p : List α).length - 1

/-- Zero test for a `DensePoly`: `true` iff it normalizes to `[]`. -/
def cisZero {α : Type*} [CCommRing α] (p : DensePoly α) : Bool := (cnorm p : List α).isEmpty

/-- **Keystone instance.** A `DensePoly` over a computable commutative ring is itself a computable commutative
ring (`add := cadd`, `mul := cmul`, `neg := cneg`, `zero := []`, `one := [one]`, `isZero := cisZero`) — so
`DensePoly (DensePoly _)` is a valid coefficient tower and bivariate polynomials need no separate definition. All
ops reduce, so the tower stays `native_decide`-executable. See `docs/ring-generalization-plan.md`. -/
instance instCCommRingCPoly {α : Type*} [CCommRing α] : CCommRing (DensePoly α) where
  zero := []
  one := [CCommRing.one]
  add := cadd
  mul := cmul
  neg := cneg
  isZero := cisZero

/-- Make a `DensePoly` monic (lead coefficient `1`) by scaling by `(clead)⁻¹`; the zero polynomial
stays `[]`. -/
def cmonic {α : Type*} [CField α] (p : DensePoly α) : DensePoly α :=
  let p := cnorm p
  if cisZero p then [] else cscale (CField.inv (clead p)) p

/-- Monic test for a `DensePoly`: `true` iff `cmonic p = p` as normalized lists. -/
def cisMonic {α : Type*} [CField α] (p : DensePoly α) : Bool := cisZero (csub (cmonic p) p)

/-! ### The generic Horner bridge `toPoly` and its homomorphism lemmas

From here on the bridge `[CFieldSpec α]` is in scope: `toPoly` and every correctness lemma carry the
extra binder, while the engine ops above need only `[CField α]`. -/

/-- Generic bridge to `(CFieldSpec.K α)[X]`: `toPoly p` reads a `DensePoly` coefficient list (index =
degree, low to high) as a `Polynomial (CFieldSpec.K α)` in Horner form `p₀ + x·(p₁ + x·(p₂ + …))`,
each coefficient embedded via `toK`. -/
noncomputable def toPoly {α : Type*} [CCommRing α] [CRingSpec α] : DensePoly α → (CRingSpec.R α)[X]
  | [] => 0
  | a :: p => Polynomial.C (CRingSpec.toR a) + X * toPoly p

/-- `toPoly [] = 0`: the empty coefficient list is the zero polynomial. -/
@[simp, denote] theorem toPolyG_nil {α : Type*} [CCommRing α] [CRingSpec α] :
    toPoly ([] : DensePoly α) = 0 := rfl

/-- `toPoly`'s leading recursion (Horner): `toPoly (a :: p) = C (toK a) + X · toPoly p`. -/
@[simp, denote] theorem toPolyG_cons {α : Type*} [CCommRing α] [CRingSpec α] (a : α) (p : DensePoly α) :
    toPoly (a :: p) = Polynomial.C (CRingSpec.toR a) + X * toPoly p := rfl

/-- `toPoly [CCommRing.one] = 1`: the singleton coefficient list `[1]` reads as the polynomial `1`. -/
@[denote] theorem toPolyG_one_singleton {α : Type*} [CCommRing α] [CRingSpec α] :
    toPoly ([CCommRing.one] : DensePoly α) = 1 := by
  rw [toPolyG_cons, toPolyG_nil, mul_zero, add_zero, CRingSpec.toR_one, map_one]

/-- `toPoly [CCommRing.one] ≠ 0`: the singleton coefficient list `[1]` reads nontrivially. -/
theorem toPolyG_one_singleton_ne_zero {α : Type*} [CField α] [CFieldSpec α] :
    toPoly ([CCommRing.one] : DensePoly α) ≠ 0 := by
  simp only [denote, map_one, mul_zero, add_zero]
  exact (one_ne_zero : (1 : Polynomial (CFieldSpec.K α)) ≠ 0)

/-- `toPoly` is additive: `cadd` realizes `(CFieldSpec.K α)[X]` addition under the Horner bridge. -/
@[simp, denote] theorem toPolyG_caddG {α : Type*} [CCommRing α] [CRingSpec α] (p q : DensePoly α) :
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
    (f : α × α → DensePoly α) (pts : List (α × α)) (init : DensePoly α) :
    toPoly (pts.foldl (fun acc p => cadd acc (f p)) init)
      = toPoly init + (pts.map (fun p => toPoly (f p))).sum := by
  induction pts generalizing init with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons, ih]
    simp only [denote, List.map_cons, List.sum_cons]
    ring

/-- `toPoly` commutes with negation: `toPoly (cneg p) = − toPoly p`. -/
@[simp, denote] theorem toPolyG_cnegG {α : Type*} [CCommRing α] [CRingSpec α] (p : DensePoly α) :
    toPoly (cneg p) = - toPoly p := by
  induction p with
  | nil => simp [cneg]
  | cons a as ih =>
    show toPoly (CCommRing.neg a :: cneg as) = -toPoly (a :: as)
    simp only [denote, ih, map_neg]; ring

/-- `toPoly` realizes subtraction: `toPoly (csub p q) = toPoly p − toPoly q`. -/
@[simp, denote] theorem toPolyG_csubG {α : Type*} [CCommRing α] [CRingSpec α] (p q : DensePoly α) :
    toPoly (csub p q) = toPoly p - toPoly q := by
  rw [csub]
  simp only [denote, sub_eq_add_neg]

/-- `toPoly` realizes scalar multiplication: `toPoly (cscale c p) = C (toK c) · toPoly p`. -/
@[simp, denote] theorem toPolyG_cscaleG {α : Type*} [CCommRing α] [CRingSpec α] (c : α) (p : DensePoly α) :
    toPoly (cscale c p) = Polynomial.C (CRingSpec.toR c) * toPoly p := by
  induction p with
  | nil => simp [cscale]
  | cons a as ih =>
    show toPoly (CCommRing.mul c a :: cscale c as) = Polynomial.C (CRingSpec.toR c) * toPoly (a :: as)
    simp only [denote, ih, map_mul]; ring

/-- `toPoly` realizes the degree shift: `toPoly (cshift k p) = X^k · toPoly p`. -/
@[simp, denote] theorem toPolyG_cshiftG {α : Type*} [CCommRing α] [CRingSpec α] (k : ℕ) (p : DensePoly α) :
    toPoly (cshift k p) = X ^ k * toPoly p := by
  induction k with
  | zero => simp [cshift]
  | succ n ih =>
    show toPoly (CCommRing.zero :: cshift n p) = X ^ (n + 1) * toPoly p
    simp only [denote, ih, map_zero]; ring

/-- `toPoly` is multiplicative: `cmul` realizes `(CFieldSpec.K α)[X]` multiplication. -/
@[simp, denote] theorem toPolyG_cmulG {α : Type*} [CCommRing α] [CRingSpec α] (p q : DensePoly α) :
    toPoly (cmul p q) = toPoly p * toPoly q := by
  induction p with
  | nil => simp [cmul]
  | cons a as ih =>
    show toPoly (cadd (cscale a q) (CCommRing.zero :: cmul as q)) = toPoly (a :: as) * toPoly q
    simp only [denote, ih, map_zero]; ring

/-- Repeated right multiplication over `List.range n` denotes multiplication by `toPoly V ^ n`. -/
@[denote] theorem toPolyG_foldl_range_cmulG {α : Type*} [CCommRing α] [CRingSpec α]
    (V : DensePoly α) (n : ℕ) (init : DensePoly α) :
    toPoly ((List.range n).foldl (fun acc _ => cmul acc V) init)
      = toPoly init * toPoly V ^ n := by
  induction n generalizing init with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_concat, toPolyG_cmulG, ih, pow_succ]
    ring

/-- `toPoly` realizes the `ℕ`-power: `toPoly (cpow p n) = (toPoly p) ^ n`. -/
@[simp, denote] theorem toPolyG_cpowG {α : Type*} [CCommRing α] [CRingSpec α] (p : DensePoly α) (n : ℕ) :
    toPoly (cpow p n) = (toPoly p) ^ n := by
  induction n with
  | zero => simp [cpow, denote]
  | succ n ih =>
    rw [cpow]
    simp only [denote, ih, pow_succ, mul_comm]

/-! ### Generic formal derivative `cderiv` over a `CField` -/

/-- Generic `ℕ`-scaling `cnsmul k a = a + a + … + a` (`k` times), built from `CCommRing.add`. -/
def cnsmul {α : Type*} [CField α] : ℕ → α → α
  | 0, _ => CCommRing.zero
  | k + 1, a => CCommRing.add a (cnsmul k a)

/-- `toK (cnsmul k a) = k • toK a` in `K`. -/
@[denote] theorem toK_nsmulG {α : Type*} [CField α] [CFieldSpec α] (k : ℕ) (a : α) :
    CFieldSpec.toK (cnsmul k a) = k • CFieldSpec.toK a := by
  induction k with
  | zero => rw [cnsmul, CFieldSpec.toK_zero, zero_smul]
  | succ n ih => rw [cnsmul, CFieldSpec.toK_add, ih, succ_nsmul']

/-- Generic formal derivative `cderiv [a₀,a₁,a₂,…] = [1·a₁, 2·a₂, 3·a₃, …]`. -/
def cderiv {α : Type*} [CField α] : DensePoly α → DensePoly α
  | [] => []
  | _ :: as => go 1 as
where
  /-- Auxiliary: from degree `k`, emit `cnsmul k a` for each coefficient `a` (the derivative tail). -/
  go : ℕ → DensePoly α → DensePoly α
  | _, [] => []
  | k, a :: as => cnsmul k a :: go (k + 1) as

/-- `cderiv` realizes the `K[X]` derivative: `toPoly (cderiv p) = Polynomial.derivative (toPoly p)`. -/
@[denote] theorem toPolyG_cderivG {α : Type*} [CField α] [CFieldSpec α] (p : DensePoly α) :
    toPoly (cderiv p) = Polynomial.derivative (toPoly p) := by
  suffices h : ∀ (as : DensePoly α) (k : ℕ),
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
@[simp] theorem cnormG_nil {α : Type*} [CCommRing α] : cnorm ([] : DensePoly α) = [] := rfl

/-- `cnorm` on a cons cell, unfolded to its defining `match` (definitional). -/
theorem cnormG_cons_eq {α : Type*} [CCommRing α] (a : α) (as : DensePoly α) :
    cnorm (a :: as)
      = (match cnorm as with | [] => if CCommRing.isZero a then [] else [a] | r => a :: r) := rfl

/-- `cnorm` is idempotent: stripping trailing zeros twice is the same as once. -/
@[simp] theorem cnormG_idem {α : Type*} [CCommRing α] (p : DensePoly α) : cnorm (cnorm p) = cnorm p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [cnormG_cons_eq]
    cases h : cnorm as with
    | nil => cases ha : CCommRing.isZero a <;> simp [cnormG_cons_eq, ha]
    | cons b bs =>
      rw [h] at ih
      simp only [cnormG_cons_eq, ih]

/-- `cnorm` does not increase the coefficient-list length. -/
theorem cnormG_length_le {α : Type*} [CCommRing α] (p : DensePoly α) :
    (cnorm p : List α).length ≤ (p : List α).length := by
  induction p with
  | nil => simp [cnorm]
  | cons a as ih =>
    rw [cnorm]
    cases h : cnorm as with
    | nil => by_cases ha : CCommRing.isZero a <;> simp [ha, List.length_cons]
    | cons b bs =>
      simp only [List.length_cons]
      have : (b :: bs : List α).length ≤ (as : List α).length := h ▸ ih
      simp only [List.length_cons] at this
      omega

/-- `clead` is invariant under `cnorm`: `clead (cnorm p) = clead p`. -/
theorem cleadG_cnormG {α : Type*} [CCommRing α] (p : DensePoly α) : clead (cnorm p) = clead p := by
  simp only [clead, cnormG_idem]

/-- `cisZero` is invariant under `cnorm`. -/
theorem cisZeroG_cnormG {α : Type*} [CCommRing α] (q : DensePoly α) : cisZero (cnorm q) = cisZero q := by
  simp only [cisZero, cnormG_idem]

/-- `cdeg` is invariant under `cnorm`. -/
theorem cdegG_cnormG {α : Type*} [CCommRing α] (p : DensePoly α) : cdeg (cnorm p) = cdeg p := by
  simp only [cdeg, cnormG_idem]

/-- `toPoly` ignores normalization: `toPoly (cnorm p) = toPoly p` — stripping trailing zeros
does not change the polynomial (the dropped coefficients are zero, via `isZero_iff`). -/
@[simp, denote] theorem toPolyG_cnormG {α : Type*} [CCommRing α] [CRingSpec α] (p : DensePoly α) :
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
theorem toPolyG_coeff {α : Type*} [CCommRing α] [CRingSpec α] (p : DensePoly α) (i : ℕ) :
    (toPoly p).coeff i = CRingSpec.toR ((p : List α).getD i CCommRing.zero) := by
  induction p generalizing i with
  | nil => simp [CRingSpec.toR_zero]
  | cons a as ih =>
    rw [toPolyG_cons]
    cases i with
    | zero => simp [coeff_C]
    | succ n => simp [coeff_X_mul, ih]

/-- `toPoly` of a coefficient list is its dense polynomial `∑ i, C(toK cᵢ) * X^i`. -/
theorem toPolyG_eq_sum_range {α : Type*} [CCommRing α] [CRingSpec α] (l : DensePoly α) :
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
theorem toR_cnormG_getD {α : Type*} [CCommRing α] [CRingSpec α] (p : DensePoly α) (k : ℕ) :
    CRingSpec.toR ((cnorm p : List α).getD k CCommRing.zero) = (toPoly p).coeff k := by
  rw [← toPolyG_coeff, toPolyG_cnormG]

/-- `cnorm` has no trailing zero: `(cnorm p).getLast?` is never a zero coefficient. -/
theorem cnormG_getLast?_ne_some_zero {α : Type*} [CCommRing α] (p : DensePoly α) :
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

/-- For a normalized nonzero `DensePoly`, the leading coefficient `clead` is nonzero (in `K`). -/
theorem toR_cleadG_ne_zero {α : Type*} [CCommRing α] [CRingSpec α] {p : DensePoly α} (h : cnorm p ≠ []) :
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
theorem toR_cleadG_eq_coeff {α : Type*} [CCommRing α] [CRingSpec α] (p : DensePoly α) :
    CRingSpec.toR (clead p) = (toPoly p).coeff (cdeg p) := by
  rw [clead, cdeg, ← toPolyG_cnormG, toPolyG_coeff, List.getD_eq_getElem?_getD,
    ← List.getLast?_eq_getElem?]

/-- Degree bound: `natDegree (toPoly p) ≤ (cnorm p).length − 1`. -/
theorem natDegree_toPolyG_le {α : Type*} [CCommRing α] [CRingSpec α] (p : DensePoly α) :
    (toPoly p).natDegree ≤ (cnorm p : List α).length - 1 := by
  rw [← toPolyG_cnormG]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [toPolyG_coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none,
    CRingSpec.toR_zero]

/-- `cdeg` is the honest `natDegree`: `cdeg p = (toPoly p).natDegree`. -/
theorem cdegG_eq_natDegree {α : Type*} [CCommRing α] [CRingSpec α] (p : DensePoly α) :
    cdeg p = (toPoly p).natDegree := by
  rcases eq_or_ne (cnorm p) [] with h | h
  · have h0 : toPoly p = 0 := by rw [← toPolyG_cnormG, h, toPolyG_nil]
    rw [cdeg, h, h0]; simp

  · refine le_antisymm ?_ (natDegree_toPolyG_le p)
    apply Polynomial.le_natDegree_of_ne_zero
    rw [← toR_cleadG_eq_coeff]
    exact toR_cleadG_ne_zero h

/-- A dense polynomial of degree zero is the constant given by its coefficient at index zero. -/
theorem toPolyG_eq_C_of_cdeg_eq_zero {α : Type*} [CCommRing α] [CRingSpec α]
    (p : DensePoly α) (h : cdeg p = 0) :
    toPoly p = Polynomial.C (CRingSpec.toR ((p : List α).getD 0 CCommRing.zero)) := by
  have hdeg : (toPoly p).natDegree = 0 := by rwa [← cdegG_eq_natDegree]
  calc
    toPoly p = Polynomial.C ((toPoly p).coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero hdeg
    _ = Polynomial.C (CRingSpec.toR ((p : List α).getD 0 CCommRing.zero)) := by
      rw [toPolyG_coeff]

example {α : Type*} [CCommRing α] [CRingSpec α] (p : DensePoly α) (h : cdeg p = 0) :
    toPoly p = Polynomial.C (CRingSpec.toR ((p : List α).getD 0 CCommRing.zero)) :=
  toPolyG_eq_C_of_cdeg_eq_zero p h

/-- For a nonzero generic polynomial, the normalized list length is `natDegree + 1`. -/
theorem length_cnormG_of_ne {α : Type*} [CCommRing α] [CRingSpec α] (p : DensePoly α)
    (h : cnorm p ≠ []) :
    (cnorm p : List α).length = (toPoly p).natDegree + 1 := by
  have hd := cdegG_eq_natDegree p
  rw [cdeg] at hd
  have hlen : 1 ≤ (cnorm p : List α).length := List.length_pos_iff.mpr h
  omega

/-- `toK (clead p)` is the honest `leadingCoeff`: `toK (clead p) = (toPoly p).leadingCoeff`. -/
theorem toR_cleadG_eq_leadingCoeff {α : Type*} [CCommRing α] [CRingSpec α] (p : DensePoly α) :
    CRingSpec.toR (clead p) = (toPoly p).leadingCoeff := by
  rw [Polynomial.leadingCoeff, ← cdegG_eq_natDegree, ← toR_cleadG_eq_coeff]

/-! ### Field-path `toK` aliases of the `toR` clead/coeff readings
On a field coefficient the ring bridge is the field bridge (`toR = toK`, by defeq), so these expose the
same readings phrased with `CFieldSpec.toK` for the field-only call sites. -/

/-- Field-path alias: `toK` reads a normalized coefficient as the corresponding `toPoly` coefficient. -/
theorem toK_cnormG_getD {α : Type*} [CField α] [CFieldSpec α] (p : DensePoly α) (k : ℕ) :
    CFieldSpec.toK ((cnorm p : List α).getD k CCommRing.zero) = (toPoly p).coeff k :=
  toR_cnormG_getD p k

/-- Field-path alias: `toK (clead p) = (toPoly p).coeff (cdeg p)`. -/
theorem toK_cleadG_eq_coeff {α : Type*} [CField α] [CFieldSpec α] (p : DensePoly α) :
    CFieldSpec.toK (clead p) = (toPoly p).coeff (cdeg p) :=
  toR_cleadG_eq_coeff p

/-- Field-path alias: `toK (clead p) = (toPoly p).leadingCoeff`. -/
theorem toK_cleadG_eq_leadingCoeff {α : Type*} [CField α] [CFieldSpec α] (p : DensePoly α) :
    CFieldSpec.toK (clead p) = (toPoly p).leadingCoeff :=
  toR_cleadG_eq_leadingCoeff p

/-- `cnorm p = []` iff `toPoly p = 0` (the list normalizes to empty exactly for the zero
polynomial). -/
theorem cnormG_eq_nil_iff {α : Type*} [CCommRing α] [CRingSpec α] (p : DensePoly α) :
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
theorem toPolyG_degree_lt_of_length_lt {α : Type*} [CCommRing α] [CRingSpec α] (p q : DensePoly α)
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
theorem cisZeroG_iff {α : Type*} [CCommRing α] [CRingSpec α] (p : DensePoly α) :
    cisZero p = true ↔ toPoly p = 0 := by
  rw [cisZero, ← cnormG_eq_nil_iff]
  exact (List.isEmpty_iff (l := (cnorm p : List α)))

/-- `cisZero p = false` gives `toPoly p ≠ 0`. -/
theorem toPolyG_ne_zero_of_cisZeroG_false {α : Type*} [CCommRing α] [CRingSpec α] {p : DensePoly α}
    (h : cisZero p = false) :
    toPoly p ≠ 0 := by
  rw [Bool.eq_false_iff, Ne, cisZeroG_iff] at h
  exact h

/-- **Denotational keystone.** A `DensePoly` over `[CCommRing α] [CRingSpec α]` is a `CRingSpec` with
`R := (CRingSpec.R α)[X]` and `toR := toPoly`, the Horner ring homomorphism (its hom laws are the
`toPolyG_*` squares). Together with `instCCommRingCPoly` this makes `DensePoly (DensePoly _)` a fully
denotable ring coefficient — bivariate polynomials denote into the iterated polynomial ring
`(R α)[X][X]` with no separate development. See `docs/ring-generalization-plan.md`. -/
noncomputable instance instCRingSpecCPoly {α : Type*} [CCommRing α] [CRingSpec α] :
    CRingSpec (DensePoly α) where
  R := (CRingSpec.R α)[X]
  toR := toPoly
  toR_zero := toPolyG_nil
  toR_one := toPolyG_one_singleton
  toR_add := toPolyG_caddG
  toR_mul := toPolyG_cmulG
  toR_neg := toPolyG_cnegG
  isZero_iff := cisZeroG_iff

/-- The `CRingSpec` denotation of a nested `DensePoly` is its Horner polynomial `toPoly`. -/
@[simp] theorem toR_densePoly {α : Type*} [CCommRing α] [CRingSpec α] (p : DensePoly α) :
    CRingSpec.toR p = toPoly p := rfl

/-- Nested Horner recursion reads a `DensePoly α` coefficient through its own `toPoly`. -/
@[simp] theorem toPolyG_cons_dense {α : Type*} [CCommRing α] [CRingSpec α]
    (a : DensePoly α) (p : DensePoly (DensePoly α)) :
    toPoly (a :: p) = Polynomial.C (toPoly a) + Polynomial.X * toPoly p := by
  rw [toPolyG_cons, toR_densePoly]

/-- A nested `DensePoly` coefficient is the inner `toPoly` of `getD i []`. -/
theorem toPolyG_coeff_dense {α : Type*} [CCommRing α] [CRingSpec α]
    (p : DensePoly (DensePoly α)) (i : ℕ) :
    (toPoly p).coeff i = toPoly ((p : List (DensePoly α)).getD i []) := by
  rw [toPolyG_coeff, toR_densePoly, show (CCommRing.zero : DensePoly α) = [] from rfl]

/-- If the base denotation ring is a domain, so is the denotation ring of `DensePoly α`. -/
instance instIsDomainRDensePoly {α : Type*} [CCommRing α] [CRingSpec α]
    [IsDomain (CRingSpec.R α)] : IsDomain (CRingSpec.R (DensePoly α)) :=
  inferInstanceAs (IsDomain ((CRingSpec.R α)[X]))

/-- Monic-normalization is a unit-scaling: `toPoly (cmonic p)` is associated to `toPoly p` in `K[X]`. -/
theorem associated_toPolyG_cmonicG {α : Type*} [CField α] [CFieldSpec α] (p : DensePoly α) :
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
theorem monic_toPolyG_cmonicG {α : Type*} [CField α] [CFieldSpec α] (p : DensePoly α)
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

end DensePoly

end DeepWiki.SymbolicIntegration
