import DeepWiki.ComputableAlgebra.Polynomial

/-! # A representation-independent computable-polynomial interface

`CPolyRepr P` abstracts a computable polynomial over the *representation* `P` (dense `List`, sparse
`List (ℕ × α)`, …) behind three primitives — `coeff` (coefficient at a degree, `0` past the end),
`degBound` (an upper bound on the degree), and `ofFn` (dense construction from a length + coefficient
function) — plus two spec laws. Arithmetic and its correctness are then defined **once, generically**,
so a new representation is a drop-in instance. The dense `List` instance below recovers the concrete
`CPoly α := List α` engine.

Feasibility (both validated here): the derived ops reduce under `native_decide` at the `List` instance,
and the coefficient-correctness squares are representation-generic — proven through the `CRingSpec`
denotation `toR` (where the ring laws live; `CCommRing` itself is Prop-free). See
`docs/representation-independent-poly.md` for the design and the phased migration plan. -/

namespace DeepWiki.SymbolicIntegration

universe u

/-- Representation-independent computable-polynomial interface over a computable commutative-ring
coefficient: `coeff` reads a coefficient (the ring `zero` past the end), `degBound` bounds the degree,
`ofFn` builds densely from a length and coefficient function. The two laws pin `coeff` on both. -/
class CPolyRepr (P : Type u → Type u) where
  /-- Coefficient at degree `i` (`CCommRing.zero` past the end). -/
  coeff : {α : Type u} → [CCommRing α] → P α → ℕ → α
  /-- A degree bound: `coeff p i = 0` for `i ≥ degBound p`. -/
  degBound : {α : Type u} → P α → ℕ
  /-- Dense construction: `coeff (ofFn n f) i = f i` for `i < n`, else `0`. -/
  ofFn : {α : Type u} → [CCommRing α] → ℕ → (ℕ → α) → P α
  /-- `ofFn` reads back its coefficient function up to the length. -/
  coeff_ofFn : ∀ {α} [CCommRing α] (n : ℕ) (f : ℕ → α) (i : ℕ),
    coeff (ofFn n f) i = if i < n then f i else CCommRing.zero
  /-- Coefficients past the degree bound are `0`. -/
  coeff_ge : ∀ {α} [CCommRing α] (p : P α) (i : ℕ), degBound p ≤ i → coeff p i = CCommRing.zero

namespace CPolyRepr

/-! ### The dense-`List` instance (the concrete `CPoly α = List α` engine) -/

/-- Dense-coefficient-list representation (index = degree, low→high) — the concrete `CPoly` engine. -/
instance instList : CPolyRepr List where
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

/-! ### Generic arithmetic — defined once against the interface

Each op is a coefficient formula through `ofFn`; its correctness is the `toR`-image square
`toR (coeff (op …) i) = <ring formula on toR (coeff …) i>`, proven from the interface laws + the
`CRingSpec` ring-hom laws alone — so it holds for **every** representation (no `List` induction). -/

variable {P : Type u → Type u} [CPolyRepr P] {α : Type u} [CCommRing α]

/-- Coefficientwise addition. -/
def add (p q : P α) : P α :=
  ofFn (max (degBound p) (degBound q)) (fun i => CCommRing.add (coeff p i) (coeff q i))

/-- Coefficientwise negation. -/
def neg (p : P α) : P α := ofFn (degBound p) (fun i => CCommRing.neg (coeff p i))

/-- Scalar multiplication by `c : α`. -/
def scale (c : α) (p : P α) : P α := ofFn (degBound p) (fun i => CCommRing.mul c (coeff p i))

/-- Convolution multiplication: `coeff i = ∑_{j≤i} coeff p j · coeff q (i−j)` (a computable
`CCommRing.add`-fold, since the Prop-free `CCommRing` has no `Finset.sum`). -/
def mul (p q : P α) : P α :=
  ofFn (degBound p + degBound q) (fun i =>
    ((List.range (i + 1)).map (fun j => CCommRing.mul (coeff p j) (coeff q (i - j)))).foldr
      CCommRing.add CCommRing.zero)

section Spec
variable [CRingSpec α]

/-- The `add` coefficient square (through the denotation `toR`, where the ring laws live):
`toR (coeff (add p q) i) = toR (coeff p i) + toR (coeff q i)`. Representation-generic. -/
theorem toR_coeff_add (p q : P α) (i : ℕ) :
    CRingSpec.toR (coeff (add p q) i) = CRingSpec.toR (coeff p i) + CRingSpec.toR (coeff q i) := by
  rw [add, coeff_ofFn]
  split
  · rw [CRingSpec.toR_add]
  · rename_i h; simp only [not_lt] at h
    rw [coeff_ge p i (le_trans (le_max_left _ _) h), coeff_ge q i (le_trans (le_max_right _ _) h),
      CRingSpec.toR_zero, add_zero]

/-- The `neg` coefficient square through `toR`. -/
theorem toR_coeff_neg (p : P α) (i : ℕ) :
    CRingSpec.toR (coeff (neg p) i) = - CRingSpec.toR (coeff p i) := by
  rw [neg, coeff_ofFn]
  split
  · rw [CRingSpec.toR_neg]
  · rename_i h; simp only [not_lt] at h
    rw [coeff_ge p i h, CRingSpec.toR_zero, neg_zero]

/-- The `scale` coefficient square through `toR`. -/
theorem toR_coeff_scale (c : α) (p : P α) (i : ℕ) :
    CRingSpec.toR (coeff (scale c p) i) = CRingSpec.toR c * CRingSpec.toR (coeff p i) := by
  rw [scale, coeff_ofFn]
  split
  · rw [CRingSpec.toR_mul]
  · rename_i h; simp only [not_lt] at h
    rw [coeff_ge p i h, CRingSpec.toR_zero, mul_zero]

/-- `toR` of a `CCommRing.add`-fold is the `R`-sum of the `toR` images (the fold homomorphism). -/
theorem toR_foldr_add (l : List α) :
    CRingSpec.toR (l.foldr CCommRing.add CCommRing.zero) = (l.map CRingSpec.toR).sum := by
  induction l with
  | nil => simp [CRingSpec.toR_zero]
  | cons a as ih => rw [List.foldr_cons, CRingSpec.toR_add, ih, List.map_cons, List.sum_cons]

/-- The `mul` coefficient square through `toR`: the `i`-th coefficient is the convolution sum. -/
theorem toR_coeff_mul (p q : P α) (i : ℕ) (hi : i < degBound p + degBound q) :
    CRingSpec.toR (coeff (mul p q) i)
      = ((List.range (i + 1)).map
          (fun j => CRingSpec.toR (coeff p j) * CRingSpec.toR (coeff q (i - j)))).sum := by
  rw [mul, coeff_ofFn, if_pos hi, toR_foldr_add, List.map_map]
  congr 1; apply List.map_congr_left; intro j _
  simp only [Function.comp_apply, CRingSpec.toR_mul]

end Spec

/-! ### `native_decide` showcase — the dense `List` instance reduces through the interface -/

/-- Generic `add` reduces under `native_decide` at the `List` instance. -/
example : (add ([1, 2, 3] : List ℚ) [10, 20]) = [11, 22, 3] := by native_decide

/-- Generic `neg` reduces under `native_decide` at the `List` instance. -/
example : (neg ([1, -2, 3] : List ℚ)) = [-1, 2, -3] := by native_decide

/-- Generic `scale` reduces under `native_decide` at the `List` instance. -/
example : (scale (2 : ℚ) [1, -2, 3]) = [2, -4, 6] := by native_decide

/-- Generic `mul` (convolution) reduces under `native_decide`: `(1+2x)(3+4x) = 3+10x+8x²`
(length `degBound p + degBound q = 4`, so an unnormalized trailing `0` — Phase 2 adds `cnorm`). -/
example : (mul ([1, 2] : List ℚ) [3, 4]) = [3, 10, 8, 0] := by native_decide

end CPolyRepr

end DeepWiki.SymbolicIntegration
