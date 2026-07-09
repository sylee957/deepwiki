import DeepWiki.ComputableAlgebra.PolyReprSparse
import DeepWiki.ComputableAlgebra.PolyReprDivisionDegree
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # Representation-generic fractions over `CPoly` (Step 6)

Once the polynomial layer is representation-independent, a *fraction* is just a num/den pair over any
`CPoly P` — `GFrac P α` — with the standard fraction arithmetic built from the generic polynomial
ops. Its denotation into `RatFunc` and the field-homomorphism laws follow from the `toPoly` squares, so
they hold for **every** representation. `native_decide` validates the computable ops on both the dense
`List` and the sparse `SparsePoly` carriers. See `docs/representation-independent-poly.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.CPoly

/-- A fraction over a representation-independent polynomial: a numerator/denominator pair. -/
structure GFrac (P : Type u → Type u) (α : Type u) where
  /-- Numerator. -/
  num : P α
  /-- Denominator. -/
  den : P α

namespace GFrac

variable {P : Type u → Type u} [CPoly P] {α : Type u}

/-- Componentwise decidable equality (computable; reduces under `native_decide`). -/
instance instDecidableEq [DecidableEq (P α)] : DecidableEq (GFrac P α)
  | ⟨n₁, d₁⟩, ⟨n₂, d₂⟩ =>
    if h : n₁ = n₂ ∧ d₁ = d₂ then isTrue (by rw [h.1, h.2])
    else isFalse (fun he => h (by injection he with h1 h2; exact ⟨h1, h2⟩))

/-- Fraction multiplication `(n₁/d₁)·(n₂/d₂) = (n₁n₂)/(d₁d₂)`. -/
def mul [CCommRing α] (x y : GFrac P α) : GFrac P α :=
  ⟨CPoly.mul x.num y.num, CPoly.mul x.den y.den⟩

/-- Fraction addition `(n₁/d₁)+(n₂/d₂) = (n₁d₂ + n₂d₁)/(d₁d₂)`. -/
def add [CCommRing α] (x y : GFrac P α) : GFrac P α :=
  ⟨CPoly.add (CPoly.mul x.num y.den) (CPoly.mul y.num x.den),
    CPoly.mul x.den y.den⟩

/-- **Reduce to lowest terms** by dividing numerator and denominator by their gcd (adopts the fuel-less
`cgcd` + `cdivmod`). -/
def reduce [CField α] (x : GFrac P α) : GFrac P α :=
  let g := cgcd x.num x.den
  ⟨(cdivmod x.num g).1, (cdivmod x.den g).1⟩

section Denote
variable [CField α] [CFieldSpec α]

/-- Denotation into `RatFunc (CRingSpec.R α)` (`= CFieldSpec.K α`, a field on the field path):
`num/den ↦ ⟦num⟧/⟦den⟧` through the poly denotation. -/
noncomputable def toRatFunc (x : GFrac P α) : RatFunc (CRingSpec.R α) :=
  algebraMap (CRingSpec.R α)[X] (RatFunc (CRingSpec.R α)) (toPoly x.num) /
    algebraMap (CRingSpec.R α)[X] (RatFunc (CRingSpec.R α)) (toPoly x.den)

/-- **Fraction `mul` is a homomorphism** into `RatFunc`: `⟦x·y⟧ = ⟦x⟧·⟦y⟧` (unconditional in a field). -/
theorem toRatFunc_mul (x y : GFrac P α) : toRatFunc (mul x y) = toRatFunc x * toRatFunc y := by
  simp only [toRatFunc, mul, toPoly_mul, map_mul]
  rw [div_mul_div_comm]

/-- **`reduce` preserves the value:** cancelling the gcd keeps `⟦reduce x⟧ = ⟦x⟧` (for `den ≠ 0`). -/
theorem toRatFunc_reduce (x : GFrac P α) (hden : ¬ cisZero (P := P) x.den = true) :
    toRatFunc (reduce x) = toRatFunc x := by
  have hgn := (cgcd_dvd x.num x.den).1
  have hgd := (cgcd_dvd x.num x.den).2
  have hg : ¬ cisZero (P := P) (cgcd x.num x.den) = true := fun hz => by
    rw [(cisZero_iff _).mp hz, zero_dvd_iff] at hgd
    exact hden ((cisZero_iff _).mpr hgd)
  have hgne : toPoly (cgcd x.num x.den) ≠ 0 := fun h => hg ((cisZero_iff _).mpr h)
  have hnum := toPoly_mul_cdiv_of_dvd x.num (cgcd x.num x.den) hg hgn
  have hden' := toPoly_mul_cdiv_of_dvd x.den (cgcd x.num x.den) hg hgd
  have hc : algebraMap (CRingSpec.R α)[X] (RatFunc (CRingSpec.R α)) (toPoly (cgcd x.num x.den)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (CRingSpec.R α)[X] (RatFunc (CRingSpec.R α)))).mpr hgne
  simp only [toRatFunc, reduce]
  rw [hnum, hden', map_mul, map_mul, mul_div_mul_left _ _ hc]

end Denote

end GFrac

/-! ### `native_decide` — generic fraction ops compute on BOTH the dense and the sparse carrier -/

/-- Dense: `(1+x)/1 · 1/x = (1+x)/x` (`GFrac (List ℚ)`); the convolution `mul` carries unnormalized
trailing zeros (`[1,1,0]`, `[0,1,0]`) — a `cnorm` on the components would strip them. -/
example : GFrac.mul (⟨[1, 1], [1]⟩ : GFrac List ℚ) ⟨[1], [0, 1]⟩ = ⟨[1, 1, 0], [0, 1, 0]⟩ := by
  native_decide

/-- `reduce` lowers `(x² − 1)/(x − 1)` to `(x + 1)/1`: numerator honest degree `1`, denominator `0`. -/
example :
    (CPoly.cdeg (GFrac.reduce (⟨[-1, 0, 1], [-1, 1]⟩ : GFrac List ℚ)).num,
      CPoly.cdeg (GFrac.reduce (⟨[-1, 0, 1], [-1, 1]⟩ : GFrac List ℚ)).den) = (1, 0) := by
  native_decide

/-- Sparse: the same fraction multiplication over the sparse carrier `GFrac SparsePoly ℚ` computes —
its numerator `(1+x)·1` has honest degree `1`, its denominator `1·x` degree `1` (via the rep-agnostic
`cdeg`, since the `mul` result lands in dense `ofFn` form on either carrier). -/
example :
    (CPoly.cdeg (GFrac.mul
        (⟨SparsePoly.ofList [(0, 1), (1, 1)], SparsePoly.ofList [(0, 1)]⟩ : GFrac SparsePoly ℚ)
        ⟨SparsePoly.ofList [(0, 1)], SparsePoly.ofList [(1, 1)]⟩).num,
      CPoly.cdeg (GFrac.mul
        (⟨SparsePoly.ofList [(0, 1), (1, 1)], SparsePoly.ofList [(0, 1)]⟩ : GFrac SparsePoly ℚ)
        ⟨SparsePoly.ofList [(0, 1)], SparsePoly.ofList [(1, 1)]⟩).den) = (1, 1) := by native_decide

end DeepWiki.SymbolicIntegration.CPoly
