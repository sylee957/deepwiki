import DeepWiki.SymbolicIntegration.CanonicalRepresentation.Classify
import DeepWiki.SymbolicIntegration.Core.Differential.Gcd.PrimeFactors
import DeepWiki.SymbolicIntegration.CanonicalRepresentation.NormalSqfree
import DeepWiki.SymbolicIntegration.CanonicalRepresentation.RootCharacterization
import DeepWiki.SymbolicIntegration.CanonicalRepresentation.SplitFactor
import DeepWiki.SymbolicIntegration.CanonicalRepresentation.SplitSquarefreeFactor
import DeepWiki.SymbolicIntegration.Core.Differential.ImplicitDerivLinearFactors
import DeepWiki.ComputableAlgebra.PolySquarefreeTheory
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Radical.Basic

/-! # Canonical representation assembly

Bézout splitting and final rational-function assembly for canonical representations.
-/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section CanonicalRep
variable {K : Type*} [Field K] [Differential K]

/-- The Bézout split of `r` over coprime `dₙ, dₛ` given `u·dₙ + w·dₛ = 1`: returns `(b, c)` solving
`b·dₙ + c·dₛ = r` with `deg b < deg dₛ` (`b = (u·r) %ₘ dₛ`, `c = w·r + (u·r /ₘ dₛ)·dₙ`). -/
noncomputable def extendedEuclideanSplit (dn ds r u w : K[X]) : K[X] × K[X] :=
  ((u * r) %ₘ ds, w * r + (u * r /ₘ ds) * dn)

omit [Differential K] in
/-- The Bézout split solves `b·dₙ + c·dₛ = r` whenever `u·dₙ + w·dₛ = 1`. -/
theorem extendedEuclideanSplit_spec (dn ds r u w : K[X])
    (hbez : u * dn + w * ds = 1) :
    (extendedEuclideanSplit dn ds r u w).1 * dn
        + (extendedEuclideanSplit dn ds r u w).2 * ds = r := by
  simp only [extendedEuclideanSplit]
  have hmod : (u * r) %ₘ ds = u * r - ds * (u * r /ₘ ds) := by
    have := modByMonic_add_div (u * r) ds
    linear_combination this
  rw [hmod]
  have hr : (u * dn + w * ds) * r = r := by rw [hbez, one_mul]
  linear_combination hr

omit [Differential K] in
/-- The `b` part of the Bézout split has degree `< deg dₛ` (`b = (u·r) %ₘ dₛ`, a remainder modulo
the monic `dₛ`). -/
theorem extendedEuclideanSplit_degree_lt (dn ds r u w : K[X]) (hds : ds.Monic) :
    (extendedEuclideanSplit dn ds r u w).1.degree < ds.degree := by
  simp only [extendedEuclideanSplit]
  exact degree_modByMonic_lt (u * r) hds

open Classical in
/-- A Bézout pair `(u, w)` with `u·a + w·b = 1` for coprime `a, b`; `(0, 0)` otherwise. -/
noncomputable def bezoutOne (a b : K[X]) : K[X] × K[X] :=
  if h : IsCoprime a b then (h.choose, h.choose_spec.choose) else (0, 0)

omit [Differential K] in
/-- `bezoutOne a b` solves `u·a + w·b = 1` when `a, b` are coprime. -/
theorem bezoutOne_spec {a b : K[X]} (h : IsCoprime a b) :
    (bezoutOne a b).1 * a + (bezoutOne a b).2 * b = 1 := by
  rw [bezoutOne, dif_pos h]
  exact h.choose_spec.choose_spec

open Classical in
/-- The canonical representation of `f ∈ k(t)` as `(q, b/dₛ, c/dₙ)` — polynomial, reduced, and
simple parts — from the polynomial division `num f = q·d + r`, the denominator split
`(dₙ, dₛ) = splitFactor v d`, and the Bézout split `(b, c)` of `r`. -/
noncomputable def canonicalRepresentation (v : K[X]) (f : RatFunc K) :
    K[X] × RatFunc K × RatFunc K :=
  let a := f.num
  let d := f.denom
  let q := a /ₘ d
  let r := a %ₘ d
  let dn := (splitFactor v d).1
  let ds := (splitFactor v d).2
  let uw := bezoutOne dn ds
  let bc := extendedEuclideanSplit dn ds r uw.1 uw.2
  (q, algebraMap K[X] (RatFunc K) bc.1 / algebraMap K[X] (RatFunc K) ds,
      algebraMap K[X] (RatFunc K) bc.2 / algebraMap K[X] (RatFunc K) dn)

omit [Differential K] in
open Classical in
/-- `canonicalRepresentation` correctness (additive form): given `denom f = dₛ·dₙ` and a Bézout
pair `u·dₙ + w·dₛ = 1`, the canonical pieces sum back to `f = q + b/dₛ + c/dₙ`. -/
theorem canonicalRepresentation_add_eq (f : RatFunc K)
    {dn ds u w : K[X]} (hsplit : f.denom = ds * dn)
    (hdn : dn ≠ 0) (hds : ds ≠ 0) (hbez : u * dn + w * ds = 1) :
    (algebraMap K[X] (RatFunc K) (f.num /ₘ f.denom))
        + algebraMap K[X] (RatFunc K) (extendedEuclideanSplit dn ds (f.num %ₘ f.denom) u w).1
            / algebraMap K[X] (RatFunc K) ds
        + algebraMap K[X] (RatFunc K) (extendedEuclideanSplit dn ds (f.num %ₘ f.denom) u w).2
            / algebraMap K[X] (RatFunc K) dn
      = f := by
  set A := algebraMap K[X] (RatFunc K) with hA
  set d := f.denom with hd
  set a := f.num with ha
  set r := a %ₘ d with hr
  set q := a /ₘ d with hq
  set b := (extendedEuclideanSplit dn ds r u w).1 with hb
  set c := (extendedEuclideanSplit dn ds r u w).2 with hc
  have hbcr : b * dn + c * ds = r := extendedEuclideanSplit_spec dn ds r u w hbez
  have hdne : d ≠ 0 := RatFunc.denom_ne_zero f
  have hAdn : A dn ≠ 0 := by rw [hA]; exact (RatFunc.algebraMap_ne_zero hdn)
  have hAds : A ds ≠ 0 := by rw [hA]; exact (RatFunc.algebraMap_ne_zero hds)
  have hAd : A d ≠ 0 := by rw [hA]; exact (RatFunc.algebraMap_ne_zero hdne)
  -- `f = A a / A d`
  have hf : f = A a / A d := by rw [hA, hd, ha, RatFunc.num_div_denom]
  -- `a = q * d + r` from `modByMonic_add_div` (d monic)
  have hadiv : a = q * d + r := by
    have := modByMonic_add_div a d
    rw [← hr, ← hq] at this; linear_combination -this
  -- combine into the field identity
  rw [hf, hadiv, hsplit]
  rw [map_add, map_mul]
  have hAdsdn : A (ds * dn) = A ds * A dn := map_mul A ds dn
  rw [hAdsdn]
  -- now everything is over A ds, A dn; clear denominators
  field_simp
  -- goal is a polynomial identity in RatFunc; reduce to the Bézout identity
  rw [← hbcr]
  push_cast [hA]
  ring

open Classical in
/-- `canonicalRepresentation` correctness: the three pieces `(q, fₛ, fₙ)` sum to `f`, given that
the `splitFactor` output splits the denominator (`denom f = dₛ·dₙ`) and is coprime. -/
theorem canonicalRepresentation_sum_eq (v : K[X]) (f : RatFunc K)
    (hsplit : f.denom = (splitFactor v f.denom).2 * (splitFactor v f.denom).1)
    (hcop : IsCoprime (splitFactor v f.denom).1 (splitFactor v f.denom).2)
    (hdn : (splitFactor v f.denom).1 ≠ 0) (hds : (splitFactor v f.denom).2 ≠ 0) :
    algebraMap K[X] (RatFunc K) (canonicalRepresentation v f).1
        + (canonicalRepresentation v f).2.1 + (canonicalRepresentation v f).2.2 = f := by
  set dn := (splitFactor v f.denom).1 with hdndef
  set ds := (splitFactor v f.denom).2 with hdsdef
  have hbez := bezoutOne_spec hcop
  simp only [canonicalRepresentation, ← hdndef, ← hdsdef]
  exact canonicalRepresentation_add_eq f hsplit hdn hds hbez

end CanonicalRep

end DeepWiki.SymbolicIntegration
