import DeepWiki.SymbolicIntegration.Computable.SplitFactorHelpers
import DeepWiki.SymbolicIntegration.Computable.GenericBezout

/-! # The canonical field identity `q + b/dₛ + c/dₙ = a/d`

The abstract field-arithmetic recombination lemma over `RatFunc K` used by the generic
canonical-representation proof: from the division, denominator split, and Bézout split, the three
pieces recombine to `a/d`. Pure Layer-0 math, independent of the computable engine. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-- **The abstract canonical field identity** over ℚ(x)(t): from the division `a = q·d + r`, the
denominator split `d = dₛ·dₙ`, and the Bézout split `b·dₙ + c·dₛ = r`, the three pieces recombine to
`a/d` — `q + b/dₛ + c/dₙ = a/d`. The field-arithmetic core, independent of the computable engine. -/
theorem canonicalRepFast_field_identity {K : Type*} [Field K] (a d q r dn ds b c : K[X])
    (hd : d ≠ 0) (hdn : dn ≠ 0) (hds : ds ≠ 0)
    (hadiv : a = q * d + r) (hsplit : d = ds * dn) (hbcr : b * dn + c * ds = r) :
    (algebraMap K[X] (RatFunc K) q)
        + algebraMap K[X] (RatFunc K) b / algebraMap K[X] (RatFunc K) ds
        + algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) dn
      = algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) d := by
  set A := algebraMap K[X] (RatFunc K) with hA
  have hAd : A d ≠ 0 := RatFunc.algebraMap_ne_zero hd
  have hAdn : A dn ≠ 0 := RatFunc.algebraMap_ne_zero hdn
  have hAds : A ds ≠ 0 := RatFunc.algebraMap_ne_zero hds
  have hAa : A a = A q * (A ds * A dn) + (A b * A dn + A c * A ds) := by
    rw [hadiv, hsplit, ← hbcr]; push_cast [hA]; ring
  rw [show A d = A ds * A dn by rw [hsplit, map_mul]]
  rw [eq_div_iff (mul_ne_zero hAds hAdn), hAa]
  field_simp
  ring

end DeepWiki.SymbolicIntegration
