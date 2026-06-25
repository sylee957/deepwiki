import DeepWiki.SymbolicIntegration.GenericPolyEngine

/-! # Generic Bézout cofactors and the extended-Euclidean split (`[CField α]`)
The computable Bézout helpers used by the canonical-representation engine (Bronstein §3.5), kept
**generic over `[CField α]`** so the tower (`…G`) engine and `native_decide` validations can reuse
them without the `QFunNZ`-specific denominator-splitting machinery.

* **`cbezoutOne fuel a b = (u, w)`** with `u·a + w·b = 1` for coprime `a, b`: rescale the `cgcdExtG`
  cofactors by the inverse of the (constant) gcd's leading coefficient.
* **`cextendedEuclideanSplit fuel dₙ dₛ r u w = (b, c)`** mirrors the abstract
  `extendedEuclideanSplit`: from a Bézout pair `u·dₙ + w·dₛ = 1`, returns `(b, c)` solving
  `b·dₙ + c·dₛ = r` with `deg b < deg dₛ`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### The computable extended-Euclidean Bézout split

`cextendedEuclideanSplit` is the computable mirror of the abstract `extendedEuclideanSplit`: from a
Bézout pair `(u, w)` with `u·dₙ + w·dₛ = 1` it produces `(b, c)` solving `b·dₙ + c·dₛ = r` with
`deg b < deg dₛ` (`b = (u·r) mod dₛ`). `cbezoutOne` extracts the rescaled cofactors from `cgcdExtG`. -/

/-- **Bézout cofactors** `cbezoutOne fuel a b = (u, w)` with `u·a + w·b = 1` for coprime `a, b`: run
`cgcdExtG` to get `(g, s, t)` with `s·a + t·b = g` (a nonzero constant, since `a, b` are coprime),
then rescale by `g⁻¹` so `u = s/g`, `w = t/g` (the cofactors of the *monic* gcd `1`). -/
def cbezoutOne (fuel : ℕ) (a b : CPolyG α) : CPolyG α × CPolyG α :=
  let (g, s, t) := cgcdExtG fuel a b
  let ginv := CField.inv (cleadG g)
  (cscaleG ginv s, cscaleG ginv t)

/-- **Computable Bézout split** `cextendedEuclideanSplit fuel dₙ dₛ r u w = (b, c)`: with a Bézout
pair `u·dₙ + w·dₛ = 1`, returns `b = (u·r) mod dₛ` and `c = w·r + (u·r div dₛ)·dₙ`, solving
`b·dₙ + c·dₛ = r` with `deg b < deg dₛ`. Mirrors the abstract `extendedEuclideanSplit`. -/
def cextendedEuclideanSplit (fuel : ℕ) (dn ds r u w : CPolyG α) : CPolyG α × CPolyG α :=
  let ur := cmulG u r
  let (quo, rem) := cdivmodG fuel ur ds
  (rem, caddG (cmulG w r) (cmulG quo dn))

end CPolyG

end DeepWiki.SymbolicIntegration
