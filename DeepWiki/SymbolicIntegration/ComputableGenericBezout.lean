import DeepWiki.SymbolicIntegration.GenericPolyEngine

/-! # Generic Bézout cofactors and the extended-Euclidean split (`[CField α]`)
The computable Bézout helpers used by the canonical-representation engine (Bronstein §3.5), kept
**generic over `[CField α]`** so the tower (`…G`) engine and `native_decide` validations can reuse
them without the `QFunNZ`-specific denominator-splitting machinery.

* **`cbezoutOne fuel a b = (u, w)`** with `u·a + w·b = 1` for coprime `a, b`: rescale the `cgcdExtG`
  cofactors by the inverse of the (constant) gcd's leading coefficient.
* **`cextendedEuclideanSplit fuel dₙ dₛ r u w = (b, c)`** mirrors the abstract
  `extendedEuclideanSplit`: from a Bézout pair `u·dₙ + w·dₛ = 1`, returns `(b, c)` solving
  `b·dₙ + c·dₛ = r` with `deg b < deg dₛ`.
* **`cnatCastG k`** = `k`-fold `CField.one` sum (so it reduces under `native_decide`).
* **`cdiophantineG fuel p q rhs = (b, c)`** solves `b·p + c·q = rhs` with `deg b < deg q` for coprime
  `p, q` — the `ExtendedEuclidean(p, q, rhs)` step of Bronstein's §5.3 `HermiteReduce`. -/

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

/-- **Natural number as a field element** `cnatCastG k = 1 + 1 + … + 1` (`k` times), built only from
`CField.add`/`CField.one`. Needs only `[CField α]`, so it reduces (`native_decide`); used to form the
`−a/j` scaling in the Hermite inner loop. (`ComputableFieldGcd.nsmulG` carries a `[CFieldSpec α]`
binder and so does not reduce in the bridge-free engine context.) -/
def cnatCastG : ℕ → α
  | 0 => CField.zero
  | k + 1 => CField.add CField.one (cnatCastG k)

/-! ### The generic Bézout/Diophantine solver over a `[CField α]`

`cdiophantineG fuel p q rhs = (b, c)` solving `b·p + c·q = rhs` with `deg b < deg q`, for coprime
`p, q` (so `gcd(p,q)` is a nonzero constant). The generic mirror of `Compute.cdiophantine`
(`HermiteCompute`): from `cgcdExtG p q = (g, s, t)` with `s·p + t·q = g` (constant), scale `(s,t)` by
`rhs/g`, then reduce the first cofactor mod `q` and absorb the quotient into the second. This is the
`ExtendedEuclidean(p, q, rhs)` step of Bronstein's §5.3 `HermiteReduce`. -/

/-- **Generic Diophantine/Bézout solver** `cdiophantineG fuel p q rhs = (b, c)` solving
`b·p + c·q = rhs` with `deg b < deg q`, for **coprime** `p, q`. From `cgcdExtG p q = (g, s, t)` with
`s·p + t·q = g` (a nonzero constant), rescale `(s,t)` by `rhs/g`, reduce the first cofactor mod `q`
(`S = quo·q + b`), and absorb `quo·p` into the second (`c = T + quo·p`). Generic over `[CField α]`. -/
def cdiophantineG (fuel : ℕ) (p q rhs : CPolyG α) : CPolyG α × CPolyG α :=
  let (g, s, t) := cgcdExtG fuel p q
  let ginv := CField.inv (cleadG g)
  let S := cscaleG ginv (cmulG rhs s)
  let T := cscaleG ginv (cmulG rhs t)
  let (quo, b) := cdivmodG fuel S q
  let c := caddG T (cmulG quo p)
  (cnormG b, cnormG c)

end CPolyG

end DeepWiki.SymbolicIntegration
