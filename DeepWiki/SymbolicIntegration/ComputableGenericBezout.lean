import DeepWiki.SymbolicIntegration.GenericPolyEngine

/-! # Generic Bézout cofactors and the extended-Euclidean split (`[CField α]`)
The computable Bézout helpers used by the canonical-representation engine (Bronstein §3.5), kept
**generic over `[CField α]`** so the tower (`…G`) engine and `native_decide` validations can reuse
them at any carrier level, with no carrier-pinned denominator-splitting machinery.

* **`cbezoutOne fuel a b = (u, w)`** with `u·a + w·b = 1` for coprime `a, b`: rescale the `cgcdExtG`
  cofactors by the inverse of the (constant) gcd's leading coefficient.
* **`cextendedEuclideanSplit fuel dₙ dₛ r u w = (b, c)`** mirrors the abstract
  `extendedEuclideanSplit`: from a Bézout pair `u·dₙ + w·dₛ = 1`, returns `(b, c)` solving
  `b·dₙ + c·dₛ = r` with `deg b < deg dₛ`.
* **`cnatCastG k`** = `k`-fold `CField.one` sum (so it reduces under `native_decide`).
* **`cdiophantineG fuel p q rhs = (b, c)`** solves `b·p + c·q = rhs` with `deg b < deg q` for coprime
  `p, q` — the `ExtendedEuclidean(p, q, rhs)` step of Bronstein's §5.3 `HermiteReduce`.
* **`cfpow c n = cⁿ`** / **`cresultantG fuel p q = res(p, q)`** (Euclidean-PRS resultant) /
  **`clagNumG`**, **`cinterpolateG`** (Lagrange interpolation) — the residue-resultant building blocks
  used by §5.6's `cResidueResultantTower`. -/

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

/-! ### Generic univariate resultant over a `CField` (Euclidean-PRS route)

`cresultantG fuel p q = res(p, q) ∈ α`, the generic mirror of `Compute.cresultant` over any
`[CField α]` (ℚ-arithmetic replaced by `CField`/`CPolyG` ops): the Euclidean polynomial-remainder
sequence identity `res(p, q) = (−1)^(deg p·deg q)·lc(q)^(deg p − deg r)·res(q, r)` with `r = p mod q`,
bottoming out at `res(p, c) = c^(deg p)` for a constant `q = c`. Reduces over the tower
(`native_decide`); `fuel ≥ deg p + deg q` is safe. -/

/-- **Generic power of a field element** `cfpow c n = cⁿ` over `[CField α]` (by `ℕ`-recursion). -/
def cfpow (c : α) : ℕ → α
  | 0 => CField.one
  | n + 1 => CField.mul c (cfpow c n)

/-- **Generic univariate resultant** `cresultantG fuel p q = res(p, q) ∈ α`, fuel-bounded, via the
Euclidean polynomial-remainder-sequence identity over `[CField α]`. With `r = p mod q`, `dp = deg p`,
`dq = deg q`, `dr = deg r`: `res(p, q) = (−1)^(dp·dq)·lc(q)^(dp − dr)·res(q, r)`, bottoming out at
`res(p, c) = c^(deg p)` for a constant `q = c`, `res(p, 0) = 1` if `p` constant else `0`. Mirrors
`Compute.cresultant`; `fuel ≥ deg p + deg q` is safe. -/
def cresultantG : ℕ → CPolyG α → CPolyG α → α
  | 0, _, _ => CField.zero
  | fuel + 1, p, q =>
    let p := cnormG p
    let q := cnormG q
    if cisZeroG q then
      if (p : List α).length ≤ 1 then CField.one else CField.zero
    else if (q : List α).length ≤ 1 then
      cfpow (cleadG q) (cdegG p)
    else if (p : List α).length < (q : List α).length then
      let s := cfpow (CField.neg CField.one) (cdegG p * cdegG q)
      CField.mul s (cresultantG fuel q p)
    else
      let r := cnormG (cmodG (fuel + 1) p q)
      let sign := cfpow (CField.neg CField.one) (cdegG p * cdegG q)
      let lcpow := cfpow (cleadG q) (cdegG p - cdegG r)
      CField.mul (CField.mul sign lcpow) (cresultantG fuel q r)

/-! ### Generic Lagrange interpolation over a `CField`

`cinterpolateG pts = R(z) ∈ CPolyG α` with `R(zₖ) = yₖ`, the generic mirror of `Compute.cinterpolate`
over a field `α` (distinct abscissas `zₖ`). `∑ₖ yₖ · ∏_{j≠k}(z − zⱼ)/(zₖ − zⱼ)` built with
`cmulG`/`caddG`/`cscaleG` and the `CField.div`/`CField.inv` scalar `1/∏(zₖ − zⱼ)`. -/

/-- **Generic Lagrange basis numerator** `clagNumG zs = ∏ⱼ (z − zⱼ)` over abscissas `zs` (call with the
`k`-th abscissa removed). Built from the degree-1 factors `[−zⱼ, 1]` via `cmulG`. -/
def clagNumG : List α → CPolyG α
  | [] => [CField.one]
  | z :: zs => cmulG [CField.neg z, CField.one] (clagNumG zs)

/-- **Generic Lagrange interpolation** `cinterpolateG pts = R(z)` with `R(zₖ) = yₖ` for each
`(zₖ, yₖ) ∈ pts` (distinct abscissas, over the field `α`): `∑ₖ yₖ · ∏_{j≠k}(z − zⱼ)/(zₖ − zⱼ)`. The
scalar `1/∏(zₖ − zⱼ)` is a `CField.inv`; the per-term polynomial uses `cmulG`/`cscaleG`/`caddG`. -/
def cinterpolateG (pts : List (α × α)) : CPolyG α :=
  let zs := pts.map Prod.fst
  let term : α × α → CPolyG α := fun (zk, yk) =>
    let others := zs.filter (fun zj => CField.isZero (CField.sub zj zk) = false)
    let num := clagNumG others
    let denom := others.foldl (fun acc zj => CField.mul acc (CField.sub zk zj)) CField.one
    cscaleG (CField.div yk denom) num
  cnormG (pts.foldl (fun acc p => caddG acc (term p)) [])

end CPolyG

end DeepWiki.SymbolicIntegration
