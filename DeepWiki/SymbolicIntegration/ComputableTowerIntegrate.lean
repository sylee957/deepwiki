import DeepWiki.SymbolicIntegration.ComputableTowerField
import DeepWiki.SymbolicIntegration.ComputableTowerDeriv
import DeepWiki.SymbolicIntegration.ComputableHermiteTower
import DeepWiki.SymbolicIntegration.ComputableSplitSquarefree

/-! # The generic integration pipeline over arbitrary-depth differential towers
`ComputableTowerField`/`ComputableTowerDeriv` built the generic fraction-field carrier `QFunNZG α`
(the next tower level ℚ(x)(t₁)(t₂)…) with a *computable* `CField` instance AND a *computable*
derivation tower (`CDiffField (QFunNZG α)`, `towerDerivQFunNZG`). What was still
**`QFunNZ`-hardwired** is the §3.5/§5.3 integration pipeline: `cSplitFactorFast`,
`canonicalRepresentationFast`, `cHermiteReduceTower` (`ComputableSplitFactorFast`/
`ComputableCanonicalRep`/`ComputableHermiteTower`). Those are already on the **generic** engine ops
(`caddG`/`cmulG`/`cmonomialDeriv`/`cdivG`/…) — the *only* `QFunNZ`-specific call is the fraction-free
gcd `cgcdFF` (with its `BPoly = ℚ[x][t]` `clearDenoms` bridge).

This file produces **generic copies** (suffix `G`) over `[CField α] [CFieldDomain α] [CDiffField α]`,
replacing every `cgcdFF fuel p q` with `cgcdMonicG fuel p q := cmonicG (cgcdExtG fuel p q).1` — the
already-generic Euclidean gcd (validated at tower level 2 in `ComputableTowerField`). We accept the
ℚ(x)-coefficient swell of the Euclidean kernel: it is a separate optimization, and the small
level-2 validations stay in budget.

* **`cgcdMonicG`** — the monic gcd via the generic extended Euclidean `cgcdExtG`, the generic
  drop-in for `cgcdFF`.
* **`cSplitFactorFastG`** (§3.5 special/normal split `p = pₙ·pₛ` via the derivation `D` + gcd).
* **`cSqfreeYunFFG`** (Yun squarefree factorization in `t`, the formal `dp/dt`) — what the Hermite
  reduction factors the denominator with.
* **`canonicalRepresentationFastG`** (the `a/d → (fₚ, (b, dₛ), (c, dₙ))` canonical representation),
  reusing the already-generic Bézout helpers `cbezoutOne`/`cextendedEuclideanSplit`.
* **`cHermiteReduceTowerG`** (the transcendental Hermite reduction of the simple normal part →
  rational `g` + reduced remainder — the RATIONAL PART of the integral), reusing the already-generic
  inner loop `cHermiteReduceTowerInner`/`cdiophantineG`.

**★ The headline `native_decide`** runs `canonicalRepresentationFastG` + `cHermiteReduceTowerG` on a
concrete proper fraction over `CPolyG (QFunNZG (QFunNZG ℚ)) = ℚ(x)(t₁)[t₂]` whose denominator has a
**repeated `t₂`-factor**, and certifies `D(g) + h = f`: tower integration, rational part, executing
at **level 2**. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### The generic monic gcd — the drop-in for `cgcdFF`

`cgcdFF` (the `QFunNZ`-specific fraction-free primitive PRS) and the generic Euclidean
`cgcdExtG` compute the *same* gcd up to a unit; `cgcdFF` already monic-normalizes. The generic
replacement is `cmonicG (cgcdExtG fuel p q).1`: the gcd component of the extended Euclidean triple,
monic-normalized over the field. It carries the ℚ(x)-coefficient swell of the field-division kernel
(that is the documented optimization gap), but is fully `[CField α]`-generic — it runs at any tower
level (validated at level 2 in `ComputableTowerField`). -/

/-- **Generic monic gcd** `cgcdMonicG fuel p q = monic gcd(p, q)`: the gcd component of the generic
extended Euclidean `cgcdExtG`, monic-normalized (`cmonicG`). The `[CField α]`-generic drop-in for the
`QFunNZ`-specific fraction-free `cgcdFF` (same gcd up to a unit, both monic). Runs at any tower
level. -/
def cgcdMonicG (fuel : ℕ) (p q : CPolyG α) : CPolyG α :=
  cmonicG (cgcdExtG fuel p q).1

end CPolyG

/-! ### Generic `splitFactor` over the tower (§3.5)

`cSplitFactorFastG` is the `[CField α] [CDiffField α]`-generic mirror of `cSplitFactorFast`: Bronstein's
splitting-factorization loop with the generic monic gcd `cgcdMonicG` (for the two gcds `gcd(p, Dp)` and
`gcd(p, dp/dt)`) and the generic exact division `cdivG`. `Dp = cmonomialDeriv Dt p` is the differential
derivation (needs `[CDiffField α]`); `dp/dt = cderivG p` the formal `t`-derivative. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

/-- **Generic splitting-factorization loop** (Bronstein §3.5): `cSplitFactorFastG Dt fuel p =
(pₙ, pₛ)`, the same recursion as `cSplitFactorFast` but on a generic `[CField α] [CDiffField α]`
carrier with the generic monic gcd `cgcdMonicG` for the two gcds `gcd(p, Dp)` and `gcd(p, dp/dt)`. One
step extracts `S = gcd(p, Dp)/gcd(p, dp/dt)` (`Dp = cmonomialDeriv Dt p` the differential derivation,
`dp/dt = cderivG p` the formal one); constant `S` ⇒ `p` is normal, else recurse on `p/S` and accumulate
`S` into the special part. Fuel-bounded; runs at any tower level. -/
def cSplitFactorFastG (Dt : CPolyG α) : ℕ → CPolyG α → CPolyG α × CPolyG α
  | 0, p => (p, [CField.one])
  | fuel + 1, p =>
    let S := cdivG (fuel + 1) (cgcdMonicG (fuel + 1) p (cmonomialDeriv Dt p))
      (cgcdMonicG (fuel + 1) p (cderivG p))
    if cdegG S = 0 then (p, [CField.one])
    else
      let (qn, qs) := cSplitFactorFastG Dt fuel (cdivG (fuel + 1) p S)
      (qn, cmulG S qs)

end CPolyG

/-! ### Generic Yun squarefree factorization in `t` (the formal derivative)

`cSqfreeYunFFG` is the `[CField α]`-generic mirror of `cSqfreeYunFF`: Yun's squarefree factorization in
`t` using the *formal* derivative `dp/dt = cderivG` (NOT the differential `D`), with the generic monic
gcd `cgcdMonicG` everywhere. Returns the position-indexed list `[p₁, …, pₘ]` (`pᵢ` the monic squarefree
part of multiplicity `i`), so `p` is associate to `∏ᵢ pᵢ^i`. This is what `cHermiteReduceTowerG` factors
the denominator with. It needs only `[CField α]` (the formal derivative `cderivG` is field-only). -/

namespace CPolyG

variable {α : Type*} [CField α]

/-- Yun's main loop (generic): from `(b, d, i)` emit `pᵢ = cgcdMonicG b d` (monic), recurse on
`bᵢ₊₁ = b/pᵢ`, `dᵢ₊₁ = d/pᵢ − bᵢ₊₁'` (the formal `'`). Stops when `b` is constant. The generic mirror
of `cSqfreeYunFFgo` with `cgcdMonicG` for `cgcdFF`. -/
def cSqfreeYunFFGgo (fuel : ℕ) : ℕ → CPolyG α → CPolyG α → List (CPolyG α)
  | 0, _, _ => []
  | fo + 1, b, d =>
    if cdegG b = 0 then []
    else
      let p := cmonicG (cgcdMonicG fuel b d)
      let b' := cdivG fuel b p
      let d' := csubG (cdivG fuel d p) (cderivG b')
      p :: cSqfreeYunFFGgo fuel fo b' d'

/-- **Generic Yun squarefree factorization in `t`** `cSqfreeYunFFG fuel p = [p₁, …, pₘ]`: the
purely-algebraic squarefree factorization in `t` (the formal derivative `dp/dt = cderivG`), with the
generic monic gcd `cgcdMonicG` for `cgcdFF`. With `g = cgcdMonicG p (cderivG p)`, `b₁ = p/g`,
`d₁ = p'/g − b₁'`, the recurrence `pᵢ = cgcdMonicG bᵢ dᵢ` peels the monic squarefree part of
multiplicity `i`. `p` is associate to `∏ᵢ pᵢ^i`. `[CField α]`-generic — runs at any tower level. -/
def cSqfreeYunFFG (fuel : ℕ) (p : CPolyG α) : List (CPolyG α) :=
  let g := cgcdMonicG fuel p (cderivG p)
  let b1 := cdivG fuel p g
  let d1 := csubG (cdivG fuel (cderivG p) g) (cderivG b1)
  cSqfreeYunFFGgo fuel fuel b1 d1

end CPolyG

/-! ### Generic canonical representation over the tower (§3.5)

`canonicalRepresentationFastG` is the `[CField α] [CDiffField α]`-generic mirror of
`canonicalRepresentationFast`: it splits `f = a/d` (d monic) into `(fₚ, fₛ, fₙ) = (q, (b, dₛ), (c, dₙ))`.
The denominator split `d = dₛ·dₙ` uses the generic `cSplitFactorFastG`; the Bézout-split of the
remainder reuses the **already-generic** `cbezoutOne`/`cextendedEuclideanSplit` from
`ComputableCanonicalRep` (those need only `[CField α]`). -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

/-- **Generic `CanonicalRepresentation`** (Bronstein §3.5, p.103) over the tower:
`canonicalRepresentationFastG Dt fuel (a, d) = (fₚ, fₛ, fₙ) = (q, (b, dₛ), (c, dₙ))` for `f = a/d`
(`d` monic). Steps: divide `a = q·d + r` (`cdivmodG`); split the denominator `d = dₛ·dₙ`
(`cSplitFactorFastG`, generic); Bézout-split `r` over the coprime `(dₙ, dₛ)` (`cextendedEuclideanSplit`
with `cbezoutOne`, the already-generic helpers). The reduced part is `b/dₛ`, the simple part `c/dₙ`.
`[CField α] [CDiffField α]`-generic — runs at any tower level. -/
def canonicalRepresentationFastG (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) :
    CPolyG α × (CPolyG α × CPolyG α) × (CPolyG α × CPolyG α) :=
  let (q, r) := cdivmodG fuel a d
  let (dn, ds) := cSplitFactorFastG Dt fuel d
  let (u, w) := cbezoutOne fuel dn ds
  let (b, c) := cextendedEuclideanSplit fuel dn ds r u w
  (q, (b, ds), (c, dn))

/-! ### Generic transcendental Hermite reduction over the tower (§5.3) — the RATIONAL PART

`cHermiteReduceTowerG` is the `[CField α] [CDiffField α]`-generic mirror of `cHermiteReduceTower`:
Bronstein's `HermiteReduce(f, D)` (§5.3, quadratic version) rewrites the normal part `fₙ = a/d` of an
element of a monomial extension as `D(g) + h` with `h`'s denominator squarefree — `g` is the integral's
**rational part**. The squarefree factorization uses the generic `cSqfreeYunFFG`; the inner Bézout loop
reuses the already-generic `cHermiteReduceTowerInner`/`cdiophantineG`. The monomial derivation `D =
cmonomialDeriv Dt` needs `[CDiffField α]`. -/

/-- **Generic transcendental Hermite reduction** `cHermiteReduceTowerG Dt fuel a d = ((gnum, gden),
(h_num, h_den))` (Bronstein §5.3, p.139) over the tower: input `f = a/d` reduced/normal (`d` monic,
squarefree-factorable, `deg a < deg d`), output the rational part `g = gnum/gden` (already integrated)
and the residual `h = h_num/h_den` with `h_den` squarefree, satisfying `D(g) + h = a/d` for the monomial
derivation `D = cmonomialDeriv Dt`. The generic mirror of `cHermiteReduceTower`: squarefree-factor `d`
with the generic `cSqfreeYunFFG`; for each factor `(v, i)` of multiplicity `i ≥ 2`, run the already-
generic `cHermiteReduceTowerInner`; recover `h_num` over the squarefree radical `Dstar = ∏ᵢ vᵢ` exactly
from `a/d = D(g) + h_num/Dstar`. `[CField α] [CDiffField α]`-generic — runs at any tower level. -/
def cHermiteReduceTowerG (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) :
    (CPolyG α × CPolyG α) × (CPolyG α × CPolyG α) :=
  let factors := cSqfreeYunFFG fuel d                          -- `[v₁, …, vₘ]`, vᵢ of multiplicity i
  let Dstar := factors.foldl (fun acc vi => cmulG acc vi) [CField.one]   -- squarefree radical ∏ᵢ vᵢ
  let g : CPolyG α × CPolyG α := factors.zipIdx.foldl
    (fun (gAcc : CPolyG α × CPolyG α) (vi, idx) =>
      let i := idx + 1
      if i ≤ 1 then gAcc
      else
        let Vi_pow := cpowG vi i
        let u := cdivG fuel d Vi_pow
        let (gloc, _) := cHermiteReduceTowerInner Dt fuel vi u (i - 1) a ([CField.zero], [CField.one])
        (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))  -- gAcc + gloc
    ([CField.zero], [CField.one])
  let (gnum, gden) := g
  -- residual numerator `h_num` over `Dstar`, from `a/d − D(g) = h_num/Dstar`:
  let gprimeNum := csubG (cmulG (cmonomialDeriv Dt gnum) gden) (cmulG gnum (cmonomialDeriv Dt gden))
  let gden2 := cmulG gden gden
  let resNum := csubG (cmulG a gden2) (cmulG d gprimeNum)
  let resDen := cmulG d gden2
  let hNum := cdivG fuel (cmulG resNum Dstar) resDen
  ((cnormG gnum, cnormG gden), (cnormG hNum, cnormG Dstar))

end CPolyG

/-! ### ★ The KEY VALIDATION: tower integration, RATIONAL PART, at LEVEL 2 (`native_decide`)

This is the headline. We run `cHermiteReduceTowerG` over `CPolyG (QFunNZG (QFunNZG ℚ)) =
ℚ(x)(t₁)[t₂]` (tower **level 2**, the new monomial `t₂`) on a concrete proper fraction whose
denominator has a **repeated `t₂`-factor**, and certify `D(g) + h = f`. The setting is Bronstein's
Example 5.3.1 lifted one level up: `t₂ = tan` (the monomial derivative is `Dt₂ = t₂² + 1`), and
`f = a/d = 1/t₂²`, whose denominator `d = t₂²` has the **normal factor `t₂` of multiplicity 2**
(`t₂` is normal: `gcd(t₂, Dt₂) = gcd(t₂, t₂²+1) = 1`). The reduction lowers the multiplicity:
`g = −1/t₂`, `h = −1` (squarefree denominator `t₂`), with `D(−1/t₂) = (t₂²+1)/t₂²` so
`D(g) + h = (t₂²+1)/t₂² − 1 = 1/t₂² = f`.

All coefficients are level-2 *constants* (elements of ℚ ⊂ ℚ(x)(t₁) = `Lvl2`), so the engine genuinely
runs the level-2 `CField`/`CDiffField` instances over `CPolyG Lvl2`. The `CField (QFunNZG (QFunNZG ℚ))`
and `CDiffField (QFunNZG (QFunNZG ℚ))` instances are `[CField …]`-computable with `Prop`-erased subtype
proofs, so nothing noncomputable reaches the native compiler — `native_decide` reduces. The load-bearing
check is the cleared-denominator form of `D(gnum/gden) + h_num/h_den = a/d`, equating numerators over the
common denominator `gden²·h_den·d`: `(gprimeNum·h_den + h_num·gden²)·d = a·(gden²·h_den)`. -/

open QFunNZG

/-- Level-2 scalar `2 = 1 + 1 ∈ Lvl2 = ℚ(x)(t₁)`. -/
def lvl2Two : Lvl2 := CField.add CField.one CField.one

/-- Level-2 monomial derivative `Dt₂ = t₂² + 1` over `CPolyG Lvl2 = ℚ(x)(t₁)[t₂]` (so `t₂ = tan`,
Bronstein Example 5.3.1 lifted to level 2; constant coefficients in ℚ ⊂ ℚ(x)(t₁)). -/
def towerHermiteLvl2Dt : CPolyG Lvl2 := [CField.one, CField.zero, CField.one]

/-- Level-2 numerator `a = 1` over `CPolyG Lvl2` (constant coefficient `1 ∈ ℚ(x)(t₁)`). -/
def towerHermiteLvl2A : CPolyG Lvl2 := [CField.one]

/-- Level-2 denominator `d = t₂²` over `CPolyG Lvl2` — the normal factor `t₂` of multiplicity 2 (under
`Dt₂ = t₂² + 1`, `t₂` is normal and `t₂²` its square), so Hermite lowers the power. -/
def towerHermiteLvl2D : CPolyG Lvl2 := [CField.zero, CField.zero, CField.one]

/-- **★ `cHermiteReduceTowerG` computes the RATIONAL PART at tower level 2** (`native_decide`): for
`f = a/d = 1/t₂²` over `ℚ(x)(t₁)[t₂]` (`= CPolyG (QFunNZG (QFunNZG ℚ))`, tower level 2) with the monomial
derivation `D = cmonomialDeriv Dt`, `Dt₂ = t₂² + 1` (`t₂ = tan`), the computed
`((gnum, gden), (h_num, h_den))` satisfies the Hermite identity `D(gnum/gden) + h_num/h_den = a/d`. With
`D(g) = gprimeNum/gden²`, `gprimeNum = D(gnum)·gden − gnum·D(gden)`, equate numerators over `gden²·h_den·d`:
`(gprimeNum·h_den + h_num·gden²)·d = a·(gden²·h_den)`, by `cisZeroG` of the difference over ℚ(x)(t₁)[t₂].
The denominator `d = t₂²` has a repeated normal factor `t₂`, so this exercises the genuine
multiplicity-lowering step (`g = −1/t₂`, `h = −1`). **This is the deliverable: tower integration, rational
part, executing at LEVEL 2** — the whole generic engine (`cSqfreeYunFFG`/`cgcdMonicG`/`cHermiteReduceTowerInner`/
`cmonomialDeriv`) reduces over `ℚ(x)(t₁)[t₂]`. -/
theorem towerHermiteLvl2_rationalPart :
    (let res := CPolyG.cHermiteReduceTowerG towerHermiteLvl2Dt 12
        towerHermiteLvl2A towerHermiteLvl2D
      let gnum := res.1.1
      let gden := res.1.2
      let hNum := res.2.1
      let hDen := res.2.2
      let Dgnum := CPolyG.cmonomialDeriv towerHermiteLvl2Dt gnum
      let Dgden := CPolyG.cmonomialDeriv towerHermiteLvl2Dt gden
      let gprimeNum := CPolyG.csubG (CPolyG.cmulG Dgnum gden) (CPolyG.cmulG gnum Dgden)
      let gden2 := CPolyG.cmulG gden gden
      let lhs := CPolyG.cmulG
        (CPolyG.caddG (CPolyG.cmulG gprimeNum hDen) (CPolyG.cmulG hNum gden2)) towerHermiteLvl2D
      let rhs := CPolyG.cmulG towerHermiteLvl2A (CPolyG.cmulG gden2 hDen)
      CPolyG.cisZeroG (CPolyG.csubG lhs rhs)) = true := by native_decide

/-- **The level-2 residual `h` has a squarefree denominator** (`native_decide`): the Hermite reduction
lowered the multiplicity-2 factor `t₂` of `d = t₂²` to multiplicity 1, so the residual denominator
`h_den = Dstar = t₂` is squarefree (`t₂`-degree 1) over ℚ(x)(t₁)[t₂], as the reduction guarantees. -/
theorem towerHermiteLvl2_residual_degree :
    CPolyG.cdegG (CPolyG.cHermiteReduceTowerG towerHermiteLvl2Dt 12
      towerHermiteLvl2A towerHermiteLvl2D).2.2 = 1 := by native_decide

#print axioms towerHermiteLvl2_rationalPart

end DeepWiki.SymbolicIntegration
