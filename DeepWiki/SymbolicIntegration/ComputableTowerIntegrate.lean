import DeepWiki.SymbolicIntegration.ComputableTowerField
import DeepWiki.SymbolicIntegration.ComputableTowerDeriv
import DeepWiki.SymbolicIntegration.ComputableHermiteTower
import DeepWiki.SymbolicIntegration.ComputableSplitSquarefree
import DeepWiki.SymbolicIntegration.ComputableTowerGcdFFCore

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
replacing every `cgcdFF fuel p q` with the **flat** generic fraction-free gcd
`CFracGcdCore.cgcdFFCore fuel p q` (`ComputableTowerGcdFFCore`) — the recursive primitive-PRS gcd that
stays polynomial-sized over the tower (it AGREES with `cgcdFF` and the swelling Euclidean `cgcdMonicG`,
both being the unique monic gcd, but computes it without the fraction-field coefficient swell that made
`cIntegrateG`-at-`QFunNZ` take ~86 s). Every pipeline def that calls a `t`-gcd therefore carries the
`[CFracGcdCore α]` constraint, resolved automatically at every concrete tower level (base `CFracGcdCore ℚ`
+ recursive `CFracGcdCore (QFunNZG β)`).

* **`cgcdMonicG`** — the (super-exponentially swelling) monic gcd via the generic extended Euclidean
  `cgcdExtG`, kept for the `ComputableTowerReduce` correctness layer; the pipeline now calls the flat
  `CFracGcdCore.cgcdFFCore` instead.
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

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α]

/-- **Generic splitting-factorization loop** (Bronstein §3.5): `cSplitFactorFastG Dt fuel p =
(pₙ, pₛ)`, the same recursion as `cSplitFactorFast` but on a generic `[CField α] [CDiffField α]`
carrier with the flat fraction-free gcd `CFracGcdCore.cgcdFFCore` for the two gcds `gcd(p, Dp)` and
`gcd(p, dp/dt)`. One step extracts `S = gcd(p, Dp)/gcd(p, dp/dt)` (`Dp = cmonomialDeriv Dt p` the
differential derivation, `dp/dt = cderivG p` the formal one); constant `S` ⇒ `p` is normal, else recurse
on `p/S` and accumulate `S` into the special part. Fuel-bounded; runs at any tower level. -/
def cSplitFactorFastG (Dt : CPolyG α) : ℕ → CPolyG α → CPolyG α × CPolyG α
  | 0, p => (p, [CField.one])
  | fuel + 1, p =>
    let S := cdivG (fuel + 1) (CFracGcdCore.cgcdFFCore (fuel + 1) p (cmonomialDeriv Dt p))
      (CFracGcdCore.cgcdFFCore (fuel + 1) p (cderivG p))
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

variable {α : Type*} [CField α] [CFracGcdCore α]

/-- Yun's main loop (generic): from `(b, d, i)` emit `pᵢ = CFracGcdCore.cgcdFFCore b d` (monic), recurse
on `bᵢ₊₁ = b/pᵢ`, `dᵢ₊₁ = d/pᵢ − bᵢ₊₁'` (the formal `'`). Stops when `b` is constant. The generic mirror
of `cSqfreeYunFFgo` with the flat fraction-free gcd `CFracGcdCore.cgcdFFCore` for `cgcdFF`. -/
def cSqfreeYunFFGgo (fuel : ℕ) : ℕ → CPolyG α → CPolyG α → List (CPolyG α)
  | 0, _, _ => []
  | fo + 1, b, d =>
    if cdegG b = 0 then []
    else
      let p := cmonicG (CFracGcdCore.cgcdFFCore fuel b d)
      let b' := cdivG fuel b p
      let d' := csubG (cdivG fuel d p) (cderivG b')
      p :: cSqfreeYunFFGgo fuel fo b' d'

/-- **Generic Yun squarefree factorization in `t`** `cSqfreeYunFFG fuel p = [p₁, …, pₘ]`: the
purely-algebraic squarefree factorization in `t` (the formal derivative `dp/dt = cderivG`), with the flat
fraction-free gcd `CFracGcdCore.cgcdFFCore` for `cgcdFF`. With `g = CFracGcdCore.cgcdFFCore p (cderivG p)`,
`b₁ = p/g`, `d₁ = p'/g − b₁'`, the recurrence `pᵢ = CFracGcdCore.cgcdFFCore bᵢ dᵢ` peels the monic
squarefree part of multiplicity `i`. `p` is associate to `∏ᵢ pᵢ^i`.
`[CField α] [CFracGcdCore α]`-generic — runs at any tower level. -/
def cSqfreeYunFFG (fuel : ℕ) (p : CPolyG α) : List (CPolyG α) :=
  let g := CFracGcdCore.cgcdFFCore fuel p (cderivG p)
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

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α]

/-- **Generic `CanonicalRepresentation`** (Bronstein §3.5, p.103) over the tower:
`canonicalRepresentationFastG Dt fuel (a, d) = (fₚ, fₛ, fₙ) = (q, (b, dₛ), (c, dₙ))` for `f = a/d`
(`d` monic). Steps: divide `a = q·d + r` (`cdivmodG`); split the denominator `d = dₛ·dₙ`
(`cSplitFactorFastG`, generic); Bézout-split `r` over the coprime `(dₙ, dₛ)` (`cextendedEuclideanSplit`
with `cbezoutOne`, the already-generic helpers). The reduced part is `b/dₛ`, the simple part `c/dₙ`.
`[CField α] [CDiffField α] [CFracGcdCore α]`-generic — runs at any tower level. -/
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

/-! ### Level-2 validation of `canonicalRepresentationFastG` — the parts recombine to `f`

The canonical-representation companion to the Hermite check, at the same tower level. `f = a/d` with
`a = t₂³` and the monic `d = (t₂−1)(t₂−2) = t₂² − 3t₂ + 2` over `ℚ(x)(t₁)[t₂]`, monomial `t₂` with
`Dt₂ = t₂ − 1` (so the root `t₂ = 1` is special, `t₂ = 2` normal). `canonicalRepresentationFastG`
returns `(q, (b, dₛ), (c, dₙ))`; the load-bearing identity `q + b/dₛ + c/dₙ = a/d` is checked by
clearing denominators: numerator `N = q·dₛ·dₙ + b·dₙ + c·dₛ`, identity `N · d = a · (dₛ·dₙ)`, by
`cisZeroG` of the difference over ℚ(x)(t₁)[t₂]. Scalar-robust (independent of the split's internal
scalar ambiguity). -/

/-- Level-2 scalar `−1 ∈ Lvl2 = ℚ(x)(t₁)`. -/
def lvl2NegOne : Lvl2 := CField.neg CField.one

/-- Level-2 scalar `−2 ∈ Lvl2`. -/
def lvl2NegTwo : Lvl2 := CField.neg (CField.add CField.one CField.one)

/-- Level-2 scalar `−3 ∈ Lvl2`. -/
def lvl2NegThree : Lvl2 := CField.neg (CField.add CField.one (CField.add CField.one CField.one))

/-- Level-2 canonical-rep numerator `a = t₂³` over `ℚ(x)(t₁)[t₂]` (constant coefficients in ℚ). -/
def towerCanRepLvl2A : CPolyG Lvl2 := [CField.zero, CField.zero, CField.zero, CField.one]

/-- Level-2 canonical-rep denominator `d = (t₂−1)(t₂−2) = t₂² − 3t₂ + 2` over `ℚ(x)(t₁)[t₂]` (monic). -/
def towerCanRepLvl2D : CPolyG Lvl2 := [lvl2Two, lvl2NegThree, CField.one]

/-- Level-2 monomial derivative `Dt₂ = t₂ − 1` (root `t₂ = 1` special, `t₂ = 2` normal). -/
def towerCanRepLvl2Dt : CPolyG Lvl2 := [lvl2NegOne, CField.one]

/-- **`canonicalRepresentationFastG` recombines to `f` at tower level 2** (`native_decide`): for
`f = t₂³/((t₂−1)(t₂−2))` over `ℚ(x)(t₁)[t₂]` (`= CPolyG (QFunNZG (QFunNZG ℚ))`, tower level 2) with
`Dt₂ = t₂ − 1`, the computed parts `(q, (b, dₛ), (c, dₙ))` satisfy the canonical identity
`q + b/dₛ + c/dₙ = a/d` — checked, after clearing denominators, as
`(q·dₛ·dₙ + b·dₙ + c·dₛ)·d = a·(dₛ·dₙ)` via `cisZeroG` of the difference over ℚ(x)(t₁)[t₂]. The generic
canonical-representation engine (`cSplitFactorFastG` denominator split + Bézout) executes over the tower
at level 2 and its output genuinely reconstructs `f`. -/
theorem towerCanRepLvl2_recombines :
    (let res := CPolyG.canonicalRepresentationFastG towerCanRepLvl2Dt 8
        towerCanRepLvl2A towerCanRepLvl2D
      let q := res.1
      let b := res.2.1.1
      let ds := res.2.1.2
      let c := res.2.2.1
      let dn := res.2.2.2
      let dsdn := CPolyG.cmulG ds dn
      let num := CPolyG.caddG (CPolyG.caddG (CPolyG.cmulG q dsdn) (CPolyG.cmulG b dn))
        (CPolyG.cmulG c ds)
      CPolyG.cisZeroG (CPolyG.csubG (CPolyG.cmulG num towerCanRepLvl2D)
        (CPolyG.cmulG towerCanRepLvl2A dsdn))) = true := by native_decide

#print axioms towerCanRepLvl2_recombines

/-! ## STRETCH — the logarithmic part (Rothstein–Trager §5.6) and the tower integral `cIntegrateG`

The rational part (Hermite) is done. The remaining piece of the elementary integral `∫ f = g + ∑ᵢ
cᵢ·log(vᵢ)` is the **logarithmic part**: the Rothstein–Trager residue criterion (§5.6). For a simple
`h = a/d` (`d` squarefree), `∫ h = ∑_{R(c)=0} c·log(gcd_t(d, a − c·Dd))` with `R(z) = res_t(d, a − z·Dd)`
the residue resultant.

The generic engine pieces `cevalG`/`cresultantG`/`cinterpolateG` are *already* `[CField α]`-generic. The
ONLY `QFunNZ`-specific barrier beyond `cgcdFF` is the embedding `ℚ → α` (`ofConstNZ`): the residue
resultant samples `z` at the natural nodes `0, 1, …, n`, and a residue is a field constant. We lift the
nodes through the existing `cnatCastG : ℕ → α` (`[CField α]`-only), and take the residue **candidates as
`α` elements** (the natural generic form) — so the whole log part generalizes. `cratCastG` additionally
gives the `ℚ → α` embedding for convenience. -/

namespace CPolyG

variable {α : Type*} [CField α]

/-- **Rational into a `CField`** `cratCastG q = (sign · cnatCastG |num|) / cnatCastG den`: embed `q ∈ ℚ`
into any `[CField α]` via the numerator/denominator natural casts (`cnatCastG`) and a sign, all from
`CField` ops. The generic `ℚ → α` constant embedding (the generic `ofConstNZ` at the scalar level). -/
def cratCastG (q : ℚ) : α :=
  let n : α := cnatCastG q.num.natAbs
  let nsigned : α := if q.num < 0 then CField.neg n else n
  CField.mul nsigned (CField.inv (cnatCastG q.den))

/-- **Generic Horner evaluation** `cHornerG p c = p(c) ∈ α`: evaluate the dense coefficient list `p`
(index = degree, low→high) at `c ∈ α` by Horner's rule. The generic mirror of `cevalG`
(`ComputableIntegrate`), redefined here to avoid that heavy import. Used to test whether a candidate
residue `c` is a root of the residue resultant `R(c) = 0`. Needs only `[CField α]`. -/
def cHornerG (p : CPolyG α) (c : α) : α :=
  (p : List α).foldr (fun coeff acc => CField.add coeff (CField.mul c acc)) CField.zero

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α]

/-! ### The generic residue resultant `R(z) = res_t(d, a − z·Dd)` and the log argument

`cResidueResultantTowerG` mirrors `cResidueResultantTower`: sample `R(zₖ) = res_t(d, a − zₖ·Dd)` at the
natural nodes `zₖ = cnatCastG k` (`k = 0…deg_t d`, the generic node lift replacing `ofConstNZ (k : ℚ)`)
and Lagrange-interpolate (`cinterpolateG`). `cLogArgTowerG` is `gcd_t(d, a − c·Dd)` (`cgcdMonicG` for
`cgcdFF`) for a residue `c : α`. Both reuse the already-generic `cresultantG`/`cmonomialDeriv`. -/

/-- **Generic `a − c·Dd`** `cAmcDdG Dt a d c` for a residue value `c : α`: `a − c·(cmonomialDeriv Dt d)`,
the polynomial in `t` whose `t`-gcd with `d` is the log argument at `c`. Generic mirror of `cAmcDd`. -/
def cAmcDdG (Dt a d : CPolyG α) (c : α) : CPolyG α :=
  csubG a (cscaleG c (cmonomialDeriv Dt d))

/-- **Generic residue resultant** `cResidueResultantTowerG Dt fuel a d = R(z) = res_t(d, a − z·Dd)`,
returned as a `CPolyG α` whose variable is the residue indeterminate `z` (Bronstein §5.6). Sample
`R(zₖ) = res_t(d, a − zₖ·Dd)` (`cresultantG`) at the natural nodes `zₖ = cnatCastG k` for
`k = 0, …, deg_t d` (the generic node lift, replacing `ofConstNZ (k : ℚ)`), then Lagrange-interpolate
(`cinterpolateG`). `deg_z R ≤ deg_t d`, so `deg_t d + 1` nodes are exact. `[CField α] [CDiffField α]`-
generic — runs at any tower level. -/
def cResidueResultantTowerG (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) : CPolyG α :=
  let n := cdegG d
  let pts : List (α × α) := (List.range (n + 1)).map (fun k =>
    let zk : α := cnatCastG k
    (zk, cresultantG fuel d (cAmcDdG Dt a d zk)))
  cinterpolateG pts

/-- **Generic log argument** `cLogArgTowerG Dt fuel a d c = gcd_t(d, a − c·Dd)` for a residue `c : α`
(Bronstein §5.6, the `g_i` inside `log`): the generic monic-in-`t` gcd (`cgcdMonicG`) of `d` and
`a − c·Dd`. Together with the residues `c` (roots of `cResidueResultantTowerG`),
`∑_c c·log(cLogArgTowerG … c)` is the logarithmic part of `∫ a/d`. -/
def cLogArgTowerG (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (c : α) : CPolyG α :=
  CFracGcdCore.cgcdFFCore fuel d (cAmcDdG Dt a d c)

/-! ### The generic rational-residue scan and logarithmic part

`cRationalResiduesG`/`cLogPartG` mirror `cRationalResidues`/`cLogPart`, but take the residue candidates
**as `α` elements** `cands : List α` (the generic form — a residue is a field constant). Keep those `c`
with `R(c) = 0` (`cHornerG R c`, `[CField α]`-generic Horner), and pair each with its log argument. -/

/-- **Generic rational/field residues** `cRationalResiduesG Dt fuel a d cands`: from the candidate list
`cands : List α`, keep those `c` that are roots of the residue resultant `R(z) =
cResidueResultantTowerG Dt fuel a d`, i.e. `R(c) = 0` (tested by `CField.isZero (cHornerG R c)`, the
generic Horner evaluation). The residues of the simple element `a/d` whose logarithmic part is
`∑ c·log(cLogArgTowerG … c)`. -/
def cRationalResiduesG (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α) : List α :=
  let R := cResidueResultantTowerG Dt fuel a d
  cands.filter (fun c => CField.isZero (cHornerG R c))

/-- **Generic logarithmic part** `cLogPartG Dt fuel a d cands = [(c, gcd_t(d, a − c·Dd)) | c ∈
residues]`: pair each residue `c : α` (from `cRationalResiduesG`) with its log argument
`cLogArgTowerG Dt fuel a d c`, so `∑ (c, v) ∈ cLogPartG, c·log(v)` is the residue logarithmic part of
`∫ a/d`. `[CField α] [CDiffField α]`-generic — runs at any tower level. -/
def cLogPartG (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α) : List (α × CPolyG α) :=
  (cRationalResiduesG Dt fuel a d cands).map (fun c => (c, cLogArgTowerG Dt fuel a d c))

end CPolyG

/-! ### The generic integral result and the cleared antiderivative identity

`IntegralResultG α` is the generic mirror of `IntegralResult`: the rational part `g = num/den ∈ α(t)`
plus the logarithmic part `[(cᵢ, vᵢ)]` (coefficients `cᵢ : α`, arguments `vᵢ : CPolyG α`).
`checkIdentityG` verifies the antiderivative identity `D(g) + ∑ᵢ cᵢ·(D(vᵢ)/vᵢ) = f`, cleared of
denominators — the generic mirror of `IntegralResult.checkIdentity`. -/

/-- **The generic integral result**: `∫ f = rational + ∑ᵢ coeff·log(arg)` over the tower, with
`rational = (num, den)` the rational part `g = num/den ∈ α(t)` and `logs = [(cᵢ, vᵢ)]` the logarithmic
part (each `cᵢ : α`, each `vᵢ : CPolyG α`). The generic mirror of `IntegralResult`. -/
structure IntegralResultG (α : Type*) [CField α] where
  /-- The rational part `g = num/den ∈ α(t)` of `∫ f`. -/
  rational : CPolyG α × CPolyG α
  /-- The logarithmic part `∑ᵢ coeff·log(arg)` of `∫ f` (`α`-coefficients, `CPolyG α` arguments). -/
  logs : List (α × CPolyG α)

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α]

/-- **The generic antiderivative identity, cleared of denominators** `checkIdentityG Dt res anum aden`:
`true` iff `res` is a genuine antiderivative of `f = anum/aden`, i.e. `D(g) + ∑ᵢ cᵢ·(D(vᵢ)/vᵢ) = f` for
`D = cmonomialDeriv Dt`. Accumulate `∑ᵢ cᵢ·D(vᵢ)/vᵢ` as a single fraction `(Lnum, Lden)` over `∏ᵢ vᵢ`,
add `D(g) = (D(gnum)·gden − gnum·D(gden))/gden²`, and equate with `f` over `gden²·Lden·aden`:
`(gprimeNum·Lden + Lnum·gden²)·aden = anum·(gden²·Lden)`, by `cisZeroG` of the cleared difference. The
generic mirror of `IntegralResult.checkIdentity` (`α` has no `DecidableEq`, hence the `cisZeroG∘csubG`
form). -/
def checkIdentityG (Dt : CPolyG α) (res : IntegralResultG α) (anum aden : CPolyG α) : Bool :=
  let gnum := res.rational.1
  let gden := res.rational.2
  let gprimeNum := csubG (cmulG (cmonomialDeriv Dt gnum) gden) (cmulG gnum (cmonomialDeriv Dt gden))
  let gden2 := cmulG gden gden
  let Lstart : CPolyG α × CPolyG α := ([CField.zero], [CField.one])
  let (Lnum, Lden) := res.logs.foldl
    (fun (acc : CPolyG α × CPolyG α) (cv : α × CPolyG α) =>
      let c := cv.1
      let v := cv.2
      let Dv := cmonomialDeriv Dt v
      let termNum := cscaleG c Dv
      (caddG (cmulG acc.1 v) (cmulG termNum acc.2), cmulG acc.2 v))
    Lstart
  let lhs := cmulG (caddG (cmulG gprimeNum Lden) (cmulG Lnum gden2)) aden
  let rhs := cmulG anum (cmulG gden2 Lden)
  cisZeroG (csubG lhs rhs)

/-! ### The generic reduced-case integration capstone and the tower integral driver

`cIntegrateReducedG` integrates a reduced/simple `f = a/d` over the tower: Hermite rational part
(`cHermiteReduceTowerG`) + Rothstein–Trager residue logs (`cLogPartG`). `cIntegrateG` is the assembled
top-level driver: canonical split (`canonicalRepresentationFastG`) + reduced capstone on the simple
normal part, returning `none` when the polynomial/special part is left non-disposed (the conservative
reduced-case driver — full poly/special handling over the generic tower is the documented continuation).
Candidates are `α` elements (the generic residue form). -/

/-- **The generic reduced-case integration capstone** `cIntegrateReducedG Dt fuel a d cands`: for
`f = a/d` reduced/normal (no polynomial or special part), `∫ f = g + ∑ c·log(v)`. Hermite-reduce
(`cHermiteReduceTowerG`) to the rational part `g = gnum/gden` and the simple residual `h = h_num/h_den`
(squarefree denominator), then take the residue log part of `h` (`cLogPartG`, residues drawn from
`cands : List α`). Returns the `IntegralResultG` `⟨(gnum, gden), [(c, v)]⟩`. `[CField α] [CDiffField α]`-
generic — runs at any tower level. -/
def cIntegrateReducedG (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α) :
    IntegralResultG α :=
  let ((gnum, gden), (hNum, hDen)) := cHermiteReduceTowerG Dt fuel a d
  let logs := cLogPartG Dt fuel hNum hDen cands
  ⟨(gnum, gden), logs⟩

/-- **The generic top-level tower integral** `cIntegrateG Dt fuel a d cands` (Bronstein Ch. 5, the
reduced-case driver over the tower): integrate `f = a/d ∈ α(t)` over `D = cmonomialDeriv Dt`, returning
`some ⟨(gnum, gden), [(cᵢ, vᵢ)]⟩` with `∫ f = gnum/gden + ∑ᵢ cᵢ·log(vᵢ)`, or `none`. Steps: (1)
`canonicalRepresentationFastG` splits `f = fₚ + fₛ + fₙ = q + (b/dₛ) + (c/dₙ)`; (2) the simple normal
part `fₙ = c/dₙ` is integrated by `cIntegrateReducedG` (Hermite + residue logs from `cands`); (3) if the
polynomial part `fₚ = q` and the special part `b/dₛ` both vanish, return the simple-part integral, else
`none` (the conservative reduced-case driver; the generic poly/special engines are the documented
continuation). `[CField α] [CDiffField α]`-generic — runs at any tower level. -/
def cIntegrateG (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α) :
    Option (IntegralResultG α) :=
  let (fp, (b, _ds), (cn, dn)) := canonicalRepresentationFastG Dt fuel a d
  let nrm := cIntegrateReducedG Dt fuel cn dn cands
  if cisZeroG fp && cisZeroG b then some nrm else none

end CPolyG

/-! ### ★★ The STRETCH validation: a FULL elementary tower integral at LEVEL 2 (`native_decide`)

Bronstein's Example 5.6.2 construction lifted to **tower level 2**. Over `CPolyG Lvl2 =
ℚ(x)(t₁)[t₂]` the monomial `t₂` is independent (`Dt₂ = 1`), and the simple integrand
`f = (1/2)·D(t₂+1)/(t₂+1) − (1/2)·D(t₂−1)/(t₂−1)` over ℚ(x)(t₁)(t₂) has the **known elementary
antiderivative** `(1/2)log(t₂+1) − (1/2)log(t₂−1)`. Since `D(t₂±1) = Dt₂ = 1`, the integrand is
`f = (1/2)/(t₂+1) − (1/2)/(t₂−1)`, assembled as a single fraction `a/d` with `d = (t₂+1)(t₂−1) =
t₂² − 1`. The residues of `R(z) = res_t(d, a − z·Dd)` are `±1/2` with log arguments `t₂ ± 1`.

The generic tower integrator `cIntegrateG` (canonical split + Hermite rational part + Rothstein–Trager
residue logs) runs over `CPolyG Lvl2` and recovers the integral: `g = 0`, residues `±1/2` from the
candidate set, logs `t₂ ± 1`. The headline check is the **antiderivative identity** `D(∫f) = f`
(`checkIdentityG`, cleared of denominators, by `cisZeroG`) — the whole elementary tower integral
executing and differentiating back to `f`, at level 2. All coefficients are ℚ-constants lifted into
`Lvl2` (via `cratCastG`), so the engine genuinely runs the level-2 `CField`/`CDiffField` instances. -/

open CPolyG

/-- Level-2 monomial derivative `Dt₂ = 1` over `CPolyG Lvl2 = ℚ(x)(t₁)[t₂]` (`t₂` independent). -/
def towerIntLvl2Dt : CPolyG Lvl2 := [CField.one]

/-- Level-2 log argument `v₊ = t₂ + 1` over `CPolyG Lvl2` (low→high in `t₂`). -/
def towerIntLvl2VPlus : CPolyG Lvl2 := [CField.one, CField.one]

/-- Level-2 log argument `v₋ = t₂ − 1` over `CPolyG Lvl2`. -/
def towerIntLvl2VMinus : CPolyG Lvl2 := [CField.neg CField.one, CField.one]

/-- Level-2 scalar `1/2 ∈ Lvl2` (the residue coefficient), via the generic `cratCastG`. -/
def towerIntLvl2Half : Lvl2 := cratCastG (1/2)

/-- The level-2 integrand numerator `a = (1/2)·D(v₊)·v₋ − (1/2)·D(v₋)·v₊` over `CPolyG Lvl2`, so
`a/d = (1/2)·D(v₊)/v₊ − (1/2)·D(v₋)/v₋` with `d = v₊·v₋`. Its elementary antiderivative is
`(1/2)log(v₊) − (1/2)log(v₋)`. -/
def towerIntLvl2Num : CPolyG Lvl2 :=
  csubG
    (cscaleG towerIntLvl2Half
      (cmulG (cmonomialDeriv towerIntLvl2Dt towerIntLvl2VPlus) towerIntLvl2VMinus))
    (cscaleG towerIntLvl2Half
      (cmulG (cmonomialDeriv towerIntLvl2Dt towerIntLvl2VMinus) towerIntLvl2VPlus))

/-- The level-2 integrand denominator `d = v₊·v₋ = (t₂+1)(t₂−1) = t₂² − 1` over `CPolyG Lvl2`. -/
def towerIntLvl2Den : CPolyG Lvl2 := cmulG towerIntLvl2VPlus towerIntLvl2VMinus

/-- The level-2 residue candidate set `{1/2, −1/2, 1, −1, 0}` as `Lvl2` constants (the residues `±1/2`
are inside; the rest are rejected by `R(c) ≠ 0`). -/
def towerIntLvl2Cands : List Lvl2 :=
  [cratCastG (1/2), cratCastG (-1/2), cratCastG 1, cratCastG (-1), cratCastG 0]

/-- **The recovered level-2 logarithmic part has length 2** (`native_decide`): the residue scan over
`ℚ(x)(t₁)[t₂]` finds exactly the two rational residues `±1/2` (log arguments `t₂ ± 1`), so the capstone's
`logs` list has length `2`, matching the Rothstein–Trager construction at tower level 2. -/
theorem towerIntLvl2_logs_length :
    (CPolyG.cIntegrateReducedG towerIntLvl2Dt 30 towerIntLvl2Num towerIntLvl2Den
      towerIntLvl2Cands).logs.length = 2 := by native_decide

/-- **★★ A FULL elementary tower integral at LEVEL 2, and `D(∫f) = f`** (`native_decide`, the stretch
deliverable). For the simple element `f = (1/2)·D(t₂+1)/(t₂+1) − (1/2)·D(t₂−1)/(t₂−1)` over
ℚ(x)(t₁)(t₂) (`= CPolyG (QFunNZG (QFunNZG ℚ))`, tower **level 2**, `Dt₂ = 1`), whose elementary
antiderivative is `(1/2)log(t₂+1) − (1/2)log(t₂−1)`, the assembled generic tower integrator
`cIntegrateReducedG` — canonical split, Hermite rational part, Rothstein–Trager residue logarithms —
returns an `IntegralResultG` whose **antiderivative identity** `D(rational) + ∑ᵢ cᵢ·(D(vᵢ)/vᵢ) = f` holds
**exactly**, checked cleared of denominators by `checkIdentityG` (`cisZeroG` of the cleared difference
over ℚ(x)(t₁)[t₂]). This is the stretch: the WHOLE elementary tower integral — rational part *and*
logarithmic part — *computes* over the monomial tower ℚ(x)(t₁)[t₂] at level 2, and the returned
`g + ∑ cᵢ·log(vᵢ)` genuinely differentiates back to `f`. -/
theorem towerIntLvl2_fullIntegral :
    CPolyG.checkIdentityG towerIntLvl2Dt
      (CPolyG.cIntegrateReducedG towerIntLvl2Dt 30 towerIntLvl2Num towerIntLvl2Den
        towerIntLvl2Cands)
      towerIntLvl2Num towerIntLvl2Den = true := by native_decide

/-- **The full `cIntegrateG` driver runs end-to-end at level 2 and `D(∫f) = f`** (`native_decide`): on
the same level-2 simple integrand (a pure normal element, so `fₚ = fₛ = 0`), the assembled top-level
`cIntegrateG` — canonical split + reduced capstone — returns `some res`, and `res` satisfies the
antiderivative identity `D(res) = f` over ℚ(x)(t₁)[t₂]. This pins the assembled tower driver at level 2,
not just the reduced core. -/
theorem towerIntLvl2_driver :
    (match CPolyG.cIntegrateG towerIntLvl2Dt 30 towerIntLvl2Num towerIntLvl2Den
        towerIntLvl2Cands with
      | some res => CPolyG.checkIdentityG towerIntLvl2Dt res towerIntLvl2Num towerIntLvl2Den
      | none => false) = true := by native_decide

#print axioms towerIntLvl2_fullIntegral

end DeepWiki.SymbolicIntegration
