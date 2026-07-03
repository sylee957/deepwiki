import DeepWiki.SymbolicIntegration.Computable.Tower.Field
import DeepWiki.SymbolicIntegration.Computable.Tower.Deriv
import DeepWiki.SymbolicIntegration.Computable.Tower.GcdFFCore
import DeepWiki.SymbolicIntegration.Computable.FuelFreeDiophantine

/-! # The generic integration pipeline over arbitrary-depth differential towers
`ComputableTowerField`/`ComputableTowerDeriv` built the generic fraction-field carrier `QFunNZG α`
(the next tower level ℚ(x)(t₁)(t₂)…) with a *computable* `CField` instance AND a *computable*
derivation tower (`CDiffField (QFunNZG α)`, `towerDerivQFunNZG`). This file supplies the §3.5/§5.3
integration pipeline (split/normal factor, canonical representation, transcendental Hermite reduction)
over that generic carrier. The pipeline runs on the generic engine ops
(`caddG`/`cmulG`/`cmonomialDeriv`/`cdivWf`/…); the one operation needing care is the fraction-free
`t`-gcd.

The pipeline defs (suffix `G`) over `[CField α] [CFieldDomain α] [CDiffField α]` take every `t`-gcd from
the flat generic fraction-free gcd `CFracGcdCore.cgcdFFCore fuel p q` (`ComputableTowerGcdFFCore`) —
the recursive primitive-PRS gcd that stays polynomial-sized over the tower (it AGREES with the swelling
fuel-free Euclidean `cgcdMonicWf`, both being the unique monic gcd, but computes it without the fraction-field
coefficient swell that would make the integration pipeline over a fraction-field carrier blow up). Every
pipeline def that calls a `t`-gcd therefore carries the
`[CFracGcdCore α]` constraint, resolved automatically at every concrete tower level (base `CFracGcdCore ℚ`
+ recursive `CFracGcdCore (QFunNZG β)`).

* `CFracGcdCore.cgcdFFCore` — the flat fraction-free monic gcd used by the pipeline.
* `cSplitFactorFastG` (§3.5 special/normal split `p = pₙ·pₛ` via the derivation `D` + gcd).
* `cSqfreeYunFFG` (Yun squarefree factorization in `t`, the formal `dp/dt`) — what the Hermite
  reduction factors the denominator with.
* `canonicalRepresentationFastG` (the `a/d → (fₚ, (b, dₛ), (c, dₙ))` canonical representation),
  reusing the already-generic fuel-free Bézout helpers `cbezoutOneWf`/`cextendedEuclideanSplitWf`.
* `cHermiteReduceTowerG` (the transcendental Hermite reduction of the simple normal part →
  rational `g` + reduced remainder — the RATIONAL PART of the integral), reusing the already-generic
  fuel-free inner loop `cHermiteReduceTowerInnerWf`/`cdiophantineGWf`.

This file keeps the fueled generic engine and the shared level-2 example data. The corresponding
fuel-free `native_decide` validations live in `ComputableTowerWellFounded`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

/-! ### Generic `splitFactor` over the tower (§3.5)

`cSplitFactorFastG` is the `[CField α] [CDiffField α]`-generic mirror of `cSplitFactorFast`: Bronstein's
splitting-factorization loop with the flat fraction-free monic gcd `CFracGcdCore.cgcdFFCore` (for the two
gcds `gcd(p, Dp)` and `gcd(p, dp/dt)`) and the fuel-free generic exact division `cdivWf`. `Dp = cmonomialDeriv Dt p` is the differential
derivation (needs `[CDiffField α]`); `dp/dt = cderivG p` the formal `t`-derivative. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α]

/-- Generic splitting-factorization loop (Bronstein §3.5): `cSplitFactorFastG Dt fuel p =
(pₙ, pₛ)`, the same recursion as `cSplitFactorFast` but on a generic `[CField α] [CDiffField α]`
carrier with the flat fraction-free gcd `CFracGcdCore.cgcdFFCore` for the two gcds `gcd(p, Dp)` and
`gcd(p, dp/dt)`. One step extracts `S = gcd(p, Dp)/gcd(p, dp/dt)` (`Dp = cmonomialDeriv Dt p` the
differential derivation, `dp/dt = cderivG p` the formal one); constant `S` ⇒ `p` is normal, else recurse
on `p/S` and accumulate `S` into the special part. Fuel-bounded; runs at any tower level. -/
def cSplitFactorFastG (Dt : CPolyG α) : ℕ → CPolyG α → CPolyG α × CPolyG α
  | 0, p => (p, [CField.one])
  | fuel + 1, p =>
    let S := cdivWf (CFracGcdCore.cgcdFFCore (fuel + 1) p (cmonomialDeriv Dt p))
      (CFracGcdCore.cgcdFFCore (fuel + 1) p (cderivG p))
    if cdegG S = 0 then (p, [CField.one])
    else
      let (qn, qs) := cSplitFactorFastG Dt fuel (cdivWf p S)
      (qn, cmulG S qs)

end CPolyG

/-! ### Generic Yun squarefree factorization in `t` (the formal derivative)

`cSqfreeYunFFG` is the `[CField α]`-generic mirror of `cSqfreeYunFF`: Yun's squarefree factorization in
`t` using the *formal* derivative `dp/dt = cderivG` (NOT the differential `D`), with the flat
fraction-free monic gcd `CFracGcdCore.cgcdFFCore` everywhere. Returns the position-indexed list
`[p₁, …, pₘ]` (`pᵢ` the monic squarefree part of multiplicity `i`), so `p` is associate to
`∏ᵢ pᵢ^i`. This is what `cHermiteReduceTowerG` factors the denominator with. -/

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
      let b' := cdivWf b p
      let d' := csubG (cdivWf d p) (cderivG b')
      p :: cSqfreeYunFFGgo fuel fo b' d'

/-- Generic Yun squarefree factorization in `t` `cSqfreeYunFFG fuel p = [p₁, …, pₘ]`: the
purely-algebraic squarefree factorization in `t` (the formal derivative `dp/dt = cderivG`), with the flat
fraction-free gcd `CFracGcdCore.cgcdFFCore` for `cgcdFF`. With `g = CFracGcdCore.cgcdFFCore p (cderivG p)`,
`b₁ = p/g`, `d₁ = p'/g − b₁'`, the recurrence `pᵢ = CFracGcdCore.cgcdFFCore bᵢ dᵢ` peels the monic
squarefree part of multiplicity `i`. `p` is associate to `∏ᵢ pᵢ^i`.
`[CField α] [CFracGcdCore α]`-generic — runs at any tower level. -/
def cSqfreeYunFFG (fuel : ℕ) (p : CPolyG α) : List (CPolyG α) :=
  let g := CFracGcdCore.cgcdFFCore fuel p (cderivG p)
  let b1 := cdivWf p g
  let d1 := csubG (cdivWf (cderivG p) g) (cderivG b1)
  cSqfreeYunFFGgo fuel fuel b1 d1

end CPolyG

/-! ### Generic canonical representation over the tower (§3.5)

`canonicalRepresentationFastG` is the `[CField α] [CDiffField α]`-generic mirror of
`canonicalRepresentationFast`: it splits `f = a/d` (d monic) into `(fₚ, fₛ, fₙ) = (q, (b, dₛ), (c, dₙ))`.
The denominator split `d = dₛ·dₙ` uses the generic `cSplitFactorFastG`; the Bézout-split of the
remainder reuses the already-generic `cbezoutOne`/`cextendedEuclideanSplit` from
`ComputableCanonicalRep` (those need only `[CField α]`). -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α]

/-- Generic `CanonicalRepresentation` (Bronstein §3.5, p.103) over the tower:
`canonicalRepresentationFastG Dt fuel (a, d) = (fₚ, fₛ, fₙ) = (q, (b, dₛ), (c, dₙ))` for `f = a/d`
(`d` monic). Steps: divide `a = q·d + r` (`cdivmodWf`); split the denominator `d = dₛ·dₙ`
(`cSplitFactorFastG`, generic); Bézout-split `r` over the coprime `(dₙ, dₛ)` (`cextendedEuclideanSplitWf`
with `cbezoutOneWf`, the already-generic fuel-free helpers). The reduced part is `b/dₛ`, the simple part `c/dₙ`.
`[CField α] [CDiffField α] [CFracGcdCore α]`-generic — runs at any tower level. -/
def canonicalRepresentationFastG (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) :
    CPolyG α × (CPolyG α × CPolyG α) × (CPolyG α × CPolyG α) :=
  let (q, r) := cdivmodWf a d
  let (dn, ds) := cSplitFactorFastG Dt fuel d
  let (u, w) := cbezoutOneWf dn ds
  let (b, c) := cextendedEuclideanSplitWf dn ds r u w
  (q, (b, ds), (c, dn))

end CPolyG

/-! ### The KEY VALIDATION: tower integration, RATIONAL PART, at LEVEL 2 (`native_decide`)

This is the headline. We run `cHermiteReduceTowerG` over `CPolyG (QFunNZG (QFunNZG ℚ)) =
ℚ(x)(t₁)[t₂]` (tower level 2, the new monomial `t₂`) on a concrete proper fraction whose
denominator has a repeated `t₂`-factor, and certify `D(g) + h = f`. The setting is Bronstein's
Example 5.3.1 lifted one level up: `t₂ = tan` (the monomial derivative is `Dt₂ = t₂² + 1`), and
`f = a/d = 1/t₂²`, whose denominator `d = t₂²` has the normal factor `t₂` of multiplicity 2
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

/-! ### Level-2 canonical-representation test data

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

/-! ## The logarithmic part (Rothstein-Trager §5.6) and the reduced-case capstone `cIntegrateReducedG`

The rational part (Hermite) is done. The remaining piece of the elementary integral `∫ f = g + ∑ᵢ
cᵢ·log(vᵢ)` is the logarithmic part: the Rothstein–Trager residue criterion (§5.6). For a simple
`h = a/d` (`d` squarefree), `∫ h = ∑_{R(c)=0} c·log(gcd_t(d, a − c·Dd))` with `R(z) = res_t(d, a − z·Dd)`
the residue resultant.

The generic engine pieces `cevalG`/`cresultantG`/`cinterpolateG` are *already* `[CField α]`-generic. The
remaining carrier-specific concern beyond the `t`-gcd is the embedding `ℚ → α`: the residue
resultant samples `z` at the natural nodes `0, 1, …, n`, and a residue is a field constant. We lift the
nodes through the existing `cnatCastG : ℕ → α` (`[CField α]`-only), and take the residue candidates as
`α` elements (the natural generic form) — so the whole log part generalizes. `cratCastG` additionally
gives the `ℚ → α` embedding for convenience. -/

namespace CPolyG

variable {α : Type*} [CField α]

/-- Rational into a `CField` `cratCastG q = (sign · cnatCastG |num|) / cnatCastG den`: embed `q ∈ ℚ`
into any `[CField α]` via the numerator/denominator natural casts (`cnatCastG`) and a sign, all from
`CField` ops. The generic `ℚ → α` constant embedding (the generic `ofConstNZ` at the scalar level). -/
def cratCastG (q : ℚ) : α :=
  let n : α := cnatCastG q.num.natAbs
  let nsigned : α := if q.num < 0 then CField.neg n else n
  CField.mul nsigned (CField.inv (cnatCastG q.den))

/-- Generic Horner evaluation `cHornerG p c = p(c) ∈ α`: evaluate the dense coefficient list `p`
(index = degree, low→high) at `c ∈ α` by Horner's rule. The generic mirror of `cevalG`
(`ComputableIntegrate`), redefined here to avoid that heavy import. Used to test whether a candidate
residue `c` is a root of the residue resultant `R(c) = 0`. Needs only `[CField α]`. -/
def cHornerG (p : CPolyG α) (c : α) : α :=
  (p : List α).foldr (fun coeff acc => CField.add coeff (CField.mul c acc)) CField.zero

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α]

/-! ### The generic Rothstein–Trager numerator `a − c·Dd`

`cAmcDdG` is the polynomial in `t` whose `t`-gcd with `d` is the Rothstein–Trager log argument at a
residue `c` — the shared building block of the fuel-free residue resultant / log-argument engine
(`cResidueResultantTowerGWf` / `cLogArgTowerGWf`, `Tower/WellFounded`). -/

/-- Generic `a − c·Dd` `cAmcDdG Dt a d c` for a residue value `c : α`: `a − c·(cmonomialDeriv Dt d)`,
the polynomial in `t` whose `t`-gcd with `d` is the log argument at `c`. Generic mirror of `cAmcDd`. -/
def cAmcDdG (Dt a d : CPolyG α) (c : α) : CPolyG α :=
  csubG a (cscaleG c (cmonomialDeriv Dt d))

end CPolyG

/-! ### The generic integral result and the cleared antiderivative identity

`IntegralResultG α` is the generic mirror of `IntegralResult`: the rational part `g = num/den ∈ α(t)`
plus the logarithmic part `[(cᵢ, vᵢ)]` (coefficients `cᵢ : α`, arguments `vᵢ : CPolyG α`).
`checkIdentityG` verifies the antiderivative identity `D(g) + ∑ᵢ cᵢ·(D(vᵢ)/vᵢ) = f`, cleared of
denominators — the generic mirror of `IntegralResult.checkIdentity`. -/

/-- The generic integral result: `∫ f = rational + ∑ᵢ coeff·log(arg)` over the tower, with
`rational = (num, den)` the rational part `g = num/den ∈ α(t)` and `logs = [(cᵢ, vᵢ)]` the logarithmic
part (each `cᵢ : α`, each `vᵢ : CPolyG α`). The generic mirror of `IntegralResult`. -/
structure IntegralResultG (α : Type*) [CField α] where
  /-- The rational part `g = num/den ∈ α(t)` of `∫ f`. -/
  rational : CPolyG α × CPolyG α
  /-- The logarithmic part `∑ᵢ coeff·log(arg)` of `∫ f` (`α`-coefficients, `CPolyG α` arguments). -/
  logs : List (α × CPolyG α)

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α]

/-- The generic antiderivative identity, cleared of denominators `checkIdentityG Dt res anum aden`:
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

end CPolyG

/-! ### Level-2 reduced integration test data

Bronstein's Example 5.6.2 construction lifted to tower level 2. Over `CPolyG Lvl2 =
ℚ(x)(t₁)[t₂]` the monomial `t₂` is independent (`Dt₂ = 1`), and the simple integrand
`f = (1/2)·D(t₂+1)/(t₂+1) − (1/2)·D(t₂−1)/(t₂−1)` over ℚ(x)(t₁)(t₂) has the known elementary
antiderivative `(1/2)log(t₂+1) − (1/2)log(t₂−1)`. Since `D(t₂±1) = Dt₂ = 1`, the integrand is
`f = (1/2)/(t₂+1) − (1/2)/(t₂−1)`, assembled as a single fraction `a/d` with `d = (t₂+1)(t₂−1) =
t₂² − 1`. The residues of `R(z) = res_t(d, a − z·Dd)` are `±1/2` with log arguments `t₂ ± 1`.

The generic reduced-case capstone `cIntegrateReducedG` (Hermite rational part + Rothstein–Trager
residue logs) runs over `CPolyG Lvl2` and recovers the integral: `g = 0`, residues `±1/2` from the
candidate set, logs `t₂ ± 1`. The headline check is the antiderivative identity `D(∫f) = f`
(`checkIdentityG`, cleared of denominators, by `cisZeroG`) — the whole elementary tower integral
executing and differentiating back to `f`, at level 2. All coefficients are ℚ-constants lifted into
`Lvl2` (via `cratCastG`), so the engine genuinely runs the level-2 `CField`/`CDiffField` instances. The
fuel-free validations are in `ComputableTowerWellFounded`. -/

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

end DeepWiki.SymbolicIntegration
