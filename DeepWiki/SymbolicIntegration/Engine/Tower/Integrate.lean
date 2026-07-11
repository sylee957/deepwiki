import DeepWiki.SymbolicIntegration.Engine.Tower.Lvl2
import DeepWiki.SymbolicIntegration.Engine.Tower.Deriv
import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFFCore
import DeepWiki.SymbolicIntegration.Engine.FuelFreeDiophantine

/-! # The generic integration pipeline over arbitrary-depth differential towers
The integration pipeline (special/normal split, canonical representation, transcendental Hermite
reduction, Rothstein–Trager logarithmic part) over the generic tower carrier `DenseFrac α`. Pipeline defs
carry the suffix `G`, run on the generic engine ops, and take every `t`-gcd from the flat fraction-free
`CFracGcdCore.cgcdFFCore` to avoid fraction-field coefficient swell. This file keeps the fueled engine and
the shared level-2 example data; the fuel-free `ccompute` validations live downstream. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u v

/-! ### The KEY VALIDATION: tower integration, RATIONAL PART, at LEVEL 2 (`ccompute`)

This is the headline. We run `cHermiteReduceTower` over `DensePoly (DenseFrac (DenseFrac ℚ)) =
ℚ(x)(t₁)[t₂]` (tower level 2, the new monomial `t₂`) on a concrete proper fraction whose
denominator has a repeated `t₂`-factor, and certify `D(g) + h = f`. The setting is Bronstein's
Example 5.3.1 lifted one level up: `t₂ = tan` (the monomial derivative is `Dt₂ = t₂² + 1`), and
`f = a/d = 1/t₂²`, whose denominator `d = t₂²` has the normal factor `t₂` of multiplicity 2
(`t₂` is normal: `gcd(t₂, Dt₂) = gcd(t₂, t₂²+1) = 1`). The reduction lowers the multiplicity:
`g = −1/t₂`, `h = −1` (squarefree denominator `t₂`), with `D(−1/t₂) = (t₂²+1)/t₂²` so
`D(g) + h = (t₂²+1)/t₂² − 1 = 1/t₂² = f`.

All coefficients are level-2 *constants* (elements of ℚ ⊂ ℚ(x)(t₁) = `Lvl2`), so the engine genuinely
runs the level-2 `CField`/`CDiffField` instances over `DensePoly Lvl2`. The `CField (DenseFrac (DenseFrac ℚ))`
and `CDiffField (DenseFrac (DenseFrac ℚ))` instances are `[CField …]`-computable with `Prop`-erased subtype
proofs, so nothing noncomputable reaches the compiled decision procedure — `ccompute` reduces. The load-bearing
check is the cleared-denominator form of `D(gnum/gden) + h_num/h_den = a/d`, equating numerators over the
common denominator `gden²·h_den·d`: `(gprimeNum·h_den + h_num·gden²)·d = a·(gden²·h_den)`. -/

open CFrac

/-- Level-2 scalar `2 = 1 + 1 ∈ Lvl2 = ℚ(x)(t₁)`. -/
def lvl2Two : Lvl2 := CCommRing.add CCommRing.one CCommRing.one

/-- Level-2 monomial derivative `Dt₂ = t₂² + 1` over `DensePoly Lvl2 = ℚ(x)(t₁)[t₂]` (so `t₂ = tan`,
Bronstein Example 5.3.1 lifted to level 2; constant coefficients in ℚ ⊂ ℚ(x)(t₁)). -/
def towerHermiteLvl2Dt : DensePoly Lvl2 := [CCommRing.one, CCommRing.zero, CCommRing.one]

/-- Level-2 numerator `a = 1` over `DensePoly Lvl2` (constant coefficient `1 ∈ ℚ(x)(t₁)`). -/
def towerHermiteLvl2A : DensePoly Lvl2 := [CCommRing.one]

/-- Level-2 denominator `d = t₂²` over `DensePoly Lvl2` — the normal factor `t₂` of multiplicity 2 (under
`Dt₂ = t₂² + 1`, `t₂` is normal and `t₂²` its square), so Hermite lowers the power. -/
def towerHermiteLvl2D : DensePoly Lvl2 := [CCommRing.zero, CCommRing.zero, CCommRing.one]

/-! ### Level-2 canonical-representation test data

The canonical-representation companion to the Hermite check, at the same tower level. `f = a/d` with
`a = t₂³` and the monic `d = (t₂−1)(t₂−2) = t₂² − 3t₂ + 2` over `ℚ(x)(t₁)[t₂]`, monomial `t₂` with
`Dt₂ = t₂ − 1` (so the root `t₂ = 1` is special, `t₂ = 2` normal). `canonicalRepresentationFast`
returns `(q, (b, dₛ), (c, dₙ))`; the load-bearing identity `q + b/dₛ + c/dₙ = a/d` is checked by
clearing denominators: numerator `N = q·dₛ·dₙ + b·dₙ + c·dₛ`, identity `N · d = a · (dₛ·dₙ)`, by
`cisZero` of the difference over ℚ(x)(t₁)[t₂]. Scalar-robust (independent of the split's internal
scalar ambiguity). -/

/-- Level-2 scalar `−1 ∈ Lvl2 = ℚ(x)(t₁)`. -/
def lvl2NegOne : Lvl2 := CCommRing.neg CCommRing.one

/-- Level-2 scalar `−2 ∈ Lvl2`. -/
def lvl2NegTwo : Lvl2 := CCommRing.neg (CCommRing.add CCommRing.one CCommRing.one)

/-- Level-2 scalar `−3 ∈ Lvl2`. -/
def lvl2NegThree : Lvl2 := CCommRing.neg (CCommRing.add CCommRing.one (CCommRing.add CCommRing.one CCommRing.one))

/-- Level-2 canonical-rep numerator `a = t₂³` over `ℚ(x)(t₁)[t₂]` (constant coefficients in ℚ). -/
def towerCanRepLvl2A : DensePoly Lvl2 := [CCommRing.zero, CCommRing.zero, CCommRing.zero, CCommRing.one]

/-- Level-2 canonical-rep denominator `d = (t₂−1)(t₂−2) = t₂² − 3t₂ + 2` over `ℚ(x)(t₁)[t₂]` (monic). -/
def towerCanRepLvl2D : DensePoly Lvl2 := [lvl2Two, lvl2NegThree, CCommRing.one]

/-- Level-2 monomial derivative `Dt₂ = t₂ − 1` (root `t₂ = 1` special, `t₂ = 2` normal). -/
def towerCanRepLvl2Dt : DensePoly Lvl2 := [lvl2NegOne, CCommRing.one]

/-! ## The logarithmic part (Rothstein-Trager §5.6) and the reduced-case capstone `cIntegrateReduced`

The rational part (Hermite) is done. The remaining piece of the elementary integral `∫ f = g + ∑ᵢ
cᵢ·log(vᵢ)` is the logarithmic part: the Rothstein–Trager residue criterion (§5.6). For a simple
`h = a/d` (`d` squarefree), `∫ h = ∑_{R(c)=0} c·log(gcd_t(d, a − c·Dd))` with `R(z) = res_t(d, a − z·Dd)`
the residue resultant.

The generic engine pieces `ceval`/`cresultantG`/`cinterpolate` are *already* `[CField α]`-generic. The
remaining carrier-specific concern beyond the `t`-gcd is the embedding `ℚ → α`: the residue
resultant samples `z` at the natural nodes `0, 1, …, n`, and a residue is a field constant. We lift the
nodes through the existing `CField.natCast : ℕ → α` (`[CField α]`-only), and take the residue candidates as
`α` elements (the natural generic form) — so the whole log part generalizes. `cratCast` additionally
gives the `ℚ → α` embedding for convenience. -/

namespace DensePoly

variable {α : Type*} [CField α]

/-- Rational into a `CField` `cratCast q = (sign · CField.natCast |num|) / CField.natCast den`: embed `q ∈ ℚ`
into any `[CField α]` via the numerator/denominator natural casts (`CField.natCast`) and a sign, all from
`CField` ops. The generic `ℚ → α` constant embedding (the generic `ofConstNZ` at the scalar level). -/
def cratCast (q : ℚ) : α :=
  let n : α := CField.natCast q.num.natAbs
  let nsigned : α := if q.num < 0 then CCommRing.neg n else n
  CCommRing.mul nsigned (CField.inv (CField.natCast q.den))

end DensePoly

namespace CPoly

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P]
  {α : Type u} [CField α] [CDiffField α]

/-! ### The generic Rothstein–Trager numerator `a − c·Dd`

`CPoly.amcDd` is the polynomial in `t` whose `t`-gcd with `d` is the Rothstein–Trager log argument at a
residue `c` — the shared building block of the fuel-free residue resultant / log-argument engine
(`cResidueResultantTower` / `cLogArgTower`, `Tower/WellFounded`). -/

/-- Generic `a − c·Dd` for a residue value `c`, whose `t`-gcd with `d` is the log argument. -/
def amcDd (Dt a d : P α) (c : α) : P α :=
  CPolyEngine.sub a (CPolyEngine.scale c (CPolyEngine.monomialDeriv Dt d))

end CPoly

namespace DensePoly

variable {α : Type u} [CField α] [CDiffField α]

/-- Dense specialization of the representation-independent Rothstein–Trager numerator. -/
def cAmcDd (Dt a d : DensePoly α) (c : α) : DensePoly α := CPoly.amcDd Dt a d c

/-- Dense `cAmcDd` specializes to the concrete dense engine operations. -/
theorem cAmcDd_dense_eq (Dt a d : DensePoly α) (c : α) :
    cAmcDd Dt a d c = csub a (cscale c (CPolyEngine.monomialDeriv Dt d)) := rfl

end DensePoly

namespace CPolyEngine

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
  {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]

/-- Generic `cAmcDd` denotes the Rothstein–Trager numerator `a - c·Dd`. -/
@[denote] theorem toPoly_cAmcDd (Dt a d : P α) (c : α) :
    CPoly.toPoly (CPoly.amcDd Dt a d c) =
      CPoly.toPoly a - Polynomial.C (CFieldSpec.toK c) *
        Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly d) := by
  rw [CPoly.amcDd, toPoly_sub, LawfulCPolyEngine.toPoly_scale,
    toPoly_monomialDeriv]
  simp only [toR_eq_toK]

end CPolyEngine

namespace DensePoly

example :
    CPolyEngine.cisZero
      (CPoly.amcDd
        (CPoly.SparsePoly.ofList [(0, (1 : ℚ))])
        (CPoly.SparsePoly.ofList [(1, 2)])
        (CPoly.SparsePoly.ofList [(2, 1)]) 1) = true := by
  ccompute

end DensePoly

/-! ### The representation-independent integral result and cleared antiderivative identity

`IntegralResult α P` stores the rational part `g = num/den ∈ α(t)` and the logarithmic part
`[(cᵢ, vᵢ)]` in any polynomial representation `P`; its default `P := DensePoly` preserves the existing
`IntegralResult α` API.
`checkIdentity` verifies the antiderivative identity `D(g) + ∑ᵢ cᵢ·(D(vᵢ)/vᵢ) = f`, cleared of
denominators. -/

/-- A representation-independent integral result `∫ f = rational + ∑ᵢ coeff·log(arg)`, defaulting to
the dense polynomial representation for compatibility. -/
structure IntegralResult (α : Type u) [CField α] (P : Type u → Type u := DensePoly) where
  /-- The rational part `g = num/den ∈ α(t)` of `∫ f`. -/
  rational : P α × P α
  /-- The logarithmic part `∑ᵢ coeff·log(arg)` of `∫ f`. -/
  logs : List (α × P α)

namespace DensePoly

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P]
  {α : Type u} [CField α] [CDiffField α]

/-- The generic antiderivative identity, cleared of denominators `checkIdentity Dt res anum aden`:
`true` iff `res` is a genuine antiderivative of `f = anum/aden`, i.e. `D(g) + ∑ᵢ cᵢ·(D(vᵢ)/vᵢ) = f` for
`D = CPolyEngine.monomialDeriv Dt`. Accumulate `∑ᵢ cᵢ·D(vᵢ)/vᵢ` as a single fraction `(Lnum, Lden)` over `∏ᵢ vᵢ`,
add `D(g) = (D(gnum)·gden − gnum·D(gden))/gden²`, and equate with `f` over `gden²·Lden·aden`:
`(gprimeNum·Lden + Lnum·gden²)·aden = anum·(gden²·Lden)`, by `cisZero` of the cleared difference. The
generic mirror of `IntegralResult.checkIdentity` (`α` has no `DecidableEq`, hence the `cisZero∘csub`
form). -/
def checkIdentity (Dt : P α) (res : IntegralResult α P) (anum aden : P α) : Bool :=
  let gnum := res.rational.1
  let gden := res.rational.2
  let gprimeNum := CPolyEngine.sub
    (CPolyEngine.mul (CPolyEngine.monomialDeriv Dt gnum) gden)
    (CPolyEngine.mul gnum (CPolyEngine.monomialDeriv Dt gden))
  let gden2 := CPolyEngine.mul gden gden
  let Lstart : P α × P α :=
    (CPolyEngine.ofCoeffList [CCommRing.zero], CPolyEngine.ofCoeffList [CCommRing.one])
  let (Lnum, Lden) := res.logs.foldl
    (fun (acc : P α × P α) (cv : α × P α) =>
      let c := cv.1
      let v := cv.2
      let Dv := CPolyEngine.monomialDeriv Dt v
      let termNum := CPolyEngine.scale c Dv
      (CPolyEngine.add (CPolyEngine.mul acc.1 v) (CPolyEngine.mul termNum acc.2),
        CPolyEngine.mul acc.2 v))
    Lstart
  let lhs := CPolyEngine.mul
    (CPolyEngine.add (CPolyEngine.mul gprimeNum Lden) (CPolyEngine.mul Lnum gden2)) aden
  let rhs := CPolyEngine.mul anum (CPolyEngine.mul gden2 Lden)
  CPolyEngine.cisZero (CPolyEngine.sub lhs rhs)

/-- The cleared antiderivative checker executes on sparse polynomial results. -/
example :
    let ofList : List ℚ → CPoly.SparsePoly ℚ := CPolyEngine.ofCoeffList
    let res : IntegralResult ℚ CPoly.SparsePoly :=
      ⟨(ofList [0, 0, 1 / 2], ofList [1]), []⟩
    checkIdentity (ofList [1]) res (ofList [0, 1]) (ofList [1]) = true := by
  ccompute

end DensePoly

/-! ### Level-2 reduced integration test data

Bronstein's Example 5.6.2 construction lifted to tower level 2. Over `DensePoly Lvl2 =
ℚ(x)(t₁)[t₂]` the monomial `t₂` is independent (`Dt₂ = 1`), and the simple integrand
`f = (1/2)·D(t₂+1)/(t₂+1) − (1/2)·D(t₂−1)/(t₂−1)` over ℚ(x)(t₁)(t₂) has the known elementary
antiderivative `(1/2)log(t₂+1) − (1/2)log(t₂−1)`. Since `D(t₂±1) = Dt₂ = 1`, the integrand is
`f = (1/2)/(t₂+1) − (1/2)/(t₂−1)`, assembled as a single fraction `a/d` with `d = (t₂+1)(t₂−1) =
t₂² − 1`. The residues of `R(z) = res_t(d, a − z·Dd)` are `±1/2` with log arguments `t₂ ± 1`.

The generic reduced-case capstone `cIntegrateReduced` (Hermite rational part + Rothstein–Trager
residue logs) runs over `DensePoly Lvl2` and recovers the integral: `g = 0`, residues `±1/2` from the
candidate set, logs `t₂ ± 1`. The headline check is the antiderivative identity `D(∫f) = f`
(`checkIdentity`, cleared of denominators, by `cisZero`) — the whole elementary tower integral
executing and differentiating back to `f`, at level 2. All coefficients are ℚ-constants lifted into
`Lvl2` (via `cratCast`), so the engine genuinely runs the level-2 `CField`/`CDiffField` instances. The
fuel-free validations are in `ComputableTowerWellFounded`. -/

open DensePoly

/-- Level-2 monomial derivative `Dt₂ = 1` over `DensePoly Lvl2 = ℚ(x)(t₁)[t₂]` (`t₂` independent). -/
def towerIntLvl2Dt : DensePoly Lvl2 := [CCommRing.one]

/-- Level-2 log argument `v₊ = t₂ + 1` over `DensePoly Lvl2` (low→high in `t₂`). -/
def towerIntLvl2VPlus : DensePoly Lvl2 := [CCommRing.one, CCommRing.one]

/-- Level-2 log argument `v₋ = t₂ − 1` over `DensePoly Lvl2`. -/
def towerIntLvl2VMinus : DensePoly Lvl2 := [CCommRing.neg CCommRing.one, CCommRing.one]

/-- Level-2 scalar `1/2 ∈ Lvl2` (the residue coefficient), via the generic `cratCast`. -/
def towerIntLvl2Half : Lvl2 := cratCast (1/2)

/-- The level-2 integrand numerator `a = (1/2)·D(v₊)·v₋ − (1/2)·D(v₋)·v₊` over `DensePoly Lvl2`, so
`a/d = (1/2)·D(v₊)/v₊ − (1/2)·D(v₋)/v₋` with `d = v₊·v₋`. Its elementary antiderivative is
`(1/2)log(v₊) − (1/2)log(v₋)`. -/
def towerIntLvl2Num : DensePoly Lvl2 :=
  csub
    (cscale towerIntLvl2Half
      (cmul (CPolyEngine.monomialDeriv towerIntLvl2Dt towerIntLvl2VPlus) towerIntLvl2VMinus))
    (cscale towerIntLvl2Half
      (cmul (CPolyEngine.monomialDeriv towerIntLvl2Dt towerIntLvl2VMinus) towerIntLvl2VPlus))

/-- The level-2 integrand denominator `d = v₊·v₋ = (t₂+1)(t₂−1) = t₂² − 1` over `DensePoly Lvl2`. -/
def towerIntLvl2Den : DensePoly Lvl2 := cmul towerIntLvl2VPlus towerIntLvl2VMinus

/-- The level-2 residue candidate set `{1/2, −1/2, 1, −1, 0}` as `Lvl2` constants (the residues `±1/2`
are inside; the rest are rejected by `R(c) ≠ 0`). -/
def towerIntLvl2Cands : List Lvl2 :=
  [cratCast (1/2), cratCast (-1/2), cratCast 1, cratCast (-1), cratCast 0]

end DeepWiki.SymbolicIntegration
