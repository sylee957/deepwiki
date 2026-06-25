import DeepWiki.SymbolicIntegration.ComputableTowerField
import DeepWiki.SymbolicIntegration.ComputableTowerDeriv
import DeepWiki.SymbolicIntegration.ComputableTowerIntegrate
import DeepWiki.SymbolicIntegration.ComputableRischDE

/-! # The recursive Risch-DE oracle over arbitrary-depth differential towers (Bronstein Ch. 6)
`ComputableTowerField`/`Deriv`/`Integrate` built the generic tower carrier `QFunNZG α` (the next level
ℚ(x)(t₁)(t₂)…), its computable derivation, and the generic §3.5/§5 integration pipeline — but the
integration **driver** `cIntegrateG` is the reduced-case driver, because the §6 Risch-DE oracle
`cRischDE` (`ComputableRischDE`) is still `QFunNZ`-hardwired: it bottoms out at the concrete base solve
`cRationalRDE` over ℚ(x). This file makes the §6 oracle **generic and recursive over the tower**.

The clean encoding is a **typeclass-carried base solve**:

* **`class CRischField α`** — one method `crischDESolve : α → α → Option α` (solve `Dy + f·y = g` over
  the FIELD `α` itself). This is the "RDE over the coefficient field" that every §6 cancellation case
  recurses into (eq. 6.23 `RischDE(b, lc(c))`).
* **`instance : CRischField ℚ`** — the constant-field base (`D = 0`): `b·y = g`, so `y = g/b` (`b ≠ 0`),
  `b = 0` needs `g = 0`.
* **`cRischDEG`** — the generic §6 pipeline over `CPolyG α = α[t]`, the mechanical generalization of
  `cRischDE` (`QFunNZ → α`, `cgcdFF → cgcdMonicG`, base solve → `CRischField.crischDESolve`): weak
  normalization + normal/special denominator + degree bound + SPDE + the §6.5/§6.6 PolyRischDE dispatch.
  It reduces an RDE over `α[t]` to RDEs over `α` via `crischDESolve`.
* **`instance : CRischField (QFunNZG β)`** — the RDE over `β(s) = QFunNZG β`, **built by running
  `cRischDEG` over `CPolyG β = β[s]`** with the new monomial `s` (`Ds = [1]`) and `[CRischField β]` for
  the base solve. This ties the recursion: the level-`n+1` oracle runs the §6 pipeline at level `n`,
  recursing to the level-`n` oracle, bottoming at `CRischField ℚ`. So `CRischField (QFunNZG ℚ)` is the
  RDE over ℚ(x), `CRischField (QFunNZG (QFunNZG ℚ))` the RDE over ℚ(x)(t₁), … — uniformly, with no
  special-cased `cRationalRDE`.

**★ The headline `native_decide`** solves an RDE `Dy + f·y = g` over the **level-2** field `ℚ(x)(t₁)`
(`= QFunNZG (QFunNZG ℚ)`) by the recursive oracle — `crischDESolve f g = some y` with `D(y) + f·y = g`
certified by `native_decide`, the oracle recursing ℚ(x)(t₁) → ℚ(x) → ℚ. Everything stays
`[CField α]`/`[CDiffField α]`/`[CFieldDomain α]`/`[CRischField α]`-only with `Prop`-erased subtype
proofs, so nothing noncomputable reaches the native compiler.

**Scope.** The generic pipeline mirrors the **non-cancellation** path and the **primitive/hyperexponential
cancellation** cases of `cRischDE` exactly (the base solve is now the generic `crischDESolve` rather than
the `QFunNZ`-bound `cRischDEBase`). The §6.6 hypertangent cancellation (`PolyRischDECancelTan`, needs the
Ch. 8 coupled system) and the cancellation refinements inside the special-denominator/degree-bound steps
(needing the full §5.12/§7.3 parametric-log-derivative recognizer) are the documented continuation, exactly
as in `cRischDE`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### The `CRischField` class — the base Risch-DE solve over the field itself

`crischDESolve f g` solves `Dy + f·y = g` for `y ∈ α`, where `D` is `α`'s own derivation
(`CDiffField.cderiv`). This is the leading-coefficient recursion target of every §6.6 cancellation case
(eq. 6.23). The recursion is carried by the *instances*: `CRischField ℚ` is the constant base, and
`CRischField (QFunNZG β)` runs the generic §6 pipeline over `β[s]` with `[CRischField β]`. -/

/-- **Base Risch-DE solver over the field `α`**: `crischDESolve f g = some y` with `y ∈ α` solving
`Dy + f·y = g` (`D = α`'s own derivation), or `none`. The leading-coefficient recursion target of the
§6.6 cancellation cases (Bronstein eq. 6.23). Carried as a typeclass so the tower recursion is
structural: `CRischField (QFunNZG β)` runs the §6 pipeline over `β[s]` and recurses to
`CRischField β`, bottoming at `CRischField ℚ`. -/
class CRischField (α : Type*) [CField α] where
  /-- Solve `Dy + f·y = g` over the field `α` (`D = α`'s own derivation); `none` if unsolvable. -/
  crischDESolve : α → α → Option α

/-- **`CRischField ℚ`** — the constant-field base (`D = 0`): `Dy + f·y = g` collapses to `f·y = g`
(`Dy = 0` for constant `y`), so `y = g/f` when `f ≠ 0`; `f = 0` needs `g = 0` (then `y = 0`). The
bottoming-out solve of the whole tower recursion. -/
instance instCRischFieldQ : CRischField ℚ where
  crischDESolve f g := if f = 0 then (if g = 0 then some 0 else none) else some (g / f)

/-! ### Generic polynomial evaluation at a `CField` constant (positive-integer-root test)

`cevalConstG p c = p(c) ∈ α` for `c : α` lifted from `ℕ` by `cnatCastG`. The §6.1 `WeakNormalizer` step
needs the positive integer roots of the residue resultant `r ∈ α[z]`; over the generic tower the nodes
`n` are lifted by `cnatCastG n : α` (the `[CField α]`-only natural cast), replacing `ofConstNZ (n : ℚ)`. -/

namespace CPolyG

variable {α : Type*} [CField α]

/-- **Evaluate `r ∈ α[z]` at `cnatCastG n`** `cisRootNatG r n`: `true` iff `r(cnatCastG n) = 0` in `α`
(Horner via `cHornerG`). Decides whether the natural number `n`, lifted to `α`, is a root of the residue
resultant `r` — the generic mirror of `cisRootConst r (n : ℚ)`. -/
def cisRootNatG (r : CPolyG α) (n : ℕ) : Bool :=
  CField.isZero (cHornerG r (cnatCastG n))

/-- **Positive integer roots of `r ∈ α[z]` up to a bound** `cPosIntRootsG r bound = [n ∈ {1,…,bound} :
r(cnatCastG n) = 0]` (the §6.1 step). The residue resultant's positive integer roots are the
multiplicities `nᵢ` of the `WeakNormalizer` product; for an already-weakly-normalized `f` this is empty.
Generic mirror of `cPosIntRoots`. -/
def cPosIntRootsG (r : CPolyG α) (bound : ℕ) : List ℕ :=
  (List.range bound).filterMap (fun k =>
    let n : ℕ := k + 1
    if cisRootNatG r n then some n else none)

end CPolyG

/-! ### The generic §6.1 weak normalizer over the tower

`cWeakNormalizerG` mirrors `cWeakNormalizer` (`QFunNZ → α`, `cgcdFF → cgcdMonicG`, `cdivFF → cdivG`,
`ofConstNZ (n : ℚ) → cnatCastG n`, `cResidueResultantTower → cResidueResultantTowerG`). Everything else
is the already-generic engine. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

/-- **Generic weak normalizer** `cWeakNormalizerG Dt fuel fnum fden = q ∈ α[t]` (Bronstein §6.1, book
p.183) with `f − Dq/q` weakly normalized for `f = fnum/fden`, the `[CField α] [CDiffField α]`-generic
mirror of `cWeakNormalizer`. Split the denominator into its normal part `dₙ` (`cSplitFactorFastG`), form
`d₁ = (dₙ/g)/gcd(dₙ/g, g)` with `g = gcd(dₙ, dₙ')`, solve `ExtendedEuclidean(fden/d₁, d₁, fnum)` for the
residue numerator `a` (`cdiophantineG`), build the residue resultant `r = res_t(a − z·Dd₁, d₁)`
(`cResidueResultantTowerG`), and return `∏ᵢ gcd(a − nᵢ·Dd₁, d₁)^{nᵢ}` over the positive integer roots
`nᵢ` of `r` (`cPosIntRootsG`, nodes lifted by `cnatCastG`). For an already-weakly-normalized `f`, `r` has
no positive integer roots and the result is `q = 1`. -/
def cWeakNormalizerG (Dt : CPolyG α) (fuel : ℕ) (fnum fden : CPolyG α)
    (boundRoots : ℕ := 16) : CPolyG α :=
  let dn := (cSplitFactorFastG Dt fuel fden).1
  let g := cgcdMonicG fuel dn (cderivG dn)
  let dstar := cdivG fuel dn g
  let d1 := cdivG fuel dstar (cgcdMonicG fuel dstar g)
  let fdenOverD1 := cdivG fuel fden d1
  let a := (cdiophantineG fuel fdenOverD1 d1 fnum).1
  let Dd1 := cmonomialDeriv Dt d1
  let r := cResidueResultantTowerG Dt fuel a d1
  let roots := cPosIntRootsG r boundRoots
  roots.foldl (fun (acc : CPolyG α) (n : ℕ) =>
    let gi := cgcdMonicG fuel (csubG a (cscaleG (cnatCastG n) Dd1)) d1
    cmulG acc (cpowG gi n)) [CField.one]

/-! ### The generic §6.2 normal-denominator reduction over the tower

`cRdeNormalDenominatorG` mirrors `cRdeNormalDenominator` (the same `QFunNZ → α`, `cgcdFF → cgcdMonicG`,
`cdivFF → cdivG` substitutions). Returns `none` ("no solution") or the reduction quadruplet
`(a, b, c, h)` reducing `Dy + fy = g` to `a·Dq + b·q = c` with `q = y·h`. -/

/-- **Generic normal-denominator reduction** `cRdeNormalDenominatorG Dt fuel fnum fden gnum gden`
(Bronstein §6.2, book p.185), the `[CField α] [CDiffField α]`-generic mirror of `cRdeNormalDenominator`,
for weakly normalized `f = fnum/fden`, `g = gnum/gden`. Returns `none` ("no solution") or
`some (a, b, c, h)` with `a, h ∈ α[t]`, `b, c` the numerator polynomials over `fden`/`gden`, such that
every solution `y` of `Dy + fy = g` has `q = y·h` solving `a·Dq + b·q = c`. Steps: split the
denominators into normal parts `dₙ, eₙ` (`cSplitFactorFastG`); `p = gcd(dₙ, eₙ)`,
`h = gcd(eₙ, eₙ')/gcd(p, p')`; if `eₙ ∤ dₙh²` then `none`; else `a = dₙh`,
`b = (dₙh·fnum − dₙ·Dh·fden)/fden`, `c = dₙh²·gnum/gden`. -/
def cRdeNormalDenominatorG (Dt : CPolyG α) (fuel : ℕ) (fnum fden gnum gden : CPolyG α) :
    Option (CPolyG α × CPolyG α × CPolyG α × CPolyG α) :=
  let dn := (cSplitFactorFastG Dt fuel fden).1
  let en := (cSplitFactorFastG Dt fuel gden).1
  let p := cgcdMonicG fuel dn en
  let h := cdivG fuel (cgcdMonicG fuel en (cderivG en)) (cgcdMonicG fuel p (cderivG p))
  let dnh2 := cmulG (cmulG dn h) h
  if cdvdG fuel en dnh2 then
    let a := cmulG dn h
    let Dh := cmonomialDeriv Dt h
    let b := cdivG fuel (csubG (cmulG a fnum) (cmulG (cmulG dn Dh) fden)) fden
    let c := cdivG fuel (cmulG dnh2 gnum) gden
    some (a, b, c, h)
  else none

/-! ### The generic §6.2 special-denominator reduction over the tower

`cRdeSpecialDenominatorG` mirrors `cRdeSpecialDenominator`. The special monic irreducible `p` of the
monomial is `cSpecialPolyG` (`cSplitFactorFastG` of `Dt`, monic); `ν_p(·)` is `cValuationG`. The
cancellation refinement (`n_b = 0` branch) needs the §5.12/§7.3 recognizer and is documented but not run,
exactly as in `cRdeSpecialDenominator`. -/

/-- **Generic `p`-adic valuation** `cValuationG fuel p x = ν_p(x)`: the multiplicity of the monic
irreducible `p` dividing `x` (largest `k` with `pᵏ ∣ x`), by trial division. Generic mirror of
`cValuation`. -/
def cValuationG (fuel : ℕ) (p x : CPolyG α) : ℕ :=
  let rec go : ℕ → CPolyG α → ℕ
    | 0, _ => 0
    | fuel + 1, x =>
        if cisZeroG x then 0
        else if cdegG p = 0 then 0
        else if cdvdG fuel p x then 1 + go fuel (cdivG fuel x p)
        else 0
  go fuel x

/-- **Generic special monic irreducible of the monomial** `cSpecialPolyG Dt fuel = p`: the monic special
part of the monomial derivative `Dt` (`t²+1` hypertangent, `t` hyperexponential, `1` primitive), computed
as the monic special part of `Dt` via `cSplitFactorFastG`. Generic mirror of `cSpecialPoly`. -/
def cSpecialPolyG (Dt : CPolyG α) (fuel : ℕ) : CPolyG α :=
  cmonicG (cSplitFactorFastG Dt fuel Dt).2

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

/-- **Generic special-denominator reduction** `cRdeSpecialDenominatorG Dt fuel a b c` (Bronstein §6.2,
book p.190/192), the `[CField α] [CDiffField α]`-generic mirror of `cRdeSpecialDenominator`. Given
`a·Dq + b·q = c` (eq. 6.6) with `a` free of special factors, returns the special-cleared quadruplet
`(ā, b̄, c̄, h)` (`h = p^{−n}`) so that `r = q·h ∈ α[t]` solves `ā·Dr + b̄·r = c̄`. Steps: `p ←
cSpecialPolyG Dt` (constant ⇒ trivial, returns `(a,b,c,1)`); `n_b = ν_p(b)`, `n_c = ν_p(c)`,
`n = min(0, n_c − min(0, n_b))`, `N = max(0, −n_b, n − n_c)`; return `(a·pᴺ, (b + n·a·Dp/p)·pᴺ,
c·p^{N−n}, p^{−n})`. The cancellation refinement (`n_b = 0` branch) is the documented continuation. The
scalar `−negn` is lifted by `cnatCastG` (negated). -/
def cRdeSpecialDenominatorG (Dt : CPolyG α) (fuel : ℕ) (a b c : CPolyG α) :
    CPolyG α × CPolyG α × CPolyG α × CPolyG α :=
  let p := cSpecialPolyG Dt fuel
  if cdegG p = 0 then (a, b, c, [CField.one])
  else
    let nb : ℤ := (cValuationG fuel p b : ℤ)
    let nc : ℤ := (cValuationG fuel p c : ℤ)
    let n : ℤ := min 0 (nc - min 0 nb)
    let N : ℤ := max (max 0 (-nb)) (n - nc)
    let Nnat : ℕ := N.toNat
    let negn : ℕ := (-n).toNat
    let Nminusn : ℕ := (N - n).toNat
    let pN := cpowG p Nnat
    let abar := cmulG a pN
    let DpOverp := cdivG fuel (cmonomialDeriv Dt p) p
    -- `b + n·a·Dp/p` with `n = -negn`: the additive term is `-(negn)·a·(Dp/p)`.
    let bterm := cscaleG (CField.neg (cnatCastG negn)) (cmulG a DpOverp)
    let bbar := cmulG (caddG b bterm) pN
    let cbar := cmulG c (cpowG p Nminusn)
    let h := cpowG p negn
    (abar, bbar, cbar, h)

/-! ### The generic §6.3 degree bound over the tower

`cRdeBoundDegreeG` mirrors `cRdeBoundDegree`: the explicit `deg_t(q)` upper bound, case-split by
`δ = deg(Dt)`. Purely list-degree arithmetic — already `[CField α]`-only; we only swap the binder. The
cancellation refinements (Ch. 7) are documented but not run, exactly as in `cRdeBoundDegree`. -/

/-- **Generic degree bound** `cRdeBoundDegreeG Dt fuel a b c = n ∈ ℕ` (Bronstein §6.3, book p.198–201),
the generic mirror of `cRdeBoundDegree`: an upper bound on `deg_t(q)` for any polynomial solution
`q ∈ α[t]` of `a·Dq + b·q = c`. With `d_a, d_b, d_c` the degrees and `δ = deg(Dt)`: nonlinear (`δ ≥ 2`)
`max(0, d_c − max(d_a + δ − 1, d_b))`; hyperexponential (`δ = 1`) `max(0, d_c − max(d_b, d_a))`;
primitive (`δ = 0`) `max(0, d_c − d_b)` if `d_b > d_a` else `max(0, d_c − d_a + 1)`. The non-cancellation
formula reproduced exactly; the cancellation refinements are the documented continuation. -/
def cRdeBoundDegreeG (Dt : CPolyG α) (_fuel : ℕ) (a b c : CPolyG α) : ℕ :=
  let da : ℤ := (cdegG a : ℤ)
  let db : ℤ := (cdegG b : ℤ)
  let dc : ℤ := (cdegG c : ℤ)
  let δ : ℤ := (cdegG Dt : ℤ)
  let n : ℤ :=
    if 2 ≤ δ then
      max 0 (dc - max (da + δ - 1) db)
    else if δ = 1 then
      max 0 (dc - max db da)
    else
      if da < db then max 0 (dc - db) else max 0 (dc - da + 1)
  n.toNat

/-! ### The generic §6.4 SPDE over the tower

`cSPDEG` mirrors `cSPDE` (Rothstein's `gcd(a,b)`-peel). `cgcdFF → cgcdMonicG`, `cdivFF → cdivG`,
`cmonomialDeriv` already generic. -/

/-- **Generic SPDE** `cSPDEG Dt fuel a b c n` (Bronstein §6.4, Rothstein's box, book p.203), the generic
mirror of `cSPDE`: the `g = gcd(a, b)`-peel reducing the degree-bounded `a·Dq + b·q = c` to one with
`a = 1`. Returns `none` ("no solution of degree `≤ n`") or `some (b̄, c̄, m, α', β)` so any solution is
`q = α'·h + β` with `h` solving `Dh + b̄·h = c̄`, `deg(h) ≤ m`. Fuel-bounded (one level per `gcd`-peel);
the `n < 0`/`c = 0` short-circuit returns the all-zero tuple. -/
def cSPDEG (Dt : CPolyG α) : ℕ → (a b c : CPolyG α) → (n : ℤ) →
    Option (CPolyG α × CPolyG α × ℤ × CPolyG α × CPolyG α)
  | 0, _, _, _, _ => none
  | fuel + 1, a, b, c, n =>
    if n < 0 then
      if cisZeroG c then some ([], [], 0, [], []) else none
    else
      let g := cgcdMonicG fuel a b
      if cdvdG fuel g c then
        let a := cdivG fuel a g
        let b := cdivG fuel b g
        let c := cdivG fuel c g
        if cdegG a = 0 then
          let ainv := CField.inv (cleadG a)
          some (cscaleG ainv b, cscaleG ainv c, n, [CField.one], [])
        else
          let (r, z) := cdiophantineG fuel b a c
          let Da := cmonomialDeriv Dt a
          let Dr := cmonomialDeriv Dt r
          match cSPDEG Dt fuel a (caddG b Da) (csubG z Dr) (n - (cdegG a : ℤ)) with
          | none => none
          | some (bbar, cbar, m, α', β) =>
              some (bbar, cbar, m, cmulG a α', caddG (cmulG a β) r)
      else none

/-! ### The generic §6.5 non-cancellation PolyRischDE over the tower

`cPolyRischDENoCancelG` mirrors `cPolyRischDENoCancel` — the degree-by-degree top-down solve when the
leading terms of `Dq` and `bq` don't cancel. Only `cmonomialDeriv`/`cdegG`/`cleadG`/`CField.div` — all
already generic. -/

/-- **Generic Poly-Risch-DE, non-cancellation case** `cPolyRischDENoCancelG Dt fuel b c n` (Bronstein
§6.5, book p.208), the generic mirror of `cPolyRischDENoCancel`. Solves `Dq + b·q = c` for `q ∈ α[t]`,
`deg(q) ≤ n`, in the non-cancellation case, top-down: `m = deg(c) − deg(b)`, leading monomial
`(lc(c)/lc(b))·tᵐ`, subtract `D(·) + b·(·)`, recurse on the lower-degree remainder. Returns `none` or
`some q`. Fuel-bounded. -/
def cPolyRischDENoCancelG (Dt : CPolyG α) : ℕ → (b c : CPolyG α) → (n : ℤ) →
    Option (CPolyG α)
  | 0, _, _, _ => none
  | fuel + 1, b, c, n =>
    if cisZeroG c then some []
    else
      let m : ℤ := (cdegG c : ℤ) - (cdegG b : ℤ)
      if n < 0 ∨ m < 0 ∨ m > n then none
      else
        let coeff := CField.div (cleadG c) (cleadG b)
        let p := cshiftG m.toNat [coeff]
        let c' := csubG (csubG c (cmonomialDeriv Dt p)) (cmulG b p)
        match cPolyRischDENoCancelG Dt fuel b c' (m - 1) with
        | none => none
        | some q => some (caddG p q)

end CPolyG

end DeepWiki.SymbolicIntegration
