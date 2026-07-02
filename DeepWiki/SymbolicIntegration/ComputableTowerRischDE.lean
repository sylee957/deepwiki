import DeepWiki.SymbolicIntegration.ComputableTowerField
import DeepWiki.SymbolicIntegration.ComputableTowerDeriv
import DeepWiki.SymbolicIntegration.ComputableTowerIntegrate
import DeepWiki.SymbolicIntegration.Computable.QFunReduce
import DeepWiki.SymbolicIntegration.Computable.RischFieldCore
import DeepWiki.SymbolicIntegration.Computable.Hyperexp.Eta

/-! # The recursive Risch-DE oracle over arbitrary-depth differential towers

The generic Risch differential-equation pipeline `cRischDEG` over `CPolyG α = α[t]` — weak
normalization, normal/special denominator, degree bound, SPDE, and the PolyRischDE dispatch — with
the base solve carried by the typeclass `CRischField α`. The instance `CRischField (QFunNZG β)`
runs `cRischDEG` one level down and recurses into `[CRischField β]`, bottoming at `CRischField ℚ`,
so one oracle serves every tower level ℚ(x)(t₁)(t₂)…. Implements the non-cancellation path and the
primitive/hyperexponential cancellation cases; hypertangent cancellation falls back to the
non-cancellation loop. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### Positive-integer-root test for residue resultants

The weak normalizer needs the positive integer roots of the residue resultant `r ∈ α[z]`; the nodes
`n : ℕ` are lifted by the `[CField α]`-only natural cast `cnatCastG`. -/

namespace CPolyG

variable {α : Type*} [CField α]

/-- `cisRootNatG r n = true` iff `r(cnatCastG n) = 0` in `α` (Horner via `cHornerG`): whether the
natural number `n`, lifted to `α`, is a root of `r`. -/
def cisRootNatG (r : CPolyG α) (n : ℕ) : Bool :=
  CField.isZero (cHornerG r (cnatCastG n))

/-- `cPosIntRootsG r bound = [n ∈ {1,…,bound} : r(cnatCastG n) = 0]`: the positive integer roots of
`r` up to `bound` — the multiplicities of the weak-normalizer product; empty for an
already-weakly-normalized input. -/
def cPosIntRootsG (r : CPolyG α) (bound : ℕ) : List ℕ :=
  (List.range bound).filterMap (fun k =>
    let n : ℕ := k + 1
    if cisRootNatG r n then some n else none)

end CPolyG

/-! ### The generic weak normalizer over the tower -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α]

/-- Weak normalizer `cWeakNormalizerG Dt fuel fnum fden = q ∈ α[t]` with `f − Dq/q` weakly
normalized for `f = fnum/fden` (`fuel` bounds the split/gcd sub-ops). Split the denominator into its
normal part `dₙ`, form `d₁ = (dₙ/g)/gcd(dₙ/g, g)` with `g = gcd(dₙ, dₙ')`, solve the Diophantine
equation for the residue numerator `a`, build the residue resultant `r = res_t(a − z·Dd₁, d₁)`, and
return `∏ᵢ gcd(a − nᵢ·Dd₁, d₁)^{nᵢ}` over the positive integer roots `nᵢ` of `r`. For an
already-weakly-normalized `f` the result is `q = 1`. -/
def cWeakNormalizerG (Dt : CPolyG α) (fuel : ℕ) (fnum fden : CPolyG α)
    (boundRoots : ℕ := 16) : CPolyG α :=
  let dn := (cSplitFactorFastG Dt fuel fden).1
  let g := CFracGcdCore.cgcdFFCore fuel dn (cderivG dn)
  let dstar := cdivWf dn g
  let d1 := cdivWf dstar (CFracGcdCore.cgcdFFCore fuel dstar g)
  let fdenOverD1 := cdivWf fden d1
  let a := (cdiophantineGWf fdenOverD1 d1 fnum).1
  let Dd1 := cmonomialDeriv Dt d1
  let r := cResidueResultantTowerG Dt fuel a d1
  let roots := cPosIntRootsG r boundRoots
  roots.foldl (fun (acc : CPolyG α) (n : ℕ) =>
    let gi := CFracGcdCore.cgcdFFCore fuel (csubG a (cscaleG (cnatCastG n) Dd1)) d1
    cmulG acc (cpowG gi n)) [CField.one]

/-! ### The generic normal-denominator reduction over the tower -/

/-- Normal-denominator reduction `cRdeNormalDenominatorG Dt fuel fnum fden gnum gden` for weakly
normalized `f = fnum/fden`, `g = gnum/gden`. Returns `none` ("no solution") or `some (a, b, c, h)`
such that every solution `y` of `Dy + fy = g` has `q = y·h` solving `a·Dq + b·q = c`. Split the
denominators into normal parts `dₙ, eₙ`; `p = gcd(dₙ, eₙ)`, `h = gcd(eₙ, eₙ')/gcd(p, p')`; if
`eₙ ∤ dₙh²` then `none`; else `a = dₙh`, `b = (dₙh·fnum − dₙ·Dh·fden)/fden`, `c = dₙh²·gnum/gden`. -/
def cRdeNormalDenominatorG (Dt : CPolyG α) (fuel : ℕ) (fnum fden gnum gden : CPolyG α) :
    Option (CPolyG α × CPolyG α × CPolyG α × CPolyG α) :=
  let dn := (cSplitFactorFastG Dt fuel fden).1
  let en := (cSplitFactorFastG Dt fuel gden).1
  let p := CFracGcdCore.cgcdFFCore fuel dn en
  let h := cdivWf (CFracGcdCore.cgcdFFCore fuel en (cderivG en)) (CFracGcdCore.cgcdFFCore fuel p (cderivG p))
  let dnh2 := cmulG (cmulG dn h) h
  if cdvdG fuel en dnh2 then
    let a := cmulG dn h
    let Dh := cmonomialDeriv Dt h
    let b := cdivWf (csubG (cmulG a fnum) (cmulG (cmulG dn Dh) fden)) fden
    let c := cdivWf (cmulG dnh2 gnum) gden
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
        else if cdvdG fuel p x then 1 + go fuel (cdivWf x p)
        else 0
  go fuel x

/-- **Generic special monic irreducible of the monomial** `cSpecialPolyG Dt fuel = p`: the monic special
part of the monomial derivative `Dt` (`t²+1` hypertangent, `t` hyperexponential, `1` primitive), computed
as the monic special part of `Dt` via `cSplitFactorFastG`. Generic mirror of `cSpecialPoly`. -/
def cSpecialPolyG (Dt : CPolyG α) (fuel : ℕ) : CPolyG α :=
  cmonicG (cSplitFactorFastG Dt fuel Dt).2

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α]

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
    let DpOverp := cdivWf (cmonomialDeriv Dt p) p
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

/-- **Generic degree bound** `cRdeBoundDegreeG Dt a b c = n ∈ ℕ` (Bronstein §6.3, book p.198–201),
the generic mirror of `cRdeBoundDegree`: an upper bound on `deg_t(q)` for any polynomial solution
`q ∈ α[t]` of `a·Dq + b·q = c`. With `d_a, d_b, d_c` the degrees and `δ = deg(Dt)`: nonlinear (`δ ≥ 2`)
`max(0, d_c − max(d_a + δ − 1, d_b))`; hyperexponential (`δ = 1`) `max(0, d_c − max(d_b, d_a))`;
primitive (`δ = 0`) `max(0, d_c − d_b)` if `d_b > d_a` else `max(0, d_c − d_a + 1)`. The non-cancellation
formula reproduced exactly; the cancellation refinements are the documented continuation. -/
def cRdeBoundDegreeG (Dt : CPolyG α) (a b c : CPolyG α) : ℕ :=
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

`cSPDEG` mirrors `cSPDE` (Rothstein's `gcd(a,b)`-peel). `cgcdFF → CFracGcdCore.cgcdFFCore`,
`cdivFF → cdivWf`, `cdiophantineG → cdiophantineGWf`,
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
      let g := CFracGcdCore.cgcdFFCore fuel a b
      if cdvdG fuel g c then
        let a := cdivWf a g
        let b := cdivWf b g
        let c := cdivWf c g
        if cdegG a = 0 then
          let ainv := CField.inv (cleadG a)
          some (cscaleG ainv b, cscaleG ainv c, n, [CField.one], [])
        else
          let (r, z) := cdiophantineGWf b a c
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

/-! ### The generic §6.6 primitive cancellation PolyRischDE over the tower

`cPolyRischDECancelPrimG` mirrors `cPolyRischDECancelPrim`: the primitive cancellation case (`Dt ∈ α`,
`b ∈ α*`), where `D` does not raise the `t`-degree so the leading terms cancel and the solve recurses
degree-by-degree into the **base RDE over the coefficient field `α`** — `CRischField.crischDESolve b₀
(lc c)` (eq. 6.23 `RischDE(b, lc(c))`). This is exactly where the typeclass-carried recursion ties: the
base solve is the generic `crischDESolve` over the coefficient field. The §5.12
logarithmic-derivative branch (the `b = Dz/z` optimization) is the documented continuation
(the general degree-by-degree recursion is sound without it). -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α] [CRischField α]

/-- **Generic Poly-Risch-DE, primitive cancellation case** `cPolyRischDECancelPrimG Dt fuel b c n`
(Bronstein §6.6, book p.212), the `[CRischField α]`-generic mirror of `cPolyRischDECancelPrim`. Given the
primitive monomial derivation `D` (`Dt ∈ α`), `b ∈ α*` (a degree-0 `t`-polynomial) and `c ∈ α[t]`, with
degree bound `n`, returns `none` ("no solution of degree `≤ n`") or `some q` with `q ∈ α[t]`,
`deg(q) ≤ n`, solving `Dq + b·q = c`, solving degree-by-degree: at degree `m = deg(c)`, the base RDE
`Ds + b₀·s = lc(c)` over `α` (`CRischField.crischDESolve b₀ (lc c)`, eq. 6.23) fixes the next coefficient,
then `c ← c − b·s·tᵐ − D(s·tᵐ)`, recurse. Fuel-bounded (`deg(c)` drops each pass). -/
def cPolyRischDECancelPrimG (Dt : CPolyG α) : ℕ → (b c : CPolyG α) → (n : ℤ) →
    Option (CPolyG α)
  | 0, _, _, _ => none
  | fuel + 1, b, c, n =>
    let b0 : α := cleadG b
    if cisZeroG c then some []
    else if n < (cdegG c : ℤ) then none
    else
      let m : ℕ := cdegG c
      match CRischField.crischDESolve b0 (cleadG c) with
      | none => none
      | some s =>
        let stm : CPolyG α := cshiftG m [s]               -- `s·tᵐ`
        let c' := csubG (csubG c (cmulG b stm)) (cmonomialDeriv Dt stm)
        match cPolyRischDECancelPrimG Dt fuel b c' ((m : ℤ) - 1) with
        | none => none
        | some q => some (caddG stm q)

/-! ### The generic §6.6 hyperexponential cancellation PolyRischDE over the tower

`cPolyRischDECancelExpG` mirrors `cPolyRischDECancelExp`: the hyperexponential case (`Dt/t = η ∈ α`,
`δ = 1`, `b ∈ α*`). The leading terms cancel and the solve recurses degree-by-degree into the **eq. 6.24
base RDE** `Ds + (b + m·η)·s = lc(c)` over `α` — the coefficient shifted by `m·η` (the `tᵐ` factor's
contribution `D(s·tᵐ) = (Ds + m·η·s)·tᵐ`). The shift `η = cExpEtaG Dt` makes the base coefficient
genuinely non-constant, so the base solve `crischDESolve` does real work. -/

/-- **Generic Poly-Risch-DE, hyperexponential cancellation case** `cPolyRischDECancelExpG Dt fuel b c n`
(Bronstein §6.6, book p.213), the `[CRischField α]`-generic mirror of `cPolyRischDECancelExp`. Given the
hyperexponential monomial derivation `D` (`η = Dt/t ∈ α`, `δ = 1`), `b ∈ α*` and `c ∈ α[t]`, with degree
bound `n`, returns `none` or `some q` solving `Dq + b·q = c`, degree-by-degree: at degree `m = deg(c)`,
the eq. 6.24 base RDE `Ds + (b₀ + m·η)·s = lc(c)` over `α`
(`CRischField.crischDESolve (b₀ + m·η) (lc c)`) fixes the next coefficient, then `c ← c − b·s·tᵐ −
D(s·tᵐ)`, recurse. `η = cExpEtaG Dt`; `m·η` via `cnatCastG m`. Fuel-bounded. -/
def cPolyRischDECancelExpG (Dt : CPolyG α) : ℕ → (b c : CPolyG α) → (n : ℤ) →
    Option (CPolyG α)
  | 0, _, _, _ => none
  | fuel + 1, b, c, n =>
    let b0 : α := cleadG b
    let η : α := cExpEtaG Dt
    if cisZeroG c then some []
    else if n < (cdegG c : ℤ) then none
    else
      let m : ℕ := cdegG c
      -- eq. 6.24 base RDE `Ds + (b₀ + m·η)·s = lc(c)` over `α`.
      let coeff : α := CField.add b0 (CField.mul (cnatCastG m) η)
      match CRischField.crischDESolve coeff (cleadG c) with
      | none => none
      | some s =>
        let stm : CPolyG α := cshiftG m [s]               -- `s·tᵐ`
        let c' := csubG (csubG c (cmulG b stm)) (cmonomialDeriv Dt stm)
        match cPolyRischDECancelExpG Dt fuel b c' ((m : ℤ) - 1) with
        | none => none
        | some q => some (caddG stm q)

/-! ### The generic primitive `b = 0` integration branch (Bronstein §6.5, the `cIntegratePolyQ` analog)

When `b = 0` the equation `Dq + b·q = c` is the pure integration `Dq = c`. In the **primitive base** case
the monomial is the canonical iterating variable (`Dt = [1]`, `Dt = 1`, `δ = 0`) with *constant*
coefficients (the level-`n` reduced equation's `cbar` traces back to ℚ-constants, which `α`'s derivation
annihilates), so integration is **termwise**: `∫ Σ cᵢtⁱ = Σ (cᵢ/(i+1)) t^{i+1}`. This is the
`[CField α]`-generic mirror of `cIntegratePolyQ` (the `b = 0` branch of `cPolyRischDEQ`); the division by
`(i+1)` is `CField.div · (cnatCastG (i+1))`. (Termwise integration is exact precisely when `Dt = 1` and
the coefficients are constants — the tower-iteration setting; the dispatcher routes `b = 0` here only in
the primitive case `δ = 0`, exactly as `cPolyRischDEQ` does.) -/

/-- **Generic polynomial antiderivative** `cIntegratePolyG c = q` with `Dq = c` and `q(0) = 0`, for the
canonical primitive monomial (`Dt = 1`) and constant coefficients: termwise
`∫ Σ cᵢtⁱ = Σ (cᵢ/(i+1)) t^{i+1}` (`cᵢ/(i+1) = CField.div cᵢ (cnatCastG (i+1))`). The `[CField α]`-generic
mirror of `cIntegratePolyQ`, the `b = 0` branch of the primitive PolyRischDE. -/
def cIntegratePolyG (c : CPolyG α) : CPolyG α :=
  CField.zero :: ((c : List α).zipIdx.map (fun (a, i) => CField.div a (cnatCastG (i + 1))))

/-! ### The generic §6.5+§6.6 PolyRischDE dispatcher over the tower

`cPolyRischDEG` mirrors `cPolyRischDE` (Lemma 6.5.1 dispatch), with one addition over the tower `cRischDE`
dispatcher: the **`b = 0` primitive-integration branch** (mirroring `cPolyRischDEQ`'s `cisZeroG b` branch),
since the tower recursion always runs the primitive monomial (`Dt = [1]`) where `b = 0` is reachable and
must integrate rather than recurse to a constant solve. Routes by `δ = deg(Dt)` and `deg(b)`. The
hypertangent (`δ ≥ 2`) cancellation falls back to the non-cancellation loop (correct whenever it does not
actually cancel), exactly as in `cPolyRischDE`. -/

/-- **Generic Poly-Risch-DE dispatcher** `cPolyRischDEG Dt fuel b c n` (Bronstein §6.5 + §6.6), the
`[CRischField α]`-generic mirror of `cPolyRischDE` (with the `cPolyRischDEQ` `b = 0` branch folded in).
Solves `Dq + b·q = c` for `q ∈ α[t]`, `deg(q) ≤ n`, routing by monomial type and `deg(b)` (Lemma 6.5.1):
`b = 0` ⇒ pure integration (`cIntegratePolyG`, with the `deg(c)+1 ≤ n` check — the primitive base branch);
`deg(b) > max(0, δ−1)` ⇒ non-cancellation (`cPolyRischDENoCancelG`); `δ = 0, deg(b) = 0` ⇒ primitive
cancellation (`cPolyRischDECancelPrimG`); `δ = 1, deg(b) = 0` ⇒ hyperexponential cancellation
(`cPolyRischDECancelExpG`); else (hypertangent `δ ≥ 2`, the documented Ch. 8 continuation) ⇒ falls back to
the non-cancellation loop. -/
def cPolyRischDEG (Dt : CPolyG α) (fuel : ℕ) (b c : CPolyG α) (n : ℤ) :
    Option (CPolyG α) :=
  let δ : ℤ := (cdegG Dt : ℤ)
  let db : ℤ := (cdegG b : ℤ)
  if cisZeroG b then
    if cisZeroG c then some []
    else if (cdegG c : ℤ) + 1 > n then none
    else some (cIntegratePolyG c)
  else if db > max 0 (δ - 1) then
    cPolyRischDENoCancelG Dt fuel b c n
  else if δ = 0 ∧ db = 0 then
    cPolyRischDECancelPrimG Dt fuel b c n
  else if δ = 1 ∧ db = 0 then
    cPolyRischDECancelExpG Dt fuel b c n
  else
    cPolyRischDENoCancelG Dt fuel b c n

/-! ### The assembled generic Risch-DE solver `cRischDEG` over the tower

`cRischDEG` threads the generic stages, the mechanical generalization of `cRischDE`. For
`f = fnum/fden`, `g = gnum/gden ∈ α(t)` it returns `some (ynum, yden)` with `y = ynum/yden` solving
`Dy + f·y = g`, or `none`. The base solve inside the cancellation cases is the typeclass `crischDESolve`,
so a *level-`n+1`* call of `cRischDEG` recurses into the *level-`n`* `crischDESolve`. -/

/-- **The generic Risch differential equation solver** `cRischDEG Dt fuel fnum fden gnum gden` (Bronstein
Ch. 6, assembled), the `[CField α] [CDiffField α] [CRischField α]`-generic mirror of `cRischDE`. For
`f = fnum/fden`, `g = gnum/gden ∈ α(t)` and the monomial derivation `D = cmonomialDeriv Dt`, returns
`some (ynum, yden)` with `y = ynum/yden ∈ α(t)` solving `Dy + f·y = g`, or `none`. Stages: §6.2 normal
denominator (`cRdeNormalDenominatorG`) → §6.2 special denominator (`cRdeSpecialDenominatorG`) → §6.3
degree bound (`cRdeBoundDegreeG`) → §6.4 SPDE (`cSPDEG`) → §6.5/§6.6 PolyRischDE dispatch
(`cPolyRischDEG`), with the polynomial unknown `Q = α'·v + β` reassembled to `y = Q·h₁ / h₀`. The
cancellation cases recurse into `CRischField.crischDESolve` over `α` — at level `n+1` this is the level-`n`
oracle. (`f` is assumed weakly normalized — the post-Hermite RDE input; `cWeakNormalizerG` returns `q = 1`
on such `f`.) -/
def cRischDEG (Dt : CPolyG α) (fuel : ℕ) (fnum fden gnum gden : CPolyG α) :
    Option (CPolyG α × CPolyG α) :=
  match cRdeNormalDenominatorG Dt fuel fnum fden gnum gden with
  | none => none
  | some (a0, b0, c0, h0) =>
    let (a, b, c, h1) := cRdeSpecialDenominatorG Dt fuel a0 b0 c0
    let N := cRdeBoundDegreeG Dt a b c
    match cSPDEG Dt fuel a b c (N : ℤ) with
    | none => none
    | some (bbar, cbar, m, α', β) =>
      match cPolyRischDEG Dt fuel bbar cbar m with
      | none => none
      | some v =>
        let Q := caddG (cmulG α' v) β
        some (cmulG Q h1, h0)

end CPolyG

/-! ### ★ The recursive instance `CRischField (QFunNZG β)` — the tower recursion tie

The RDE over the field `β(s) = QFunNZG β` is solved by running the generic §6 pipeline `cRischDEG` over
`CPolyG β = β[s]` with the new monomial `s` (`Ds = [1]`, the canonical iterating choice, exactly as the
derivation `CDiffField (QFunNZG β)` uses `towerDerivQFunNZG [1]`), recursing into `[CRischField β]` for
the base solve inside the cancellation cases. **This is where the recursion lives**: a level-`n+1` solve
runs the §6 pipeline at level `n` and recurses to the level-`n` `crischDESolve`, bottoming at
`CRischField ℚ`. So `CRischField (QFunNZG ℚ)` is the RDE over ℚ(x), `CRischField (QFunNZG (QFunNZG ℚ))`
the RDE over ℚ(x)(t₁), … — uniformly, no special-cased `cRationalRDE`.

The instance is `[CField β] [CDiffField β] [CFieldDomain β] [CRischField β]`-built: `CFieldDomain β`
supplies the `CField`/`CDiffField (QFunNZG β)` instances, `CRischField β` the recursive base solve. It is
**computable** (everything routes through the engine; the subtype proofs are `Prop`-erased), so the tower
`crischDESolve` reduces in the native compiler. There is no resolution loop — `CRischField (QFunNZG β)`
requires `CRischField β`, strictly one level down. -/

/-- **The fixed fuel budget** for the recursive tower RDE solve (the class method carries no fuel
argument). Generous enough for the small-degree level-2 validations; deeper/larger problems take a larger
constant. -/
def towerRischDEFuel : ℕ := 60

section Gate
variable {β : Type*} [CField β] [CDiffField β] [CFracGcdCore β]

/-- **★ The denominator-direct §6.1 solvability gate** `cdenomNormalGateG a`: `true` iff the §3.5 normal
part of the denominator **component** `a.1.2` equals `a.1.2` itself — `cisZeroG (normalPart(a.1.2) − a.1.2)`.
The Bronstein §6.1 normality test the raw recursive oracle **omits**: an unsolvable RDE (a special pole with
a non-positive-integer residue surviving in the lowest-terms denominator) fails it, so the gated
`instCRischFieldQFunNZG.crischDESolve` returns `none` rather than a spurious `some`. Reads `a.1.2` directly
(no re-reduction), the denominator the production solver already holds after reducing its RDE input to lowest
terms. The fuel-free API now exposes the corresponding Wf reconciliation in
`ComputableCanonNormalizedReduce`.
`[CField β]`-data only (the `Prop`-erased subtype proof aside), so the gated oracle stays
`native_decide`-reducible. -/
def cdenomNormalGateG (a : QFunNZG β) : Bool :=
  CPolyG.cisZeroG (CPolyG.csubG
    (CPolyG.cSplitFactorFastG ([CField.one] : CPolyG β) towerRischDEFuel a.1.2).1
    a.1.2)

end Gate

section
variable {β : Type*} [CField β] [CDiffField β] [CFieldDomain β] [CFracGcdCore β] [CRischField β]

/-- **★ `CRischField (QFunNZG β)`** — the **§6.1-gated, sound** RDE over `β(s) = QFunNZG β`, built by running
`cRischDEG` over `CPolyG β = β[s]` with the new monomial `s` (`Ds = [1]`) and `[CRischField β]` for the base
solve, **behind the denominator-normality gate `cdenomNormalGateG`**. This ties the tower recursion: solving
an RDE at level `n+1` runs the full §6 pipeline at level `n` and recurses into the level-`n` `crischDESolve`,
bottoming at `CRischField ℚ`. **The gate** (the step the raw oracle skipped, the soundness bug): return `none`
when the §3.5 normal part of `f`'s lowest-terms denominator is not the denominator itself (an unsolvable RDE
— a non-positive-integer-residue special pole survives); else read `f, g` as num/den pairs over `β[s]`, run
`cRischDEG [1] fuel …`, and lift the returned `(ynum, yden)` back to `QFunNZG β` (guarding den-nonzero with
the `cisZeroG` test). Computable (`Prop`-erased subtype proofs), so the tower oracle `native_decide`s. -/
instance instCRischFieldQFunNZG : CRischField (QFunNZG β) where
  crischDESolve f g :=
    if cdenomNormalGateG f then
      match CPolyG.cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2 with
      | none => none
      | some (ynum, yden) =>
        if h : CPolyG.cisZeroG yden = false then some ⟨(ynum, yden), h⟩ else none
    else none

/-- **The gated oracle reduces to the raw solve when the gate passes** (`crischDESolve_eq_solve_of_normal`):
if `cdenomNormalGateG f = true` then `instCRischFieldQFunNZG.crischDESolve f g` is the bare
`cRischDEG [1] fuel`-then-`cisZeroG`-guard match (no gate). The `if_pos` branch of the gate, peeled so the
downstream soundness reductions reach the raw `cRischDEG` success exactly as before the re-pin. -/
theorem crischDESolve_eq_solve_of_normal (f g : QFunNZG β) (hgate : cdenomNormalGateG f = true) :
    CRischField.crischDESolve f g
      = (match CPolyG.cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2 with
         | none => none
         | some (ynum, yden) =>
           if h : CPolyG.cisZeroG yden = false then some ⟨(ynum, yden), h⟩ else none) := by
  rw [show CRischField.crischDESolve f g
      = (if cdenomNormalGateG f then
           match CPolyG.cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2 with
           | none => none
           | some (ynum, yden) =>
             if h : CPolyG.cisZeroG yden = false then some ⟨(ynum, yden), h⟩ else none
         else none) from rfl, if_pos hgate]

/-- **A successful gated solve passed the gate** (`cdenomNormalGateG_of_crischDESolve_isSome`): if
`instCRischFieldQFunNZG.crischDESolve f g = some y` then `cdenomNormalGateG f = true`. The `else none`
branch of the gate forces the check: a `some` result can only come from the `if_pos` branch. So the gated
oracle's success witnesses denominator normality — the soundness gate it now performs. -/
theorem cdenomNormalGateG_of_crischDESolve_isSome (f g y : QFunNZG β)
    (hsolve : CRischField.crischDESolve f g = some y) : cdenomNormalGateG f = true := by
  by_cases hgate : cdenomNormalGateG f = true
  · exact hgate
  · rw [show CRischField.crischDESolve f g
        = (if cdenomNormalGateG f then
             match CPolyG.cRischDEG ([CField.one] : CPolyG β) towerRischDEFuel f.1.1 f.1.2 g.1.1 g.1.2 with
             | none => none
             | some (ynum, yden) =>
               if h : CPolyG.cisZeroG yden = false then some ⟨(ynum, yden), h⟩ else none
           else none) from rfl, if_neg hgate] at hsolve
    exact absurd hsolve (by simp)

end

/-! ### Shared level-2 RDE data

The level-2 right-hand side below is reused by the fuel-free RDE and sound-solver validations. -/

/-- The level-2 right-hand side `g = t₁ + 1 ∈ Lvl2 = ℚ(x)(t₁)` for the non-trivial-`f` headline case
(`lvl2T1` from `ComputableTowerDeriv` is `t₁`). -/
def towerRdeLvl2GPlusOne : Lvl2 := CField.add lvl2T1 CField.one

/-! ## STRETCH — the full poly/special integration driver `cIntegrateGFull` (Bronstein §5.4)

The reduced-case capstone `cIntegrateReducedG` (`ComputableTowerIntegrate`) only does the simple normal
part (Hermite + residue logs); it leaves the **polynomial part** `fₚ` and the **special part** `b/dₛ` of
`f = a/d` undisposed. With the recursive RDE oracle now in hand we can dispatch the **polynomial
part**: for a primitive monomial (`Dt ∈ α`), `∫ fₚ` is the `b = 0` Risch-DE `Dq = fₚ` over `α[t]`, solved
by `cPolyRischDEG Dt fuel 0 fₚ (deg fₚ + 1)` (Bronstein §5.4 `IntegratePolynomial`, primitive case — the
degree-by-degree antiderivative). `cIntegrateGFull` adds this on top of the canonical split and the
reduced-case capstone: split `f`, solve
the polynomial part by the oracle, integrate the normal part by `cIntegrateReducedG`, **combine the two
rational parts** `qₚ + gₙ/gₙd`, and require the special part to vanish (special-part integration over a
primitive extension is degenerate — `dₛ = 1` — so this loses nothing in the primitive case; the genuine
hyperexp/hypertangent special part is the documented continuation). This uses the new
`CRischField`/`cPolyRischDEG`, so it lands the integrals the reduced-case capstone could not. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α] [CRischField α]

/-- **The full poly/special tower integral** `cIntegrateGFull Dt fuel a d cands` (Bronstein Ch. 5,
extending the reduced-case capstone `cIntegrateReducedG` with the polynomial part). Integrate `f = a/d ∈ α(t)` over
`D = cmonomialDeriv Dt`, returning `some ⟨(num, den), logs⟩` with `∫ f = num/den + ∑ᵢ cᵢ·log(vᵢ)`, or
`none`. Steps: (1) `canonicalRepresentationFastG` splits `f = fₚ + (b/dₛ) + (cₙ/dₙ)`; (2) the polynomial
part `fₚ` is integrated by the **RDE oracle** — `cPolyRischDEG Dt fuel 0 fₚ (deg fₚ + 1)` solves the
`b = 0` equation `Dqₚ = fₚ` (primitive case); (3) the simple normal part `cₙ/dₙ` by `cIntegrateReducedG`
(Hermite + residue logs); (4) combine the rational parts `qₚ + gₙ/gₙd = (qₚ·gₙd + gₙ)/gₙd`; require the
special part `b` to vanish (else `none`, the documented continuation). `[CField α] [CDiffField α]
[CRischField α]`-generic — runs at any tower level. Lands the polynomial-part integrals that the
reduced-case capstone `cIntegrateReducedG` leaves undisposed. -/
def cIntegrateGFull (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α) :
    Option (IntegralResultG α) :=
  let (fp, (b, _ds), (cn, dn)) := canonicalRepresentationFastG Dt fuel a d
  if cisZeroG b then
    -- normal part: rational `gₙ/gₙd` + logs.
    let nrm := cIntegrateReducedG Dt fuel cn dn cands
    let (gnum, gden) := nrm.rational
    if cisZeroG fp then
      some nrm
    else
      -- polynomial part: solve `Dqₚ = fₚ` by the `b = 0` RDE oracle (primitive case).
      match cPolyRischDEG Dt fuel [] fp ((cdegG fp : ℤ) + 1) with
      | none => none
      | some qp =>
        -- combine `qₚ + gₙ/gₙd = (qₚ·gₙd + gₙ)/gₙd`.
        let num := caddG (cmulG qp gden) gnum
        some ⟨(num, gden), nrm.logs⟩
  else none

end CPolyG

end DeepWiki.SymbolicIntegration
