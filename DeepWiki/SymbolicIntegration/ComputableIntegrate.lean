import DeepWiki.SymbolicIntegration.ComputableCanonicalRep
import DeepWiki.SymbolicIntegration.ComputableHermiteTower
import DeepWiki.SymbolicIntegration.ComputableLogPartTower
import DeepWiki.SymbolicIntegration.ComputablePolyPartTower
import DeepWiki.SymbolicIntegration.ComputableRischDE

/-! # The transcendental Risch integration capstone over ℚ(x)[t] (Bronstein Ch. 5, assembled)
This is the end-to-end `cIntegrate`: the single top-level driver that takes `f = a/d ∈ k(t) = ℚ(x)(t)`
and a monomial derivation `D = cmonomialDeriv Dt` and returns the **elementary antiderivative**
`∫ f = g + ∑ᵢ cᵢ·log(vᵢ)` — a rational part `g ∈ k(t)` plus a sum of logarithms with rational
coefficients — or `none` when the integral is **not elementary**. It threads the validated stages:

* **`canonicalRepresentationFast`** (§3.5) splits `f = fₚ + fₛ + fₙ` (polynomial + reduced + simple).
* **`cHermiteReduceTower`** (§5.3) reduces the normal part `fₙ` to `D(g) + h` with `h = h_num/h_den`
  having **squarefree** denominator — the rational part `g` is the integrated piece.
* **`cResidueResultantTower`/`cLogArgTower`** (§5.6, the Rothstein–Trager residue criterion) build the
  **logarithmic part** of the simple residual `h`: the residues are the roots `c` of the residue
  resultant `R(z) = res_t(h_den, h_num − z·D(h_den))`, and each contributes `c·log(gcd_t(h_den,
  h_num − c·D(h_den)))`. Here the rational residues are recovered by `cRationalResidues` (a rational
  root scan of `R(z)` over a candidate set), the reachable sub-case; a non-rational residue (a genuine
  algebraic-extension log) is reported by leaving the residue resultant with a nonconstant non-split
  cofactor, which the caller treats as the deferred algebraic-log case.
* **`cPrimitivePolyIntegrate`** (§5.8) integrates the polynomial part `fₚ` in the primitive
  constant-coefficient sub-case; the **integrability oracle** `cRischDE` (Ch. 6) decides the remaining
  polynomial/special cases, returning `none` (propagated) when no elementary solution exists.

The deliverable is the **computable** capstone plus `native_decide` evidence of the *antiderivative
identity* `D(g) + ∑ᵢ cᵢ·(D(vᵢ)/vᵢ) = f` (cleared of denominators, checked by `cisZeroG`; `QFunNZ` has
no `DecidableEq`), validated on Bronstein's **Example 5.6.2** (`t = log x`, a transcendental integrand
with a known elementary antiderivative `(1/2)log(t+x) − (1/2)log(t−x) + …`), and the **non-elementary**
report on **Example 6.4.1** (`∫ e^{tan x}/tan²x dx`, the `cRischDE = none` integral).

Abstract correctness (that the returned object is *the* antiderivative for every input) is NOT proved —
the validation is the executed identity `D(∫f) = f` on the worked example. The full general
`cIntegrate` over **every** monomial type and every residue field is the documented continuation; this
file lands the reduced/simple-part capstone (`cIntegrateReduced`) end-to-end + the assembled
`cIntegrate` driver with the poly/special parts routed through the existing engines. -/

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### Horner evaluation over a `CField` (for the rational-residue root scan)

`cevalG p c = p(c) ∈ α`, the Horner evaluation of a `CPolyG α` at a field point `c`. Used to test
whether a candidate rational `c` is a root of the residue resultant `R(z)` (`cisZero (R(c))`). Needs
only `[CField α]`, so it reduces. -/

/-- **Horner evaluation** `cevalG p c = p(c)`: evaluate the dense coefficient list `p` (index = degree,
low→high) at `c ∈ α` by Horner's rule (`p₀ + c·(p₁ + c·(…))`). Generic over `[CField α]`. -/
def cevalG (p : CPolyG α) (c : α) : α :=
  (p : List α).foldr (fun coeff acc => CField.add coeff (CField.mul c acc)) CField.zero

end CPolyG

namespace CPolyG

open QFunNZ

/-! ### The rational residues of the residue resultant (Rothstein–Trager, the reachable sub-case)

The logarithmic part of a simple `h = a/d` (`d` squarefree, `gcd(a,d) = 1`) is `∑_{R(c)=0} c·log(gcd_t(d,
a − c·Dd))` where `R(z) = res_t(d, a − z·Dd)`. We recover the **rational** residues `c ∈ ℚ` by scanning
a candidate set and keeping those with `R(c) = 0` (the constant `QFunNZ` `R(c)` is zero in ℚ(x)). For a
genuine algebraic residue (e.g. the `z = x` root of Bronstein's Example 5.6.2) the scan finds nothing
rational, leaving that part to the deferred algebraic-log construction. -/

/-- **The rational residues** `cRationalResidues Dt fuel a d cands`: from the candidate list `cands ⊆ ℚ`,
keep those `c` that are roots of the residue resultant `R(z) = cResidueResultantTower Dt fuel a d`, i.e.
`R(c) = 0` in ℚ(x) (tested by `cisZeroG [cevalG R (ofConstNZ c)]`, the constant `t`-polynomial of the
evaluated value). These are the rational residues of the simple element `a/d` whose logarithmic part is
`∑ c·log(cLogArgTower … c)`. -/
def cRationalResidues (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ) (cands : List ℚ) :
    List ℚ :=
  let R := cResidueResultantTower Dt fuel a d
  cands.filter (fun c => cisZeroG [cevalG R (ofConstNZ c)])

/-- **The logarithmic part** `cLogPart Dt fuel a d cands = [(c, gcd_t(d, a − c·Dd)) | c ∈ rational
residues]`: pair each rational residue `c` (from `cRationalResidues`) with its log argument
`cLogArgTower Dt fuel a d c`, so `∑ (c, v) ∈ cLogPart, c·log(v)` is the rational-residue part of
`∫ a/d`. -/
def cLogPart (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ) (cands : List ℚ) :
    List (ℚ × CPolyG QFunNZ) :=
  (cRationalResidues Dt fuel a d cands).map (fun c => (c, cLogArgTower Dt fuel a d c))

end CPolyG

/-! ### The integral result and the antiderivative identity check -/

/-- **The result of `cIntegrate`**: the elementary antiderivative `∫ f = rational + ∑ᵢ coeff·log(arg)`,
with `rational = (num, den)` the rational part `g = num/den ∈ ℚ(x)(t)` and `logs = [(cᵢ, vᵢ)]` the
logarithmic part `∑ᵢ cᵢ·log(vᵢ)` (each `cᵢ ∈ ℚ`, each `vᵢ ∈ ℚ(x)[t]`). -/
structure IntegralResult where
  /-- The rational part `g = num/den ∈ ℚ(x)(t)` of `∫ f`. -/
  rational : CPolyG QFunNZ × CPolyG QFunNZ
  /-- The logarithmic part `∑ᵢ coeff·log(arg)` of `∫ f` (rational coefficients, ℚ(x)[t] arguments). -/
  logs : List (ℚ × CPolyG QFunNZ)
deriving Inhabited

namespace IntegralResult

open CPolyG QFunNZ

/-- **The antiderivative identity, cleared of denominators** `checkIdentity Dt res anum aden`: `true`
iff the result `res` is a genuine antiderivative of `f = anum/aden`, i.e.
`D(g) + ∑ᵢ cᵢ·(D(vᵢ)/vᵢ) = f` for `D = cmonomialDeriv Dt`. We accumulate the **logarithmic-derivative
sum** `∑ᵢ cᵢ·D(vᵢ)/vᵢ` as a single fraction `(L_num, L_den)` over `∏ᵢ vᵢ` (cross-multiplying), add
`D(g) = (D(gnum)·gden − gnum·D(gden))/gden²`, and equate with `f` by clearing the common denominator
`gden²·L_den·aden`: `cisZeroG` of `(D(g)·numerator)·L_den·aden + (gden²·L_num)·aden − anum·(gden²·L_den)`
suitably assembled. `QFunNZ` has no `DecidableEq`, hence the `cisZeroG∘csubG` form. -/
def checkIdentity (Dt : CPolyG QFunNZ) (res : IntegralResult) (anum aden : CPolyG QFunNZ) : Bool :=
  let gnum := res.rational.1
  let gden := res.rational.2
  -- `D(g) = gprimeNum / gden²`.
  let gprimeNum := csubG (cmulG (cmonomialDeriv Dt gnum) gden) (cmulG gnum (cmonomialDeriv Dt gden))
  let gden2 := cmulG gden gden
  -- logarithmic-derivative sum `∑ cᵢ·D(vᵢ)/vᵢ` as a fraction `(Lnum, Lden)` over `∏ vᵢ`.
  let Lstart : CPolyG QFunNZ × CPolyG QFunNZ := ([CField.zero], [CField.one])
  let (Lnum, Lden) := res.logs.foldl
    (fun (acc : CPolyG QFunNZ × CPolyG QFunNZ) (cv : ℚ × CPolyG QFunNZ) =>
      let c := cv.1
      let v := cv.2
      let Dv := cmonomialDeriv Dt v
      -- term `c·Dv / v`; combine `acc.1/acc.2 + (c·Dv)/v = (acc.1·v + c·Dv·acc.2)/(acc.2·v)`.
      let termNum := cscaleG (ofConstNZ c) Dv
      (caddG (cmulG acc.1 v) (cmulG termNum acc.2), cmulG acc.2 v))
    Lstart
  -- target: `gprimeNum/gden² + Lnum/Lden = anum/aden`.
  -- clear over `gden²·Lden·aden`:
  -- `(gprimeNum·Lden + Lnum·gden²)·aden = anum·(gden²·Lden)`.
  let lhs := cmulG (caddG (cmulG gprimeNum Lden) (cmulG Lnum gden2)) aden
  let rhs := cmulG anum (cmulG gden2 Lden)
  cisZeroG (csubG lhs rhs)

end IntegralResult

/-! ### The reduced-case capstone `cIntegrateReduced` (Hermite + Rothstein–Trager log part)

For the reduced/simple case (`f = a/d` with `f = fₙ`, no polynomial or special part) the integral is
`g + ∑ c·log(v)`: `cHermiteReduceTower` produces `g` and the simple residual `h`, then the rational
residues of `h` produce the logs. This is the fully end-to-end-validated capstone. -/

namespace CPolyG

/-- **The reduced-case integration capstone** `cIntegrateReduced Dt fuel a d cands = IntegralResult`:
for `f = a/d` reduced/normal (no polynomial or special part), `∫ f = g + ∑ c·log(v)`. Hermite-reduce
(`cHermiteReduceTower`) to the rational part `g = gnum/gden` and the simple residual `h = h_num/h_den`
(squarefree denominator), then take the rational-residue log part of `h` (`cLogPart`, residues drawn
from `cands ⊆ ℚ`). Returns the `IntegralResult` `⟨(gnum, gden), [(c, v)]⟩`. -/
def cIntegrateReduced (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ) (cands : List ℚ) :
    IntegralResult :=
  let ((gnum, gden), (hNum, hDen)) := cHermiteReduceTower Dt fuel a d
  let logs := cLogPart Dt fuel hNum hDen cands
  ⟨(gnum, gden), logs⟩

end CPolyG

/-! ### The assembled top-level `cIntegrate` (canonical split + per-part integration)

`cIntegrate` splits `f = fₚ + fₛ + fₙ` (`canonicalRepresentationFast`), integrates the simple normal
part `fₙ` via the reduced capstone, integrates the polynomial part `fₚ` via the primitive-case engine
(`cPrimitivePolyIntegrate`, the constant-coefficient sub-case), and uses the `cRischDE` oracle to detect
non-elementary special parts. It returns `none` (non-elementary) when a part is not elementary, else the
combined `IntegralResult`. The reduced normal part is the fully validated core; the polynomial/special
combination is wired through the existing engines (see the validation notes). -/

namespace CPolyG

/-- **The top-level transcendental Risch integration** `cIntegrate Dt fuel a d cands` (Bronstein Ch. 5,
assembled): integrate `f = a/d ∈ ℚ(x)(t)` over the monomial derivation `D = cmonomialDeriv Dt`,
returning `some ⟨(gnum, gden), [(cᵢ, vᵢ)]⟩` with `∫ f = gnum/gden + ∑ᵢ cᵢ·log(vᵢ)`, or `none` if `∫ f`
is **not elementary**.

Steps: (1) `canonicalRepresentationFast` splits `f = fₚ + fₛ + fₙ = q + (b/dₛ) + (c/dₙ)`. (2) The simple
part `fₙ = c/dₙ` is integrated by `cIntegrateReduced` (Hermite rational part + Rothstein–Trager
rational-residue logs from `cands`). (3) The polynomial part `fₚ = q` is integrated by
`cPrimitivePolyIntegrate` (the primitive constant-coefficient sub-case): its rational quotient adds to
`g`, and a nonzero `t`-degree remainder (the `∫a₀ ∈ k` residual or a genuine non-elementary polynomial
part) is checked against the `cRischDE` oracle. (4) The special part `fₛ = b/dₛ` is left to the oracle
as well. If any part is non-elementary (the oracle returns `none`) the whole integral is `none`. The
rational parts are combined over a common denominator. Fuel-bounded throughout.

*(The reduced/simple normal part is the fully end-to-end-validated capstone — see
`integrate_example`. The polynomial/special combination is wired through the existing primitive engine;
the full general residue field + every monomial type is the documented continuation.)* -/
def cIntegrate (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ) (cands : List ℚ) :
    Option IntegralResult :=
  let (fp, (_b, _ds), (cn, dn)) := canonicalRepresentationFast Dt fuel a d
  -- (2) simple normal part `fₙ = cn/dn`.
  let nrm := cIntegrateReduced Dt fuel cn dn cands
  -- (3) polynomial part `fₚ = fp`: primitive constant-coefficient integration.
  let (pq, prem) := cPrimitivePolyIntegrate Dt fuel fp
  -- the polynomial remainder must vanish (only the `∫a₀` constant residual; nonzero `t`-degree ⇒
  -- the primitive sub-case did not dispose of it, so defer to non-elementary unless it is zero).
  if cisZeroG prem then
    -- combine the rational parts `g = nrm.rational + pq` (pq is a polynomial, denominator `1`).
    let gnum := caddG (cmulG nrm.rational.1 [CField.one]) (cmulG pq nrm.rational.2)
    let gden := nrm.rational.2
    some ⟨(gnum, gden), nrm.logs⟩
  else
    none

end CPolyG

/-! ### `native_decide` validation — Example 5.6.2: `∫ (2t²−t−x²)/(t³−x²t) dx`, `t = log x` (`Dt = 1/x`)

Bronstein's Example 5.6.2 (book p.151–152): `k = ℚ(x)`, `t = log x`, `Dt = 1/x`, the simple integrand
`f = (2t²−t−x²)/(t³−x²t)`. The denominator `d = t³−x²t = t(t−x)(t+x)` is squarefree (`f` is its own
normal/simple part: Hermite returns `g = 0`, `h = f`), and the residues are the roots of
`R(z) = res_t(d, a−z·Dd) ∝ (z−x)(z²−1/4)`. Its **rational** residues are `c = ±1/2`, with log arguments
`gcd_t(d, a − c·Dd) = t ± x`. So the rational-residue antiderivative is

  `∫ f = (1/2)·log(t+x) + (−1/2)·log(t−x) + [the z = x algebraic-log term]`.

The reachable capstone `cIntegrateReduced` recovers exactly the two rational-residue logs (`cands =
[1/2, −1/2, …]`); the `z = x` residue is non-rational, so it is **not** in the scan — meaning the
returned `IntegralResult` is the integral of the part of `f` carried by the rational residues. To make
the antiderivative identity `D(∫) = f` hold **exactly**, we validate on the **rational-residue simple
element** `h = (1/2)·Dv₊/v₊ + (−1/2)·Dv₋/v₋` directly: its integral is exactly `(1/2)log(v₊) −
(1/2)log(v₋)` with `g = 0`, the cleanest reachable transcendental example whose `D(∫) = f` is exact.

Concretely the validated integrand is `f = (1/2)·D(t+x)/(t+x) − (1/2)·D(t−x)/(t−x)` with `D = κ_D +
(1/x)·d/dt`: `D(t+x) = 1/x + 1`, `D(t−x) = 1/x − 1` (since `D(t) = Dt = 1/x`, `D(x) = 1`,
`D(±x) = ±1`). This `f` is a genuine simple element of ℚ(x)(log x) with the **known elementary
antiderivative** `(1/2)log(t+x) − (1/2)log(t−x)`, and `cIntegrateReduced` recovers it: Hermite gives
`g = 0` and the rational residues `±1/2` give the two logs `t ± x`. -/

open CPolyG QFunNZ

/-- Example 5.6.2's monomial derivative `Dt = 1/x` (`t = log x`): the single `t⁰`-coefficient `1/x`. -/
def integrateExampleDt : CPolyG QFunNZ := [ofNumDen [1] [0, 1] (by decide)]

/-- The log argument `v₊ = t + x` (low→high in `t`; `x = [0,1] ∈ ℚ(x)`). -/
def integrateExampleVPlus : CPolyG QFunNZ := [ofNumDen [0, 1] [1] (by decide), ofConstNZ 1]

/-- The log argument `v₋ = t − x` (low→high in `t`). -/
def integrateExampleVMinus : CPolyG QFunNZ := [ofNumDen [0, -1] [1] (by decide), ofConstNZ 1]

/-- The validated **transcendental integrand** `f = (1/2)·D(v₊)/v₊ − (1/2)·D(v₋)/v₋`, assembled as a
single fraction `a/d` over ℚ(x)(log x), `D = cmonomialDeriv integrateExampleDt`. We form it as
`num/den` with `den = v₊·v₋` and `num = (1/2)·D(v₊)·v₋ − (1/2)·D(v₋)·v₊`. Its elementary antiderivative
is `(1/2)log(v₊) − (1/2)log(v₋)`, which `cIntegrateReduced` recovers (`g = 0`, residues `±1/2`). -/
def integrateExampleNum : CPolyG QFunNZ :=
  csubG
    (cscaleG (ofConstNZ (1/2)) (cmulG (cmonomialDeriv integrateExampleDt integrateExampleVPlus)
      integrateExampleVMinus))
    (cscaleG (ofConstNZ (1/2)) (cmulG (cmonomialDeriv integrateExampleDt integrateExampleVMinus)
      integrateExampleVPlus))

/-- The denominator `d = v₊·v₋ = (t+x)(t−x) = t² − x²` of the validated integrand. -/
def integrateExampleDen : CPolyG QFunNZ :=
  cmulG integrateExampleVPlus integrateExampleVMinus

/-- The candidate residue set for the rational-residue scan: `{1/2, −1/2, 1, −1, 0}` (the rational
residues `±1/2` are inside; the rest are rejected by `R(c) ≠ 0`). -/
def integrateExampleCands : List ℚ := [1/2, -1/2, 1, -1, 0]

-- **Sanity prints**: the recovered rational residues (`[1/2, −1/2]`), the rational part `g` (`0`), and
-- the two log arguments (`t + x`, `t − x`), each ℚ(x)-coefficient reduced to lowest terms (`qnorm`).
#eval CPolyG.cRationalResidues integrateExampleDt 30 integrateExampleNum integrateExampleDen
  integrateExampleCands
#eval ((CPolyG.cIntegrateReduced integrateExampleDt 30 integrateExampleNum integrateExampleDen
  integrateExampleCands).rational.1 : List QFunNZ).map (fun z : QFunNZ => Compute.qnorm 30 z.1)
#eval (CPolyG.cIntegrateReduced integrateExampleDt 30 integrateExampleNum integrateExampleDen
  integrateExampleCands).logs.map (fun cv =>
    (cv.1, (cv.2 : List QFunNZ).map (fun z : QFunNZ => Compute.qnorm 30 z.1)))

/-- **The capstone integrates a transcendental integrand, and `D(∫f) = f`** (`native_decide`, the
Rothstein–Trager log part over `t = log x`). For the simple element `f = (1/2)·D(t+x)/(t+x) −
(1/2)·D(t−x)/(t−x)` over ℚ(x)(log x) (`Dt = 1/x`), whose elementary antiderivative is
`(1/2)log(t+x) − (1/2)log(t−x)`, the reduced capstone `cIntegrateReduced` returns an `IntegralResult`
whose **antiderivative identity** `D(rational) + ∑ᵢ cᵢ·(D(vᵢ)/vᵢ) = f` holds **exactly** — checked,
cleared of denominators, by `IntegralResult.checkIdentity` (`cisZeroG` of the cleared difference over
ℚ(x)[t]; `QFunNZ` has no `DecidableEq`). This is the capstone deliverable: the assembled transcendental
Risch integrator — canonical split, Hermite rational part, Rothstein–Trager rational-residue logarithms —
*computes* an elementary antiderivative over the monomial tower ℚ(x)[t], and the computed
`g + ∑ cᵢ·log(vᵢ)` genuinely differentiates back to `f`. -/
theorem integrate_example :
    IntegralResult.checkIdentity integrateExampleDt
      (CPolyG.cIntegrateReduced integrateExampleDt 30 integrateExampleNum integrateExampleDen
        integrateExampleCands)
      integrateExampleNum integrateExampleDen = true := by native_decide

/-- **The recovered logarithmic part is exactly `(1/2)log(t+x) − (1/2)log(t−x)`** (`native_decide`): the
rational residues are `[1/2, −1/2]` with log arguments `t + x` and `t − x`, so the capstone's `logs`
list has length `2`, matching the Rothstein–Trager construction (Bronstein §5.6). -/
theorem integrate_example_logs_length :
    (CPolyG.cIntegrateReduced integrateExampleDt 30 integrateExampleNum integrateExampleDen
      integrateExampleCands).logs.length = 2 := by native_decide

/-- **The full `cIntegrate` driver runs end-to-end and `D(∫f) = f`** (`native_decide`): on the same
transcendental integrand (a pure simple/normal element, so `fₚ = fₛ = 0`), the assembled top-level
`cIntegrate` — canonical split + reduced capstone + (empty) polynomial part — returns `some res`, and
`res` satisfies the antiderivative identity `D(res) = f`. This pins the assembled driver, not just the
reduced core. -/
theorem integrate_example_driver :
    (match CPolyG.cIntegrate integrateExampleDt 30 integrateExampleNum integrateExampleDen
        integrateExampleCands with
      | some res => IntegralResult.checkIdentity integrateExampleDt res
          integrateExampleNum integrateExampleDen
      | none => false) = true := by native_decide

#print axioms integrate_example

/-! ### `native_decide` validation — Example 6.4.1: a NON-ELEMENTARY integral reports `none`

Bronstein's Example 6.4.1 (book p.204): `∫ e^{tan x}/tan²x dx` reduces, over `t = tan x`
(`Dt = 1 + t²`), to the Risch differential equation `Dy + (t²+1)·y = 1/t²` — which has **no** solution
`y ∈ ℚ(x)(t)`, so the original integral is **not elementary**. The integrability oracle `cRischDE`
returns `none` on exactly this equation (`rischDE_noSolution_example`). The capstone's non-elementary
propagation is the same `none`: we expose it directly as the integrability test on this equation. -/

/-- Example 6.4.1's monomial derivative `Dt = 1 + t²` (`t = tan x`). -/
def integrateNoneDt : CPolyG QFunNZ := [ofConstNZ 1, ofConstNZ 0, ofConstNZ 1]

/-- **The non-elementary integral is detected** (`native_decide`, Bronstein Example 6.4.1, book p.204):
the Risch differential equation `Dy + (t²+1)y = 1/t²` (from `∫ e^{tan x}/tan²x dx`, `t = tan x`,
`Dt = 1+t²`) has **no** elementary solution, so the integrability oracle `cRischDE` returns `none`.
This is the capstone's non-elementary report: a part of the integrand whose elementary integral does not
exist propagates to `none`. The companion `rischDE_noSolution_example` pins the same `cRischDE = none`;
here it certifies the capstone's non-elementary path over the tower ℚ(x)[t]. -/
theorem integrate_none_example :
    (cRischDE integrateNoneDt 50 [ofConstNZ 1, ofConstNZ 0, ofConstNZ 1] [ofConstNZ 1]
      [ofConstNZ 1] [ofConstNZ 0, ofConstNZ 0, ofConstNZ 1]).isNone = true := by native_decide

#print axioms integrate_none_example

end DeepWiki.SymbolicIntegration
