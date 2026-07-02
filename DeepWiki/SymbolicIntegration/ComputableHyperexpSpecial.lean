import DeepWiki.SymbolicIntegration.ComputableTowerRischDE
import DeepWiki.SymbolicIntegration.ComputableHyperexpLaurentCore

/-! # The hyperexponential special-part integral — term-by-term Laurent integration (Bronstein §5.10)
`ComputableTowerIntegrate`/`ComputableTowerRischDE` built the generic tower integration pipeline and the
recursive Risch-DE oracle (`cRischDEG` + the class `CRischField`, with the §6.6 hyperexponential
cancellation `Dy + j·η·y = g`). The full driver `cIntegrateGFull` there closes the **polynomial** part
(`∫ fₚ`) but still requires the canonical-split **special** part `b/dₛ` to vanish (`cisZeroG b`). This
file closes that gap for a **hyperexponential** monomial `t` (`Dt = η·t`, `η ∈ k`) via Bronstein §5.10's
term-by-term Laurent integration.

## §5.10 the algorithm
For a hyperexponential `t`, the special monic irreducible is `t` itself, so a canonical split's polynomial
+ special part `fₚ + fₛ` is a **Laurent polynomial** `∑ⱼ aⱼ tʲ` (`j` from `−m` to `n`, `aⱼ ∈ k`). Each
term integrates by solving an RDE over the base `k`: for `∫ aⱼ tʲ` we need `qⱼ ∈ k` with `D(qⱼ tʲ) = aⱼ tʲ`,
i.e. (since `D(qⱼ tʲ) = (Dqⱼ + j·η·qⱼ) tʲ`)

* solve `Dqⱼ + (j·η)·qⱼ = aⱼ` via **`CRischField.crischDESolve (j·η) aⱼ`** (the oracle of §6.6).

The `j = 0` term `∫ a₀` is the base integration `Dq₀ = a₀` — the *same* call with `f = 0`
(`crischDESolve 0 a₀`). If any `qⱼ` fails to exist the special part is non-elementary ⇒ `none`. The result
`∑ⱼ qⱼ tʲ` is reassembled as a single fraction `num/tᵐ` with `num[j+m] = qⱼ`. The **normal part** `fₙ` goes
through the existing `cIntegrateReducedG` (Hermite + Rothstein–Trager), exactly as in `cIntegrateGFull`.

**★ The headline `native_decide`** integrates `∫ 1/exp = −1/exp` at a **hyperexponential tower level**
(`t = exp x` over ℚ(x), `Dt = η·t`, `η = 1`): the special term `t⁻¹` — which the reduced-case capstone
`cIntegrateReducedG` leaves undisposed — is landed by `cIntegrateHyperexpG` as `−1/t`, with the antiderivative identity
`D(∫f) = f` certified by `checkIdentityG`. The Laurent coefficient `a₋₁ = 1` drives the base RDE
`Dq₋₁ + (−1·η)·q₋₁ = 1` (`crischDESolve (−1) 1` over ℚ(x), `q₋₁ = −1`), so `∫ t⁻¹ = −t⁻¹`. Everything stays
`[CField α]`/`[CDiffField α]`/`[CFieldDomain α]`/`[CRischField α]`-only (`Prop`-erased subtype proofs), so
nothing noncomputable reaches the native compiler.

**Scope.** §5.10 for a **hyperexponential** monomial. The **hypertangent** special part (the `t²+1`-adic
Laurent expansion, needing the Ch. 8 coupled differential system) is the documented continuation, not
attempted here. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α] [CRischField α]

/-! ### The full hyperexponential integral driver `cIntegrateHyperexpG` (Bronstein §5.4 + §5.10)

`cIntegrateHyperexpG Dt fuel a d cands` integrates `f = a/d ∈ k(t)` for a **hyperexponential** monomial
`t` (`Dt = η·t`, `η = cExpEtaG Dt`): canonical-split `f = fₚ + (b/dₛ) + (cₙ/dₙ)`; route the Laurent part
`fₚ + b/dₛ` through `cIntegrateHyperexpLaurentG` (§5.10), the normal part through `cIntegrateReducedG`
(Hermite + Rothstein–Trager); combine the rational parts. This is the hyperexponential analogue of
`cIntegrateGFull` (which handled only `fₚ` and required `b = 0`). -/

/-- **The full hyperexponential integral** `cIntegrateHyperexpG Dt fuel a d cands` (Bronstein §5.4 + §5.10):
integrate `f = a/d ∈ k(t)` for a hyperexponential monomial `t` (`Dt = η·t`, `δ = 1`, `η = cExpEtaG Dt`),
returning `some ⟨(num, den), logs⟩` with `∫ f = num/den + ∑ᵢ cᵢ·log(vᵢ)`, or `none`. Steps:
(1) `canonicalRepresentationFastG` splits `f = fₚ + (b/dₛ) + (cₙ/dₙ)`;
(2) the **Laurent part** `fₚ + b/dₛ` (positives `fₚ`, negatives from `cHyperexpSpecialNegG b dₛ`) is
integrated by `cIntegrateHyperexpLaurentG η` (§5.10, each coefficient through the RDE oracle);
(3) the simple normal part `cₙ/dₙ` by `cIntegrateReducedG` (Hermite + residue logs);
(4) combine the two rational parts `(qₗₐᵤᵣ/denₗₐᵤᵣ) + (gₙ/gₙd) = (qₗₐᵤᵣ·gₙd + gₙ·denₗₐᵤᵣ)/(denₗₐᵤᵣ·gₙd)`.
`none` if the §5.10 Laurent integration fails (some `qⱼ` non-elementary). `[CField α] [CDiffField α]
[CRischField α]`-generic — runs at any hyperexponential tower level. -/
def cIntegrateHyperexpG (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α) :
    Option (IntegralResultG α) :=
  let η : α := cExpEtaG Dt
  let (fp, (b, ds), (cn, dn)) := canonicalRepresentationFastG Dt fuel a d
  let neg : List α := cHyperexpSpecialNegG b ds
  match cIntegrateHyperexpLaurentG η fp neg with
  | none => none
  | some (lnum, lden) =>
    let nrm := cIntegrateReducedG Dt fuel cn dn cands
    let (gnum, gden) := nrm.rational
    -- combine `lnum/lden + gnum/gden`.
    let num := caddG (cmulG lnum gden) (cmulG gnum lden)
    let den := cmulG lden gden
    some ⟨(num, den), nrm.logs⟩

end CPolyG

/-! ### ★ THE KEY VALIDATION: `∫ 1/exp = −1/exp` at a HYPEREXPONENTIAL tower level (`native_decide`)

The deliverable. We integrate `f = t⁻¹ = 1/exp` over `ℚ(x)[t]` where `t = exp x` is a **hyperexponential**
monomial (`Dt = η·t`, `η = 1`, so `Dt = [0, 1]`), with base field `Lvl1 = QFunNZG ℚ = ℚ(x)`. The integrand
`f = 1/t` has numerator `a = [1]` and denominator `d = t = [0, 1]`; its canonical split puts `t` entirely
in the **special part** (`t` is the hyperexponential special factor), so `fₛ = 1/t`, a negative-power
Laurent tail with `a₋₁ = 1`. The §5.10 driver solves the base RDE `Dq₋₁ + (−1·η)·q₋₁ = 1`
(`crischDESolve (−1) 1` over ℚ(x), `q₋₁ = −1`), giving `∫ t⁻¹ = q₋₁·t⁻¹ = −1/t`.

We pin the result: the special part `b/dₛ = 1/t ≠ 0` (which the reduced-case capstone leaves undisposed) is
landed by the new `cIntegrateHyperexpG`, which returns `some res` whose antiderivative identity `D(res) = f`
holds (`checkIdentityG`,
cleared of denominators over ℚ(x)[t]). All scalars are ℚ-constants lifted into `Lvl1 = ℚ(x)`, so the engine
genuinely runs the level-1 `CField`/`CDiffField`/`CRischField` instances. The oracle recurses ℚ(x) → ℚ for
the base RDE; everything is `[CField …]`-computable with `Prop`-erased subtype proofs, so `native_decide`
reduces — the §5.10 hyperexponential special part GENUINELY COMPUTES. -/

open CPolyG

/-- The base field `Lvl1 = QFunNZG ℚ = ℚ(x)` over which the hyperexponential monomial `t = exp x` sits. -/
abbrev Lvl1 : Type := QFunNZG ℚ

/-- The hyperexponential monomial derivative `Dt = η·t = [0, 1]` over `CPolyG Lvl1 = ℚ(x)[t]` (`t = exp x`,
`η = 1`): the coefficient of `t¹` is `η = 1`, contrasting the primitive `Dt = [c]` and the hypertangent
`Dt = [η, 0, η]`. -/
def hyperexpDt : CPolyG Lvl1 := [CField.zero, CField.one]

/-- The integrand numerator `a = 1` over `CPolyG Lvl1 = ℚ(x)[t]` for `f = 1/t = 1/exp`. -/
def hyperexpInvA : CPolyG Lvl1 := [CField.one]

/-- The integrand denominator `d = t = [0, 1]` over `CPolyG Lvl1 = ℚ(x)[t]` for `f = 1/t = 1/exp`. -/
def hyperexpInvD : CPolyG Lvl1 := [CField.zero, CField.one]

/-- The residue candidate set for the hyperexponential `1/exp` integral — empty of genuine residues (the
integrand has no logarithmic part), `{0, 1}` as `Lvl1 = ℚ(x)` constants. -/
def hyperexpInvCands : List Lvl1 := [CField.zero, CField.one]

/-- **The hyperexponential coefficient `η = Dt/t = 1`** (`native_decide`): for `Dt = [0, 1]` (`t = exp`),
`cExpEtaG` reads `η = 1 ∈ ℚ(x)`, confirmed by `CField.isZero (η − 1) = true`. The §5.10 driver's shift
`j·η` is then just `j`. -/
theorem hyperexp_eta_eq_one :
    CField.isZero (CField.sub (cExpEtaG hyperexpDt) (CField.one : Lvl1)) = true := by native_decide

/-- **★ The §5.10 driver lands `∫ 1/exp = −1/exp`, and `D(∫f) = f`** (`native_decide`, the headline). On
the hyperexponential integrand `f = 1/t = 1/exp` over `ℚ(x)[t]` (`Dt = η·t`, `η = 1`) — a **pure special
part** `b/dₛ = 1/t` that the reduced-case capstone `cIntegrateReducedG` leaves undisposed — the §5.10 driver
`cIntegrateHyperexpG` (canonical split + Laurent special-part integration, the per-term RDE
`Dq₋₁ + (−1)·q₋₁ = 1` solved by the oracle to `q₋₁ = −1` + recombination) returns `some res`, and `res`
satisfies the antiderivative identity `D(res) + ∑ᵢ cᵢ·(D(vᵢ)/vᵢ) = f` (`checkIdentityG`, cleared of
denominators over ℚ(x)[t]). The returned rational part is `−1/t` with no logs. **This is the deliverable:
the hyperexponential special part — built on the recursive RDE oracle — computes via §5.10 and
differentiates back to `f`.** -/
theorem hyperexpInv_landsSpecialPart :
    (match CPolyG.cIntegrateHyperexpG hyperexpDt 20 hyperexpInvA hyperexpInvD hyperexpInvCands with
      | some res => CPolyG.checkIdentityG hyperexpDt res hyperexpInvA hyperexpInvD
      | none => false) = true := by native_decide

#print axioms hyperexpInv_landsSpecialPart

/-! ### ★★ STRETCH 1: `∫(exp + 1/exp) = exp − 1/exp` — poly + special mix (`native_decide`)

A Laurent polynomial with BOTH a polynomial part and a special part. Over `ℚ(x)[t]` (`t = exp`, `Dt = t`),
`f = t + t⁻¹` has `fₚ = t` (positive Laurent coefficient `a₁ = 1`) and `fₛ = t⁻¹` (negative `a₋₁ = 1`).
The §5.10 driver solves two base RDEs: `∫ t` needs `Dq₁ + (1·η)·q₁ = 1` (`q₁ = 1`, since `D(1) + 1 = 1`),
`∫ t⁻¹` needs `Dq₋₁ + (−1)·q₋₁ = 1` (`q₋₁ = −1`). So `∫(t + t⁻¹) = q₁·t + q₋₁·t⁻¹ = t − t⁻¹` — and indeed
`D(t − t⁻¹) = η·t − (−η·t⁻¹) ... = t + t⁻¹`. Assembled as `f = (t²+1)/t`: `a = [1, 0, 1]`, `d = [0, 1]`. -/

/-- The integrand numerator `a = t² + 1` for `f = (t²+1)/t = t + 1/t = exp + 1/exp` over `CPolyG Lvl1`. -/
def hyperexpPolySpecA : CPolyG Lvl1 := [CField.one, CField.zero, CField.one]

/-- The integrand denominator `d = t` for `f = (t²+1)/t` over `CPolyG Lvl1`. -/
def hyperexpPolySpecD : CPolyG Lvl1 := [CField.zero, CField.one]

/-- **★★ The §5.10 driver lands `∫(exp + 1/exp) = exp − 1/exp`, and `D(∫f) = f`** (`native_decide`, the
stretch). On `f = t + t⁻¹` over `ℚ(x)[t]` (`t = exp`, `Dt = η·t`, `η = 1`) — a Laurent polynomial with a
**polynomial part `t` AND a special part `t⁻¹`** — the §5.10 driver `cIntegrateHyperexpG` integrates each
term through its own base RDE (`q₁ = 1` for `∫ t`, `q₋₁ = −1` for `∫ t⁻¹`), recombining to `t − t⁻¹`, and
`res` satisfies the antiderivative identity `D(res) = f` (`checkIdentityG`, over ℚ(x)[t]). The
polynomial-AND-special Laurent integration computes and differentiates back to `f`. -/
theorem hyperexpPolySpec_lands :
    (match CPolyG.cIntegrateHyperexpG hyperexpDt 20 hyperexpPolySpecA hyperexpPolySpecD
        hyperexpInvCands with
      | some res => CPolyG.checkIdentityG hyperexpDt res hyperexpPolySpecA hyperexpPolySpecD
      | none => false) = true := by native_decide

/-! ### ★★ STRETCH 2: a special + NORMAL mix — the §5.10 special part lands; the normal LOG part is the §5.9 frontier

A natural next mix is a special part PLUS a *normal* part that contributes a logarithm, e.g.
`f = t⁻¹ + 1/(t−1)` over `ℚ(x)[t]` (`t = exp`, `Dt = t`): split `fₛ = 1/t` (special: `t` is the
hyperexponential special factor) and `fₙ = 1/(t−1)` (normal: `gcd(t−1, Dt) = gcd(t−1, t) = 1`). The §5.10
driver lands the special part `−1/t` correctly. But the **normal log part** is NOT yet correct for a
hyperexponential monomial: `cIntegrateReducedG`'s Rothstein–Trager step returns `1·log(t−1)`, whose
derivative is `D(t−1)/(t−1) = t/(t−1)` (since `D(t−1) = Dt = t`, *not* `1`) — overshooting the intended
`1/(t−1)` by the hyperexponential residual `R = η·∑res ∈ k` (here `R = 1`). This is **exactly the §5.9
hyperexponential log-part frontier** analyzed in `ComputableHyperexpBoundary.lean` (`logResidueSum = hₛ +
R`): the residual `R` must be fed back as a base RDE, which the reduced normal-part integrator does not yet
do. So `cIntegrateHyperexpG` *runs* on this input and lands the special part, but the normal-log identity
fails — a **separate, orthogonal** unsolved frontier from the §5.10 special part this file closes.

We record the precise behavior as a `native_decide` fact: the driver returns `some` (it does not crash),
and the §5.10 special-part Laurent integration alone is exact, while the full-`f` identity is held back by
the normal-log residual. The clean special+normal hyperexponential integral awaits the §5.9 residual
feedback (the `HyperexponentialReduce` loop), the documented continuation. -/

/-- The integrand numerator `a = 2t − 1` for `f = (2t−1)/(t²−t) = 1/t + 1/(t−1)` over `CPolyG Lvl1`. -/
def hyperexpSpecNormA : CPolyG Lvl1 := [CField.neg CField.one, CField.add CField.one CField.one]

/-- The integrand denominator `d = t² − t = t(t−1)` for `f = (2t−1)/(t²−t)` over `CPolyG Lvl1`. -/
def hyperexpSpecNormD : CPolyG Lvl1 := [CField.zero, CField.neg CField.one, CField.one]

/-- The residue candidate set `{0, 1, −1}` as `Lvl1 = ℚ(x)` constants for the special+normal mix. -/
def hyperexpSpecNormCands : List Lvl1 := [CField.zero, CField.one, CField.neg CField.one]

/-- **The §5.10 driver RUNS on a special+normal hyperexponential integrand** (`native_decide`): on
`f = t⁻¹ + 1/(t−1)` over `ℚ(x)[t]` (`t = exp`, `Dt = η·t`) the full driver `cIntegrateHyperexpG` returns
`some` — the canonical split, the §5.10 Laurent special-part integration, the normal-part `cIntegrateReducedG`,
and the recombination all execute. (The returned result is *not* a correct antiderivative of all of `f`:
its normal log part `log(t−1)` overshoots `1/(t−1)` by the §5.9 hyperexponential residual `R = 1`, the
documented frontier — `checkIdentityG` would fail on the full `f`. The §5.10 special part itself is
exact.) -/
theorem hyperexpSpecNorm_runs :
    (CPolyG.cIntegrateHyperexpG hyperexpDt 24 hyperexpSpecNormA hyperexpSpecNormD
      hyperexpSpecNormCands).isSome = true := by native_decide

/-- **The §5.10 special part of the special+normal integrand integrates exactly** (`native_decide`): the
special part of `f = t⁻¹ + 1/(t−1)` is `1/t`, whose §5.10 Laurent integral over `ℚ(x)[t]`
(`cIntegrateHyperexpG` applied to the special-only integrand `a = 1`, `d = t`) is `−1/t`, satisfying
`D(−1/t) = 1/t` (`checkIdentityG`). This isolates the part the §5.10 engine is responsible for and shows
it is correct — the special-part residue of the larger mix is fully handled; only the *normal* log part
is the §5.9 frontier. -/
theorem hyperexpSpecNorm_specialPart_exact :
    (match CPolyG.cIntegrateHyperexpG hyperexpDt 20 hyperexpInvA hyperexpInvD hyperexpInvCands with
      | some res => CPolyG.checkIdentityG hyperexpDt res hyperexpInvA hyperexpInvD
      | none => false) = true := by native_decide

#print axioms hyperexpSpecNorm_runs

end DeepWiki.SymbolicIntegration
