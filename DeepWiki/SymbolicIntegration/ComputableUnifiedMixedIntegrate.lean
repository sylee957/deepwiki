import DeepWiki.SymbolicIntegration.ComputableMixedTowerIntegrate
import DeepWiki.SymbolicIntegration.ComputableRadicalIntegrateFull

/-! # The UNIFIED top-level integration entry `cIntegrateMixed` — one dispatcher for BOTH the
transcendental and the algebraic engine.

The engine integrates over mixed towers in **both** directions: transcendental-over-algebraic
(`cIntegrateGFull` run over the radical base `RadX3 = ℚ(x)[√(x³+1)]`, validated in
`ComputableMixedTowerIntegrate`) and algebraic-over-transcendental (`cIntegrateAlgebraic`,
`ComputableRadicalIntegrateFull`). But the **entry points were separate** — a caller had to know
in advance whether the integrand's top extension is transcendental or algebraic and reach for
`cIntegrateGFull` vs `cIntegrateAlgebraic`. This file unifies them behind ONE dispatcher.

* **`IntegrandSpec α`** — a tagged input describing the integrand by the *kind of its top extension*:
  - `transcendental Dt a d cands` — the data `cIntegrateGFull` needs (a primitive/hyperexp/tangent
    monomial `Dt`, the integrand `a/d ∈ α(t)`, the residue candidates), **generic over the base `α`**.
    Because `α` is free, this is `α = ℚ`, a transcendental tower, OR a `RadExt` algebraic base — exactly
    the mixed-tower genericity that lets a transcendental `t` stack on an algebraic `√(x³+1)`.
  - `algebraic ρ R B residual c D degBound` — the data `cIntegrateAlgebraic` needs over `y² = ρ`
    (rational data `(R, B)`, the residual integrand, the residue coefficient `c`, the log-solve
    denominator `D`, the ansatz degree). The algebraic engine is fixed at base `ℚ(x) = QFunNZG ℚ`.

* **`MixedIntegralResult α`** — the unified output: a SUM of the two engines' results,
  `transcendental (Option (IntegralResultG α))` | `algebraic AlgIntegralResult`. One result type so a
  caller can hold the answer of either route uniformly.

* **`cIntegrateMixed fuel`** — `match` on the `IntegrandSpec` and route to `cIntegrateGFull` (transcendental)
  or `cIntegrateAlgebraic` (algebraic), wrapping the answer in the corresponding `MixedIntegralResult`
  constructor. **Non-recursive**: the dispatch picks one engine by the top-extension tag; fuel flows only
  through the sub-engine. (The fully-recursive alternating mixed-tower dispatch — detecting the extension
  kind *per level* and peeling the tower one extension at a time — is the documented follow-up.)

* **`checkMixed`** — the matching validator, dispatching on the *result*: a transcendental result is checked
  by the cleared antiderivative identity `D(∫f) = f` (`checkIdentityG`) against the transcendental integrand;
  an algebraic result by `algDeriv` against the supplied algebraic integrand (`radIsZero (radSub …)`). So a
  single `checkMixed (cIntegrateMixed …)` validates BOTH routes through one call.

* **★ The milestone** (`native_decide`): a **transcendental** integral (`∫ t dt = t²/2` over the algebraic
  base `RadX3 = ℚ(x)[√(x³+1)]`, the `transcendental` tag) AND an **algebraic** integral
  (`∫ dx/(x√(x²+1)) = log((y−1)/x)` over `y² = x²+1`, the `algebraic` tag), **both dispatched through the
  SAME entry `cIntegrateMixed`**, each validated `D(∫f) = f`. The proof that one entry handles all cases.

**Follow-up** (documented here, not yet built): (1) the fully-recursive **alternating mixed-tower** dispatch
— per-level top-extension detection peeling `ℚ(x)(t₁)[√…][t₂]…` one extension at a time, rather than a single
top-tag switch; (2) the **fuel-free** version of the algebraic path (a sibling subagent is replacing
`cIntegrateAlgebraic`'s fuel with well-founded recursion in `ComputableRadicalWellFounded.lean`). The
transcendental path here threads `fuel` into `cIntegrateGFull` unchanged. -/

namespace DeepWiki.SymbolicIntegration

open CPolyG RadElem

/-! ### The tagged input `IntegrandSpec` and unified result `MixedIntegralResult` -/

/-- **The unified integrand specification** — a tagged input naming the integrand by the *kind of its top
tower extension*, so the top-level integrator can dispatch on it. `transcendental` carries what
`cIntegrateGFull` needs over the generic base `α` (the monomial derivative `Dt`, the integrand `a/d ∈ α(t)`,
the residue candidates `cands`); `algebraic` carries what `cIntegrateAlgebraic` needs over `y² = ρ` (the
rational data `R/B`, the residual integrand, the residue coefficient `c`, the log-solve denominator `D`, the
ansatz degree). Generic over `α`: the `transcendental` arm works whether `α = ℚ`, a transcendental tower, or a
`RadExt` algebraic base (the mixed-tower genericity); the `algebraic` arm is fixed at `ℚ(x) = QFunNZG ℚ`. -/
inductive IntegrandSpec (α : Type*) [CField α] where
  /-- A **transcendental** top extension: integrate `a/d ∈ α(t)` over `D = cmonomialDeriv Dt` (primitive,
  hyperexponential, or hypertangent) with residue candidates `cands` — the input of `cIntegrateGFull`. -/
  | transcendental (Dt a d : CPolyG α) (cands : List α)
  /-- An **algebraic** top extension `y² = ρ` over `ℚ(x)`: integrate `R/(B·y)` plus a `residual` log part,
  with residue coefficient `c`, log-solve denominator `D`, ansatz degree `degBound` — the input of
  `cIntegrateAlgebraic`. -/
  | algebraic (ρ : QFunNZG ℚ) (R B : CPolyG ℚ) (residual : RadElem (QFunNZG ℚ))
      (c : QFunNZG ℚ) (D : CPolyG ℚ) (degBound : ℕ)

/-- **The unified integral result** — a sum of the two engines' result types, so one value can hold the
answer of either route. `transcendental` wraps `cIntegrateGFull`'s `Option (IntegralResultG α)` (the
`α(t)` rational part `+ ∑ cᵢ·log vᵢ`, or `none`); `algebraic` wraps `cIntegrateAlgebraic`'s
`AlgIntegralResult` (the radical-extension rational part `v + ∑ cᵢ·log uᵢ`). The common shape `cIntegrateMixed`
returns. -/
inductive MixedIntegralResult (α : Type*) [CField α] where
  /-- The result of the **transcendental** route: `cIntegrateGFull`'s `Option (IntegralResultG α)`. -/
  | transcendental (res : Option (IntegralResultG α))
  /-- The result of the **algebraic** route: `cIntegrateAlgebraic`'s `AlgIntegralResult`. -/
  | algebraic (res : AlgIntegralResult)

/-! ### `cIntegrateMixed` — the single dispatcher

`match` on the top-extension tag and route to the right sub-engine. Non-recursive: one tag, one engine; fuel
flows only through the sub-engine. -/

/-- **★ The UNIFIED top-level integrator** `cIntegrateMixed fuel spec` — ONE entry handling BOTH the
transcendental and the algebraic integrand. Dispatch on the `IntegrandSpec` top-extension tag: a
`transcendental Dt a d cands` routes to `cIntegrateGFull Dt fuel a d cands` (the canonical-split + RDE-oracle
poly part + Rothstein–Trager log part driver, run at the base `α` — which may itself be a transcendental tower
OR an algebraic `RadExt`, the mixed-tower genericity); an `algebraic ρ R B residual c D degBound` routes to
`cIntegrateAlgebraic fuel ρ R B residual c D degBound` (the multi-case rational dispatch + principal-case log
solve over `y² = ρ`). Each answer is wrapped in the matching `MixedIntegralResult` constructor. **Non-recursive**
— the dispatch is a single top-tag switch (fuel only via the sub-engine); the fully-recursive alternating
mixed-tower dispatch (per-level extension detection) is the documented follow-up. -/
def cIntegrateMixed {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α] [CRischField α]
    (fuel : ℕ) : IntegrandSpec α → MixedIntegralResult α
  | .transcendental Dt a d cands =>
      MixedIntegralResult.transcendental (CPolyG.cIntegrateGFull Dt fuel a d cands)
  | .algebraic ρ R B residual c D degBound =>
      MixedIntegralResult.algebraic (cIntegrateAlgebraic fuel ρ R B residual c D degBound)

/-! ### `checkMixed` — the matching validator

Dispatch on the *result* (and the original integrand) to apply the right `D(∫f) = f` certificate: the cleared
identity `checkIdentityG` for a transcendental result, `algDeriv`-against-integrand for an algebraic one. So
one `checkMixed (cIntegrateMixed …)` validates either route. -/

/-- **Validate a unified result against its integrand** `checkMixed Dt result anum aden algRho algIntegrand` —
`true` iff `result` is a genuine antiderivative. A `transcendental res` is checked by the cleared antiderivative
identity `checkIdentityG Dt · anum aden` (`D(∫f) = f` over `α(t)`); a `none` transcendental result is `false`.
An `algebraic res` is checked by `radIsZero (radSub (algDeriv algRho res) algIntegrand)` (the radical-extension
derivative of `res` equals the supplied integrand over `y² = algRho`). The transcendental certificate uses the
transcendental integrand `anum/aden`; the algebraic certificate uses `algRho`/`algIntegrand`. So a single call
validates whichever route fired. -/
def checkMixed {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α]
    (Dt : CPolyG α) (result : MixedIntegralResult α) (anum aden : CPolyG α)
    (algRho : QFunNZG ℚ) (algIntegrand : RadElem (QFunNZG ℚ)) : Bool :=
  match result with
  | .transcendental res =>
      match res with
      | some r => CPolyG.checkIdentityG Dt r anum aden
      | none => false
  | .algebraic res =>
      radIsZero (radSub (algDeriv algRho res) algIntegrand)

/-! ### ★ Validation through the UNIFIED entry: a transcendental AND an algebraic integral, one dispatcher

Both integrals below are built as an `IntegrandSpec`, run through `cIntegrateMixed`, and validated by
`checkMixed` — the *same* two-call sequence (`cIntegrateMixed` then `checkMixed`) for the transcendental and
the algebraic case. The proof that one entry handles all cases. -/

/-! #### Transcendental case: `∫ t dt = t²/2` over `RadX3 = ℚ(x)[√(x³+1)]`, via `cIntegrateMixed`

The transcendental `transcendental` tag, run over the **algebraic** base `RadX3` (the transcendental-over-
algebraic mixed tower of `ComputableMixedTowerIntegrate`). The integrand data `mixedDt`, `mixedTa`, `mixedD`,
`mixedCands` are reused verbatim — the same `∫ t dt = t²/2` validated directly there, here routed through the
unified entry. -/

/-- **The transcendental integrand `∫ t dt` as an `IntegrandSpec`** over `RadX3 = ℚ(x)[√(x³+1)]` — the
`transcendental` tag carrying `Dt = mixedDt` (`t` primitive, `Dt = 1`), integrand `t/1` (`mixedTa`/`mixedD`),
residue candidates `mixedCands`. The top extension is the transcendental `t`; its base is the algebraic
`√(x³+1)`. -/
def umTranscSpec : IntegrandSpec RadX3 :=
  .transcendental mixedDt mixedTa mixedD mixedCands

/-- **`cIntegrateMixed` routes the transcendental spec to a `transcendental` result** (`native_decide`): on
`umTranscSpec` the unified entry dispatches to `cIntegrateGFull` and returns
`MixedIntegralResult.transcendental (some _)` — the transcendental engine fired and produced a result. Checked
by the result being the `transcendental (some …)` shape. -/
theorem umTransc_routes_transcendental :
    (match cIntegrateMixed 20 umTranscSpec with
      | .transcendental (some _) => true
      | _ => false) = true := by native_decide

/-- **★ `∫ t dt = t²/2` over `RadX3 = ℚ(x)[√(x³+1)]`, dispatched through `cIntegrateMixed`, validated
`D(∫f) = f`** (`native_decide`, the transcendental half of the milestone). The unified entry `cIntegrateMixed`
routes the `transcendental` spec `umTranscSpec` to `cIntegrateGFull` over the algebraic base `RadX3`; the
result is validated by `checkMixed` (the cleared antiderivative identity `checkIdentityG`, `D(∫f) = f`) against
the integrand `t/1`. A TRANSCENDENTAL integral validated through the unified entry — the transcendental `t` over
the algebraic `√(x³+1)`, routed and certified via the single `cIntegrateMixed`/`checkMixed` pair. (The
`algRho`/`algIntegrand` arguments to `checkMixed` are unused on the transcendental branch; `radX3radicand`
constants stand in.) -/
theorem umTransc_validated :
    checkMixed (α := RadX3) mixedDt (cIntegrateMixed 20 umTranscSpec) mixedTa mixedD
      (CField.zero) ([] : RadElem (QFunNZG ℚ)) = true := by native_decide

/-! #### Algebraic case: `∫ dx/(x√(x²+1)) = log((y−1)/x)` over `y² = x²+1`, via `cIntegrateMixed`

The `algebraic` tag, over `y² = x²+1` (the log-only round-trip of `ComputableRadicalIntegrateFull`). The data
`rtLogRho`, `rtLogIntegrand`, `rtLogD` are reused verbatim — the same `∫ dx/(x√(x²+1)) = log((y−1)/x)` validated
directly there, here routed through the unified entry. The integrand is reconstructed from `R = 1`, `B = 1`,
the residual = the integrand, residue `c = 1`, `D = x`, degree `0`. -/

/-- **The algebraic integrand `∫ dx/(x√(x²+1))` as an `IntegrandSpec`** over `y² = x²+1` (`rtLogRho`) — the
`algebraic` tag carrying rational data `R = 1`, `B = 1` (empty rational part), the residual = the lifted
integrand `[0, 1/(x·(x²+1))]` (`rtLogIntegrand`), residue coefficient `c = 1`, log-solve denominator `D = x`
(`rtLogD`), ansatz degree `0`. The top extension is the algebraic `√(x²+1)`; its base is `ℚ(x)`. -/
def umAlgSpec : IntegrandSpec RadX3 :=
  .algebraic rtLogRho [1] [1] rtLogIntegrand CField.one rtLogD 0

/-- **`cIntegrateMixed` routes the algebraic spec to an `algebraic` result** (`native_decide`): on `umAlgSpec`
the unified entry dispatches to `cIntegrateAlgebraic` and returns `MixedIntegralResult.algebraic _` — the
algebraic engine fired. Checked by the result being the `algebraic …` shape. -/
theorem umAlg_routes_algebraic :
    (match cIntegrateMixed 12 umAlgSpec with
      | .algebraic _ => true
      | _ => false) = true := by native_decide

/-- **★ `∫ dx/(x√(x²+1)) = log((y−1)/x)` over `y² = x²+1`, dispatched through `cIntegrateMixed`, validated
`D(∫f) = f`** (`native_decide`, the algebraic half of the milestone). The unified entry `cIntegrateMixed`
routes the `algebraic` spec `umAlgSpec` to `cIntegrateAlgebraic` over `y² = x²+1`; the result is validated by
`checkMixed` (`algDeriv` of the result equals the supplied integrand `rtLogIntegrand`, `radIsZero (radSub …)`).
An ALGEBRAIC integral validated through the unified entry — `cIntegrateAlgebraic` solves the log argument
`u = (y−1)/x`, and `algDeriv` of the recovered result returns the integrand. (The `anum`/`aden` transcendental
arguments to `checkMixed` are unused on the algebraic branch; the trivial `[1]`/`[1]` stand in.) -/
theorem umAlg_validated :
    checkMixed (α := RadX3) mixedDt (cIntegrateMixed 12 umAlgSpec) [CField.one] [CField.one]
      rtLogRho rtLogIntegrand = true := by native_decide

/-! ### `#print axioms` — the unified-entry validations

Each carries `[propext, Classical.choice, Quot.sound]` + the `native_decide` compiler axiom (`native`), with
NO `sorry`. The transcendental `∫ t dt = t²/2` (over the algebraic base `RadX3`) and the algebraic
`∫ dx/(x√(x²+1)) = log((y−1)/x)` (over `y² = x²+1`) are BOTH dispatched and validated through the *same* entry
`cIntegrateMixed` + `checkMixed` — one top-level integrator handling both the transcendental and the algebraic
case. -/

-- ★ Transcendental, through the unified entry: `∫ t dt = t²/2` over ℚ(x)[√(x³+1)], validated `D(∫f) = f`:
#print axioms umTransc_validated
-- ★ Algebraic, through the unified entry: `∫ dx/(x√(x²+1)) = log((y−1)/x)`, validated `D(∫f) = f`:
#print axioms umAlg_validated
-- The routing facts (transcendental spec → transcendental result; algebraic spec → algebraic result):
#print axioms umTransc_routes_transcendental
#print axioms umAlg_routes_algebraic

end DeepWiki.SymbolicIntegration
