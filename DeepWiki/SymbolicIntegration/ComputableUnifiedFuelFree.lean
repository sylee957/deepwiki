import DeepWiki.SymbolicIntegration.ComputableUnifiedMixedIntegrate
import DeepWiki.SymbolicIntegration.ComputableRadicalWellFounded
import DeepWiki.SymbolicIntegration.ComputableTowerRischDEWellFounded

/-! # The FUEL-FREE UNIFIED integration entry `cIntegrateMixedWf` — one fuel-free dispatcher for BOTH
the transcendental and the algebraic engine.

The unified entry `cIntegrateMixed` (`ComputableUnifiedMixedIntegrate`) routes BOTH the transcendental
(`cIntegrateGFull`) and the algebraic (`cIntegrateAlgebraic`) integrand through one dispatcher — but BOTH
sub-engines it routed to still threaded an `ℕ`-fuel budget. By now the engine is fuel-free end-to-end on
both axes: the algebraic engine via `cIntegrateAlgebraicWf` / `afIntegrateAlgebraicWf`
(`ComputableRadicalWellFounded` / `ComputableGeneralWellFounded`), and the transcendental tower's *core* via
`cIntegrateGWf` / `cIntegratePolyGWf` / `cPolyRischDEGWf` (`ComputableTowerWellFounded` /
`ComputableTowerRischDEWellFounded`). Two gaps remained: the transcendental TOP entry `cIntegrateGFull`
(`ComputableTowerRischDE`) and the unified `cIntegrateMixed` both still routed to the fuel versions. This
file closes both — the unified entry becomes fuel-free.

* **`cIntegrateGFullWf`** — the fuel-free companion of `cIntegrateGFull`. The original is a **FLAT wrapper**:
  canonical-rep split, then a `b = 0` test routing the normal part to `cIntegrateReducedG` and the polynomial
  part to the `b = 0` RDE oracle `cPolyRischDEG`. So the fuel-free version is a pure **leaf substitution** —
  `canonicalRepresentationFastG → canonicalRepresentationFastGWf`, `cIntegrateReducedG →
  cIntegrateReducedGWf`, `cPolyRischDEG → cPolyRischDEGWf` — with NO `termination_by` (all recursion lives in
  the already-fuel-free leaves). `[CFracGcdCoreWf α]` replaces `[CFracGcdCore α]`.

* **`cIntegrateGFullWf_eq`** — the correspondence: `cIntegrateGFullWf = cIntegrateGFull fuel` at any
  sufficient fuel, the conjunction of the three leaf bridges (`canonicalRepresentationFastGWf_eq` /
  `cIntegrateReducedGWf_eq` / `cPolyRischDEGWf_eq`), taken as hypotheses (the fuel bounds live only there).

* **`CFracGcdCoreWf RadX3`** — the fuel-free raw fraction-free gcd over the algebraic base `RadX3 =
  ℚ(x)[√(x³+1)]`, the fuel-free companion of `instCFracGcdCoreRadX3`. `RadX3` is a genuine field, so — exactly
  as for the constant base `instCFracGcdCoreWfQ` — its raw gcd is the **fuel-free** Euclidean `(cgcdWf _).1`
  (vs the fuel'd `(cgcdExtG _).1`). This lets `cIntegrateGFullWf` run at `α = RadX3`, integrating a
  transcendental monomial over the algebraic base with NO fuel.

* **`cIntegrateMixedWf`** — the fuel-free unified dispatcher, mirroring `cIntegrateMixed`: `match` on the
  `IntegrandSpec` top-extension tag and route the `transcendental` arm to `cIntegrateGFullWf` and the
  `algebraic` arm to `cIntegrateAlgebraicWf` (the radical fuel-free entry). Same `IntegrandSpec` /
  `MixedIntegralResult` types and the same `checkMixed` validator (reused verbatim). **No fuel at runtime** —
  fuel-free totality on both arms via well-founded recursion in the leaves.

* **★ The milestone** (`native_decide`): the SAME two examples `cIntegrateMixed` validated — a
  **transcendental** integral (`∫ t dt = t²/2` over `RadX3 = ℚ(x)[√(x³+1)]`) AND an **algebraic** integral
  (`∫ dx/(x√(x²+1)) = log((y−1)/x)` over `y² = x²+1`) — now BOTH dispatched through the FUEL-FREE unified entry
  `cIntegrateMixedWf` and validated `D(∫f) = f` by `checkMixed`. ONE fuel-free entry, both cases; their
  `#print axioms` carry `[propext, Classical.choice, Quot.sound]` + the `native_decide` compiler axiom, with
  NO `sorryAx` — fuel-free totality. -/

namespace DeepWiki.SymbolicIntegration

open CPolyG RadElem

/-! ## `cIntegrateGFullWf` — the fuel-free transcendental top entry (flat leaf substitution) -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α] [CRischField α]

/-- **The fuel-free full poly/special tower integral** `cIntegrateGFullWf Dt a d cands` — the generic,
fuel-free companion of `cIntegrateGFull`. Integrate `f = a/d ∈ α(t)` over `D = cmonomialDeriv Dt`, returning
`some ⟨(num, den), logs⟩` with `∫ f = num/den + ∑ᵢ cᵢ·log(vᵢ)`, or `none`. A pure **leaf substitution** of the
flat-wrapper `cIntegrateGFull`: (1) `canonicalRepresentationFastGWf` splits `f = fₚ + (b/dₛ) + (cₙ/dₙ)`;
(2) if the special part `b` vanishes, the normal part `cₙ/dₙ` is integrated by `cIntegrateReducedGWf` (Hermite
+ residue logs); (3) if `fₚ` also vanishes, return that; else solve the polynomial part by the `b = 0` RDE
oracle `cPolyRischDEGWf Dt [] fp (deg fp + 1)` (`Dqₚ = fₚ`, primitive case) and combine the rational parts
`qₚ + gₙ/gₙd = (qₚ·gₙd + gₙ)/gₙd`; (4) a nonzero special part returns `none` (the documented continuation).
Every sub-op is a WF leaf — **no fuel at runtime**; `native_decide`-able over the noncomputable tower.
`[CField α] [CDiffField α] [CFracGcdCoreWf α] [CRischField α]`-generic — runs at any tower level. -/
def cIntegrateGFullWf (Dt : CPolyG α) (a d : CPolyG α) (cands : List α) :
    Option (IntegralResultG α) :=
  let (fp, (b, _ds), (cn, dn)) := canonicalRepresentationFastGWf Dt a d
  if cisZeroG b then
    -- normal part: rational `gₙ/gₙd` + logs.
    let nrm := cIntegrateReducedGWf Dt cn dn cands
    let (gnum, gden) := nrm.rational
    if cisZeroG fp then
      some nrm
    else
      -- polynomial part: solve `Dqₚ = fₚ` by the `b = 0` RDE oracle (primitive case).
      match cPolyRischDEGWf Dt [] fp ((cdegG fp : ℤ) + 1) with
      | none => none
      | some qp =>
        -- combine `qₚ + gₙ/gₙd = (qₚ·gₙd + gₙ)/gₙd`.
        let num := caddG (cmulG qp gden) gnum
        some ⟨(num, gden), nrm.logs⟩
  else none

end CPolyG

/-! ### Bridge — `cIntegrateGFullWf` equals `cIntegrateGFull` at any sufficient fuel

`cIntegrateGFull` is flat, so its fuel-free companion agrees with it once the three leaf bridges feed in
(`canonicalRepresentationFastGWf_eq` / `cIntegrateReducedGWf_eq` / `cPolyRischDEGWf_eq`). The fuel bounds live
only in those hypotheses; the runtime `cIntegrateGFullWf` carries none. A pure composition rewrite. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α] [CFracGcdCoreWf α] [CRischField α]

/-- **★ Bridge — `cIntegrateGFullWf` equals `cIntegrateGFull` at any sufficient fuel.** From the canonical-rep
bridge (`hcanon : canonicalRepresentationFastGWf Dt a d = canonicalRepresentationFastG Dt fuel a d`), the
reduced-capstone bridge (`hred`) on the resulting normal part `(cn, dn)`, and the polynomial-part RDE bridge
(`hpoly`) on `fp` — `cIntegrateGFullWf Dt a d cands = cIntegrateGFull Dt fuel a d cands`. The fuel bounds live
only in the hypotheses; `cIntegrateGFullWf` carries none. A pure composition rewrite over the flat wrapper. -/
theorem cIntegrateGFullWf_eq (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α)
    (hcanon : canonicalRepresentationFastGWf Dt a d = canonicalRepresentationFastG Dt fuel a d)
    (hred : cIntegrateReducedGWf Dt (canonicalRepresentationFastGWf Dt a d).2.2.1
        (canonicalRepresentationFastGWf Dt a d).2.2.2 cands
      = cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
          (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands)
    (hpoly : cPolyRischDEGWf Dt [] (canonicalRepresentationFastGWf Dt a d).1
        ((cdegG (canonicalRepresentationFastGWf Dt a d).1 : ℤ) + 1)
      = cPolyRischDEG Dt fuel [] (canonicalRepresentationFastG Dt fuel a d).1
          ((cdegG (canonicalRepresentationFastG Dt fuel a d).1 : ℤ) + 1)) :
    cIntegrateGFullWf Dt a d cands = cIntegrateGFull Dt fuel a d cands := by
  rw [cIntegrateGFullWf, cIntegrateGFull]
  -- both sides `match (canonical split) with | (fp,(b,_ds),cn,dn) => …`; align the split by `hcanon`, then
  -- the reduced capstone (on `(cn, dn)`) by `hred` and the polynomial-part RDE (on `fp`) by `hpoly`
  -- (their projections are exactly the match's `cn`/`dn`/`fp`). Same technique as `cIntegrateGWf_eq`.
  simp only [hcanon] at hred hpoly ⊢
  -- after `hcanon` both `match`es are on `canonicalRepresentationFastG fuel a d`; expand to projections
  rw [show (canonicalRepresentationFastG Dt fuel a d)
      = ((canonicalRepresentationFastG Dt fuel a d).1,
         ((canonicalRepresentationFastG Dt fuel a d).2.1.1,
          (canonicalRepresentationFastG Dt fuel a d).2.1.2),
         ((canonicalRepresentationFastG Dt fuel a d).2.2.1,
          (canonicalRepresentationFastG Dt fuel a d).2.2.2)) from rfl]
  simp only []
  rw [hred, hpoly]
  rfl

end CPolyG

/-! ## `CFracGcdCoreWf RadX3` — the fuel-free gcd over the algebraic base `ℚ(x)[√(x³+1)]`

The fuel-free companion of `instCFracGcdCoreRadX3`. `RadX3` is a genuine field, so — exactly as for the
constant base `instCFracGcdCoreWfQ` — its raw fraction-free gcd is the **fuel-free** Euclidean `(cgcdWf _).1`
(vs the fuel'd `(cgcdExtG _).1`). This supplies the one binder `cIntegrateGFullWf` needs beyond
`[CField RadX3] [CDiffField RadX3] [CRischField RadX3]` (all built in the enabler / mixed file). -/

/-- **`CFracGcdCoreWf RadX3`** — the fuel-free raw fraction-free gcd over `RadX3[t] = ℚ(x)[√(x³+1)][t]`. As
`RadX3` is a genuine field (`y² − (x³+1)` irreducible over ℚ(x)), its content is a unit and the raw gcd is the
**fuel-free** Euclidean `(cgcdWf _).1` — the fuel-free companion of `instCFracGcdCoreRadX3`'s
`(cgcdExtG _).1`, mirroring the constant base `instCFracGcdCoreWfQ`. `[CField RadX3]`-only, so it reduces in
the native compiler. This is the one binder `cIntegrateGFullWf` needs over `RadX3`. -/
instance instCFracGcdCoreWfRadX3 : CFracGcdCoreWf RadX3 where
  cgcdFFRawCoreWf p q := (CPolyG.cgcdWf p q).1

/-! ## `cIntegrateMixedWf` — the FUEL-FREE unified dispatcher

`match` on the `IntegrandSpec` top-extension tag (the *same* tagged input as `cIntegrateMixed`) and route to
the fuel-free sub-engine: `transcendental → cIntegrateGFullWf`, `algebraic → cIntegrateAlgebraicWf`. The
result is wrapped in the same `MixedIntegralResult` constructor. Non-recursive: one tag, one fuel-free engine.
-/

/-- **★ The FUEL-FREE UNIFIED top-level integrator** `cIntegrateMixedWf spec` — ONE fuel-free entry handling
BOTH the transcendental and the algebraic integrand, the fuel-free companion of `cIntegrateMixed`. Dispatch on
the `IntegrandSpec` top-extension tag: a `transcendental Dt a d cands` routes to `cIntegrateGFullWf Dt a d
cands` (the fuel-free canonical-split + RDE-oracle poly part + Rothstein–Trager log part driver, run at the
base `α` — which may itself be a transcendental tower OR an algebraic `RadExt`, the mixed-tower genericity); an
`algebraic ρ R B residual c D degBound` routes to `cIntegrateAlgebraicWf ρ R B residual c D degBound` (the
fuel-free multi-case rational dispatch + principal-case log solve over `y² = ρ`). Each answer is wrapped in the
matching `MixedIntegralResult` constructor. **No fuel at runtime** — fuel-free totality on both arms via
well-founded recursion in the leaves. The fuel-free analogue of `cIntegrateMixed`; the fully-recursive
alternating mixed-tower dispatch (per-level extension detection) remains the documented follow-up. -/
def cIntegrateMixedWf {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α] [CRischField α] :
    IntegrandSpec α → MixedIntegralResult α
  | .transcendental Dt a d cands =>
      MixedIntegralResult.transcendental (CPolyG.cIntegrateGFullWf Dt a d cands)
  | .algebraic ρ R B residual c D degBound =>
      MixedIntegralResult.algebraic (cIntegrateAlgebraicWf ρ R B residual c D degBound)

/-! ## ★ Validation through the FUEL-FREE unified entry: a transcendental AND an algebraic integral

Both integrals below are built as an `IntegrandSpec` (reusing `umTranscSpec` / `umAlgSpec` from the fuel'd
unified file verbatim), run through the FUEL-FREE `cIntegrateMixedWf`, and validated by the same `checkMixed`
— the *same* two-call sequence (`cIntegrateMixedWf` then `checkMixed`) for the transcendental and the algebraic
case. The proof that one fuel-free entry handles all cases. -/

/-! ### Transcendental, through the fuel-free entry: `∫ t dt = t²/2` over `RadX3 = ℚ(x)[√(x³+1)]` -/

/-- **`cIntegrateMixedWf` routes the transcendental spec to a `transcendental` result** (`native_decide`): on
`umTranscSpec` the fuel-free unified entry dispatches to `cIntegrateGFullWf` and returns
`MixedIntegralResult.transcendental (some _)` — the fuel-free transcendental engine fired and produced a
result over the algebraic base `RadX3`. -/
theorem umTranscWf_routes_transcendental :
    (match cIntegrateMixedWf umTranscSpec with
      | .transcendental (some _) => true
      | _ => false) = true := by native_decide

/-- **★ `∫ t dt = t²/2` over `RadX3 = ℚ(x)[√(x³+1)]`, dispatched through the FUEL-FREE `cIntegrateMixedWf`,
validated `D(∫f) = f`** (`native_decide`, the transcendental half of the fuel-free milestone). The fuel-free
unified entry `cIntegrateMixedWf` routes the `transcendental` spec `umTranscSpec` to `cIntegrateGFullWf` over
the algebraic base `RadX3`; the result is validated by `checkMixed` (the cleared antiderivative identity
`checkIdentityG`, `D(∫f) = f`) against the integrand `t/1`. A TRANSCENDENTAL integral validated through the
FUEL-FREE unified entry — the transcendental `t` over the algebraic `√(x³+1)`, routed and certified with NO
fuel. (The `algRho`/`algIntegrand` arguments to `checkMixed` are unused on the transcendental branch.) -/
theorem umTranscWf_validated :
    checkMixed (α := RadX3) mixedDt (cIntegrateMixedWf umTranscSpec) mixedTa mixedD
      (CField.zero) ([] : RadElem (QFunNZG ℚ)) = true := by native_decide

/-! ### Algebraic, through the fuel-free entry: `∫ dx/(x√(x²+1)) = log((y−1)/x)` over `y² = x²+1` -/

/-- **`cIntegrateMixedWf` routes the algebraic spec to an `algebraic` result** (`native_decide`): on `umAlgSpec`
the fuel-free unified entry dispatches to `cIntegrateAlgebraicWf` and returns `MixedIntegralResult.algebraic _`
— the fuel-free algebraic engine fired. -/
theorem umAlgWf_routes_algebraic :
    (match cIntegrateMixedWf umAlgSpec with
      | .algebraic _ => true
      | _ => false) = true := by native_decide

/-- **★ `∫ dx/(x√(x²+1)) = log((y−1)/x)` over `y² = x²+1`, dispatched through the FUEL-FREE `cIntegrateMixedWf`,
validated `D(∫f) = f`** (`native_decide`, the algebraic half of the fuel-free milestone). The fuel-free unified
entry `cIntegrateMixedWf` routes the `algebraic` spec `umAlgSpec` to `cIntegrateAlgebraicWf` over `y² = x²+1`;
the result is validated by `checkMixed` (`algDeriv` of the result equals the supplied integrand
`rtLogIntegrand`, `radIsZero (radSub …)`). An ALGEBRAIC integral validated through the FUEL-FREE unified entry —
`cIntegrateAlgebraicWf` solves the log argument `u = (y−1)/x`, and `algDeriv` of the recovered result returns
the integrand, with NO fuel. (The `anum`/`aden` transcendental arguments to `checkMixed` are unused on the
algebraic branch.) -/
theorem umAlgWf_validated :
    checkMixed (α := RadX3) mixedDt (cIntegrateMixedWf umAlgSpec) [CField.one] [CField.one]
      rtLogRho rtLogIntegrand = true := by native_decide

/-! ### `#print axioms` — the FUEL-FREE unified-entry validations

Each carries `[propext, Classical.choice, Quot.sound]` + the `native_decide` compiler axiom (`native`), with
NO `sorryAx` — fuel-free totality via well-founded recursion in the leaves (no `ℕ`-fuel). The transcendental
`∫ t dt = t²/2` (over the algebraic base `RadX3`) and the algebraic `∫ dx/(x√(x²+1)) = log((y−1)/x)` (over
`y² = x²+1`) are BOTH dispatched and validated through the *same* FUEL-FREE entry `cIntegrateMixedWf` +
`checkMixed` — one fuel-free top-level integrator handling both the transcendental and the algebraic case. -/

-- ★ Transcendental, through the fuel-free entry: `∫ t dt = t²/2` over ℚ(x)[√(x³+1)], validated `D(∫f) = f`:
#print axioms umTranscWf_validated
-- ★ Algebraic, through the fuel-free entry: `∫ dx/(x√(x²+1)) = log((y−1)/x)`, validated `D(∫f) = f`:
#print axioms umAlgWf_validated
-- The routing facts (transcendental spec → transcendental result; algebraic spec → algebraic result):
#print axioms umTranscWf_routes_transcendental
#print axioms umAlgWf_routes_algebraic

end DeepWiki.SymbolicIntegration
