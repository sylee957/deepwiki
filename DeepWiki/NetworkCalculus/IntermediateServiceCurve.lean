import DeepWiki.NetworkCalculus.ServiceCurveStrictTandem
import DeepWiki.NetworkCalculus.ServiceCurveStrictTandemDilution
import DeepWiki.NetworkCalculus.ServiceCurveStrictMinimal
import DeepWiki.NetworkCalculus.ConvexPWLNormalForm
import DeepWiki.NetworkCalculus.ConvolutionContinuity

/-! # No good intermediate type of service curve (the upper half, and the rate case)

The book asks (Theorem 9.7, §9.3.1) whether some service-curve type sits *strictly*
between strict (`S_strict`) and min-plus (`S_mp`): for each convex piecewise-linear
`β` one associates a system `Ŝ(β)` of strict-service servers with
`S_strict(β) ⊆ Ŝ(β) ⊆ S_mp(β)`, and *if* the systems compose
(`Ŝ(β₂) ∘ Ŝ(β₁) ⊆ Ŝ(β₁ ∗ β₂)`) then `S̄(Ŝ(β)) = S_mp(β)` — there is no intermediate
type. The book proves only the pure-delay base case (Lemma 9.5, the delay dilution
`S̄(⋃ₙ (S_strict(δ_{T/n}))ⁿ) = S_mp(δ_T)`, formalized in `ServiceCurveStrictTandem`);
the general convex-PWL construction and the composition hypothesis are left open.

This file delivers the parts that are *unconditionally* true:

* **The upper inclusion `S̄(S) ⊆ S_mp(β)` (general).** Whenever a system `S` is min-plus
  served by `β` and the served output `A ∗ β` is itself a (left-continuous) curve, the
  whole system closure stays min-plus served by `β`. This is the easy, always-true half
  of the sandwich, and it factors the delay-specific `systemClosure_delayTandemUnion_le`
  through one general lemma.

* **The complete sandwich for a constant rate `λ_R` (the next case after `δ_T`).**
  A single strict rate server is already a one-server system, so
  `S_strict(λ_R) ⊆ S̄(S_strict(λ_R)) ⊆ S_mp(λ_R)` with no dilution needed — and the
  closure collapses, `S̄(S_strict(λ_R)) = S_mp(λ_R)` *fails to require* the composition
  hypothesis. This extends the dilution equality past pure delay to a genuinely nonzero
  rate.

* **The upper half for rate-latency `β_{R,T}` and any convex-PWL `β` (general).** The
  served output `A ∗ β` is a left-continuous curve, so `S̄ ⊆ S_mp(β)` holds for the
  rate-latency and full convex-PWL targets too.

What remains open is exactly the book's open part: the *construction* `Ŝ(β)` realizing
`S_strict(β) ⊆ Ŝ(β)` for a general convex-PWL `β` with latency, and the composition
hypothesis `Ŝ(β₂) ∘ Ŝ(β₁) ⊆ Ŝ(β₁ ∗ β₂)` that closes the lower inclusion. -/

namespace DeepWiki

open Set Filter Topology
open scoped Classical NNReal ENNReal

/-- **Left limit dominated by a uniform bound (`EReal`-valued)**: for a
left-continuous `g : ℝ≥0 → EReal`, if `g (x − ε) ≤ c` for every `ε > 0`, then
`g x ≤ c`. The `EReal` sibling of `le_of_forall_sub_pos_le_of_isLeftContinuous`,
used to take the closure's `ε → 0⁺` limit on the served output `A ∗ β`. -/
theorem le_of_forall_sub_pos_le_of_isLeftContinuous_ereal {g : ℝ≥0 → EReal}
    (hg : IsLeftContinuous g) {x : ℝ≥0} {c : EReal}
    (h : ∀ ε : ℝ≥0, 0 < ε → g (x - ε) ≤ c) : g x ≤ c := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ x) with hx | hx
  · subst hx
    have h0 := h 1 one_pos
    rwa [zero_tsub] at h0
  · haveI : (𝓝[<] x).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hx⟩
    refine le_of_tendsto (hg x).tendsto ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hyx : y < x := hy
    have hb := h (x - y) (tsub_pos_of_lt hyx)
    rwa [tsub_tsub_cancel_of_le hyx.le] at hb

/-! ## The general upper inclusion `S̄(S) ⊆ S_mp(β)`

The system closure of any system min-plus served by `β` is again min-plus served by `β`,
provided the served output `A ∗ β` is a left-continuous curve. This is the always-true
half of Theorem 9.7's sandwich, and the only analytic input is left-continuity of the
convolution output (the same input the delay base case used). -/

/-- **The closure of `S_mp(β)` stays min-plus served by `β`**, when the convolution output
`A ∗ β` is realized by a curve `convCurve A` (so it is real-valued and left-continuous).
The closure's `ε`-approximation gives `(A ∗ β)(t − ε) ≤ D' t` for every `ε > 0`; the left
limit of the left-continuous `A ∗ β` yields `(A ∗ β) t ≤ D' t`. The pure-delay instance is
`systemClosure_minimalServiceRel_delay_le` (`convCurve A = shiftCurve A T`). -/
theorem systemClosure_minimalServiceRel_le_of_eq_curveEReal {β : ℝ≥0 → EReal}
    (convCurve : Curve → Curve)
    (hconv : ∀ A : Curve, minConv (curveEReal A) β = curveEReal (convCurve A)) :
    systemClosure (minimalServiceRel β) ≤ minimalServiceRel β := by
  rintro A D' ⟨hcaus, happ⟩
  refine mem_minimalServiceRel_iff.mpr ⟨hcaus, ?_⟩
  rw [hconv A]
  intro t
  -- reduce to the real-valued left-continuous output curve `convCurve A`
  have key : convCurve A t ≤ D' t := by
    refine le_of_forall_sub_pos_le_of_isLeftContinuous (convCurve A).leftCont
      (fun ε hε => ?_)
    obtain ⟨D, hD, hDε⟩ := happ ε hε
    have hmpD := (mem_minimalServiceRel_iff.mp hD).2
    rw [hconv A] at hmpD
    have h := hmpD (t - ε)
    simp only [curveEReal_apply] at h
    have h1 : convCurve A (t - ε) ≤ D (t - ε) := by exact_mod_cast h
    exact h1.trans (hDε t)
  simp only [curveEReal_apply]
  exact_mod_cast key

/-- **The general upper inclusion of Theorem 9.7's sandwich.** If a system `S` is min-plus
served by `β` (`S ⊆ S_mp(β)`) and the served output `A ∗ β` is a (left-continuous) curve,
then the whole system closure is min-plus served by `β`: `S̄(S) ⊆ S_mp(β)`. This is the
always-true half — no composition hypothesis, no construction. -/
theorem systemClosure_le_minimalServiceRel_of_eq_curveEReal {β : ℝ≥0 → EReal}
    {S : Curve → Curve → Prop} (hS : S ≤ minimalServiceRel β)
    (convCurve : Curve → Curve)
    (hconv : ∀ A : Curve, minConv (curveEReal A) β = curveEReal (convCurve A)) :
    systemClosure S ≤ minimalServiceRel β :=
  le_trans (systemClosure_mono hS)
    (systemClosure_minimalServiceRel_le_of_eq_curveEReal convCurve hconv)

/-! ### The same upper inclusion from `EReal` left-continuity of `A ∗ β`

The closure stays min-plus served whenever the served output `A ∗ β` is a monotone,
left-continuous `EReal` curve with no `(+∞)+(−∞)` collision at its splits — which is
exactly `isLeftContinuous_minConv_ereal`. This form does not need a closed-form output
curve, so it covers rate-latency and full convex-PWL targets where `A ∗ β` has no simple
shift expression. -/

/-- **The closure of `S_mp(β)` stays min-plus served by `β`** when `β` is monotone,
left-continuous, and never collides with `curveEReal A` under `+` (no `(+∞)+(−∞)` at the
convolution splits). The served output `A ∗ β` is then left-continuous
(`isLeftContinuous_minConv_ereal`), and the closure's `ε → 0⁺` limit gives
`(A ∗ β) t ≤ D' t`. -/
theorem systemClosure_minimalServiceRel_le_of_leftCont {β : ℝ≥0 → EReal}
    (hβmono : Monotone β) (hβlc : IsLeftContinuous β)
    (hpair : ∀ (A : Curve) (r u : ℝ≥0), AddDefined (curveEReal A u) (β (r - u))) :
    systemClosure (minimalServiceRel β) ≤ minimalServiceRel β := by
  rintro A D' ⟨hcaus, happ⟩
  refine mem_minimalServiceRel_iff.mpr ⟨hcaus, fun t => ?_⟩
  have hlc : IsLeftContinuous (minConv (curveEReal A) β) :=
    isLeftContinuous_minConv_ereal (curveEReal A) β (monotone_curveEReal A) hβmono
      (isLeftContinuous_curveEReal A) hβlc (hpair A)
  refine le_of_forall_sub_pos_le_of_isLeftContinuous_ereal hlc (fun ε hε => ?_)
  obtain ⟨D, hD, hDε⟩ := happ ε hε
  have hmpD := (mem_minimalServiceRel_iff.mp hD).2
  calc minConv (curveEReal A) β (t - ε)
      ≤ curveEReal D (t - ε) := hmpD (t - ε)
    _ = ((D (t - ε) : ℝ) : EReal) := curveEReal_apply D (t - ε)
    _ ≤ ((D' t : ℝ) : EReal) := by exact_mod_cast hDε t
    _ = curveEReal D' t := (curveEReal_apply D' t).symm

/-- **The general upper inclusion, `EReal`-left-continuity form.** If `S ⊆ S_mp(β)`, `β` is
monotone and left-continuous, and `β` never collides with `curveEReal A` under `+`, then
`S̄(S) ⊆ S_mp(β)`. Used for rate-latency and convex-PWL targets. -/
theorem systemClosure_le_minimalServiceRel_of_leftCont {β : ℝ≥0 → EReal}
    {S : Curve → Curve → Prop} (hS : S ≤ minimalServiceRel β)
    (hβmono : Monotone β) (hβlc : IsLeftContinuous β)
    (hpair : ∀ (A : Curve) (r u : ℝ≥0), AddDefined (curveEReal A u) (β (r - u))) :
    systemClosure S ≤ minimalServiceRel β :=
  le_trans (systemClosure_mono hS)
    (systemClosure_minimalServiceRel_le_of_leftCont hβmono hβlc hpair)

/-- **The upper inclusion for any finite (`liftEReal`) target `β`.** When the system is
served by the lift of a monotone left-continuous real curve `β`, the closure stays served
by it: `S̄(S) ⊆ S_mp(liftEReal β)`. The `AddDefined` collision condition is automatic
(`liftEReal` values are finite real coercions). -/
theorem systemClosure_le_minimalServiceRel_liftEReal {β : ℝ≥0 → ℝ≥0}
    {S : Curve → Curve → Prop} (hS : S ≤ minimalServiceRel (liftEReal β))
    (hβmono : Monotone β) (hβlc : IsLeftContinuous β) :
    systemClosure S ≤ minimalServiceRel (liftEReal β) :=
  systemClosure_le_minimalServiceRel_of_leftCont hS (monotone_liftEReal hβmono)
    (isLeftContinuous_liftEReal hβlc)
    (fun A _ _ => addDefined_liftEReal ⇑A _ _)

/-! ## The complete sandwich for a constant rate `λ_R` (the next case after `δ_T`)

A constant-rate strict service curve `λ_R` is itself realized by a *single* strict server,
so no dilution is needed: the one-server system `S_strict(λ_R)` already satisfies
`S_strict(λ_R) ⊆ S̄(S_strict(λ_R)) ⊆ S_mp(λ_R)`. This is the cleanest extension of the
delay dilution past pure delay (`R > 0` rate), and — unlike the general convex-PWL
construction — it needs *no* composition hypothesis. -/

/-- **`S̄(S_strict(λ_R)) ⊆ S_mp(λ_R)`**: the closure of the single strict rate server is
min-plus served by `λ_R`. The served output `A ∗ λ_R` is left-continuous (`λ_R` is
continuous), so the closure's `ε → 0⁺` limit applies. -/
theorem systemClosure_strictServiceRel_rate_le (R : ℝ≥0) :
    systemClosure (strictServiceRel (rate R)) ≤ minimalServiceRel (liftEReal (rate R)) :=
  systemClosure_le_minimalServiceRel_liftEReal
    (strictServiceRel_le_minimalServiceRel (rate R)) (rate_mono R)
    (isLeftContinuous_of_continuous _ (rate_continuous R))

/-- **The complete sandwich for `λ_R`**: `S_strict(λ_R) ⊆ S̄(S_strict(λ_R)) ⊆ S_mp(λ_R)`,
the single strict rate server placed in the system closure. No composition hypothesis is
needed — `λ_R` has no latency to stack. -/
theorem strictServiceRel_rate_le_systemClosure_le_minimalServiceRel (R : ℝ≥0) :
    strictServiceRel (rate R) ≤ systemClosure (strictServiceRel (rate R)) ∧
      systemClosure (strictServiceRel (rate R)) ≤ minimalServiceRel (liftEReal (rate R)) :=
  ⟨subset_systemClosure (isServer_strictServiceRel (rate_zero_eq R)).1,
    systemClosure_strictServiceRel_rate_le R⟩

/-! ## The upper half for rate-latency `β_{R,T}` and convex-PWL `β`

The served output `A ∗ β` stays left-continuous for any monotone left-continuous real
target, so the upper inclusion of the sandwich holds for rate-latency and convex-PWL too.
The *lower* inclusion `S_strict(β) ⊆ Ŝ(β)` for a general convex-PWL `β` with latency is the
book's open construction (see the adjudication at the end of the file). -/

/-- **`S̄(S_strict(β_{R,T})) ⊆ S_mp(β_{R,T})`**: the closure of a single strict rate-latency
server is min-plus served by `β_{R,T}` (the rate-latency curve is continuous). -/
theorem systemClosure_strictServiceRel_rateLatency_le (R T : ℝ≥0) :
    systemClosure (strictServiceRel (rateLatency R T))
      ≤ minimalServiceRel (liftEReal (rateLatency R T)) :=
  systemClosure_le_minimalServiceRel_liftEReal
    (strictServiceRel_le_minimalServiceRel (rateLatency R T)) (rateLatency_mono R T)
    (isLeftContinuous_of_continuous _ (rateLatency_continuous R T))

/-- `rateLatencyEReal R T` is left-continuous (the `EReal` rate-latency curve, a continuous
real curve coerced into `EReal`). -/
theorem isLeftContinuous_rateLatencyEReal (R T : ℝ≥0) :
    IsLeftContinuous (rateLatencyEReal R T) := by
  have h : rateLatencyEReal R T = liftEReal (rateLatency R T) := by
    funext u; simp [rateLatencyEReal, liftEReal, rateLatency]
  rw [h]
  exact isLeftContinuous_liftEReal (isLeftContinuous_of_continuous _ (rateLatency_continuous R T))

/-- A convex piecewise-linear curve `convexNFEval l` (a finite supremum of rate-latency
curves, `⊥` at the empty list) is left-continuous — the `EReal` join of left-continuous
curves is left-continuous. -/
theorem isLeftContinuous_convexNFEval (l : List (ℝ≥0 × ℝ≥0)) :
    IsLeftContinuous (convexNFEval l) := by
  induction l with
  | nil => exact fun t => continuousWithinAt_const
  | cons rt l ih =>
    rw [convexNFEval_cons]
    exact fun t => (isLeftContinuous_rateLatencyEReal rt.1 rt.2 t).sup (ih t)

/-- **`S̄(S) ⊆ S_mp(β)` for a convex piecewise-linear target `β = convexNFEval l`.** Whenever
the system `S` is min-plus served by a convex-PWL curve `β`, the whole closure stays served
by `β`: the served output `A ∗ β` is left-continuous (`β` is a finite sup of continuous
rate-latencies), and no `(+∞)+(−∞)` collision occurs (`A` is finite). This is the
always-true upper inclusion of Theorem 9.7's sandwich, for the *general* convex-PWL target.
The matching lower inclusion `S_strict(β) ⊆ Ŝ(β)` for `β` with latency is the book's open
construction. -/
theorem systemClosure_le_minimalServiceRel_convexNFEval
    {l : List (ℝ≥0 × ℝ≥0)} {S : Curve → Curve → Prop}
    (hS : S ≤ minimalServiceRel (convexNFEval l)) :
    systemClosure S ≤ minimalServiceRel (convexNFEval l) :=
  systemClosure_le_minimalServiceRel_of_leftCont hS (monotone_convexNFEval l)
    (isLeftContinuous_convexNFEval l)
    (fun A _ _ => addDefined_liftEReal ⇑A _ (convexNFEval l _))

/-! ## Book restatement (Theorem 9.7, §9.3.1, p. 227)

> For each convex and piecewise linear function `β` in `ℱ`, associate `Ŝ(β)` a system such
> that `S_strict(β) ⊆ Ŝ(β) ⊆ S_mp(β)`. If for all convex piecewise linear `β₁, β₂`,
> `Ŝ(β₂) ∘ Ŝ(β₁) ⊆ Ŝ(β₁ ∗ β₂)`, then for all `β`, `S̄(Ŝ(β)) = S_mp(β)`.

The book proves only the pure-delay base case (Lemma 9.5, the delay dilution, formalized in
`ServiceCurveStrictTandem`/`ServiceCurveStrictTandemDilution`). The two ingredients of the
theorem's *conclusion* are the sandwich `S_strict(β) ⊆ Ŝ(β) ⊆ S_mp(β)` and the closure
collapse `S̄(Ŝ(β)) = S_mp(β)`. Of these:

* the **upper inclusion `S̄(S) ⊆ S_mp(β)`** is unconditional (this file), and
* the **lower inclusion of the sandwich plus the closure collapse hold completely for a
  constant rate `λ_R`** with `Ŝ(λ_R) := S_strict(λ_R)` — no composition hypothesis.

`Ŝ(β)` for a general convex-PWL `β` with latency, and the composition hypothesis, are open
(see the adjudication block). -/

/-- The always-true upper inclusion of the sandwich, for the convex-PWL target
`β = convexNFEval l`: any system served by `β` keeps its closure served by `β`. -/
example {l : List (ℝ≥0 × ℝ≥0)} {S : Curve → Curve → Prop}
    (hS : S ≤ minimalServiceRel (convexNFEval l)) :
    systemClosure S ≤ minimalServiceRel (convexNFEval l) :=
  systemClosure_le_minimalServiceRel_convexNFEval hS

/-- The full sandwich `S_strict(β) ⊆ Ŝ(β) ⊆ S_mp(β)` for the constant rate `λ_R`, realized
by the single strict server `Ŝ(λ_R) := S_strict(λ_R)`. -/
example (R : ℝ≥0) :
    strictServiceRel (rate R) ≤ systemClosure (strictServiceRel (rate R)) ∧
      systemClosure (strictServiceRel (rate R)) ≤ minimalServiceRel (liftEReal (rate R)) :=
  strictServiceRel_rate_le_systemClosure_le_minimalServiceRel R

/-- The pure-delay base case (Lemma 9.5) is the closure collapse `S̄(Ŝ(δ_T)) = S_mp(δ_T)`,
formalized as `systemClosure_delayTandemUnion_eq` — the model this file generalizes. -/
example {T : ℝ≥0} (hT : 0 < T) :
    systemClosure (delayTandemUnion T) = minimalServiceRel (delayEReal T) :=
  systemClosure_delayTandemUnion_eq hT

/-! ## Adjudication: what the general Theorem 9.7 still needs

The book (Bouillard, Boyer, Le Corronc, §9.3.1) states Theorem 9.7 but proves only the
pure-delay base case (Lemma 9.5). It is explicitly *conditional*: the closure collapse
`S̄(Ŝ(β)) = S_mp(β)` is asserted only **under** the composition hypothesis
`Ŝ(β₂) ∘ Ŝ(β₁) ⊆ Ŝ(β₁ ∗ β₂)`, which the book does not establish for the construction it
sketches. So the general statement is research-grade / open; a faithful formalization must
not assert it unconditionally.

What is unconditionally true and formalized here:

* **Upper inclusion `S̄(S) ⊆ S_mp(β)`** for any `β` whose convolution output `A ∗ β` is a
  left-continuous curve (`systemClosure_minimalServiceRel_le_of_leftCont`), discharged for
  pure delay, constant rate, rate-latency, and full convex-PWL targets. The only analytic
  input is left-continuity of `A ∗ β` — exactly what the delay base case used.

* **Complete sandwich + collapse for `λ_R`** (`R > 0`, no latency): the single strict rate
  server `S_strict(λ_R)` is already a one-server system, so
  `S_strict(λ_R) ⊆ S̄(S_strict(λ_R)) ⊆ S_mp(λ_R)` with no dilution and no composition
  hypothesis. This extends the delay dilution past pure delay.

What the general convex-PWL theorem needs that this file does *not* provide:

* **The construction `Ŝ(β)` realizing the lower inclusion `S_strict(β) ⊆ Ŝ(β)` for a
  convex-PWL `β` with latency.** A convex-PWL `β = ⨆ᵢ β_{Rᵢ,Tᵢ}` stacks rate-latency
  segments; the delay (`Tᵢ`) part demands the *dilution* of Lemma 9.5 (an `n → ∞` family of
  finer strict-`δ_{T/n}` tandems), while the rate (`Rᵢ`) part is a single strict server.
  Combining them is a *per-segment tandem* of (delay-dilution) ∘ (strict-rate) stages — and
  composing a dilution system with a rate server is precisely where the composition
  hypothesis is needed. The delay base case (`delayTandemUnion`) realizes only the latency
  of a *single* segment; the multi-segment convex-NF decomposition feeding the construction,
  and the proof that the stacked system meets `S_strict(β)`, are not formalized.

* **The composition hypothesis `Ŝ(β₂) ∘ Ŝ(β₁) ⊆ Ŝ(β₁ ∗ β₂)`.** This is the open lemma the
  book defers; the strict-service composition results in `ServiceCurveStrictTandem` go the
  *other* way (strict curves with positive vanishing points do *not* compose to a nonzero
  strict curve — `eq_zero_of_comp_strictServiceRel_le`), which is exactly why the *system*
  closure, not a single strict server, is needed, and why this hypothesis is delicate.

Hence the deliverable is the unconditional upper half (general) + the complete `λ_R`
sandwich (honestly scoped) + this adjudication; the general construction and composition
hypothesis remain the book's open part. -/

end DeepWiki
