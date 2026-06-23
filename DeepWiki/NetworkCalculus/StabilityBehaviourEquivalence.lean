import DeepWiki.NetworkCalculus.StabilityLocalOfGlobal
import DeepWiki.NetworkCalculus.StabilityGlobal

/-! # Lemma 12.2 (global ⟹ local stability), via a behaviour-preserving service-curve raise
The book's proof of **Lemma 12.2** raises each strict service curve `β` to
`β ∨ δ_T`, where `δ_T` is the pure-delay function (`0` up to `T`, `+∞` after)
and `T` bounds every backlogged period. By Proposition 5.13, *only the part of a
service curve before `T` matters* on backlogged periods of length `≤ T`, so the
behaviour is unchanged; but `R(β ∨ δ_T) = ∞`, so every server is locally stable.

Two obstructions are handled here:

* **The infinite jump of `δ_T` is not `ℝ≥0`-valued.** `longTermServiceRate` is
  typed `(ℝ≥0 → ℝ≥0) → ℝ≥0∞`, so the literal `δ_T = delay T` (which jumps to
  `+∞`) is not in its domain. We use the *representable surrogate*
  `rateLatency n T : t ↦ n·(t − T)₊`: like `δ_T` it vanishes on `[0, T]`
  (`rateLatency n T u = 0` for `u ≤ T`), so it leaves the strict bound on
  short backlogged periods untouched; unlike `δ_T` it is finite-valued with
  `longTermServiceRate (rateLatency n T) = n`, so `n → ∞` realizes the
  book's `R = ∞` through an arbitrarily large *finite* surrogate rate.

* **The behaviour-equivalence (Prop 5.13).** `isStrictMinimalServiceCurve_sup_of_maxBackloggedLength_le`
  raises a strict service curve `β` to `β ⊔ γ` for *any* `γ` vanishing on
  `[0, T]`, provided every backlogged period of the served pair has length
  `≤ T` — the strict bound on `Ioc s t` (with `t − s ≤ T`) reads
  `(β ⊔ γ)(t − s) = β(t − s)`, unchanged. With `γ = rateLatency n T` this is
  the surrogate of the `β ∨ δ_T` raise.

Assembling these gives the per-pair Lemma 12.2 for the linear (token-bucket)
model: a globally stable server (max backlogged period `≤ T`) carrying a
token-bucket-bounded flow is locally stable against the raised curve
`β ⊔ rateLatency n T` with `r < n`. The fully general "network is globally
stable ⟹ locally stable" over an arbitrary strict service curve `β` needs the
behaviour-equivalence at the *served-pair-relation* level; see the scoping note
at the foot of this file and the catalog's `## NOT YET FORMALIZED`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Filter

/-! ## (1) The representable `δ_T` surrogate `rateLatency n T` and its long-term rate -/

/-- `rateLatency R T` vanishes on `[0, T]`: `rateLatency R T u = 0` for `u ≤ T`
(the `(u − T)₊` is `0`), exactly as the pure-delay `δ_T` does. -/
theorem rateLatency_eq_zero_of_le {R T u : ℝ≥0} (h : u ≤ T) :
    rateLatency R T u = 0 := by
  show R * (u - T) = 0
  rw [tsub_eq_zero_of_le h, mul_zero]

/-- The long-term service rate is monotone under a pointwise join on the right:
`R(β) ≤ R(β ⊔ γ)` and `R(γ) ≤ R(β ⊔ γ)`. -/
theorem longTermServiceRate_le_sup_right (β γ : ℝ≥0 → ℝ≥0) :
    longTermServiceRate γ ≤ longTermServiceRate (fun t => β t ⊔ γ t) :=
  longTermServiceRate_mono fun _ => le_sup_right

/-- **The surrogate raise has an arbitrarily large service rate**: raising any
`β` by the representable `rateLatency n T` (the finite `δ_T` surrogate) makes the
long-term service rate at least `n`,
`(n : ℝ≥0∞) ≤ R(β ⊔ rateLatency n T)`. Taking `n` large realizes the book's
`R = ∞` of `β ∨ δ_T` through an arbitrarily large *finite* rate. -/
theorem le_longTermServiceRate_sup_rateLatency (β : ℝ≥0 → ℝ≥0) (n T : ℝ≥0) :
    (n : ℝ≥0∞) ≤ longTermServiceRate (fun t => β t ⊔ rateLatency n T t) := by
  calc (n : ℝ≥0∞) = longTermServiceRate (rateLatency n T) :=
        (longTermServiceRate_rateLatency n T).symm
    _ ≤ longTermServiceRate (fun t => β t ⊔ rateLatency n T t) :=
        longTermServiceRate_le_sup_right β (rateLatency n T)

/-! ## (2) Behaviour-equivalence: raising `β` to `β ⊔ γ` on short backlogged periods (Prop 5.13)

The Prop 5.13 content needed for Lemma 12.2: on a backlogged period of length
`≤ T`, a service curve and any raise of it that agrees with it on `[0, T]`
give the *same* strict bound. The raise `β ⊔ γ` (with `γ` vanishing on `[0, T]`,
e.g. `γ = δ_T` or its surrogate `rateLatency n T`) is therefore still a strict
service curve, while having a much larger long-term rate. -/

/-- **The strict bound is insensitive to a raise that vanishes on `[0, T]`**
(pointwise, the core of Prop 5.13 for Lemma 12.2): if the strict bound
`D s + β (t − s) ≤ D t` holds and the period has length `t − s ≤ T`, then the
*raised* bound `D s + (β ⊔ γ)(t − s) ≤ D t` holds for any `γ` vanishing on
`[0, T]` — because `(β ⊔ γ)(t − s) = β (t − s) ⊔ 0 = β (t − s)`. -/
theorem strictBound_sup_of_le {β γ : ℝ≥0 → ℝ≥0} {D : ℝ≥0 → ℝ≥0} {s t T : ℝ≥0}
    (hγ : ∀ u ≤ T, γ u = 0) (hlen : t - s ≤ T)
    (hbound : D s + β (t - s) ≤ D t) :
    D s + (β (t - s) ⊔ γ (t - s)) ≤ D t := by
  rw [hγ (t - s) hlen, sup_eq_left.mpr zero_le]
  exact hbound

/-- **Behaviour-preserving service-curve raise (Prop 5.13 for Lemma 12.2).**
If every backlogged period of every pair served by `S` has length `≤ T`, then a
strict service curve `β` for `S` can be raised to `β ⊔ γ` for any `γ` vanishing
on `[0, T]` and remain a strict service curve for `S`: on a backlogged period
`Ioc s t` (necessarily `t − s ≤ T`) the raise `(β ⊔ γ)(t − s)` equals
`β (t − s)`, so the bound is unchanged. -/
theorem isStrictMinimalServiceCurve_sup_of_backloggedLength_le
    {S : Curve → Curve → Prop} {β γ : ℝ≥0 → ℝ≥0} {T : ℝ≥0}
    (hβ : IsStrictMinimalServiceCurve β S)
    (hγ : ∀ u ≤ T, γ u = 0)
    (hshort : ∀ A D : Curve, S A D → ∀ s t, s ≤ t →
      IsBacklogged (⇑A) (⇑D) (Set.Ioc s t) → t - s ≤ T) :
    IsStrictMinimalServiceCurve (fun u => β u ⊔ γ u) S := by
  intro A D hp s t hst hbl
  exact strictBound_sup_of_le hγ (hshort A D hp s t hst hbl) (hβ A D hp s t hst hbl)

/-- A pair whose maximal backlogged period is `≤ T` has every concrete
backlogged period `Ioc s t` of length `t − s ≤ T`: such a period is backlogged
on `Ioc s t = Ioc s (s + (t − s))`, so its length is dominated by the maximum,
`(t − s : ℝ≥0∞) ≤ maxBackloggedLength A D ≤ T`. -/
theorem backloggedLength_le_of_maxBackloggedLength_le {A D : ℝ≥0 → ℝ≥0} {T : ℝ≥0}
    (hmax : maxBackloggedLength A D ≤ (T : ℝ≥0∞)) {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged A D (Set.Ioc s t)) : t - s ≤ T := by
  have hbl' : IsBacklogged A D (Set.Ioc s (s + (t - s))) := by
    rwa [add_tsub_cancel_of_le hst]
  have hle : ((t - s : ℝ≥0) : ℝ≥0∞) ≤ (T : ℝ≥0∞) :=
    (le_maxBackloggedLength_of_isBacklogged hbl').trans hmax
  exact_mod_cast hle

/-- **Global stability of a server bounds its backlogged periods by a common
`T`** (the book's "let `T` be the maximum of all these backlogged periods"):
when every pair served by `S` has its maximal backlogged period bounded by the
same `T`, every concrete backlogged period of every served pair has length
`≤ T`. The `hshort` hypothesis of the raise. -/
theorem backloggedLength_le_of_forall_maxBackloggedLength_le
    {S : Curve → Curve → Prop} {T : ℝ≥0}
    (hmax : ∀ A D : Curve, S A D → maxBackloggedLength (⇑A) (⇑D) ≤ (T : ℝ≥0∞))
    (A D : Curve) (hp : S A D) {s t : ℝ≥0} (hst : s ≤ t)
    (hbl : IsBacklogged (⇑A) (⇑D) (Set.Ioc s t)) : t - s ≤ T :=
  backloggedLength_le_of_maxBackloggedLength_le (hmax A D hp) hst hbl

/-! ## (3) Lemma 12.2 (global ⟹ local), per-server, via the surrogate raise -/

/-- **Lemma 12.2, server form (with the surrogate raise).** If a server `S` is
globally stable — every served pair has maximal backlogged period bounded by a
common `T` — and offers a strict service curve `β`, then for *any* surrogate
rate `n` strictly above a finite arrival rate `r(α) < n`, the server with `β`
raised to the behaviour-equivalent `β ⊔ rateLatency n T` is **locally stable**
against `α`. This is the book's `β ∨ δ_T` argument with the representable
`rateLatency n T` standing in for `δ_T`: the raise is behaviour-preserving
(Prop 5.13, `isStrictMinimalServiceCurve_sup_of_backloggedLength_le`) and lifts
the service rate above the arrival rate (`le_longTermServiceRate_sup_rateLatency`). -/
theorem isLocallyStableServer_sup_rateLatency_of_globallyStable
    {S : Curve → Curve → Prop} {β α : ℝ≥0 → ℝ≥0} {T n : ℝ≥0}
    (hβ : IsStrictMinimalServiceCurve β S)
    (hmax : ∀ A D : Curve, S A D → maxBackloggedLength (⇑A) (⇑D) ≤ (T : ℝ≥0∞))
    (hrate : longTermArrivalRate α < (n : ℝ≥0∞)) :
    IsStrictMinimalServiceCurve (fun u => β u ⊔ rateLatency n T u) S ∧
      IsLocallyStableServer α (fun u => β u ⊔ rateLatency n T u) := by
  refine ⟨isStrictMinimalServiceCurve_sup_of_backloggedLength_le hβ
      (fun _ h => rateLatency_eq_zero_of_le h)
      (backloggedLength_le_of_forall_maxBackloggedLength_le hmax), ?_⟩
  exact hrate.trans_le (le_longTermServiceRate_sup_rateLatency β n T)

/-- **Lemma 12.2 for the token-bucket model.** A globally stable server (common
backlogged bound `T`) offering a strict service curve `β`, carrying a flow with
finite arrival rate (here a token-bucket curve `γ_{r,b}`, `r(γ_{r,b}) = r`), is
locally stable once the surrogate rate exceeds the arrival rate, `r < n`: the
behaviour-preserving raise `β ⊔ rateLatency n T` has service rate `≥ n > r`. -/
theorem isLocallyStableServer_affine_sup_rateLatency_of_globallyStable
    {S : Curve → Curve → Prop} {β : ℝ≥0 → ℝ≥0} {T n r b : ℝ≥0}
    (hβ : IsStrictMinimalServiceCurve β S)
    (hmax : ∀ A D : Curve, S A D → maxBackloggedLength (⇑A) (⇑D) ≤ (T : ℝ≥0∞))
    (hrn : r < n) :
    IsLocallyStableServer (fun t => r * t + b)
      (fun u => β u ⊔ rateLatency n T u) :=
  (isLocallyStableServer_sup_rateLatency_of_globallyStable hβ hmax
    (by rw [longTermArrivalRate_affine]; exact_mod_cast hrn)).2

/-! ## Faithfulness checks against §12.1 (Lemma 12.2) -/

/-- Faithfulness (the surrogate `δ_T`): on `[0, T]` the surrogate
`rateLatency n T` agrees with the pure-delay `δ_T = delayNN T` (both vanish
there), the property Prop 5.13 uses; the surrogate differs from `δ_T` only past
`T`, where it stays finite instead of jumping to `+∞`. -/
example (n T u : ℝ≥0) (h : u ≤ T) :
    ((rateLatency n T u : ℝ≥0) : ℝ≥0∞) = delayNN T u := by
  rw [rateLatency_eq_zero_of_le h, ENNReal.coe_zero,
    show delayNN T u = delay T u from rfl, delay_eq_zero T h]

/-- Faithfulness (Lemma 12.2 mechanism): a globally stable strict server, with
its service curve raised by the behaviour-preserving surrogate `rateLatency n T`,
is locally stable against any finite-rate flow with `r(α) < n`. -/
example {S : Curve → Curve → Prop} {β α : ℝ≥0 → ℝ≥0} {T n : ℝ≥0}
    (hβ : IsStrictMinimalServiceCurve β S)
    (hmax : ∀ A D : Curve, S A D → maxBackloggedLength (⇑A) (⇑D) ≤ (T : ℝ≥0∞))
    (hrate : longTermArrivalRate α < (n : ℝ≥0∞)) :
    IsLocallyStableServer α (fun u => β u ⊔ rateLatency n T u) :=
  (isLocallyStableServer_sup_rateLatency_of_globallyStable hβ hmax hrate).2

/-! ## Scoping: what the *fully general* Lemma 12.2 needs beyond this file

This file delivers Lemma 12.2 for the representable surrogate of `δ_T`
(`rateLatency n T`), which is enough whenever the served flows have finite
arrival rate (the linear/token-bucket model that the rest of §12 uses, and the
only regime in which local stability is even defined: `r(α) < ⊤`). The *literal*
book statement raises `β` to `β ∨ δ_T` with the genuine infinite-jump `δ_T` and
concludes `R = ∞`. Two model-level pieces, both out of scope for this chapter
(they touch the core carriers / served-pair model, which this task does not
modify), are what a verbatim Lemma 12.2 would still need:

* **An `ℝ≥0∞`-valued long-term service rate.** `longTermServiceRate` is typed
  `(ℝ≥0 → ℝ≥0) → ℝ≥0∞`, so the genuine `δ_T = delay T : ℝ≥0 → ℝ≥0∞` (and hence
  `β ∨ δ_T`, valued in `ℝ≥0∞`) is not in its domain, and `R(β ∨ δ_T) = ∞` cannot
  even be stated. A faithful verbatim proof needs the rate functionals restated
  over `ℝ≥0∞`-valued (or `EReal`-valued) curves — a curve-carrier change living in
  `Stability.lean`/`StabilityRates.lean`, not here. The surrogate sidesteps this:
  an arbitrarily large *finite* rate `n` plays the role of `R = ∞`.

* **A served-pair-relation behaviour-equivalence op.** The book asserts the
  network's *behaviour* is unchanged when every `β` is replaced by `β ∨ δ_T`.
  Here the raise is shown behaviour-preserving at the level of the strict bound
  (`isStrictMinimalServiceCurve_sup_of_backloggedLength_le`: the raised curve is
  still a strict service curve for the *same* relation `S`). A verbatim
  "behaviour (output `D`) is identical, not merely still-bounded" statement needs
  a served-pair-level operation "replace `β`, served pairs preserved" over the
  `Servers` model — again a core-model addition, not a chapter lemma. -/

end DeepWiki
