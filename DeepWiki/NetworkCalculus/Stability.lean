import DeepWiki.NetworkCalculus.ArrivalCurves
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.ENNReal

/-! # Stability primitives
The self-contained building blocks of the stability theory: the long-term
arrival/service rates (`limsup`/`liminf` of `f(t)/t`), the per-server local
stability condition (arrival rate below service rate) and its central
consequence — eventually the arrival curve drops below the service curve, so
the first crossing (hence the maximal backlogged-period length `ℓmax`) is
finite. Also the scaling of a flow by a constant and the fact that scaling
preserves an arrival constraint. (Global stability as a network predicate, the
fix-point sufficient condition, and the universally-stable policies build a
network model on top of these and are not formalized here.) -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Filter

/-- The long-term arrival rate of a flow, `limsup_{t→∞} α(t)/t`
(Definition 12.1). -/
noncomputable def longTermArrivalRate (α : ℝ≥0 → ℝ≥0) : ℝ≥0∞ :=
  limsup (fun t => (α t : ℝ≥0∞) / (t : ℝ≥0∞)) atTop

/-- The long-term service rate of a server, `liminf_{t→∞} β(t)/t`
(Definition 12.1). -/
noncomputable def longTermServiceRate (β : ℝ≥0 → ℝ≥0) : ℝ≥0∞ :=
  liminf (fun t => (β t : ℝ≥0∞) / (t : ℝ≥0∞)) atTop

/-- Subadditivity of `limsup` over `atTop` in `ℝ≥0∞`: `limsup (u + v) ≤ limsup u
+ limsup v`. (Off-the-shelf `limsup_add_le` does not apply — `ENNReal`'s needs
`CountableInterFilter` which `atTop` lacks, the group version needs a group;
this is the hand proof via `ENNReal.le_of_forall_pos_le_add`.) -/
theorem limsup_add_le_atTop (u v : ℝ≥0 → ℝ≥0∞) :
    limsup (fun t => u t + v t) atTop ≤ limsup u atTop + limsup v atTop := by
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε hfin
  set Lu := limsup u atTop
  set Lv := limsup v atTop
  obtain ⟨hLuf, hLvf⟩ := ENNReal.add_lt_top.mp hfin
  have hu : ∀ᶠ t in atTop, u t < Lu + (ε / 2 : ℝ≥0) :=
    eventually_lt_of_limsup_lt (ENNReal.lt_add_right hLuf.ne (by positivity))
  have hv : ∀ᶠ t in atTop, v t < Lv + (ε / 2 : ℝ≥0) :=
    eventually_lt_of_limsup_lt (ENNReal.lt_add_right hLvf.ne (by positivity))
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hu, hv] with t htu htv
  calc u t + v t ≤ (Lu + (ε / 2 : ℝ≥0)) + (Lv + (ε / 2 : ℝ≥0)) := add_le_add htu.le htv.le
    _ = (Lu + Lv) + ((ε / 2 : ℝ≥0) + (ε / 2 : ℝ≥0)) := by ring
    _ = (Lu + Lv) + (ε : ℝ≥0) := by rw [← ENNReal.coe_add]; norm_num

/-- The long-term arrival rate is subadditive: `r(A + B) ≤ r(A) + r(B)`
(the per-flow rates upper-bound the aggregate rate). -/
theorem longTermArrivalRate_add_le (A B : ℝ≥0 → ℝ≥0) :
    longTermArrivalRate (fun t => A t + B t)
      ≤ longTermArrivalRate A + longTermArrivalRate B := by
  have hfun : (fun t => ((A t + B t : ℝ≥0) : ℝ≥0∞) / (t : ℝ≥0∞))
      = (fun t => ((A t : ℝ≥0) : ℝ≥0∞) / (t : ℝ≥0∞)
                + ((B t : ℝ≥0) : ℝ≥0∞) / (t : ℝ≥0∞)) := by
    funext t; rw [ENNReal.coe_add, ENNReal.add_div]
  show limsup (fun t => ((A t + B t : ℝ≥0) : ℝ≥0∞) / (t : ℝ≥0∞)) atTop
      ≤ longTermArrivalRate A + longTermArrivalRate B
  rw [hfun]
  exact limsup_add_le_atTop _ _

/-- The long-term arrival rate of a finite aggregate is below the sum of the
per-flow rates: `r(∑_{i∈s} Aᵢ) ≤ ∑_{i∈s} r(Aᵢ)` (the rate-sum bridge of the
network local-stability condition `∑ rᵢ < R`). -/
theorem longTermArrivalRate_sum_le {ι : Type*} (s : Finset ι) (A : ι → ℝ≥0 → ℝ≥0) :
    longTermArrivalRate (fun t => ∑ i ∈ s, A i t)
      ≤ ∑ i ∈ s, longTermArrivalRate (A i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · have h0 : longTermArrivalRate (fun _ : ℝ≥0 => (0 : ℝ≥0)) = 0 := by
      simp only [longTermArrivalRate]
      have hz : (fun t : ℝ≥0 => ((0 : ℝ≥0) : ℝ≥0∞) / (t : ℝ≥0∞)) = fun _ => (0 : ℝ≥0∞) := by
        funext t; simp
      rw [hz, Filter.limsup_const]
    simp only [Finset.sum_empty]
    exact h0.le
  · intro a s ha ih
    have hL : longTermArrivalRate (fun t => ∑ i ∈ insert a s, A i t)
        = longTermArrivalRate (fun t => A a t + ∑ i ∈ s, A i t) := by
      congr 1; funext t; rw [Finset.sum_insert ha]
    rw [hL, Finset.sum_insert ha]
    calc longTermArrivalRate (fun t => A a t + ∑ i ∈ s, A i t)
        ≤ longTermArrivalRate (A a) + longTermArrivalRate (fun t => ∑ i ∈ s, A i t) :=
          longTermArrivalRate_add_le (A a) (fun t => ∑ i ∈ s, A i t)
      _ ≤ longTermArrivalRate (A a) + ∑ i ∈ s, longTermArrivalRate (A i) := by gcongr

/-- The empty flow has zero long-term rate: `r(0) = 0` (every ratio `0/t` is `0`,
so the `limsup` is `0`). -/
@[simp] theorem longTermArrivalRate_zero : longTermArrivalRate 0 = 0 := by
  unfold longTermArrivalRate
  simp only [Pi.zero_apply, ENNReal.coe_zero, ENNReal.zero_div, Filter.limsup_const]

/-- The long-term arrival rate is monotone under pointwise domination: a flow
dominated by another has no larger long-term rate (`A ≤ B ⟹ r(A) ≤ r(B)`). -/
theorem longTermArrivalRate_mono {A B : ℝ≥0 → ℝ≥0} (h : ∀ t, A t ≤ B t) :
    longTermArrivalRate A ≤ longTermArrivalRate B := by
  refine Filter.limsup_le_limsup (Filter.Eventually.of_forall fun t => ?_)
  show (A t : ℝ≥0∞) / (t : ℝ≥0∞) ≤ (B t : ℝ≥0∞) / (t : ℝ≥0∞)
  gcongr
  exact_mod_cast h t

/-- A single server is **locally stable** when the long-term arrival rate of
its (aggregate) input flow is strictly below its long-term service rate
(Definition 12.2, per-server form: `∑ rᵢ < R` for the aggregate `α`). -/
def IsLocallyStableServer (α β : ℝ≥0 → ℝ≥0) : Prop :=
  longTermArrivalRate α < longTermServiceRate β

/-- **The analytic heart of local stability**: if the long-term arrival rate
of `α` is strictly below the long-term service rate of `β`, then eventually
(for all large `t`) the arrival curve drops to or below the service curve,
`α t ≤ β t`. Proof: pick a rate `c` strictly between the `limsup` and the
`liminf`; then eventually `α t / t < c < β t / t`, and dividing out the common
`t` (monotonicity of `·/t`) gives `α t ≤ β t`. -/
theorem eventually_le_of_longTermArrivalRate_lt {α β : ℝ≥0 → ℝ≥0}
    (h : longTermArrivalRate α < longTermServiceRate β) :
    ∀ᶠ t in atTop, α t ≤ β t := by
  obtain ⟨c, hac, hcb⟩ := exists_between h
  have h1 : ∀ᶠ t in atTop, (α t : ℝ≥0∞) / (t : ℝ≥0∞) < c :=
    eventually_lt_of_limsup_lt hac
  have h2 : ∀ᶠ t in atTop, c < (β t : ℝ≥0∞) / (t : ℝ≥0∞) :=
    eventually_lt_of_lt_liminf hcb
  filter_upwards [h1, h2] with t ht1 ht2
  have hlt : (α t : ℝ≥0∞) / (t : ℝ≥0∞) < (β t : ℝ≥0∞) / (t : ℝ≥0∞) := ht1.trans ht2
  rw [← ENNReal.coe_le_coe]
  by_contra hcon
  rw [not_le] at hcon
  have hle : (β t : ℝ≥0∞) ≤ (α t : ℝ≥0∞) := hcon.le
  have hdiv : (β t : ℝ≥0∞) / (t : ℝ≥0∞) ≤ (α t : ℝ≥0∞) / (t : ℝ≥0∞) := by gcongr
  exact lt_irrefl _ (hdiv.trans_lt hlt)

/-- The crossing set of a locally stable server is nonempty: eventually
`α t ≤ β t`, so some positive time witnesses the crossing. -/
theorem crossingSet_nonempty_of_isLocallyStableServer {α β : ℝ≥0 → ℝ≥0}
    (h : IsLocallyStableServer α β) : (crossingSet α β).Nonempty := by
  obtain ⟨x, hx0, hxle⟩ :=
    ((eventually_gt_atTop 0).and (eventually_le_of_longTermArrivalRate_lt h)).exists
  exact ⟨x, hx0, hxle⟩

/-- **Lemma 12.1** (local stability ⟹ finite backlogged period): a locally
stable server has a *finite* first crossing `firstCrossing α β < ⊤`. Since the
maximal backlogged-period length `ℓmax` is bounded by this first crossing
(Theorem 5.5, `maxBackloggedLength_le_firstCrossing`), `ℓmax < ∞`. -/
theorem firstCrossing_lt_top_of_isLocallyStableServer {α β : ℝ≥0 → ℝ≥0}
    (h : IsLocallyStableServer α β) : firstCrossing α β < ⊤ := by
  obtain ⟨x, hx0, hxle⟩ := crossingSet_nonempty_of_isLocallyStableServer h
  calc firstCrossing α β ≤ (x : ℝ≥0∞) := iInf₂_le x ⟨hx0, hxle⟩
    _ < ⊤ := ENNReal.coe_lt_top

/-- A flow scaled by a constant `m ∈ ℝ≥0`: `(m · A)(t) = m · A t`
(Definition 12.4). -/
def scaledFlow (m : ℝ≥0) (A : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 := fun t => m * A t

/-- `scaledFlow m A t = m * A t`. -/
@[simp] theorem scaledFlow_apply (m : ℝ≥0) (A : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    scaledFlow m A t = m * A t := rfl

/-- Scaling a flow scales its long-term arrival rate (§12.4.2): the long-term
arrival rate of `m·A` is `m` times that of `A`. The constant `↑m ≠ ⊤` factors
out of the `limsup` (`ENNReal.limsup_const_mul_of_ne_top`). -/
theorem longTermArrivalRate_scaledFlow (m : ℝ≥0) (A : ℝ≥0 → ℝ≥0) :
    longTermArrivalRate (scaledFlow m A) = (m : ℝ≥0∞) * longTermArrivalRate A := by
  have hfun : (fun t => ((scaledFlow m A t : ℝ≥0) : ℝ≥0∞) / (t : ℝ≥0∞))
      = (fun t => (m : ℝ≥0∞) * (((A t : ℝ≥0) : ℝ≥0∞) / (t : ℝ≥0∞))) := by
    funext t
    rw [scaledFlow_apply, ENNReal.coe_mul, mul_div_assoc]
  rw [longTermArrivalRate, hfun, ENNReal.limsup_const_mul_of_ne_top ENNReal.coe_ne_top,
    longTermArrivalRate]

/-- Scaling preserves a maximal arrival bound: if `α` upper-bounds the flow
`A`, then `m·α` upper-bounds the scaled flow `m·A` (Lemma 12.6). -/
theorem isMaximalArrivalBound_scaledFlow {A α : ℝ≥0 → ℝ≥0} (m : ℝ≥0)
    (h : IsMaximalArrivalBound A α) :
    IsMaximalArrivalBound (scaledFlow m A) (scaledFlow m α) := by
  rw [isMaximalArrivalBound_iff_increment] at h ⊢
  intro t d
  calc scaledFlow m A (t + d) = m * A (t + d) := rfl
    _ ≤ m * (A t + α d) := by have := h t d; gcongr
    _ = m * A t + m * α d := mul_add m (A t) (α d)
    _ = scaledFlow m A t + scaledFlow m α d := rfl

/-- **Linear fix-point convergence criterion**: a positive-offset linear recursion `σ = c·σ + d`
(`d > 0`) has a solution in `ℝ≥0` iff the gain `c < 1`. This is the boundary `c = 1` of
network-calculus fix-point iterations (the §12.1 fix-point method; the cyclic scaling instability of
§12.4.2, where the per-flow burst recursion has gain `m₂m₄/((1−m₂)(1−m₄))`): below it the bound
`d/(1−c)` converges, at or above it the iteration diverges and no finite bound exists — local
stability of the constituent servers is *not* sufficient to make the network's fix-point converge. -/
theorem exists_linearFixpoint_iff {c d : ℝ≥0} (hd : 0 < d) :
    (∃ σ : ℝ≥0, σ = c * σ + d) ↔ c < 1 := by
  constructor
  · rintro ⟨σ, hσ⟩
    by_contra hcon
    rw [not_lt] at hcon
    have hσle : σ ≤ c * σ := le_mul_of_one_le_left (zero_le) hcon
    have hcontra : σ + d ≤ σ := by
      calc σ + d ≤ c * σ + d := by gcongr
        _ = σ := hσ.symm
    exact absurd hcontra (not_le.mpr (lt_add_of_pos_right σ hd))
  · intro hc
    have h1c : (0 : ℝ≥0) < 1 - c := tsub_pos_of_lt hc
    refine ⟨d / (1 - c), ?_⟩
    have hu : d / (1 - c) * (1 - c) = d := div_mul_cancel₀ d h1c.ne'
    have hcle : c * (d / (1 - c)) ≤ d / (1 - c) := mul_le_of_le_one_left (zero_le) hc.le
    rw [eq_comm]
    calc c * (d / (1 - c)) + d
        = c * (d / (1 - c)) + d / (1 - c) * (1 - c) := by rw [hu]
      _ = c * (d / (1 - c)) + (d / (1 - c) - d / (1 - c) * c) := by rw [mul_tsub, mul_one]
      _ = c * (d / (1 - c)) + (d / (1 - c) - c * (d / (1 - c))) := by rw [mul_comm (d / (1 - c)) c]
      _ = d / (1 - c) := add_tsub_cancel_of_le hcle

/-- **The §12.4.2 scaling-instability boundary**: the cyclic two-server scaling network's per-flow
burst gain `m₂m₄/((1−m₂)(1−m₄))` is below `1` iff `m₂ + m₄ < 1` (`m₂, m₄ < 1`). -/
theorem scaling_gain_lt_one_iff {m2 m4 : ℝ≥0} (h2 : m2 < 1) (h4 : m4 < 1) :
    m2 * m4 / ((1 - m2) * (1 - m4)) < 1 ↔ m2 + m4 < 1 := by
  have hden : (0 : ℝ≥0) < (1 - m2) * (1 - m4) := mul_pos (tsub_pos_of_lt h2) (tsub_pos_of_lt h4)
  rw [div_lt_one hden, ← NNReal.coe_lt_coe, ← NNReal.coe_lt_coe]
  push_cast [NNReal.coe_sub h2.le, NNReal.coe_sub h4.le]
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

/-- **The §12.4.2 cyclic scaling network's fix-point converges iff `m₂ + m₄ < 1`**: combining the
linear fix-point criterion with the scaling-gain boundary. The book's point: this is *strictly
stronger* than the local stability `m₁ + m₄ < 1 ∧ m₂ + m₃ < 1`, so a locally stable scaling network
can have a diverging fix-point (no finite network-calculus bound) — local stability is not sufficient
for the cyclic network's stability. -/
theorem exists_scalingFixpoint_iff {m2 m4 d : ℝ≥0} (h2 : m2 < 1) (h4 : m4 < 1) (hd : 0 < d) :
    (∃ σ : ℝ≥0, σ = m2 * m4 / ((1 - m2) * (1 - m4)) * σ + d) ↔ m2 + m4 < 1 := by
  rw [exists_linearFixpoint_iff hd, scaling_gain_lt_one_iff h2 h4]

/-- Substituting the `σ₂`-equation into the `σ₁`-equation of the §12.4.2 coupled burst recursion:
`1 + m₄(1 + m₂σ/(1−m₂))/(1−m₄)` collapses to the single-variable form `c·σ + d` with gain
`c = m₂m₄/((1−m₂)(1−m₄))` and offset `d = 1 + m₄/(1−m₄)`. The arithmetic is a field identity in the
positive denominators `1−m₂`, `1−m₄`, proved over `ℝ`. -/
theorem scalingFixpointPair_substitute {m2 m4 : ℝ≥0} (h2 : m2 < 1) (h4 : m4 < 1) (σ : ℝ≥0) :
    1 + m4 * (1 + m2 * σ / (1 - m2)) / (1 - m4)
      = m2 * m4 / ((1 - m2) * (1 - m4)) * σ + (1 + m4 / (1 - m4)) := by
  have ha : (m2 : ℝ) < 1 := by exact_mod_cast h2
  have hb : (m4 : ℝ) < 1 := by exact_mod_cast h4
  rw [← NNReal.coe_inj]
  push_cast [NNReal.coe_sub h2.le, NNReal.coe_sub h4.le]
  have ha' : (1 : ℝ) - m2 ≠ 0 := by linarith
  have hb' : (1 : ℝ) - m4 ≠ 0 := by linarith
  field_simp
  ring

/-- **The §12.4.2 coupled burst fix-point system is solvable iff `m₂ + m₄ < 1`** (the book's two
displayed equations, faithfully): the per-flow burstinesses `σ'₁`, `σ'₂` between the two servers solve
`σ'₁ = 1 + m₄σ'₂/(1−m₄)` and `σ'₂ = 1 + m₂σ'₁/(1−m₂)` (Corollary 5.3 / Theorem 7.1 / Lemma 12.6, with
`αᵢ = γ_{1,1}`) in `ℝ≥0` iff `m₂ + m₄ < 1`. Eliminating `σ'₂` collapses the system to the
single-variable fix-point of `exists_scalingFixpoint_iff`; below the threshold both bursts converge,
at or above it no finite pair exists. -/
theorem exists_scalingFixpointPair_iff {m2 m4 : ℝ≥0} (h2 : m2 < 1) (h4 : m4 < 1) :
    (∃ σ1 σ2 : ℝ≥0, σ1 = 1 + m4 * σ2 / (1 - m4) ∧ σ2 = 1 + m2 * σ1 / (1 - m2)) ↔ m2 + m4 < 1 := by
  have hd : (0 : ℝ≥0) < 1 + m4 / (1 - m4) := by positivity
  constructor
  · rintro ⟨σ1, σ2, h1, h2eq⟩
    rw [h2eq, scalingFixpointPair_substitute h2 h4 σ1] at h1
    exact (scaling_gain_lt_one_iff h2 h4).mp ((exists_linearFixpoint_iff hd).mp ⟨σ1, h1⟩)
  · intro hlt
    obtain ⟨σ1, hσ1⟩ :=
      (exists_linearFixpoint_iff hd).mpr ((scaling_gain_lt_one_iff h2 h4).mpr hlt)
    exact ⟨σ1, 1 + m2 * σ1 / (1 - m2), by rw [scalingFixpointPair_substitute h2 h4 σ1]; exact hσ1, rfl⟩

/-- **The diverging fix-point iteration**: with gain `c ≥ 1` and positive offset `d > 0`, the
network-calculus fix-point iteration `σₙ₊₁ = c·σₙ + d` is unbounded (every `M` is exceeded) — it
grows at least linearly (`σₙ ≥ n·d`), so no finite bound exists. The dynamic counterpart of
`exists_linearFixpoint_iff` (which rules out a *static* fixed point). -/
theorem linearIterate_unbounded {c d : ℝ≥0} (hc : 1 ≤ c) (hd : 0 < d) (σ₀ M : ℝ≥0) :
    ∃ n : ℕ, M ≤ (fun σ => c * σ + d)^[n] σ₀ := by
  have hge : ∀ n : ℕ, (n : ℝ≥0) * d ≤ (fun σ => c * σ + d)^[n] σ₀ := by
    intro n; induction n with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have h1 : (fun σ => c * σ + d)^[k] σ₀ ≤ c * (fun σ => c * σ + d)^[k] σ₀ :=
        le_mul_of_one_le_left (zero_le) hc
      calc ((k + 1 : ℕ) : ℝ≥0) * d = (k : ℝ≥0) * d + d := by push_cast; ring
        _ ≤ (fun σ => c * σ + d)^[k] σ₀ + d := by gcongr
        _ ≤ c * (fun σ => c * σ + d)^[k] σ₀ + d := by gcongr
  obtain ⟨n, hn⟩ := exists_nat_ge (M / d)
  refine ⟨n, le_trans ?_ (hge n)⟩
  calc M = M / d * d := (div_mul_cancel₀ M (ne_of_gt hd)).symm
    _ ≤ (n : ℝ≥0) * d := by gcongr

/-- **The §12.4.2 cyclic scaling network's NC iteration diverges when `m₂ + m₄ ≥ 1`**: in the unstable
regime the per-flow burst iteration is unbounded, so the network-calculus method yields no finite
end-to-end bound — even where local stability `m₁ + m₄ < 1 ∧ m₂ + m₃ < 1` may still hold. -/
theorem scalingIterate_unbounded {m2 m4 d : ℝ≥0} (h2 : m2 < 1) (h4 : m4 < 1)
    (hge : 1 ≤ m2 + m4) (hd : 0 < d) (σ₀ M : ℝ≥0) :
    ∃ n : ℕ, M ≤ (fun σ => m2 * m4 / ((1 - m2) * (1 - m4)) * σ + d)^[n] σ₀ :=
  linearIterate_unbounded (not_lt.mp fun h => absurd ((scaling_gain_lt_one_iff h2 h4).mp h)
    (not_lt.mpr hge)) hd σ₀ M

/-- **Local stability does not imply cyclic fix-point convergence** (§12.4.2, the punchline): for every
threshold `M` there is a *locally stable* parameter choice (`m₁+m₄ < 1 ∧ m₂+m₃ < 1`) whose per-flow
burst iteration `σₙ₊₁ = (m₂m₄/((1−m₂)(1−m₄)))·σₙ + d` exceeds `M` — so the network-calculus method has
no finite end-to-end bound even though every server is locally stable. Witness `m₁ = m₃ = 0`,
`m₂ = m₄ = ½` (gain `= 1`): local stability `m₁+m₄ < 1 ∧ m₂+m₃ < 1` is strictly weaker than the
fix-point convergence `m₂+m₄ < 1`. -/
theorem exists_locallyStable_scalingIterate_unbounded (d σ₀ M : ℝ≥0) (hd : 0 < d) :
    ∃ m1 m2 m3 m4 : ℝ≥0, (m1 + m4 < 1 ∧ m2 + m3 < 1) ∧ m2 < 1 ∧ m4 < 1 ∧
      ∃ n : ℕ, M ≤ (fun σ => m2 * m4 / ((1 - m2) * (1 - m4)) * σ + d)^[n] σ₀ := by
  refine ⟨0, 1 / 2, 0, 1 / 2, ⟨by norm_num, by norm_num⟩, by norm_num, by norm_num, ?_⟩
  exact scalingIterate_unbounded (by norm_num) (by norm_num) (by norm_num) hd σ₀ M

/-- Faithfulness check against the book's §12.4.2 display: the coupled burst system
`σ₁' = 1 + m₄σ₂'/(1−m₄)`, `σ₂' = 1 + m₂σ₁'/(1−m₂)` is solvable iff `m₂ + m₄ < 1`. -/
example {m2 m4 : ℝ≥0} (h2 : m2 < 1) (h4 : m4 < 1) :
    (∃ σ1 σ2 : ℝ≥0, σ1 = 1 + m4 * σ2 / (1 - m4) ∧ σ2 = 1 + m2 * σ1 / (1 - m2)) ↔ m2 + m4 < 1 :=
  exists_scalingFixpointPair_iff h2 h4

end DeepWiki
