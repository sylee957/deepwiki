import Mathlib.Data.Real.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Order.CompleteLattice.Basic
import DeepWiki.NetworkCalculus.DeviationsBoundsTight

/-! # Worst-case performance by linear / mixed-integer programming
Two pieces of the tight-worst-case theory. First, the worst-case value of a
performance program is the **optimum** of its objective over the feasible
configurations — and that optimum is precisely the *least upper bound* of the
realized objective, so "the optimum equals the worst case" (Theorems 11.1 and
11.2) is the `IsLUB` characterization `isLUB_programOptimum`. Second, the big-M
Boolean-ordering encoding (Lemma 11.1) that linearises the FIFO service-order
choice into a mixed-integer linear program. (What is *not* formalized here is
that this worst-case optimum is computed by a *finite* linear/mixed-integer
program — the §11.1.2/§11.2.2 construction with its `O(nm)` variables — which is
the modeling content of the equivalence theorems.) -/

namespace DeepWiki

/-- The **optimum** of a worst-case performance program: the supremum of the
objective `obj` over the feasible configurations `{c | Feasible c}`. For the
worst-case delay (resp. backlog) program of a tandem network, `Feasible` is the
network-calculus constraint set (monotonicity, causality, arrival `α`, service
`β`) on a trajectory and `obj` the realized delay (resp. backlog); the optimum
is the worst-case value. -/
noncomputable def programOptimum {ι : Type*} (Feasible : ι → Prop)
    (obj : ι → EReal) : EReal :=
  ⨆ c : {c // Feasible c}, obj c.1

/-- A realizable (feasible) configuration's objective lies below the optimum:
every achievable delay/backlog lower-bounds the worst case. -/
theorem le_programOptimum {ι : Type*} {Feasible : ι → Prop} {obj : ι → EReal}
    {c : ι} (hc : Feasible c) : obj c ≤ programOptimum Feasible obj :=
  le_iSup (fun c : {c // Feasible c} => obj c.1) ⟨c, hc⟩

/-- The optimum is the least upper bound: any value bounding the objective on
every feasible configuration bounds the optimum (worst-case tightness). -/
theorem programOptimum_le {ι : Type*} {Feasible : ι → Prop} {obj : ι → EReal}
    {B : EReal} (h : ∀ c, Feasible c → obj c ≤ B) :
    programOptimum Feasible obj ≤ B :=
  iSup_le fun c => h c.1 c.2

/-- **The optimum is the worst case** (the `IsLUB` form of Theorems 11.1/11.2):
the program optimum is the least upper bound of the objective over the feasible
configurations — an upper bound on every realizable delay/backlog and the
tightest one. -/
theorem isLUB_programOptimum {ι : Type*} (Feasible : ι → Prop) (obj : ι → EReal) :
    IsLUB (Set.range fun c : {c // Feasible c} => obj c.1)
      (programOptimum Feasible obj) :=
  isLUB_iSup

open scoped NNReal ENNReal

/-- A feasible single-server trajectory for a flow with arrival curve `α` under
a min-plus service curve `β`: `A` is monotone and `α`-arrival-constrained, and
`(A, D)` is served by `β` (`A ∗ β ≤ D` in the `ℝ≥0∞` reading). These are exactly
the network-calculus constraints of the single-node worst-case program. -/
def ServerFeasible (α : ℝ≥0 → ℝ≥0) (β : ℝ≥0 → ℝ≥0∞) (A D : ℝ≥0 → ℝ≥0) : Prop :=
  Monotone A ∧ IsMaximalArrivalBound (Deviation.liftENN A) (Deviation.liftENN α) ∧
    ∀ t, minConv (Deviation.liftENN A) β t ≤ (D t : ℝ≥0∞)

/-- The worst-case delay of a single server: the supremum of the realized delay
over every feasible (`α`-arrival-constrained, `β`-served) trajectory — the
optimum of the single-node worst-case program. -/
noncomputable def worstCaseServerDelay (α : ℝ≥0 → ℝ≥0) (β : ℝ≥0 → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ p : {p : (ℝ≥0 → ℝ≥0) × (ℝ≥0 → ℝ≥0) // ServerFeasible α β p.1 p.2},
    Deviation.delay p.1.1 p.1.2

/-- **Single-server worst-case delay = horizontal deviation** (the genuine
optimum-equals-worst-case for one node): for monotone sub-additive `α ∈ ℱ₀` and
monotone `β ∈ ℱ₀`, `worstCaseServerDelay α β = hDev(α, β)`. The bound
`delay ≤ hDev` holds on *every* feasible trajectory (so it bounds the
supremum), and the greedy pair `(α, α ∗ β)` is feasible and *attains* it (so the
supremum reaches it). Thus the worst case over the infinite feasible set is the
concrete closed-form value `hDev(α, β)`. -/
theorem worstCaseServerDelay_eq_hDev {α : ℝ≥0 → ℝ≥0} {β : ℝ≥0 → ℝ≥0∞}
    (hαmono : Monotone α) (hα0 : IsNullAtOrigin α) (hαsub : IsSubadditive α)
    (hβmono : Monotone β) (hβ0 : β 0 = 0) :
    worstCaseServerDelay α β = (hDev (Deviation.liftENN α) β : ℝ≥0∞) := by
  apply le_antisymm
  · -- every feasible trajectory's delay is below the bound
    refine iSup_le fun p => ?_
    obtain ⟨hA, harr, hserv⟩ := p.2
    exact Deviation.delay_le_hDev hA hβmono harr hserv
  · -- the greedy pair `(α, α ∗ β)` is feasible and attains the bound
    have hle : ∀ t, minConv (Deviation.liftENN α) β t ≤ (α t : ℝ≥0∞) := fun t => by
      have h := minConv_le_add (Deviation.liftENN α) β (add_zero t)
      rwa [hβ0, add_zero] at h
    have hne : ∀ t, minConv (Deviation.liftENN α) β t ≠ ⊤ := fun t =>
      ne_top_of_le_ne_top (ENNReal.coe_ne_top (r := α t)) (hle t)
    set D : ℝ≥0 → ℝ≥0 := fun t => (minConv (Deviation.liftENN α) β t).toNNReal with hDdef
    have hD : ∀ t, (D t : ℝ≥0∞) = minConv (Deviation.liftENN α) β t := fun t =>
      ENNReal.coe_toNNReal (hne t)
    have harr : IsMaximalArrivalBound (Deviation.liftENN α) (Deviation.liftENN α) :=
      isMaximalArrivalBound_self_of_subadditive hαsub.liftENN
    have hfeas : ServerFeasible α β α D := ⟨hαmono, harr, fun t => (hD t).ge⟩
    have hdelay : Deviation.delay α D = (hDev (Deviation.liftENN α) β : ℝ≥0∞) :=
      Deviation.delay_eq_hDev_of_minConv_eq hαmono hα0 hαsub hβmono hD
    rw [← hdelay]
    exact le_iSup
      (fun p : {p : (ℝ≥0 → ℝ≥0) × (ℝ≥0 → ℝ≥0) // ServerFeasible α β p.1 p.2} =>
        Deviation.delay p.1.1 p.1.2) ⟨(α, D), hfeas⟩

/-- **Lemma 11.1** (the big-M Boolean ordering): with a `0/1` selector `b` and
the four big-M constraints `x₁+(1−b)M ≥ x₂`, `x₂+bM ≥ x₁`, `y₁+(1−b)M ≥ y₂`,
`y₂+bM ≥ y₁`, a strict order on `(x₁,x₂)` forces `b` and hence the matching
order on `(y₁,y₂)`: `x₁ < x₂ ⟹ b = 0 ∧ y₁ ≤ y₂`, and `x₂ < x₁ ⟹ b = 1 ∧ y₂ ≤ y₁`.
(The book also bounds the values in `[0,M]` for the surrounding LP's
well-formedness; the ordering implication needs only the constraints above.) -/
theorem bigM_ordering {x₁ x₂ y₁ y₂ M b : ℝ}
    (h1 : x₁ + (1 - b) * M ≥ x₂) (h2 : x₂ + b * M ≥ x₁)
    (h3 : y₁ + (1 - b) * M ≥ y₂) (h4 : y₂ + b * M ≥ y₁)
    (hb : b = 0 ∨ b = 1) :
    (x₁ < x₂ → b = 0 ∧ y₁ ≤ y₂) ∧ (x₂ < x₁ → b = 1 ∧ y₂ ≤ y₁) := by
  rcases hb with rfl | rfl <;>
    simp only [sub_zero, sub_self, one_mul, zero_mul, add_zero, ge_iff_le] at h1 h2 h3 h4
  · exact ⟨fun _ => ⟨rfl, h4⟩, fun hlt => absurd h2 (not_le.mpr hlt)⟩
  · exact ⟨fun hlt => absurd h1 (not_le.mpr hlt), fun _ => ⟨rfl, h3⟩⟩

end DeepWiki
