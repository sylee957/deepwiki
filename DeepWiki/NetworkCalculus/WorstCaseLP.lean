import Mathlib.Data.Real.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Order.CompleteLattice.Basic

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
