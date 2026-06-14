import Mathlib.Data.Real.Basic

/-! # Worst-case performance by linear / mixed-integer programming
The big-M Boolean-ordering encoding (Lemma 11.1) that linearises the FIFO
service-order choice into a mixed-integer linear program: a `0/1` variable `b`
ties the order of `(x₁, x₂)` to the order of `(y₁, y₂)` through four big-M
constraints. (The full LP/MILP feasible-trajectory model and the
optimum-equals-worst-case theorems — Theorem 11.1 for arbitrary multiplexing
and Theorem 11.2 for the FIFO policy — build a trajectory-optimization layer
on top of this and are not formalized here.) -/

namespace DeepWiki

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
