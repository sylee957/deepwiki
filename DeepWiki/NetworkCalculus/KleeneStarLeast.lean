import DeepWiki.NetworkCalculus.Closures
import DeepWiki.NetworkCalculus.Additivity

/-! # Theorem 2.3: the Kleene star is the least solution of `x = a x ⊕ b`
The Kleene-star theorem in the `(min,+)` function dioid. Its sum `⊕` is `⊓` and its canonical order
is the *reverse* of the numeric one, so the dioid-**least** solution of `x = a ∗ x ⊕ b` is the
numeric-**greatest** fixpoint, and it is `a⋆ ∗ b = minConv (subadditiveClosureENN a) b` (with
`a⋆ = subadditiveClosureENN a`, Def 2.9). The hard "least" half reuses the unconditional feedback
bound `le_minConv_subadditiveClosureENN_of_le_inf`. -/

namespace DeepWiki

open scoped NNReal ENNReal

variable {D : Type} [_root_.AddCommMonoid D]

/-- The Kleene star is a sub-solution: `a⋆ ≤ a ∗ a⋆` (`(min,+)`, pointwise). -/
theorem subadditiveClosureENN_le_minConv_self (w : D → ℝ≥0∞) (s : D) :
    subadditiveClosureENN w s ≤ minConv w (subadditiveClosureENN w) s := by
  rw [minConv_subadditiveClosureENN_eq_iInf, subadditiveClosureENN_eq_iInf]
  refine le_iInf fun n => ?_
  rw [show minConv w (minConvPow w n) s = minConvPow w (n + 1) s from by
    rw [minConvPow_succ, minConv_comm]]
  exact iInf_le _ (n + 1)

/-- `a⋆ ∗ b` is a fixpoint of `x ↦ a ∗ x ⊕ b` (`(min,+)`): it solves `x = a ∗ x ⊓ b`. -/
theorem minConv_subadditiveClosureENN_fixpoint (w b : D → ℝ≥0∞) :
    minConv (subadditiveClosureENN w) b
      = minConv w (minConv (subadditiveClosureENN w) b) ⊓ b := by
  funext t
  rw [Pi.inf_apply]
  apply le_antisymm
  · refine le_inf ?_ ?_
    · rw [← minConv_assoc_enn]
      exact minConv_le_minConv (subadditiveClosureENN_le_minConv_self w) (fun _ => le_rfl) t
    · refine (minConv_le_add (subadditiveClosureENN w) b (zero_add t)).trans_eq ?_
      rw [subadditiveClosureENN_zero_eq, zero_add]
  · have hRHS : minConv (subadditiveClosureENN w) b t
        = ⨅ n, minConv (minConvPow w n) b t := by
      rw [minConv_comm, minConv_subadditiveClosureENN_eq_iInf]
      exact iInf_congr fun n => congrFun (minConv_comm b (minConvPow w n)) t
    rw [hRHS]
    refine le_iInf fun n => ?_
    cases n with
    | zero =>
        rw [show minConv (minConvPow w 0) b t = b t from by
          rw [minConv_comm, minConv_minConvPow_zero]]
        exact inf_le_right
    | succ n =>
        refine inf_le_left.trans ?_
        calc minConv w (minConv (subadditiveClosureENN w) b) t
            ≤ minConv w (minConv (minConvPow w n) b) t := by
              refine minConv_le_minConv (fun _ => le_rfl) (fun s => ?_) t
              exact minConv_le_minConv
                (fun s' => by rw [subadditiveClosureENN_eq_iInf]; exact iInf_le _ n)
                (fun _ => le_rfl) s
          _ = minConv (minConvPow w (n + 1)) b t := by
              rw [← minConv_assoc_enn, minConv_comm w (minConvPow w n), ← minConvPow_succ]

/-- **Theorem 2.3** (Kleene star theorem, `(min,+)` form): `a⋆ ∗ b` is the greatest fixpoint of
`x ↦ a ∗ x ⊓ b` — equivalently, since the dioid order is the reverse of the numeric one, the
**least** solution of `x = a ∗ x ⊕ b` in the dioid. The "is a fixpoint" half is
`minConv_subadditiveClosureENN_fixpoint`; the upper bound is the unconditional feedback lemma. -/
theorem isGreatest_minConv_subadditiveClosureENN (w b : D → ℝ≥0∞) :
    IsGreatest {x : D → ℝ≥0∞ | x = minConv w x ⊓ b}
      (minConv (subadditiveClosureENN w) b) := by
  refine ⟨minConv_subadditiveClosureENN_fixpoint w b, fun x hx t => ?_⟩
  have hle : ∀ s, x s ≤ b s ⊓ minConv x w s := fun s => by
    rw [show x s = minConv w x s ⊓ b s from by rw [congrFun hx s, Pi.inf_apply]]
    exact le_inf inf_le_right (inf_le_left.trans_eq (congrFun (minConv_comm w x) s))
  exact (le_minConv_subadditiveClosureENN_of_le_inf hle t).trans_eq
    (congrFun (minConv_comm b (subadditiveClosureENN w)) t)

-- Restatement (book Thm 2.3): `a⋆ ∗ b` solves `x = a ∗ x ⊕ b` and dominates every solution.
example (a b : ℝ≥0 → ℝ≥0∞) :
    minConv (subadditiveClosureENN a) b
        = minConv a (minConv (subadditiveClosureENN a) b) ⊓ b
      ∧ ∀ x, x = minConv a x ⊓ b → x ≤ minConv (subadditiveClosureENN a) b :=
  ⟨(isGreatest_minConv_subadditiveClosureENN a b).1,
   fun _ hx => (isGreatest_minConv_subadditiveClosureENN a b).2 hx⟩

end DeepWiki
