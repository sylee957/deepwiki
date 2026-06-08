import Book.FunctionDioids
import Book.NdClosure

/-!
(min,plus) convolution specialized to real (`ℝ≥0`) functions:
non-decreasing and super-additive closures via max-plus convolution, and the
(min,+) sub-additive closure.
-/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge

/-- `ndClosure beta` equals the max-plus convolution `maxConv beta 0`. -/
theorem ndClosure_eq_maxConv (beta : ℝ≥0 → ℝ≥0) :
    ndClosure beta = maxConv beta 0 := by
  funext t
  have hrange :
      Set.range
          (fun u : {u : ℝ≥0 // u ≤ t} => beta u.1)
        = Set.range
          (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
            beta p.1.1) := by
    ext x
    constructor
    · rintro ⟨⟨u, hu⟩, rfl⟩
      exact ⟨⟨(u, t - u),
        add_tsub_cancel_of_le hu⟩, rfl⟩
    · rintro ⟨⟨⟨u, s⟩, hus⟩, rfl⟩
      exact ⟨⟨u, hus ▸ le_self_add⟩, rfl⟩
  unfold ndClosure maxConv
  simp only [Pi.zero_apply, add_zero]
  exact congrArg sSup hrange

/-- Joining with `0` is a no-op for `ℝ≥0`-valued functions. -/
theorem sup_zero_eq_self {D : Type*} (beta : D → ℝ≥0) :
    (fun t => beta t ⊔ 0) = beta := by
  funext t
  exact sup_eq_left.mpr zero_le'

/-- `n`-fold `maxConvProj` self-convolution iterate of `beta`. -/
noncomputable def maxConvProjPow (beta : ℝ≥0 → ℝ≥0) :
    ℕ → (ℝ≥0 → ℝ≥0)
  | 0 => beta
  | n + 1 =>
      maxConvProj (maxConvProjPow beta n)
        (maxConvProjPow beta n)

/-- (max,+) super-additive closure: supremum of all `maxConvProjPow`
iterates. -/
noncomputable def superAdditiveClosureMax (beta : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t => ⨆ n : ℕ, maxConvProjPow beta n t

/-- `beta` is below its super-additive closure `superAdditiveClosureMax beta`. -/
theorem le_superAdditiveClosureMax (beta : ℝ≥0 → ℝ≥0)
    (hbdd : ∀ t, BddAbove
      (Set.range (fun n => maxConvProjPow beta n t)))
    (t : ℝ≥0) : beta t ≤ superAdditiveClosureMax beta t := by
  unfold superAdditiveClosureMax
  exact le_ciSup (hbdd t) 0

/-- `n`-fold (min,+) self-convolution iterate of `beta`, indexed from `beta`:
`minConvProjPow beta 0 = beta`, `minConvProjPow beta (n+1) = beta ∗ ·`. Indexing
from `beta` (not the `+∞`-valued unit `δ₀`) keeps the iterate `ℝ≥0`-valued. -/
noncomputable def minConvProjPow (beta : ℝ≥0 → ℝ≥0) :
    ℕ → (ℝ≥0 → ℝ≥0)
  | 0 => beta
  | n + 1 => minConvProj beta (minConvProjPow beta n)

/-- (min,+) sub-additive closure: pointwise infimum of all `minConvProjPow`
iterates, `⨅ₙ minConvProjPow beta n t`. -/
noncomputable def subadditiveClosureMin (beta : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t => ⨅ n : ℕ, minConvProjPow beta n t

/-- The closure is below `beta`: `subadditiveClosureMin beta t ≤ beta t`, as the
`n = 0` term of the infimum. -/
theorem subadditiveClosureMin_le (beta : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    subadditiveClosureMin beta t ≤ beta t :=
  ciInf_le (OrderBot.bddBelow _) 0

end DeepWiki
