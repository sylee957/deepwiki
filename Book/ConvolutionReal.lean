import Book.FunctionDioids
import Book.ClosureNd
import Book.Additivity

/-!
(min,plus) convolution specialized to real (`ℝ≥0`) functions:
non-decreasing and super-additive closures via max-plus convolution, and the
(min,+) sub-additive closure.
-/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge

/-- `ndClosure beta` equals the max-plus convolution `maxConv beta 0`, over
any conditionally complete codomain with additive zero. -/
theorem ndClosure_eq_maxConv {T : Type*} [ConditionallyCompleteLattice T]
    [AddZeroClass T] (beta : ℝ≥0 → T) :
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

/-- `n`-fold `maxConvProj` self-convolution iterate of `beta`. -/
noncomputable def maxConvProjPow (beta : ℝ≥0 → ℝ≥0) :
    ℕ → (ℝ≥0 → ℝ≥0)
  | 0 => beta
  | n + 1 =>
      maxConvProj (maxConvProjPow beta n)
        (maxConvProjPow beta n)

/-- (max,+) super-additive closure: supremum of all `maxConvProjPow`
iterates. -/
noncomputable def superadditiveClosureMax (beta : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t => ⨆ n : ℕ, maxConvProjPow beta n t

/-- `beta` is below its super-additive closure `superadditiveClosureMax beta`. -/
theorem le_superadditiveClosureMax (beta : ℝ≥0 → ℝ≥0)
    (hbdd : ∀ t, BddAbove
      (Set.range (fun n => maxConvProjPow beta n t)))
    (t : ℝ≥0) : beta t ≤ superadditiveClosureMax beta t := by
  unfold superadditiveClosureMax
  exact le_ciSup (hbdd t) 0

/-- Under an affine bound `beta s ≤ r * s`, each self-convolution iterate stays
below `r * ·`: `maxConvProjPow beta n t ≤ r * t`, since `r * a + r * b = r * t`
on any split `a + b = t`. -/
theorem maxConvProjPow_le_of_affine_bound {beta : ℝ≥0 → ℝ≥0} {r : ℝ≥0}
    (hr : ∀ s, beta s ≤ r * s) (n : ℕ) (t : ℝ≥0) :
    maxConvProjPow beta n t ≤ r * t := by
  induction n generalizing t with
  | zero => exact hr t
  | succ n ih =>
    show maxConvProj (maxConvProjPow beta n) (maxConvProjPow beta n) t ≤ r * t
    refine maxConvProj_le _ _ t (r * t) (fun p => ?_)
    obtain ⟨⟨a, b⟩, (hab : a + b = t)⟩ := p
    calc maxConvProjPow beta n a + maxConvProjPow beta n b
        ≤ r * a + r * b := add_le_add (ih a) (ih b)
      _ = r * (a + b) := (mul_add r a b).symm
      _ = r * t := by rw [hab]

/-- Under an affine bound, the iterate range at each `t` is bounded above
by `r * t`. -/
theorem bddAbove_range_maxConvProjPow_of_affine_bound {beta : ℝ≥0 → ℝ≥0}
    {r : ℝ≥0} (hr : ∀ s, beta s ≤ r * s) (t : ℝ≥0) :
    BddAbove (Set.range fun n => maxConvProjPow beta n t) :=
  ⟨r * t, by
    rintro x ⟨n, rfl⟩
    exact maxConvProjPow_le_of_affine_bound hr n t⟩

/-- Under an affine bound, a splitting bounds the next self-convolution
iterate from below:
`maxConvProjPow beta n a + maxConvProjPow beta n b ≤
maxConvProjPow beta (n + 1) (a + b)`. -/
theorem maxConvProjPow_add_le_succ_of_affine_bound {beta : ℝ≥0 → ℝ≥0}
    {r : ℝ≥0} (hr : ∀ s, beta s ≤ r * s) (n : ℕ) (a b : ℝ≥0) :
    maxConvProjPow beta n a + maxConvProjPow beta n b
      ≤ maxConvProjPow beta (n + 1) (a + b) := by
  have hbound : ∀ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = a + b},
      maxConvProjPow beta n p.1.1 + maxConvProjPow beta n p.1.2
        ≤ r * (a + b) :=
    fun p => by
      calc maxConvProjPow beta n p.1.1 + maxConvProjPow beta n p.1.2
          ≤ r * p.1.1 + r * p.1.2 :=
            add_le_add (maxConvProjPow_le_of_affine_bound hr n _)
              (maxConvProjPow_le_of_affine_bound hr n _)
        _ = r * (a + b) := by rw [← mul_add, p.2]
  exact le_maxConvProj_of_bound hbound ⟨(a, b), rfl⟩

/-- Under an affine bound, the self-convolution iterates are non-decreasing
in the index: the `(t, 0)` splitting. -/
theorem maxConvProjPow_le_succ_of_affine_bound {beta : ℝ≥0 → ℝ≥0} {r : ℝ≥0}
    (hr : ∀ s, beta s ≤ r * s) (n : ℕ) (t : ℝ≥0) :
    maxConvProjPow beta n t ≤ maxConvProjPow beta (n + 1) t := by
  have h := maxConvProjPow_add_le_succ_of_affine_bound hr n t 0
  rw [add_zero] at h
  exact le_self_add.trans h

/-- Under an affine bound, the self-convolution iterates are monotone in the
index. -/
theorem maxConvProjPow_le_maxConvProjPow_of_affine_bound
    {beta : ℝ≥0 → ℝ≥0} {r : ℝ≥0} (hr : ∀ s, beta s ≤ r * s)
    {n m : ℕ} (hnm : n ≤ m) (t : ℝ≥0) :
    maxConvProjPow beta n t ≤ maxConvProjPow beta m t := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih =>
      exact ih.trans (maxConvProjPow_le_succ_of_affine_bound hr m t)

/-- Under an affine bound, `beta` is below its super-additive closure (the
iterate range is bounded, so the supremum is not junk). -/
theorem le_superadditiveClosureMax_of_affine_bound {beta : ℝ≥0 → ℝ≥0}
    (hr : ∃ r : ℝ≥0, ∀ s, beta s ≤ r * s) (t : ℝ≥0) :
    beta t ≤ superadditiveClosureMax beta t := by
  obtain ⟨r, hr⟩ := hr
  exact le_superadditiveClosureMax beta
    (bddAbove_range_maxConvProjPow_of_affine_bound hr) t

/-- **Super-additivity of the closure.** Under an affine bound on `beta`,
the super-additive closure `superadditiveClosureMax beta` is super-additive:
two iterates at `u` and `s` are dominated by the next iterate at `u + s`. -/
theorem isSuperadditive_superadditiveClosureMax_of_affine_bound
    {beta : ℝ≥0 → ℝ≥0} (hr : ∃ r : ℝ≥0, ∀ s, beta s ≤ r * s) :
    IsSuperadditive (superadditiveClosureMax beta) := by
  obtain ⟨r, hr⟩ := hr
  intro u s
  show (⨆ n : ℕ, maxConvProjPow beta n u) + (⨆ n : ℕ, maxConvProjPow beta n s)
    ≤ superadditiveClosureMax beta (u + s)
  rw [add_comm]
  refine add_ciSup_le _ _ _ fun n => ?_
  rw [add_comm]
  refine add_ciSup_le _ _ _ fun m => ?_
  calc maxConvProjPow beta n u + maxConvProjPow beta m s
      ≤ maxConvProjPow beta (max n m) u + maxConvProjPow beta (max n m) s :=
        add_le_add
          (maxConvProjPow_le_maxConvProjPow_of_affine_bound hr
            (le_max_left n m) u)
          (maxConvProjPow_le_maxConvProjPow_of_affine_bound hr
            (le_max_right n m) s)
    _ ≤ maxConvProjPow beta (max n m + 1) (u + s) :=
        maxConvProjPow_add_le_succ_of_affine_bound hr (max n m) u s
    _ ≤ superadditiveClosureMax beta (u + s) :=
        le_ciSup (bddAbove_range_maxConvProjPow_of_affine_bound hr (u + s))
          (max n m + 1)

/-- Under an affine bound, the self-convolution iterates of a monotone `beta`
are monotone: a splitting of `t` widens to a splitting of `t' ≥ t`. -/
theorem monotone_maxConvProjPow_of_affine_bound {beta : ℝ≥0 → ℝ≥0} {r : ℝ≥0}
    (hmono : Monotone beta) (hr : ∀ s, beta s ≤ r * s) (n : ℕ) :
    Monotone (maxConvProjPow beta n) := by
  induction n with
  | zero => exact hmono
  | succ n ih =>
      intro t t' htt
      refine maxConvProj_le _ _ t (maxConvProjPow beta (n + 1) t')
        fun p => ?_
      have hsplit : p.1.1 + (p.1.2 + (t' - t)) = t' := by
        rw [← add_assoc, p.2, add_tsub_cancel_of_le htt]
      calc maxConvProjPow beta n p.1.1 + maxConvProjPow beta n p.1.2
          ≤ maxConvProjPow beta n p.1.1
              + maxConvProjPow beta n (p.1.2 + (t' - t)) :=
            add_le_add le_rfl (ih le_self_add)
        _ ≤ maxConvProjPow beta (n + 1) (p.1.1 + (p.1.2 + (t' - t))) :=
            maxConvProjPow_add_le_succ_of_affine_bound hr n _ _
        _ = maxConvProjPow beta (n + 1) t' := by rw [hsplit]

/-- Under an affine bound, the super-additive closure of a monotone `beta`
is monotone. -/
theorem monotone_superadditiveClosureMax_of_affine_bound
    {beta : ℝ≥0 → ℝ≥0} (hmono : Monotone beta)
    (hr : ∃ r : ℝ≥0, ∀ s, beta s ≤ r * s) :
    Monotone (superadditiveClosureMax beta) := by
  obtain ⟨r, hr⟩ := hr
  intro t t' htt
  show (⨆ n : ℕ, maxConvProjPow beta n t)
    ≤ ⨆ n : ℕ, maxConvProjPow beta n t'
  refine ciSup_le fun n => ?_
  exact (monotone_maxConvProjPow_of_affine_bound hmono hr n htt).trans
    (le_ciSup (bddAbove_range_maxConvProjPow_of_affine_bound hr t') n)

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
