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
    refine maxConvProj_le fun a b hab => ?_
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

/-! ## The super-additive closure on the `ℝ≥0∞` carrier
The `ℝ≥0` closure above needs the affine bound only because unbounded
`ℝ≥0` suprema collapse to junk; on the complete carrier `ℝ≥0∞` (the
book's `R⁺ ∪ {+∞}`) the closure and all its properties are
unconditional. -/

/-- `n`-fold `maxConv` self-convolution iterate on the `ℝ≥0∞` carrier. -/
noncomputable def maxConvPow (beta : ℝ≥0 → ℝ≥0∞) : ℕ → (ℝ≥0 → ℝ≥0∞)
  | 0 => beta
  | n + 1 => maxConv (maxConvPow beta n) (maxConvPow beta n)

/-- (max,+) super-additive closure on the `ℝ≥0∞` carrier: supremum of all
`maxConvPow` iterates (`+∞` allowed, so no boundedness is needed). -/
noncomputable def superadditiveClosureMaxNN (beta : ℝ≥0 → ℝ≥0∞) :
    ℝ≥0 → ℝ≥0∞ :=
  fun t => ⨆ n : ℕ, maxConvPow beta n t

/-- `beta` is below its `ℝ≥0∞` super-additive closure, unconditionally. -/
theorem le_superadditiveClosureMaxNN (beta : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    beta t ≤ superadditiveClosureMaxNN beta t :=
  le_iSup (fun n => maxConvPow beta n t) 0

/-- The `ℝ≥0∞` iterates are non-decreasing in the index: the `(t, 0)`
splitting. -/
theorem maxConvPow_le_succ (beta : ℝ≥0 → ℝ≥0∞) (n : ℕ) (t : ℝ≥0) :
    maxConvPow beta n t ≤ maxConvPow beta (n + 1) t :=
  le_self_add.trans (add_le_maxConv _ _ (add_zero t))

/-- The `ℝ≥0∞` iterates are monotone in the index. -/
theorem maxConvPow_le_maxConvPow (beta : ℝ≥0 → ℝ≥0∞)
    {n m : ℕ} (hnm : n ≤ m) (t : ℝ≥0) :
    maxConvPow beta n t ≤ maxConvPow beta m t := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => exact ih.trans (maxConvPow_le_succ beta m t)

/-- **Super-additivity of the `ℝ≥0∞` closure**, unconditional: two iterates
at `u` and `s` are dominated by the next iterate at `u + s`. -/
theorem isSuperadditive_superadditiveClosureMaxNN (beta : ℝ≥0 → ℝ≥0∞) :
    IsSuperadditive (superadditiveClosureMaxNN beta) := by
  intro u s
  show (⨆ n : ℕ, maxConvPow beta n u) + (⨆ n : ℕ, maxConvPow beta n s)
    ≤ superadditiveClosureMaxNN beta (u + s)
  refine ENNReal.iSup_add_iSup_le fun n m => ?_
  calc maxConvPow beta n u + maxConvPow beta m s
      ≤ maxConvPow beta (max n m) u + maxConvPow beta (max n m) s :=
        add_le_add (maxConvPow_le_maxConvPow beta (le_max_left n m) u)
          (maxConvPow_le_maxConvPow beta (le_max_right n m) s)
    _ ≤ maxConvPow beta (max n m + 1) (u + s) := add_le_maxConv _ _ rfl
    _ ≤ superadditiveClosureMaxNN beta (u + s) :=
        le_iSup (fun k => maxConvPow beta k (u + s)) (max n m + 1)

/-- The `ℝ≥0∞` closure of a monotone curve is monotone, unconditionally. -/
theorem monotone_superadditiveClosureMaxNN {beta : ℝ≥0 → ℝ≥0∞}
    (hmono : Monotone beta) :
    Monotone (superadditiveClosureMaxNN beta) := by
  have hpow : ∀ n, Monotone (maxConvPow beta n) := by
    intro n
    induction n with
    | zero => exact hmono
    | succ n ih => exact monotone_maxConv ih
  exact fun a b hab => iSup_mono fun n => hpow n hab

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
