import DeepWiki.NetworkCalculus.Closures
import DeepWiki.NetworkCalculus.KleeneStarLeast

/-! # Lagrange's sub-additive-closure factorization (Lemma 4.7)
The (min,+) closure-algebra identity, credited (unpublished) to S. Lagrange, that turns the
closure of a function into a *finite* convolution problem:
`(f ⊓ g ∗ h⋆)⋆ = f⋆ ∗ (δ₀ ⊓ g ∗ (g ⊓ h)⋆)`, where `⊓` is the pointwise minimum (the dioid
sum `⊕`), `∗ = minConv` is the (min,+) convolution (the dioid product), `⋆ = subadditiveClosureENN`
is the Kleene star / sub-additive closure, and `δ₀ = minConvPow g 0` is the convolution unit.

The engine is the **star-of-a-meet** identity `(σ ⊓ τ)⋆ = σ⋆ ∗ τ⋆` (`subadditiveClosureENN_min`,
book Prop 2.6): the lemma reduces to the inner identity `(g ∗ h⋆)⋆ = δ₀ ⊓ g ∗ (g ⊓ h)⋆`, which we
prove by antisymmetry from `(g ∗ h⋆)ⁿ = gⁿ ∗ h⋆` (`n ≥ 1`) and `g ∗ g⋆ = ⨅_{n} gⁿ⁺¹`. -/

namespace DeepWiki

open scoped NNReal ENNReal

variable {D : Type} [_root_.AddCommMonoid D]

/-! ## Closure-algebra toolkit -/

/-- The (min,+) convolution distributes over an arbitrary infimum on the right:
`(f ∗ ⨅ₙ gₙ) t = ⨅ₙ (f ∗ gₙ) t` (from `(⨅ₙ aₙ) + b = ⨅ₙ (aₙ + b)` in `ℝ≥0∞`). -/
theorem minConv_iInf_right {ι : Type*} [Nonempty ι] (f : D → ℝ≥0∞)
    (g : ι → D → ℝ≥0∞) (t : D) :
    minConv f (fun s => ⨅ n, g n s) t = ⨅ n, minConv f (g n) t := by
  apply le_antisymm
  · refine le_iInf fun n => ?_
    exact minConv_le_minConv (fun _ => le_rfl) (fun s => iInf_le _ n) t
  · refine le_minConv fun u s hus => ?_
    rw [ENNReal.add_iInf]
    exact le_iInf fun n => iInf_le_of_le n (minConv_le_add f (g n) hus)

/-- Iterating idempotence: a positive convolution power of a closure is the closure itself,
`(σ⋆)ⁿ⁺¹ = σ⋆`. -/
theorem minConvPow_subadditiveClosureENN_succ (σ : D → ℝ≥0∞) (n : ℕ) :
    minConvPow (subadditiveClosureENN σ) (n + 1) = subadditiveClosureENN σ := by
  induction n with
  | zero => exact minConvPow_one _
  | succ n ih =>
      rw [minConvPow_succ, ih, minConv_comm, subadditiveClosureENN_idem]

/-- Closure is below its original: `σ⋆ ≤ σ` (function form of `subadditiveClosureENN_le`). -/
theorem subadditiveClosureENN_le_self (σ : D → ℝ≥0∞) :
    subadditiveClosureENN σ ≤ σ :=
  fun t => subadditiveClosureENN_le σ t

/-- The closure absorbs convolution with another closure on either side:
`g⋆ ∗ h⋆ ≤ h⋆` (the unit `δ₀ ≤ g⋆` makes `g⋆` a left identity up to `≤`). -/
theorem minConv_subadditiveClosureENN_subadditiveClosureENN_le (g h : D → ℝ≥0∞) (t : D) :
    minConv (subadditiveClosureENN g) (subadditiveClosureENN h) t
      ≤ subadditiveClosureENN h t := by
  rw [minConv_comm]
  exact minConv_subadditiveClosureENN_le (subadditiveClosureENN h) g t

/-- `g ∗ g⋆` is the meet of the *positive* convolution powers: `(g ∗ g⋆) t = ⨅ₙ gⁿ⁺¹ t`. -/
theorem minConv_self_subadditiveClosureENN_eq_iInf (g : D → ℝ≥0∞) (t : D) :
    minConv g (subadditiveClosureENN g) t = ⨅ n : ℕ, minConvPow g (n + 1) t := by
  rw [minConv_subadditiveClosureENN_eq_iInf]
  refine iInf_congr fun n => ?_
  rw [minConvPow_succ, minConv_comm]

/-- `g ∗ g⋆ ≤ gⁿ⁺¹`: the positive-power meet lies below each positive power. -/
theorem minConv_self_subadditiveClosureENN_le_minConvPow_succ (g : D → ℝ≥0∞) (n : ℕ) (t : D) :
    minConv g (subadditiveClosureENN g) t ≤ minConvPow g (n + 1) t := by
  rw [minConv_self_subadditiveClosureENN_eq_iInf]
  exact iInf_le _ n

/-- A positive power of a convolution-with-a-closure collapses the closure's powers:
`(g ∗ h⋆)ⁿ⁺¹ = gⁿ⁺¹ ∗ h⋆` (since `(h⋆)ⁿ⁺¹ = h⋆`). -/
theorem minConvPow_minConv_subadditiveClosureENN_succ (g h : D → ℝ≥0∞) (n : ℕ) :
    minConvPow (minConv g (subadditiveClosureENN h)) (n + 1)
      = minConv (minConvPow g (n + 1)) (subadditiveClosureENN h) := by
  rw [minConvPow_minConv, minConvPow_subadditiveClosureENN_succ]

/-- `g ∗ (g ⊓ h)⋆` as a meet of the positive powers convolved with `h⋆`:
`g ∗ (g ⊓ h)⋆ t = ⨅ₙ (gⁿ⁺¹ ∗ h⋆) t`. Combines Prop 2.6 (`(g ⊓ h)⋆ = g⋆ ∗ h⋆`),
associativity, and `g ∗ g⋆ = ⨅ₙ gⁿ⁺¹`. -/
theorem minConv_minConv_subadditiveClosureENN_min_eq_iInf (g h : D → ℝ≥0∞) (t : D) :
    minConv g (subadditiveClosureENN (fun s => min (g s) (h s))) t
      = ⨅ n : ℕ, minConv (minConvPow g (n + 1)) (subadditiveClosureENN h) t := by
  -- `(g ⊓ h)⋆ = g⋆ ∗ h⋆`, then reassociate to `(g ∗ g⋆) ∗ h⋆`.
  rw [subadditiveClosureENN_min, ← minConv_assoc_enn]
  -- `g ∗ g⋆ = ⨅ₙ gⁿ⁺¹`, then push the meet through the outer `∗ h⋆`.
  rw [show minConv g (subadditiveClosureENN g)
        = (fun s => ⨅ n : ℕ, minConvPow g (n + 1) s) from
      funext fun s => minConv_self_subadditiveClosureENN_eq_iInf g s]
  rw [minConv_comm, minConv_iInf_right]
  exact iInf_congr fun n => congrFun (minConv_comm _ _) t

/-! ## The inner Lagrange identity -/

/-- **Inner Lagrange identity**: `(g ∗ h⋆)⋆ = δ₀ ⊓ g ∗ (g ⊓ h)⋆`, where `δ₀` is the
convolution unit `minConvPow g 0`. This is the heart of Lemma 4.7; the full statement
follows by the star-of-a-meet identity `subadditiveClosureENN_min`. -/
theorem subadditiveClosureENN_minConv_subadditiveClosureENN (g h : D → ℝ≥0∞) :
    subadditiveClosureENN (minConv g (subadditiveClosureENN h))
      = fun t => min (minConvPow g 0 t)
          (minConv g (subadditiveClosureENN (fun s => min (g s) (h s))) t) := by
  set σ := minConv g (subadditiveClosureENN h) with hσ
  apply le_antisymm
  · -- `σ⋆ ≤ δ₀` and `σ⋆ ≤ g ∗ (g ⊓ h)⋆`, pointwise.
    intro t
    refine le_min ?_ ?_
    · -- `σ⋆ ≤ σ⁰ = δ₀`: closure lies below its zeroth power, and `σ⁰ = g⁰`.
      rw [subadditiveClosureENN_eq_iInf]
      refine (iInf_le _ 0).trans ?_
      rw [minConvPow_zero, minConvPow_zero]
    · -- `σ⋆ ≤ ⨅ₙ σⁿ⁺¹ = g ∗ (g ⊓ h)⋆`.
      rw [minConv_minConv_subadditiveClosureENN_min_eq_iInf]
      refine le_iInf fun n => ?_
      rw [← minConvPow_minConv_subadditiveClosureENN_succ, subadditiveClosureENN_eq_iInf]
      exact iInf_le _ (n + 1)
  · -- `δ₀ ⊓ g ∗ (g ⊓ h)⋆ ≤ σⁿ` for every `n`, so `≤ σ⋆`.
    rw [le_subadditiveClosureENN_iff]
    intro n
    cases n with
    | zero =>
        intro t
        simp only [minConvPow_zero]
        exact min_le_left _ _
    | succ k =>
        intro t
        refine min_le_of_right_le ?_
        rw [minConvPow_minConv_subadditiveClosureENN_succ,
          minConv_minConv_subadditiveClosureENN_min_eq_iInf]
        exact iInf_le _ k

/-! ## Lemma 4.7 -/

/-- **Lemma 4.7** (Lagrange's sub-additive-closure factorization):
`(f ⊓ g ∗ h⋆)⋆ = f⋆ ∗ (δ₀ ⊓ g ∗ (g ⊓ h)⋆)`, with `δ₀ = minConvPow g 0` the convolution
unit. Proof: the star-of-a-meet identity `(f ⊓ x)⋆ = f⋆ ∗ x⋆` (Prop 2.6) with `x = g ∗ h⋆`,
then the inner identity `(g ∗ h⋆)⋆ = δ₀ ⊓ g ∗ (g ⊓ h)⋆`. -/
theorem subadditiveClosureENN_min_minConv_subadditiveClosureENN (f g h : D → ℝ≥0∞) :
    subadditiveClosureENN (fun t => min (f t) (minConv g (subadditiveClosureENN h) t))
      = minConv (subadditiveClosureENN f)
          (fun t => min (minConvPow g 0 t)
            (minConv g (subadditiveClosureENN (fun s => min (g s) (h s))) t)) := by
  rw [subadditiveClosureENN_min f (minConv g (subadditiveClosureENN h)),
    subadditiveClosureENN_minConv_subadditiveClosureENN]

-- Restatement (book Lemma 4.7, §4.3 p.77): with `⊓` the pointwise meet, `∗ = minConv`,
-- `⋆ = subadditiveClosureENN`, and `δ₀ = minConvPow g 0` the convolution unit:
-- `(f ⊓ g ∗ h⋆)⋆ = f⋆ ∗ (δ₀ ⊓ g ∗ (g ⊓ h)⋆)`.
example (f g h : ℝ≥0 → ℝ≥0∞) :
    subadditiveClosureENN (f ⊓ minConv g (subadditiveClosureENN h))
      = minConv (subadditiveClosureENN f)
          (minConvPow g 0
            ⊓ minConv g (subadditiveClosureENN (g ⊓ h))) := by
  have key := subadditiveClosureENN_min_minConv_subadditiveClosureENN f g h
  simp only [Pi.inf_def] at key ⊢
  exact key

end DeepWiki
