import Book.RealCurves

/-! Super- and sub-additivity of the real curves and their additive
closures: each curve's `IsSubadditive`/`IsSuperadditive` status, the staircase
ceiling/clamp lemmas, and the `*_closure` fixed-point identities. -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
open Set Topology Filter

/-- `rate R = rateLatency R 0`. -/
theorem rate_eq_rateLatency_zero (R : ℝ≥0) :
    rate R = rateLatency R 0 := by
  funext t; simp [rate, rateLatency]

/-- `rate R = tokenBucket R 0`. -/
theorem rate_eq_tokenBucket_zero (R : ℝ≥0) :
    rate R = tokenBucket R 0 := by
  funext t
  simp only [rate, tokenBucket, Pi.inf_apply,
    ENNReal.coe_zero, add_zero]
  rcases eq_or_ne t 0 with h | h
  · subst h; simp [delay]
  · have ht : ¬ t ≤ 0 := by simpa using h
    simp [delay, ht]

/-- `test 0 = tokenBucket 0 1`. -/
theorem test_zero_eq_tokenBucket :
    test (0 : ℝ≥0) = tokenBucket 0 1 := by
  funext t
  rcases eq_or_ne t 0 with h | h
  · subst h; simp [test, tokenBucket, delay]
  · have ht : ¬ t ≤ 0 := by simpa using h
    simp [test, tokenBucket, delay, ht]

/-- `rate R` is subadditive. -/
theorem rate_subadditive (R : ℝ≥0) :
    IsSubadditive (rate R) := by
  intro u s; simp only [rate]; push_cast; rw [mul_add]

/-- `rate R` is superadditive (hence additive). -/
theorem rate_superadditive (R : ℝ≥0) :
    IsSuperadditive (rate R) := by
  intro u s; simp only [rate]; push_cast; rw [mul_add]

/-- `delay d` is superadditive. -/
theorem delay_superadditive (d : ℝ≥0) :
    IsSuperadditive (delay d) := by
  intro u s
  simp only [delay]
  rcases le_or_gt (u + s) d with h | h
  · rw [if_pos h, if_pos (le_trans le_self_add h),
      if_pos (le_trans le_add_self h)]; simp
  · rw [if_neg (not_le.mpr h)]; exact le_top

/-- Truncated subtraction is superadditive: `(u-T)+(s-T) ≤ (u+s)-T`. -/
theorem tsub_add_tsub_le_tsub (u s T : ℝ≥0) :
    (u - T) + (s - T) ≤ (u + s) - T := by
  rcases le_or_gt u T with hu | hu
  · rw [tsub_eq_zero_of_le hu, zero_add]
    exact tsub_le_tsub_right le_add_self T
  · rcases le_or_gt s T with hs | hs
    · rw [tsub_eq_zero_of_le hs, add_zero]
      exact tsub_le_tsub_right le_self_add T
    · rw [tsub_add_tsub_comm (le_of_lt hu) (le_of_lt hs)]
      exact tsub_le_tsub_left le_add_self _

/-- `rateLatency R T` is superadditive. -/
theorem rateLatency_superadditive (R T : ℝ≥0) :
    IsSuperadditive (rateLatency R T) := by
  intro u s
  simp only [rateLatency]
  rw [← ENNReal.coe_mul, ← ENNReal.coe_mul,
    ← ENNReal.coe_mul, ← ENNReal.coe_add,
    ENNReal.coe_le_coe, ← mul_add]
  exact _root_.mul_le_mul_right (tsub_add_tsub_le_tsub u s T) R

/-- `tokenBucket r b` is subadditive. -/
theorem tokenBucket_subadditive (r b : ℝ≥0) :
    IsSubadditive (tokenBucket r b) := by
  intro u s
  rcases eq_or_ne u 0 with hu | hu
  · subst hu; rw [zero_add, tokenBucket_zero_eq, zero_add]
  · rcases eq_or_ne s 0 with hs | hs
    · subst hs
      rw [add_zero, tokenBucket_zero_eq, add_zero]
    · have hu0 : ¬ u ≤ 0 := by simpa using hu
      have hs0 : ¬ s ≤ 0 := by simpa using hs
      have hus0 : ¬ (u + s) ≤ 0 := by
        rw [nonpos_iff_eq_zero, add_eq_zero]
        rintro ⟨h1, _⟩; exact hu h1
      simp only [tokenBucket, Pi.inf_apply, delay,
        if_neg hu0, if_neg hs0, if_neg hus0, min_top_right]
      push_cast [mul_add]
      calc (r:ℝ≥0∞)*u + r*s + b
          ≤ (r*u + r*s + b) + b := le_self_add
        _ = (r*u + b) + (r*s + b) := by ring

/-- `test 0` is subadditive. -/
theorem test_zero_subadditive :
    IsSubadditive (test (0 : ℝ≥0)) := by
  rw [test_zero_eq_tokenBucket]
  exact tokenBucket_subadditive 0 1

/-- Subadditive step-count bound when `J ≥ 0`. -/
theorem staircase_ceil_sub (P : ℝ≥0) (hP : (0:ℝ) < P)
    (J : ℝ) (hJ : 0 ≤ J) (u s : ℝ≥0) :
    ⌈((u:ℝ)+(s:ℝ)+J)/P⌉
      ≤ ⌈((u:ℝ)+J)/P⌉ + ⌈((s:ℝ)+J)/P⌉ := by
  calc ⌈((u:ℝ)+(s:ℝ)+J)/P⌉
      ≤ ⌈((u:ℝ)+J)/P + ((s:ℝ)+J)/P⌉ := by
        apply Int.ceil_mono
        rw [← add_div, div_le_div_iff_of_pos_right hP]
        linarith
    _ ≤ ⌈((u:ℝ)+J)/P⌉ + ⌈((s:ℝ)+J)/P⌉ :=
        Int.ceil_add_le _ _

/-- Subadditive bound on the clamped staircase value (`J ≥ 0`). -/
theorem staircase_val_sub (P h : ℝ≥0) (hP : (0:ℝ) < P)
    (J : ℝ) (hJ : 0 ≤ J) (u s : ℝ≥0) :
    ENNReal.ofReal
        (max ((h:ℝ) * (⌈((u:ℝ)+(s:ℝ)+J)/P⌉:ℝ)) 0)
      ≤ ENNReal.ofReal
          (max ((h:ℝ)*(⌈((u:ℝ)+J)/P⌉:ℝ)) 0)
        + ENNReal.ofReal
          (max ((h:ℝ)*(⌈((s:ℝ)+J)/P⌉:ℝ)) 0) := by
  rw [← ENNReal.ofReal_add (le_max_right _ _)
    (le_max_right _ _)]
  apply ENNReal.ofReal_le_ofReal
  have hkey := staircase_ceil_sub P hP J hJ u s
  rcases le_or_gt ((h:ℝ) * (⌈((u:ℝ)+(s:ℝ)+J)/P⌉:ℝ)) 0
    with h0 | h0
  · rw [max_eq_right h0]
    exact add_nonneg (le_max_right _ _) (le_max_right _ _)
  · rw [max_eq_left (le_of_lt h0)]
    calc (h:ℝ) * (⌈((u:ℝ)+(s:ℝ)+J)/P⌉:ℝ)
        ≤ (h:ℝ) * ((⌈((u:ℝ)+J)/P⌉:ℝ)
            + (⌈((s:ℝ)+J)/P⌉:ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ h.coe_nonneg
          exact_mod_cast hkey
      _ = (h:ℝ)*(⌈((u:ℝ)+J)/P⌉:ℝ)
          + (h:ℝ)*(⌈((s:ℝ)+J)/P⌉:ℝ) := by ring
      _ ≤ max ((h:ℝ)*(⌈((u:ℝ)+J)/P⌉:ℝ)) 0
          + max ((h:ℝ)*(⌈((s:ℝ)+J)/P⌉:ℝ)) 0 :=
          add_le_add (le_max_left _ _) (le_max_left _ _)

/-- `staircase P h J` is subadditive when `J ≥ 0`. -/
theorem staircase_subadditive (P h : ℝ≥0)
    (hP : (0:ℝ) < P) (J : ℝ) (hJ : 0 ≤ J) :
    IsSubadditive (staircase P h J) := by
  intro u s
  rcases eq_or_ne u 0 with hu | hu
  · subst hu; rw [zero_add, staircase_zero_eq, zero_add]
  · rcases eq_or_ne s 0 with hs | hs
    · subst hs
      rw [add_zero, staircase_zero_eq, add_zero]
    · have hu0 : ¬ u ≤ 0 := by simpa using hu
      have hs0 : ¬ s ≤ 0 := by simpa using hs
      have hus0 : ¬ (u + s) ≤ 0 := by
        rw [nonpos_iff_eq_zero, add_eq_zero]
        rintro ⟨h1, _⟩; exact hu h1
      simp only [staircase, delay, if_neg hu0,
        if_neg hs0, if_neg hus0, min_top_right]
      push_cast
      exact staircase_val_sub P h hP J hJ u s

/-- `⌈x⌉ + ⌈y⌉ ≤ ⌈x+y⌉ + 1`. -/
theorem ceil_add_le_ceil_succ (x y : ℝ) :
    ⌈x⌉ + ⌈y⌉ ≤ ⌈x + y⌉ + 1 := by
  have hx := Int.ceil_lt_add_one x
  have hy := Int.ceil_lt_add_one y
  have hxy := Int.le_ceil (x + y)
  have hi : ⌈x⌉ + ⌈y⌉ < ⌈x+y⌉ + 2 := by
    have : (⌈x⌉:ℝ) + ⌈y⌉ < ⌈x+y⌉ + 2 := by linarith
    exact_mod_cast this
  omega

/-- Superadditive step-count bound when `J < -P`. -/
theorem staircase_ceil_super (P : ℝ≥0) (hP : (0:ℝ) < P)
    (J : ℝ) (hJ : J < -P) (u s : ℝ≥0) :
    ⌈((u:ℝ)+J)/P⌉ + ⌈((s:ℝ)+J)/P⌉
      ≤ ⌈((u:ℝ)+(s:ℝ)+J)/P⌉ := by
  have hPne : (P:ℝ) ≠ 0 := ne_of_gt hP
  have hab : ((u:ℝ)+J)/P + ((s:ℝ)+J)/P
      ≤ ((u:ℝ)+(s:ℝ)+J)/P - 1 := by
    rw [← add_div, le_sub_iff_add_le,
      div_add' _ _ _ hPne,
      div_le_div_iff_of_pos_right hP]
    nlinarith [hJ]
  have h1 := ceil_add_le_ceil_succ
    (((u:ℝ)+J)/P) (((s:ℝ)+J)/P)
  have h2 : ⌈((u:ℝ)+J)/P + ((s:ℝ)+J)/P⌉
      ≤ ⌈((u:ℝ)+(s:ℝ)+J)/P - 1⌉ := Int.ceil_mono hab
  have h3 : ⌈((u:ℝ)+(s:ℝ)+J)/P - 1⌉
      = ⌈((u:ℝ)+(s:ℝ)+J)/P⌉ - 1 := by
    rw [show ((u:ℝ)+(s:ℝ)+J)/P - 1
        = ((u:ℝ)+(s:ℝ)+J)/P + ((-1 : ℤ) : ℝ) by
      push_cast; ring, Int.ceil_add_intCast]; ring
  omega

/-- Superadditivity of `max (h·n) 0` clamps under `n+m ≤ k`. -/
theorem clamp_super (h : ℝ) (hh : 0 ≤ h) (n m k : ℤ)
    (hn : n ≤ k) (hm : m ≤ k) (hnm : n + m ≤ k) :
    max (h * n) 0 + max (h * m) 0 ≤ max (h * k) 0 := by
  rcases le_or_gt (h*(n:ℝ)) 0 with hN | hN
  · rw [max_eq_right hN, zero_add]
    rcases le_or_gt (h*(m:ℝ)) 0 with hM | hM
    · rw [max_eq_right hM]; exact le_max_right _ _
    · rw [max_eq_left (le_of_lt hM)]
      apply le_max_of_le_left
      have : (m:ℝ) ≤ k := by exact_mod_cast hm
      nlinarith [hh, this]
  · rcases le_or_gt (h*(m:ℝ)) 0 with hM | hM
    · rw [max_eq_left (le_of_lt hN), max_eq_right hM,
        add_zero]
      apply le_max_of_le_left
      have : (n:ℝ) ≤ k := by exact_mod_cast hn
      nlinarith [hh, this]
    · rw [max_eq_left (le_of_lt hN),
        max_eq_left (le_of_lt hM)]
      apply le_max_of_le_left
      have : (n:ℝ) + m ≤ k := by exact_mod_cast hnm
      nlinarith [hh, this]

/-- `staircase P h J` is superadditive when `J < -P`. -/
theorem staircase_superadditive (P h : ℝ≥0)
    (hP : (0:ℝ) < P) (J : ℝ) (hJ : J < -P) :
    IsSuperadditive (staircase P h J) := by
  intro u s
  rcases eq_or_ne u 0 with hu | hu
  · subst hu; rw [zero_add, staircase_zero_eq, zero_add]
  · rcases eq_or_ne s 0 with hs | hs
    · subst hs
      rw [add_zero, staircase_zero_eq, add_zero]
    · have hu0 : ¬ u ≤ 0 := by simpa using hu
      have hs0 : ¬ s ≤ 0 := by simpa using hs
      have hus0 : ¬ (u + s) ≤ 0 := by
        rw [nonpos_iff_eq_zero, add_eq_zero]
        rintro ⟨h1, _⟩; exact hu h1
      simp only [staircase, delay, if_neg hu0,
        if_neg hs0, if_neg hus0, min_top_right]
      rw [← ENNReal.ofReal_add (le_max_right _ _)
        (le_max_right _ _)]
      apply ENNReal.ofReal_le_ofReal
      have hnk : ⌈((u:ℝ)+J)/P⌉
          ≤ ⌈((u:ℝ)+(s:ℝ)+J)/P⌉ :=
        Int.ceil_mono ((div_le_div_iff_of_pos_right hP).2
          (by linarith [s.coe_nonneg]))
      have hmk : ⌈((s:ℝ)+J)/P⌉
          ≤ ⌈((u:ℝ)+(s:ℝ)+J)/P⌉ :=
        Int.ceil_mono ((div_le_div_iff_of_pos_right hP).2
          (by linarith [u.coe_nonneg]))
      exact clamp_super (h:ℝ) h.coe_nonneg _ _ _ hnk hmk
        (staircase_ceil_super P hP J hJ u s)

/-- The token-bucket is its own subadditive closure. -/
theorem tokenBucket_closure (r b : ℝ≥0) :
    subadditiveClosureE (tokenBucket r b)
      = tokenBucket r b :=
  subadditiveClosureE_eq_self _
    (tokenBucket_subadditive r b)
    (tokenBucket_zero_eq r b)

/-- The staircase (`J ≥ 0`) is its own subadditive closure. -/
theorem staircase_closure (P h : ℝ≥0) (hP : (0:ℝ) < P)
    (J : ℝ) (hJ : 0 ≤ J) :
    subadditiveClosureE (staircase P h J)
      = staircase P h J :=
  subadditiveClosureE_eq_self _
    (staircase_subadditive P h hP J hJ)
    (staircase_zero_eq P h J)

/-- Pointwise coercion `(ℝ≥0 → ℝ≥0∞) → (ℝ≥0 → WithBot ℝ≥0∞)`. -/
instance : Coe (ℝ≥0 → ℝ≥0∞) (ℝ≥0 → WithBot ℝ≥0∞) :=
  ⟨fun g t => ((g t : ℝ≥0∞) : WithBot ℝ≥0∞)⟩

/-- A superadditive `g` with `g 0 = 0` is its own superadditive closure. -/
theorem superadditiveClosure_coe_eq_self
    (g : ℝ≥0 → ℝ≥0∞)
    (hsup : IsSuperadditive g) (h0 : g 0 = 0) :
    superadditiveClosure (↑g)
      = (↑g : ℝ≥0 → WithBot ℝ≥0∞) := by
  apply superadditiveClosure_eq_self
  · intro u s
    show ((g u : ℝ≥0∞) : WithBot ℝ≥0∞)
        + ((g s : ℝ≥0∞) : WithBot ℝ≥0∞)
      ≤ ((g (u + s) : ℝ≥0∞) : WithBot ℝ≥0∞)
    rw [← WithBot.coe_add]
    exact_mod_cast hsup u s
  · show ((g 0 : ℝ≥0∞) : WithBot ℝ≥0∞) = 0
    rw [h0]; rfl

/-- Superadditive-closure of `g` recovers `g` after `unbotD 0`. -/
theorem superadditiveClosure_unbotD_eq
    (g : ℝ≥0 → ℝ≥0∞)
    (hsup : IsSuperadditive g) (h0 : g 0 = 0)
    (t : ℝ≥0) :
    (superadditiveClosure (↑g) t).unbotD 0 = g t := by
  rw [superadditiveClosure_coe_eq_self g hsup h0]
  show (((g t : ℝ≥0∞) : WithBot ℝ≥0∞)).unbotD 0 = g t
  rw [WithBot.unbotD_coe]

/-- `delay d` is fixed by its superadditive closure. -/
theorem delay_closure (d : ℝ≥0) (t : ℝ≥0) :
    (superadditiveClosure (↑(delay d)) t).unbotD 0
      = delay d t :=
  superadditiveClosure_unbotD_eq _
    (delay_superadditive d) (delay_zero_eq d) t

/-- `rate R` is fixed by its superadditive closure. -/
theorem rate_closure (R : ℝ≥0) (t : ℝ≥0) :
    (superadditiveClosure (↑(rate R)) t).unbotD 0
      = rate R t :=
  superadditiveClosure_unbotD_eq _
    (rate_superadditive R) (rate_zero_eq R) t

/-- `rateLatency R T` is fixed by its superadditive closure. -/
theorem rateLatency_closure (R T : ℝ≥0) (t : ℝ≥0) :
    (superadditiveClosure (↑(rateLatency R T)) t).unbotD 0
      = rateLatency R T t :=
  superadditiveClosure_unbotD_eq _
    (rateLatency_superadditive R T)
    (rateLatency_zero_eq R T) t

/-- The staircase (`J < -P`) is fixed by its superadditive closure. -/
theorem staircase_closure_super (P h : ℝ≥0)
    (hP : (0:ℝ) < P) (J : ℝ) (hJ : J < -P) (t : ℝ≥0) :
    (superadditiveClosure (↑(staircase P h J)) t).unbotD 0
      = staircase P h J t :=
  superadditiveClosure_unbotD_eq _
    (staircase_superadditive P h hP J hJ)
    (staircase_zero_eq P h J) t
end DeepWiki
