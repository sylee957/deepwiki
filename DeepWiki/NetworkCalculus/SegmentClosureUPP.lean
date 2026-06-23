import DeepWiki.NetworkCalculus.Closures
import DeepWiki.NetworkCalculus.UltimatelyPseudoPeriodic

/-! # Sub- and super-additive closure of an open segment (§4.3, working toward Lemma 4.9)

An **open segment** `segNN a b va s` is the affine map `va + s·(t−a)` on the open interval
`(a, b)` and `⊤` (= `+∞`, the dioid `𝟘`) outside, over the `ℝ≥0∞`-valued carrier
`ℝ≥0 → ℝ≥0∞`.  This file builds the structural facts behind DNC Lemma 4.9 — *the
sub-additive closure of an open segment is ultimately pseudo-periodic*:

* `segNN` and its `@[simp]` reductions, in- and off-support readings, endpoint behavior,
  and finiteness on the support (Goal 1).
* **Support of the convolution powers** (Goal 2): for `n ≥ 1`,
  `minConvPow (segNN a b va s) n` is `⊤` off the `n`-fold open support `(n·a, n·b)`
  (`minConvPow_segNN_eq_top_of_le` / `…_of_ge`) — proved by `Nat.le_induction` over the
  single-segment support using the `minConv` intro/elim API.
* **Exact value of the powers** (Goal 3): on its support `(n·a, n·b)` the power is the open
  segment `n·va + s·(t − n·a)` of the *same slope* `s` — `minConvPow_segNN_eq_affine`, the
  book's "`fⁿ` is an open segment of slope `f'` on `(na, nb)`".  Proved as a lower bound
  (off-support factors are `⊤`) and a matching upper bound (the equal-split witness `t/n`).

The full UPP theorem (the supports-overlap eventual-periodicity / infimum-selection
argument, book Lemma 4.9 proper) is **not** closed here; see the closing note. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-! ## The open segment over `ℝ≥0∞` -/

/-- Open segment over `ℝ≥0∞`: affine `va + s·(t−a)` (value `va` at `a⁺`, slope `s`) on the
open interval `(a, b)`, and `⊤` (the dioid zero `𝟘 = +∞`) outside. -/
noncomputable def segNN (a b va s : ℝ≥0) : ℝ≥0 → ℝ≥0∞ :=
  fun t => if a < t ∧ t < b then ((va + s * (t - a) : ℝ≥0) : ℝ≥0∞) else ⊤

/-- `segNN` reduces to its defining `if`. -/
theorem segNN_apply (a b va s t : ℝ≥0) :
    segNN a b va s t =
      if a < t ∧ t < b then ((va + s * (t - a) : ℝ≥0) : ℝ≥0∞) else ⊤ :=
  rfl

/-- On the open interval `(a,b)`, `segNN` is the affine value. -/
@[simp] theorem segNN_apply_mem (a b va s t : ℝ≥0) (h : a < t ∧ t < b) :
    segNN a b va s t = ((va + s * (t - a) : ℝ≥0) : ℝ≥0∞) :=
  if_pos h

/-- Off the open interval `(a,b)`, `segNN` is `⊤`. -/
@[simp] theorem segNN_apply_not_mem (a b va s t : ℝ≥0) (h : ¬ (a < t ∧ t < b)) :
    segNN a b va s t = ⊤ :=
  if_neg h

/-- In-support reading from the two strict bounds. -/
theorem segNN_mem (a b va s t : ℝ≥0) (hl : a < t) (hr : t < b) :
    segNN a b va s t = ((va + s * (t - a) : ℝ≥0) : ℝ≥0∞) :=
  if_pos ⟨hl, hr⟩

/-- At or left of `a`, the open segment is `⊤`. -/
theorem segNN_of_le_left (a b va s t : ℝ≥0) (h : t ≤ a) :
    segNN a b va s t = ⊤ :=
  if_neg fun hmem => absurd hmem.1 (not_lt.mpr h)

/-- At or right of `b`, the open segment is `⊤`. -/
theorem segNN_of_ge_right (a b va s t : ℝ≥0) (h : b ≤ t) :
    segNN a b va s t = ⊤ :=
  if_neg fun hmem => absurd hmem.2 (not_lt.mpr h)

/-- On its support, the open segment is finite (`≠ ⊤`). -/
theorem segNN_ne_top_of_mem (a b va s t : ℝ≥0) (hl : a < t) (hr : t < b) :
    segNN a b va s t ≠ ⊤ := by
  rw [segNN_mem a b va s t hl hr]; exact ENNReal.coe_ne_top

/-- On its support, the open segment value is below `⊤` (`< ⊤`). -/
theorem segNN_lt_top_of_mem (a b va s t : ℝ≥0) (hl : a < t) (hr : t < b) :
    segNN a b va s t < ⊤ :=
  lt_top_iff_ne_top.mpr (segNN_ne_top_of_mem a b va s t hl hr)

/-- An empty (or degenerate) open segment `b ≤ a` is identically `⊤`. -/
theorem segNN_of_le (a b va s : ℝ≥0) (h : b ≤ a) : segNN a b va s = fun _ => ⊤ := by
  funext t
  exact if_neg fun hmem => absurd (hmem.1.trans hmem.2) (not_lt.mpr h)

/-! ## Support of the convolution powers (Goal 2)

For `n ≥ 1` the `n`-fold (min,+) convolution power of an open segment is supported in the
*open* interval `(n·a, n·b)`: it is `⊤` whenever `t ≤ n·a` or `n·b ≤ t`.  The proof is a
`Nat.le_induction` from `n = 1` (where `minConvPow … 1 = segNN`), splitting any `u + v = t`:
on the left side one of `u ≤ n·a` (apply IH) or `v ≤ a` (the segment is `⊤`) must hold;
dually on the right. -/

/-- Left support boundary of the powers: for `n ≥ 1`, `minConvPow (segNN a b va s) n t = ⊤`
whenever `t ≤ n·a` (off the `n`-fold open support on the left). -/
theorem minConvPow_segNN_eq_top_of_le (a b va s : ℝ≥0) :
    ∀ {n : ℕ}, 1 ≤ n → ∀ {t : ℝ≥0}, t ≤ (n : ℝ≥0) * a →
      minConvPow (segNN a b va s) n t = ⊤ := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      intro t ht
      rw [minConvPow_one]
      rw [Nat.cast_one, one_mul] at ht
      exact segNN_of_le_left a b va s t ht
  | succ n hn ih =>
      intro t ht
      rw [minConvPow_succ]
      refine le_antisymm le_top (le_minConv fun u v huv => ?_)
      -- t ≤ (n+1)·a = n·a + a, so u ≤ n·a or v ≤ a
      have hsum : u + v ≤ (n : ℝ≥0) * a + a := by
        rw [huv]
        calc t ≤ ((n + 1 : ℕ) : ℝ≥0) * a := ht
          _ = (n : ℝ≥0) * a + a := by push_cast; ring
      have hcase : u ≤ (n : ℝ≥0) * a ∨ v ≤ a := by
        rcases le_or_gt u ((n : ℝ≥0) * a) with hu | hu
        · exact Or.inl hu
        · refine Or.inr (le_of_not_gt fun hv => ?_)
          exact absurd hsum (not_le.mpr (add_lt_add hu hv))
      rcases hcase with hu | hv
      · rw [ih hu, top_add]
      · rw [segNN_of_le_left a b va s v hv, add_top]

/-- Right support boundary of the powers: for `n ≥ 1`, `minConvPow (segNN a b va s) n t = ⊤`
whenever `n·b ≤ t` (off the `n`-fold open support on the right). -/
theorem minConvPow_segNN_eq_top_of_ge (a b va s : ℝ≥0) :
    ∀ {n : ℕ}, 1 ≤ n → ∀ {t : ℝ≥0}, (n : ℝ≥0) * b ≤ t →
      minConvPow (segNN a b va s) n t = ⊤ := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      intro t ht
      rw [minConvPow_one]
      rw [Nat.cast_one, one_mul] at ht
      exact segNN_of_ge_right a b va s t ht
  | succ n hn ih =>
      intro t ht
      rw [minConvPow_succ]
      refine le_antisymm le_top (le_minConv fun u v huv => ?_)
      have hsum : (n : ℝ≥0) * b + b ≤ u + v := by
        rw [huv]
        calc (n : ℝ≥0) * b + b = ((n + 1 : ℕ) : ℝ≥0) * b := by push_cast; ring
          _ ≤ t := ht
      have hcase : (n : ℝ≥0) * b ≤ u ∨ b ≤ v := by
        rcases le_or_gt ((n : ℝ≥0) * b) u with hu | hu
        · exact Or.inl hu
        · refine Or.inr (le_of_not_gt fun hv => ?_)
          exact absurd hsum (not_le.mpr (add_lt_add hu hv))
      rcases hcase with hu | hv
      · rw [ih hu, top_add]
      · rw [segNN_of_ge_right a b va s v hv, add_top]

/-- Combined off-support reading: for `n ≥ 1`, the `n`-fold power is `⊤` outside the open
support `(n·a, n·b)`. -/
theorem minConvPow_segNN_eq_top_of_not_mem (a b va s : ℝ≥0) {n : ℕ} (hn : 1 ≤ n)
    {t : ℝ≥0} (h : ¬ ((n : ℝ≥0) * a < t ∧ t < (n : ℝ≥0) * b)) :
    minConvPow (segNN a b va s) n t = ⊤ := by
  rw [not_and_or, not_lt, not_lt] at h
  rcases h with h | h
  · exact minConvPow_segNN_eq_top_of_le a b va s hn h
  · exact minConvPow_segNN_eq_top_of_ge a b va s hn h

/-- Closure value left of the first segment: for `0 < t ≤ a` every power `n ≥ 1` has
`t ≤ a ≤ n·a` (off-support, `= ⊤`) and the `n = 0` term is `⊤` too, so the closure is `⊤`. -/
theorem subadditiveClosureENN_segNN_eq_top_of_le_left (a b va s : ℝ≥0)
    {t : ℝ≥0} (ht : 0 < t) (hta : t ≤ a) :
    subadditiveClosureENN (segNN a b va s) t = ⊤ := by
  rw [subadditiveClosureENN_eq_iInf]
  refine le_antisymm le_top (le_iInf fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [minConvPow_zero, if_neg (by exact_mod_cast ht.ne')]
  · refine le_of_eq (minConvPow_segNN_eq_top_of_le a b va s hn ?_).symm
    calc t ≤ a := hta
      _ = (1 : ℝ≥0) * a := (one_mul a).symm
      _ ≤ (n : ℝ≥0) * a := by
          gcongr
          exact_mod_cast hn

/-! ## Convolution-value bounds through a segment (Goal 3)

Upper bounds for a convolution `minConv f (segNN …)`: any split landing inside `(a, b)`
gives the affine contribution, and the two-fold value `segNN ∗ segNN` at the doubled
midpoint is the doubled segment value (the (min,+) convolution of two segments is convex,
the book Theorem 4.1 ingredient; only the midpoint instance is recorded here). -/

/-- Convolution upper bound through an open segment: for any split `u + v = t` with `v`
*strictly inside* `(a,b)`, `minConv f (segNN a b va s) t ≤ f u + (va + s·(v−a))`. -/
theorem minConv_segNN_le (f : ℝ≥0 → ℝ≥0∞) (a b va s : ℝ≥0)
    {u v t : ℝ≥0} (hsum : u + v = t) (hl : a < v) (hr : v < b) :
    minConv f (segNN a b va s) t ≤ f u + ((va + s * (v - a) : ℝ≥0) : ℝ≥0∞) := by
  have := minConv_le_add f (segNN a b va s) (u := u) (s := v) hsum
  rwa [segNN_mem a b va s v hl hr] at this

/-- Two-fold value at the doubled midpoint: for `a < m < b`, the convolution `segNN ∗ segNN`
at `2·m` is bounded above by the doubled segment value `2·va + 2·s·(m−a)` (split `m + m`). -/
theorem minConv_segNN_segNN_two_mul_le (a b va s m : ℝ≥0) (hl : a < m) (hr : m < b) :
    minConv (segNN a b va s) (segNN a b va s) (m + m)
      ≤ ((va + s * (m - a) : ℝ≥0) : ℝ≥0∞) + ((va + s * (m - a) : ℝ≥0) : ℝ≥0∞) := by
  have h := minConv_segNN_le (segNN a b va s) a b va s (u := m) (v := m) rfl hl hr
  rwa [segNN_mem a b va s m hl hr] at h

/-! ## Affine lower bound for the powers (toward the exact value of Lemma 4.9)

On its `n`-fold support `(n·a, n·b)` the power `minConvPow (segNN a b va s) n` is *at least*
the affine envelope `t ↦ n·va + s·(t − n·a)` (slope `s`, the book's "fⁿ is a segment of
slope f' on (na, nb)").  This is the clean half of the exact-value computation: any split
`u + v = t` either lands both `u ∈ (n·a, n·b)` and `v ∈ (a, b)` — where the inductive
affine bound on `minConvPow n u` plus the segment value at `v` sum to the affine value via
the truncated-subtraction identity `(u−na) + (v−a) = (u+v) − (na+a)` — or lands one factor
off-support, contributing `⊤` (by the support lemmas above).  The matching *upper* bound
(choosing an interior split) is the harder direction and is not proved here. -/

/-- Affine lower bound: for `n ≥ 1` and `t` strictly inside the `n`-fold support
`(n·a, n·b)`, the power dominates the affine envelope `n·va + s·(t − n·a)`. -/
theorem minConvPow_segNN_affine_le (a b va s : ℝ≥0) :
    ∀ {n : ℕ}, 1 ≤ n → ∀ {t : ℝ≥0}, (n : ℝ≥0) * a < t → t < (n : ℝ≥0) * b →
      (((n : ℝ≥0) * va + s * (t - (n : ℝ≥0) * a) : ℝ≥0) : ℝ≥0∞)
        ≤ minConvPow (segNN a b va s) n t := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      intro t htl htr
      rw [Nat.cast_one, one_mul] at htl htr
      rw [minConvPow_one, segNN_mem a b va s t htl htr, Nat.cast_one, one_mul, one_mul]
  | succ n hn ih =>
      intro t htl htr
      rw [minConvPow_succ]
      refine le_minConv fun u v huv => ?_
      -- Split into: both factors on support (affine identity), or one off-support (⊤).
      by_cases hu : (n : ℝ≥0) * a < u ∧ u < (n : ℝ≥0) * b
      · by_cases hv : a < v ∧ v < b
        · -- both interior: use IH on `u` and the segment value on `v`.
          have hil := ih hu.1 hu.2
          rw [segNN_mem a b va s v hv.1 hv.2]
          refine le_trans ?_ (add_le_add hil le_rfl)
          rw [← ENNReal.coe_add]
          refine ENNReal.coe_le_coe.mpr (le_of_eq ?_)
          -- arithmetic: (n+1)va + s(t-(n+1)a) = (nva + s(u-na)) + (va + s(v-a))
          have hau : (n : ℝ≥0) * a ≤ u := le_of_lt hu.1
          have hav : a ≤ v := le_of_lt hv.1
          have hsub : (u - (n : ℝ≥0) * a) + (v - a) = t - ((n : ℝ≥0) * a + a) := by
            rw [tsub_add_tsub_comm hau hav, huv]
          have hcast : ((n + 1 : ℕ) : ℝ≥0) * a = (n : ℝ≥0) * a + a := by push_cast; ring
          have hcastva : ((n + 1 : ℕ) : ℝ≥0) * va = (n : ℝ≥0) * va + va := by push_cast; ring
          calc ((n + 1 : ℕ) : ℝ≥0) * va + s * (t - ((n + 1 : ℕ) : ℝ≥0) * a)
              = ((n : ℝ≥0) * va + va) + s * (t - ((n : ℝ≥0) * a + a)) := by
                rw [hcastva, hcast]
            _ = ((n : ℝ≥0) * va + va) + s * ((u - (n : ℝ≥0) * a) + (v - a)) := by rw [hsub]
            _ = ((n : ℝ≥0) * va + s * (u - (n : ℝ≥0) * a)) + (va + s * (v - a)) := by ring
        · rw [segNN_apply_not_mem a b va s v hv, add_top]; exact le_top
      · rw [minConvPow_segNN_eq_top_of_not_mem a b va s hn hu, top_add]; exact le_top

/-! ## Affine upper bound and exact value for the powers

The matching *upper* bound uses the **equal split** witness `v = t/n`, `u = t − v`: at
level `n+1`, `v = t/(n+1) ∈ (a, b)` and `u = t − t/(n+1) ∈ (n·a, n·b)` (both checked by
clearing the denominator in `ℝ`), so the elimination rule `minConv_le_add` yields the
affine value.  Combined with the lower bound, this is the **exact value** of the power on
its support — the book's "`fⁿ` is an open segment of slope `f'` on `(n·a, n·b)`". -/

/-- Affine upper bound: for `n ≥ 1` and `t` strictly inside `(n·a, n·b)`, the power is
*below* the affine envelope `n·va + s·(t − n·a)` (equal-split witness `t/n`). -/
theorem minConvPow_segNN_le_affine (a b va s : ℝ≥0) :
    ∀ {n : ℕ}, 1 ≤ n → ∀ {t : ℝ≥0}, (n : ℝ≥0) * a < t → t < (n : ℝ≥0) * b →
      minConvPow (segNN a b va s) n t
        ≤ (((n : ℝ≥0) * va + s * (t - (n : ℝ≥0) * a) : ℝ≥0) : ℝ≥0∞) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      intro t htl htr
      rw [Nat.cast_one, one_mul] at htl htr ⊢
      rw [minConvPow_one, segNN_mem a b va s t htl htr, one_mul]
  | succ n hn ih =>
      intro t htl htr
      rw [minConvPow_succ]
      -- equal split: v = t/(n+1), u = t − v.  Both interior; work bounds in ℝ.
      set N : ℝ≥0 := ((n + 1 : ℕ) : ℝ≥0) with hN
      have hN1 : (1 : ℝ≥0) ≤ N := by rw [hN]; exact_mod_cast Nat.le_add_left 1 n
      have hNpos : (0 : ℝ≥0) < N := lt_of_lt_of_le one_pos hN1
      set v : ℝ≥0 := t / N with hv
      have hvle : v ≤ t := by
        rw [hv, div_le_iff₀ hNpos]
        calc t = t * 1 := (mul_one t).symm
          _ ≤ t * N := by gcongr
      set u : ℝ≥0 := t - v with hu
      have huv : u + v = t := tsub_add_cancel_of_le hvle
      -- v ∈ (a, b)
      have hva : a < v := by rw [hv, lt_div_iff₀ hNpos, mul_comm]; exact htl
      have hvb : v < b := by rw [hv, div_lt_iff₀ hNpos, mul_comm]; exact htr
      -- u = t − t/N.  In ℝ: u = t·(N−1)/N = t·n/N.  Bounds reduce to htl/htr.
      have hcoeN : (N : ℝ) = (n : ℝ) + 1 := by rw [hN]; push_cast; ring
      have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
      have hnposR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hcoeu : (u : ℝ) = (t : ℝ) - (t : ℝ) / (N : ℝ) := by
        rw [hu, NNReal.coe_sub hvle, hv, NNReal.coe_div]
      have hnposR' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hua : (n : ℝ≥0) * a < u := by
        rw [← NNReal.coe_lt_coe]; push_cast; rw [hcoeu, hcoeN]
        have htlR : ((n : ℝ) + 1) * (a : ℝ) < (t : ℝ) := by
          have := htl; rw [← NNReal.coe_lt_coe] at this; push_cast at this; rw [hcoeN] at this; linarith
        rw [lt_sub_iff_add_lt, ← sub_pos]
        rw [show (t : ℝ) - ((n : ℝ) * a + t / ((n : ℝ) + 1))
              = ((n : ℝ) * (t - ((n : ℝ) + 1) * a)) / ((n : ℝ) + 1) by field_simp; ring]
        exact div_pos (mul_pos hnposR' (by linarith)) hnposR
      have hub : u < (n : ℝ≥0) * b := by
        rw [← NNReal.coe_lt_coe]; push_cast; rw [hcoeu, hcoeN]
        have htrR : (t : ℝ) < ((n : ℝ) + 1) * (b : ℝ) := by
          have := htr; rw [← NNReal.coe_lt_coe] at this; push_cast at this; rw [hcoeN] at this; linarith
        rw [← sub_pos]
        rw [show (n : ℝ) * b - ((t : ℝ) - t / ((n : ℝ) + 1))
              = ((n : ℝ) * (((n : ℝ) + 1) * b - t)) / ((n : ℝ) + 1) by field_simp; ring]
        exact div_pos (mul_pos hnposR' (by linarith)) hnposR
      -- assemble: the equal split gives the affine value.
      refine le_trans (minConv_le_add (minConvPow (segNN a b va s) n) (segNN a b va s) huv) ?_
      rw [segNN_mem a b va s v hva hvb]
      refine le_trans (add_le_add (ih hua hub) le_rfl) ?_
      rw [← ENNReal.coe_add]
      refine ENNReal.coe_le_coe.mpr (le_of_eq ?_)
      -- arithmetic identity: (nva + s(u-na)) + (va + s(v-a)) = (n+1)va + s(t-(n+1)a)
      have hau : (n : ℝ≥0) * a ≤ u := le_of_lt hua
      have hav : a ≤ v := le_of_lt hva
      have hsub : (u - (n : ℝ≥0) * a) + (v - a) = t - ((n : ℝ≥0) * a + a) := by
        rw [tsub_add_tsub_comm hau hav, huv]
      have hcast : ((n + 1 : ℕ) : ℝ≥0) * a = (n : ℝ≥0) * a + a := by push_cast; ring
      have hcastva : ((n + 1 : ℕ) : ℝ≥0) * va = (n : ℝ≥0) * va + va := by push_cast; ring
      calc ((n : ℝ≥0) * va + s * (u - (n : ℝ≥0) * a)) + (va + s * (v - a))
          = ((n : ℝ≥0) * va + va) + s * ((u - (n : ℝ≥0) * a) + (v - a)) := by ring
        _ = ((n : ℝ≥0) * va + va) + s * (t - ((n : ℝ≥0) * a + a)) := by rw [hsub]
        _ = ((n + 1 : ℕ) : ℝ≥0) * va + s * (t - ((n + 1 : ℕ) : ℝ≥0) * a) := by
              rw [hcastva, hcast]

/-- **Exact value of the powers** (combining the two bounds): for `n ≥ 1` and `t` strictly
inside `(n·a, n·b)`, `minConvPow (segNN a b va s) n t = n·va + s·(t − n·a)` — the `n`-fold
convolution power of an open segment is itself an open segment of the *same slope* `s` on
`(n·a, n·b)` (book Lemma 4.9, "`fⁿ` is an open segment of slope `f'` on `(na, nb)`"). -/
theorem minConvPow_segNN_eq_affine (a b va s : ℝ≥0) {n : ℕ} (hn : 1 ≤ n)
    {t : ℝ≥0} (htl : (n : ℝ≥0) * a < t) (htr : t < (n : ℝ≥0) * b) :
    minConvPow (segNN a b va s) n t
      = (((n : ℝ≥0) * va + s * (t - (n : ℝ≥0) * a) : ℝ≥0) : ℝ≥0∞) :=
  le_antisymm (minConvPow_segNN_le_affine a b va s hn htl htr)
    (minConvPow_segNN_affine_le a b va s hn htl htr)

/-! ## Toward the UPP conclusion (Lemma 4.9 proper — not closed)

The exact value `minConvPow … n t = n·va + s·(t − n·a)` on `(n·a, n·b)` is the per-segment
data; the sub-additive closure is the pointwise infimum over `n`.  Book Lemma 4.9 then
splits on the sign of `va − s·a`:

* if `va ≤ s·a` the closure is UPP from `n₀·a` with period `a`, increment `s·a`
  (the *first* segment of each new copy wins the infimum, value `n·va + s·t` on `(n·a, (n+1)·a]`);
* if `va > s·a` it is UPP from `n₀·b` with period `b`, increment `s·b`.

Closing this needs the *infimum-selection* argument — for each `t` past the rank, identify
which power `n` achieves `subadditiveClosureENN (segNN …) t` and verify the pseudo-period
step `closure (t + a) = closure t + s·a`.  That argument (which power wins, and the
overlap-of-supports geometry behind `n₀ = ⌈(b−a)/a⌉`) is **not** formalized here; the
exact-value and support lemmas above are its building blocks. -/

/-! ## Restatements (verification against the intended wording) -/

-- Open segment over `ℝ≥0∞`: affine on `(a,b)`, `⊤` outside.
example (a b va s : ℝ≥0) :
    segNN a b va s =
      fun t => if a < t ∧ t < b then ((va + s * (t - a) : ℝ≥0) : ℝ≥0∞) else ⊤ :=
  rfl

-- Goal 2: for n ≥ 1, the n-fold power vanishes (= ⊤) off the n-fold open support.
example (a b va s : ℝ≥0) {n : ℕ} (hn : 1 ≤ n) {t : ℝ≥0}
    (h : t ≤ (n : ℝ≥0) * a ∨ (n : ℝ≥0) * b ≤ t) :
    minConvPow (segNN a b va s) n t = ⊤ := by
  rcases h with h | h
  · exact minConvPow_segNN_eq_top_of_le a b va s hn h
  · exact minConvPow_segNN_eq_top_of_ge a b va s hn h

-- Book Lemma 4.9 core: `fⁿ` is an open segment of slope `s` (= `f'`) on `(n·a, n·b)`.
example (a b va s : ℝ≥0) {n : ℕ} (hn : 1 ≤ n) {t : ℝ≥0}
    (htl : (n : ℝ≥0) * a < t) (htr : t < (n : ℝ≥0) * b) :
    minConvPow (segNN a b va s) n t
      = (((n : ℝ≥0) * va + s * (t - (n : ℝ≥0) * a) : ℝ≥0) : ℝ≥0∞) :=
  minConvPow_segNN_eq_affine a b va s hn htl htr

end DeepWiki
