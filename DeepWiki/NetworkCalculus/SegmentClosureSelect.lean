import DeepWiki.NetworkCalculus.SegmentClosureUPP
import DeepWiki.NetworkCalculus.UltimatelyPseudoPeriodic

/-! # Infimum selection for the closure of an open segment (DNC Lemma 4.9, the `va ≤ s·a` case)

`SegmentClosureUPP` proved the per-segment geometry: the `n`-fold (min,+) convolution power
`minConvPow (segNN a b va s) n` of an open segment is itself an open segment of the *same*
slope `s` on `(n·a, n·b)` (`minConvPow_segNN_eq_affine`) and `⊤` outside.  The sub-additive
closure is the pointwise infimum `closure t = ⨅ₙ σⁿ t` (`subadditiveClosureENN_eq_iInf`).

This file closes the **infimum-selection** half of Lemma 4.9 in the book's *second* case
`f(a) ≤ f'·a` — in our naming `va ≤ s·a` — where the closure is ultimately pseudo-periodic
of period `a`.  The pieces:

* **Overlap arithmetic (Goal 1):** for `0 < a < b` and `a < n·(b−a)`, consecutive supports
  chain-cover: `(n+1)·a < n·b`, so `(n·a, n·b) ∪ ((n+1)·a, (n+1)·b)` is an interval, and the
  supports cover `(n₀·a, +∞)` from the rank `n₀ = ⌈a/(b−a)⌉`.
* **Pointwise selection lower bound (Goal 2):** for `t ∈ (0, a]` and `va ≤ s·a`, *every*
  power dominates the candidate `n·va + s·t` — `m ≤ n` by the sign of `(n−m)(va − s·a) ≤ 0`,
  `m > n` because the point falls left of the `m`-fold support (`= ⊤`).  Combined with the
  matching upper bound (power `n` itself, on `(n·a, n·b)` past the rank) this gives the exact
  closure value `closure (n·a + t) = n·va + s·t` (the book's `f*(na+t) = nf(a) + f't`).
* **Pseudo-period step + UPP (Goal 3):** the reindex `n ↦ n+1` shifting the half-period
  window gives `closure (u + a) = closure u + va` for `u` past the rank, hence
  `IsUPP (subadditiveClosureENN (segNN a b va s))`.

**Book misprint, repaired here.**  The book states the increment as `f'·a = s·a`; from the
value formula `closure(na+t) = n·va + s·t` the genuine per-period increment is
`closure((n+1)a+t) − closure(na+t) = va = f(a)` (the *per-copy value*, not the slope
contribution `s·a`).  They coincide only on the boundary `va = s·a`.  We formalize the
corrected increment `c = va`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-! ## Overlap rank and chain-covering arithmetic (Goal 1) -/

/-- The book's overlap rank `n₀ = ⌈a/(b−a)⌉` (over `ℝ≥0`): the first power level from which
consecutive segment supports overlap.  When `a < b` it satisfies `a ≤ n₀·(b−a)`. -/
noncomputable def segOverlapRank (a b : ℝ≥0) : ℕ := ⌈a / (b - a)⌉₊

/-- Past the overlap rank the supports cover on the left: `a ≤ n₀·(b−a)`, i.e. the first
copy's right end reaches the second copy's left end. -/
theorem le_segOverlapRank_mul_sub (a b : ℝ≥0) (hab : a < b) :
    a ≤ (segOverlapRank a b : ℝ≥0) * (b - a) := by
  have hpos : 0 < b - a := tsub_pos_of_lt hab
  rw [← div_le_iff₀ hpos]
  exact Nat.le_ceil _

/-- **Overlap fact (Goal 1).** For `0 < a < b` and `a < n·(b−a)`, consecutive supports chain:
`(n+1)·a < n·b`.  Hence `(n·a, n·b) ∪ ((n+1)·a, (n+1)·b)` is a single interval covering
`(n·a, (n+1)·b)` (the supports overlap once past the rank `n₀ = ⌈a/(b−a)⌉`). -/
theorem succ_mul_lt_mul_of_lt (a b : ℝ≥0) (hab : a < b) {n : ℕ}
    (hn : a < (n : ℝ≥0) * (b - a)) :
    ((n + 1 : ℕ) : ℝ≥0) * a < (n : ℝ≥0) * b := by
  calc ((n + 1 : ℕ) : ℝ≥0) * a = (n : ℝ≥0) * a + a := by push_cast; ring
    _ < (n : ℝ≥0) * a + (n : ℝ≥0) * (b - a) := by gcongr
    _ = (n : ℝ≥0) * b := by rw [← mul_add, add_tsub_cancel_of_le (le_of_lt hab)]

/-! ## Pointwise selection lower bound (Goal 2)

For `t ∈ (0, a]` and `va ≤ s·a`, the candidate value `n·va + s·t` lies below *every*
convolution power at the point `n·a + t`.  Split on the power index `m`:

* `m = 0`: the point is `≠ 0`, so `σ⁰ = ⊤`.
* `1 ≤ m ≤ n`: if the power is finite there, its value is `m·va + s·t + s·(n−m)·a`, and
  `(n−m)(va − s·a) ≤ 0` gives `n·va + s·t ≤` it.
* `m > n`: the point `n·a + t ≤ (n+1)·a ≤ m·a` falls left of the `m`-fold support, so `= ⊤`. -/

/-- **Selection lower bound.**  For `va ≤ s·a`, `0 < a`, `t ∈ (0, a]` and `n ≥ 1`, the
candidate `n·va + s·t` is below the `m`-th convolution power at `n·a + t`, for *every* `m` —
the book's `nf(a) + f't ≤ f^m(na+t)` (the half that selects `n` as the winning index). -/
theorem segNN_candidate_le_minConvPow (a b va s : ℝ≥0) (hsa : va ≤ s * a)
    (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) {t : ℝ≥0} (ht0 : 0 < t) (hta : t ≤ a) (m : ℕ) :
    (((n : ℝ≥0) * va + s * t : ℝ≥0) : ℝ≥0∞)
      ≤ minConvPow (segNN a b va s) m ((n : ℝ≥0) * a + t) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- `m = 0`: power is `⊤` away from the origin.
    rw [minConvPow_zero]
    have hne : (n : ℝ≥0) * a + t ≠ 0 := by positivity
    rw [if_neg hne]; exact le_top
  · -- `m ≥ 1`.  Either off-support (`⊤`) or the affine value.
    by_cases hmem : (m : ℝ≥0) * a < (n : ℝ≥0) * a + t ∧ (n : ℝ≥0) * a + t < (m : ℝ≥0) * b
    · -- in `m`-fold support: read the affine value and compare via `(n−m)(va − s·a) ≤ 0`.
      rw [minConvPow_segNN_eq_affine a b va s hm hmem.1 hmem.2]
      -- finiteness of the affine value forces `m ≤ n` (else point is left of support).
      have hmle : m ≤ n := by
        by_contra hlt
        rw [Nat.not_le] at hlt
        -- `n < m` ⟹ `n + 1 ≤ m` ⟹ `m·a ≥ (n+1)·a ≥ n·a + t`, contradicting `m·a < n·a + t`.
        have hge : (n : ℝ≥0) * a + t ≤ (m : ℝ≥0) * a := by
          have h1 : (n : ℝ≥0) * a + t ≤ (n : ℝ≥0) * a + a := by gcongr
          have h2 : (n : ℝ≥0) * a + a ≤ (m : ℝ≥0) * a := by
            have hcm : ((n + 1 : ℕ) : ℝ≥0) ≤ (m : ℝ≥0) := by exact_mod_cast hlt
            calc (n : ℝ≥0) * a + a = ((n + 1 : ℕ) : ℝ≥0) * a := by push_cast; ring
              _ ≤ (m : ℝ≥0) * a := by gcongr
          exact h1.trans h2
        exact absurd hmem.1 (not_lt.mpr hge)
      -- write `n = m + k` (`k = n − m ≥ 0`); ℝ≥0 has no `Nat.cast_sub`, so go through `+`.
      obtain ⟨k, hk⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
      have hcastn : (n : ℝ≥0) = (m : ℝ≥0) + (k : ℝ≥0) := by rw [hk]; push_cast; ring
      rw [ENNReal.coe_le_coe]
      -- `m·va + s·((n·a + t) − m·a) = m·va + s·t + s·(k·a)` since `(n·a + t) − m·a = k·a + t`.
      have hsub : (n : ℝ≥0) * a + t - (m : ℝ≥0) * a = (k : ℝ≥0) * a + t := by
        rw [hcastn]
        rw [show ((m : ℝ≥0) + (k : ℝ≥0)) * a + t = (m : ℝ≥0) * a + ((k : ℝ≥0) * a + t) by ring,
          add_tsub_cancel_left]
      rw [hsub, mul_add]
      -- reduce to `k·va ≤ s·(k·a)` (the `va ≤ s·a` sign).
      have hkey : (k : ℝ≥0) * va ≤ s * ((k : ℝ≥0) * a) := by
        calc (k : ℝ≥0) * va ≤ (k : ℝ≥0) * (s * a) := by gcongr
          _ = s * ((k : ℝ≥0) * a) := by ring
      calc (n : ℝ≥0) * va + s * t
          = (m : ℝ≥0) * va + (k : ℝ≥0) * va + s * t := by rw [hcastn]; ring
        _ ≤ (m : ℝ≥0) * va + s * ((k : ℝ≥0) * a) + s * t := by gcongr
        _ = (m : ℝ≥0) * va + (s * ((k : ℝ≥0) * a) + s * t) := by ring
    · rw [minConvPow_segNN_eq_top_of_not_mem a b va s hm hmem]; exact le_top

/-! ## Exact closure value on a half-period (Goal 2, assembled)

Past the rank `(n₀+1)·a`, the candidate is also an upper bound (power `n` itself is finite on
`(n·a, n·b)`), so the closure equals it. -/

/-- **Closure value (Goal 2).**  For `va ≤ s·a`, `0 < a < b`, `t ∈ (0, a]` and
`n ≥ segOverlapRank a b + 1`, the closure of the open segment at `n·a + t` is the open
segment value `n·va + s·t` — the book's `f*(na+t) = nf(a) + f't`. -/
theorem subadditiveClosureENN_segNN_eq (a b va s : ℝ≥0) (hab : a < b) (hsa : va ≤ s * a)
    {n : ℕ} (hn : segOverlapRank a b + 1 ≤ n) {t : ℝ≥0} (ht0 : 0 < t) (hta : t ≤ a) :
    subadditiveClosureENN (segNN a b va s) ((n : ℝ≥0) * a + t)
      = (((n : ℝ≥0) * va + s * t : ℝ≥0) : ℝ≥0∞) := by
  have ha : 0 < a := lt_of_lt_of_le ht0 hta
  have hn1 : 1 ≤ n := le_trans (Nat.le_add_left 1 _) hn
  have hsubpos : 0 < b - a := tsub_pos_of_lt hab
  -- `a < n·(b−a)` past the rank `n₀+1`: `n·(b−a) ≥ n₀·(b−a) + (b−a) ≥ a + (b−a) > a`.
  have hstrict : a < (n : ℝ≥0) * (b - a) := by
    have hge : (segOverlapRank a b : ℝ≥0) + 1 ≤ (n : ℝ≥0) := by
      have h : ((segOverlapRank a b + 1 : ℕ) : ℝ≥0) ≤ (n : ℝ≥0) := by exact_mod_cast hn
      push_cast at h; exact h
    calc a < a + (b - a) := lt_add_of_pos_right _ hsubpos
      _ ≤ (segOverlapRank a b : ℝ≥0) * (b - a) + (b - a) := by
          gcongr; exact le_segOverlapRank_mul_sub a b hab
      _ = ((segOverlapRank a b : ℝ≥0) + 1) * (b - a) := by ring
      _ ≤ (n : ℝ≥0) * (b - a) := by gcongr
  rw [subadditiveClosureENN_eq_iInf]
  refine le_antisymm ?_ ?_
  · -- upper bound: the `n`-th power is finite on `(n·a, n·b)` and equals the value.
    refine iInf_le_of_le n ?_
    have hl : (n : ℝ≥0) * a < (n : ℝ≥0) * a + t := lt_add_of_pos_right _ ht0
    -- `n·a + t < n·b`: `t ≤ a < n·(b−a)`.
    have hr : (n : ℝ≥0) * a + t < (n : ℝ≥0) * b := by
      calc (n : ℝ≥0) * a + t ≤ (n : ℝ≥0) * a + a := by gcongr
        _ < (n : ℝ≥0) * a + (n : ℝ≥0) * (b - a) := by gcongr
        _ = (n : ℝ≥0) * b := by rw [← mul_add, add_tsub_cancel_of_le (le_of_lt hab)]
    rw [minConvPow_segNN_eq_affine a b va s hn1 hl hr]
    rw [ENNReal.coe_le_coe]
    have : (n : ℝ≥0) * a + t - (n : ℝ≥0) * a = t := by rw [add_comm, add_tsub_cancel_right]
    rw [this]
  · -- lower bound: candidate ≤ every power.
    exact le_iInf fun m =>
      segNN_candidate_le_minConvPow a b va s hsa ha hn1 ht0 hta m

/-! ## Pseudo-period step and the UPP conclusion (Goal 3) -/

/-- Half-period decomposition: any `u` past `(n₀+2)·a` is `n·a + t` with `t ∈ (0, a]` and the
copy index `n ≥ n₀+1` (so the closure-value lemma applies, and `u + a` stays in range). -/
theorem exists_copy_index (a b : ℝ≥0) (ha : 0 < a) {u : ℝ≥0}
    (hu : (segOverlapRank a b + 2 : ℕ) * a ≤ u) :
    ∃ n : ℕ, segOverlapRank a b + 1 ≤ n ∧ ∃ t : ℝ≥0, 0 < t ∧ t ≤ a ∧ u = (n : ℝ≥0) * a + t := by
  -- `k = ⌈u/a⌉`, `n = k − 1`; `t = u − n·a ∈ (0, a]`.
  have hupos : 0 < u := lt_of_lt_of_le (by positivity) hu
  have hkpos : 1 ≤ ⌈(u / a : ℝ≥0)⌉₊ := by
    rw [Nat.one_le_ceil_iff]; exact div_pos hupos ha
  -- `⌈u/a⌉ ≥ n₀ + 2` from `u/a ≥ n₀ + 2` (`Nat.ceil_mono`).
  have hk2 : segOverlapRank a b + 2 ≤ ⌈(u / a : ℝ≥0)⌉₊ := by
    have hle : ((segOverlapRank a b + 2 : ℕ) : ℝ≥0) ≤ u / a := by
      rw [le_div_iff₀ ha]; exact_mod_cast hu
    calc segOverlapRank a b + 2 = ⌈((segOverlapRank a b + 2 : ℕ) : ℝ≥0)⌉₊ := by
          rw [Nat.ceil_natCast]
      _ ≤ ⌈(u / a : ℝ≥0)⌉₊ := Nat.ceil_mono hle
  set n : ℕ := ⌈(u / a : ℝ≥0)⌉₊ - 1 with hn
  have hkeq : ⌈(u / a : ℝ≥0)⌉₊ = n + 1 := by omega
  have hkn : ((n + 1 : ℕ) : ℝ≥0) = (n : ℝ≥0) + 1 := by push_cast; ring
  -- the two ceiling bounds, transported to `n·a < u ≤ (n+1)·a`.
  have hub : u ≤ ((n : ℝ≥0) + 1) * a := by
    rw [← hkn, ← div_le_iff₀ ha, ← hkeq]; exact Nat.le_ceil _
  have hlb : (n : ℝ≥0) * a < u := by
    rw [← lt_div_iff₀ ha]
    have hlt : n < ⌈(u / a : ℝ≥0)⌉₊ := by omega
    exact Nat.lt_ceil.mp hlt
  refine ⟨n, by omega, u - (n : ℝ≥0) * a, tsub_pos_of_lt hlb, ?_, ?_⟩
  · rw [tsub_le_iff_right]
    calc u ≤ ((n : ℝ≥0) + 1) * a := hub
      _ = a + (n : ℝ≥0) * a := by ring
  · rw [add_comm, tsub_add_cancel_of_le (le_of_lt hlb)]

/-- **Lemma 4.9 (`va ≤ s·a` case).**  The sub-additive closure of the open segment
`segNN a b va s` (with `0 < a < b`) is ultimately pseudo-periodic of period `a` and increment
`va` (the *per-copy value*), from the rank `(n₀+2)·a` with `n₀ = ⌈a/(b−a)⌉`.  The book states
the increment as `s·a`; from `closure(na+t) = n·va + s·t` the true increment is `va` (these
coincide only when `va = s·a`). -/
theorem isUPPWith_subadditiveClosureENN_segNN (a b va s : ℝ≥0) (ha : 0 < a) (hab : a < b)
    (hsa : va ≤ s * a) :
    IsUPPWith (subadditiveClosureENN (segNN a b va s))
      ((segOverlapRank a b + 2 : ℕ) * a) a ((va : ℝ≥0∞)) := by
  refine ⟨ha, fun u hu => ?_⟩
  obtain ⟨n, hn, t, ht0, hta, rfl⟩ := exists_copy_index a b ha hu
  -- value at `u = n·a + t` and at `u + a = (n+1)·a + t`.
  have hval : subadditiveClosureENN (segNN a b va s) ((n : ℝ≥0) * a + t)
      = (((n : ℝ≥0) * va + s * t : ℝ≥0) : ℝ≥0∞) :=
    subadditiveClosureENN_segNN_eq a b va s hab hsa hn ht0 hta
  have hshift : (n : ℝ≥0) * a + t + a = ((n + 1 : ℕ) : ℝ≥0) * a + t := by push_cast; ring
  have hn' : segOverlapRank a b + 1 ≤ n + 1 := Nat.le_succ_of_le hn
  have hval' : subadditiveClosureENN (segNN a b va s) (((n + 1 : ℕ) : ℝ≥0) * a + t)
      = ((((n + 1 : ℕ) : ℝ≥0) * va + s * t : ℝ≥0) : ℝ≥0∞) :=
    subadditiveClosureENN_segNN_eq a b va s hab hsa hn' ht0 hta
  rw [hshift, hval', hval]
  rw [← ENNReal.coe_add]
  refine congrArg _ ?_
  push_cast; ring

/-- **Lemma 4.9 (`va ≤ s·a` case), existential form.**  The sub-additive closure of an open
segment with `va ≤ s·a` and `0 < a < b` is ultimately pseudo-periodic. -/
theorem isUPP_subadditiveClosureENN_segNN (a b va s : ℝ≥0) (ha : 0 < a) (hab : a < b)
    (hsa : va ≤ s * a) :
    IsUPP (subadditiveClosureENN (segNN a b va s)) :=
  (isUPPWith_subadditiveClosureENN_segNN a b va s ha hab hsa).isUPP

/-! ## Restatements (verification against the intended wording) -/

-- Goal 1: consecutive supports overlap past the rank — `(n+1)·a < n·b`.
example (a b : ℝ≥0) (hab : a < b) {n : ℕ} (hn : a < (n : ℝ≥0) * (b - a)) :
    ((n + 1 : ℕ) : ℝ≥0) * a < (n : ℝ≥0) * b :=
  succ_mul_lt_mul_of_lt a b hab hn

-- Goal 2: closure value on a half-period, `f*(na+t) = nf(a) + f't` (book, case `f(a) ≤ f'a`).
example (a b va s : ℝ≥0) (hab : a < b) (hsa : va ≤ s * a)
    {n : ℕ} (hn : segOverlapRank a b + 1 ≤ n) {t : ℝ≥0} (ht0 : 0 < t) (hta : t ≤ a) :
    subadditiveClosureENN (segNN a b va s) ((n : ℝ≥0) * a + t)
      = (((n : ℝ≥0) * va + s * t : ℝ≥0) : ℝ≥0∞) :=
  subadditiveClosureENN_segNN_eq a b va s hab hsa hn ht0 hta

-- Goal 3: the closure of an open segment with `va ≤ s·a` is ultimately pseudo-periodic.
example (a b va s : ℝ≥0) (ha : 0 < a) (hab : a < b) (hsa : va ≤ s * a) :
    IsUPP (subadditiveClosureENN (segNN a b va s)) :=
  isUPP_subadditiveClosureENN_segNN a b va s ha hab hsa

end DeepWiki
