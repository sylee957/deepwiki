import DeepWiki.NetworkCalculus.SegmentClosureSelect
import DeepWiki.NetworkCalculus.UltimatelyPseudoPeriodic

/-! # Infimum selection for the closure of an open segment (DNC Lemma 4.9, the `va > s·a` case)

`SegmentClosureSelect` closed the book's *second* case `f(a) ≤ f'·a` (our `va ≤ s·a`): the
sub-additive closure of the open segment `segNN a b va s` is ultimately pseudo-periodic of
period `a`, anchored on the *left* of each power's support (the first segment of every new
copy wins the infimum).

This file closes the **dual** — the book's *first* case `f(a) > f'·a`, in our naming
`s·a ≤ va` — where the closure is **right-anchored** at the points `n·b`.  Because the
per-copy increment of the affine value `m·va + s·(x − m·a) = m·(va − s·a) + s·x` is
non-negative in `m` (the `va ≥ s·a` sign), the affine value is *increasing* in the copy
index, so the *smallest* power whose support contains a point wins the infimum.  For a point
`x` in the right portion `[(n−1)·b, n·b)` of copy `n`, that winning index is `n`, giving the
book's `f*(n·b − t) = n·f(b) − f'·t` for `t ∈ (0, b]`.  In the support reading this is exactly
the power-`n` affine value `n·va + s·(x − n·a)` (the two agree, since
`n·f(b) − s·t = n·va + s·(n·(b−a) − t) = n·va + s·(x − n·a)` at `x = n·b − t`).

The pieces mirror the `va ≤ s·a` case with the dual sign:

* **Selection lower bound (Goal 2):** for `s·a ≤ va` and `x` in the right portion (`n·a < x`,
  `x < n·b`, `(n−1)·b ≤ x`), *every* power dominates the candidate `n·va + s·(x − n·a)` —
  `m < n` falls right of the `m`-fold support (`= ⊤`), `m > n` is selected against by the sign
  `(n−m)(va − s·a) ≤ 0`.  Combined with power `n` itself (finite on `(n·a, n·b)`) this is the
  exact closure value.
* **Pseudo-period step + UPP (Goal 3):** the reindex `n ↦ n+1` shifting the right window by `b`
  gives `closure (u + b) = closure u + (va + s·(b−a))` for `u` past the rank, hence
  `IsUPP (subadditiveClosureENN (segNN a b va s))`.

**Book misprint, repaired here (dual of the first case).**  The book states period `b` and
increment `f'·b = s·b`.  From the value formula `closure(n·b − t) = n·f(b) − s·t` the genuine
per-period increment is `closure((n+1)·b − t) − closure(n·b − t) = f(b) = va + s·(b−a)` (the
*per-copy value* at the right end, not the slope contribution `s·b`).  They coincide only on
the boundary `va = s·a`, exactly as in the left-anchored case (whose true increment was the
per-copy value `va`, not the printed `s·a`).  We formalize the corrected increment
`c = va + s·(b−a) = f(b⁻)`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-! ## Pointwise selection lower bound (Goal 2, dual)

For `x` in the right portion `[(n−1)·b, n·b)` of copy `n` and `s·a ≤ va`, the candidate value
`n·va + s·(x − n·a)` lies below *every* convolution power at `x`.  Split on the power index `m`:

* `m = 0`: the point is `≠ 0`, so `σ⁰ = ⊤`.
* `1 ≤ m < n`: `m·b ≤ (n−1)·b ≤ x`, so the point is at/right of the `m`-fold support (`= ⊤`).
* `m ≥ n`: if the power is finite there, its value is `m·va + s·(x − m·a)`, and
  `(n−m)(va − s·a) ≤ 0` gives `n·va + s·(x − n·a) ≤` it (using `m ≥ n` and the `s·a ≤ va` sign). -/

/-- **Selection lower bound (dual).**  For `s·a ≤ va`, `0 < a`, `n ≥ 1` and `x` in the right
portion of copy `n` (`n·a < x`, `x < n·b`, `(n−1)·b ≤ x`, i.e. `n·b ≤ x + b`), the candidate
`n·va + s·(x − n·a)` is below the `m`-th convolution power at `x`, for *every* `m` — the book's
`n·f(b) − f'·t ≤ f^m(n·b − t)` (the half selecting `n` as the winning index, right-anchored). -/
theorem segNN_candidate_le_minConvPow_right (a b va s : ℝ≥0) (hsa : s * a ≤ va)
    {n : ℕ} {x : ℝ≥0}
    (hxl : (n : ℝ≥0) * a < x) (hxr : x < (n : ℝ≥0) * b) (hxb : (n : ℝ≥0) * b ≤ x + b) (m : ℕ) :
    (((n : ℝ≥0) * va + s * (x - (n : ℝ≥0) * a) : ℝ≥0) : ℝ≥0∞)
      ≤ minConvPow (segNN a b va s) m x := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- `m = 0`: power is `⊤` away from the origin.
    rw [minConvPow_zero]
    have hne : x ≠ 0 := by
      rintro rfl; exact absurd hxl (by simp)
    rw [if_neg hne]; exact le_top
  · -- `m ≥ 1`.  Either off-support (`⊤`) or the affine value.
    by_cases hmem : (m : ℝ≥0) * a < x ∧ x < (m : ℝ≥0) * b
    · -- in `m`-fold support: finiteness forces `n ≤ m` (else point is right of m's support).
      rw [minConvPow_segNN_eq_affine a b va s hm hmem.1 hmem.2]
      have hnm : n ≤ m := by
        by_contra hlt
        rw [Nat.not_le] at hlt
        -- `m < n` ⟹ `m ≤ n − 1` ⟹ `m·b ≤ (n−1)·b ≤ x`, contradicting `x < m·b`.
        have hmb : ((m + 1 : ℕ) : ℝ≥0) ≤ (n : ℝ≥0) := by exact_mod_cast hlt
        have hle : (m : ℝ≥0) * b ≤ x := by
          -- `(m+1)·b ≤ n·b ≤ x + b`, so `m·b + b ≤ x + b`, i.e. `m·b ≤ x`.
          have h1 : (m : ℝ≥0) * b + b ≤ (n : ℝ≥0) * b := by
            calc (m : ℝ≥0) * b + b = ((m + 1 : ℕ) : ℝ≥0) * b := by push_cast; ring
              _ ≤ (n : ℝ≥0) * b := by gcongr
          have h2 : (m : ℝ≥0) * b + b ≤ x + b := h1.trans hxb
          exact le_of_add_le_add_right h2
        exact absurd hmem.2 (not_lt.mpr hle)
      -- write `m = n + k` (`k = m − n ≥ 0`).
      obtain ⟨k, hk⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
      have hcastm : (m : ℝ≥0) = (n : ℝ≥0) + (k : ℝ≥0) := by rw [hk]; push_cast; ring
      rw [ENNReal.coe_le_coe]
      -- `x − m·a = (x − n·a) − k·a` (both genuine: `n·a < x` and `m·a < x`).
      have hxna : (n : ℝ≥0) * a ≤ x := le_of_lt hxl
      have hsub : x - (m : ℝ≥0) * a = (x - (n : ℝ≥0) * a) - (k : ℝ≥0) * a := by
        rw [hcastm, add_mul, ← tsub_tsub]
      rw [hsub]
      -- candidate `n·va + s·(x−n·a)` vs power `m·va + s·((x−n·a) − k·a)`.
      -- set `y = x − n·a`.  Compare `n·va + s·y` and `(n+k)·va + s·(y − k·a)`.
      set y : ℝ≥0 := x - (n : ℝ≥0) * a with hy
      -- `(n+k)·va + s·(y − k·a) ≥ n·va + s·y`:  add `k·va` and `s·(y−k·a)`; need
      -- `s·y ≤ k·va + s·(y − k·a)`, i.e. `s·(k·a) ≤ k·va` (the `s·a ≤ va` sign), with care on
      -- truncated subtraction when `y < k·a`.
      rw [hcastm, add_mul]
      -- Goal: `n·va + s·y ≤ (n·va + k·va) + s·(y ⊖ k·a)`.  `s·(k·a) ≤ k·va` (the sign).
      have hkey : s * ((k : ℝ≥0) * a) ≤ (k : ℝ≥0) * va := by
        calc s * ((k : ℝ≥0) * a) = (k : ℝ≥0) * (s * a) := by ring
          _ ≤ (k : ℝ≥0) * va := by gcongr
      -- `s·y ≤ k·va + s·(y ⊖ k·a)`, handling truncation by `k·a ≤ y` vs `y < k·a`.
      have hbound : s * y ≤ (k : ℝ≥0) * va + s * (y - (k : ℝ≥0) * a) := by
        rcases le_or_gt ((k : ℝ≥0) * a) y with hle | hlt
        · -- `k·a ≤ y`: `y = (y − k·a) + k·a`, so `s·y = s·(y−k·a) + s·(k·a) ≤ s·(y−k·a) + k·va`.
          calc s * y = s * ((y - (k : ℝ≥0) * a) + (k : ℝ≥0) * a) := by
                rw [tsub_add_cancel_of_le hle]
            _ = s * (y - (k : ℝ≥0) * a) + s * ((k : ℝ≥0) * a) := by rw [mul_add]
            _ ≤ s * (y - (k : ℝ≥0) * a) + (k : ℝ≥0) * va := by gcongr
            _ = (k : ℝ≥0) * va + s * (y - (k : ℝ≥0) * a) := by ring
        · -- `y < k·a`: `y ⊖ k·a = 0`, and `s·y ≤ s·(k·a) ≤ k·va`.
          rw [tsub_eq_zero_of_le (le_of_lt hlt), mul_zero, add_zero]
          calc s * y ≤ s * ((k : ℝ≥0) * a) := by gcongr
            _ ≤ (k : ℝ≥0) * va := hkey
      calc (n : ℝ≥0) * va + s * y
          ≤ (n : ℝ≥0) * va + ((k : ℝ≥0) * va + s * (y - (k : ℝ≥0) * a)) := by gcongr
        _ = (n : ℝ≥0) * va + (k : ℝ≥0) * va + s * (y - (k : ℝ≥0) * a) := by ring
    · rw [minConvPow_segNN_eq_top_of_not_mem a b va s hm hmem]; exact le_top

/-! ## Exact closure value on a right half-period (Goal 2, assembled)

On the right portion `[(n−1)·b, n·b)` the candidate is also an upper bound (power `n` is
finite on `(n·a, n·b)`), so the closure equals it. -/

/-- **Closure value (dual).**  For `s·a ≤ va`, `n ≥ 1` and `x` in the right portion of copy `n`
(`n·a < x`, `x < n·b`, `(n−1)·b ≤ x`), the closure of the open segment at `x` equals the
power-`n` affine value `n·va + s·(x − n·a)` — the book's `f*(n·b − t) = n·f(b) − f'·t` at
`x = n·b − t`. -/
theorem subadditiveClosureENN_segNN_eq_right (a b va s : ℝ≥0) (hsa : s * a ≤ va)
    {n : ℕ} (hn : 1 ≤ n) {x : ℝ≥0}
    (hxl : (n : ℝ≥0) * a < x) (hxr : x < (n : ℝ≥0) * b) (hxb : (n : ℝ≥0) * b ≤ x + b) :
    subadditiveClosureENN (segNN a b va s) x
      = (((n : ℝ≥0) * va + s * (x - (n : ℝ≥0) * a) : ℝ≥0) : ℝ≥0∞) := by
  rw [subadditiveClosureENN_eq_iInf]
  refine le_antisymm ?_ ?_
  · -- upper bound: the `n`-th power is finite on `(n·a, n·b)` and equals the value.
    refine iInf_le_of_le n ?_
    rw [minConvPow_segNN_eq_affine a b va s hn hxl hxr]
  · -- lower bound: candidate ≤ every power.
    exact le_iInf fun m =>
      segNN_candidate_le_minConvPow_right a b va s hsa hxl hxr hxb m

/-! ## Pseudo-period step and the UPP conclusion (Goal 3, dual)

`segOverlapRank a b = ⌈a/(b−a)⌉` is the book's `n₀ = ⌈a/(b−a)⌉` (same rank as the left case;
the OCR `⌈(b−a)/a⌉` in the proof is a misprint — the rendered fraction is `a/(b−a)`).  Past
`n₀+2`, `n·a < (n−1)·b`, so the right portion `[(n−1)·b, n·b)` of copy `n` is a genuine
sub-interval of the support `(n·a, n·b)` and shifting by `b` lands in copy `n+1`'s right
portion. -/

/-- Past the rank `n₀+2`, `n·a + b < n·b`, i.e. `n·a < (n−1)·b`: the right portion
`[(n−1)·b, n·b)` sits strictly inside the `n`-fold support.  (`b/(b−a) = a/(b−a) + 1`, so
`⌈b/(b−a)⌉ = n₀ + 1 < n`.) -/
theorem mul_add_lt_mul_of_segOverlapRank (a b : ℝ≥0) (hab : a < b) {n : ℕ}
    (hn : segOverlapRank a b + 2 ≤ n) :
    (n : ℝ≥0) * a + b < (n : ℝ≥0) * b := by
  have hsubpos : 0 < b - a := tsub_pos_of_lt hab
  -- `b < n·(b−a)`:  `n ≥ n₀ + 2`, `n₀·(b−a) ≥ a`, so `n·(b−a) ≥ a + 2(b−a) = b + (b−a) > b`.
  have hge : (segOverlapRank a b : ℝ≥0) + 2 ≤ (n : ℝ≥0) := by
    have h : ((segOverlapRank a b + 2 : ℕ) : ℝ≥0) ≤ (n : ℝ≥0) := by exact_mod_cast hn
    push_cast at h; exact h
  have hb : b < (n : ℝ≥0) * (b - a) := by
    calc b = a + (b - a) := by rw [add_tsub_cancel_of_le (le_of_lt hab)]
      _ < a + ((b - a) + (b - a)) := by
          rw [← add_assoc]; exact lt_add_of_pos_right _ hsubpos
      _ ≤ (segOverlapRank a b : ℝ≥0) * (b - a) + ((b - a) + (b - a)) := by
          gcongr; exact le_segOverlapRank_mul_sub a b hab
      _ = ((segOverlapRank a b : ℝ≥0) + 2) * (b - a) := by ring
      _ ≤ (n : ℝ≥0) * (b - a) := by gcongr
  calc (n : ℝ≥0) * a + b < (n : ℝ≥0) * a + (n : ℝ≥0) * (b - a) := by gcongr
    _ = (n : ℝ≥0) * b := by rw [← mul_add, add_tsub_cancel_of_le (le_of_lt hab)]

/-- Right half-period decomposition: any `u` past `(n₀+2)·b` is in the right portion
`[(n−1)·b, n·b)` of some copy `n ≥ n₀+2` — with `(n−1)·b ≤ u < n·b` (strict on the right) and
`n·a < u` (the portion is interior past the rank).  So the value lemma applies, and `u + b`
stays one copy up.  Witness `n = ⌊u/b⌋ + 1`. -/
theorem exists_copy_index_right (a b : ℝ≥0) (hab : a < b) {u : ℝ≥0}
    (hu : (segOverlapRank a b + 2 : ℕ) * b ≤ u) :
    ∃ n : ℕ, segOverlapRank a b + 2 ≤ n ∧
      (n : ℝ≥0) * a < u ∧ u < (n : ℝ≥0) * b ∧ (n : ℝ≥0) * b ≤ u + b := by
  have hbpos : 0 < b := lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ a) hab
  -- `n = ⌊u/b⌋ + 1`; then `(n−1)·b ≤ u < n·b` (both via `Nat.floor`), strict on the right always.
  set k : ℕ := ⌊(u / b : ℝ≥0)⌋₊ with hkdef
  refine ⟨k + 1, ?_, ?_, ?_, ?_⟩
  · -- `k + 1 ≥ n₀ + 2`:  `k ≥ n₀ + 2` from `u/b ≥ n₀ + 2` (`Nat.le_floor`).
    have hle : ((segOverlapRank a b + 2 : ℕ) : ℝ≥0) ≤ u / b := by
      rw [le_div_iff₀ hbpos]; exact_mod_cast hu
    have hkge : segOverlapRank a b + 2 ≤ k := Nat.le_floor hle
    omega
  · -- `(k+1)·a < u`:  `(k+1)·a + b < (k+1)·b` (past rank) and `(k+1)·b ≤ u + b`, so
    -- `(k+1)·a + b < u + b`, giving `(k+1)·a < u`.
    have hk2 : segOverlapRank a b + 2 ≤ k + 1 := by
      have hle : ((segOverlapRank a b + 2 : ℕ) : ℝ≥0) ≤ u / b := by
        rw [le_div_iff₀ hbpos]; exact_mod_cast hu
      have hkge : segOverlapRank a b + 2 ≤ k := Nat.le_floor hle
      omega
    have hstr := mul_add_lt_mul_of_segOverlapRank a b hab hk2
    -- `(k+1)·b ≤ u + b`:  `k ≤ u/b`, so `k·b ≤ u`, and `(k+1)·b = k·b + b ≤ u + b`.
    have hkle : (k : ℝ≥0) * b ≤ u := by
      rw [← le_div_iff₀ hbpos]; exact Nat.floor_le (by positivity)
    have hkb : ((k + 1 : ℕ) : ℝ≥0) * b ≤ u + b := by
      calc ((k + 1 : ℕ) : ℝ≥0) * b = (k : ℝ≥0) * b + b := by push_cast; ring
        _ ≤ u + b := by gcongr
    have : ((k + 1 : ℕ) : ℝ≥0) * a + b < u + b := lt_of_lt_of_le hstr hkb
    exact lt_of_add_lt_add_right this
  · -- `u < (k+1)·b`:  `u/b < k + 1` (`Nat.lt_floor_add_one`), transported.
    have hlt : u / b < ((k + 1 : ℕ) : ℝ≥0) := by push_cast; exact Nat.lt_floor_add_one _
    rw [div_lt_iff₀ hbpos] at hlt
    exact hlt
  · -- `(k+1)·b ≤ u + b`:  `k·b ≤ u`.
    have hkle : (k : ℝ≥0) * b ≤ u := by
      rw [← le_div_iff₀ hbpos]; exact Nat.floor_le (by positivity)
    calc ((k + 1 : ℕ) : ℝ≥0) * b = (k : ℝ≥0) * b + b := by push_cast; ring
      _ ≤ u + b := by gcongr

/-- **Lemma 4.9 (`s·a ≤ va` case).**  The sub-additive closure of the open segment
`segNN a b va s` (with `0 < a < b`) is ultimately pseudo-periodic of period `b` and increment
`va + s·(b−a) = f(b⁻)` (the *per-copy value* at the right end), from the rank `(n₀+2)·b` with
`n₀ = ⌈a/(b−a)⌉`.  The book states the increment as `s·b`; from `closure(n·b − t) = n·f(b) − s·t`
the true increment is `f(b) = va + s·(b−a)` (these coincide only when `va = s·a`). -/
theorem isUPPWith_subadditiveClosureENN_segNN_right (a b va s : ℝ≥0) (ha : 0 < a) (hab : a < b)
    (hsa : s * a ≤ va) :
    IsUPPWith (subadditiveClosureENN (segNN a b va s))
      ((segOverlapRank a b + 2 : ℕ) * b) b (((va + s * (b - a) : ℝ≥0) : ℝ≥0∞)) := by
  have hbpos : 0 < b := lt_of_lt_of_le ha (le_of_lt hab)
  refine ⟨hbpos, fun u hu => ?_⟩
  obtain ⟨n, hn, hxl, hxr, hxb⟩ := exists_copy_index_right a b hab hu
  have hn1 : 1 ≤ n := by omega
  -- value at `u` (copy `n`).
  have hval : subadditiveClosureENN (segNN a b va s) u
      = (((n : ℝ≥0) * va + s * (u - (n : ℝ≥0) * a) : ℝ≥0) : ℝ≥0∞) :=
    subadditiveClosureENN_segNN_eq_right a b va s hsa hn1 hxl hxr hxb
  -- value at `u + b` (copy `n+1`): need `(n+1)·a < u + b`, `u + b < (n+1)·b`, `(n+1)·b ≤ u + 2b`.
  have hna : ((n + 1 : ℕ) : ℝ≥0) * a = (n : ℝ≥0) * a + a := by push_cast; ring
  have hnb : ((n + 1 : ℕ) : ℝ≥0) * b = (n : ℝ≥0) * b + b := by push_cast; ring
  have hxl' : ((n + 1 : ℕ) : ℝ≥0) * a < u + b := by
    rw [hna]; exact add_lt_add hxl hab
  have hxr' : u + b < ((n + 1 : ℕ) : ℝ≥0) * b := by
    rw [hnb]; gcongr
  have hxb' : ((n + 1 : ℕ) : ℝ≥0) * b ≤ (u + b) + b := by
    rw [hnb]; gcongr
  have hn1' : 1 ≤ n + 1 := Nat.le_add_left 1 n
  have hval' : subadditiveClosureENN (segNN a b va s) (u + b)
      = ((((n + 1 : ℕ) : ℝ≥0) * va + s * ((u + b) - ((n + 1 : ℕ) : ℝ≥0) * a) : ℝ≥0) : ℝ≥0∞) :=
    subadditiveClosureENN_segNN_eq_right a b va s hsa hn1' hxl' hxr' hxb'
  rw [hval', hval, ← ENNReal.coe_add]
  refine congrArg _ ?_
  -- arithmetic: `(n+1)·va + s·((u+b) − (n+1)·a) = (n·va + s·(u − n·a)) + (va + s·(b−a))`.
  have hna_le : (n : ℝ≥0) * a ≤ u := le_of_lt hxl
  have hab_le : a ≤ b := le_of_lt hab
  -- `(u + b) − ((n+1)·a) = (u − n·a) + (b − a)`.
  have hsub : (u + b) - ((n + 1 : ℕ) : ℝ≥0) * a = (u - (n : ℝ≥0) * a) + (b - a) := by
    rw [hna]; exact (tsub_add_tsub_comm hna_le hab_le).symm
  rw [hsub, mul_add]
  have hcastva : ((n + 1 : ℕ) : ℝ≥0) * va = (n : ℝ≥0) * va + va := by push_cast; ring
  rw [hcastva]
  ring

/-- **Lemma 4.9 (`s·a ≤ va` case), existential form.**  The sub-additive closure of an open
segment with `s·a ≤ va` and `0 < a < b` is ultimately pseudo-periodic. -/
theorem isUPP_subadditiveClosureENN_segNN_right (a b va s : ℝ≥0) (ha : 0 < a) (hab : a < b)
    (hsa : s * a ≤ va) :
    IsUPP (subadditiveClosureENN (segNN a b va s)) :=
  (isUPPWith_subadditiveClosureENN_segNN_right a b va s ha hab hsa).isUPP

/-! ## Both cases reconciled: Lemma 4.9 unconditionally -/

/-- **Lemma 4.9 (both cases).**  The sub-additive closure of *any* open segment
`segNN a b va s` with `0 < a < b` is ultimately pseudo-periodic — combining the left-anchored
case `va ≤ s·a` (period `a`) and the right-anchored case `s·a ≤ va` (period `b`).  The boundary
`va = s·a` falls under both. -/
theorem isUPP_subadditiveClosureENN_segNN_of_lt (a b va s : ℝ≥0) (ha : 0 < a) (hab : a < b) :
    IsUPP (subadditiveClosureENN (segNN a b va s)) := by
  rcases le_total va (s * a) with h | h
  · exact isUPP_subadditiveClosureENN_segNN a b va s ha hab h
  · exact isUPP_subadditiveClosureENN_segNN_right a b va s ha hab h

/-! ## Restatements (verification against the intended wording) -/

-- Goal 2 (dual): right-anchored closure value `f*(n·b − t) = n·f(b) − f'·t`, here in support
-- coordinates `closure x = n·va + s·(x − n·a)` on the right portion `[(n−1)·b, n·b)`.
example (a b va s : ℝ≥0) (hsa : s * a ≤ va) {n : ℕ} (hn : 1 ≤ n) {x : ℝ≥0}
    (hxl : (n : ℝ≥0) * a < x) (hxr : x < (n : ℝ≥0) * b) (hxb : (n : ℝ≥0) * b ≤ x + b) :
    subadditiveClosureENN (segNN a b va s) x
      = (((n : ℝ≥0) * va + s * (x - (n : ℝ≥0) * a) : ℝ≥0) : ℝ≥0∞) :=
  subadditiveClosureENN_segNN_eq_right a b va s hsa hn hxl hxr hxb

-- Goal 3 (dual): the closure of an open segment with `s·a ≤ va` is ultimately pseudo-periodic
-- (period `b`, increment `va + s·(b−a) = f(b⁻)`).
example (a b va s : ℝ≥0) (ha : 0 < a) (hab : a < b) (hsa : s * a ≤ va) :
    IsUPPWith (subadditiveClosureENN (segNN a b va s))
      ((segOverlapRank a b + 2 : ℕ) * b) b (((va + s * (b - a) : ℝ≥0) : ℝ≥0∞)) :=
  isUPPWith_subadditiveClosureENN_segNN_right a b va s ha hab hsa

-- Lemma 4.9, unconditional: the closure of any open segment is ultimately pseudo-periodic.
example (a b va s : ℝ≥0) (ha : 0 < a) (hab : a < b) :
    IsUPP (subadditiveClosureENN (segNN a b va s)) :=
  isUPP_subadditiveClosureENN_segNN_of_lt a b va s ha hab

end DeepWiki
