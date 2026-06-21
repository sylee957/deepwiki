import DeepWiki.NetworkCalculus.UltimatelyPseudoPeriodic

/-! # Finite representation of UPP functions: pseudo-periodic sequences
The *computable* layer toward an executable (min,plus) calculator. A `UppSeq` stores a finite
prefix `vals` of values `f(0), …, f(L-1)` together with a positive `period` and an `incr`-ement; it
denotes the discrete pseudo-periodic sequence `evalNat : ℕ → V` with `f(n) = f(n - period) + incr`
for `n ≥ L`. `evalNat` is native-compilable (`#eval`-able), and `evalNat_add_period` is its discrete
pseudo-periodicity. (The step-function reading `ℝ≥0 → V` that ties this to the semantic
`IsUPPWith`/`IsUPP` layer is the next step.) -/

namespace DeepWiki

open scoped NNReal

/-- A finite representation of a discrete ultimately-pseudo-periodic sequence: the stored prefix
`vals` (`= f(0), …, f(vals.length-1)`, the transient part plus one full period), a positive
`period`, and the per-period `incr`-ement. The invariants `0 < period ≤ vals.length` guarantee one
full period is stored (so the pseudo-periodic extension is well-defined). -/
structure UppSeq (V : Type*) where
  /-- Stored values `f(0), …, f(vals.length-1)` (transient + one period). -/
  vals : List V
  /-- The per-period increment `c`. -/
  incr : V
  /-- The period `d`. -/
  period : ℕ
  /-- The period is positive. -/
  hperiod : 0 < period
  /-- At least one full period is stored. -/
  hlen : period ≤ vals.length

namespace UppSeq

variable {V : Type*}

/-- The denoted discrete sequence `f : ℕ → V`: stored values up to `vals.length`, then extended
pseudo-periodically by `f(n) = f(n - period) + incr`. Native-compilable. -/
def evalNat [Add V] (r : UppSeq V) (n : ℕ) : V :=
  if hn : n < r.vals.length then r.vals.get ⟨n, hn⟩
  else r.evalNat (n - r.period) + r.incr
termination_by n
decreasing_by
  have := r.hperiod; have := r.hlen
  exact Nat.sub_lt (by omega) r.hperiod

/-- The pseudo-period step on the sequence: `f(n + period) = f(n) + incr` once `n` reaches the
periodic part (`n ≥ vals.length - period`). The discrete `IsUPPWith` of the representation. -/
theorem evalNat_add_period [Add V] (r : UppSeq V) {n : ℕ}
    (hn : r.vals.length - r.period ≤ n) :
    r.evalNat (n + r.period) = r.evalNat n + r.incr := by
  have hge : ¬ (n + r.period < r.vals.length) := by have := r.hlen; omega
  conv_lhs => rw [evalNat.eq_def]
  rw [dif_neg hge, Nat.add_sub_cancel]

/-- Iterated pseudo-period: `f(n + k·period) = f(n) + k·incr` past the rank — `period` scaled by any
`k`, the discrete analogue of `IsUPPWith.iterate`. Lets sequences with commensurable periods be put
on a common period (their `lcm`). -/
theorem evalNat_add_mul_period [AddMonoid V] (r : UppSeq V) (k : ℕ) {n : ℕ}
    (hn : r.vals.length - r.period ≤ n) :
    r.evalNat (n + k * r.period) = r.evalNat n + k • r.incr := by
  induction k with
  | zero => simp
  | succ j ih =>
    have hjn : r.vals.length - r.period ≤ n + j * r.period := le_trans hn (Nat.le_add_right _ _)
    have e : n + (j + 1) * r.period = (n + j * r.period) + r.period := by ring
    rw [e, r.evalNat_add_period hjn, ih, succ_nsmul, add_assoc]

/-- `evalNat` over a multiple of any period-divisor: if `r.period ∣ e`, then
`f(m + q·e) = f(m) + q·((e/d_f)·c_f)` past the rank (generalises `evalNat_add_mul_period` to any
common period `e`, e.g. an `lcm`). -/
theorem evalNat_add_mul_of_dvd [AddMonoid V] (r : UppSeq V) {e : ℕ} (he : r.period ∣ e) (q : ℕ)
    {m : ℕ} (hm : r.vals.length - r.period ≤ m) :
    r.evalNat (m + q * e) = r.evalNat m + q • ((e / r.period) • r.incr) := by
  have h1 : q * e = q * (e / r.period) * r.period := by rw [mul_assoc, Nat.div_mul_cancel he]
  rw [h1, r.evalNat_add_mul_period (q * (e / r.period)) hm, mul_smul]

/-- **Dominant-slope crossover.** If `r` has strictly smaller asymptotic slope than `s`
(`(d/d_r)·c_r < (d/d_s)·c_s` over the common period `d = lcm`), then `r` is eventually pointwise
`≤ s`. Needs `V` Archimedean: the linearly-growing slope gap eventually dominates the bounded
transient window `[R, R+d)`. The kernel of general `min`-of-UPP (and the non-balanced Lemma 4.4). -/
theorem evalNat_eventually_le [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Archimedean V]
    (r s : UppSeq V)
    (hslope : (Nat.lcm r.period s.period / r.period) • r.incr
            < (Nat.lcm r.period s.period / s.period) • s.incr) :
    ∃ N, ∀ n, N ≤ n → r.evalNat n ≤ s.evalNat n := by
  set d := Nat.lcm r.period s.period with hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (Nat.lcm_ne_zero r.hperiod.ne' s.hperiod.ne')
  set cr := (d / r.period) • r.incr with hcr
  set cs := (d / s.period) • s.incr with hcs
  set R := max (r.vals.length - r.period) (s.vals.length - s.period) with hR
  have hwin : (Finset.range d).Nonempty := ⟨0, Finset.mem_range.mpr hd0⟩
  set M := (Finset.range d).sup' hwin (fun rem => r.evalNat (R + rem)) with hM
  set ms := (Finset.range d).inf' hwin (fun rem => s.evalNat (R + rem)) with hms
  have hδ : 0 < cs - cr := sub_pos.mpr hslope
  obtain ⟨Q, hQ⟩ := Archimedean.arch (M - ms) hδ
  refine ⟨R + Q * d, fun n hn => ?_⟩
  have hRn : R ≤ n := by omega
  set rem := (n - R) % d with hrem
  set q := (n - R) / d with hq
  have hremlt : rem < d := Nat.mod_lt _ hd0
  have hsplit : d * q + rem = n - R := Nat.div_add_mod (n - R) d
  have hdecomp : n = (R + rem) + q * d := by rw [mul_comm q d]; omega
  have hqQ : Q ≤ q := by rw [hq]; exact (Nat.le_div_iff_mul_le hd0).mpr (by omega)
  have hrn : r.evalNat n = r.evalNat (R + rem) + q • cr := by
    rw [hdecomp]
    exact r.evalNat_add_mul_of_dvd (hd ▸ Nat.dvd_lcm_left r.period s.period) q (by omega)
  have hsn : s.evalNat n = s.evalNat (R + rem) + q • cs := by
    rw [hdecomp]
    exact s.evalNat_add_mul_of_dvd (hd ▸ Nat.dvd_lcm_right r.period s.period) q (by omega)
  have hMb : r.evalNat (R + rem) ≤ M :=
    Finset.le_sup' (fun rem => r.evalNat (R + rem)) (Finset.mem_range.mpr hremlt)
  have hmsb : ms ≤ s.evalNat (R + rem) :=
    Finset.inf'_le (fun rem => s.evalNat (R + rem)) (Finset.mem_range.mpr hremlt)
  have hqδ : M - ms ≤ q • (cs - cr) := le_trans hQ (nsmul_le_nsmul_left (le_of_lt hδ) hqQ)
  have hkey : M + q • cr ≤ ms + q • cs := by
    have h2 : M - ms ≤ q • cs - q • cr := by rw [← smul_sub]; exact hqδ
    have h3 : M + q • cr ≤ q • cs + ms := sub_le_sub_iff.mp h2
    rwa [add_comm (q • cs) ms] at h3
  rw [hrn, hsn]
  calc r.evalNat (R + rem) + q • cr ≤ M + q • cr := add_le_add_left hMb _
    _ ≤ ms + q • cs := hkey
    _ ≤ s.evalNat (R + rem) + q • cs := add_le_add_left hmsb _

/-- The denoted sequence is unchanged on the stored transient/period prefix: `f(n) = vals[n]`. -/
theorem evalNat_of_lt [Add V] (r : UppSeq V) {n : ℕ} (hn : n < r.vals.length) :
    r.evalNat n = r.vals.get ⟨n, hn⟩ := by
  conv_lhs => rw [evalNat.eq_def]
  rw [dif_pos hn]

/-- **`evalNat` is monotone** (a UPP sequence is nondecreasing) from two *decidable* checks: the
stored prefix is nondecreasing (`hsorted`) and the wrap step `f(len-1) ≤ f(len)` holds (`hwrap`);
induction extends it past the prefix (each `+period` adds `incr`, cancelling). Discharges the
`Monotone` hypotheses of the general Lemma 4.4 for concrete sequences by `decide`. -/
theorem evalNat_monotone [AddCommMonoid V] [LinearOrder V] [IsOrderedAddMonoid V] (r : UppSeq V)
    (hsorted : ∀ i, i < r.vals.length - 1 → r.evalNat i ≤ r.evalNat (i + 1))
    (hwrap : r.evalNat (r.vals.length - 1) ≤ r.evalNat r.vals.length) :
    Monotone r.evalNat := by
  apply monotone_nat_of_le_succ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_trichotomy (n + 1) r.vals.length with hlt | heq | hgt
    · exact hsorted n (by omega)
    · rw [heq, show n = r.vals.length - 1 from by omega]; exact hwrap
    · have hnL : ¬ n < r.vals.length := by omega
      have hn1L : ¬ n + 1 < r.vals.length := by omega
      have hper := r.hperiod
      have hlenle := r.hlen
      have hen : r.evalNat n = r.evalNat (n - r.period) + r.incr := by
        conv_lhs => rw [evalNat.eq_def]
        rw [dif_neg hnL]
      have hen1 : r.evalNat (n + 1) = r.evalNat (n + 1 - r.period) + r.incr := by
        conv_lhs => rw [evalNat.eq_def]
        rw [dif_neg hn1L]
      rw [hen, hen1, show n + 1 - r.period = (n - r.period) + 1 from by omega]
      exact add_le_add_left (ih (n - r.period) (by omega)) r.incr

/-- Vertically shift a UPP sequence by a constant `b` (add `b` to every value); same period and
increment. -/
def addConst [Add V] (r : UppSeq V) (b : V) : UppSeq V where
  vals := r.vals.map (· + b)
  incr := r.incr
  period := r.period
  hperiod := r.hperiod
  hlen := by rw [List.length_map]; exact r.hlen

/-- `addConst` shifts the denoted sequence by `b`: `(r.addConst b)(n) = r(n) + b`. -/
theorem evalNat_addConst [AddCommMonoid V] (r : UppSeq V) (b : V) (n : ℕ) :
    (r.addConst b).evalNat n = r.evalNat n + b := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hL : n < r.vals.length
    · have hL' : n < (r.addConst b).vals.length := by simpa [addConst] using hL
      rw [evalNat_of_lt _ hL', evalNat_of_lt r hL]; simp [addConst]
    · have hge : ¬ n < (r.addConst b).vals.length := by simpa [addConst] using hL
      conv_lhs => rw [evalNat.eq_def]
      rw [dif_neg hge]
      show (r.addConst b).evalNat (n - r.period) + r.incr = _
      rw [ih (n - r.period) (by have := r.hperiod; have := r.hlen; omega)]
      conv_rhs => rw [evalNat.eq_def]
      rw [dif_neg hL]; abel

/-- **Offset crossover.** If `r` has strictly smaller asymptotic slope than `s`, then `r` is
eventually below `s` *by any margin* `b`: `r(n) + b ≤ s(n)` for large `n`. (Derived from
`evalNat_eventually_le` on `r.addConst b`, whose slope equals `r`'s.) -/
theorem evalNat_add_const_eventually_le [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]
    [Archimedean V] (r s : UppSeq V) (b : V)
    (hslope : (Nat.lcm r.period s.period / r.period) • r.incr
            < (Nat.lcm r.period s.period / s.period) • s.incr) :
    ∃ N, ∀ n, N ≤ n → r.evalNat n + b ≤ s.evalNat n := by
  obtain ⟨N, hN⟩ := (r.addConst b).evalNat_eventually_le s hslope
  exact ⟨N, fun n hn => by rw [← evalNat_addConst r b n]; exact hN n hn⟩

/-- **Crossover window reduction** — makes the crossover rank *computable*. If `N₀` is past the
periodic threshold (`max(rank_r, rank_s) ≤ N₀`) and the slower sequence satisfies `r ≤ s` on one full
period-window `[N₀, N₀+d)`, then `r ≤ s` for **all** `n ≥ N₀` — each `+d` step preserves it because
`cr ≤ cs`. The hypothesis `hwin` is a finite check (decidable for concrete sequences), so a valid
crossover rank can be found by search + `decide`, with no `Archimedean` argument. -/
theorem evalNat_le_of_window_le [AddCommMonoid V] [LinearOrder V] [IsOrderedAddMonoid V]
    (r s : UppSeq V) {N₀ : ℕ}
    (hR : max (r.vals.length - r.period) (s.vals.length - s.period) ≤ N₀)
    (hslope : (Nat.lcm r.period s.period / r.period) • r.incr
            ≤ (Nat.lcm r.period s.period / s.period) • s.incr)
    (hwin : ∀ rem, rem < Nat.lcm r.period s.period →
      r.evalNat (N₀ + rem) ≤ s.evalNat (N₀ + rem))
    (n : ℕ) (hn : N₀ ≤ n) : r.evalNat n ≤ s.evalNat n := by
  set d := Nat.lcm r.period s.period with hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (Nat.lcm_ne_zero r.hperiod.ne' s.hperiod.ne')
  set rem := (n - N₀) % d with hrem
  set q := (n - N₀) / d with hq
  have hremlt : rem < d := Nat.mod_lt _ hd0
  have hsplit : d * q + rem = n - N₀ := Nat.div_add_mod (n - N₀) d
  have hdecomp : n = (N₀ + rem) + q * d := by rw [mul_comm q d]; omega
  have hrn : r.evalNat n = r.evalNat (N₀ + rem) + q • ((d / r.period) • r.incr) := by
    rw [hdecomp]; exact r.evalNat_add_mul_of_dvd (hd ▸ Nat.dvd_lcm_left r.period s.period) q (by omega)
  have hsn : s.evalNat n = s.evalNat (N₀ + rem) + q • ((d / s.period) • s.incr) := by
    rw [hdecomp]; exact s.evalNat_add_mul_of_dvd (hd ▸ Nat.dvd_lcm_right r.period s.period) q (by omega)
  rw [hrn, hsn]
  exact add_le_add (hwin rem hremlt) (by gcongr)

/-- **Shifted window-descent** — the faithfulness core of the delay bound. If `r(t) ≤ s(t+d)` holds on
one full period-window `[N₀, N₀+L)` past the periodic threshold (`L = lcm`), it holds for *all* `t ≥
N₀`: the gap `r(t) − s(t+d)` is non-increasing per period when `slope_r ≤ slope_s`. So whether a shift
`d` makes `s(·+d)` dominate `r` — the predicate the delay bound searches — is decided by a finite
window. -/
theorem evalNat_le_shift_of_window [AddCommMonoid V] [LinearOrder V] [IsOrderedAddMonoid V]
    (r s : UppSeq V) (d : ℕ) {N₀ : ℕ}
    (hR : max (r.vals.length - r.period) (s.vals.length - s.period) ≤ N₀)
    (hslope : (Nat.lcm r.period s.period / r.period) • r.incr
            ≤ (Nat.lcm r.period s.period / s.period) • s.incr)
    (hwin : ∀ rem, rem < Nat.lcm r.period s.period →
      r.evalNat (N₀ + rem) ≤ s.evalNat (N₀ + rem + d))
    (n : ℕ) (hn : N₀ ≤ n) : r.evalNat n ≤ s.evalNat (n + d) := by
  set L := Nat.lcm r.period s.period with hL
  have hL0 : 0 < L := Nat.pos_of_ne_zero (Nat.lcm_ne_zero r.hperiod.ne' s.hperiod.ne')
  set rem := (n - N₀) % L with hrem
  set q := (n - N₀) / L with hq
  have hremlt : rem < L := Nat.mod_lt _ hL0
  have hsplit : L * q + rem = n - N₀ := Nat.div_add_mod (n - N₀) L
  have hdecomp : n = (N₀ + rem) + q * L := by rw [mul_comm q L]; omega
  have hrn : r.evalNat n = r.evalNat (N₀ + rem) + q • ((L / r.period) • r.incr) := by
    rw [hdecomp]; exact r.evalNat_add_mul_of_dvd (hL ▸ Nat.dvd_lcm_left r.period s.period) q (by omega)
  have hsn : s.evalNat (n + d) = s.evalNat (N₀ + rem + d) + q • ((L / s.period) • s.incr) := by
    rw [show n + d = (N₀ + rem + d) + q * L from by rw [mul_comm q L]; omega]
    exact s.evalNat_add_mul_of_dvd (hL ▸ Nat.dvd_lcm_right r.period s.period) q (by omega)
  rw [hrn, hsn]
  exact add_le_add (hwin rem hremlt) (by gcongr)

/-- **Lemma 4.3, minimum — general case** (the pointwise minimum of two UPP sequences is ultimately
pseudo-periodic). From some rank, `min(f,g)(n+d) = min(f,g)(n) + min(c_f', c_g')` with `d = lcm` and
`c_f' = (d/d_f)·c_f` (the per-`d` increments) — the increment is the smaller slope. Covers all three
slope cases: when one operand is strictly slower it *is* the min past the crossover
(`evalNat_eventually_le`); when balanced, both shift by the common increment. -/
theorem min_evalNat_add_lcm [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Archimedean V]
    (r s : UppSeq V) :
    ∃ N, ∀ n, N ≤ n →
      Min.min (r.evalNat (n + Nat.lcm r.period s.period))
              (s.evalNat (n + Nat.lcm r.period s.period))
        = Min.min (r.evalNat n) (s.evalNat n)
          + Min.min ((Nat.lcm r.period s.period / r.period) • r.incr)
                    ((Nat.lcm r.period s.period / s.period) • s.incr) := by
  set d := Nat.lcm r.period s.period with hd
  set cr := (d / r.period) • r.incr with hcr
  set cs := (d / s.period) • s.incr with hcs
  have hrstep : ∀ n, r.vals.length - r.period ≤ n → r.evalNat (n + d) = r.evalNat n + cr := by
    intro n hn; simpa using r.evalNat_add_mul_of_dvd (hd ▸ Nat.dvd_lcm_left r.period s.period) 1 hn
  have hsstep : ∀ n, s.vals.length - s.period ≤ n → s.evalNat (n + d) = s.evalNat n + cs := by
    intro n hn; simpa using s.evalNat_add_mul_of_dvd (hd ▸ Nat.dvd_lcm_right r.period s.period) 1 hn
  rcases lt_trichotomy cr cs with h | h | h
  · obtain ⟨N, hN⟩ := r.evalNat_eventually_le s h
    refine ⟨max N (max (r.vals.length - r.period) (s.vals.length - s.period)), fun n hn => ?_⟩
    rw [min_eq_left (hN n (by omega)), min_eq_left (hN (n + d) (by omega)),
      hrstep n (by omega), min_eq_left (le_of_lt h)]
  · refine ⟨max (r.vals.length - r.period) (s.vals.length - s.period), fun n hn => ?_⟩
    rw [hrstep n (by omega), hsstep n (by omega), h, min_self]
    rcases le_total (r.evalNat n) (s.evalNat n) with hle | hle
    · rw [min_eq_left hle, min_eq_left (add_le_add_left hle cs)]
    · rw [min_eq_right hle, min_eq_right (add_le_add_left hle cs)]
  · obtain ⟨N, hN⟩ := s.evalNat_eventually_le r (by rw [Nat.lcm_comm s.period r.period]; exact h)
    refine ⟨max N (max (r.vals.length - r.period) (s.vals.length - s.period)), fun n hn => ?_⟩
    rw [min_eq_right (hN n (by omega)), min_eq_right (hN (n + d) (by omega)),
      hsstep n (by omega), min_eq_right (le_of_lt h)]

/-- **Lemma 4.3, maximum — general case** (the pointwise maximum of two UPP sequences is ultimately
pseudo-periodic). Dual of `min_evalNat_add_lcm`: `max(f,g)(n+d) = max(f,g)(n) + max(c_f', c_g')` —
the increment is the *larger* slope; past the crossover (`evalNat_eventually_le`) the faster function
*is* the max. -/
theorem max_evalNat_add_lcm [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Archimedean V]
    (r s : UppSeq V) :
    ∃ N, ∀ n, N ≤ n →
      Max.max (r.evalNat (n + Nat.lcm r.period s.period))
              (s.evalNat (n + Nat.lcm r.period s.period))
        = Max.max (r.evalNat n) (s.evalNat n)
          + Max.max ((Nat.lcm r.period s.period / r.period) • r.incr)
                    ((Nat.lcm r.period s.period / s.period) • s.incr) := by
  set d := Nat.lcm r.period s.period with hd
  set cr := (d / r.period) • r.incr with hcr
  set cs := (d / s.period) • s.incr with hcs
  have hrstep : ∀ n, r.vals.length - r.period ≤ n → r.evalNat (n + d) = r.evalNat n + cr := by
    intro n hn; simpa using r.evalNat_add_mul_of_dvd (hd ▸ Nat.dvd_lcm_left r.period s.period) 1 hn
  have hsstep : ∀ n, s.vals.length - s.period ≤ n → s.evalNat (n + d) = s.evalNat n + cs := by
    intro n hn; simpa using s.evalNat_add_mul_of_dvd (hd ▸ Nat.dvd_lcm_right r.period s.period) 1 hn
  rcases lt_trichotomy cr cs with h | h | h
  · obtain ⟨N, hN⟩ := r.evalNat_eventually_le s h
    refine ⟨max N (max (r.vals.length - r.period) (s.vals.length - s.period)), fun n hn => ?_⟩
    rw [max_eq_right (hN n (by omega)), max_eq_right (hN (n + d) (by omega)),
      hsstep n (by omega), max_eq_right (le_of_lt h)]
  · refine ⟨max (r.vals.length - r.period) (s.vals.length - s.period), fun n hn => ?_⟩
    rw [hrstep n (by omega), hsstep n (by omega), h, max_self]
    rcases le_total (r.evalNat n) (s.evalNat n) with hle | hle
    · rw [max_eq_right hle, max_eq_right (add_le_add_left hle cs)]
    · rw [max_eq_left hle, max_eq_left (add_le_add_left hle cs)]
  · obtain ⟨N, hN⟩ := s.evalNat_eventually_le r (by rw [Nat.lcm_comm s.period r.period]; exact h)
    refine ⟨max N (max (r.vals.length - r.period) (s.vals.length - s.period)), fun n hn => ?_⟩
    rw [max_eq_left (hN n (by omega)), max_eq_left (hN (n + d) (by omega)),
      hrstep n (by omega), max_eq_left (le_of_lt h)]

/-- **Lemma 4.3 minimum — explicit-rank form.** Past a crossover `N₀` (where `r ≤ s` holds on a full
period-window `hwin`, hence everywhere by `evalNat_le_of_window_le`) the slower operand `r` *is* the
minimum, so `min(f,g)` steps by `min(cr,cs) = cr` per period. Computable rank for `minupp`. -/
theorem min_evalNat_add_lcm_window [AddCommMonoid V] [LinearOrder V] [IsOrderedAddMonoid V]
    (r s : UppSeq V) {N₀ : ℕ}
    (hR : max (r.vals.length - r.period) (s.vals.length - s.period) ≤ N₀)
    (hle : (Nat.lcm r.period s.period / r.period) • r.incr
         ≤ (Nat.lcm r.period s.period / s.period) • s.incr)
    (hwin : ∀ rem, rem < Nat.lcm r.period s.period →
      r.evalNat (N₀ + rem) ≤ s.evalNat (N₀ + rem))
    (n : ℕ) (hn : N₀ ≤ n) :
    Min.min (r.evalNat (n + Nat.lcm r.period s.period))
            (s.evalNat (n + Nat.lcm r.period s.period))
      = Min.min (r.evalNat n) (s.evalNat n)
        + Min.min ((Nat.lcm r.period s.period / r.period) • r.incr)
                  ((Nat.lcm r.period s.period / s.period) • s.incr) := by
  have hrs : ∀ m, N₀ ≤ m → r.evalNat m ≤ s.evalNat m :=
    fun m hm => evalNat_le_of_window_le r s hR hle hwin m hm
  rw [min_eq_left (hrs n hn),
    min_eq_left (hrs (n + Nat.lcm r.period s.period) (by omega)), min_eq_left hle]
  simpa using r.evalNat_add_mul_of_dvd (Nat.dvd_lcm_left r.period s.period) 1 (by omega)

/-- **Lemma 4.3 maximum — explicit-rank form.** Dual of `min_evalNat_add_lcm_window`: past the
crossover the faster operand `s` is the maximum, so `max(f,g)` steps by `max(cr,cs) = cs`. -/
theorem max_evalNat_add_lcm_window [AddCommMonoid V] [LinearOrder V] [IsOrderedAddMonoid V]
    (r s : UppSeq V) {N₀ : ℕ}
    (hR : max (r.vals.length - r.period) (s.vals.length - s.period) ≤ N₀)
    (hle : (Nat.lcm r.period s.period / r.period) • r.incr
         ≤ (Nat.lcm r.period s.period / s.period) • s.incr)
    (hwin : ∀ rem, rem < Nat.lcm r.period s.period →
      r.evalNat (N₀ + rem) ≤ s.evalNat (N₀ + rem))
    (n : ℕ) (hn : N₀ ≤ n) :
    Max.max (r.evalNat (n + Nat.lcm r.period s.period))
            (s.evalNat (n + Nat.lcm r.period s.period))
      = Max.max (r.evalNat n) (s.evalNat n)
        + Max.max ((Nat.lcm r.period s.period / r.period) • r.incr)
                  ((Nat.lcm r.period s.period / s.period) • s.incr) := by
  have hrs : ∀ m, N₀ ≤ m → r.evalNat m ≤ s.evalNat m :=
    fun m hm => evalNat_le_of_window_le r s hR hle hwin m hm
  rw [max_eq_right (hrs n hn),
    max_eq_right (hrs (n + Nat.lcm r.period s.period) (by omega)), max_eq_right hle]
  simpa using s.evalNat_add_mul_of_dvd (Nat.dvd_lcm_right r.period s.period) 1 (by omega)

/-- `⌊t + n⌋₊ = ⌊t⌋₊ + n` on `ℝ≥0` — proved directly (the ring lemma `Nat.floor_add_natCast` needs
a ring, which `ℝ≥0` is not). -/
private theorem nnFloor_add_nat (t : ℝ≥0) (m : ℕ) : ⌊t + (m : ℝ≥0)⌋₊ = ⌊t⌋₊ + m := by
  rw [Nat.floor_eq_iff zero_le]
  refine ⟨?_, ?_⟩
  · calc ((⌊t⌋₊ + m : ℕ) : ℝ≥0) = (⌊t⌋₊ : ℝ≥0) + m := by push_cast; ring
      _ ≤ t + m := by gcongr; exact Nat.floor_le zero_le
  · calc t + (m : ℝ≥0) < ((⌊t⌋₊ : ℝ≥0) + 1) + m := by gcongr; exact Nat.lt_floor_add_one t
      _ = ((⌊t⌋₊ + m : ℕ) : ℝ≥0) + 1 := by push_cast; ring

/-- The step-function reading `f : ℝ≥0 → V`, sampling the sequence at `⌊t⌋`. -/
noncomputable def toFun [Add V] (r : UppSeq V) : ℝ≥0 → V := fun t => r.evalNat ⌊t⌋₊

/-- **The finite representation is genuinely UPP.** Its step-function reading `toFun` is ultimately
pseudo-periodic (`IsUPPWith`) with rank `vals.length - period`, period `period` and increment
`incr` — tying the computable `UppSeq` to the semantic layer of the (min,plus) calculus. -/
theorem isUPPWith_toFun [AddMonoid V] (r : UppSeq V) :
    IsUPPWith r.toFun (↑(r.vals.length - r.period)) (↑r.period) r.incr := by
  refine ⟨by exact_mod_cast r.hperiod, fun t ht => ?_⟩
  show r.evalNat ⌊t + (↑r.period : ℝ≥0)⌋₊ = r.evalNat ⌊t⌋₊ + r.incr
  rw [nnFloor_add_nat]
  exact r.evalNat_add_period (Nat.le_floor ht)

/-! ## A worked example (sanity checks, gate-verified by `native_decide`) -/

/-- `f(0),f(1),f(2) = 0,1,2`, then period `2`, increment `3`: so `f(n+2) = f(n)+3` for `n ≥ 1`. -/
def demoSeq : UppSeq ℕ := ⟨[0, 1, 2], 3, 2, by decide, by decide⟩

/-- Purely-periodic rate sequence `f(n) = n` (no transient: `vals.length = period = 1`, increment `1`). -/
def rate1 : UppSeq ℕ := ⟨[0], 1, 1, by decide, by decide⟩

/-- Purely-periodic rate sequence `f(n) = 2n` (no transient: `vals.length = period = 1`, increment `2`). -/
def rate2 : UppSeq ℕ := ⟨[0], 2, 1, by decide, by decide⟩

example : demoSeq.evalNat 2 = 2 := by native_decide
example : demoSeq.evalNat 3 = 4 := by native_decide  -- f(1) + 3
example : demoSeq.evalNat 4 = 5 := by native_decide  -- f(2) + 3
example : demoSeq.evalNat 5 = 7 := by native_decide  -- f(3) + 3
example : demoSeq.evalNat 7 = 10 := by native_decide -- f(5) + 3

/-! ## Executable pointwise addition (Lemma 4.2) -/

/-- **Executable pointwise sum** (Lemma 4.2): common period `lcm(d_f, d_g)`, prefix recomputed via
`evalNat` over a long-enough range, increment `(D/d_f)·c_f + (D/d_g)·c_g`. Native-compilable; its
correctness `evalNat (add r s) = evalNat r + evalNat s` is the next step. -/
def add [AddMonoid V] (r s : UppSeq V) : UppSeq V where
  vals := (List.range (max r.vals.length s.vals.length + Nat.lcm r.period s.period)).map
    (fun n => r.evalNat n + s.evalNat n)
  incr := (Nat.lcm r.period s.period / r.period) • r.incr
        + (Nat.lcm r.period s.period / s.period) • s.incr
  period := Nat.lcm r.period s.period
  hperiod := Nat.pos_of_ne_zero (Nat.lcm_ne_zero r.hperiod.ne' s.hperiod.ne')
  hlen := by rw [List.length_map, List.length_range]; exact Nat.le_add_left _ _

/-- **Correctness of `add`** (Lemma 4.2): the executable sum denotes the pointwise sum,
`evalNat (add r s) n = evalNat r n + evalNat s n`, for every `n`. By strong induction: on the stored
prefix it reads the recomputed value; past it, the `lcm` recurrence matches `r`'s and `s`'s own
period-multiple steps (`evalNat_add_mul_period`). -/
theorem evalNat_add [AddCommMonoid V] (r s : UppSeq V) (n : ℕ) :
    (r.add s).evalNat n = r.evalNat n + s.evalNat n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hL : n < (r.add s).vals.length
    · rw [evalNat_of_lt _ hL]; simp [add]
    · rw [not_lt] at hL
      have hlen : (r.add s).vals.length
          = max r.vals.length s.vals.length + Nat.lcm r.period s.period := by simp [add]
      have hDpos : 0 < Nat.lcm r.period s.period :=
        Nat.pos_of_ne_zero (Nat.lcm_ne_zero r.hperiod.ne' s.hperiod.ne')
      have hDn : Nat.lcm r.period s.period ≤ n := by omega
      have hrec : (r.add s).evalNat n
          = (r.add s).evalNat (n - Nat.lcm r.period s.period) + (r.add s).incr := by
        conv_lhs => rw [evalNat.eq_def]
        rw [dif_neg (not_lt.mpr hL)]; rfl
      have hrn : r.evalNat n = r.evalNat (n - Nat.lcm r.period s.period)
          + (Nat.lcm r.period s.period / r.period) • r.incr := by
        have key := r.evalNat_add_mul_period (Nat.lcm r.period s.period / r.period)
          (n := n - Nat.lcm r.period s.period) (by omega)
        rwa [Nat.div_mul_cancel (Nat.dvd_lcm_left _ _), Nat.sub_add_cancel hDn] at key
      have hsn : s.evalNat n = s.evalNat (n - Nat.lcm r.period s.period)
          + (Nat.lcm r.period s.period / s.period) • s.incr := by
        have key := s.evalNat_add_mul_period (Nat.lcm r.period s.period / s.period)
          (n := n - Nat.lcm r.period s.period) (by omega)
        rwa [Nat.div_mul_cancel (Nat.dvd_lcm_right _ _), Nat.sub_add_cancel hDn] at key
      have hincr : (r.add s).incr = (Nat.lcm r.period s.period / r.period) • r.incr
          + (Nat.lcm r.period s.period / s.period) • s.incr := rfl
      rw [hrec, ih (n - Nat.lcm r.period s.period) (by omega), hincr, hrn, hsn]
      abel

/-- Sanity check (gate-verified): `add` computes the pointwise sum across the period boundary. -/
example : ∀ n ∈ Finset.range 12,
    (demoSeq.add demoSeq).evalNat n = demoSeq.evalNat n + demoSeq.evalNat n := by native_decide

/-! ## Executable pointwise minimum (Lemma 4.3, balanced case) -/

/-- **Executable pointwise minimum** (Lemma 4.3): common period `lcm`, prefix the pointwise min
recomputed via `evalNat`, increment `(D/d_f)·c_f`. Correct in the **balanced** case where the scaled
increments agree (the book's `d_g c_f = d_f c_g`); native-compilable. (The dominant-slope cases —
where the slower function eventually wins — need an Archimedean crossover bound, not yet formalized.) -/
def min [AddMonoid V] [LinearOrder V] (r s : UppSeq V) : UppSeq V where
  vals := (List.range (max r.vals.length s.vals.length + Nat.lcm r.period s.period)).map
    (fun n => Min.min (r.evalNat n) (s.evalNat n))
  incr := (Nat.lcm r.period s.period / r.period) • r.incr
  period := Nat.lcm r.period s.period
  hperiod := Nat.pos_of_ne_zero (Nat.lcm_ne_zero r.hperiod.ne' s.hperiod.ne')
  hlen := by rw [List.length_map, List.length_range]; exact Nat.le_add_left _ _

/-- **Correctness of `min`** in the balanced case: when the scaled increments agree, the executable
minimum denotes the pointwise minimum, `evalNat (min r s) n = Min.min (evalNat r n) (evalNat s n)`. -/
theorem evalNat_min [AddCommMonoid V] [LinearOrder V] [IsOrderedAddMonoid V] (r s : UppSeq V)
    (hbal : (Nat.lcm r.period s.period / r.period) • r.incr
          = (Nat.lcm r.period s.period / s.period) • s.incr) (n : ℕ) :
    (r.min s).evalNat n = Min.min (r.evalNat n) (s.evalNat n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hL : n < (r.min s).vals.length
    · rw [evalNat_of_lt _ hL]; simp [min]
    · rw [not_lt] at hL
      have hlen : (r.min s).vals.length
          = max r.vals.length s.vals.length + Nat.lcm r.period s.period := by simp [min]
      have hDpos : 0 < Nat.lcm r.period s.period :=
        Nat.pos_of_ne_zero (Nat.lcm_ne_zero r.hperiod.ne' s.hperiod.ne')
      have hDn : Nat.lcm r.period s.period ≤ n := by omega
      have hrec : (r.min s).evalNat n
          = (r.min s).evalNat (n - Nat.lcm r.period s.period) + (r.min s).incr := by
        conv_lhs => rw [evalNat.eq_def]
        rw [dif_neg (not_lt.mpr hL)]; rfl
      have hrn : r.evalNat n = r.evalNat (n - Nat.lcm r.period s.period)
          + (Nat.lcm r.period s.period / r.period) • r.incr := by
        have key := r.evalNat_add_mul_period (Nat.lcm r.period s.period / r.period)
          (n := n - Nat.lcm r.period s.period) (by omega)
        rwa [Nat.div_mul_cancel (Nat.dvd_lcm_left _ _), Nat.sub_add_cancel hDn] at key
      have hsn : s.evalNat n = s.evalNat (n - Nat.lcm r.period s.period)
          + (Nat.lcm r.period s.period / s.period) • s.incr := by
        have key := s.evalNat_add_mul_period (Nat.lcm r.period s.period / s.period)
          (n := n - Nat.lcm r.period s.period) (by omega)
        rwa [Nat.div_mul_cancel (Nat.dvd_lcm_right _ _), Nat.sub_add_cancel hDn] at key
      have hincr : (r.min s).incr = (Nat.lcm r.period s.period / r.period) • r.incr := rfl
      rw [hrec, ih (n - Nat.lcm r.period s.period) (by omega), hincr, hrn, hsn, hbal]
      rcases le_total (r.evalNat (n - Nat.lcm r.period s.period))
        (s.evalNat (n - Nat.lcm r.period s.period)) with h | h
      · rw [min_eq_left h, min_eq_left (add_le_add_left h _)]
      · rw [min_eq_right h, min_eq_right (add_le_add_left h _)]

/-- Sanity check (gate-verified): `min` of a sequence with itself is itself (balanced). -/
example : ∀ n ∈ Finset.range 12,
    (demoSeq.min demoSeq).evalNat n = demoSeq.evalNat n := by native_decide

/-! ## Pointwise (min,plus) convolution -/

/-- The discrete **(min,plus) convolution** at `n`: `(f ⊗ g)(n) = ⨅_{k ≤ n} f(k) + g(n-k)`, the
`Finset.inf'` over `k ∈ {0,…,n}`. Native-compilable; this is the convolution *by definition*
(`convNat_le` + `convNat_eq` certify it is exactly the minimum). The UPP closed form — that the
result is again a `UppSeq`, Lemma 4.4 — is future work. -/
def convNat [Add V] [LinearOrder V] (r s : UppSeq V) (n : ℕ) : V :=
  (Finset.range (n + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
    (fun k => r.evalNat k + s.evalNat (n - k))

/-- `convNat` lower-bounds every convolution term `f(k) + g(n-k)` (`k ≤ n`). -/
theorem convNat_le [Add V] [LinearOrder V] (r s : UppSeq V) {n k : ℕ} (hk : k ≤ n) :
    r.convNat s n ≤ r.evalNat k + s.evalNat (n - k) :=
  Finset.inf'_le _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

/-- `convNat` is attained at some `k ≤ n` — so it is exactly the minimum, the (min,plus)
convolution value `⨅_{k ≤ n} f(k) + g(n-k)`. -/
theorem convNat_eq [Add V] [LinearOrder V] (r s : UppSeq V) (n : ℕ) :
    ∃ k ≤ n, r.convNat s n = r.evalNat k + s.evalNat (n - k) := by
  obtain ⟨k, hk, heq⟩ := Finset.exists_mem_eq_inf' (s := Finset.range (n + 1))
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩ (fun k => r.evalNat k + s.evalNat (n - k))
  exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), heq⟩

/-- **(min,plus) convolution is commutative**: `(f ⊗ g)(n) = (g ⊗ f)(n)`. -/
theorem convNat_comm [AddCommMonoid V] [LinearOrder V] (r s : UppSeq V) (n : ℕ) :
    r.convNat s n = s.convNat r n := by
  refine le_antisymm ?_ ?_
  · obtain ⟨k, hk, hke⟩ := s.convNat_eq r n
    rw [hke]
    calc r.convNat s n ≤ r.evalNat (n - k) + s.evalNat (n - (n - k)) := r.convNat_le s (by omega)
      _ = r.evalNat (n - k) + s.evalNat k := by rw [show n - (n - k) = k from by omega]
      _ = s.evalNat k + r.evalNat (n - k) := by rw [add_comm]
  · obtain ⟨k, hk, hke⟩ := r.convNat_eq s n
    rw [hke]
    calc s.convNat r n ≤ s.evalNat (n - k) + r.evalNat (n - (n - k)) := s.convNat_le r (by omega)
      _ = s.evalNat (n - k) + r.evalNat k := by rw [show n - (n - k) = k from by omega]
      _ = r.evalNat k + s.evalNat (n - k) := by rw [add_comm]

/-- Search bound for `deconvNat`: past `max(rank_r,rank_s) + d` the deconvolution terms
`f(n+k) - g(k)` are non-increasing per period (when `slope_f ≤ slope_g`), so the supremum over all
`k ≥ 0` is attained within `[0, deconvBound)`. -/
def deconvBound (r s : UppSeq V) : ℕ :=
  max (r.vals.length - r.period) (s.vals.length - s.period) + Nat.lcm r.period s.period

/-- `deconvBound` is positive (it is `≥ lcm ≥ 1`), so the search window is nonempty. -/
theorem deconvBound_pos (r s : UppSeq V) : 0 < deconvBound r s := by
  have := Nat.pos_of_ne_zero (Nat.lcm_ne_zero r.hperiod.ne' s.hperiod.ne')
  unfold deconvBound; omega

/-- The discrete **(min,plus) deconvolution** at `n`: `(f ⊘ g)(n) = ⨆_{k≥0} f(n+k) - g(k)`, computed
as the `Finset.sup'` over the finite window `[0, deconvBound)`. When `slope_f ≤ slope_g` (the
deconvolution is then finite) this window captures the true supremum — the terms peak, then decrease
per period; `slope_f > slope_g` gives `+∞`, not represented here. -/
def deconvNat [Add V] [Sub V] [LinearOrder V] (r s : UppSeq V) (n : ℕ) : V :=
  (Finset.range (deconvBound r s)).sup' ⟨0, Finset.mem_range.mpr (deconvBound_pos r s)⟩
    (fun k => r.evalNat (n + k) - s.evalNat k)

/-- `deconvNat` upper-bounds every in-window deconvolution term `f(n+k) - g(k)` (`k < deconvBound`). -/
theorem le_deconvNat [Add V] [Sub V] [LinearOrder V] (r s : UppSeq V) {n k : ℕ}
    (hk : k < deconvBound r s) : r.evalNat (n + k) - s.evalNat k ≤ r.deconvNat s n :=
  Finset.le_sup' (fun k => r.evalNat (n + k) - s.evalNat k) (Finset.mem_range.mpr hk)

/-- `deconvNat` is attained at some `k < deconvBound` — it is exactly the maximum over the window. -/
theorem deconvNat_eq [Add V] [Sub V] [LinearOrder V] (r s : UppSeq V) (n : ℕ) :
    ∃ k < deconvBound r s, r.deconvNat s n = r.evalNat (n + k) - s.evalNat k := by
  obtain ⟨k, hk, heq⟩ := Finset.exists_mem_eq_sup' (s := Finset.range (deconvBound r s))
    ⟨0, Finset.mem_range.mpr (deconvBound_pos r s)⟩ (fun k => r.evalNat (n + k) - s.evalNat k)
  exact ⟨k, Finset.mem_range.mp hk, heq⟩

/-- Sanity (gate-verified): `(rate1 ⊘ rate2)(n) = n` — deconvolving `n` by `2n` (slower by faster,
finite) recovers `n` (`⨆_k (n+k) - 2k` is maximal at `k=0`). -/
example : ∀ n ∈ Finset.range 5, rate1.deconvNat rate2 n = n := by native_decide

/-- **Deconvolution faithfulness.** When `slope_f ≤ slope_g` (`cr' ≤ cs'`, so the deconvolution is
finite), the finite-window `deconvNat` upper-bounds the deconvolution term at *every* `k ≥ 0`, not
just `k < deconvBound`: past the window the terms are non-increasing per period
(`term(k) = term(k-d) + (cr'-cs') ≤ term(k-d)`), so any `k` descends into the window. Together with
`deconvNat_eq` this gives `deconvNat r s n = ⨆_{k≥0} f(n+k) - g(k)` — the genuine deconvolution. -/
theorem deconvNat_ge [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] (r s : UppSeq V)
    (hle : (Nat.lcm r.period s.period / r.period) • r.incr
         ≤ (Nat.lcm r.period s.period / s.period) • s.incr) (n k : ℕ) :
    r.evalNat (n + k) - s.evalNat k ≤ r.deconvNat s n := by
  have hd0 : 0 < Nat.lcm r.period s.period :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero r.hperiod.ne' s.hperiod.ne')
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < deconvBound r s
    · exact le_deconvNat r s hk
    · simp only [deconvBound, not_lt] at hk
      have hr : r.evalNat (n + k) = r.evalNat (n + (k - Nat.lcm r.period s.period))
          + (Nat.lcm r.period s.period / r.period) • r.incr := by
        rw [show n + k = (n + (k - Nat.lcm r.period s.period)) + Nat.lcm r.period s.period from by omega]
        simpa using r.evalNat_add_mul_of_dvd (Nat.dvd_lcm_left r.period s.period) 1 (by omega)
      have hs : s.evalNat k = s.evalNat (k - Nat.lcm r.period s.period)
          + (Nat.lcm r.period s.period / s.period) • s.incr := by
        rw [show k = (k - Nat.lcm r.period s.period) + Nat.lcm r.period s.period from by omega]
        simpa using s.evalNat_add_mul_of_dvd (Nat.dvd_lcm_right r.period s.period) 1 (by omega)
      have hc : (Nat.lcm r.period s.period / r.period) • r.incr
              - (Nat.lcm r.period s.period / s.period) • s.incr ≤ 0 := sub_nonpos.mpr hle
      calc r.evalNat (n + k) - s.evalNat k
          = (r.evalNat (n + (k - Nat.lcm r.period s.period))
              - s.evalNat (k - Nat.lcm r.period s.period))
            + ((Nat.lcm r.period s.period / r.period) • r.incr
               - (Nat.lcm r.period s.period / s.period) • s.incr) := by rw [hr, hs]; abel
        _ ≤ (r.evalNat (n + (k - Nat.lcm r.period s.period))
              - s.evalNat (k - Nat.lcm r.period s.period)) + 0 := by gcongr
        _ = r.evalNat (n + (k - Nat.lcm r.period s.period))
              - s.evalNat (k - Nat.lcm r.period s.period) := add_zero _
        _ ≤ r.deconvNat s n := ih (k - Nat.lcm r.period s.period) (by omega)

/-- **`deconvNat` is the genuine (min,plus) deconvolution** (when `slope_f ≤ slope_g`): it is the
*greatest* of all deconvolution terms `f(n+k) - g(k)` over `k ≥ 0` — i.e. `⨆_{k≥0} f(n+k) - g(k)`.
Combines `deconvNat_eq` (attained in the window) with `deconvNat_ge` (bounds every `k`). -/
theorem deconvNat_isGreatest [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] (r s : UppSeq V)
    (hle : (Nat.lcm r.period s.period / r.period) • r.incr
         ≤ (Nat.lcm r.period s.period / s.period) • s.incr) (n : ℕ) :
    IsGreatest (Set.range (fun k => r.evalNat (n + k) - s.evalNat k)) (r.deconvNat s n) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨k, _, heq⟩ := deconvNat_eq r s n
    exact ⟨k, heq.symm⟩
  · rintro _ ⟨k, rfl⟩
    exact deconvNat_ge r s hle n k

/-- **Deconvolution is ultimately pseudo-periodic** (Lemma 4.5): for `n ≥ rank_f` (and
`slope_f ≤ slope_g`), `(f⊘g)(n + d_f) = (f⊘g)(n) + c_f` — shifting `n` by `f`'s period `d_f` shifts
every term `f(n+k) - g(k)` by `c_f` (since `n+k ≥ rank_f` for all `k`), so the whole supremum shifts
by `c_f`. The deconvolution thus has `f`'s period `d_f` and increment `c_f`. -/
theorem deconvNat_add_period [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] (r s : UppSeq V)
    (hle : (Nat.lcm r.period s.period / r.period) • r.incr
         ≤ (Nat.lcm r.period s.period / s.period) • s.incr)
    {n : ℕ} (hn : r.vals.length - r.period ≤ n) :
    r.deconvNat s (n + r.period) = r.deconvNat s n + r.incr := by
  have hper : ∀ k, r.evalNat (n + r.period + k) = r.evalNat (n + k) + r.incr := by
    intro k
    rw [show n + r.period + k = (n + k) + r.period from by omega]
    exact r.evalNat_add_period (by omega)
  refine le_antisymm ?_ ?_
  · obtain ⟨k, _, heq⟩ := deconvNat_eq r s (n + r.period)
    rw [heq, hper k]
    calc r.evalNat (n + k) + r.incr - s.evalNat k
        = (r.evalNat (n + k) - s.evalNat k) + r.incr := by abel
      _ ≤ r.deconvNat s n + r.incr := by gcongr; exact deconvNat_ge r s hle n k
  · obtain ⟨k, _, heq⟩ := deconvNat_eq r s n
    rw [heq]
    calc r.evalNat (n + k) - s.evalNat k + r.incr
        = r.evalNat (n + r.period + k) - s.evalNat k := by rw [hper k]; abel
      _ ≤ r.deconvNat s (n + r.period) := deconvNat_ge r s hle (n + r.period) k

/-- **Lemma 4.4, balanced case** — the convolution is ultimately pseudo-periodic. When the two
operands have equal asymptotic slope (`(d/d_f)·c_f = (d/d_g)·c_g = c`, the book's balanced case),
their (min,plus) convolution satisfies the pseudo-period step `(f⊗g)(n+d) = (f⊗g)(n) + c` with
`d = lcm(d_f,d_g)` from the rank `T = T_f + T_g + d` onward — the book's rank and increment. (The
non-balanced case needs the dominant-slope crossover / general min-of-UPP, deferred.)

Proof: both bounds via the minimizer (`convNat_eq`) — push the `+d` time-shift into whichever
operand's *periodic* part is reachable (`evalNat_add_mul_period`); since `n ≥ T_f + T_g`, at least one
side is always in its periodic régime, and balancedness makes both shifts equal `c`. -/
theorem convNat_add_lcm_of_balanced [AddCommMonoid V] [LinearOrder V] [IsOrderedAddMonoid V]
    (r s : UppSeq V)
    (hbal : (Nat.lcm r.period s.period / r.period) • r.incr
          = (Nat.lcm r.period s.period / s.period) • s.incr)
    {n : ℕ} (hn : (r.vals.length - r.period) + (s.vals.length - s.period)
      + Nat.lcm r.period s.period ≤ n) :
    r.convNat s (n + Nat.lcm r.period s.period)
      = r.convNat s n + (Nat.lcm r.period s.period / r.period) • r.incr := by
  set d := Nat.lcm r.period s.period with hd
  set c := (d / r.period) • r.incr with hc
  have hrshift : ∀ m, r.vals.length - r.period ≤ m → r.evalNat (m + d) = r.evalNat m + c := by
    intro m hm
    have h := r.evalNat_add_mul_period (d / r.period) (n := m) hm
    rwa [Nat.div_mul_cancel (hd ▸ Nat.dvd_lcm_left r.period s.period)] at h
  have hsshift : ∀ m, s.vals.length - s.period ≤ m → s.evalNat (m + d) = s.evalNat m + c := by
    intro m hm
    have h := s.evalNat_add_mul_period (d / s.period) (n := m) hm
    rw [Nat.div_mul_cancel (hd ▸ Nat.dvd_lcm_right r.period s.period)] at h
    rw [h, hbal]
  refine le_antisymm ?_ ?_
  · obtain ⟨j, hj, hje⟩ := r.convNat_eq s n
    by_cases hjf : r.vals.length - r.period ≤ j
    · calc r.convNat s (n + d)
          ≤ r.evalNat (j + d) + s.evalNat (n + d - (j + d)) := r.convNat_le s (by omega)
        _ = r.evalNat (j + d) + s.evalNat (n - j) := by rw [show n + d - (j + d) = n - j from by omega]
        _ = r.evalNat j + c + s.evalNat (n - j) := by rw [hrshift j hjf]
        _ = r.convNat s n + c := by rw [hje]; abel
    · calc r.convNat s (n + d)
          ≤ r.evalNat j + s.evalNat (n + d - j) := r.convNat_le s (by omega)
        _ = r.evalNat j + s.evalNat (n - j + d) := by rw [show n + d - j = n - j + d from by omega]
        _ = r.evalNat j + (s.evalNat (n - j) + c) := by rw [hsshift (n - j) (by omega)]
        _ = r.convNat s n + c := by rw [hje]; abel
  · obtain ⟨k, hk, hke⟩ := r.convNat_eq s (n + d)
    by_cases hkf : r.vals.length - r.period + d ≤ k
    · have hconv : r.convNat s n ≤ r.evalNat (k - d) + s.evalNat (n - (k - d)) :=
        r.convNat_le s (by omega)
      have e1 : r.evalNat (k - d) + c = r.evalNat k := by
        rw [← hrshift (k - d) (by omega), show k - d + d = k from by omega]
      calc r.convNat s n + c
          ≤ (r.evalNat (k - d) + s.evalNat (n - (k - d))) + c := add_le_add_left hconv _
        _ = (r.evalNat (k - d) + c) + s.evalNat (n - (k - d)) := by abel
        _ = r.evalNat k + s.evalNat (n + d - k) := by rw [e1, show n - (k - d) = n + d - k from by omega]
        _ = r.convNat s (n + d) := hke.symm
    · have hconv : r.convNat s n ≤ r.evalNat k + s.evalNat (n - k) := r.convNat_le s (by omega)
      calc r.convNat s n + c
          ≤ (r.evalNat k + s.evalNat (n - k)) + c := add_le_add_left hconv _
        _ = r.evalNat k + (s.evalNat (n - k) + c) := by abel
        _ = r.evalNat k + s.evalNat (n + d - k) := by
            rw [← hsshift (n - k) (by omega), show n - k + d = n + d - k from by omega]
        _ = r.convNat s (n + d) := hke.symm

/-- **Lemma 4.4, lower bound** (general — all slope cases, no Archimedean needed). The convolution
grows at least by the smaller per-`d` slope: `(f⊗g)(n) + min(c_f', c_g') ≤ (f⊗g)(n+d)` from rank
`T_f + T_g + d`. (The matching upper bound — full Lemma 4.4 — needs the dominant-slope minimizer to
stay in the periodic region, the remaining open step.) Proof: the minimizer `k` of `(f⊗g)(n+d)` lands
either deep enough to shift `+d` out of `f` (giving `+c_f'`) or far enough that the `g`-argument is
periodic (giving `+c_g'`); `min` is below both. -/
theorem convNat_add_lcm_ge [AddCommMonoid V] [LinearOrder V] [IsOrderedAddMonoid V] (r s : UppSeq V)
    {n : ℕ} (hn : (r.vals.length - r.period) + (s.vals.length - s.period)
      + Nat.lcm r.period s.period ≤ n) :
    r.convNat s n + Min.min ((Nat.lcm r.period s.period / r.period) • r.incr)
        ((Nat.lcm r.period s.period / s.period) • s.incr)
      ≤ r.convNat s (n + Nat.lcm r.period s.period) := by
  set d := Nat.lcm r.period s.period with hd
  set cr := (d / r.period) • r.incr with hcr
  set cs := (d / s.period) • s.incr with hcs
  have hrstep : ∀ m, r.vals.length - r.period ≤ m → r.evalNat (m + d) = r.evalNat m + cr := by
    intro m hm; simpa using r.evalNat_add_mul_of_dvd (hd ▸ Nat.dvd_lcm_left r.period s.period) 1 hm
  have hsstep : ∀ m, s.vals.length - s.period ≤ m → s.evalNat (m + d) = s.evalNat m + cs := by
    intro m hm; simpa using s.evalNat_add_mul_of_dvd (hd ▸ Nat.dvd_lcm_right r.period s.period) 1 hm
  obtain ⟨k, hk, hke⟩ := r.convNat_eq s (n + d)
  by_cases hkf : r.vals.length - r.period + d ≤ k
  · have hconv : r.convNat s n ≤ r.evalNat (k - d) + s.evalNat (n - (k - d)) := r.convNat_le s (by omega)
    have e1 : r.evalNat (k - d) + cr = r.evalNat k := by
      rw [← hrstep (k - d) (by omega), show k - d + d = k from by omega]
    have hbound : r.convNat s n + cr ≤ r.convNat s (n + d) := by
      rw [hke]
      calc r.convNat s n + cr ≤ (r.evalNat (k - d) + s.evalNat (n - (k - d))) + cr :=
            add_le_add_left hconv _
        _ = (r.evalNat (k - d) + cr) + s.evalNat (n - (k - d)) := by abel
        _ = r.evalNat k + s.evalNat (n + d - k) := by rw [e1, show n - (k - d) = n + d - k from by omega]
    exact le_trans (add_le_add_right (min_le_left cr cs) _) hbound
  · have hconv : r.convNat s n ≤ r.evalNat k + s.evalNat (n - k) := r.convNat_le s (by omega)
    have hbound : r.convNat s n + cs ≤ r.convNat s (n + d) := by
      rw [hke]
      calc r.convNat s n + cs ≤ (r.evalNat k + s.evalNat (n - k)) + cs := add_le_add_left hconv _
        _ = r.evalNat k + (s.evalNat (n - k) + cs) := by abel
        _ = r.evalNat k + s.evalNat (n + d - k) := by
            rw [← hsstep (n - k) (by omega), show n - k + d = n + d - k from by omega]
    exact le_trans (add_le_add_right (min_le_right cr cs) _) hbound

/-- **Lemma 4.4, `≤` direction — no-transient slower operand.** When the smaller-increment operand
`r` (`cr ≤ cs`) has no transient (`r.vals.length ≤ r.period`, so `r` is pseudo-periodic from index
`0`), the convolution grows by at most `min(cr,cs) = cr` per common period: `(f⊗g)(n+d) ≤ (f⊗g)(n) +
cr`. The minimizer of `(f⊗g)(n)` lies in `r`'s periodic région automatically (rank `= 0`), so the
`+d` time-shift pushes straight into `r` — no dominant-slope crossover needed. (The general `≤`,
where the minimizer can sit in `r`'s transient, is the deferred hard case.) -/
theorem convNat_add_lcm_le_of_noTransient [AddCommMonoid V] [LinearOrder V] [IsOrderedAddMonoid V]
    (r s : UppSeq V) (hrf : r.vals.length ≤ r.period)
    (hslope : (Nat.lcm r.period s.period / r.period) • r.incr
            ≤ (Nat.lcm r.period s.period / s.period) • s.incr) (n : ℕ) :
    r.convNat s (n + Nat.lcm r.period s.period)
      ≤ r.convNat s n + Min.min ((Nat.lcm r.period s.period / r.period) • r.incr)
          ((Nat.lcm r.period s.period / s.period) • s.incr) := by
  set d := Nat.lcm r.period s.period with hd
  set cr := (d / r.period) • r.incr with hcr
  have hrstep : ∀ m, r.evalNat (m + d) = r.evalNat m + cr := fun m => by
    simpa using r.evalNat_add_mul_of_dvd (hd ▸ Nat.dvd_lcm_left r.period s.period) 1 (by omega)
  obtain ⟨k, hk, hke⟩ := r.convNat_eq s n
  rw [min_eq_left hslope]
  calc r.convNat s (n + d)
      ≤ r.evalNat (k + d) + s.evalNat ((n + d) - (k + d)) := r.convNat_le s (by omega)
    _ = r.evalNat (k + d) + s.evalNat (n - k) := by rw [show (n + d) - (k + d) = n - k from by omega]
    _ = (r.evalNat k + cr) + s.evalNat (n - k) := by rw [hrstep k]
    _ = (r.evalNat k + s.evalNat (n - k)) + cr := by abel
    _ = r.convNat s n + cr := by rw [hke]

/-- **Lemma 4.4 (`=`) — no-transient slower operand.** Combining the general `≥`
(`convNat_add_lcm_ge`) with the no-transient `≤`: when the smaller-increment operand `r` (`cr ≤ cs`)
has no transient, the convolution is exactly pseudo-periodic past rank `T_s + d`, with the book's
increment `min(cr,cs)`: `(f⊗g)(n+d) = (f⊗g)(n) + min(cr,cs)`. -/
theorem convNat_add_lcm_of_noTransient [AddCommMonoid V] [LinearOrder V] [IsOrderedAddMonoid V]
    (r s : UppSeq V) (hrf : r.vals.length ≤ r.period)
    (hslope : (Nat.lcm r.period s.period / r.period) • r.incr
            ≤ (Nat.lcm r.period s.period / s.period) • s.incr)
    {n : ℕ} (hn : (s.vals.length - s.period) + Nat.lcm r.period s.period ≤ n) :
    r.convNat s (n + Nat.lcm r.period s.period)
      = r.convNat s n + Min.min ((Nat.lcm r.period s.period / r.period) • r.incr)
          ((Nat.lcm r.period s.period / s.period) • s.incr) :=
  le_antisymm (convNat_add_lcm_le_of_noTransient r s hrf hslope n)
    (convNat_add_lcm_ge r s (by omega))

/-- **Lemma 4.4 (`=`) — no-transient slower operand on the right.** Symmetric to
`convNat_add_lcm_of_noTransient` via commutativity (`convNat_comm`): when the smaller-increment
operand is `s` (the second, `cs ≤ cr`) and `s` has no transient, the convolution is exactly
pseudo-periodic past rank `T_r + d`, with increment `min(cr,cs)`. -/
theorem convNat_add_lcm_of_noTransient_right [AddCommMonoid V] [LinearOrder V] [IsOrderedAddMonoid V]
    (r s : UppSeq V) (hsf : s.vals.length ≤ s.period)
    (hslope : (Nat.lcm r.period s.period / s.period) • s.incr
            ≤ (Nat.lcm r.period s.period / r.period) • r.incr)
    {n : ℕ} (hn : (r.vals.length - r.period) + Nat.lcm r.period s.period ≤ n) :
    r.convNat s (n + Nat.lcm r.period s.period)
      = r.convNat s n + Min.min ((Nat.lcm r.period s.period / r.period) • r.incr)
          ((Nat.lcm r.period s.period / s.period) • s.incr) := by
  have hlcm : Nat.lcm s.period r.period = Nat.lcm r.period s.period := Nat.lcm_comm s.period r.period
  have key := convNat_add_lcm_of_noTransient s r hsf (by rw [hlcm]; exact hslope)
    (n := n) (by rw [hlcm]; exact hn)
  rw [hlcm] at key
  rw [convNat_comm r s (n + Nat.lcm r.period s.period), convNat_comm r s n, min_comm]
  exact key

/-- **Minimizer-region lemma** — the crux of the general non-balanced Lemma 4.4. When `r` has
strictly smaller asymptotic slope than `s` (`cr < cs`) and both are nondecreasing, the convolution
`(r⊗s)(n)` is, for large `n`, attained at some `k` in `r`'s *periodic* région (`rank_r ≤ k`): a
transient index `k₀ < rank_r` forces `s(n-k₀) ~ slope_s·n`, which the periodic-region competitor
`k = n - rank_r` (giving `r(n-rank_r)+s(rank_r) ~ slope_r·n`) eventually beats. Both sides of that
comparison land at the *same* index `n - rank_r`, so the offset crossover
(`evalNat_add_const_eventually_le`) closes it directly. -/
theorem convNat_minimizer_periodic [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]
    [Archimedean V] (r s : UppSeq V) (hrmono : Monotone r.evalNat) (hsmono : Monotone s.evalNat)
    (hslope : (Nat.lcm r.period s.period / r.period) • r.incr
            < (Nat.lcm r.period s.period / s.period) • s.incr) :
    ∃ N, ∀ n, N ≤ n → ∃ k, r.vals.length - r.period ≤ k ∧ k ≤ n ∧
      r.convNat s n = r.evalNat k + s.evalNat (n - k) := by
  set Tr := r.vals.length - r.period with hTr
  obtain ⟨N0, hN0⟩ := evalNat_add_const_eventually_le r s (s.evalNat Tr - r.evalNat 0) hslope
  refine ⟨max N0 Tr + Tr, fun n hn => ?_⟩
  have hnTr : Tr ≤ n := by omega
  have hn2 : Tr ≤ n - Tr := by omega
  have hm0 : N0 ≤ n - Tr := by omega
  have hIcc : (Finset.Icc Tr n).Nonempty := ⟨Tr, Finset.mem_Icc.mpr ⟨le_rfl, hnTr⟩⟩
  obtain ⟨k, hkmem, hkeq⟩ := Finset.exists_mem_eq_inf' hIcc (fun k => r.evalNat k + s.evalNat (n - k))
  rw [Finset.mem_Icc] at hkmem
  refine ⟨k, hkmem.1, hkmem.2, le_antisymm (r.convNat_le s hkmem.2) ?_⟩
  obtain ⟨j, hj, hje⟩ := r.convNat_eq s n
  rw [hje]
  by_cases hjT : Tr ≤ j
  · rw [← hkeq]; exact Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨hjT, hj⟩)
  · rw [not_le] at hjT
    have hcomp : r.evalNat k + s.evalNat (n - k) ≤ r.evalNat (n - Tr) + s.evalNat Tr := by
      rw [← hkeq]
      have h2 := Finset.inf'_le (fun k => r.evalNat k + s.evalNat (n - k))
        (show n - Tr ∈ Finset.Icc Tr n from Finset.mem_Icc.mpr ⟨hn2, by omega⟩)
      simpa [show n - (n - Tr) = Tr from by omega] using h2
    have hcross : r.evalNat (n - Tr) + s.evalNat Tr ≤ r.evalNat 0 + s.evalNat (n - Tr) := by
      have h := hN0 (n - Tr) hm0
      calc r.evalNat (n - Tr) + s.evalNat Tr
          = (r.evalNat (n - Tr) + (s.evalNat Tr - r.evalNat 0)) + r.evalNat 0 := by abel
        _ ≤ s.evalNat (n - Tr) + r.evalNat 0 := by gcongr
        _ = r.evalNat 0 + s.evalNat (n - Tr) := by abel
    calc r.evalNat k + s.evalNat (n - k)
        ≤ r.evalNat (n - Tr) + s.evalNat Tr := hcomp
      _ ≤ r.evalNat 0 + s.evalNat (n - Tr) := hcross
      _ ≤ r.evalNat j + s.evalNat (n - j) := add_le_add (hrmono (Nat.zero_le j)) (hsmono (by omega))

/-- **Lemma 4.4, `≤` direction — general (non-balanced) case.** For nondecreasing `r, s` with `r`
strictly slower (`cr < cs`), the convolution grows by at most `min(cr,cs) = cr` per common period,
eventually: `∃ N, ∀ n ≥ N, (r⊗s)(n+d) ≤ (r⊗s)(n) + cr`. Via the minimizer-region lemma the minimizer
of `(r⊗s)(n)` lies in `r`'s periodic région, so the `+d` time-shift pushes straight into `r`. -/
theorem convNat_add_lcm_le [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Archimedean V]
    (r s : UppSeq V) (hrmono : Monotone r.evalNat) (hsmono : Monotone s.evalNat)
    (hslope : (Nat.lcm r.period s.period / r.period) • r.incr
            < (Nat.lcm r.period s.period / s.period) • s.incr) :
    ∃ N, ∀ n, N ≤ n → r.convNat s (n + Nat.lcm r.period s.period)
      ≤ r.convNat s n + Min.min ((Nat.lcm r.period s.period / r.period) • r.incr)
          ((Nat.lcm r.period s.period / s.period) • s.incr) := by
  obtain ⟨N, hN⟩ := convNat_minimizer_periodic r s hrmono hsmono hslope
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, hkT, hkn, hkeq⟩ := hN n hn
  set d := Nat.lcm r.period s.period with hd
  set cr := (d / r.period) • r.incr with hcr
  have hrstep : r.evalNat (k + d) = r.evalNat k + cr := by
    simpa using r.evalNat_add_mul_of_dvd (hd ▸ Nat.dvd_lcm_left r.period s.period) 1 hkT
  rw [min_eq_left (le_of_lt hslope)]
  calc r.convNat s (n + d)
      ≤ r.evalNat (k + d) + s.evalNat ((n + d) - (k + d)) := r.convNat_le s (by omega)
    _ = r.evalNat (k + d) + s.evalNat (n - k) := by rw [show (n + d) - (k + d) = n - k from by omega]
    _ = (r.evalNat k + cr) + s.evalNat (n - k) := by rw [hrstep]
    _ = (r.evalNat k + s.evalNat (n - k)) + cr := by abel
    _ = r.convNat s n + cr := by rw [hkeq]

/-- **Lemma 4.4, `=` — general (non-balanced) closed form.** For nondecreasing `r, s` with `r`
strictly slower, the convolution is ultimately pseudo-periodic with period `d = lcm` and the book's
increment `min(cr,cs)`: `∃ N, ∀ n ≥ N, (r⊗s)(n+d) = (r⊗s)(n) + min(cr,cs)`. Combines the general `≤`
(minimizer-region) with the general `≥` (`convNat_add_lcm_ge`) — the headline Chapter 4 result. -/
theorem convNat_add_lcm [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Archimedean V]
    (r s : UppSeq V) (hrmono : Monotone r.evalNat) (hsmono : Monotone s.evalNat)
    (hslope : (Nat.lcm r.period s.period / r.period) • r.incr
            < (Nat.lcm r.period s.period / s.period) • s.incr) :
    ∃ N, ∀ n, N ≤ n → r.convNat s (n + Nat.lcm r.period s.period)
      = r.convNat s n + Min.min ((Nat.lcm r.period s.period / r.period) • r.incr)
          ((Nat.lcm r.period s.period / s.period) • s.incr) := by
  obtain ⟨N, hN⟩ := convNat_add_lcm_le r s hrmono hsmono hslope
  exact ⟨max N ((r.vals.length - r.period) + (s.vals.length - s.period) + Nat.lcm r.period s.period),
    fun n hn => le_antisymm (hN n (by omega)) (convNat_add_lcm_ge r s (by omega))⟩

/-- **Minimizer-region lemma — explicit-rank form.** Same as `convNat_minimizer_periodic` but takes
the crossover as a hypothesis `hcross` at an explicit rank `N₀` (stated subtraction-free, so no group
or `Archimedean` is needed) rather than producing it from `Archimedean.arch`. For concrete sequences
`hcross` is discharged by `evalNat_le_of_window_le` + `decide`, making the stabilization rank
`max N₀ rank_r + rank_r` computable. -/
theorem convNat_minimizer_periodic_from [AddCommMonoid V] [LinearOrder V] [IsOrderedAddMonoid V]
    (r s : UppSeq V) (hrmono : Monotone r.evalNat) (hsmono : Monotone s.evalNat) {N₀ : ℕ}
    (hcross : ∀ m, N₀ ≤ m →
      r.evalNat m + s.evalNat (r.vals.length - r.period) ≤ r.evalNat 0 + s.evalNat m)
    (n : ℕ) (hn : max N₀ (r.vals.length - r.period) + (r.vals.length - r.period) ≤ n) :
    ∃ k, r.vals.length - r.period ≤ k ∧ k ≤ n ∧
      r.convNat s n = r.evalNat k + s.evalNat (n - k) := by
  set Tr := r.vals.length - r.period with hTr
  have hnTr : Tr ≤ n := by omega
  have hn2 : Tr ≤ n - Tr := by omega
  have hm0 : N₀ ≤ n - Tr := by omega
  have hIcc : (Finset.Icc Tr n).Nonempty := ⟨Tr, Finset.mem_Icc.mpr ⟨le_rfl, hnTr⟩⟩
  obtain ⟨k, hkmem, hkeq⟩ := Finset.exists_mem_eq_inf' hIcc (fun k => r.evalNat k + s.evalNat (n - k))
  rw [Finset.mem_Icc] at hkmem
  refine ⟨k, hkmem.1, hkmem.2, le_antisymm (r.convNat_le s hkmem.2) ?_⟩
  obtain ⟨j, hj, hje⟩ := r.convNat_eq s n
  rw [hje]
  by_cases hjT : Tr ≤ j
  · rw [← hkeq]; exact Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨hjT, hj⟩)
  · rw [not_le] at hjT
    have hcomp : r.evalNat k + s.evalNat (n - k) ≤ r.evalNat (n - Tr) + s.evalNat Tr := by
      rw [← hkeq]
      have h2 := Finset.inf'_le (fun k => r.evalNat k + s.evalNat (n - k))
        (show n - Tr ∈ Finset.Icc Tr n from Finset.mem_Icc.mpr ⟨hn2, by omega⟩)
      simpa [show n - (n - Tr) = Tr from by omega] using h2
    calc r.evalNat k + s.evalNat (n - k)
        ≤ r.evalNat (n - Tr) + s.evalNat Tr := hcomp
      _ ≤ r.evalNat 0 + s.evalNat (n - Tr) := hcross (n - Tr) hm0
      _ ≤ r.evalNat j + s.evalNat (n - j) := add_le_add (hrmono (Nat.zero_le j)) (hsmono (by omega))

/-- **Lemma 4.4, `=` — explicit-rank form.** Same as `convNat_add_lcm` but from an explicit,
*computable* stabilization rank: combining the explicit-rank minimizer-region (`≤`) with the general
`≥` (`convNat_add_lcm_ge`). With `hcross` discharged by `evalNat_le_of_window_le` + `decide`, this
gives a concrete rank for `convFrom`. -/
theorem convNat_add_lcm_from [AddCommMonoid V] [LinearOrder V] [IsOrderedAddMonoid V]
    (r s : UppSeq V) (hrmono : Monotone r.evalNat) (hsmono : Monotone s.evalNat) {N₀ : ℕ}
    (hcross : ∀ m, N₀ ≤ m →
      r.evalNat m + s.evalNat (r.vals.length - r.period) ≤ r.evalNat 0 + s.evalNat m)
    (hle : (Nat.lcm r.period s.period / r.period) • r.incr
         ≤ (Nat.lcm r.period s.period / s.period) • s.incr)
    (n : ℕ) (hn : max (max N₀ (r.vals.length - r.period) + (r.vals.length - r.period))
        ((r.vals.length - r.period) + (s.vals.length - s.period) + Nat.lcm r.period s.period) ≤ n) :
    r.convNat s (n + Nat.lcm r.period s.period)
      = r.convNat s n + Min.min ((Nat.lcm r.period s.period / r.period) • r.incr)
          ((Nat.lcm r.period s.period / s.period) • s.incr) := by
  have hub : r.convNat s (n + Nat.lcm r.period s.period)
      ≤ r.convNat s n + Min.min ((Nat.lcm r.period s.period / r.period) • r.incr)
          ((Nat.lcm r.period s.period / s.period) • s.incr) := by
    obtain ⟨k, hkT, hkn, hkeq⟩ := convNat_minimizer_periodic_from r s hrmono hsmono hcross n (by omega)
    set d := Nat.lcm r.period s.period with hd
    set cr := (d / r.period) • r.incr with hcr
    have hrstep : r.evalNat (k + d) = r.evalNat k + cr := by
      simpa using r.evalNat_add_mul_of_dvd (hd ▸ Nat.dvd_lcm_left r.period s.period) 1 hkT
    rw [min_eq_left hle]
    calc r.convNat s (n + d)
        ≤ r.evalNat (k + d) + s.evalNat ((n + d) - (k + d)) := r.convNat_le s (by omega)
      _ = r.evalNat (k + d) + s.evalNat (n - k) := by rw [show (n + d) - (k + d) = n - k from by omega]
      _ = (r.evalNat k + cr) + s.evalNat (n - k) := by rw [hrstep]
      _ = (r.evalNat k + s.evalNat (n - k)) + cr := by abel
      _ = r.convNat s n + cr := by rw [hkeq]
  exact le_antisymm hub (convNat_add_lcm_ge r s (by omega))

/-- **Offset crossover window reduction** (generalizes `evalNat_le_of_window_le` with constants
`a, b`). If `r(·)+a ≤ s(·)+b` holds on one full period-window `[N₀, N₀+d)` past the periodic
threshold, it holds for all `n ≥ N₀` — each `+d` step preserves it (`cr ≤ cs`). The window check is
finite/decidable. -/
theorem evalNat_add_le_of_window_le [AddCommMonoid V] [LinearOrder V] [IsOrderedAddMonoid V]
    (r s : UppSeq V) (a b : V) {N₀ : ℕ}
    (hR : max (r.vals.length - r.period) (s.vals.length - s.period) ≤ N₀)
    (hslope : (Nat.lcm r.period s.period / r.period) • r.incr
            ≤ (Nat.lcm r.period s.period / s.period) • s.incr)
    (hwin : ∀ rem, rem < Nat.lcm r.period s.period →
      r.evalNat (N₀ + rem) + a ≤ s.evalNat (N₀ + rem) + b)
    (n : ℕ) (hn : N₀ ≤ n) : r.evalNat n + a ≤ s.evalNat n + b := by
  set d := Nat.lcm r.period s.period with hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero (Nat.lcm_ne_zero r.hperiod.ne' s.hperiod.ne')
  set rem := (n - N₀) % d with hrem
  set q := (n - N₀) / d with hq
  have hremlt : rem < d := Nat.mod_lt _ hd0
  have hsplit : d * q + rem = n - N₀ := Nat.div_add_mod (n - N₀) d
  have hdecomp : n = (N₀ + rem) + q * d := by rw [mul_comm q d]; omega
  have hrn : r.evalNat n = r.evalNat (N₀ + rem) + q • ((d / r.period) • r.incr) := by
    rw [hdecomp]; exact r.evalNat_add_mul_of_dvd (hd ▸ Nat.dvd_lcm_left r.period s.period) q (by omega)
  have hsn : s.evalNat n = s.evalNat (N₀ + rem) + q • ((d / s.period) • s.incr) := by
    rw [hdecomp]; exact s.evalNat_add_mul_of_dvd (hd ▸ Nat.dvd_lcm_right r.period s.period) q (by omega)
  rw [hrn, hsn]
  calc r.evalNat (N₀ + rem) + q • ((d / r.period) • r.incr) + a
      = (r.evalNat (N₀ + rem) + a) + q • ((d / r.period) • r.incr) := by abel
    _ ≤ (s.evalNat (N₀ + rem) + b) + q • ((d / s.period) • s.incr) :=
        add_le_add (hwin rem hremlt) (by gcongr)
    _ = s.evalNat (N₀ + rem) + q • ((d / s.period) • s.incr) + b := by abel

/-- **Lemma 4.4, `=` — fully from a decidable window check.** Combines `convNat_add_lcm_from` with the
offset window reduction: the crossover hypothesis is discharged from a *finite* window check `hwin`
(plus `hR`, `hle`). So for nondecreasing `r, s`, the convolution closed form follows from
`decide`-able hypotheses — the computable route to `convFrom`'s stabilization rank. -/
theorem convNat_add_lcm_window [AddCommMonoid V] [LinearOrder V] [IsOrderedAddMonoid V]
    (r s : UppSeq V) (hrmono : Monotone r.evalNat) (hsmono : Monotone s.evalNat) {N₀ : ℕ}
    (hR : max (r.vals.length - r.period) (s.vals.length - s.period) ≤ N₀)
    (hle : (Nat.lcm r.period s.period / r.period) • r.incr
         ≤ (Nat.lcm r.period s.period / s.period) • s.incr)
    (hwin : ∀ rem, rem < Nat.lcm r.period s.period →
      r.evalNat (N₀ + rem) + s.evalNat (r.vals.length - r.period)
        ≤ s.evalNat (N₀ + rem) + r.evalNat 0)
    (n : ℕ) (hn : max (max N₀ (r.vals.length - r.period) + (r.vals.length - r.period))
        ((r.vals.length - r.period) + (s.vals.length - s.period) + Nat.lcm r.period s.period) ≤ n) :
    r.convNat s (n + Nat.lcm r.period s.period)
      = r.convNat s n + Min.min ((Nat.lcm r.period s.period / r.period) • r.incr)
          ((Nat.lcm r.period s.period / s.period) • s.incr) := by
  refine convNat_add_lcm_from r s hrmono hsmono (N₀ := N₀) (fun m hm => ?_) hle n hn
  rw [add_comm (r.evalNat 0)]
  exact evalNat_add_le_of_window_le r s (s.evalNat (r.vals.length - r.period)) (r.evalNat 0)
    hR hle hwin m hm

/-- **Generic sample-and-close constructor.** Build a `UppSeq` denoting `f : ℕ → V` from its prefix
`f(0 .. T+p-1)`, period `p`, increment `c`. When `T` is a stabilization rank (`f(n+p) = f(n)+c` for
`n ≥ T`), `evalNat` reproduces `f` exactly (`evalNat_fromSamples`). The composable core behind
`minUpp`/`maxUpp` (and the shape of `convFrom`). -/
def fromSamples [Add V] (f : ℕ → V) (c : V) (p : ℕ) (hp : 0 < p) (T : ℕ) : UppSeq V where
  vals := (List.range (T + p)).map f
  incr := c
  period := p
  hperiod := hp
  hlen := by rw [List.length_map, List.length_range]; omega

/-- **`fromSamples` is correct**: when `T` is a stabilization rank (`f(n+p) = f(n)+c` for `n ≥ T`),
the assembled sequence denotes `f` — `(fromSamples f c p hp T).evalNat n = f n` for all `n`. -/
theorem evalNat_fromSamples [AddCommMonoid V] (f : ℕ → V) (c : V) (p : ℕ) (hp : 0 < p) (T : ℕ)
    (hstep : ∀ n, T ≤ n → f (n + p) = f n + c) (n : ℕ) :
    (fromSamples f c p hp T).evalNat n = f n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hL : n < (fromSamples f c p hp T).vals.length
    · rw [evalNat_of_lt _ hL]; simp [fromSamples]
    · have hge : T + p ≤ n := by
        simpa [fromSamples, List.length_map, List.length_range, not_lt] using hL
      conv_lhs => rw [evalNat.eq_def]
      rw [dif_neg hL]
      show (fromSamples f c p hp T).evalNat (n - p) + c = _
      rw [ih (n - p) (by omega), ← hstep (n - p) (by omega), show n - p + p = n from by omega]

/-- **Composable convolution constructor.** Assemble `r ⊗ s` as an actual `UppSeq`: prefix
`(r⊗s)(0 .. T+d-1)` (sampled via `convNat`), period `d = lcm`, increment `min(cr,cs)`. `T` is any
stabilization rank past which the pseudo-period step holds. Computable (`convNat` is), so convolution
results chain through further operators — the heart of the executable (min,plus) calculator. -/
def convFrom [AddCommMonoid V] [LinearOrder V] (r s : UppSeq V) (T : ℕ) : UppSeq V where
  vals := (List.range (T + Nat.lcm r.period s.period)).map (fun n => r.convNat s n)
  incr := Min.min ((Nat.lcm r.period s.period / r.period) • r.incr)
      ((Nat.lcm r.period s.period / s.period) • s.incr)
  period := Nat.lcm r.period s.period
  hperiod := Nat.pos_of_ne_zero (Nat.lcm_ne_zero r.hperiod.ne' s.hperiod.ne')
  hlen := by rw [List.length_map, List.length_range]; omega

/-- **`convFrom` is correct**: when `T` is a genuine stabilization rank (the pseudo-period step
`(r⊗s)(n+d) = (r⊗s)(n) + min(cr,cs)` holds for `n ≥ T`), the assembled `UppSeq` denotes exactly the
convolution — `(r.convFrom s T).evalNat n = (r⊗s)(n)` for all `n`. -/
theorem evalNat_convFrom [AddCommMonoid V] [LinearOrder V] (r s : UppSeq V) (T : ℕ)
    (hstep : ∀ n, T ≤ n → r.convNat s (n + Nat.lcm r.period s.period)
      = r.convNat s n + Min.min ((Nat.lcm r.period s.period / r.period) • r.incr)
          ((Nat.lcm r.period s.period / s.period) • s.incr))
    (n : ℕ) : (r.convFrom s T).evalNat n = r.convNat s n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hL : n < (r.convFrom s T).vals.length
    · rw [evalNat_of_lt _ hL]; simp [convFrom]
    · have hge : T + Nat.lcm r.period s.period ≤ n := by
        simpa [convFrom, List.length_map, List.length_range, not_lt] using hL
      have hd0 : 0 < Nat.lcm r.period s.period :=
        Nat.pos_of_ne_zero (Nat.lcm_ne_zero r.hperiod.ne' s.hperiod.ne')
      conv_lhs => rw [evalNat.eq_def]
      rw [dif_neg hL]
      show (r.convFrom s T).evalNat (n - Nat.lcm r.period s.period)
        + Min.min ((Nat.lcm r.period s.period / r.period) • r.incr)
          ((Nat.lcm r.period s.period / s.period) • s.incr) = _
      rw [ih (n - Nat.lcm r.period s.period) (by omega),
        ← hstep (n - Nat.lcm r.period s.period) (by omega),
        show n - Nat.lcm r.period s.period + Nat.lcm r.period s.period = n from by omega]

/-- Sanity check (gate-verified): `(demoSeq ⊗ demoSeq)(3) = 3` and `(·)(5) = 6`
(`f = 0,1,2,4,5,7,…`; e.g. at `n=3` the min is `f(1)+f(2) = 1+2`). -/
example : demoSeq.convNat demoSeq 3 = 3 ∧ demoSeq.convNat demoSeq 5 = 6 := by native_decide

/-- Sanity (gate-verified): the no-transient closed form on `rate1 (n)=n` ⊗ `rate2 (n)=2n` — both
purely periodic — steps by `min(1,2)=1` per period (`d = lcm 1 1 = 1`): `(r⊗s)(n+1) = (r⊗s)(n)+1`. -/
example : ∀ n ∈ Finset.range 5, rate1.convNat rate2 (n + 1) = rate1.convNat rate2 n + 1 := by
  native_decide

/-- Sanity (gate-verified): the window reduction makes the crossover **decidable** — `rate1 (n)=n ≤
rate2 (n)=2n` for every `n`, discharged from the single-point window check at `N₀ = 0` (`d = lcm 1 1
= 1`) by `decide`/`native_decide`, with no `Archimedean` argument. -/
example (n : ℕ) : rate1.evalNat n ≤ rate2.evalNat n :=
  evalNat_le_of_window_le rate1 rate2 (N₀ := 0) (by decide) (by native_decide)
    (by native_decide) n (Nat.zero_le n)

/-- Sanity (gate-verified): `evalNat_monotone` discharges monotonicity of `rate1 (n)=n` purely by
`decide` — the sorted-prefix check (vacuous, length 1) and the wrap `f(0) ≤ f(1)`. -/
example : Monotone rate1.evalNat := evalNat_monotone rate1 (by decide) (by native_decide)

/-- Sanity (gate-verified): the composable constructor `convFrom` computes the convolution correctly —
`(rate1.convFrom rate2 1)` denotes `rate1 ⊗ rate2` (`= n`), agreeing on the sampled prefix. -/
example : ∀ n ∈ Finset.range 6, (rate1.convFrom rate2 1).evalNat n = rate1.convNat rate2 n := by
  native_decide

/-- Sanity (gate-verified): the convolution's pseudo-period step from rank `T = 4`
(`demoSeq` balanced with itself, `d = 2`, `c = 3`): `(f⊗f)(n+2) = (f⊗f)(n) + 3` for `n ≥ 4`. -/
example : ∀ n ∈ Finset.range 4,
    demoSeq.convNat demoSeq (n + 4 + 2) = demoSeq.convNat demoSeq (n + 4) + 3 := by native_decide

/-! ## Sub-additive-closure foundation — the ⊤-extended carrier `WithTop ℤ`
The closure `f* = ⨅ₙ f^⊗ⁿ` needs the convolution identity `f^⊗0 = δ₀` (`0` at `0`, `+∞` elsewhere),
which `UppSeq` over ℤ cannot hold. `convNat` is generic, so it works over `WithTop ℤ` (where `⊤ = +∞`),
and `δ₀` is representable there — this de-risks the closure arc. -/

/-- The (min,plus) **convolution identity** `δ₀` over `WithTop V`: `δ₀(0) = 0`, `δ₀(n) = ⊤` for
`n ≥ 1` (the closure's neutral element `f^⊗0`). Generic over any pointed value type. -/
def delta0 [Zero V] : UppSeq (WithTop V) := ⟨[0, ⊤], ⊤, 1, by decide, (by decide : (1 : ℕ) ≤ 2)⟩

/-- `δ₀(0) = 0`. -/
theorem delta0_zero [AddMonoid V] : (delta0 (V := V)).evalNat 0 = 0 := by
  rw [evalNat_of_lt delta0 (show (0 : ℕ) < 2 by decide)]; rfl

/-- `δ₀(k) = ⊤` for `k ≥ 1` (the identity is `+∞` off the origin). -/
theorem delta0_pos [AddMonoid V] {k : ℕ} (hk : 1 ≤ k) : (delta0 (V := V)).evalNat k = ⊤ := by
  have hlen : (delta0 (V := V)).vals.length = 2 := rfl
  rcases lt_or_ge k 2 with h | h
  · obtain rfl : k = 1 := by omega
    rw [evalNat_of_lt delta0 (show (1 : ℕ) < 2 by decide)]; rfl
  · conv_lhs => rw [evalNat.eq_def]
    rw [dif_neg (by omega)]
    show (delta0 (V := V)).evalNat (k - 1) + (⊤ : WithTop V) = ⊤
    exact WithTop.add_top _

/-- **`δ₀` is the (min,plus) convolution identity**: `δ₀ ⊗ f = f` for every `f` over `WithTop V`. The
`k = 0` term is `0 + f(n) = f(n)`; every `k ≥ 1` term is `⊤ + f(n-k) = ⊤ ≥ f(n)`, so the infimum is
`f(n)`. This is `f^⊗0 ⊗ f = f`, the base of the closure iteration. -/
theorem convNat_delta0 [AddCommMonoid V] [LinearOrder V] [IsOrderedAddMonoid V]
    (f : UppSeq (WithTop V)) (n : ℕ) : delta0.convNat f n = f.evalNat n := by
  refine le_antisymm ?_ ?_
  · calc delta0.convNat f n ≤ delta0.evalNat 0 + f.evalNat (n - 0) := delta0.convNat_le f (Nat.zero_le n)
      _ = f.evalNat n := by rw [delta0_zero, Nat.sub_zero, zero_add]
  · obtain ⟨k, hk, heq⟩ := delta0.convNat_eq f n
    rw [heq]
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · simp [delta0_zero]
    · rw [delta0_pos hk1, WithTop.top_add]; exact le_top

/-- A ⊤-extended demo sequence over `WithTop ℤ` (to exercise the closure carrier). -/
def demoWT : UppSeq (WithTop ℤ) := ⟨[0, 1, 2], 3, 2, by decide, by decide⟩

/-- Sanity (gate-verified): `δ₀ ⊗ f = f` computed natively over `WithTop ℤ` (the general proof is
`convNat_delta0`), confirming the ⊤-extended carrier evaluates correctly. -/
example : ∀ n ∈ Finset.range 6, delta0.convNat demoWT n = demoWT.evalNat n := by native_decide

/-- One (min,plus) convolution by a function null at the origin can only **decrease**: if `f(0) = 0`
then `(f ⊗ g)(n) ≤ g(n)` (take `k = 0` in the infimum). Hence the closure iterates `f^⊗ⁿ` are
non-increasing in `n` — the structural basis of `f* = ⨅ₙ f^⊗ⁿ`. -/
theorem convNat_le_of_zero [AddCommMonoid V] [LinearOrder V] (r s : UppSeq V) (h0 : r.evalNat 0 = 0)
    (n : ℕ) : r.convNat s n ≤ s.evalNat n := by
  calc r.convNat s n ≤ r.evalNat 0 + s.evalNat (n - 0) := r.convNat_le s (Nat.zero_le n)
    _ = s.evalNat n := by rw [h0, Nat.sub_zero, zero_add]

/-- The `m`-fold (min,plus) self-convolution `f^⊗m` at `n` over `WithTop ℤ`: `f^⊗0 = δ₀`,
`f^⊗(m+1) = f ⊗ f^⊗m`. The building block of the sub-additive closure. -/
def iterConvNat (f : UppSeq (WithTop ℤ)) : ℕ → ℕ → WithTop ℤ
  | 0, n => delta0.evalNat n
  | (m + 1), n => (Finset.range (n + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
      (fun k => f.evalNat k + iterConvNat f m (n - k))

/-- The **sub-additive-closure approximant** `⨅_{m=0}^{N} f^⊗m` at `n` — the closure truncated to `N`
iterations. The true closure `f* = ⨅ₘ f^⊗m` is reached at finite `N` for UPP `f` (Lemma 4.7); the
stabilization bound and UPP-ness of `f*` are future work (the research-grade part). -/
def closureApproxNat (f : UppSeq (WithTop ℤ)) (N n : ℕ) : WithTop ℤ :=
  (Finset.range (N + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩ (fun m => iterConvNat f m n)

/-- Pure rate `f(n) = n` over `WithTop ℤ` (null at the origin). -/
def rateWT : UppSeq (WithTop ℤ) := ⟨[0], 1, 1, by decide, by decide⟩

/-- Sanity (gate-verified): the sub-additive closure of a pure rate function is itself,
`(rate)* = rate` — since `rate ⊗ rate = rate`, so `⨅ₘ rate^⊗m = δ₀ ⊓ rate = rate`. -/
example : ∀ n ∈ Finset.range 5, closureApproxNat rateWT 3 n = rateWT.evalNat n := by native_decide

/-- `f^⊗1 = f`: one iteration is the identity convolution (`f ⊗ δ₀ = f`, by `convNat_delta0`). -/
theorem iterConvNat_one (f : UppSeq (WithTop ℤ)) (n : ℕ) : iterConvNat f 1 n = f.evalNat n := by
  have h : iterConvNat f 1 n = f.convNat delta0 n := rfl
  rw [h, convNat_comm, convNat_delta0]

/-- The closure approximant is `≤ δ₀` (the `m = 0` term `f^⊗0 = δ₀`). -/
theorem closureApproxNat_le_delta0 (f : UppSeq (WithTop ℤ)) (N n : ℕ) :
    closureApproxNat f N n ≤ delta0.evalNat n :=
  Finset.inf'_le (fun m => iterConvNat f m n) (Finset.mem_range.mpr (Nat.succ_pos N))

/-- The closure approximant is `≤ f` (for `N ≥ 1`, the `m = 1` term `f^⊗1 = f`). -/
theorem closureApproxNat_le_self (f : UppSeq (WithTop ℤ)) {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    closureApproxNat f N n ≤ f.evalNat n := by
  rw [← iterConvNat_one f n]
  exact Finset.inf'_le (fun m => iterConvNat f m n) (Finset.mem_range.mpr (by omega))

/-- The closure approximant is **antitone in `N`** — `⨅_{m≤N+1} f^⊗ᵐ ≤ ⨅_{m≤N} f^⊗ᵐ` (one more term
can only lower the infimum). So the approximants form a non-increasing sequence and converge
pointwise; the closure is their limit. -/
theorem closureApproxNat_antitone (f : UppSeq (WithTop ℤ)) (N n : ℕ) :
    closureApproxNat f (N + 1) n ≤ closureApproxNat f N n := by
  unfold closureApproxNat
  apply Finset.le_inf'
  intro m hm
  exact Finset.inf'_le _ (Finset.mem_range.mpr
    (lt_trans (Finset.mem_range.mp hm) (Nat.lt_succ_self _)))

/-- For an **idempotent** (sub-additive) `f` — `f ⊗ f = f` — every iterate collapses: `f^⊗ᵐ = f`
for all `m ≥ 1` (induction: `f^⊗(m+1) = f ⊗ f^⊗ᵐ = f ⊗ f = f`). -/
theorem iterConvNat_eq_self_of_idem (f : UppSeq (WithTop ℤ))
    (hidem : ∀ n, f.convNat f n = f.evalNat n) :
    ∀ m, 1 ≤ m → ∀ n, iterConvNat f m n = f.evalNat n := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ k ih =>
    intro _ n
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · exact iterConvNat_one f n
    · rw [show iterConvNat f (k + 1) n
            = (Finset.range (n + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
                (fun j => f.evalNat j + iterConvNat f k (n - j)) from rfl,
        show (fun j => f.evalNat j + iterConvNat f k (n - j))
            = (fun j => f.evalNat j + f.evalNat (n - j)) from
          funext fun j => by rw [ih hk1 (n - j)]]
      exact hidem n

/-- Lower-bound the closure approximant: `x ≤ ⨅_{m≤N} f^⊗ᵐ` from `x ≤ f^⊗ᵐ` for every `m ≤ N`. -/
theorem le_closureApproxNat {x : WithTop ℤ} (f : UppSeq (WithTop ℤ)) {N n : ℕ}
    (h : ∀ m, m < N + 1 → x ≤ iterConvNat f m n) : x ≤ closureApproxNat f N n :=
  Finset.le_inf' _ _ (fun m hm => h m (Finset.mem_range.mp hm))

/-- **Closure iteration recurrence**: `closureApprox(N+1) = δ₀ ⊓ (f ⊗ closureApprox(N))` (pointwise) —
splitting off `f^⊗0 = δ₀` and pulling `f` out of the remaining iterates. This realizes the closure as
an actual fixed-point iteration `g_{N+1} = δ₀ ⊓ (f ⊗ g_N)`, and gives "fixed point ⟹ stable" for free
(`closureApproxNat_stable`). -/
theorem closureApproxNat_succ (f : UppSeq (WithTop ℤ)) (N n : ℕ) :
    closureApproxNat f (N + 1) n = Min.min (delta0.evalNat n)
      ((Finset.range (n + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
        (fun k => f.evalNat k + closureApproxNat f N (n - k))) := by
  refine le_antisymm (le_min (closureApproxNat_le_delta0 f (N + 1) n) ?_) ?_
  · apply Finset.le_inf'
    intro k hk
    obtain ⟨m, hm, hmeq⟩ := Finset.exists_mem_eq_inf' (s := Finset.range (N + 1))
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩ (fun m => iterConvNat f m (n - k))
    have hmle : m < N + 1 := Finset.mem_range.mp hm
    have hmeq' : closureApproxNat f N (n - k) = iterConvNat f m (n - k) := hmeq
    calc closureApproxNat f (N + 1) n
        ≤ iterConvNat f (m + 1) n := Finset.inf'_le _ (Finset.mem_range.mpr (by omega))
      _ ≤ f.evalNat k + iterConvNat f m (n - k) := Finset.inf'_le _ hk
      _ = f.evalNat k + closureApproxNat f N (n - k) := by rw [hmeq']
  · apply le_closureApproxNat
    intro m hmr
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · exact min_le_left _ _
    · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      have hm'le : m' < N + 1 := by omega
      refine le_trans (min_le_right _ _) ?_
      show (Finset.range (n + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
          (fun k => f.evalNat k + closureApproxNat f N (n - k)) ≤ iterConvNat f (m' + 1) n
      apply Finset.le_inf'
      intro j hj
      calc (Finset.range (n + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
            (fun k => f.evalNat k + closureApproxNat f N (n - k))
          ≤ f.evalNat j + closureApproxNat f N (n - j) := Finset.inf'_le _ hj
        _ ≤ f.evalNat j + iterConvNat f m' (n - j) := by
            gcongr
            exact Finset.inf'_le _ (Finset.mem_range.mpr hm'le)

/-- **Fixed point ⟹ stable** (from the recurrence): *if* the approximant stops changing at step `N`
(`closureApprox(N+1) = closureApprox(N)` pointwise everywhere), the next step is unchanged too —
`closureApprox(N+2) = δ₀ ⊓ (f ⊗ closureApprox(N+1)) = δ₀ ⊓ (f ⊗ closureApprox(N)) = closureApprox(N+1)`.
Caveat: this *global* hypothesis holds for **idempotent** `f` (at `N = 1`, `closureApproxNat_idem`) but
**not** for general `f` — e.g. `β_{1,2}` has `closureApprox(N) = β_{1,2N}`, which never globally
stabilizes (`f^⊗ᵐ` does not reach `f*` at finite `N`). The general closure needs the min-plus matrix
cyclicity theorem (`Aᵏ⁺ᵈ = Aᵏ + λd`, BCOQ Thm 3.112), not truncated convolution. -/
theorem closureApproxNat_stable_step (f : UppSeq (WithTop ℤ)) {N : ℕ}
    (h : ∀ n, closureApproxNat f (N + 1) n = closureApproxNat f N n) (n : ℕ) :
    closureApproxNat f (N + 2) n = closureApproxNat f (N + 1) n := by
  rw [show N + 2 = N + 1 + 1 from rfl, closureApproxNat_succ f (N + 1) n, closureApproxNat_succ f N n]
  simp only [h]

/-- **Once stable, stays stable.** If `closureApprox(N+1) = closureApprox(N)` (pointwise everywhere)
then `closureApprox(N+j) = closureApprox(N)` for *every* `j` — the approximant is constant from `N` on,
hence equals `f*`. (Induction via the recurrence.) Same caveat as `closureApproxNat_stable_step`: the
global hypothesis is met only for **idempotent** `f`; for general `f` the truncated approximant never
globally stabilizes, so this does not yield the general closure (which needs matrix cyclicity). -/
theorem closureApproxNat_eq_of_stable (f : UppSeq (WithTop ℤ)) {N : ℕ}
    (h : ∀ n, closureApproxNat f (N + 1) n = closureApproxNat f N n) :
    ∀ j n, closureApproxNat f (N + j) n = closureApproxNat f N n := by
  intro j
  induction j with
  | zero => intro n; rfl
  | succ i ih =>
    intro n
    have hstep : closureApproxNat f (N + i + 1) n = closureApproxNat f (N + 1) n := by
      rw [closureApproxNat_succ f (N + i) n, closureApproxNat_succ f N n]
      simp only [ih]
    rw [show N + (i + 1) = N + i + 1 from rfl, hstep, h]

/-- **Sub-additive closure of an idempotent `f`**: `f* = δ₀ ⊓ f`. For `f ⊗ f = f` (e.g. a
sub-additive service curve) the closure stabilizes at one iteration — `⨅_{m≤N} f^⊗ᵐ = δ₀ ⊓ f` for
every `N ≥ 1` — so the closure is computed exactly with no iteration bound needed. (The general
non-idempotent case, where the iterates genuinely descend, needs the stabilization theory of Lemma
4.7–4.9 and remains open.) -/
theorem closureApproxNat_idem (f : UppSeq (WithTop ℤ)) (hidem : ∀ n, f.convNat f n = f.evalNat n)
    {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    closureApproxNat f N n = Min.min (delta0.evalNat n) (f.evalNat n) := by
  refine le_antisymm
    (le_min (closureApproxNat_le_delta0 f N n) (closureApproxNat_le_self f hN n)) ?_
  apply Finset.le_inf'
  intro m _
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · exact min_le_left _ _
  · rw [iterConvNat_eq_self_of_idem f hidem m hm1 n]
    exact min_le_right _ _

/-- The rate-latency curve `β_{1,2}(n) = (n-2)₊` over `WithTop ℤ` — a **non-idempotent** `f`
(`β ⊗ β = β_{1,4} ≠ β`, super-additive), to exercise the *general* closure iteration. -/
def betaWT : UppSeq (WithTop ℤ) := ⟨[0, 0, 0], 1, 1, by decide, by decide⟩

/-- Gate-verified **caution** — why the truncated approximant is *not* the general closure. For the
non-idempotent `β_{1,2}`, `closureApprox(N) = β_{1,2N}` (rate 1, latency `2N`), which never converges
globally: it agrees with the next step on a small window (`closureApprox(2) = closureApprox(3)` on
`[0,4)`, both `0` there) yet **differs** at `n = 5` (`1 ≠ 0`). So a finite-window fixpoint check gives
a false positive, and `closureApproxNat_stable_step`'s global hypothesis fails here — the general
closure genuinely requires min-plus matrix cyclicity (BCOQ Thm 3.112), not truncated convolution. -/
example : (∀ n ∈ Finset.range 4, closureApproxNat betaWT 2 n = closureApproxNat betaWT 3 n)
    ∧ closureApproxNat betaWT 2 5 ≠ closureApproxNat betaWT 3 5 := by native_decide

end UppSeq
end DeepWiki
