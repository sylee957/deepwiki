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

/-- The denoted sequence is unchanged on the stored transient/period prefix: `f(n) = vals[n]`. -/
theorem evalNat_of_lt [Add V] (r : UppSeq V) {n : ℕ} (hn : n < r.vals.length) :
    r.evalNat n = r.vals.get ⟨n, hn⟩ := by
  conv_lhs => rw [evalNat.eq_def]
  rw [dif_pos hn]

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

end UppSeq
end DeepWiki
