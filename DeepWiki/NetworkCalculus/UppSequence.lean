import DeepWiki.NetworkCalculus.UltimatelyPseudoPeriodic

/-! # Finite representation of UPP functions: pseudo-periodic sequences
The *computable* layer toward an executable (min,plus) calculator. A `UppSeq` stores a finite
prefix `vals` of values `f(0), …, f(L-1)` together with a positive `period` and an `incr`-ement; it
denotes the discrete pseudo-periodic sequence `evalNat : ℕ → V` with `f(n) = f(n - period) + incr`
for `n ≥ L`. `evalNat` is native-compilable (`#eval`-able), and `evalNat_add_period` is its discrete
pseudo-periodicity. (The step-function reading `ℝ≥0 → V` that ties this to the semantic
`IsUPPWith`/`IsUPP` layer is the next step.) -/

namespace DeepWiki

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

/-- The denoted sequence is unchanged on the stored transient/period prefix: `f(n) = vals[n]`. -/
theorem evalNat_of_lt [Add V] (r : UppSeq V) {n : ℕ} (hn : n < r.vals.length) :
    r.evalNat n = r.vals.get ⟨n, hn⟩ := by
  conv_lhs => rw [evalNat.eq_def]
  rw [dif_pos hn]

/-! ## A worked example (sanity checks, gate-verified by `native_decide`) -/

/-- `f(0),f(1),f(2) = 0,1,2`, then period `2`, increment `3`: so `f(n+2) = f(n)+3` for `n ≥ 1`. -/
def demoSeq : UppSeq ℕ := ⟨[0, 1, 2], 3, 2, by decide, by decide⟩

example : demoSeq.evalNat 2 = 2 := by native_decide
example : demoSeq.evalNat 3 = 4 := by native_decide  -- f(1) + 3
example : demoSeq.evalNat 4 = 5 := by native_decide  -- f(2) + 3
example : demoSeq.evalNat 5 = 7 := by native_decide  -- f(3) + 3
example : demoSeq.evalNat 7 = 10 := by native_decide -- f(5) + 3

end UppSeq
end DeepWiki
