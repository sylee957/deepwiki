import DeepWiki.NetworkCalculus.UppSequence
import DeepWiki.NetworkCalculus.FunctionDioids

/-! # The continuous-time convolution of PWL readings vs the discrete convolution
The discrete-to-continuous bridge for the (min,+) convolution. A UPP sequence's piecewise-linear
reading `toFunPWL` (`DeepWiki/NetworkCalculus/UppSequence.lean`) is a genuine continuous-time curve;
its continuous (min,+) convolution `minConv` (`FunctionDioids`) over `ℝ` is **bounded above by the
discrete convolution `convNat`** at integer points — the continuous model never gives a larger value,
since the integer splits are among the real splits. (The reverse — equality — needs the convexity of
the curves: for convex PWL functions the continuous infimum is attained at an integer breakpoint. That
is the remaining open step of the bridge.) -/

namespace DeepWiki.UppSeq

open DeepWiki
open scoped NNReal Classical

/-- **Bridge (one direction):** the continuous (min,+) convolution of the PWL readings is `≤` the
discrete convolution at integer arguments — `minConv (toFunPWL r) (toFunPWL s) n ≤ convNat r s n`.
The discrete convolution's minimizing integer split `(k, n−k)` is also a real split, and there
`toFunPWL` reads off the samples (`toFunPWL_natCast`); boundedness below (`toFunPWL_ge_finite_inf`)
makes the infimum a genuine lower bound over `ℝ`. -/
theorem minConv_toFunPWL_le_convNat (r s : UppSeq ℚ) (n : ℕ) :
    minConv r.toFunPWL s.toFunPWL (n : ℝ≥0) ≤ (r.convNat s n : ℝ) := by
  set Lr := (Finset.range (n + 2)).inf' (Finset.nonempty_range_iff.mpr (by omega))
    (fun j => (r.evalNat j : ℝ)) with hLr
  set Ls := (Finset.range (n + 2)).inf' (Finset.nonempty_range_iff.mpr (by omega))
    (fun j => (s.evalNat j : ℝ)) with hLs
  have hbb : BddBelow (Set.range fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = (n : ℝ≥0)} =>
      r.toFunPWL p.1.1 + s.toFunPWL p.1.2) := by
    refine ⟨Lr + Ls, ?_⟩
    rintro x ⟨p, rfl⟩
    have hp1 : p.1.1 ≤ (n : ℝ≥0) := (self_le_add_right p.1.1 p.1.2).trans_eq p.2
    have hp2 : p.1.2 ≤ (n : ℝ≥0) := (self_le_add_left p.1.2 p.1.1).trans_eq p.2
    exact add_le_add (toFunPWL_ge_finite_inf r n p.1.1 hp1) (toFunPWL_ge_finite_inf s n p.1.2 hp2)
  obtain ⟨k, hk, hke⟩ := r.convNat_eq s n
  rw [hke]
  have hsplit : (k : ℝ≥0) + ((n - k : ℕ) : ℝ≥0) = (n : ℝ≥0) := by
    rw [← Nat.cast_add]; congr 1; omega
  push_cast
  calc minConv r.toFunPWL s.toFunPWL (n : ℝ≥0)
      ≤ r.toFunPWL (k : ℝ≥0) + s.toFunPWL ((n - k : ℕ) : ℝ≥0) :=
        ciInf_le_of_le hbb ⟨((k : ℝ≥0), ((n - k : ℕ) : ℝ≥0)), hsplit⟩ le_rfl
    _ = (r.evalNat k : ℝ) + (s.evalNat (n - k) : ℝ) := by
        rw [toFunPWL_natCast, toFunPWL_natCast]

/-- **Per real split, the discrete convolution dominates** — `convNat r s n ≤ toFunPWL r u + toFunPWL
s v` for *every* real split `u + v = n`, with **no convexity hypothesis**. The integer parts satisfy
`⌊u⌋ + ⌊v⌋ ∈ {n−1, n}`; the lerp value is then a convex combination of the two "rounding-corner"
integer-split values `(⌊u⌋, ⌊v⌋+1)` and `(⌊u⌋+1, ⌊v⌋)` (both summing to `n`), each `≥ convNat`. -/
theorem convNat_le_toFunPWL_add (r s : UppSeq ℚ) (n : ℕ) (u v : ℝ≥0) (huv : u + v = (n : ℝ≥0)) :
    (r.convNat s n : ℝ) ≤ r.toFunPWL u + s.toFunPWL v := by
  have huv_r : (u : ℝ) + (v : ℝ) = (n : ℝ) := by exact_mod_cast huv
  have ha_le : ((⌊u⌋₊ : ℕ) : ℝ) ≤ (u : ℝ) := by exact_mod_cast Nat.floor_le zero_le
  have ha_lt : (u : ℝ) < ((⌊u⌋₊ : ℕ) : ℝ) + 1 := by exact_mod_cast Nat.lt_floor_add_one u
  have hb_le : ((⌊v⌋₊ : ℕ) : ℝ) ≤ (v : ℝ) := by exact_mod_cast Nat.floor_le zero_le
  have hb_lt : (v : ℝ) < ((⌊v⌋₊ : ℕ) : ℝ) + 1 := by exact_mod_cast Nat.lt_floor_add_one v
  have hab_le : ⌊u⌋₊ + ⌊v⌋₊ ≤ n := by
    have : ((⌊u⌋₊ + ⌊v⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hn_le : n ≤ ⌊u⌋₊ + ⌊v⌋₊ + 1 := by
    have h : (n : ℝ) < ((⌊u⌋₊ + ⌊v⌋₊ + 2 : ℕ) : ℝ) := by push_cast; linarith
    have : n < ⌊u⌋₊ + ⌊v⌋₊ + 2 := by exact_mod_cast h
    omega
  have hu_eq : r.toFunPWL u = (1 - ((u : ℝ) - (⌊u⌋₊ : ℕ))) * (r.evalNat ⌊u⌋₊ : ℝ)
      + ((u : ℝ) - (⌊u⌋₊ : ℕ)) * (r.evalNat (⌊u⌋₊ + 1) : ℝ) := by
    rw [toFunPWL_eq_lerp]; push_cast; ring
  have hv_eq : s.toFunPWL v = (1 - ((v : ℝ) - (⌊v⌋₊ : ℕ))) * (s.evalNat ⌊v⌋₊ : ℝ)
      + ((v : ℝ) - (⌊v⌋₊ : ℕ)) * (s.evalNat (⌊v⌋₊ + 1) : ℝ) := by
    rw [toFunPWL_eq_lerp]; push_cast; ring
  rw [hu_eq, hv_eq]
  rcases (by omega : n = ⌊u⌋₊ + ⌊v⌋₊ ∨ n = ⌊u⌋₊ + ⌊v⌋₊ + 1) with hcase | hcase
  · have hnr : (n : ℝ) = (⌊u⌋₊ : ℕ) + (⌊v⌋₊ : ℕ) := by rw [hcase]; push_cast; ring
    have hαz : (u : ℝ) - (⌊u⌋₊ : ℕ) = 0 := by linarith
    have hβz : (v : ℝ) - (⌊v⌋₊ : ℕ) = 0 := by linarith
    have key : (r.convNat s n : ℝ) ≤ (r.evalNat ⌊u⌋₊ : ℝ) + (s.evalNat ⌊v⌋₊ : ℝ) := by
      have h := r.convNat_le s (show ⌊u⌋₊ ≤ n by omega)
      have hnb : n - ⌊u⌋₊ = ⌊v⌋₊ := by omega
      rw [hnb] at h; exact_mod_cast h
    rw [hαz, hβz]; nlinarith [key]
  · have hnr : (n : ℝ) = (⌊u⌋₊ : ℕ) + (⌊v⌋₊ : ℕ) + 1 := by rw [hcase]; push_cast; ring
    have hsum : ((u : ℝ) - (⌊u⌋₊ : ℕ)) + ((v : ℝ) - (⌊v⌋₊ : ℕ)) = 1 := by linarith
    have hα0 : 0 ≤ (u : ℝ) - (⌊u⌋₊ : ℕ) := by linarith
    have hα1 : (u : ℝ) - (⌊u⌋₊ : ℕ) ≤ 1 := by linarith
    have hC1 : (r.convNat s n : ℝ) ≤ (r.evalNat ⌊u⌋₊ : ℝ) + (s.evalNat (⌊v⌋₊ + 1) : ℝ) := by
      have h := r.convNat_le s (show ⌊u⌋₊ ≤ n by omega)
      have hnb : n - ⌊u⌋₊ = ⌊v⌋₊ + 1 := by omega
      rw [hnb] at h; exact_mod_cast h
    have hC2 : (r.convNat s n : ℝ) ≤ (r.evalNat (⌊u⌋₊ + 1) : ℝ) + (s.evalNat ⌊v⌋₊ : ℝ) := by
      have h := r.convNat_le s (show ⌊u⌋₊ + 1 ≤ n by omega)
      have hnb : n - (⌊u⌋₊ + 1) = ⌊v⌋₊ := by omega
      rw [hnb] at h; exact_mod_cast h
    have hβval : (v : ℝ) - (⌊v⌋₊ : ℕ) = 1 - ((u : ℝ) - (⌊u⌋₊ : ℕ)) := by linarith
    rw [hβval]
    nlinarith [mul_nonneg (sub_nonneg.mpr hα1) (sub_nonneg.mpr hC1),
      mul_nonneg hα0 (sub_nonneg.mpr hC2)]

/-- **Bridge (reverse direction):** the discrete convolution is `≤` the continuous one at integers —
every real split dominates `convNat` (`convNat_le_toFunPWL_add`), so `le_minConv` lifts it to the
infimum. -/
theorem convNat_le_minConv_toFunPWL (r s : UppSeq ℚ) (n : ℕ) :
    (r.convNat s n : ℝ) ≤ minConv r.toFunPWL s.toFunPWL (n : ℝ≥0) :=
  le_minConv (fun u v huv => convNat_le_toFunPWL_add r s n u v huv)

/-- **The discrete-to-continuous convolution bridge, as an equality (unconditional).** At every
integer point the continuous (min,+) convolution of the PWL readings equals the discrete convolution:
`minConv (toFunPWL r) (toFunPWL s) n = convNat r s n`. No convexity is needed — the piecewise-linear
interpolation already forces each real split to be a convex combination of integer splits. This is the
faithfulness of the discrete UPP convolution as a continuous-time network-calculus operation. -/
theorem minConv_toFunPWL_eq_convNat (r s : UppSeq ℚ) (n : ℕ) :
    minConv r.toFunPWL s.toFunPWL (n : ℝ≥0) = (r.convNat s n : ℝ) :=
  le_antisymm (minConv_toFunPWL_le_convNat r s n) (convNat_le_minConv_toFunPWL r s n)

end DeepWiki.UppSeq
