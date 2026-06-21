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

end DeepWiki.UppSeq
