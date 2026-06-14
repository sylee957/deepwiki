import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.NNReal.Basic

/-! # Packet curves
Lower and upper bounds on the total length of any block of consecutive packets.
For a packet-length sequence `L : ℕ → ℝ≥0`, the pair `(Lˡ, Lᵘ)` is a packet
curve when `Lˡ n ≤ ∑_{j=i+1}^{i+n} L j ≤ Lᵘ n` for every starting index `i` and
block size `n` — the packetizer analogue of arrival/service curves. -/

namespace DeepWiki

open scoped NNReal

/-- **Packet curves**: `Lˡ, Lᵘ : ℕ → ℝ≥0` bound the total length of any `n`
consecutive packets of the packet-length sequence `L`:
`Lˡ n ≤ ∑_{j = i+1}^{i+n} L j ≤ Lᵘ n` for all start `i` and count `n`. -/
def IsPacketCurve (L Ll Lu : ℕ → ℝ≥0) : Prop :=
  ∀ i n : ℕ,
    Ll n ≤ (∑ j ∈ Finset.Ico (i + 1) (i + n + 1), L j)
      ∧ (∑ j ∈ Finset.Ico (i + 1) (i + n + 1), L j) ≤ Lu n

/-- The lower packet curve vanishes at `0`: a block of zero packets has total
length `0`. -/
theorem IsPacketCurve.lower_zero {L Ll Lu : ℕ → ℝ≥0}
    (h : IsPacketCurve L Ll Lu) : Ll 0 = 0 := by
  have hle := (h 0 0).1
  simpa using hle

/-- The packet-curve bounds compose: at any start `i`, the block sum lies
between `Lˡ n` and `Lᵘ n`. -/
theorem IsPacketCurve.block_mem {L Ll Lu : ℕ → ℝ≥0}
    (h : IsPacketCurve L Ll Lu) (i n : ℕ) :
    Ll n ≤ (∑ j ∈ Finset.Ico (i + 1) (i + n + 1), L j)
      ∧ (∑ j ∈ Finset.Ico (i + 1) (i + n + 1), L j) ≤ Lu n := h i n

end DeepWiki
