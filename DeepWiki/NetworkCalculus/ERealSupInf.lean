import Mathlib.Data.EReal.Operations
import Mathlib.Order.CompleteLattice.Basic

/-! # `EReal` distributivity of negation and finite addition over `⨆`/`⨅`
The supremum/infimum identities Mathlib provides only as inequalities
(`iSup_add_le_add_iSup`, `add_iInf_le_iInf_add`) or not at all, needed for the
Legendre–Fenchel transform of an inf-convolution: negation swaps `⨆`/`⨅`, and a
*finite* additive shift commutes with `⨆` (hence with the `c − ⨅` reading). -/

namespace DeepWiki

open scoped Classical

/-- Negation turns a supremum into an infimum: `−(⨆ i, x i) = ⨅ i, −x i`. -/
theorem neg_iSup {ι : Sort*} (x : ι → EReal) : -(⨆ i, x i) = ⨅ i, -(x i) := by
  apply le_antisymm
  · refine le_iInf fun i => ?_
    rw [EReal.neg_le_neg_iff]
    exact le_iSup x i
  · rw [EReal.le_neg]
    refine iSup_le fun i => ?_
    rw [EReal.le_neg]
    exact iInf_le (fun i => -(x i)) i

/-- Negation turns an infimum into a supremum: `−(⨅ i, x i) = ⨆ i, −x i`. -/
theorem neg_iInf {ι : Sort*} (x : ι → EReal) : -(⨅ i, x i) = ⨆ i, -(x i) := by
  apply le_antisymm
  · rw [EReal.neg_le]
    refine le_iInf fun i => ?_
    rw [EReal.neg_le]
    exact le_iSup (fun i => -(x i)) i
  · refine iSup_le fun i => ?_
    rw [EReal.neg_le_neg_iff]
    exact iInf_le x i

/-- A finite additive shift commutes with a supremum:
`↑r + ⨆ i, x i = ⨆ i, (↑r + x i)`. -/
theorem coe_add_iSup {ι : Sort*} (r : ℝ) (x : ι → EReal) :
    (r : EReal) + ⨆ i, x i = ⨆ i, ((r : EReal) + x i) := by
  apply le_antisymm
  · have hs : (⨆ i, x i) ≤ (⨆ i, ((r : EReal) + x i)) - (r : EReal) := by
      refine iSup_le fun i => ?_
      rw [EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot r)) (.inl (EReal.coe_ne_top r)), add_comm]
      exact le_iSup (fun i => (r : EReal) + x i) i
    rw [add_comm]
    exact (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot r)) (.inl (EReal.coe_ne_top r))).mp hs
  · exact iSup_le fun i => add_le_add le_rfl (le_iSup x i)

/-- A finite shift commutes with a supremum on the right:
`(⨆ i, x i) + ↑r = ⨆ i, (x i + ↑r)`. -/
theorem iSup_add_coe {ι : Sort*} (r : ℝ) (x : ι → EReal) :
    (⨆ i, x i) + (r : EReal) = ⨆ i, (x i + (r : EReal)) := by
  simp only [add_comm _ (r : EReal)]
  exact coe_add_iSup r x

/-- A finite value minus an infimum is the supremum of the differences:
`↑r − ⨅ i, x i = ⨆ i, (↑r − x i)`. -/
theorem coe_sub_iInf {ι : Sort*} (r : ℝ) (x : ι → EReal) :
    (r : EReal) - ⨅ i, x i = ⨆ i, ((r : EReal) - x i) := by
  rw [sub_eq_add_neg, neg_iInf, coe_add_iSup]
  simp only [sub_eq_add_neg]

end DeepWiki
