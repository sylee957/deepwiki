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

/-- Addition distributes over a (nonempty) supremum on the left, for *any*
shift `c` — including `±∞`: `c + ⨆ i, b i = ⨆ i, (c + b i)`. (For `c = ⊤` the
`≤` direction uses that a non-`⊥` supremum has a non-`⊥` witness.) -/
theorem add_iSup {ι : Sort*} [Nonempty ι] (c : EReal) (b : ι → EReal) :
    c + ⨆ i, b i = ⨆ i, (c + b i) := by
  apply le_antisymm
  · induction c using EReal.rec with
    | bot => rw [EReal.bot_add]; exact bot_le
    | coe r => exact le_of_eq (coe_add_iSup r b)
    | top =>
      rcases eq_or_ne (⨆ i, b i) ⊥ with hsup | hsup
      · rw [hsup, EReal.add_bot]; exact bot_le
      · obtain ⟨j, hj⟩ : ∃ j, b j ≠ ⊥ := by
          by_contra h
          push Not at h
          exact hsup (by simp only [h, iSup_const])
        rw [EReal.top_add_of_ne_bot hsup]
        exact le_iSup_of_le j (le_of_eq (EReal.top_add_of_ne_bot hj).symm)
  · exact iSup_le fun i => add_le_add le_rfl (le_iSup b i)

/-- Addition distributes over a (nonempty) supremum on the right:
`(⨆ i, a i) + c = ⨆ i, (a i + c)`. -/
theorem iSup_add {ι : Sort*} [Nonempty ι] (a : ι → EReal) (c : EReal) :
    (⨆ i, a i) + c = ⨆ i, (a i + c) := by
  rw [add_comm, add_iSup]
  exact iSup_congr fun i => add_comm c (a i)

/-- The sum of two (nonempty) suprema is the supremum of the pairwise sums:
`(⨆ i, a i) + (⨆ j, b j) = ⨆ i, ⨆ j, (a i + b j)`. -/
theorem iSup_add_iSup {ι κ : Sort*} [Nonempty ι] [Nonempty κ]
    (a : ι → EReal) (b : κ → EReal) :
    (⨆ i, a i) + (⨆ j, b j) = ⨆ i, ⨆ j, (a i + b j) := by
  rw [iSup_add]
  exact iSup_congr fun i => add_iSup (a i) b

/-- A finite value minus an infimum is the supremum of the differences:
`↑r − ⨅ i, x i = ⨆ i, (↑r − x i)`. -/
theorem coe_sub_iInf {ι : Sort*} (r : ℝ) (x : ι → EReal) :
    (r : EReal) - ⨅ i, x i = ⨆ i, ((r : EReal) - x i) := by
  rw [sub_eq_add_neg, neg_iInf, coe_add_iSup]
  simp only [sub_eq_add_neg]

/-- Regrouping a finite sum minus a paired sum, valid when neither subtrahend
is `⊥` (so the only `±∞` case is `⊤`, where both sides collapse to `⊥`):
`↑x + ↑y − (c + d) = (↑x − c) + (↑y − d)`. -/
theorem coe_add_coe_sub_add {x y : ℝ} {c d : EReal} (hc : c ≠ ⊥) (hd : d ≠ ⊥) :
    (x : EReal) + (y : EReal) - (c + d) = ((x : EReal) - c) + ((y : EReal) - d) := by
  rcases eq_or_ne c ⊤ with rfl | hc'
  · rw [EReal.top_add_of_ne_bot hd, EReal.sub_top, EReal.sub_top, EReal.bot_add]
  · rcases eq_or_ne d ⊤ with rfl | hd'
    · rw [EReal.add_top_of_ne_bot hc, EReal.sub_top, EReal.sub_top, EReal.add_bot]
    · obtain ⟨c', rfl⟩ : ∃ c' : ℝ, c = (c' : EReal) := ⟨c.toReal, (EReal.coe_toReal hc' hc).symm⟩
      obtain ⟨d', rfl⟩ : ∃ d' : ℝ, d = (d' : EReal) := ⟨d.toReal, (EReal.coe_toReal hd' hd).symm⟩
      have : x + y - (c' + d') = (x - c') + (y - d') := by ring
      exact_mod_cast this

end DeepWiki
