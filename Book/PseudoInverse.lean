import Book.RealCurvesConv

/-! # Pseudo-inverse
The (lower) pseudo-inverse of a non-negative non-decreasing curve
`f : ℝ≥0 → ℝ≥0∞`, `f⁻¹(x) = inf {t | f t ≥ x}` (Definition 3.3). The
infimum is taken in `ℝ≥0∞`, so "no admissible `t`" yields `⊤`. Core
API: value at `0`, the admissibility/Galois bounds, monotonicity, and
the worked first-crossing example on `delay`. -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge
open Set Topology Filter

/-- The admissible-time set `{t | x ≤ f t}` of the pseudo-inverse, in `ℝ≥0∞`. -/
def pseudoInvSet (f : ℝ≥0 → ℝ≥0∞) (x : ℝ≥0∞) : Set ℝ≥0∞ :=
  ENNReal.ofNNReal '' {t : ℝ≥0 | x ≤ f t}

/-- Lower pseudo-inverse `f⁻¹(x) = inf {t | f t ≥ x}` (in `ℝ≥0∞`). -/
noncomputable def pseudoInv (f : ℝ≥0 → ℝ≥0∞) : ℝ≥0∞ → ℝ≥0∞ :=
  fun x => sInf (pseudoInvSet f x)

/-- `(t : ℝ≥0∞) ∈ pseudoInvSet f x` iff `x ≤ f t`. -/
theorem mem_pseudoInvSet {f : ℝ≥0 → ℝ≥0∞} {x : ℝ≥0∞} {t : ℝ≥0} :
    (t : ℝ≥0∞) ∈ pseudoInvSet f x ↔ x ≤ f t := by
  unfold pseudoInvSet
  rw [Set.mem_image]
  constructor
  · rintro ⟨s, hs, hst⟩
    rwa [ENNReal.coe_inj.mp hst] at hs
  · intro h; exact ⟨t, h, rfl⟩

/-- Admissibility: if `x ≤ f t` then `f⁻¹ x ≤ t`. -/
theorem pseudoInv_le_of_le {f : ℝ≥0 → ℝ≥0∞} {x : ℝ≥0∞} {t : ℝ≥0}
    (h : x ≤ f t) : pseudoInv f x ≤ t :=
  sInf_le (mem_pseudoInvSet.mpr h)

/-- `d ≤ f⁻¹ x` when no time `≤ d` is admissible (`d` lower-bounds the set). -/
theorem le_pseudoInv {f : ℝ≥0 → ℝ≥0∞} {x : ℝ≥0∞} {d : ℝ≥0∞}
    (h : ∀ t : ℝ≥0, x ≤ f t → d ≤ t) : d ≤ pseudoInv f x := by
  refine le_sInf ?_
  rintro z ⟨t, ht, rfl⟩
  exact_mod_cast h t ht

/-- The pseudo-inverse is monotone in `x` (antitone admissible sets). -/
theorem pseudoInv_mono (f : ℝ≥0 → ℝ≥0∞) : Monotone (pseudoInv f) := by
  intro x y hxy
  refine sInf_le_sInf ?_
  rintro z ⟨t, ht, rfl⟩
  exact ⟨t, le_trans hxy ht, rfl⟩

/-- `f⁻¹ 0 = 0` (`0` is admissible for every `t`, in particular `t = 0`). -/
theorem pseudoInv_zero (f : ℝ≥0 → ℝ≥0∞) : pseudoInv f 0 = 0 :=
  le_antisymm (pseudoInv_le_of_le (t := 0) bot_le) bot_le

/-! ## Worked example (Definition 3.3)

The book illustrates Definition 3.3 with a curve `f` that is flat then
jumps, so that `f⁻¹(x)` is the *first crossing time* `inf {t | f t ≥ x}`:
a value already attained by a flat segment is inverted to the left edge of
that segment, while the right limit can be strictly larger. The book's `f`
is given only graphically; the `delay d` curve is the exact codebase analog
with the same flat-then-jump shape (`0` on `[0, d]`, then `⊤`), and exhibits
the identical first-crossing behaviour: every positive level is first reached
just after `d`, so `(delay d)⁻¹ x = d` for `x > 0`, while `(delay d)⁻¹ 0 = 0`.
-/

/-- For `0 < x`, `x ≤ delay d t` holds exactly when `d < t`. -/
theorem le_delay_iff {d : ℝ≥0} {x : ℝ≥0∞} (hx : 0 < x) (t : ℝ≥0) :
    x ≤ delay d t ↔ d < t := by
  unfold delay
  rcases le_or_gt t d with ht | ht
  · simp only [if_pos ht]
    exact ⟨fun h => absurd (le_antisymm (h.trans bot_le) bot_le)
      hx.ne', fun h => absurd ht (not_le.mpr h)⟩
  · simp only [if_neg (not_le.mpr ht)]
    exact ⟨fun _ => ht, fun _ => le_top⟩

/-- First-crossing: `(delay d)⁻¹ x = d` for `0 < x` (the level is first
reached just past `d`, mirroring the book's `f⁻¹(2) = 2`). -/
theorem pseudoInv_delay_pos (d : ℝ≥0) {x : ℝ≥0∞} (hx : 0 < x) :
    pseudoInv (delay d) x = d := by
  apply le_antisymm
  · -- `d` is approached from above: every `d < t` is admissible.
    refine ENNReal.le_of_forall_pos_le_add ?_
    intro ε hε _
    have hadm : x ≤ delay d (d + ε) :=
      (le_delay_iff hx (d + ε)).mpr (by
        simpa using (lt_add_iff_pos_right (d : ℝ≥0)).mpr hε)
    refine le_trans (pseudoInv_le_of_le hadm) ?_
    rw [ENNReal.coe_add]
  · -- `d` lower-bounds the admissible set (`d < t ⇒ d ≤ t`).
    exact le_pseudoInv (fun t ht =>
      le_of_lt (by exact_mod_cast (le_delay_iff hx t).mp ht))

/-- `(delay d)⁻¹ 0 = 0`. -/
theorem pseudoInv_delay_zero (d : ℝ≥0) : pseudoInv (delay d) 0 = 0 :=
  pseudoInv_zero (delay d)

end DeepWiki
