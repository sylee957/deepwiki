import DeepWiki.ReactiveSystems.TimedInvariantObstruction

/-! # A delay-forcing clause fixes the invariant obstruction (positive result)
`TimedInvariantObstruction` showed the naive safety body `νX. (x ≤ c) ∧ ∀∀X` (`mtInv`) is *not*
characteristic: it fails to separate `(false, 0)` (invariant `x ≤ 2`) from `(true, 0)` (invariant
`x ≤ 1`), which are not timed bisimilar. The fix is a **delay-forcing** clause — a *forceable
delay-successor* — `∃∃(x = c ∧ X)`, which forces the candidate to be able to delay all the way to
the invariant boundary `x = c`. Together with the safety `∀∀X` and the convexity (prefix-closure)
of invariant-gated delays, this pins the delay capability exactly.

Here we verify it on the obstruction's automaton: the forcing body
`charInvF = νX. (x ≤ 2) ∧ ∀∀X ∧ ∃∃(x = 2 ∧ X)` **does** separate the two states —
`((false,0),0) ∈ charInvF` but `((true,0),0) ∉ charInvF` — because `(true,0)`, capped at `x ≤ 1`,
cannot delay to `x = 2`. This is the design behind the region-graph step of the full LLW
construction, demonstrated on the single-clock pure-delay case. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

/-- The forcing characteristic body for the `x ≤ 2` location: `(x ≤ 2) ∧ ∀∀X ∧ ∃∃(x = 2 ∧ X)`.
The last conjunct is the delay-forcing clause — it demands a delay all the way to the boundary
`x = 2`. -/
def charInvBody : MtR Empty Unit :=
  .and (.guard (.atom () .le 2))
    (.and (.forallDelay .var) (.existsDelay (.and (.guard (.atom () .eq 2)) .var)))

/-- The greatest fixed point of the forcing body. -/
def charInvF : Set ((Bool × ℝ≥0) × Valuation Unit) := recMax invTLTS charInvBody

/-- Candidate set for the fixpoint: `false`-location states whose formula clock tracks the
automaton clock and stays `≤ 2`. -/
def ForceR : Set ((Bool × ℝ≥0) × Valuation Unit) :=
  {x | x.1.1 = false ∧ x.2 () = x.1.2 ∧ x.1.2 ≤ (2 : ℝ≥0)}

/-- `ForceR` is a post-fixed point of the forcing body: the delay-forcing `∃∃(x = 2)` is met by
delaying `2 - w` to the boundary. -/
theorem ForceR_postfixed : ForceR ⊆ denotMtR invTLTS charInvBody ForceR := by
  rintro ⟨⟨b, w⟩, u⟩ hx
  simp only [ForceR, Set.mem_setOf_eq] at hx
  obtain ⟨hb, hu, hw⟩ := hx
  subst hb
  simp only [charInvBody, denotMtR, Set.mem_inter_iff, Set.mem_setOf_eq, satisfies, Cmp.holds]
  refine ⟨?_, ?_, ?_⟩
  · -- x ≤ 2
    rw [hu]; exact_mod_cast hw
  · -- ∀∀: every delay stays in ForceR
    rintro d p' hd
    rw [inv_delay] at hd
    cases hd with
    | delay _ _ _ _ h2 =>
      refine ⟨rfl, ?_, ?_⟩
      · simp only [Valuation.add_apply, hu]
      · exact le_trans h2 (bnd_le_two false)
  · -- ∃∃: delay 2 - w to the boundary x = 2
    refine ⟨2 - w, (false, w + (2 - w)), ?_, ?_, ?_⟩
    · -- the delay exists: w + (2 - w) ≤ bnd false = 2
      exact InvStep.delay false w (2 - w) hw (by simp [bnd, add_tsub_cancel_of_le hw])
    · -- formula clock reaches 2
      simp [Valuation.add_apply, hu, add_tsub_cancel_of_le hw]
    · -- the boundary state is in ForceR
      exact ⟨rfl, by simp [Valuation.add_apply, hu, add_tsub_cancel_of_le hw],
        by simp [add_tsub_cancel_of_le hw]⟩

/-- **`(false, 0)` satisfies the forcing body** (it can delay to `x = 2`). -/
theorem mem_charInvF_false : ((false, 0), fun _ => 0) ∈ charInvF :=
  (denotMtRHom invTLTS charInvBody).le_gfp ForceR_postfixed ⟨rfl, rfl, by norm_num⟩

/-- **`(true, 0)` does NOT satisfy the forcing body**: capped at `x ≤ 1`, it cannot delay to the
boundary `x = 2`, so the delay-forcing `∃∃(x = 2)` fails. -/
theorem not_mem_charInvF_true : ((true, 0), fun _ => 0) ∉ charInvF := by
  intro h
  rw [charInvF, ← denotMtR_recMax invTLTS charInvBody] at h
  simp only [charInvBody, denotMtR, Set.mem_inter_iff, Set.mem_setOf_eq, satisfies, Cmp.holds] at h
  obtain ⟨_, _, s, p', hd, heq, _⟩ := h
  rw [inv_delay] at hd
  cases hd with
  | delay _ _ _ _ h2 =>
    -- the forcing clock equation forces s = 2, but the invariant gives 0 + s ≤ 1
    simp only [Valuation.add_apply] at heq
    rw [heq] at h2
    -- h2 : 0 + 2 ≤ bnd true = 1, impossible
    exact absurd h2 (by rw [bnd]; rw [← NNReal.coe_le_coe]; push_cast; norm_num)

/-- **The delay-forcing body separates the obstruction's two states** (contrast
`naive_invariant_not_characteristic`, where the naive safety body satisfies both): adding the
forceable delay-successor `∃∃(x = 2)` is exactly what distinguishes the non-bisimilar `(false,0)`
and `(true,0)`. -/
theorem charInvF_separates :
    ((false, 0), fun _ => 0) ∈ charInvF ∧ ((true, 0), fun _ => 0) ∉ charInvF :=
  ⟨mem_charInvF_false, not_mem_charInvF_true⟩

end TLTS

end DeepWiki.ReactiveSystems
