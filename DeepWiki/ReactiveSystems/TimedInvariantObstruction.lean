import DeepWiki.ReactiveSystems.TimedHmlRecursion

/-! # Why location invariants need more than safety (an obstruction)
The location-indexed characteristic construction (`TimedGeneralGuardCharacteristic` and its
predecessors) handles nondeterministic multi-clock multi-action general-guard timed automata —
but *without* location invariants. The natural fix, adding `guard(inv ℓ) ∧ ∀∀X_ℓ` to the body,
is **pure safety** and is *not* characteristic: it cannot force a candidate to delay as far as
the invariant permits, because the formula clocks track the canonical state's clocks while the
candidate's delay capability is gated by the candidate's *own* invariant.

This file makes that precise. Take two pure-delay locations with upper-bound invariants `x ≤ 2`
(`false`) and `x ≤ 1` (`true`). The states `(false, 0)` and `(true, 0)` are **not** timed
bisimilar (the first can delay `2`, the second only `1`), yet *both* satisfy the naive invariant
formula `νX. (x ≤ 2) ∧ ∀∀X` — the library's `mtInv (x ≤ 2)`, which is exactly the safety body for
the `false`-location with no edges. So the naive body fails to characterise timed bisimilarity:
invariants genuinely require a *delay-forcing* clause (in the LLW construction, supplied by the
region graph, which discretises the continuum of delays into forceable successor steps). -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

/-- The two locations' invariant bounds: `x ≤ 2` for `false`, `x ≤ 1` for `true`. -/
def bnd : Bool → ℝ≥0
  | false => 2
  | true => 1

theorem bnd_le_two (b : Bool) : bnd b ≤ 2 := by cases b <;> simp [bnd]

/-- A pure-delay two-location automaton with upper-bound invariants: `(b, w)` may delay `t`
exactly while `w` and `w + t` stay within `bnd b` (no actions). -/
inductive InvStep : (Bool × ℝ≥0) → (Empty ⊕ ℝ≥0) → (Bool × ℝ≥0) → Prop
  /-- Delay `t`, gated by the location invariant at both endpoints. -/
  | delay (b : Bool) (w t : ℝ≥0) (h1 : w ≤ bnd b) (h2 : w + t ≤ bnd b) :
      InvStep (b, w) (Sum.inr t) (b, w + t)

/-- The invariant automaton's TLTS. -/
def invTLTS : TLTS (Bool × ℝ≥0) Empty := ⟨InvStep⟩

@[simp] theorem inv_delay {q q' : Bool × ℝ≥0} {d : ℝ≥0} :
    invTLTS.delay q d q' ↔ InvStep q (Sum.inr d) q' := Iff.rfl

/-- The naive invariant formula for the `false`-location: `x ≤ 2`. -/
def naiveInvFormula : Mt Empty Unit := .guard (.atom () .le 2)

/-- The candidate set for the greatest fixed point: extended states whose formula clock tracks
the automaton clock and stays `≤ 2`. -/
def InvR : Set ((Bool × ℝ≥0) × Valuation Unit) :=
  {x | x.2 () = x.1.2 ∧ x.1.2 ≤ (2 : ℝ≥0)}

/-- `InvR` is a post-fixed point of the naive invariant body (safety only). -/
theorem InvR_postfixed :
    InvR ⊆ denotMtR invTLTS (mtInvBody naiveInvFormula) InvR := by
  rintro ⟨⟨b, w⟩, u⟩ hx
  simp only [InvR, Set.mem_setOf_eq] at hx
  obtain ⟨hu, hw⟩ := hx
  simp only [mtInvBody, naiveInvFormula, denotMtR, Set.mem_inter_iff, Set.mem_setOf_eq,
    mem_denotMtR_toMtR]
  refine ⟨?_, ?_, ?_⟩
  · -- the invariant holds now: u(y) = w ≤ 2
    simp only [MtSat, satisfies, Cmp.holds]
    rw [hu]; exact_mod_cast hw
  · -- no actions, vacuously
    exact fun a => a.elim
  · -- every (invariant-gated) delay stays in InvR
    rintro d p' hd
    rw [inv_delay] at hd
    cases hd with
    | delay _ _ _ _ h2 =>
      refine ⟨?_, ?_⟩
      · simp only [Valuation.add_apply, hu]
      · exact le_trans h2 (bnd_le_two b)

/-- Both `(false, 0)` and `(true, 0)` satisfy the naive invariant formula at formula clock `0`
— it is `mtInv invTLTS (x ≤ 2)`. -/
theorem InvR_subset_mtInv : InvR ⊆ mtInv invTLTS naiveInvFormula :=
  (denotMtRHom invTLTS (mtInvBody naiveInvFormula)).le_gfp InvR_postfixed

/-- `(false, 0)` and `(true, 0)` are **not** timed bisimilar: `(false, 0)` can delay `2`,
`(true, 0)` cannot (its invariant `x ≤ 1` blocks it). -/
theorem not_timedBisimilar_inv :
    ¬ TimedBisimilar invTLTS (false, 0) (true, 0) := by
  intro h
  obtain ⟨_, _, hdf, _⟩ := (timedBisimilar_iff invTLTS (false, 0) (true, 0)).1 h
  obtain ⟨q', hq', _⟩ := hdf 2 (false, 0 + 2)
    (InvStep.delay false 0 2 (by simp [bnd])
      (by simp only [bnd]; rw [← NNReal.coe_le_coe]; push_cast; norm_num))
  rw [inv_delay] at hq'
  cases hq' with
  | delay _ _ _ _ h2 =>
    exact absurd h2 (by simp only [bnd]; rw [← NNReal.coe_le_coe]; push_cast; norm_num)

/-- **The obstruction.** The naive invariant body `νX. (x ≤ 2) ∧ ∀∀X` (`mtInv (x ≤ 2)`, i.e. the
safety body for an edge-free location with invariant `x ≤ 2`) does **not** characterise timed
bisimilarity: `(false, 0)` and `(true, 0)` both satisfy it yet are not timed bisimilar. Hence
location invariants need a delay-forcing clause beyond the safety `∀∀` — the region-graph step of
the full Laroussinie–Larsen–Weise construction. -/
theorem naive_invariant_not_characteristic :
    (((false, 0), fun _ => 0) ∈ mtInv invTLTS naiveInvFormula) ∧
    (((true, 0), fun _ => 0) ∈ mtInv invTLTS naiveInvFormula) ∧
    ¬ TimedBisimilar invTLTS (false, 0) (true, 0) :=
  ⟨InvR_subset_mtInv ⟨rfl, by norm_num⟩,
   InvR_subset_mtInv ⟨rfl, by norm_num⟩,
   not_timedBisimilar_inv⟩

end TLTS

end DeepWiki.ReactiveSystems
