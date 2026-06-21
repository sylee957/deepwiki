import DeepWiki.ReactiveSystems.TimedInvariantDelayForcing
import DeepWiki.ReactiveSystems.TimedHmlClocks

/-! # Why invariant-free (unbounded) locations need the region graph (an obstruction)
`TimedGeneralCharacteristic.fchar_iff` characterizes timed bisimilarity for general timed automata
*provided every location carries an invariant* (`hne : inv ℓ ≠ []`). This file shows the remaining
case — a location with **no** invariant, where delays are unbounded — genuinely cannot be handled in
the location-indexed framework, mirroring why Laroussinie–Larsen–Weise pass to the region graph.

Take a pure-delay automaton with an **unbounded** location (`false`, any delay) and one bounded by
`x ≤ 1` (`true`). The states `(false, 0)` and `(true, 0)` are **not** timed bisimilar (the first
delays `2`, the second only `1`). Two complementary failures pin the obstruction:

* **No-forcing is too weak.** The naive safety body `νX. ∀∀X` admits *both* states (it is the whole
  space), so it cannot separate them (`naive_unbounded_not_separating`).
* **Any single boundary-forcing is too strong.** The boundary-forcing `νX. ∀∀X ∧ ∃∃(x = c ∧ X)` that
  characterizes *bounded* locations excludes the genuine unbounded state `(false, 0)`: its `∀∀X`
  forces the successor `(false, c+1)` (reachable since delays are unbounded), which can never satisfy
  `∃∃(x = c ∧ X)` because the formula clock only grows past `c` (`unbounded_fails_boundary_forcing`).

So no location-indexed body works: there is no finite boundary constant for an unbounded location.
This is exactly the role of the region graph (the executable complete checker `decSatisfiesMtFull`
takes that route). -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

/-- A pure-delay two-location automaton: `false` is **unbounded** (any delay), `true` is bounded by
`x ≤ 1`. -/
inductive UbStep : (Bool × ℝ≥0) → (Empty ⊕ ℝ≥0) → (Bool × ℝ≥0) → Prop
  /-- The unbounded location delays by any amount. -/
  | delayF (w t : ℝ≥0) : UbStep (false, w) (Sum.inr t) (false, w + t)
  /-- The bounded location delays only while `x ≤ 1` at both endpoints. -/
  | delayT (w t : ℝ≥0) (h1 : w ≤ 1) (h2 : w + t ≤ 1) : UbStep (true, w) (Sum.inr t) (true, w + t)

/-- The automaton's TLTS. -/
def ubTLTS : TLTS (Bool × ℝ≥0) Empty := ⟨UbStep⟩

@[simp] theorem ub_delay {q q' : Bool × ℝ≥0} {d : ℝ≥0} :
    ubTLTS.delay q d q' ↔ UbStep q (Sum.inr d) q' := Iff.rfl

/-- `(false, 0)` and `(true, 0)` are **not** timed bisimilar: the unbounded location can delay `2`,
the bounded one cannot. -/
theorem not_timedBisimilar_false_true :
    ¬ TimedBisimilar ubTLTS (false, 0) (true, 0) := by
  intro hb
  obtain ⟨_, _, hdf, _⟩ := (timedBisimilar_iff ubTLTS (false, 0) (true, 0)).1 hb
  obtain ⟨q', hq', _⟩ := hdf 2 (false, 0 + 2) (UbStep.delayF 0 2)
  rw [ub_delay] at hq'
  cases hq' with
  | delayT _ _ _ h2 => exact absurd h2 (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)

/-! ### Failure 1 — no forcing is too weak -/

/-- The naive body for the unbounded location: pure delay-safety `∀∀X` (no forcing). -/
def ubNaiveBody : MtR Empty Unit := .forallDelay .var

/-- Its greatest fixed point. -/
def ubNaiveF : Set ((Bool × ℝ≥0) × Valuation Unit) := recMax ubTLTS ubNaiveBody

/-- The naive body is satisfied by the whole space (so it characterizes nothing). -/
theorem ubNaiveF_eq_univ : ubNaiveF = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  have huniv : (Set.univ : Set ((Bool × ℝ≥0) × Valuation Unit)) ⊆
      denotMtR ubTLTS ubNaiveBody Set.univ := by
    intro q' _
    simp only [ubNaiveBody, denotMtR, Set.mem_setOf_eq]
    intro d p' _
    exact Set.mem_univ _
  exact (denotMtRHom ubTLTS ubNaiveBody).le_gfp huniv (Set.mem_univ q)

/-- **The naive (no-forcing) body fails to separate the two non-bisimilar states**: both are in it,
yet they are not timed bisimilar. -/
theorem naive_unbounded_not_separating :
    ((false, 0), (fun _ => 0 : Valuation Unit)) ∈ ubNaiveF ∧
      ((true, 0), (fun _ => 0 : Valuation Unit)) ∈ ubNaiveF ∧
      ¬ TimedBisimilar ubTLTS (false, 0) (true, 0) :=
  ⟨ubNaiveF_eq_univ ▸ Set.mem_univ _, ubNaiveF_eq_univ ▸ Set.mem_univ _,
    not_timedBisimilar_false_true⟩

/-! ### Failure 2 — any single boundary-forcing is too strong -/

/-- The boundary-forcing body at constant `1` (the clause that *characterizes* bounded locations):
`∀∀X ∧ ∃∃(x = 1 ∧ X)`. -/
def ubForceBody : MtR Empty Unit :=
  .and (.forallDelay .var) (.existsDelay (.and (.guard (.atom () .eq 1)) .var))

/-- Its greatest fixed point. -/
def ubForceF : Set ((Bool × ℝ≥0) × Valuation Unit) := recMax ubTLTS ubForceBody

/-- **The boundary-forcing body excludes the genuine unbounded state `(false, 0)`**: `∀∀X` forces
the successor `(false, 2)` (reachable since the location is unbounded), which can never meet
`∃∃(x = 1)` — the formula clock at `(false, 2)` is already `2` and only grows. So no fixed boundary
constant works for an unbounded location. -/
theorem unbounded_fails_boundary_forcing :
    ((false, 0), (fun _ => 0 : Valuation Unit)) ∉ ubForceF := by
  intro h
  rw [ubForceF, ← denotMtR_recMax ubTLTS ubForceBody] at h
  simp only [ubForceBody, denotMtR, Set.mem_inter_iff, Set.mem_setOf_eq] at h
  obtain ⟨hforall, _⟩ := h
  have hmem2 := hforall 2 (false, 0 + 2) (UbStep.delayF 0 2)
  rw [← denotMtR_recMax] at hmem2
  simp only [denotMtR, Set.mem_inter_iff, Set.mem_setOf_eq, satisfies, Cmp.holds] at hmem2
  obtain ⟨_, d, _, _, heq, _⟩ := hmem2
  simp only [Valuation.add_apply] at heq
  -- heq : 0 + 2 + d = 1, impossible
  exact absurd heq (by
    intro heq'
    have hd : (0 : ℝ) ≤ (d : ℝ) := NNReal.coe_nonneg d
    rw [← NNReal.coe_inj] at heq'
    push_cast at heq'
    linarith)

end TLTS

end DeepWiki.ReactiveSystems
