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

/-! ### The definitive obstruction — no finite set of boundary constants works -/

/-- A finite conjunction of `MtR` formulae. -/
def bigAndMtR {Act D : Type*} : List (MtR Act D) → MtR Act D
  | [] => .tt
  | F :: Fs => .and F (bigAndMtR Fs)

theorem denotMtR_bigAndMtR_map {Act D Proc α : Type*} (T : TLTS Proc Act)
    (L : List α) (g : α → MtR Act D) (ρ : Set (Proc × Valuation D)) :
    denotMtR T (bigAndMtR (L.map g)) ρ = {q | ∀ a ∈ L, q ∈ denotMtR T (g a) ρ} := by
  induction L with
  | nil => ext q; simp [bigAndMtR, denotMtR]
  | cons a as ih =>
    ext q
    simp only [List.map_cons, bigAndMtR, denotMtR, Set.mem_inter_iff, ih, Set.mem_setOf_eq,
      List.mem_cons, forall_eq_or_imp]

/-- The general boundary-forcing body: safety `∀∀X` plus a forcing `∃∃(x = c ∧ X)` for every constant
`c` in a finite set `S`. This is the entire design space of location-indexed bodies for a pure-delay
location — pure safety plus finitely many forceable boundaries. -/
def boundaryForcingBody (S : List ℕ) : MtR Empty Unit :=
  .and (.forallDelay .var)
    (bigAndMtR (S.map fun c => .existsDelay (.and (.guard (.atom () .eq c)) .var)))

/-- **No finite set of boundary constants admits the genuine unbounded state.** For any nonempty `S`,
the unbounded `(false, 0)` is excluded from `νX. ∀∀X ∧ ⋀_{c∈S} ∃∃(x=c ∧ X)`: take any `c₀ ∈ S`; `∀∀X`
forces the successor `(false, c₀+1)` (reachable since delays are unbounded), and there the conjunct
`∃∃(x=c₀)` is unsatisfiable because the formula clock is already `c₀+1` and only grows. So enriching
the body with more boundary-forcings never recovers the unbounded location — the region graph is
genuinely required. (Together with `naive_unbounded_not_separating` for `S = []`, this rules out the
whole family.) -/
theorem unbounded_fails_boundary_forcing_general (S : List ℕ) (hS : S ≠ []) :
    ((false, 0), (fun _ => 0 : Valuation Unit)) ∉ recMax ubTLTS (boundaryForcingBody S) := by
  obtain ⟨c₀, Fs, rfl⟩ : ∃ c₀ Fs, S = c₀ :: Fs := by
    cases S with
    | nil => exact absurd rfl hS
    | cons c₀ Fs => exact ⟨c₀, Fs, rfl⟩
  intro h
  rw [← denotMtR_recMax ubTLTS (boundaryForcingBody _)] at h
  simp only [boundaryForcingBody, denotMtR, Set.mem_inter_iff, Set.mem_setOf_eq] at h
  obtain ⟨hforall, _⟩ := h
  -- delay c₀ + 1 to (false, c₀ + 1), which ∀∀ keeps in the fixpoint
  have hmem2 := hforall ((c₀ : ℝ≥0) + 1) (false, 0 + ((c₀ : ℝ≥0) + 1)) (UbStep.delayF 0 _)
  rw [← denotMtR_recMax] at hmem2
  simp only [denotMtR, Set.mem_inter_iff, denotMtR_bigAndMtR_map,
    Set.mem_setOf_eq, satisfies, Cmp.holds, Valuation.add_apply] at hmem2
  -- the `c₀` conjunct: ∃∃(x = c₀) must hold at formula clock c₀ + 1 — impossible
  obtain ⟨_, hforce⟩ := hmem2
  obtain ⟨d, _, _, heq, _⟩ := hforce c₀ List.mem_cons_self
  -- heq : 0 + (↑c₀ + 1) + d = ↑c₀, impossible
  exact absurd heq (by
    intro heq'
    have hd : (0 : ℝ) ≤ (d : ℝ) := NNReal.coe_nonneg d
    rw [← NNReal.coe_inj] at heq'
    push_cast at heq'
    linarith)

/-- **The location-indexed framework cannot characterize an unbounded location.** Every body of the
natural design space — pure safety `∀∀X` optionally enriched with boundary-forcings `∃∃(x=c∧X)` for a
finite constant set `S` — fails: with no forcing (`S = []`) it is the whole space and admits the
non-bisimilar impostor `(true, 0)`; with any forcing (`S ≠ []`) it excludes the genuine `(false, 0)`.
This is precisely why Laroussinie–Larsen–Weise pass to the region graph (the route taken
unconditionally by the executable checker `decSatisfiesMtFull`). -/
theorem unbounded_no_location_indexed_characteristic (S : List ℕ) :
    (S = [] → ((false, 0), (fun _ => 0 : Valuation Unit)) ∈ recMax ubTLTS (boundaryForcingBody S) ∧
        ((true, 0), (fun _ => 0 : Valuation Unit)) ∈ recMax ubTLTS (boundaryForcingBody S) ∧
        ¬ TimedBisimilar ubTLTS (false, 0) (true, 0)) ∧
      (S ≠ [] → ((false, 0), (fun _ => 0 : Valuation Unit)) ∉ recMax ubTLTS (boundaryForcingBody S)) := by
  refine ⟨fun hS => ?_, unbounded_fails_boundary_forcing_general S⟩
  subst hS
  -- with S = [] the body is `∀∀X ∧ tt`, whose fixpoint is the whole space
  have hbody : boundaryForcingBody [] = MtR.and (MtR.forallDelay MtR.var) MtR.tt := rfl
  have heq : recMax ubTLTS (boundaryForcingBody []) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    rw [hbody]
    have huniv : (Set.univ : Set ((Bool × ℝ≥0) × Valuation Unit)) ⊆
        denotMtR ubTLTS (MtR.and (MtR.forallDelay MtR.var) MtR.tt) Set.univ := by
      intro q' _
      simp [denotMtR]
    exact (denotMtRHom ubTLTS (MtR.and (MtR.forallDelay MtR.var) MtR.tt)).le_gfp huniv
      (Set.mem_univ q)
  exact ⟨heq ▸ Set.mem_univ _, heq ▸ Set.mem_univ _, not_timedBisimilar_false_true⟩

end TLTS

end DeepWiki.ReactiveSystems
