import DeepWiki.ReactiveSystems.TimedSqrt2AsymRegion

/-! # The `√2` Mt-bisimulation, step 4c: the augmented relation and its non-delay clauses (Ex 12.12(3))
Assembles the asymmetric single-irrational-cut relation from the foundations. The live regime carries,
besides the formula-clock region equivalence and the `√2`-side, the **asymmetric crossing-value match**
`AsymMatch` on each clock's delay-invariant crossing-value `crossVal d v = v + (√2 − d)` (its value when
the process reaches `√2`) and on the process's own `crossVal d 0 = √2 − d`.

`AsymMatch c c' := ∀ m, (m < c ↔ m ≤ c')` is exactly "A (open threshold) and B (closed) agree on
a-availability at every integer clock value `m`" (`a_avail_iff_lt_crossing`); it forces `⌊c'⌋ = ⌊c⌋`
when `c ∉ ℤ` and `⌊c'⌋ = m−1` when `c = m` — B's crossing-value just below, placing B strictly past `√2`
at the double-coincidence.

This file proves the **reset, guard, action, and seed** clauses. The reset clause is the crux of the
design: resetting a clock sets its crossing-value to `√2 − d`, and the relation's separately-tracked
*process* match `AsymMatch (√2−d) (√2−e)` is exactly what re-supplies the crossing-value match — so the
match is preserved with no delay reasoning. The delay clause (standard time-successor + `√2`-side
window, the crossing-values auto-carried) is the remaining step. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- The crossing-value of a clock with value `v` at process `d`: its value when the process reaches
`√2` (delay-invariant, `clock_at_sqrt2_delay_invariant`). -/
noncomputable def crossVal (d v : ℝ≥0) : ℝ≥0 := v + (sqrt2NN - d)

/-- The asymmetric crossing-value match: A (open threshold `< √2`) and B (closed `≤ √2`) agree on
a-availability at every integer clock value `m`. Forces `⌊c'⌋ = ⌊c⌋` for `c ∉ ℤ`, and `⌊c'⌋ = m − 1`
for `c = m` (B's value just below). -/
def AsymMatch (c c' : ℝ≥0) : Prop := ∀ m : ℕ, ((m : ℝ≥0) < c ↔ (m : ℝ≥0) ≤ c')

/-- An integer cast never equals `√2`. -/
theorem natCast_ne_sqrt2NN (m : ℕ) : (m : ℝ≥0) ≠ sqrt2NN := by
  intro h
  exact irrational_sqrt2NN.ne_nat m (by rw [← h]; push_cast; ring)

/-- `AsymMatch √2 √2` holds (since `√2` is never an integer). -/
theorem asymMatch_sqrt2_self : AsymMatch sqrt2NN sqrt2NN := fun m =>
  ⟨le_of_lt, fun h => lt_of_le_of_ne h (natCast_ne_sqrt2NN m)⟩

/-- **The floor content of `AsymMatch`** (the heart of the straddle): B's crossing-value floor is at
most A's. Since `AsymMatch c c'` forces `⌊c'⌋ = ⌊c⌋` (for `c ∉ ℤ`) or `⌊c'⌋ = ⌊c⌋ − 1` (for `c ∈ ℤ`),
in both cases `⌊c'⌋ ≤ ⌊c⌋` — so wherever A's process reaches `√2` before a clock's next integer (a
crossing-value below that integer), B's does too. This is what makes the clocks-region window straddle
`√2` consistently between A and B. -/
theorem AsymMatch.floor_le {c c' : ℝ≥0} (h : AsymMatch c c') : ⌊c'⌋₊ ≤ ⌊c⌋₊ := by
  have h1 : ((⌊c'⌋₊ : ℕ) : ℝ≥0) ≤ c' := Nat.floor_le zero_le
  have h2 : ((⌊c'⌋₊ : ℕ) : ℝ≥0) < c := (h ⌊c'⌋₊).mpr h1
  exact Nat.le_floor (le_of_lt h2)

/-- **The process τ-match collapses to a single threshold in the live regime.** Because `√2 − e ≥ 0`
always (truncated subtraction) the `m = 0` clause is vacuous, and because `√2 − d < 2` the `m ≥ 2`
clauses are vacuous; so `AsymMatch (√2−d) (√2−e)` is just the `m = 1` condition — the `√2−1` cut
`d + 1 < √2 ↔ e + 1 ≤ √2`. -/
theorem asymMatch_tau_live {d e : ℝ≥0} (hd : d < sqrt2NN) (he : e ≤ sqrt2NN) :
    AsymMatch (sqrt2NN - d) (sqrt2NN - e) ↔ (d + 1 < sqrt2NN ↔ e + 1 ≤ sqrt2NN) := by
  have e1 : ((1 : ℝ≥0) < sqrt2NN - d) ↔ (d + 1 < sqrt2NN) := by
    rw [← NNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_sub (le_of_lt hd), NNReal.coe_add]
    push_cast; constructor <;> intro <;> linarith
  have e2 : ((1 : ℝ≥0) ≤ sqrt2NN - e) ↔ (e + 1 ≤ sqrt2NN) := by
    rw [← NNReal.coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_sub he, NNReal.coe_add]
    push_cast; constructor <;> intro <;> linarith
  constructor
  · intro h
    have h1 := h 1; rw [Nat.cast_one, e1, e2] at h1; exact h1
  · intro h m
    match m with
    | 0 => rw [Nat.cast_zero]; exact ⟨fun _ => zero_le, fun _ => tsub_pos_of_lt hd⟩
    | 1 => rw [Nat.cast_one, e1, e2]; exact h
    | (n + 2) =>
      have hslt : sqrt2NN < ((n + 2 : ℕ) : ℝ≥0) := by
        rw [← NNReal.coe_lt_coe]; push_cast
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith [sqrt2NN_lt_two]
      exact iff_of_false
        (not_lt.mpr (le_of_lt (lt_of_le_of_lt tsub_le_self hslt)))
        (not_le.mpr (lt_of_le_of_lt tsub_le_self hslt))

/-- `crossVal d 0 = √2 − d`. -/
@[simp] theorem crossVal_zero (d : ℝ≥0) : crossVal d 0 = sqrt2NN - d := by
  simp [crossVal]

/-- **Process past `√2` ⟺ clock past its crossing-value.** For any clock value `v`, the process (at
`d ≤ √2`) is past `√2` after a delay `δ` exactly when `v`'s post-delay value `v + δ` is past its
crossing-value `crossVal d v`. This reduces the (process-level) `√2`-side condition to a clock-level
comparison, which the clocks-region match and the crossing-value match control. -/
theorem process_past_iff_clock_past_cross {d δ : ℝ≥0} (v : ℝ≥0) (hd : d ≤ sqrt2NN) :
    sqrt2NN < d + δ ↔ crossVal d v < v + δ := by
  rw [crossVal, add_lt_add_iff_left, ← NNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_sub hd,
    NNReal.coe_add]
  constructor <;> intro <;> linarith

/-- Dually, the process is at-or-below `√2` (`B`'s closed side) iff `v + δ ≤ crossVal d v`. -/
theorem process_le_iff_clock_le_cross {d δ : ℝ≥0} (v : ℝ≥0) (hd : d ≤ sqrt2NN) :
    d + δ ≤ sqrt2NN ↔ v + δ ≤ crossVal d v := by
  rw [crossVal, add_le_add_iff_left, ← NNReal.coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_sub hd,
    NNReal.coe_add]
  constructor <;> intro <;> linarith

/-- The **crossing-value valuation** (clock crossings only): `y ↦ u y + (√2 − d)`, the value clock `y`
holds when the process reaches `√2`. This is the delay-invariant object; the process's own τ = `√2 − d`
is *not* invariant and is tracked separately. -/
noncomputable def cv {D : Type*} (d : ℝ≥0) (u : Valuation D) : Valuation D := fun y => u y + (sqrt2NN - d)

@[simp] theorem cv_apply {D : Type*} (d : ℝ≥0) (u : Valuation D) (y : D) :
    cv d u y = u y + (sqrt2NN - d) := rfl

/-- **The crossing-value valuation is delay-invariant** (for live delays `d + δ ≤ √2`): advancing the
process and all clocks together leaves every clock's `√2`-crossing value unchanged. This is what makes
the crossing-value region match auto-preserved under delay — the structural key to the construction. -/
theorem cv_delay_invariant {D : Type*} {d δ : ℝ≥0} {u : Valuation D} (h : d + δ ≤ sqrt2NN) :
    cv (d + δ) (u.add δ) = cv d u := by
  funext y
  simp only [cv_apply, Valuation.add_apply]
  exact TLTS.clock_at_sqrt2_delay_invariant h

namespace TLTS

/-- The live regime's coupling: formula-clock region equivalence, the `√2`-side (open/closed), the
process crossing-value match, and the per-clock crossing-value match. -/
def Sq2FRel {D : Type*} (d : ℝ≥0) (u : Valuation D) (e : ℝ≥0) (u' : Valuation D) : Prop :=
  RegionEqAll u u' ∧ d < sqrt2NN ∧ e ≤ sqrt2NN
    ∧ AsymMatch (crossVal d 0) (crossVal e 0)
    ∧ ∀ y, AsymMatch (crossVal d (u y)) (crossVal e (u' y))

/-- The augmented `√2` relation: past regime (both `a`-disabled, formula clocks region-equivalent) or
live regime `(A d) ~ (B e)` with the `Sq2FRel` coupling. -/
def Sq2FullRel {D : Type*} (p : Sq2) (u : Valuation D) (q : Sq2) (u' : Valuation D) : Prop :=
  (aDisabled sqrt2NN p ∧ aDisabled sqrt2NN q ∧ RegionEqAll u u')
  ∨ (∃ d e : ℝ≥0, p = Sq2.A d ∧ q = Sq2.B e ∧ Sq2FRel d u e u')

/-- Both regimes give region-equivalent formula clocks. -/
theorem Sq2FullRel.regionEqAll {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2FullRel p u q u') : RegionEqAll u u' := by
  rcases h with ⟨_, _, hr⟩ | ⟨_, _, _, _, hr, _⟩ <;> exact hr

/-- **Guard clause.** -/
theorem Sq2FullRel.guard {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2FullRel p u q u') (g : ClockConstraint D) : satisfies u g ↔ satisfies u' g :=
  regionEqAll_satisfies h.regionEqAll g

/-- **Reset clause.** Resetting clock `x` preserves the relation: the reset clock's crossing-value
becomes `√2 − d`, supplied by the process match; the others are unchanged. -/
theorem Sq2FullRel.reset {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2FullRel p u q u') (x : D) :
    Sq2FullRel p (Valuation.reset {x} u) q (Valuation.reset {x} u') := by
  rcases h with ⟨hpd, hqd, hr⟩ | ⟨d, e, hp, hq, hr, hd, he, hτ, hcross⟩
  · exact Or.inl ⟨hpd, hqd, hr.reset {x}⟩
  · refine Or.inr ⟨d, e, hp, hq, hr.reset {x}, hd, he, hτ, fun y => ?_⟩
    by_cases hxy : y = x
    · subst hxy
      have hu : Valuation.reset {y} u y = 0 := Valuation.reset_mem (Set.mem_singleton y) u
      have hu' : Valuation.reset {y} u' y = 0 := Valuation.reset_mem (Set.mem_singleton y) u'
      rw [hu, hu']; exact hτ
    · have hu : Valuation.reset {x} u y = u y := by
        simp [Valuation.reset, Set.mem_singleton_iff, hxy]
      have hu' : Valuation.reset {x} u' y = u' y := by
        simp [Valuation.reset, Set.mem_singleton_iff, hxy]
      rw [hu, hu']; exact hcross y

/-- **Action clause (forth).** -/
theorem Sq2FullRel.act_forth {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2FullRel p u q u') (α : Sq2Act) (p' : Sq2)
    (hstep : (sq2TLTS sqrt2NN).act p α p') :
    ∃ q', (sq2TLTS sqrt2NN).act q α q' ∧ Sq2FullRel p' u q' u' := by
  rw [sq2_act] at hstep
  rcases h with ⟨hpd, _, _⟩ | ⟨d, e, hp, hq, hr, hd, he, _, _⟩
  · exact absurd hstep (fun hs => hpd.no_act hs)
  · subst hp; subst hq
    cases hstep with
    | aA _ => exact ⟨Sq2.End, sq2_act.mpr (Sq2Step.aB he), Or.inl ⟨trivial, trivial, hr⟩⟩

/-- **Action clause (back).** -/
theorem Sq2FullRel.act_back {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2FullRel p u q u') (α : Sq2Act) (q' : Sq2)
    (hstep : (sq2TLTS sqrt2NN).act q α q') :
    ∃ p', (sq2TLTS sqrt2NN).act p α p' ∧ Sq2FullRel p' u q' u' := by
  rw [sq2_act] at hstep
  rcases h with ⟨_, hqd, _⟩ | ⟨d, e, hp, hq, hr, hd, he, _, _⟩
  · exact absurd hstep (fun hs => hqd.no_act hs)
  · subst hp; subst hq
    cases hstep with
    | aB _ => exact ⟨Sq2.End, sq2_act.mpr (Sq2Step.aA hd), Or.inl ⟨trivial, trivial, hr⟩⟩

/-- **Delay clause, past regime.** Both `a`-disabled: the formula-clock region time-successor matches a
left delay by a right delay, landing again `a`-disabled and region-equivalent. -/
theorem Sq2FullRel.delay_past {D : Type*} [Fintype D] {p q : Sq2} {u u' : Valuation D}
    (hpd : aDisabled sqrt2NN p) (hqd : aDisabled sqrt2NN q) (hr : RegionEqAll u u')
    (d : ℝ≥0) (p' : Sq2) (hstep : (sq2TLTS sqrt2NN).delay p d p') :
    ∃ d' q', (sq2TLTS sqrt2NN).delay q d' q' ∧ Sq2FullRel p' (u.add d) q' (u'.add d') := by
  rw [sq2_delay] at hstep
  obtain ⟨d', hr'⟩ := regionEqAll_timeSuccessor hr d
  obtain ⟨q', hqstep, hq'd⟩ := hqd.delay_succ d'
  exact ⟨d', q', sq2_delay.mpr hqstep, Or.inl ⟨hpd.delay_pres hstep, hq'd, hr'⟩⟩

/-- The per-clock crossing-values are **auto-carried** under a live delay (`d + δ ≤ √2`): the
crossing-value match needs no re-establishment, only the process τ-match and the clocks region do
(`clock_at_sqrt2_delay_invariant`). -/
theorem crossVal_live_invariant {d δ v : ℝ≥0} (h : d + δ ≤ sqrt2NN) :
    crossVal (d + δ) (v + δ) = crossVal d v :=
  clock_at_sqrt2_delay_invariant h

/-- The seed: `(A 0) ~ (B 0)` at the all-zero formula valuation. -/
theorem sq2FullRel_seed {D : Type*} :
    Sq2FullRel (Sq2.A 0) (fun _ : D => 0) (Sq2.B 0) (fun _ : D => 0) := by
  refine Or.inr ⟨0, 0, rfl, rfl, RegionEqAll.refl _, zero_lt_sqrt2NN, le_of_lt zero_lt_sqrt2NN, ?_, ?_⟩
  · simp only [crossVal_zero, tsub_zero]; exact asymMatch_sqrt2_self
  · intro _; simp only [crossVal, tsub_zero, zero_add]; exact asymMatch_sqrt2_self

end TLTS

end DeepWiki.ReactiveSystems
