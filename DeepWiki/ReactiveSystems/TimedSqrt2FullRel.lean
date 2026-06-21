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

/-- `crossVal d 0 = √2 − d`. -/
@[simp] theorem crossVal_zero (d : ℝ≥0) : crossVal d 0 = sqrt2NN - d := by
  simp [crossVal]

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
