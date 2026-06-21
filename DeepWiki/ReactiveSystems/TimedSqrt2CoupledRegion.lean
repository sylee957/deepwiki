import DeepWiki.ReactiveSystems.TimedSqrt2FullRel

/-! # The `√2` Mt-bisimulation, step 5: the coupled relation via a `jointValW` process-bump (Ex 12.12(3))

`Sq2FullRel` proved five of six clauses but its live regime was insufficient (it tracked the
process-to-clock coupling only at the integer level). The fix is the **single-irrational-cut region**,
and the clean realization is a `jointValW` valuation with the process value bumped *up* by an
infinitesimal `η`:

`Sq2CoupledFRel d u e u' := d < √2 ∧ e ≤ √2 ∧ ∃ η₀ > 0, ∀ η ∈ (0, η₀), RegionEqAll (jointValW (d+η) u) (jointValW e u')`.

**Why this works (the successor breakthrough).** The earlier `combShift` form (a `D ⊕ Option D`
valuation with the crossing-values `cv` shifted *down* by `η`) made the live-delay a *non-uniform*
shear (clocks up, crossings fixed) — seemingly needing a 600-line region successor. But shifting `cv`
down by `η` is the same as shifting the process clock `p` up by `η` (`cv = u + 2 − p`), and bumping the
process *value* by `η` is exactly `jointValW (d+η) u` (it bumps `none`, leaving the clocks). Since
`jointValW` advances **uniformly** under delay (`jointValW_add`), the η-bump *commutes* with the
advance — so the live-delay is just the **existing** `jointValW_delay_match` (the irrational cut rides
inside `none`'s integer region). `jointValW`'s region already *determines* the crossing-orderings (via
the clock–process orderings), so the explicit crossings were redundant. The clauses are then clean:
delay = `jointValW_delay_match`, reset = `jointValW_reset_some`, guard = `jointValW_comp_some`. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

namespace TLTS

/-- The **coupled live relation**: A's process bumped up by an infinitesimal `η` matches B's, in the
augmented `jointValW` region (the single-irrational-cut region). The `∀ small η` makes the bump
robustly infinitesimal (B's process is infinitesimally ahead — the open A / closed B asymmetry). -/
def Sq2CoupledFRel {D : Type*} (d : ℝ≥0) (u : Valuation D) (e : ℝ≥0) (u' : Valuation D) : Prop :=
  d < sqrt2NN ∧ e ≤ sqrt2NN ∧
    ∃ η₀ : ℝ≥0, 0 < η₀ ∧ ∀ η : ℝ≥0, 0 < η → η < η₀ →
      RegionEqAll (jointValW (d + η) u) (jointValW e u')

/-- The coupled `√2` relation: past regime (both `a`-disabled, clocks region-equivalent) or the
coupled live regime. -/
def Sq2CoupledRel {D : Type*} (p : Sq2) (u : Valuation D) (q : Sq2) (u' : Valuation D) : Prop :=
  (aDisabled sqrt2NN p ∧ aDisabled sqrt2NN q ∧ RegionEqAll u u')
  ∨ (∃ d e : ℝ≥0, p = Sq2.A d ∧ q = Sq2.B e ∧ Sq2CoupledFRel d u e u')

/-- The clock region (for the guard clause): restricting the augmented region to the formula clocks. -/
theorem Sq2CoupledFRel.regionEqAll {D : Type*} {d e : ℝ≥0} {u u' : Valuation D}
    (h : Sq2CoupledFRel d u e u') : RegionEqAll u u' := by
  obtain ⟨_, _, η₀, hη₀, hreg⟩ := h
  have hp := RegionEqAll.precomp (f := Option.some) (Option.some_injective D)
    (hreg (η₀ / 2) (half_pos hη₀) (NNReal.half_lt_self hη₀.ne'))
  rwa [jointValW_comp_some, jointValW_comp_some] at hp

/-- Both regimes give region-equivalent formula clocks. -/
theorem Sq2CoupledRel.regionEqAll {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2CoupledRel p u q u') : RegionEqAll u u' := by
  rcases h with ⟨_, _, hr⟩ | ⟨_, _, _, _, hfr⟩
  · exact hr
  · exact hfr.regionEqAll

/-- **Guard clause** for the coupled relation. -/
theorem Sq2CoupledRel.guard {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2CoupledRel p u q u') (g : ClockConstraint D) : satisfies u g ↔ satisfies u' g :=
  regionEqAll_satisfies h.regionEqAll g

/-- **Reset clause** (live regime): resetting a formula clock leaves the augmented process clock
untouched (`jointValW_reset_some`), so the bumped region equivalence is preserved. -/
theorem Sq2CoupledFRel.reset {D : Type*} [DecidableEq D] {d e : ℝ≥0} {u u' : Valuation D}
    (h : Sq2CoupledFRel d u e u') (x : D) :
    Sq2CoupledFRel d (Valuation.reset {x} u) e (Valuation.reset {x} u') := by
  obtain ⟨hd, he, η₀, hη₀, hreg⟩ := h
  refine ⟨hd, he, η₀, hη₀, fun η hηpos hηlt => ?_⟩
  have hp := (hreg η hηpos hηlt).reset {some x}
  rwa [jointValW_reset_some, jointValW_reset_some] at hp

/-- **Reset clause** for the coupled relation: resetting clock `x` preserves it (both regimes). -/
theorem Sq2CoupledRel.reset {D : Type*} [DecidableEq D] {p q : Sq2} {u u' : Valuation D}
    (h : Sq2CoupledRel p u q u') (x : D) :
    Sq2CoupledRel p (Valuation.reset {x} u) q (Valuation.reset {x} u') := by
  rcases h with ⟨hpd, hqd, hr⟩ | ⟨d, e, hp, hq, hfr⟩
  · exact Or.inl ⟨hpd, hqd, hr.reset {x}⟩
  · exact Or.inr ⟨d, e, hp, hq, hfr.reset x⟩

/-- **The seed** `(A 0, 0) ~ (B 0, 0)`: A and B coincide; for any `η < √2 − 1` the process clock
`η + (2−√2)` stays in `(0,1)` (frac `≠ 0`, above the all-zero clocks), so the bumped augmented region
matches — the relation relates the initial states. -/
theorem sq2CoupledRel_seed {D : Type*} :
    Sq2CoupledRel (Sq2.A 0) (fun _ : D => 0) (Sq2.B 0) (fun _ : D => 0) := by
  have h1 : (1 : ℝ≥0) < sqrt2NN := by rw [← NNReal.coe_lt_coe]; push_cast; exact one_lt_sqrt2NN
  refine Or.inr ⟨0, 0, rfl, rfl, zero_lt_sqrt2NN, le_of_lt zero_lt_sqrt2NN, sqrt2NN - 1, ?_, ?_⟩
  · rw [tsub_pos_iff_lt]; exact h1
  · intro η _ hη
    rw [zero_add]
    have hs1 : (1 : ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two
    have hs2 : Real.sqrt 2 < 2 := by rw [← coe_sqrt2NN]; exact sqrt2NN_lt_two
    have hηR : (η : ℝ) < Real.sqrt 2 - 1 := by
      have h := hη
      rw [← NNReal.coe_lt_coe, NNReal.coe_sub (le_of_lt h1), coe_sqrt2NN, NNReal.coe_one] at h
      exact h
    have hVn : (jointValW η (fun _ : D => 0)) none = η + twoSubSqrt2NN := by
      rw [jointValW, jointVal_none, add_comm]
    have hV'n : (jointValW (0 : ℝ≥0) (fun _ : D => 0)) none = twoSubSqrt2NN := by
      rw [jointValW, jointVal_none, zero_add]
    have hApos : (0 : ℝ≥0) < η + twoSubSqrt2NN := by
      rw [← NNReal.coe_lt_coe]; push_cast [coe_twoSubSqrt2NN]; linarith [η.coe_nonneg]
    have hAlt1 : η + twoSubSqrt2NN < 1 := by
      rw [← NNReal.coe_lt_coe]; push_cast [coe_twoSubSqrt2NN]; linarith
    have hBpos : (0 : ℝ≥0) < twoSubSqrt2NN := by
      rw [← NNReal.coe_lt_coe]; push_cast [coe_twoSubSqrt2NN]; linarith
    have hBlt1 : twoSubSqrt2NN < 1 := by
      rw [← NNReal.coe_lt_coe]; push_cast [coe_twoSubSqrt2NN]; linarith
    -- floors are 0, frac = value, frac of clocks (= 0) is 0
    have hfloorA : ⌊η + twoSubSqrt2NN⌋₊ = 0 := Nat.floor_eq_zero.mpr hAlt1
    have hfloorB : ⌊twoSubSqrt2NN⌋₊ = 0 := Nat.floor_eq_zero.mpr hBlt1
    have hfrA : fracPart (η + twoSubSqrt2NN) = ((η + twoSubSqrt2NN : ℝ≥0) : ℝ) :=
      Int.fract_eq_self.mpr ⟨(η + twoSubSqrt2NN).coe_nonneg, by exact_mod_cast hAlt1⟩
    have hfrB : fracPart twoSubSqrt2NN = ((twoSubSqrt2NN : ℝ≥0) : ℝ) :=
      Int.fract_eq_self.mpr ⟨twoSubSqrt2NN.coe_nonneg, by exact_mod_cast hBlt1⟩
    have hfrApos : 0 < fracPart (η + twoSubSqrt2NN) := by rw [hfrA]; exact_mod_cast hApos
    have hfrBpos : 0 < fracPart twoSubSqrt2NN := by rw [hfrB]; exact_mod_cast hBpos
    have hfr0 : fracPart (0 : ℝ≥0) = 0 := by simp [fracPart]
    apply regionEqAll_of_exact
    · rintro (_ | x)
      · rw [hVn, hV'n, hfloorA, hfloorB]
      · rfl
    · rintro (_ | x)
      · rw [hVn, hV'n]
        exact ⟨fun h => absurd h hfrApos.ne', fun h => absurd h hfrBpos.ne'⟩
      · rfl
    · have hsv : ∀ (T : ℝ≥0) (z : D), jointValW T (fun _ : D => 0) (some z) = 0 := fun T z => by
        rw [jointValW, jointVal_some]
      rintro (_ | x) (_ | y)
      · simp only [hVn, hV'n]; exact ⟨fun _ => le_refl _, fun _ => le_refl _⟩
      · simp only [hVn, hV'n, hsv, hfr0]
        exact ⟨fun h => absurd (lt_of_lt_of_le hfrApos h) (lt_irrefl _),
          fun h => absurd (lt_of_lt_of_le hfrBpos h) (lt_irrefl _)⟩
      · simp only [hVn, hV'n, hsv, hfr0]
        exact ⟨fun _ => le_of_lt hfrBpos, fun _ => le_of_lt hfrApos⟩
      · simp only [hsv, hfr0]

end TLTS

end DeepWiki.ReactiveSystems
