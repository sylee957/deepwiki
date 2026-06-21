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

/-- **Small process-bump invariance.** Two infinitesimally different process-bumps give the same
augmented region: for all sufficiently small `a, b > 0`, `jointValW (T+a) w` and `jointValW (T+b) w`
are region-equivalent. This is the `∀`-small-`η` uniformity that lets a single `δ'` (from
`jointValW_delay_match`) serve the live-delay result's `∀ η`. The bound is the gap from the process
clock's fractional part up to the next clock-fraction or its next integer. -/
theorem jointValW_smallBump {D : Type*} [Fintype D] (T : ℝ≥0) (w : Valuation D) :
    ∃ η₂ : ℝ≥0, 0 < η₂ ∧ ∀ a b : ℝ≥0, 0 < a → a < η₂ → 0 < b → b < η₂ →
      RegionEqAll (jointValW (T + a) w) (jointValW (T + b) w) := by
  set φ : ℝ := fracPart (T + twoSubSqrt2NN) with hφ
  have hφ1 : φ < 1 := fracPart_lt_one _
  have hφ0 : (0 : ℝ) ≤ φ := fracPart_nonneg _
  obtain ⟨bnd, hbnd0, hbnd1, hbndx⟩ :
      ∃ bnd : ℝ, 0 < bnd ∧ bnd ≤ 1 - φ ∧ ∀ x, φ < fracPart (w x) → bnd ≤ fracPart (w x) - φ := by
    rcases isEmpty_or_nonempty D with hD | hD
    · exact ⟨1 - φ, by linarith, le_refl _, fun x _ => (hD.false x).elim⟩
    · obtain ⟨x₀, -, hx₀⟩ := Finset.exists_min_image Finset.univ
        (fun x => if φ < fracPart (w x) then fracPart (w x) - φ else 1 - φ) Finset.univ_nonempty
      refine ⟨min (1 - φ) (if φ < fracPart (w x₀) then fracPart (w x₀) - φ else 1 - φ),
        lt_min (by linarith) ?_, min_le_left _ _, fun x hx => ?_⟩
      · split <;> linarith
      · refine le_trans (min_le_right _ _) ?_
        have h := hx₀ x (Finset.mem_univ x)
        rwa [if_pos hx] at h
  refine ⟨bnd.toNNReal, by rw [Real.toNNReal_pos]; exact hbnd0, fun a b ha haη hb hbη => ?_⟩
  have hbndax : (a : ℝ) < bnd := by
    have h := NNReal.coe_lt_coe.mpr haη; rwa [Real.coe_toNNReal bnd hbnd0.le] at h
  have hbndbx : (b : ℝ) < bnd := by
    have h := NNReal.coe_lt_coe.mpr hbη; rwa [Real.coe_toNNReal bnd hbnd0.le] at h
  have haR : (a : ℝ) < 1 - φ := lt_of_lt_of_le hbndax hbnd1
  have hbR : (b : ℝ) < 1 - φ := lt_of_lt_of_le hbndbx hbnd1
  have haR0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hval : ∀ c : ℝ≥0, jointValW (T + c) w none = (T + twoSubSqrt2NN) + c := fun c => by
    rw [jointValW, jointVal_none]; ring
  have hfa : fracPart ((T + twoSubSqrt2NN) + a) = φ + (a : ℝ) :=
    (fracPart_add_of_no_wrap (by rw [← hφ]; linarith)).1
  have hfb : fracPart ((T + twoSubSqrt2NN) + b) = φ + (b : ℝ) :=
    (fracPart_add_of_no_wrap (by rw [← hφ]; linarith)).1
  have hflra : ⌊(T + twoSubSqrt2NN) + a⌋₊ = ⌊T + twoSubSqrt2NN⌋₊ :=
    (fracPart_add_of_no_wrap (by rw [← hφ]; linarith)).2
  have hflrb : ⌊(T + twoSubSqrt2NN) + b⌋₊ = ⌊T + twoSubSqrt2NN⌋₊ :=
    (fracPart_add_of_no_wrap (by rw [← hφ]; linarith)).2
  apply regionEqAll_of_exact
  · rintro (_ | x)
    · rw [hval, hval, hflra, hflrb]
    · rfl
  · rintro (_ | x)
    · rw [hval, hval, hfa, hfb]
      exact iff_of_false (fun h => by linarith) (fun h => by linarith)
    · exact Iff.rfl
  · rintro (_ | x) (_ | y)
    · rw [hval, hval]; exact ⟨fun _ => le_refl _, fun _ => le_refl _⟩
    · simp only [hval, hfa, hfb]
      show φ + (a : ℝ) ≤ fracPart (w y) ↔ φ + (b : ℝ) ≤ fracPart (w y)
      by_cases hwy : φ < fracPart (w y)
      · exact iff_of_true (by linarith [hbndx y hwy]) (by linarith [hbndx y hwy])
      · rw [not_lt] at hwy
        exact iff_of_false (fun h => by linarith) (fun h => by linarith)
    · simp only [hval, hfa, hfb]
      show fracPart (w x) ≤ φ + (a : ℝ) ↔ fracPart (w x) ≤ φ + (b : ℝ)
      by_cases hwx : φ < fracPart (w x)
      · exact iff_of_false (fun h => by linarith [hbndx x hwx]) (fun h => by linarith [hbndx x hwx])
      · rw [not_lt] at hwx
        exact iff_of_true (by linarith) (by linarith)
    · exact Iff.rfl

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

/-- **Live-stay delay** (the successor breakthrough realized): when A delays to a process still below
`√2`, B matches via the *existing* `jointValW_delay_match` — the asymmetric η-bump rides through the
uniform advance. A single `δ'` serves the result's `∀η` (via `jointValW_smallBump`), and `e + δ' ≤ √2`
because the bumped process stays below `√2` (`jointValW_sqrt2_side`). -/
theorem Sq2CoupledFRel.delayLiveStay {D : Type*} [Fintype D] {d e : ℝ≥0} {u u' : Valuation D}
    (h : Sq2CoupledFRel d u e u') (δ : ℝ≥0) (hstay : d + δ < sqrt2NN) :
    ∃ δ', Sq2CoupledFRel (d + δ) (u.add δ) (e + δ') (u'.add δ') := by
  obtain ⟨_, _, η₀, hη₀, hreg⟩ := h
  obtain ⟨η₂, hη₂0, hsb⟩ := jointValW_smallBump (d + δ) (u.add δ)
  have hgap : 0 < sqrt2NN - (d + δ) := tsub_pos_of_lt hstay
  have hm0 : 0 < min η₀ (min η₂ (sqrt2NN - (d + δ))) := lt_min hη₀ (lt_min hη₂0 hgap)
  set η₁ : ℝ≥0 := min η₀ (min η₂ (sqrt2NN - (d + δ))) / 2 with hη₁
  have hη₁0 : 0 < η₁ := half_pos hm0
  have hη₁m : η₁ < min η₀ (min η₂ (sqrt2NN - (d + δ))) := NNReal.half_lt_self hm0.ne'
  have hη₁η₀ : η₁ < η₀ := lt_of_lt_of_le hη₁m (min_le_left _ _)
  have hη₁η₂ : η₁ < η₂ := lt_of_lt_of_le hη₁m (le_trans (min_le_right _ _) (min_le_left _ _))
  have hη₁gap : η₁ < sqrt2NN - (d + δ) :=
    lt_of_lt_of_le hη₁m (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨δ', hδ'⟩ := jointValW_delay_match (hreg η₁ hη₁0 hη₁η₀) δ
  rw [show d + η₁ + δ = (d + δ) + η₁ from by ring] at hδ'
  have hAlt : (d + δ) + η₁ < sqrt2NN :=
    calc (d + δ) + η₁ < (d + δ) + (sqrt2NN - (d + δ)) := by gcongr
      _ = sqrt2NN := add_tsub_cancel_of_le (le_of_lt hstay)
  refine ⟨δ', hstay, le_of_lt ((jointValW_sqrt2_side hδ').mp hAlt), η₁, hη₁0, fun η' hη'0 hη'η₁ => ?_⟩
  exact (hsb η' η₁ hη'0 (lt_trans hη'η₁ hη₁η₂) hη₁0 hη₁η₂).trans hδ'

/-- **Crossing delay** (`√2 ≤ d + δ`): A lands at or past `√2` (`a`-disabled); B matches into the past
regime. The η-bump forces B *strictly* past `√2` even at the double-coincidence — the bumped process
`(d+δ)+η > √2` has `frac ≠ 0`, so the region match (`jointValW_sqrt2_side` + `jointValW_sqrt2_eq_side`)
puts B's process strictly above `√2`. The formula clocks land region-equivalent (`precomp some`). -/
theorem Sq2CoupledFRel.delayCross {D : Type*} [Fintype D] {d e : ℝ≥0} {u u' : Valuation D}
    (h : Sq2CoupledFRel d u e u') (δ : ℝ≥0) (hcross : sqrt2NN ≤ d + δ) :
    ∃ δ', sqrt2NN < e + δ' ∧ RegionEqAll (u.add δ) (u'.add δ') := by
  obtain ⟨_, _, η₀, hη₀, hreg⟩ := h
  obtain ⟨δ', hδ'⟩ :=
    jointValW_delay_match (hreg (η₀ / 2) (half_pos hη₀) (NNReal.half_lt_self hη₀.ne')) δ
  rw [show d + η₀ / 2 + δ = (d + δ) + η₀ / 2 from by ring] at hδ'
  have hApast : sqrt2NN < (d + δ) + η₀ / 2 := lt_of_le_of_lt hcross (lt_add_of_pos_right _ (half_pos hη₀))
  refine ⟨δ', ?_, ?_⟩
  · have hge : sqrt2NN ≤ e + δ' :=
      not_lt.mp (fun hlt => absurd ((jointValW_sqrt2_side hδ').mpr hlt) (not_lt.mpr (le_of_lt hApast)))
    have hne : e + δ' ≠ sqrt2NN := fun heq => (ne_of_gt hApast) ((jointValW_sqrt2_eq_side hδ').mpr heq)
    exact lt_of_le_of_ne hge (Ne.symm hne)
  · have hp := RegionEqAll.precomp (f := Option.some) (Option.some_injective D) hδ'
    rwa [jointValW_comp_some, jointValW_comp_some] at hp

/-- **Action clause (forth).** A does `a` (so `d < √2`); B matches (`e ≤ √2`), both reaching `End` —
the past regime. -/
theorem Sq2CoupledRel.act_forth {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2CoupledRel p u q u') (α : Sq2Act) (p' : Sq2)
    (hstep : (sq2TLTS sqrt2NN).act p α p') :
    ∃ q', (sq2TLTS sqrt2NN).act q α q' ∧ Sq2CoupledRel p' u q' u' := by
  rw [sq2_act] at hstep
  rcases h with ⟨hpd, _, _⟩ | ⟨d, e, hp, hq, hfr⟩
  · exact absurd hstep (fun hs => hpd.no_act hs)
  · subst hp; subst hq
    cases hstep with
    | aA _ => exact ⟨Sq2.End, sq2_act.mpr (Sq2Step.aB hfr.2.1), Or.inl ⟨trivial, trivial, hfr.regionEqAll⟩⟩

/-- **Action clause (back).** B does `a` (so `e ≤ √2`); A matches (`d < √2`), both reaching `End`. -/
theorem Sq2CoupledRel.act_back {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2CoupledRel p u q u') (α : Sq2Act) (q' : Sq2)
    (hstep : (sq2TLTS sqrt2NN).act q α q') :
    ∃ p', (sq2TLTS sqrt2NN).act p α p' ∧ Sq2CoupledRel p' u q' u' := by
  rw [sq2_act] at hstep
  rcases h with ⟨_, hqd, _⟩ | ⟨d, e, hp, hq, hfr⟩
  · exact absurd hstep (fun hs => hqd.no_act hs)
  · subst hp; subst hq
    cases hstep with
    | aB _ => exact ⟨Sq2.End, sq2_act.mpr (Sq2Step.aA hfr.1), Or.inl ⟨trivial, trivial, hfr.regionEqAll⟩⟩

/-- **Delay clause (forth).** Combines the past-regime time-successor, the live-stay delay
(`delayLiveStay`), and the crossing delay (`delayCross`), wrapping the TLTS `delB` step. -/
theorem Sq2CoupledRel.delayForth {D : Type*} [Fintype D] {p q : Sq2} {u u' : Valuation D}
    (h : Sq2CoupledRel p u q u') (δ : ℝ≥0) (p' : Sq2)
    (hstep : (sq2TLTS sqrt2NN).delay p δ p') :
    ∃ δ' q', (sq2TLTS sqrt2NN).delay q δ' q' ∧ Sq2CoupledRel p' (u.add δ) q' (u'.add δ') := by
  rw [sq2_delay] at hstep
  rcases h with ⟨hpd, hqd, hr⟩ | ⟨d, e, hp, hq, hfr⟩
  · obtain ⟨δ', hr'⟩ := regionEqAll_timeSuccessor hr δ
    obtain ⟨q', hqstep, hq'd⟩ := hqd.delay_succ δ'
    exact ⟨δ', q', sq2_delay.mpr hqstep, Or.inl ⟨hpd.delay_pres hstep, hq'd, hr'⟩⟩
  · subst hp; subst hq
    cases hstep with
    | delA =>
      by_cases hc : d + δ < sqrt2NN
      · obtain ⟨δ', hfr'⟩ := hfr.delayLiveStay δ hc
        exact ⟨δ', Sq2.B (e + δ'), sq2_delay.mpr Sq2Step.delB, Or.inr ⟨d + δ, e + δ', rfl, rfl, hfr'⟩⟩
      · rw [not_lt] at hc
        obtain ⟨δ', hBpast, hr'⟩ := hfr.delayCross δ hc
        exact ⟨δ', Sq2.B (e + δ'), sq2_delay.mpr Sq2Step.delB, Or.inl ⟨hc, hBpast, hr'⟩⟩

end TLTS

end DeepWiki.ReactiveSystems
