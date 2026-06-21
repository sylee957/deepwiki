import DeepWiki.ReactiveSystems.TimedSqrt2BisimulationDelay

/-! # The `√2` Mt-bisimulation, step 3: the exact-crossing good case (Ex 12.12(3))
Continues `TimedSqrt2BisimulationDelay`. The last delay sub-case is the *exact* crossing `d + δ = √2`.
There `jointValW` forces B to exactly `√2` (`a`-enabled, against an `a`-disabled A) — but when **no
formula clock sits on an integer** (the "good" case), there is open wiggle-room: B can be nudged
strictly past `√2` while the formula-clock regions are preserved. This file supplies the reusable
region lemma behind that nudge — *a small advance preserves the region when no clock is on an
integer* — and assembles the exact-crossing good case. The remaining hole is then exactly the
double-coincidence (a formula clock on an integer at `√2`), the single-irrational-cut core. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-! ### The √2-cut as a fractional comparison (foundation for the single-irrational-cut region)
Within the integer region `(1, 2)` the irrational boundary `√2` is exactly the fractional cut at
`√2 − 1`: `p < √2 ↔ fracPart p < fracPart √2`. This is the foundation for tracking the `√2`-cut
*correctly* (decoupled from the integer clock cuts), the fix for the double-coincidence — where the
relation must be **asymmetric**, mapping A-at-`√2` (`a`-disabled, open threshold) to B strictly past
`√2` (`a`-disabled, closed threshold). -/

/-- The fractional part of `√2` is `√2 − 1`. -/
theorem fracPart_sqrt2NN : fracPart sqrt2NN = Real.sqrt 2 - 1 := by
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := le_of_lt Real.one_lt_sqrt_two
  have h2 : Real.sqrt 2 < 2 := by rw [← coe_sqrt2NN]; exact sqrt2NN_lt_two
  have hfloor : ⌊Real.sqrt 2⌋ = 1 := by
    rw [Int.floor_eq_iff]; refine ⟨by push_cast; linarith, by push_cast; linarith⟩
  unfold fracPart; rw [coe_sqrt2NN, Int.fract, hfloor]; push_cast; ring

/-- Within `[1, 2)` the `√2`-side is the fractional comparison with `fracPart √2 = √2 − 1`. -/
theorem sqrt2_side_iff_fracPart {p : ℝ≥0} (h1 : 1 ≤ p) (h2 : p < 2) :
    p < sqrt2NN ↔ fracPart p < fracPart sqrt2NN := by
  have hfp : fracPart p = (p : ℝ) - 1 := by
    have hpf : ⌊(p : ℝ)⌋ = 1 := by
      rw [Int.floor_eq_iff]
      exact ⟨by push_cast; exact_mod_cast h1, by push_cast; exact_mod_cast h2⟩
    unfold fracPart; rw [Int.fract, hpf]; push_cast; ring
  rw [fracPart_sqrt2NN, hfp, ← NNReal.coe_lt_coe, coe_sqrt2NN]
  constructor <;> intro h <;> linarith

/-- **Small advance preserves the region.** If no clock of `W` sits on an integer and `ε` is small
enough that no clock crosses its next integer (`fracPart (W x) + ε < 1`), then `W` and `W + ε` are
region-equivalent. -/
theorem regionEqAll_add_small {D : Type*} [Fintype D] (W : Valuation D)
    (hno : ∀ x, fracPart (W x) ≠ 0) {ε : ℝ≥0} (hpos : 0 < ε)
    (hε : ∀ x, fracPart (W x) + (ε : ℝ) < 1) : RegionEqAll W (W.add ε) := by
  have hpos' : (0 : ℝ) < ε := by exact_mod_cast hpos
  apply regionEqAll_of_exact
  · intro x; simp only [Valuation.add_apply]; exact (fracPart_add_of_no_wrap (hε x)).2.symm
  · intro x
    simp only [Valuation.add_apply, (fracPart_add_of_no_wrap (hε x)).1]
    refine ⟨fun h => absurd h (hno x), fun h => ?_⟩
    exact absurd h (by have := fracPart_nonneg (W x); positivity)
  · intro x y
    simp only [Valuation.add_apply, (fracPart_add_of_no_wrap (hε x)).1,
      (fracPart_add_of_no_wrap (hε y)).1]
    constructor <;> intro h <;> linarith

/-- Existence form: a clock valuation with no clock on an integer has a strictly positive advance
into a region-equivalent valuation. -/
theorem regionEqAll_exists_add_small {D : Type*} [Fintype D] (W : Valuation D)
    (hno : ∀ x, fracPart (W x) ≠ 0) : ∃ ε : ℝ≥0, 0 < ε ∧ RegionEqAll W (W.add ε) := by
  obtain ⟨ε, hpos, hε⟩ : ∃ ε : ℝ≥0, 0 < ε ∧ ∀ x, fracPart (W x) + (ε : ℝ) < 1 := by
    rcases isEmpty_or_nonempty D with hD | hD
    · exact ⟨1, one_pos, fun x => (hD.false x).elim⟩
    · obtain ⟨x₀, -, hx₀⟩ := Finset.exists_min_image Finset.univ
        (fun x => (1 : ℝ) - fracPart (W x)) Finset.univ_nonempty
      have hm0 : 0 < 1 - fracPart (W x₀) := by have := fracPart_lt_one (W x₀); linarith
      refine ⟨((1 - fracPart (W x₀)) / 2).toNNReal, by rw [Real.toNNReal_pos]; linarith, fun x => ?_⟩
      rw [Real.coe_toNNReal _ (by linarith)]
      have hxle := hx₀ x (Finset.mem_univ x)
      have := fracPart_lt_one (W x₀)
      linarith
  exact ⟨ε, hpos, regionEqAll_add_small W hno hpos hε⟩

/-- Frac-zero status is a region invariant (at every clock, via an arbitrarily large `cmax`). -/
theorem regionEqAll_fracPart_zero_iff {D : Type*} {V V' : Valuation D}
    (h : RegionEqAll V V') (x : D) : fracPart (V x) = 0 ↔ fracPart (V' x) = 0 := by
  obtain ⟨_, h2, _⟩ := h (fun y => ⌊V y⌋₊ + ⌊V' y⌋₊ + 1)
  refine h2 x ?_
  refine le_of_lt (lt_of_lt_of_le (Nat.lt_floor_add_one (V x)) ?_)
  exact_mod_cast Nat.le_add_right (⌊V x⌋₊ + 1) (⌊V' x⌋₊) |>.trans_eq (by ring)

namespace TLTS

/-- **Delay clause, live and exactly crossing — good case.** When A delays exactly to `√2` and **no
formula clock lands on an integer**, B is nudged strictly past `√2` (`regionEqAll_exists_add_small`)
while the formula-clock regions are preserved, so both become `a`-disabled (the past regime). This
discharges every exact-crossing except the double-coincidence (a formula clock on an integer). -/
theorem Sq2Rel.delay_live_cross_exact_good {D : Type*} [Fintype D] {d e : ℝ≥0} {u u' : Valuation D}
    (hr : RegionEqAll (jointValW d u) (jointValW e u')) (δ : ℝ≥0) (hexact : d + δ = sqrt2NN)
    (hgood : ∀ x, fracPart ((u.add δ) x) ≠ 0) :
    ∃ δ' q', (sq2TLTS sqrt2NN).delay (Sq2.B e) δ' q' ∧
      Sq2Rel (Sq2.A (d + δ)) (u.add δ) q' (u'.add δ') := by
  obtain ⟨δ'₀, hr'⟩ := jointValW_delay_match hr δ
  have hrf : RegionEqAll (u.add δ) (u'.add δ'₀) := by
    have hp := RegionEqAll.precomp (Option.some_injective D) hr'
    rwa [jointValW_comp_some, jointValW_comp_some] at hp
  have hno' : ∀ x, fracPart ((u'.add δ'₀) x) ≠ 0 := fun x h =>
    hgood x ((regionEqAll_fracPart_zero_iff hrf x).mpr h)
  obtain ⟨ε, hpos, hreg⟩ := regionEqAll_exists_add_small (u'.add δ'₀) hno'
  have hadd : (u'.add δ'₀).add ε = u'.add (δ'₀ + ε) := by
    funext x; simp only [Valuation.add_apply]; ring
  have hrf' : RegionEqAll (u.add δ) (u'.add (δ'₀ + ε)) := by rw [← hadd]; exact hrf.trans hreg
  have heq0 : e + δ'₀ = sqrt2NN := (jointValW_sqrt2_eq_side hr').mp hexact
  have hgt : sqrt2NN < e + (δ'₀ + ε) := by
    rw [← add_assoc, heq0]; exact lt_add_of_pos_right sqrt2NN hpos
  refine ⟨δ'₀ + ε, Sq2.B (e + (δ'₀ + ε)), sq2_delay.mpr Sq2Step.delB,
    Or.inl ⟨le_of_eq hexact.symm, hgt, hrf'⟩⟩

end TLTS

end DeepWiki.ReactiveSystems
