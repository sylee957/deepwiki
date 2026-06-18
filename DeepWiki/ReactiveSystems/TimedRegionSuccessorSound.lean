import DeepWiki.ReactiveSystems.TimedRegionSuccessor

/-! # Soundness of the region time-successor (Alur–Dill §4.3)
Each elapse step `regionCodeStep` on a region code is **realized by an actual delay**:
for every valuation `w` there is a `δ` with `fp (w + δ) = regionCodeStep (fp w)`. Composing
along the orbit gives `SuccSound` for `regionCodeDelaySucc` — every code it lists is the
fingerprint of `w` after some delay. (The converse, `SuccComplete`, is the deep direction.)
This file builds step soundness case by case (Alur–Dill's three cases). -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

variable {C : Type*} [Fintype C] [DecidableEq C]

omit [Fintype C] [DecidableEq C] in
/-- Delaying by `0` is the identity valuation. -/
theorem Valuation.add_zero (w : Valuation C) : w.add 0 = w := by
  funext x; simp [Valuation.add_apply]

omit [DecidableEq C] in
/-- **Step soundness, case A** (all clocks saturated): when every clock already exceeds its
clamp, the elapse step is the identity, realized by the zero delay. -/
theorem regionCodeStep_sound_allUnbounded {cmax : C → ℕ} {w : Valuation C}
    (h : ∀ x, (cmax x : ℝ≥0) < w x) :
    regionFingerprint cmax (w.add 0) = regionCodeStep (regionFingerprint cmax w) := by
  have hcond : decide (∀ x, ((regionFingerprint cmax w).1 x).val = cmax x + 1) = true := by
    rw [decide_eq_true_iff]
    intro x
    rw [regionFingerprint_floor]
    unfold regionFloor
    rw [if_neg (not_le.mpr (h x))]
  rw [Valuation.add_zero]
  show regionFingerprint cmax w = regionCodeStep (regionFingerprint cmax w)
  unfold regionCodeStep
  rw [if_pos hcond]

omit [Fintype C] [DecidableEq C] in
open Classical in
/-- **Saturated states stay put.** If every clock already exceeds its clamp, the region is
unchanged by any delay — `fp (w + t) = fp w`. (The fixpoint base case of completeness: a
saturated region is its own only time-successor.) -/
theorem regionFingerprint_add_of_allUnbounded {cmax : C → ℕ} {w : Valuation C}
    (h : ∀ x, (cmax x : ℝ≥0) < w x) (t : ℝ≥0) :
    regionFingerprint cmax (w.add t) = regionFingerprint cmax w := by
  have hub : ∀ x, ¬ ((w.add t) x ≤ (cmax x : ℝ≥0)) := fun x => by
    rw [Valuation.add_apply]; exact not_le.mpr (lt_of_lt_of_le (h x) le_self_add)
  have hub0 : ∀ x, ¬ (w x ≤ (cmax x : ℝ≥0)) := fun x => not_le.mpr (h x)
  rw [Prod.ext_iff, Prod.ext_iff]
  refine ⟨funext fun x => ?_, funext fun x => ?_, funext fun x => funext fun y => ?_⟩
  · apply Fin.ext
    show regionFloor cmax (w.add t) x = regionFloor cmax w x
    unfold regionFloor; rw [if_neg (hub x), if_neg (hub0 x)]
  · rw [regionFingerprint_fracZero, regionFingerprint_fracZero,
      decide_eq_false_iff_not.mpr (fun hc => hub x hc.1),
      decide_eq_false_iff_not.mpr (fun hc => hub0 x hc.1)]
  · rw [regionFingerprint_fracOrder, regionFingerprint_fracOrder,
      decide_eq_false_iff_not.mpr (fun hc => hub x hc.1),
      decide_eq_false_iff_not.mpr (fun hc => hub0 x hc.1)]

/-! ## Fixpoint detection (a non-saturated region genuinely advances) -/

omit [DecidableEq C] in
open Classical in
/-- **A region is a `step`-fixpoint only if fully saturated.** If `regionCodeStep (fp w) =
fp w` then every clock exceeds its clamp — a non-saturated region always advances (case B
flips an integral clock's frac-zero bit; case C bumps a maximal-fraction clock's floor). -/
theorem regionCodeStep_eq_self_imp_allUnbounded {cmax : C → ℕ} {w : Valuation C}
    (h : regionCodeStep (regionFingerprint cmax w) = regionFingerprint cmax w) :
    ∀ x, (cmax x : ℝ≥0) < w x := by
  set γ := regionFingerprint cmax w with hγ
  by_contra hcon
  simp only [not_forall, not_lt] at hcon
  obtain ⟨x₀, hx₀⟩ := hcon
  have hnotA : ¬ (decide (∀ x, (γ.1 x).val = cmax x + 1) = true) := by
    rw [decide_eq_true_iff]
    intro hall
    have he := hall x₀
    rw [hγ, regionFingerprint_floor] at he
    have hle : regionFloor cmax w x₀ ≤ cmax x₀ := (regionFloor_le_clamp_iff w x₀).mpr hx₀
    omega
  by_cases hdB : decide (∃ x, γ.2.1 x = true) = true
  · obtain ⟨x₁, hx₁⟩ := decide_eq_true_iff.mp hdB
    have hstepB : (regionCodeStep γ).2.1 x₁ = false := by
      unfold regionCodeStep; rw [if_neg hnotA, if_pos hdB]
    have hcontra : γ.2.1 x₁ = false := h ▸ hstepB
    rw [hx₁] at hcontra
    exact absurd hcontra (by decide)
  · set S : Finset C := Finset.univ.filter (fun x => w x ≤ (cmax x : ℝ≥0)) with hS
    have hx₀S : x₀ ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx₀⟩
    obtain ⟨x₁, hx₁S, hx₁max⟩ := S.exists_max_image (fun x => fracPart (w x)) ⟨x₀, hx₀S⟩
    have hbnd1 : w x₁ ≤ (cmax x₁ : ℝ≥0) := (Finset.mem_filter.mp hx₁S).2
    have hfl1 : (γ.1 x₁).val ≤ cmax x₁ := by
      rw [hγ, regionFingerprint_floor]; exact (regionFloor_le_clamp_iff w x₁).mpr hbnd1
    have hisMax : (decide ((γ.1 x₁).val ≤ cmax x₁) &&
        decide (∀ y, (γ.1 y).val ≤ cmax y → γ.2.2 y x₁ = true)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_iff]
      refine ⟨hfl1, fun y hy => ?_⟩
      have hbndy : w y ≤ (cmax y : ℝ≥0) := by
        rw [hγ, regionFingerprint_floor] at hy; exact (regionFloor_le_clamp_iff w y).mp hy
      rw [hγ, regionFingerprint_fracOrder, decide_eq_true_iff]
      exact ⟨hbndy, hbnd1, hx₁max y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbndy⟩)⟩
    have hstepC : (regionCodeStep γ).1 x₁ = bumpFloor cmax x₁ ((γ.1 x₁).val + 1) := by
      unfold regionCodeStep; rw [if_neg hnotA, if_neg hdB]; exact if_pos hisMax
    have hval : ((regionCodeStep γ).1 x₁).val = min ((γ.1 x₁).val + 1) (cmax x₁ + 1) := by
      rw [hstepC]; rfl
    have heq : (γ.1 x₁).val = ((regionCodeStep γ).1 x₁).val := by rw [h]
    rw [hval] at heq
    omega

/-! ## Case-C dispatch (the step's components when no clock is integral) -/

omit [DecidableEq C] in
/-- In case C (not all saturated, no integral clock), the elapse step's floor at `x`. -/
theorem regionCodeStep_caseC_fst {cmax : C → ℕ} {γ : RegionCode cmax}
    (hA : ¬ ∀ x, (γ.1 x).val = cmax x + 1) (hB : ¬ ∃ x, γ.2.1 x = true) (x : C) :
    (regionCodeStep γ).1 x =
      if (decide ((γ.1 x).val ≤ cmax x) &&
          decide (∀ y, (γ.1 y).val ≤ cmax y → γ.2.2 y x = true)) = true then
        bumpFloor cmax x ((γ.1 x).val + 1) else γ.1 x := by
  unfold regionCodeStep
  rw [if_neg (by rw [decide_eq_true_iff]; exact hA), if_neg (by rw [decide_eq_true_iff]; exact hB)]

omit [DecidableEq C] in
/-- In case C, the elapse step's frac-zero bit at `x` (the maximal-fraction clocks become
integral). -/
theorem regionCodeStep_caseC_snd {cmax : C → ℕ} {γ : RegionCode cmax}
    (hA : ¬ ∀ x, (γ.1 x).val = cmax x + 1) (hB : ¬ ∃ x, γ.2.1 x = true) (x : C) :
    (regionCodeStep γ).2.1 x =
      (decide ((γ.1 x).val ≤ cmax x) &&
        decide (∀ y, (γ.1 y).val ≤ cmax y → γ.2.2 y x = true)) := by
  unfold regionCodeStep
  rw [if_neg (by rw [decide_eq_true_iff]; exact hA), if_neg (by rw [decide_eq_true_iff]; exact hB)]

omit [DecidableEq C] in
/-- In case C, the elapse step's frac-order bit at `(x, y)`. -/
theorem regionCodeStep_caseC_thd {cmax : C → ℕ} {γ : RegionCode cmax}
    (hA : ¬ ∀ x, (γ.1 x).val = cmax x + 1) (hB : ¬ ∃ x, γ.2.1 x = true) (x y : C) :
    (regionCodeStep γ).2.2 x y =
      (if (decide ((γ.1 x).val = cmax x + 1) || decide ((γ.1 y).val = cmax y + 1)) = true then false
       else if (decide ((γ.1 x).val ≤ cmax x) &&
            decide (∀ z, (γ.1 z).val ≤ cmax z → γ.2.2 z x = true)) = true then true
       else if (decide ((γ.1 y).val ≤ cmax y) &&
            decide (∀ z, (γ.1 z).val ≤ cmax z → γ.2.2 z y = true)) = true then false
       else γ.2.2 x y) := by
  unfold regionCodeStep
  rw [if_neg (by rw [decide_eq_true_iff]; exact hA), if_neg (by rw [decide_eq_true_iff]; exact hB)]

/-! ## Small delays keep the region (the "before" half of the key lemma) -/

omit [Fintype C] [DecidableEq C] in
open Classical in
/-- **A small delay keeps the region.** If no bounded clock is integral and the delay `s`
carries no bounded clock past the next integer, then `fp (w + s) = fp w` — floors, frac-zero
bits and frac-order are all preserved. (Used with `s` below the first integer-crossing time in
case C.) -/
theorem regionFingerprint_add_eq_of_small {cmax : C → ℕ} {w : Valuation C} {s : ℝ≥0}
    (hNI : ∀ x, w x ≤ (cmax x : ℝ≥0) → fracPart (w x) ≠ 0)
    (hsmall : ∀ x, w x ≤ (cmax x : ℝ≥0) → fracPart (w x) + (s : ℝ) < 1) :
    regionFingerprint cmax (w.add s) = regionFingerprint cmax w := by
  -- bounded clocks stay bounded with unchanged floor and frac increased by `s`
  have hkey : ∀ x, w x ≤ (cmax x : ℝ≥0) →
      (w.add s) x ≤ (cmax x : ℝ≥0) ∧ ⌊(w.add s) x⌋₊ = ⌊w x⌋₊ ∧
        fracPart ((w.add s) x) = fracPart (w x) + (s : ℝ) := by
    intro x hx
    obtain ⟨hfr, hfl⟩ := fracPart_add_of_no_wrap (hsmall x hx)
    have hdecomp := coe_eq_floor_add_fracPart (w x)
    have hflcmax : ⌊w x⌋₊ ≤ cmax x := floor_le_of_le_cmax hx
    have hfllt : ⌊w x⌋₊ < cmax x := by
      rcases lt_or_eq_of_le hflcmax with h | h
      · exact h
      · exfalso; apply hNI x hx
        have hreal : (w x : ℝ) = cmax x := by
          have hle : (w x : ℝ) ≤ cmax x := by exact_mod_cast hx
          have hge : (cmax x : ℝ) ≤ w x := by
            rw [hdecomp, h]; have := fracPart_nonneg (w x); linarith
          linarith
        have hwx : w x = (cmax x : ℝ≥0) := by exact_mod_cast hreal
        rw [hwx]; exact fracPart_natCast (cmax x)
    have hbnd : (w.add s) x ≤ (cmax x : ℝ≥0) := by
      rw [Valuation.add_apply]
      have : ((w x + s : ℝ≥0) : ℝ) < (⌊w x⌋₊ : ℝ) + 1 := by
        rw [show ((w x + s : ℝ≥0):ℝ) = (w x:ℝ) + s by push_cast; ring, hdecomp]
        have := hsmall x hx; linarith
      have h2 : (⌊w x⌋₊ : ℝ) + 1 ≤ cmax x := by exact_mod_cast Nat.succ_le_of_lt hfllt
      have : ((w x + s : ℝ≥0) : ℝ) ≤ cmax x := by linarith
      exact_mod_cast this
    exact ⟨hbnd, hfl, hfr⟩
  rw [Prod.ext_iff, Prod.ext_iff]
  refine ⟨funext fun x => ?_, funext fun x => ?_, funext fun x => funext fun y => ?_⟩
  · apply Fin.ext
    show regionFloor cmax (w.add s) x = regionFloor cmax w x
    by_cases hx : w x ≤ (cmax x : ℝ≥0)
    · obtain ⟨hbnd, hfl, _⟩ := hkey x hx
      unfold regionFloor; rw [if_pos hbnd, if_pos hx, hfl]
    · have hx' : ¬ (w.add s) x ≤ (cmax x : ℝ≥0) := by
        rw [Valuation.add_apply]; exact fun hc => hx (le_trans le_self_add hc)
      unfold regionFloor; rw [if_neg hx', if_neg hx]
  · rw [regionFingerprint_fracZero, regionFingerprint_fracZero]
    by_cases hx : w x ≤ (cmax x : ℝ≥0)
    · obtain ⟨hbnd, _, hfr⟩ := hkey x hx
      have hnz : fracPart ((w.add s) x) ≠ 0 := by
        rw [hfr]; have := fracPart_nonneg (w x); have := hNI x hx
        have hpos : 0 < fracPart (w x) := lt_of_le_of_ne (fracPart_nonneg _) (Ne.symm (hNI x hx))
        positivity
      rw [decide_eq_false_iff_not.mpr (fun hc => hnz hc.2),
        decide_eq_false_iff_not.mpr (fun hc => hNI x hx hc.2)]
    · have hx' : ¬ (w.add s) x ≤ (cmax x : ℝ≥0) := by
        rw [Valuation.add_apply]; exact fun hc => hx (le_trans le_self_add hc)
      rw [decide_eq_false_iff_not.mpr (fun hc => hx' hc.1),
        decide_eq_false_iff_not.mpr (fun hc => hx hc.1)]
  · rw [regionFingerprint_fracOrder, regionFingerprint_fracOrder]
    by_cases hx : w x ≤ (cmax x : ℝ≥0) <;> by_cases hy : w y ≤ (cmax y : ℝ≥0)
    · obtain ⟨hbx, _, hfrx⟩ := hkey x hx
      obtain ⟨hby, _, hfry⟩ := hkey y hy
      rw [decide_eq_decide]
      rw [hfrx, hfry]
      constructor
      · rintro ⟨_, _, h3⟩; exact ⟨hx, hy, by linarith⟩
      · rintro ⟨_, _, h3⟩; exact ⟨hbx, hby, by linarith⟩
    · have hy' : ¬ (w.add s) y ≤ (cmax y : ℝ≥0) := by
        rw [Valuation.add_apply]; exact fun hc => hy (le_trans le_self_add hc)
      rw [decide_eq_false_iff_not.mpr (fun hc => hy' hc.2.1),
        decide_eq_false_iff_not.mpr (fun hc => hy hc.2.1)]
    · have hx' : ¬ (w.add s) x ≤ (cmax x : ℝ≥0) := by
        rw [Valuation.add_apply]; exact fun hc => hx (le_trans le_self_add hc)
      rw [decide_eq_false_iff_not.mpr (fun hc => hx' hc.1),
        decide_eq_false_iff_not.mpr (fun hc => hx hc.1)]
    · have hx' : ¬ (w.add s) x ≤ (cmax x : ℝ≥0) := by
        rw [Valuation.add_apply]; exact fun hc => hx (le_trans le_self_add hc)
      rw [decide_eq_false_iff_not.mpr (fun hc => hx' hc.1),
        decide_eq_false_iff_not.mpr (fun hc => hx hc.1)]

/-! ## Orbit-structure lemmas (for the completeness induction) -/

omit [DecidableEq C] in
/-- The starting region is the head of its own orbit. -/
theorem mem_regionCodeOrbit_self {cmax : C → ℕ} (fuel : ℕ) (γ : RegionCode cmax) :
    γ ∈ regionCodeOrbit fuel γ := by
  cases fuel with
  | zero => simp [regionCodeOrbit]
  | succ n => simp only [regionCodeOrbit]; split <;> simp

omit [DecidableEq C] in
/-- The orbit of the next region is contained in the orbit of `γ` (its tail), when `γ` is
not already a fixpoint. -/
theorem regionCodeOrbit_step_subset {cmax : C → ℕ} (fuel : ℕ) {γ : RegionCode cmax}
    (h : regionCodeStep γ ≠ γ) :
    regionCodeOrbit fuel (regionCodeStep γ) ⊆ regionCodeOrbit (fuel + 1) γ := by
  simp only [regionCodeOrbit, if_neg h]
  exact List.subset_cons_self _ _

omit [DecidableEq C] in
/-- The next region is in `γ`'s orbit (when `γ` is not a fixpoint). -/
theorem step_mem_regionCodeOrbit {cmax : C → ℕ} (fuel : ℕ) {γ : RegionCode cmax}
    (h : regionCodeStep γ ≠ γ) :
    regionCodeStep γ ∈ regionCodeOrbit (fuel + 1) γ :=
  regionCodeOrbit_step_subset fuel h (mem_regionCodeOrbit_self fuel _)

/-! ## The well-founded measure for the orbit -/

/-- The **descent measure** of a region code: `2·Σ(room below saturation) + #(integral
clocks)`. It strictly decreases along `regionCodeStep` (case C bumps a floor — room down 1,
weight 2 — while only adding one integral clock; case B clears an integral bit), bounding the
orbit length and well-founding the completeness induction. -/
def codeMeasure {cmax : C → ℕ} (γ : RegionCode cmax) : ℕ :=
  2 * (∑ x, (cmax x + 1 - (γ.1 x).val)) + (Finset.univ.filter (fun x => γ.2.1 x = true)).card

/-! ## The descent measure strictly decreases (case C) -/

omit [DecidableEq C] in
open Classical in
/-- **Case C decreases the measure.** When some clock is bounded and none is integral, the
elapse step bumps the maximal-fraction clocks' floors (room down by 1 each, weight 2) while
adding exactly those as integral (count up by `#maxFrac`), a net drop of `#maxFrac ≥ 1`. -/
theorem codeMeasure_step_lt_caseC {cmax : C → ℕ} {w : Valuation C}
    (hbnd : ∃ x, w x ≤ (cmax x : ℝ≥0))
    (hNI : ∀ x, w x ≤ (cmax x : ℝ≥0) → fracPart (w x) ≠ 0) :
    codeMeasure (regionCodeStep (regionFingerprint cmax w))
      < codeMeasure (regionFingerprint cmax w) := by
  set γ := regionFingerprint cmax w with hγ
  set isMaxB : C → Bool := fun x => decide ((γ.1 x).val ≤ cmax x) &&
    decide (∀ y, (γ.1 y).val ≤ cmax y → γ.2.2 y x = true) with hisMaxB
  have hA : ¬ ∀ x, (γ.1 x).val = cmax x + 1 := by
    obtain ⟨x, hx⟩ := hbnd
    intro hall; have h1 := hall x; rw [hγ, regionFingerprint_floor] at h1
    have h2 := (regionFloor_le_clamp_iff w x).mpr hx; omega
  have hB : ¬ ∃ x, γ.2.1 x = true := by
    rintro ⟨x, hx⟩
    rw [hγ, regionFingerprint_fracZero, decide_eq_true_iff] at hx
    exact hNI x hx.1 hx.2
  -- the integral filter of γ is empty
  have hintγ : (Finset.univ.filter (fun x => γ.2.1 x = true)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro x _
    rw [hγ, regionFingerprint_fracZero, decide_eq_true_iff]
    rintro ⟨hbx, hfx⟩; exact hNI x hbx hfx
  -- per-clock room identity
  have hroom : ∀ x, cmax x + 1 - (γ.1 x).val =
      (cmax x + 1 - ((regionCodeStep γ).1 x).val) + (if isMaxB x = true then 1 else 0) := by
    intro x
    rw [regionCodeStep_caseC_fst hA hB x]
    by_cases hm : isMaxB x = true
    · have hbx : (γ.1 x).val ≤ cmax x := by
        rw [hisMaxB, Bool.and_eq_true] at hm; exact decide_eq_true_iff.mp hm.1
      rw [if_pos hm, if_pos hm]
      have : (bumpFloor cmax x ((γ.1 x).val + 1)).val = min ((γ.1 x).val + 1) (cmax x + 1) := rfl
      rw [this]; omega
    · rw [if_neg hm, if_neg hm]; omega
  -- step's integral filter equals the maxFrac filter
  have hintstep : (Finset.univ.filter (fun x => (regionCodeStep γ).2.1 x = true)) =
      Finset.univ.filter (fun x => isMaxB x = true) := by
    apply Finset.filter_congr
    intro x _; rw [regionCodeStep_caseC_snd hA hB x]
  -- the maxFrac filter is nonempty
  have hpos : 0 < (Finset.univ.filter (fun x => isMaxB x = true)).card := by
    obtain ⟨x₀, hx₀⟩ := hbnd
    obtain ⟨x₁, hx₁S, hx₁max⟩ :=
      (Finset.univ.filter (fun x => w x ≤ (cmax x : ℝ≥0))).exists_max_image (fun x => fracPart (w x))
        ⟨x₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx₀⟩⟩
    have hbnd1 : w x₁ ≤ (cmax x₁ : ℝ≥0) := (Finset.mem_filter.mp hx₁S).2
    rw [Finset.card_pos]
    refine ⟨x₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [hisMaxB, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
    refine ⟨by rw [hγ, regionFingerprint_floor]; exact (regionFloor_le_clamp_iff w x₁).mpr hbnd1,
      fun y hy => ?_⟩
    have hbndy : w y ≤ (cmax y : ℝ≥0) := by
      rw [hγ, regionFingerprint_floor] at hy; exact (regionFloor_le_clamp_iff w y).mp hy
    rw [hγ, regionFingerprint_fracOrder, decide_eq_true_iff]
    exact ⟨hbndy, hbnd1, hx₁max y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbndy⟩)⟩
  -- assemble
  have hsum : (∑ x, (cmax x + 1 - (γ.1 x).val)) =
      (∑ x, (cmax x + 1 - ((regionCodeStep γ).1 x).val)) +
        (Finset.univ.filter (fun x => isMaxB x = true)).card := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => hroom x)
  unfold codeMeasure
  rw [hintγ, Finset.card_empty, hintstep, hsum]
  omega

omit [DecidableEq C] in
/-- A region of zero descent measure is fully saturated (no room, no integral clocks). -/
theorem codeMeasure_eq_zero_imp {cmax : C → ℕ} {w : Valuation C}
    (h : codeMeasure (regionFingerprint cmax w) = 0) : ∀ x, (cmax x : ℝ≥0) < w x := by
  intro x
  have hsum : (∑ y, (cmax y + 1 - ((regionFingerprint cmax w).1 y).val)) = 0 := by
    unfold codeMeasure at h; omega
  have hroom : cmax x + 1 - ((regionFingerprint cmax w).1 x).val = 0 :=
    (Finset.sum_eq_zero_iff).mp hsum x (Finset.mem_univ x)
  rw [regionFingerprint_floor] at hroom
  have hfl : regionFloor cmax w x ≤ cmax x + 1 := regionFloor_le cmax w x
  have hsat : regionFloor cmax w x = cmax x + 1 := by omega
  by_contra hb
  rw [not_lt] at hb
  have := (regionFloor_le_clamp_iff w x).mpr hb
  omega

end DeepWiki.ReactiveSystems
