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

/-! ## Case-B dispatch (the step's components when some clock is integral) -/

omit [DecidableEq C] in
/-- In case B (not all saturated, some integral clock), the elapse step's floor at `x`. -/
theorem regionCodeStep_caseB_fst {cmax : C → ℕ} {γ : RegionCode cmax}
    (hA : ¬ ∀ x, (γ.1 x).val = cmax x + 1) (hB : ∃ x, γ.2.1 x = true) (x : C) :
    (regionCodeStep γ).1 x =
      if (decide ((γ.1 x).val = cmax x + 1) || (γ.2.1 x && decide ((γ.1 x).val = cmax x))) = true then
        bumpFloor cmax x (cmax x + 1) else γ.1 x := by
  unfold regionCodeStep
  rw [if_neg (by rw [decide_eq_true_iff]; exact hA), if_pos (by rw [decide_eq_true_iff]; exact hB)]

omit [DecidableEq C] in
/-- In case B, the elapse step clears all frac-zero bits. -/
theorem regionCodeStep_caseB_snd {cmax : C → ℕ} {γ : RegionCode cmax}
    (hA : ¬ ∀ x, (γ.1 x).val = cmax x + 1) (hB : ∃ x, γ.2.1 x = true) (x : C) :
    (regionCodeStep γ).2.1 x = false := by
  unfold regionCodeStep
  rw [if_neg (by rw [decide_eq_true_iff]; exact hA), if_pos (by rw [decide_eq_true_iff]; exact hB)]

omit [DecidableEq C] in
/-- In case B, the elapse step's frac-order bit at `(x, y)`: newly-saturated clocks lose all
order, the small (integral, below-`cmax`) clocks become least, others keep `γ`'s order. -/
theorem regionCodeStep_caseB_thd {cmax : C → ℕ} {γ : RegionCode cmax}
    (hA : ¬ ∀ x, (γ.1 x).val = cmax x + 1) (hB : ∃ x, γ.2.1 x = true) (x y : C) :
    (regionCodeStep γ).2.2 x y =
      (if ((decide ((γ.1 x).val = cmax x + 1) || (γ.2.1 x && decide ((γ.1 x).val = cmax x))) ||
           (decide ((γ.1 y).val = cmax y + 1) || (γ.2.1 y && decide ((γ.1 y).val = cmax y)))) = true
         then false
       else if (γ.2.1 x && decide ((γ.1 x).val < cmax x)) = true then true
       else if (γ.2.1 y && decide ((γ.1 y).val < cmax y)) = true then false
       else γ.2.2 x y) := by
  unfold regionCodeStep
  rw [if_neg (by rw [decide_eq_true_iff]; exact hA), if_pos (by rw [decide_eq_true_iff]; exact hB)]

/-! ## The "at δ" wrap-matching (the "after" half of the key lemma) -/

omit [DecidableEq C] in
open Classical in
/-- **At the integer-crossing delay, the region steps.** With `M` the maximal fraction among
bounded clocks (achieved, an upper bound) and no integral clock, the delay `δ = 1 − M` carries
exactly the maximal-fraction clocks to the next integer, so `fp (w + δ) = regionCodeStep (fp w)`
(case C). The analytic "after" half of the key frac lemma. -/
theorem regionFingerprint_add_eq_step_caseC {cmax : C → ℕ} {w : Valuation C} {M : ℝ}
    (hMach : ∃ x, w x ≤ (cmax x : ℝ≥0) ∧ fracPart (w x) = M)
    (hMmax : ∀ x, w x ≤ (cmax x : ℝ≥0) → fracPart (w x) ≤ M)
    (hNI : ∀ x, w x ≤ (cmax x : ℝ≥0) → fracPart (w x) ≠ 0)
    {δ : ℝ≥0} (hδ : (δ : ℝ) = 1 - M) :
    regionFingerprint cmax (w.add δ) = regionCodeStep (regionFingerprint cmax w) := by
  set γ := regionFingerprint cmax w with hγ
  obtain ⟨xM, hxMb, hxMf⟩ := hMach
  have hM0 : 0 < M := by
    rw [← hxMf]; exact lt_of_le_of_ne (fracPart_nonneg _) (Ne.symm (hNI xM hxMb))
  have hM1 : M < 1 := by rw [← hxMf]; exact fracPart_lt_one (w xM)
  have hδ0 : (0 : ℝ) < δ := by rw [hδ]; linarith
  have hδ1 : (δ : ℝ) < 1 := by rw [hδ]; linarith
  have hA : ¬ ∀ x, (γ.1 x).val = cmax x + 1 := by
    intro hall; have h1 := hall xM; rw [hγ, regionFingerprint_floor] at h1
    have := (regionFloor_le_clamp_iff w xM).mpr hxMb; omega
  have hB : ¬ ∃ x, γ.2.1 x = true := by
    rintro ⟨x, hx⟩; rw [hγ, regionFingerprint_fracZero, decide_eq_true_iff] at hx
    exact hNI x hx.1 hx.2
  have hvalγ : ∀ x, w x ≤ (cmax x : ℝ≥0) → (γ.1 x).val = ⌊w x⌋₊ := by
    intro x hbx; rw [hγ, regionFingerprint_floor]; unfold regionFloor; rw [if_pos hbx]
  have hfllt : ∀ x, w x ≤ (cmax x : ℝ≥0) → ⌊w x⌋₊ < cmax x := by
    intro x hbx
    rcases lt_or_eq_of_le (floor_le_of_le_cmax hbx) with h | h
    · exact h
    · exfalso; apply hNI x hbx
      have hwx : w x = (cmax x : ℝ≥0) :=
        le_antisymm hbx (by rw [← h]; exact_mod_cast Nat.floor_le (zero_le' (a := w x)))
      rw [hwx]; exact fracPart_natCast (cmax x)
  -- the code-level `isMax` predicate on a bounded clock means maximal fraction
  have hisMaxChar : ∀ x, w x ≤ (cmax x : ℝ≥0) →
      ((decide ((γ.1 x).val ≤ cmax x) &&
        decide (∀ y, (γ.1 y).val ≤ cmax y → γ.2.2 y x = true)) = true ↔ fracPart (w x) = M) := by
    intro x hbx
    rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
    have hbxc : (γ.1 x).val ≤ cmax x := by
      rw [hγ, regionFingerprint_floor]; exact (regionFloor_le_clamp_iff w x).mpr hbx
    constructor
    · rintro ⟨_, h2⟩
      have hbxMc : (γ.1 xM).val ≤ cmax xM := by
        rw [hγ, regionFingerprint_floor]; exact (regionFloor_le_clamp_iff w xM).mpr hxMb
      have h3 := h2 xM hbxMc
      rw [hγ, regionFingerprint_fracOrder, decide_eq_true_iff] at h3
      exact le_antisymm (hMmax x hbx) (by rw [← hxMf]; exact h3.2.2)
    · intro hfM
      refine ⟨hbxc, fun y hy => ?_⟩
      have hbndy : w y ≤ (cmax y : ℝ≥0) := by
        rw [hγ, regionFingerprint_floor] at hy; exact (regionFloor_le_clamp_iff w y).mp hy
      rw [hγ, regionFingerprint_fracOrder, decide_eq_true_iff]
      exact ⟨hbndy, hbx, by rw [hfM]; exact hMmax y hbndy⟩
  -- per-bounded-clock behaviour at δ: bounded after, floor/frac as wrap (frac=M) or not
  have hbeh : ∀ x, w x ≤ (cmax x : ℝ≥0) →
      (w.add δ) x ≤ (cmax x : ℝ≥0) ∧
      regionFloor cmax (w.add δ) x = ⌊w x⌋₊ + (if fracPart (w x) = M then 1 else 0) ∧
      fracPart ((w.add δ) x) = (if fracPart (w x) = M then 0 else fracPart (w x) + (δ : ℝ)) := by
    intro x hbx
    have hdecomp := coe_eq_floor_add_fracPart (w x)
    have hfl1 := hfllt x hbx
    by_cases hm : fracPart (w x) = M
    · have hwrap1 : (1 : ℝ) ≤ fracPart (w x) + (δ : ℝ) := by rw [hm, hδ]; linarith
      obtain ⟨hfr, hfl⟩ := fracPart_add_of_wrap hδ1 hwrap1
      have hbnd : (w.add δ) x ≤ (cmax x : ℝ≥0) := by
        rw [Valuation.add_apply]
        have hval : ((w x + δ : ℝ≥0) : ℝ) = (⌊w x⌋₊ : ℝ) + 1 := by
          rw [show ((w x + δ : ℝ≥0) : ℝ) = (w x : ℝ) + δ by push_cast; ring, hdecomp, hm, hδ]; ring
        have h2 : ((w x + δ : ℝ≥0) : ℝ) ≤ cmax x := by
          rw [hval]; exact_mod_cast Nat.succ_le_of_lt hfl1
        exact_mod_cast h2
      refine ⟨hbnd, ?_, ?_⟩
      · unfold regionFloor; rw [if_pos hbnd, Valuation.add_apply, hfl]; simp [hm]
      · rw [if_pos hm, Valuation.add_apply, hfr, hm, hδ]; ring
    · have hltM : fracPart (w x) < M := lt_of_le_of_ne (hMmax x hbx) hm
      have hnw : fracPart (w x) + (δ : ℝ) < 1 := by rw [hδ]; linarith
      obtain ⟨hfr, hfl⟩ := fracPart_add_of_no_wrap hnw
      have hbnd : (w.add δ) x ≤ (cmax x : ℝ≥0) := by
        rw [Valuation.add_apply]
        have hval : ((w x + δ : ℝ≥0) : ℝ) < (⌊w x⌋₊ : ℝ) + 1 := by
          rw [show ((w x + δ : ℝ≥0) : ℝ) = (w x : ℝ) + δ by push_cast; ring, hdecomp]; linarith
        have h2 : (⌊w x⌋₊ : ℝ) + 1 ≤ cmax x := by exact_mod_cast Nat.succ_le_of_lt hfl1
        have : ((w x + δ : ℝ≥0) : ℝ) ≤ cmax x := by linarith
        exact_mod_cast this
      refine ⟨hbnd, ?_, ?_⟩
      · unfold regionFloor; rw [if_pos hbnd, Valuation.add_apply, hfl]; simp [hm]
      · rw [if_neg hm, Valuation.add_apply, hfr]
  -- unbounded clocks: stay unbounded, and `isMax` is false there
  have hub : ∀ x, ¬ w x ≤ (cmax x : ℝ≥0) → ¬ (w.add δ) x ≤ (cmax x : ℝ≥0) := by
    intro x hx; rw [Valuation.add_apply]; exact fun hc => hx (le_trans le_self_add hc)
  have hMF : ∀ x, ¬ w x ≤ (cmax x : ℝ≥0) →
      (decide ((γ.1 x).val ≤ cmax x) &&
        decide (∀ y, (γ.1 y).val ≤ cmax y → γ.2.2 y x = true)) = false := by
    intro x hbx
    have hnb : ¬ ((γ.1 x).val ≤ cmax x) := by
      rw [hγ, regionFingerprint_floor, regionFloor_le_clamp_iff]; exact hbx
    rw [decide_eq_false_iff_not.mpr hnb, Bool.false_and]
  -- the floor reading on unbounded clocks before and after the delay (saturation sentinel)
  have hvalγU : ∀ x, ¬ w x ≤ (cmax x : ℝ≥0) → (γ.1 x).val = cmax x + 1 := by
    intro x hbx; rw [hγ, regionFingerprint_floor]; unfold regionFloor; rw [if_neg hbx]
  have hub_floor : ∀ x, ¬ w x ≤ (cmax x : ℝ≥0) → regionFloor cmax (w.add δ) x = cmax x + 1 := by
    intro x hbx; unfold regionFloor; rw [if_neg (hub x hbx)]
  -- the integral-saturation bit is false on bounded clocks, true on unbounded ones
  have hbsatF : ∀ x, w x ≤ (cmax x : ℝ≥0) → decide ((γ.1 x).val = cmax x + 1) = false := by
    intro x hbx; rw [decide_eq_false_iff_not, hvalγ x hbx]
    have := floor_le_of_le_cmax hbx; omega
  have husatT : ∀ x, ¬ w x ≤ (cmax x : ℝ≥0) → decide ((γ.1 x).val = cmax x + 1) = true := by
    intro x hbx; rw [decide_eq_true_iff, hvalγU x hbx]
  rw [Prod.ext_iff, Prod.ext_iff]
  refine ⟨funext fun x => ?_, funext fun x => ?_, funext fun x => funext fun y => ?_⟩
  · -- floor component
    apply Fin.ext
    rw [regionFingerprint_floor, regionCodeStep_caseC_fst hA hB x]
    by_cases hbx : w x ≤ (cmax x : ℝ≥0)
    · obtain ⟨_, hfl, _⟩ := hbeh x hbx
      rw [hfl]
      by_cases hm : fracPart (w x) = M
      · rw [if_pos hm, if_pos ((hisMaxChar x hbx).mpr hm), hvalγ x hbx]
        show ⌊w x⌋₊ + 1 = min (⌊w x⌋₊ + 1) (cmax x + 1)
        have := hfllt x hbx; omega
      · rw [if_neg hm, if_neg (fun h => hm ((hisMaxChar x hbx).mp h)), hvalγ x hbx]; omega
    · rw [if_neg (by simp [hMF x hbx]), hub_floor x hbx, hvalγU x hbx]
  · -- frac-zero component
    rw [regionFingerprint_fracZero, regionCodeStep_caseC_snd hA hB x]
    by_cases hbx : w x ≤ (cmax x : ℝ≥0)
    · obtain ⟨hbnd, _, hfr⟩ := hbeh x hbx
      by_cases hm : fracPart (w x) = M
      · rw [(hisMaxChar x hbx).mpr hm]
        exact decide_eq_true_iff.mpr ⟨hbnd, by rw [hfr, if_pos hm]⟩
      · have hcf : (decide ((γ.1 x).val ≤ cmax x) &&
            decide (∀ y, (γ.1 y).val ≤ cmax y → γ.2.2 y x = true)) = false := by
          cases hc : (decide ((γ.1 x).val ≤ cmax x) &&
              decide (∀ y, (γ.1 y).val ≤ cmax y → γ.2.2 y x = true)) with
          | false => rfl
          | true => exact absurd ((hisMaxChar x hbx).mp hc) hm
        rw [hcf]
        refine decide_eq_false_iff_not.mpr ?_
        rintro ⟨_, hz⟩; rw [hfr, if_neg hm] at hz
        have := fracPart_nonneg (w x); linarith
    · rw [hMF x hbx]
      exact decide_eq_false_iff_not.mpr (fun ⟨hb, _⟩ => hub x hbx hb)
  · -- frac-order component
    rw [regionFingerprint_fracOrder, regionCodeStep_caseC_thd hA hB x y]
    by_cases hbx : w x ≤ (cmax x : ℝ≥0)
    · by_cases hby : w y ≤ (cmax y : ℝ≥0)
      · -- both clocks bounded
        rw [if_neg (by simp [hbsatF x hbx, hbsatF y hby])]
        obtain ⟨hbndx, _, hfrx⟩ := hbeh x hbx
        obtain ⟨hbndy, _, hfry⟩ := hbeh y hby
        by_cases hmx : fracPart (w x) = M
        · rw [if_pos ((hisMaxChar x hbx).mpr hmx)]
          exact decide_eq_true_iff.mpr
            ⟨hbndx, hbndy, by rw [hfrx, if_pos hmx]; exact fracPart_nonneg _⟩
        · rw [if_neg (fun h => hmx ((hisMaxChar x hbx).mp h))]
          by_cases hmy : fracPart (w y) = M
          · rw [if_pos ((hisMaxChar y hby).mpr hmy)]
            refine decide_eq_false_iff_not.mpr ?_
            rintro ⟨_, _, hle⟩; rw [hfrx, if_neg hmx, hfry, if_pos hmy] at hle
            have := fracPart_nonneg (w x); linarith
          · rw [if_neg (fun h => hmy ((hisMaxChar y hby).mp h)), hγ, regionFingerprint_fracOrder,
              decide_eq_decide]
            constructor
            · rintro ⟨_, _, hle⟩; rw [hfrx, if_neg hmx, hfry, if_neg hmy] at hle
              exact ⟨hbx, hby, by linarith⟩
            · rintro ⟨_, _, hle⟩
              refine ⟨hbndx, hbndy, ?_⟩; rw [hfrx, if_neg hmx, hfry, if_neg hmy]; linarith
      · -- x bounded, y unbounded
        rw [if_pos (by rw [hbsatF x hbx, husatT y hby, Bool.false_or])]
        exact decide_eq_false_iff_not.mpr (fun ⟨_, hb, _⟩ => hub y hby hb)
    · -- x unbounded
      rw [if_pos (by rw [husatT x hbx, Bool.true_or])]
      exact decide_eq_false_iff_not.mpr (fun ⟨hb, _, _⟩ => hub x hbx hb)

omit [DecidableEq C] in
open Classical in
/-- **At any small delay, an integral region steps.** With some bounded clock integral
(case B) and a delay `δ` positive but carrying no bounded clock past the next integer, the
integral clocks gain a tiny positive fraction (those at `cmax` saturate), and `fp (w + δ) =
regionCodeStep (fp w)`. The case-B analogue of `regionFingerprint_add_eq_step_caseC`. -/
theorem regionFingerprint_add_eq_step_caseB {cmax : C → ℕ} {w : Valuation C}
    (hI : ∃ x, w x ≤ (cmax x : ℝ≥0) ∧ fracPart (w x) = 0)
    {δ : ℝ≥0} (hδ0 : (0 : ℝ) < δ)
    (hnw : ∀ x, w x ≤ (cmax x : ℝ≥0) → fracPart (w x) + (δ : ℝ) < 1) :
    regionFingerprint cmax (w.add δ) = regionCodeStep (regionFingerprint cmax w) := by
  set γ := regionFingerprint cmax w with hγ
  have hA : ¬ ∀ x, (γ.1 x).val = cmax x + 1 := by
    obtain ⟨x, hbx, _⟩ := hI
    intro hall; have h1 := hall x; rw [hγ, regionFingerprint_floor] at h1
    have := (regionFloor_le_clamp_iff w x).mpr hbx; omega
  have hB : ∃ x, γ.2.1 x = true := by
    obtain ⟨x, hbx, hfx⟩ := hI
    exact ⟨x, by rw [hγ, regionFingerprint_fracZero, decide_eq_true_iff]; exact ⟨hbx, hfx⟩⟩
  have hvalγ : ∀ x, w x ≤ (cmax x : ℝ≥0) → (γ.1 x).val = ⌊w x⌋₊ := by
    intro x hbx; rw [hγ, regionFingerprint_floor]; unfold regionFloor; rw [if_pos hbx]
  have hvalγU : ∀ x, ¬ w x ≤ (cmax x : ℝ≥0) → (γ.1 x).val = cmax x + 1 := by
    intro x hbx; rw [hγ, regionFingerprint_floor]; unfold regionFloor; rw [if_neg hbx]
  have hfzγ : ∀ x, w x ≤ (cmax x : ℝ≥0) → γ.2.1 x = decide (fracPart (w x) = 0) := by
    intro x hbx; rw [hγ, regionFingerprint_fracZero, decide_eq_decide]; exact and_iff_right hbx
  -- unbounded clocks stay unbounded
  have hub : ∀ x, ¬ w x ≤ (cmax x : ℝ≥0) → ¬ (w.add δ) x ≤ (cmax x : ℝ≥0) := by
    intro x hbx; rw [Valuation.add_apply]; exact fun hc => hbx (le_trans le_self_add hc)
  -- integral-at-`cmax` clocks become unbounded
  have hcat : ∀ x, w x = (cmax x : ℝ≥0) → ¬ (w.add δ) x ≤ (cmax x : ℝ≥0) := by
    intro x hwx hc; rw [Valuation.add_apply, hwx] at hc
    have := (NNReal.coe_le_coe.mpr hc); push_cast at this; linarith
  -- all other bounded clocks stay bounded, floor unchanged, fraction shifted by `δ`
  have hother : ∀ x, w x ≤ (cmax x : ℝ≥0) → w x ≠ (cmax x : ℝ≥0) →
      (w.add δ) x ≤ (cmax x : ℝ≥0) ∧ regionFloor cmax (w.add δ) x = ⌊w x⌋₊ ∧
        fracPart ((w.add δ) x) = fracPart (w x) + (δ : ℝ) := by
    intro x hbx hne
    obtain ⟨hfr, hfl⟩ := fracPart_add_of_no_wrap (hnw x hbx)
    have hdecomp := coe_eq_floor_add_fracPart (w x)
    have hlt : (w x : ℝ) < cmax x := by
      rcases lt_or_eq_of_le (show (w x : ℝ) ≤ cmax x from by exact_mod_cast hbx) with h | h
      · exact h
      · exact absurd (by exact_mod_cast h : w x = (cmax x : ℝ≥0)) hne
    have hfllt : ⌊w x⌋₊ < cmax x := by
      have h2 : (⌊w x⌋₊ : ℝ) < cmax x := lt_of_le_of_lt (Nat.floor_le (zero_le' (a := w x))) hlt
      exact_mod_cast h2
    have hbnd : (w.add δ) x ≤ (cmax x : ℝ≥0) := by
      rw [Valuation.add_apply]
      have hval : ((w x + δ : ℝ≥0) : ℝ) < (⌊w x⌋₊ : ℝ) + 1 := by
        rw [show ((w x + δ : ℝ≥0) : ℝ) = (w x : ℝ) + δ by push_cast; ring, hdecomp]
        have := hnw x hbx; linarith
      have h2 : (⌊w x⌋₊ : ℝ) + 1 ≤ cmax x := by exact_mod_cast Nat.succ_le_of_lt hfllt
      have : ((w x + δ : ℝ≥0) : ℝ) ≤ cmax x := by linarith
      exact_mod_cast this
    refine ⟨hbnd, ?_, by rw [Valuation.add_apply]; exact hfr⟩
    unfold regionFloor; rw [if_pos hbnd, Valuation.add_apply, hfl]
  -- bounded-after clocks: bounded before, not at `cmax`
  have hbb : ∀ x, (w.add δ) x ≤ (cmax x : ℝ≥0) →
      w x ≤ (cmax x : ℝ≥0) ∧ w x ≠ (cmax x : ℝ≥0) := by
    intro x hb
    have hbef : w x ≤ (cmax x : ℝ≥0) := by
      rw [Valuation.add_apply] at hb; exact le_trans le_self_add hb
    exact ⟨hbef, fun heq => hcat x heq hb⟩
  -- `nowSat` characterizes exactly the clocks unbounded after the delay
  have hnowSat : ∀ x,
      ((decide ((γ.1 x).val = cmax x + 1) || (γ.2.1 x && decide ((γ.1 x).val = cmax x))) = true
        ↔ ¬ (w.add δ) x ≤ (cmax x : ℝ≥0)) := by
    intro x
    rw [Bool.or_eq_true, decide_eq_true_iff, Bool.and_eq_true, decide_eq_true_iff]
    by_cases hbx : w x ≤ (cmax x : ℝ≥0)
    · rw [hvalγ x hbx]
      have hflle : ⌊w x⌋₊ ≤ cmax x := floor_le_of_le_cmax hbx
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact absurd h (by omega)
        · have hfrac : fracPart (w x) = 0 := by
            rw [hfzγ x hbx] at h1; exact decide_eq_true_iff.mp h1
          have hwx : w x = (cmax x : ℝ≥0) := by
            rw [← (fracPart_eq_zero_iff (w x)).mp hfrac, h2]
          exact hcat x hwx
      · intro hub_after
        have hwx : w x = (cmax x : ℝ≥0) := by
          by_contra hne; exact hub_after (hother x hbx hne).1
        refine Or.inr ⟨?_, ?_⟩
        · rw [hfzγ x hbx, hwx]; exact decide_eq_true_iff.mpr (fracPart_natCast (cmax x))
        · rw [hwx]; exact Nat.floor_natCast (cmax x)
    · refine ⟨fun _ => hub x hbx, fun _ => Or.inl (hvalγU x hbx)⟩
  -- `nowSmall` characterizes the bounded-after integral (below-`cmax`) clocks
  have hnowSmall : ∀ x, (w.add δ) x ≤ (cmax x : ℝ≥0) →
      ((γ.2.1 x && decide ((γ.1 x).val < cmax x)) = true ↔ fracPart (w x) = 0) := by
    intro x hb
    obtain ⟨hbx, hne⟩ := hbb x hb
    have hfllt : ⌊w x⌋₊ < cmax x := by
      have hlt : (w x : ℝ) < cmax x := by
        rcases lt_or_eq_of_le (show (w x : ℝ) ≤ cmax x from by exact_mod_cast hbx) with h | h
        · exact h
        · exact absurd (by exact_mod_cast h : w x = (cmax x : ℝ≥0)) hne
      have h2 : (⌊w x⌋₊ : ℝ) < cmax x := lt_of_le_of_lt (Nat.floor_le (zero_le' (a := w x))) hlt
      exact_mod_cast h2
    rw [Bool.and_eq_true, decide_eq_true_iff, hfzγ x hbx, hvalγ x hbx, decide_eq_true_iff]
    exact and_iff_left hfllt
  -- bounded-after clocks: fraction is exactly `frac (w x) + δ`
  have hfrAfter : ∀ x, (w.add δ) x ≤ (cmax x : ℝ≥0) →
      fracPart ((w.add δ) x) = fracPart (w x) + (δ : ℝ) := by
    intro x hb; obtain ⟨hbx, hne⟩ := hbb x hb; exact (hother x hbx hne).2.2
  rw [Prod.ext_iff, Prod.ext_iff]
  refine ⟨funext fun x => ?_, funext fun x => ?_, funext fun x => funext fun y => ?_⟩
  · -- floor component
    apply Fin.ext
    rw [regionFingerprint_floor, regionCodeStep_caseB_fst hA hB x]
    by_cases hb : (w.add δ) x ≤ (cmax x : ℝ≥0)
    · rw [if_neg (fun h => (hnowSat x).mp h hb)]
      obtain ⟨hbx, hne⟩ := hbb x hb
      rw [(hother x hbx hne).2.1, hvalγ x hbx]
    · rw [if_pos ((hnowSat x).mpr hb)]
      show regionFloor cmax (w.add δ) x = min (cmax x + 1) (cmax x + 1)
      unfold regionFloor; rw [if_neg hb]; omega
  · -- frac-zero component
    rw [regionFingerprint_fracZero, regionCodeStep_caseB_snd hA hB x]
    refine decide_eq_false_iff_not.mpr ?_
    rintro ⟨hb, hz⟩
    rw [hfrAfter x hb] at hz
    have := fracPart_nonneg (w x); linarith
  · -- frac-order component
    rw [regionFingerprint_fracOrder, regionCodeStep_caseB_thd hA hB x y]
    by_cases hbx : (w.add δ) x ≤ (cmax x : ℝ≥0)
    · by_cases hby : (w.add δ) y ≤ (cmax y : ℝ≥0)
      · rw [if_neg (by
          rw [Bool.or_eq_true]
          rintro (h | h)
          · exact (hnowSat x).mp h hbx
          · exact (hnowSat y).mp h hby)]
        have hfx := hfrAfter x hbx
        have hfy := hfrAfter y hby
        by_cases hsx : fracPart (w x) = 0
        · rw [if_pos ((hnowSmall x hbx).mpr hsx)]
          refine decide_eq_true_iff.mpr ⟨hbx, hby, ?_⟩
          rw [hfx, hfy, hsx]; have := fracPart_nonneg (w y); linarith
        · rw [if_neg (fun h => hsx ((hnowSmall x hbx).mp h))]
          by_cases hsy : fracPart (w y) = 0
          · rw [if_pos ((hnowSmall y hby).mpr hsy)]
            refine decide_eq_false_iff_not.mpr ?_
            rintro ⟨_, _, hle⟩; rw [hfx, hfy, hsy] at hle
            have hpos : 0 < fracPart (w x) := lt_of_le_of_ne (fracPart_nonneg _) (Ne.symm hsx)
            linarith
          · rw [if_neg (fun h => hsy ((hnowSmall y hby).mp h)), hγ, regionFingerprint_fracOrder,
              decide_eq_decide]
            obtain ⟨hbx', _⟩ := hbb x hbx
            obtain ⟨hby', _⟩ := hbb y hby
            constructor
            · rintro ⟨_, _, hle⟩; rw [hfx, hfy] at hle; exact ⟨hbx', hby', by linarith⟩
            · rintro ⟨_, _, hle⟩; refine ⟨hbx, hby, ?_⟩; rw [hfx, hfy]; linarith
      · rw [if_pos (by
          rw [Bool.or_eq_true]; exact Or.inr ((hnowSat y).mpr hby))]
        exact decide_eq_false_iff_not.mpr (fun ⟨_, hb, _⟩ => hby hb)
    · rw [if_pos (by rw [Bool.or_eq_true]; exact Or.inl ((hnowSat x).mpr hbx))]
      exact decide_eq_false_iff_not.mpr (fun ⟨hb, _, _⟩ => hbx hb)

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
open Classical in
/-- **Case B decreases the measure.** When some clock is bounded integral, the elapse step
clears every frac-zero bit (count to `0`) and saturates the integral-at-`cₓ` clocks (room
down), a strict drop of at least the integral count `≥ 1`. -/
theorem codeMeasure_step_lt_caseB {cmax : C → ℕ} {w : Valuation C}
    (hbnd : ∃ x, w x ≤ (cmax x : ℝ≥0))
    (hI : ∃ x, w x ≤ (cmax x : ℝ≥0) ∧ fracPart (w x) = 0) :
    codeMeasure (regionCodeStep (regionFingerprint cmax w))
      < codeMeasure (regionFingerprint cmax w) := by
  set γ := regionFingerprint cmax w with hγ
  set intAtMax : C → Bool := fun x => γ.2.1 x && decide ((γ.1 x).val = cmax x) with hiam
  have hA : ¬ ∀ x, (γ.1 x).val = cmax x + 1 := by
    obtain ⟨x, hx⟩ := hbnd
    intro hall; have h1 := hall x; rw [hγ, regionFingerprint_floor] at h1
    have h2 := (regionFloor_le_clamp_iff w x).mpr hx; omega
  have hBex : ∃ x, γ.2.1 x = true := by
    obtain ⟨x, hbx, hfx⟩ := hI
    exact ⟨x, by rw [hγ, regionFingerprint_fracZero, decide_eq_true_iff]; exact ⟨hbx, hfx⟩⟩
  have hroom : ∀ x, cmax x + 1 - (γ.1 x).val =
      (cmax x + 1 - ((regionCodeStep γ).1 x).val) + (if intAtMax x = true then 1 else 0) := by
    intro x
    rw [regionCodeStep_caseB_fst hA hBex x]
    by_cases hns : (decide ((γ.1 x).val = cmax x + 1) ||
        (γ.2.1 x && decide ((γ.1 x).val = cmax x))) = true
    · rw [if_pos hns]
      have hbf : (bumpFloor cmax x (cmax x + 1)).val = min (cmax x + 1) (cmax x + 1) := rfl
      rw [hbf]
      by_cases hia : intAtMax x = true
      · rw [if_pos hia]
        have hfeq : (γ.1 x).val = cmax x := by
          rw [hiam, Bool.and_eq_true, decide_eq_true_iff] at hia; exact hia.2
        omega
      · rw [if_neg hia]
        have hsat : (γ.1 x).val = cmax x + 1 := by
          rw [Bool.or_eq_true, decide_eq_true_iff] at hns
          rcases hns with h | h
          · exact h
          · exact absurd h (by rw [hiam] at hia; exact hia)
        omega
    · rw [if_neg hns]
      have hia : intAtMax x ≠ true := by
        rw [hiam]; intro hc; exact hns (by rw [Bool.or_eq_true]; exact Or.inr hc)
      rw [if_neg hia]; omega
  have hintγ : 0 < (Finset.univ.filter (fun x => γ.2.1 x = true)).card := by
    rw [Finset.card_pos]; obtain ⟨x, hx⟩ := hBex
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  have hintstep : (Finset.univ.filter (fun x => (regionCodeStep γ).2.1 x = true)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]; intro x _
    rw [regionCodeStep_caseB_snd hA hBex x]; simp
  have hsum : (∑ x, (cmax x + 1 - (γ.1 x).val)) =
      (∑ x, (cmax x + 1 - ((regionCodeStep γ).1 x).val)) +
        (Finset.univ.filter (fun x => intAtMax x = true)).card := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => hroom x)
  unfold codeMeasure
  rw [hintstep, Finset.card_empty, hsum]
  omega

omit [DecidableEq C] in
/-- **The descent measure strictly decreases at every non-fixpoint region.** Combines cases B
and C; a non-fixpoint region is bounded somewhere (else it is saturated, a fixpoint), and
either has an integral clock (case B) or not (case C). -/
theorem codeMeasure_step_lt {cmax : C → ℕ} {w : Valuation C}
    (h : regionCodeStep (regionFingerprint cmax w) ≠ regionFingerprint cmax w) :
    codeMeasure (regionCodeStep (regionFingerprint cmax w))
      < codeMeasure (regionFingerprint cmax w) := by
  have hbnd : ∃ x, w x ≤ (cmax x : ℝ≥0) := by
    by_contra hc
    apply h
    simp only [not_exists, not_le] at hc
    have heq := regionCodeStep_sound_allUnbounded hc
    rw [Valuation.add_zero] at heq
    exact heq.symm
  by_cases hI : ∃ x, w x ≤ (cmax x : ℝ≥0) ∧ fracPart (w x) = 0
  · exact codeMeasure_step_lt_caseB hbnd hI
  · simp only [not_exists, not_and] at hI
    exact codeMeasure_step_lt_caseC hbnd hI

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
