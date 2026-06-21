import DeepWiki.ReactiveSystems.TimedSqrt2FullRel

/-! # The `√2` Mt-bisimulation, step 5: toward the coupled (single-irrational-cut) live relation

`Sq2FullRel` proves five of the six `IsMtBisimulation` clauses — including the entire crossing/past
regime (`delay_cross`) — but its live regime is **insufficient**: it tracks the process-to-clock
relationship only at the *integer* level (`AsymMatch` on crossing-values), with no information on the
process's *fractional* position relative to the clocks. So the clock time-successor's `δ'` need not
place the process within reach of the τ-target, and the live-stay clause cannot close. The fix is the
**single-irrational-cut region in crossing-value coordinates**: region-equivalence on the *combined*
valuation `[clocks u] ∪ [crossing-values cv d u] ∪ [τ = √2 − d]`.

This file fixes the combined valuation `combVal` (sound infrastructure). The *coupling* condition on
its fractional orderings is the delicate part and is **still under design** — see the warning below.

## DESIGN NOTE — the frac-orderings are ASYMMETRIC, not symmetric (finding 2026-06-21)

A first attempt stated the coupling as *symmetric* combined frac-orderings (`∀ i j, frac(combVal d u i)
≤ frac(combVal d u j) ↔ frac(combVal e u' i) ≤ frac(combVal e u' j)`). **This is wrong**, and is in fact
contradictory with the asymmetric crossing cuts at any coincidence:

* Trace the **reset** clause. After resetting clock `x`, the reset clock has frac `0`, so the ordering
  `frac(cv d u y) ≤ frac(reset) = 0` tests `frac(cv d u y) = 0` — i.e. whether crossing `y` is at an
  integer (a coincidence). At such a coincidence `AsymMatch (cv d u y = m) (cv e u' y)` forces
  `cv e u' y < m`, hence `frac(cv e u' y) ≠ 0`. So the A side is `0 ≤ 0` (true) while the B side is
  `frac(cv e u' y) ≤ 0` (false) — symmetric orderings demand a match that fails.
* Equivalently, `AsymMatch` puts B's crossing *infinitesimally below* A's: when `cv d u y = m`
  (frac `0`, floor `m`), B's `cv e u' y ≈ m⁻` (frac `≈ 1`, floor `m − 1`). A's and B's crossings sit in
  *different cells*, so the frac-orderings cannot be compared symmetrically.

So the coupling must treat crossings asymmetrically (B's crossings tie-broken/shifted down). Candidate
formulation to **paper-verify before coding**: `∃ η > 0` (small), `RegionEqAll (A's combined with
crossings shifted down by η) (B's combined)` — encoding "B's crossings = A's, infinitesimally below".
Sanity checks so far: seed (A = B) holds for small η; reset is plausibly preserved because a reset
clock's crossing lands on τ exactly (the `inr none` coordinate), which already matched. Full
clause-by-clause verification (especially the live delay) is pending; the symmetric version above is a
dead end and must not be reinstated. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- **`AsymMatch` from a floor-shift family.** If for every sufficiently small `η > 0` the shifted
floor `⌊c − η⌋₊` equals `⌊c'⌋₊` (and `c > 0`), then `AsymMatch c c'`. This is the bridge from the
coupled relation's `∃ small η, RegionEqAll (combShift …)` to `Sq2FRel`'s `AsymMatch`: the floor of
`c − η` is `⌊c⌋` off integers and `⌊c⌋ − 1` at integers, exactly `AsymMatch`'s content. -/
theorem asymMatch_of_floor_shift {c c' : ℝ≥0} {η₀ : ℝ≥0} (hc : 0 < c) (hη₀ : 0 < η₀)
    (h : ∀ η : ℝ≥0, 0 < η → η < η₀ → ⌊c - η⌋₊ = ⌊c'⌋₊) : AsymMatch c c' := by
  have hη₁pos : (0 : ℝ≥0) < η₀ / 2 := half_pos hη₀
  have hfl₁ : ⌊c - η₀ / 2⌋₊ = ⌊c'⌋₊ := h _ hη₁pos (NNReal.half_lt_self hη₀.ne')
  intro m
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · obtain ⟨η, hηpos, hηlt, hηcm⟩ :
        ∃ η : ℝ≥0, 0 < η ∧ η < η₀ ∧ η ≤ c - (m : ℝ≥0) := by
      have hmpos : (0 : ℝ≥0) < min η₀ (c - (m : ℝ≥0)) := lt_min hη₀ (tsub_pos_of_lt hm)
      refine ⟨min η₀ (c - (m : ℝ≥0)) / 2, half_pos hmpos, ?_, ?_⟩
      · exact lt_of_lt_of_le (NNReal.half_lt_self hmpos.ne') (min_le_left _ _)
      · exact le_of_lt (lt_of_lt_of_le (NNReal.half_lt_self hmpos.ne') (min_le_right _ _))
    have hsum : (m : ℝ≥0) + η ≤ c := by
      calc (m : ℝ≥0) + η ≤ (m : ℝ≥0) + (c - (m : ℝ≥0)) := by gcongr
        _ = c := add_tsub_cancel_of_le (le_of_lt hm)
    have hmf : m ≤ ⌊c - η⌋₊ := Nat.le_floor (le_tsub_of_add_le_right hsum)
    rw [h η hηpos hηlt] at hmf
    exact le_trans (by exact_mod_cast hmf) (Nat.floor_le zero_le)
  · have hmf : m ≤ ⌊c'⌋₊ := Nat.le_floor hm
    rw [← hfl₁] at hmf
    exact lt_of_le_of_lt (le_trans (by exact_mod_cast hmf) (Nat.floor_le zero_le))
      (tsub_lt_self hc hη₁pos)

/-- Fractional orderings agree under region equivalence (unconditional form, via an arbitrarily large
`cmax`): companion to `regionEqAll_floor_eq`. -/
theorem regionEqAll_fracOrder {D : Type*} {V V' : Valuation D} (h : RegionEqAll V V') (x y : D) :
    fracPart (V x) ≤ fracPart (V y) ↔ fracPart (V' x) ≤ fracPart (V' y) := by
  obtain ⟨_, _, h3⟩ := h (fun z => ⌊V z⌋₊ + ⌊V' z⌋₊ + 1)
  have hb : ∀ z, V z ≤ ((⌊V z⌋₊ + ⌊V' z⌋₊ + 1 : ℕ) : ℝ≥0) := fun z =>
    le_of_lt (lt_of_lt_of_le (Nat.lt_floor_add_one (V z))
      (by exact_mod_cast (Nat.le_add_right (⌊V z⌋₊ + 1) (⌊V' z⌋₊)).trans_eq (by ring)))
  exact h3 x y (hb x) (hb y)

namespace TLTS

/-- The **combined valuation** over `D ⊕ Option D`: the formula clocks (`inl y ↦ u y`), the per-clock
crossing-values (`inr (some y) ↦ cv d u y`), and the process's own crossing-value `τ = √2 − d`
(`inr none`). The single-irrational-cut region is region-equivalence on this combined valuation, with
the `inr` (crossing / τ) coordinates carrying *asymmetric* integer cuts and tie-broken-down
fractional orderings (see the design note). -/
noncomputable def combVal {D : Type*} (d : ℝ≥0) (u : Valuation D) : D ⊕ Option D → ℝ≥0
  | Sum.inl y => u y
  | Sum.inr (some y) => cv d u y
  | Sum.inr none => sqrt2NN - d

@[simp] theorem combVal_inl {D : Type*} (d : ℝ≥0) (u : Valuation D) (y : D) :
    combVal d u (Sum.inl y) = u y := rfl

@[simp] theorem combVal_inr_some {D : Type*} (d : ℝ≥0) (u : Valuation D) (y : D) :
    combVal d u (Sum.inr (some y)) = cv d u y := rfl

@[simp] theorem combVal_inr_none {D : Type*} (d : ℝ≥0) (u : Valuation D) :
    combVal d u (Sum.inr none) = sqrt2NN - d := rfl

/-- A reset clock lands its crossing-value exactly on `τ`: `cv d (u.reset {x}) x = √2 − d`. This is the
identity that makes the reset clause clean in crossing-value coordinates (the reset clock's crossing
coincides with the τ-coordinate, so no spurious asymmetry is introduced). -/
theorem cv_reset_self {D : Type*} [DecidableEq D] (d : ℝ≥0) (u : Valuation D) (x : D) :
    cv d (Valuation.reset {x} u) x = sqrt2NN - d := by
  rw [cv_apply, Valuation.reset_mem (Set.mem_singleton x) u, zero_add]

/-- The combined valuation with the crossing/τ coordinates (`inr`) shifted **down** by `η`; the clock
coordinates (`inl`) are untouched. As `η → 0⁺` this encodes "B's crossings are A's, infinitesimally
below" — the asymmetric (open A / closed B) √2-cut. -/
noncomputable def combShift {D : Type*} (d : ℝ≥0) (u : Valuation D) (η : ℝ≥0) : D ⊕ Option D → ℝ≥0
  | Sum.inl y => u y
  | Sum.inr c => combVal d u (Sum.inr c) - η

@[simp] theorem combShift_inl {D : Type*} (d : ℝ≥0) (u : Valuation D) (η : ℝ≥0) (y : D) :
    combShift d u η (Sum.inl y) = u y := rfl

@[simp] theorem combShift_inr {D : Type*} (d : ℝ≥0) (u : Valuation D) (η : ℝ≥0) (c : Option D) :
    combShift d u η (Sum.inr c) = combVal d u (Sum.inr c) - η := rfl

/-- The **coupled live relation** (single-irrational-cut region, crossing-value coordinates): the
clock region (via the `inl` part), the asymmetric √2-cuts and the frac-ordering coupling are *all*
captured by requiring that for every sufficiently small `η > 0`, A's combined valuation with its
crossings shifted **down** by `η` is region-equivalent to B's combined valuation. The `∀` small-`η`
form makes the witness robustly infinitesimal (so it implies the asymmetric crossing-match
`AsymMatch`, by the floor argument: `⌊cv − η⌋ = ⌊cv⌋` off integers, `⌊cv⌋ − 1` at integers). -/
def Sq2CoupledFRel {D : Type*} (d : ℝ≥0) (u : Valuation D) (e : ℝ≥0) (u' : Valuation D) : Prop :=
  d < sqrt2NN ∧ e ≤ sqrt2NN ∧
    ∃ η₀ : ℝ≥0, 0 < η₀ ∧ ∀ η : ℝ≥0, 0 < η → η < η₀ →
      RegionEqAll (combShift d u η) (combVal e u')

/-- The coupled `√2` relation: past regime (both `a`-disabled, clocks region-equivalent) or the
coupled live regime. -/
def Sq2CoupledRel {D : Type*} (p : Sq2) (u : Valuation D) (q : Sq2) (u' : Valuation D) : Prop :=
  (aDisabled sqrt2NN p ∧ aDisabled sqrt2NN q ∧ RegionEqAll u u')
  ∨ (∃ d e : ℝ≥0, p = Sq2.A d ∧ q = Sq2.B e ∧ Sq2CoupledFRel d u e u')

/-- **The seed** `(A 0, 0) ~ (B 0, 0)`: A and B coincide, every crossing-value is `√2`
(frac `√2 − 1 ≠ 0`, no coincidence), so shifting A's crossings down by any `η < √2 − 1` keeps the
combined region — the relation relates the initial states. -/
theorem sq2CoupledRel_seed {D : Type*} :
    Sq2CoupledRel (Sq2.A 0) (fun _ : D => 0) (Sq2.B 0) (fun _ : D => 0) := by
  have h1lt : (1 : ℝ≥0) < sqrt2NN := by rw [← NNReal.coe_lt_coe]; push_cast; exact one_lt_sqrt2NN
  have h2 : sqrt2NN < (2 : ℝ≥0) := by
    rw [← NNReal.coe_lt_coe]; push_cast; exact sqrt2NN_lt_two
  have hfrac0 : fracPart (0 : ℝ≥0) = 0 := by simp [fracPart]
  have hcombVal_inr : ∀ c : Option D, combVal (0 : ℝ≥0) (fun _ : D => 0) (Sum.inr c) = sqrt2NN := by
    intro c; cases c <;> simp
  refine Or.inr ⟨0, 0, rfl, rfl, zero_lt_sqrt2NN, le_of_lt zero_lt_sqrt2NN, sqrt2NN - 1, ?_, ?_⟩
  · rw [tsub_pos_iff_lt]; exact h1lt
  · intro η _ hη
    have hgt1 : 1 < sqrt2NN - η := by
      rw [lt_tsub_iff_right, add_comm]; rw [lt_tsub_iff_right] at hη; exact hη
    have hlt2 : sqrt2NN - η < 2 := lt_of_le_of_lt tsub_le_self h2
    have hfloor : ⌊sqrt2NN - η⌋₊ = 1 := by
      apply floor_eq_of_mem
      · exact_mod_cast le_of_lt hgt1
      · rw [Nat.cast_one, show (1 : ℝ≥0) + 1 = 2 from by norm_num]; exact hlt2
    have hfrne : fracPart (sqrt2NN - η) ≠ 0 := by
      intro hc; rw [fracPart_eq_zero_iff, hfloor, Nat.cast_one] at hc; exact ne_of_lt hgt1 hc
    have hfrpos : 0 < fracPart (sqrt2NN - η) := lt_of_le_of_ne (fracPart_nonneg _) (Ne.symm hfrne)
    have hfrpos2 : 0 < fracPart sqrt2NN :=
      lt_of_le_of_ne (fracPart_nonneg _) (Ne.symm fracPart_sqrt2NN_ne_zero)
    apply regionEqAll_of_exact
    · rintro (y | c)
      · rfl
      · simp only [combShift_inr, hcombVal_inr, hfloor, floor_sqrt2NN]
    · rintro (y | c)
      · exact Iff.rfl
      · simp only [combShift_inr, hcombVal_inr]
        exact ⟨fun h => absurd h hfrne, fun h => absurd h fracPart_sqrt2NN_ne_zero⟩
    · rintro (y | c) (z | c')
      · exact Iff.rfl
      · simp only [combShift_inl, combShift_inr, combVal_inl, hcombVal_inr, hfrac0]
        exact ⟨fun _ => fracPart_nonneg _, fun _ => fracPart_nonneg _⟩
      · simp only [combShift_inl, combShift_inr, combVal_inl, hcombVal_inr, hfrac0]
        exact ⟨fun h => absurd (lt_of_lt_of_le hfrpos h) (lt_irrefl _),
          fun h => absurd (lt_of_lt_of_le hfrpos2 h) (lt_irrefl _)⟩
      · simp only [combShift_inr, hcombVal_inr]
        exact ⟨fun _ => le_refl _, fun _ => le_refl _⟩

/-- **The combined reset preserves region equivalence.** Resetting clock `x` sends the combined
valuation's `inl x` coordinate to `0` and its `inr (some x)` coordinate to `τ = V (inr none)`
(`cv_reset_self`), leaving the rest unchanged; so it reduces to the original match under the remap
`inr (some x) ↦ inr none`, with the frac-`0` `inl x` coordinate handled by frac-zero. -/
theorem combReset_regionEqAll {D : Type*} [DecidableEq D] {d e η : ℝ≥0} {u u' : Valuation D} (x : D)
    (hr : RegionEqAll (combShift d u η) (combVal e u')) :
    RegionEqAll (combShift d (Valuation.reset {x} u) η) (combVal e (Valuation.reset {x} u')) := by
  have hWlx : combShift d (Valuation.reset {x} u) η (Sum.inl x) = 0 := by
    rw [combShift_inl, Valuation.reset_mem (Set.mem_singleton x)]
  have hW'lx : combVal e (Valuation.reset {x} u') (Sum.inl x) = 0 := by
    rw [combVal_inl, Valuation.reset_mem (Set.mem_singleton x)]
  have hWsx : combShift d (Valuation.reset {x} u) η (Sum.inr (some x))
      = combShift d u η (Sum.inr none) := by
    simp only [combShift_inr, combVal_inr_some, combVal_inr_none, cv_reset_self]
  have hW'sx : combVal e (Valuation.reset {x} u') (Sum.inr (some x)) = combVal e u' (Sum.inr none) := by
    simp only [combVal_inr_some, combVal_inr_none, cv_reset_self]
  have hWnone : combShift d (Valuation.reset {x} u) η (Sum.inr none) = combShift d u η (Sum.inr none) := by
    simp only [combShift_inr, combVal_inr_none]
  have hW'none : combVal e (Valuation.reset {x} u') (Sum.inr none) = combVal e u' (Sum.inr none) := by
    simp only [combVal_inr_none]
  have hWy : ∀ y, y ≠ x →
      combShift d (Valuation.reset {x} u) η (Sum.inl y) = combShift d u η (Sum.inl y)
      ∧ combVal e (Valuation.reset {x} u') (Sum.inl y) = combVal e u' (Sum.inl y) := by
    intro y hy
    have hy' : y ∉ ({x} : Set D) := fun h => hy (Set.mem_singleton_iff.mp h)
    simp only [combShift_inl, combVal_inl, Valuation.reset_not_mem hy', and_self]
  have hWsy : ∀ y, y ≠ x →
      combShift d (Valuation.reset {x} u) η (Sum.inr (some y)) = combShift d u η (Sum.inr (some y))
      ∧ combVal e (Valuation.reset {x} u') (Sum.inr (some y)) = combVal e u' (Sum.inr (some y)) := by
    intro y hy
    have hy' : y ∉ ({x} : Set D) := fun h => hy (Set.mem_singleton_iff.mp h)
    simp only [combShift_inr, combVal_inr_some, cv_apply, Valuation.reset_not_mem hy', and_self]
  -- Per-coordinate floor and frac-zero match.
  have hfl : ∀ i, ⌊combShift d (Valuation.reset {x} u) η i⌋₊ = ⌊combVal e (Valuation.reset {x} u') i⌋₊ := by
    intro i; obtain (y | (_ | y)) := i
    · by_cases hy : y = x
      · subst hy; rw [hWlx, hW'lx]
      · rw [(hWy y hy).1, (hWy y hy).2]; exact regionEqAll_floor_eq hr (Sum.inl y)
    · rw [hWnone, hW'none]; exact regionEqAll_floor_eq hr (Sum.inr none)
    · by_cases hy : y = x
      · subst hy; rw [hWsx, hW'sx]; exact regionEqAll_floor_eq hr (Sum.inr none)
      · rw [(hWsy y hy).1, (hWsy y hy).2]; exact regionEqAll_floor_eq hr (Sum.inr (some y))
  have hz : ∀ i, fracPart (combShift d (Valuation.reset {x} u) η i) = 0
      ↔ fracPart (combVal e (Valuation.reset {x} u') i) = 0 := by
    intro i; obtain (y | (_ | y)) := i
    · by_cases hy : y = x
      · subst hy; rw [hWlx, hW'lx]
      · rw [(hWy y hy).1, (hWy y hy).2]; exact regionEqAll_fracPart_zero_iff hr (Sum.inl y)
    · rw [hWnone, hW'none]; exact regionEqAll_fracPart_zero_iff hr (Sum.inr none)
    · by_cases hy : y = x
      · subst hy; rw [hWsx, hW'sx]; exact regionEqAll_fracPart_zero_iff hr (Sum.inr none)
      · rw [(hWsy y hy).1, (hWsy y hy).2]; exact regionEqAll_fracPart_zero_iff hr (Sum.inr (some y))
  -- frac-value: `W` reduces to `V` under the remap `inr (some x) ↦ inr none`, except `inl x → 0`.
  have hfrac : ∀ i, (∃ j, fracPart (combShift d (Valuation.reset {x} u) η i) = fracPart (combShift d u η j)
      ∧ fracPart (combVal e (Valuation.reset {x} u') i) = fracPart (combVal e u' j))
      ∨ (fracPart (combShift d (Valuation.reset {x} u) η i) = 0
        ∧ fracPart (combVal e (Valuation.reset {x} u') i) = 0) := by
    intro i; obtain (y | (_ | y)) := i
    · by_cases hy : y = x
      · subst hy; exact Or.inr ⟨by rw [hWlx]; simp [fracPart], by rw [hW'lx]; simp [fracPart]⟩
      · exact Or.inl ⟨Sum.inl y, by rw [(hWy y hy).1], by rw [(hWy y hy).2]⟩
    · exact Or.inl ⟨Sum.inr none, by rw [hWnone], by rw [hW'none]⟩
    · by_cases hy : y = x
      · subst hy; exact Or.inl ⟨Sum.inr none, by rw [hWsx], by rw [hW'sx]⟩
      · exact Or.inl ⟨Sum.inr (some y), by rw [(hWsy y hy).1], by rw [(hWsy y hy).2]⟩
  apply regionEqAll_of_exact hfl hz
  intro i j
  rcases hfrac i with ⟨ji, hWi, hW'i⟩ | ⟨hWi0, hW'i0⟩
  · rcases hfrac j with ⟨jj, hWj, hW'j⟩ | ⟨hWj0, hW'j0⟩
    · rw [hWi, hWj, hW'i, hW'j]; exact regionEqAll_fracOrder hr ji jj
    · rw [hWi, hWj0, hW'i, hW'j0]
      have hzji := regionEqAll_fracPart_zero_iff hr ji
      exact ⟨fun h => le_of_eq (hzji.mp (le_antisymm h (fracPart_nonneg _))),
        fun h => le_of_eq (hzji.mpr (le_antisymm h (fracPart_nonneg _)))⟩
  · rw [hWi0, hW'i0]
    exact ⟨fun _ => fracPart_nonneg _, fun _ => fracPart_nonneg _⟩

/-- **Forget the coupling**: the coupled live relation implies `Sq2FRel`. The `inl` part of the
combined region gives the clock region; the `inr` parts give the asymmetric crossing-match and
τ-match via `asymMatch_of_floor_shift` (`⌊cv − η⌋₊ = ⌊cv'⌋₊` for all small `η`). So the five proven
`Sq2FullRel` clauses transfer. -/
theorem Sq2CoupledFRel.toFRel {D : Type*} {d e : ℝ≥0} {u u' : Valuation D}
    (h : Sq2CoupledFRel d u e u') : Sq2FRel d u e u' := by
  obtain ⟨hd, he, η₀, hη₀, hreg⟩ := h
  refine ⟨?_, hd, he, ?_, ?_⟩
  · exact RegionEqAll.precomp (f := Sum.inl) Sum.inl_injective
      (hreg (η₀ / 2) (half_pos hη₀) (NNReal.half_lt_self hη₀.ne'))
  · refine asymMatch_of_floor_shift (by rw [crossVal_zero]; exact tsub_pos_of_lt hd) hη₀ ?_
    intro η hηpos hηlt
    have hfe := regionEqAll_floor_eq (hreg η hηpos hηlt) (Sum.inr none)
    simp only [combShift_inr, combVal_inr_none] at hfe
    simp only [crossVal_zero]; exact hfe
  · intro y
    refine asymMatch_of_floor_shift (lt_of_lt_of_le (tsub_pos_of_lt hd) le_add_self) hη₀ ?_
    intro η hηpos hηlt
    have hfe := regionEqAll_floor_eq (hreg η hηpos hηlt) (Sum.inr (some y))
    simp only [combShift_inr, combVal_inr_some] at hfe
    exact hfe

/-- **Forget the coupling** (state level): every coupled state is a `Sq2FullRel` state. -/
theorem Sq2CoupledRel.toFullRel {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2CoupledRel p u q u') : Sq2FullRel p u q u' := by
  rcases h with hpast | ⟨d, e, hp, hq, hfr⟩
  · exact Or.inl hpast
  · exact Or.inr ⟨d, e, hp, hq, hfr.toFRel⟩

/-- Both regimes give region-equivalent formula clocks. -/
theorem Sq2CoupledRel.regionEqAll {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2CoupledRel p u q u') : RegionEqAll u u' :=
  h.toFullRel.regionEqAll

/-- **Guard clause** for the coupled relation. -/
theorem Sq2CoupledRel.guard {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2CoupledRel p u q u') (g : ClockConstraint D) : satisfies u g ↔ satisfies u' g :=
  regionEqAll_satisfies h.regionEqAll g

/-- **Reset clause** (live regime): the coupling is preserved by resetting a clock. -/
theorem Sq2CoupledFRel.reset {D : Type*} [DecidableEq D] {d e : ℝ≥0} {u u' : Valuation D}
    (h : Sq2CoupledFRel d u e u') (x : D) :
    Sq2CoupledFRel d (Valuation.reset {x} u) e (Valuation.reset {x} u') := by
  obtain ⟨hd, he, η₀, hη₀, hreg⟩ := h
  exact ⟨hd, he, η₀, hη₀, fun η hηpos hηlt => combReset_regionEqAll x (hreg η hηpos hηlt)⟩

/-- **Reset clause** for the coupled relation: resetting clock `x` preserves it (both regimes). -/
theorem Sq2CoupledRel.reset {D : Type*} [DecidableEq D] {p q : Sq2} {u u' : Valuation D}
    (h : Sq2CoupledRel p u q u') (x : D) :
    Sq2CoupledRel p (Valuation.reset {x} u) q (Valuation.reset {x} u') := by
  rcases h with ⟨hpd, hqd, hr⟩ | ⟨d, e, hp, hq, hfr⟩
  · exact Or.inl ⟨hpd, hqd, hr.reset {x}⟩
  · exact Or.inr ⟨d, e, hp, hq, hfr.reset x⟩

end TLTS

end DeepWiki.ReactiveSystems
