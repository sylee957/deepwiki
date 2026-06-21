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

end TLTS

end DeepWiki.ReactiveSystems
