import DeepWiki.ReactiveSystems.TimedAutomata

/-! # Clock regions (§11.4)
The region construction abstracts the uncountably-branching timed transition
system of a timed automaton into a finite quotient. Each clock `x` is compared
against a maximal constant `cₓ`; two valuations are *region equivalent* when they
agree on the integer parts of all clocks (up to `cₓ`), on which clocks have a
zero fractional part, and on the ordering of the fractional parts.

The book's Definition 11.12 states three conditions verbatim; taken literally
they are **not** symmetric at integer boundaries (`not_symmetric_regionEquiv`):
a value just above `cₓ` and the integer `cₓ` share a floor, so condition 1
holds, while the asymmetric guard `v x ≤ cₓ` of condition 2 only detects the
differing fractional parts in one direction. The genuine equivalence relation
underlying Theorem 11.3 replaces the bare floor comparison by a *clamped* floor
(`regionFloor`) collapsing everything above `cₓ` to one bucket; this `RegionEq`
is a true `Equivalence` and refines the book's `≡`. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

variable {C : Type*}

/-- Integer part `⌊d⌋₊` of a clock value (Definition 11.11). -/
noncomputable def intPart (d : ℝ≥0) : ℕ := ⌊d⌋₊

/-- Fractional part `frac(d) = d − ⌊d⌋`, read in `ℝ` via the coercion
(Definition 11.11). -/
noncomputable def fracPart (d : ℝ≥0) : ℝ := Int.fract (d : ℝ)

/-- `fracPart` of an integer-valued clock is `0`. -/
@[simp] theorem fracPart_natCast (n : ℕ) : fracPart (n : ℝ≥0) = 0 := by
  simp [fracPart]

open Classical in
/-- Clamped integer part used by region equivalence: a clock above its maximal
constant `cₓ` collapses to the single bucket `cₓ + 1`, so a value just above an
integer `cₓ` is separated from `cₓ` itself — fixing the boundary gap in
Definition 11.12's bare floor comparison. -/
noncomputable def regionFloor (cmax : C → ℕ) (v : Valuation C) (x : C) : ℕ :=
  if v x ≤ cmax x then ⌊v x⌋₊ else cmax x + 1

/-- A clock at or below its maximal constant has floor at most that constant. -/
theorem floor_le_of_le_cmax {cmax : C → ℕ} {v : Valuation C} {x : C}
    (h : v x ≤ cmax x) : ⌊v x⌋₊ ≤ cmax x :=
  (Nat.floor_mono h).trans_eq (Nat.floor_natCast _)

/-- The clamped floor never exceeds `cₓ + 1`. -/
theorem regionFloor_le (cmax : C → ℕ) (v : Valuation C) (x : C) :
    regionFloor cmax v x ≤ cmax x + 1 := by
  unfold regionFloor
  split
  · exact (floor_le_of_le_cmax ‹_›).trans (Nat.le_succ _)
  · exact le_refl _

/-- Agreement of clamped floors forces the two valuations to bound clock `x`
together: this is what makes the (asymmetrically guarded) fractional-part
conditions symmetric. -/
theorem bounded_iff_regionFloor {cmax : C → ℕ} {v v' : Valuation C} {x : C}
    (h : regionFloor cmax v x = regionFloor cmax v' x) :
    (v x ≤ cmax x ↔ v' x ≤ cmax x) := by
  unfold regionFloor at h
  constructor
  · intro hx
    by_contra hx'
    rw [if_pos hx, if_neg hx'] at h
    have := floor_le_of_le_cmax hx
    omega
  · intro hx'
    by_contra hx
    rw [if_neg hx, if_pos hx'] at h
    have := floor_le_of_le_cmax hx'
    omega

/-- **Definition 11.12** (region equivalence, verbatim). Two clock valuations are
equivalent when (1) for each clock either both exceed its maximal constant `cₓ`
or their integer parts agree, (2) for each clock at most `cₓ` the two agree on
having a zero fractional part, and (3) the ordering of fractional parts (among
clocks at most their constant) agrees. -/
def RegionEquiv (cmax : C → ℕ) (v v' : Valuation C) : Prop :=
  (∀ x, ((cmax x : ℝ≥0) < v x ∧ (cmax x : ℝ≥0) < v' x) ∨ intPart (v x) = intPart (v' x)) ∧
  (∀ x, v x ≤ cmax x → (fracPart (v x) = 0 ↔ fracPart (v' x) = 0)) ∧
  (∀ x y, v x ≤ cmax x → v y ≤ cmax y →
      (fracPart (v x) ≤ fracPart (v y) ↔ fracPart (v' x) ≤ fracPart (v' y)))

/-- **Region equivalence** as used by Theorem 11.3: Definition 11.12 with the
bare floor comparison (condition 1) replaced by agreement of the *clamped* floor
`regionFloor`. This is a genuine equivalence relation. -/
def RegionEq (cmax : C → ℕ) (v v' : Valuation C) : Prop :=
  (∀ x, regionFloor cmax v x = regionFloor cmax v' x) ∧
  (∀ x, v x ≤ cmax x → (fracPart (v x) = 0 ↔ fracPart (v' x) = 0)) ∧
  (∀ x y, v x ≤ cmax x → v y ≤ cmax y →
      (fracPart (v x) ≤ fracPart (v y) ↔ fracPart (v' x) ≤ fracPart (v' y)))

/-- **Theorem 11.3** (equivalence part). Region equivalence is an equivalence
relation on clock valuations. -/
theorem regionEq_equivalence (cmax : C → ℕ) : Equivalence (RegionEq cmax) where
  refl _ := ⟨fun _ => rfl, fun _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl⟩
  symm := by
    rintro v v' ⟨h1, h2, h3⟩
    refine ⟨fun x => (h1 x).symm, ?_, ?_⟩
    · intro x hx'
      exact (h2 x ((bounded_iff_regionFloor (h1 x)).mpr hx')).symm
    · intro x y hx' hy'
      exact (h3 x y ((bounded_iff_regionFloor (h1 x)).mpr hx')
        ((bounded_iff_regionFloor (h1 y)).mpr hy')).symm
  trans := by
    rintro v v' v'' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨fun x => (h1 x).trans (h1' x), ?_, ?_⟩
    · intro x hx
      exact (h2 x hx).trans (h2' x ((bounded_iff_regionFloor (h1 x)).mp hx))
    · intro x y hx hy
      exact (h3 x y hx hy).trans
        (h3' x y ((bounded_iff_regionFloor (h1 x)).mp hx)
          ((bounded_iff_regionFloor (h1 y)).mp hy))

/-- `RegionEq` refines the book's verbatim `RegionEquiv`: agreement of clamped
floors entails condition 1 of Definition 11.12 (and conditions 2–3 coincide). -/
theorem RegionEq.regionEquiv {cmax : C → ℕ} {v v' : Valuation C}
    (h : RegionEq cmax v v') : RegionEquiv cmax v v' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun x => ?_, h2, h3⟩
  have hb := bounded_iff_regionFloor (h1 x)
  by_cases hx : v x ≤ cmax x
  · right
    have hx' : v' x ≤ cmax x := hb.mp hx
    have := h1 x
    unfold regionFloor at this
    rw [if_pos hx, if_pos hx'] at this
    exact this
  · left
    exact ⟨not_le.mp hx, not_le.mp fun c => hx (hb.mpr c)⟩

/-- The book's verbatim **Definition 11.12 is not symmetric**: with one clock and
`cₓ = 0`, the valuations `v(x) = ½` and `v'(x) = 0` satisfy the three conditions
in the order `(v, v')` (condition 1 holds — equal floors `0`; conditions 2–3 are
vacuous since `½ ≰ 0`), but fail them in the order `(v', v)` (condition 2 now
fires at `0 ≤ 0` and `frac 0 = 0 ↮ frac ½ = 0`). Theorem 11.3 needs a genuine
equivalence; `RegionEq` supplies it. -/
theorem not_symmetric_regionEquiv :
    ¬ Symmetric (RegionEquiv (C := Unit) (fun _ => 0)) := by
  have hcoe : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by push_cast; ring
  have hfrac : fracPart (1 / 2 : ℝ≥0) = 1 / 2 := by
    rw [fracPart, hcoe, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
  intro hsymm
  have hv : RegionEquiv (C := Unit) (fun _ => 0) (fun _ => 1 / 2) (fun _ => 0) := by
    refine ⟨fun _ => Or.inr ?_, fun _ hx => ?_, fun _ _ hx _ => ?_⟩
    · show ⌊(1 / 2 : ℝ≥0)⌋₊ = ⌊(0 : ℝ≥0)⌋₊
      simp [Nat.floor_eq_zero]
      norm_num
    · exact absurd hx (by norm_num)
    · exact absurd hx (by norm_num)
  obtain ⟨_, h2, _⟩ := hsymm hv
  have key : fracPart (0 : ℝ≥0) = 0 ↔ fracPart (1 / 2 : ℝ≥0) = 0 := h2 () (by norm_num)
  have h0 : fracPart (0 : ℝ≥0) = 0 := by simp [fracPart]
  rw [hfrac] at key
  exact absurd (key.mp h0) (by norm_num)

/-- The setoid of region equivalence on clock valuations. -/
def regionSetoid (cmax : C → ℕ) : Setoid (Valuation C) where
  r := RegionEq cmax
  iseqv := regionEq_equivalence cmax

/-- **Definition 11.13.** A *region* is an equivalence class `[v]_≡` of clock
valuations under region equivalence. -/
def Region (cmax : C → ℕ) : Type _ := Quotient (regionSetoid cmax)

/-- The region represented by a clock valuation, `[v]_≡`. -/
def region (cmax : C → ℕ) (v : Valuation C) : Region cmax := Quotient.mk _ v

/-- Two valuations represent the same region exactly when region equivalent. -/
theorem region_eq_iff {cmax : C → ℕ} {v v' : Valuation C} :
    region cmax v = region cmax v' ↔ RegionEq cmax v v' :=
  Quotient.eq

end DeepWiki.ReactiveSystems
