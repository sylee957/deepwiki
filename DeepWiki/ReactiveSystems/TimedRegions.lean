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

/-! ## Finiteness of the region quotient (Theorem 11.3, finite-index part) -/

open Classical in
/-- The **region fingerprint** of a clock valuation: the clamped floor of every
clock (an element of `Fin (cₓ+2)`), which bounded clocks have a zero fractional
part, and the ordering of fractional parts among bounded clocks. Region-equivalent
valuations share a fingerprint, and the fingerprint ranges over a finite type, so
there are only finitely many regions. -/
noncomputable def regionFingerprint (cmax : C → ℕ) (v : Valuation C) :
    (∀ x, Fin (cmax x + 2)) × (C → Bool) × (C → C → Bool) :=
  (fun x => ⟨regionFloor cmax v x, by have := regionFloor_le cmax v x; omega⟩,
   fun x => decide (v x ≤ cmax x ∧ fracPart (v x) = 0),
   fun x y => decide (v x ≤ cmax x ∧ v y ≤ cmax y ∧ fracPart (v x) ≤ fracPart (v y)))

/-- Region equivalence is exactly equality of region fingerprints. -/
theorem regionEq_iff_fingerprint (cmax : C → ℕ) (v v' : Valuation C) :
    RegionEq cmax v v' ↔ regionFingerprint cmax v = regionFingerprint cmax v' := by
  simp only [regionFingerprint, Prod.ext_iff, funext_iff, Fin.mk.injEq, decide_eq_decide]
  unfold RegionEq
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · intro x
      have hb := bounded_iff_regionFloor (h1 x)
      exact ⟨fun ⟨hx, hz⟩ => ⟨hb.mp hx, (h2 x hx).mp hz⟩,
        fun ⟨hx', hz'⟩ => ⟨hb.mpr hx', (h2 x (hb.mpr hx')).mpr hz'⟩⟩
    · intro x y
      have hbx := bounded_iff_regionFloor (h1 x)
      have hby := bounded_iff_regionFloor (h1 y)
      exact ⟨fun ⟨hx, hy, ho⟩ => ⟨hbx.mp hx, hby.mp hy, (h3 x y hx hy).mp ho⟩,
        fun ⟨hx', hy', ho'⟩ =>
          ⟨hbx.mpr hx', hby.mpr hy', (h3 x y (hbx.mpr hx') (hby.mpr hy')).mpr ho'⟩⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · intro x hx
      have hb := bounded_iff_regionFloor (h1 x)
      exact ⟨fun hz => ((h2 x).mp ⟨hx, hz⟩).2, fun hz' => ((h2 x).mpr ⟨hb.mp hx, hz'⟩).2⟩
    · intro x y hx hy
      have hbx := bounded_iff_regionFloor (h1 x)
      have hby := bounded_iff_regionFloor (h1 y)
      exact ⟨fun ho => ((h3 x y).mp ⟨hx, hy, ho⟩).2.2,
        fun ho' => ((h3 x y).mpr ⟨hbx.mp hx, hby.mp hy, ho'⟩).2.2⟩

/-- The fingerprint descends to the region quotient. -/
noncomputable def Region.fingerprint (cmax : C → ℕ) :
    Region cmax → (∀ x, Fin (cmax x + 2)) × (C → Bool) × (C → C → Bool) :=
  Quotient.lift (regionFingerprint cmax)
    (fun v v' h => (regionEq_iff_fingerprint cmax v v').mp h)

/-- Distinct regions have distinct fingerprints. -/
theorem Region.fingerprint_injective (cmax : C → ℕ) :
    Function.Injective (Region.fingerprint cmax) := by
  intro a b
  induction a using Quotient.ind with | _ v =>
  induction b using Quotient.ind with | _ v' =>
  exact fun h => Quotient.sound ((regionEq_iff_fingerprint cmax v v').mpr h)

/-- **Theorem 11.3** (finite-index part). For a finite clock set, region
equivalence partitions the clock valuations into only finitely many classes:
the region quotient is finite. -/
instance Region.finite [Finite C] (cmax : C → ℕ) : Finite (Region cmax) :=
  Finite.of_injective _ (Region.fingerprint_injective cmax)

/-! ## Toward Theorem 11.3: guard invariance, reset preservation, time-successor

The substantive half of Theorem 11.3 — region-equivalent configurations are
*untimed* bisimilar — rests on three facts about how region equivalence interacts
with the timed-automaton semantics. Guard invariance (region-equivalent
valuations satisfy the same bounded clock constraints) and reset preservation are
fully general; the delay-matching *time-successor* property is the Alur–Dill
combinatorial core, proved here for single-clock automata (and two general
fragments — all-clocks-above-`cₓ` and zero-delay), with the general multi-clock
case left open (it needs the cross-clock fractional-order combinatorics). -/

/-- A clock constraint is bounded by `cmax` when every atomic bound `n` in a
comparison `x ⋈ n` satisfies `n ≤ cmax x`. -/
def ClockConstraint.BoundedBy (cmax : C → ℕ) : ClockConstraint C → Prop
  | .true_ => True
  | .atom x _ n => n ≤ cmax x
  | .and g₁ g₂ => ClockConstraint.BoundedBy cmax g₁ ∧ ClockConstraint.BoundedBy cmax g₂

/-- A clock value has zero fractional part iff it equals its own integer part. -/
theorem fracPart_eq_zero_iff (a : ℝ≥0) : fracPart a = 0 ↔ (⌊a⌋₊ : ℝ≥0) = a := by
  unfold fracPart
  have hbridge : ((⌊a⌋₊ : ℝ≥0) : ℝ) = (⌊(a : ℝ)⌋ : ℝ) := by
    have e1 : ((⌊a⌋₊ : ℝ≥0) : ℝ) = (⌊(a : ℝ)⌋₊ : ℝ) := by push_cast; congr 1
    have e2 : ((⌊(a : ℝ)⌋₊ : ℤ) : ℝ) = (⌊(a : ℝ)⌋ : ℝ) := by
      rw [Int.natCast_floor_eq_floor a.coe_nonneg]
    rw [e1]; push_cast at e2 ⊢; exact e2
  rw [← NNReal.coe_inj, hbridge]
  constructor
  · intro hz
    have := Int.self_sub_fract (a : ℝ)
    rw [hz, sub_zero] at this
    exact this.symm
  · intro h
    rw [← h, Int.fract_intCast]

/-- A comparison `r ⋈ n` against an integer bound is decided by the integer part
`⌊r⌋₊` and whether `r` lands exactly on an integer (`fracPart r = 0`). -/
theorem Cmp.holds_congr (cmp : Cmp) {a b : ℝ≥0} (n : ℕ)
    (hfl : ⌊a⌋₊ = ⌊b⌋₊) (hz : fracPart a = 0 ↔ fracPart b = 0) :
    cmp.holds a n ↔ cmp.holds b n := by
  have hLT : a < (n : ℝ≥0) ↔ b < (n : ℝ≥0) := by
    rw [(Nat.floor_lt (zero_le' (a := a))).symm, (Nat.floor_lt (zero_le' (a := b))).symm, hfl]
  have heq_a : a = (n : ℝ≥0) ↔ (⌊a⌋₊ = n ∧ fracPart a = 0) := by
    constructor
    · intro h; subst h; exact ⟨Nat.floor_natCast n, fracPart_natCast n⟩
    · rintro ⟨h1, h2⟩; rw [(fracPart_eq_zero_iff a).mp h2 |>.symm, h1]
  have heq_b : b = (n : ℝ≥0) ↔ (⌊b⌋₊ = n ∧ fracPart b = 0) := by
    constructor
    · intro h; subst h; exact ⟨Nat.floor_natCast n, fracPart_natCast n⟩
    · rintro ⟨h1, h2⟩; rw [(fracPart_eq_zero_iff b).mp h2 |>.symm, h1]
  have hEQ : a = (n : ℝ≥0) ↔ b = (n : ℝ≥0) := by rw [heq_a, heq_b, hfl, hz]
  cases cmp <;> simp only [Cmp.holds]
  · rw [le_iff_lt_or_eq, le_iff_lt_or_eq, hLT, hEQ]
  · exact hLT
  · exact hEQ
  · rw [gt_iff_lt, gt_iff_lt, ← not_le, ← not_le, le_iff_lt_or_eq, le_iff_lt_or_eq, hLT, hEQ]
  · rw [ge_iff_le, ge_iff_le, ← not_lt, ← not_lt, hLT]

/-- When both values strictly exceed the integer bound `n`, every comparison
`· ⋈ n` agrees on them (the saturated region above `cₓ`). -/
theorem Cmp.holds_congr_of_lt (cmp : Cmp) {a b : ℝ≥0} {n : ℕ}
    (ha : (n : ℝ≥0) < a) (hb : (n : ℝ≥0) < b) :
    cmp.holds a n ↔ cmp.holds b n := by
  cases cmp <;> simp only [Cmp.holds]
  · exact iff_of_false (not_le.mpr ha) (not_le.mpr hb)
  · exact iff_of_false (not_lt.mpr ha.le) (not_lt.mpr hb.le)
  · exact iff_of_false (fun h => (lt_irrefl _ (h ▸ ha))) (fun h => (lt_irrefl _ (h ▸ hb)))
  · exact iff_of_true ha hb
  · exact iff_of_true ha.le hb.le

/-- Region-equivalent valuations agree on every comparison `v x ⋈ n` whose bound
satisfies `n ≤ cmax x`: below the clamp the integer-part/fractional-zero data
decide it, above it both values saturate. -/
theorem regionEq_cmp_holds {cmax : C → ℕ} {v v' : Valuation C} (cmp : Cmp) {x : C} {n : ℕ}
    (h : RegionEq cmax v v') (hn : n ≤ cmax x) :
    cmp.holds (v x) n ↔ cmp.holds (v' x) n := by
  obtain ⟨h1, h2, _⟩ := h
  have hrf := h1 x
  have hbi := bounded_iff_regionFloor hrf
  by_cases hx : v x ≤ cmax x
  · have hx' : v' x ≤ cmax x := hbi.mp hx
    have hfl : ⌊v x⌋₊ = ⌊v' x⌋₊ := by
      unfold regionFloor at hrf; rw [if_pos hx, if_pos hx'] at hrf; exact hrf
    exact Cmp.holds_congr cmp n hfl (h2 x hx)
  · have hx' : ¬ v' x ≤ cmax x := fun hc => hx (hbi.mpr hc)
    have hcn : (n : ℝ≥0) ≤ (cmax x : ℝ≥0) := by exact_mod_cast hn
    have ha : (n : ℝ≥0) < v x := lt_of_le_of_lt hcn (not_le.mp hx)
    have hb : (n : ℝ≥0) < v' x := lt_of_le_of_lt hcn (not_le.mp hx')
    exact Cmp.holds_congr_of_lt cmp ha hb

/-- **Guard invariance** (the substance of Theorem 11.3's action steps):
region-equivalent valuations satisfy exactly the same clock constraints whose
constants stay within the clamp `cmax`. -/
theorem regionEq_satisfies {cmax : C → ℕ} {v v' : Valuation C} {g : ClockConstraint C}
    (h : RegionEq cmax v v') (hg : g.BoundedBy cmax) :
    satisfies v g ↔ satisfies v' g := by
  induction g with
  | true_ => exact Iff.rfl
  | atom x c n => exact regionEq_cmp_holds c h hg
  | and g₁ g₂ ih₁ ih₂ => exact and_congr (ih₁ hg.1) (ih₂ hg.2)

/-- `frac(0) = 0`. -/
theorem fracPart_zero : fracPart (0 : ℝ≥0) = 0 := by simp [fracPart]

/-- `frac(d) ≤ 0 ↔ frac(d) = 0`, since fractional parts are nonnegative. -/
theorem fracPart_le_zero_iff (d : ℝ≥0) : fracPart d ≤ 0 ↔ fracPart d = 0 :=
  ⟨fun h => le_antisymm h (Int.fract_nonneg _), fun h => h.le⟩

/-- The clamped floor of a reset clock is `0`. -/
theorem regionFloor_reset_mem {cmax : C → ℕ} {r : Set C} {x : C} (h : x ∈ r)
    (v : Valuation C) : regionFloor cmax (Valuation.reset r v) x = 0 := by
  unfold regionFloor
  rw [Valuation.reset_mem h]
  simp

/-- **Reset preservation.** Region equivalence is preserved by clock resets. -/
theorem RegionEq.reset {cmax : C → ℕ} {v v' : Valuation C} (r : Set C)
    (h : RegionEq cmax v v') : RegionEq cmax (Valuation.reset r v) (Valuation.reset r v') := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun x => ?_, fun x hx => ?_, fun x y hx hy => ?_⟩
  · by_cases hxr : x ∈ r
    · rw [regionFloor_reset_mem hxr, regionFloor_reset_mem hxr]
    · unfold regionFloor
      rw [Valuation.reset_not_mem hxr v, Valuation.reset_not_mem hxr v']
      exact h1 x
  · by_cases hxr : x ∈ r
    · rw [Valuation.reset_mem hxr v, Valuation.reset_mem hxr v', fracPart_zero]
    · rw [Valuation.reset_not_mem hxr v] at hx
      rw [Valuation.reset_not_mem hxr v, Valuation.reset_not_mem hxr v']
      exact h2 x hx
  · by_cases hxr : x ∈ r
    · by_cases hyr : y ∈ r
      · rw [Valuation.reset_mem hxr v, Valuation.reset_mem hyr v,
          Valuation.reset_mem hxr v', Valuation.reset_mem hyr v', fracPart_zero]
      · rw [Valuation.reset_not_mem hyr v] at hy
        rw [Valuation.reset_mem hxr v, Valuation.reset_not_mem hyr v,
          Valuation.reset_mem hxr v', Valuation.reset_not_mem hyr v', fracPart_zero]
        exact iff_of_true (Int.fract_nonneg _) (Int.fract_nonneg _)
    · by_cases hyr : y ∈ r
      · rw [Valuation.reset_not_mem hxr v] at hx
        rw [Valuation.reset_not_mem hxr v, Valuation.reset_mem hyr v,
          Valuation.reset_not_mem hxr v', Valuation.reset_mem hyr v', fracPart_zero,
          fracPart_le_zero_iff, fracPart_le_zero_iff]
        exact h2 x hx
      · rw [Valuation.reset_not_mem hxr v] at hx
        rw [Valuation.reset_not_mem hyr v] at hy
        rw [Valuation.reset_not_mem hxr v, Valuation.reset_not_mem hyr v,
          Valuation.reset_not_mem hxr v', Valuation.reset_not_mem hyr v']
        exact h3 x y hx hy

/-- `fracPart T ≠ 0` exactly when `T` lies strictly above its integer part. -/
theorem fracPart_ne_zero_iff (T : ℝ≥0) : fracPart T ≠ 0 ↔ ((⌊T⌋₊ : ℝ≥0) < T) := by
  rw [show (fracPart T ≠ 0) ↔ ¬ (fracPart T = 0) from Iff.rfl, fracPart_eq_zero_iff]
  exact ⟨fun h => lt_of_le_of_ne (Nat.floor_le (zero_le' (a := T))) h, fun h => ne_of_lt h⟩

/-- Closed form of the clamped floor after a uniform delay `e` on clock `x`. -/
theorem regionFloor_add (cmax : C → ℕ) (w : Valuation C) (e : ℝ≥0) (x : C) :
    regionFloor cmax (w.add e) x = if w x + e ≤ cmax x then ⌊w x + e⌋₊ else cmax x + 1 := by
  unfold regionFloor; simp only [Valuation.add_apply]

/-- A value strictly inside `[n, n+1)` has `Nat.floor` equal to `n`. -/
theorem floor_eq_of_mem {S : ℝ≥0} {n : ℕ} (h1 : (n : ℝ≥0) ≤ S) (h2 : S < (n : ℝ≥0) + 1) :
    ⌊S⌋₊ = n := by
  rw [Nat.floor_eq_iff (zero_le' (a := S))]
  exact ⟨h1, by exact_mod_cast h2⟩

/-- **Per-clock time-successor.** If a single clock `x` agrees on clamped floor and
on frac-zero status between `v` and `v'`, then after delaying `v` by `d` there is a
delay `d'` reproducing the same clamped floor and frac-zero status for `v'`. The
witness is constructed explicitly: an integer target (`d' = ⌊v x + d⌋ − v' x`), an
open-interval target (`d'` reaching `max (v' x) (v x + d)`), or an above-`cₓ`
target (`d' = cₓ + 1`). -/
theorem exists_delay_match_clock {cmax : C → ℕ} {v v' : Valuation C} {x : C}
    (hfloor : regionFloor cmax v x = regionFloor cmax v' x)
    (hfrac : v x ≤ cmax x → (fracPart (v x) = 0 ↔ fracPart (v' x) = 0))
    (d : ℝ≥0) :
    ∃ d', regionFloor cmax (v.add d) x = regionFloor cmax (v'.add d') x ∧
      ((v.add d) x ≤ cmax x → (fracPart ((v.add d) x) = 0 ↔ fracPart ((v'.add d') x) = 0)) := by
  set T := v x + d with hT
  by_cases hTb : T ≤ cmax x
  · have hvb : v x ≤ cmax x := le_trans le_self_add hTb
    have hv'b : v' x ≤ cmax x := (bounded_iff_regionFloor hfloor).mp hvb
    have hflv : (⌊v x⌋₊ : ℕ) = ⌊v' x⌋₊ := by
      unfold regionFloor at hfloor; rw [if_pos hvb, if_pos hv'b] at hfloor; exact hfloor
    set n := ⌊T⌋₊ with hn
    have hnle : n ≤ cmax x := (Nat.floor_mono hTb).trans_eq (Nat.floor_natCast _)
    have hv'len : ⌊v' x⌋₊ ≤ n := by rw [← hflv]; exact Nat.floor_mono le_self_add
    have hv'lt : v' x < (n : ℝ≥0) + 1 := by
      calc v' x < (⌊v' x⌋₊ : ℝ≥0) + 1 := Nat.lt_floor_add_one _
        _ ≤ (n : ℝ≥0) + 1 := by gcongr
    by_cases hfz : fracPart T = 0
    · have hTn : (n : ℝ≥0) = T := (fracPart_eq_zero_iff T).mp hfz
      have hv'len' : v' x ≤ (n : ℝ≥0) := by
        rcases lt_or_eq_of_le hv'len with hlt | heq
        · have h1 : v' x < (⌊v' x⌋₊ : ℝ≥0) + 1 := Nat.lt_floor_add_one _
          have h2 : (⌊v' x⌋₊ : ℝ≥0) + 1 ≤ (n : ℝ≥0) := by exact_mod_cast (hlt : ⌊v' x⌋₊ + 1 ≤ n)
          exact le_of_lt (lt_of_lt_of_le h1 h2)
        · have hflvn : ⌊v x⌋₊ = n := by rw [hflv, heq]
          have hvxge : (n : ℝ≥0) ≤ v x := by rw [← hflvn]; exact Nat.floor_le (zero_le' (a := v x))
          have hvxle : v x ≤ (n : ℝ≥0) := by rw [hTn]; exact le_self_add
          have hvxn : v x = (n : ℝ≥0) := le_antisymm hvxle hvxge
          have hfvx0 : fracPart (v x) = 0 := by rw [fracPart_eq_zero_iff, hvxn, Nat.floor_natCast]
          have hfv'0 : fracPart (v' x) = 0 := (hfrac hvb).mp hfvx0
          have hv'eq : (⌊v' x⌋₊ : ℝ≥0) = v' x := (fracPart_eq_zero_iff (v' x)).mp hfv'0
          rw [← hv'eq]; exact_mod_cast (heq : ⌊v' x⌋₊ = n).le
      have hsum : v' x + ((n : ℝ≥0) - v' x) = (n : ℝ≥0) := add_tsub_cancel_of_le hv'len'
      refine ⟨(n : ℝ≥0) - v' x, ?_, ?_⟩
      · rw [regionFloor_add, regionFloor_add, hsum, ← hT, hTn]
      · intro _
        simp only [Valuation.add_apply]; rw [hsum, hTn, ← hT, hfz]
    · have hTgt : (n : ℝ≥0) < T := (fracPart_ne_zero_iff T).mp hfz
      have hTlt : T < (n : ℝ≥0) + 1 := Nat.lt_floor_add_one T
      have hncmax : n < cmax x := by
        have : (n : ℝ≥0) < cmax x := lt_of_lt_of_le hTgt hTb
        exact_mod_cast this
      set M := max (v' x) T with hM
      have hnM : (n : ℝ≥0) < M := lt_of_lt_of_le hTgt (le_max_right _ _)
      have hMlt : M < (n : ℝ≥0) + 1 := max_lt hv'lt hTlt
      have hv'leM : v' x ≤ M := le_max_left _ _
      have hsum : v' x + (M - v' x) = M := add_tsub_cancel_of_le hv'leM
      have hMfloor : ⌊M⌋₊ = n := floor_eq_of_mem (le_of_lt hnM) hMlt
      have hMb : M ≤ cmax x := by
        have hn1 : (n : ℝ≥0) + 1 ≤ cmax x := by exact_mod_cast Nat.succ_le_of_lt hncmax
        exact le_of_lt (lt_of_lt_of_le hMlt hn1)
      refine ⟨M - v' x, ?_, ?_⟩
      · rw [regionFloor_add, regionFloor_add, hsum, ← hT, if_pos hTb, if_pos hMb, hMfloor]
      · intro _
        simp only [Valuation.add_apply]; rw [hsum]
        constructor
        · intro h; exact absurd h hfz
        · intro h
          have : (n : ℝ≥0) = M := by rw [← hMfloor]; exact (fracPart_eq_zero_iff M).mp h
          exact absurd this (ne_of_lt hnM)
  · have hTgt : (cmax x : ℝ≥0) < T := not_le.mp hTb
    refine ⟨(cmax x : ℝ≥0) + 1, ?_, ?_⟩
    · have hv' : ¬ v' x + ((cmax x : ℝ≥0) + 1) ≤ cmax x := by
        intro hc
        have : (cmax x : ℝ≥0) + 1 ≤ cmax x := le_trans le_add_self hc
        simp at this
      rw [regionFloor_add, regionFloor_add, ← hT, if_neg hTb, if_neg hv']
    · intro hc
      exact absurd hc (by rw [Valuation.add_apply, ← hT]; exact hTb)

/-- The region **time-successor** property: from region-equivalent valuations, any
delay on the left is matched by *some* delay on the right into region-equivalent
valuations. This is the delay-matching ingredient of Theorem 11.3's untimed
bisimulation. -/
def TimeSuccessor (cmax : C → ℕ) : Prop :=
  ∀ ⦃v v' : Valuation C⦄, RegionEq cmax v v' → ∀ d : ℝ≥0, ∃ d', RegionEq cmax (v.add d) (v'.add d')

/-- **Alur–Dill time-successor, single-clock fragment.** For a subsingleton clock
set there is no cross-clock fractional-ordering constraint, so the per-clock
construction at the unique clock yields the matching delay. This is the *full*
time-successor for one-clock automata. -/
theorem RegionEq.timeSuccessor_subsingleton [Subsingleton C] {cmax : C → ℕ}
    {v v' : Valuation C} (h : RegionEq cmax v v') (d : ℝ≥0) :
    ∃ d', RegionEq cmax (v.add d) (v'.add d') := by
  obtain ⟨h1, h2, _⟩ := h
  rcases isEmpty_or_nonempty C with hC | hne
  · exact ⟨d, fun x => (hC.false x).elim, fun x => (hC.false x).elim,
      fun x => (hC.false x).elim⟩
  · obtain ⟨x0⟩ := hne
    obtain ⟨d', hd'floor, hd'frac⟩ := exists_delay_match_clock (h1 x0) (h2 x0) d
    refine ⟨d', ?_, ?_, ?_⟩
    · intro x; rw [Subsingleton.elim x x0]; exact hd'floor
    · intro x hx; rw [Subsingleton.elim x x0]; rw [Subsingleton.elim x x0] at hx; exact hd'frac hx
    · intro x y _ _
      rw [Subsingleton.elim x y]
      exact ⟨fun _ => le_refl _, fun _ => le_refl _⟩

/-- For a subsingleton clock set the time-successor property holds outright. -/
theorem timeSuccessor_of_subsingleton [Subsingleton C] (cmax : C → ℕ) : TimeSuccessor cmax :=
  fun _ _ h d => RegionEq.timeSuccessor_subsingleton h d

/-- **Time-successor when every clock already exceeds `cₓ`:** take `d' = d`. Every
clock stays above `cₓ`, so all clamped floors are `cₓ+1` and conditions 2–3 are
vacuous. -/
theorem RegionEq.timeSuccessor_allUnbounded {cmax : C → ℕ} {v v' : Valuation C}
    (h : RegionEq cmax v v') (d : ℝ≥0)
    (hub : ∀ x, (cmax x : ℝ≥0) < v x) :
    ∃ d', RegionEq cmax (v.add d) (v'.add d') := by
  obtain ⟨h1, _, _⟩ := h
  have hub' : ∀ x, (cmax x : ℝ≥0) < v' x := by
    intro x
    by_contra hc
    have hv'b : v' x ≤ cmax x := not_lt.mp hc
    have hvb : v x ≤ cmax x := (bounded_iff_regionFloor (h1 x)).mpr hv'b
    exact absurd hvb (not_le.mpr (hub x))
  refine ⟨d, ?_, ?_, ?_⟩
  · intro x
    have hvub : ¬ v x + d ≤ cmax x := not_le.mpr (lt_of_lt_of_le (hub x) le_self_add)
    have hv'ub : ¬ v' x + d ≤ cmax x := not_le.mpr (lt_of_lt_of_le (hub' x) le_self_add)
    rw [regionFloor_add, regionFloor_add, if_neg hvub, if_neg hv'ub]
  · intro x hx
    simp only [Valuation.add_apply] at hx
    exact absurd hx (not_le.mpr (lt_of_lt_of_le (hub x) le_self_add))
  · intro x _ hx _
    simp only [Valuation.add_apply] at hx
    exact absurd hx (not_le.mpr (lt_of_lt_of_le (hub x) le_self_add))

/-- **Time-successor with zero delay:** take `d' = 0` (region equivalence is
reflexive). -/
theorem RegionEq.timeSuccessor_zero {cmax : C → ℕ} {v v' : Valuation C}
    (h : RegionEq cmax v v') :
    ∃ d', RegionEq cmax (v.add 0) (v'.add d') := by
  refine ⟨0, ?_⟩
  have e : ∀ w : Valuation C, w.add 0 = w := fun w => by funext x; simp
  rw [e, e]; exact h

end DeepWiki.ReactiveSystems
