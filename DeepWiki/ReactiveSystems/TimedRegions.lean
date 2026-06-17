import DeepWiki.ReactiveSystems.TimedAutomata

/-! # Clock regions
The region construction abstracts the uncountably-branching timed transition
system of a timed automaton into a finite quotient. Each clock `x` is compared
against a maximal constant `cₓ`; two valuations are *region equivalent* when they
agree on the integer parts of all clocks (up to `cₓ`), on which clocks have a
zero fractional part, and on the ordering of the fractional parts.

The book's verbatim three conditions, taken literally, are
**not** symmetric at integer boundaries (`not_symmetric_regionEquiv`):
a value just above `cₓ` and the integer `cₓ` share a floor, so condition 1
holds, while the asymmetric guard `v x ≤ cₓ` of condition 2 only detects the
differing fractional parts in one direction. The genuine equivalence relation
underlying the finiteness theorem replaces the bare floor comparison by a *clamped* floor
(`regionFloor`) collapsing everything above `cₓ` to one bucket; this `RegionEq`
is a true `Equivalence` and refines the book's `≡`. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

variable {C : Type*}

/-- Integer part `⌊d⌋₊` of a clock value. -/
noncomputable def intPart (d : ℝ≥0) : ℕ := ⌊d⌋₊

/-- Fractional part `frac(d) = d − ⌊d⌋`, read in `ℝ` via the coercion. -/
noncomputable def fracPart (d : ℝ≥0) : ℝ := Int.fract (d : ℝ)

/-- `fracPart` of an integer-valued clock is `0`. -/
@[simp] theorem fracPart_natCast (n : ℕ) : fracPart (n : ℝ≥0) = 0 := by
  simp [fracPart]

open Classical in
/-- Clamped integer part used by region equivalence: a clock above its maximal
constant `cₓ` collapses to the single bucket `cₓ + 1`, so a value just above an
integer `cₓ` is separated from `cₓ` itself — fixing the boundary gap in
the book's bare floor comparison. -/
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

/-- Region equivalence (the book's verbatim conditions). Two clock valuations are
equivalent when (1) for each clock either both exceed its maximal constant `cₓ`
or their integer parts agree, (2) for each clock at most `cₓ` the two agree on
having a zero fractional part, and (3) the ordering of fractional parts (among
clocks at most their constant) agrees. -/
def RegionEquiv (cmax : C → ℕ) (v v' : Valuation C) : Prop :=
  (∀ x, ((cmax x : ℝ≥0) < v x ∧ (cmax x : ℝ≥0) < v' x) ∨ intPart (v x) = intPart (v' x)) ∧
  (∀ x, v x ≤ cmax x → (fracPart (v x) = 0 ↔ fracPart (v' x) = 0)) ∧
  (∀ x y, v x ≤ cmax x → v y ≤ cmax y →
      (fracPart (v x) ≤ fracPart (v y) ↔ fracPart (v' x) ≤ fracPart (v' y)))

/-- **Region equivalence** (the working relation): the book's conditions with the
bare floor comparison (condition 1) replaced by agreement of the *clamped* floor
`regionFloor`. This is a genuine equivalence relation. -/
def RegionEq (cmax : C → ℕ) (v v' : Valuation C) : Prop :=
  (∀ x, regionFloor cmax v x = regionFloor cmax v' x) ∧
  (∀ x, v x ≤ cmax x → (fracPart (v x) = 0 ↔ fracPart (v' x) = 0)) ∧
  (∀ x y, v x ≤ cmax x → v y ≤ cmax y →
      (fracPart (v x) ≤ fracPart (v y) ↔ fracPart (v' x) ≤ fracPart (v' y)))

/-- Region equivalence is an equivalence
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
floors entails condition 1 (and conditions 2–3 coincide). -/
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

/-- The book's verbatim region equivalence **is not symmetric**: with one clock and
`cₓ = 0`, the valuations `v(x) = ½` and `v'(x) = 0` satisfy the three conditions
in the order `(v, v')` (condition 1 holds — equal floors `0`; conditions 2–3 are
vacuous since `½ ≰ 0`), but fail them in the order `(v', v)` (condition 2 now
fires at `0 ≤ 0` and `frac 0 = 0 ↮ frac ½ = 0`). The finiteness theorem needs a genuine
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

/-- A *region* is an equivalence class `[v]_≡` of clock
valuations under region equivalence. -/
def Region (cmax : C → ℕ) : Type _ := Quotient (regionSetoid cmax)

/-- The region represented by a clock valuation, `[v]_≡`. -/
def region (cmax : C → ℕ) (v : Valuation C) : Region cmax := Quotient.mk _ v

/-- Two valuations represent the same region exactly when region equivalent. -/
theorem region_eq_iff {cmax : C → ℕ} {v v' : Valuation C} :
    region cmax v = region cmax v' ↔ RegionEq cmax v v' :=
  Quotient.eq

/-! ## Finiteness of the region quotient -/

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

/-- For a finite clock set, region
equivalence partitions the clock valuations into only finitely many classes:
the region quotient is finite. -/
instance Region.finite [Finite C] (cmax : C → ℕ) : Finite (Region cmax) :=
  Finite.of_injective _ (Region.fingerprint_injective cmax)

/-! ## Guard invariance, reset preservation, time-successor

The substantive half of the region theorem — region-equivalent configurations are
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

/-- **Guard invariance** (the substance of the region theorem's action steps):
region-equivalent valuations satisfy exactly the same clock constraints whose
constants stay within the clamp `cmax`. -/
theorem regionEq_satisfies {cmax : C → ℕ} {v v' : Valuation C} {g : ClockConstraint C}
    (h : RegionEq cmax v v') (hg : g.BoundedBy cmax) :
    satisfies v g ↔ satisfies v' g := by
  induction g with
  | true_ => exact Iff.rfl
  | atom x c n => exact regionEq_cmp_holds c h hg
  | and g₁ g₂ ih₁ ih₂ => exact and_congr (ih₁ hg.1) (ih₂ hg.2)

/-! ### Unbounded region equivalence

`Mt`-equivalence quantifies over clock constraints with *unbounded* constants, so no
single clamp `cmax` makes `RegionEq cmax` agree on every guard. `RegionEqAll` —
region-equivalence at *every* clamp — is the right notion for it, and is the guard-agreement
component of an `Mt`-bisimulation. -/

/-- `BoundedBy` is monotone in the clamp. -/
theorem ClockConstraint.boundedBy_mono {cmax cmax' : C → ℕ} (hle : ∀ x, cmax x ≤ cmax' x) :
    ∀ {g : ClockConstraint C}, g.BoundedBy cmax → g.BoundedBy cmax' := by
  intro g
  induction g with
  | true_ => exact fun _ => trivial
  | atom x cmp n => exact fun h => le_trans h (hle x)
  | and g₁ g₂ ih₁ ih₂ => exact fun h => ⟨ih₁ h.1, ih₂ h.2⟩

/-- A clock constraint is bounded by some uniform clamp `(fun _ => N)`. -/
theorem ClockConstraint.exists_boundedBy (g : ClockConstraint C) :
    ∃ N : ℕ, g.BoundedBy (fun _ => N) := by
  induction g with
  | true_ => exact ⟨0, trivial⟩
  | atom x cmp n => exact ⟨n, le_refl n⟩
  | and g₁ g₂ ih₁ ih₂ =>
      obtain ⟨N₁, h₁⟩ := ih₁
      obtain ⟨N₂, h₂⟩ := ih₂
      refine ⟨max N₁ N₂, ?_, ?_⟩
      · exact ClockConstraint.boundedBy_mono (fun _ => le_max_left N₁ N₂) h₁
      · exact ClockConstraint.boundedBy_mono (fun _ => le_max_right N₁ N₂) h₂

/-- **Unbounded region equivalence**: region-equivalent at *every* clamp `cmax`. It
equates valuations for clock constraints of arbitrary size. -/
def RegionEqAll (v v' : Valuation C) : Prop := ∀ cmax : C → ℕ, RegionEq cmax v v'

/-- `RegionEqAll` is reflexive. -/
@[refl] theorem RegionEqAll.refl (v : Valuation C) : RegionEqAll v v :=
  fun cmax => (regionEq_equivalence cmax).refl v

/-- `RegionEqAll` is symmetric. -/
theorem RegionEqAll.symm {v v' : Valuation C} (h : RegionEqAll v v') : RegionEqAll v' v :=
  fun cmax => (regionEq_equivalence cmax).symm (h cmax)

/-- `RegionEqAll` is transitive. -/
theorem RegionEqAll.trans {v v' v'' : Valuation C}
    (h : RegionEqAll v v') (h' : RegionEqAll v' v'') : RegionEqAll v v'' :=
  fun cmax => (regionEq_equivalence cmax).trans (h cmax) (h' cmax)

/-- Unbounded-region-equivalent valuations satisfy exactly the same clock constraints
(of any constant size) — the guard-agreement an `Mt`-bisimulation needs. -/
theorem regionEqAll_satisfies {v v' : Valuation C} (h : RegionEqAll v v')
    (g : ClockConstraint C) : satisfies v g ↔ satisfies v' g := by
  obtain ⟨N, hN⟩ := g.exists_boundedBy
  exact regionEq_satisfies (h (fun _ => N)) hN

/-- **Constructing `RegionEqAll` from exact (unclamped) region data**: equal integer
parts, matching zero-fractional-parts, and matching fractional order — for *all*
clocks — give region equivalence at every clamp. -/
theorem regionEqAll_of_exact {u u' : Valuation C}
    (hfloor : ∀ x, ⌊u x⌋₊ = ⌊u' x⌋₊)
    (hzero : ∀ x, fracPart (u x) = 0 ↔ fracPart (u' x) = 0)
    (horder : ∀ x y, fracPart (u x) ≤ fracPart (u y) ↔ fracPart (u' x) ≤ fracPart (u' y)) :
    RegionEqAll u u' := by
  -- A clock bounded by `cmax` on one side is bounded on the other (same floor + zero-frac).
  have hbound : ∀ {v w : Valuation C} (x : C), (∀ y, ⌊v y⌋₊ = ⌊w y⌋₊) →
      (∀ y, fracPart (v y) = 0 ↔ fracPart (w y) = 0) → ∀ {cmax : C → ℕ},
      v x ≤ (cmax x : ℝ≥0) → w x ≤ (cmax x : ℝ≥0) := by
    intro v w x hf hz cmax hvx
    by_cases hzc : fracPart (v x) = 0
    · have e1 : (⌊v x⌋₊ : ℝ≥0) = v x := (fracPart_eq_zero_iff (v x)).mp hzc
      have e2 : (⌊w x⌋₊ : ℝ≥0) = w x := (fracPart_eq_zero_iff (w x)).mp ((hz x).mp hzc)
      rw [← e2, ← hf x, e1]; exact hvx
    · have hlt : ⌊v x⌋₊ < cmax x := by
        by_contra hge
        push Not at hge
        have hle2 : v x ≤ (⌊v x⌋₊ : ℝ≥0) := le_trans hvx (by exact_mod_cast hge)
        exact hzc ((fracPart_eq_zero_iff (v x)).mpr
          (le_antisymm (Nat.floor_le zero_le) hle2))
      refine le_of_lt ?_
      calc w x < (⌊w x⌋₊ : ℝ≥0) + 1 := Nat.lt_floor_add_one (w x)
        _ = (⌊v x⌋₊ : ℝ≥0) + 1 := by rw [hf x]
        _ ≤ (cmax x : ℝ≥0) := by exact_mod_cast Nat.succ_le_of_lt hlt
  intro cmax
  refine ⟨fun x => ?_, fun x _ => hzero x, fun x y _ _ => horder x y⟩
  unfold regionFloor
  by_cases hux : u x ≤ (cmax x : ℝ≥0)
  · rw [if_pos hux, if_pos (hbound x hfloor hzero hux), hfloor x]
  · have hux' : ¬ u' x ≤ (cmax x : ℝ≥0) := fun h =>
      hux (hbound x (fun y => (hfloor y).symm) (fun y => (hzero y).symm) h)
    rw [if_neg hux, if_neg hux']

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

/-- `RegionEqAll` is preserved by resetting a set of clocks. -/
theorem RegionEqAll.reset {u u' : Valuation C} (h : RegionEqAll u u') (r : Set C) :
    RegionEqAll (Valuation.reset r u) (Valuation.reset r u') :=
  fun cmax => RegionEq.reset r (h cmax)

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
valuations. This is the delay-matching ingredient of the region theorem's untimed
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

/-! ## The general time-successor (finite clock sets)

The general multi-clock time-successor is reduced to two pieces, then assembled:
adding an integer delay preserves region equivalence (`regionEq_add_natCast` —
fractional parts are unchanged); and a sub-unit delay `δ ∈ [0,1)` is matched by a
sub-unit delay `δ'` (`RegionEq.timeSuccessor_frac`), constructed by transporting
the wrap threshold `1 − δ` across the (shared) fractional order of the bounded
clocks (`threshold_transport`) and feeding the matched wrap/integer-hit bits to
the region-equivalence reduction `regionEq_add_of_match`. Combining via
`d = ⌊d⌋ + frac d` gives `timeSuccessor_of_fintype`. -/

/-- `fracPart (r + 1) = fracPart r`: the integer shift leaves the fractional part fixed. -/
theorem fracPart_add_one (r : ℝ≥0) : fracPart (r + 1) = fracPart r := by
  unfold fracPart; push_cast; exact Int.fract_add_one _

/-- `⌊r + 1⌋₊ = ⌊r⌋₊ + 1` on `ℝ≥0`. -/
theorem floor_add_one_nnreal (r : ℝ≥0) : ⌊r + 1⌋₊ = ⌊r⌋₊ + 1 :=
  Nat.floor_add_one (zero_le' (a := r))

/-- `r + 1 ≤ cmax` characterized by `⌊r⌋₊` and whether `r` is integral. -/
theorem add_one_le_iff_of_frac {cmax : ℕ} (r : ℝ≥0) :
    (r + 1 ≤ (cmax : ℝ≥0)) ↔
      (if fracPart r = 0 then ⌊r⌋₊ + 1 ≤ cmax else ⌊r⌋₊ + 2 ≤ cmax) := by
  have hcast : (r + 1 ≤ (cmax : ℝ≥0)) ↔ ((r:ℝ) + 1 ≤ (cmax:ℝ)) := by
    constructor
    · intro h; have : ((r+1:ℝ≥0):ℝ) ≤ ((cmax:ℝ≥0):ℝ) := by exact_mod_cast h
      push_cast at this; linarith
    · intro h
      have h2 : ((r+1:ℝ≥0):ℝ) ≤ ((cmax:ℝ≥0):ℝ) := by push_cast; push_cast at h; linarith
      exact_mod_cast h2
  rw [hcast]
  have hfloor : (⌊r⌋₊ : ℝ) ≤ (r:ℝ) := by
    have := Nat.floor_le (zero_le' (a := r)); exact_mod_cast this
  have hceil : (r:ℝ) < (⌊r⌋₊ : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one (a := r)
    have h2 : (r:ℝ) < ((⌊r⌋₊ : ℝ≥0) + 1 : ℝ≥0) := by exact_mod_cast h
    push_cast at h2; linarith
  by_cases hf : fracPart r = 0
  · simp only [hf, if_true]
    have heq : (⌊r⌋₊ : ℝ) = (r:ℝ) := by
      have := (fracPart_eq_zero_iff r).mp hf; exact_mod_cast this
    constructor
    · intro h; have hh : (⌊r⌋₊ : ℝ) + 1 ≤ (cmax:ℝ) := by rw [heq]; linarith
      exact_mod_cast hh
    · intro h; have hc : (⌊r⌋₊ : ℝ) + 1 ≤ (cmax:ℝ) := by exact_mod_cast h
      rw [← heq]; linarith
  · simp only [hf, if_false]
    have hlt : (⌊r⌋₊ : ℝ) < (r:ℝ) := by
      have := (fracPart_ne_zero_iff r).mp hf; exact_mod_cast this
    constructor
    · intro h; have : (⌊r⌋₊ : ℝ) + 1 < (cmax:ℝ) := by linarith
      have : ⌊r⌋₊ + 1 < cmax := by exact_mod_cast this
      omega
    · intro h; have hc : (⌊r⌋₊ : ℝ) + 2 ≤ (cmax:ℝ) := by exact_mod_cast h
      linarith

/-- If `r + 1 ≤ cmax` then `r ≤ cmax`. -/
theorem le_cmax_of_add_one_le {cmax : ℕ} {r : ℝ≥0} (h : r + 1 ≤ (cmax : ℝ≥0)) :
    r ≤ (cmax : ℝ≥0) := le_trans le_self_add h

/-- If `(v.add 1) x ≤ cmax x` then `v x ≤ cmax x` (pointwise valuation form). -/
theorem le_cmax_of_add_one_le_apply {cmax : C → ℕ} {v : Valuation C} {x : C}
    (h : (v.add 1) x ≤ (cmax x : ℝ≥0)) : v x ≤ (cmax x : ℝ≥0) := by
  simp only [Valuation.add_apply] at h; exact le_cmax_of_add_one_le h

/-- Region floors agree after the unit shift when they agree before. -/
theorem regionFloor_add_one_eq {cmax : C → ℕ} {v v' : Valuation C}
    (h : RegionEq cmax v v') (x : C) :
    regionFloor cmax (v.add 1) x = regionFloor cmax (v'.add 1) x := by
  obtain ⟨h1, h2, _⟩ := h
  have hb := bounded_iff_regionFloor (h1 x)
  rw [regionFloor_add, regionFloor_add]
  simp only [floor_add_one_nnreal]
  by_cases hvb : v x ≤ (cmax x : ℝ≥0)
  · have hv'b : v' x ≤ (cmax x : ℝ≥0) := hb.mp hvb
    have hfloors : (⌊v x⌋₊ : ℕ) = ⌊v' x⌋₊ := by
      have := h1 x; rw [regionFloor, regionFloor] at this
      simp only [hvb, hv'b, if_true] at this; exact this
    have hfrac : fracPart (v x) = 0 ↔ fracPart (v' x) = 0 := h2 x hvb
    have hguard : (v x + 1 ≤ (cmax x : ℝ≥0)) ↔ (v' x + 1 ≤ (cmax x : ℝ≥0)) := by
      rw [add_one_le_iff_of_frac, add_one_le_iff_of_frac, hfloors]
      by_cases hfz : fracPart (v x) = 0
      · rw [if_pos hfz, if_pos (hfrac.mp hfz)]
      · rw [if_neg hfz, if_neg (fun c => hfz (hfrac.mpr c))]
    by_cases hg : v x + 1 ≤ (cmax x : ℝ≥0)
    · rw [if_pos hg, if_pos (hguard.mp hg), hfloors]
    · rw [if_neg hg, if_neg (fun c => hg (hguard.mpr c))]
  · have hv'b : ¬ v' x ≤ (cmax x : ℝ≥0) := fun c => hvb (hb.mpr c)
    have hg : ¬ (v x + 1 ≤ (cmax x : ℝ≥0)) := fun c => hvb (le_cmax_of_add_one_le c)
    have hg' : ¬ (v' x + 1 ≤ (cmax x : ℝ≥0)) := fun c => hv'b (le_cmax_of_add_one_le c)
    rw [if_neg hg, if_neg hg']

/-- `RegionEq` is preserved by adding the unit delay. -/
theorem regionEq_add_one {cmax : C → ℕ} {v v' : Valuation C} (h : RegionEq cmax v v') :
    RegionEq cmax (v.add 1) (v'.add 1) := by
  refine ⟨fun x => regionFloor_add_one_eq h x, ?_, ?_⟩
  · intro x hx
    have hvx : v x ≤ (cmax x : ℝ≥0) := le_cmax_of_add_one_le_apply hx
    simp only [Valuation.add_apply, fracPart_add_one]
    exact h.2.1 x hvx
  · intro x y hx hy
    have hvx : v x ≤ (cmax x : ℝ≥0) := le_cmax_of_add_one_le_apply hx
    have hvy : v y ≤ (cmax y : ℝ≥0) := le_cmax_of_add_one_le_apply hy
    simp only [Valuation.add_apply, fracPart_add_one]
    exact h.2.2 x y hvx hvy

/-- `RegionEq` is preserved by adding any natural-number delay. -/
theorem regionEq_add_natCast {cmax : C → ℕ} {v v' : Valuation C}
    (h : RegionEq cmax v v') (N : ℕ) :
    RegionEq cmax (v.add (N : ℝ≥0)) (v'.add (N : ℝ≥0)) := by
  induction N with
  | zero =>
    have e : ∀ w : Valuation C, w.add ((0 : ℕ) : ℝ≥0) = w := by
      intro w; funext x; simp [Valuation.add_apply]
    rw [e, e]; exact h
  | succ n ih =>
    have e : ∀ w : Valuation C, w.add (((n + 1 : ℕ) : ℝ≥0)) = (w.add (n : ℝ≥0)).add 1 := by
      intro w; funext x; simp only [Valuation.add_apply]; push_cast; ring
    rw [e, e]; exact regionEq_add_one ih

/-- A clock value over `ℝ` decomposes as `⌊a⌋₊ + fracPart a`. -/
theorem coe_eq_floor_add_fracPart (a : ℝ≥0) : (a : ℝ) = (⌊a⌋₊ : ℝ) + fracPart a := by
  unfold fracPart
  have hbridge : ((⌊a⌋₊ : ℝ≥0) : ℝ) = (⌊(a : ℝ)⌋ : ℝ) := by
    have e1 : ((⌊a⌋₊ : ℝ≥0) : ℝ) = (⌊(a : ℝ)⌋₊ : ℝ) := by push_cast; congr 1
    have e2 : ((⌊(a : ℝ)⌋₊ : ℤ) : ℝ) = (⌊(a : ℝ)⌋ : ℝ) := by
      rw [Int.natCast_floor_eq_floor a.coe_nonneg]
    rw [e1]; push_cast at e2 ⊢; exact e2
  push_cast at hbridge ⊢
  rw [hbridge]
  linarith [Int.fract_add_floor (a : ℝ)]

/-- `fracPart a < 1`. -/
theorem fracPart_lt_one (a : ℝ≥0) : fracPart a < 1 := Int.fract_lt_one _

/-- `0 ≤ fracPart a`. -/
theorem fracPart_nonneg (a : ℝ≥0) : 0 ≤ fracPart a := Int.fract_nonneg _

/-- **No wrap.** A delay keeping the fractional part below `1` adds to it and fixes the
integer part. -/
theorem fracPart_add_of_no_wrap {a δ : ℝ≥0} (h : fracPart a + (δ : ℝ) < 1) :
    fracPart (a + δ) = fracPart a + (δ : ℝ) ∧ ⌊a + δ⌋₊ = ⌊a⌋₊ := by
  have hdecomp := coe_eq_floor_add_fracPart a
  have hfr : fracPart (a + δ) = fracPart a + (δ : ℝ) := by
    unfold fracPart
    push_cast
    rw [Int.fract_eq_iff]
    refine ⟨by have := fracPart_nonneg a; positivity, h, ⌊(a : ℝ)⌋, ?_⟩
    have hf := Int.self_sub_fract (a : ℝ)
    unfold fracPart at hdecomp
    linarith [hf]
  refine ⟨hfr, ?_⟩
  apply floor_eq_of_mem
  · exact le_trans (Nat.floor_le (zero_le' (a := a))) le_self_add
  · have : ((a + δ : ℝ≥0) : ℝ) < (⌊a⌋₊ : ℝ) + 1 := by
      push_cast
      have : (a : ℝ) + δ = (⌊a⌋₊ : ℝ) + (fracPart a + δ) := by rw [hdecomp]; ring
      rw [this]; linarith
    exact_mod_cast this

/-- **Wrap.** A sub-unit delay carrying the fractional part to `1` or beyond drops it by `1`
and raises the integer part by `1`. -/
theorem fracPart_add_of_wrap {a δ : ℝ≥0} (hδ : (δ : ℝ) < 1) (h : 1 ≤ fracPart a + (δ : ℝ)) :
    fracPart (a + δ) = fracPart a + (δ : ℝ) - 1 ∧ ⌊a + δ⌋₊ = ⌊a⌋₊ + 1 := by
  have hdecomp := coe_eq_floor_add_fracPart a
  have hfrac1 : 1 ≤ Int.fract (a : ℝ) + (δ : ℝ) := h
  have hfr : fracPart (a + δ) = fracPart a + (δ : ℝ) - 1 := by
    unfold fracPart
    push_cast
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith [Int.fract_lt_one (a : ℝ)], ⌊(a : ℝ)⌋ + 1, ?_⟩
    have hf := Int.self_sub_fract (a : ℝ)
    unfold fracPart at hdecomp
    push_cast
    linarith [hf]
  refine ⟨hfr, ?_⟩
  apply floor_eq_of_mem
  · have h2 : (⌊a⌋₊ : ℝ) + 1 ≤ ((a + δ : ℝ≥0) : ℝ) := by
      push_cast
      have hd : (a : ℝ) + δ = (⌊a⌋₊ : ℝ) + (fracPart a + δ) := by rw [hdecomp]; ring
      rw [hd]; linarith
    rw [Nat.cast_add, Nat.cast_one]; exact_mod_cast h2
  · have h2 : ((a + δ : ℝ≥0) : ℝ) < (((⌊a⌋₊ + 1 : ℕ) : ℝ≥0) : ℝ) + 1 := by
      push_cast
      have hd : (a : ℝ) + δ = (⌊a⌋₊ : ℝ) + (fracPart a + δ) := by rw [hdecomp]; ring
      rw [hd]; linarith [fracPart_lt_one a]
    exact_mod_cast h2

/-- For a clock bounded in `v` and a strictly positive delay `δ < 1`, the clamped floor
after delay is a function of the integer part, the maximal constant, and the wrap/hit bits:
no wrap keeps the integer part (collapsing to `cₓ+1` only at the top band); a wrap raises it
by one, surviving the clamp exactly when below the top band or landing on the integer. -/
theorem regionFloor_add_pos {cmax : C → ℕ} {v : Valuation C} {x : C}
    (hvb : v x ≤ cmax x) {δ : ℝ≥0} (hδ0 : (0 : ℝ) < δ) (hδ1 : (δ : ℝ) < 1) :
    regionFloor cmax (v.add δ) x =
      (if 1 ≤ fracPart (v x) + (δ : ℝ) then
        (if ⌊v x⌋₊ + 1 < cmax x then ⌊v x⌋₊ + 1
         else if fracPart (v x) + (δ : ℝ) = 1 ∧ ⌊v x⌋₊ + 1 = cmax x then ⌊v x⌋₊ + 1
         else cmax x + 1)
      else (if ⌊v x⌋₊ < cmax x then ⌊v x⌋₊ else cmax x + 1)) := by
  have hflcmax : ⌊v x⌋₊ ≤ cmax x := floor_le_of_le_cmax hvb
  rw [regionFloor_add]
  have hdecomp := coe_eq_floor_add_fracPart (v x)
  by_cases hw : 1 ≤ fracPart (v x) + (δ : ℝ)
  · rw [if_pos hw]
    obtain ⟨_, hfl⟩ := fracPart_add_of_wrap hδ1 hw
    have hval : ((v x + δ : ℝ≥0) : ℝ) = (⌊v x⌋₊ : ℝ) + 1 + (fracPart (v x) + δ - 1) := by
      push_cast; rw [hdecomp]; ring
    by_cases hlt : ⌊v x⌋₊ + 1 < cmax x
    · rw [if_pos hlt]
      have hbnd : v x + δ ≤ cmax x := by
        have hv2 : ((v x + δ : ℝ≥0) : ℝ) < (⌊v x⌋₊ : ℝ) + 1 + 1 := by
          rw [hval]; linarith [fracPart_lt_one (v x)]
        have hc2 : (⌊v x⌋₊ : ℝ) + 1 + 1 ≤ cmax x := by
          exact_mod_cast (by omega : ⌊v x⌋₊ + 1 + 1 ≤ cmax x)
        have : ((v x + δ : ℝ≥0) : ℝ) ≤ (cmax x : ℝ) := by linarith
        exact_mod_cast this
      rw [if_pos hbnd, hfl]
    · rw [if_neg hlt]
      by_cases hh : fracPart (v x) + (δ : ℝ) = 1
      · -- hit
        have hvalint : ((v x + δ : ℝ≥0) : ℝ) = (⌊v x⌋₊ : ℝ) + 1 := by rw [hval, hh]; ring
        by_cases heq : ⌊v x⌋₊ + 1 = cmax x
        · have hbnd : v x + δ ≤ cmax x := by
            have : ((v x + δ : ℝ≥0) : ℝ) ≤ (cmax x : ℝ) := by
              rw [hvalint]; have : (⌊v x⌋₊ : ℝ) + 1 = cmax x := by exact_mod_cast heq
              linarith
            exact_mod_cast this
          rw [if_pos hbnd, hfl, if_pos ⟨hh, heq⟩]
        · have hgt : cmax x < ⌊v x⌋₊ + 1 := by omega
          have hub : ¬ v x + δ ≤ cmax x := by
            intro hc
            have hcr : ((v x + δ : ℝ≥0) : ℝ) ≤ (cmax x : ℝ) := by exact_mod_cast hc
            rw [hvalint] at hcr
            have : (cmax x : ℝ) + 1 ≤ ⌊v x⌋₊ + 1 := by exact_mod_cast Nat.succ_le_of_lt hgt
            linarith
          rw [if_neg hub, if_neg (by tauto)]
      · -- strict wrap
        have hsw : (⌊v x⌋₊ : ℝ) + 1 < ((v x + δ : ℝ≥0) : ℝ) := by
          rw [hval]
          have : 0 < fracPart (v x) + (δ : ℝ) - 1 := by
            rcases lt_or_eq_of_le hw with h | h
            · linarith
            · exact absurd h.symm hh
          linarith
        have hge : cmax x ≤ ⌊v x⌋₊ + 1 := by omega
        have hub : ¬ v x + δ ≤ cmax x := by
          intro hc
          have hcr : ((v x + δ : ℝ≥0) : ℝ) ≤ (cmax x : ℝ) := by exact_mod_cast hc
          have hge' : (cmax x : ℝ) ≤ ⌊v x⌋₊ + 1 := by exact_mod_cast hge
          linarith
        rw [if_neg hub, if_neg (by tauto)]
  · rw [if_neg hw]
    push Not at hw
    obtain ⟨_, hfl⟩ := fracPart_add_of_no_wrap hw
    have hval : ((v x + δ : ℝ≥0) : ℝ) = (⌊v x⌋₊ : ℝ) + (fracPart (v x) + δ) := by
      push_cast; rw [hdecomp]; ring
    by_cases hlt : ⌊v x⌋₊ < cmax x
    · rw [if_pos hlt]
      have hbnd : v x + δ ≤ cmax x := by
        have hv2 : ((v x + δ : ℝ≥0) : ℝ) < (⌊v x⌋₊ : ℝ) + 1 := by rw [hval]; linarith
        have hc2 : (⌊v x⌋₊ : ℝ) + 1 ≤ cmax x := by exact_mod_cast Nat.succ_le_of_lt hlt
        have : ((v x + δ : ℝ≥0) : ℝ) ≤ (cmax x : ℝ) := by linarith
        exact_mod_cast this
      rw [if_pos hbnd, hfl]
    · rw [if_neg hlt]
      have heq : ⌊v x⌋₊ = cmax x := le_antisymm hflcmax (by omega)
      have hub : ¬ v x + δ ≤ cmax x := by
        intro hc
        have hcr : ((v x + δ : ℝ≥0) : ℝ) ≤ (cmax x : ℝ) := by exact_mod_cast hc
        rw [hval, heq] at hcr
        have : 0 < fracPart (v x) + (δ : ℝ) := by linarith [fracPart_nonneg (v x)]
        linarith
      rw [if_neg hub]

/-- Fractional part after a positive sub-unit delay: the sum, dropping `1` on a wrap. -/
theorem fracPart_add_value {a δ : ℝ≥0} (hδ1 : (δ : ℝ) < 1) :
    fracPart (a + δ) = if 1 ≤ fracPart a + (δ : ℝ) then fracPart a + (δ : ℝ) - 1
      else fracPart a + (δ : ℝ) := by
  by_cases hw : 1 ≤ fracPart a + (δ : ℝ)
  · rw [if_pos hw]; exact (fracPart_add_of_wrap hδ1 hw).1
  · rw [if_neg hw]; exact (fracPart_add_of_no_wrap (by push Not at hw; exact hw)).1

/-- After a positive sub-unit delay, the fractional part is zero exactly at an integer hit
(`fracPart a + δ = 1`). -/
theorem fracPart_add_eq_zero_iff {a δ : ℝ≥0} (hδ0 : (0 : ℝ) < δ) (hδ1 : (δ : ℝ) < 1) :
    fracPart (a + δ) = 0 ↔ fracPart a + (δ : ℝ) = 1 := by
  rw [fracPart_add_value hδ1]
  by_cases hw : 1 ≤ fracPart a + (δ : ℝ)
  · rw [if_pos hw]
    constructor
    · intro h; linarith
    · intro h; linarith
  · rw [if_neg hw]
    constructor
    · intro h
      have := fracPart_nonneg a
      linarith
    · intro h
      push Not at hw; linarith

/-- **Reduction step.** Given region-equivalent valuations and positive sub-unit delays
`δ, δ'` that match the *wrap* bit (whether a bounded clock's fractional part reaches the
next integer) and the *integer-hit* bit (whether it lands exactly on it) at every clock
bounded in `v`, the delayed valuations are again region-equivalent. The clamped floor,
fractional-zero set and fractional order after the delay are all determined by the integer
parts (shared) together with these two matched bits. -/
theorem regionEq_add_of_match {cmax : C → ℕ} {v v' : Valuation C} (h : RegionEq cmax v v')
    {δ δ' : ℝ≥0} (hδ0 : (0 : ℝ) < δ) (hδ1 : (δ : ℝ) < 1)
    (hδ'0 : (0 : ℝ) < δ') (hδ'1 : (δ' : ℝ) < 1)
    (hwrap : ∀ x, v x ≤ cmax x →
      (1 ≤ fracPart (v x) + (δ : ℝ) ↔ 1 ≤ fracPart (v' x) + (δ' : ℝ)))
    (hhit : ∀ x, v x ≤ cmax x →
      (fracPart (v x) + (δ : ℝ) = 1 ↔ fracPart (v' x) + (δ' : ℝ) = 1)) :
    RegionEq cmax (v.add δ) (v'.add δ') := by
  obtain ⟨h1, h2, h3⟩ := h
  -- shared integer parts on bounded clocks
  have hfleq : ∀ x, v x ≤ cmax x → ⌊v x⌋₊ = ⌊v' x⌋₊ := by
    intro x hx
    have hx' : v' x ≤ cmax x := (bounded_iff_regionFloor (h1 x)).mp hx
    have := h1 x; unfold regionFloor at this
    rw [if_pos hx, if_pos hx'] at this; exact this
  refine ⟨?_, ?_, ?_⟩
  · -- C1: clamped floors agree after delay
    intro x
    by_cases hx : v x ≤ cmax x
    · have hx' : v' x ≤ cmax x := (bounded_iff_regionFloor (h1 x)).mp hx
      rw [regionFloor_add_pos hx hδ0 hδ1, regionFloor_add_pos hx' hδ'0 hδ'1, ← hfleq x hx]
      by_cases hw : 1 ≤ fracPart (v x) + (δ : ℝ)
      · have hw' : 1 ≤ fracPart (v' x) + (δ' : ℝ) := (hwrap x hx).mp hw
        rw [if_pos hw, if_pos hw']
        by_cases hlt : ⌊v x⌋₊ + 1 < cmax x
        · rw [if_pos hlt]; rw [if_pos hlt]
        · rw [if_neg hlt, if_neg hlt]
          by_cases heq : ⌊v x⌋₊ + 1 = cmax x
          · by_cases hh : fracPart (v x) + (δ : ℝ) = 1
            · have hh' : fracPart (v' x) + (δ' : ℝ) = 1 := (hhit x hx).mp hh
              rw [if_pos ⟨hh, heq⟩, if_pos ⟨hh', heq⟩]
            · have hh' : ¬ fracPart (v' x) + (δ' : ℝ) = 1 := fun c => hh ((hhit x hx).mpr c)
              rw [if_neg (by tauto), if_neg (by tauto)]
          · rw [if_neg (by tauto), if_neg (by tauto)]
      · have hw' : ¬ 1 ≤ fracPart (v' x) + (δ' : ℝ) := fun c => hw ((hwrap x hx).mpr c)
        rw [if_neg hw, if_neg hw']
    · -- unbounded in v (hence in v'): stays unbounded
      have hx' : ¬ v' x ≤ cmax x := fun hc => hx ((bounded_iff_regionFloor (h1 x)).mpr hc)
      have hgt : (cmax x : ℝ≥0) < v x := not_le.mp hx
      have hgt' : (cmax x : ℝ≥0) < v' x := not_le.mp hx'
      have hub : ¬ (v.add δ) x ≤ cmax x := by
        simp only [Valuation.add_apply]
        exact not_le.mpr (lt_of_lt_of_le hgt le_self_add)
      have hub' : ¬ (v'.add δ') x ≤ cmax x := by
        simp only [Valuation.add_apply]
        exact not_le.mpr (lt_of_lt_of_le hgt' le_self_add)
      unfold regionFloor; rw [if_neg hub, if_neg hub']
  · -- C2: frac-zero agreement after delay, on clocks bounded-after
    intro x hxa
    simp only [Valuation.add_apply] at hxa
    have hx : v x ≤ cmax x := le_trans le_self_add hxa
    have hx' : v' x ≤ cmax x := (bounded_iff_regionFloor (h1 x)).mp hx
    simp only [Valuation.add_apply]
    rw [fracPart_add_eq_zero_iff hδ0 hδ1, fracPart_add_eq_zero_iff hδ'0 hδ'1]
    exact hhit x hx
  · -- C3: frac-order agreement after delay, on clocks bounded-after
    intro x y hxa hya
    simp only [Valuation.add_apply] at hxa hya
    have hx : v x ≤ cmax x := le_trans le_self_add hxa
    have hy : v y ≤ cmax y := le_trans le_self_add hya
    simp only [Valuation.add_apply]
    rw [fracPart_add_value hδ1, fracPart_add_value hδ1, fracPart_add_value hδ'1,
      fracPart_add_value hδ'1]
    have hfx := fracPart_lt_one (v x); have hfy := fracPart_lt_one (v y)
    have hfx' := fracPart_lt_one (v' x); have hfy' := fracPart_lt_one (v' y)
    have hnx := fracPart_nonneg (v x); have hny := fracPart_nonneg (v y)
    have hnx' := fracPart_nonneg (v' x); have hny' := fracPart_nonneg (v' y)
    by_cases hwx : 1 ≤ fracPart (v x) + (δ : ℝ) <;> by_cases hwy : 1 ≤ fracPart (v y) + (δ : ℝ)
    · -- both wrap
      have hwx' : 1 ≤ fracPart (v' x) + (δ' : ℝ) := (hwrap x hx).mp hwx
      have hwy' : 1 ≤ fracPart (v' y) + (δ' : ℝ) := (hwrap y hy).mp hwy
      rw [if_pos hwx, if_pos hwy, if_pos hwx', if_pos hwy']
      rw [show (fracPart (v x) + (δ:ℝ) - 1 ≤ fracPart (v y) + (δ:ℝ) - 1) ↔
        (fracPart (v x) ≤ fracPart (v y)) by constructor <;> intro <;> linarith,
        show (fracPart (v' x) + (δ':ℝ) - 1 ≤ fracPart (v' y) + (δ':ℝ) - 1) ↔
        (fracPart (v' x) ≤ fracPart (v' y)) by constructor <;> intro <;> linarith]
      exact h3 x y hx hy
    · -- x wrap, y no-wrap : both sides True
      have hwx' : 1 ≤ fracPart (v' x) + (δ' : ℝ) := (hwrap x hx).mp hwx
      have hwy' : ¬ 1 ≤ fracPart (v' y) + (δ' : ℝ) := fun c => hwy ((hwrap y hy).mpr c)
      rw [if_pos hwx, if_neg hwy, if_pos hwx', if_neg hwy']
      exact iff_of_true (by linarith) (by linarith)
    · -- x no-wrap, y wrap : both sides False
      have hwx' : ¬ 1 ≤ fracPart (v' x) + (δ' : ℝ) := fun c => hwx ((hwrap x hx).mpr c)
      have hwy' : 1 ≤ fracPart (v' y) + (δ' : ℝ) := (hwrap y hy).mp hwy
      rw [if_neg hwx, if_pos hwy, if_neg hwx', if_pos hwy']
      exact iff_of_false (by linarith) (by linarith)
    · -- both no-wrap
      have hwx' : ¬ 1 ≤ fracPart (v' x) + (δ' : ℝ) := fun c => hwx ((hwrap x hx).mpr c)
      have hwy' : ¬ 1 ≤ fracPart (v' y) + (δ' : ℝ) := fun c => hwy ((hwrap y hy).mpr c)
      rw [if_neg hwx, if_neg hwy, if_neg hwx', if_neg hwy']
      rw [show (fracPart (v x) + (δ:ℝ) ≤ fracPart (v y) + (δ:ℝ)) ↔
        (fracPart (v x) ≤ fracPart (v y)) by constructor <;> intro <;> linarith,
        show (fracPart (v' x) + (δ':ℝ) ≤ fracPart (v' y) + (δ':ℝ)) ↔
        (fracPart (v' x) ≤ fracPart (v' y)) by constructor <;> intro <;> linarith]
      exact h3 x y hx hy

open Classical in
/-- **Threshold transport.** On a finite index set `B`, given two `[0,1)`-valued families
agreeing on which entries are zero and on their order, any threshold `t ∈ (0,1)` for the
first family is matched by a threshold `t' ∈ (0,1)` for the second: the entries weakly
above the threshold, and exactly at it, are the same. -/
theorem threshold_transport [Fintype C] (B : Finset C) (f f' : C → ℝ)
    (hf' : ∀ x ∈ B, 0 ≤ f' x ∧ f' x < 1)
    (hzero : ∀ x ∈ B, f x = 0 ↔ f' x = 0)
    (horder : ∀ x ∈ B, ∀ y ∈ B, f x ≤ f y ↔ f' x ≤ f' y)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ t', 0 < t' ∧ t' < 1 ∧ (∀ x ∈ B, (t ≤ f x ↔ t' ≤ f' x)) ∧
      (∀ x ∈ B, (f x = t ↔ f' x = t')) := by
  -- strict order transfer from order + zero agreement
  have hstrict : ∀ x ∈ B, ∀ y ∈ B, f x < f y → f' x < f' y := by
    intro x hx y hy hlt
    have h1 : f' x ≤ f' y := (horder x hx y hy).mp hlt.le
    have h2 : ¬ f' y ≤ f' x := fun c => absurd ((horder y hy x hx).mpr c) (not_le.mpr hlt)
    exact lt_of_le_not_ge h1 h2
  have hpos : ∀ x ∈ B, 0 < f x → 0 < f' x := by
    intro x hx hfx
    have : f' x ≠ 0 := fun c => absurd ((hzero x hx).mpr c) (ne_of_gt hfx)
    exact lt_of_le_of_ne (hf' x hx).1 (Ne.symm this)
  by_cases hhit : ∃ x0 ∈ B, f x0 = t
  · -- hit case
    obtain ⟨x0, hx0B, hx0eq⟩ := hhit
    refine ⟨f' x0, hpos x0 hx0B (hx0eq ▸ ht0), (hf' x0 hx0B).2, ?_, ?_⟩
    · intro x hxB
      rw [← hx0eq]; exact horder x0 hx0B x hxB
    · intro x hxB
      constructor
      · intro h
        rw [← hx0eq] at h
        exact le_antisymm ((horder x hxB x0 hx0B).mp h.le) ((horder x0 hx0B x hxB).mp h.ge)
      · intro h
        rw [← hx0eq]
        exact le_antisymm ((horder x hxB x0 hx0B).mpr h.le) ((horder x0 hx0B x hxB).mpr h.ge)
  · -- no-hit case: every x∈B has f x ≠ t
    push Not at hhit
    by_cases hBne : B.Nonempty
    · -- partition B by f x vs t
      set Hi := B.filter (fun x => t < f x) with hHi
      set Lo := B.filter (fun x => f x < t) with hLo
      have hpart : ∀ x ∈ B, x ∈ Hi ∨ x ∈ Lo := by
        intro x hxB
        rcases lt_trichotomy (f x) t with h | h | h
        · right; rw [hLo, Finset.mem_filter]; exact ⟨hxB, h⟩
        · exact absurd h (hhit x hxB)
        · left; rw [hHi, Finset.mem_filter]; exact ⟨hxB, h⟩
      by_cases hHine : Hi.Nonempty
      · by_cases hLone : Lo.Nonempty
        · -- mixed
          obtain ⟨xh, hxhHi, hxhmin⟩ := Finset.exists_min_image Hi f' hHine
          obtain ⟨xl, hxlLo, hxlmax⟩ := Finset.exists_max_image Lo f' hLone
          have hxhB : xh ∈ B := (Finset.mem_filter.mp hxhHi).1
          have hxhgt : t < f xh := (Finset.mem_filter.mp hxhHi).2
          have hxlB : xl ∈ B := (Finset.mem_filter.mp hxlLo).1
          have hxllt : f xl < t := (Finset.mem_filter.mp hxlLo).2
          have hlt' : f' xl < f' xh := hstrict xl hxlB xh hxhB (lt_trans hxllt hxhgt)
          have hfxhpos : 0 < f' xh := hpos xh hxhB (lt_trans ht0 hxhgt)
          refine ⟨(f' xl + f' xh) / 2, by linarith [(hf' xl hxlB).1], by linarith [(hf' xh hxhB).2],
            ?_, ?_⟩
          · intro x hxB
            rcases hpart x hxB with hxHi | hxLo
            · have hge : f' xh ≤ f' x := hxhmin x hxHi
              have hgt : t < f x := (Finset.mem_filter.mp hxHi).2
              constructor
              · intro _; linarith
              · intro _; exact hgt.le
            · have hle : f' x ≤ f' xl := hxlmax x hxLo
              have hlt : f x < t := (Finset.mem_filter.mp hxLo).2
              constructor
              · intro h; linarith
              · intro h; linarith
          · intro x hxB
            rcases hpart x hxB with hxHi | hxLo
            · have hge : f' xh ≤ f' x := hxhmin x hxHi
              have hgt : t < f x := (Finset.mem_filter.mp hxHi).2
              constructor
              · intro h; exact absurd h (ne_of_gt hgt)
              · intro h; linarith
            · have hle : f' x ≤ f' xl := hxlmax x hxLo
              have hlt : f x < t := (Finset.mem_filter.mp hxLo).2
              constructor
              · intro h; exact absurd h (ne_of_lt hlt)
              · intro h; linarith
        · -- Lo empty: all of B is Hi
          obtain ⟨xh, hxhB, hxhmin⟩ := Finset.exists_min_image B f' hBne
          have hxhgt : t < f xh := by
            rcases hpart xh hxhB with h | h
            · exact (Finset.mem_filter.mp h).2
            · exact absurd ⟨xh, h⟩ hLone
          have hfxhpos : 0 < f' xh := hpos xh hxhB (lt_trans ht0 hxhgt)
          refine ⟨f' xh / 2, by linarith, by linarith [(hf' xh hxhB).2], ?_, ?_⟩
          · intro x hxB
            have hge : f' xh ≤ f' x := hxhmin x hxB
            have hgt : t < f x := by
              rcases hpart x hxB with h | h
              · exact (Finset.mem_filter.mp h).2
              · exact absurd ⟨x, h⟩ hLone
            constructor
            · intro _; linarith
            · intro _; exact hgt.le
          · intro x hxB
            have hge : f' xh ≤ f' x := hxhmin x hxB
            have hgt : t < f x := by
              rcases hpart x hxB with h | h
              · exact (Finset.mem_filter.mp h).2
              · exact absurd ⟨x, h⟩ hLone
            constructor
            · intro h; exact absurd h (ne_of_gt hgt)
            · intro h; linarith
      · -- Hi empty: all of B is Lo
        obtain ⟨xl, hxlB, hxlmax⟩ := Finset.exists_max_image B f' hBne
        refine ⟨(f' xl + 1) / 2, by linarith [(hf' xl hxlB).1], by linarith [(hf' xl hxlB).2],
          ?_, ?_⟩
        · intro x hxB
          have hle : f' x ≤ f' xl := hxlmax x hxB
          have hlt : f x < t := by
            rcases hpart x hxB with h | h
            · exact absurd ⟨x, h⟩ hHine
            · exact (Finset.mem_filter.mp h).2
          have hf'le1 : f' xl < 1 := (hf' xl hxlB).2
          constructor
          · intro h; linarith
          · intro h; linarith
        · intro x hxB
          have hle : f' x ≤ f' xl := hxlmax x hxB
          have hlt : f x < t := by
            rcases hpart x hxB with h | h
            · exact absurd ⟨x, h⟩ hHine
            · exact (Finset.mem_filter.mp h).2
          have hf'le1 : f' xl < 1 := (hf' xl hxlB).2
          constructor
          · intro h; exact absurd h (ne_of_lt hlt)
          · intro h; linarith
    · -- B empty
      rw [Finset.not_nonempty_iff_eq_empty] at hBne
      refine ⟨1 / 2, by norm_num, by norm_num, ?_, ?_⟩ <;>
        (intro x hxB; rw [hBne] at hxB; exact absurd hxB (Finset.notMem_empty x))

open Classical in
/-- **Alur–Dill time-successor, fractional fragment.** For a finite clock set and a delay
`δ < 1`, advancing region-equivalent valuations by `δ` on the left is matched by some delay
`δ'` on the right, landing in region-equivalent valuations. As `δ` grows in `[0,1)` the
bounded clocks cross their next integer in decreasing order of fractional part; since the
fractional order and the integer-hit set are shared, a single matching threshold — and hence
a single matching delay — exists. This is the combinatorial core of the general
time-successor (the full delay `d = N + δ` reduces to this case via the integer shift). -/
theorem RegionEq.timeSuccessor_frac [Fintype C] {cmax : C → ℕ} {v v' : Valuation C}
    (h : RegionEq cmax v v') {δ : ℝ≥0} (hδ : δ < 1) :
    ∃ δ', RegionEq cmax (v.add δ) (v'.add δ') := by
  -- δ = 0 is reflexivity; otherwise δ ∈ (0,1)
  rcases eq_or_lt_of_le (zero_le' (a := δ)) with hδ0 | hδ0
  · exact ⟨0, by
      have e : ∀ w : Valuation C, w.add (0 : ℝ≥0) = w := fun w => by funext x; simp
      rw [← hδ0]; rw [e, e]; exact h⟩
  · have hδ0r : (0 : ℝ) < δ := by exact_mod_cast hδ0
    have hδ1r : (δ : ℝ) < 1 := by exact_mod_cast hδ
    obtain ⟨h1, h2, h3⟩ := h
    -- bounded clocks of v (equivalently of v')
    set B := Finset.univ.filter (fun x => v x ≤ cmax x) with hB
    have hmemB : ∀ x, x ∈ B ↔ v x ≤ cmax x := by
      intro x; rw [hB, Finset.mem_filter]; simp
    -- apply the threshold transport at t = 1 - δ
    obtain ⟨t', ht'0, ht'1, htle, hteq⟩ :=
      threshold_transport B (fun x => fracPart (v x)) (fun x => fracPart (v' x))
        (fun x _ => ⟨fracPart_nonneg _, fracPart_lt_one _⟩)
        (fun x hx => h2 x ((hmemB x).mp hx))
        (fun x hx y hy => h3 x y ((hmemB x).mp hx) ((hmemB y).mp hy))
        (1 - (δ : ℝ)) (by linarith) (by linarith [hδ0r])
    -- δ' := 1 - t' ∈ (0,1)
    set δ' : ℝ≥0 := ⟨1 - t', by linarith⟩ with hδ'def
    have hδ'val : (δ' : ℝ) = 1 - t' := rfl
    refine ⟨δ', ?_⟩
    apply regionEq_add_of_match ⟨h1, h2, h3⟩ hδ0r hδ1r
      (by rw [hδ'val]; linarith) (by rw [hδ'val]; linarith)
    · -- wrap match
      intro x hx
      have hxB : x ∈ B := (hmemB x).mpr hx
      rw [hδ'val]
      have hl := htle x hxB
      constructor
      · intro hw; have : (1 - (δ:ℝ)) ≤ fracPart (v x) := by linarith
        have := hl.mp this; linarith
      · intro hw; have : t' ≤ fracPart (v' x) := by linarith
        have := hl.mpr this; linarith
    · -- hit match
      intro x hx
      have hxB : x ∈ B := (hmemB x).mpr hx
      rw [hδ'val]
      have he := hteq x hxB
      constructor
      · intro hh; have : fracPart (v x) = 1 - (δ:ℝ) := by linarith
        have := he.mp this; linarith
      · intro hh; have : fracPart (v' x) = t' := by linarith
        have := he.mpr this; linarith

/-- **General time-successor for a finite clock set** (the delay case,
multi-clock). Writing `d = N + δ` with `N = ⌊d⌋` and `δ ∈ [0,1)`, the integer
shift by `N` preserves region equivalence (`regionEq_add_natCast`) and the
fractional remainder is matched by `RegionEq.timeSuccessor_frac`. -/
theorem timeSuccessor_of_fintype [Fintype C] (cmax : C → ℕ) : TimeSuccessor cmax := by
  intro v v' h d
  have hNd : (⌊d⌋₊ : ℝ≥0) ≤ d := Nat.floor_le (zero_le' (a := d))
  set δ := d - (⌊d⌋₊ : ℝ≥0) with hδdef
  have hsum : (⌊d⌋₊ : ℝ≥0) + δ = d := add_tsub_cancel_of_le hNd
  have hδ1 : δ < 1 := by
    have hadd : δ + (⌊d⌋₊ : ℝ≥0) = d := by rw [hδdef]; exact tsub_add_cancel_of_le hNd
    have hlt : δ + (⌊d⌋₊ : ℝ≥0) < 1 + (⌊d⌋₊ : ℝ≥0) := by
      rw [hadd, add_comm]; exact Nat.lt_floor_add_one d
    exact lt_of_add_lt_add_right hlt
  obtain ⟨δ', hδ'⟩ := RegionEq.timeSuccessor_frac (regionEq_add_natCast h ⌊d⌋₊) hδ1
  refine ⟨(⌊d⌋₊ : ℝ≥0) + δ', ?_⟩
  have e1 : (v.add (⌊d⌋₊ : ℝ≥0)).add δ = v.add d := by rw [Valuation.add_add, hsum]
  rw [e1, Valuation.add_add] at hδ'
  exact hδ'


end DeepWiki.ReactiveSystems
