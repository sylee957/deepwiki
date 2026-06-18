import DeepWiki.ReactiveSystems.TimedRegions

/-! # Computable region codes (executable leaf check)
The decision procedure for timed model checking cannot run on the real-valued region
quotient `Region cmax` (its fingerprint `regionFingerprint` is `noncomputable` — it
decides real comparisons via `Classical`). Instead it runs on `RegionCode cmax`, the
*combinatorial* codomain of `regionFingerprint` — clamped floors, frac-zero bits, and
frac-order bits — a genuine `Fintype` with `DecidableEq`. A Bool leaf check
`RegionCode.satisfies` decides a bounded clock constraint from a code, proven to agree
with the real-valued `satisfies` on the fingerprint of any valuation
(`regionCode_satisfies_iff`). The `noncomputable` `regionFingerprint` appears only in
the *correctness* statement, never in the computation. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

variable {C : Type*}

/-- A **region code**: the combinatorial data of a region — per-clock clamped floor
(`Fin (cmax x + 2)`), frac-zero bits, frac-order bits — the computable codomain of
`regionFingerprint`. A genuine `Fintype`/`DecidableEq` for finitely many clocks. -/
abbrev RegionCode (cmax : C → ℕ) : Type _ :=
  (∀ x, Fin (cmax x + 2)) × (C → Bool) × (C → C → Bool)

/-- The Bool decision of a comparison `· ⋈ n` from a clamped floor `f` and a frac-zero
bit `z`: below the clamp the floor and frac-zero status decide it, at/above the clamp
the floor saturates. (`gt`/`ge` are the Bool negations of `le`/`lt`.) -/
def RegionCode.cmpHolds (f : ℕ) (z : Bool) : Cmp → ℕ → Bool
  | .le, n => decide (f < n) || (decide (f = n) && z)
  | .lt, n => decide (f < n)
  | .eq, n => decide (f = n) && z
  | .gt, n => !(decide (f < n) || (decide (f = n) && z))
  | .ge, n => !decide (f < n)

/-- The Bool decision of an atom `x ⋈ n` against a region code, from clock `x`'s clamped
floor and frac-zero bit. -/
def RegionCode.holds {cmax : C → ℕ} (γ : RegionCode cmax) (x : C) (cmp : Cmp) (n : ℕ) : Bool :=
  RegionCode.cmpHolds (γ.1 x).val (γ.2.1 x) cmp n

/-- The Bool decision of a whole clock constraint against a region code. -/
def RegionCode.satisfies {cmax : C → ℕ} (γ : RegionCode cmax) : ClockConstraint C → Bool
  | .true_ => true
  | .atom x cmp n => RegionCode.holds γ x cmp n
  | .and g₁ g₂ => RegionCode.satisfies γ g₁ && RegionCode.satisfies γ g₂

section Fintype
variable [Fintype C] [DecidableEq C]

/-- Region codes form a finite type (finitely many clocks). -/
example (cmax : C → ℕ) : Fintype (RegionCode cmax) := inferInstance

/-- Region codes have decidable equality. -/
example (cmax : C → ℕ) : DecidableEq (RegionCode cmax) := inferInstance

end Fintype

/-- `regionFingerprint`'s floor component is the clamped region floor. -/
theorem regionFingerprint_floor (cmax : C → ℕ) (v : Valuation C) (x : C) :
    ((regionFingerprint cmax v).1 x).val = regionFloor cmax v x := rfl

open Classical in
/-- `regionFingerprint`'s frac-zero bit equals the classical decision of boundedness with
zero fractional part. -/
theorem regionFingerprint_fracZero (cmax : C → ℕ) (v : Valuation C) (x : C) :
    (regionFingerprint cmax v).2.1 x = decide (v x ≤ cmax x ∧ fracPart (v x) = 0) := rfl

open Classical in
/-- **Atomic agreement.** The Bool leaf check on `regionFingerprint cmax v` decides the
real comparison `cmp.holds (v x) n` for any bound `n ≤ cmax x`. -/
theorem regionCode_holds_iff {cmax : C → ℕ} (v : Valuation C) (x : C) (cmp : Cmp) {n : ℕ}
    (hn : n ≤ cmax x) :
    RegionCode.holds (regionFingerprint cmax v) x cmp n = true ↔ cmp.holds (v x) n := by
  unfold RegionCode.holds
  rw [regionFingerprint_floor, regionFingerprint_fracZero]
  by_cases hb : v x ≤ cmax x
  · rw [show regionFloor cmax v x = ⌊v x⌋₊ from by unfold regionFloor; rw [if_pos hb]]
    rw [show decide (v x ≤ cmax x ∧ fracPart (v x) = 0) = decide (fracPart (v x) = 0) from by
      rw [decide_eq_decide]; exact and_iff_right hb]
    have flt : (⌊v x⌋₊ < n) ↔ (v x < (n : ℝ≥0)) := Nat.floor_lt (zero_le')
    have feq : (v x = (n : ℝ≥0)) ↔ (⌊v x⌋₊ = n ∧ fracPart (v x) = 0) := by
      constructor
      · intro h; rw [h]; exact ⟨Nat.floor_natCast n, fracPart_natCast n⟩
      · rintro ⟨h1, h2⟩; rw [← (fracPart_eq_zero_iff (v x)).mp h2, h1]
    have hle : (RegionCode.cmpHolds ⌊v x⌋₊ (decide (fracPart (v x) = 0)) Cmp.le n = true) ↔
        v x ≤ ↑n := by
      simp only [RegionCode.cmpHolds, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff]
      rw [le_iff_lt_or_eq]; exact or_congr flt feq.symm
    have hlt : (RegionCode.cmpHolds ⌊v x⌋₊ (decide (fracPart (v x) = 0)) Cmp.lt n = true) ↔
        v x < ↑n := by
      simp only [RegionCode.cmpHolds, decide_eq_true_iff]; exact flt
    cases cmp
    · exact hle
    · exact hlt
    · simp only [RegionCode.cmpHolds, Cmp.holds, Bool.and_eq_true, decide_eq_true_iff]
      exact feq.symm
    · show (!(RegionCode.cmpHolds ⌊v x⌋₊ (decide (fracPart (v x) = 0)) Cmp.le n)) = true ↔ (v x > ↑n)
      rw [Bool.not_eq_true', ← Bool.not_eq_true, hle, gt_iff_lt]; exact not_le
    · show (!(RegionCode.cmpHolds ⌊v x⌋₊ (decide (fracPart (v x) = 0)) Cmp.lt n)) = true ↔ (v x ≥ ↑n)
      rw [Bool.not_eq_true', ← Bool.not_eq_true, hlt, ge_iff_le]; exact not_lt
  · rw [show regionFloor cmax v x = cmax x + 1 from by unfold regionFloor; rw [if_neg hb]]
    rw [show decide (v x ≤ cmax x ∧ fracPart (v x) = 0) = false from by
      rw [decide_eq_false_iff_not]; rintro ⟨h, _⟩; exact hb h]
    have hvn : (↑n : ℝ≥0) < v x := lt_of_le_of_lt (by exact_mod_cast hn) (not_le.mp hb)
    have dfn : decide (cmax x + 1 < n) = false := by rw [decide_eq_false_iff_not]; omega
    cases cmp
    · refine iff_of_false ?_ (not_le.mpr hvn); simp [RegionCode.cmpHolds, dfn]
    · refine iff_of_false ?_ (not_lt.mpr hvn.le); simp [RegionCode.cmpHolds, dfn]
    · refine iff_of_false ?_ (ne_of_gt hvn); simp [RegionCode.cmpHolds]
    · refine iff_of_true ?_ hvn; simp [RegionCode.cmpHolds, dfn]
    · refine iff_of_true ?_ hvn.le; simp [RegionCode.cmpHolds, dfn]

/-- **Leaf-check agreement.** The Bool check `RegionCode.satisfies` on `regionFingerprint
cmax v` decides the real-valued `satisfies v g` for any constraint `g` bounded by `cmax`. -/
theorem regionCode_satisfies_iff {cmax : C → ℕ} (v : Valuation C) :
    ∀ {g : ClockConstraint C}, g.BoundedBy cmax →
      (RegionCode.satisfies (regionFingerprint cmax v) g = true ↔ satisfies v g) := by
  intro g
  induction g with
  | true_ => intro _; simp [RegionCode.satisfies, satisfies]
  | atom x cmp n => intro hg; exact regionCode_holds_iff v x cmp hg
  | and g₁ g₂ ih₁ ih₂ =>
      intro hg
      simp only [RegionCode.satisfies, satisfies, Bool.and_eq_true]
      exact and_congr (ih₁ hg.1) (ih₂ hg.2)

end DeepWiki.ReactiveSystems
