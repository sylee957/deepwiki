import Book.Continuity
import Book.FunctionDioids

/-!
# Servers and service curves
Arrival/departure curves (`Curve`) and servers as causal,
left-total input/output relations.
-/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge

/-- A function `ℝ≥0 → ℝ≥0` is a curve when it is nondecreasing, null at the
origin, piecewise-continuous, and left-continuous. -/
def IsCurve (f : ℝ≥0 → ℝ≥0) : Prop :=
  Monotone f ∧ IsNullAtOrigin f ∧ IsPiecewiseContinuous f ∧ IsLeftContinuous f

/-- A curve: a function `ℝ≥0 → ℝ≥0` satisfying `IsCurve`. -/
abbrev Curve : Type := {f : ℝ≥0 → ℝ≥0 // IsCurve f}

/-- A `Curve` is nondecreasing. -/
theorem Curve.mono (A : Curve) : Monotone A.val := A.property.1

/-- A `Curve` is null at the origin: `A 0 = 0`. -/
theorem Curve.zero (A : Curve) : A.val 0 = 0 := A.property.2.1

/-- A `Curve` is piecewise-continuous. -/
theorem Curve.pwc (A : Curve) : IsPiecewiseContinuous A.val := A.property.2.2.1

/-- A `Curve` is left-continuous. -/
theorem Curve.leftCont (A : Curve) : IsLeftContinuous A.val := A.property.2.2.2

/-- Embed a `Curve` into the `(min,plus)` function dioid `Fmin`. -/
instance : Coe Curve Fmin where
  coe := fun A => fun t => ⟨(A.val t : ℝ≥0∞)⟩

/-- `D ≤ A` (inherited `Subtype`/`Pi` order) unfolds to pointwise numeric `≤`. -/
theorem Curve.le_def {D A : Curve} :
    D ≤ A ↔ ∀ t, D.val t ≤ A.val t :=
  Iff.rfl

/-- Numeric `D ≤ A` is the reversed dioid order on the `Fmin` images. -/
theorem Curve.le_iff_conv {D A : Curve} :
    D ≤ A ↔ (↑A : Fmin) ≤ (↑D : Fmin) := by
  constructor
  · intro h t
    refine (MinPlusNN.le_iff _ _).mpr ?_
    show ((D.val t : ℝ≥0∞)) ≤ (A.val t : ℝ≥0∞)
    exact_mod_cast h t
  · intro h t
    have ht := (MinPlusNN.le_iff _ _).mp (h t)
    show D.val t ≤ A.val t
    have : ((D.val t : ℝ≥0∞)) ≤ (A.val t : ℝ≥0∞) := ht
    exact_mod_cast this

/-- A relation on curves is a server when it is causal (`D ≤ A`) and
left-total (every input has an output). -/
def IsServer (rel : Set (Curve × Curve)) : Prop :=
  (∀ A D : Curve, (A, D) ∈ rel → D ≤ A) ∧
    (∀ A : Curve, ∃ D : Curve, (A, D) ∈ rel)

/-- A server: a relation on curves satisfying `IsServer`. -/
abbrev Server : Type := {rel : Set (Curve × Curve) // IsServer rel}

/-- A `Server` is causal: `(A, D) ∈ S → D ≤ A`. -/
theorem Server.causal (S : Server) :
    ∀ A D : Curve, (A, D) ∈ S.val → D ≤ A := S.property.1

/-- A `Server` is left-total: every input `A` has an output `D`. -/
theorem Server.leftTotal (S : Server) :
    ∀ A : Curve, ∃ D : Curve, (A, D) ∈ S.val := S.property.2

end DeepWiki
