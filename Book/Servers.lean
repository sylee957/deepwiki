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
  Monotone f ∧ f 0 = 0 ∧ IsPiecewiseContinuous f ∧ IsLeftContinuous f

/-- A curve: a function `ℝ≥0 → ℝ≥0` satisfying `IsCurve`. -/
abbrev Curve : Type := {f : ℝ≥0 → ℝ≥0 // IsCurve f}

/-- A `Curve` is nondecreasing. -/
theorem Curve.mono (A : Curve) : Monotone A.1 := A.2.1

/-- A `Curve` is null at the origin: `A 0 = 0`. -/
theorem Curve.zero (A : Curve) : A.1 0 = 0 := A.2.2.1

/-- A `Curve` is piecewise-continuous. -/
theorem Curve.pwc (A : Curve) : IsPiecewiseContinuous A.1 := A.2.2.2.1

/-- A `Curve` is left-continuous. -/
theorem Curve.leftCont (A : Curve) : IsLeftContinuous A.1 := A.2.2.2.2

/-- Embed a `Curve` into the `(min,plus)` function dioid `Fmin`. -/
instance : Coe Curve Fmin where
  coe := fun A => fun t => ⟨(A.1 t : ℝ≥0∞)⟩

/-- `D ≤ A` (inherited `Subtype`/`Pi` order) unfolds to pointwise numeric `≤`. -/
theorem Curve.le_def {D A : Curve} :
    D ≤ A ↔ ∀ t, D.1 t ≤ A.1 t :=
  Iff.rfl

/-- Numeric `D ≤ A` is the reversed dioid order on the `Fmin` images. -/
theorem Curve.le_iff_conv {D A : Curve} :
    D ≤ A ↔ (↑A : Fmin) ≤ (↑D : Fmin) := by
  constructor
  · intro h t
    refine (MinPlusNN.le_iff _ _).mpr ?_
    show ((D.1 t : ℝ≥0∞)) ≤ (A.1 t : ℝ≥0∞)
    exact_mod_cast h t
  · intro h t
    have ht := (MinPlusNN.le_iff _ _).mp (h t)
    show D.1 t ≤ A.1 t
    have : ((D.1 t : ℝ≥0∞)) ≤ (A.1 t : ℝ≥0∞) := ht
    exact_mod_cast this

/-- A server: a causal, left-total input/output relation on curves. -/
structure Server where
  rel : Set (Curve × Curve)
  causal : ∀ A D : Curve, (A, D) ∈ rel → D ≤ A
  leftTotal : ∀ A : Curve, ∃ D : Curve, (A, D) ∈ rel

/-- Membership `(A, D) ∈ S` reads through to `S.rel`. -/
instance : Membership (Curve × Curve) Server where
  mem S p := p ∈ S.rel

/-- `S` maps input `A` to output `D`, i.e. `(A, D) ∈ S`. -/
def Serves (S : Server) (A D : Curve) : Prop :=
  (A, D) ∈ S

/-- Notation `A ⟶[S] D` for `Serves S A D`. -/
scoped notation:50 A:51 " ⟶[" S "] " D:51 =>
  Serves S A D

end DeepWiki
