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

/-- The underlying `ℝ≥0 → ℝ≥0` function of a `Curve`. -/
def Curve.toFun (A : Curve) : ℝ≥0 → ℝ≥0 := A.1

/-- A `Curve` is nondecreasing. -/
theorem Curve.mono (A : Curve) : Monotone A.toFun := A.2.1

/-- A `Curve` is null at the origin: `A 0 = 0`. -/
theorem Curve.zero (A : Curve) : A.toFun 0 = 0 := A.2.2.1

/-- A `Curve` is piecewise-continuous. -/
theorem Curve.pwc (A : Curve) : IsPiecewiseContinuous A.toFun := A.2.2.2.1

/-- A `Curve` is left-continuous. -/
theorem Curve.leftCont (A : Curve) : IsLeftContinuous A.toFun := A.2.2.2.2

/-- Apply a `Curve` as its underlying `ℝ≥0 → ℝ≥0` function. -/
instance : CoeFun Curve (fun _ => ℝ≥0 → ℝ≥0) where
  coe := Curve.toFun

/-- Embed a `Curve` into the `(min,plus)` function dioid `Fmin`. -/
instance : Coe Curve Fmin where
  coe := fun A => fun t => ⟨(A.toFun t : ℝ≥0∞)⟩

/-- `D ≤ A` (inherited `Subtype`/`Pi` order) unfolds to pointwise numeric `≤`. -/
theorem Curve.le_def {D A : Curve} :
    D ≤ A ↔ ∀ t, D.toFun t ≤ A.toFun t :=
  Iff.rfl

/-- Numeric `D ≤ A` is the reversed dioid order on the `Fmin` images. -/
theorem Curve.le_iff_conv {D A : Curve} :
    D ≤ A ↔ (↑A : Fmin) ≤ (↑D : Fmin) := by
  constructor
  · intro h t
    refine (MinPlusNN.le_iff _ _).mpr ?_
    show ((D.toFun t : ℝ≥0∞)) ≤ (A.toFun t : ℝ≥0∞)
    exact_mod_cast h t
  · intro h t
    have ht := (MinPlusNN.le_iff _ _).mp (h t)
    show D.toFun t ≤ A.toFun t
    have : ((D.toFun t : ℝ≥0∞)) ≤ (A.toFun t : ℝ≥0∞) := ht
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
