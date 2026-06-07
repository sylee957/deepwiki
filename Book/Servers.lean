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

/-- A nondecreasing, left-continuous, piecewise-continuous curve with `f 0 = 0`. -/
structure Curve where
  toFun : ℝ≥0 → ℝ≥0
  mono : Monotone toFun
  zero : toFun 0 = 0
  pwc : IsPiecewiseContinuous toFun
  leftCont : IsLeftContinuous toFun

/-- Apply a `Curve` as its underlying `ℝ≥0 → ℝ≥0` function. -/
instance : CoeFun Curve (fun _ => ℝ≥0 → ℝ≥0) where
  coe := Curve.toFun

/-- Embed a `Curve` into the `(min,plus)` function dioid `Fmin`. -/
instance : Coe Curve Fmin where
  coe := fun A => fun t => ⟨(A.toFun t : ℝ≥0∞)⟩

/-- Pointwise (numeric) order on curves: `D ≤ A ↔ ∀ t, D t ≤ A t`. -/
instance : LE Curve where
  le D A := ∀ t, D.toFun t ≤ A.toFun t

/-- `D ≤ A` unfolds to pointwise numeric `≤`. -/
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
