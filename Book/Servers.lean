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

/-- A curve: a `ℝ≥0 → ℝ≥0` function that is nondecreasing, null at the origin,
piecewise-continuous, and left-continuous. -/
structure Curve where
  /-- The underlying function `ℝ≥0 → ℝ≥0`. -/
  toFun : ℝ≥0 → ℝ≥0
  /-- A curve is nondecreasing. -/
  mono : Monotone toFun
  /-- A curve is zero at the origin: `f 0 = 0`. -/
  zero : IsNullAtOrigin toFun
  /-- A curve is piecewise-continuous. -/
  pwc : IsPiecewiseContinuous toFun
  /-- A curve is left-continuous. -/
  leftCont : IsLeftContinuous toFun

/-- A `Curve` is callable as its underlying function: `A t` means `A.toFun t`. -/
instance : FunLike Curve ℝ≥0 ℝ≥0 where
  coe := Curve.toFun
  coe_injective' f g h := by cases f; cases g; congr

/-- Two curves are equal when equal as functions. -/
@[ext] theorem Curve.ext {A B : Curve} (h : ∀ t, A t = B t) : A = B :=
  DFunLike.ext A B h

/-- Pointwise order on curves: `D ≤ A ↔ ∀ t, D t ≤ A t`. -/
instance : LE Curve where
  le D A := ∀ t, D t ≤ A t

/-- `D ≤ A` on curves unfolds to the pointwise numeric order. -/
theorem Curve.le_def {D A : Curve} : D ≤ A ↔ ∀ t, D t ≤ A t := Iff.rfl

/-- Embed a curve into the `(min,plus)` function dioid `Fmin`. -/
def toFmin (A : Curve) : Fmin := fun t => ⟨(A t : ℝ≥0∞)⟩

/-- Numeric `D ≤ A` is the reversed dioid order on the `Fmin` images. -/
theorem le_iff_toFmin {D A : Curve} :
    D ≤ A ↔ toFmin A ≤ toFmin D := by
  constructor
  · intro h t
    refine (MinPlusNN.le_iff _ _).mpr ?_
    show ((D t : ℝ≥0∞)) ≤ (A t : ℝ≥0∞)
    exact_mod_cast h t
  · intro h t
    have ht := (MinPlusNN.le_iff _ _).mp (h t)
    show D t ≤ A t
    have : ((D t : ℝ≥0∞)) ≤ (A t : ℝ≥0∞) := ht
    exact_mod_cast this

/-- A relation on curves is a server when it is causal (`D ≤ A`) and left-total
(every curve input has an output). -/
def IsServer (S : Set (Curve × Curve)) : Prop :=
  (∀ p ∈ S, p.2 ≤ p.1) ∧ (∀ A : Curve, ∃ D : Curve, (A, D) ∈ S)

/-- A server: a set of curve pairs satisfying `IsServer`. -/
abbrev Server : Type := {S : Set (Curve × Curve) // IsServer S}

/-- `Server` is `SetLike`: it coerces to its underlying set of curve pairs, so
`(A, D) ∈ S` is membership and `S₁ ≤ S₂` is inclusion. -/
instance : SetLike Server (Curve × Curve) where
  coe S := S.val
  coe_injective' := Subtype.val_injective

/-- Subset of servers `S₁ ⊆ S₂`: every member of `S₁` is a member of `S₂`. -/
instance : HasSubset Server := ⟨fun S₁ S₂ => ∀ ⦃p⦄, p ∈ S₁ → p ∈ S₂⟩

/-- `S₁ ⊆ S₂` and `S₁ ≤ S₂` coincide on servers. -/
theorem Server.subset_iff_le {S₁ S₂ : Server} : S₁ ⊆ S₂ ↔ S₁ ≤ S₂ := Iff.rfl

/-- A `Server` is causal: `(A, D) ∈ S → D ≤ A`. -/
theorem Server.causal (S : Server) {A D : Curve} (h : (A, D) ∈ S) : D ≤ A :=
  S.property.1 _ h

/-- A `Server` is left-total: every curve input `A` has an output `D`. -/
theorem Server.leftTotal (S : Server) (A : Curve) : ∃ D : Curve, (A, D) ∈ S :=
  S.property.2 A

end DeepWiki
