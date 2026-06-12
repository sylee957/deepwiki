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

/-- Pointwise sum of curves is a curve: monotonicity, null at origin, and
left-continuity are termwise; the discontinuities of the sum lie in the
union of the summands' (finite) discontinuity sets. -/
noncomputable instance : Add Curve where
  add A B :=
    { toFun := fun t => A t + B t
      mono := fun _ _ h => add_le_add (A.mono h) (B.mono h)
      zero := by
        have hA : A 0 = 0 := A.zero
        have hB : B 0 = 0 := B.zero
        show A 0 + B 0 = 0
        rw [hA, hB, add_zero]
      pwc := by
        intro T
        refine Set.Finite.subset ((A.pwc T).union (B.pwc T)) ?_
        rintro t ⟨ht, htm⟩
        by_cases hA : ContinuousAt (⇑A) t
        · by_cases hB : ContinuousAt (⇑B) t
          · exact absurd (hA.add hB) ht
          · exact Or.inr ⟨hB, htm⟩
        · exact Or.inl ⟨hA, htm⟩
      leftCont := fun t => (A.leftCont t).add (B.leftCont t) }

/-- `(A + B) t = A t + B t`: curve addition is pointwise. -/
@[simp] theorem Curve.add_apply (A B : Curve) (t : ℝ≥0) :
    (A + B) t = A t + B t := rfl

/-- The zero curve: no data ever arrives or departs. -/
noncomputable def zeroCurve : Curve :=
  ⟨fun _ => 0, monotone_const, rfl,
    isPiecewiseContinuous_of_continuous _ continuous_const,
    isLeftContinuous_of_continuous _ continuous_const⟩

/-- `zeroCurve t = 0`. -/
@[simp] theorem zeroCurve_apply (t : ℝ≥0) : zeroCurve t = 0 := rfl

/-- The zero curve is the zero of the curve monoid. -/
noncomputable instance : Zero Curve := ⟨zeroCurve⟩

/-- Curves form an additive commutative monoid under pointwise sum with
`zeroCurve` as zero — the carrier for aggregating finitely many flows. -/
noncomputable instance : _root_.AddCommMonoid Curve where
  add_assoc A B C := Curve.ext fun t => add_assoc (A t) (B t) (C t)
  zero := zeroCurve
  zero_add A := Curve.ext fun t => zero_add (A t)
  add_zero A := Curve.ext fun t => add_zero (A t)
  add_comm A B := Curve.ext fun t => add_comm (A t) (B t)
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl

/-- The zero of the curve monoid is `zeroCurve`. -/
theorem Curve.zero_def : (0 : Curve) = zeroCurve := rfl

/-- `(0 : Curve) t = 0`. -/
@[simp] theorem Curve.zero_apply (t : ℝ≥0) : (0 : Curve) t = 0 := rfl

/-- Evaluation at `t` as an additive monoid morphism `Curve →+ ℝ≥0`. -/
noncomputable def Curve.evalHom (t : ℝ≥0) : Curve →+ ℝ≥0 where
  toFun A := A t
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A finite sum of curves evaluates pointwise:
`(∑ i ∈ s, A i) t = ∑ i ∈ s, A i t`. -/
@[simp] theorem Curve.sum_apply {ι : Type*} (s : Finset ι) (A : ι → Curve)
    (t : ℝ≥0) : (∑ i ∈ s, A i) t = ∑ i ∈ s, A i t :=
  map_sum (Curve.evalHom t) A s

/-- The underlying function of a finite sum of curves is the pointwise
sum of the underlying functions. -/
theorem Curve.coe_sum {ι : Type*} (s : Finset ι) (A : ι → Curve) :
    ⇑(∑ i ∈ s, A i) = fun t => ∑ i ∈ s, A i t :=
  funext fun t => Curve.sum_apply s A t

/-- Lift a `Curve` into the `(min,plus)` function dioid `Fmin` via `liftFmin`. -/
abbrev Curve.liftFmin (A : Curve) : Fmin := DeepWiki.liftFmin ⇑A

/-- Numeric `D ≤ A` is the reversed dioid order on the `Fmin` images. -/
theorem Curve.le_iff_liftFmin_le {D A : Curve} :
    D ≤ A ↔ A.liftFmin ≤ D.liftFmin := by
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

/-- `S` is causal: an output never exceeds its input, `S A D → D ≤ A`. -/
def IsCausal (S : Curve → Curve → Prop) : Prop :=
  ∀ A D : Curve, S A D → D ≤ A

/-- `S` is left-total: every curve input `A` has an output `D` (`Relator.LeftTotal`). -/
def IsLeftTotal (S : Curve → Curve → Prop) : Prop :=
  ∀ A : Curve, ∃ D : Curve, S A D

/-- A relation `S` on curves is a server when it is causal and left-total. -/
def IsServer (S : Curve → Curve → Prop) : Prop :=
  IsCausal S ∧ IsLeftTotal S

end DeepWiki
