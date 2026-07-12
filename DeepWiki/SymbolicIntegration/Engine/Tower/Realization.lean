import DeepWiki.SymbolicIntegration.Engine.DifferentialAlgebraicClosure
import DeepWiki.SymbolicIntegration.Engine.LrtSoundness
import DeepWiki.SymbolicIntegration.Engine.Tower.CarrierRec

/-! # Recursive semantic realizations of transcendental towers

An LRT certificate at depth `n` lives in a rational-function field over an algebraic closure of
the depth-`n` coefficient field.  A successor must embed that whole function field as
coefficients before adding its own logarithms.  `TowerRealization` records precisely this
recursive field chain; it replaces the unsound idea that all levels can be evaluated directly in
one final field.
-/

namespace DeepWiki.SymbolicIntegration

universe u

/-- The finite index corresponding to a realized tower depth. -/
def TowerRealization.index {N n : ℕ} (hn : n ≤ N) : Fin (N + 1) :=
  ⟨n, Nat.lt_succ_iff.mpr hn⟩

/-- A finite recursive field realization for the represented dense fraction tower.

`carrier n` is an algebraically closed differential coefficient field for depth `n`.  The
successor carrier contains `RatFunc (carrier n)` as a differential subfield, and `coherent` says
that this embedding agrees with the represented dense-fraction tower inclusion. -/
structure TowerRealization (N : ℕ) where
  /-- Algebraically closed coefficient field selected at each realized depth. -/
  carrier : Fin (N + 1) → Type u
  /-- Field structure on every selected coefficient field. -/
  field : ∀ i, Field (carrier i)
  /-- Differential-field structure on every selected coefficient field. -/
  differential : ∀ i, Differential (carrier i)
  /-- Characteristic-zero structure on every selected coefficient field. -/
  charZero : ∀ i, CharZero (carrier i)
  /-- Rational scalar algebra on every selected coefficient field. -/
  algebraQ : ∀ i, Algebra ℚ (carrier i)
  /-- Algebraic closedness of every selected coefficient field. -/
  isAlgClosed : ∀ i, IsAlgClosed (carrier i)
  /-- Embed each represented coefficient field into its selected realization. -/
  algebra : ∀ n (hn : n ≤ N), Algebra (CFieldSpec.K (DenseFracTower n))
    (carrier (TowerRealization.index hn))
  /-- The represented derivation commutes with each coefficient-field embedding. -/
  differentialAlgebra : ∀ n (hn : n ≤ N),
    letI : Field (carrier (TowerRealization.index hn)) := field (TowerRealization.index hn)
    letI : Differential (carrier (TowerRealization.index hn)) := differential (TowerRealization.index hn)
    letI : Algebra (CFieldSpec.K (DenseFracTower n)) (carrier (TowerRealization.index hn)) := algebra n hn
    DifferentialAlgebra (CFieldSpec.K (DenseFracTower n)) (carrier (TowerRealization.index hn))
  /-- The represented monomial derivative selected at every strict successor level. -/
  monomialDerivative : ∀ n (_ : n + 1 ≤ N), DensePoly (DenseFracTower n)
  /-- The concrete monomial derivation carried by a realized successor field. -/
  stepDifferential : ∀ n (hn : n + 1 ≤ N),
    letI : Field (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))) :=
      field (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))
    letI : Differential (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))) :=
      differential (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))
    Differential (RatFunc (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))))
  /-- The selected function-field differential is the extension induced by its monomial derivative. -/
  stepDifferential_eq : ∀ n (hn : n + 1 ≤ N),
    letI : Field (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))) :=
      field (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))
    letI : Differential (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))) :=
      differential (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))
    letI : Algebra ℚ (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))) :=
      algebraQ (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))
    letI : Algebra (CFieldSpec.K (DenseFracTower n))
        (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))) :=
      algebra n (Nat.le_trans (Nat.le_succ n) hn)
    ∀ x : RatFunc (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))),
      @Differential.deriv (RatFunc (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))))
          _ (stepDifferential n hn) x =
        towerDerivExt (E := carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn)))
          (monomialDerivative n hn) x
  /-- Embed each realized function field into the next coefficient field. -/
  stepAlgebra : ∀ n (hn : n + 1 ≤ N),
    letI : Field (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))) :=
      field (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))
    letI : Field (carrier (TowerRealization.index hn)) := field (TowerRealization.index hn)
    Algebra (RatFunc (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))))
      (carrier (TowerRealization.index hn))
  /-- The successor embedding commutes with the selected function-field derivation. -/
  stepDifferentialAlgebra : ∀ n (hn : n + 1 ≤ N),
    letI : Field (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))) :=
      field (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))
    letI : Differential (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))) :=
      differential (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))
    letI : Differential (RatFunc (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn)))) :=
      stepDifferential n hn
    letI : Field (carrier (TowerRealization.index hn)) := field (TowerRealization.index hn)
    letI : Differential (carrier (TowerRealization.index hn)) := differential (TowerRealization.index hn)
    letI : Algebra (RatFunc (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))))
        (carrier (TowerRealization.index hn)) := stepAlgebra n hn
    DifferentialAlgebra (RatFunc (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))))
      (carrier (TowerRealization.index hn))
  /-- The successor represented-field map factors through the prior realized function field. -/
  coherent : ∀ n (hn : n + 1 ≤ N),
    letI : Field (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))) :=
      field (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))
    letI : Differential (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))) :=
      differential (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))
    letI : Algebra ℚ (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))) :=
      algebraQ (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))
    letI : Algebra (CFieldSpec.K (DenseFracTower n))
        (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))) :=
      algebra n (Nat.le_trans (Nat.le_succ n) hn)
    letI : Field (carrier (TowerRealization.index hn)) := field (TowerRealization.index hn)
    letI : Algebra (RatFunc (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))))
        (carrier (TowerRealization.index hn)) := stepAlgebra n hn
    letI : Algebra (CFieldSpec.K (DenseFracTower (n + 1))) (carrier (TowerRealization.index hn)) :=
      algebra (n + 1) hn
    (algebraMap (RatFunc (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))))
      (carrier (TowerRealization.index hn))).comp
        (ratFuncBaseChange (α := DenseFracTower n)
          (carrier (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn)))) =
      algebraMap (CFieldSpec.K (DenseFracTower (n + 1))) (carrier (TowerRealization.index hn))

namespace TowerRealization

/-- The selected coefficient field at a realized depth. -/
abbrev Carrier (R : TowerRealization N) (n : ℕ) (hn : n ≤ N) : Type u :=
  R.carrier (TowerRealization.index hn)

/-- The represented-field embedding at a realized depth. -/
noncomputable def map (R : TowerRealization N) (n : ℕ) (hn : n ≤ N) :
    letI : Field (R.Carrier n hn) := R.field (TowerRealization.index hn)
    CFieldSpec.K (DenseFracTower n) →+* R.Carrier n hn := by
  letI : Field (R.Carrier n hn) := R.field (TowerRealization.index hn)
  letI : Algebra (CFieldSpec.K (DenseFracTower n)) (R.Carrier n hn) := R.algebra n hn
  exact algebraMap _ _

/-- The map of the prior realized function field into the successor coefficient field. -/
noncomputable def lift (R : TowerRealization N) (n : ℕ) (hn : n + 1 ≤ N) :
    letI : Field (R.Carrier n (Nat.le_trans (Nat.le_succ n) hn)) :=
      R.field (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))
    letI : Field (R.Carrier (n + 1) hn) := R.field (TowerRealization.index hn)
    RatFunc (R.Carrier n (Nat.le_trans (Nat.le_succ n) hn)) →+*
      R.Carrier (n + 1) hn := by
  letI : Field (R.Carrier n (Nat.le_trans (Nat.le_succ n) hn)) :=
    R.field (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))
  letI : Field (R.Carrier (n + 1) hn) := R.field (TowerRealization.index hn)
  letI : Algebra (RatFunc (R.Carrier n (Nat.le_trans (Nat.le_succ n) hn)))
      (R.Carrier (n + 1) hn) := R.stepAlgebra n hn
  exact algebraMap _ _

/-- The successor realization lift commutes with differentiation. -/
theorem lift_deriv (R : TowerRealization N) (n : ℕ) (hn : n + 1 ≤ N) :
    letI : Field (R.Carrier n (Nat.le_trans (Nat.le_succ n) hn)) :=
      R.field (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))
    letI : Differential (R.Carrier n (Nat.le_trans (Nat.le_succ n) hn)) :=
      R.differential (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))
    letI : Differential (RatFunc (R.Carrier n (Nat.le_trans (Nat.le_succ n) hn))) :=
      R.stepDifferential n hn
    letI : Field (R.Carrier (n + 1) hn) := R.field (TowerRealization.index hn)
    letI : Differential (R.Carrier (n + 1) hn) := R.differential (TowerRealization.index hn)
    letI : Algebra (RatFunc (R.Carrier n (Nat.le_trans (Nat.le_succ n) hn)))
        (R.Carrier (n + 1) hn) := R.stepAlgebra n hn
    letI : DifferentialAlgebra (RatFunc (R.Carrier n (Nat.le_trans (Nat.le_succ n) hn)))
        (R.Carrier (n + 1) hn) := R.stepDifferentialAlgebra n hn
    ∀ x : RatFunc (R.Carrier n (Nat.le_trans (Nat.le_succ n) hn)),
      R.lift n hn (Differential.deriv x) = Differential.deriv (R.lift n hn x) := by
  letI : Field (R.Carrier n (Nat.le_trans (Nat.le_succ n) hn)) :=
    R.field (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))
  letI : Differential (R.Carrier n (Nat.le_trans (Nat.le_succ n) hn)) :=
    R.differential (TowerRealization.index (Nat.le_trans (Nat.le_succ n) hn))
  letI : Differential (RatFunc (R.Carrier n (Nat.le_trans (Nat.le_succ n) hn))) :=
    R.stepDifferential n hn
  letI : Field (R.Carrier (n + 1) hn) := R.field (TowerRealization.index hn)
  letI : Differential (R.Carrier (n + 1) hn) := R.differential (TowerRealization.index hn)
  letI : Algebra (RatFunc (R.Carrier n (Nat.le_trans (Nat.le_succ n) hn)))
      (R.Carrier (n + 1) hn) := R.stepAlgebra n hn
  letI : DifferentialAlgebra (RatFunc (R.Carrier n (Nat.le_trans (Nat.le_succ n) hn)))
      (R.Carrier (n + 1) hn) := R.stepDifferentialAlgebra n hn
  intro x
  change algebraMap (RatFunc (R.Carrier n (Nat.le_trans (Nat.le_succ n) hn)))
      (R.Carrier (n + 1) hn) (Differential.deriv x) =
    Differential.deriv
      (algebraMap (RatFunc (R.Carrier n (Nat.le_trans (Nat.le_succ n) hn)))
        (R.Carrier (n + 1) hn) x)
  exact (DifferentialAlgebra.deriv_algebraMap x).symm

end TowerRealization

end DeepWiki.SymbolicIntegration
