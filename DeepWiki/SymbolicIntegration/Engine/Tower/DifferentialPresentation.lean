import DeepWiki.SymbolicIntegration.Engine.Tower.CarrierRec

/-! # Explicit differential presentations of finite represented towers

`DenseFracTower` fixes a legacy primitive derivative through its global `CDiffField` instance. A
`DifferentialTowerPresentation` instead carries the computable and mathematical derivatives at
each finite depth as explicit data. Its successor square is stated with an explicit lower
differential, so exponential and tangent monomials cannot accidentally fall back to `t′ = 1`.
-/

namespace DeepWiki.SymbolicIntegration

/-- A finite represented-fraction tower with explicitly selected, coherent differential data. -/
structure DifferentialTowerPresentation (N : ℕ) where
  /-- The selected computable coefficient derivative at every realized tower depth. -/
  derivation : ∀ n, n ≤ N → CFieldDerivation (DenseFracTower n)
  /-- The mathematical differential selected at every realized tower depth. -/
  differential : ∀ n, n ≤ N → Differential (CFieldSpec.K (DenseFracTower n))
  /-- Each computable derivative realizes its explicitly selected mathematical differential. -/
  lawful : ∀ n (hn : n ≤ N),
    LawfulCFieldDerivation (DenseFracTower n) (derivation n hn) (differential n hn)
  /-- The derivative of the newly adjoined monomial at each strict successor depth. -/
  monomialDerivative : ∀ n, n + 1 ≤ N → DensePoly (DenseFracTower n)
  /-- Each selected successor derivative is the quotient-rule extension of the preceding one. -/
  successor : ∀ n (hn : n + 1 ≤ N) (x : DenseFracTower (n + 1)),
    (derivation (n + 1) hn).cderiv x =
      CFrac.towerDerivCFracWithDerivation
        (derivation n (Nat.le_trans (Nat.le_succ n) hn)) (monomialDerivative n hn) x
  /-- The successor quotient-rule square commutes with the explicitly selected lower differential. -/
  successorSemantics : ∀ n (hn : n + 1 ≤ N) (x : DenseFracTower (n + 1)),
    let hprev : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
    letI : Differential (CFieldSpec.K (DenseFracTower n)) := differential n hprev
    letI : Differential (CRingSpec.R (DenseFracTower n)) := differential n hprev
    letI : Algebra ℚ (CRingSpec.R (DenseFracTower n)) := by
      change Algebra ℚ (CFieldSpec.K (DenseFracTower n))
      infer_instance
    CFieldSpec.toK ((derivation (n + 1) hn).cderiv x) =
      extendDeriv (Differential.implicitDeriv (CPoly.toPoly (monomialDerivative n hn)))
        (CFieldSpec.toK x)

namespace DifferentialTowerPresentation

/-- The legacy dense fraction tower, viewed as the all-primitive explicit presentation. -/
noncomputable def primitive (N : ℕ) : DifferentialTowerPresentation N where
  derivation n _ := CFieldDerivation.ofCDiffField (DenseFracTower n)
  differential n _ := CDiffFieldSpec.diffK
  lawful n _ := LawfulCFieldDerivation.ofCDiffField (DenseFracTower n)
  monomialDerivative n _ := CPoly.one
  successor n _ x := rfl
  successorSemantics n _ x := by
    rw [denseFracTower_toK_succ]
    exact CFrac.toRatFunc_towerDerivCFracWith (P := DensePoly) (F := DenseFrac) CPoly.one x

/-- The selected derivative commutes with its field denotation at every realized depth. -/
theorem toK_cderiv (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n ≤ N)
    (x : DenseFracTower n) :
    CFieldSpec.toK ((T.derivation n hn).cderiv x) =
      @Differential.deriv _ _ (T.differential n hn) (CFieldSpec.toK x) :=
  (T.lawful n hn).toK_cderiv x

/-- The successor operation of a presentation is its selected quotient-rule extension. -/
theorem successor_cderiv (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n + 1 ≤ N)
    (x : DenseFracTower (n + 1)) :
    (T.derivation (n + 1) hn).cderiv x =
      CFrac.towerDerivCFracWithDerivation
        (T.derivation n (Nat.le_trans (Nat.le_succ n) hn)) (T.monomialDerivative n hn) x :=
  T.successor n hn x

/-- The successor semantic square is available without resolving a global differential instance. -/
theorem successor_toK_cderiv (T : DifferentialTowerPresentation N) (n : ℕ) (hn : n + 1 ≤ N)
    (x : DenseFracTower (n + 1)) :
    let hprev : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
    letI : Differential (CFieldSpec.K (DenseFracTower n)) := T.differential n hprev
    letI : Differential (CRingSpec.R (DenseFracTower n)) := T.differential n hprev
    letI : Algebra ℚ (CRingSpec.R (DenseFracTower n)) := by
      change Algebra ℚ (CFieldSpec.K (DenseFracTower n))
      infer_instance
    CFieldSpec.toK ((T.derivation (n + 1) hn).cderiv x) =
      extendDeriv (Differential.implicitDeriv (CPoly.toPoly (T.monomialDerivative n hn)))
        (CFieldSpec.toK x) :=
  T.successorSemantics n hn x

end DifferentialTowerPresentation

end DeepWiki.SymbolicIntegration
