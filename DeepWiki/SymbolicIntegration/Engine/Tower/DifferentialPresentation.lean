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

/-- Build a one-step explicit tower presentation from a chosen monomial derivative over `ℚ`. -/
noncomputable def oneStep (Dt : DensePoly ℚ) : DifferentialTowerPresentation 1 where
  derivation
    | 0, _ => CFieldDerivation.ofCDiffField ℚ
    | 1, _ =>
      ⟨CFrac.towerDerivCFracWithDerivation (CFieldDerivation.ofCDiffField ℚ) Dt⟩
    | n + 2, hn => False.elim (by omega)
  differential
    | 0, _ => instDifferentialQ
    | 1, _ => by
      letI : Differential (CRingSpec.R ℚ) := instDifferentialQ
      exact fractionFieldDifferential (Differential.implicitDeriv (CPoly.toPoly Dt))
    | n + 2, hn => False.elim (by omega)
  lawful
    | 0, _ => LawfulCFieldDerivation.ofCDiffField ℚ
    | 1, _ => by
      letI : LawfulCFieldDerivation ℚ (CFieldDerivation.ofCDiffField ℚ) instDifferentialQ :=
        LawfulCFieldDerivation.ofCDiffField ℚ
      refine ⟨?_⟩
      intro x
      rw [denseFracTower_toK_succ]
      change CFrac.toRatFunc
          (CFrac.towerDerivCFracWithDerivation (CFieldDerivation.ofCDiffField ℚ) Dt x) =
        @Differential.deriv _ _
          (fractionFieldDifferential (Differential.implicitDeriv (CPoly.toPoly Dt)))
          (CFrac.toRatFunc x)
      rw [fractionFieldDifferential_deriv]
      exact CFrac.toRatFunc_towerDerivCFracWithDerivation
        (CFieldDerivation.ofCDiffField ℚ) instDifferentialQ Dt x
    | n + 2, hn => False.elim (by omega)
  monomialDerivative
    | 0, _ => Dt
    | n + 1, hn => False.elim (by omega)
  successor
    | 0, _, x => rfl
    | n + 1, hn, x => False.elim (by omega)
  successorSemantics
    | 0, _, x => by
      letI : LawfulCFieldDerivation ℚ (CFieldDerivation.ofCDiffField ℚ) instDifferentialQ :=
        LawfulCFieldDerivation.ofCDiffField ℚ
      rw [denseFracTower_toK_succ]
      exact CFrac.toRatFunc_towerDerivCFracWithDerivation
        (CFieldDerivation.ofCDiffField ℚ) instDifferentialQ Dt x
    | n + 1, hn, x => False.elim (by omega)

/-- The one-step primitive presentation has `t′ = 1`. -/
noncomputable def primitiveOneStep : DifferentialTowerPresentation 1 := oneStep [1]

/-- The one-step exponential presentation has `t′ = t`. -/
noncomputable def exponentialOneStep : DifferentialTowerPresentation 1 := oneStep [0, 1]

/-- The one-step tangent presentation has `t′ = t² + 1`. -/
noncomputable def tangentOneStep : DifferentialTowerPresentation 1 := oneStep [1, 0, 1]

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
