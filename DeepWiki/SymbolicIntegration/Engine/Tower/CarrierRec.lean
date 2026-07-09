import DeepWiki.SymbolicIntegration.Engine.Tower.Deriv
import DeepWiki.SymbolicIntegration.Core.Differential.FractionFieldDeriv

/-! # Global-recursive tower-carrier instances

Since `CFieldSpec.K (CFrac α) = RatFunc (CFieldSpec.K α)` (Tower/Field), the base-field structure the Risch
tower needs on `CFieldSpec.K` — `CharZero`, `Algebra ℚ` — is **preserved by `RatFunc`**, so it iterates by one
global recursive instance each (base + step). This replaces the `noncomputable local instance … :=
inferInstanceAs (… (RatFunc ℚ))` copies that pinned the tower to the concrete `ℚ` base and blocked a single
recursive tower solver. With these, `CharZero (CFieldSpec.K (CFracGⁿ ℚ))` / `Algebra ℚ (…)` resolve at every
depth automatically. -/

namespace DeepWiki.SymbolicIntegration


/-- **`CharZero` iterates up the tower.** `CFieldSpec.K (CFrac α) = RatFunc (CFieldSpec.K α)` is `CharZero`
whenever `CFieldSpec.K α` is — one recursive instance for the whole tower. -/
noncomputable instance instCharZeroKCFrac {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α]
    [CharZero (CFieldSpec.K α)] : CharZero (CFieldSpec.K (CFrac α)) :=
  inferInstanceAs (CharZero (RatFunc (CFieldSpec.K α)))

/-- **`Algebra ℚ` iterates up the tower.** `RatFunc (CFieldSpec.K α)` is a `ℚ`-algebra whenever
`CFieldSpec.K α` is — one recursive instance for the whole tower. -/
noncomputable instance instAlgebraQKCFrac {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α]
    [Algebra ℚ (CFieldSpec.K α)] : Algebra ℚ (CFieldSpec.K (CFrac α)) :=
  inferInstanceAs (Algebra ℚ (RatFunc (CFieldSpec.K α)))

/-- **`CDiffFieldSpec` iterates up the tower.** The carrier's `cderiv` is `towerDerivCFrac [1]` (the new
monomial as an independent variable); its abstract realization on `RatFunc (CFieldSpec.K α)` is
`fractionFieldDifferential (implicitDeriv (toPoly [1]))` — the base derivation of `CDiffFieldSpec α` lifted to
the fraction field — and the intertwining `toK_cderiv` is the generic `toCFracG_towerDerivCFracG [1]`. One
recursive instance for the whole tower, generalizing the ℚ-specific base `instCDiffFieldSpecCFrac`. -/
noncomputable instance instCDiffFieldSpecCFracGRec {α : Type*} [CField α] [CFieldSpec α] [CDiffField α]
    [CDiffFieldSpec α] [CFieldDomain α] [Algebra ℚ (CFieldSpec.K α)] : CDiffFieldSpec (CFrac α) where
  diffK := fractionFieldDifferential
    (Differential.implicitDeriv (CPoly.toPoly ([CField.one] : CPoly α)))
  toK_cderiv a := by
    show CFrac.toCFrac (CFrac.towerDerivCFrac [CField.one] a)
      = @Differential.deriv _ _ (fractionFieldDifferential
          (Differential.implicitDeriv (CPoly.toPoly ([CField.one] : CPoly α)))) (CFrac.toCFrac a)
    rw [CFrac.toCFracG_towerDerivCFracG [CField.one] a]
    rfl

end DeepWiki.SymbolicIntegration
