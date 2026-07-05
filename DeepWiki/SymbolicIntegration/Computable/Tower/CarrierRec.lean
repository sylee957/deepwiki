import DeepWiki.SymbolicIntegration.Computable.Tower.Field

/-! # Global-recursive tower-carrier instances

Since `CFieldSpec.K (QFunNZG α) = RatFunc (CFieldSpec.K α)` (Tower/Field), the base-field structure the Risch
tower needs on `CFieldSpec.K` — `CharZero`, `Algebra ℚ` — is **preserved by `RatFunc`**, so it iterates by one
global recursive instance each (base + step). This replaces the `noncomputable local instance … :=
inferInstanceAs (… (RatFunc ℚ))` copies that pinned the tower to the concrete `ℚ` base and blocked a single
recursive tower solver. With these, `CharZero (CFieldSpec.K (QFunNZGⁿ ℚ))` / `Algebra ℚ (…)` resolve at every
depth automatically. -/

namespace DeepWiki.SymbolicIntegration

open Compute

/-- **`CharZero` iterates up the tower.** `CFieldSpec.K (QFunNZG α) = RatFunc (CFieldSpec.K α)` is `CharZero`
whenever `CFieldSpec.K α` is — one recursive instance for the whole tower. -/
noncomputable instance instCharZeroKQFunNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α]
    [CharZero (CFieldSpec.K α)] : CharZero (CFieldSpec.K (QFunNZG α)) :=
  inferInstanceAs (CharZero (RatFunc (CFieldSpec.K α)))

/-- **`Algebra ℚ` iterates up the tower.** `RatFunc (CFieldSpec.K α)` is a `ℚ`-algebra whenever
`CFieldSpec.K α` is — one recursive instance for the whole tower. -/
noncomputable instance instAlgebraQKQFunNZG {α : Type*} [CField α] [CFieldSpec α] [CFieldDomain α]
    [Algebra ℚ (CFieldSpec.K α)] : Algebra ℚ (CFieldSpec.K (QFunNZG α)) :=
  inferInstanceAs (Algebra ℚ (RatFunc (CFieldSpec.K α)))

end DeepWiki.SymbolicIntegration
