import DeepWiki.SymbolicIntegration.ComputableField

/-! # The computable Risch-DE field oracle interface

This file contains only the base oracle class and the constant-field instance, separated from the
fueled tower implementation.
-/

namespace DeepWiki.SymbolicIntegration

/-! ### The `CRischField` class — the base Risch-DE solve over the field itself

`crischDESolve f g` solves `Dy + f·y = g` for `y ∈ α`, where `D` is `α`'s own derivation
(`CDiffField.cderiv`). This is the leading-coefficient recursion target of every §6.6 cancellation case
(eq. 6.23). The recursion is carried by the *instances*: `CRischField ℚ` is the constant base, and the
tower instance is supplied by `ComputableTowerRischDE`. -/

/-- **Base Risch-DE solver over the field `α`**: `crischDESolve f g = some y` with `y ∈ α` solving
`Dy + f·y = g` (`D = α`'s own derivation), or `none`. The leading-coefficient recursion target of the
§6.6 cancellation cases (Bronstein eq. 6.23). Carried as a typeclass so tower recursion can be structural:
the tower instance runs the §6 pipeline over `β[s]` and recurses to `CRischField β`, bottoming at
`CRischField ℚ`. -/
class CRischField (α : Type*) [CField α] where
  /-- Solve `Dy + f·y = g` over the field `α` (`D = α`'s own derivation); `none` if unsolvable. -/
  crischDESolve : α → α → Option α

/-- **`CRischField ℚ`** — the constant-field base (`D = 0`): `Dy + f·y = g` collapses to `f·y = g`
(`Dy = 0` for constant `y`), so `y = g/f` when `f ≠ 0`; `f = 0` needs `g = 0` (then `y = 0`). The
bottoming-out solve of the whole tower recursion. -/
instance instCRischFieldQ : CRischField ℚ where
  crischDESolve f g := if f = 0 then (if g = 0 then some 0 else none) else some (g / f)

end DeepWiki.SymbolicIntegration
