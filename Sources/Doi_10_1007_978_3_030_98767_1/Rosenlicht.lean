import DeepWiki.SymbolicIntegration.AlgebraicCompleteness.LiouvilleFrontier
import DeepWiki.SymbolicIntegration.Computable.LiouvilleStructure
import Sources.Doi_10_1007_978_3_030_98767_1.Source

/-! # Rosenlicht, "Integration in Finite Terms" — catalog (chapter DOI `…_1`)
Maxwell Rosenlicht's reprint (Amer. Math. Monthly 79(9), 963–972, 1972; book pp.1–10, chapter DOI
`10.1007/978-3-030-98767-1_1`), the purely-algebraic proof of **Liouville's theorem**. The
`DeepWiki.SymbolicIntegration` library renders Rosenlicht's structure theorem (the *Weak Liouville
Theorem*) over Mathlib's differential-Liouville framework, in the shape that discharges the
algebraic-completeness frontier.

## NOT YET FORMALIZED (subtractive — delete each item once it is formalized)
The transcendental **exponential** layer of the tower induction (`θ = exp η`, Rosenlicht's Case 2.2)
[research]: the residual `ExponentialLayerResidual` — the one open per-layer Liouville instance; its local
degree engine (`coeff_natDegree_expMonomialDeriv`) is proved, but the layer-Liouville statement
`K(exp η)/K` is not (never met by the algebraic integrator, so the algebraic frontier closes without it).
-/

namespace DeepWiki.Ros

open DeepWiki.SymbolicIntegration.LiouvilleStructure

/-- **Liouville's theorem (Rosenlicht 1972), descent form** (§p.963, Thm): if `L/F` is an elementary
(Liouville) extension with no new constants and `g ∈ L` has `g′ ∈ F`, then `g′ = v₀′ + Σ cᵢ·vᵢ′/vᵢ`
with `vᵢ, v₀ ∈ F`, `cᵢ ∈ C_F` — an antiderivative is elementary over the base. The library's
`weakLiouville_of_isLiouville`. -/
abbrev liouville_theorem := @weakLiouville_of_isLiouville

/-- **Liouville's theorem, algebraic case** (§pp.966–969, Rosenlicht's averaging over conjugates): for a
finite-dimensional (algebraic) elementary extension `L/F` in char 0, `g ∈ L` with `g′ ∈ F` yields the
Liouville form over `F` — the trace/norm-averaging argument, via Mathlib's `isLiouville_of_finiteDimensional`.
The library's `weakLiouville_finiteDimensional`. -/
abbrev liouville_theorem_algebraic := @weakLiouville_finiteDimensional

/-- **Liouville's theorem as the algebraic-completeness frontier — a THEOREM** (§p.963, the structural
content): the `AlgebraicLiouvilleFrontier` (base non-elementarity propagates up a Liouville extension)
holds, proved by the Liouville-form descent. The library's `algebraicLiouvilleFrontier_proved`. -/
abbrev algebraicLiouvilleFrontier := @algebraicLiouvilleFrontier_proved

/-- **Liouville's theorem, unconditional finite-algebraic discharge** (§pp.966–969): with the
`[IsLiouville]` hypothesis dropped, base non-elementarity propagates up any finite-dimensional extension —
the operative Trager case (finite algebraic function field), via `isLiouville_of_finiteDimensional`. The
library's `isAlgebraicElementary_finiteDimensional_discharge`. -/
abbrev liouville_finiteDimensional_discharge :=
  @isAlgebraicElementary_finiteDimensional_discharge

end DeepWiki.Ros
