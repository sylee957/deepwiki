import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalGenericExamples.Helpers
import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalGenericExamples.X3Minus2
import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalGenericExamples.X3PlusX
import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalGenericExamples.X5MinusXMinus1

/-! # The radical/mixed-tower engine over a family of radicands

Aggregator for generic odd-degree radicand helpers and concrete mixed-tower
derivation examples over three square-root radical extensions.
-/

namespace DeepWiki.SymbolicIntegration

/-! ### Scope note

Prime-`n` irreducibility (hence the genuine field `AdjoinRoot (Xⁿ − C(toK f))` and abstract
`CFieldDomain`) is reachable from `X_pow_sub_C_irreducible_iff_of_prime` and a not-a-perfect-`p`-th-power
argument. The computable `CField (RadExt α n f)` carrier is `n = 2` only until the general-`n` inverse
(extended Euclid) lands; the four radicands here are members of that `n = 2` slice. -/

/-! ### `#print axioms` -/

#print axioms not_isSquare_algebraMap_of_odd_natDegree
#print axioms irreducible_radDeg2_of_not_isSquare
#print axioms irreducible_radX3m2
#print axioms irreducible_radX5mXm1
#print axioms irreducible_radX3pX

#print axioms radX3m2_monomialDeriv_t2sq
#print axioms radX3m2_monomialDeriv_genT
#print axioms radX5_monomialDeriv_t2sq
#print axioms radX5_monomialDeriv_genT
#print axioms radX3pX_monomialDeriv_t2sq
#print axioms radX3pX_monomialDeriv_genT

end DeepWiki.SymbolicIntegration
