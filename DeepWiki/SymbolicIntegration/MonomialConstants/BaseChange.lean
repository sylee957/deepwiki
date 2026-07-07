import DeepWiki.SymbolicIntegration.MonomialConstants.Basic

/-! # Monomial constant base change

Base-change preservation for normality of special-polynomial candidates. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {k : Type*} [Field k] [Differential k]

section AlgebraicExtension
variable {E : Type*} [Field E] [Differential E] [Algebra k E] [DifferentialAlgebra k E]

/-- Coprimality of `p` and `implicitDeriv v p` is preserved by differential base change. -/
theorem isCoprime_map_implicitDeriv_of_isCoprime {v p : k[X]}
    (hp : IsCoprime p (Differential.implicitDeriv v p)) :
    IsCoprime (p.map (algebraMap k E))
      (Differential.implicitDeriv (v.map (algebraMap k E)) (p.map (algebraMap k E))) := by
  rw [← implicitDeriv_map]
  have := hp.map (Polynomial.mapRingHom (algebraMap k E))
  simpa only [coe_mapRingHom] using this

end AlgebraicExtension

end DeepWiki.SymbolicIntegration
