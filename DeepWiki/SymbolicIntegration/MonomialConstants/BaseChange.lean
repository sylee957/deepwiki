import DeepWiki.SymbolicIntegration.MonomialConstants.Basic

/-! # Monomial constant base change

Base-change preservation for normality of special-polynomial candidates. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {k : Type*} [Field k] [Differential k]

section AlgebraicExtension
variable {E : Type*} [Field E] [Differential E] [Algebra k E] [DifferentialAlgebra k E]

/-- `mapCoeffs` commutes with base change along a differential-algebra hom. -/
theorem mapCoeffs_map (p : k[X]) :
    (Differential.mapCoeffs p).map (algebraMap k E)
      = Differential.mapCoeffs (p.map (algebraMap k E)) := by
  ext i
  rw [coeff_map, Differential.coeff_mapCoeffs, Differential.coeff_mapCoeffs, coeff_map,
    deriv_algebraMap]

/-- The monomial derivation commutes with base change: `(D[v] p).map = D[v.map] (p.map)`
(`mapCoeffs` commutes, and `v*p'` maps to `(v.map)*(p.map)'`). -/
theorem implicitDeriv_map (v p : k[X]) :
    (Differential.implicitDeriv v p).map (algebraMap k E)
      = Differential.implicitDeriv (v.map (algebraMap k E)) (p.map (algebraMap k E)) := by
  have h1 : Differential.implicitDeriv v p = Differential.mapCoeffs p + v * derivative p := by
    simp [Differential.implicitDeriv, derivative']
  have h2 : Differential.implicitDeriv (v.map (algebraMap k E)) (p.map (algebraMap k E))
      = Differential.mapCoeffs (p.map (algebraMap k E))
        + (v.map (algebraMap k E)) * derivative (p.map (algebraMap k E)) := by
    simp [Differential.implicitDeriv, derivative']
  rw [h1, h2, Polynomial.map_add, Polynomial.map_mul, mapCoeffs_map, derivative_map]

/-- A special polynomial stays special after a base change: `p ∣ Dp` gives `p.map ∣ D(p.map)`. -/
theorem isSpecial_map_of_isSpecial {v p : k[X]} (hp : p ∣ Differential.implicitDeriv v p) :
    (p.map (algebraMap k E)) ∣
      Differential.implicitDeriv (v.map (algebraMap k E)) (p.map (algebraMap k E)) := by
  rw [← implicitDeriv_map]; exact Polynomial.map_dvd _ hp

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
