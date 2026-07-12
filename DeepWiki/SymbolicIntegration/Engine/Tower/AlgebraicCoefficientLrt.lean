import DeepWiki.SymbolicIntegration.Engine.Tower.AlgebraicCoefficient
import DeepWiki.SymbolicIntegration.Engine.Tower.LrtDepth

/-! # Primitive LRT coefficient-stage adapter

Turns a certified primitive root-free LRT stage into a heterogeneous coefficient stage. The adapter retains
the residue-log families and their root-free constant-residue certificates. -/

namespace DeepWiki.SymbolicIntegration

open CFrac

/-- View a represented lower fraction as the primitive LRT input with monomial derivative `D(t) = 1`. -/
noncomputable def lrtCoefficientInput (c : DenseFrac (DenseFracTower n)) :
    RischStageInput DensePoly (DenseFracTower n) where
  Dt := [CCommRing.one]
  num := CFrac.num c
  den := CFrac.den c
  den_nonzero := CFrac.toPoly_den_ne_zero_generic c

/-- A genuine primitive LRT stage is a heterogeneous coefficient stage. -/
noncomputable def DenseLrtStage.asAlgebraicCoefficientStage (S : DenseLrtStage n) :
    IntegrationStage (DenseFrac (DenseFracTower n))
      (AlgebraicCoefficientIntegralResult (DenseFracTower n))
      (fun c => IsElementaryIntegrableGenuineLrt ([CCommRing.one] : DensePoly (DenseFracTower n))
        (CFrac.num c) (CFrac.den c))
      IsGenuineAlgebraicCoefficientIntegralResult where
  run _fuel c := (S.integrateGenuine ([CCommRing.one] : DensePoly (DenseFracTower n))
    (CFrac.num c) (CFrac.den c)).map AlgebraicCoefficientIntegralResult.ofLrt
  domain c := S.genuineFullDomain ([CCommRing.one] : DensePoly (DenseFracTower n))
    (CFrac.num c) (CFrac.den c)
  sound _fuel c output _hdomain hrun := by
    obtain ⟨lrt, hlrt, rfl⟩ := Option.map_eq_some_iff.mp hrun
    have hgenuine := S.genuine_sound ([CCommRing.one] : DensePoly (DenseFracTower n))
      (CFrac.num c) (CFrac.den c) lrt hlrt
    exact ⟨isAlgebraicCoefficientIntegralResult_ofLrt c lrt hgenuine.1,
      AlgebraicCoefficientIntegralResult.logsGenuine_ofLrt lrt hgenuine.2⟩
  complete c hdomain hintegrable := by
    obtain ⟨lrt, hlrt⟩ := S.genuine_complete_of_fullDomain
      ([CCommRing.one] : DensePoly (DenseFracTower n)) (CFrac.num c) (CFrac.den c) hdomain
      (CFrac.toPoly_den_ne_zero_generic c) hintegrable
    exact ⟨0, AlgebraicCoefficientIntegralResult.ofLrt lrt, by simp [hlrt]⟩

end DeepWiki.SymbolicIntegration
