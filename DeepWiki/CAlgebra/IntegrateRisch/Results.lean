import DeepWiki.CAlgebra.IntegrateRisch.DerivationExtend
import DeepWiki.CAlgebra.Integrate.DerivData

/-! # Transcendental integration results

`ResultRisch` — the bundled antiderivative record of a transcendental level `(K, d, t)`:
an in-field principal part plus `RootSum` log data whose residues are constants (the
constancy carried as an invariant field), with the computable derivative
`ResultRisch.deriv` via the derivation-parametric root-sum deformation
`rootSumDerivD`. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {K : Type u} [Field K] [DecidableEq K] [DensePolyGcd K]

open scoped Differential FormalDiff

/-- The bivariate reading of the level derivation on a produced pair's log argument:
`z`-coefficients (residue placeholders) are constants, `t`-coefficients differentiate
by `d`, and the outer variable contributes `Dt ·` the formal derivative. -/
def bivDeriv (d : K → K) (Dt : DensePoly K) (S : DensePoly (DensePoly K)) :
    DensePoly (DensePoly K) :=
  DensePoly.extendDeriv (mapCoeffs d) (ofList (Dt.coeffs.map C)) S

/-- **Root-sum derivative of a produced pair at level data `(d, Dt)`**, by resultant
deformation: `F(τ) = Res_z(Q, S + τ·z·DS)` with `DS` the level derivative of the log
argument; the sum `∑_{Q(α)=0} α·DS(α,t)/S(α,t)` is `F.coeff 1 / F.coeff 0`. -/
def rootSumDerivD (d : K → K) (Dt : DensePoly K) (Q : DensePoly K)
    (S : DensePoly (DensePoly K)) : DenseFrac K :=
  let Sz := zSwap S
  let Sxz := zSwap (bivDeriv d Dt S)
  let QC : DensePoly (DensePoly (DensePoly K)) :=
    DensePoly.ofList (Q.coeffs.map fun r => DensePoly.C (DensePoly.C r))
  let SzC : DensePoly (DensePoly (DensePoly K)) :=
    DensePoly.ofList (Sz.coeffs.map fun c => DensePoly.C c)
  let SxzT : DensePoly (DensePoly (DensePoly K)) :=
    DensePoly.ofList (Sxz.coeffs.map fun c => DensePoly.ofList [0, c])
  let A := SzC + DensePoly.ofList [0, 1] * SxzT
  let F := DensePolyResultant.resultant QC A
  DenseFrac.normalize (F.coeff 1) (F.coeff 0)

omit [DensePolyGcd K] in
/-- The constant-in-`z` lift of the base one is one. -/
private theorem ofList_one_map_C :
    (ofList ((1 : DensePoly K).coeffs.map C) : DensePoly (DensePoly K)) = 1 := by
  have hC1 : (C (1 : K) : DensePoly K) = 1 := by
    ext m
    rw [coeff_C, coeff_one]
  ext n
  rw [coeff_ofList_map C C_zero, coeff_one, coeff_one, apply_ite C, hC1, C_zero]

omit [DensePolyGcd K] in
/-- At the base data (`d = 0`, `Dt = 1`) the bivariate level derivative is the formal
derivative. -/
theorem bivDeriv_zero_one (S : DensePoly (DensePoly K)) :
    bivDeriv (fun _ => (0 : K)) 1 S = S′ := by
  rw [bivDeriv, DensePoly.extendDeriv, ofList_one_map_C,
    mapCoeffs_eq_zero (fun c => mapCoeffs_eq_zero (fun _ => rfl) c), one_mul, zero_add]

/-- At the base data the root-sum derivative is the rational one. -/
theorem rootSumDerivD_zero_one (Q : DensePoly K) (S : DensePoly (DensePoly K)) :
    rootSumDerivD (fun _ => (0 : K)) 1 Q S = rootSumDeriv Q S := by
  simp only [rootSumDerivD, rootSumDeriv, bivDeriv_zero_one]

/-- **Bundled transcendental integration result** over a level with coefficient
derivation `d`: an in-field principal part and `RootSum` log data `(Qᵢ, Sᵢ)` meaning
`∑ᵢ ∑_{Qᵢ(α)=0} α · log Sᵢ(α, t)`, with the produced-pair contracts — squarefreeness
and residue constancy — carried as invariants. -/
structure ResultRisch (K : Type u) [Field K] [DecidableEq K] [DensePolyGcd K]
    (d : K → K) where
  /-- The in-field part of the antiderivative. -/
  principal : DenseFrac K
  /-- The log-term pairs `(Qᵢ, Sᵢ)`. -/
  terms : List (DensePoly K × DensePoly (DensePoly K))
  /-- Every `Qᵢ` is squarefree and nonconstant. -/
  fst_squarefree : ∀ t ∈ terms, Squarefree t.1 ∧ 1 < t.1.size
  /-- Residue constancy: every `Qᵢ` has constant coefficients. -/
  fst_constant : ∀ t ∈ terms, mapCoeffs d t.1 = 0

/-- **The computable derivative of a transcendental result** at level data `(d, Dt)`:
the level derivative of the principal part plus the root-sum derivatives of the log
data. -/
def ResultRisch.deriv {d : K → K} (Dt : DensePoly K) (res : ResultRisch K d) :
    DenseFrac K :=
  DenseFrac.extendDeriv d Dt res.principal
    + (res.terms.map (fun QS => rootSumDerivD d Dt QS.1 QS.2)).sum

/-- Read a rational-integration record as a base-level record (zero coefficient
derivation): the principal part collects the rational and polynomial parts, the log
data carries over, and residue constancy is trivial. -/
def ResultRisch.ofRatIntegral (res : ResultRatIntegral K) :
    ResultRisch K (fun _ => 0) where
  principal := res.rational + DenseFrac.ofPoly res.poly
  terms := res.logs.terms
  fst_squarefree := res.logs.fst_squarefree
  fst_constant := fun t _ => mapCoeffs_eq_zero (fun _ => rfl) t.1

/-- The base-level reading differentiates as the rational record. -/
theorem ResultRisch.ofRatIntegral_deriv (res : ResultRatIntegral K) :
    (ResultRisch.ofRatIntegral res).deriv 1 = res.deriv := by
  show DenseFrac.extendDeriv (fun _ => 0) 1 (res.rational + DenseFrac.ofPoly res.poly)
      + ((res.logs.terms.map fun QS => rootSumDerivD (fun _ => 0) 1 QS.1 QS.2)).sum
      = res.deriv
  rw [DenseFrac.extendDeriv_zero_one, DenseFrac.fracDeriv_add, DenseFrac.fracDeriv_ofPoly,
    show (res.logs.terms.map fun QS => rootSumDerivD (fun _ => 0) 1 QS.1 QS.2)
        = res.logs.terms.map fun QS => rootSumDeriv QS.1 QS.2 from
      List.map_congr_left fun QS _ => rootSumDerivD_zero_one QS.1 QS.2]
  rfl

end DensePoly

end DeepWiki.CAlgebra
