import DeepWiki.SymbolicIntegration.Computable.LrtSoundness
import DeepWiki.SymbolicIntegration.Computable.DifferentialAlgebraicClosure
import DeepWiki.SymbolicIntegration.Computable.FuelFreeDiophantine
import DeepWiki.SymbolicIntegration.Computable.RefinesPolyG

/-! # Genuine-monomial discharge for reduced LRT

Discharges the normality, coprimality, and Hermite-properness side conditions that follow from
genuine primitive monomial data for the reduced LRT integrator. -/

namespace DeepWiki.SymbolicIntegration

open Polynomial Compute CPolyG QFunNZG Classical
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]

omit [CFracGcdCoreWf α] in
open scoped Differential in
/-- **`η ∉ range(D_K)` from the genuine monomial property.** At `E = AlgebraicClosure K` the property gives
`η_K̄ ∉ range(D_K̄)`; it descends to `K` via `deriv_algebraMap` (the derivation intertwines base change): if
`γ′ = η` in `K` then `(φγ)′ = φη` in `K̄`, contradicting the property at `β = φγ`. -/
theorem eta_not_range_der [CharZero (CFieldSpec.K α)] (Dt : CPolyG α)
    (hgen : GenuinePrimitiveMonomialLrt Dt) (hDt0 : (toPolyG Dt).natDegree = 0) :
    ∀ (γ : CFieldSpec.K α), γ′ ≠ (toPolyG Dt).coeff 0 := by
  intro γ hγ
  refine hgen (AlgebraicClosure (CFieldSpec.K α))
    (algebraMap (CFieldSpec.K α) (AlgebraicClosure (CFieldSpec.K α)) γ) ?_
  rw [Polynomial.eq_C_of_natDegree_eq_zero hDt0, Polynomial.map_C, Polynomial.eval_C, ← hγ,
    deriv_algebraMap]

open scoped Differential in
/-- **`hm` from the genuine monomial property.** The monomial-derivative degree drop
`cdegG (cmonomialDeriv Dt Dstar) = cdegG Dstar − 1` is `natDegree_implicitDeriv_eq_of_monic_of_not_range`
(monic `Dstar` from Hermite; `η ∉ range D` from `eta_not_range_der`) through the `cdegG`/`cmonomialDeriv`
bridges. The degenerate `deg Dstar = 0` (`Dstar = 1`) case is handled separately (both sides `0`). -/
theorem hm_of_genuineMonomial [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (Dt a d : CPolyG α) (hd0 : toPolyG d ≠ 0) (hgen : GenuinePrimitiveMonomialLrt Dt)
    (hDt0 : (toPolyG Dt).natDegree = 0) :
    cdegG (cmonomialDeriv Dt (cHermiteReduceTowerGWf Dt a d).2.2)
      = cdegG (cHermiteReduceTowerGWf Dt a d).2.2 - 1 := by
  have hmonic : (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2).Monic :=
    toPolyG_cHermiteReduceTowerGWf_Dstar_monic hgcd Dt a d hd0
  rw [cdegG_eq_natDegree, cdegG_eq_natDegree]
  simp only [denote]
  by_cases hdeg : 1 ≤ (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2).natDegree
  · exact natDegree_implicitDeriv_eq_of_monic_of_not_range _ _ hmonic hDt0 hdeg
      (eta_not_range_der Dt hgen hDt0)
  · have h0 : (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2).natDegree = 0 := by omega
    have hC : toPolyG (cHermiteReduceTowerGWf Dt a d).2.2 = Polynomial.C 1 := by
      conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
      rw [show (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2).coeff 0 = 1 from by
        rw [← h0]; exact hmonic.coeff_natDegree]
    rw [h0, hC, Differential.implicitDeriv_C]
    simp

omit [CFracGcdCoreWf α] in
open scoped Differential in
/-- **Normality of a monic squarefree factor, from the genuine monomial property.** `IsCoprime v (D v)`
(`D = implicitDeriv Dt`) for monic squarefree `v` over `K`. The proof base-changes to `K̄`, splits `v`, and
reduces coprimality to rootwise genuine monomial normality. -/
theorem isCoprime_implicitDeriv_of_genuineMonomial [CharZero (CFieldSpec.K α)] (Dt v : CPolyG α)
    (hgen : GenuinePrimitiveMonomialLrt Dt) (hmonic : (toPolyG v).Monic)
    (hsf : Squarefree (toPolyG v)) :
    IsCoprime (toPolyG v) (Differential.implicitDeriv (toPolyG Dt) (toPolyG v)) := by
  rw [← Polynomial.isCoprime_map (algebraMap (CFieldSpec.K α) (AlgebraicClosure (CFieldSpec.K α))),
    implicitDeriv_map]
  have hmonicE := hmonic.map (algebraMap (CFieldSpec.K α) (AlgebraicClosure (CFieldSpec.K α)))
  have hsepE : ((toPolyG v).map
      (algebraMap (CFieldSpec.K α) (AlgebraicClosure (CFieldSpec.K α)))).Separable :=
    (Polynomial.separable_map _).mpr (PerfectField.separable_iff_squarefree.mpr hsf)
  rw [monic_separable_eq_nodal _ hmonicE hsepE, Lagrange.nodal]
  exact (isCoprime_prod_X_sub_C_implicitDeriv_iff _ _).mpr
    (fun β _ => hgen (AlgebraicClosure (CFieldSpec.K α)) β)

omit [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α] in
/-- **The `cgcdWf`-unit bridge.** `IsCoprime (toPolyG a) (toPolyG b)` makes the fraction-free gcd a unit
(`IsCoprime.isUnit_of_dvd'` with `toPolyG_cgcdWf_dvd`), hence degree `0` and nonzero — the computable
`hcopgcd`-shape conclusion from the abstract coprimality. -/
theorem natDegree_cgcdWf_eq_zero_of_isCoprime (a b : CPolyG α)
    (h : IsCoprime (toPolyG a) (toPolyG b)) :
    (toPolyG (cgcdWf a b).1).natDegree = 0 ∧ toPolyG (cgcdWf a b).1 ≠ 0 := by
  obtain ⟨hda, hdb⟩ := toPolyG_cgcdWf_dvd a b
  have hunit : IsUnit (toPolyG (cgcdWf a b).1) := h.isUnit_of_dvd' hda hdb
  exact ⟨Polynomial.natDegree_eq_zero_of_isUnit hunit, hunit.ne_zero⟩

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Cofactor coprimality from the Yun multiplicity structure.** For the `idx`-th Yun factor
`v = get idx` of `d` (multiplicity `idx+1`) and its cofactor `u = d / v^(idx+1)`, `IsCoprime u v` — the
cofactor half of `hcopgcd`. Base-change to `K̄`, where `v` splits (monic squarefree); at each root `β` of `v`,
`rootMult β d = idx+1` (`rootMult_R_map_eq_idx_succ`) equals `rootMult β (v^(idx+1))` (`β` a simple root),
forcing `rootMult β u = 0` — `β` is not a root of `u`. -/
theorem isCoprime_cofactor_yunFactor [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (d : CPolyG α) (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0)
    (idx : ℕ) (hidx : idx < (cSqfreeYunFFGWf d).length) :
    IsCoprime (toPolyG (cdivWf d (cpowG ((cSqfreeYunFFGWf d).get ⟨idx, hidx⟩) (idx + 1))))
      (toPolyG ((cSqfreeYunFFGWf d).get ⟨idx, hidx⟩)) := by
  classical
  set v := (cSqfreeYunFFGWf d).get ⟨idx, hidx⟩ with hvdef
  set u := cdivWf d (cpowG v (idx + 1)) with hudef
  have hφinj : Function.Injective (algebraMap (CFieldSpec.K α) (AlgebraicClosure (CFieldSpec.K α))) :=
    (algebraMap (CFieldSpec.K α) (AlgebraicClosure (CFieldSpec.K α))).injective
  have hv0 : toPolyG v ≠ 0 := cSqfreeYunFFGWf_get_ne_zero hgcd d hd0 hpp idx hidx
  have hpow : toPolyG v ^ (idx + 1) ∣ toPolyG d := by
    have h := cSqfreeYunFFGWf_pow_dvd hgcd d hd0 hpp idx hidx
    rwa [Nat.add_comm 1 idx] at h
  have hmul : toPolyG u * toPolyG v ^ (idx + 1) = toPolyG d :=
    toPolyG_cdivWf_pow_mul d v (idx + 1) hv0 hpow
  -- base-change the goal `IsCoprime u v` to `K̄`
  rw [← Polynomial.isCoprime_map (algebraMap (CFieldSpec.K α) (AlgebraicClosure (CFieldSpec.K α)))]
  refine IsCoprime.symm ?_
  -- `v` splits over `K̄` (monic squarefree ⟹ separable)
  have hvmonicE : ((toPolyG v).map (algebraMap (CFieldSpec.K α)
      (AlgebraicClosure (CFieldSpec.K α)))).Monic :=
    (cSqfreeYunFFGWf_monic hgcd d hd0 v (List.getElem_mem hidx)).map _
  have hvsfE : Squarefree ((toPolyG v).map (algebraMap (CFieldSpec.K α)
      (AlgebraicClosure (CFieldSpec.K α)))) := yun_factor_map_squarefree hgcd d ⟨hd0, hpp⟩ hidx
  have hvsepE : ((toPolyG v).map (algebraMap (CFieldSpec.K α)
      (AlgebraicClosure (CFieldSpec.K α)))).Separable :=
    PerfectField.separable_iff_squarefree.mpr hvsfE
  have hvmap0 : (toPolyG v).map (algebraMap (CFieldSpec.K α)
      (AlgebraicClosure (CFieldSpec.K α))) ≠ 0 := (Polynomial.map_ne_zero_iff hφinj).mpr hv0
  have hdmap0 : (toPolyG d).map (algebraMap (CFieldSpec.K α)
      (AlgebraicClosure (CFieldSpec.K α))) ≠ 0 := (Polynomial.map_ne_zero_iff hφinj).mpr hd0
  have humap0 : (toPolyG u).map (algebraMap (CFieldSpec.K α)
      (AlgebraicClosure (CFieldSpec.K α))) ≠ 0 := (Polynomial.map_ne_zero_iff hφinj).mpr (by
    intro h0; rw [h0, zero_mul] at hmul; exact hd0 hmul.symm)
  rw [monic_separable_eq_nodal _ hvmonicE hvsepE, Lagrange.nodal]
  refine IsCoprime.prod_left ?_
  intro β hβ
  simp only [id_eq]
  have hβroot : β ∈ ((toPolyG v).map (algebraMap (CFieldSpec.K α)
      (AlgebraicClosure (CFieldSpec.K α)))).roots := Multiset.mem_toFinset.mp hβ
  -- `IsCoprime (X - C β) u ⟺ β` is not a root of `u`
  rw [(Polynomial.irreducible_X_sub_C β).coprime_iff_not_dvd, Polynomial.dvd_iff_isRoot]
  intro hroot
  have hmd : rootMultiplicity β ((toPolyG d).map (algebraMap (CFieldSpec.K α)
      (AlgebraicClosure (CFieldSpec.K α)))) = idx + 1 :=
    rootMult_R_map_eq_idx_succ hgcd d ⟨hd0, hpp⟩ idx hidx β hβroot
  have hmapmul : (toPolyG d).map (algebraMap (CFieldSpec.K α)
        (AlgebraicClosure (CFieldSpec.K α)))
      = ((toPolyG u).map (algebraMap (CFieldSpec.K α) (AlgebraicClosure (CFieldSpec.K α))))
        * ((toPolyG v).map (algebraMap (CFieldSpec.K α)
            (AlgebraicClosure (CFieldSpec.K α)))) ^ (idx + 1) := by
    rw [← Polynomial.map_pow, ← Polynomial.map_mul, hmul]
  have hmv : rootMultiplicity β ((toPolyG v).map (algebraMap (CFieldSpec.K α)
      (AlgebraicClosure (CFieldSpec.K α)))) = 1 :=
    squarefree_rootMultiplicity_eq_one hvsfE β (Polynomial.isRoot_of_mem_roots hβroot)
  rw [hmapmul, Polynomial.rootMultiplicity_mul (mul_ne_zero humap0 (pow_ne_zero _ hvmap0)),
    rootMultiplicity_pow_eq _ _ _ hvmap0, hmv, mul_one] at hmd
  have hpos : 0 < rootMultiplicity β ((toPolyG u).map (algebraMap (CFieldSpec.K α)
      (AlgebraicClosure (CFieldSpec.K α)))) :=
    (Polynomial.rootMultiplicity_pos humap0).mpr hroot
  omega

open scoped Differential in
/-- **`hcopgcd` from the genuine monomial property** — the full subsumption of the third normality condition.
For each repeated Yun factor `v = x.1` (multiplicity `x.2 + 1 ≥ 2`) of `d`, the differential-normality guard
`gcd(u·D(v), v)` (`u = d/v^(x.2+1)`, `D = implicitDeriv Dt`) is a unit: `u·D(v)` is coprime to `v` by
`IsCoprime.mul_left` of the cofactor coprimality (`isCoprime_cofactor_yunFactor`) and the tower-derivative
normality (`isCoprime_implicitDeriv_of_genuineMonomial`, from `hgen`), and `natDegree_cgcdWf_eq_zero_of_isCoprime`
reads off the `hcopgcd` shape. -/
theorem hcopgcd_of_genuineMonomial [CharZero (CFieldSpec.K α)] (hgcd : GcdFFCorrect (α := α))
    (Dt d : CPolyG α) (hd0 : toPolyG d ≠ 0) (hpp : (toPolyG d).primPart ≠ 0)
    (hgen : GenuinePrimitiveMonomialLrt Dt) :
    ∀ x ∈ (cSqfreeYunFFGWf d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPolyG (cgcdWf (cmulG (cdivWf d (cpowG x.1 (x.2 + 1)))
          (cmonomialDeriv Dt x.1)) x.1).1 ≠ 0 := by
  intro x hx
  have hxzip : x ∈ (cSqfreeYunFFGWf d).zipIdx := List.mem_of_mem_filter hx
  obtain ⟨hidx, hget⟩ := List.getElem?_eq_some_iff.mp
    (List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hxzip))
  have hxmem : x.1 ∈ cSqfreeYunFFGWf d := by rw [← hget]; exact List.getElem_mem hidx
  apply natDegree_cgcdWf_eq_zero_of_isCoprime
  simp only [denote]
  refine IsCoprime.mul_left ?_ ?_
  · -- cofactor coprimality `IsCoprime (d/v^(x.2+1)) v`
    rw [← hget]
    exact isCoprime_cofactor_yunFactor hgcd d hd0 hpp x.2 hidx
  · -- tower-derivative normality `IsCoprime (D v) v`
    refine (isCoprime_implicitDeriv_of_genuineMonomial Dt x.1 hgen
      (cSqfreeYunFFGWf_monic hgcd d hd0 x.1 hxmem) ?_).symm
    rw [← hget]; exact cSqfreeYunFFGWf_squarefree hgcd d hd0 hpp x.2 hidx

set_option maxHeartbeats 1600000 in
open scoped Differential in
/-- **The Hermite properness `hAD` (`degree` form) discharged from the genuine monomial property.** For
`deg Dt ≤ 1` and a proper input `deg a < deg d`, `deg (…).2.1 < deg (…).2.2`, resting only on
`(hgcd, hd0, hpp, hgen)`. Discharges every hypothesis of `cHermiteReduceTowerGWf_leftover_proper_of_degree_le_one`:
`hv`/`hb` from Yun `get_ne_zero` + `cdiophantineGWf_fst_degree_lt`; `hDstar`/`hresDen` from the radical/denominator
nonvanishing; and the residual divisibility `hdvd` from `hWgd_of_multiplicity` (the Yun coprimality `hcopgcd`
*derived* from `hgen` via `hcopgcd_of_genuineMonomial`) via the `d = W·Dstar` cancellation, bridging the raw
fold `g` to the `cnormG`-projections through `toPolyG`. -/
theorem hAD_degree_of_genuineMonomial [CharZero (CFieldSpec.K α)]
    (hgcd : GcdFFCorrect (α := α)) (Dt a d : CPolyG α) (hd0 : toPolyG d ≠ 0)
    (hpp : (toPolyG d).primPart ≠ 0) (hDtdeg : (toPolyG Dt).natDegree ≤ 1)
    (haProper : (toPolyG a).degree < (toPolyG d).degree) (hgen : GenuinePrimitiveMonomialLrt Dt) :
    (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1).degree
      < (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2).degree := by
  have hcopgcd := hcopgcd_of_genuineMonomial hgcd Dt d hd0 hpp hgen
  have hgd0 : toPolyG (cHermiteReduceTowerGWf Dt a d).1.2 ≠ 0 :=
    toPolyG_cHermiteReduceTowerGWf_den_ne_zero hgcd Dt a d hd0 hpp
  set g := (cSqfreeYunFFGWf d).zipIdx.foldl
      (fun (gAcc : CPolyG α × CPolyG α) (vi, idx) =>
          let i := idx + 1
          if i ≤ 1 then gAcc
          else
            let Vi_pow := cpowG vi i
            let u := cdivWf d Vi_pow
            let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a ([CField.zero], [CField.one])).1
            (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
      ([CField.zero], [CField.one]) with hg_def
  -- raw-fold `g` ↔ `cnormG`-projection bridges (equal through `toPolyG`)
  have hg1 : toPolyG (cHermiteReduceTowerGWf Dt a d).1.1 = toPolyG g.1 := by
    rw [hg_def]; simp only [cHermiteReduceTowerGWf, denote]
  have hg2 : toPolyG (cHermiteReduceTowerGWf Dt a d).1.2 = toPolyG g.2 := by
    rw [hg_def]; simp only [cHermiteReduceTowerGWf, denote]
  have hDsF : toPolyG (cHermiteReduceTowerGWf Dt a d).2.2
      = toPolyG ((cSqfreeYunFFGWf d).foldl (fun acc vi => cmulG acc vi) [CField.one]) := by
    simp only [cHermiteReduceTowerGWf, denote]
  have hDstar0 : toPolyG ((cSqfreeYunFFGWf d).foldl (fun acc vi => cmulG acc vi) [CField.one]) ≠ 0 := by
    rw [← hDsF]; exact (toPolyG_cHermiteReduceTowerGWf_Dstar_monic hgcd Dt a d hd0).ne_zero
  have hg2ne : toPolyG g.2 ≠ 0 := by rw [← hg2]; exact hgd0
  refine cHermiteReduceTowerGWf_leftover_proper_of_degree_le_one Dt a d hDtdeg haProper
    ?_ g hg_def ?_ ?_ hDstar0
  · -- hfac : each repeated Yun factor is nonzero and has proper Diophantine cofactors
    intro p hp _
    refine ⟨?_, ?_⟩
    · obtain ⟨hidx, hget⟩ := List.getElem?_eq_some_iff.mp
        (List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hp))
      rw [← hget]; exact cSqfreeYunFFGWf_get_ne_zero hgcd d hd0 hpp p.2 hidx
    · intro rhs
      refine cdiophantineGWf_fst_degree_lt _ p.1 rhs ?_
      intro h
      obtain ⟨hidx, hget⟩ := List.getElem?_eq_some_iff.mp
        (List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hp))
      rw [← hget] at h
      exact cSqfreeYunFFGWf_get_ne_zero hgcd d hd0 hpp p.2 hidx ((cnormG_eq_nil_iff _).mp h)
  · -- hdvd : `d·g.2² ∣ resNum·Dstar`, from `hWgd` (`W·g.2² ∣ resNum`) and `d = W·Dstar`
    have hWgd := hWgd_of_multiplicity hgcd Dt a d hd0 hpp hgd0 hcopgcd
    have hHermDsNe : toPolyG (cHermiteReduceTowerGWf Dt a d).2.2 ≠ 0 :=
      (toPolyG_cHermiteReduceTowerGWf_Dstar_monic hgcd Dt a d hd0).ne_zero
    have hWD : toPolyG (cdivWf d (cHermiteReduceTowerGWf Dt a d).2.2)
        * toPolyG ((cSqfreeYunFFGWf d).foldl (fun acc vi => cmulG acc vi) [CField.one]) = toPolyG d := by
      rw [← hDsF]
      exact toPolyG_cdivWf_exact d (cHermiteReduceTowerGWf Dt a d).2.2
        (fun h => hHermDsNe ((cnormG_eq_nil_iff _).mp h))
        (toPolyG_cHermiteReduceTowerGWf_Dstar_dvd hgcd Dt a d hd0)
    -- push `hWgd` from the `cnormG`-projections to `g` (through `toPolyG`)
    rw [hg2] at hWgd
    have htransport :
        toPolyG (csubG (cmulG a (cmulG (cHermiteReduceTowerGWf Dt a d).1.2
              (cHermiteReduceTowerGWf Dt a d).1.2))
            (cmulG d (csubG (cmulG (cmonomialDeriv Dt (cHermiteReduceTowerGWf Dt a d).1.1)
                (cHermiteReduceTowerGWf Dt a d).1.2)
              (cmulG (cHermiteReduceTowerGWf Dt a d).1.1
                (cmonomialDeriv Dt (cHermiteReduceTowerGWf Dt a d).1.2)))))
          = toPolyG (csubG (cmulG a (cmulG g.2 g.2))
            (cmulG d (csubG (cmulG (cmonomialDeriv Dt g.1) g.2)
              (cmulG g.1 (cmonomialDeriv Dt g.2))))) := by
      simp only [denote, hg1, hg2]
    rw [htransport] at hWgd
    -- assemble `d·g.2² ∣ resNum·Dstar` from `W·g.2² ∣ resNum` and `d = W·Dstar`
    rw [toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG]
    rw [show toPolyG d * (toPolyG g.2 * toPolyG g.2)
          = toPolyG ((cSqfreeYunFFGWf d).foldl (fun acc vi => cmulG acc vi) [CField.one])
            * (toPolyG (cdivWf d (cHermiteReduceTowerGWf Dt a d).2.2) * (toPolyG g.2 * toPolyG g.2))
        from by rw [← hWD]; ring,
      mul_comm (toPolyG (csubG (cmulG a (cmulG g.2 g.2))
        (cmulG d (csubG (cmulG (cmonomialDeriv Dt g.1) g.2) (cmulG g.1 (cmonomialDeriv Dt g.2))))))]
    exact mul_dvd_mul_left _ hWgd
  · -- hresDen : `d·g.2² ≠ 0`
    intro h
    have h0 := (cnormG_eq_nil_iff _).mp h
    simp only [denote] at h0
    exact mul_ne_zero hd0 (mul_ne_zero hg2ne hg2ne) h0

end DeepWiki.SymbolicIntegration
