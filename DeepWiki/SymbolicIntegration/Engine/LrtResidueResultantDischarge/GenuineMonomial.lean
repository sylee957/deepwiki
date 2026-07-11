import DeepWiki.SymbolicIntegration.Engine.LrtSoundness
import DeepWiki.SymbolicIntegration.Engine.DifferentialAlgebraicClosure
import DeepWiki.SymbolicIntegration.Engine.FuelFreeDiophantine
import DeepWiki.SymbolicIntegration.Engine.RefinesPoly

/-! # Genuine-monomial discharge for reduced LRT

Discharges the normality, coprimality, and Hermite-properness side conditions that follow from
genuine primitive monomial data for the reduced LRT integrator. -/

namespace DeepWiki.SymbolicIntegration

open Polynomial DensePoly CFrac Classical
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]

omit [CFracGcdCoreWf α] in
open scoped Differential in
/-- **`η ∉ range(D_K)` from the genuine monomial property.** At `E = AlgebraicClosure K` the property gives
`η_K̄ ∉ range(D_K̄)`; it descends to `K` via `deriv_algebraMap` (the derivation intertwines base change): if
`γ′ = η` in `K` then `(φγ)′ = φη` in `K̄`, contradicting the property at `β = φγ`. -/
theorem eta_not_range_der [CharZero (CFieldSpec.K α)] (Dt : DensePoly α)
    (hgen : GenuinePrimitiveMonomialLrt Dt) (hDt0 : (toPoly Dt).natDegree = 0) :
    ∀ (γ : CFieldSpec.K α), γ′ ≠ (toPoly Dt).coeff 0 := by
  intro γ hγ
  refine hgen (AlgebraicClosure (CFieldSpec.K α))
    (algebraMap (CFieldSpec.K α) (AlgebraicClosure (CFieldSpec.K α)) γ) ?_
  rw [Polynomial.eq_C_of_natDegree_eq_zero hDt0, Polynomial.map_C, Polynomial.eval_C, ← hγ,
    deriv_algebraMap]

open scoped Differential in
/-- **`hm` from the genuine monomial property.** The monomial-derivative degree drop
`cdeg (CPolyEngine.monomialDeriv Dt Dstar) = cdeg Dstar − 1` is `natDegree_implicitDeriv_eq_of_monic_of_not_range`
(monic `Dstar` from Hermite; `η ∉ range D` from `eta_not_range_der`) through the `cdeg`/`CPolyEngine.monomialDeriv`
bridges. The degenerate `deg Dstar = 0` (`Dstar = 1`) case is handled separately (both sides `0`). -/
theorem hm_of_genuineMonomial [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0) (hgen : GenuinePrimitiveMonomialLrt Dt)
    (hDt0 : (toPoly Dt).natDegree = 0) :
    cdeg (CPolyEngine.monomialDeriv Dt (cHermiteReduceTower Dt a d).2.2)
      = cdeg (cHermiteReduceTower Dt a d).2.2 - 1 := by
  have hmonic : (toPoly (cHermiteReduceTower Dt a d).2.2).Monic :=
    toPolyG_cHermiteReduceTowerG_Dstar_monic hgcd Dt a d hd0
  rw [cdegG_eq_natDegree, cdegG_eq_natDegree]
  simp only [denote]
  by_cases hdeg : 1 ≤ (toPoly (cHermiteReduceTower Dt a d).2.2).natDegree
  · exact natDegree_implicitDeriv_eq_of_monic_of_not_range _ _ hmonic hDt0 hdeg
      (eta_not_range_der Dt hgen hDt0)
  · have h0 : (toPoly (cHermiteReduceTower Dt a d).2.2).natDegree = 0 := by omega
    have hC : toPoly (cHermiteReduceTower Dt a d).2.2 = Polynomial.C 1 := by
      conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
      rw [show (toPoly (cHermiteReduceTower Dt a d).2.2).coeff 0 = 1 from by
        rw [← h0]; exact hmonic.coeff_natDegree]
    rw [h0, hC, Differential.implicitDeriv_C]
    simp

omit [CFracGcdCoreWf α] in
open scoped Differential in
/-- **Normality of a monic squarefree factor, from the genuine monomial property.** `IsCoprime v (D v)`
(`D = implicitDeriv Dt`) for monic squarefree `v` over `K`. The proof base-changes to `K̄`, splits `v`, and
reduces coprimality to rootwise genuine monomial normality. -/
theorem isCoprime_implicitDeriv_of_genuineMonomial [CharZero (CFieldSpec.K α)] (Dt v : DensePoly α)
    (hgen : GenuinePrimitiveMonomialLrt Dt) (hmonic : (toPoly v).Monic)
    (hsf : Squarefree (toPoly v)) :
    IsCoprime (toPoly v) (Differential.implicitDeriv (toPoly Dt) (toPoly v)) := by
  rw [← Polynomial.isCoprime_map (algebraMap (CFieldSpec.K α) (AlgebraicClosure (CFieldSpec.K α))),
    implicitDeriv_map]
  have hmonicE := hmonic.map (algebraMap (CFieldSpec.K α) (AlgebraicClosure (CFieldSpec.K α)))
  have hsepE : ((toPoly v).map
      (algebraMap (CFieldSpec.K α) (AlgebraicClosure (CFieldSpec.K α)))).Separable :=
    (Polynomial.separable_map _).mpr (PerfectField.separable_iff_squarefree.mpr hsf)
  rw [monic_separable_eq_nodal _ hmonicE hsepE, Lagrange.nodal]
  exact (isCoprime_prod_X_sub_C_implicitDeriv_iff _ _).mpr
    (fun β _ => hgen (AlgebraicClosure (CFieldSpec.K α)) β)

omit [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α] in
/-- **The `CPolyEuclidean.gcdExt`-unit bridge.** `IsCoprime (toPoly a) (toPoly b)` makes the fraction-free gcd a unit
(`IsCoprime.isUnit_of_dvd'` with `toPolyG_cgcdWf_dvd`), hence degree `0` and nonzero — the computable
`hcopgcd`-shape conclusion from the abstract coprimality. -/
theorem natDegree_cgcdWf_eq_zero_of_isCoprime (a b : DensePoly α)
    (h : IsCoprime (toPoly a) (toPoly b)) :
    (toPoly (CPolyEuclidean.gcdExt a b).1).natDegree = 0 ∧ toPoly (CPolyEuclidean.gcdExt a b).1 ≠ 0 := by
  obtain ⟨hda, hdb⟩ := toPolyG_cgcdWf_dvd a b
  have hunit : IsUnit (toPoly (CPolyEuclidean.gcdExt a b).1) := h.isUnit_of_dvd' hda hdb
  exact ⟨Polynomial.natDegree_eq_zero_of_isUnit hunit, hunit.ne_zero⟩

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Cofactor coprimality from the Yun multiplicity structure.** For the `idx`-th Yun factor
`v = get idx` of `d` (multiplicity `idx+1`) and its cofactor `u = d / v^(idx+1)`, `IsCoprime u v` — the
cofactor half of `hcopgcd`. Base-change to `K̄`, where `v` splits (monic squarefree); at each root `β` of `v`,
`rootMult β d = idx+1` (`rootMult_R_map_eq_idx_succ`) equals `rootMult β (v^(idx+1))` (`β` a simple root),
forcing `rootMult β u = 0` — `β` is not a root of `u`. -/
theorem isCoprime_cofactor_yunFactor [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (d : DensePoly α) (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0)
    (idx : ℕ) (hidx : idx < (cSqfreeYunFF d).length) :
    IsCoprime (toPoly (CPolyEuclidean.div d (cpow ((cSqfreeYunFF d).get ⟨idx, hidx⟩) (idx + 1))))
      (toPoly ((cSqfreeYunFF d).get ⟨idx, hidx⟩)) := by
  classical
  set v := (cSqfreeYunFF d).get ⟨idx, hidx⟩ with hvdef
  set u := CPolyEuclidean.div d (cpow v (idx + 1)) with hudef
  have hφinj : Function.Injective (algebraMap (CFieldSpec.K α) (AlgebraicClosure (CFieldSpec.K α))) :=
    (algebraMap (CFieldSpec.K α) (AlgebraicClosure (CFieldSpec.K α))).injective
  have hv0 : toPoly v ≠ 0 := cSqfreeYunFFG_get_ne_zero hgcd d hd0 hpp idx hidx
  have hpow : toPoly v ^ (idx + 1) ∣ toPoly d := by
    have h := cSqfreeYunFFG_pow_dvd hgcd d hd0 hpp idx hidx
    rwa [Nat.add_comm 1 idx] at h
  have hmul : toPoly u * toPoly v ^ (idx + 1) = toPoly d :=
    toPolyG_cdivWf_pow_mul d v (idx + 1) hv0 hpow
  -- base-change the goal `IsCoprime u v` to `K̄`
  rw [← Polynomial.isCoprime_map (algebraMap (CFieldSpec.K α) (AlgebraicClosure (CFieldSpec.K α)))]
  refine IsCoprime.symm ?_
  -- `v` splits over `K̄` (monic squarefree ⟹ separable)
  have hvmonicE : ((toPoly v).map (algebraMap (CFieldSpec.K α)
      (AlgebraicClosure (CFieldSpec.K α)))).Monic :=
    (cSqfreeYunFFG_monic hgcd d hd0 v (List.getElem_mem hidx)).map _
  have hvsfE : Squarefree ((toPoly v).map (algebraMap (CFieldSpec.K α)
      (AlgebraicClosure (CFieldSpec.K α)))) := yun_factor_map_squarefree hgcd d ⟨hd0, hpp⟩ hidx
  have hvsepE : ((toPoly v).map (algebraMap (CFieldSpec.K α)
      (AlgebraicClosure (CFieldSpec.K α)))).Separable :=
    PerfectField.separable_iff_squarefree.mpr hvsfE
  have hvmap0 : (toPoly v).map (algebraMap (CFieldSpec.K α)
      (AlgebraicClosure (CFieldSpec.K α))) ≠ 0 := (Polynomial.map_ne_zero_iff hφinj).mpr hv0
  have hdmap0 : (toPoly d).map (algebraMap (CFieldSpec.K α)
      (AlgebraicClosure (CFieldSpec.K α))) ≠ 0 := (Polynomial.map_ne_zero_iff hφinj).mpr hd0
  have humap0 : (toPoly u).map (algebraMap (CFieldSpec.K α)
      (AlgebraicClosure (CFieldSpec.K α))) ≠ 0 := (Polynomial.map_ne_zero_iff hφinj).mpr (by
    intro h0; rw [h0, zero_mul] at hmul; exact hd0 hmul.symm)
  rw [monic_separable_eq_nodal _ hvmonicE hvsepE, Lagrange.nodal]
  refine IsCoprime.prod_left ?_
  intro β hβ
  simp only [id_eq]
  have hβroot : β ∈ ((toPoly v).map (algebraMap (CFieldSpec.K α)
      (AlgebraicClosure (CFieldSpec.K α)))).roots := Multiset.mem_toFinset.mp hβ
  -- `IsCoprime (X - C β) u ⟺ β` is not a root of `u`
  rw [(Polynomial.irreducible_X_sub_C β).coprime_iff_not_dvd, Polynomial.dvd_iff_isRoot]
  intro hroot
  have hmd : rootMultiplicity β ((toPoly d).map (algebraMap (CFieldSpec.K α)
      (AlgebraicClosure (CFieldSpec.K α)))) = idx + 1 :=
    rootMult_R_map_eq_idx_succ hgcd d ⟨hd0, hpp⟩ idx hidx β hβroot
  have hmapmul : (toPoly d).map (algebraMap (CFieldSpec.K α)
        (AlgebraicClosure (CFieldSpec.K α)))
      = ((toPoly u).map (algebraMap (CFieldSpec.K α) (AlgebraicClosure (CFieldSpec.K α))))
        * ((toPoly v).map (algebraMap (CFieldSpec.K α)
            (AlgebraicClosure (CFieldSpec.K α)))) ^ (idx + 1) := by
    rw [← Polynomial.map_pow, ← Polynomial.map_mul, hmul]
  have hmv : rootMultiplicity β ((toPoly v).map (algebraMap (CFieldSpec.K α)
      (AlgebraicClosure (CFieldSpec.K α)))) = 1 :=
    squarefree_rootMultiplicity_eq_one hvsfE β (Polynomial.isRoot_of_mem_roots hβroot)
  rw [hmapmul, Polynomial.rootMultiplicity_mul (mul_ne_zero humap0 (pow_ne_zero _ hvmap0)),
    rootMultiplicity_pow_eq _ _ _ hvmap0, hmv, mul_one] at hmd
  have hpos : 0 < rootMultiplicity β ((toPoly u).map (algebraMap (CFieldSpec.K α)
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
theorem hcopgcd_of_genuineMonomial [CharZero (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (Dt d : DensePoly α) (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0)
    (hgen : GenuinePrimitiveMonomialLrt Dt) :
    ∀ x ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1 ≠ 0 := by
  intro x hx
  have hxzip : x ∈ (cSqfreeYunFF d).zipIdx := List.mem_of_mem_filter hx
  obtain ⟨hidx, hget⟩ := List.getElem?_eq_some_iff.mp
    (List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hxzip))
  have hxmem : x.1 ∈ cSqfreeYunFF d := by rw [← hget]; exact List.getElem_mem hidx
  apply natDegree_cgcdWf_eq_zero_of_isCoprime
  simp only [denote]
  refine IsCoprime.mul_left ?_ ?_
  · -- cofactor coprimality `IsCoprime (d/v^(x.2+1)) v`
    rw [← hget]
    exact isCoprime_cofactor_yunFactor hgcd d hd0 hpp x.2 hidx
  · -- tower-derivative normality `IsCoprime (D v) v`
    refine (isCoprime_implicitDeriv_of_genuineMonomial Dt x.1 hgen
      (cSqfreeYunFFG_monic hgcd d hd0 x.1 hxmem) ?_).symm
    rw [← hget]; exact cSqfreeYunFFG_squarefree hgcd d hd0 hpp x.2 hidx

set_option maxHeartbeats 1600000 in
open scoped Differential in
/-- **Hermite properness from the per-factor differential-normality certificate.** For `deg Dt ≤ 1` and a
proper input, the Hermite remainder is proper whenever every repeated Yun factor satisfies `hcopgcd`.
Discharges every other hypothesis of `cHermiteReduceTowerG_leftover_proper_of_degree_le_one`:
`hv`/`hb` from Yun `get_ne_zero` + `diophantineReduced_fst_degree_lt`; `hDstar`/`hresDen` from the radical/denominator
nonvanishing; and residual divisibility from `hWgd_of_multiplicity` via `d = W·Dstar`. -/
theorem hAD_degree_of_hcopgcd [CharZero (CFieldSpec.K α)]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0)
    (hpp : (toPoly d).primPart ≠ 0) (hDtdeg : (toPoly Dt).natDegree ≤ 1)
    (haProper : (toPoly a).degree < (toPoly d).degree)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1 ≠ 0) :
    (toPoly (cHermiteReduceTower Dt a d).2.1).degree
      < (toPoly (cHermiteReduceTower Dt a d).2.2).degree := by
  have hgd0 : toPoly (cHermiteReduceTower Dt a d).1.2 ≠ 0 :=
    toPolyG_cHermiteReduceTowerG_den_ne_zero hgcd Dt a d hd0 hpp
  set g := (cSqfreeYunFF d).zipIdx.foldl
      (fun (gAcc : DensePoly α × DensePoly α) (vi, idx) =>
          let i := idx + 1
          if i ≤ 1 then gAcc
          else
            let Vi_pow := cpow vi i
            let u := CPolyEuclidean.div d Vi_pow
            let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a ([CCommRing.zero], [CCommRing.one])).1
            (cadd (cmul gAcc.1 gloc.2) (cmul gloc.1 gAcc.2), cmul gAcc.2 gloc.2))
      ([CCommRing.zero], [CCommRing.one]) with hg_def
  -- raw-fold `g` ↔ `cnorm`-projection bridges (equal through `toPoly`)
  have hg1 : toPoly (cHermiteReduceTower Dt a d).1.1 = toPoly g.1 := by
    rw [hg_def]; simp only [cHermiteReduceTower, squarefreeYun_dense_wf_eq, denote]
  have hg2 : toPoly (cHermiteReduceTower Dt a d).1.2 = toPoly g.2 := by
    rw [hg_def]; simp only [cHermiteReduceTower, squarefreeYun_dense_wf_eq, denote]
  have hDsF : toPoly (cHermiteReduceTower Dt a d).2.2
      = toPoly ((cSqfreeYunFF d).foldl (fun acc vi => cmul acc vi) [CCommRing.one]) := by
    simp only [cHermiteReduceTower, squarefreeYun_dense_wf_eq, denote]
  have hDstar0 : toPoly ((cSqfreeYunFF d).foldl (fun acc vi => cmul acc vi) [CCommRing.one]) ≠ 0 := by
    rw [← hDsF]; exact (toPolyG_cHermiteReduceTowerG_Dstar_monic hgcd Dt a d hd0).ne_zero
  have hg2ne : toPoly g.2 ≠ 0 := by rw [← hg2]; exact hgd0
  refine cHermiteReduceTowerG_leftover_proper_of_degree_le_one Dt a d hDtdeg haProper
    ?_ g hg_def ?_ ?_ hDstar0
  · -- hfac : each repeated Yun factor is nonzero and has proper Diophantine cofactors
    intro p hp _
    refine ⟨?_, ?_⟩
    · obtain ⟨hidx, hget⟩ := List.getElem?_eq_some_iff.mp
        (List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hp))
      rw [← hget]; exact cSqfreeYunFFG_get_ne_zero hgcd d hd0 hpp p.2 hidx
    · intro rhs
      refine diophantineReduced_fst_degree_lt _ p.1 rhs ?_
      intro h
      obtain ⟨hidx, hget⟩ := List.getElem?_eq_some_iff.mp
        (List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hp))
      rw [← hget] at h
      exact cSqfreeYunFFG_get_ne_zero hgcd d hd0 hpp p.2 hidx ((cnormG_eq_nil_iff _).mp h)
  · -- hdvd : `d·g.2² ∣ resNum·Dstar`, from `hWgd` (`W·g.2² ∣ resNum`) and `d = W·Dstar`
    have hWgd := hWgd_of_multiplicity hgcd Dt a d hd0 hpp hgd0 hcopgcd
    have hHermDsNe : toPoly (cHermiteReduceTower Dt a d).2.2 ≠ 0 :=
      (toPolyG_cHermiteReduceTowerG_Dstar_monic hgcd Dt a d hd0).ne_zero
    have hWD : toPoly (CPolyEuclidean.div d (cHermiteReduceTower Dt a d).2.2)
        * toPoly ((cSqfreeYunFF d).foldl (fun acc vi => cmul acc vi) [CCommRing.one]) = toPoly d := by
      rw [← hDsF]
      exact toPolyG_div_exact d (cHermiteReduceTower Dt a d).2.2
        (fun h => hHermDsNe ((cnormG_eq_nil_iff _).mp h))
        (toPolyG_cHermiteReduceTowerG_Dstar_dvd hgcd Dt a d hd0)
    -- push `hWgd` from the `cnorm`-projections to `g` (through `toPoly`)
    rw [hg2] at hWgd
    have htransport :
        toPoly (csub (cmul a (cmul (cHermiteReduceTower Dt a d).1.2
              (cHermiteReduceTower Dt a d).1.2))
            (cmul d (csub (cmul (CPolyEngine.monomialDeriv Dt (cHermiteReduceTower Dt a d).1.1)
                (cHermiteReduceTower Dt a d).1.2)
              (cmul (cHermiteReduceTower Dt a d).1.1
                (CPolyEngine.monomialDeriv Dt (cHermiteReduceTower Dt a d).1.2)))))
          = toPoly (csub (cmul a (cmul g.2 g.2))
            (cmul d (csub (cmul (CPolyEngine.monomialDeriv Dt g.1) g.2)
              (cmul g.1 (CPolyEngine.monomialDeriv Dt g.2))))) := by
      simp only [denote, hg1, hg2]
    rw [htransport] at hWgd
    -- assemble `d·g.2² ∣ resNum·Dstar` from `W·g.2² ∣ resNum` and `d = W·Dstar`
    rw [toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG]
    rw [show toPoly d * (toPoly g.2 * toPoly g.2)
          = toPoly ((cSqfreeYunFF d).foldl (fun acc vi => cmul acc vi) [CCommRing.one])
            * (toPoly (CPolyEuclidean.div d (cHermiteReduceTower Dt a d).2.2) * (toPoly g.2 * toPoly g.2))
        from by rw [← hWD]; ring,
      mul_comm (toPoly (csub (cmul a (cmul g.2 g.2))
        (cmul d (csub (cmul (CPolyEngine.monomialDeriv Dt g.1) g.2) (cmul g.1 (CPolyEngine.monomialDeriv Dt g.2))))))]
    exact mul_dvd_mul_left _ hWgd
  · -- hresDen : `d·g.2² ≠ 0`
    intro h
    have h0 := (cnormG_eq_nil_iff _).mp h
    simp only [denote] at h0
    exact mul_ne_zero hd0 (mul_ne_zero hg2ne hg2ne) h0

/-- Hermite properness follows from the genuine primitive-monomial property. -/
theorem hAD_degree_of_genuineMonomial [CharZero (CFieldSpec.K α)]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0)
    (hpp : (toPoly d).primPart ≠ 0) (hDtdeg : (toPoly Dt).natDegree ≤ 1)
    (haProper : (toPoly a).degree < (toPoly d).degree) (hgen : GenuinePrimitiveMonomialLrt Dt) :
    (toPoly (cHermiteReduceTower Dt a d).2.1).degree
      < (toPoly (cHermiteReduceTower Dt a d).2.2).degree :=
  hAD_degree_of_hcopgcd hgcd Dt a d hd0 hpp hDtdeg haProper
    (hcopgcd_of_genuineMonomial hgcd Dt d hd0 hpp hgen)

end DeepWiki.SymbolicIntegration
