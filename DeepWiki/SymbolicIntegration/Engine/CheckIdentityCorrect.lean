import DeepWiki.SymbolicIntegration.Engine.Tower.RischDE
import DeepWiki.SymbolicIntegration.Engine.RischDE.TowerCorrectG

/-! # Representation-independent `checkIdentity` correctness

The executable checker is defined over any lawful `CPoly` representation. This module proves its
field-identity meaning through `CPoly.toPoly`; the older dense bridge remains a specialization for
call sites stated with `DensePoly.toPoly`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open CFrac

universe u v

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]
  [Algebra ℚ (CFieldSpec.K α)]

/-! ### The generic fraction-field derivation -/

/-- The tower fraction-field derivation induced by the represented monomial derivative `Dt`. -/
noncomputable def towerFractionFieldDerivP (Dt : P α) :
    Derivation ℤ (RatFunc (CFieldSpec.K α)) (RatFunc (CFieldSpec.K α)) :=
  extendDeriv (Differential.implicitDeriv (CPoly.toPoly Dt))

omit [CPolyEngine P] [LawfulCPolyEngine P] in
/-- Quotient rule for the represented tower fraction-field derivation. -/
theorem towerFractionFieldDerivP_div (Dt : P α) (gnum gden : (CFieldSpec.K α)[X]) :
    towerFractionFieldDerivP Dt (CFrac.am α gnum / CFrac.am α gden)
      = (CFrac.am α (Differential.implicitDeriv (CPoly.toPoly Dt) gnum) * CFrac.am α gden
          - CFrac.am α gnum * CFrac.am α (Differential.implicitDeriv (CPoly.toPoly Dt) gden))
        / (CFrac.am α gden) ^ 2 := by
  rw [towerFractionFieldDerivP, ← RatFunc.mk_eq_div, extendDeriv_mk, RatFunc.mk_eq_div, map_sub,
    map_mul, map_mul, map_pow]

/-- A represented monomial logarithmic derivative reads through `towerFractionFieldDerivP`. -/
theorem towerFractionFieldDerivP_logDeriv (Dt v : P α) :
    towerFractionFieldDerivP Dt (CFrac.am α (CPoly.toPoly v)) / CFrac.am α (CPoly.toPoly v)
      = CFrac.am α (CPoly.toPoly (CPolyEngine.monomialDeriv Dt v)) /
          CFrac.am α (CPoly.toPoly v) := by
  rw [towerFractionFieldDerivP, extendDeriv_algebraMap]
  simp only [CPolyEngine.toPoly_monomialDeriv]

/-! ### The logarithmic-part residue sum -/

/-- The generic logarithmic residue sum induced by a represented tower derivative. -/
noncomputable def logResidueSumP (Dt : P α) (logs : List (α × P α)) :
    RatFunc (CFieldSpec.K α) :=
  (logs.map (fun cv =>
    CFrac.am α (Polynomial.C (CFieldSpec.toK cv.1)) *
      (CFrac.am α (CPoly.toPoly (CPolyEngine.monomialDeriv Dt cv.2)) /
        CFrac.am α (CPoly.toPoly cv.2)))).sum

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] [LawfulCPolyEngine P] in
/-- An empty generic logarithmic residue sum is zero. -/
@[simp] theorem logResidueSumP_nil (Dt : P α) : logResidueSumP Dt ([] : List (α × P α)) = 0 :=
  rfl

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] [LawfulCPolyEngine P] in
/-- `logResidueSumP` peels its leading logarithmic term. -/
theorem logResidueSumP_cons (Dt : P α) (cv : α × P α) (rest : List (α × P α)) :
    logResidueSumP Dt (cv :: rest)
      = CFrac.am α (Polynomial.C (CFieldSpec.toK cv.1)) *
          (CFrac.am α (CPoly.toPoly (CPolyEngine.monomialDeriv Dt cv.2)) /
            CFrac.am α (CPoly.toPoly cv.2))
        + logResidueSumP Dt rest := by
  simp only [logResidueSumP, List.map_cons, List.sum_cons]

/-- `logResidueSumP` is the sum of the represented arguments' field logarithmic derivatives. -/
theorem logResidueSumP_eq_logDeriv_sum (Dt : P α) (logs : List (α × P α)) :
    logResidueSumP Dt logs
      = (logs.map (fun cv =>
          CFrac.am α (Polynomial.C (CFieldSpec.toK cv.1)) *
            (towerFractionFieldDerivP Dt (CFrac.am α (CPoly.toPoly cv.2)) /
              CFrac.am α (CPoly.toPoly cv.2)))).sum := by
  rw [logResidueSumP]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro cv _
  rw [towerFractionFieldDerivP_logDeriv]

/-! ### The checker fold computes the residue sum -/

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The generic `checkIdentity` logarithmic fold denotes its seed plus `logResidueSumP`. -/
theorem checkIdentityP_fold_eq (Dt : P α) :
    ∀ (logs : List (α × P α)) (snum sden : P α),
      CPoly.toPoly sden ≠ 0 →
      (∀ cv ∈ logs, CPoly.toPoly cv.2 ≠ 0) →
      let res := logs.foldl
        (fun (acc : P α × P α) (cv : α × P α) =>
          let c := cv.1
          let v := cv.2
          let Dv := CPolyEngine.monomialDeriv Dt v
          let termNum := CPolyEngine.scale c Dv
          (CPolyEngine.add (CPolyEngine.mul acc.1 v) (CPolyEngine.mul termNum acc.2),
            CPolyEngine.mul acc.2 v))
        (snum, sden)
      CPoly.toPoly res.2 ≠ 0 ∧
        CFrac.am α (CPoly.toPoly res.1) / CFrac.am α (CPoly.toPoly res.2)
          = CFrac.am α (CPoly.toPoly snum) / CFrac.am α (CPoly.toPoly sden) +
            logResidueSumP Dt logs := by
  intro logs
  induction logs with
  | nil =>
    intro snum sden hsden _
    refine ⟨hsden, ?_⟩
    simp only [logResidueSumP_nil, add_zero, List.foldl_nil]
  | cons cv rest ih =>
    intro snum sden hsden hv
    have hvne : CPoly.toPoly cv.2 ≠ 0 := hv cv List.mem_cons_self
    set newnum := CPolyEngine.add (CPolyEngine.mul snum cv.2)
      (CPolyEngine.mul (CPolyEngine.scale cv.1 (CPolyEngine.monomialDeriv Dt cv.2)) sden)
      with hnewnum
    set newden := CPolyEngine.mul sden cv.2 with hnewden
    have hnewden_ne : CPoly.toPoly newden ≠ 0 := by
      rw [hnewden, LawfulCPolyEngine.toPoly_mul]
      exact mul_ne_zero hsden hvne
    have hrest : ∀ cv' ∈ rest, CPoly.toPoly cv'.2 ≠ 0 :=
      fun cv' hcv' => hv cv' (List.mem_cons_of_mem _ hcv')
    obtain ⟨hden, heq⟩ := ih newnum newden hnewden_ne hrest
    refine ⟨?_, ?_⟩
    · simp only [List.foldl_cons]
      exact hden
    simp only [List.foldl_cons]
    rw [heq, logResidueSumP_cons]
    have hAsden : CFrac.am α (CPoly.toPoly sden) ≠ 0 := CFrac.am_ne_zero hsden
    have hAv : CFrac.am α (CPoly.toPoly cv.2) ≠ 0 := CFrac.am_ne_zero hvne
    have hstep : CFrac.am α (CPoly.toPoly newnum) / CFrac.am α (CPoly.toPoly newden)
        = CFrac.am α (CPoly.toPoly snum) / CFrac.am α (CPoly.toPoly sden)
          + CFrac.am α (Polynomial.C (CFieldSpec.toK cv.1)) *
              (CFrac.am α (CPoly.toPoly (CPolyEngine.monomialDeriv Dt cv.2)) /
                CFrac.am α (CPoly.toPoly cv.2)) := by
      rw [hnewnum, hnewden]
      simp only [LawfulCPolyEngine.toPoly_add, LawfulCPolyEngine.toPoly_mul,
        LawfulCPolyEngine.toPoly_scale, toR_eq_toK, map_add, map_mul]
      field_simp
    rw [hstep]
    ring

/-! ### The generic checker-to-identity bridge -/

/-- A successful representation-independent `checkIdentity` check yields the corresponding field identity. -/
theorem field_identity_of_checkIdentityP (Dt : P α) (res : IntegralResult α P)
    (anum aden : P α)
    (hgden : CPoly.toPoly res.rational.2 ≠ 0) (haden : CPoly.toPoly aden ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, CPoly.toPoly cv.2 ≠ 0)
    (hcheck : CPoly.checkIdentity Dt res anum aden = true) :
    towerFractionFieldDerivP Dt
        (CFrac.am α (CPoly.toPoly res.rational.1) / CFrac.am α (CPoly.toPoly res.rational.2))
      + logResidueSumP Dt res.logs
      = CFrac.am α (CPoly.toPoly anum) / CFrac.am α (CPoly.toPoly aden) := by
  set gnum := res.rational.1 with hgnum
  set gden := res.rational.2 with hgdenE
  set gprimeNum := CPolyEngine.sub
    (CPolyEngine.mul (CPolyEngine.monomialDeriv Dt gnum) gden)
    (CPolyEngine.mul gnum (CPolyEngine.monomialDeriv Dt gden)) with hgp
  set gden2 := CPolyEngine.mul gden gden with hgden2
  set folded := res.logs.foldl
    (fun (acc : P α × P α) (cv : α × P α) =>
      let c := cv.1
      let v := cv.2
      let Dv := CPolyEngine.monomialDeriv Dt v
      let termNum := CPolyEngine.scale c Dv
      (CPolyEngine.add (CPolyEngine.mul acc.1 v) (CPolyEngine.mul termNum acc.2),
        CPolyEngine.mul acc.2 v))
    (CPolyEngine.ofCoeffList [CCommRing.zero], CPolyEngine.ofCoeffList [CCommRing.one]) with hfolded
  have hseedden : CPoly.toPoly
      (CPolyEngine.ofCoeffList (P := P) [(CCommRing.one : α)]) ≠ 0 := by
    rw [LawfulCPolyEngine.toPoly_ofCoeffList, CPoly.toPoly_ofList_one]
    exact one_ne_zero
  obtain ⟨hLden_ne, hLfield⟩ := checkIdentityP_fold_eq Dt res.logs
    (CPolyEngine.ofCoeffList [(CCommRing.zero : α)])
    (CPolyEngine.ofCoeffList [(CCommRing.one : α)]) hseedden hlogs
  rw [← hfolded] at hLden_ne hLfield
  have hseed0 : CFrac.am α
      (CPoly.toPoly (CPolyEngine.ofCoeffList (P := P) [(CCommRing.zero : α)])) /
      CFrac.am α
        (CPoly.toPoly (CPolyEngine.ofCoeffList (P := P) [(CCommRing.one : α)])) = 0 := by
    simp only [LawfulCPolyEngine.toPoly_ofCoeffList, CPoly.toPoly_ofList_zero,
      CPoly.toPoly_ofList_one, map_zero, map_one, zero_div]
  rw [hseed0, zero_add] at hLfield
  set GP := CFrac.am α (CPoly.toPoly gprimeNum) with hGP
  set LN := CFrac.am α (CPoly.toPoly folded.1) with hLN
  set LD := CFrac.am α (CPoly.toPoly folded.2) with hLD
  set AN := CFrac.am α (CPoly.toPoly anum) with hAN
  set AD := CFrac.am α (CPoly.toPoly aden) with hAD
  set GD := CFrac.am α (CPoly.toPoly gden) with hGD
  have hGDne : GD ≠ 0 := by rw [hGD]; exact CFrac.am_ne_zero hgden
  have hLDne : LD ≠ 0 := by rw [hLD]; exact CFrac.am_ne_zero hLden_ne
  have hADne : AD ≠ 0 := by rw [hAD]; exact CFrac.am_ne_zero haden
  have hGD2 : CFrac.am α (CPoly.toPoly gden2) = GD ^ 2 := by
    rw [hgden2, LawfulCPolyEngine.toPoly_mul]
    simp only [map_mul, hGD, pow_two]
  have hquot : towerFractionFieldDerivP Dt (CFrac.am α (CPoly.toPoly gnum) /
      CFrac.am α (CPoly.toPoly gden)) = GP / GD ^ 2 := by
    rw [towerFractionFieldDerivP_div, hGP, hgp, CPolyEngine.toPoly_sub]
    simp only [LawfulCPolyEngine.toPoly_mul, CPolyEngine.toPoly_monomialDeriv,
      map_sub, map_mul]
    rw [hGD]
  have hLfield' : logResidueSumP Dt res.logs = LN / LD := by rw [← hLfield, hLN, hLD]
  rw [CPoly.checkIdentity] at hcheck
  rw [LawfulCPolyEngine.cisZero_iff] at hcheck
  simp only [← hgnum, ← hgdenE, ← hgp, ← hgden2, ← hfolded,
    CPolyEngine.toPoly_sub, LawfulCPolyEngine.toPoly_mul,
    LawfulCPolyEngine.toPoly_add, sub_eq_zero] at hcheck
  rw [← (RatFunc.algebraMap_injective (CFieldSpec.K α)).eq_iff] at hcheck
  simp only [map_mul, map_add] at hcheck
  change (GP * LD + LN * CFrac.am α (CPoly.toPoly gden2)) * AD =
    AN * (CFrac.am α (CPoly.toPoly gden2) * LD) at hcheck
  rw [hGD2] at hcheck
  have hfield : GP / GD ^ 2 + LN / LD = AN / AD := by
    rw [div_add_div _ _ (pow_ne_zero 2 hGDne) hLDne,
      div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hGDne) hLDne) hADne]
    ring_nf
    ring_nf at hcheck
    linear_combination hcheck
  rw [hGD, hquot, hLfield', hfield]

/-- A valid field identity with nonzero represented denominators is accepted by `checkIdentity`. -/
theorem checkIdentityP_of_field_identity (Dt : P α) (res : IntegralResult α P)
    (anum aden : P α)
    (hgden : CPoly.toPoly res.rational.2 ≠ 0) (haden : CPoly.toPoly aden ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, CPoly.toPoly cv.2 ≠ 0)
    (hidentity :
      towerFractionFieldDerivP Dt
          (CFrac.am α (CPoly.toPoly res.rational.1) /
            CFrac.am α (CPoly.toPoly res.rational.2)) +
        logResidueSumP Dt res.logs =
          CFrac.am α (CPoly.toPoly anum) / CFrac.am α (CPoly.toPoly aden)) :
    CPoly.checkIdentity Dt res anum aden = true := by
  set gnum := res.rational.1 with hgnum
  set gden := res.rational.2 with hgdenE
  set gprimeNum := CPolyEngine.sub
    (CPolyEngine.mul (CPolyEngine.monomialDeriv Dt gnum) gden)
    (CPolyEngine.mul gnum (CPolyEngine.monomialDeriv Dt gden)) with hgp
  set gden2 := CPolyEngine.mul gden gden with hgden2
  set folded := res.logs.foldl
    (fun (acc : P α × P α) (cv : α × P α) =>
      let c := cv.1
      let v := cv.2
      let Dv := CPolyEngine.monomialDeriv Dt v
      let termNum := CPolyEngine.scale c Dv
      (CPolyEngine.add (CPolyEngine.mul acc.1 v) (CPolyEngine.mul termNum acc.2),
        CPolyEngine.mul acc.2 v))
    (CPolyEngine.ofCoeffList [CCommRing.zero], CPolyEngine.ofCoeffList [CCommRing.one]) with hfolded
  have hseedden : CPoly.toPoly
      (CPolyEngine.ofCoeffList (P := P) [(CCommRing.one : α)]) ≠ 0 := by
    rw [LawfulCPolyEngine.toPoly_ofCoeffList, CPoly.toPoly_ofList_one]
    exact one_ne_zero
  obtain ⟨hLden_ne, hLfield⟩ := checkIdentityP_fold_eq Dt res.logs
    (CPolyEngine.ofCoeffList [(CCommRing.zero : α)])
    (CPolyEngine.ofCoeffList [(CCommRing.one : α)]) hseedden hlogs
  rw [← hfolded] at hLden_ne hLfield
  have hseed0 : CFrac.am α
      (CPoly.toPoly (CPolyEngine.ofCoeffList (P := P) [(CCommRing.zero : α)])) /
      CFrac.am α
        (CPoly.toPoly (CPolyEngine.ofCoeffList (P := P) [(CCommRing.one : α)])) = 0 := by
    simp only [LawfulCPolyEngine.toPoly_ofCoeffList, CPoly.toPoly_ofList_zero,
      CPoly.toPoly_ofList_one, map_zero, map_one, zero_div]
  rw [hseed0, zero_add] at hLfield
  set GP := CFrac.am α (CPoly.toPoly gprimeNum) with hGP
  set LN := CFrac.am α (CPoly.toPoly folded.1) with hLN
  set LD := CFrac.am α (CPoly.toPoly folded.2) with hLD
  set AN := CFrac.am α (CPoly.toPoly anum) with hAN
  set AD := CFrac.am α (CPoly.toPoly aden) with hAD
  set GD := CFrac.am α (CPoly.toPoly gden) with hGD
  have hGDne : GD ≠ 0 := by rw [hGD]; exact CFrac.am_ne_zero hgden
  have hLDne : LD ≠ 0 := by rw [hLD]; exact CFrac.am_ne_zero hLden_ne
  have hADne : AD ≠ 0 := by rw [hAD]; exact CFrac.am_ne_zero haden
  have hGD2 : CFrac.am α (CPoly.toPoly gden2) = GD ^ 2 := by
    rw [hgden2, LawfulCPolyEngine.toPoly_mul]
    simp only [map_mul, hGD, pow_two]
  have hquot : towerFractionFieldDerivP Dt (CFrac.am α (CPoly.toPoly gnum) /
      CFrac.am α (CPoly.toPoly gden)) = GP / GD ^ 2 := by
    rw [towerFractionFieldDerivP_div, hGP, hgp, CPolyEngine.toPoly_sub]
    simp only [LawfulCPolyEngine.toPoly_mul, CPolyEngine.toPoly_monomialDeriv,
      map_sub, map_mul]
    rw [hGD]
  have hLfield' : logResidueSumP Dt res.logs = LN / LD := by rw [← hLfield, hLN, hLD]
  have hfield : GP / GD ^ 2 + LN / LD = AN / AD := by
    rw [hGD, hquot, hLfield'] at hidentity
    exact hidentity
  have hcleared : (GP * LD + LN * GD ^ 2) * AD = AN * (GD ^ 2 * LD) := by
    rw [div_add_div _ _ (pow_ne_zero 2 hGDne) hLDne,
      div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hGDne) hLDne) hADne] at hfield
    ring_nf at hfield ⊢
    linear_combination hfield
  rw [CPoly.checkIdentity, LawfulCPolyEngine.cisZero_iff]
  simp only [← hgnum, ← hgdenE, ← hgp, ← hgden2, ← hfolded,
    CPolyEngine.toPoly_sub, LawfulCPolyEngine.toPoly_mul,
    LawfulCPolyEngine.toPoly_add, sub_eq_zero]
  rw [← (RatFunc.algebraMap_injective (CFieldSpec.K α)).eq_iff]
  simp only [map_mul, map_add]
  change (GP * LD + LN * CFrac.am α (CPoly.toPoly gden2)) * AD =
    AN * (CFrac.am α (CPoly.toPoly gden2) * LD)
  rw [hGD2]
  exact hcleared

/-- With nonzero represented denominators, `checkIdentity` exactly reflects its field identity. -/
theorem checkIdentityP_iff_field_identity (Dt : P α) (res : IntegralResult α P)
    (anum aden : P α)
    (hgden : CPoly.toPoly res.rational.2 ≠ 0) (haden : CPoly.toPoly aden ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, CPoly.toPoly cv.2 ≠ 0) :
    CPoly.checkIdentity Dt res anum aden = true ↔
      towerFractionFieldDerivP Dt
          (CFrac.am α (CPoly.toPoly res.rational.1) /
            CFrac.am α (CPoly.toPoly res.rational.2)) +
        logResidueSumP Dt res.logs =
          CFrac.am α (CPoly.toPoly anum) / CFrac.am α (CPoly.toPoly aden) :=
  ⟨field_identity_of_checkIdentityP Dt res anum aden hgden haden hlogs,
    checkIdentityP_of_field_identity Dt res anum aden hgden haden hlogs⟩

end DeepWiki.SymbolicIntegration
