import DeepWiki.SymbolicIntegration.Engine.Tower.RischDE
import DeepWiki.SymbolicIntegration.Engine.RischDE.TowerCorrectG

/-! # The `checkIdentity` ⟹ field-identity bridge

`checkIdentity = true` implies the field identity `D(∫f) = f` over the tower fraction field
`RatFunc (CFieldSpec.K α)`, via the residue sum `logResidueSum` and derivation
`towerFractionFieldDeriv`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

/-! ### The generic fraction-field derivation -/

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Tower fraction-field derivation `extendDeriv (implicitDeriv (toPoly Dt))` on
`RatFunc (CFieldSpec.K α)`. -/
noncomputable def towerFractionFieldDeriv (Dt : DensePoly α) :
    Derivation ℤ (RatFunc (CFieldSpec.K α)) (RatFunc (CFieldSpec.K α)) :=
  extendDeriv (Differential.implicitDeriv (toPoly Dt))

/-- Quotient rule on a fraction of polynomial images: `towerFractionFieldDeriv Dt (am gnum / am gden)
= (am(Δ gnum)·am(gden) − am(gnum)·am(Δ gden)) / (am gden)²`, `Δ = implicitDeriv (toPoly Dt)`. -/
theorem towerFractionFieldDerivG_div (Dt : DensePoly α) (gnum gden : (CFieldSpec.K α)[X]) :
    towerFractionFieldDeriv Dt (am α gnum / am α gden)
      = (am α (Differential.implicitDeriv (toPoly Dt) gnum) * am α gden
          - am α gnum * am α (Differential.implicitDeriv (toPoly Dt) gden))
        / (am α gden) ^ 2 := by
  rw [towerFractionFieldDeriv, ← RatFunc.mk_eq_div, extendDeriv_mk, RatFunc.mk_eq_div, map_sub,
    map_mul, map_mul, map_pow]

/-- Per-term log-derivative reading:
`towerFractionFieldDeriv Dt (am v)/am v = am (toPoly (CPolyEngine.monomialDeriv Dt v))/am (toPoly v)`. -/
theorem towerFractionFieldDerivG_logDeriv (Dt v : DensePoly α) :
    towerFractionFieldDeriv Dt (am α (toPoly v)) / am α (toPoly v)
      = am α (toPoly (CPolyEngine.monomialDeriv Dt v)) / am α (toPoly v) := by
  rw [towerFractionFieldDeriv, extendDeriv_algebraMap]
  simp only [denote]

/-! ### The logarithmic-part residue sum -/

/-- Logarithmic-part residue sum `∑_{(c,v)∈logs} am(C(toK c))·(Δv)/v` over
`RatFunc (CFieldSpec.K α)`, `Δ = implicitDeriv (toPoly Dt)`. -/
noncomputable def logResidueSum (Dt : DensePoly α) (logs : List (α × DensePoly α)) :
    RatFunc (CFieldSpec.K α) :=
  (logs.map (fun cv =>
    am α (Polynomial.C (CFieldSpec.toK cv.1))
      * (am α (toPoly (CPolyEngine.monomialDeriv Dt cv.2)) / am α (toPoly cv.2)))).sum

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `logResidueSum` of the empty list is `0`. -/
@[simp] theorem logResidueSumG_nil (Dt : DensePoly α) : logResidueSum Dt ([] : List (α × DensePoly α)) = 0 :=
  rfl

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `logResidueSum` peels the head: `logResidueSum Dt ((c,v) :: rest) = am(C(toK c))·(Δv)/v
+ logResidueSum Dt rest`. -/
theorem logResidueSumG_cons (Dt : DensePoly α) (cv : α × DensePoly α) (rest : List (α × DensePoly α)) :
    logResidueSum Dt (cv :: rest)
      = am α (Polynomial.C (CFieldSpec.toK cv.1))
          * (am α (toPoly (CPolyEngine.monomialDeriv Dt cv.2)) / am α (toPoly cv.2))
        + logResidueSum Dt rest := by
  simp only [logResidueSum, List.map_cons, List.sum_cons]

/-- `logResidueSum` reads as the monomial log-derivative sum
`∑_{(c,v)} am(C(toK c))·(towerFractionFieldDeriv Dt (am v)/am v)`. -/
theorem logResidueSumG_eq_logDeriv_sum (Dt : DensePoly α) (logs : List (α × DensePoly α)) :
    logResidueSum Dt logs
      = (logs.map (fun cv =>
          am α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDeriv Dt (am α (toPoly cv.2)) / am α (toPoly cv.2)))).sum := by
  rw [logResidueSum]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro cv _
  rw [towerFractionFieldDerivG_logDeriv]

/-! ### The `checkIdentity` fold computes the residue sum -/

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The `checkIdentity` fold computes the residue sum: its running fraction equals the seed fraction
plus `logResidueSum`, with the running denominator staying nonzero. -/
theorem checkIdentityG_fold_eq (Dt : DensePoly α) :
    ∀ (logs : List (α × DensePoly α)) (snum sden : DensePoly α),
      toPoly sden ≠ 0 →
      (∀ cv ∈ logs, toPoly cv.2 ≠ 0) →
      let res := logs.foldl
        (fun (acc : DensePoly α × DensePoly α) (cv : α × DensePoly α) =>
          let c := cv.1
          let v := cv.2
          let Dv := CPolyEngine.monomialDeriv Dt v
          let termNum := cscale c Dv
          (cadd (cmul acc.1 v) (cmul termNum acc.2), cmul acc.2 v))
        (snum, sden)
      toPoly res.2 ≠ 0 ∧
        am α (toPoly res.1) / am α (toPoly res.2)
          = am α (toPoly snum) / am α (toPoly sden) + logResidueSum Dt logs := by
  intro logs
  induction logs with
  | nil =>
    intro snum sden hsden _
    refine ⟨hsden, ?_⟩
    simp only [logResidueSumG_nil, add_zero, List.foldl_nil]
  | cons cv rest ih =>
    intro snum sden hsden hv
    -- the head argument `v` is nonzero
    have hvne : toPoly cv.2 ≠ 0 := hv cv List.mem_cons_self
    -- one fold step: new accumulator
    set newnum := cadd (cmul snum cv.2) (cmul (cscale cv.1 (CPolyEngine.monomialDeriv Dt cv.2)) sden)
      with hnewnum
    set newden := cmul sden cv.2 with hnewden
    have hnewden_ne : toPoly newden ≠ 0 := by
      rw [hnewden]
      simp only [denote]
      exact mul_ne_zero hsden hvne
    -- the IH applied to the rest with the new seed
    have hrest : ∀ cv' ∈ rest, toPoly cv'.2 ≠ 0 := fun cv' hcv' => hv cv' (List.mem_cons_of_mem _ hcv')
    obtain ⟨hden, heq⟩ := ih newnum newden hnewden_ne hrest
    refine ⟨?_, ?_⟩
    · -- the running denominator after the head step is `(newnum, newden)`
      simp only [List.foldl_cons]
      exact hden
    simp only [List.foldl_cons]
    rw [heq, logResidueSumG_cons]
    -- the field algebra: `snum/sden + C(c)·(Δv)/v = newnum/newden`
    have hAsden : am α (toPoly sden) ≠ 0 := am_ne_zero hsden
    have hAv : am α (toPoly cv.2) ≠ 0 := am_ne_zero hvne
    have hstep : am α (toPoly newnum) / am α (toPoly newden)
        = am α (toPoly snum) / am α (toPoly sden)
          + am α (Polynomial.C (CFieldSpec.toK cv.1))
              * (am α (toPoly (CPolyEngine.monomialDeriv Dt cv.2)) / am α (toPoly cv.2)) := by
      rw [hnewnum, hnewden]
      simp only [denote, map_add, map_mul]
      field_simp
    rw [hstep]; ring

/-! ### The `checkIdentity` ⟹ field-identity bridge -/

/-- `checkIdentity = true ⟹ field identity`: a passed check gives
`towerFractionFieldDeriv Dt (am gnum / am gden) + logResidueSum Dt res.logs = am anum / am aden`
over `RatFunc (CFieldSpec.K α)` — the engine's `D(∫f) = f` in field form. -/
theorem field_identity_of_checkIdentityG (Dt : DensePoly α) (res : IntegralResult α)
    (anum aden : DensePoly α)
    (hgden : toPoly res.rational.2 ≠ 0) (haden : toPoly aden ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPoly cv.2 ≠ 0)
    (hcheck : CPoly.checkIdentity Dt res anum aden = true) :
    towerFractionFieldDeriv Dt (am α (toPoly res.rational.1) / am α (toPoly res.rational.2))
        + logResidueSum Dt res.logs
      = am α (toPoly anum) / am α (toPoly aden) := by
  -- names matching `checkIdentity`
  set gnum := res.rational.1 with hgnum
  set gden := res.rational.2 with hgdenE
  set gprimeNum := csub (cmul (CPolyEngine.monomialDeriv Dt gnum) gden) (cmul gnum (CPolyEngine.monomialDeriv Dt gden))
    with hgp
  set gden2 := cmul gden gden with hgden2
  -- the fold result `(Lnum, Lden)`
  set folded := res.logs.foldl
    (fun (acc : DensePoly α × DensePoly α) (cv : α × DensePoly α) =>
      let c := cv.1
      let v := cv.2
      let Dv := CPolyEngine.monomialDeriv Dt v
      let termNum := cscale c Dv
      (cadd (cmul acc.1 v) (cmul termNum acc.2), cmul acc.2 v))
    ([CCommRing.zero], [CCommRing.one]) with hfolded
  -- the fold computes `logResidueSum` over the field, with nonzero `Lden`
  have hseedden : toPoly ([CCommRing.one] : DensePoly α) ≠ 0 := by
    simp only [denote, mul_zero, add_zero]
    exact one_ne_zero
  obtain ⟨hLden_ne, hLfield⟩ := checkIdentityG_fold_eq Dt res.logs [CCommRing.zero] [CCommRing.one]
    hseedden hlogs
  rw [← hfolded] at hLden_ne hLfield
  -- the seed fraction `0/1 = 0`
  have hseed0 : am α (toPoly ([CCommRing.zero] : DensePoly α))
      / am α (toPoly ([CCommRing.one] : DensePoly α)) = 0 := by
    simp only [denote, map_zero, mul_zero, add_zero, zero_div]
  rw [hseed0, zero_add] at hLfield
  -- abbreviations over the field
  set GP := am α (toPoly gprimeNum) with hGP
  set LN := am α (toPoly folded.1) with hLN
  set LD := am α (toPoly folded.2) with hLD
  set AN := am α (toPoly anum) with hAN
  set AD := am α (toPoly aden) with hAD
  set GD := am α (toPoly gden) with hGD
  -- nonzero readings
  have hGDne : GD ≠ 0 := by rw [hGD]; exact am_ne_zero hgden
  have hLDne : LD ≠ 0 := by rw [hLD]; exact am_ne_zero hLden_ne
  have hADne : AD ≠ 0 := by rw [hAD]; exact am_ne_zero haden
  -- `D(gnum/gden) = GP/GD²` (quotient rule); `logResidueSum = LN/LD` (fold bridge)
  have hquot : towerFractionFieldDeriv Dt (am α (toPoly gnum) / am α (toPoly gden))
      = GP / GD ^ 2 := by
    rw [towerFractionFieldDerivG_div, hGP, hgp]
    simp only [denote, map_sub, map_mul]
    rw [hGD]
  have hLfield' : logResidueSum Dt res.logs = LN / LD := by rw [← hLfield, hLN, hLD]
  -- ── the converse direction: extract the cleared polynomial identity from `checkIdentity = true` ──
  rw [CPoly.checkIdentity] at hcheck
  simp only [CPolyEngine.sub_dense_eq, CPolyEngine.mul_dense_eq, CPolyEngine.add_dense_eq,
    CPolyEngine.scale_dense_eq, CPolyEngine.ofCoeffList_dense_eq,
    CPolyEngine.cisZero_dense_eq] at hcheck
  simp only [← hgnum, ← hgdenE, ← hgp, ← hgden2, ← hfolded] at hcheck
  rw [cisZeroG_iff] at hcheck
  simp only [denote, sub_eq_zero] at hcheck
  -- lift the cleared polynomial equation into the tower fraction field (am injective)
  rw [← (RatFunc.algebraMap_injective (CFieldSpec.K α)).eq_iff] at hcheck
  simp only [map_mul, map_add, hgden2, denote] at hcheck
  -- now `hcheck` is the cleared field equation `(GP·LD + LN·GD²)·AD = AN·(GD²·LD)` (over the field)
  rw [← hGP, ← hLN, ← hLD, ← hAN, ← hAD, ← hGD] at hcheck
  -- divide through the nonzero `GD²·LD·AD` to land the field fraction identity `GP/GD² + LN/LD = AN/AD`
  have hfield : GP / GD ^ 2 + LN / LD = AN / AD := by
    rw [div_add_div _ _ (pow_ne_zero 2 hGDne) hLDne,
      div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hGDne) hLDne) hADne]
    ring_nf
    ring_nf at hcheck
    linear_combination hcheck
  -- assemble: rewrite the field readings back into the goal
  rw [hquot, hLfield', hfield]

end DeepWiki.SymbolicIntegration
