import DeepWiki.SymbolicIntegration.Engine.Tower.RischDE
import DeepWiki.SymbolicIntegration.Engine.RischDE.TowerCorrectG

/-! # The `checkIdentity` ⟹ field-identity bridge

`checkIdentity = true` implies the field identity `D(∫f) = f` over the tower fraction field
`RatFunc (CFieldSpec.K α)`, via the residue sum `logResidueSumG` and derivation
`towerFractionFieldDerivG`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open CPoly QFunNZG

/-! ### The generic fraction-field derivation -/

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-- Tower fraction-field derivation `extendDeriv (implicitDeriv (toPoly Dt))` on
`RatFunc (CFieldSpec.K α)`. -/
noncomputable def towerFractionFieldDerivG (Dt : CPoly α) :
    Derivation ℤ (RatFunc (CFieldSpec.K α)) (RatFunc (CFieldSpec.K α)) :=
  extendDeriv (Differential.implicitDeriv (toPoly Dt))

/-- Quotient rule on a fraction of polynomial images: `towerFractionFieldDerivG Dt (amG gnum / amG gden)
= (amG(Δ gnum)·amG(gden) − amG(gnum)·amG(Δ gden)) / (amG gden)²`, `Δ = implicitDeriv (toPoly Dt)`. -/
theorem towerFractionFieldDerivG_div (Dt : CPoly α) (gnum gden : (CFieldSpec.K α)[X]) :
    towerFractionFieldDerivG Dt (amG α gnum / amG α gden)
      = (amG α (Differential.implicitDeriv (toPoly Dt) gnum) * amG α gden
          - amG α gnum * amG α (Differential.implicitDeriv (toPoly Dt) gden))
        / (amG α gden) ^ 2 := by
  rw [towerFractionFieldDerivG, ← RatFunc.mk_eq_div, extendDeriv_mk, RatFunc.mk_eq_div, map_sub,
    map_mul, map_mul, map_pow]

/-- Per-term log-derivative reading:
`towerFractionFieldDerivG Dt (amG v)/amG v = amG (toPoly (cmonomialDeriv Dt v))/amG (toPoly v)`. -/
theorem towerFractionFieldDerivG_logDeriv (Dt v : CPoly α) :
    towerFractionFieldDerivG Dt (amG α (toPoly v)) / amG α (toPoly v)
      = amG α (toPoly (cmonomialDeriv Dt v)) / amG α (toPoly v) := by
  rw [towerFractionFieldDerivG, extendDeriv_algebraMap]
  simp only [denote]

/-! ### The logarithmic-part residue sum -/

/-- Logarithmic-part residue sum `∑_{(c,v)∈logs} amG(C(toK c))·(Δv)/v` over
`RatFunc (CFieldSpec.K α)`, `Δ = implicitDeriv (toPoly Dt)`. -/
noncomputable def logResidueSumG (Dt : CPoly α) (logs : List (α × CPoly α)) :
    RatFunc (CFieldSpec.K α) :=
  (logs.map (fun cv =>
    amG α (Polynomial.C (CFieldSpec.toK cv.1))
      * (amG α (toPoly (cmonomialDeriv Dt cv.2)) / amG α (toPoly cv.2)))).sum

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `logResidueSumG` of the empty list is `0`. -/
@[simp] theorem logResidueSumG_nil (Dt : CPoly α) : logResidueSumG Dt ([] : List (α × CPoly α)) = 0 :=
  rfl

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `logResidueSumG` peels the head: `logResidueSumG Dt ((c,v) :: rest) = amG(C(toK c))·(Δv)/v
+ logResidueSumG Dt rest`. -/
theorem logResidueSumG_cons (Dt : CPoly α) (cv : α × CPoly α) (rest : List (α × CPoly α)) :
    logResidueSumG Dt (cv :: rest)
      = amG α (Polynomial.C (CFieldSpec.toK cv.1))
          * (amG α (toPoly (cmonomialDeriv Dt cv.2)) / amG α (toPoly cv.2))
        + logResidueSumG Dt rest := by
  simp only [logResidueSumG, List.map_cons, List.sum_cons]

/-- `logResidueSumG` reads as the monomial log-derivative sum
`∑_{(c,v)} amG(C(toK c))·(towerFractionFieldDerivG Dt (amG v)/amG v)`. -/
theorem logResidueSumG_eq_logDeriv_sum (Dt : CPoly α) (logs : List (α × CPoly α)) :
    logResidueSumG Dt logs
      = (logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPoly cv.2)) / amG α (toPoly cv.2)))).sum := by
  rw [logResidueSumG]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro cv _
  rw [towerFractionFieldDerivG_logDeriv]

/-! ### The `checkIdentity` fold computes the residue sum -/

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The `checkIdentity` fold computes the residue sum: its running fraction equals the seed fraction
plus `logResidueSumG`, with the running denominator staying nonzero. -/
theorem checkIdentityG_fold_eq (Dt : CPoly α) :
    ∀ (logs : List (α × CPoly α)) (snum sden : CPoly α),
      toPoly sden ≠ 0 →
      (∀ cv ∈ logs, toPoly cv.2 ≠ 0) →
      let res := logs.foldl
        (fun (acc : CPoly α × CPoly α) (cv : α × CPoly α) =>
          let c := cv.1
          let v := cv.2
          let Dv := cmonomialDeriv Dt v
          let termNum := cscale c Dv
          (cadd (cmul acc.1 v) (cmul termNum acc.2), cmul acc.2 v))
        (snum, sden)
      toPoly res.2 ≠ 0 ∧
        amG α (toPoly res.1) / amG α (toPoly res.2)
          = amG α (toPoly snum) / amG α (toPoly sden) + logResidueSumG Dt logs := by
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
    set newnum := cadd (cmul snum cv.2) (cmul (cscale cv.1 (cmonomialDeriv Dt cv.2)) sden)
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
    have hAsden : amG α (toPoly sden) ≠ 0 := amG_toPolyG_ne_zero hsden
    have hAv : amG α (toPoly cv.2) ≠ 0 := amG_toPolyG_ne_zero hvne
    have hstep : amG α (toPoly newnum) / amG α (toPoly newden)
        = amG α (toPoly snum) / amG α (toPoly sden)
          + amG α (Polynomial.C (CFieldSpec.toK cv.1))
              * (amG α (toPoly (cmonomialDeriv Dt cv.2)) / amG α (toPoly cv.2)) := by
      rw [hnewnum, hnewden]
      simp only [denote, map_add, map_mul]
      field_simp
    rw [hstep]; ring

/-! ### The `checkIdentity` ⟹ field-identity bridge -/

/-- `checkIdentity = true ⟹ field identity`: a passed check gives
`towerFractionFieldDerivG Dt (amG gnum / amG gden) + logResidueSumG Dt res.logs = amG anum / amG aden`
over `RatFunc (CFieldSpec.K α)` — the engine's `D(∫f) = f` in field form. -/
theorem field_identity_of_checkIdentityG (Dt : CPoly α) (res : IntegralResultG α)
    (anum aden : CPoly α)
    (hgden : toPoly res.rational.2 ≠ 0) (haden : toPoly aden ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPoly cv.2 ≠ 0)
    (hcheck : CPoly.checkIdentity Dt res anum aden = true) :
    towerFractionFieldDerivG Dt (amG α (toPoly res.rational.1) / amG α (toPoly res.rational.2))
        + logResidueSumG Dt res.logs
      = amG α (toPoly anum) / amG α (toPoly aden) := by
  -- names matching `checkIdentity`
  set gnum := res.rational.1 with hgnum
  set gden := res.rational.2 with hgdenE
  set gprimeNum := csub (cmul (cmonomialDeriv Dt gnum) gden) (cmul gnum (cmonomialDeriv Dt gden))
    with hgp
  set gden2 := cmul gden gden with hgden2
  -- the fold result `(Lnum, Lden)`
  set folded := res.logs.foldl
    (fun (acc : CPoly α × CPoly α) (cv : α × CPoly α) =>
      let c := cv.1
      let v := cv.2
      let Dv := cmonomialDeriv Dt v
      let termNum := cscale c Dv
      (cadd (cmul acc.1 v) (cmul termNum acc.2), cmul acc.2 v))
    ([CField.zero], [CField.one]) with hfolded
  -- the fold computes `logResidueSumG` over the field, with nonzero `Lden`
  have hseedden : toPoly ([CField.one] : CPoly α) ≠ 0 := by
    simp only [denote, mul_zero, add_zero]
    exact one_ne_zero
  obtain ⟨hLden_ne, hLfield⟩ := checkIdentityG_fold_eq Dt res.logs [CField.zero] [CField.one]
    hseedden hlogs
  rw [← hfolded] at hLden_ne hLfield
  -- the seed fraction `0/1 = 0`
  have hseed0 : amG α (toPoly ([CField.zero] : CPoly α))
      / amG α (toPoly ([CField.one] : CPoly α)) = 0 := by
    simp only [denote, map_zero, mul_zero, add_zero, zero_div]
  rw [hseed0, zero_add] at hLfield
  -- abbreviations over the field
  set GP := amG α (toPoly gprimeNum) with hGP
  set LN := amG α (toPoly folded.1) with hLN
  set LD := amG α (toPoly folded.2) with hLD
  set AN := amG α (toPoly anum) with hAN
  set AD := amG α (toPoly aden) with hAD
  set GD := amG α (toPoly gden) with hGD
  -- nonzero readings
  have hGDne : GD ≠ 0 := by rw [hGD]; exact amG_toPolyG_ne_zero hgden
  have hLDne : LD ≠ 0 := by rw [hLD]; exact amG_toPolyG_ne_zero hLden_ne
  have hADne : AD ≠ 0 := by rw [hAD]; exact amG_toPolyG_ne_zero haden
  -- `D(gnum/gden) = GP/GD²` (quotient rule); `logResidueSumG = LN/LD` (fold bridge)
  have hquot : towerFractionFieldDerivG Dt (amG α (toPoly gnum) / amG α (toPoly gden))
      = GP / GD ^ 2 := by
    rw [towerFractionFieldDerivG_div, hGP, hgp]
    simp only [denote, map_sub, map_mul]
    rw [hGD]
  have hLfield' : logResidueSumG Dt res.logs = LN / LD := by rw [← hLfield, hLN, hLD]
  -- ── the converse direction: extract the cleared polynomial identity from `checkIdentity = true` ──
  rw [CPoly.checkIdentity] at hcheck
  simp only [← hgnum, ← hgdenE, ← hgp, ← hgden2, ← hfolded] at hcheck
  rw [cisZeroG_iff] at hcheck
  simp only [denote, sub_eq_zero] at hcheck
  -- lift the cleared polynomial equation into the tower fraction field (amG injective)
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
