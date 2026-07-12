import DeepWiki.SymbolicIntegration.Engine.PrimPRSRegular.Assembly

/-! # Primitive PRS regularity: total termination

The degree-fuelled pseudo-remainder and content preservation turn the structural drop into a total
regularity witness for every primitive PRS input. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open DensePoly GBPolyCore

variable {β : Type*} [CField β] [CFieldSpec β]

/-- Every degree-fuelled primitive PRS has a finite regular run when its content gcd is correct. -/
theorem cPrimPRSGenRegular_exists (cgcdB : DensePoly β → DensePoly β → DensePoly β)
    (hcorr : CgcdBCorrect cgcdB) (P Q : GBPolyCore β) :
    ∃ fuel, CPrimPRSGenRegular cgcdB fuel P Q := by
  induction hlen : (gbnormCore Q).length using Nat.strong_induction_on generalizing P Q with
  | h n ih =>
    by_cases hQ : DensePoly.cisZero (gbnormCore Q) = true
    · exact ⟨0, CPrimPRSGenRegular.stop hQ⟩
    · let Pn := gbnormCore P
      let Qn := gbnormCore Q
      let prem := gbpsremainderCore Pn.length Pn Qn
      let r := gbprimitivePartCore cgcdB prem
      have hQf : DensePoly.cisZero (gbnormCore Q) = false := by
        simpa only [Bool.eq_false_iff] using hQ
      have hqpos : 0 < Qn.length := by
        simpa only [Qn] using gbnormCore_length_pos hQf
      have hguard : (gbnormCore r).length < Qn.length := by
        by_cases hr : DensePoly.cisZero r = true
        · have hrnil : gbnormCore r = [] :=
            (gbnormCore_eq_nil_iff_toPolyG r).mpr ((DensePoly.cisZeroG_iff r).mp hr)
          rw [hrnil]
          exact hqpos
        · have hr' : DensePoly.cisZero r = false := by simpa using hr
          have hrne : ¬ DensePoly.cisZero r = true := by
            simpa only [Bool.eq_false_iff] using hr'
          have hP : DensePoly.cisZero Pn = false := by
            apply Bool.eq_false_iff.mpr
            intro hP
            have hPnil : Pn = [] := by
              have hPnil' : gbnormCore Pn = [] :=
                (gbnormCore_eq_nil_iff_toPolyG Pn).mpr ((DensePoly.cisZeroG_iff Pn).mp hP)
              simpa only [Pn, gbnormCore_idemp] using hPnil'
            have hprem0 : DensePoly.toPoly prem = 0 := by
              change DensePoly.toPoly (gbpsremainderCore Pn.length Pn Qn) = 0
              simp [hPnil, gbpsremainderCore]
            have hassoc : Associated (toGBPoly r) (toGBPoly prem) :=
              associated_toGBPolyG_gbprimitivePartCore_total cgcdB hcorr prem
            have hr0 : DensePoly.toPoly r = 0 := by
              have hzero : toGBPoly prem = 0 := (toGBPolyG_eq_zero_iff prem).mpr hprem0
              exact (toGBPolyG_eq_zero_iff r).mp (hassoc.eq_zero_iff.mpr hzero)
            exact hrne ((DensePoly.cisZeroG_iff r).mpr hr0)
          have hP' : DensePoly.cisZero (gbnormCore Pn) = false := by
            rw [cisZero_gbnormCore]
            exact hP
          have hpdeg : (DensePoly.toPoly Pn).natDegree < Pn.length := by
            have hpl : Pn.length = (DensePoly.toPoly Pn).natDegree + 1 := by
              simpa only [Pn, gbnormCore_idemp] using gbnormCore_length_eq_natDegree_succ hP
            omega
          have hpremdeg : (DensePoly.toPoly prem).natDegree < (DensePoly.toPoly Qn).natDegree := by
            rcases gbpsremainderCore_degree_lt Qn (by simpa only [Qn, gbnormCore_idemp] using hQf)
              Pn.length Pn hpdeg with h | h
            · simpa only [prem] using h
            · exact False.elim (hrne (by
                have hassoc : Associated (toGBPoly r) (toGBPoly prem) :=
                  associated_toGBPolyG_gbprimitivePartCore_total cgcdB hcorr prem
                have hzero : toGBPoly prem = 0 := (toGBPolyG_eq_zero_iff prem).mpr h
                apply (DensePoly.cisZeroG_iff r).mpr
                apply (toGBPolyG_eq_zero_iff r).mp
                exact hassoc.eq_zero_iff.mpr hzero))
          exact (gbnormGuard_iff_premDegree cgcdB hcorr P Q (by simpa only [Qn] using hQf) hr').mpr
            (by simpa only [Pn, Qn, prem] using hpremdeg)
      have hguardn : (gbnormCore r).length < n := by
        simpa only [Qn, hlen] using hguard
      obtain ⟨fuel, hrec⟩ := ih (gbnormCore r).length hguardn Qn r rfl
      exact ⟨fuel + 1, CPrimPRSGenRegular.step (by simpa only [Qn] using hQf)
        (by simpa only [Pn, Qn, prem, r] using hguard) (by simpa only [Pn, Qn, prem, r] using hrec)⟩

end DeepWiki.SymbolicIntegration
