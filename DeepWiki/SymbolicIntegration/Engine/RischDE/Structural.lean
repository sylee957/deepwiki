import DeepWiki.SymbolicIntegration.Engine.RischFieldSpec
import DeepWiki.SymbolicIntegration.Engine.OneShotSoundness

/-! # RDE structural decomposition

A successful `cRischDE … = some (ynum, yden)` structurally forces each intermediate stage to have
returned `some`. This file derives the dispatcher → non-cancellation bridge and isolates the residual
regularity conditions the algorithm does not self-certify (`RischDEStructuralResidualWf`). -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

variable {α : Type*} [CField α] [CDiffField α]

/-! ### The dispatcher → non-cancellation bridge

In the primitive regime (`cdeg Dt = 0`) with positive `deg(bbar)`, the dispatcher `cPolyRischDE`
routes to the non-cancellation solve `cPolyRischDENoCancel`. -/

/-- In the primitive regime (`cdeg Dt = 0`) with positive `deg(bbar)`, `cPolyRischDE` reduces to
`cPolyRischDENoCancel`. -/
theorem cPolyRischDEG_eq_noCancel_of_primitive [CRischField α] (Dt : DensePoly α)
    (bbar cbar : DensePoly α) (m : ℤ) (hδ : cdeg Dt = 0) (hdb : 0 < cdeg bbar) :
    cPolyRischDE Dt bbar cbar m = cPolyRischDENoCancel Dt bbar cbar m := by
  rw [cPolyRischDE]
  have hlen : 0 < (cnorm bbar : List α).length := by
    have := hdb; rw [cdeg] at this; omega
  have hbne : cisZero bbar = false := by
    rw [cisZero, List.isEmpty_eq_false_iff_exists_mem]
    exact List.exists_mem_of_length_pos hlen
  simp only [hbne, Bool.false_eq_true, if_false, hδ, Nat.cast_zero, zero_sub]
  rw [if_pos]
  rw [show (max (0 : ℤ) (-1)) = 0 by norm_num]
  exact_mod_cast hdb

/-- From a bare `cRischDE` success in the primitive regime, the normal-denominator, SPDE, and
non-cancellation stage results all hold. -/
theorem cRischDEG_some_imp_noCancel_of_primitive [CFracGcdCoreWf α] [CRischField α] (Dt : DensePoly α)
    (fnum fden gnum gden ynum yden : DensePoly α) (hδ : cdeg Dt = 0)
    (hsucc : cRischDE Dt fnum fden gnum gden = some (ynum, yden)) :
    ∃ (a0 b0 c0 h0 bbar cbar : DensePoly α) (m : ℤ) (α' β v : DensePoly α),
      cRdeNormalDenominator Dt fnum fden gnum gden = some (a0, b0, c0, h0)
      ∧ cSPDE Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.1 (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1
          (cRdeBoundDegree Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
            (cRdeSpecialDenominator Dt a0 b0 c0).2.1
            (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α', β)
      ∧ (0 < cdeg bbar → cPolyRischDENoCancel Dt bbar cbar m = some v)
      ∧ ynum = cmul (cadd (cmul α' v) β) (cRdeSpecialDenominator Dt a0 b0 c0).2.2.2
      ∧ yden = h0 := by
  obtain ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, hdisp, hynum, hyden⟩ :=
    cRischDEG_some_imp_stages Dt fnum fden gnum gden ynum yden hsucc
  refine ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, ?_, hynum, hyden⟩
  intro hdb
  rw [← cPolyRischDEG_eq_noCancel_of_primitive Dt bbar cbar m hδ hdb]
  exact hdisp


/-! ## Cleared-identity ports -/

section WfCleared

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-- A `cPolyRischDENoCancel` success `= some q` yields the identity `D(q) + b·q = c` over
`(CFieldSpec.K α)[X]`. -/
theorem cPolyRischDENoCancelG_cleared_identity (Dt b c : DensePoly α) (n : ℤ) (q : DensePoly α)
    (hsolve : cPolyRischDENoCancel Dt b c n = some q) :
    Differential.implicitDeriv (toPoly Dt) (toPoly q) + toPoly b * toPoly q = toPoly c := by
  fun_induction cPolyRischDENoCancel Dt b c n generalizing q with
  | case1 c _n hc =>
    rw [Option.some.injEq] at hsolve
    subst q
    rw [(cisZeroG_iff c).mp hc, toPolyG_nil, map_zero, mul_zero, add_zero]
  | case2 => exact absurd hsolve (by simp)
  | case3 => exact absurd hsolve (by simp)
  | case4 _c _n _hc _hguard _m _coeff p c' _hlen q' hrec ih =>
    rw [Option.some.injEq] at hsolve
    subst q
    have hih := ih q' hrec
    simp only [c', p, denote, map_add] at hih ⊢
    linear_combination hih
  | case5 => exact absurd hsolve (by simp)

end WfCleared

section WfSPDECleared

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]

/-- `cSPDEGClearedGenWf`: the per-level certificate for `cSPDE`, with `g = cgcdFFCoreWf a b` and
divided coefficients via `CPolyEuclidean.div`. -/
def cSPDEGClearedGenWf (Dt a b c : DensePoly α) (n : ℤ) : Prop :=
  if n < 0 then True
  else
    let g := CPolyGcd.compute a b
    if CPolyEuclidean.dvd g c then
      let ad := CPolyEuclidean.div a g
      let bd := CPolyEuclidean.div b g
      let cd := CPolyEuclidean.div c g
      (toPoly ad * toPoly g = toPoly a) ∧ (toPoly bd * toPoly g = toPoly b)
        ∧ (toPoly cd * toPoly g = toPoly c)
        ∧ (toPoly ad ≠ 0)
        ∧ (if cdeg ad = 0 then True
           else
             let rz := CPoly.diophantineReduced bd ad cd
             (toPoly bd * toPoly rz.1 + toPoly ad * toPoly rz.2 = toPoly cd)
               ∧ (if (n - (cdeg ad : ℤ) + 1).toNat < (n + 1).toNat then
                    cSPDEGClearedGenWf Dt ad (cadd bd (CPolyEngine.monomialDeriv Dt ad))
                      (csub rz.2 (CPolyEngine.monomialDeriv Dt rz.1)) (n - (cdeg ad : ℤ))
                  else True))
    else True
termination_by (n + 1).toNat
decreasing_by assumption

/-- Under `cSPDEGClearedGenWf`, if `cSPDE … = some (b̄, c̄, m, α, β)` then for every `h` solving
`D(h) + b̄·h = c̄`, the reconstruction `q = α·h + β` solves `a·D(q) + b·q = c`. -/
theorem cSPDEG_cleared_lifting_gen (Dt a b c : DensePoly α) (n : ℤ) (bbar cbar : DensePoly α) (m : ℤ)
    (α' β : DensePoly α)
    (hspde : cSPDE Dt a b c n = some (bbar, cbar, m, α', β))
    (hcert : cSPDEGClearedGenWf Dt a b c n) :
    ∀ h : DensePoly α,
      Differential.implicitDeriv (toPoly Dt) (toPoly h) + toPoly bbar * toPoly h = toPoly cbar →
      toPoly a * Differential.implicitDeriv (toPoly Dt) (toPoly (cadd (cmul α' h) β))
          + toPoly b * toPoly (cadd (cmul α' h) β)
        = toPoly c := by
  fun_induction cSPDE Dt a b c n generalizing bbar cbar m α' β with
  | case1 a b c n hn hc =>
    intro h hh
    rw [Option.some.injEq] at hspde
    simp only [Prod.mk.injEq] at hspde
    obtain ⟨hbbar, hcbar, hm, hα, hβ⟩ := hspde
    subst hα; subst hβ
    have hcc : toPoly c = 0 := (cisZeroG_iff c).mp hc
    simp only [denote, toPolyG_nil, zero_mul, add_zero, map_zero, mul_zero, hcc]
  | case2 => exact absurd hspde (by simp)
  | case3 a b c n hn g hdvd a' b' c' hdeg ainv =>
    intro h hh
    rw [Option.some.injEq] at hspde
    simp only [Prod.mk.injEq] at hspde
    obtain ⟨hbbar, hcbar, hm, hα, hβ⟩ := hspde
    subst hα; subst hβ
    simp only [denote, toPolyG_nil, add_zero]
    simp only [map_one, mul_zero, add_zero, one_mul]
    have hdvd' : CPolyEuclidean.dvd (CPolyGcd.compute a b) c = true := hdvd
    rw [cSPDEGClearedGenWf] at hcert
    simp only [hn, hdvd'] at hcert
    obtain ⟨hdiva, hdivb, hdivc, hadne, _⟩ := hcert
    set a0 : CFieldSpec.K α := CFieldSpec.toK (clead a') with ha0def
    have ha0ne : a0 ≠ 0 := by
      rw [ha0def, toK_cleadG_eq_leadingCoeff]
      exact Polynomial.leadingCoeff_ne_zero.mpr hadne
    have hadC : toPoly a' = Polynomial.C a0 := by
      have hnd : (toPoly a').natDegree = 0 := by rw [← cdegG_eq_natDegree, hdeg]
      rw [ha0def, toK_cleadG_eq_leadingCoeff, Polynomial.leadingCoeff, hnd]
      conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hnd]
    rw [← hbbar, ← hcbar] at hh
    simp only [denote] at hh
    rw [CFieldSpec.toK_inv, ← ha0def] at hh
    have hdivided : toPoly a' * Differential.implicitDeriv (toPoly Dt) (toPoly h)
        + toPoly b' * toPoly h = toPoly c' := by
      rw [hadC]
      exact spde_const_base (Differential.implicitDeriv (toPoly Dt)) a0 (toPoly b') (toPoly c')
        (toPoly h) ha0ne hh
    rw [← hdiva, ← hdivb, ← hdivc]
    linear_combination toPoly (CPolyGcd.compute a b) * hdivided
  | case4 a b c n hn g hdvd a' b' c' hdeg => exact absurd hspde (by simp)
  | case5 a b c n hn g hdvd a' b' c' hdeg r z hdioph Da Dr hguard bbar' cbar' m' α'' β'' hrec ih =>
    intro h hh
    rw [Option.some.injEq] at hspde
    simp only [Prod.mk.injEq] at hspde
    obtain ⟨hbbar, hcbar, hm, hα, hβ⟩ := hspde
    rw [← hbbar] at hh; rw [← hcbar] at hh
    have hdvd' : CPolyEuclidean.dvd (CPolyGcd.compute a b) c = true := hdvd
    have hguard' : (n - ((CPolyEuclidean.div a (CPolyGcd.compute a b)).cdeg : ℤ) + 1).toNat
        < (n + 1).toNat := hguard
    rw [cSPDEGClearedGenWf] at hcert
    simp only [hn, hdvd'] at hcert
    obtain ⟨hdiva, hdivb, hdivc, _hadne, hcertrest⟩ := hcert
    rw [if_neg hdeg] at hcertrest
    obtain ⟨hbez'0, hcertrecOpt⟩ := hcertrest
    rw [if_pos hguard'] at hcertrecOpt
    have hdioph' : CPoly.diophantineReduced
        (CPolyEuclidean.div b (CPolyGcd.compute a b))
        (CPolyEuclidean.div a (CPolyGcd.compute a b)) (CPolyEuclidean.div c (CPolyGcd.compute a b))
        = (r, z) := hdioph
    rw [hdioph'] at hbez'0 hcertrecOpt
    have hbez' : toPoly b' * toPoly r + toPoly a' * toPoly z = toPoly c' := hbez'0
    have hcertrecOpt' : cSPDEGClearedGenWf Dt a' (cadd b' Da) (csub z Dr) (n - (cdeg a' : ℤ)) :=
      hcertrecOpt
    have hihrec := ih bbar' cbar' m' α'' β'' hrec hcertrecOpt' h hh
    have hred : toPoly a' * Differential.implicitDeriv (toPoly Dt) (toPoly (cadd (cmul α'' h) β''))
          + (toPoly b' + Differential.implicitDeriv (toPoly Dt) (toPoly a'))
              * toPoly (cadd (cmul α'' h) β'')
        = toPoly z - Differential.implicitDeriv (toPoly Dt) (toPoly r) := by
      simp only [Da, Dr, denote] at hihrec ⊢
      linear_combination hihrec
    subst hα; subst hβ
    have hpeel := cSPDE_peel_cleared_gen Dt a' b' c' r z (cadd (cmul α'' h) β'') hbez' hred
    have hqeq : toPoly (cadd (cmul (cmul a' α'') h) (cadd (cmul a' β'') r))
        = toPoly (cadd (cmul a' (cadd (cmul α'' h) β'')) r) := by
      simp only [denote]; ring
    rw [hqeq, ← hdiva, ← hdivb, ← hdivc]
    linear_combination toPoly (CPolyGcd.compute a b) * hpeel
  | case6 => exact absurd hspde (by simp)
  | case7 a b c n hn g hdvd => exact absurd hspde (by simp)

/-- `CSPDEGClearedInputsGenWf`: the transparent per-level input predicate for `cSPDE`'s
cleared-certificate discharge. -/
def CSPDEGClearedInputsGenWf (Dt a b c : DensePoly α) (n : ℤ) : Prop :=
  if n < 0 then True
  else
    let g := CPolyGcd.compute a b
    if CPolyEuclidean.dvd g c then
      let ad := CPolyEuclidean.div a g
      (cnorm g ≠ []) ∧ Associated (toPoly g) (gcd (toPoly a) (toPoly b))
        ∧ (cnorm a ≠ [])
        ∧ (if cdeg ad = 0 then True
           else
             let bd := CPolyEuclidean.div b g
             let rz := CPoly.diophantineReduced bd ad (CPolyEuclidean.div c g)
             (if (n - (cdeg ad : ℤ) + 1).toNat < (n + 1).toNat then
                CSPDEGClearedInputsGenWf Dt ad (cadd bd (CPolyEngine.monomialDeriv Dt ad))
                  (csub rz.2 (CPolyEngine.monomialDeriv Dt rz.1)) (n - (cdeg ad : ℤ))
              else True))
    else True
termination_by (n + 1).toNat
decreasing_by assumption

omit [CDiffFieldSpec α] in
/-- `CSPDEGClearedInputsGenWf Dt a b c n` implies the per-level certificate `cSPDEGClearedGenWf Dt a b c n`. -/
theorem cSPDEGClearedGenWf_of_inputs (Dt a b c : DensePoly α) (n : ℤ) (hin : CSPDEGClearedInputsGenWf Dt a b c n) :
    cSPDEGClearedGenWf Dt a b c n := by
  fun_induction CSPDEGClearedInputsGenWf Dt a b c n with
  | case1 a b c n hn =>
    rw [cSPDEGClearedGenWf]
    rw [if_pos hn]
    trivial
  | case2 a b c n hn g hdvd ad ih1 =>
    have hdvd' : CPolyEuclidean.dvd (CPolyGcd.compute a b) c = true := hdvd
    have hgdef : g = CPolyGcd.compute a b := rfl
    have hadef : ad = CPolyEuclidean.div a g := rfl
    rw [cSPDEGClearedGenWf]
    simp only [hn, hdvd'] at hin ⊢
    obtain ⟨hg0, hgassoc, ha0, hrest⟩ := hin
    set bd := CPolyEuclidean.div b g with hbd
    have hdiva : toPoly ad * toPoly g = toPoly a := div_a_exact_of_gcd a b g hg0 hgassoc
    have hdivb : toPoly bd * toPoly g = toPoly b := div_b_exact_of_gcd a b g hg0 hgassoc
    have hdivc : toPoly (CPolyEuclidean.div c g) * toPoly g = toPoly c :=
      div_c_exact_of_dvd_eq_true c g hg0 hdvd'
    have hane : toPoly a ≠ 0 := fun h => ha0 ((cnormG_eq_nil_iff a).mpr h)
    have hadne : toPoly ad ≠ 0 := by
      intro h; apply hane; rw [← hdiva, h, zero_mul]
    have hgne : toPoly g ≠ 0 := fun h => hg0 ((cnormG_eq_nil_iff g).mpr h)
    refine ⟨hdiva, hdivb, hdivc, hadne, ?_⟩
    by_cases hdeg : cdeg ad = 0
    · rw [if_pos hdeg] at hrest ⊢; trivial
    · rw [if_neg hdeg] at hrest ⊢
      have hadnil : cnorm ad ≠ [] := fun h => hadne ((cnormG_eq_nil_iff ad).mp h)
      have hunitWf := gcdExt_isUnit_of_divided a b ad bd g hgne hgassoc hdiva hdivb
      have hgdegWf : (toPoly (CPolyEuclidean.gcdExt bd ad).1).natDegree = 0 :=
        Polynomial.natDegree_eq_zero_of_isUnit hunitWf
      have hgneWf : toPoly (CPolyEuclidean.gcdExt bd ad).1 ≠ 0 := hunitWf.ne_zero
      have hbez := toPolyG_diophantineReduced bd ad (CPolyEuclidean.div c g) hadnil hgdegWf hgneWf
      by_cases hguard : (n - (cdeg ad : ℤ) + 1).toNat < (n + 1).toNat
      · rw [if_pos hguard] at hrest ⊢
        refine ⟨?_, ih1 hguard hrest⟩
        simpa [hadef, hgdef, mul_comm] using hbez
      · rw [if_neg hguard] at hrest ⊢
        exact ⟨by simpa [hadef, hgdef, mul_comm] using hbez, trivial⟩
  | case3 a b c n hn g hdvd =>
    have hdvd' : ¬ CPolyEuclidean.dvd (CPolyGcd.compute a b) c = true := hdvd
    rw [cSPDEGClearedGenWf]
    simp only [hn, if_neg hdvd']
    trivial

end WfSPDECleared

section WfNormalDenominator

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]

/-- Writing `dₙ = (CPoly.splitFactor Dt fden).1`, if `cRdeNormalDenominator … = some (a, b, c, h)`,
the clearings are exact, and `Q` solves `a·D(Q) + b·Q = c`, then `Q` solves the cleared
`gden·fden·(D(Q)·h − Q·D(h)) + gden·fnum·Q·h = gnum·fden·h²`. -/
theorem cRdeNormalDenominatorG_cleared_lift (Dt : DensePoly α) (fnum fden gnum gden a b c h Q : DensePoly α)
    (hres : cRdeNormalDenominator Dt fnum fden gnum gden = some (a, b, c, h))
    (hdn : toPoly (CPoly.splitFactor Dt fden).1 ≠ 0)
    (hfden0 : cnorm fden ≠ []) (hgden0 : cnorm gden ≠ [])
    (hdvdB : toPoly fden ∣ toPoly (csub (cmul (cmul (CPoly.splitFactor Dt fden).1 h) fnum)
        (cmul (cmul (CPoly.splitFactor Dt fden).1 (CPolyEngine.monomialDeriv Dt h)) fden)))
    (hdvdC : toPoly gden ∣ toPoly (cmul (cmul (cmul (CPoly.splitFactor Dt fden).1 h) h) gnum))
    (hred : toPoly a * Differential.implicitDeriv (toPoly Dt) (toPoly Q) + toPoly b * toPoly Q
      = toPoly c) :
    toPoly gden * toPoly fden
        * (Differential.implicitDeriv (toPoly Dt) (toPoly Q) * toPoly h
            - toPoly Q * Differential.implicitDeriv (toPoly Dt) (toPoly h))
        + toPoly gden * toPoly fnum * toPoly Q * toPoly h
      = toPoly gnum * toPoly fden * toPoly h ^ 2 := by
  set dn := (CPoly.splitFactor Dt fden).1 with hdndef
  set bNum := csub (cmul (cmul dn h) fnum) (cmul (cmul dn (CPolyEngine.monomialDeriv Dt h)) fden) with hbNum
  set cNum := cmul (cmul (cmul dn h) h) gnum with hcNum
  rw [cRdeNormalDenominator] at hres
  split at hres
  · rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hres
    obtain ⟨ha, hb, hc, hh⟩ := hres
    rw [hh] at ha hb hc
    have hA : toPoly a = toPoly dn * toPoly h := by
      rw [← ha, ← hdndef]
      simp only [denote]
    have hBexact : toPoly b * toPoly fden = toPoly bNum := by
      rw [← hb]; exact DensePoly.toPolyG_div_exact bNum fden hfden0 hdvdB
    have hBeq : toPoly bNum = toPoly a * toPoly fnum
        - toPoly dn * Differential.implicitDeriv (toPoly Dt) (toPoly h) * toPoly fden := by
      simp only [hbNum, denote]
      rw [← hA]
    have hCexact : toPoly c * toPoly gden = toPoly cNum := by
      rw [← hc]; exact DensePoly.toPolyG_div_exact cNum gden hgden0 hdvdC
    have hCeq : toPoly cNum = toPoly dn * toPoly h ^ 2 * toPoly gnum := by
      simp only [hcNum, denote]; ring
    have hBcert : toPoly b * toPoly fden = toPoly a * toPoly fnum
        - toPoly dn * Differential.implicitDeriv (toPoly Dt) (toPoly h) * toPoly fden := by
      rw [hBexact]; exact hBeq
    have hCcert : toPoly c * toPoly gden = toPoly dn * toPoly h ^ 2 * toPoly gnum := by
      rw [hCexact]; exact hCeq
    have hglue := rdeNormalDenominator_glue (Differential.implicitDeriv (toPoly Dt))
      (toPoly dn) (toPoly h) (toPoly fnum) (toPoly fden) (toPoly gnum) (toPoly gden)
      (toPoly a) (toPoly b) (toPoly c) (toPoly Q) hdn hA hBcert hCcert hred
    linear_combination hglue
  · exact absurd hres (by simp)

end WfNormalDenominator

section WfCapstone

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]

/-- Lift under the transparent input predicate directly, composing `cSPDEG_cleared_lifting_gen` with
`cSPDEGClearedGenWf_of_inputs`. -/
theorem cSPDEG_cleared_lifting_of_inputs (Dt : DensePoly α) (a b c : DensePoly α) (n : ℤ)
    (bbar cbar : DensePoly α) (m : ℤ) (α' β : DensePoly α)
    (hspde : cSPDE Dt a b c n = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGenWf Dt a b c n) (h : DensePoly α)
    (hh : Differential.implicitDeriv (toPoly Dt) (toPoly h) + toPoly bbar * toPoly h
      = toPoly cbar) :
    toPoly a * Differential.implicitDeriv (toPoly Dt) (toPoly (cadd (cmul α' h) β))
        + toPoly b * toPoly (cadd (cmul α' h) β)
      = toPoly c :=
  cSPDEG_cleared_lifting_gen Dt a b c n bbar cbar m α' β hspde
    (cSPDEGClearedGenWf_of_inputs Dt a b c n hin) h hh

/-- Feed the non-cancellation success through `cPolyRischDENoCancelG_cleared_identity` into the SPDE lifting. -/
theorem cSPDEG_polyRischDENoCancel_cleared_of_inputs (Dt : DensePoly α) (a b c : DensePoly α) (n : ℤ)
    (bbar cbar : DensePoly α) (m : ℤ) (α' β v : DensePoly α)
    (hspde : cSPDE Dt a b c n = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGenWf Dt a b c n)
    (hpoly : cPolyRischDENoCancel Dt bbar cbar m = some v) :
    toPoly a * Differential.implicitDeriv (toPoly Dt) (toPoly (cadd (cmul α' v) β))
        + toPoly b * toPoly (cadd (cmul α' v) β)
      = toPoly c :=
  cSPDEG_cleared_lifting_of_inputs Dt a b c n bbar cbar m α' β hspde hin v
    (cPolyRischDENoCancelG_cleared_identity Dt bbar cbar m v hpoly)

/-- The spine instantiated at the degree bound `n = cRdeBoundDegree Dt a b c`. -/
theorem cSPDEG_polyRischDENoCancel_cleared_at_boundDegree (Dt : DensePoly α) (a b c : DensePoly α)
    (bbar cbar : DensePoly α) (m : ℤ) (α' β v : DensePoly α)
    (hspde : cSPDE Dt a b c (cRdeBoundDegree Dt a b c : ℤ) = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGenWf Dt a b c (cRdeBoundDegree Dt a b c : ℤ))
    (hpoly : cPolyRischDENoCancel Dt bbar cbar m = some v) :
    toPoly a * Differential.implicitDeriv (toPoly Dt) (toPoly (cadd (cmul α' v) β))
        + toPoly b * toPoly (cadd (cmul α' v) β)
      = toPoly c :=
  cSPDEG_polyRischDENoCancel_cleared_of_inputs Dt a b c
    (cRdeBoundDegree Dt a b c : ℤ) bbar cbar m α' β v hspde hin hpoly

/-- In the primitive regime, from the normal-denominator output, its divisibility certificates, the
SPDE output under `CSPDEGClearedInputsGenWf`, and the poly-RDE identity `D(v) + bbar·v = cbar`, the
reconstruction `ynum = (α'·v + β)·[1]`, `yden = h0` satisfies the cleared Risch-DE identity. -/
theorem rdeClearedIdentityWf_of_polyRDEIdentity (Dt : DensePoly α)
    (fnum fden gnum gden a0 b0 c0 h0 : DensePoly α)
    (bbar cbar : DensePoly α) (m : ℤ) (α' β v : DensePoly α)
    (hprim : cdeg (cSpecialPoly Dt) = 0)
    (hnorm : cRdeNormalDenominator Dt fnum fden gnum gden = some (a0, b0, c0, h0))
    (hdn : toPoly (CPoly.splitFactor Dt fden).1 ≠ 0)
    (hfden0 : cnorm fden ≠ []) (hgden0 : cnorm gden ≠ [])
    (hdvdB : toPoly fden ∣ toPoly (csub (cmul (cmul (CPoly.splitFactor Dt fden).1 h0) fnum)
        (cmul (cmul (CPoly.splitFactor Dt fden).1 (CPolyEngine.monomialDeriv Dt h0)) fden)))
    (hdvdC : toPoly gden ∣ toPoly (cmul (cmul (cmul (CPoly.splitFactor Dt fden).1 h0) h0) gnum))
    (hspde : cSPDE Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
        (cRdeSpecialDenominator Dt a0 b0 c0).2.1 (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1
        (cRdeBoundDegree Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGenWf Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
        (cRdeSpecialDenominator Dt a0 b0 c0).2.1 (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1
        (cRdeBoundDegree Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1 : ℤ))
    (hidentity : Differential.implicitDeriv (toPoly Dt) (toPoly v) + toPoly bbar * toPoly v
      = toPoly cbar) :
    toPoly gden * toPoly fden
        * (Differential.implicitDeriv (toPoly Dt) (toPoly (cmul (cadd (cmul α' v) β) [CCommRing.one]))
              * toPoly h0
            - toPoly (cmul (cadd (cmul α' v) β) [CCommRing.one])
              * Differential.implicitDeriv (toPoly Dt) (toPoly h0))
        + toPoly gden * toPoly fnum * toPoly (cmul (cadd (cmul α' v) β) [CCommRing.one]) * toPoly h0
      = toPoly gnum * toPoly fden * toPoly h0 ^ 2 := by
  set Q := cadd (cmul α' v) β with hQ
  have hspecial := cRdeSpecialDenominatorG_primitive_eq Dt a0 b0 c0 hprim
  rw [hspecial] at hspde hin
  simp only at hspde hin
  have hred : toPoly a0 * Differential.implicitDeriv (toPoly Dt) (toPoly Q) + toPoly b0 * toPoly Q
      = toPoly c0 :=
    cSPDEG_cleared_lifting_of_inputs Dt a0 b0 c0
      (cRdeBoundDegree Dt a0 b0 c0 : ℤ) bbar cbar m α' β hspde hin v hidentity
  have hone : toPoly ([CCommRing.one] : DensePoly α) = 1 := by
    simp only [denote, mul_zero, add_zero, map_one]
  have hynum : toPoly (cmul Q [CCommRing.one]) = toPoly Q := by
    simp only [denote, hone, mul_one]
  have hlift := cRdeNormalDenominatorG_cleared_lift Dt fnum fden gnum gden a0 b0 c0 h0 Q
    hnorm hdn hfden0 hgden0 hdvdB hdvdC hred
  rw [hynum]
  exact hlift

end WfCapstone

section WfResidual

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
  [CRischField α]

/-- `RischDEStructuralResidualWf`: the residual hypotheses of `rdeClearedIdentityWf_of_polyRDEIdentity`
that a bare `cRischDE` success does not self-certify. -/
structure RischDEStructuralResidualWf (Dt : DensePoly α) (fnum fden gnum gden a0 b0 c0 h0 : DensePoly α) :
    Prop where
  /-- Primitive special regime: `cdeg (cSpecialPoly Dt) = 0`. -/
  hprim : cdeg (cSpecialPoly Dt) = 0
  /-- The normal part `dₙ = (CPoly.splitFactor Dt fden).1` is nonzero. -/
  hdn : toPoly (CPoly.splitFactor Dt fden).1 ≠ 0
  /-- The input denominator `fden` is nonzero. -/
  hfden0 : cnorm fden ≠ []
  /-- The input denominator `gden` is nonzero. -/
  hgden0 : cnorm gden ≠ []
  /-- `fden` divides the `B`-numerator (the `CPolyEuclidean.div` clearing is exact). -/
  hdvdB : toPoly fden ∣ toPoly (csub (cmul (cmul (CPoly.splitFactor Dt fden).1 h0) fnum)
      (cmul (cmul (CPoly.splitFactor Dt fden).1 (CPolyEngine.monomialDeriv Dt h0)) fden))
  /-- `gden` divides the `C`-numerator (the `CPolyEuclidean.div` clearing is exact). -/
  hdvdC : toPoly gden ∣ toPoly (cmul (cmul (cmul (CPoly.splitFactor Dt fden).1 h0) h0) gnum)
  /-- The transparent-input chain `CSPDEGClearedInputsGenWf` on the special-cleared coefficients at
  the bound degree. -/
  hin : CSPDEGClearedInputsGenWf Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
      (cRdeSpecialDenominator Dt a0 b0 c0).2.1 (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1
      (cRdeBoundDegree Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
        (cRdeSpecialDenominator Dt a0 b0 c0).2.1
        (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1 : ℤ)

/-- Given a `cRischDE` success, `cdeg Dt = 0`, positive `deg(bbar)`, and the residual
`RischDEStructuralResidualWf`, the returned `y = ynum/yden` satisfies the cleared identity
`gden·fden·(D(ynum)·yden − ynum·D(yden)) + gden·fnum·ynum·yden = gnum·fden·yden²`. -/
theorem rdeClearedWf_of_success_and_residual (Dt : DensePoly α)
    (fnum fden gnum gden ynum yden : DensePoly α) (hδ : cdeg Dt = 0)
    (hsucc : cRischDE Dt fnum fden gnum gden = some (ynum, yden))
    (hres : ∀ a0 b0 c0 h0 : DensePoly α,
      cRdeNormalDenominator Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
      RischDEStructuralResidualWf Dt fnum fden gnum gden a0 b0 c0 h0)
    (hdb : ∀ a0 b0 c0 bbar cbar : DensePoly α, ∀ m : ℤ, ∀ α' β : DensePoly α,
      cSPDE Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1
          (cRdeBoundDegree Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
            (cRdeSpecialDenominator Dt a0 b0 c0).2.1
            (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α', β) → 0 < cdeg bbar) :
    toPoly gden * toPoly fden
        * (Differential.implicitDeriv (toPoly Dt) (toPoly ynum) * toPoly yden
            - toPoly ynum * Differential.implicitDeriv (toPoly Dt) (toPoly yden))
        + toPoly gden * toPoly fnum * toPoly ynum * toPoly yden
      = toPoly gnum * toPoly fden * toPoly yden ^ 2 := by
  obtain ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, hdisp, hynum, hyden⟩ :=
    cRischDEG_some_imp_stages Dt fnum fden gnum gden ynum yden hsucc
  have hres' := hres a0 b0 c0 h0 hnorm
  have hdb' := hdb a0 b0 c0 bbar cbar m α' β hspde
  have hpoly : cPolyRischDENoCancel Dt bbar cbar m = some v := by
    rw [← cPolyRischDEG_eq_noCancel_of_primitive Dt bbar cbar m hδ hdb']; exact hdisp
  have hidentity : Differential.implicitDeriv (toPoly Dt) (toPoly v) + toPoly bbar * toPoly v
      = toPoly cbar := cPolyRischDENoCancelG_cleared_identity Dt bbar cbar m v hpoly
  have hcap := rdeClearedIdentityWf_of_polyRDEIdentity Dt fnum fden gnum gden a0 b0 c0 h0
    bbar cbar m α' β v hres'.hprim hnorm hres'.hdn hres'.hfden0 hres'.hgden0 hres'.hdvdB
    hres'.hdvdC hspde hres'.hin hidentity
  have hh1 : (cRdeSpecialDenominator Dt a0 b0 c0).2.2.2 = ([CCommRing.one] : DensePoly α) := by
    rw [cRdeSpecialDenominatorG_primitive_eq Dt a0 b0 c0 hres'.hprim]
  rw [hh1] at hynum
  rw [hynum, hyden]
  exact hcap

end WfResidual

section WfFieldHeadline

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
  [CRischField α] [Algebra ℚ (CFieldSpec.K α)]

/-- The RDE oracle's field-level soundness in the primitive regime, from bare `cRischDE` success
and the residual: composes `rdeClearedWf_of_success_and_residual` with `rischDE_field_of_cleared`. -/
theorem crischDEWf_field_of_success_and_residual (Dt : DensePoly α)
    (fnum fden gnum gden ynum yden : DensePoly α) (hδ : cdeg Dt = 0)
    (hsucc : cRischDE Dt fnum fden gnum gden = some (ynum, yden))
    (hres : ∀ a0 b0 c0 h0 : DensePoly α,
      cRdeNormalDenominator Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
      RischDEStructuralResidualWf Dt fnum fden gnum gden a0 b0 c0 h0)
    (hdb : ∀ a0 b0 c0 bbar cbar : DensePoly α, ∀ m : ℤ, ∀ α' β : DensePoly α,
      cSPDE Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1
          (cRdeBoundDegree Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
            (cRdeSpecialDenominator Dt a0 b0 c0).2.1
            (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α', β) → 0 < cdeg bbar)
    (hfden : toPoly fden ≠ 0) (hgden : toPoly gden ≠ 0) (hyden : toPoly yden ≠ 0) :
    towerFractionFieldDeriv Dt (am α (toPoly ynum) / am α (toPoly yden))
        + am α (toPoly fnum) / am α (toPoly fden)
          * (am α (toPoly ynum) / am α (toPoly yden))
      = am α (toPoly gnum) / am α (toPoly gden) := by
  have hcleared := rdeClearedWf_of_success_and_residual Dt fnum fden gnum gden ynum yden hδ hsucc hres hdb
  have hclam := congrArg (am α) hcleared
  simp only [map_add, map_mul, map_sub, map_pow] at hclam
  exact rischDE_field_of_cleared Dt fnum fden gnum gden ynum yden hfden hgden hyden hclam

end WfFieldHeadline

end DeepWiki.SymbolicIntegration
