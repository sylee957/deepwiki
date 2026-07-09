import DeepWiki.SymbolicIntegration.Engine.RischFieldSpec
import DeepWiki.SymbolicIntegration.Engine.OneShotSoundness

/-! # RDE structural decomposition

A successful `cRischDEG … = some (ynum, yden)` structurally forces each intermediate stage to have
returned `some`. This file derives those stage results (`cRischDEG_some_imp_stages_structural`, the
dispatcher → non-cancellation bridge) and isolates the residual regularity conditions the algorithm
does not self-certify (`RischDEStructuralResidualWf`). -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open CPolyG QFunNZG

variable {α : Type*} [CField α] [CDiffField α]

/-! ### Structural decomposition

This wrapper exposes the `cRischDEG` control-flow reading from the structural layer. -/

/-- `cRischDEG = some _` forces the stage `some`-results. -/
theorem cRischDEG_some_imp_stages_structural [CFracGcdCoreWf α] [CRischField α] (Dt : CPolyG α)
    (fnum fden gnum gden ynum yden : CPolyG α)
    (hsucc : cRischDEG Dt fnum fden gnum gden = some (ynum, yden)) :
    ∃ (a0 b0 c0 h0 bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α),
      cRdeNormalDenominatorG Dt fnum fden gnum gden = some (a0, b0, c0, h0)
      ∧ cSPDEG Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1
          (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α', β)
      ∧ cPolyRischDEG Dt bbar cbar m = some v
      ∧ ynum = cmulG (caddG (cmulG α' v) β) (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.2
      ∧ yden = h0 :=
  cRischDEG_some_imp_stages Dt fnum fden gnum gden ynum yden hsucc

/-! ### The dispatcher → non-cancellation bridge

In the primitive regime (`cdegG Dt = 0`) with positive `deg(bbar)`, the dispatcher `cPolyRischDEG`
routes to the non-cancellation solve `cPolyRischDENoCancelG`. -/

/-- In the primitive regime (`cdegG Dt = 0`) with positive `deg(bbar)`, `cPolyRischDEG` reduces to
`cPolyRischDENoCancelG`. -/
theorem cPolyRischDEG_eq_noCancel_of_primitive [CRischField α] (Dt : CPolyG α)
    (bbar cbar : CPolyG α) (m : ℤ) (hδ : cdegG Dt = 0) (hdb : 0 < cdegG bbar) :
    cPolyRischDEG Dt bbar cbar m = cPolyRischDENoCancelG Dt bbar cbar m := by
  rw [cPolyRischDEG]
  have hlen : 0 < (cnormG bbar : List α).length := by
    have := hdb; rw [cdegG] at this; omega
  have hbne : cisZeroG bbar = false := by
    rw [cisZeroG, List.isEmpty_eq_false_iff_exists_mem]
    exact List.exists_mem_of_length_pos hlen
  simp only [hbne, Bool.false_eq_true, if_false, hδ, Nat.cast_zero, zero_sub]
  rw [if_pos]
  rw [show (max (0 : ℤ) (-1)) = 0 by norm_num]
  exact_mod_cast hdb

/-- From a bare `cRischDEG` success in the primitive regime, the normal-denominator, SPDE, and
non-cancellation stage results all hold. -/
theorem cRischDEG_some_imp_noCancel_of_primitive [CFracGcdCoreWf α] [CRischField α] (Dt : CPolyG α)
    (fnum fden gnum gden ynum yden : CPolyG α) (hδ : cdegG Dt = 0)
    (hsucc : cRischDEG Dt fnum fden gnum gden = some (ynum, yden)) :
    ∃ (a0 b0 c0 h0 bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α),
      cRdeNormalDenominatorG Dt fnum fden gnum gden = some (a0, b0, c0, h0)
      ∧ cSPDEG Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1 (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1
          (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α', β)
      ∧ (0 < cdegG bbar → cPolyRischDENoCancelG Dt bbar cbar m = some v)
      ∧ ynum = cmulG (caddG (cmulG α' v) β) (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.2
      ∧ yden = h0 := by
  obtain ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, hdisp, hynum, hyden⟩ :=
    cRischDEG_some_imp_stages Dt fnum fden gnum gden ynum yden hsucc
  refine ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, ?_, hynum, hyden⟩
  intro hdb
  rw [← cPolyRischDEG_eq_noCancel_of_primitive Dt bbar cbar m hδ hdb]
  exact hdisp


/-! ### Axiom audit -/

#print axioms cRischDEG_some_imp_stages_structural

/-! ## Cleared-identity ports -/

section WfCleared

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-- A `cPolyRischDENoCancelG` success `= some q` yields the identity `D(q) + b·q = c` over
`(CFieldSpec.K α)[X]`. -/
theorem cPolyRischDENoCancelG_cleared_identity (Dt b c : CPolyG α) (n : ℤ) (q : CPolyG α)
    (hsolve : cPolyRischDENoCancelG Dt b c n = some q) :
    Differential.implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG b * toPolyG q = toPolyG c := by
  fun_induction cPolyRischDENoCancelG Dt b c n generalizing q with
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

/-- `cSPDEGClearedGenWf`: the per-level certificate for `cSPDEG`, with `g = cgcdFFCoreWf a b` and
divided coefficients via `cdivWf`. -/
def cSPDEGClearedGenWf (Dt a b c : CPolyG α) (n : ℤ) : Prop :=
  if n < 0 then True
  else
    let g := CFracGcdCoreWf.cgcdFFCoreWf a b
    if cdvdG g c then
      let ad := cdivWf a g
      let bd := cdivWf b g
      let cd := cdivWf c g
      (toPolyG ad * toPolyG g = toPolyG a) ∧ (toPolyG bd * toPolyG g = toPolyG b)
        ∧ (toPolyG cd * toPolyG g = toPolyG c)
        ∧ (toPolyG ad ≠ 0)
        ∧ (if cdegG ad = 0 then True
           else
             let rz := cdiophantineG bd ad cd
             (toPolyG bd * toPolyG rz.1 + toPolyG ad * toPolyG rz.2 = toPolyG cd)
               ∧ (if (n - (cdegG ad : ℤ) + 1).toNat < (n + 1).toNat then
                    cSPDEGClearedGenWf Dt ad (caddG bd (cmonomialDeriv Dt ad))
                      (csubG rz.2 (cmonomialDeriv Dt rz.1)) (n - (cdegG ad : ℤ))
                  else True))
    else True
termination_by (n + 1).toNat
decreasing_by assumption

/-- Under `cSPDEGClearedGenWf`, if `cSPDEG … = some (b̄, c̄, m, α, β)` then for every `h` solving
`D(h) + b̄·h = c̄`, the reconstruction `q = α·h + β` solves `a·D(q) + b·q = c`. -/
theorem cSPDEG_cleared_lifting_gen (Dt a b c : CPolyG α) (n : ℤ) (bbar cbar : CPolyG α) (m : ℤ)
    (α' β : CPolyG α)
    (hspde : cSPDEG Dt a b c n = some (bbar, cbar, m, α', β))
    (hcert : cSPDEGClearedGenWf Dt a b c n) :
    ∀ h : CPolyG α,
      Differential.implicitDeriv (toPolyG Dt) (toPolyG h) + toPolyG bbar * toPolyG h = toPolyG cbar →
      toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α' h) β))
          + toPolyG b * toPolyG (caddG (cmulG α' h) β)
        = toPolyG c := by
  fun_induction cSPDEG Dt a b c n generalizing bbar cbar m α' β with
  | case1 a b c n hn hc =>
    intro h hh
    rw [Option.some.injEq] at hspde
    simp only [Prod.mk.injEq] at hspde
    obtain ⟨hbbar, hcbar, hm, hα, hβ⟩ := hspde
    subst hα; subst hβ
    have hcc : toPolyG c = 0 := (cisZeroG_iff c).mp hc
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
    have hdvd' : (CFracGcdCoreWf.cgcdFFCoreWf a b).cdvdG c = true := hdvd
    rw [cSPDEGClearedGenWf] at hcert
    simp only [hn, hdvd'] at hcert
    obtain ⟨hdiva, hdivb, hdivc, hadne, _⟩ := hcert
    set a0 : CFieldSpec.K α := CFieldSpec.toK (cleadG a') with ha0def
    have ha0ne : a0 ≠ 0 := by
      rw [ha0def, toK_cleadG_eq_leadingCoeff]
      exact Polynomial.leadingCoeff_ne_zero.mpr hadne
    have hadC : toPolyG a' = Polynomial.C a0 := by
      have hnd : (toPolyG a').natDegree = 0 := by rw [← cdegG_eq_natDegree, hdeg]
      rw [ha0def, toK_cleadG_eq_leadingCoeff, Polynomial.leadingCoeff, hnd]
      conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hnd]
    rw [← hbbar, ← hcbar] at hh
    simp only [denote] at hh
    rw [CFieldSpec.toK_inv, ← ha0def] at hh
    have hdivided : toPolyG a' * Differential.implicitDeriv (toPolyG Dt) (toPolyG h)
        + toPolyG b' * toPolyG h = toPolyG c' := by
      rw [hadC]
      exact spde_const_base (Differential.implicitDeriv (toPolyG Dt)) a0 (toPolyG b') (toPolyG c')
        (toPolyG h) ha0ne hh
    rw [← hdiva, ← hdivb, ← hdivc]
    linear_combination toPolyG (CFracGcdCoreWf.cgcdFFCoreWf a b) * hdivided
  | case4 a b c n hn g hdvd a' b' c' hdeg => exact absurd hspde (by simp)
  | case5 a b c n hn g hdvd a' b' c' hdeg r z hdioph Da Dr hguard bbar' cbar' m' α'' β'' hrec ih =>
    intro h hh
    rw [Option.some.injEq] at hspde
    simp only [Prod.mk.injEq] at hspde
    obtain ⟨hbbar, hcbar, hm, hα, hβ⟩ := hspde
    rw [← hbbar] at hh; rw [← hcbar] at hh
    have hdvd' : (CFracGcdCoreWf.cgcdFFCoreWf a b).cdvdG c = true := hdvd
    have hguard' : (n - ((a.cdivWf (CFracGcdCoreWf.cgcdFFCoreWf a b)).cdegG : ℤ) + 1).toNat
        < (n + 1).toNat := hguard
    rw [cSPDEGClearedGenWf] at hcert
    simp only [hn, hdvd'] at hcert
    obtain ⟨hdiva, hdivb, hdivc, _hadne, hcertrest⟩ := hcert
    rw [if_neg hdeg] at hcertrest
    obtain ⟨hbez'0, hcertrecOpt⟩ := hcertrest
    rw [if_pos hguard'] at hcertrecOpt
    have hdioph' : (b.cdivWf (CFracGcdCoreWf.cgcdFFCoreWf a b)).cdiophantineG
        (a.cdivWf (CFracGcdCoreWf.cgcdFFCoreWf a b)) (c.cdivWf (CFracGcdCoreWf.cgcdFFCoreWf a b))
        = (r, z) := hdioph
    rw [hdioph'] at hbez'0 hcertrecOpt
    have hbez' : toPolyG b' * toPolyG r + toPolyG a' * toPolyG z = toPolyG c' := hbez'0
    have hcertrecOpt' : cSPDEGClearedGenWf Dt a' (caddG b' Da) (csubG z Dr) (n - (cdegG a' : ℤ)) :=
      hcertrecOpt
    have hihrec := ih bbar' cbar' m' α'' β'' hrec hcertrecOpt' h hh
    have hred : toPolyG a' * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α'' h) β''))
          + (toPolyG b' + Differential.implicitDeriv (toPolyG Dt) (toPolyG a'))
              * toPolyG (caddG (cmulG α'' h) β'')
        = toPolyG z - Differential.implicitDeriv (toPolyG Dt) (toPolyG r) := by
      simp only [Da, Dr, denote] at hihrec ⊢
      linear_combination hihrec
    subst hα; subst hβ
    have hpeel := cSPDE_peel_cleared_gen Dt a' b' c' r z (caddG (cmulG α'' h) β'') hbez' hred
    have hqeq : toPolyG (caddG (cmulG (cmulG a' α'') h) (caddG (cmulG a' β'') r))
        = toPolyG (caddG (cmulG a' (caddG (cmulG α'' h) β'')) r) := by
      simp only [denote]; ring
    rw [hqeq, ← hdiva, ← hdivb, ← hdivc]
    linear_combination toPolyG (CFracGcdCoreWf.cgcdFFCoreWf a b) * hpeel
  | case6 => exact absurd hspde (by simp)
  | case7 a b c n hn g hdvd => exact absurd hspde (by simp)

/-- `CSPDEGClearedInputsGenWf`: the transparent per-level input predicate for `cSPDEG`'s
cleared-certificate discharge. -/
def CSPDEGClearedInputsGenWf (Dt a b c : CPolyG α) (n : ℤ) : Prop :=
  if n < 0 then True
  else
    let g := CFracGcdCoreWf.cgcdFFCoreWf a b
    if cdvdG g c then
      let ad := cdivWf a g
      (cnormG g ≠ []) ∧ Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b))
        ∧ (cnormG a ≠ [])
        ∧ (if cdegG ad = 0 then True
           else
             let bd := cdivWf b g
             let rz := cdiophantineG bd ad (cdivWf c g)
             (if (n - (cdegG ad : ℤ) + 1).toNat < (n + 1).toNat then
                CSPDEGClearedInputsGenWf Dt ad (caddG bd (cmonomialDeriv Dt ad))
                  (csubG rz.2 (cmonomialDeriv Dt rz.1)) (n - (cdegG ad : ℤ))
              else True))
    else True
termination_by (n + 1).toNat
decreasing_by assumption

omit [CDiffFieldSpec α] in
/-- `CSPDEGClearedInputsGenWf Dt a b c n` implies the per-level certificate `cSPDEGClearedGenWf Dt a b c n`. -/
theorem cSPDEGClearedGenWf_of_inputs (Dt a b c : CPolyG α) (n : ℤ) (hin : CSPDEGClearedInputsGenWf Dt a b c n) :
    cSPDEGClearedGenWf Dt a b c n := by
  fun_induction CSPDEGClearedInputsGenWf Dt a b c n with
  | case1 a b c n hn =>
    rw [cSPDEGClearedGenWf]
    rw [if_pos hn]
    trivial
  | case2 a b c n hn g hdvd ad ih1 =>
    have hdvd' : (CFracGcdCoreWf.cgcdFFCoreWf a b).cdvdG c = true := hdvd
    rw [cSPDEGClearedGenWf]
    simp only [hn, hdvd'] at hin ⊢
    obtain ⟨hg0, hgassoc, ha0, hrest⟩ := hin
    set bd := cdivWf b g with hbd
    have hdiva : toPolyG ad * toPolyG g = toPolyG a := cdivWf_a_exact_of_gcd a b g hg0 hgassoc
    have hdivb : toPolyG bd * toPolyG g = toPolyG b := cdivWf_b_exact_of_gcd a b g hg0 hgassoc
    have hdivc : toPolyG (cdivWf c g) * toPolyG g = toPolyG c :=
      cdivWf_c_exact_of_cdvdG c g hg0 hdvd'
    have hane : toPolyG a ≠ 0 := fun h => ha0 ((cnormG_eq_nil_iff a).mpr h)
    have hadne : toPolyG ad ≠ 0 := by
      intro h; apply hane; rw [← hdiva, h, zero_mul]
    have hgne : toPolyG g ≠ 0 := fun h => hg0 ((cnormG_eq_nil_iff g).mpr h)
    refine ⟨hdiva, hdivb, hdivc, hadne, ?_⟩
    by_cases hdeg : cdegG ad = 0
    · rw [if_pos hdeg] at hrest ⊢; trivial
    · rw [if_neg hdeg] at hrest ⊢
      have hadnil : cnormG ad ≠ [] := fun h => hadne ((cnormG_eq_nil_iff ad).mp h)
      have hunitWf := cgcdWf_isUnit_of_divided_gen a b ad bd g hgne hgassoc hdiva hdivb
      have hgdegWf : (toPolyG (cgcdWf bd ad).1).natDegree = 0 :=
        Polynomial.natDegree_eq_zero_of_isUnit hunitWf
      have hgneWf : toPolyG (cgcdWf bd ad).1 ≠ 0 := hunitWf.ne_zero
      have hbez := toPolyG_cdiophantineG bd ad (cdivWf c g) hadnil hgdegWf hgneWf
      by_cases hguard : (n - (cdegG ad : ℤ) + 1).toNat < (n + 1).toNat
      · rw [if_pos hguard] at hrest ⊢
        refine ⟨?_, ih1 hguard hrest⟩
        simpa [mul_comm] using hbez
      · rw [if_neg hguard] at hrest ⊢
        exact ⟨by simpa [mul_comm] using hbez, trivial⟩
  | case3 a b c n hn g hdvd =>
    have hdvd' : ¬ (CFracGcdCoreWf.cgcdFFCoreWf a b).cdvdG c = true := hdvd
    rw [cSPDEGClearedGenWf]
    simp only [hn, if_neg hdvd']
    trivial

end WfSPDECleared

section WfNormalDenominator

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]

/-- Writing `dₙ = (cSplitFactorFastG Dt fden).1`, if `cRdeNormalDenominatorG … = some (a, b, c, h)`,
the clearings are exact, and `Q` solves `a·D(Q) + b·Q = c`, then `Q` solves the cleared
`gden·fden·(D(Q)·h − Q·D(h)) + gden·fnum·Q·h = gnum·fden·h²`. -/
theorem cRdeNormalDenominatorG_cleared_lift (Dt : CPolyG α) (fnum fden gnum gden a b c h Q : CPolyG α)
    (hres : cRdeNormalDenominatorG Dt fnum fden gnum gden = some (a, b, c, h))
    (hdn : toPolyG (cSplitFactorFastG Dt fden).1 ≠ 0)
    (hfden0 : cnormG fden ≠ []) (hgden0 : cnormG gden ≠ [])
    (hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fden).1 h) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fden).1 (cmonomialDeriv Dt h)) fden)))
    (hdvdC : toPolyG gden ∣ toPolyG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fden).1 h) h) gnum))
    (hred : toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG Q) + toPolyG b * toPolyG Q
      = toPolyG c) :
    toPolyG gden * toPolyG fden
        * (Differential.implicitDeriv (toPolyG Dt) (toPolyG Q) * toPolyG h
            - toPolyG Q * Differential.implicitDeriv (toPolyG Dt) (toPolyG h))
        + toPolyG gden * toPolyG fnum * toPolyG Q * toPolyG h
      = toPolyG gnum * toPolyG fden * toPolyG h ^ 2 := by
  set dn := (cSplitFactorFastG Dt fden).1 with hdndef
  set bNum := csubG (cmulG (cmulG dn h) fnum) (cmulG (cmulG dn (cmonomialDeriv Dt h)) fden) with hbNum
  set cNum := cmulG (cmulG (cmulG dn h) h) gnum with hcNum
  rw [cRdeNormalDenominatorG] at hres
  split at hres
  · rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hres
    obtain ⟨ha, hb, hc, hh⟩ := hres
    rw [hh] at ha hb hc
    have hA : toPolyG a = toPolyG dn * toPolyG h := by
      rw [← ha, ← hdndef]
      simp only [denote]
    have hBexact : toPolyG b * toPolyG fden = toPolyG bNum := by
      rw [← hb]; exact toPolyG_cdivWf_exact_mul_gen bNum fden hfden0 hdvdB
    have hBeq : toPolyG bNum = toPolyG a * toPolyG fnum
        - toPolyG dn * Differential.implicitDeriv (toPolyG Dt) (toPolyG h) * toPolyG fden := by
      simp only [hbNum, denote]
      rw [← hA]
    have hCexact : toPolyG c * toPolyG gden = toPolyG cNum := by
      rw [← hc]; exact toPolyG_cdivWf_exact_mul_gen cNum gden hgden0 hdvdC
    have hCeq : toPolyG cNum = toPolyG dn * toPolyG h ^ 2 * toPolyG gnum := by
      simp only [hcNum, denote]; ring
    have hBcert : toPolyG b * toPolyG fden = toPolyG a * toPolyG fnum
        - toPolyG dn * Differential.implicitDeriv (toPolyG Dt) (toPolyG h) * toPolyG fden := by
      rw [hBexact]; exact hBeq
    have hCcert : toPolyG c * toPolyG gden = toPolyG dn * toPolyG h ^ 2 * toPolyG gnum := by
      rw [hCexact]; exact hCeq
    have hglue := rdeNormalDenominator_glue (Differential.implicitDeriv (toPolyG Dt))
      (toPolyG dn) (toPolyG h) (toPolyG fnum) (toPolyG fden) (toPolyG gnum) (toPolyG gden)
      (toPolyG a) (toPolyG b) (toPolyG c) (toPolyG Q) hdn hA hBcert hCcert hred
    linear_combination hglue
  · exact absurd hres (by simp)

end WfNormalDenominator

section WfCapstone

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]

/-- Lift under the transparent input predicate directly, composing `cSPDEG_cleared_lifting_gen` with
`cSPDEGClearedGenWf_of_inputs`. -/
theorem cSPDEG_cleared_lifting_of_inputs (Dt : CPolyG α) (a b c : CPolyG α) (n : ℤ)
    (bbar cbar : CPolyG α) (m : ℤ) (α' β : CPolyG α)
    (hspde : cSPDEG Dt a b c n = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGenWf Dt a b c n) (h : CPolyG α)
    (hh : Differential.implicitDeriv (toPolyG Dt) (toPolyG h) + toPolyG bbar * toPolyG h
      = toPolyG cbar) :
    toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α' h) β))
        + toPolyG b * toPolyG (caddG (cmulG α' h) β)
      = toPolyG c :=
  cSPDEG_cleared_lifting_gen Dt a b c n bbar cbar m α' β hspde
    (cSPDEGClearedGenWf_of_inputs Dt a b c n hin) h hh

/-- Feed the non-cancellation success through `cPolyRischDENoCancelG_cleared_identity` into the SPDE lifting. -/
theorem cSPDEG_polyRischDENoCancel_cleared_of_inputs (Dt : CPolyG α) (a b c : CPolyG α) (n : ℤ)
    (bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α)
    (hspde : cSPDEG Dt a b c n = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGenWf Dt a b c n)
    (hpoly : cPolyRischDENoCancelG Dt bbar cbar m = some v) :
    toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α' v) β))
        + toPolyG b * toPolyG (caddG (cmulG α' v) β)
      = toPolyG c :=
  cSPDEG_cleared_lifting_of_inputs Dt a b c n bbar cbar m α' β hspde hin v
    (cPolyRischDENoCancelG_cleared_identity Dt bbar cbar m v hpoly)

/-- The spine instantiated at the degree bound `n = cRdeBoundDegreeG Dt a b c`. -/
theorem cSPDEG_polyRischDENoCancel_cleared_at_boundDegree (Dt : CPolyG α) (a b c : CPolyG α)
    (bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α)
    (hspde : cSPDEG Dt a b c (cRdeBoundDegreeG Dt a b c : ℤ) = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGenWf Dt a b c (cRdeBoundDegreeG Dt a b c : ℤ))
    (hpoly : cPolyRischDENoCancelG Dt bbar cbar m = some v) :
    toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α' v) β))
        + toPolyG b * toPolyG (caddG (cmulG α' v) β)
      = toPolyG c :=
  cSPDEG_polyRischDENoCancel_cleared_of_inputs Dt a b c
    (cRdeBoundDegreeG Dt a b c : ℤ) bbar cbar m α' β v hspde hin hpoly

/-- In the primitive regime, from the normal-denominator output, its divisibility certificates, the
SPDE output under `CSPDEGClearedInputsGenWf`, and the poly-RDE identity `D(v) + bbar·v = cbar`, the
reconstruction `ynum = (α'·v + β)·[1]`, `yden = h0` satisfies the cleared Risch-DE identity. -/
theorem rdeClearedIdentityWf_of_polyRDEIdentity (Dt : CPolyG α)
    (fnum fden gnum gden a0 b0 c0 h0 : CPolyG α)
    (bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α)
    (hprim : cdegG (cSpecialPolyG Dt) = 0)
    (hnorm : cRdeNormalDenominatorG Dt fnum fden gnum gden = some (a0, b0, c0, h0))
    (hdn : toPolyG (cSplitFactorFastG Dt fden).1 ≠ 0)
    (hfden0 : cnormG fden ≠ []) (hgden0 : cnormG gden ≠ [])
    (hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fden).1 h0) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fden).1 (cmonomialDeriv Dt h0)) fden)))
    (hdvdC : toPolyG gden ∣ toPolyG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fden).1 h0) h0) gnum))
    (hspde : cSPDEG Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1 (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGenWf Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1 (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1 : ℤ))
    (hidentity : Differential.implicitDeriv (toPolyG Dt) (toPolyG v) + toPolyG bbar * toPolyG v
      = toPolyG cbar) :
    toPolyG gden * toPolyG fden
        * (Differential.implicitDeriv (toPolyG Dt) (toPolyG (cmulG (caddG (cmulG α' v) β) [CField.one]))
              * toPolyG h0
            - toPolyG (cmulG (caddG (cmulG α' v) β) [CField.one])
              * Differential.implicitDeriv (toPolyG Dt) (toPolyG h0))
        + toPolyG gden * toPolyG fnum * toPolyG (cmulG (caddG (cmulG α' v) β) [CField.one]) * toPolyG h0
      = toPolyG gnum * toPolyG fden * toPolyG h0 ^ 2 := by
  set Q := caddG (cmulG α' v) β with hQ
  have hspecial := cRdeSpecialDenominatorG_primitive_eq Dt a0 b0 c0 hprim
  rw [hspecial] at hspde hin
  simp only at hspde hin
  have hred : toPolyG a0 * Differential.implicitDeriv (toPolyG Dt) (toPolyG Q) + toPolyG b0 * toPolyG Q
      = toPolyG c0 :=
    cSPDEG_cleared_lifting_of_inputs Dt a0 b0 c0
      (cRdeBoundDegreeG Dt a0 b0 c0 : ℤ) bbar cbar m α' β hspde hin v hidentity
  have hone : toPolyG ([CField.one] : CPolyG α) = 1 := by
    simp only [denote, mul_zero, add_zero, map_one]
  have hynum : toPolyG (cmulG Q [CField.one]) = toPolyG Q := by
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
that a bare `cRischDEG` success does not self-certify. -/
structure RischDEStructuralResidualWf (Dt : CPolyG α) (fnum fden gnum gden a0 b0 c0 h0 : CPolyG α) :
    Prop where
  /-- Primitive special regime: `cdegG (cSpecialPolyG Dt) = 0`. -/
  hprim : cdegG (cSpecialPolyG Dt) = 0
  /-- The normal part `dₙ = (cSplitFactorFastG Dt fden).1` is nonzero. -/
  hdn : toPolyG (cSplitFactorFastG Dt fden).1 ≠ 0
  /-- The input denominator `fden` is nonzero. -/
  hfden0 : cnormG fden ≠ []
  /-- The input denominator `gden` is nonzero. -/
  hgden0 : cnormG gden ≠ []
  /-- `fden` divides the `B`-numerator (the `cdivWf` clearing is exact). -/
  hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fden).1 h0) fnum)
      (cmulG (cmulG (cSplitFactorFastG Dt fden).1 (cmonomialDeriv Dt h0)) fden))
  /-- `gden` divides the `C`-numerator (the `cdivWf` clearing is exact). -/
  hdvdC : toPolyG gden ∣ toPolyG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fden).1 h0) h0) gnum)
  /-- The transparent-input chain `CSPDEGClearedInputsGenWf` on the special-cleared coefficients at
  the bound degree. -/
  hin : CSPDEGClearedInputsGenWf Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
      (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1 (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1
      (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
        (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1 : ℤ)

/-- Given a `cRischDEG` success, `cdegG Dt = 0`, positive `deg(bbar)`, and the residual
`RischDEStructuralResidualWf`, the returned `y = ynum/yden` satisfies the cleared identity
`gden·fden·(D(ynum)·yden − ynum·D(yden)) + gden·fnum·ynum·yden = gnum·fden·yden²`. -/
theorem rdeClearedWf_of_success_and_residual (Dt : CPolyG α)
    (fnum fden gnum gden ynum yden : CPolyG α) (hδ : cdegG Dt = 0)
    (hsucc : cRischDEG Dt fnum fden gnum gden = some (ynum, yden))
    (hres : ∀ a0 b0 c0 h0 : CPolyG α,
      cRdeNormalDenominatorG Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
      RischDEStructuralResidualWf Dt fnum fden gnum gden a0 b0 c0 h0)
    (hdb : ∀ a0 b0 c0 bbar cbar : CPolyG α, ∀ m : ℤ, ∀ α' β : CPolyG α,
      cSPDEG Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1
          (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α', β) → 0 < cdegG bbar) :
    toPolyG gden * toPolyG fden
        * (Differential.implicitDeriv (toPolyG Dt) (toPolyG ynum) * toPolyG yden
            - toPolyG ynum * Differential.implicitDeriv (toPolyG Dt) (toPolyG yden))
        + toPolyG gden * toPolyG fnum * toPolyG ynum * toPolyG yden
      = toPolyG gnum * toPolyG fden * toPolyG yden ^ 2 := by
  obtain ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, hdisp, hynum, hyden⟩ :=
    cRischDEG_some_imp_stages Dt fnum fden gnum gden ynum yden hsucc
  have hres' := hres a0 b0 c0 h0 hnorm
  have hdb' := hdb a0 b0 c0 bbar cbar m α' β hspde
  have hpoly : cPolyRischDENoCancelG Dt bbar cbar m = some v := by
    rw [← cPolyRischDEG_eq_noCancel_of_primitive Dt bbar cbar m hδ hdb']; exact hdisp
  have hidentity : Differential.implicitDeriv (toPolyG Dt) (toPolyG v) + toPolyG bbar * toPolyG v
      = toPolyG cbar := cPolyRischDENoCancelG_cleared_identity Dt bbar cbar m v hpoly
  have hcap := rdeClearedIdentityWf_of_polyRDEIdentity Dt fnum fden gnum gden a0 b0 c0 h0
    bbar cbar m α' β v hres'.hprim hnorm hres'.hdn hres'.hfden0 hres'.hgden0 hres'.hdvdB
    hres'.hdvdC hspde hres'.hin hidentity
  have hh1 : (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.2 = ([CField.one] : CPolyG α) := by
    rw [cRdeSpecialDenominatorG_primitive_eq Dt a0 b0 c0 hres'.hprim]
  rw [hh1] at hynum
  rw [hynum, hyden]
  exact hcap

end WfResidual

section WfFieldHeadline

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
  [CRischField α] [Algebra ℚ (CFieldSpec.K α)]

/-- The RDE oracle's field-level soundness in the primitive regime, from bare `cRischDEG` success
and the residual: composes `rdeClearedWf_of_success_and_residual` with `rischDE_field_of_cleared`. -/
theorem crischDEWf_field_of_success_and_residual (Dt : CPolyG α)
    (fnum fden gnum gden ynum yden : CPolyG α) (hδ : cdegG Dt = 0)
    (hsucc : cRischDEG Dt fnum fden gnum gden = some (ynum, yden))
    (hres : ∀ a0 b0 c0 h0 : CPolyG α,
      cRdeNormalDenominatorG Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
      RischDEStructuralResidualWf Dt fnum fden gnum gden a0 b0 c0 h0)
    (hdb : ∀ a0 b0 c0 bbar cbar : CPolyG α, ∀ m : ℤ, ∀ α' β : CPolyG α,
      cSPDEG Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1
          (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α', β) → 0 < cdegG bbar)
    (hfden : toPolyG fden ≠ 0) (hgden : toPolyG gden ≠ 0) (hyden : toPolyG yden ≠ 0) :
    towerFractionFieldDerivG Dt (amG α (toPolyG ynum) / amG α (toPolyG yden))
        + amG α (toPolyG fnum) / amG α (toPolyG fden)
          * (amG α (toPolyG ynum) / amG α (toPolyG yden))
      = amG α (toPolyG gnum) / amG α (toPolyG gden) := by
  have hcleared := rdeClearedWf_of_success_and_residual Dt fnum fden gnum gden ynum yden hδ hsucc hres hdb
  have hclam := congrArg (amG α) hcleared
  simp only [map_add, map_mul, map_sub, map_pow] at hclam
  exact rischDE_field_of_cleared Dt fnum fden gnum gden ynum yden hfden hgden hyden hclam

end WfFieldHeadline

end DeepWiki.SymbolicIntegration
