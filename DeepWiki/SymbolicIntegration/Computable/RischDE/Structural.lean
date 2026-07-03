import DeepWiki.SymbolicIntegration.Computable.RischFieldSpec
import DeepWiki.SymbolicIntegration.Computable.OneShotSoundness

/-! # §6 RDE structural decomposition — `cRischDEG = some _` ⟹ the stage `some`-results

`ComputableRischFieldSpec` records the **recursive** `CRischFieldSpec (QFunNZG β)` instance as the
documented layer-bridge obstruction: the §6 correctness `cRischDEG_rdeCleared_gen`
(`ComputableRischDETowerCorrectG`) is **conditional** on ≈13 hypotheses, none of which were yet derived
from the bare success `cRischDEG … = some (ynum, yden)`. This file **attempts** that derivation — the §6
*structural-decomposition theorem* — and partitions the ≈13 hypotheses into the **derivable** class
(forced by `cRischDEG`'s own `match` structure) and the **irreducible residual** (global regularity the
algorithm does not self-certify), stating each precisely.

The §6 RDE oracle `cRischDEG Dt fuel fnum fden gnum gden` is a chain of `match … with | none => none | …`
forms:

  `match cRdeNormalDenominatorG … with | some (a0,b0,c0,h0) =>`
  `  let (a,b,c,h1) := cRdeSpecialDenominatorG Dt fuel a0 b0 c0`
  `  match cSPDEG Dt fuel a b c (cRdeBoundDegreeG Dt a b c) with | some (bbar,cbar,m,α',β) =>`
  `    match cPolyRischDEG Dt fuel bbar cbar m with | some v => some (cmulG (caddG (cmulG α' v) β) h1, h0)`

so a successful run **structurally forces** each intermediate stage to have returned `some` with the very
reassembly the capstone consumes. This is exactly the **derivable** bulk of the capstone's hypotheses.

* **`cRischDEG_some_imp_stages`** — ★ the structural-decomposition core: `cRischDEG … = some (ynum, yden)`
  yields the §6.2 `hnorm` (`cRdeNormalDenominatorG = some (a0,b0,c0,h0)`), the §6.4 `hspde` (`cSPDEG … =
  some (bbar,cbar,m,α',β)` at the bound degree on the special-cleared coefficients), the §6.5/§6.6
  dispatcher result `cPolyRischDEG … = some v`, and the output identification `ynum = (α'·v+β)·h1`,
  `yden = h0`. The three stage-`some`-results derived from bare success.
* **`cRischDEGWf_some_imp_stages_structural`** — the same structural reading for `cRischDEGWf`, exported
  from this structural module so Wf proofs can use one structural API instead of reaching into the runtime
  well-founded module for control-flow facts.
* **`cPolyRischDEG_some_imp_noCancel_of_primitive`** — the dispatcher → non-cancellation bridge in the
  primitive regime: when `Dt` is primitive (`cdegG Dt = 0`) and `bbar ≠ 0` (`db > max 0 (δ−1) = 0`),
  `cPolyRischDEG Dt fuel bbar cbar m = cPolyRischDENoCancelG Dt fuel bbar cbar m`, so the capstone's
  `hpoly` (which is the §6.5 non-cancellation solve, NOT the dispatcher) is the dispatcher result.

The genuinely **irreducible residual** — `hprim` (primitive-regime restriction; `cRischDEG` runs all
regimes), the §6.2 divisibility side-conditions (`hdn`, `hdvdB`, `hdvdC`), and the
transparent-input chain `hin : CSPDEGClearedInputsGen` (whose per-level `Associated`-gcd clauses are the
`CPrimPRSGenAssocReg` regularity that `associated_toPolyG_cgcdFFCore` itself takes as a hypothesis, and
which the engine never self-certifies) — is isolated and named in `RischDEStructuralResidual` below, with
the precise reason each is not forced by bare success. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

variable {α : Type*} [CField α] [CDiffField α]

/-! ### Fuel-free structural decomposition

The well-founded runtime module defines the same control-flow reading for `cRischDEGWf`. This wrapper exposes
it from the structural layer, matching the legacy fueled API location. -/

/-- **Wf structural decomposition**: `cRischDEGWf = some _` forces the Wf stage `some`-results. -/
theorem cRischDEGWf_some_imp_stages_structural [CFracGcdCoreWf α] [CRischField α] (Dt : CPolyG α)
    (fnum fden gnum gden ynum yden : CPolyG α)
    (hsucc : cRischDEGWf Dt fnum fden gnum gden = some (ynum, yden)) :
    ∃ (a0 b0 c0 h0 bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α),
      cRdeNormalDenominatorGWf Dt fnum fden gnum gden = some (a0, b0, c0, h0)
      ∧ cSPDEGWf Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1
          (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α', β)
      ∧ cPolyRischDEGWf Dt bbar cbar m = some v
      ∧ ynum = cmulG (caddG (cmulG α' v) β) (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.2
      ∧ yden = h0 :=
  cRischDEGWf_some_imp_stages Dt fnum fden gnum gden ynum yden hsucc

/-! ### The dispatcher → non-cancellation bridge (primitive regime, positive `deg(bbar)`)

The capstone `cRischDEG_rdeCleared_gen` takes `hpoly : cPolyRischDENoCancelG Dt fuel bbar cbar m = some v`
— the §6.5 **non-cancellation** solve — whereas `cRischDEG`'s body (and hence `cRischDEG_some_imp_stages`)
yields the §6.5/§6.6 **dispatcher** `cPolyRischDEG Dt fuel bbar cbar m = some v`. The dispatcher routes by
`δ = cdegG Dt` and `db = cdegG bbar` (Lemma 6.5.1): in the **primitive** regime (`δ = 0`) with
`db > max 0 (δ−1) = 0` (i.e. `bbar` of positive degree) it routes to `cPolyRischDENoCancelG` verbatim. So
under `cdegG Dt = 0` and `0 < cdegG bbar`, the dispatcher result IS the capstone's non-cancellation result.
(`bbar = 0` would route to pure integration `cIntegratePolyG`; `db = 0` to the primitive cancellation
recursion `cPolyRischDECancelPrimG` — neither is `cPolyRischDENoCancelG`, so the bridge needs
`0 < cdegG bbar`, which the capstone's downstream consumption implicitly assumes.) -/

/-- **Fuel-free mirror of `cPolyRischDEG_eq_noCancel_of_primitive`**: in the primitive regime
(`cdegG Dt = 0`) with positive `deg(bbar)`, the fuel-free dispatcher `cPolyRischDEGWf` reduces to the
non-cancellation solve `cPolyRischDENoCancelGWf`. Same Lemma-6.5.1 routing; a structural mirror of the
retired fuel'd dispatcher. -/
theorem cPolyRischDEGWf_eq_noCancel_of_primitive [CRischField α] (Dt : CPolyG α)
    (bbar cbar : CPolyG α) (m : ℤ) (hδ : cdegG Dt = 0) (hdb : 0 < cdegG bbar) :
    cPolyRischDEGWf Dt bbar cbar m = cPolyRischDENoCancelGWf Dt bbar cbar m := by
  rw [cPolyRischDEGWf]
  have hlen : 0 < (cnormG bbar : List α).length := by
    have := hdb; rw [cdegG] at this; omega
  have hbne : cisZeroG bbar = false := by
    rw [cisZeroG, List.isEmpty_eq_false_iff_exists_mem]
    exact List.exists_mem_of_length_pos hlen
  simp only [hbne, Bool.false_eq_true, if_false, hδ, Nat.cast_zero, zero_sub]
  rw [if_pos]
  rw [show (max (0 : ℤ) (-1)) = 0 by norm_num]
  exact_mod_cast hdb

/-- **Fuel-free mirror of `cRischDEG_some_imp_noCancel_of_primitive`**: from a bare `cRischDEGWf`
success in the primitive regime with positive `deg(bbar)`, the §6.2 `hnorm`, §6.4 `hspde`, and the
capstone's §6.5 non-cancellation `hpoly` (`cPolyRischDENoCancelGWf … = some v`) all hold. Composes
`cRischDEGWf_some_imp_stages` with `cPolyRischDEGWf_eq_noCancel_of_primitive`. -/
theorem cRischDEGWf_some_imp_noCancel_of_primitive [CFracGcdCoreWf α] [CRischField α] (Dt : CPolyG α)
    (fnum fden gnum gden ynum yden : CPolyG α) (hδ : cdegG Dt = 0)
    (hsucc : cRischDEGWf Dt fnum fden gnum gden = some (ynum, yden)) :
    ∃ (a0 b0 c0 h0 bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α),
      cRdeNormalDenominatorGWf Dt fnum fden gnum gden = some (a0, b0, c0, h0)
      ∧ cSPDEGWf Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1 (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1
          (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α', β)
      ∧ (0 < cdegG bbar → cPolyRischDENoCancelGWf Dt bbar cbar m = some v)
      ∧ ynum = cmulG (caddG (cmulG α' v) β) (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.2
      ∧ yden = h0 := by
  obtain ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, hdisp, hynum, hyden⟩ :=
    cRischDEGWf_some_imp_stages Dt fnum fden gnum gden ynum yden hsucc
  refine ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, ?_, hynum, hyden⟩
  intro hdb
  rw [← cPolyRischDEGWf_eq_noCancel_of_primitive Dt bbar cbar m hδ hdb]
  exact hdisp


/-! ### Axiom audit (the structural decomposition rests only on the standard kernel axioms) -/

#print axioms cRischDEGWf_some_imp_stages_structural

/-! ## Fuel-free cleared-identity ports (Phase P1 of the RischDE Wf migration) -/

section WfCleared

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-- **Fuel-free mirror of `cPolyRischDENoCancelG_cleared_identity_gen`**: a `cPolyRischDENoCancelGWf`
success `= some q` yields the §6.5 non-cancellation identity `D(q) + b·q = c` over `(CFieldSpec.K α)[X]`.
`fun_induction` on the well-founded `cPolyRischDENoCancelGWf` recursion, mirroring the fuel'd fuel-induction
proof (base `c = 0`; recursive `q = p + qrec`, closed by `linear_combination` on the IH). -/
theorem cPolyRischDENoCancelGWf_cleared_identity (Dt b c : CPolyG α) (n : ℤ) (q : CPolyG α)
    (hsolve : cPolyRischDENoCancelGWf Dt b c n = some q) :
    Differential.implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG b * toPolyG q = toPolyG c := by
  fun_induction cPolyRischDENoCancelGWf Dt b c n generalizing q with
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

/-- **Fuel-free mirror of `cSPDEGClearedGen`**: the per-level certificate for `cSPDEGWf`, with
`g = cgcdFFCoreWf a b` and divided coefficients via `cdivWf`. Fuel-free (no fuel-bound clauses),
well-founded on `(n+1).toNat` mirroring `cSPDEGWf`'s own recursion structure exactly (same explicit
`(n − deg ad + 1).toNat < (n+1).toNat` guard, so `decreasing_by assumption` applies verbatim). -/
def cSPDEGClearedGenWf (Dt a b c : CPolyG α) (n : ℤ) : Prop :=
  if n < 0 then True
  else
    let g := CFracGcdCoreWf.cgcdFFCoreWf a b
    if cdvdGWf g c then
      let ad := cdivWf a g
      let bd := cdivWf b g
      let cd := cdivWf c g
      (toPolyG ad * toPolyG g = toPolyG a) ∧ (toPolyG bd * toPolyG g = toPolyG b)
        ∧ (toPolyG cd * toPolyG g = toPolyG c)
        ∧ (toPolyG ad ≠ 0)
        ∧ (if cdegG ad = 0 then True
           else
             let rz := cdiophantineGWf bd ad cd
             (toPolyG bd * toPolyG rz.1 + toPolyG ad * toPolyG rz.2 = toPolyG cd)
               ∧ (if (n - (cdegG ad : ℤ) + 1).toNat < (n + 1).toNat then
                    cSPDEGClearedGenWf Dt ad (caddG bd (cmonomialDeriv Dt ad))
                      (csubG rz.2 (cmonomialDeriv Dt rz.1)) (n - (cdegG ad : ℤ))
                  else True))
    else True
termination_by (n + 1).toNat
decreasing_by assumption

/-- **Fuel-free mirror of `cSPDEG_cleared_lifting_gen`**: under `cSPDEGClearedGenWf`, if `cSPDEGWf Dt a b c n
= some (b̄, c̄, m, α, β)` then for every `h` solving the reduced `D(h) + b̄·h = c̄`, the reconstruction `q =
α·h + β` solves the original `a·D(q) + b·q = c` over `(CFieldSpec.K α)[X]`. `fun_induction` on the
well-founded `cSPDEGWf` recursion, mirroring the fuel'd fuel-induction proof case-by-case (constant-`a'` base
via `spde_const_base`, recursive peel via `cSPDE_peel_cleared_gen`). -/
theorem cSPDEGWf_cleared_lifting_gen (Dt a b c : CPolyG α) (n : ℤ) (bbar cbar : CPolyG α) (m : ℤ)
    (α' β : CPolyG α)
    (hspde : cSPDEGWf Dt a b c n = some (bbar, cbar, m, α', β))
    (hcert : cSPDEGClearedGenWf Dt a b c n) :
    ∀ h : CPolyG α,
      Differential.implicitDeriv (toPolyG Dt) (toPolyG h) + toPolyG bbar * toPolyG h = toPolyG cbar →
      toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α' h) β))
          + toPolyG b * toPolyG (caddG (cmulG α' h) β)
        = toPolyG c := by
  fun_induction cSPDEGWf Dt a b c n generalizing bbar cbar m α' β with
  | case1 a b c n hn hc =>
    intro h hh
    rw [Option.some.injEq] at hspde
    simp only [Prod.mk.injEq] at hspde
    obtain ⟨hbbar, hcbar, hm, hα, hβ⟩ := hspde
    subst hα; subst hβ
    have hcc : toPolyG c = 0 := (cisZeroG_iff c).mp hc
    rw [toPolyG_caddG, toPolyG_cmulG, toPolyG_nil, zero_mul, add_zero, map_zero, mul_zero,
      mul_zero, add_zero, hcc]
  | case2 => exact absurd hspde (by simp)
  | case3 a b c n hn g hdvd a' b' c' hdeg ainv =>
    intro h hh
    rw [Option.some.injEq] at hspde
    simp only [Prod.mk.injEq] at hspde
    obtain ⟨hbbar, hcbar, hm, hα, hβ⟩ := hspde
    subst hα; subst hβ
    rw [toPolyG_caddG, toPolyG_cmulG, toPolyG_nil, add_zero]
    have hone : toPolyG ([CField.one] : CPolyG α) = 1 := by
      rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]
    rw [hone, one_mul]
    have hdvd' : (CFracGcdCoreWf.cgcdFFCoreWf a b).cdvdGWf c = true := hdvd
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
    rw [← hbbar, ← hcbar, toPolyG_cscaleG, toPolyG_cscaleG, CFieldSpec.toK_inv, ← ha0def] at hh
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
    have hdvd' : (CFracGcdCoreWf.cgcdFFCoreWf a b).cdvdGWf c = true := hdvd
    have hguard' : (n - ((a.cdivWf (CFracGcdCoreWf.cgcdFFCoreWf a b)).cdegG : ℤ) + 1).toNat
        < (n + 1).toNat := hguard
    rw [cSPDEGClearedGenWf] at hcert
    simp only [hn, hdvd'] at hcert
    obtain ⟨hdiva, hdivb, hdivc, _hadne, hcertrest⟩ := hcert
    rw [if_neg hdeg] at hcertrest
    obtain ⟨hbez'0, hcertrecOpt⟩ := hcertrest
    rw [if_pos hguard'] at hcertrecOpt
    have hdioph' : (b.cdivWf (CFracGcdCoreWf.cgcdFFCoreWf a b)).cdiophantineGWf
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

/-- **Fuel-free mirror of `CSPDEGClearedInputsGen`**: the transparent per-level input predicate for
`cSPDEGWf`'s cleared-certificate discharge. Fuel-free (no fuel-bound length clauses), well-founded on
`(n+1).toNat` with the same explicit recursion guard as `cSPDEGClearedGenWf`. -/
def CSPDEGClearedInputsGenWf (Dt a b c : CPolyG α) (n : ℤ) : Prop :=
  if n < 0 then True
  else
    let g := CFracGcdCoreWf.cgcdFFCoreWf a b
    if cdvdGWf g c then
      let ad := cdivWf a g
      (cnormG g ≠ []) ∧ Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b))
        ∧ (cnormG a ≠ [])
        ∧ (if cdegG ad = 0 then True
           else
             let bd := cdivWf b g
             let rz := cdiophantineGWf bd ad (cdivWf c g)
             (if (n - (cdegG ad : ℤ) + 1).toNat < (n + 1).toNat then
                CSPDEGClearedInputsGenWf Dt ad (caddG bd (cmonomialDeriv Dt ad))
                  (csubG rz.2 (cmonomialDeriv Dt rz.1)) (n - (cdegG ad : ℤ))
              else True))
    else True
termination_by (n + 1).toNat
decreasing_by assumption

omit [CDiffFieldSpec α] in
/-- **Fuel-free mirror of `cSPDEGCleared_of_inputs_gen`**: `CSPDEGClearedInputsGenWf Dt a b c n` implies the
per-level certificate `cSPDEGClearedGenWf Dt a b c n`. `fun_induction` on the well-founded
`CSPDEGClearedInputsGenWf` recursion, mirroring the fuel'd fuel-induction proof (exact-division witnesses via
`cdivWf_a/b_exact_of_gcd` + `cdivWf_c_exact_of_cdvdGWf`, the Bézout clause via `toPolyG_cdiophantineGWf` with
the divided-coefficient Wf gcd shown unit by `cgcdWf_isUnit_of_divided_gen`). -/
theorem cSPDEGClearedGenWf_of_inputs (Dt a b c : CPolyG α) (n : ℤ) (hin : CSPDEGClearedInputsGenWf Dt a b c n) :
    cSPDEGClearedGenWf Dt a b c n := by
  fun_induction CSPDEGClearedInputsGenWf Dt a b c n with
  | case1 a b c n hn =>
    rw [cSPDEGClearedGenWf]
    rw [if_pos hn]
    trivial
  | case2 a b c n hn g hdvd ad ih1 =>
    have hdvd' : (CFracGcdCoreWf.cgcdFFCoreWf a b).cdvdGWf c = true := hdvd
    rw [cSPDEGClearedGenWf]
    simp only [hn, hdvd'] at hin ⊢
    obtain ⟨hg0, hgassoc, ha0, hrest⟩ := hin
    set bd := cdivWf b g with hbd
    have hdiva : toPolyG ad * toPolyG g = toPolyG a := cdivWf_a_exact_of_gcd a b g hg0 hgassoc
    have hdivb : toPolyG bd * toPolyG g = toPolyG b := cdivWf_b_exact_of_gcd a b g hg0 hgassoc
    have hdivc : toPolyG (cdivWf c g) * toPolyG g = toPolyG c :=
      cdivWf_c_exact_of_cdvdGWf c g hg0 hdvd'
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
      have hbez := toPolyG_cdiophantineGWf bd ad (cdivWf c g) hadnil hgdegWf hgneWf
      by_cases hguard : (n - (cdegG ad : ℤ) + 1).toNat < (n + 1).toNat
      · rw [if_pos hguard] at hrest ⊢
        refine ⟨?_, ih1 hguard hrest⟩
        simpa [mul_comm] using hbez
      · rw [if_neg hguard] at hrest ⊢
        exact ⟨by simpa [mul_comm] using hbez, trivial⟩
  | case3 a b c n hn g hdvd =>
    have hdvd' : ¬ (CFracGcdCoreWf.cgcdFFCoreWf a b).cdvdGWf c = true := hdvd
    rw [cSPDEGClearedGenWf]
    simp only [hn, if_neg hdvd']
    trivial

end WfSPDECleared

section WfNormalDenominator

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]

/-- **Fuel-free mirror of `cRdeNormalDenominatorG_cleared_lift_gen`**: writing `dₙ = (cSplitFactorFastGWf Dt
fden).1`, if `cRdeNormalDenominatorGWf Dt fnum fden gnum gden = some (a, b, c, h)`, the normal part is
nonzero, the two `cdivWf`-clearings are exact, and a polynomial `Q` solves the reduced `a·D(Q) + b·Q = c`,
then `y = Q/h` solves the cleared `gden·fden·(D(Q)·h − Q·D(h)) + gden·fnum·Q·h = gnum·fden·h²` over
`(CFieldSpec.K α)[X]`. Fuel-free mirror, reusing the fuel-agnostic `rdeNormalDenominator_glue` /
`toPolyG_cdivWf_exact_mul_gen` verbatim. -/
theorem cRdeNormalDenominatorGWf_cleared_lift (Dt : CPolyG α) (fnum fden gnum gden a b c h Q : CPolyG α)
    (hres : cRdeNormalDenominatorGWf Dt fnum fden gnum gden = some (a, b, c, h))
    (hdn : toPolyG (cSplitFactorFastGWf Dt fden).1 ≠ 0)
    (hfden0 : cnormG fden ≠ []) (hgden0 : cnormG gden ≠ [])
    (hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (cSplitFactorFastGWf Dt fden).1 h) fnum)
        (cmulG (cmulG (cSplitFactorFastGWf Dt fden).1 (cmonomialDeriv Dt h)) fden)))
    (hdvdC : toPolyG gden ∣ toPolyG (cmulG (cmulG (cmulG (cSplitFactorFastGWf Dt fden).1 h) h) gnum))
    (hred : toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG Q) + toPolyG b * toPolyG Q
      = toPolyG c) :
    toPolyG gden * toPolyG fden
        * (Differential.implicitDeriv (toPolyG Dt) (toPolyG Q) * toPolyG h
            - toPolyG Q * Differential.implicitDeriv (toPolyG Dt) (toPolyG h))
        + toPolyG gden * toPolyG fnum * toPolyG Q * toPolyG h
      = toPolyG gnum * toPolyG fden * toPolyG h ^ 2 := by
  set dn := (cSplitFactorFastGWf Dt fden).1 with hdndef
  set bNum := csubG (cmulG (cmulG dn h) fnum) (cmulG (cmulG dn (cmonomialDeriv Dt h)) fden) with hbNum
  set cNum := cmulG (cmulG (cmulG dn h) h) gnum with hcNum
  rw [cRdeNormalDenominatorGWf] at hres
  split at hres
  · rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hres
    obtain ⟨ha, hb, hc, hh⟩ := hres
    rw [hh] at ha hb hc
    have hA : toPolyG a = toPolyG dn * toPolyG h := by rw [← ha, toPolyG_cmulG]
    have hBexact : toPolyG b * toPolyG fden = toPolyG bNum := by
      rw [← hb]; exact toPolyG_cdivWf_exact_mul_gen bNum fden hfden0 hdvdB
    have hBeq : toPolyG bNum = toPolyG a * toPolyG fnum
        - toPolyG dn * Differential.implicitDeriv (toPolyG Dt) (toPolyG h) * toPolyG fden := by
      rw [hbNum, toPolyG_csubG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG,
        toPolyG_cmonomialDeriv, ← ha, toPolyG_cmulG]
    have hCexact : toPolyG c * toPolyG gden = toPolyG cNum := by
      rw [← hc]; exact toPolyG_cdivWf_exact_mul_gen cNum gden hgden0 hdvdC
    have hCeq : toPolyG cNum = toPolyG dn * toPolyG h ^ 2 * toPolyG gnum := by
      rw [hcNum, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG]; ring
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

/-- **Fuel-free mirror of `cSPDEG_cleared_lifting_of_inputs_gen`**: composes `cSPDEGWf_cleared_lifting_gen`
with `cSPDEGClearedGenWf_of_inputs` to lift under the transparent input predicate directly. -/
theorem cSPDEGWf_cleared_lifting_of_inputs (Dt : CPolyG α) (a b c : CPolyG α) (n : ℤ)
    (bbar cbar : CPolyG α) (m : ℤ) (α' β : CPolyG α)
    (hspde : cSPDEGWf Dt a b c n = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGenWf Dt a b c n) (h : CPolyG α)
    (hh : Differential.implicitDeriv (toPolyG Dt) (toPolyG h) + toPolyG bbar * toPolyG h
      = toPolyG cbar) :
    toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α' h) β))
        + toPolyG b * toPolyG (caddG (cmulG α' h) β)
      = toPolyG c :=
  cSPDEGWf_cleared_lifting_gen Dt a b c n bbar cbar m α' β hspde
    (cSPDEGClearedGenWf_of_inputs Dt a b c n hin) h hh

/-- **Fuel-free mirror of `cSPDEG_polyRischDENoCancel_cleared_of_inputs_gen`**: feeds the §6.5
non-cancellation success through `cPolyRischDENoCancelGWf_cleared_identity` into the SPDE lifting. -/
theorem cSPDEGWf_polyRischDENoCancel_cleared_of_inputs (Dt : CPolyG α) (a b c : CPolyG α) (n : ℤ)
    (bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α)
    (hspde : cSPDEGWf Dt a b c n = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGenWf Dt a b c n)
    (hpoly : cPolyRischDENoCancelGWf Dt bbar cbar m = some v) :
    toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α' v) β))
        + toPolyG b * toPolyG (caddG (cmulG α' v) β)
      = toPolyG c :=
  cSPDEGWf_cleared_lifting_of_inputs Dt a b c n bbar cbar m α' β hspde hin v
    (cPolyRischDENoCancelGWf_cleared_identity Dt bbar cbar m v hpoly)

/-- **Fuel-free mirror of `cSPDEG_polyRischDENoCancel_cleared_at_boundDegree_gen`**: the spine instantiated
at the §6.3 degree bound `n = cRdeBoundDegreeG Dt a b c`. -/
theorem cSPDEGWf_polyRischDENoCancel_cleared_at_boundDegree (Dt : CPolyG α) (a b c : CPolyG α)
    (bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α)
    (hspde : cSPDEGWf Dt a b c (cRdeBoundDegreeG Dt a b c : ℤ) = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGenWf Dt a b c (cRdeBoundDegreeG Dt a b c : ℤ))
    (hpoly : cPolyRischDENoCancelGWf Dt bbar cbar m = some v) :
    toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α' v) β))
        + toPolyG b * toPolyG (caddG (cmulG α' v) β)
      = toPolyG c :=
  cSPDEGWf_polyRischDENoCancel_cleared_of_inputs Dt a b c
    (cRdeBoundDegreeG Dt a b c : ℤ) bbar cbar m α' β v hspde hin hpoly

/-- **Fuel-free mirror of `rdeClearedIdentity_of_polyRDEIdentity`** (primitive regime): the fuel-free §6
cleared identity from the residual and the bare poly-RDE identity `D(v) + bbar·v = cbar`, taken directly
rather than through the non-cancellation solver-success form. Given the primitive special regime, the §6.2
normal-denominator output, its divisibility certificates, the §6.4 SPDE output under
`CSPDEGClearedInputsGenWf`, and `hidentity`, the reconstruction `ynum = (α'·v + β)·[1]`, `yden = h0`
satisfies the cleared Risch-DE identity over `(CFieldSpec.K α)[X]`. -/
theorem rdeClearedIdentityWf_of_polyRDEIdentity (Dt : CPolyG α)
    (fnum fden gnum gden a0 b0 c0 h0 : CPolyG α)
    (bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α)
    (hprim : cdegG (cSpecialPolyGWf Dt) = 0)
    (hnorm : cRdeNormalDenominatorGWf Dt fnum fden gnum gden = some (a0, b0, c0, h0))
    (hdn : toPolyG (cSplitFactorFastGWf Dt fden).1 ≠ 0)
    (hfden0 : cnormG fden ≠ []) (hgden0 : cnormG gden ≠ [])
    (hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (cSplitFactorFastGWf Dt fden).1 h0) fnum)
        (cmulG (cmulG (cSplitFactorFastGWf Dt fden).1 (cmonomialDeriv Dt h0)) fden)))
    (hdvdC : toPolyG gden ∣ toPolyG (cmulG (cmulG (cmulG (cSplitFactorFastGWf Dt fden).1 h0) h0) gnum))
    (hspde : cSPDEGWf Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
        (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1 (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGenWf Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
        (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1 (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1 : ℤ))
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
  have hspecial := cRdeSpecialDenominatorGWf_primitive_eq Dt a0 b0 c0 hprim
  rw [hspecial] at hspde hin
  simp only at hspde hin
  have hred : toPolyG a0 * Differential.implicitDeriv (toPolyG Dt) (toPolyG Q) + toPolyG b0 * toPolyG Q
      = toPolyG c0 :=
    cSPDEGWf_cleared_lifting_of_inputs Dt a0 b0 c0
      (cRdeBoundDegreeG Dt a0 b0 c0 : ℤ) bbar cbar m α' β hspde hin v hidentity
  have hone : toPolyG ([CField.one] : CPolyG α) = 1 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]
  have hynum : toPolyG (cmulG Q [CField.one]) = toPolyG Q := by
    rw [toPolyG_cmulG, hone, mul_one]
  have hlift := cRdeNormalDenominatorGWf_cleared_lift Dt fnum fden gnum gden a0 b0 c0 h0 Q
    hnorm hdn hfden0 hgden0 hdvdB hdvdC hred
  rw [hynum]
  exact hlift

end WfCapstone

section WfResidual

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
  [CRischField α]

/-- **Fuel-free mirror of `RischDEStructuralResidual`**: the irreducible residual of the fuel-free §6 RDE
structural decomposition — the hypotheses of `rdeClearedIdentityWf_of_polyRDEIdentity` that a bare
`cRischDEGWf` success does NOT self-certify (the primitive-regime restriction, the §6.2 divisibility
side-conditions, and the per-level transparent-input chain `CSPDEGClearedInputsGenWf`). -/
structure RischDEStructuralResidualWf (Dt : CPolyG α) (fnum fden gnum gden a0 b0 c0 h0 : CPolyG α) :
    Prop where
  /-- Primitive special regime: `cdegG (cSpecialPolyGWf Dt) = 0` (the capstone is primitive-only). -/
  hprim : cdegG (cSpecialPolyGWf Dt) = 0
  /-- §6.2: the normal part `dₙ = (cSplitFactorFastGWf Dt fden).1` is nonzero. -/
  hdn : toPolyG (cSplitFactorFastGWf Dt fden).1 ≠ 0
  /-- §6.2: the input denominator `fden` is nonzero. -/
  hfden0 : cnormG fden ≠ []
  /-- §6.2: the input denominator `gden` is nonzero. -/
  hgden0 : cnormG gden ≠ []
  /-- §6.2: `fden` divides the `B`-numerator (the `cdivWf` clearing is exact). -/
  hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (cSplitFactorFastGWf Dt fden).1 h0) fnum)
      (cmulG (cmulG (cSplitFactorFastGWf Dt fden).1 (cmonomialDeriv Dt h0)) fden))
  /-- §6.2: `gden` divides the `C`-numerator (the `cdivWf` clearing is exact). -/
  hdvdC : toPolyG gden ∣ toPolyG (cmulG (cmulG (cmulG (cSplitFactorFastGWf Dt fden).1 h0) h0) gnum)
  /-- §6.4: the per-level transparent-input chain `CSPDEGClearedInputsGenWf` on the special-cleared
  coefficients at the §6.3 bound degree. -/
  hin : CSPDEGClearedInputsGenWf Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
      (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1 (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1
      (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
        (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
        (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1 : ℤ)

/-- **Fuel-free mirror of `rdeCleared_of_success_and_residual`**: given `cRischDEGWf Dt fnum fden gnum gden
= some (ynum, yden)`, `cdegG Dt = 0`, the SPDE output `bbar` of positive degree, and the irreducible
residual `RischDEStructuralResidualWf` on the matching §6.2 normal-denominator output, the returned `y =
ynum/yden` satisfies the cleared identity `gden·fden·(D(ynum)·yden − ynum·D(yden)) + gden·fnum·ynum·yden =
gnum·fden·yden²` over `(CFieldSpec.K α)[X]` — with NO fuel dependency anywhere in the statement or proof. -/
theorem rdeClearedWf_of_success_and_residual (Dt : CPolyG α)
    (fnum fden gnum gden ynum yden : CPolyG α) (hδ : cdegG Dt = 0)
    (hsucc : cRischDEGWf Dt fnum fden gnum gden = some (ynum, yden))
    (hres : ∀ a0 b0 c0 h0 : CPolyG α,
      cRdeNormalDenominatorGWf Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
      RischDEStructuralResidualWf Dt fnum fden gnum gden a0 b0 c0 h0)
    (hdb : ∀ a0 b0 c0 bbar cbar : CPolyG α, ∀ m : ℤ, ∀ α' β : CPolyG α,
      cSPDEGWf Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1
          (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α', β) → 0 < cdegG bbar) :
    toPolyG gden * toPolyG fden
        * (Differential.implicitDeriv (toPolyG Dt) (toPolyG ynum) * toPolyG yden
            - toPolyG ynum * Differential.implicitDeriv (toPolyG Dt) (toPolyG yden))
        + toPolyG gden * toPolyG fnum * toPolyG ynum * toPolyG yden
      = toPolyG gnum * toPolyG fden * toPolyG yden ^ 2 := by
  obtain ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, hdisp, hynum, hyden⟩ :=
    cRischDEGWf_some_imp_stages Dt fnum fden gnum gden ynum yden hsucc
  have hres' := hres a0 b0 c0 h0 hnorm
  have hdb' := hdb a0 b0 c0 bbar cbar m α' β hspde
  have hpoly : cPolyRischDENoCancelGWf Dt bbar cbar m = some v := by
    rw [← cPolyRischDEGWf_eq_noCancel_of_primitive Dt bbar cbar m hδ hdb']; exact hdisp
  have hidentity : Differential.implicitDeriv (toPolyG Dt) (toPolyG v) + toPolyG bbar * toPolyG v
      = toPolyG cbar := cPolyRischDENoCancelGWf_cleared_identity Dt bbar cbar m v hpoly
  have hcap := rdeClearedIdentityWf_of_polyRDEIdentity Dt fnum fden gnum gden a0 b0 c0 h0
    bbar cbar m α' β v hres'.hprim hnorm hres'.hdn hres'.hfden0 hres'.hgden0 hres'.hdvdB
    hres'.hdvdC hspde hres'.hin hidentity
  have hh1 : (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.2 = ([CField.one] : CPolyG α) := by
    rw [cRdeSpecialDenominatorGWf_primitive_eq Dt a0 b0 c0 hres'.hprim]
  rw [hh1] at hynum
  rw [hynum, hyden]
  exact hcap

end WfResidual

section WfFieldHeadline

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
  [CRischField α] [Algebra ℚ (CFieldSpec.K α)]

/-- **★ The fuel-free §6 RDE oracle's field-level soundness, from bare success + the isolated residual**
(primitive regime): composes `rdeClearedWf_of_success_and_residual` (bare `cRischDEGWf` success + the
residual ⟹ the cleared polynomial identity) with the cleared → field bridge `rischDE_field_of_cleared`.
The Wf-track analogue of `crischDESolve_field_of_witness_residual`'s field-level conclusion, but for the
*fuel-free* oracle directly — no tower-gcd witness, no fuel, no `native_decide`. -/
theorem crischDEWf_field_of_success_and_residual (Dt : CPolyG α)
    (fnum fden gnum gden ynum yden : CPolyG α) (hδ : cdegG Dt = 0)
    (hsucc : cRischDEGWf Dt fnum fden gnum gden = some (ynum, yden))
    (hres : ∀ a0 b0 c0 h0 : CPolyG α,
      cRdeNormalDenominatorGWf Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
      RischDEStructuralResidualWf Dt fnum fden gnum gden a0 b0 c0 h0)
    (hdb : ∀ a0 b0 c0 bbar cbar : CPolyG α, ∀ m : ℤ, ∀ α' β : CPolyG α,
      cSPDEGWf Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1
          (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1 : ℤ)
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
