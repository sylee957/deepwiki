import DeepWiki.SymbolicIntegration.ComputableRischDETowerGlue
import DeepWiki.SymbolicIntegration.ComputableSplitFactorTowerCorrectG

/-! # §6 RDE cleared-identity correctness at the GENERIC carrier `α = QFunNZG ℚ`

`ComputableRischDETowerCorrect` proved the generic §6 RDE oracle `cRischDEG`'s abstract cleared identity
`Dy + f·y = g` (`cRischDEG_rdeCleared`) and the §6.4 SPDE certificate discharge (`cSPDEGCleared_of_inputs`)
**pinned at `α = QFunNZ`**: there `CFracGcdCore.cgcdFFCore` resolves to `instCFracGcdCoreQFunNZ`, which is
`cmonicG ∘ cgcdFF`, so the QFunNZ §6 correctness depends on the hand-built `cgcdFF`.

This file re-founds the entire §6 RDE cleared chain at the **generic level-1 carrier** `α = QFunNZG ℚ =
Frac(ℚ[x])`, exactly the chunk-1 pattern of `ComputableSplitFactorTowerCorrectG` (which re-founded §5 at
`QFunNZG ℚ`). At `QFunNZG ℚ`, `CFracGcdCore.cgcdFFCore` resolves to the **recursive** `instCFracGcdCoreQFunNZG`,
whose Euclidean work bottoms at `cgcdWf` over ℚ — **never `cgcdFF`**. The single gcd-correctness obligation
the SPDE discharge needs — `Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b))` for `g = cgcdFFCore fuel a
b` — is discharged through the **generic** theorem `associated_toPolyG_cgcdFFCore`
(`ComputableTowerGcdFFCorrect`), NOT the QFunNZ `cgcdFF` bridge.

The carriers `QFunNZ` and `QFunNZG ℚ` are genuinely different types, but **both read through `toPolyG` into
the same field `RatFunc ℚ = CFieldSpec.K QFunNZ = CFieldSpec.K (QFunNZG ℚ)`**, so the abstract conclusions
(the cleared polynomial identities over `(RatFunc ℚ)[X]`) are identical between them — only the gcd-correctness
discharger changes (`cgcdFF`-based ⤳ `cgcdFFCore`-based). The cleared-lifting *engine*
(`cSPDEG_cleared_lifting`-style induction, `rdeNormalDenominator_glue`, `spde_const_base`, `cSPDE_peel_cleared`,
`toPolyG_cdiophantineG`, `dvd_of_cdvdG`, `toPolyG_cdivG_exact`) is gcd-agnostic, so it transports verbatim with
the carrier swapped; the genuinely new ingredient is the gcd-discharge route.

ADDITIVE: the QFunNZ versions remain; this adds the `QFunNZG ℚ` correctness. With them in hand the QFunNZ §6
RDE correctness no longer pins `cgcdFF`, leaving only the QFunNZ §5 cluster on `cgcdFF`.

* **Generic helper lemmas** — the QFunNZ-pinned `cgcdExtG`-unit / exact-division / SPDE-peel helpers, lifted
  to `{α} [CField α] [CFieldSpec α]`-generic (their bodies were already gcd-agnostic, taking the gcd `g`
  abstractly).
* **`cSPDECleared_of_inputs_qfunNZG`** — the §6.4 SPDE per-level certificate, discharged from transparent
  inputs, at `α = QFunNZG ℚ` (the gcd obligation via `associated_toPolyG_cgcdFFCore`, NOT `cgcdFF`).
* **★ `cRischDEG_rdeCleared_qfunNZG`** — the generic RDE oracle's cleared identity `Dy + f·y = g` at
  `α = QFunNZG ℚ`, cgcdFF-free. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ### Generic helper lemmas (lifting the QFunNZ-pinned §6.4 helpers to any tower level)

The §6.4 SPDE certificate discharge needs five engine facts that `ComputableRischDESPDECorrect` proved over
`CPolyG QFunNZ` but whose proofs only ever touch the gcd `g` **abstractly** (through an `Associated (toPolyG
g) (gcd …)` hypothesis and the generic `cgcdExtG`/`cdivG`/`cdvdG` API). We re-derive them once, generically
over `{α} [CField α] [CFieldSpec α]`, so they apply at `QFunNZG ℚ` (and any level). Each reuses the already
generic `toPolyG_cgcdExtG_dvd` / `toPolyG_cdivG_exact` / `dvd_of_cdvdG` / `spde_const_base` /
`spde_step_glue`. -/

/-- **The divided coefficients' Euclidean gcd is a unit** (generic): if `g ~ gcd(a, b)` (`g ≠ 0`) with the
exact divisions `toPolyG ad · toPolyG g = toPolyG a`, `toPolyG bd · toPolyG g = toPolyG b`, then under the
Euclidean termination `cgcdTerminatesG fuel bd ad` the gcd `G = (cgcdExtG fuel bd ad).1` is a unit of
`(CFieldSpec.K α)[X]`. Generic mirror of `cgcdExtG_isUnit_of_divided` (taking `g` abstractly, so
carrier-agnostic). -/
theorem cgcdExtG_isUnit_of_divided_gen {α : Type*} [CField α] [CFieldSpec α] (fuel : ℕ)
    (a b ad bd g : CPolyG α) (hgne : toPolyG g ≠ 0)
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b)))
    (hdiva : toPolyG ad * toPolyG g = toPolyG a)
    (hdivb : toPolyG bd * toPolyG g = toPolyG b)
    (hterm : cgcdTerminatesG fuel bd ad) :
    IsUnit (toPolyG (cgcdExtG fuel bd ad).1) := by
  obtain ⟨hGbd, hGad⟩ := toPolyG_cgcdExtG_dvd fuel bd ad hterm
  set G := toPolyG (cgcdExtG fuel bd ad).1 with hGdef
  have hGg_a : G * toPolyG g ∣ toPolyG a := by rw [← hdiva]; exact mul_dvd_mul_right hGad _
  have hGg_b : G * toPolyG g ∣ toPolyG b := by rw [← hdivb]; exact mul_dvd_mul_right hGbd _
  have hGg_gcd : G * toPolyG g ∣ gcd (toPolyG a) (toPolyG b) := dvd_gcd hGg_a hGg_b
  have hGg_g : G * toPolyG g ∣ toPolyG g := hGg_gcd.trans hgassoc.symm.dvd
  obtain ⟨k, hk⟩ := hGg_g
  have hcancel : toPolyG g * 1 = toPolyG g * (G * k) := by rw [mul_one]; nth_rewrite 1 [hk]; ring
  have hG1 : G ∣ 1 := ⟨k, mul_left_cancel₀ hgne hcancel⟩
  exact isUnit_of_dvd_one hG1

/-- **The divided coefficients' Euclidean gcd is the constant `C (leadingCoeff)`** (generic): the unit gcd
`G = (cgcdExtG fuel bd ad).1` of `cgcdExtG_isUnit_of_divided_gen` has degree `0`, so `toPolyG G = C (toK
(cleadG G))`. Generic mirror of `toPolyG_cgcdExtG_eq_C_of_divided`. -/
theorem toPolyG_cgcdExtG_eq_C_of_divided_gen {α : Type*} [CField α] [CFieldSpec α] (fuel : ℕ)
    (a b ad bd g : CPolyG α) (hgne : toPolyG g ≠ 0)
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b)))
    (hdiva : toPolyG ad * toPolyG g = toPolyG a)
    (hdivb : toPolyG bd * toPolyG g = toPolyG b)
    (hterm : cgcdTerminatesG fuel bd ad) :
    toPolyG (cgcdExtG fuel bd ad).1
      = Polynomial.C (CFieldSpec.toK (cleadG (cgcdExtG fuel bd ad).1)) := by
  have hunit := cgcdExtG_isUnit_of_divided_gen fuel a b ad bd g hgne hgassoc hdiva hdivb hterm
  have hnd : (toPolyG (cgcdExtG fuel bd ad).1).natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit hunit
  rw [toK_cleadG_eq_leadingCoeff, Polynomial.leadingCoeff, hnd]
  exact Polynomial.eq_C_of_natDegree_eq_zero hnd

/-- **The divided coefficients' Euclidean gcd has nonzero leading coefficient** (generic): a unit is
nonzero, so `toK (cleadG G) ≠ 0`. Generic mirror of `toK_cleadG_cgcdExtG_ne_zero_of_divided`. -/
theorem toK_cleadG_cgcdExtG_ne_zero_of_divided_gen {α : Type*} [CField α] [CFieldSpec α] (fuel : ℕ)
    (a b ad bd g : CPolyG α) (hgne : toPolyG g ≠ 0)
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b)))
    (hdiva : toPolyG ad * toPolyG g = toPolyG a)
    (hdivb : toPolyG bd * toPolyG g = toPolyG b)
    (hterm : cgcdTerminatesG fuel bd ad) :
    CFieldSpec.toK (cleadG (cgcdExtG fuel bd ad).1) ≠ 0 := by
  have hunit := cgcdExtG_isUnit_of_divided_gen fuel a b ad bd g hgne hgassoc hdiva hdivb hterm
  rw [toK_cleadG_eq_leadingCoeff]
  exact Polynomial.leadingCoeff_ne_zero.mpr hunit.ne_zero

/-- **The `a`-exact-division witness** (generic) `toPolyG (cdivG fuel a g) · toPolyG g = toPolyG a` from
`g ~ gcd(a, b)` (`g ∣ a`), `g ≠ 0`, and the fuel bound. Generic mirror of `cdivFF_a_exact_of_gcd`
(`cdivFF := cdivG`). -/
theorem cdivG_a_exact_of_gcd {α : Type*} [CField α] [CFieldSpec α] (fuel : ℕ) (a b g : CPolyG α)
    (hg0 : cnormG g ≠ []) (hfuel : (cnormG a : List α).length ≤ fuel)
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b))) :
    toPolyG (cdivG fuel a g) * toPolyG g = toPolyG a := by
  have hgdvd : toPolyG g ∣ toPolyG a := hgassoc.dvd.trans (gcd_dvd_left _ _)
  exact toPolyG_cdivG_exact fuel a g hg0 hfuel hgdvd

/-- **The `b`-exact-division witness** (generic) `toPolyG (cdivG fuel b g) · toPolyG g = toPolyG b` from
`g ~ gcd(a, b)` (`g ∣ b`). Generic mirror of `cdivFF_b_exact_of_gcd`. -/
theorem cdivG_b_exact_of_gcd {α : Type*} [CField α] [CFieldSpec α] (fuel : ℕ) (a b g : CPolyG α)
    (hg0 : cnormG g ≠ []) (hfuel : (cnormG b : List α).length ≤ fuel)
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b))) :
    toPolyG (cdivG fuel b g) * toPolyG g = toPolyG b := by
  have hgdvd : toPolyG g ∣ toPolyG b := hgassoc.dvd.trans (gcd_dvd_right _ _)
  exact toPolyG_cdivG_exact fuel b g hg0 hfuel hgdvd

/-- **The `c`-exact-division witness** (generic) `toPolyG (cdivG fuel c g) · toPolyG g = toPolyG c` from the
`cdvdG fuel g c = true` branch (`g ∣ c`). Generic mirror of `cdivFF_c_exact_of_cdvdG`. -/
theorem cdivG_c_exact_of_cdvdG {α : Type*} [CField α] [CFieldSpec α] (fuel : ℕ) (c g : CPolyG α)
    (hg0 : cnormG g ≠ []) (hfuel : (cnormG c : List α).length ≤ fuel)
    (hdvd : cdvdG fuel g c = true) :
    toPolyG (cdivG fuel c g) * toPolyG g = toPolyG c := by
  have hgdvd : toPolyG g ∣ toPolyG c := dvd_of_cdvdG fuel g c hg0 hdvd
  exact toPolyG_cdivG_exact fuel c g hg0 hfuel hgdvd

/-- **One `cSPDEG` peel's cleared lifting** (generic) at `D = cmonomialDeriv Dt = implicitDeriv (toPolyG
Dt)`. Given the divided coefficients `ad, bd, cd`, the Bézout cofactors `r, z` with the certificate
`toPolyG bd · toPolyG r + toPolyG ad · toPolyG z = toPolyG cd`, and any `h` solving the reduced equation,
the reconstruction `q = ad·h + r` solves `ad·D(q) + bd·q = cd` over `(CFieldSpec.K α)[X]`. Generic mirror of
`cSPDE_peel_cleared` (carrier-agnostic, via `spde_step_glue`). -/
theorem cSPDE_peel_cleared_gen {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    (Dt ad bd cd r z h : CPolyG α)
    (hbez : toPolyG bd * toPolyG r + toPolyG ad * toPolyG z = toPolyG cd)
    (hred : toPolyG ad * Differential.implicitDeriv (toPolyG Dt) (toPolyG h)
        + (toPolyG bd + Differential.implicitDeriv (toPolyG Dt) (toPolyG ad)) * toPolyG h
      = toPolyG z - Differential.implicitDeriv (toPolyG Dt) (toPolyG r)) :
    toPolyG ad * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG ad h) r))
        + toPolyG bd * toPolyG (caddG (cmulG ad h) r)
      = toPolyG cd := by
  rw [toPolyG_caddG, toPolyG_cmulG]
  exact spde_step_glue (Differential.implicitDeriv (toPolyG Dt))
    (toPolyG ad) (toPolyG bd) (toPolyG cd) (toPolyG r) (toPolyG z) (toPolyG h) hbez hred

/-! ### §6.4 — the generic SPDE certificate, lifting, transparent inputs and discharge (any tower level)

The §6.4 cleared-lifting *engine* is gcd-agnostic — the gcd `g = cgcdFFCore fuel a b` is `set`-abstracted and
read only through the certificate's `Associated (toPolyG g) (gcd …)` clause. We therefore re-state the whole
§6.4 chain generically over `{α} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]` (the §6.5
non-cancellation identity transports the same way). The QFunNZ-specific helpers are replaced by the `_gen`
versions above; the gcd-correctness discharge enters only in `cSPDECleared_of_inputs_gen` through the per-call
`Associated` clause (supplied at `QFunNZG ℚ` by `associated_toPolyG_cgcdFFCore`, NOT `cgcdFF`). -/

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-- **Generic per-level certificate predicate for `cSPDEG`** `cSPDEGClearedGen Dt fuel a b c n`: the
carrier-generic mirror of `cSPDEGCleared`, with `g = cgcdFFCore fuel a b` and the divided coefficients
`ad = a/g`, `bd = b/g`, `cd = c/g` via `cdivG`. At each non-base level (`n ≥ 0`, `g ∣ c`, `deg(ad) > 0`) it
asserts the three exact-division witnesses, the nonzero-leading `toPolyG ad ≠ 0`, and the Bézout
`toPolyG bd·toPolyG r + toPolyG ad·toPolyG z = toPolyG cd`, then recurses on the reduced equation. Identical
shape to `cSPDEGCleared` (only the carrier is generic). -/
def cSPDEGClearedGen [CFracGcdCore α] (Dt : CPolyG α) :
    ℕ → (a b c : CPolyG α) → (n : ℤ) → Prop
  | 0, _, _, _, _ => True
  | fuel + 1, a, b, c, n =>
    if n < 0 then True
    else
      let g := CFracGcdCore.cgcdFFCore fuel a b
      if cdvdG fuel g c then
        let ad := cdivG fuel a g
        let bd := cdivG fuel b g
        let cd := cdivG fuel c g
        (toPolyG ad * toPolyG g = toPolyG a) ∧ (toPolyG bd * toPolyG g = toPolyG b)
          ∧ (toPolyG cd * toPolyG g = toPolyG c)
          ∧ (toPolyG ad ≠ 0)
          ∧ (if cdegG ad = 0 then True
             else
               let rz := cdiophantineG fuel bd ad cd
               (toPolyG bd * toPolyG rz.1 + toPolyG ad * toPolyG rz.2 = toPolyG cd)
                 ∧ cSPDEGClearedGen Dt fuel ad (caddG bd (cmonomialDeriv Dt ad))
                     (csubG rz.2 (cmonomialDeriv Dt rz.1)) (n - (cdegG ad : ℤ)))
      else True

/-- **The full recursive generic `cSPDEG` cleared lifting**: under `cSPDEGClearedGen`, if `cSPDEG Dt fuel a b
c n = some (b̄, c̄, m, α, β)` then for every `h` solving the reduced `D(h) + b̄·h = c̄` (`D = implicitDeriv
(toPolyG Dt)`), the reconstruction `q = α·h + β` solves the original `a·D(q) + b·q = c` over `(CFieldSpec.K
α)[X]`. The carrier-generic mirror of `cSPDEG_cleared_lifting` (the gcd is `set`-abstracted, the helpers
`spde_const_base`/`cSPDE_peel_cleared_gen` are gcd-agnostic). -/
theorem cSPDEG_cleared_lifting_gen [CFracGcdCore α] (Dt : CPolyG α) :
    ∀ (fuel : ℕ) (a b c : CPolyG α) (n : ℤ) (bbar cbar : CPolyG α) (m : ℤ)
      (α' β : CPolyG α),
      cSPDEG Dt fuel a b c n = some (bbar, cbar, m, α', β) →
      cSPDEGClearedGen Dt fuel a b c n →
      ∀ h : CPolyG α,
        Differential.implicitDeriv (toPolyG Dt) (toPolyG h) + toPolyG bbar * toPolyG h = toPolyG cbar →
        toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α' h) β))
            + toPolyG b * toPolyG (caddG (cmulG α' h) β)
          = toPolyG c := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b c n bbar cbar m α' β hspde _ h _
    rw [cSPDEG] at hspde
    exact absurd hspde (by simp)
  | succ fuel ih =>
    intro a b c n bbar cbar m α' β hspde hcert h hh
    rw [cSPDEG] at hspde
    by_cases hn : n < 0
    · rw [if_pos hn] at hspde
      by_cases hc0 : cisZeroG c = true
      · rw [if_pos hc0, Option.some.injEq] at hspde
        simp only [Prod.mk.injEq] at hspde
        obtain ⟨_hbbar, _hcbar, _, hα, hβ⟩ := hspde
        subst hα; subst hβ
        have hcc : toPolyG c = 0 := (cisZeroG_iff c).mp hc0
        rw [toPolyG_caddG, toPolyG_cmulG, toPolyG_nil, zero_mul, add_zero, map_zero, mul_zero,
          mul_zero, add_zero, hcc]
      · rw [if_neg hc0] at hspde
        exact absurd hspde (by simp)
    · rw [if_neg hn] at hspde
      rw [cSPDEGClearedGen] at hcert
      simp only [if_neg hn] at hcert
      set g := CFracGcdCore.cgcdFFCore fuel a b with hg
      by_cases hdvd : cdvdG fuel g c = true
      · rw [if_pos hdvd] at hspde hcert
        set ad := cdivG fuel a g with had
        set bd := cdivG fuel b g with hbd
        set cd := cdivG fuel c g with hcd
        obtain ⟨hdiva, hdivb, hdivc, hadne, hcertrest⟩ := hcert
        by_cases hdeg : cdegG ad = 0
        · rw [if_pos hdeg, Option.some.injEq] at hspde
          simp only [Prod.mk.injEq] at hspde
          obtain ⟨hbbar, hcbar, _, hα, hβ⟩ := hspde
          subst hα; subst hβ
          rw [toPolyG_caddG, toPolyG_cmulG, toPolyG_nil, add_zero]
          have hone : toPolyG ([CField.one] : CPolyG α) = 1 := by
            rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]
          rw [hone, one_mul]
          set a0 : CFieldSpec.K α := CFieldSpec.toK (cleadG ad) with ha0def
          have ha0ne : a0 ≠ 0 := by
            rw [ha0def, toK_cleadG_eq_leadingCoeff]
            exact Polynomial.leadingCoeff_ne_zero.mpr hadne
          have hadC : toPolyG ad = Polynomial.C a0 := by
            have hnd : (toPolyG ad).natDegree = 0 := by rw [← cdegG_eq_natDegree, hdeg]
            rw [ha0def, toK_cleadG_eq_leadingCoeff, Polynomial.leadingCoeff, hnd]
            conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hnd]
          rw [← hbbar, ← hcbar, toPolyG_cscaleG, toPolyG_cscaleG, CFieldSpec.toK_inv,
            ← ha0def] at hh
          have hdivided : toPolyG ad * Differential.implicitDeriv (toPolyG Dt) (toPolyG h)
              + toPolyG bd * toPolyG h = toPolyG cd := by
            rw [hadC]
            exact spde_const_base (Differential.implicitDeriv (toPolyG Dt)) a0 (toPolyG bd) (toPolyG cd)
              (toPolyG h) ha0ne hh
          rw [← hdiva, ← hdivb, ← hdivc]
          linear_combination toPolyG g * hdivided
        · rw [if_neg hdeg] at hspde
          rw [if_neg hdeg] at hcertrest
          rcases hrz : cdiophantineG fuel bd ad cd with ⟨r, z⟩
          rw [hrz] at hspde hcertrest
          simp only at hspde hcertrest
          obtain ⟨hbez', hcertrec⟩ := hcertrest
          rcases hrec : cSPDEG Dt fuel ad (caddG bd (cmonomialDeriv Dt ad))
            (csubG z (cmonomialDeriv Dt r)) (n - (cdegG ad : ℤ))
            with _ | ⟨bbar', cbar', m', α'', β''⟩
          · rw [hrec] at hspde; exact absurd hspde (by simp)
          · rw [hrec, Option.some.injEq] at hspde
            simp only [Prod.mk.injEq] at hspde
            obtain ⟨hbbar, hcbar, _hm, hα, hβ⟩ := hspde
            rw [← hbbar] at hh; rw [← hcbar] at hh
            have hihrec := ih ad (caddG bd (cmonomialDeriv Dt ad))
              (csubG z (cmonomialDeriv Dt r)) (n - (cdegG ad : ℤ))
              bbar' cbar' m' α'' β'' hrec hcertrec h hh
            have hred : toPolyG ad
                  * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α'' h) β''))
                + (toPolyG bd + Differential.implicitDeriv (toPolyG Dt) (toPolyG ad))
                    * toPolyG (caddG (cmulG α'' h) β'')
                = toPolyG z - Differential.implicitDeriv (toPolyG Dt) (toPolyG r) := by
              simp only [toPolyG_caddG, toPolyG_cmonomialDeriv, toPolyG_csubG] at hihrec ⊢
              linear_combination hihrec
            subst hα; subst hβ
            have hpeel := cSPDE_peel_cleared_gen Dt ad bd cd r z (caddG (cmulG α'' h) β'') hbez' hred
            have hqeq : toPolyG (caddG (cmulG (cmulG ad α'') h) (caddG (cmulG ad β'') r))
                = toPolyG (caddG (cmulG ad (caddG (cmulG α'' h) β'')) r) := by
              simp only [toPolyG_caddG, toPolyG_cmulG]; ring
            rw [hqeq, ← hdiva, ← hdivb, ← hdivc]
            linear_combination toPolyG g * hpeel
      · rw [if_neg hdvd] at hspde
        exact absurd hspde (by simp)

/-- **Generic transparent per-level input predicate for the `cSPDEGClearedGen` discharge**
`CSPDEGClearedInputsGen Dt fuel a b c n`, mirroring `cSPDEG`'s recursion. At each non-base level (`n ≥ 0`,
`cdvdG fuel g c`), with `g = cgcdFFCore fuel a b`, `ad = a/g`, `bd = b/g`: the gcd is nonzero (`cnormG g ≠
[]`) and `Associated` to `gcd(toPolyG a, toPolyG b)`, the fuel bounds each exact division, and `a ≠ 0`. In the
recursion branch (`cdegG ad ≠ 0`) additionally the Euclidean termination `cgcdTerminatesG fuel bd ad` and
`CSPDEGClearedInputsGen` on the reduced equation. Carrier-generic mirror of `CSPDEGClearedInputs`. -/
def CSPDEGClearedInputsGen [CFracGcdCore α] (Dt : CPolyG α) :
    ℕ → (a b c : CPolyG α) → (n : ℤ) → Prop
  | 0, _, _, _, _ => True
  | fuel + 1, a, b, c, n =>
    if n < 0 then True
    else
      let g := CFracGcdCore.cgcdFFCore fuel a b
      if cdvdG fuel g c then
        let ad := cdivG fuel a g
        let bd := cdivG fuel b g
        (cnormG g ≠ []) ∧ Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b))
          ∧ ((cnormG a : List α).length ≤ fuel)
          ∧ ((cnormG b : List α).length ≤ fuel)
          ∧ ((cnormG c : List α).length ≤ fuel)
          ∧ (cnormG a ≠ [])
          ∧ (if cdegG ad = 0 then True
             else
               let rz := cdiophantineG fuel bd ad (cdivG fuel c g)
               cgcdTerminatesG fuel bd ad
                 ∧ CSPDEGClearedInputsGen Dt fuel ad (caddG bd (cmonomialDeriv Dt ad))
                     (csubG rz.2 (cmonomialDeriv Dt rz.1)) (n - (cdegG ad : ℤ)))
      else True

omit [CDiffFieldSpec α] in
/-- **Generic `cSPDEGClearedGen` discharged from transparent inputs**: `CSPDEGClearedInputsGen Dt fuel a b c
n` implies the per-level certificate `cSPDEGClearedGen Dt fuel a b c n`, over any tower level. By fuel
induction: the three exact-division witnesses from `cdivG_a`/`cdivG_b`/`cdivG_c` exactness, the nonzero-`ad`
clause from `ad·g = a` with `a ≠ 0`, and (recursion branch) the Bézout clause from `toPolyG_cdiophantineG`
with the divided-coefficient gcd shown constant by `toPolyG_cgcdExtG_eq_C_of_divided_gen`. Carrier-generic
mirror of `cSPDEGCleared_of_inputs`. -/
theorem cSPDEGCleared_of_inputs_gen [CFracGcdCore α] (Dt : CPolyG α) :
    ∀ (fuel : ℕ) (a b c : CPolyG α) (n : ℤ),
      CSPDEGClearedInputsGen Dt fuel a b c n → cSPDEGClearedGen Dt fuel a b c n := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b c n _
    rw [cSPDEGClearedGen]; trivial
  | succ fuel ih =>
    intro a b c n hin
    rw [cSPDEGClearedGen]
    rw [CSPDEGClearedInputsGen] at hin
    by_cases hn : n < 0
    · rw [if_pos hn]; trivial
    · rw [if_neg hn] at hin ⊢
      set g := CFracGcdCore.cgcdFFCore fuel a b with hg
      by_cases hdvd : cdvdG fuel g c = true
      · rw [if_pos hdvd] at hin ⊢
        set ad := cdivG fuel a g with had
        set bd := cdivG fuel b g with hbd
        obtain ⟨hg0, hgassoc, hfa, hfb, hfc, ha0, hrest⟩ := hin
        have hdiva : toPolyG ad * toPolyG g = toPolyG a :=
          cdivG_a_exact_of_gcd fuel a b g hg0 hfa hgassoc
        have hdivb : toPolyG bd * toPolyG g = toPolyG b :=
          cdivG_b_exact_of_gcd fuel a b g hg0 hfb hgassoc
        have hdivc : toPolyG (cdivG fuel c g) * toPolyG g = toPolyG c :=
          cdivG_c_exact_of_cdvdG fuel c g hg0 hfc hdvd
        have hane : toPolyG a ≠ 0 := fun h => ha0 ((cnormG_eq_nil_iff a).mpr h)
        have hadne : toPolyG ad ≠ 0 := by
          intro h; apply hane; rw [← hdiva, h, zero_mul]
        have hgne : toPolyG g ≠ 0 := fun h => hg0 ((cnormG_eq_nil_iff g).mpr h)
        refine ⟨hdiva, hdivb, hdivc, hadne, ?_⟩
        by_cases hdeg : cdegG ad = 0
        · rw [if_pos hdeg] at hrest ⊢; trivial
        · rw [if_neg hdeg] at hrest ⊢
          obtain ⟨hterm, hrec⟩ := hrest
          have hadnil : cnormG ad ≠ [] := fun h => hadne ((cnormG_eq_nil_iff ad).mp h)
          have hgC := toPolyG_cgcdExtG_eq_C_of_divided_gen fuel a b ad bd g hgne hgassoc hdiva hdivb hterm
          have hgCne := toK_cleadG_cgcdExtG_ne_zero_of_divided_gen fuel a b ad bd g hgne hgassoc hdiva
            hdivb hterm
          have hbez := toPolyG_cdiophantineG fuel bd ad (cdivG fuel c g) hadnil hgC hgCne
          refine ⟨?_, ih ad (caddG bd (cmonomialDeriv Dt ad))
            (csubG (cdiophantineG fuel bd ad (cdivG fuel c g)).2
              (cmonomialDeriv Dt (cdiophantineG fuel bd ad (cdivG fuel c g)).1))
            (n - (cdegG ad : ℤ)) hrec⟩
          linear_combination hbez
      · rw [if_neg (by simpa using hdvd : ¬ cdvdG fuel g c = true)] at hin ⊢; trivial

/-! ### §6.5 — the generic non-cancellation cleared identity `D(q) + b·q = c` (any tower level)

`cPolyRischDENoCancelG` has **no gcd** anywhere (only `cdegG`/`cleadG`/`cmonomialDeriv`/`cshiftG`/`csub/mul/
addG`), so its cleared-identity proof transports verbatim with the carrier generic. Carrier-generic mirror of
`cPolyRischDENoCancelG_cleared_identity`. -/

/-- **`cPolyRischDENoCancelG` satisfies the cleared RDE identity `D(q) + b·q = c`** (generic, all inputs)
over `(CFieldSpec.K α)[X]`, whenever the non-cancellation solve **succeeds**. If `cPolyRischDENoCancelG Dt
fuel b c n = some q` then `implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG b * toPolyG q = toPolyG c`.
Carrier-generic mirror of `cPolyRischDENoCancelG_cleared_identity` (the loop body has no gcd). -/
theorem cPolyRischDENoCancelG_cleared_identity_gen (Dt b : CPolyG α) :
    ∀ (fuel : ℕ) (c : CPolyG α) (n : ℤ) (q : CPolyG α),
      cPolyRischDENoCancelG Dt fuel b c n = some q →
        Differential.implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG b * toPolyG q = toPolyG c := by
  intro fuel
  induction fuel with
  | zero =>
    intro c n q hq
    rw [cPolyRischDENoCancelG] at hq
    exact absurd hq (by simp)
  | succ fuel ih =>
    intro c n q hq
    rw [cPolyRischDENoCancelG] at hq
    by_cases hc : cisZeroG c = true
    · rw [if_pos hc, Option.some.injEq] at hq
      subst hq
      have hc0 : toPolyG c = 0 := (cisZeroG_iff c).mp hc
      rw [toPolyG_nil, map_zero, mul_zero, add_zero, hc0]
    · rw [if_neg hc] at hq
      set m : ℤ := (cdegG c : ℤ) - (cdegG b : ℤ) with hm
      by_cases hguard : n < 0 ∨ m < 0 ∨ m > n
      · rw [if_pos hguard] at hq
        exact absurd hq (by simp)
      · rw [if_neg hguard] at hq
        simp only at hq
        set coeff := CField.div (cleadG c) (cleadG b) with hcoeff
        set p := cshiftG m.toNat [coeff] with hp
        set c' := csubG (csubG c (cmonomialDeriv Dt p)) (cmulG b p) with hc'
        rcases hrec : cPolyRischDENoCancelG Dt fuel b c' (m - 1) with _ | qrec
        · rw [hrec] at hq; exact absurd hq (by simp)
        · rw [hrec, Option.some.injEq] at hq
          have ihrec := ih c' (m - 1) qrec hrec
          subst hq
          rw [toPolyG_caddG, map_add, mul_add]
          have hc'eq : toPolyG c' = toPolyG c
              - Differential.implicitDeriv (toPolyG Dt) (toPolyG p) - toPolyG b * toPolyG p := by
            rw [hc', toPolyG_csubG, toPolyG_csubG, toPolyG_cmonomialDeriv, toPolyG_cmulG]
          rw [hc'eq] at ihrec
          linear_combination ihrec

/-! ### §6.4-§6.5 — the generic polynomial-stage spine under transparent inputs (any tower level) -/

/-- **The generic §6.4 `cSPDEG` cleared lifting under transparent inputs**: `cSPDEG_cleared_lifting_gen` with
its `cSPDEGClearedGen` gate discharged by `cSPDEGCleared_of_inputs_gen`. Carrier-generic. -/
theorem cSPDEG_cleared_lifting_of_inputs_gen [CFracGcdCore α] (Dt : CPolyG α) (fuel : ℕ)
    (a b c : CPolyG α) (n : ℤ) (bbar cbar : CPolyG α) (m : ℤ) (α' β : CPolyG α)
    (hspde : cSPDEG Dt fuel a b c n = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGen Dt fuel a b c n) (h : CPolyG α)
    (hh : Differential.implicitDeriv (toPolyG Dt) (toPolyG h) + toPolyG bbar * toPolyG h
      = toPolyG cbar) :
    toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α' h) β))
        + toPolyG b * toPolyG (caddG (cmulG α' h) β)
      = toPolyG c :=
  cSPDEG_cleared_lifting_gen Dt fuel a b c n bbar cbar m α' β hspde
    (cSPDEGCleared_of_inputs_gen Dt fuel a b c n hin) h hh

/-- **The generic §6.4-§6.5 polynomial-stage spine under transparent inputs**: if `cSPDEG Dt fuel a b c n =
some (b̄, c̄, m, α', β)` (under transparent `CSPDEGClearedInputsGen`) and `cPolyRischDENoCancelG Dt fuel b̄ c̄
m = some v`, then `q = α'·v + β` solves the original `a·D(q) + b·q = c` over `(CFieldSpec.K α)[X]`.
Carrier-generic mirror of `cSPDEG_polyRischDENoCancel_cleared_of_inputs`. -/
theorem cSPDEG_polyRischDENoCancel_cleared_of_inputs_gen [CFracGcdCore α] (Dt : CPolyG α) (fuel : ℕ)
    (a b c : CPolyG α) (n : ℤ) (bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α)
    (hspde : cSPDEG Dt fuel a b c n = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGen Dt fuel a b c n)
    (hpoly : cPolyRischDENoCancelG Dt fuel bbar cbar m = some v) :
    toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α' v) β))
        + toPolyG b * toPolyG (caddG (cmulG α' v) β)
      = toPolyG c :=
  cSPDEG_cleared_lifting_of_inputs_gen Dt fuel a b c n bbar cbar m α' β hspde hin v
    (cPolyRischDENoCancelG_cleared_identity_gen Dt bbar fuel cbar m v hpoly)

/-- **The generic §6.4-§6.5 spine instantiated at the §6.3 degree bound** (carrier-generic): the spine holds
for every `n`, in particular at `n = cRdeBoundDegreeG Dt fuel a b c`. Carrier-generic mirror of
`cSPDEG_polyRischDENoCancel_cleared_at_boundDegree`. -/
theorem cSPDEG_polyRischDENoCancel_cleared_at_boundDegree_gen [CFracGcdCore α] (Dt : CPolyG α)
    (fuel : ℕ) (a b c : CPolyG α) (bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α)
    (hspde : cSPDEG Dt fuel a b c (cRdeBoundDegreeG Dt fuel a b c : ℤ) = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGen Dt fuel a b c (cRdeBoundDegreeG Dt fuel a b c : ℤ))
    (hpoly : cPolyRischDENoCancelG Dt fuel bbar cbar m = some v) :
    toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α' v) β))
        + toPolyG b * toPolyG (caddG (cmulG α' v) β)
      = toPolyG c :=
  cSPDEG_polyRischDENoCancel_cleared_of_inputs_gen Dt fuel a b c
    (cRdeBoundDegreeG Dt fuel a b c : ℤ) bbar cbar m α' β v hspde hin hpoly

/-! ### §6.2 — the generic normal-denominator cleared lifting and special-denominator primitive case -/

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Generic exact-division reorientation** `toPolyG (cdivG fuel p q) · toPolyG q = toPolyG p` from `toPolyG
q ∣ toPolyG p` (nonzero divisor, fuel bound). Carrier-generic mirror of `toPolyG_cdivG_exact_mul`
(reorienting the already-generic `toPolyG_cdivG_exact`). -/
theorem toPolyG_cdivG_exact_mul_gen [CFracGcdCore α] (fuel : ℕ) (p q : CPolyG α)
    (hq0 : cnormG q ≠ []) (hfuel : (cnormG p : List α).length ≤ fuel)
    (hQdvd : toPolyG q ∣ toPolyG p) :
    toPolyG (cdivG fuel p q) * toPolyG q = toPolyG p :=
  toPolyG_cdivG_exact fuel p q hq0 hfuel hQdvd

/-! #### ★ `cValuationG`-correctness — the `ν_p` trial-division divides and is sharp (the §6.2 keystone) -/

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **`cValuationG` divides** (carrier-generic): `toPolyG p ^ (cValuationG fuel p x) ∣ toPolyG x` — the
`ν_p` trial-division power always divides `x`. By `fuel`-induction on the `cValuationG.go` recursion: each
step divides out one exact factor of `p` (`toPolyG_cdivG_exact`), so `p^(1+k) ∣ p·(x/p) = x` from the
inductive `p^k ∣ x/p`. The `dvd` half of the §6.2 valuation correctness; no regularity needed. -/
theorem toPolyG_pow_cValuationG_dvd (fuel : ℕ) (p x : CPolyG α) :
    toPolyG p ^ (cValuationG fuel p x) ∣ toPolyG x := by
  rw [cValuationG]
  induction fuel generalizing x with
  | zero => rw [cValuationG.go, pow_zero]; exact one_dvd _
  | succ fuel ih =>
    rw [cValuationG.go]
    by_cases hx : cisZeroG x = true
    · simp only [if_pos hx, pow_zero]; exact one_dvd _
    · rw [if_neg hx]
      by_cases hp : cdegG p = 0
      · simp only [if_pos hp, pow_zero]; exact one_dvd _
      · rw [if_neg hp]
        by_cases hdvd : cdvdG fuel p x = true
        · rw [if_pos hdvd]
          -- `p ∣ x` exactly: `toPolyG x = toPolyG(x/p)·toPolyG p` (no fuel bound — the remainder is `0`).
          have hpne : cnormG p ≠ [] := by
            intro hpe; exact hp (by rw [cdegG, hpe]; rfl)
          have hrem0 : toPolyG (cmodG fuel x p) = 0 := (cdvdG_iff fuel p x).mp hdvd
          have hid := toPolyG_cdivmodG' fuel x p hpne
          rw [show (cdivmodG fuel x p).2 = cmodG fuel x p from rfl, hrem0, add_zero,
            show (cdivmodG fuel x p).1 = cdivG fuel x p from rfl] at hid
          -- IH: `p^k ∣ x/p`; multiply by `p` to get `p^(1+k) ∣ (x/p)·p = x`.
          have hih := ih (cdivG fuel x p)
          rw [add_comm, pow_add, pow_one, hid]
          exact mul_dvd_mul hih dvd_rfl
        · rw [if_neg (by simpa using hdvd), pow_zero]; exact one_dvd _

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **`cdvdG = false` refutes divisibility** (carrier-generic, fuel-covered): with `cnormG p ≠ []` and the
fuel covering `x`, `cdvdG fuel p x = false` gives `¬ toPolyG p ∣ toPolyG x` — the converse direction of
`dvd_of_cdvdG`. Contrapositive of `toPolyG_cmodG_eq_zero_of_dvd` + `cdvdG_iff`. -/
theorem not_dvd_of_cdvdG_false [CFracGcdCore α] (fuel : ℕ) (p x : CPolyG α)
    (hpne : cnormG p ≠ []) (hfuel : (cnormG x : List α).length ≤ fuel)
    (hdvd : cdvdG fuel p x = false) : ¬ toPolyG p ∣ toPolyG x := by
  intro hpx
  have hrem0 : toPolyG (cmodG fuel x p) = 0 := toPolyG_cmodG_eq_zero_of_dvd fuel x p hpne hfuel hpx
  rw [← cdvdG_iff fuel p x] at hrem0
  rw [hrem0] at hdvd
  exact absurd hdvd (by decide)

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **`cValuationG` is sharp** (carrier-generic, fuel-covered): for a non-constant `p` (`cdegG p ≠ 0`) and a
nonzero `x` (`toPolyG x ≠ 0`) with the fuel strictly covering `x` (`(cnormG x).length < fuel`, so the inner
`cdvdG`/`cdivG` calls — each at one less fuel — are themselves fuel-covered), `¬ toPolyG p ^ (cValuationG fuel
p x + 1) ∣ toPolyG x` — the trial-division stops exactly at the multiplicity (one more power does NOT divide).
By `fuel`-induction mirroring `cValuationG.go`: the terminating non-dividing step refutes `p ∣ remainder`
(`not_dvd_of_cdvdG_false`); each peeling step cancels one nonzero `p` in the integral domain `(CFieldSpec.K
α)[X]` to descend to the inductive hypothesis on `x/p` (degree strictly drops on each exact division by a
non-constant `p`). The strict bound is the §6.2 valuation `sharp`ness half. -/
theorem cValuationG_sharp [CFracGcdCore α] (fuel : ℕ) (p x : CPolyG α)
    (hp : cdegG p ≠ 0) (hx0 : toPolyG x ≠ 0) (hfuel : (cnormG x : List α).length < fuel) :
    ¬ toPolyG p ^ (cValuationG fuel p x + 1) ∣ toPolyG x := by
  have hpne : cnormG p ≠ [] := fun hpe => hp (by rw [cdegG, hpe]; rfl)
  have hp0 : toPolyG p ≠ 0 := fun h => hpne (by rw [cnormG_eq_nil_iff]; exact h)
  have hpdeg : 0 < (toPolyG p).natDegree := by rw [← cdegG_eq_natDegree]; omega
  rw [cValuationG]
  induction fuel generalizing x with
  | zero =>
    -- fuel `0` cannot strictly cover any `x` (`(cnormG x).length < 0` is impossible).
    exact absurd hfuel (by omega)
  | succ fuel ih =>
    rw [cValuationG.go]
    have hxne : cisZeroG x ≠ true := fun h => hx0 ((cisZeroG_iff x).mp h)
    have hxlen : (cnormG x : List α).length = (toPolyG x).natDegree + 1 :=
      length_cnormG_of_ne x (fun he => hx0 (by rw [← toPolyG_cnormG, he, toPolyG_nil]))
    rw [if_neg hxne, if_neg hp]
    by_cases hdvd : cdvdG fuel p x = true
    · rw [if_pos hdvd]
      -- `p ∣ x` exactly; `x = (x/p)·p`, descend to `x/p` and cancel one `p`.
      have hrem0 : toPolyG (cmodG fuel x p) = 0 := (cdvdG_iff fuel p x).mp hdvd
      have hid : toPolyG x = toPolyG (cdivG fuel x p) * toPolyG p := by
        have h := toPolyG_cdivmodG' fuel x p hpne
        rw [show (cdivmodG fuel x p).2 = cmodG fuel x p from rfl, hrem0, add_zero,
          show (cdivmodG fuel x p).1 = cdivG fuel x p from rfl] at h
        exact h
      have hq0 : toPolyG (cdivG fuel x p) ≠ 0 := by
        intro h; apply hx0; rw [hid, h, zero_mul]
      have hqne : cnormG (cdivG fuel x p) ≠ [] := fun he => hq0 (by rw [cnormG_eq_nil_iff] at he; exact he)
      have hdeg : (toPolyG (cdivG fuel x p)).natDegree < (toPolyG x).natDegree := by
        rw [hid, Polynomial.natDegree_mul hq0 hp0]; omega
      have hfuelq : (cnormG (cdivG fuel x p) : List α).length < fuel := by
        rw [length_cnormG_of_ne _ hqne]; omega
      -- IH refutes `p^(go(x/p)+1) ∣ x/p`; cancel one `p` from a hypothetical `p^(1+go+1) ∣ (x/p)·p`.
      have hihq := ih (cdivG fuel x p) hq0 hfuelq
      intro hcontra
      apply hihq
      rw [hid, show 1 + cValuationG.go p fuel (cdivG fuel x p) + 1
          = (cValuationG.go p fuel (cdivG fuel x p) + 1) + 1 by ring, pow_succ] at hcontra
      exact (mul_dvd_mul_iff_right hp0).mp hcontra
    · rw [if_neg (by simpa using hdvd), zero_add, pow_one]
      exact not_dvd_of_cdvdG_false fuel p x hpne (by omega) (Bool.not_eq_true _ ▸ hdvd)

/-! #### ★ Special-part self-derivative divisibility — `p ∣ D(p)` for the §6.2 monomial special polynomial -/

open Classical in
/-- **The special monomial polynomial divides its own monomial derivative** (`α = QFunNZG ℚ`): under a regular
`cSplitFactorFastG` run on `Dt` (`toPolyG Dt ≠ 0`, fuel covering the `t`-degree), `toPolyG (cSpecialPolyG Dt
fuel) ∣ toPolyG (cmonomialDeriv Dt (cSpecialPolyG Dt fuel))`. The special part `pₛ` of any `IsSplittingFactorizationGen`
is `IsSpecial` (`pₛ ∣ pₛ′`, Bronstein Def 3.4.2); `cSpecialPolyG Dt fuel = cmonicG (cSplitFactorFastG Dt fuel
Dt).2` is `Associated` to that special part, and `IsSpecial` is associate-invariant — so the monic special
polynomial is special, i.e. divides its `implicitDeriv (toPolyG Dt)`-derivative, which `toPolyG_cmonomialDeriv`
identifies with `toPolyG (cmonomialDeriv Dt (cSpecialPolyG Dt fuel))`. The §6.2 `Dp = E·p` premise
(`specialDenominatorSubst_expand`) at the carrier level. -/
theorem toPolyG_cSpecialPolyG_dvd_cmonomialDeriv (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ)
    (hDt : toPolyG Dt ≠ 0) (hdeg : (toPolyG Dt).natDegree ≤ fuel)
    (hreg : CSplitFactorFastGRegularQ Dt fuel Dt) :
    toPolyG (cSpecialPolyG Dt fuel)
      ∣ toPolyG (cmonomialDeriv Dt (cSpecialPolyG Dt fuel)) := by
  letI : Differential (CFieldSpec.K (QFunNZG ℚ))[X] := ⟨Differential.implicitDeriv (toPolyG Dt)⟩
  -- the split-factor special part `pₛ = (cSplitFactorFastG Dt fuel Dt).2` is `IsSpecial`
  have hsplit := cSplitFactorFastG_isSplittingFactorizationGen_qfunNZG Dt fuel Dt hDt hdeg hreg
  have hspecPs : IsSpecial (toPolyG (cSplitFactorFastG Dt fuel Dt).2) := hsplit.2.1
  -- `cSpecialPolyG = cmonicG pₛ` is associated to `pₛ`, so it too is `IsSpecial`
  have hassoc : Associated (toPolyG (cSplitFactorFastG Dt fuel Dt).2)
      (toPolyG (cSpecialPolyG Dt fuel)) := by
    rw [cSpecialPolyG]; exact (associated_toPolyG_cmonicG _).symm
  have hspec : IsSpecial (toPolyG (cSpecialPolyG Dt fuel)) := IsSpecial.of_associated hassoc hspecPs
  -- `IsSpecial p` is `p ∣ p′` with `p′ = implicitDeriv (toPolyG Dt) p = toPolyG (cmonomialDeriv Dt p)`
  rw [toPolyG_cmonomialDeriv]
  exact hspec

/-- **The §6.2 generic normal-denominator cleared lifting through `toPolyG`** (carrier-generic): writing
`dₙ = (cSplitFactorFastG Dt fuel fden).1`, if `cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a, b,
c, h)`, the normal part is nonzero, the two `cdivG`-clearings are exact, and a polynomial `Q` solves the
reduced `a·D(Q) + b·Q = c`, then `y = Q/h` solves the cleared `gden·fden·(D(Q)·h − Q·D(h)) + gden·fnum·Q·h =
gnum·fden·h²` over `(CFieldSpec.K α)[X]`. Carrier-generic mirror of `cRdeNormalDenominatorG_cleared_lift`
(`rdeNormalDenominator_glue` is engine-agnostic, the `B/C` certificates via `toPolyG_cdivG_exact_mul_gen`). -/
theorem cRdeNormalDenominatorG_cleared_lift_gen [CFracGcdCore α] (Dt : CPolyG α) (fuel : ℕ)
    (fnum fden gnum gden a b c h Q : CPolyG α)
    (hres : cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a, b, c, h))
    (hdn : toPolyG (cSplitFactorFastG Dt fuel fden).1 ≠ 0)
    (hfden0 : cnormG fden ≠ []) (hgden0 : cnormG gden ≠ [])
    (hfbB : (cnormG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h)) fden)) :
        List α).length ≤ fuel)
    (hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h)) fden)))
    (hfbC : (cnormG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h) h) gnum) :
        List α).length ≤ fuel)
    (hdvdC : toPolyG gden ∣ toPolyG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h) h) gnum))
    (hred : toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG Q) + toPolyG b * toPolyG Q
      = toPolyG c) :
    toPolyG gden * toPolyG fden
        * (Differential.implicitDeriv (toPolyG Dt) (toPolyG Q) * toPolyG h
            - toPolyG Q * Differential.implicitDeriv (toPolyG Dt) (toPolyG h))
        + toPolyG gden * toPolyG fnum * toPolyG Q * toPolyG h
      = toPolyG gnum * toPolyG fden * toPolyG h ^ 2 := by
  set dn := (cSplitFactorFastG Dt fuel fden).1 with hdndef
  set bNum := csubG (cmulG (cmulG dn h) fnum) (cmulG (cmulG dn (cmonomialDeriv Dt h)) fden) with hbNum
  set cNum := cmulG (cmulG (cmulG dn h) h) gnum with hcNum
  rw [cRdeNormalDenominatorG] at hres
  split at hres
  · rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hres
    obtain ⟨ha, hb, hc, hh⟩ := hres
    rw [hh] at ha hb hc
    have hA : toPolyG a = toPolyG dn * toPolyG h := by rw [← ha, toPolyG_cmulG]
    have hBexact : toPolyG b * toPolyG fden = toPolyG bNum := by
      rw [← hb]; exact toPolyG_cdivG_exact_mul_gen fuel bNum fden hfden0 hfbB hdvdB
    have hBeq : toPolyG bNum = toPolyG a * toPolyG fnum
        - toPolyG dn * Differential.implicitDeriv (toPolyG Dt) (toPolyG h) * toPolyG fden := by
      rw [hbNum, toPolyG_csubG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG,
        toPolyG_cmonomialDeriv, ← ha, toPolyG_cmulG]
    have hCexact : toPolyG c * toPolyG gden = toPolyG cNum := by
      rw [← hc]; exact toPolyG_cdivG_exact_mul_gen fuel cNum gden hgden0 hfbC hdvdC
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

omit [CFieldSpec α] [CDiffFieldSpec α] in
/-- **The generic special-denominator stage is the identity in the primitive regime** (carrier-generic): when
the monic special irreducible `p = cSpecialPolyG Dt fuel` is constant (`cdegG p = 0`), `cRdeSpecialDenominatorG
Dt fuel a b c = (a, b, c, [CField.one])`. Carrier-generic mirror of `cRdeSpecialDenominatorG_primitive_eq`. -/
theorem cRdeSpecialDenominatorG_primitive_eq_gen [CFracGcdCore α] (Dt : CPolyG α) (fuel : ℕ)
    (a b c : CPolyG α) (hp : cdegG (cSpecialPolyG Dt fuel) = 0) :
    cRdeSpecialDenominatorG Dt fuel a b c = (a, b, c, [CField.one]) := by
  rw [cRdeSpecialDenominatorG]
  simp only [hp, if_pos]

/-- **`negn = 0` predicate for the special-denominator stage** `CSpecialDenomNoClearG Dt fuel b c`: the
`ν_p`-shift exponent `negn = (−n).toNat` (`n = min(0, ν_p(c) − min(0, ν_p(b)))`) is `0`, i.e. `ν_p(c) ≥
min(0, ν_p(b))` — the special-denominator reconstruction power `h₁ = pⁿᵉᵍⁿ` is trivial (`[1]`), the
validated hyperexp sub-regime. -/
def CSpecialDenomNoClearG [CFracGcdCore α] (Dt : CPolyG α) (fuel : ℕ) (b c : CPolyG α) : Prop :=
  min (0 : ℤ) ((cValuationG fuel (cSpecialPolyG Dt fuel) c : ℤ)
    - min 0 (cValuationG fuel (cSpecialPolyG Dt fuel) b : ℤ)) = 0

omit [CFieldSpec α] [CDiffFieldSpec α] in
/-- **The special-denominator reconstruction power is trivial in the `negn = 0` sub-regime**: under
`CSpecialDenomNoClearG` (and a non-constant `p`), the special-denominator stage returns `h₁ = [CField.one]`
(`pⁿᵉᵍⁿ = p⁰`), so the reconstruction `ynum = Q·h₁` carries no `p`-power. -/
theorem cRdeSpecialDenominatorG_h1_eq_one_of_noClear [CFracGcdCore α] (Dt : CPolyG α) (fuel : ℕ)
    (a b c : CPolyG α) (hp : cdegG (cSpecialPolyG Dt fuel) ≠ 0)
    (hn : CSpecialDenomNoClearG Dt fuel b c) :
    (cRdeSpecialDenominatorG Dt fuel a b c).2.2.2 = [CField.one] := by
  rw [cRdeSpecialDenominatorG]
  simp only [if_neg hp]
  rw [CSpecialDenomNoClearG] at hn
  -- `negn = (−n).toNat` with `n = 0`, so `h = cpowG p 0 = [1]`
  show cpowG (cSpecialPolyG Dt fuel) (-(min 0 ((cValuationG fuel (cSpecialPolyG Dt fuel) c : ℤ)
    - min 0 (cValuationG fuel (cSpecialPolyG Dt fuel) b : ℤ)))).toNat = [CField.one]
  rw [hn]; rfl

omit [CDiffFieldSpec α] in
/-- **The special-denominator-cleared coefficients factor as `(·)·pᴺ` in the `negn = 0` sub-regime**
(carrier-generic): under `CSpecialDenomNoClearG` and non-constant `p = cSpecialPolyG Dt fuel`, writing `N =
max(max 0 (−ν_p b), −ν_p c)`, the three cleared coefficients read through `toPolyG` as `ā = a·pᴺ`, `b̄ = b·pᴺ`
(the `ν_p`-correction `n·a·Dp/p` vanishes since `n = 0`), `c̄ = c·pᴺ`. The structural input to the `negn = 0`
special-denominator discharge. -/
theorem toPolyG_cRdeSpecialDenominatorG_coeffs_of_noClear [CFracGcdCore α] (Dt : CPolyG α) (fuel : ℕ)
    (a b c : CPolyG α) (hp : cdegG (cSpecialPolyG Dt fuel) ≠ 0)
    (hn : CSpecialDenomNoClearG Dt fuel b c) :
    let pN : CPolyG α := cpowG (cSpecialPolyG Dt fuel)
      (max (max 0 (-(cValuationG fuel (cSpecialPolyG Dt fuel) b : ℤ)))
        (-(cValuationG fuel (cSpecialPolyG Dt fuel) c : ℤ))).toNat
    toPolyG (cRdeSpecialDenominatorG Dt fuel a b c).1 = toPolyG a * toPolyG pN
    ∧ toPolyG (cRdeSpecialDenominatorG Dt fuel a b c).2.1 = toPolyG b * toPolyG pN
    ∧ toPolyG (cRdeSpecialDenominatorG Dt fuel a b c).2.2.1 = toPolyG c * toPolyG pN := by
  intro pN
  rw [CSpecialDenomNoClearG] at hn
  -- with `n = 0`: `N = max(max 0 (−nb), 0 − nc) = max(max 0 (−nb), −nc)`, `Nminusn = N`, `negn = 0`.
  have hbterm0 : CFieldSpec.toK (CField.neg (CField.zero : α)) = 0 := by
    rw [CFieldSpec.toK_neg, CFieldSpec.toK_zero, neg_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [cRdeSpecialDenominatorG]
    simp only [if_neg hp, hn, toPolyG_cmulG, zero_sub]
    rfl
  · rw [cRdeSpecialDenominatorG]
    simp only [if_neg hp, hn, neg_zero, Int.toNat_zero, cnatCastG, toPolyG_cmulG, toPolyG_caddG,
      toPolyG_cscaleG, hbterm0, map_zero, zero_mul, add_zero, zero_sub]
    rfl
  · rw [cRdeSpecialDenominatorG]
    simp only [if_neg hp, hn, sub_zero, toPolyG_cmulG, zero_sub]
    rfl

/-! ### ★ THE CAPSTONE — the generic RDE oracle `cRischDEG` returns a cleared solution (primitive regime) -/

/-- **★ The composed generic §6 RDE pipeline correctness (primitive regime, carrier-generic)**: with the
primitive special regime (`cdegG (cSpecialPolyG Dt fuel) = 0`), and the pipeline's intermediate `some`-results
(§6.2 normal denominator, §6.4 SPDE under transparent `CSPDEGClearedInputsGen`, §6.5 non-cancellation),
together with the §6.2 normal-denominator certificates, the reconstruction `ynum = (α'·v + β)·[1]`, `yden = h0`
(exactly what `cRischDEG` returns in the primitive regime) satisfies the cleared Risch-DE identity
`gden·fden·(D(ynum)·yden − ynum·D(yden)) + gden·fnum·ynum·yden = gnum·fden·yden²` over `(CFieldSpec.K α)[X]`.
Carrier-generic mirror of `cRischDEG_rdeCleared`. -/
theorem cRischDEG_rdeCleared_gen [CFracGcdCore α] (Dt : CPolyG α) (fuel : ℕ)
    (fnum fden gnum gden a0 b0 c0 h0 : CPolyG α)
    (bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α)
    (hprim : cdegG (cSpecialPolyG Dt fuel) = 0)
    (hnorm : cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0))
    (hdn : toPolyG (cSplitFactorFastG Dt fuel fden).1 ≠ 0)
    (hfden0 : cnormG fden ≠ []) (hgden0 : cnormG gden ≠ [])
    (hfbB : (cnormG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h0)) fden)) :
        List α).length ≤ fuel)
    (hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h0)) fden)))
    (hfbC : (cnormG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) h0) gnum) :
        List α).length ≤ fuel)
    (hdvdC : toPolyG gden ∣ toPolyG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) h0) gnum))
    (hspde : cSPDEG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1 (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGen Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1 (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1 : ℤ))
    (hpoly : cPolyRischDENoCancelG Dt fuel bbar cbar m = some v) :
    let Q := caddG (cmulG α' v) β
    let ynum := cmulG Q [CField.one]
    let yden := h0
    toPolyG gden * toPolyG fden
        * (Differential.implicitDeriv (toPolyG Dt) (toPolyG ynum) * toPolyG yden
            - toPolyG ynum * Differential.implicitDeriv (toPolyG Dt) (toPolyG yden))
        + toPolyG gden * toPolyG fnum * toPolyG ynum * toPolyG yden
      = toPolyG gnum * toPolyG fden * toPolyG yden ^ 2 := by
  intro Q ynum yden
  have hspecial := cRdeSpecialDenominatorG_primitive_eq_gen Dt fuel a0 b0 c0 hprim
  rw [hspecial] at hspde hin
  simp only at hspde hin
  have hred : toPolyG a0 * Differential.implicitDeriv (toPolyG Dt) (toPolyG Q) + toPolyG b0 * toPolyG Q
      = toPolyG c0 :=
    cSPDEG_polyRischDENoCancel_cleared_at_boundDegree_gen Dt fuel a0 b0 c0 bbar cbar m α' β v hspde hin hpoly
  have hynum : toPolyG ynum = toPolyG Q := by
    show toPolyG (cmulG Q [CField.one]) = toPolyG Q
    have hone : toPolyG ([CField.one] : CPolyG α) = 1 := by
      rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]
    rw [toPolyG_cmulG, hone, mul_one]
  have hlift := cRdeNormalDenominatorG_cleared_lift_gen Dt fuel fnum fden gnum gden a0 b0 c0 h0 Q
    hnorm hdn hfden0 hgden0 hfbB hdvdB hfbC hdvdC hred
  show toPolyG gden * toPolyG fden
      * (Differential.implicitDeriv (toPolyG Dt) (toPolyG ynum) * toPolyG h0
          - toPolyG ynum * Differential.implicitDeriv (toPolyG Dt) (toPolyG h0))
      + toPolyG gden * toPolyG fnum * toPolyG ynum * toPolyG h0
    = toPolyG gnum * toPolyG fden * toPolyG h0 ^ 2
  rw [hynum]
  exact hlift

/-! ### ★ The `α = QFunNZG ℚ` instantiations — the §6 RDE cleared identities, `cgcdFF`-free

Instantiating the carrier-generic chain at `α = QFunNZG ℚ` (via `instCFracGcdCoreQFunNZG`/the chunk-1
`instCDiffFieldSpecQFunNZG`). At this carrier `CFracGcdCore.cgcdFFCore` is the recursive tower gcd bottoming at
`cgcdWf` over ℚ — **never `cgcdFF`** — so the discharge route is `associated_toPolyG_cgcdFFCore`, NOT
`cgcdFF`. These are the deliverables: the §6.4 SPDE certificate discharge and the ★ capstone RDE cleared
identity at the generic ℚ(x) carrier. -/

/-- **★ `cSPDEGCleared` discharged from transparent inputs at `α = QFunNZG ℚ`** (`cgcdFF`-free): the §6.4 SPDE
per-level certificate `cSPDEGClearedGen` discharged from the transparent `CSPDEGClearedInputsGen` at the
generic ℚ(x) carrier. The gcd obligation `Associated (toPolyG g) (gcd …)` (a clause of
`CSPDEGClearedInputsGen`) is the generic gcd correctness `associated_toPolyG_cgcdFFCore` at `QFunNZG ℚ` — NOT
`cgcdFF`. The `QFunNZG ℚ` instance of `cSPDEGCleared_of_inputs_gen`; mirror of `cSPDEGCleared_of_inputs`. -/
theorem cSPDECleared_of_inputs_qfunNZG (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ)
    (a b c : CPolyG (QFunNZG ℚ)) (n : ℤ)
    (hin : CSPDEGClearedInputsGen Dt fuel a b c n) :
    cSPDEGClearedGen Dt fuel a b c n :=
  cSPDEGCleared_of_inputs_gen Dt fuel a b c n hin

/-- **★ THE CAPSTONE at `α = QFunNZG ℚ`** (`cgcdFF`-free): the generic §6 RDE oracle `cRischDEG`'s cleared
identity `Dy + f·y = g` at the generic ℚ(x) = `QFunNZG ℚ` carrier, in the primitive regime. The returned
`y = (α'·v + β)·[1] / h0` solves the cleared Risch-DE identity over `(RatFunc ℚ)[X] = (CFieldSpec.K (QFunNZG
ℚ))[X]`. Every gcd inside the §6.4/§6.2 stages is the recursive tower `cgcdFFCore` (bottoming at `cgcdWf` over
ℚ); the single gcd-correctness obligation is discharged through `associated_toPolyG_cgcdFFCore`, NOT `cgcdFF`.
The `QFunNZG ℚ` instance of `cRischDEG_rdeCleared_gen`; the deliverable — §6 RDE correctness re-founded at the
generic ℚ(x) carrier. -/
theorem cRischDEG_rdeCleared_qfunNZG (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ)
    (fnum fden gnum gden a0 b0 c0 h0 : CPolyG (QFunNZG ℚ))
    (bbar cbar : CPolyG (QFunNZG ℚ)) (m : ℤ) (α' β v : CPolyG (QFunNZG ℚ))
    (hprim : cdegG (cSpecialPolyG Dt fuel) = 0)
    (hnorm : cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0))
    (hdn : toPolyG (cSplitFactorFastG Dt fuel fden).1 ≠ 0)
    (hfden0 : cnormG fden ≠ []) (hgden0 : cnormG gden ≠ [])
    (hfbB : (cnormG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h0)) fden)) :
        List (QFunNZG ℚ)).length ≤ fuel)
    (hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h0)) fden)))
    (hfbC : (cnormG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) h0) gnum) :
        List (QFunNZG ℚ)).length ≤ fuel)
    (hdvdC : toPolyG gden ∣ toPolyG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) h0) gnum))
    (hspde : cSPDEG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1 (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGen Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1 (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1 : ℤ))
    (hpoly : cPolyRischDENoCancelG Dt fuel bbar cbar m = some v) :
    let Q := caddG (cmulG α' v) β
    let ynum := cmulG Q [CField.one]
    let yden := h0
    toPolyG gden * toPolyG fden
        * (Differential.implicitDeriv (toPolyG Dt) (toPolyG ynum) * toPolyG yden
            - toPolyG ynum * Differential.implicitDeriv (toPolyG Dt) (toPolyG yden))
        + toPolyG gden * toPolyG fnum * toPolyG ynum * toPolyG yden
      = toPolyG gnum * toPolyG fden * toPolyG yden ^ 2 :=
  cRischDEG_rdeCleared_gen Dt fuel fnum fden gnum gden a0 b0 c0 h0 bbar cbar m α' β v
    hprim hnorm hdn hfden0 hgden0 hfbB hdvdB hfbC hdvdC hspde hin hpoly

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- The §6.4 SPDE certificate discharged from transparent inputs at `α = QFunNZG ℚ` (`cgcdFF`-free).
example (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ) (a b c : CPolyG (QFunNZG ℚ)) (n : ℤ)
    (hin : CSPDEGClearedInputsGen Dt fuel a b c n) :
    cSPDEGClearedGen Dt fuel a b c n :=
  cSPDECleared_of_inputs_qfunNZG Dt fuel a b c n hin

-- ★ THE CAPSTONE at `α = QFunNZG ℚ`: `cRischDEG`'s returned `y = (Q·1)/h0` solves `D(y)+f·y=g`
-- (cleared, primitive regime), threaded through the GENERIC gcd correctness (NO `cgcdFF`).
example (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ) (fnum fden gnum gden a0 b0 c0 h0 : CPolyG (QFunNZG ℚ))
    (bbar cbar : CPolyG (QFunNZG ℚ)) (m : ℤ) (α' β v : CPolyG (QFunNZG ℚ))
    (hprim : cdegG (cSpecialPolyG Dt fuel) = 0)
    (hnorm : cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0))
    (hdn : toPolyG (cSplitFactorFastG Dt fuel fden).1 ≠ 0)
    (hfden0 : cnormG fden ≠ []) (hgden0 : cnormG gden ≠ [])
    (hfbB : (cnormG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h0)) fden)) :
        List (QFunNZG ℚ)).length ≤ fuel)
    (hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h0)) fden)))
    (hfbC : (cnormG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) h0) gnum) :
        List (QFunNZG ℚ)).length ≤ fuel)
    (hdvdC : toPolyG gden ∣ toPolyG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) h0) gnum))
    (hspde : cSPDEG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1 (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGen Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1 (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1 : ℤ))
    (hpoly : cPolyRischDENoCancelG Dt fuel bbar cbar m = some v) :
    let Q := caddG (cmulG α' v) β
    let ynum := cmulG Q [CField.one]
    let yden := h0
    toPolyG gden * toPolyG fden
        * (Differential.implicitDeriv (toPolyG Dt) (toPolyG ynum) * toPolyG yden
            - toPolyG ynum * Differential.implicitDeriv (toPolyG Dt) (toPolyG yden))
        + toPolyG gden * toPolyG fnum * toPolyG ynum * toPolyG yden
      = toPolyG gnum * toPolyG fden * toPolyG yden ^ 2 :=
  cRischDEG_rdeCleared_qfunNZG Dt fuel fnum fden gnum gden a0 b0 c0 h0 bbar cbar m α' β v
    hprim hnorm hdn hfden0 hgden0 hfbB hdvdB hfbC hdvdC hspde hin hpoly

-- ★ `cValuationG` divides: `p^{ν_p(x)} ∣ x` (the §6.2 valuation `dvd` half), carrier-generic.
example {α : Type*} [CField α] [CFieldSpec α] [CFracGcdCore α] (fuel : ℕ) (p x : CPolyG α) :
    toPolyG p ^ (cValuationG fuel p x) ∣ toPolyG x :=
  toPolyG_pow_cValuationG_dvd fuel p x

-- ★ `cValuationG` is sharp: `¬ p^{ν_p(x)+1} ∣ x` for non-constant `p`, nonzero `x`, fuel strictly covering.
example {α : Type*} [CField α] [CFieldSpec α] [CFracGcdCore α] (fuel : ℕ) (p x : CPolyG α)
    (hp : cdegG p ≠ 0) (hx0 : toPolyG x ≠ 0) (hfuel : (cnormG x : List α).length < fuel) :
    ¬ toPolyG p ^ (cValuationG fuel p x + 1) ∣ toPolyG x :=
  cValuationG_sharp fuel p x hp hx0 hfuel

-- ★ The special monomial polynomial divides its own monomial derivative (`Dp = E·p`, §6.2 premise).
example (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ) (hDt : toPolyG Dt ≠ 0)
    (hdeg : (toPolyG Dt).natDegree ≤ fuel) (hreg : CSplitFactorFastGRegularQ Dt fuel Dt) :
    toPolyG (cSpecialPolyG Dt fuel) ∣ toPolyG (cmonomialDeriv Dt (cSpecialPolyG Dt fuel)) :=
  toPolyG_cSpecialPolyG_dvd_cmonomialDeriv Dt fuel hDt hdeg hreg

/-! ### Axiom audit (the `QFunNZG ℚ` §6 RDE correctness rests only on the standard kernel axioms) -/

#print axioms cSPDECleared_of_inputs_qfunNZG
#print axioms cRischDEG_rdeCleared_qfunNZG
#print axioms toPolyG_pow_cValuationG_dvd
#print axioms cValuationG_sharp
#print axioms toPolyG_cSpecialPolyG_dvd_cmonomialDeriv

end DeepWiki.SymbolicIntegration
