import DeepWiki.SymbolicIntegration.ComputableRischDETowerCorrect
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

end DeepWiki.SymbolicIntegration
