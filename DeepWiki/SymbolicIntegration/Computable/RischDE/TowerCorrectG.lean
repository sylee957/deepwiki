import DeepWiki.SymbolicIntegration.ComputableTowerRischDE
import DeepWiki.SymbolicIntegration.Computable.RischDE.TowerGlue
import DeepWiki.SymbolicIntegration.Computable.SplitFactorTowerCorrectG

/-! # §6 RDE cleared-identity correctness at the level-1 carrier `α = QFunNZG ℚ`

This file establishes the §6 RDE cleared chain — the generic §6 RDE oracle `cRischDEG`'s abstract cleared
identity `Dy + f·y = g` (`cRischDEG_rdeCleared`) and the §6.4 SPDE certificate discharge
(`cSPDEGCleared_of_inputs`) — at the **level-1 carrier** `α = QFunNZG ℚ = Frac(ℚ[x])`, following the same
pattern as `ComputableSplitFactorTowerCorrectG` (§5 at `QFunNZG ℚ`). At `QFunNZG ℚ`,
`CFracGcdCore.cgcdFFCore` resolves to the **recursive** `instCFracGcdCoreQFunNZG`, whose Euclidean work
bottoms at `cgcdWf` over ℚ. The single gcd-correctness obligation the SPDE discharge needs —
`Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b))` for `g = cgcdFFCore fuel a b` — is discharged through
the **generic** theorem `associated_toPolyG_cgcdFFCore` (`ComputableTowerGcdFFCorrect`).

The carrier `QFunNZG ℚ` reads through `toPolyG` into the field `RatFunc ℚ = CFieldSpec.K (QFunNZG ℚ)`, so the
abstract conclusions (the cleared polynomial identities over `(RatFunc ℚ)[X]`) live over that field. The
cleared-lifting *engine* (`cSPDEG_cleared_lifting`-style induction, `rdeNormalDenominator_glue`,
`spde_const_base`, `cSPDE_peel_cleared`, `toPolyG_cdiophantineGWf`, the `dvd_of_cdvdG`/`dvd_of_cdvdGWf`
read-offs, and `toPolyG_cdivWf_exact`) is
gcd-agnostic, so it applies at any tower level; the gcd-discharge route enters through
`associated_toPolyG_cgcdFFCore`.

* **Generic helper lemmas** — the `cgcdWf`-unit / exact-division / SPDE-peel helpers, stated
  `{α} [CField α] [CFieldSpec α]`-generic (their bodies are gcd-agnostic, taking the gcd `g`
  abstractly).
* **`cSPDECleared_of_inputs_qfunNZG`** — the §6.4 SPDE per-level certificate, discharged from transparent
  inputs, at `α = QFunNZG ℚ` (the gcd obligation via `associated_toPolyG_cgcdFFCore`, NOT `cgcdFF`).
* **★ `cRischDEG_rdeCleared_qfunNZG`** — the generic RDE oracle's cleared identity `Dy + f·y = g` at
  `α = QFunNZG ℚ`, cgcdFF-free. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ### Generic helper lemmas (the §6.4 helpers at any tower level)

The §6.4 SPDE certificate discharge needs five engine facts whose proofs only ever touch the gcd `g`
**abstractly** (through an `Associated (toPolyG g) (gcd …)` hypothesis and the generic
`cgcdWf`/`cdivWf`/`cdvdG`/`cdvdGWf` API). We state them generically over `{α} [CField α] [CFieldSpec α]`, so they
apply at `QFunNZG ℚ` (and any level). Each reuses the already generic `toPolyG_cgcdWf_dvd` /
`toPolyG_cdivWf_exact` / divisibility read-offs / `spde_const_base` / `spde_step_glue`. -/

/-- **The divided coefficients' fuel-free gcd is a unit** (generic): after dividing `a,b` by a nonzero gcd
`g`, the Wf gcd of `bd, ad` is a unit. -/
theorem cgcdWf_isUnit_of_divided_gen {α : Type*} [CField α] [CFieldSpec α]
    (a b ad bd g : CPolyG α) (hgne : toPolyG g ≠ 0)
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b)))
    (hdiva : toPolyG ad * toPolyG g = toPolyG a)
    (hdivb : toPolyG bd * toPolyG g = toPolyG b) :
    IsUnit (toPolyG (cgcdWf bd ad).1) := by
  obtain ⟨hGbd, hGad⟩ := toPolyG_cgcdWf_dvd bd ad
  set G := toPolyG (cgcdWf bd ad).1 with hGdef
  have hGg_a : G * toPolyG g ∣ toPolyG a := by rw [← hdiva]; exact mul_dvd_mul_right hGad _
  have hGg_b : G * toPolyG g ∣ toPolyG b := by rw [← hdivb]; exact mul_dvd_mul_right hGbd _
  have hGg_gcd : G * toPolyG g ∣ gcd (toPolyG a) (toPolyG b) := dvd_gcd hGg_a hGg_b
  have hGg_g : G * toPolyG g ∣ toPolyG g := hGg_gcd.trans hgassoc.symm.dvd
  obtain ⟨k, hk⟩ := hGg_g
  have hcancel : toPolyG g * 1 = toPolyG g * (G * k) := by rw [mul_one]; nth_rewrite 1 [hk]; ring
  have hG1 : G ∣ 1 := ⟨k, mul_left_cancel₀ hgne hcancel⟩
  exact isUnit_of_dvd_one hG1

/-- **The `a`-exact-division witness** (generic) `toPolyG (cdivWf a g) · toPolyG g = toPolyG a` from
`g ~ gcd(a, b)` (`g ∣ a`) and `g ≠ 0`. Generic mirror of `cdivFF_a_exact_of_gcd`
(`cdivFF := cdivWf`). -/
theorem cdivWf_a_exact_of_gcd {α : Type*} [CField α] [CFieldSpec α] (a b g : CPolyG α)
    (hg0 : cnormG g ≠ [])
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b))) :
    toPolyG (cdivWf a g) * toPolyG g = toPolyG a := by
  have hgdvd : toPolyG g ∣ toPolyG a := hgassoc.dvd.trans (gcd_dvd_left _ _)
  exact toPolyG_cdivWf_exact a g hg0 hgdvd

/-- **The `b`-exact-division witness** (generic) `toPolyG (cdivWf b g) · toPolyG g = toPolyG b` from
`g ~ gcd(a, b)` (`g ∣ b`). Generic mirror of `cdivFF_b_exact_of_gcd`. -/
theorem cdivWf_b_exact_of_gcd {α : Type*} [CField α] [CFieldSpec α] (a b g : CPolyG α)
    (hg0 : cnormG g ≠ [])
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b))) :
    toPolyG (cdivWf b g) * toPolyG g = toPolyG b := by
  have hgdvd : toPolyG g ∣ toPolyG b := hgassoc.dvd.trans (gcd_dvd_right _ _)
  exact toPolyG_cdivWf_exact b g hg0 hgdvd

/-- **The `c`-exact-division witness** (generic) `toPolyG (cdivWf c g) · toPolyG g = toPolyG c` from the
`cdvdG fuel g c = true` branch (`g ∣ c`). Generic mirror of `cdivFF_c_exact_of_cdvdG`. -/
theorem cdivWf_c_exact_of_cdvdG {α : Type*} [CField α] [CFieldSpec α] (fuel : ℕ) (c g : CPolyG α)
    (hg0 : cnormG g ≠ [])
    (hdvd : cdvdG fuel g c = true) :
    toPolyG (cdivWf c g) * toPolyG g = toPolyG c := by
  have hgdvd : toPolyG g ∣ toPolyG c := dvd_of_cdvdG fuel g c hg0 hdvd
  exact toPolyG_cdivWf_exact c g hg0 hgdvd

/-- **The Wf `c`-exact-division witness** (generic) `toPolyG (cdivWf c g) · toPolyG g = toPolyG c`
from the fuel-free `cdvdGWf g c = true` branch (`g ∣ c`). -/
theorem cdivWf_c_exact_of_cdvdGWf {α : Type*} [CField α] [CFieldSpec α] (c g : CPolyG α)
    (hg0 : cnormG g ≠ [])
    (hdvd : cdvdGWf g c = true) :
    toPolyG (cdivWf c g) * toPolyG g = toPolyG c := by
  have hgdvd : toPolyG g ∣ toPolyG c := dvd_of_cdvdGWf g c hg0 hdvd
  exact toPolyG_cdivWf_exact c g hg0 hgdvd

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
read only through the certificate's `Associated (toPolyG g) (gcd …)` clause. We therefore state the whole
§6.4 chain generically over `{α} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]` (the §6.5
non-cancellation identity follows the same way), using the `_gen` helpers above; the gcd-correctness
discharge enters only in `cSPDECleared_of_inputs_gen` through the per-call `Associated` clause (supplied at
`QFunNZG ℚ` by `associated_toPolyG_cgcdFFCore`). -/

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-- **Generic per-level certificate predicate for `cSPDEG`** `cSPDEGClearedGen Dt fuel a b c n`: the
carrier-generic mirror of `cSPDEGCleared`, with `g = cgcdFFCore fuel a b` and the divided coefficients
`ad = a/g`, `bd = b/g`, `cd = c/g` via `cdivWf`. At each non-base level (`n ≥ 0`, `g ∣ c`, `deg(ad) > 0`) it
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
        set ad := cdivWf a g with had
        set bd := cdivWf b g with hbd
        set cd := cdivWf c g with hcd
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
          rcases hrz : cdiophantineGWf bd ad cd with ⟨r, z⟩
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
[]`) and `Associated` to `gcd(toPolyG a, toPolyG b)`, the fuel bounds the divisibility checks, and `a ≠ 0`. In
the recursion branch (`cdegG ad ≠ 0`) it carries `CSPDEGClearedInputsGen` on the reduced equation. Carrier-generic
mirror of `CSPDEGClearedInputs`. -/
def CSPDEGClearedInputsGen [CFracGcdCore α] (Dt : CPolyG α) :
    ℕ → (a b c : CPolyG α) → (n : ℤ) → Prop
  | 0, _, _, _, _ => True
  | fuel + 1, a, b, c, n =>
    if n < 0 then True
    else
      let g := CFracGcdCore.cgcdFFCore fuel a b
      if cdvdG fuel g c then
        let ad := cdivWf a g
        let bd := cdivWf b g
        (cnormG g ≠ []) ∧ Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b))
          ∧ ((cnormG a : List α).length ≤ fuel)
          ∧ ((cnormG b : List α).length ≤ fuel)
          ∧ ((cnormG c : List α).length ≤ fuel)
          ∧ (cnormG a ≠ [])
          ∧ (if cdegG ad = 0 then True
             else
               let rz := cdiophantineGWf bd ad (cdivWf c g)
               CSPDEGClearedInputsGen Dt fuel ad (caddG bd (cmonomialDeriv Dt ad))
                 (csubG rz.2 (cmonomialDeriv Dt rz.1)) (n - (cdegG ad : ℤ)))
      else True

omit [CDiffFieldSpec α] in
/-- **Generic `cSPDEGClearedGen` discharged from transparent inputs**: `CSPDEGClearedInputsGen Dt fuel a b c
n` implies the per-level certificate `cSPDEGClearedGen Dt fuel a b c n`, over any tower level. By fuel
induction: the three exact-division witnesses from `cdivWf_a`/`cdivWf_b`/`cdivWf_c` exactness, the nonzero-`ad`
clause from `ad·g = a` with `a ≠ 0`, and (recursion branch) the Bézout clause from `toPolyG_cdiophantineGWf`
with the divided-coefficient Wf gcd shown unit by `cgcdWf_isUnit_of_divided_gen`. Carrier-generic
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
        set ad := cdivWf a g with had
        set bd := cdivWf b g with hbd
        obtain ⟨hg0, hgassoc, hfa, hfb, hfc, ha0, hrest⟩ := hin
        have hdiva : toPolyG ad * toPolyG g = toPolyG a :=
          cdivWf_a_exact_of_gcd a b g hg0 hgassoc
        have hdivb : toPolyG bd * toPolyG g = toPolyG b :=
          cdivWf_b_exact_of_gcd a b g hg0 hgassoc
        have hdivc : toPolyG (cdivWf c g) * toPolyG g = toPolyG c :=
          cdivWf_c_exact_of_cdvdG fuel c g hg0 hdvd
        have hane : toPolyG a ≠ 0 := fun h => ha0 ((cnormG_eq_nil_iff a).mpr h)
        have hadne : toPolyG ad ≠ 0 := by
          intro h; apply hane; rw [← hdiva, h, zero_mul]
        have hgne : toPolyG g ≠ 0 := fun h => hg0 ((cnormG_eq_nil_iff g).mpr h)
        refine ⟨hdiva, hdivb, hdivc, hadne, ?_⟩
        by_cases hdeg : cdegG ad = 0
        · rw [if_pos hdeg] at hrest ⊢; trivial
        · rw [if_neg hdeg] at hrest ⊢
          let hrec := hrest
          have hadnil : cnormG ad ≠ [] := fun h => hadne ((cnormG_eq_nil_iff ad).mp h)
          have hunitWf := cgcdWf_isUnit_of_divided_gen a b ad bd g hgne hgassoc hdiva hdivb
          have hgdegWf : (toPolyG (cgcdWf bd ad).1).natDegree = 0 :=
            Polynomial.natDegree_eq_zero_of_isUnit hunitWf
          have hgneWf : toPolyG (cgcdWf bd ad).1 ≠ 0 := hunitWf.ne_zero
          have hbez := toPolyG_cdiophantineGWf bd ad (cdivWf c g) hadnil hgdegWf hgneWf
          refine ⟨?_, ih ad (caddG bd (cmonomialDeriv Dt ad))
            (csubG (cdiophantineGWf bd ad (cdivWf c g)).2
              (cmonomialDeriv Dt (cdiophantineGWf bd ad (cdivWf c g)).1))
            (n - (cdegG ad : ℤ)) hrec⟩
          simpa [mul_comm] using hbez
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
for every `n`, in particular at `n = cRdeBoundDegreeG Dt a b c`. Carrier-generic mirror of
`cSPDEG_polyRischDENoCancel_cleared_at_boundDegree`. -/
theorem cSPDEG_polyRischDENoCancel_cleared_at_boundDegree_gen [CFracGcdCore α] (Dt : CPolyG α)
    (fuel : ℕ) (a b c : CPolyG α) (bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α)
    (hspde : cSPDEG Dt fuel a b c (cRdeBoundDegreeG Dt a b c : ℤ) = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGen Dt fuel a b c (cRdeBoundDegreeG Dt a b c : ℤ))
    (hpoly : cPolyRischDENoCancelG Dt fuel bbar cbar m = some v) :
    toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α' v) β))
        + toPolyG b * toPolyG (caddG (cmulG α' v) β)
      = toPolyG c :=
  cSPDEG_polyRischDENoCancel_cleared_of_inputs_gen Dt fuel a b c
    (cRdeBoundDegreeG Dt a b c : ℤ) bbar cbar m α' β v hspde hin hpoly

/-! ### §6.2 — the generic normal-denominator cleared lifting and special-denominator primitive case -/

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Generic exact-division reorientation** `toPolyG (cdivWf p q) · toPolyG q = toPolyG p` from `toPolyG
q ∣ toPolyG p` (nonzero divisor). Carrier-generic mirror of `toPolyG_cdivG_exact_mul`
(reorienting the already-generic `toPolyG_cdivWf_exact`). -/
theorem toPolyG_cdivWf_exact_mul_gen (p q : CPolyG α)
    (hq0 : cnormG q ≠ [])
    (hQdvd : toPolyG q ∣ toPolyG p) :
    toPolyG (cdivWf p q) * toPolyG q = toPolyG p :=
  toPolyG_cdivWf_exact p q hq0 hQdvd

/-! #### ★ The derivation-generic pole order-drop — the polynomial kernel of Bronstein Lemma 6.1.1 / Thm 4.4.2

The §6.1 normal-denominator necessity (Theorem 6.1.2(i) / Corollary 6.1.1) rests on the valuation fact that
*a derivation lowers the order of a pole at a **normal** irreducible by exactly one* — `νₚ(D y) = νₚ(y) − 1`
when `νₚ(y) < 0` and `p ∤ D p` (Bronstein Lemma 6.1.1, via Theorem 4.4.2). Its polynomial kernel — stated for
an arbitrary `Derivation` `D`, not just `Polynomial.derivative` — is recorded here in two halves:

* `pow_sub_one_dvd_deriv_of_pow_dvd` — the universally-true LOWER bound `q^n ∣ p ⟹ q^{n−1} ∣ D p` (no
  primality/normality/characteristic needed): the order drops by **at most** one. The `Derivation`-generic
  analogue of Mathlib's `pow_sub_one_dvd_derivative_of_pow_dvd`.
* `not_pow_dvd_deriv_of_normal` — the EXACT half at a normal prime: if `pⁿ ∥ f` (`n ≥ 1`, `p ∤ r` for
  `f = pⁿ·r`), `p` prime, `p ∤ D p` (normal), over a characteristic-zero field, then `pⁿ ∤ D f` — so the
  order is *exactly* `n − 1`. The Leibniz expansion `D f = p^{n−1}·(n·(Dp)·r + p·Dr)` has `p ∤ n·(Dp)·r`.

Assembled, `emultiplicity_deriv_eq_sub_one_of_normal` gives `emultiplicity p (D f) = emultiplicity p f − 1`
for a normal prime `p ∣ f`. These are the reusable §6.1 order-drop kernel; the genuine *fractional*-solution
necessity additionally needs the `K(t)`-valuation lift, weak normalization, and the `k⟨t⟩` differential
subring (see `hnormalize`'s remaining-obligation note in `ComputableRischDESolveExhaustiveness`). -/

section DerivationPoleOrderDrop

variable {R : Type*} [CommRing R]

/-- **Derivation-generic order-drop, lower bound** (`pow_sub_one_dvd_deriv_of_pow_dvd`): for any
`Derivation ℤ R R` and `q^n ∣ p`, `q^(n-1) ∣ D p`. The Leibniz expansion of `p = qⁿ·r` is
`D p = qⁿ·D r + (n • q^{n−1} • D q)·r`, both summands divisible by `q^{n−1}`. The `Derivation`-generic
analogue of Mathlib's `pow_sub_one_dvd_derivative_of_pow_dvd` (which is pinned to `Polynomial.derivative`) —
"a derivation drops a pole's order by at most one", needing no primality, normality, or characteristic. -/
theorem pow_sub_one_dvd_deriv_of_pow_dvd (D : Derivation ℤ R R) {p q : R} {n : ℕ}
    (hdvd : q ^ n ∣ p) : q ^ (n - 1) ∣ D p := by
  obtain ⟨r, rfl⟩ := hdvd
  rw [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, smul_eq_mul]
  -- `D(qⁿ·r) = qⁿ·D r + r·(n·q^{n−1}·D q)`, both divisible by `q^{n−1}`.
  refine dvd_add ((pow_dvd_pow q (Nat.sub_le n 1)).mul_right _) ?_
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) _

end DerivationPoleOrderDrop

section DerivationNormalOrderDrop

variable {K : Type*} [Field K] [CharZero K]

/-- **Derivation-generic order-drop, exact half at a normal prime** (`not_pow_dvd_deriv_of_normal`): over a
characteristic-zero field, for a prime `p` that is normal for the derivation (`¬ p ∣ D p`), if `f = pⁿ·r` with
`n ≥ 1` and `p ∤ r` (i.e. `pⁿ ∥ f` exactly), then `pⁿ ∤ D f`. Leibniz gives `D f = p^{n−1}·(n·(Dp)·r + p·Dr)`;
dividing a hypothetical `pⁿ ∣ D f` by `p^{n−1}` forces `p ∣ n·(Dp)·r`, but `p` is prime, `p ∤ Dp` (normal),
`p ∤ r`, and `(n : K) ≠ 0` (char zero) is a unit — contradiction. With the lower bound, this pins the order
at exactly `n − 1`: the heart of Bronstein Lemma 6.1.1 / Theorem 4.4.2. -/
theorem not_pow_dvd_deriv_of_normal (D : Derivation ℤ K[X] K[X]) {p r : K[X]} {n : ℕ}
    (hp : Prime p) (hnormal : ¬ p ∣ D p) (hn : 1 ≤ n) (hr : ¬ p ∣ r) :
    ¬ p ^ n ∣ D (p ^ n * r) := by
  -- write `n = m + 1`; Leibniz gives `D(p^{m+1}·r) = pᵐ·((m+1)·(Dp)·r + p·D r)`.
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  simp only [Nat.zero_add] at *
  have hexp : D (p ^ (m + 1) * r)
      = p ^ m * ((m + 1 : ℕ) • (D p * r) + p * D r) := by
    rw [Derivation.leibniz, Derivation.leibniz_pow, Nat.add_sub_cancel]
    rw [nsmul_eq_mul, nsmul_eq_mul, smul_eq_mul, pow_succ]
    push_cast; ring
  intro hdvd
  -- cancel `pᵐ` (`K[X]` a domain): `p ∣ (m+1)·(Dp)·r + p·D r`, hence `p ∣ (m+1)·(Dp)·r`.
  have hpm0 : p ^ m ≠ 0 := pow_ne_zero m hp.ne_zero
  rw [hexp, pow_succ, mul_dvd_mul_iff_left hpm0] at hdvd
  have hp_dvd : p ∣ (m + 1 : ℕ) • (D p * r) + p * D r := hdvd
  have hp_smul : p ∣ (m + 1 : ℕ) • (D p * r) :=
    (dvd_add_right (dvd_mul_right p (D r))).mp (by rwa [add_comm] at hp_dvd)
  -- `(m+1 : K) ≠ 0` (char zero) is a unit constant, so `p ∣ Dp·r`.
  rw [nsmul_eq_mul] at hp_smul
  have hunit : IsUnit ((m + 1 : ℕ) : K[X]) := by
    rw [← Polynomial.C_eq_natCast]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero m))
  have hp_DpR : p ∣ D p * r := hunit.dvd_mul_left.mp hp_smul
  -- `p` prime ⟹ `p ∣ Dp` (contradicts normality) or `p ∣ r` (contradicts exactness).
  rcases (hp.dvd_mul.mp hp_DpR) with h | h
  · exact hnormal h
  · exact hr h

/-- **Derivation-generic exact pole order-drop** (`emultiplicity_deriv_eq_sub_one_of_normal`): over a
characteristic-zero field, for a prime `p` normal for the derivation (`¬ p ∣ D p`), if `f = pⁿ·r` with `n ≥ 1`
and `p ∤ r` (so `emultiplicity p f = n`), then `emultiplicity p (D f) = n − 1`. Both bounds combine: the
universal lower bound `p^{n−1} ∣ D f` (`pow_sub_one_dvd_deriv_of_pow_dvd`) and the normal exact bound
`pⁿ ∤ D f` (`not_pow_dvd_deriv_of_normal`). This is the polynomial-ring statement of Bronstein Lemma 6.1.1 /
Theorem 4.4.2 — "a derivation drops the order at a normal pole by exactly one" — the kernel the §6.1
fractional-solution denominator necessity (`hnormalize`) rests on, once lifted to `K(t)` valuations. -/
theorem emultiplicity_deriv_eq_sub_one_of_normal (D : Derivation ℤ K[X] K[X]) {p r : K[X]} {n : ℕ}
    (hp : Prime p) (hnormal : ¬ p ∣ D p) (hn : 1 ≤ n) (hr : ¬ p ∣ r) :
    emultiplicity p (D (p ^ n * r)) = (n - 1 : ℕ) := by
  apply emultiplicity_eq_of_dvd_of_not_dvd
  · exact pow_sub_one_dvd_deriv_of_pow_dvd D (Dvd.intro r rfl)
  · rw [Nat.sub_add_cancel hn]; exact not_pow_dvd_deriv_of_normal D hp hnormal hn hr

/-! #### ★ The Wronskian-numerator order-drop — the `K(t)`-valuation lift of Bronstein Lemma 6.1.1

For `y = a/b ∈ K(t)` the derivative is `Dy = (D a·b − a·D b)/b²`, so the `p`-adic valuation
`νₚ(Dy) = νₚ(D a·b − a·D b) − 2·νₚ(b)`. The fractional Lemma 6.1.1 (`νₚ(Dy) = νₚ(y) − 1` at a normal
pole `νₚ(y) < 0`) therefore reduces to the **polynomial** identity `νₚ(D a·b − a·D b) = νₚ(a) + νₚ(b) − 1`
when `p` is normal and `νₚ(a) < νₚ(b)` (a genuine pole). Writing `a = pᵐ·a'`, `b = pᵏ·b'` (`p ∤ a',b'`,
`m < k`), the Leibniz expansion is `D a·b − a·D b = p^{m+k−1}·((m−k)·(Dp)·a'·b' + p·(Da'·b' − a'·Db'))`,
whose cofactor is `p`-coprime: mod `p` it is `(m−k)·(Dp)·a'·b'`, a product of `p`-non-divisors
(`(m−k : K) ≠ 0` char zero, `p ∤ Dp` normal, `p ∤ a'`, `p ∤ b'`). This is the `K(t)`-valuation lift's
numerator core — Bronstein Lemma 6.1.1 lifted off `K[X]` to the fraction field `K(t) = RatFunc K`. -/
theorem emultiplicity_wronskian_numerator_eq_of_normal (D : Derivation ℤ K[X] K[X]) {p a' b' : K[X]}
    {m k : ℕ} (hp : Prime p) (hnormal : ¬ p ∣ D p) (hlt : m < k) (ha' : ¬ p ∣ a') (hb' : ¬ p ∣ b') :
    emultiplicity p (D (p ^ m * a') * (p ^ k * b') - (p ^ m * a') * D (p ^ k * b'))
      = (m + k - 1 : ℕ) := by
  -- `k ≥ 1`, so `m + k - 1` is honest; set `j := k - 1` with `k = j + 1`.
  have hk1 : 1 ≤ k := Nat.one_le_of_lt hlt
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hk1)
  simp only [Nat.zero_add] at *
  -- Leibniz: `D(pⁿ·s) = pⁿ·D s + n·pⁿ⁻¹·(Dp)·s`.
  have hleib : ∀ (n : ℕ) (s : K[X]),
      D (p ^ n * s) = p ^ n * D s + (n : ℤ) • (p ^ (n - 1) * (D p * s)) := by
    intro n s
    rw [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      nsmul_eq_mul, zsmul_eq_mul]
    push_cast; ring
  -- The combination factors as `p^{m+j}·W` with `W = (m−(j+1))·(Dp)·a'·b' + p·(Da'·b' − a'·Db')`.
  set W : K[X] := ((m : ℤ) - (j + 1 : ℕ)) • (D p * (a' * b')) + p * (D a' * b' - a' * D b') with hW
  have hfactor : D (p ^ m * a') * (p ^ (j + 1) * b') - (p ^ m * a') * D (p ^ (j + 1) * b')
      = p ^ (m + j) * W := by
    rw [hleib m a', hleib (j + 1) b', hW, Nat.add_sub_cancel]
    -- expand: cancel the `pᵐ·D a'·pʲ⁺¹·b'` and `pᵐ·a'·pʲ⁺¹·D b'` symmetric terms, leaving the `Dp` terms.
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0; simp only [pow_zero, one_mul, Nat.cast_zero, zero_sub, Nat.zero_add, zsmul_eq_mul]
      push_cast; ring
    · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
      simp only [Nat.succ_sub_one, zsmul_eq_mul]
      push_cast
      rw [show m' + 1 + j = (m' + j) + 1 by ring, pow_succ]
      ring
  rw [hfactor]
  -- `νₚ(p^{m+j}·W) = (m+j) + νₚ(W)`, and `p ∤ W` gives `νₚ(W) = 0`.
  have hpne : (p : K[X]) ≠ 0 := hp.ne_zero
  have hWne : ¬ p ∣ W := by
    -- mod `p`: `W ≡ (m − (j+1))·(Dp)·(a'·b')`, a product of `p`-non-divisors.
    rw [hW]
    intro hdvd
    have hp_lead : p ∣ ((m : ℤ) - (j + 1 : ℕ)) • (D p * (a' * b')) :=
      (dvd_add_right (dvd_mul_right p _)).mp (by rwa [add_comm] at hdvd)
    rw [zsmul_eq_mul] at hp_lead
    -- the integer constant `m − (j+1) ≠ 0` (char zero, `m < j+1`) is a unit in `K[X]`.
    have hconstK : ((m : ℤ) - (j + 1 : ℕ) : K) ≠ 0 := by
      have hmj : ((m : ℤ) - (j + 1 : ℕ) : ℤ) ≠ 0 := by omega
      simpa using (Int.cast_ne_zero (α := K)).mpr hmj
    have hcast : (((m : ℤ) - (j + 1 : ℕ) : ℤ) : K[X]) = Polynomial.C ((m : ℤ) - (j + 1 : ℕ) : K) := by
      simp
    have hunit : IsUnit (((m : ℤ) - (j + 1 : ℕ) : ℤ) : K[X]) := by
      rw [hcast]; exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hconstK)
    have hp_DpAB : p ∣ D p * (a' * b') := hunit.dvd_mul_left.mp hp_lead
    rcases hp.dvd_mul.mp hp_DpAB with h | h
    · exact hnormal h
    · rcases hp.dvd_mul.mp h with h' | h'
      · exact ha' h'
      · exact hb' h'
  rw [emultiplicity_mul hp, emultiplicity_pow_self_of_prime hp, emultiplicity_eq_zero.mpr hWne,
    add_zero, show m + (j + 1) - 1 = m + j from by omega]

end DerivationNormalOrderDrop

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
(`rdeNormalDenominator_glue` is engine-agnostic, the `B/C` certificates via `toPolyG_cdivWf_exact_mul_gen`). -/
theorem cRdeNormalDenominatorG_cleared_lift_gen [CFracGcdCore α] (Dt : CPolyG α) (fuel : ℕ)
    (fnum fden gnum gden a b c h Q : CPolyG α)
    (hres : cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a, b, c, h))
    (hdn : toPolyG (cSplitFactorFastG Dt fuel fden).1 ≠ 0)
    (hfden0 : cnormG fden ≠ []) (hgden0 : cnormG gden ≠ [])
    (hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h)) fden)))
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
    (hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h0)) fden)))
    (hdvdC : toPolyG gden ∣ toPolyG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) h0) gnum))
    (hspde : cSPDEG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1 (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGen Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1 (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
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
    hnorm hdn hfden0 hgden0 hdvdB hdvdC hred
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
    (hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h0)) fden)))
    (hdvdC : toPolyG gden ∣ toPolyG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) h0) gnum))
    (hspde : cSPDEG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1 (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGen Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1 (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
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
    hprim hnorm hdn hfden0 hgden0 hdvdB hdvdC hspde hin hpoly

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
    (hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h0)) fden)))
    (hdvdC : toPolyG gden ∣ toPolyG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) h0) gnum))
    (hspde : cSPDEG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1 (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGen Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1 (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
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
    hprim hnorm hdn hfden0 hgden0 hdvdB hdvdC hspde hin hpoly

-- ★ The special monomial polynomial divides its own monomial derivative (`Dp = E·p`, §6.2 premise).
example (Dt : CPolyG (QFunNZG ℚ)) (fuel : ℕ) (hDt : toPolyG Dt ≠ 0)
    (hdeg : (toPolyG Dt).natDegree ≤ fuel) (hreg : CSplitFactorFastGRegularQ Dt fuel Dt) :
    toPolyG (cSpecialPolyG Dt fuel) ∣ toPolyG (cmonomialDeriv Dt (cSpecialPolyG Dt fuel)) :=
  toPolyG_cSpecialPolyG_dvd_cmonomialDeriv Dt fuel hDt hdeg hreg

-- ★ Derivation-generic pole order-drop, lower bound: `q^n ∣ p ⟹ q^{n−1} ∣ D p` (the §6.1 νₚ kernel half).
example {R : Type*} [CommRing R] (D : Derivation ℤ R R) {p q : R} {n : ℕ} (hdvd : q ^ n ∣ p) :
    q ^ (n - 1) ∣ D p :=
  pow_sub_one_dvd_deriv_of_pow_dvd D hdvd

-- ★ Derivation-generic pole order-drop, exact at a normal prime: `νₚ(D(pⁿ·r)) = n − 1` (Bronstein Lem 6.1.1).
example {K : Type*} [Field K] [CharZero K] (D : Derivation ℤ K[X] K[X]) {p r : K[X]} {n : ℕ}
    (hp : Prime p) (hnormal : ¬ p ∣ D p) (hn : 1 ≤ n) (hr : ¬ p ∣ r) :
    emultiplicity p (D (p ^ n * r)) = (n - 1 : ℕ) :=
  emultiplicity_deriv_eq_sub_one_of_normal D hp hnormal hn hr

/-! ### Axiom audit (the `QFunNZG ℚ` §6 RDE correctness rests only on the standard kernel axioms) -/

#print axioms cSPDECleared_of_inputs_qfunNZG
#print axioms cRischDEG_rdeCleared_qfunNZG
#print axioms toPolyG_cSpecialPolyG_dvd_cmonomialDeriv
#print axioms pow_sub_one_dvd_deriv_of_pow_dvd
#print axioms not_pow_dvd_deriv_of_normal
#print axioms emultiplicity_deriv_eq_sub_one_of_normal

end DeepWiki.SymbolicIntegration
