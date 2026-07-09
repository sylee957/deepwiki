import DeepWiki.SymbolicIntegration.Engine.Tower.RischDE
import DeepWiki.SymbolicIntegration.Engine.RatFuncValuation.PolynomialOrderDrop
import DeepWiki.SymbolicIntegration.Engine.RischDE.TowerGlue
import DeepWiki.SymbolicIntegration.Engine.QFunNZGDiffSpec

/-! # Carrier-generic RDE cleared-identity building blocks

Carrier-generic, gcd-agnostic RDE helper lemmas for cleared SPDE and normal-denominator
certificates. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ### Generic helper lemmas

Carrier-generic SPDE certificate helpers, stated over `{α} [CField α] [CFieldSpec α]` with the
gcd `g` taken abstractly. -/

/-- After dividing `a, b` by a nonzero gcd `g`, the gcd of `bd, ad` is a unit. -/
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

/-- `toPolyG (cdivWf a g) * toPolyG g = toPolyG a` from `g ~ gcd(a, b)` (`g ∣ a`) and `g ≠ 0`. -/
theorem cdivWf_a_exact_of_gcd {α : Type*} [CField α] [CFieldSpec α] (a b g : CPolyG α)
    (hg0 : cnormG g ≠ [])
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b))) :
    toPolyG (cdivWf a g) * toPolyG g = toPolyG a := by
  have hgdvd : toPolyG g ∣ toPolyG a := hgassoc.dvd.trans (gcd_dvd_left _ _)
  exact toPolyG_cdivWf_exact a g hg0 hgdvd

/-- `toPolyG (cdivWf b g) * toPolyG g = toPolyG b` from `g ~ gcd(a, b)` (`g ∣ b`). -/
theorem cdivWf_b_exact_of_gcd {α : Type*} [CField α] [CFieldSpec α] (a b g : CPolyG α)
    (hg0 : cnormG g ≠ [])
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b))) :
    toPolyG (cdivWf b g) * toPolyG g = toPolyG b := by
  have hgdvd : toPolyG g ∣ toPolyG b := hgassoc.dvd.trans (gcd_dvd_right _ _)
  exact toPolyG_cdivWf_exact b g hg0 hgdvd

/-- `toPolyG (cdivWf c g) * toPolyG g = toPolyG c` from `cdvdGWf g c = true` (`g ∣ c`). -/
theorem cdivWf_c_exact_of_cdvdGWf {α : Type*} [CField α] [CFieldSpec α] (c g : CPolyG α)
    (hg0 : cnormG g ≠ [])
    (hdvd : cdvdGWf g c = true) :
    toPolyG (cdivWf c g) * toPolyG g = toPolyG c := by
  have hgdvd : toPolyG g ∣ toPolyG c := dvd_of_cdvdGWf g c hg0 hdvd
  exact toPolyG_cdivWf_exact c g hg0 hgdvd

/-- One `cSPDEG` peel's cleared lifting: with `D = implicitDeriv (toPolyG Dt)`, Bézout certificate
`bd·r + ad·z = cd`, and `h` solving the reduced equation, `q = ad·h + r` solves `ad·D(q) + bd·q = cd`. -/
theorem cSPDE_peel_cleared_gen {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    (Dt ad bd cd r z h : CPolyG α)
    (hbez : toPolyG bd * toPolyG r + toPolyG ad * toPolyG z = toPolyG cd)
    (hred : toPolyG ad * Differential.implicitDeriv (toPolyG Dt) (toPolyG h)
        + (toPolyG bd + Differential.implicitDeriv (toPolyG Dt) (toPolyG ad)) * toPolyG h
      = toPolyG z - Differential.implicitDeriv (toPolyG Dt) (toPolyG r)) :
    toPolyG ad * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG ad h) r))
        + toPolyG bd * toPolyG (caddG (cmulG ad h) r)
      = toPolyG cd := by
  simp only [denote]
  exact spde_step_glue (Differential.implicitDeriv (toPolyG Dt))
    (toPolyG ad) (toPolyG bd) (toPolyG cd) (toPolyG r) (toPolyG z) (toPolyG h) hbez hred

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-! ### Generic normal-denominator cleared lifting and special-denominator primitive case -/

omit [CDiffField α] [CDiffFieldSpec α] in
/-- `toPolyG (cdivWf p q) * toPolyG q = toPolyG p` from `toPolyG q ∣ toPolyG p` (nonzero divisor). -/
theorem toPolyG_cdivWf_exact_mul_gen (p q : CPolyG α)
    (hq0 : cnormG q ≠ [])
    (hQdvd : toPolyG q ∣ toPolyG p) :
    toPolyG (cdivWf p q) * toPolyG q = toPolyG p :=
  toPolyG_cdivWf_exact p q hq0 hQdvd

end DeepWiki.SymbolicIntegration
