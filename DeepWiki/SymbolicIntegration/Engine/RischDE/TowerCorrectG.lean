import DeepWiki.SymbolicIntegration.Engine.Tower.RischDE
import DeepWiki.SymbolicIntegration.Engine.RischDE.TowerGlue
import DeepWiki.SymbolicIntegration.Engine.Tower.CarrierRec

/-! # Carrier-generic RDE cleared-identity building blocks

Carrier-generic, gcd-agnostic RDE helper lemmas for cleared SPDE and normal-denominator
certificates. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

/-! ### Generic helper lemmas

Carrier-generic SPDE certificate helpers, stated over `{α} [CField α] [CFieldSpec α]` with the
gcd `g` taken abstractly. -/

/-- After dividing `a, b` by a nonzero gcd `g`, the gcd of `bd, ad` is a unit. -/
theorem gcdExt_isUnit_of_divided {α : Type*} [CField α] [CFieldSpec α]
    (a b ad bd g : DensePoly α) (hgne : toPoly g ≠ 0)
    (hgassoc : Associated (toPoly g) (gcd (toPoly a) (toPoly b)))
    (hdiva : toPoly ad * toPoly g = toPoly a)
    (hdivb : toPoly bd * toPoly g = toPoly b) :
    IsUnit (toPoly (CPolyEuclidean.gcdExt bd ad).1) := by
  have hdvd := LawfulCPolyEuclidean.gcdExt_dvd (P := DensePoly) bd ad
  have hdvd' :
      toPoly (CPolyEuclidean.gcdExt bd ad).1 ∣ toPoly bd ∧
        toPoly (CPolyEuclidean.gcdExt bd ad).1 ∣ toPoly ad := by
    simpa only [toPoly_list_eq] using hdvd
  obtain ⟨hGbd, hGad⟩ := hdvd'
  set G := toPoly (CPolyEuclidean.gcdExt bd ad).1 with hGdef
  have hGg_a : G * toPoly g ∣ toPoly a := by rw [← hdiva]; exact mul_dvd_mul_right hGad _
  have hGg_b : G * toPoly g ∣ toPoly b := by rw [← hdivb]; exact mul_dvd_mul_right hGbd _
  have hGg_gcd : G * toPoly g ∣ gcd (toPoly a) (toPoly b) := dvd_gcd hGg_a hGg_b
  have hGg_g : G * toPoly g ∣ toPoly g := hGg_gcd.trans hgassoc.symm.dvd
  obtain ⟨k, hk⟩ := hGg_g
  have hcancel : toPoly g * 1 = toPoly g * (G * k) := by rw [mul_one]; nth_rewrite 1 [hk]; ring
  have hG1 : G ∣ 1 := ⟨k, mul_left_cancel₀ hgne hcancel⟩
  exact isUnit_of_dvd_one hG1

/-- `toPoly (CPolyEuclidean.div a g) * toPoly g = toPoly a` from `g ~ gcd(a, b)` (`g ∣ a`) and `g ≠ 0`. -/
theorem div_a_exact_of_gcd {α : Type*} [CField α] [CFieldSpec α] (a b g : DensePoly α)
    (hg0 : cnorm g ≠ [])
    (hgassoc : Associated (toPoly g) (gcd (toPoly a) (toPoly b))) :
    toPoly (CPolyEuclidean.div a g) * toPoly g = toPoly a := by
  have hgdvd : toPoly g ∣ toPoly a := hgassoc.dvd.trans (gcd_dvd_left _ _)
  exact toPolyG_div_exact a g hg0 hgdvd

/-- `toPoly (CPolyEuclidean.div b g) * toPoly g = toPoly b` from `g ~ gcd(a, b)` (`g ∣ b`). -/
theorem div_b_exact_of_gcd {α : Type*} [CField α] [CFieldSpec α] (a b g : DensePoly α)
    (hg0 : cnorm g ≠ [])
    (hgassoc : Associated (toPoly g) (gcd (toPoly a) (toPoly b))) :
    toPoly (CPolyEuclidean.div b g) * toPoly g = toPoly b := by
  have hgdvd : toPoly g ∣ toPoly b := hgassoc.dvd.trans (gcd_dvd_right _ _)
  exact toPolyG_div_exact b g hg0 hgdvd

/-- `toPoly (CPolyEuclidean.div c g) * toPoly g = toPoly c` from `CPolyEuclidean.dvd g c = true` (`g ∣ c`). -/
theorem div_c_exact_of_dvd_eq_true {α : Type*} [CField α] [CFieldSpec α] (c g : DensePoly α)
    (hg0 : cnorm g ≠ [])
    (hdvd : CPolyEuclidean.dvd g c = true) :
    toPoly (CPolyEuclidean.div c g) * toPoly g = toPoly c := by
  have hg0' : CPoly.toPoly g ≠ 0 := by
    rw [toPoly_list_eq]
    exact fun h => hg0 ((cnormG_eq_nil_iff _).mpr h)
  have hgdvd : toPoly g ∣ toPoly c := by
    simpa only [toPoly_list_eq] using
      CPolyEuclidean.toPoly_dvd_of_dvd_eq_true g c hg0' hdvd
  exact toPolyG_div_exact c g hg0 hgdvd

/-- One `cSPDE` peel's cleared lifting: with `D = implicitDeriv (toPoly Dt)`, Bézout certificate
`bd·r + ad·z = cd`, and `h` solving the reduced equation, `q = ad·h + r` solves `ad·D(q) + bd·q = cd`. -/
theorem cSPDE_peel_cleared_gen {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    (Dt ad bd cd r z h : DensePoly α)
    (hbez : toPoly bd * toPoly r + toPoly ad * toPoly z = toPoly cd)
    (hred : toPoly ad * Differential.implicitDeriv (toPoly Dt) (toPoly h)
        + (toPoly bd + Differential.implicitDeriv (toPoly Dt) (toPoly ad)) * toPoly h
      = toPoly z - Differential.implicitDeriv (toPoly Dt) (toPoly r)) :
    toPoly ad * Differential.implicitDeriv (toPoly Dt) (toPoly (cadd (cmul ad h) r))
        + toPoly bd * toPoly (cadd (cmul ad h) r)
      = toPoly cd := by
  simp only [denote]
  exact spde_step_glue (Differential.implicitDeriv (toPoly Dt))
    (toPoly ad) (toPoly bd) (toPoly cd) (toPoly r) (toPoly z) (toPoly h) hbez hred

end DeepWiki.SymbolicIntegration
