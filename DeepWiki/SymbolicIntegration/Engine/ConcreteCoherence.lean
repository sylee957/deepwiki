import DeepWiki.ComputableAlgebra.GenericPolyEngine
import DeepWiki.SymbolicIntegration.Compute.LogToAtan
import DeepWiki.SymbolicIntegration.Compute.Correctness
import DeepWiki.SymbolicIntegration.Compute.RationalFunction

/-! # Coherence of the generic polynomial engine with the concrete `CPolyQ := List ℚ` engine

Coherence lemmas showing the generic engine specializes at `α = ℚ` back to the concrete
`Compute.*` engine (`cadd (α := ℚ) = cadd`, …, `toPoly (α := ℚ) = toPoly`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPoly

variable {α : Type*} [CField α]

/-! ### Coherence with the concrete `CPolyQ` engine at `α = ℚ` -/

/-- `cadd` at `ℚ` is the concrete `cadd` (both add coefficientwise with `ℚ`'s `+`). -/
theorem caddG_eq_cadd : (cadd : CPoly ℚ → CPoly ℚ → CPoly ℚ) = Compute.cadd := by
  funext p q
  induction p generalizing q with
  | nil => rfl
  | cons a as ih => cases q with
    | nil => rfl
    | cons b bs => show CField.add a b :: cadd as bs = _; rw [ih]; rfl

/-- `cneg` at `ℚ` is the concrete `cneg`. -/
theorem cnegG_eq_cneg : (cneg : CPoly ℚ → CPoly ℚ) = Compute.cneg := rfl

/-- `csub` at `ℚ` is the concrete `csub`. -/
theorem csubG_eq_csub : (csub : CPoly ℚ → CPoly ℚ → CPoly ℚ) = Compute.csub := by
  funext p q
  rw [csub, Compute.csub, cnegG_eq_cneg, congrFun (congrFun caddG_eq_cadd _) _]

/-- `cscale` at `ℚ` is the concrete `cscale`. -/
theorem cscaleG_eq_cscale (c : ℚ) : (cscale c : CPoly ℚ → CPoly ℚ) = Compute.cscale c := rfl

/-- `cshift` at `ℚ` is the concrete `cshift`. -/
theorem cshiftG_eq_cshift (k : ℕ) : (cshift k : CPoly ℚ → CPoly ℚ) = Compute.cshift k := by
  funext p
  induction k generalizing p with
  | zero => rfl
  | succ n ih => show CField.zero :: cshift n p = _; rw [ih]; rfl

/-- `cmul` at `ℚ` is the concrete `cmul`. -/
theorem cmulG_eq_cmul : (cmul : CPoly ℚ → CPoly ℚ → CPoly ℚ) = Compute.cmul := by
  funext p q
  induction p generalizing q with
  | nil => rfl
  | cons a as ih =>
    show cadd (cscale a q) (CField.zero :: cmul as q) = Compute.cmul (a :: as) q
    rw [cscaleG_eq_cscale, ih, congrFun (congrFun caddG_eq_cadd _) _]; rfl

/-- `cnorm` at `ℚ` is the concrete `cnorm`. -/
theorem cnormG_eq_cnorm : (cnorm : CPoly ℚ → CPoly ℚ) = Compute.cnorm := by
  funext p
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [cnormG_cons_eq, Compute.cnorm_cons_eq, ih]
    cases Compute.cnorm as with
    | nil =>
      show (if (decide (a = 0) = true) then ([] : CPoly ℚ) else [a]) = (if a = 0 then [] else [a])
      by_cases ha : a = 0 <;> simp [ha]
    | cons b bs => rfl

/-- `cisZero` at `ℚ` is the concrete `cisZero`. -/
theorem cisZeroG_eq_cisZero : (cisZero : CPoly ℚ → Bool) = Compute.cisZero := by
  funext p
  rw [cisZero, cnormG_eq_cnorm, Compute.cisZero]
  cases h : Compute.cnorm p <;> simp

/-- `clead` at `ℚ` is the concrete `clead`. -/
theorem cleadG_eq_clead : (clead : CPoly ℚ → ℚ) = Compute.clead := by
  funext p
  rw [clead, Compute.clead, cnormG_eq_cnorm]
  rfl

/-- `toPoly` at `ℚ` is the concrete `toPoly` (`toK = id`, `CFieldSpec.K ℚ = ℚ`). -/
theorem toPolyG_eq_toPoly : (toPoly : CPoly ℚ → ℚ[X]) = Compute.toPoly := by
  funext p
  induction p with
  | nil => rfl
  | cons a as ih => show Polynomial.C (CFieldSpec.toK a) + X * toPoly as = _; rw [ih]; rfl

/-- `cnsmul` at `ℚ` is multiplication by the natural-number cast: `cnsmul k a = (k : ℚ) * a`. -/
theorem nsmulG_eq_natCast_mul (k : ℕ) (a : ℚ) : (cnsmul k a : ℚ) = (k : ℚ) * a := by
  induction k with
  | zero => show (CField.zero : ℚ) = _; rw [show (CField.zero : ℚ) = 0 from rfl]; simp
  | succ n ih => rw [cnsmul]; show a + cnsmul n a = _; rw [ih]; push_cast; ring

/-- `cderiv` at `ℚ` is the concrete `cderiv`. -/
theorem cderivG_eq_cderiv : (cderiv : CPoly ℚ → CPoly ℚ) = Compute.cderiv := by
  have hgo : ∀ (k : ℕ) (as : CPoly ℚ), cderiv.go k as = Compute.cderiv.go k as := by
    intro k as
    induction as generalizing k with
    | nil => rfl
    | cons b bs ih =>
      show cnsmul k b :: cderiv.go (k + 1) bs = ((k : ℚ) * b) :: Compute.cderiv.go (k + 1) bs
      rw [ih, nsmulG_eq_natCast_mul]
  funext p
  cases p with
  | nil => rfl
  | cons a as => show cderiv.go 1 as = Compute.cderiv.go 1 as; rw [hgo]

end CPoly

end DeepWiki.SymbolicIntegration
