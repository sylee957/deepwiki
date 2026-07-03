import DeepWiki.SymbolicIntegration.Computable.GenericPolyEngine
import DeepWiki.SymbolicIntegration.Compute.LogToAtan
import DeepWiki.SymbolicIntegration.Compute.Correctness
import DeepWiki.SymbolicIntegration.Compute.RationalFunction

/-! # Coherence of the generic polynomial engine with the concrete `CPoly := List ℚ` engine

Coherence lemmas showing the generic engine specializes at `α = ℚ` back to the concrete
`Compute.*` engine (`caddG (α := ℚ) = cadd`, …, `toPolyG (α := ℚ) = toPoly`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### Coherence with the concrete `CPoly` engine at `α = ℚ` -/

/-- `caddG` at `ℚ` is the concrete `cadd` (both add coefficientwise with `ℚ`'s `+`). -/
theorem caddG_eq_cadd : (caddG : CPolyG ℚ → CPolyG ℚ → CPolyG ℚ) = Compute.cadd := by
  funext p q
  induction p generalizing q with
  | nil => rfl
  | cons a as ih => cases q with
    | nil => rfl
    | cons b bs => show CField.add a b :: caddG as bs = _; rw [ih]; rfl

/-- `cnegG` at `ℚ` is the concrete `cneg`. -/
theorem cnegG_eq_cneg : (cnegG : CPolyG ℚ → CPolyG ℚ) = Compute.cneg := rfl

/-- `cscaleG` at `ℚ` is the concrete `cscale`. -/
theorem cscaleG_eq_cscale (c : ℚ) : (cscaleG c : CPolyG ℚ → CPolyG ℚ) = Compute.cscale c := rfl

/-- `cshiftG` at `ℚ` is the concrete `cshift`. -/
theorem cshiftG_eq_cshift (k : ℕ) : (cshiftG k : CPolyG ℚ → CPolyG ℚ) = Compute.cshift k := by
  funext p
  induction k generalizing p with
  | zero => rfl
  | succ n ih => show CField.zero :: cshiftG n p = _; rw [ih]; rfl

/-- `cmulG` at `ℚ` is the concrete `cmul`. -/
theorem cmulG_eq_cmul : (cmulG : CPolyG ℚ → CPolyG ℚ → CPolyG ℚ) = Compute.cmul := by
  funext p q
  induction p generalizing q with
  | nil => rfl
  | cons a as ih =>
    show caddG (cscaleG a q) (CField.zero :: cmulG as q) = Compute.cmul (a :: as) q
    rw [cscaleG_eq_cscale, ih, congrFun (congrFun caddG_eq_cadd _) _]; rfl

/-- `cnormG` at `ℚ` is the concrete `cnorm`. -/
theorem cnormG_eq_cnorm : (cnormG : CPolyG ℚ → CPolyG ℚ) = Compute.cnorm := by
  funext p
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [cnormG_cons_eq, Compute.cnorm_cons_eq, ih]
    cases Compute.cnorm as with
    | nil =>
      show (if (decide (a = 0) = true) then ([] : CPolyG ℚ) else [a]) = (if a = 0 then [] else [a])
      by_cases ha : a = 0 <;> simp [ha]
    | cons b bs => rfl

/-- `cisZeroG` at `ℚ` is the concrete `cisZero`. -/
theorem cisZeroG_eq_cisZero : (cisZeroG : CPolyG ℚ → Bool) = Compute.cisZero := by
  funext p
  rw [cisZeroG, cnormG_eq_cnorm, Compute.cisZero]
  cases h : Compute.cnorm p <;> simp

/-- `toPolyG` at `ℚ` is the concrete `toPoly` (`toK = id`, `CFieldSpec.K ℚ = ℚ`). -/
theorem toPolyG_eq_toPoly : (toPolyG : CPolyG ℚ → ℚ[X]) = Compute.toPoly := by
  funext p
  induction p with
  | nil => rfl
  | cons a as ih => show Polynomial.C (CFieldSpec.toK a) + X * toPolyG as = _; rw [ih]; rfl

end CPolyG

end DeepWiki.SymbolicIntegration
