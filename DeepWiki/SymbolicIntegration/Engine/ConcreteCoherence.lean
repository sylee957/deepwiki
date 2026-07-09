import DeepWiki.ComputableAlgebra.GenericPolyEngine
import DeepWiki.SymbolicIntegration.Compute.LogToAtan
import DeepWiki.SymbolicIntegration.Compute.Correctness
import DeepWiki.SymbolicIntegration.Compute.RationalFunction

/-! # Coherence of the generic polynomial engine with the concrete `CPoly ℚ := List ℚ` engine

The concrete `ℚ` engine now re-exports the generic ring-engine ops directly (`Compute.{cnorm,cadd,cneg,
cscale,cshift,cmul,clead}` are `export`s of the generic `CPoly.*`, so `Compute.cadd` *is* `CPoly.cadd` —
no separate constant to bridge). What remains here relates the genuinely-separate concrete defs —
`Compute.toPoly` (the `ℚ` denotation), `Compute.cderiv`, and the `ℚ`-cast of `cnsmul` — to the generic
engine at `α = ℚ`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPoly

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
