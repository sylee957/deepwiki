import DeepWiki.SymbolicIntegration.Computable.Tower.WellFounded
import DeepWiki.SymbolicIntegration.Computable.SplitFactorHelpers
import DeepWiki.SymbolicIntegration.Computable.FuelFreeGcd
import DeepWiki.SymbolicIntegration.Computable.FieldGcd
import DeepWiki.SymbolicIntegration.SquarefreeFactorization

/-! # Abstract correctness of the fuel-free splitting factorization `cSplitFactorFastGWf`

The computable `cSplitFactorFastGWf` mirrors the abstract `splitFactor`
(`CanonicalRepresentation.splitFactor_isSplittingFactorizationGen`). This file reduces its correctness to
the single fraction-free gcd frontier `GcdFFCorrect` — dischargeable at the `ℚ` base where the gcd is the
plain Euclidean gcd. M1: the per-step bridge `toPolyG (cstepGWf Dt p) ~ splitFactorStep (toPolyG Dt) (toPolyG p)`.
-/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]

/-- The fraction-free gcd frontier: `cgcdFFCoreWf` is a genuine gcd through `toPolyG`. Holds
unconditionally at `ℚ` (the Euclidean gcd); the tower case is the engine's PRS-regularity frontier. -/
def GcdFFCorrect : Prop :=
  ∀ a b : CPolyG α,
    Associated (toPolyG (CFracGcdCoreWf.cgcdFFCoreWf a b)) (gcd (toPolyG a) (toPolyG b))

/-- **M1 — the per-step bridge.** Under the gcd frontier, the computable split step
`cstepGWf Dt p = cdivWf (gcd_t(p, Dp)) (gcd_t(p, dp/dt))` denotes the abstract
`splitFactorStep (toPolyG Dt) (toPolyG p) = gcd(P, D P)/gcd(P, dP)` up to associates. -/
theorem toPolyG_cstepGWf_associated [CharZero (CFieldSpec.K α)]
    (hgcd : GcdFFCorrect (α := α)) (Dt p : CPolyG α) (hp : toPolyG p ≠ 0) :
    Associated (toPolyG (cstepGWf Dt p)) (splitFactorStep (toPolyG Dt) (toPolyG p)) := by
  set A := CFracGcdCoreWf.cgcdFFCoreWf p (cmonomialDeriv Dt p) with hAdef
  set B := CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p) with hBdef
  have hA : Associated (toPolyG A)
      (gcd (toPolyG p) (Differential.implicitDeriv (toPolyG Dt) (toPolyG p))) := by
    have := hgcd p (cmonomialDeriv Dt p)
    rwa [toPolyG_cmonomialDeriv] at this
  have hB : Associated (toPolyG B) (gcd (toPolyG p) (derivative (toPolyG p))) := by
    have := hgcd p (cderivG p)
    rwa [toPolyG_cderivG] at this
  have hgcdBne : gcd (toPolyG p) (derivative (toPolyG p)) ≠ 0 := by
    rw [Ne, gcd_eq_zero_iff]; exact fun h => hp h.1
  have hB0 : toPolyG B ≠ 0 := fun h => hgcdBne (hB.eq_zero_iff.mp h)
  have hBnorm : cnormG B ≠ [] := fun h => hB0 ((cisZeroG_iff B).mp (by simp [cisZeroG, h]))
  have hBA : toPolyG B ∣ toPolyG A :=
    hB.dvd.trans ((gcd_derivative_dvd_gcd_implicitDeriv (toPolyG Dt) hp).trans hA.symm.dvd)
  have hexact : toPolyG (cdivWf A B) * toPolyG B = toPolyG A := toPolyG_cdivWf_exact A B hBnorm hBA
  have hstepB : Associated (splitFactorStep (toPolyG Dt) (toPolyG p) * toPolyG B) (toPolyG A) := by
    refine (Associated.mul_left _ hB).trans ?_
    rw [splitFactorStep, mul_comm,
      EuclideanDomain.mul_div_cancel' hgcdBne (gcd_derivative_dvd_gcd_implicitDeriv (toPolyG Dt) hp)]
    exact hA.symm
  show Associated (toPolyG (cdivWf A B)) (splitFactorStep (toPolyG Dt) (toPolyG p))
  have key : Associated (toPolyG (cdivWf A B) * toPolyG B)
      (splitFactorStep (toPolyG Dt) (toPolyG p) * toPolyG B) := by
    rw [hexact]; exact hstepB.symm
  exact key.of_mul_right (Associated.refl _) hB0

end DeepWiki.SymbolicIntegration
