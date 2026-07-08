import DeepWiki.SymbolicIntegration.Computable.Tower.WellFounded
import DeepWiki.SymbolicIntegration.Computable.SplitFactorHelpers
import DeepWiki.SymbolicIntegration.Computable.FuelFreeGcd
import DeepWiki.SymbolicIntegration.Computable.FuelFreeGcd
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

/-- **M2 — full abstract correctness of `cSplitFactorFastGWf`.** Under the gcd frontier `GcdFFCorrect`,
`cSplitFactorFastGWf Dt p = (pₙ, pₛ)` denotes a general splitting factorization of `p` w.r.t. the monomial
derivation `D = implicitDeriv (toPolyG Dt)`: `toPolyG p = toPolyG pₛ · toPolyG pₙ`, `pₛ` special, and every
squarefree factor of `pₙ` normal. Well-founded induction mirroring the abstract `splitFactor`, with the
per-step bridge (M1) transferring the `IsSpecial`/`IsNormalSqfree`/degree-drop facts through `toPolyG`. -/
theorem cSplitFactorFastGWf_isSplittingFactorizationGen [CharZero (CFieldSpec.K α)]
    (hgcd : GcdFFCorrect (α := α)) (Dt : CPolyG α) :
    ∀ (p : CPolyG α), toPolyG p ≠ 0 →
      @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (toPolyG Dt)⟩ (toPolyG p)
        (toPolyG (cSplitFactorFastGWf Dt p).2) (toPolyG (cSplitFactorFastGWf Dt p).1) := by
  letI : Differential (CFieldSpec.K α)[X] := ⟨Differential.implicitDeriv (toPolyG Dt)⟩
  have hmain : ∀ (n : ℕ) (p : CPolyG α), (cnormG p : List α).length ≤ n → toPolyG p ≠ 0 →
      IsSplittingFactorizationGen (toPolyG p)
        (toPolyG (cSplitFactorFastGWf Dt p).2) (toPolyG (cSplitFactorFastGWf Dt p).1) := by
    intro n
    induction n with
    | zero =>
      intro p hn hp
      exact absurd ((cnormG_eq_nil_iff p).mp (List.length_eq_zero_iff.mp (Nat.le_zero.mp hn))) hp
    | succ n ih =>
      intro p hn hp
      rw [cSplitFactorFastGWf]
      set S := cstepGWf Dt p with hSdef
      have hAstep : Associated (toPolyG S) (splitFactorStep (toPolyG Dt) (toPolyG p)) :=
        toPolyG_cstepGWf_associated hgcd Dt p hp
      by_cases hSdeg : cdegG S = 0
      · rw [if_pos hSdeg]
        have hstepdeg : (splitFactorStep (toPolyG Dt) (toPolyG p)).natDegree = 0 := by
          rw [← natDegree_eq_of_associated hAstep, ← cdegG_eq_natDegree, hSdeg]
        have hnorm := isNormalSqfree_of_splitFactorStep_natDegree_zero (toPolyG Dt) hp hstepdeg
        have hone : toPolyG ([CField.one] : CPolyG α) = 1 := by
          simp only [denote]
          simp
        show IsSplittingFactorizationGen (toPolyG p) (toPolyG ([CField.one] : CPolyG α)) (toPolyG p)
        rw [hone]
        exact ⟨(one_mul _).symm, isSpecial_one, hnorm⟩
      · rw [if_neg hSdeg]
        have hSnorm : cnormG S ≠ [] := by
          intro h; rw [cdegG, h, List.length_nil] at hSdeg; simp at hSdeg
        have hSne : toPolyG S ≠ 0 := fun h => hSnorm ((cnormG_eq_nil_iff S).mpr h)
        have hSpos : 0 < (toPolyG S).natDegree := by
          rw [← cdegG_eq_natDegree]; omega
        have hSdvd : toPolyG S ∣ toPolyG p :=
          hAstep.dvd.trans (splitFactorStep_dvd (toPolyG Dt) hp)
        have hexact : toPolyG (cdivWf p S) * toPolyG S = toPolyG p :=
          toPolyG_cdivWf_exact p S hSnorm hSdvd
        have hpqne : toPolyG (cdivWf p S) ≠ 0 := by
          intro h; rw [h, zero_mul] at hexact; exact hp hexact.symm
        have hdegsum : (toPolyG (cdivWf p S)).natDegree + (toPolyG S).natDegree
            = (toPolyG p).natDegree := by rw [← natDegree_mul hpqne hSne, hexact]
        have hlendrop : (cnormG (cdivWf p S) : List α).length < (cnormG p : List α).length := by
          rw [length_cnormG_of_ne _ (fun h => hpqne ((cnormG_eq_nil_iff _).mp h)),
            length_cnormG_of_ne _ (fun h => hp ((cnormG_eq_nil_iff _).mp h))]
          omega
        rw [if_pos hlendrop]
        rcases hres : cSplitFactorFastGWf Dt (cdivWf p S) with ⟨qn, qs⟩
        have hih := ih (cdivWf p S) (by omega) hpqne
        rw [hres] at hih
        obtain ⟨heq, hqspec, hqnorm⟩ := hih
        refine ⟨?_, ?_, hqnorm⟩
        · simp only [denote]
          rw [mul_assoc, ← heq, ← hexact, mul_comm]
        · simp only [denote]
          exact (IsSpecial.of_associated hAstep.symm
            (isSpecial_splitFactorStep (toPolyG Dt) hp)).mul hqspec
  intro p hp
  exact hmain (cnormG p : List α).length p le_rfl hp

/-! ### M3 — discharging the gcd frontier at the `ℚ` base -/

/-- **The gcd frontier is unconditional at `ℚ`.** There `cgcdFFCoreWf = cmonicG ∘ (cgcdWf ·).1 =
cgcdMonicWf` (the plain monic Euclidean gcd), whose correctness is `associated_toPolyG_cgcdMonicWf`. -/
theorem gcdFFCorrect_Q : GcdFFCorrect (α := ℚ) := fun a b => associated_toPolyG_cgcdMonicWf a b

/-- **The gcd frontier as a resolvable `Fact` at the `ℚ` base.** Lets `[Fact (GcdFFCorrect (α := ℚ))]`
resolve automatically (the tower case above `ℚ` is the PRS-regularity frontier — no such instance there). -/
instance instFactGcdFFCorrectQ : Fact (GcdFFCorrect (α := ℚ)) := ⟨gcdFFCorrect_Q⟩

/-- `CharZero (CFieldSpec.K ℚ) = CharZero ℚ`: local instance for the `ℚ`-base split correctness. -/
instance : CharZero (CFieldSpec.K ℚ) := inferInstanceAs (CharZero ℚ)

/-- **Unconditional abstract correctness of `cSplitFactorFastGWf` at the `ℚ` base.** For `p ≠ 0`,
`cSplitFactorFastGWf Dt p` is a genuine general splitting factorization of `p` — no gcd hypothesis. -/
theorem cSplitFactorFastGWf_isSplittingFactorizationGen_Q (Dt p : CPolyG ℚ) (hp : toPolyG p ≠ 0) :
    @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (toPolyG Dt)⟩ (toPolyG p)
      (toPolyG (cSplitFactorFastGWf Dt p).2) (toPolyG (cSplitFactorFastGWf Dt p).1) :=
  cSplitFactorFastGWf_isSplittingFactorizationGen gcdFFCorrect_Q Dt p hp

end DeepWiki.SymbolicIntegration
