import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded
import DeepWiki.SymbolicIntegration.Engine.Tower.GcdFFCorrect
import DeepWiki.SymbolicIntegration.Engine.SplitFactorHelpers
import DeepWiki.ComputableAlgebra.PolyEuclideanDense
import DeepWiki.SymbolicIntegration.SquarefreeFactorization

/-! # Abstract correctness of the fuel-free splitting factorization `cSplitFactorFast`

The computable `cSplitFactorFast` mirrors the abstract `splitFactor`
(`CanonicalRepresentation.splitFactor_isSplittingFactorizationGen`). Correctness depends on the selected
gcd only through `LawfulCPolyGcd`.
M1: the per-step bridge `toPoly (cstep Dt p) ~ splitFactorStep (toPoly Dt) (toPoly p)`.
-/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly

universe u v

variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec α]
  [CPolyGcd DensePoly α] [LawfulCPolyGcd.{u,v} DensePoly α]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- Dense-denotation form of the selected lawful gcd's associatedness law. -/
private theorem selectedGcd_associated (p q : DensePoly α) :
    Associated (toPoly (CPolyGcd.compute p q)) (gcd (toPoly p) (toPoly q)) := by
  obtain ⟨hleft, hright, hgreatest⟩ := LawfulCPolyGcd.compute_isGCD' p q
  have hleft' : toPoly (CPolyGcd.compute p q) ∣ toPoly p := by
    simpa only [toPoly_list_eq] using hleft
  have hright' : toPoly (CPolyGcd.compute p q) ∣ toPoly q := by
    simpa only [toPoly_list_eq] using hright
  apply associated_of_dvd_dvd (dvd_gcd hleft' hright')
  have h := hgreatest (gcd (toPoly p) (toPoly q))
      (by simpa only [toPoly_list_eq] using gcd_dvd_left (toPoly p) (toPoly q))
      (by simpa only [toPoly_list_eq] using gcd_dvd_right (toPoly p) (toPoly q))
  simpa only [toPoly_list_eq] using h

/-- **M1 — the per-step bridge.** Under the gcd frontier, the computable split step
`cstep Dt p = CPolyEuclidean.div (gcd_t(p, Dp)) (gcd_t(p, dp/dt))` denotes the abstract
`splitFactorStep (toPoly Dt) (toPoly p) = gcd(P, D P)/gcd(P, dP)` up to associates. -/
theorem toPolyG_cstepG_associated [CharZero (CFieldSpec.K α)]
    (Dt p : DensePoly α) (hp : toPoly p ≠ 0) :
    Associated (toPoly (cstep Dt p)) (splitFactorStep (toPoly Dt) (toPoly p)) := by
  set A := CPolyGcd.compute p (CPolyEngine.monomialDeriv Dt p) with hAdef
  set B := CPolyGcd.compute p (cderiv p) with hBdef
  have hA : Associated (toPoly A)
      (gcd (toPoly p) (Differential.implicitDeriv (toPoly Dt) (toPoly p))) := by
    have hraw := selectedGcd_associated p (CPolyEngine.monomialDeriv Dt p)
    simpa only [hAdef, toPolyG_cmonomialDeriv] using hraw
  have hB : Associated (toPoly B) (gcd (toPoly p) (derivative (toPoly p))) := by
    have hraw := selectedGcd_associated p (cderiv p)
    simpa only [hBdef, toPolyG_cderivG] using hraw
  have hgcdBne : gcd (toPoly p) (derivative (toPoly p)) ≠ 0 := by
    rw [Ne, gcd_eq_zero_iff]; exact fun h => hp h.1
  have hB0 : toPoly B ≠ 0 := fun h => hgcdBne (hB.eq_zero_iff.mp h)
  have hBnorm : cnorm B ≠ [] := fun h => hB0 ((cisZeroG_iff B).mp (by simp [cisZero, h]))
  have hBA : toPoly B ∣ toPoly A :=
    hB.dvd.trans ((gcd_derivative_dvd_gcd_implicitDeriv (toPoly Dt) hp).trans hA.symm.dvd)
  have hexact : toPoly (CPolyEuclidean.div A B) * toPoly B = toPoly A := by
    simpa only [CPolyEuclidean.div_dense_eq] using toPolyG_div_exact A B hBnorm hBA
  have hstepB : Associated (splitFactorStep (toPoly Dt) (toPoly p) * toPoly B) (toPoly A) := by
    refine (Associated.mul_left _ hB).trans ?_
    rw [splitFactorStep, mul_comm,
      EuclideanDomain.mul_div_cancel' hgcdBne (gcd_derivative_dvd_gcd_implicitDeriv (toPoly Dt) hp)]
    exact hA.symm
  show Associated (toPoly (CPolyEuclidean.div A B)) (splitFactorStep (toPoly Dt) (toPoly p))
  have key : Associated (toPoly (CPolyEuclidean.div A B) * toPoly B)
      (splitFactorStep (toPoly Dt) (toPoly p) * toPoly B) := by
    rw [hexact]; exact hstepB.symm
  exact key.of_mul_right (Associated.refl _) hB0

/-- **M2 — full abstract correctness of `cSplitFactorFast`.** Under `CgcdBCorrect cgcdFFCoreWf`,
`cSplitFactorFast Dt p = (pₙ, pₛ)` denotes a general splitting factorization of `p` w.r.t. the monomial
derivation `D = implicitDeriv (toPoly Dt)`: `toPoly p = toPoly pₛ · toPoly pₙ`, `pₛ` special, and every
squarefree factor of `pₙ` normal. Well-founded induction mirroring the abstract `splitFactor`, with the
per-step bridge (M1) transferring the `IsSpecial`/`IsNormalSqfree`/degree-drop facts through `toPoly`. -/
theorem cSplitFactorFastG_isSplittingFactorizationGen [CharZero (CFieldSpec.K α)]
    (Dt : DensePoly α) :
    ∀ (p : DensePoly α), toPoly p ≠ 0 →
      @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (toPoly Dt)⟩ (toPoly p)
        (toPoly (cSplitFactorFast Dt p).2) (toPoly (cSplitFactorFast Dt p).1) := by
  letI : Differential (CFieldSpec.K α)[X] := ⟨Differential.implicitDeriv (toPoly Dt)⟩
  have hmain : ∀ (n : ℕ) (p : DensePoly α), (cnorm p : List α).length ≤ n → toPoly p ≠ 0 →
      IsSplittingFactorizationGen (toPoly p)
        (toPoly (cSplitFactorFast Dt p).2) (toPoly (cSplitFactorFast Dt p).1) := by
    intro n
    induction n with
    | zero =>
      intro p hn hp
      exact absurd ((cnormG_eq_nil_iff p).mp (List.length_eq_zero_iff.mp (Nat.le_zero.mp hn))) hp
    | succ n ih =>
      intro p hn hp
      rw [cSplitFactorFast]
      set S := cstep Dt p with hSdef
      have hAstep : Associated (toPoly S) (splitFactorStep (toPoly Dt) (toPoly p)) :=
        toPolyG_cstepG_associated Dt p hp
      by_cases hSdeg : cdeg S = 0
      · rw [if_pos hSdeg]
        have hstepdeg : (splitFactorStep (toPoly Dt) (toPoly p)).natDegree = 0 := by
          rw [← natDegree_eq_of_associated hAstep, ← cdegG_eq_natDegree, hSdeg]
        have hnorm := isNormalSqfree_of_splitFactorStep_natDegree_zero (toPoly Dt) hp hstepdeg
        have hone : toPoly ([CCommRing.one] : DensePoly α) = 1 := by
          simp only [denote]
          simp
        show IsSplittingFactorizationGen (toPoly p) (toPoly ([CCommRing.one] : DensePoly α)) (toPoly p)
        rw [hone]
        exact ⟨(one_mul _).symm, isSpecial_one, hnorm⟩
      · rw [if_neg hSdeg]
        have hSnorm : cnorm S ≠ [] := by
          intro h; rw [cdeg, h, List.length_nil] at hSdeg; simp at hSdeg
        have hSne : toPoly S ≠ 0 := fun h => hSnorm ((cnormG_eq_nil_iff S).mpr h)
        have hSpos : 0 < (toPoly S).natDegree := by
          rw [← cdegG_eq_natDegree]; omega
        have hSdvd : toPoly S ∣ toPoly p :=
          hAstep.dvd.trans (splitFactorStep_dvd (toPoly Dt) hp)
        have hexact : toPoly (CPolyEuclidean.div p S) * toPoly S = toPoly p := by
          simpa only [CPolyEuclidean.div_dense_eq] using toPolyG_div_exact p S hSnorm hSdvd
        have hpqne : toPoly (CPolyEuclidean.div p S) ≠ 0 := by
          intro h; rw [h, zero_mul] at hexact; exact hp hexact.symm
        have hdegsum : (toPoly (CPolyEuclidean.div p S)).natDegree + (toPoly S).natDegree
            = (toPoly p).natDegree := by rw [← natDegree_mul hpqne hSne, hexact]
        have hlendrop : (cnorm (CPolyEuclidean.div p S) : List α).length < (cnorm p : List α).length := by
          rw [length_cnormG_of_ne _ (fun h => hpqne ((cnormG_eq_nil_iff _).mp h)),
            length_cnormG_of_ne _ (fun h => hp ((cnormG_eq_nil_iff _).mp h))]
          omega
        rw [if_pos hlendrop]
        rcases hres : cSplitFactorFast Dt (CPolyEuclidean.div p S) with ⟨qn, qs⟩
        have hih := ih (CPolyEuclidean.div p S) (by omega) hpqne
        rw [hres] at hih
        obtain ⟨heq, hqspec, hqnorm⟩ := hih
        refine ⟨?_, ?_, hqnorm⟩
        · simp only [denote]
          rw [mul_assoc, ← heq, ← hexact, mul_comm]
        · simp only [denote]
          exact (IsSpecial.of_associated hAstep.symm
            (isSpecial_splitFactorStep (toPoly Dt) hp)).mul hqspec
  intro p hp
  exact hmain (cnorm p : List α).length p le_rfl hp

/-- The selected dense split implementation computes a general splitting factorization. -/
theorem CPoly.splitFactor_isSplittingFactorizationGen [CharZero (CFieldSpec.K α)]
    (Dt : DensePoly α) :
    ∀ (p : DensePoly α), DensePoly.toPoly p ≠ 0 →
      @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (DensePoly.toPoly Dt)⟩
        (DensePoly.toPoly p) (DensePoly.toPoly (CPoly.splitFactor Dt p).2)
        (DensePoly.toPoly (CPoly.splitFactor Dt p).1) := by
  intro p hp
  rw [CPoly.splitFactor_dense_eq]
  exact cSplitFactorFastG_isSplittingFactorizationGen Dt p hp

/-! ### M3 — discharging the gcd frontier at the `ℚ` base -/

/-- **The gcd frontier is unconditional at `ℚ`.** There `cgcdFFCoreWf` selects
`DensePoly.cgcdMonicWf`, whose correctness is `associated_toPolyG_cgcdMonicWf`. -/
theorem cgcdFFCoreWf_correct_Q : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := ℚ)) :=
  fun a b => associated_toPolyG_cgcdMonicWf a b

/-- **The gcd frontier as a resolvable `Fact` at the `ℚ` base.** Lets `[Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := ℚ)))]`
resolve automatically (the tower case above `ℚ` is the PRS-regularity frontier — no such instance there). -/
instance instFactCgcdFFCoreWfCorrectQ :
    Fact (CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := ℚ))) :=
  ⟨cgcdFFCoreWf_correct_Q⟩

/-- `CharZero (CFieldSpec.K ℚ) = CharZero ℚ`: local instance for the `ℚ`-base split correctness. -/
instance : CharZero (CFieldSpec.K ℚ) := inferInstanceAs (CharZero ℚ)

/-- **Unconditional abstract correctness of `cSplitFactorFast` at the `ℚ` base.** For `p ≠ 0`,
`cSplitFactorFast Dt p` is a genuine general splitting factorization of `p` — no gcd hypothesis. -/
theorem cSplitFactorFastG_isSplittingFactorizationGen_Q (Dt p : DensePoly ℚ) (hp : toPoly p ≠ 0) :
    @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (toPoly Dt)⟩ (toPoly p)
      (toPoly (cSplitFactorFast Dt p).2) (toPoly (cSplitFactorFast Dt p).1) :=
  cSplitFactorFastG_isSplittingFactorizationGen Dt p hp

end DeepWiki.SymbolicIntegration
