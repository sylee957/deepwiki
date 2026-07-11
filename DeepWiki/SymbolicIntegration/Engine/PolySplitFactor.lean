import DeepWiki.ComputableAlgebra.PolyGcdAlgorithms
import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv
import DeepWiki.SymbolicIntegration.CanonicalRepresentation.SplitFactor

/-! # Representation-independent differential split factorization

The normal/special polynomial split composes the selected gcd and Euclidean algorithms with the
representation-independent monomial derivative.
-/

namespace DeepWiki.SymbolicIntegration

universe u v

open Polynomial Classical
open scoped Differential

/-- Executable differential split factorization selected for a polynomial representation and coefficient field. -/
class CPolySplitFactor (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] [CDiffField α] where
  /-- Split a polynomial into its differential normal and special factors. -/
  compute : P α → P α → P α × P α

namespace CPolySplitFactor

/-- Internal bounded driver for differential normal/special factorization. -/
private def splitFactorAux {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CPolyGcd P α] [CPolyEuclidean P] [CDiffField α]
    (Dt : P α) : ℕ → P α → P α × P α
  | 0, p => (p, CPoly.one)
  | fuel + 1, p =>
    let implicitGcd := CPolyGcd.compute p (CPolyEngine.monomialDeriv Dt p)
    let formalGcd := CPolyGcd.compute p (CPolyEngine.deriv p)
    let special := CPolyEuclidean.div implicitGcd formalGcd
    if CPolyEngine.cdeg special = 0 then (p, CPoly.one)
    else
      let quotient := CPolyEuclidean.div p special
      if CPolyEngine.cdeg quotient < CPolyEngine.cdeg p then
        let parts := splitFactorAux Dt fuel quotient
        (parts.1, CPolyEngine.mul special parts.2)
      else (p, CPoly.one)

/-- File-local generic bounded differential split factorization through selected gcd and Euclidean operations. -/
private def default {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CPolyGcd P α] [CPolyEuclidean P] [CDiffField α]
    (Dt p : P α) : P α × P α :=
  splitFactorAux Dt (CPoly.degBound p) p

/-- The selected lawful gcd is associated to the abstract polynomial gcd. -/
private theorem selectedGcd_associated {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    [CPolyGcd P α] [LawfulCPolyGcd.{u,v} P α] (p q : P α) :
    Associated (CPoly.toPoly (CPolyGcd.compute p q)) (gcd (CPoly.toPoly p) (CPoly.toPoly q)) := by
  obtain ⟨hleft, hright, hgreatest⟩ := LawfulCPolyGcd.compute_isGCD' p q
  apply associated_of_dvd_dvd (dvd_gcd hleft hright)
  exact hgreatest _ (gcd_dvd_left _ _) (gcd_dvd_right _ _)

/-- One selected generic split step denotes the abstract differential split step up to associates. -/
private theorem toPoly_splitStep_associated {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    [LawfulCPolyEngine.{u,v} P] [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]
    [CharZero (CFieldSpec.K α)] [CPolyGcd P α] [LawfulCPolyGcd.{u,v} P α]
    (Dt p : P α) (hp : CPoly.toPoly p ≠ 0) :
    Associated
      (CPoly.toPoly (CPolyEuclidean.div
        (CPolyGcd.compute p (CPolyEngine.monomialDeriv Dt p))
      (CPolyGcd.compute p (CPolyEngine.deriv p))))
      (splitFactorStep (CPoly.toPoly Dt) (CPoly.toPoly p)) := by
  set A := CPolyGcd.compute p (CPolyEngine.monomialDeriv Dt p) with hAdef
  set B := CPolyGcd.compute p (CPolyEngine.deriv p) with hBdef
  have hA : Associated (CPoly.toPoly A)
      (gcd (CPoly.toPoly p)
        (Differential.implicitDeriv (CPoly.toPoly Dt) (CPoly.toPoly p))) := by
    simpa only [hAdef, CPolyEngine.toPoly_monomialDeriv] using
      selectedGcd_associated p (CPolyEngine.monomialDeriv Dt p)
  have hB : Associated (CPoly.toPoly B) (gcd (CPoly.toPoly p) (CPoly.toPoly p).derivative) := by
    simpa only [hBdef, LawfulCPolyEngine.toPoly_deriv] using
      selectedGcd_associated p (CPolyEngine.deriv p)
  have hgcdBne : gcd (CPoly.toPoly p) (CPoly.toPoly p).derivative ≠ 0 := by
    rw [Ne, gcd_eq_zero_iff]
    exact fun h => hp h.1
  have hB0 : CPoly.toPoly B ≠ 0 := fun h => hgcdBne (hB.eq_zero_iff.mp h)
  have hBA : CPoly.toPoly B ∣ CPoly.toPoly A :=
    hB.dvd.trans ((gcd_derivative_dvd_gcd_implicitDeriv (CPoly.toPoly Dt) hp).trans hA.symm.dvd)
  have hexact : CPoly.toPoly A = CPoly.toPoly B * CPoly.toPoly (CPolyEuclidean.div A B) :=
    LawfulCPolyEuclidean.div_exact A B hB0 hBA
  have hstepB : Associated (splitFactorStep (CPoly.toPoly Dt) (CPoly.toPoly p) * CPoly.toPoly B)
      (CPoly.toPoly A) := by
    refine (Associated.mul_left _ hB).trans ?_
    rw [splitFactorStep, mul_comm,
      EuclideanDomain.mul_div_cancel' hgcdBne
        (gcd_derivative_dvd_gcd_implicitDeriv (CPoly.toPoly Dt) hp)]
    exact hA.symm
  show Associated (CPoly.toPoly (CPolyEuclidean.div A B))
    (splitFactorStep (CPoly.toPoly Dt) (CPoly.toPoly p))
  have key : Associated (CPoly.toPoly (CPolyEuclidean.div A B) * CPoly.toPoly B)
      (splitFactorStep (CPoly.toPoly Dt) (CPoly.toPoly p) * CPoly.toPoly B) := by
    rw [mul_comm, ← hexact]
    exact hstepB.symm
  exact key.of_mul_right (Associated.refl _) hB0

/-- The generic bounded split loop denotes a splitting factorization whenever its fuel bounds degree. -/
private theorem splitFactorAux_isSplittingFactorizationGen
    {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]
    [CharZero (CFieldSpec.K α)] [CPolyGcd P α] [LawfulCPolyGcd.{u,v} P α]
    (Dt : P α) : ∀ (fuel : ℕ) (p : P α), CPoly.toPoly p ≠ 0 →
      (CPoly.toPoly p).natDegree ≤ fuel →
      @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩
        (CPoly.toPoly p) (CPoly.toPoly (splitFactorAux Dt fuel p).2)
          (CPoly.toPoly (splitFactorAux Dt fuel p).1) := by
  letI : Differential (CRingSpec.R α)[X] :=
    ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩
  intro fuel
  induction fuel with
  | zero =>
    intro p hp hdeg
    rw [Nat.le_zero, Polynomial.natDegree_eq_zero] at hdeg
    obtain ⟨c, hconst⟩ := hdeg
    have hc : c ≠ 0 := fun h => hp (by rw [← hconst, h, map_zero])
    have hnormC : IsNormalSqfree (Polynomial.C c) :=
      (isNormal_of_isUnit (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc))).isNormalSqfree
    have hnorm : IsNormalSqfree (CPoly.toPoly p) := by rw [← hconst]; exact hnormC
    simp only [splitFactorAux, CPoly.toPoly_one]
    exact ⟨(one_mul (CPoly.toPoly p)).symm, isSpecial_one, hnorm⟩
  | succ fuel ih =>
    intro p hp hdeg
    rw [splitFactorAux]
    simp only
    set special := CPolyEuclidean.div
      (CPolyGcd.compute p (CPolyEngine.monomialDeriv Dt p))
      (CPolyGcd.compute p (CPolyEngine.deriv p)) with hspecial
    have hassoc : Associated (CPoly.toPoly special)
        (splitFactorStep (CPoly.toPoly Dt) (CPoly.toPoly p)) := by
      simpa only [hspecial] using toPoly_splitStep_associated Dt p hp
    by_cases hdegSpecial : CPolyEngine.cdeg special = 0
    · rw [if_pos hdegSpecial]
      have hstepdeg : (splitFactorStep (CPoly.toPoly Dt) (CPoly.toPoly p)).natDegree = 0 := by
        rw [← Polynomial.natDegree_eq_of_degree_eq
          (Polynomial.degree_eq_degree_of_associated hassoc),
          ← LawfulCPolyEngine.cdeg_eq_natDegree, hdegSpecial]
      have hnorm := isNormalSqfree_of_splitFactorStep_natDegree_zero (CPoly.toPoly Dt) hp hstepdeg
      rw [CPoly.toPoly_one]
      exact ⟨(one_mul _).symm, isSpecial_one, hnorm⟩
    · rw [if_neg hdegSpecial]
      have hspecialPos : 0 < (CPoly.toPoly special).natDegree := by
        rw [← LawfulCPolyEngine.cdeg_eq_natDegree]
        exact Nat.pos_of_ne_zero hdegSpecial
      have hspecialNe : CPoly.toPoly special ≠ 0 := by
        intro hzero
        simp [hzero] at hspecialPos
      have hspecialDvd : CPoly.toPoly special ∣ CPoly.toPoly p :=
        hassoc.dvd.trans (splitFactorStep_dvd (CPoly.toPoly Dt) hp)
      have hexact : CPoly.toPoly p = CPoly.toPoly special *
          CPoly.toPoly (CPolyEuclidean.div p special) :=
        LawfulCPolyEuclidean.div_exact p special hspecialNe hspecialDvd
      have hquotNe : CPoly.toPoly (CPolyEuclidean.div p special) ≠ 0 := by
        intro hzero
        rw [hzero, mul_zero] at hexact
        exact hp hexact
      have hdegSum : (CPoly.toPoly special).natDegree +
          (CPoly.toPoly (CPolyEuclidean.div p special)).natDegree =
            (CPoly.toPoly p).natDegree := by
        rw [← Polynomial.natDegree_mul hspecialNe hquotNe, hexact]
      have hquotDeg : (CPoly.toPoly (CPolyEuclidean.div p special)).natDegree ≤ fuel := by
        omega
      have hdegDrop : CPolyEngine.cdeg (CPolyEuclidean.div p special) < CPolyEngine.cdeg p := by
        rw [LawfulCPolyEngine.cdeg_eq_natDegree, LawfulCPolyEngine.cdeg_eq_natDegree]
        omega
      rw [if_pos hdegDrop]
      obtain ⟨heq, hquotSpecial, hquotNormal⟩ :=
        ih (CPolyEuclidean.div p special) hquotNe hquotDeg
      refine ⟨?_, ?_, hquotNormal⟩
      · calc
          CPoly.toPoly p = CPoly.toPoly special * CPoly.toPoly (CPolyEuclidean.div p special) := hexact
          _ = CPoly.toPoly special *
              (CPoly.toPoly (splitFactorAux Dt fuel (CPolyEuclidean.div p special)).2 *
                CPoly.toPoly (splitFactorAux Dt fuel (CPolyEuclidean.div p special)).1) := by rw [heq]
          _ = CPoly.toPoly special *
                CPoly.toPoly (splitFactorAux Dt fuel (CPolyEuclidean.div p special)).2 *
              CPoly.toPoly (splitFactorAux Dt fuel (CPolyEuclidean.div p special)).1 :=
            (mul_assoc _ _ _).symm
          _ = CPoly.toPoly (CPolyEngine.mul special
                (splitFactorAux Dt fuel (CPolyEuclidean.div p special)).2) *
              CPoly.toPoly (splitFactorAux Dt fuel (CPolyEuclidean.div p special)).1 := by
            rw [LawfulCPolyEngine.toPoly_mul]
      · have hspecialSpecial : IsSpecial (CPoly.toPoly special) :=
          IsSpecial.of_associated hassoc.symm
            (isSpecial_splitFactorStep (CPoly.toPoly Dt) hp)
        rw [LawfulCPolyEngine.toPoly_mul]
        exact hspecialSpecial.mul hquotSpecial

/-- The representation-generic bounded split implementation satisfies its semantic contract. -/
private theorem default_isSplittingFactorizationGen
    {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α] [CDiffFieldSpec.{u,v} α]
    [CharZero (CFieldSpec.K α)] [CPolyGcd P α] [LawfulCPolyGcd.{u,v} P α]
    (Dt p : P α) (hp : CPoly.toPoly p ≠ 0) :
    @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩
      (CPoly.toPoly p) (CPoly.toPoly (default Dt p).2) (CPoly.toPoly (default Dt p).1) := by
  rw [default]
  apply splitFactorAux_isSplittingFactorizationGen Dt (CPoly.degBound p) p hp
  rw [← CPoly.cdeg_eq_natDegree]
  exact Nat.le_of_lt (CPoly.cdeg_lt_degBound_of_toPoly_ne_zero p hp)

end CPolySplitFactor

/-- Sparse polynomials select the representation-generic bounded split-factor kernel. -/
instance instCPolySplitFactorSparse {α : Type u} [CField α] [CDiffField α] :
    CPolySplitFactor CPoly.SparsePoly α where
  compute := CPolySplitFactor.default

namespace CPoly

/-- Split a represented differential polynomial using its selected implementation. -/
def splitFactor {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CDiffField α] [CPolySplitFactor P α]
    (Dt p : P α) : P α × P α :=
  CPolySplitFactor.compute Dt p

/-- Sparse splitting with the zero derivation extracts `(x - 1)²` as entirely special. -/
example :
    let p : CPoly.SparsePoly ℚ := CPoly.SparsePoly.ofList [(0, 1), (1, -2), (2, 1)]
    let parts := splitFactor (CPoly.czero : CPoly.SparsePoly ℚ) p
    CPolyEngine.cdeg parts.1 = 0
      ∧ CPolyEngine.cisZero
          (CPolyEngine.sub (CPolyEngine.mul parts.1 parts.2) p) = true := by
  ccompute

end CPoly

/-- Denotation law for a selected differential split factorization. -/
class LawfulCPolySplitFactor (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    (α : Type u) [CField α] [CDiffField α] [CFieldSpec.{u,v} α] [CDiffFieldSpec α]
    [CharZero (CFieldSpec.K α)] [CPolySplitFactor P α] : Prop where
  /-- The selected split is a normal/special splitting factorization of every nonzero input. -/
  compute_isSplittingFactorizationGen : ∀ (Dt p : P α), CPoly.toPoly p ≠ 0 →
    @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩
      (CPoly.toPoly p) (CPoly.toPoly (CPoly.splitFactor Dt p).2)
        (CPoly.toPoly (CPoly.splitFactor Dt p).1)

namespace LawfulCPolySplitFactor

/-- The selected split-factorization operation satisfies its denotation law. -/
theorem compute_isSplittingFactorizationGen' {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CDiffField α] [CFieldSpec.{u,v} α] [CDiffFieldSpec α]
    [CharZero (CFieldSpec.K α)] [CPolySplitFactor P α] [LawfulCPolySplitFactor P α]
    (Dt p : P α) (hp : CPoly.toPoly p ≠ 0) :
    @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩
      (CPoly.toPoly p) (CPoly.toPoly (CPoly.splitFactor Dt p).2)
        (CPoly.toPoly (CPoly.splitFactor Dt p).1) :=
  LawfulCPolySplitFactor.compute_isSplittingFactorizationGen Dt p hp

end LawfulCPolySplitFactor

/-- Sparse splitting's generic gcd/division loop satisfies the selected split-factor law. -/
instance instLawfulCPolySplitFactorSparse {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    [CDiffField α] [CDiffFieldSpec.{u,v} α] [CharZero (CFieldSpec.K α)] :
    LawfulCPolySplitFactor CPoly.SparsePoly α where
  compute_isSplittingFactorizationGen := by
    intro Dt p hp
    change @IsSplittingFactorizationGen _ _
      ⟨Differential.implicitDeriv (CPoly.toPoly Dt)⟩
        (CPoly.toPoly p) (CPoly.toPoly (CPolySplitFactor.default Dt p).2)
          (CPoly.toPoly (CPolySplitFactor.default Dt p).1)
    exact CPolySplitFactor.default_isSplittingFactorizationGen Dt p hp

end DeepWiki.SymbolicIntegration
