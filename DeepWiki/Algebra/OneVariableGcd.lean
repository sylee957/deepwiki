import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.RingTheory.Bezout
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # One-variable polynomial gcd API

GCD and Bézout infrastructure on `MvPolynomial (Fin 1) K`, transported through
the equivalence with `Polynomial K` and kept as local instances. -/

set_option linter.defProp false

open MvPolynomial

namespace DeepWiki.SymbolicIntegration

/-! ## GCD / Bézout structure on the leading-`y`-coefficient ring `MvPolynomial (Fin 1) K`

A chosen `GCDMonoid` and Bézout identity on `MvPolynomial (Fin 1) K ≃ K[x]` (a PID), transferred
from `K[x]`. Provided as local `letI` instances, not global (to avoid diamonds). -/

open scoped Classical in
/-- The ring equivalence `MvPolynomial (Fin 1) K ≃+* K[x]`: pull out the single variable
(`finSuccEquiv K 0`), then erase the now-empty inner `MvPolynomial (Fin 0) K ≃ K`. -/
noncomputable def mvPolynomialFinOneEquivPolynomial (K : Type*) [Field K] :
    MvPolynomial (Fin 1) K ≃+* Polynomial K :=
  ((finSuccEquiv K 0).trans (Polynomial.mapAlgEquiv (isEmptyAlgEquiv K (Fin 0)))).toRingEquiv

open scoped Classical in
/-- A chosen `GCDMonoid` on `MvPolynomial (Fin 1) K` (UFD `⟹` GCD domain). Used as a local
`letI`; not a global instance. -/
@[reducible] noncomputable def gcdMonoidMvPolynomialFinOne (K : Type*) [Field K] :
    GCDMonoid (MvPolynomial (Fin 1) K) :=
  UniqueFactorizationMonoid.toGCDMonoid _

/-- `MvPolynomial (Fin 1) K` is a Bézout ring (transfer `K[x]`'s `IsBezout` through the surjective
`mvPolynomialFinOneEquivPolynomial.symm`). Used as a local `letI`; not a global instance. -/
@[reducible] noncomputable def isBezoutMvPolynomialFinOne (K : Type*) [Field K] :
    IsBezout (MvPolynomial (Fin 1) K) :=
  Function.Surjective.isBezout (mvPolynomialFinOneEquivPolynomial K).symm.toRingHom
    (mvPolynomialFinOneEquivPolynomial K).symm.surjective

open scoped Classical in
/-- Bézout's identity: there are `a, b` with `a·g + b·g' = gcd g g'` in `MvPolynomial (Fin 1) K`. -/
theorem exists_mul_add_mul_eq_gcd {K : Type*} [Field K] (g g' : MvPolynomial (Fin 1) K) :
    ∃ a b : MvPolynomial (Fin 1) K,
      a * g + b * g' = @gcd _ _ (gcdMonoidMvPolynomialFinOne K) g g' := by
  letI := gcdMonoidMvPolynomialFinOne K
  letI := isBezoutMvPolynomialFinOne K
  have hdvd : @gcd _ _ (gcdMonoidMvPolynomialFinOne K) g g' ∣ gcd g g' := dvd_refl _
  rw [gcd_dvd_iff_exists] at hdvd
  obtain ⟨a, b, hab⟩ := hdvd
  exact ⟨a, b, by rw [hab]; ring⟩

/-- `gcd g g' ∣ g` (left) for the chosen `GCDMonoid` on `MvPolynomial (Fin 1) K`. -/
theorem gcd_dvd_left_mvPolynomialFinOne {K : Type*} [Field K] (g g' : MvPolynomial (Fin 1) K) :
    @gcd _ _ (gcdMonoidMvPolynomialFinOne K) g g' ∣ g :=
  letI := gcdMonoidMvPolynomialFinOne K
  gcd_dvd_left g g'

/-- `gcd g g' ∣ g'` (right) for the chosen `GCDMonoid` on `MvPolynomial (Fin 1) K`. -/
theorem gcd_dvd_right_mvPolynomialFinOne {K : Type*} [Field K] (g g' : MvPolynomial (Fin 1) K) :
    @gcd _ _ (gcdMonoidMvPolynomialFinOne K) g g' ∣ g' :=
  letI := gcdMonoidMvPolynomialFinOne K
  gcd_dvd_right g g'

/-- `natDegree (e r) = degreeOf 0 r` for `e = mvPolynomialFinOneEquivPolynomial K`. -/
theorem natDegree_mvPolynomialFinOneEquivPolynomial {K : Type*} [Field K]
    (r : MvPolynomial (Fin 1) K) :
    (mvPolynomialFinOneEquivPolynomial K r).natDegree = degreeOf 0 r := by
  rw [mvPolynomialFinOneEquivPolynomial]
  show (Polynomial.mapAlgEquiv (isEmptyAlgEquiv K (Fin 0)) (finSuccEquiv K 0 r)).natDegree = _
  rw [Polynomial.coe_mapAlgEquiv, ← natDegree_finSuccEquiv r]
  apply Polynomial.natDegree_map_eq_of_injective
  exact EquivLike.injective (isEmptyAlgEquiv K (Fin 0))

/-- On `MvPolynomial (Fin 1) K`, `p ∣ q` and `q ≠ 0` imply `degreeOf 0 p ≤ degreeOf 0 q`. -/
theorem degreeOf_le_of_dvd {K : Type*} [Field K] {p q : MvPolynomial (Fin 1) K}
    (hpq : p ∣ q) (hq : q ≠ 0) : degreeOf 0 p ≤ degreeOf 0 q := by
  set e := mvPolynomialFinOneEquivPolynomial K with he
  rw [← natDegree_mvPolynomialFinOneEquivPolynomial, ← natDegree_mvPolynomialFinOneEquivPolynomial]
  refine Polynomial.natDegree_le_of_dvd (map_dvd e hpq) ?_
  rwa [Ne, map_eq_zero_iff _ e.injective]

/-- On `MvPolynomial (Fin 1) K`, if `p ∣ q`, `q ≠ 0` and `degreeOf 0 q ≤ degreeOf 0 p`, then
`q ∣ p`. -/
theorem dvd_of_dvd_of_degreeOf_le {K : Type*} [Field K] {p q : MvPolynomial (Fin 1) K}
    (hpq : p ∣ q) (hq : q ≠ 0) (hdeg : degreeOf 0 q ≤ degreeOf 0 p) : q ∣ p := by
  set e := mvPolynomialFinOneEquivPolynomial K with he
  have heq : e p ∣ e q := map_dvd e hpq
  have hq' : e q ≠ 0 := by rwa [Ne, map_eq_zero_iff _ e.injective]
  rw [← natDegree_mvPolynomialFinOneEquivPolynomial, ← natDegree_mvPolynomialFinOneEquivPolynomial]
    at hdeg
  have hassoc : Associated (e p) (e q) :=
    Polynomial.associated_of_dvd_of_natDegree_le heq hq' hdeg
  have h2 : e q ∣ e p := hassoc.symm.dvd
  have h3 : e.symm (e q) ∣ e.symm (e p) := map_dvd e.symm h2
  rwa [e.symm_apply_apply, e.symm_apply_apply] at h3

-- Restatements against the intended wording.
noncomputable example {K : Type*} [Field K] : MvPolynomial (Fin 1) K ≃+* Polynomial K :=
  mvPolynomialFinOneEquivPolynomial K

example {K : Type*} [Field K] (g g' : MvPolynomial (Fin 1) K) :
    ∃ a b : MvPolynomial (Fin 1) K,
      a * g + b * g' = @gcd _ _ (gcdMonoidMvPolynomialFinOne K) g g' :=
  exists_mul_add_mul_eq_gcd g g'

end DeepWiki.SymbolicIntegration
