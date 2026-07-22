import DeepWiki.Algebra.GcdBasics
import DeepWiki.SymbolicIntegration.DifferentialAlgebra
import Mathlib.RingTheory.Coprime.Lemmas

/-! # GCDs and derivations

Generic gcd identities for elements of a differential ring.
-/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

/-- gcd of a derivative, two-factor case: for coprime `a, b`,
`gcd(a·b, (a·b)′) ~ gcd(a, a′)·gcd(b, b′)`. -/
theorem associated_gcd_deriv_mul {R : Type*} [CommRing R] [Differential R] [NormalizedGCDMonoid R]
    {a b : R} (hab : IsUnit (gcd a b)) :
    Associated (gcd (a * b) ((a * b)′)) (gcd a a′ * gcd b b′) := by
  have hba : IsUnit (gcd b a) := by rwa [gcd_comm]
  rw [deriv_mul_eq]
  refine (associated_gcd_mul_of_isUnit_gcd hab _).trans (Associated.mul_mul ?_ ?_)
  · rw [add_comm (a * b′) (b * a′)]
    exact (associated_gcd_add_mul a (b * a′) b′).trans (associated_gcd_mul_left_cancel hab)
  · exact (associated_gcd_add_mul b (a * b′) a′).trans (associated_gcd_mul_left_cancel hba)

/-- gcd of a derivative, prime-power case: for `n ≥ 1` a unit,
`gcd(pⁿ, (pⁿ)′) ~ pⁿ⁻¹·gcd(p, p′)`. -/
theorem associated_gcd_deriv_pow {R : Type*} [CommRing R] [Differential R] [NormalizedGCDMonoid R]
    {p : R} {n : ℕ} (hn : 1 ≤ n) (he : IsUnit (n : R)) :
    Associated (gcd (p ^ n) ((p ^ n)′)) (p ^ (n - 1) * gcd p p′) := by
  have hd : (p ^ n)′ = (n : R) * (p ^ (n - 1) * p′) := by
    rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
  have hpe : p ^ n = p ^ (n - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [hd, hpe, show (n : R) * (p ^ (n - 1) * p′) = p ^ (n - 1) * ((n : R) * p′) from by ring]
  refine (gcd_mul_left' (p ^ (n - 1)) p ((n : R) * p′)).trans ?_
  exact Associated.mul_left _
    (associated_gcd_mul_left_cancel (isUnit_of_dvd_unit (gcd_dvd_right p (n : R)) he))

/-- gcd of a derivative, pairwise-coprime product: `gcd(∏ f i, (∏ f i)′) ~ ∏ gcd(f i, (f i)′)`. -/
theorem associated_gcd_deriv_prod {R : Type*} [CommRing R] [Differential R] [NormalizedGCDMonoid R]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → R) :
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsUnit (gcd (f i) (f j))) →
    Associated (gcd (∏ i ∈ s, f i) ((∏ i ∈ s, f i)′)) (∏ i ∈ s, gcd (f i) (f i)′) := by
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.prod_empty]
    exact associated_one_iff_isUnit.mpr (isUnit_of_dvd_one (gcd_dvd_left (1 : R) _))
  | insert a s ha ih =>
    intro hco
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hu : IsUnit (gcd (f a) (∏ i ∈ s, f i)) := by
      apply isUnit_gcd_prod
      intro i hi
      exact hco a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (by rintro rfl; exact ha hi)
    refine (associated_gcd_deriv_mul hu).trans (Associated.mul_left _ (ih ?_))
    intro i hi j hj hij
    exact hco i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij

/-- gcd-with-derivative is an associate invariant: `Associated p q → gcd(p, Dp) ~ gcd(q, Dq)`. -/
theorem associated_gcd_deriv_of_associated {R : Type*} [CommRing R] [NormalizedGCDMonoid R]
    [Differential R] {p q : R} (h : Associated p q) :
    Associated (gcd p p′) (gcd q q′) := by
  obtain ⟨u, rfl⟩ := h
  have hugcd : IsUnit (gcd p (u : R)) := isUnit_of_dvd_unit (gcd_dvd_right _ _) u.isUnit
  have hbase := associated_gcd_deriv_mul (a := p) (b := (u : R)) hugcd
  have huu : IsUnit (gcd (u : R) ((u : R)′)) :=
    isUnit_of_dvd_unit (gcd_dvd_left _ _) u.isUnit
  refine (hbase.trans ?_).symm
  exact (associated_mul_unit_right _ _ huu).symm

end DeepWiki.SymbolicIntegration
