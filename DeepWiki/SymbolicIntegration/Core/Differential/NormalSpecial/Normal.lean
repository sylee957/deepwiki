import DeepWiki.SymbolicIntegration.DifferentialAlgebra
import Mathlib.RingTheory.Coprime.Lemmas

/-! # Normal elements in differential rings

Defines elements coprime to their derivative and proves the basic product,
factor, and squarefree API.
-/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

/-- `p` is *normal*: coprime to its derivative `p'` (`gcd(p, p') = 1`). -/
def IsNormal {R : Type*} [CommRing R] [Differential R] (p : R) : Prop := IsCoprime p p′

/-- `1` is normal. -/
theorem isNormal_one {R : Type*} [CommRing R] [Differential R] : IsNormal (1 : R) := by
  have h : ((1 : R)′) = 0 := (Differential.deriv : Derivation ℤ R R).map_one_eq_zero
  rw [IsNormal, h]
  exact isCoprime_one_left

/-- The product of two coprime normal polynomials is normal. -/
theorem IsNormal.mul {R : Type*} [CommRing R] [Differential R] {p q : R}
    (hp : IsNormal p) (hq : IsNormal q) (hpq : IsCoprime p q) : IsNormal (p * q) := by
  show IsCoprime (p * q) ((p * q)′)
  rw [deriv_mul_eq]
  refine IsCoprime.mul_left ?_ ?_
  · rw [add_comm]; exact (hpq.mul_right hp).add_mul_left_right q′
  · exact (hpq.symm.mul_right hq).add_mul_left_right p′

/-- A finite product of pairwise-coprime normal polynomials is normal. -/
theorem IsNormal.prod {R : Type*} [CommRing R] [Differential R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ s, IsNormal (f i))
    (hco : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (f i) (f j)) :
    IsNormal (∏ i ∈ s, f i) := by
  induction s using Finset.induction with
  | empty => simpa using isNormal_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hfa : IsNormal (f a) := hf a (Finset.mem_insert_self a s)
    have hcoa : IsCoprime (f a) (∏ i ∈ s, f i) :=
      IsCoprime.prod_right fun i hi => hco a (Finset.mem_insert_self a s) i
        (Finset.mem_insert_of_mem hi) (by rintro rfl; exact ha hi)
    refine hfa.mul (ih ?_ ?_) hcoa
    · exact fun i hi => hf i (Finset.mem_insert_of_mem hi)
    · exact fun i hi j hj hij => hco i (Finset.mem_insert_of_mem hi) j
        (Finset.mem_insert_of_mem hj) hij

/-- If `p * q` is normal then `p` is normal. -/
theorem IsNormal.of_mul_left {R : Type*} [CommRing R] [Differential R] {p q : R}
    (h : IsNormal (p * q)) : IsNormal p := by
  have h0 : IsCoprime (p * q) ((p * q)′) := h
  have h1 : IsCoprime p ((p * q)′) := h0.of_mul_left_left
  rw [deriv_mul_eq] at h1
  have h2 : IsCoprime p (q * p′) := by
    have := h1.add_mul_left_right (-q′)
    rwa [show (p * q′ + q * p′) + p * -q′ = q * p′ from by ring] at this
  exact h2.of_mul_right_right

/-- If `p * q` is normal then `q` is normal. -/
theorem IsNormal.of_mul_right {R : Type*} [CommRing R] [Differential R] {p q : R}
    (h : IsNormal (p * q)) : IsNormal q :=
  IsNormal.of_mul_left (mul_comm p q ▸ h)

/-- Any factor of a normal polynomial is normal. -/
theorem IsNormal.of_dvd {R : Type*} [CommRing R] [Differential R] {p q : R}
    (h : IsNormal p) (hq : q ∣ p) : IsNormal q := by
  obtain ⟨r, rfl⟩ := hq
  exact h.of_mul_left

/-- A normal polynomial is squarefree (for any derivation). -/
theorem IsNormal.squarefree {R : Type*} [CommRing R] [Differential R] {p : R}
    (hp : IsNormal p) : Squarefree p := by
  intro x hx
  obtain ⟨r, hr⟩ := hx
  have hxp : x ∣ p := ⟨x * r, by rw [hr]; ring⟩
  have hxp' : x ∣ p′ := by
    rw [hr]
    have e : ((x * x) * r)′ = x * (x * r′ + r * x′ + r * x′) := by
      rw [deriv_mul_eq (x * x) r, deriv_mul_eq x x]; ring
    rw [e]; exact dvd_mul_right x _
  exact IsCoprime.isUnit_of_dvd' hp hxp hxp'

end DeepWiki.SymbolicIntegration
