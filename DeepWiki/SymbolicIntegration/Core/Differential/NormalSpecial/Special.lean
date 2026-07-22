import DeepWiki.SymbolicIntegration.DifferentialAlgebra
import Mathlib.RingTheory.Coprime.Lemmas

/-! # Special elements in differential rings

Defines elements whose derivative is divisible by the element and proves the
basic product and factor API.
-/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

/-- `p` is *special* (w.r.t. `D`) if `p ∣ p'` (so `gcd(p, p') = p`). -/
def IsSpecial {R : Type*} [CommRing R] [Differential R] (p : R) : Prop := p ∣ p′

/-- Special polynomials are closed under multiplication. -/
theorem IsSpecial.mul {R : Type*} [CommRing R] [Differential R] {p q : R}
    (hp : IsSpecial p) (hq : IsSpecial q) : IsSpecial (p * q) := by
  obtain ⟨s, hs⟩ := hp
  obtain ⟨u, hu⟩ := hq
  refine ⟨u + s, ?_⟩
  rw [deriv_mul_eq, hs, hu]
  ring

/-- `1` is special. -/
theorem isSpecial_one {R : Type*} [CommRing R] [Differential R] : IsSpecial (1 : R) := by
  simp [IsSpecial]

/-- A finite product of special polynomials is special. -/
theorem IsSpecial.prod {R : Type*} [CommRing R] [Differential R] {ι : Type*} (s : Finset ι)
    (f : ι → R) (hf : ∀ i ∈ s, IsSpecial (f i)) : IsSpecial (∏ i ∈ s, f i) :=
  Finset.prod_induction f IsSpecial (fun _ _ ha hb => ha.mul hb) isSpecial_one hf

/-- If `p * q` is special and `p, q` are coprime, then `p` is special. -/
theorem IsSpecial.of_mul_coprime {R : Type*} [CommRing R] [Differential R] {p q : R}
    (h : IsSpecial (p * q)) (hco : IsCoprime p q) : IsSpecial p := by
  have h0 : (p * q) ∣ ((p * q)′) := h
  rw [deriv_mul_eq] at h0
  have hp1 : p ∣ (p * q′ + q * p′) := (dvd_mul_right p q).trans h0
  have hp2 : p ∣ q * p′ := (dvd_add_right (dvd_mul_right p q′)).mp hp1
  exact hco.dvd_of_dvd_mul_left hp2

end DeepWiki.SymbolicIntegration
