import DeepWiki.SymbolicIntegration.DifferentialFields
import Mathlib.RingTheory.Derivation.MapCoeffs

/-! # Monomial extensions — normal and special polynomials (Bronstein §3.4)
A *monomial* `t` over a differential field `k` is a transcendental element with `Dt ∈ k[t]`, so
`k[t]` is closed under `D`. Mathlib's `Differential.implicitDeriv v = mapCoeffs + v • d/dX` is
exactly this derivation on `k[X]` with `Dt = v` (`implicitDeriv_X`/`implicitDeriv_C`). A
polynomial is *normal* if it is coprime to its derivative and *special* if it divides its
derivative; special polynomials cut out differential ideals. We work over a general differential
ring (these are derivation/divisibility facts), the monomial case being `R = k[t]`. -/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

variable {R : Type*} [CommRing R] [Differential R]

/-- **Definition 3.4.2** (§3.4): `p` is *normal* (w.r.t. `D`) if `gcd(p, Dp) = 1`, i.e. `p` and
its derivative `p′` are coprime. -/
def IsNormal (p : R) : Prop := IsCoprime p p′

/-- **Definition 3.4.2** (§3.4): `p` is *special* (w.r.t. `D`) if `p ∣ Dp` (so `gcd(p, Dp) = p`). -/
def IsSpecial (p : R) : Prop := p ∣ p′

/-- The derivative of `a` is `Const`-linear over a special divisor: `(p·b)′ = p·b′ + b·p′`. -/
theorem deriv_mul_eq (p b : R) : (p * b)′ = p * b′ + b * p′ := by
  simp only [Derivation.leibniz, smul_eq_mul]

/-- **Lemma 3.4.3** (§3.4, p.92): a special polynomial generates a *differential ideal* — if
`p ∣ Dp` then `(p)` is closed under `D`. -/
theorem IsSpecial.isDifferentialIdeal {p : R} (hp : IsSpecial p) :
    IsDifferentialIdeal (Ideal.span {p}) := by
  intro a ha
  rw [Ideal.mem_span_singleton] at ha ⊢
  obtain ⟨b, rfl⟩ := ha
  rw [deriv_mul_eq]
  exact dvd_add (dvd_mul_right p b′) (hp.mul_left b)

/-- **Theorem 3.4.1(ii)** (§3.4, p.93): the special polynomials are closed under multiplication
(`S` is a multiplicative monoid). -/
theorem IsSpecial.mul {p q : R} (hp : IsSpecial p) (hq : IsSpecial q) : IsSpecial (p * q) := by
  obtain ⟨s, hs⟩ := hp
  obtain ⟨u, hu⟩ := hq
  refine ⟨u + s, ?_⟩
  rw [deriv_mul_eq, hs, hu]
  ring

/-- `1` is special (the unit of the monoid `S`). -/
theorem isSpecial_one : IsSpecial (1 : R) := by
  simp [IsSpecial]

end DeepWiki.SymbolicIntegration
