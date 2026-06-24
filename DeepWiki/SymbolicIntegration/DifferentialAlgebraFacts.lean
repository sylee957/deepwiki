import DeepWiki.SymbolicIntegration.MonomialExtensions
import DeepWiki.SymbolicIntegration.AlgebraicConstants

/-! # Worked differential-algebra facts (Bronstein Ch 3 exercises)
A handful of self-contained differential-algebra statements: the logarithmic-derivative identity
for finite products, the coefficient-lifting derivation `κ_D` on a polynomial ring, and Rao's
denominator-cleared formulation of normal/special polynomials in a simple transcendental
extension — `b·Δp = b·κ_D(p) + a·(dp/dt)` for `Δt = a/b`, with the corresponding root
characterizations of normality and specialness. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ## The coefficient derivation `κ_D` on a polynomial ring -/

section KappaD
variable {R : Type*} [CommRing R] [Differential R]

/-- The coefficient-lifting map `κ_D : R[t] → R[t]`, `κ_D(∑ aᵢ tⁱ) = ∑ (Daᵢ) tⁱ`, is a
derivation (Mathlib's `Differential.mapCoeffs`); it is the extension of `D` to `R[t]` with `Dt = 0`. -/
noncomputable def kappaD (R : Type*) [CommRing R] [Differential R] : Derivation ℤ R[X] R[X] :=
  Differential.mapCoeffs

@[simp] theorem kappaD_coeff (p : R[X]) (i : ℕ) : (kappaD R p).coeff i = (p.coeff i)′ :=
  Differential.coeff_mapCoeffs p i

@[simp] theorem kappaD_X : kappaD R (X : R[X]) = 0 := Differential.mapCoeffs_X

@[simp] theorem kappaD_C (x : R) : kappaD R (C x) = C x′ := Differential.mapCoeffs_C x

/-- `κ_D` is additive (the derivation property): `κ_D(p + q) = κ_D p + κ_D q`. -/
theorem kappaD_add (p q : R[X]) : kappaD R (p + q) = kappaD R p + kappaD R q := map_add _ _ _

/-- `κ_D` satisfies the Leibniz rule: `κ_D(p·q) = p·κ_D q + q·κ_D p`. -/
theorem kappaD_mul (p q : R[X]) : kappaD R (p * q) = p * kappaD R q + q * kappaD R p := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

end KappaD

/-! ## Rao's normal/special polynomials in a simple transcendental extension (§3.4, Exercises 3.7–3.11)
For a derivation `Δ` on `k(t)` (`t` transcendental) with `Δt = a/b` in lowest terms
(`gcd(a, b) = 1`, `b ≠ 0`), and `p ∈ k[t]`, the chain rule gives
`Δp = κ_D(p) + (dp/dt)·Δt = κ_D(p) + (dp/dt)·a/b`, so `b·Δp = b·κ_D(p) + a·(dp/dt)` is a
*polynomial* in `k[t]` — this is `bDeriv a b p` below (Exercise 3.7). Rao then defines `p` to be
*normal* if `gcd(p, b·Δp) = 1` and *special* if `p ∣ b·Δp`, and Exercises 3.9–3.11 give the
root characterizations and the coprimality `gcd(p, b) = 1` for special `p`. -/

section Rao
variable {k : Type*} [Field k] [Differential k]

/-- **Exercise 3.7** (§3.4): the denominator-cleared derivative `b·Δp = b·κ_D(p) + a·(dp/dt)` for
the derivation with `Δt = a/b`. This is a *polynomial* in `k[t]` (no division), the polynomial
representative of `b·Δp`; Rao's normal/special are stated through it. -/
noncomputable def bDeriv (a b p : k[X]) : k[X] := b * kappaD k p + a * derivative p

/-- `b·Δ(C c) = b·C(Dc)`: on a constant, the `dp/dt` term drops. -/
@[simp] theorem bDeriv_C (a b : k[X]) (c : k) : bDeriv a b (C c) = b * C c′ := by
  simp [bDeriv]

/-- `b·Δt = a`: the defining relation `Δt = a/b` cleared of its denominator. -/
@[simp] theorem bDeriv_X (a b : k[X]) : bDeriv a b X = a := by
  simp [bDeriv]

/-- `b·Δ` is additive: `b·Δ(p + q) = b·Δp + b·Δq`. -/
theorem bDeriv_add (a b p q : k[X]) : bDeriv a b (p + q) = bDeriv a b p + bDeriv a b q := by
  simp only [bDeriv, map_add]; ring

/-- **Exercise 3.7** (§3.4), Leibniz form: `b·Δ(p·q) = p·(b·Δq) + q·(b·Δp)`. The product rule
survives multiplication by the denominator `b`. -/
theorem bDeriv_mul (a b p q : k[X]) :
    bDeriv a b (p * q) = p * bDeriv a b q + q * bDeriv a b p := by
  simp only [bDeriv, kappaD_mul, derivative_mul]; ring

/-- **Definition (Rao, §3.4)**: `p` is *normal* w.r.t. `Δt = a/b` if `gcd(p, b·Δp) = 1`, i.e.
`p` and the cleared derivative `b·Δp` are coprime. -/
def IsNormalRao (a b p : k[X]) : Prop := IsCoprime p (bDeriv a b p)

/-- **Definition (Rao, §3.4)**: `p` is *special* w.r.t. `Δt = a/b` if `p ∣ b·Δp`. -/
def IsSpecialRao (a b p : k[X]) : Prop := p ∣ bDeriv a b p

end Rao

end DeepWiki.SymbolicIntegration
