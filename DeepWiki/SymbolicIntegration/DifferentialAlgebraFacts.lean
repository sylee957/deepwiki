import DeepWiki.SymbolicIntegration.MonomialExtensions
import DeepWiki.SymbolicIntegration.AlgebraicConstants

/-! # Worked differential-algebra facts
The logarithmic-derivative identity for finite products, the coefficient-lifting derivation `κ_D`,
and the denominator-cleared derivation `b·Δp = b·κ_D(p) + a·(dp/dt)` with root characterizations of
normal and special polynomials in a simple transcendental extension. -/

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

/-! ## The logarithmic-derivative identity for a finite product -/

section LogDerivIdentity
variable {F : Type*} [Field F] [Differential F]

/-- Logarithmic-derivative identity for a finite product with integer exponents:
`D(∏ᵢ uᵢ^{eᵢ}) / (∏ᵢ uᵢ^{eᵢ}) = ∑ᵢ eᵢ·(Duᵢ/uᵢ)` — `logDeriv_prod_zpow` in explicit `D(P)/P`
shape. -/
theorem logDeriv_prod_zpow_div {ι : Type*} (s : Finset ι) (u : ι → F) (e : ι → ℤ)
    (h : ∀ i ∈ s, u i ≠ 0) :
    (∏ i ∈ s, u i ^ e i)′ / (∏ i ∈ s, u i ^ e i)
      = ∑ i ∈ s, (e i : F) * ((u i)′ / u i) := by
  have hlhs : Differential.logDeriv (∏ i ∈ s, u i ^ e i)
      = (∏ i ∈ s, u i ^ e i)′ / (∏ i ∈ s, u i ^ e i) := rfl
  rw [← hlhs, logDeriv_prod_zpow s u e h]
  exact Finset.sum_congr rfl fun i _ => by rw [Differential.logDeriv]

end LogDerivIdentity

/-! ## A logarithm/arc-tangent combination is a constant -/

section LogArctan
variable {E : Type*} [Field E] [Differential E] [CharZero E]

/-- An element `i` with `i² = −1` is a constant: `Di = 0`. (Differentiate `i² = −1`: `2i·Di = 0`,
and `i ≠ 0` with `2 ≠ 0` in characteristic `0`.) -/
theorem deriv_eq_zero_of_sq_eq_neg_one {i : E} (hi : i ^ 2 = -1) : i′ = 0 := by
  have hine : i ≠ 0 := by rintro rfl; simp at hi
  have hd : (i ^ 2)′ = 0 := by rw [hi]; simp
  rw [deriv_pow] at hd
  -- `hd : (2 : E) * i ^ (2 - 1) * i′ = 0`, with `2 ≠ 0`, `i ≠ 0`.
  have h2 : (2 : E) ≠ 0 := by norm_num
  have : i ^ (2 - 1) = i := by norm_num
  rw [this] at hd
  exact (mul_eq_zero.mp hd).resolve_left (mul_ne_zero h2 hine)

/-- The combination of a logarithm of `v = (u + i)/(u − i)` and an
arc-tangent of `u` is a constant. With `i² = −1`, `u² + 1 ≠ 0`, `Δt₁ = Δv/v` (logarithm of `v`),
and `Δt₂ = Δu/(1 + u²)` (arc-tangent of `u`), the combination `t₁·i − 2·t₂` has zero derivative:
`i·Δv/v = 2·Δu/(1+u²)` (since `Δv/v = −2i·Δu/(u²+1)` and `i² = −1`), cancelling `2·Δt₂`. -/
theorem deriv_log_arctan_combination_eq_zero {i u v t₁ t₂ : E} (hi : i ^ 2 = -1)
    (hu : u ^ 2 + 1 ≠ 0) (hv : v = (u + i) / (u - i))
    (ht₁ : t₁′ = v′ / v) (ht₂ : t₂′ = u′ / (1 + u ^ 2)) :
    (t₁ * i - 2 * t₂)′ = 0 := by
  have hi0 : i′ = 0 := deriv_eq_zero_of_sq_eq_neg_one hi
  -- `u ± i ≠ 0`: else `u² = i² = −1`, i.e. `u² + 1 = 0`.
  have hupi : u + i ≠ 0 := by
    intro h; apply hu; have huv : u = -i := by linear_combination h
    rw [huv]; linear_combination hi
  have humi : u - i ≠ 0 := by
    intro h; apply hu; have huv : u = i := by linear_combination h
    rw [huv]; linear_combination hi
  have hvne : v ≠ 0 := by rw [hv]; exact div_ne_zero hupi humi
  -- `Δv/v = −2i·Δu/(u² + 1)`.
  -- `i`-power reduction from `i² = −1`.
  have hi3 : i ^ 3 = -i := by linear_combination i * hi
  have hdv : v′ / v = (-2 * i) * u′ / (u ^ 2 + 1) := by
    have hv2 : v′ = ((u - i) * u′ - (u + i) * u′) / (u - i) ^ 2 := by
      rw [hv, deriv_div, map_sub, map_add, hi0, add_zero, sub_zero]
    rw [hv2, hv]
    field_simp
    ring_nf
    simp only [hi3]
    ring
  -- assemble: `(t₁·i − 2·t₂)′ = i·Δt₁ − 2·Δt₂ = i·(Δv/v) − 2·Δu/(1+u²) = 0`.
  have h20 : (2 : E)′ = 0 := by
    have h2eq : (2 : E) = 1 + 1 := by norm_num
    rw [h2eq, map_add]; simp
  have hprod : (t₁ * i)′ = i * t₁′ := by rw [deriv_mul_eq, hi0, mul_zero, zero_add]
  have htwo : (2 * t₂ : E)′ = 2 * t₂′ := by rw [deriv_mul_eq, h20, mul_zero, add_zero]
  rw [map_sub, hprod, htwo, ht₁, ht₂, hdv]
  rw [show (1 : E) + u ^ 2 = u ^ 2 + 1 from by ring]
  field_simp
  linear_combination (-2 * u′) * hi

end LogArctan

/-! ## Rao's normal/special polynomials in a simple transcendental extension
For a derivation `Δ` on `k(t)` (`t` transcendental) with `Δt = a/b` in lowest terms
(`gcd(a, b) = 1`, `b ≠ 0`), and `p ∈ k[t]`, the chain rule gives
`Δp = κ_D(p) + (dp/dt)·Δt`, so `b·Δp = b·κ_D(p) + a·(dp/dt)` is a *polynomial* in `k[t]` —
this is `bDeriv a b p` below. Rao defines `p` to be *normal* if `gcd(p, b·Δp) = 1` and
*special* if `p ∣ b·Δp`; the root characterizations and the coprimality `gcd(p, b) = 1` for
special `p` follow. -/

section Rao
variable {k : Type*} [Field k] [Differential k]

/-- The denominator-cleared derivation `b·Δ = b·κ_D + a·(d/dt) : k[t] → k[t]` (for `Δt = a/b`),
bundled as a `Derivation ℤ k[t] k[t]`: a linear combination `b • κ_D + a • (d/dt)` of the
coefficient derivation and `t`-differentiation, mirroring `Differential.implicitDeriv`. -/
noncomputable def bDerivation (a b : k[X]) : Derivation ℤ k[X] k[X] :=
  b • kappaD k + a • (derivative' (R := k)).restrictScalars ℤ

/-- The denominator-cleared derivative `b·Δp = b·κ_D(p) + a·(dp/dt)` for
the derivation with `Δt = a/b`. This is a *polynomial* in `k[t]` (no division), the polynomial
representative of `b·Δp`; Rao's normal/special are stated through it. -/
noncomputable def bDeriv (a b p : k[X]) : k[X] := bDerivation a b p

/-- `b·Δ` unfolds to the chain-rule polynomial `b·κ_D(p) + a·(dp/dt)`. -/
theorem bDeriv_eq (a b p : k[X]) : bDeriv a b p = b * kappaD k p + a * derivative p := by
  simp only [bDeriv, bDerivation, Derivation.add_apply, Derivation.smul_apply,
    Derivation.coe_restrictScalars, derivative'_apply, smul_eq_mul]

/-- `b·Δ(C c) = b·C(Dc)`: on a constant, the `dp/dt` term drops. -/
theorem bDeriv_C (a b : k[X]) (c : k) : bDeriv a b (C c) = b * C c′ := by
  rw [bDeriv_eq, kappaD_C, derivative_C, mul_zero, add_zero]

/-- `b·Δt = a`: the defining relation `Δt = a/b` cleared of its denominator. -/
theorem bDeriv_X (a b : k[X]) : bDeriv a b X = a := by
  rw [bDeriv_eq, kappaD_X, mul_zero, zero_add, derivative_X, mul_one]

/-- `b·Δ` is additive: `b·Δ(p + q) = b·Δp + b·Δq`. -/
theorem bDeriv_add (a b p q : k[X]) : bDeriv a b (p + q) = bDeriv a b p + bDeriv a b q :=
  map_add (bDerivation a b) p q

/-- Leibniz form: `b·Δ(p·q) = p·(b·Δq) + q·(b·Δp)`. The product rule
survives multiplication by the denominator `b`. -/
theorem bDeriv_mul (a b p q : k[X]) :
    bDeriv a b (p * q) = p * bDeriv a b q + q * bDeriv a b p := by
  simp only [bDeriv_eq, kappaD_mul, derivative_mul]; ring

/-- The `b·Δ` derivation packaged as a `Differential k[t]` structure: under it, `p′ = b·Δp`. Used
locally (via `letI`) to reuse the generic monomial-extension `IsNormal`/`IsSpecial` API. -/
@[reducible] noncomputable def bDifferential (a b : k[X]) : Differential k[X] := ⟨bDerivation a b⟩

/-- Rao's normality: `p` is *normal* w.r.t. `Δt = a/b` if `gcd(p, b·Δp) = 1`, i.e.
`p` and the cleared derivative `b·Δp` are coprime. (Definitionally `IsNormal p` under `b·Δ`.) -/
def IsNormalRao (a b p : k[X]) : Prop := IsCoprime p (bDeriv a b p)

/-- Rao's specialness: `p` is *special* w.r.t. `Δt = a/b` if `p ∣ b·Δp`. (Definitionally
`IsSpecial p` under `b·Δ`.) -/
def IsSpecialRao (a b p : k[X]) : Prop := p ∣ bDeriv a b p

/-- The cleared derivative of a linear factor: `b·Δ(t − α) = a − b·C(Dα)` — how `Δ` reaches the
root value, the crux of the root characterizations below. -/
theorem bDeriv_X_sub_C (a b : k[X]) (α : k) : bDeriv a b (X - C α) = a - b * C α′ := by
  show bDerivation a b (X - C α) = _
  rw [map_sub]; show bDeriv a b X - bDeriv a b (C α) = _
  rw [bDeriv_X, bDeriv_C]

/-- Single linear factor: `t − α` is *special* w.r.t. `Δt = a/b` iff
`b(α)·Δα = a(α)` at its root — i.e. `a.eval α = b.eval α · α′`. (Specialize `b·Δ(t−α) = a − b·C(α′)`
and read off the root condition `(t − α) ∣ b·Δ(t − α)`.) -/
theorem isSpecialRao_X_sub_C_iff (a b : k[X]) (α : k) :
    IsSpecialRao a b (X - C α) ↔ a.eval α = b.eval α * α′ := by
  rw [IsSpecialRao, bDeriv_X_sub_C, dvd_iff_isRoot, IsRoot.def, eval_sub, eval_mul, eval_C,
    sub_eq_zero]

/-- Single linear factor: `t − α` is *normal* w.r.t. `Δt = a/b` iff
`b(α)·Δα ≠ a(α)` at its root — i.e. `a.eval α ≠ b.eval α · α′`. -/
theorem isNormalRao_X_sub_C_iff (a b : k[X]) (α : k) :
    IsNormalRao a b (X - C α) ↔ a.eval α ≠ b.eval α * α′ := by
  rw [IsNormalRao, bDeriv_X_sub_C, isCoprime_X_sub_C_iff, eval_sub, eval_mul, eval_C, sub_ne_zero]

/-- Squarefree form: a squarefree polynomial `∏_{α∈s}(t − α)` is *normal*
w.r.t. `Δt = a/b` iff `b(α)·Δα ≠ a(α)` at *every* root — `∀ α ∈ s, a.eval α ≠ b.eval α · α′`.
Forward: each `t − α` divides the product so inherits normality (`IsNormal.of_dvd`); backward: the
pairwise-coprime normal factors multiply to a normal product (`IsNormal.prod`), reusing the generic
monomial-extension machinery under the `b·Δ` differential structure. -/
theorem isNormalRao_prod_X_sub_C_iff (a b : k[X]) (s : Finset k) :
    IsNormalRao a b (∏ α ∈ s, (X - C α)) ↔ ∀ α ∈ s, a.eval α ≠ b.eval α * α′ := by
  classical
  letI : Differential k[X] := bDifferential a b
  -- `IsNormalRao a b · = IsNormal ·` under this instance.
  have hbridge : ∀ p : k[X], IsNormalRao a b p ↔ IsNormal p := fun p => Iff.rfl
  rw [hbridge]
  constructor
  · intro hnorm α hα
    have hdvd : (X - C α) ∣ ∏ β ∈ s, (X - C β) := Finset.dvd_prod_of_mem _ hα
    exact (isNormalRao_X_sub_C_iff a b α).mp ((hbridge _).mpr (IsNormal.of_dvd hnorm hdvd))
  · intro h
    refine IsNormal.prod s (fun α => X - C α) (fun α hα => (hbridge _).mp ?_) (fun α _ β _ hαβ => ?_)
    · exact (isNormalRao_X_sub_C_iff a b α).mpr (h α hα)
    · exact isCoprime_X_sub_C_iff.mpr (by rw [eval_sub, eval_X, eval_C]; exact sub_ne_zero.mpr hαβ)

/-- Squarefree form: a squarefree polynomial `∏_{α∈s}(t − α)` is *special*
w.r.t. `Δt = a/b` iff `b(α)·Δα = a(α)` at *every* root — `∀ α ∈ s, a.eval α = b.eval α · α′`.
Backward: special is closed under products (`IsSpecial.prod`); forward: each `t − α` is a coprime
factor of the product, hence special (`IsSpecial.of_mul_coprime`). -/
theorem isSpecialRao_prod_X_sub_C_iff (a b : k[X]) (s : Finset k) :
    IsSpecialRao a b (∏ α ∈ s, (X - C α)) ↔ ∀ α ∈ s, a.eval α = b.eval α * α′ := by
  classical
  letI : Differential k[X] := bDifferential a b
  have hbridge : ∀ p : k[X], IsSpecialRao a b p ↔ IsSpecial p := fun p => Iff.rfl
  rw [hbridge]
  constructor
  · intro hsp α hα
    rw [← Finset.mul_prod_erase s (fun β => X - C β) hα] at hsp
    have hcop : IsCoprime (X - C α) (∏ β ∈ s.erase α, (X - C β)) := by
      rw [isCoprime_X_sub_C_iff, eval_prod]
      refine Finset.prod_ne_zero_iff.mpr (fun β hβ => ?_)
      rw [eval_sub, eval_X, eval_C]
      exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hβ).symm
    exact (isSpecialRao_X_sub_C_iff a b α).mp ((hbridge _).mpr (IsSpecial.of_mul_coprime hsp hcop))
  · intro h
    exact IsSpecial.prod s (fun α => X - C α)
      (fun α hα => (hbridge _).mp ((isSpecialRao_X_sub_C_iff a b α).mpr (h α hα)))

/-- Prime case: if `Δt = a/b` is in lowest terms (`gcd(a, b) = 1`) and a
prime (irreducible) `π ∈ k[t]` is *special* (`π ∣ b·Δπ`), then `gcd(π, b) = 1`. Suppose `π ∣ b`;
then from `π ∣ b·κ_D(π) + a·(dπ/dt)` and `π ∣ b·κ_D(π)` we get `π ∣ a·(dπ/dt)`. Primality forces
`π ∣ a` (impossible: `π ∣ gcd(a, b) = 1`) or `π ∣ dπ/dt` (impossible: an irreducible over a char-`0`
field is separable, so coprime to its derivative). -/
theorem isCoprime_of_isSpecialRao_prime [CharZero k] {a b π : k[X]} (hab : IsCoprime a b)
    (hπ : Prime π) (hsp : IsSpecialRao a b π) : IsCoprime π b := by
  rw [(hπ.irreducible).coprime_iff_not_dvd]
  intro hdvd
  -- `π ∣ a·(dπ/dt)`
  have hbκ : π ∣ b * kappaD k π := hdvd.mul_right _
  have hsum : π ∣ b * kappaD k π + a * derivative π := by
    rw [← bDeriv_eq]; exact hsp
  have hadπ : π ∣ a * derivative π := (dvd_add_right hbκ).mp hsum
  rcases hπ.dvd_or_dvd hadπ with hda | hdπ'
  · -- `π ∣ a` and `π ∣ b` contradict `gcd(a,b)=1`
    exact hπ.not_unit (hab.isUnit_of_dvd' hda hdvd)
  · -- `π ∣ dπ/dt` contradicts separability of the irreducible `π`
    have hsep : IsCoprime π (derivative π) := (separable_def π).mp (hπ.irreducible).separable
    exact hπ.not_unit (hsep.isUnit_of_dvd' dvd_rfl hdπ')

/-- Squarefree case: if `Δt = a/b` is in lowest terms and a *special*
squarefree `p ∈ k[t]` is written as the product `∏_{α∈s}(t − α)` of its distinct linear factors,
then `gcd(p, b) = 1` — equivalently `b.eval α ≠ 0` at every root `α`. Each `t − α` is special
(`isSpecialRao_X_sub_C_iff`), so `a(α) = b(α)·α′`; if `b(α) = 0` then `a(α) = 0` too, contradicting
`gcd(a, b) = 1` (both would vanish at `α`, so `t − α ∣ gcd(a, b)`). -/
theorem eval_ne_zero_of_isSpecialRao_prod_X_sub_C {a b : k[X]} (hab : IsCoprime a b)
    {s : Finset k} (hsp : IsSpecialRao a b (∏ α ∈ s, (X - C α))) :
    ∀ α ∈ s, b.eval α ≠ 0 := by
  intro α hα hbα
  have hroot : a.eval α = b.eval α * α′ := (isSpecialRao_prod_X_sub_C_iff a b s).mp hsp α hα
  rw [hbα, zero_mul] at hroot
  -- both `a` and `b` vanish at `α`, so `t − α ∣ gcd(a, b)`, contradicting coprimality.
  have hda : (X - C α) ∣ a := dvd_iff_isRoot.mpr hroot
  have hdb : (X - C α) ∣ b := dvd_iff_isRoot.mpr hbα
  exact (prime_X_sub_C α).not_unit (hab.isUnit_of_dvd' hda hdb)

/-! ### The generic normal/special theory transfers to Rao's definition
With `b·Δ = bDerivation a b` installed as the differential structure on `k[t]`, `IsNormalRao`/
`IsSpecialRao` are *definitionally* `IsNormal`/`IsSpecial`, so the generic normal/special
closure facts hold verbatim for Rao's normal/special. -/

/-- Rao-special polynomials are closed under multiplication. -/
theorem IsSpecialRao.mul {a b p q : k[X]} (hp : IsSpecialRao a b p) (hq : IsSpecialRao a b q) :
    IsSpecialRao a b (p * q) := by
  letI : Differential k[X] := bDifferential a b
  exact IsSpecial.mul (R := k[X]) hp hq

/-- The product of two coprime Rao-normal polynomials is Rao-normal. -/
theorem IsNormalRao.mul {a b p q : k[X]} (hp : IsNormalRao a b p) (hq : IsNormalRao a b q)
    (hpq : IsCoprime p q) : IsNormalRao a b (p * q) := by
  letI : Differential k[X] := bDifferential a b
  exact IsNormal.mul (R := k[X]) hp hq hpq

/-- Any factor of a Rao-normal polynomial is Rao-normal. -/
theorem IsNormalRao.of_dvd {a b p q : k[X]} (hp : IsNormalRao a b p) (hq : q ∣ p) :
    IsNormalRao a b q := by
  letI : Differential k[X] := bDifferential a b
  exact IsNormal.of_dvd (R := k[X]) hp hq

/-- A Rao-normal polynomial is squarefree. -/
theorem IsNormalRao.squarefree {a b p : k[X]} (hp : IsNormalRao a b p) : Squarefree p := by
  letI : Differential k[X] := bDifferential a b
  exact IsNormal.squarefree (R := k[X]) hp

/-- If `p·q` is Rao-special and `p, q` are coprime, then `p` is Rao-special. -/
theorem IsSpecialRao.of_mul_coprime {a b p q : k[X]} (h : IsSpecialRao a b (p * q))
    (hco : IsCoprime p q) : IsSpecialRao a b p := by
  letI : Differential k[X] := bDifferential a b
  exact IsSpecial.of_mul_coprime (R := k[X]) h hco

/-- A polynomial that is both Rao-normal and Rao-special is a unit (the only
normal-and-special polynomials are the units of `k`). -/
theorem isUnit_of_isNormalRao_of_isSpecialRao {a b p : k[X]} (hn : IsNormalRao a b p)
    (hs : IsSpecialRao a b p) : IsUnit p := by
  letI : Differential k[X] := bDifferential a b
  exact isUnit_of_isNormal_of_isSpecial (R := k[X]) hn hs

end Rao

/-! ## Verification examples -/

section Verification

-- The logarithmic derivative of a product of integer powers is the weighted sum of logarithmic derivatives.
example {F : Type*} [Field F] [Differential F] {ι : Type*} (s : Finset ι) (u : ι → F) (e : ι → ℤ)
    (h : ∀ i ∈ s, u i ≠ 0) :
    (∏ i ∈ s, u i ^ e i)′ / (∏ i ∈ s, u i ^ e i) = ∑ i ∈ s, (e i : F) * ((u i)′ / u i) :=
  logDeriv_prod_zpow_div s u e h

-- The logarithm-arctangent combination `t₁·√−1 − 2·t₂` is a `D`-constant.
example {E : Type*} [Field E] [Differential E] [CharZero E] {i u v t₁ t₂ : E} (hi : i ^ 2 = -1)
    (hu : u ^ 2 + 1 ≠ 0) (hv : v = (u + i) / (u - i)) (ht₁ : t₁′ = v′ / v)
    (ht₂ : t₂′ = u′ / (1 + u ^ 2)) : (t₁ * i - 2 * t₂)′ = 0 :=
  deriv_log_arctan_combination_eq_zero hi hu hv ht₁ ht₂

-- The Rao derivation satisfies the Leibniz rule.
example {k : Type*} [Field k] [Differential k] (a b p q : k[X]) :
    bDeriv a b (p * q) = p * bDeriv a b q + q * bDeriv a b p :=
  bDeriv_mul a b p q

-- A product of linear factors is Rao-normal iff every root avoids the special-value equation.
example {k : Type*} [Field k] [Differential k] (a b : k[X]) (s : Finset k) :
    IsNormalRao a b (∏ α ∈ s, (X - C α)) ↔ ∀ α ∈ s, a.eval α ≠ b.eval α * α′ :=
  isNormalRao_prod_X_sub_C_iff a b s

-- A product of linear factors is Rao-special iff every root satisfies the special-value equation.
example {k : Type*} [Field k] [Differential k] (a b : k[X]) (s : Finset k) :
    IsSpecialRao a b (∏ α ∈ s, (X - C α)) ↔ ∀ α ∈ s, a.eval α = b.eval α * α′ :=
  isSpecialRao_prod_X_sub_C_iff a b s

-- A Rao-special prime is coprime to the denominator under a coprime numerator-denominator pair.
example {k : Type*} [Field k] [Differential k] [CharZero k] {a b π : k[X]} (hab : IsCoprime a b)
    (hπ : Prime π) (hsp : IsSpecialRao a b π) : IsCoprime π b :=
  isCoprime_of_isSpecialRao_prime hab hπ hsp

end Verification

end DeepWiki.SymbolicIntegration
