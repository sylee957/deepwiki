import DeepWiki.CAlgebra.IntegrateRisch.DerivationExtend

/-! # Transcendental monomial data

The three monomial cases of a transcendental extension `K(t)` of a differential field
`(K, d)` — primitive, hyperexponential, hypertangent — as separate structures, each
carrying its defining element `η` and its Liouvillian-monomial genuineness conditions as
invariant `Prop` fields, with the prescribed variable derivative read off as
`Dt : DensePoly K`. -/

namespace DeepWiki.CAlgebra

universe u

variable {K : Type u} [Field K] [DecidableEq K]

/-- A primitive monomial `t` over `(K, d)`: `Dt = η ∈ K`, genuine when `η` is not a
derivative in `K` — then `t` is transcendental and the constants are unchanged. -/
structure MonomialPrimitive (K : Type u) [Field K] [DecidableEq K] (d : K → K) where
  /-- The defining element: `Dt = η`. -/
  η : K
  /-- Genuineness: `η` is not the derivative of an element of `K`. -/
  not_deriv : ∀ u : K, d u ≠ η

/-- A hyperexponential monomial `t` over `(K, d)`: `Dt = η·t`, genuine when `η` is not
the logarithmic derivative of a `K`-radical — then `t` is transcendental and the
constants are unchanged. -/
structure MonomialHyperexp (K : Type u) [Field K] [DecidableEq K] (d : K → K) where
  /-- The defining element: `Dt/t = η`. -/
  η : K
  /-- Genuineness: no `n ≠ 0` and `u ≠ 0` with `n·η = d u / u`. -/
  not_logDeriv_radical : ∀ n : ℤ, n ≠ 0 → ∀ u : K, u ≠ 0 → (n : K) * η * u ≠ d u

/-- A hypertangent monomial `t` over `(K, d)`: `Dt = η·(1 + t²)`, genuine when `√−1·η`
is not the logarithmic derivative of a `K(√−1)`-radical — then `t` is transcendental
and the constants are unchanged. The condition is encoded componentwise on
`u = a + b·√−1`: `n·√−1·η·u = d u` unfolds to `d a = −n·η·b` and `d b = n·η·a`. -/
structure MonomialHypertangent (K : Type u) [Field K] [DecidableEq K] (d : K → K) where
  /-- The defining element: `Dt/(1 + t²) = η`. -/
  η : K
  /-- Genuineness, componentwise on `K(√−1)`: no `n ≠ 0` and `(a, b) ≠ (0, 0)` with
  `d a = −n·η·b` and `d b = n·η·a`. -/
  not_logDeriv_radical_adjoin : ∀ n : ℤ, n ≠ 0 → ∀ a b : K, ¬(a = 0 ∧ b = 0) →
    ¬(d a = -((n : K) * η) * b ∧ d b = (n : K) * η * a)

namespace MonomialPrimitive

variable {d : K → K}

/-- The prescribed derivative of the variable: `Dt = η`. -/
def Dt (M : MonomialPrimitive K d) : DensePoly K := DensePoly.C M.η

/-- A genuine primitive has a nonzero defining element. -/
theorem η_ne_zero (hd : IsDerivation d) (M : MonomialPrimitive K d) : M.η ≠ 0 :=
  fun h0 => M.not_deriv 0 (by rw [hd.map_zero, h0])

end MonomialPrimitive

namespace MonomialHyperexp

variable {d : K → K}

/-- The prescribed derivative of the variable: `Dt = η·t`. -/
def Dt (M : MonomialHyperexp K d) : DensePoly K := DensePoly.ofList [0, M.η]

/-- A genuine hyperexponential has a nonzero defining element. -/
theorem η_ne_zero (hd : IsDerivation d) (M : MonomialHyperexp K d) : M.η ≠ 0 :=
  fun h0 => M.not_logDeriv_radical 1 one_ne_zero 1 one_ne_zero
    (by rw [h0, hd.map_one, mul_zero, zero_mul])

end MonomialHyperexp

namespace MonomialHypertangent

variable {d : K → K}

/-- The prescribed derivative of the variable: `Dt = η·(1 + t²)`. -/
def Dt (M : MonomialHypertangent K d) : DensePoly K := DensePoly.ofList [M.η, 0, M.η]

/-- A genuine hypertangent has a nonzero defining element. -/
theorem η_ne_zero (hd : IsDerivation d) (M : MonomialHypertangent K d) : M.η ≠ 0 :=
  fun h0 => M.not_logDeriv_radical_adjoin 1 one_ne_zero 1 0
    (fun h => one_ne_zero h.1)
    ⟨by rw [hd.map_one, mul_zero], by rw [hd.map_zero, h0, mul_zero, zero_mul]⟩

end MonomialHypertangent

end DeepWiki.CAlgebra
