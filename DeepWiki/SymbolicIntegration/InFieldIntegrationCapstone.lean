import DeepWiki.SymbolicIntegration.InFieldIntegration

/-! # In-field integration — the constructive antiderivative (Bronstein §2.9, "Recognizing Derivatives")
The recognition criterion `isRationalDerivative_iff` decides whether `f ∈ K(x)` has a rational
antiderivative: after the Hermite reduction `f = (algebraMap g)′ + A/D` (`D` squarefree,
`gcd(A, D) = 1`, `deg A < deg D`), `(∃ v, v′ = f) ↔ A = 0`. This file supplies the **constructive**
half the book states as "in which case `u = g`": when `A = 0` the Hermite quotient `g` *is* the
antiderivative — `inFieldIntegral g = algebraMap g` with `(inFieldIntegral g)′ = f`
(`inFieldIntegral_spec`). Combined with the criterion this gives the decision-with-witness
`inFieldIntegrable_iff`: `f` is in-field-integrable iff `A = 0`, the witness being `g`. -/

open Polynomial
open scoped Differential

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- **In-field antiderivative** (Bronstein §2.9, "Recognizing Derivatives", the constructive output):
the Hermite quotient `g ∈ K[X]` viewed in `K(x)` as the antiderivative — `inFieldIntegral g =
algebraMap g`. When the Hermite-reduced log-part numerator `A = 0` (the integrability criterion),
this `g` satisfies `(inFieldIntegral g)′ = f` (`inFieldIntegral_spec`), realizing the book's
"in which case `u = g`". -/
noncomputable def inFieldIntegral (g : K[X]) : RatFunc K :=
  algebraMap K[X] (RatFunc K) g

/-- `inFieldIntegral g = algebraMap g` — the antiderivative is the Hermite quotient, read in `K(x)`. -/
@[simp] theorem inFieldIntegral_eq (g : K[X]) :
    inFieldIntegral g = algebraMap K[X] (RatFunc K) g := rfl

/-- **In-field antiderivative correctness** (Bronstein §2.9, the constructive half of "Recognizing
Derivatives"): if the Hermite reduction is `f = (algebraMap g)′ + A/D` and the log-part numerator
`A = 0` (the integrability criterion holds), then the Hermite quotient `g` is an antiderivative of
`f` — `(inFieldIntegral g)′ = f`. This is the book's `u = g + ∫(A/D)dx` with the `∫(A/D)` term
vanishing because `A = 0`. -/
theorem inFieldIntegral_spec {f : RatFunc K} {g A D : K[X]} (hA : A = 0)
    (hf : f = (algebraMap K[X] (RatFunc K) g)′
          + algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) D) :
    (inFieldIntegral g)′ = f := by
  rw [inFieldIntegral, hf, hA, map_zero, zero_div, add_zero]

/-- **In-field integrability decision, with witness** (Bronstein §2.9, "Recognizing Derivatives" —
the payoff): for `f ∈ K(x)` with Hermite reduction `f = (algebraMap g)′ + A/D` (`D` squarefree,
`gcd(A, D) = 1`, `deg A < deg D`), `f` has a rational antiderivative **iff** `A = 0`; and when so, the
explicit Hermite quotient `g` is one — `(inFieldIntegral g)′ = f`. Packages the recognition criterion
`isRationalDerivative_iff` with the constructive antiderivative `inFieldIntegral_spec`. -/
theorem inFieldIntegrable_iff [CharZero K] {f : RatFunc K} {g A D : K[X]}
    (hD : Squarefree D) (hAD : IsCoprime A D) (hdeg : A.degree < D.degree)
    (hf : f = (algebraMap K[X] (RatFunc K) g)′
          + algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) D) :
    (∃ v : RatFunc K, v′ = f) ↔ (A = 0 ∧ (inFieldIntegral g)′ = f) := by
  rw [isRationalDerivative_iff hD hAD hdeg hf]
  constructor
  · intro hA; exact ⟨hA, inFieldIntegral_spec hA hf⟩
  · exact fun h => h.1

/-- The constructive in-field-integral against the book's wording (`A = 0` ⟹ the Hermite quotient `g`
is the antiderivative, `(algebraMap g)′ = f`). -/
example {f : RatFunc K} {g A D : K[X]} (hA : A = 0)
    (hf : f = (algebraMap K[X] (RatFunc K) g)′
          + algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) D) :
    (algebraMap K[X] (RatFunc K) g)′ = f :=
  inFieldIntegral_spec hA hf

/-- The in-field integrability decision-with-witness against the book's wording (`f` integrable iff
`A = 0`, witness the Hermite quotient `g`). -/
example [CharZero K] {f : RatFunc K} {g A D : K[X]} (hD : Squarefree D) (hAD : IsCoprime A D)
    (hdeg : A.degree < D.degree)
    (hf : f = (algebraMap K[X] (RatFunc K) g)′
          + algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) D) :
    (∃ v : RatFunc K, v′ = f) ↔ (A = 0 ∧ (inFieldIntegral g)′ = f) :=
  inFieldIntegrable_iff hD hAD hdeg hf

end DeepWiki.SymbolicIntegration
