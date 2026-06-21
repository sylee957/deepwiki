import DeepWiki.SymbolicIntegration.RationalIntegration
import Sources.Doi_10_1007_b138171.Source

/-! # Symbolic Integration catalog — Chapter 2: Integration of Rational Functions
Chapter 2 develops the algorithms that compute `∫ f` for `f ∈ K(x)` as a rational part plus a
sum of logarithms (eq 2.4). The mathematical heart of Hermite's reduction — the differential
identity that lowers the power of a squarefree denominator factor — is proved in the
`DeepWiki.SymbolicIntegration` library and cataloged here.

## NOT YET FORMALIZED (audit 2026-06-21; subtractive — delete each item once it is formalized)
§2.1: the full Bernoulli algorithm; the *arctan* term `∫ (Bx+C)/(x²+bx+c)ᵏ` (needs the `arctan`
  primitive); Ex 2.1.3.
§2.2: the full `HermiteReduce` algorithm (recursion over the squarefree factorization,
  `ExtendedEuclidean` finding `B, C`); Ex 2.2.1; Ex 2.2.2; Ex 2.2.3.
§2.3: the Horowitz–Ostrogradsky algorithm; Ex 2.3.1.
§2.4: Thm 2.4.1; the Rothstein–Trager algorithm.
§2.5: Thm 2.5.1; the Lazard–Rioboo–Trager algorithm; Ex 2.5.1; Ex 2.5.2.
§2.6: Thm 2.6.1; the Czichowski algorithm; Ex 2.6.1.
§2.7: Thm 2.7.1; Ex 2.7.2; Ex 2.7.3.
§2.8: Thm 2.8.1; Thm 2.8.4; Lemma 2.8.1; Rioboo's real-rational-function algorithm; Ex 2.8.1;
  Ex 2.8.2.
§2.9: the in-field-integration algorithm.
Exercises: Ex 2.2; Ex 2.3; Ex 2.4; Ex 2.5; Ex 2.7.
(The transcendental part §2.3–§2.9 is resultant/PRS-based, rests on the §1.4 subresultant backlog,
and is procedural — needs operational semantics.) -/

open scoped Differential
open DeepWiki.SymbolicIntegration

namespace DeepWiki.Si

/-! ## §2.1 The Bernoulli Algorithm -/

/-- **Equation 2.1** (§2.1, p.37), rational part: `∫ A·(x−a)⁻ᵏ dx = A·(x−a)¹⁻ᵏ/(1−k)` for `k ≠ 1`.
As a derivative identity in a differential field with `Dt = 1` (`t = x − a`): `D(tⁿ/n) = tⁿ⁻¹`
for `n ≠ 0`. -/
theorem eq_2_1_rational {F : Type*} [Field F] [Differential F] {t : F} (ht : t′ = 1) {n : ℤ}
    (hn : (n : F) ≠ 0) : (t ^ n / (n : F))′ = t ^ (n - 1) :=
  deriv_zpow_div_self ht hn

/-- **Equation 2.1** (§2.1, p.37), logarithmic part: `∫ dx/(x−a) = log(x−a)` — the integrand
`1/(x−a)` is the logarithmic derivative of `x−a` (`logDeriv t = t⁻¹` when `Dt = 1`). -/
theorem eq_2_1_log {F : Type*} [Field F] [Differential F] {t : F} (ht : t′ = 1) :
    Differential.logDeriv t = t⁻¹ :=
  logDeriv_eq_inv ht

/-! ## §2.2 The Hermite Reduction -/

/-- **Hermite reduction step** (§2.2, p.39): the differential identity at the core of Hermite's
reduction. With `k = m + 2`, if `Q = (1-k)(B·V' + C·V)` then
`Q / Vᵏ = (B / Vᵏ⁻¹)′ + ((1-k)·C - B') / Vᵏ⁻¹` — lowering the power of the squarefree factor `V`
by one. (The algorithm finds `B, C` with `deg B < deg V` via the extended Euclidean algorithm,
valid because `gcd(V, V') = 1` for squarefree `V`.) -/
theorem hermiteReduce_step {F : Type*} [Field F] [Differential F] (B C V : F) (hV : V ≠ 0)
    (m : ℕ) :
    (-((m : F) + 1) * (B * V′ + C * V)) / V ^ (m + 2)
      = (B / V ^ (m + 1))′ + (-((m : F) + 1) * C - B′) / V ^ (m + 1) :=
  hermite_reduction_step B C V hV m

end DeepWiki.Si
