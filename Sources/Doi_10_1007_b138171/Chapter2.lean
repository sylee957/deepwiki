import DeepWiki.SymbolicIntegration.RationalIntegration
import Sources.Doi_10_1007_b138171.Source

/-! # Symbolic Integration catalog — Chapter 2: Integration of Rational Functions
Chapter 2 develops the algorithms that compute `∫ f` for `f ∈ K(x)` as a rational part plus a
sum of logarithms (eq 2.4). The mathematical heart of Hermite's reduction — the differential
identity that lowers the power of a squarefree denominator factor — is proved in the
`DeepWiki.SymbolicIntegration` library and cataloged here.

**Deferred — `DeepWiki.SymbolicIntegration` library/algorithmic work (in book order):**
  • §2.1 the Bernoulli algorithm (the `∫ A/(x-a)ᵏ` and `∫ (Bx+C)/(x²+bx+c)ᵏ` closed forms, eqns
    2.1–2.3) — these need the formal antiderivative / `log`+`arctan` primitives.
  • §2.2 the full `HermiteReduce` algorithm (recursion over the squarefree factorization with
    `ExtendedEuclidean` finding `B, C`) and Example 2.2.1 — needs §1.7 squarefree factorization.
  • §2.3 Horowitz–Ostrogradsky, §2.4 Rothstein–Trager, §2.5 Lazard–Rioboo–Trager,
    §2.6 Czichowski, §2.7 Newton–Leibniz–Bernoulli, §2.8 Rioboo's real algorithm,
    §2.9 in-field integration — the transcendental part (resultant-based logarithm computation),
    resting on the §1.4 subresultant/PRS backlog. -/

open scoped Differential
open DeepWiki.SymbolicIntegration

namespace DeepWiki.Si

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
