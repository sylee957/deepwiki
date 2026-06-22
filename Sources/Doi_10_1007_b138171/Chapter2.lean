import DeepWiki.SymbolicIntegration.RationalIntegration
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms
import DeepWiki.SymbolicIntegration.Residues
import Sources.Doi_10_1007_b138171.Source

/-! # Symbolic Integration catalog — Chapter 2: Integration of Rational Functions
Chapter 2 develops the algorithms that compute `∫ f` for `f ∈ K(x)` as a rational part plus a
sum of logarithms (eq 2.4). The mathematical heart of Hermite's reduction — the differential
identity that lowers the power of a squarefree denominator factor — is proved in the
`DeepWiki.SymbolicIntegration` library and cataloged here.

## NOT YET FORMALIZED (audit 2026-06-21; subtractive — delete each item once it is formalized)
(Algorithms are being formalized as functional Lean `def`s + correctness lemmas, NOT operational
semantics — shared kernel `diophantineSolve` (extended-Euclidean Bézout solve) is in
`DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms`.)
§2.1: the full Bernoulli algorithm [functional]; the *arctan* term `∫ (Bx+C)/(x²+bx+c)ᵏ` (needs the
  `arctan` primitive); Ex 2.1.3.
§2.2: the full `HermiteReduce` algorithm (recursion over the squarefree factorization, `B, C` via
  `diophantineSolve`) [functional]; the per-algorithm traces of Ex 2.2.1/2.2.2/2.2.3 [functional]
  (their shared *result* is `ex_2_3_1`).
§2.3: the Horowitz–Ostrogradsky linear solve for `B, C` [functional]. The denominator split is done:
  `horowitzOstrogradsky_split` (= `hoSplit`, `(gcd(D,D'), D/gcd(D,D'))`) with `hoSplit_mul` (`D⁻·D* = D`)
  and `hoSplit_snd_squarefree` (`D*` is the squarefree radical). (Ex 2.3.1's *result* — shared with
  Ex 2.2.1 — is `ex_2_3_1`.)
§2.4: Thm 2.4.1(iii) [external: splitting-field minimality, proved in Chaps 4/5]; the Rothstein–Trager
  algorithm's formal log-sum assembly over the roots of `R` [functional: needs the root-indexed sum].
  Parts (i),(ii) are PROVED: `thm_2_4_1_i` (= `residue_iff_resultant_eq_zero`, the zeros of
  `R = resultant_x(D, A − t·D')` are exactly the residues) and `thm_2_4_1_ii` (= `isRoot_gcd_iff_residue`,
  the `Gₐ` characterization); the algorithm's two computational primitives are functional defs
  `intRationalLogPart_resultant`/`_gcd`, both on the §4.4 residue foundation.
§2.5: Thm 2.5.1 [research: subresultant-multiplicity proof, rests on Thms 1.4.1/1.4.3/1.5.1/1.5.2];
  the Lazard–Rioboo–Trager algorithm [functional]; Ex 2.5.2.
§2.6: Thm 2.6.1; the Czichowski algorithm [functional]; Ex 2.6.1.
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

/-- **Theorem 2.4.1(i)** (§2.4, p.47), the Rothstein–Trager resultant criterion: over `K̄`, the zeros
of `R = resultant_x(D, A − t·D')` are exactly the residues of `A/D` at the zeros of `D` — i.e.
`R(a) = 0 ↔ ∃ α, D(α) = 0 ∧ A(α)/D'(α) = a`, for squarefree (`Separable`) `D`. The library's
`residue_iff_resultant_eq_zero`, via Mathlib's `Polynomial.resultant` and `resultant_eq_zero_iff`. -/
abbrev thm_2_4_1_i := @DeepWiki.SymbolicIntegration.residue_iff_resultant_eq_zero

/-- **Theorem 2.4.1(ii)** (§2.4, p.47), the Rothstein–Trager residue characterization: the roots of
`Gₐ = gcd(D, A − a·D')` are exactly the roots of `D` whose residue is `a`. The library's
`isRoot_gcd_iff_residue` (built on the §4.4 residue `A(α)/D'(α)`). Part (iii) — splitting-field
minimality — is delegated to Chaps 4/5 and remains [external]. -/
abbrev thm_2_4_1_ii := @DeepWiki.SymbolicIntegration.isRoot_gcd_iff_residue

/-- **IntRationalLogPart / Rothstein–Trager algorithm** (§2.4, p.51), resultant primitive `R(t)`: the
functional def `rtResultant A D = resultant_x(D, A − t·D')`, with `rtResultant_eval` specializing it
at `t = a` and `rtResultant_eval_eq_zero_iff` (= Thm 2.4.1(i)) characterizing its roots as residues. -/
noncomputable abbrev intRationalLogPart_resultant := @DeepWiki.SymbolicIntegration.rtResultant

/-- **IntRationalLogPart / Rothstein–Trager algorithm** (§2.4, p.51), gcd primitive `Gₐ`: the
functional def `rtLogGcd A D a = gcd(D, A − a·D')`, with correctness `rtLogGcd_isRoot_iff`
(= Thm 2.4.1(ii)). The full algorithm sums `a·log(Gₐ)` over the roots `a` of `R`. -/
noncomputable abbrev intRationalLogPart_gcd := @DeepWiki.SymbolicIntegration.rtLogGcd

/-- **Horowitz–Ostrogradsky algorithm** (§2.3, p.46), denominator split: the functional def
`hoSplit D = (gcd(D, D'), D/gcd(D, D')) = (D⁻, D*)`, with `hoSplit_mul` (`D⁻·D* = D`) and
`hoSplit_snd_squarefree` (`D*` is the squarefree radical of `D`, char `0`). The algorithm then solves
a linear system for the numerators `B, C`. -/
noncomputable abbrev horowitzOstrogradsky_split := @DeepWiki.SymbolicIntegration.hoSplit

open Polynomial in
/-- **Example 2.4.1** (§2.4, p.48), the Rothstein–Trager residue computation for
`f = (x⁴−3x²+6)/(x⁶−5x⁴+5x²+4)`: `D = x⁶−5x⁴+5x²+4` is squarefree, `D' = 6x⁵−20x³+10x`, and for an
algebraic constant `a` with `4a²+1 = 0` the residue gcd is `Gₐ = gcd(D, A−aD') = x³+2ax²−3x−4a`.
Faithful core: `Gₐ` divides both `D` and `A−aD'` — exhibited by the exact cofactorizations
`D = Gₐ·(x³−2ax²−3x+4a)` and `A−aD' = Gₐ·(−6ax²−2x+6a)` (both modulo `4a²+1 = 0`). By `thm_2_4_1_ii`
this makes every root of `Gₐ` a root of `D` with residue `a`. -/
theorem ex_2_4_1 {F : Type*} [Field F] (a : F) (ha : 4 * a ^ 2 + 1 = 0) :
    ((X : F[X]) ^ 6 - 5 * X ^ 4 + 5 * X ^ 2 + 4
        = (X ^ 3 + 2 * C a * X ^ 2 - 3 * X - 4 * C a) * (X ^ 3 - 2 * C a * X ^ 2 - 3 * X + 4 * C a))
      ∧ ((X : F[X]) ^ 4 - 3 * X ^ 2 + 6 - C a * (6 * X ^ 5 - 20 * X ^ 3 + 10 * X)
        = (X ^ 3 + 2 * C a * X ^ 2 - 3 * X - 4 * C a) * (-6 * C a * X ^ 2 - 2 * X + 6 * C a)) := by
  have hb : 4 * (C a) ^ 2 + 1 = (0 : F[X]) := by
    have h := congrArg (C : F →+* F[X]) ha
    simpa [map_ofNat] using h
  refine ⟨?_, ?_⟩
  · linear_combination ((X : F[X]) ^ 2 - 2) ^ 2 * hb
  · linear_combination (3 * ((X : F[X]) ^ 2 - 1) * (X ^ 2 - 2)) * hb

/-- **Examples 2.2.1 / 2.3.1** (§2.2–2.3, p.41,46), the Hermite / Horowitz–Ostrogradsky *result*: in a
differential field with `t′ = 1` (the integration variable, `t ≠ 0`, `t²+2 ≠ 0`),
`∫ (t⁷−24t⁴−4t²+8t−8)/(t⁸+6t⁶+12t⁴+8t²) dt = (3t³+8t²+6t+4)/(t⁵+4t³+4t) + ∫ dt/t`, i.e. the rational part
is `(3t³+8t²+6t+4)/(t⁵+4t³+4t)` and the remaining integrand reduces to `1/t` (`logDeriv t`). Verified as
the differential-field identity `((3t³+8t²+6t+4)/(t⁵+4t³+4t))′ + t⁻¹ = the integrand` (`deriv_div` +
cross-multiplied `ring`). Both denominators factor as `t·(t²+2)²` and `t²·(t²+2)³`. -/
theorem ex_2_3_1 {F : Type*} [Field F] [Differential F] {t : F} (ht : t′ = 1) (ht0 : t ≠ 0) (ht2 : t ^ 2 + 2 ≠ 0) :
    ((3 * t ^ 3 + 8 * t ^ 2 + 6 * t + 4) / (t ^ 5 + 4 * t ^ 3 + 4 * t))′ + t⁻¹
      = (t ^ 7 - 24 * t ^ 4 - 4 * t ^ 2 + 8 * t - 8) / (t ^ 8 + 6 * t ^ 6 + 12 * t ^ 4 + 8 * t ^ 2) := by
  have hQ : (t ^ 5 + 4 * t ^ 3 + 4 * t : F) ≠ 0 := by
    have h : (t ^ 5 + 4 * t ^ 3 + 4 * t : F) = t * (t ^ 2 + 2) ^ 2 := by ring
    rw [h]; exact mul_ne_zero ht0 (pow_ne_zero _ ht2)
  have hD : (t ^ 8 + 6 * t ^ 6 + 12 * t ^ 4 + 8 * t ^ 2 : F) ≠ 0 := by
    have h : (t ^ 8 + 6 * t ^ 6 + 12 * t ^ 4 + 8 * t ^ 2 : F) = t ^ 2 * (t ^ 2 + 2) ^ 3 := by ring
    rw [h]; exact mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ ht2)
  have h3 : (3 : F)′ = 0 := mem_constants.mp (by norm_num)
  have h4 : (4 : F)′ = 0 := mem_constants.mp (by norm_num)
  have h6 : (6 : F)′ = 0 := mem_constants.mp (by norm_num)
  have h8 : (8 : F)′ = 0 := mem_constants.mp (by norm_num)
  rw [deriv_div]
  simp only [map_add, deriv_const_mul _ h3, deriv_const_mul _ h4, deriv_const_mul _ h6,
    deriv_const_mul _ h8, h4, deriv_pow, ht, mul_one]
  rw [show (t⁻¹ : F) = 1 / t from (one_div t).symm,
    div_add_div _ _ (pow_ne_zero 2 hQ) ht0,
    div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hQ) ht0) hD]
  ring

/-! ## §2.5 The Lazard–Rioboo–Trager Algorithm -/

open Polynomial in
/-- **Example 2.5.1** (§2.5, p.52), Lazard–Rioboo–Trager on the same integrand as Ex 2.4.1: the
subresultant PRS of `D = x⁶−5x⁴+5x²+4` and `A−tD'` has a degree-3 element `R₃ = S₃`, and at a root
`a` of `Q₃` (`4a²+1 = 0`) the book computes `S₃(a,x) = −214ax³+107x²+642ax−214`. Faithful punchline
(`ex_2_5_1`): this value is exactly `−214a·(x³+2ax²−3x−4a)`, i.e. `−214a` times the Rothstein–Trager
gcd `Gₐ` of Ex 2.4.1 — so the LRT subresultant and the RT gcd agree up to the scalar `−214a`, and
monic-normalizing `S₃(a,x)` recovers `Gₐ`. Verified as the algebraic identity modulo `4a²+1 = 0`
(`linear_combination … * hb`); this checks the normalization step, not the PRS computation itself. -/
theorem ex_2_5_1 {F : Type*} [Field F] (a : F) (ha : 4 * a ^ 2 + 1 = 0) :
    (-214 * C a * (X : F[X]) ^ 3 + 107 * X ^ 2 + 642 * C a * X - 214
      = -214 * C a * (X ^ 3 + 2 * C a * X ^ 2 - 3 * X - 4 * C a)) := by
  have hb : 4 * (C a) ^ 2 + 1 = (0 : F[X]) := by
    have h := congrArg (C : F →+* F[X]) ha
    simpa [map_ofNat] using h
  linear_combination (107 * ((X : F[X]) ^ 2 - 2)) * hb

end DeepWiki.Si
