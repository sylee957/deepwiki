import DeepWiki.SymbolicIntegration.RationalIntegration
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms
import DeepWiki.SymbolicIntegration.RationalIntegrationLogForm
import DeepWiki.SymbolicIntegration.RationalIntegrationExamples
import DeepWiki.SymbolicIntegration.PartialFraction
import DeepWiki.SymbolicIntegration.Residues
import DeepWiki.SymbolicIntegration.RationalIntegrationGcdLogForm
import DeepWiki.SymbolicIntegration.ResidueMultiplicity
import DeepWiki.SymbolicIntegration.PseudoRemainderSequence
import DeepWiki.SymbolicIntegration.LazardRiobooTragerCorrectness
import DeepWiki.SymbolicIntegration.GroebnerBasis
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
§2.4: Thm 2.4.1(iii) [external: splitting-field minimality, proved in Chaps 4/5].
§2.6: Czichowski's structural lemmas — Lazard (1985) Lemma 1 (`lazard_lemma1`), the K[x][y]
  representation bridge (`leadingYCoeff`, `degree_apply_zero_eq_natDegree_lazardView`), and Lemma 2
  (`R_{k+1} ∣ Rₖ`, `lazard_lemma2`, via the GCD/Bézout transfer `gcdMonoidMvPolynomialFinOne` /
  `exists_mul_add_mul_eq_gcd`, the gcd construction `lazard_gcd_construction`, and the x-degree
  bridge `lex_degree_apply_one`) are done. Lemma 3, the `Pₖ = Rₖ·Sₖ` factorization, and the
  normal-position analysis of `⟨A−zD', D⟩` remain [research: Czichowski normal position].
§2.7: Thm 2.7.1 (the Bronstein–Salvy full-partial-fraction coefficients `Hᵢⱼ`) [functional/infra:
  needs the Laurent-series coefficient algorithm].
§2.8: Thm 2.8.1; Thm 2.8.4; Rioboo's real-rational-function algorithm; Ex 2.8.1; Ex 2.8.2.
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
abbrev eq_2_1_rational := @DeepWiki.SymbolicIntegration.deriv_zpow_div_self

/-- **Equation 2.1** (§2.1, p.37), logarithmic part: `∫ dx/(x−a) = log(x−a)` — the integrand
`1/(x−a)` is the logarithmic derivative of `x−a` (`logDeriv t = t⁻¹` when `Dt = 1`). The library's
`logDeriv_eq_inv`. -/
abbrev eq_2_1_log := @DeepWiki.SymbolicIntegration.logDeriv_eq_inv

/-- **Equation 2.3 / Bernoulli partial fraction** (§2.1, p.38, simple-root case): for squarefree
`D = ∏_{α∈s}(X−α)` and `deg A < #s`, `A = ∑_{α∈s} (A(α)/D'(α))·(D/(X−α))`, i.e. `A/D = ∑_{α|D=0}
(A(α)/D'(α))/(X−α)` — the partial fraction over the roots of `D`, residue `A(α)/D'(α)` at each (the
`∑_{α|D(α)=0}` sum underlying Bernoulli's algorithm and the §2.4 logarithmic part). The library's
`eq_sum_residue_mul_nodal_div`, via Mathlib's Lagrange interpolation. -/
abbrev eq_2_3_residue := @DeepWiki.SymbolicIntegration.eq_sum_residue_mul_nodal_div

/-- **Bernoulli partial fraction in `K(x)`** (§2.1, eq 2.3): `A/D = ∑_{α|D=0} (A(α)/D'(α))/(X−α)` for
squarefree `D = ∏_{α∈s}(X−α)`, `deg A < #s` — the partial fraction as a rational-function identity.
The library's `ratFunc_eq_sum_residue_div`. -/
abbrev eq_2_3_ratFunc := @DeepWiki.SymbolicIntegration.ratFunc_eq_sum_residue_div

/-- **Bernoulli integral** (§2.1, eq 2.2): `∫ A/D = ∑_{α|D=0} (A(α)/D'(α))·log(X−α)` for squarefree
`D`, `deg A < deg D` — the derivative of `∑ (A(α)/D'(α))·log(X−α)` is the integrand `A/D` (modeling
`log(X−α)` by an element with derivative `1/(X−α)`). The library's `deriv_sum_residue_log`. -/
abbrev bernoulli_integral := @DeepWiki.SymbolicIntegration.deriv_sum_residue_log

/-- **Example 2.1.3** (§2.1, p.38), Bernoulli's algorithm for `f = 1/(x³+x)` over `ℚ(√−1)`: factoring
`x³+x = x(x+i)(x−i)` linearly (`i = √−1`, `i² = −1`) gives the partial-fraction decomposition
`1/(x³+x) = 1/x − (1/2)/(x+i) − (1/2)/(x−i)`, whence `∫ dx/(x³+x) = log x − ½log(x+i) − ½log(x−i)` (an
integral over `ℚ(√−1)`; cf. eq 2.2 for the `√−1`-free form). Faithful core: the field identity below,
where the numerator collapses to `−i² = 1`. -/
abbrev ex_2_1_3 := @DeepWiki.SymbolicIntegration.inv_cubic_partialFraction

/-- **Equation 2.1, the arctan term** (§2.1, p.37): for an irreducible real quadratic `x²+bx+c`
(`4c−b² > 0`, `s = √(4c−b²)`), `∫ (Bx+C)/(x²+bx+c) dx = (B/2)·log(x²+bx+c) +
(2C−bB)/s · arctan((2x+b)/s)`. Modeling `log(x²+bx+c)` by `L` with `L′ = (2x+b)/(x²+bx+c)` and
`arctan((2x+b)/s)` by `Θ` with the arctan law `Θ′ = (2x+b)/s)' / (1 + ((2x+b)/s)²)`, this verifies the
formula as the differential-field identity below: the arctan derivative simplifies via `s² = 4c−b²` to
`s/(2(x²+bx+c))`, and the two parts combine to `(Bx+C)/(x²+bx+c)`. -/
abbrev eq_2_1_arctan := @DeepWiki.SymbolicIntegration.deriv_logArctan_eq_quadratic

/-- **Equation 2.1, the arctan-term reduction — core identity** (§2.1, p.37): the polynomial identity
driving the `k>1` recursive reduction of `∫ (Bx+C)/(x²+bx+c)ᵏ = ((2C−bB)x+bC−2cB)/((k−1)(4c−b²)q^(k−1)) +
∫ (2k−3)(2C−bB)/((k−1)(4c−b²)q^(k−1))` (`q = x²+bx+c`). Differentiating the rational part and adding the
reduced integrand, the `q`-powers cancel and the whole reduction collapses to this identity
`2(2C−bB)·q − (2x+b)·((2C−bB)x + bC−2cB) = (Bx+C)·(4c−b²)` — the numerator balance that lowers `k` to
`k−1` (iterating reaches `k=1` = `eq_2_1_arctan`). -/
abbrev eq_2_1_arctan_reduce_core := @DeepWiki.SymbolicIntegration.quadraticPow_reduce_core

/-- **Equation 2.1, the arctan term for `k>1`** (§2.1, p.37), the full recursive reduction: with
`q = x²+bx+c` (`4c−b² ≠ 0`) and `k = m+2`,
`∫ (Bx+C)/qᵏ = ((2C−bB)x+bC−2cB)/((k−1)(4c−b²)q^(k−1)) + ∫ (2k−3)(2C−bB)/((k−1)(4c−b²)q^(k−1))`,
lowering the quadratic power `k → k−1` (iterating reaches `k=1` = `eq_2_1_arctan`). Verified as the
differential-field identity: the rational part's derivative plus the reduced integrand equals the
original integrand `(Bx+C)/qᵏ`, collapsing via `eq_2_1_arctan_reduce_core`. -/
abbrev eq_2_1_arctan_reduce := @DeepWiki.SymbolicIntegration.deriv_quadraticPow_reduce

/-! ## §2.2 The Hermite Reduction -/

/-- **Hermite reduction step** (§2.2, p.39): the differential identity at the core of Hermite's
reduction. With `k = m + 2`, if `Q = (1-k)(B·V' + C·V)` then
`Q / Vᵏ = (B / Vᵏ⁻¹)′ + ((1-k)·C - B') / Vᵏ⁻¹` — lowering the power of the squarefree factor `V`
by one. (The algorithm finds `B, C` with `deg B < deg V` via the extended Euclidean algorithm,
valid because `gcd(V, V') = 1` for squarefree `V`.) -/
abbrev hermiteReduce_step := @DeepWiki.SymbolicIntegration.hermite_reduction_step

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

/-- **Rothstein–Trager resultant as a product over roots** (§2.4; Thm 1.4.1 = `thm_1_4_1_prod`,
specialized at `t = a`): over `K̄`, for `deg A < deg D`,
`R(a) = lc(D)^{deg D−1}·∏_{α:D(α)=0}(A(α)−a·D'(α))`. The library's `rtResultant_eval_eq_prod_roots`. The
root `a` has multiplicity `#{α : residue(α)=a} = deg gcd(D, A−aD')` — the residue-multiplicity count
behind Thm 2.5.1. -/
abbrev intRationalLogPart_resultant_prod :=
  @DeepWiki.SymbolicIntegration.rtResultant_eval_eq_prod_roots

/-- **Logarithmic part as a `logDeriv` sum** (§2.4, the integral exhibited as logarithms): for squarefree
`D = ∏_{α∈s}(X−α)` and `deg A < #s`, `A/D = ∑_{α∈s} (A(α)/D'(α))·logDeriv(X−α)` in `K(x)`, so
`∫ A/D = ∑ (A(α)/D'(α))·log(X−α)` — the explicit (simple-root) Rothstein–Trager logarithmic part, each
`1/(X−α)` being `logDeriv(X−α)`. The library's `ratFunc_eq_sum_residue_logDeriv`. -/
abbrev intRationalLogPart_logDeriv :=
  @DeepWiki.SymbolicIntegration.ratFunc_eq_sum_residue_logDeriv

/-- **Rothstein–Trager residue-grouped log sum** (§2.4): grouping the per-root sum by residue value,
`A/D = ∑_{a} a·logDeriv(Gₐ)` over the distinct residues `a = A(α)/D'(α)`, where `Gₐ = ∏_{α:res(α)=a}(X−α)`
is the Rothstein–Trager polynomial — so `∫ A/D = ∑_a a·log(Gₐ)`, the final algorithm output. The library's
`ratFunc_eq_sum_residue_grouped`. -/
abbrev intRationalLogPart_grouped :=
  @DeepWiki.SymbolicIntegration.ratFunc_eq_sum_residue_grouped

/-- **Horowitz–Ostrogradsky algorithm** (§2.3, p.46), denominator split: the functional def
`hoSplit D = (gcd(D, D'), D/gcd(D, D')) = (D⁻, D*)`, with `hoSplit_mul` (`D⁻·D* = D`) and
`hoSplit_snd_squarefree` (`D*` is the squarefree radical of `D`, char `0`). The algorithm then solves
a linear system for the numerators `B, C`. -/
noncomputable abbrev horowitzOstrogradsky_split := @DeepWiki.SymbolicIntegration.hoSplit

/-- **Key divisibility for Horowitz** (§2.3, p.46): `D⁻ = gcd(D, D')` divides `D⁻′·D*` (`D* = D/D⁻`),
which is what makes the Horowitz polynomial `E = D⁻′·D*/D⁻` exist and the reduction stay in `K[X]`. The
library's `hoSplit_fst_dvd_deriv_mul_snd`. -/
noncomputable abbrev horowitzOstrogradsky_dvd :=
  @DeepWiki.SymbolicIntegration.hoSplit_fst_dvd_deriv_mul_snd

/-- **Horowitz–Ostrogradsky reduction identity** (§2.3, p.46): given the split `D = D⁻·D*`, the Horowitz
polynomial `E` (`E·D⁻ = D⁻′·D*`), and numerators with `B′·D* − B·E + C·D⁻ = A`, the integral identity
`A/(D⁻·D*) = (B/D⁻)′ + C/D*` holds in `K(x)` — so `∫ A/D = B/D⁻ + ∫ C/D*`, the rational part split off
in one shot. The library's `horowitzReduce_step_ratFunc`; the abstract differential-field form is
`horowitz_reduction_step`. The algorithm finds `B, C` (degree-bounded) by a linear system. -/
abbrev horowitzReduce_step_ratFunc :=
  @DeepWiki.SymbolicIntegration.horowitzReduce_step_ratFunc

/-- **Hermite reduction step**, integral form in `K(x)` (§2.2, p.39): given Bézout data
`B·V' + Cc·V = A`, `∫ (1−k)A/Vᵏ = B/Vᵏ⁻¹ + ∫ ((1−k)Cc − B')/Vᵏ⁻¹` (`k = m+2`) — the integrand's
denominator power drops by one. The library's `hermiteReduce_step_ratFunc`, a theorem about rational
functions (using `K(x) = RatFunc K`'s `Differential` structure), with `B, Cc` from `diophantineSolve`. -/
abbrev hermiteReduce_step_ratFunc := @DeepWiki.SymbolicIntegration.hermiteReduce_step_ratFunc

/-- **Hermite reduction — prime-power inner loop** (§2.2, p.39, Algorithm `HermiteReduce` inner
recursion): the functional `def hermiteReducePower V k A` iterating the reduction step to reduce
`A/Vᵏ` (squarefree `V`) to `g + r/V` — the accumulated rational part `g ∈ K(x)` and the final
numerator `r` over the squarefree `V`. The library's `hermiteReducePower`. -/
noncomputable abbrev hermiteReducePower := @DeepWiki.SymbolicIntegration.hermiteReducePower

/-- **Correctness of the Hermite prime-power loop** (§2.2, p.39): for squarefree `V` over a char-`0`
field and `k ≥ 1`, `A/Vᵏ = g′ + r/V` with `(g, r) = hermiteReducePower V k A` — i.e.
`∫ A/Vᵏ = g + ∫ r/V`, the rational part split off and the remaining integral squarefree-denominatored.
The library's `hermiteReducePower_spec`. -/
abbrev hermiteReducePower_spec := @DeepWiki.SymbolicIntegration.hermiteReducePower_spec

/-- **Two-factor partial fraction in `K(x)`** (§2.2, the coprime split feeding the outer Hermite
recursion): for coprime `P, Q ≠ 0`, `A/(P·Q) = B/Q + C/P` where `(B, C) = diophantineSolve P Q A`
(Bézout `P·B + Q·C = A`). The inductive building block of the multi-factor partial-fraction decomposition
across a squarefree factorization. The library's `ratFunc_partialFraction_coprime`. -/
abbrev ratFunc_partialFraction_coprime :=
  @DeepWiki.SymbolicIntegration.ratFunc_partialFraction_coprime

/-- **Multi-factor partial fraction in `K(x)`** (§2.2, full coprime decomposition): for a nonempty
family of pairwise-coprime nonzero `P i` (`i ∈ s`), `A/∏ᵢ Pᵢ = ∑ᵢ Bᵢ/Pᵢ` for some `B i` — iterate the
two-factor split across the family. Specializing to the prime powers `Dᵢ^i` of a squarefree factorization
decomposes `A/D` for the per-factor Hermite loop. The library's `ratFunc_partialFraction_prod`. -/
abbrev ratFunc_partialFraction_prod :=
  @DeepWiki.SymbolicIntegration.ratFunc_partialFraction_prod

/-- **Hermite reduction of a full partial-fraction sum** (§2.2, the outer reduction): for squarefree
factors `Dᵢ` with multiplicities `eᵢ ≥ 1` (char 0), `∑ᵢ Aᵢ/Dᵢ^{eᵢ} = (∑ᵢ gᵢ)′ + ∑ᵢ rᵢ/Dᵢ` with
`(gᵢ, rᵢ) = hermiteReducePower Dᵢ eᵢ Aᵢ` — the rational part collected, the remaining integrand
squarefree-denominatored. Composed with `ratFunc_partialFraction_prod` this is the full HermiteReduce.
The library's `hermiteReduce_sum_spec`. -/
abbrev hermiteReduce_sum_spec := @DeepWiki.SymbolicIntegration.hermiteReduce_sum_spec

/-- **Hermite reduction — complete outer algorithm** (§2.2, p.39, Algorithm `HermiteReduce`): for a
proper fraction `A/D` with squarefree factorization `D = ∏ᵢ Dᵢ^{eᵢ}` (`Dᵢ` squarefree, pairwise coprime,
`eᵢ ≥ 1`, char 0), there exist a rational part `g` and numerators `rᵢ` with `A/D = g′ + ∑ᵢ rᵢ/Dᵢ`, i.e.
`∫ A/D = g + ∫ ∑ᵢ rᵢ/Dᵢ` with the remaining integrand squarefree-denominatored. Composes the multi-factor
partial fraction with the per-prime-power reduction. The library's `hermiteReduce_full`. -/
abbrev hermiteReduce_full := @DeepWiki.SymbolicIntegration.hermiteReduce_full

open Polynomial in
/-- **Example 2.4.1** (§2.4, p.48), the Rothstein–Trager residue computation for
`f = (x⁴−3x²+6)/(x⁶−5x⁴+5x²+4)`: `D = x⁶−5x⁴+5x²+4` is squarefree, `D' = 6x⁵−20x³+10x`, and for an
algebraic constant `a` with `4a²+1 = 0` the residue gcd is `Gₐ = gcd(D, A−aD') = x³+2ax²−3x−4a`.
Faithful core: `Gₐ` divides both `D` and `A−aD'` — exhibited by the exact cofactorizations
`D = Gₐ·(x³−2ax²−3x+4a)` and `A−aD' = Gₐ·(−6ax²−2x+6a)` (both modulo `4a²+1 = 0`). By `thm_2_4_1_ii`
this makes every root of `Gₐ` a root of `D` with residue `a`. -/
abbrev ex_2_4_1 := @DeepWiki.SymbolicIntegration.rothsteinTrager_gcd_example

/-- **Examples 2.2.1 / 2.3.1** (§2.2–2.3, p.41,46), the Hermite / Horowitz–Ostrogradsky *result*: in a
differential field with `t′ = 1` (the integration variable, `t ≠ 0`, `t²+2 ≠ 0`),
`∫ (t⁷−24t⁴−4t²+8t−8)/(t⁸+6t⁶+12t⁴+8t²) dt = (3t³+8t²+6t+4)/(t⁵+4t³+4t) + ∫ dt/t`, i.e. the rational part
is `(3t³+8t²+6t+4)/(t⁵+4t³+4t)` and the remaining integrand reduces to `1/t` (`logDeriv t`). Verified as
the differential-field identity `((3t³+8t²+6t+4)/(t⁵+4t³+4t))′ + t⁻¹ = the integrand` (`deriv_div` +
cross-multiplied `ring`). Both denominators factor as `t·(t²+2)²` and `t²·(t²+2)³`. -/
abbrev ex_2_3_1 := @DeepWiki.SymbolicIntegration.hermiteReduce_octic_example

/-- **Example 2.2.1** (§2.2, p.40), the *original* `HermiteReduce` trace on
`(x⁷−24x⁴−4x²+8x−8)/(x⁸+6x⁶+12x⁴+8x²)`: after the partial fraction `(x−1)/x² + (x⁴−6x³−18x²−12x+8)/(x²+2)³`,
the three steps `(i,j)=(2,1),(3,2),(3,1)` each verify `V'·B + V·C = −Aᵢ/j` and the update `Aᵢ ← −jC − B'`
(table values from the book). The library's `hermiteBasic_trace_octic`. -/
abbrev ex_2_2_1 := @DeepWiki.SymbolicIntegration.hermiteBasic_trace_octic

/-- **Example 2.2.2** (§2.2, p.42), the *quadratic* Hermite reduction trace on the same integrand: the
three steps `(i,j)=(2,1),(3,2),(3,1)` (with `U₂=(x²+2)³`, `U₃=x`) each verify `U·V'·B + V·C = −A/j` and
the update `A ← −jC − U·B'`, reducing `A₀ → A₁ → A₂ → A₃ = x²+2` (no partial fraction needed). The
library's `hermiteQuadratic_trace_octic`. -/
abbrev ex_2_2_2 := @DeepWiki.SymbolicIntegration.hermiteQuadratic_trace_octic

/-- **Example 2.2.3** (§2.2, p.44), *Mack's linear* Hermite reduction trace on the same integrand:
`D⁻ = gcd(D,D') = x⁵+4x³+4x`, `D* = x³+2x`, two reduction steps each verifying `(−D*·D⁻'/D⁻)·B + D⁻*·C = A`
and `A ← C − B'·D*/D⁻*` (book `(B,C) = (8x²+4, x⁴−2x²+16x+4)` then `(3, x²+2)`), `A` reduced to `x²+2` with
`A/D* = 1/x`. The library's `hermiteMack_trace_octic`. -/
abbrev ex_2_2_3 := @DeepWiki.SymbolicIntegration.hermiteMack_trace_octic

/-- **Exercise 2.1** (§2.2, p.72), Hermite reduction of `(t⁵−t⁴+4t³+t²−t+5)/(t⁴−2t³+5t²−4t+4)`: the
denominator is `(t²−t+2)²`, so the rational part is `(7t⁴+7t³+20t+18)/(14(t²−t+2))` and the remaining
(logarithmic) integrand is `(7t+3)/(7(t²−t+2))` — verified as the differential-field identity
`(rational part)′ + (7t+3)/(7(t²−t+2)) = integrand`. The library's `hermiteReduce_quartic_example`. -/
abbrev ex_2_1 := @DeepWiki.SymbolicIntegration.hermiteReduce_quartic_example

/-! ## §2.5 The Lazard–Rioboo–Trager Algorithm -/

/-- **LRT subresultant primitive** (§2.5, p.51): the functional def `lrtSubresultant A D j` = the `j`-th
subresultant `Sⱼ(D, A − t·D')` w.r.t. `x` over `K[t]` — the one PRS whose remainders replace the
Rothstein–Trager per-residue gcds. The library's `lrtSubresultant`. -/
noncomputable abbrev lazardRiobooTrager_subresultant := @DeepWiki.SymbolicIntegration.lrtSubresultant

/-- **Specialization of the LRT subresultant** (§2.5): mapping `t ↦ a` recovers `Sⱼ(D, A − a·D')` over `K`
(`lrtSubresultant_eval`, the subresultant analog of `rtResultant_eval`). By Theorem 2.5.1 this is `gcd(D,
A−aD')` up to leading coefficient. -/
abbrev lazardRiobooTrager_subresultant_eval :=
  @DeepWiki.SymbolicIntegration.lrtSubresultant_eval

/-- **Lazard–Rioboo–Trager algorithm** `IntRationalLogPart` (§2.5, p.51): the functional log-part
computation returning the `(Qᵢ, Sᵢ)` pairs meaning `∫ A/D = ∑ᵢ ∑_{a:Qᵢ(a)=0} a·log(Sᵢ(a,x))` — `Qᵢ` the
squarefree-factorization parts of the resultant `R`, `Sᵢ = D` if `i = deg D` else the `i`-th subresultant.
The library's `lazardRiobooTrager` (the book's optional `lcₓ`-normalization omitted). -/
noncomputable abbrev lazardRiobooTrager_algorithm := @DeepWiki.SymbolicIntegration.lazardRiobooTrager

/-- **Theorem 2.5.1, part (i)** (§2.5, p.50, the `n = deg(C)` case): when the residue `α` has multiplicity
`n = deg(C)`, `gcd(C, A−αB) = C` (up to the gcd's unit ambiguity, i.e. *similar* to `C`). The library's
`isSimilar_gcd_left_of_natDegree_eq`: a degree-`deg C` divisor of `C` is similar to `C`. The general
divisor form is `isSimilar_of_dvd_of_natDegree_eq`. -/
abbrev thm_2_5_1_i := @DeepWiki.SymbolicIntegration.isSimilar_gcd_left_of_natDegree_eq

/-- **Theorem 2.5.1, part (ii)** (§2.5, p.50, the `n < deg(D)` case — *every* residue): for `D ≠ 0` and
`deg A < deg D`, the LRT subresultant `lrtSubresultant A D` at index `i = deg R_k` (`R_k` the last nonzero
element of the Euclidean p.r.s. of `D, A − a·D'`), specialized `t ↦ a`, is similar to `gcd(D, A − a·D')` —
the book's `ppₓ(R_m)(a,x) ~ gcd(D, A−aD')` (over a field `ppₓ(R_m) ~ R_m`). The library's
`isSimilar_lrtSubresultant_eval_gcd`: combines `lrtSubresultant_eval` with the concrete subresultant ↔ gcd
connection `subresultant_euclideanPRS_isSimilar_gcd`, the formal degree `deg D − 1` matched to the actual
`deg(A − a·D')` by `isSimilar_subresultant_padding` — so it holds even for the degenerate residue where
`deg(A − a·D') < deg D − 1`. -/
abbrev thm_2_5_1_ii := @DeepWiki.SymbolicIntegration.isSimilar_lrtSubresultant_eval_gcd

/-- **Theorem 2.5.1, part (ii) — the top-index `k = 1` case** (§2.5, p.50, `E := A − a·D' ∣ D`): the
Euclidean p.r.s. of `D, E` terminates in one step (`R₂ = prem(D, E) = 0`), so `R₁ = E` is the last
nonzero element and `i = deg E` is the *top* p.r.s. index — the boundary the degree-padding lemma's
`j < k` cannot reach. The library's `isSimilar_lrtSubresultant_eval_gcd_top`: the specialized LRT
subresultant `subresultant D E (deg D) (deg D−1) (deg E)` collapses by the normal-orientation degenerate
formula `subresultant_deg_ge_normal` (first poly `D` of the larger formal degree) to `C(...)·E ~ E`, then
`gcd D E ~ E` (`isSimilar_gcd_right_of_euclideanPRS_two_eq_zero`) chains to `~ gcd(D, A−a·D')`. -/
abbrev thm_2_5_1_ii_top := @DeepWiki.SymbolicIntegration.isSimilar_lrtSubresultant_eval_gcd_top

/-- **Theorem 2.5.1, residue degree dividing line** (§2.5, p.50): `A − a·D'` keeps the full degree
`deg D − 1` except at the single residue value `a = A_{n−1}/(n·lc D)` (`n = deg D`), where the `xⁿ⁻¹`
coefficient cancels — proven under the explicit non-cancellation `A_{n−1} ≠ a·(n·lc D)`. (`thm_2_5_1_ii`
no longer needs this — it handles the degenerate value uniformly via padding — but this records the
boundary.) The library's `natDegree_sub_C_mul_derivative`. -/
abbrev thm_2_5_1_nondegeneracy := @DeepWiki.SymbolicIntegration.natDegree_sub_C_mul_derivative

/-- **Theorem 2.5.1, the multiplicity identification `deg_x R_m = i`** (§2.5, p.50): over an algebraically
closed field, for separable `D` and `deg A < deg D`, the multiplicity of a residue `a` as a root of the
Rothstein–Trager resultant `R(t) = res_x(D, A − t·D')` equals the degree of the Rothstein–Trager gcd:
`rootMultiplicity a R = deg gcd(D, A − a·D')`. The library's `rootMultiplicity_rtResultant_eq_natDegree_gcd`,
combining `roots_rtResultant` (`R.roots = D.roots.map (A(α)/D'(α))`, the residues) with
`natDegree_gcd_eq_count_residue` (`deg gcd = #{α : residue α = a}`). This is the count `i` the LRT algorithm
takes as its subresultant index, supplying the `deg_x R_m = i` half of part (ii). -/
abbrev thm_2_5_1_multiplicity :=
  @DeepWiki.SymbolicIntegration.rootMultiplicity_rtResultant_eq_natDegree_gcd

/-- **Theorem 2.5.1, algorithm-level capstone** (§2.5, p.50, part (ii) at the algorithm's own index —
the full part-(ii) regime): state correctness directly at the LRT subresultant index
`i = rootMultiplicity a R` (`R = rtResultant A D`), with the p.r.s.-termination data discharged
internally — over an algebraically closed field, `D` separable, `deg A < deg D`, for a residue `a` with
`i < deg D` (`gcd(D, A − a·D')` a *proper* factor of `D`), the LRT subresultant at index `i` specialized
`t ↦ a` is similar to `gcd(D, A − a·D')`. The library's `lazardRiobooTrager_isSimilar_gcd`: assembles
`thm_2_5_1_ii`/`thm_2_5_1_ii_top` with `thm_2_5_1_multiplicity` (`i = deg gcd`) and `IsSimilar.natDegree_eq`
(`deg gcd = deg R_k`), discharging `hk0`/`hknz` via `exists_last_euclideanPRS_nonzero`. Splitting on the
p.r.s. length: `k ≥ 2` uses `thm_2_5_1_ii`, `k = 1` uses `thm_2_5_1_ii_top`; only `A − a·D' = 0` (the
part-(i) `i = deg D` regime, `gcd ~ D`) is excluded by `i < deg D`. -/
abbrev thm_2_5_1 := @DeepWiki.SymbolicIntegration.lazardRiobooTrager_isSimilar_gcd

/-- **Theorem 2.5.1, unified algorithm output** (§2.5, p.50, parts (i)+(ii) combined, NO excluded case):
for any `a`, the LRT algorithm's output curve `Sᵢ` at multiplicity `i = rootMultiplicity a R` — `D` if
`i = deg D` (part (i), `A − a·D' = 0`) else `lrtSubresultant A D i` (part (ii)) — specialized `t ↦ a`, is
similar to `gcd(D, A − a·D')`. The `if i = deg D` is exactly `lazardRiobooTrager`'s own branch, so this
covers EVERY residue. The library's `lazardRiobooTrager_output_isSimilar_gcd` (routes `i = deg D` to
`thm_2_5_1_i`, `i < deg D` to `thm_2_5_1`). -/
abbrev thm_2_5_1_output := @DeepWiki.SymbolicIntegration.lazardRiobooTrager_output_isSimilar_gcd

/-- **Roots of the Rothstein–Trager resultant** (§2.5, behind Thm 2.5.1): over an algebraically closed
field, for separable `D` and `deg A < deg D`, the roots of `R(t)` (with multiplicity) are exactly the
residues `A(α)/D'(α)` over the roots `α` of `D` — `R.roots = D.roots.map (A(α)/D'(α))`. The library's
`roots_rtResultant`, the un-evaluated root-product form `rtResultant_eq_prod_roots` factored per root by
`linearFactor_eq_residue`. -/
abbrev intRationalLogPart_resultant_roots := @DeepWiki.SymbolicIntegration.roots_rtResultant

open Polynomial in
/-- **Example 2.5.1** (§2.5, p.52), Lazard–Rioboo–Trager on the same integrand as Ex 2.4.1: the
subresultant PRS of `D = x⁶−5x⁴+5x²+4` and `A−tD'` has a degree-3 element `R₃ = S₃`, and at a root
`a` of `Q₃` (`4a²+1 = 0`) the book computes `S₃(a,x) = −214ax³+107x²+642ax−214`. Faithful punchline
(`ex_2_5_1`): this value is exactly `−214a·(x³+2ax²−3x−4a)`, i.e. `−214a` times the Rothstein–Trager
gcd `Gₐ` of Ex 2.4.1 — so the LRT subresultant and the RT gcd agree up to the scalar `−214a`, and
monic-normalizing `S₃(a,x)` recovers `Gₐ`. Verified as the algebraic identity modulo `4a²+1 = 0`
(`linear_combination … * hb`); this checks the normalization step, not the PRS computation itself. -/
abbrev ex_2_5_1 := @DeepWiki.SymbolicIntegration.lazardRiobooTrager_example

/-- **Example 2.5.2** (§2.5, p.53), the Hermite-reduction result for `f = 36/(x⁵−2x⁴−2x³+4x²+x−2)`
(denominator `(x²−1)²(x−2)`): `HermiteReduce` returns rational part `g = (12x+6)/(x²−1)` and remaining
integrand `h = 12/(x²−x−2)`, so `∫ f = (12x+6)/(x²−1) + ∫ 12/(x²−x−2)`. Verified as the differential-field
identity `((12x+6)/(x²−1))′ + 12/(x²−x−2) = 36/(x⁵−2x⁴−2x³+4x²+x−2)` (the numerator sum collapses to
`36(x+1)`). The logarithmic part `∫ 12/(x²−x−2) = Σ_{α²=16} α·log(x − 1/2 − 3α/8)` is the §2.4/§2.5
log-part computation (cf. `ex_2_4_1`). -/
abbrev ex_2_5_2 := @DeepWiki.SymbolicIntegration.hermiteReduce_quintic_example

/-- **`IntegrateRationalFunction`, the `∫ Q dx` polynomial part** (§2.5, p.52): the polynomial
antiderivative `polyIntegral Q = ∑ₙ (aₙ/(n+1))·xⁿ⁺¹` (`Q = ∑ aₙ xⁿ`) — missing from Mathlib — with
correctness `derivative (polyIntegral Q) = Q` (char `0`). The library's `polyIntegral_derivative`. -/
abbrev integrateRationalFunction_polyIntegral := @DeepWiki.SymbolicIntegration.polyIntegral_derivative

/-- **`IntegrateRationalFunction`, the `PolyDivide` split** (§2.5, p.52): for `Den ≠ 0`,
`A/Den = (A / Den) + (A % Den)/Den` in `K(x)` — the improper fraction splits into polynomial quotient
plus proper remainder (Euclidean `div_add_mod`). The library's `ratFunc_polyDivide_split`. -/
abbrev integrateRationalFunction_polyDivide := @DeepWiki.SymbolicIntegration.ratFunc_polyDivide_split

/-- **`IntegrateRationalFunction` reduction** (§2.5, p.52): for `A` over a squarefree-factored denominator
`Den = ∏ᵢ Dᵢ^{eᵢ}` (char `0`), `A/Den = g′ + (polyIntegral p)′ + ∑ᵢ rᵢ/Dᵢ` — i.e.
`∫ A/Den = g + ∫ p dx + ∫ ∑ᵢ rᵢ/Dᵢ`, the integral reduced to a rational part, a polynomial-integral part,
and a squarefree-denominator residual (the `IntRationalLogPart` input). Assembles `HermiteReduce`
(`hermiteReduce_full`), `PolyDivide` (`integrateRationalFunction_polyDivide`), and `polyIntegral`. The
final `∑ᵢ rᵢ/Dᵢ → ∑ logs` step remains. The library's `integrateRationalFunction_reduction`. -/
abbrev integrateRationalFunction_reduction :=
  @DeepWiki.SymbolicIntegration.integrateRationalFunction_reduction

/-- **Degree-reduced Diophantine solver** (§2.2, the Hermite Bézout variant): `diophantineSolveReduced
a b c` reduces the first cofactor of `diophantineSolve` modulo `b`, so it still solves `a·B + b·C = c`
(`diophantineSolveReduced_spec`) but now with `deg B < deg b` (`diophantineSolveReduced_fst_degree_lt`)
— the proper Bézout cofactor the book's `deg B < deg V` requires. The library's
`diophantineSolveReduced`. -/
noncomputable abbrev diophantineSolveReduced := @DeepWiki.SymbolicIntegration.diophantineSolveReduced

/-- **Hermite reduction keeps remainders proper** (§2.2, p.39): for squarefree `V` of positive degree
(char `0`), a proper integrand `A/Vᵏ` (`deg A < k·deg V`) reduces to a remainder with `deg < deg V` —
`deg (hermiteReducePower V k A).2 < deg V`. The degree invariant `deg A < k·deg V` is preserved by each
reduction step and bottoms out at `k = 1`. This is the properness the book asserts of `HermiteReduce`'s
output. The library's `hermiteReducePower_remainder_degree`. -/
abbrev hermiteReducePower_remainder_degree :=
  @DeepWiki.SymbolicIntegration.hermiteReducePower_remainder_degree

/-- **`IntegrateRationalFunction` reduction with proper remainders** (§2.5, p.52): the strengthened
reduction that also exposes the Hermite properness `deg rᵢ < deg Dᵢ`. For `A` over a *monic*
squarefree-factored denominator `Den = ∏ᵢ Dᵢ^{eᵢ}` (`Dᵢ` monic squarefree of positive degree, pairwise
coprime, `eᵢ ≥ 1`, char `0`), `A/Den = g′ + (polyIntegral p)′ + ∑ᵢ rᵢ/Dᵢ` with every `rᵢ` proper.
Built on Mathlib's degree-bounded partial fraction `div_prod_eq_quo_add_sum_rem_div` plus
`hermiteReducePower_remainder_degree`. The library's `integrateRationalFunction_reduction_proper`. -/
abbrev integrateRationalFunction_reduction_proper :=
  @DeepWiki.SymbolicIntegration.integrateRationalFunction_reduction_proper

/-- **`IntegrateRationalFunction` closed log-form, single squarefree denominator** (§2.5, p.52,
eq 2.4 — the `e = 1`, no-rational-part case): for a proper fraction `R/V` over a split squarefree
`V = ∏_{α∈s}(X−α)` with `deg R < #s`, `R/V = ∑_a a·logDeriv(Gₐ)`, `Gₐ = ∏_{α∈s, res(α)=a}(X−α)` — i.e.
`∫ R/V = ∑_a a·log(Gₐ)`, the §2.4/§2.5 logarithmic part with no rational/polynomial part. The library's
`ratFunc_logForm_split_squarefree`. -/
abbrev integrateRationalFunction_logForm_squarefree :=
  @DeepWiki.SymbolicIntegration.ratFunc_logForm_split_squarefree

/-- **`IntegrateRationalFunction` closed log-form** (§2.5, p.52, eq 2.4 — the culmination): for `A`
over a denominator with split squarefree factors `Dᵢ = ∏_{α∈sset i}(X−α)` (nonempty disjoint root-sets,
`eᵢ ≥ 1`, char `0`), there are a rational part `g`, a polynomial-integral part `p`, and remainders `rᵢ`
with `A/∏ᵢ Dᵢ^{eᵢ} = g′ + (polyIntegral p)′ + ∑ᵢ ∑_a a·logDeriv(Gᵢₐ)` —
`∫ A/D = g + ∫ p dx + ∑ᵢ ∑_a a·log(Gᵢₐ)`. *Unconditional*: the Hermite-remainder properness
`deg rᵢ < #sset i` is discharged internally via `integrateRationalFunction_reduction_proper`. Assembles
the §2.5 reduction with the Rothstein–Trager residue-grouped log sum. The library's
`integrateRationalFunction_logForm`. -/
abbrev integrateRationalFunction_logForm :=
  @DeepWiki.SymbolicIntegration.integrateRationalFunction_logForm

/-! ## §2.8 Rioboo's Algorithm for Real Rational Functions -/

/-- **Lemma 2.8.1** (§2.8, p.60), rewriting a complex logarithm as a real arctangent: for `u` with
`u² ≠ −1`, `√−1 · d/dx log((u+√−1)/(u−√−1)) = 2 · d/dx arctan(u)` (eq 2.17). As a differential-field
identity (with `i = √−1`, `i² = −1`, and `arctan'(u) = u'/(1+u²)`): `i · logDeriv((u+i)/(u−i)) =
2·u'/(1+u²)`. The logarithmic derivative `logDeriv((u+i)/(u−i)) = u'/(u+i) − u'/(u−i) = −2i·u'/(u²+1)`
(using `(u±i)' = u'`, `i` constant), and `i·(−2i) = −2i² = 2`. -/
abbrev lemma_2_8_1 := @DeepWiki.SymbolicIntegration.logDeriv_imagQuot_eq_arctanDeriv

/-! ## §2.6 The Czichowski Algorithm -/

open Polynomial in
/-- **Example 2.6.1** (§2.6, p.54), the Czichowski algorithm on the same integrand as Ex 2.4.1: the
reduced Gröbner basis of `(D, A − t·D')` w.r.t. pure lex `x > t` is `{4t²+1, x³+2tx²−3x−4t}`, so
`Q₁ = 4t²+1` and `S₁ = x³+2tx²−3x−4t`, yielding `∫ (x⁴−3x²+6)/(x⁶−5x⁴+5x²+4) = Σ_{4a²+1=0} a·log(x³+2ax²−3x−4a)`
— *the same integral as Example 2.4.1*. Faithful core: the Czichowski log argument `S₁(a,x) = x³+2ax²−3x−4a`
coincides with the Rothstein–Trager `Gₐ` and so divides both `D` and `A−aD'` (modulo `4a²+1 = 0`) — exactly
`ex_2_4_1`. -/
abbrev ex_2_6_1 := @DeepWiki.SymbolicIntegration.rothsteinTrager_gcd_example

/-- **Theorem 2.6.1, the integral connection** (§2.6, p.54), Czichowski's algorithm reuses the
Rothstein–Trager logarithmic part: his Gröbner-basis logarithm argument `S(x,c) = gcd(D, A − c·D')`
(Czichowski's Lemma 2.3) coincides with the RT/LRT gcd, so `∫ A/D = ∑_a a·log(gcd(D, A − a·D'))` is the
*same* integral as §2.4/§2.5. The library's `ratFunc_eq_sum_residue_gcd` (proved via
`gcd_nodal_eq_prod_residue` = Lemma 2.3); the Gröbner-basis structure remains [infra]. Double-referenced
to the source paper as `DeepWiki.Czi.integral_logForm_gcd`. -/
abbrev thm_2_6_1_integral_connection := @DeepWiki.SymbolicIntegration.ratFunc_eq_sum_residue_gcd

/-- **Cox–Little–O'Shea §2.6, Lemma 5 (the cancellation lemma)** — the self-contained crux of the
converse Buchberger criterion. Over a field, if `p₀,…,pₙ` are nonzero with one common leading
monomial `δ` and their leading terms cancel (`m.degree (∑ pᵢ) ≺[m] δ`), then `∑ᵢ dᵢ = 0`
(`dᵢ = m.leadingCoeff pᵢ`) and `∑ᵢ pᵢ = ∑_{i≠last} dᵢ·S(pᵢ, p_last)` is a combination of
S-polynomials each of strictly smaller degree `≺[m] δ`. The library's
`cancellation_lemma` (with the collapse `sPolynomial_eq_of_degree_eq` and degree bound
`sPolynomial_degree_lt_of_degree_eq`). The self-contained heart of CLO Theorem 6. -/
abbrev clo_lemma_5_cancellation := @DeepWiki.SymbolicIntegration.cancellation_lemma

/-- **Cox–Little–O'Shea §2.6, Theorem 6 (Buchberger's criterion, converse half)** — a generating
set `B` of `I` with unit leading coefficients, all of whose S-polynomials reduce to `0` modulo `B`
(each `S(b,b')` has a standard representation `∑ q c · c` over `B` with summand degrees
`≼[m] m.degree (S(b,b'))`), is a Gröbner basis of `I`. The library's
`isGroebnerBasis_of_sPolynomial_reducesToZero`, via the minimal-representation argument
(`exists_leadingMonomial_le`: minimize the representation's largest-summand degree; the strict case
cancels the top part into S-polynomials by `cancellation_lemma`/Mathlib `sPolynomial_decomposition`
and reduces each by hypothesis to a strictly smaller representation). -/
abbrev clo_thm_6_buchberger_converse :=
  @DeepWiki.SymbolicIntegration.isGroebnerBasis_of_sPolynomial_reducesToZero

/-- **Buchberger's algorithm — one completion step** (§2.6, the S-polynomial completion loop):
`buchbergerStep m hB` adjoins to `B` the nonzero division remainders (`MonomialOrder.div_set`,
via `remainder`) of all S-polynomials `S(b,b')`, `b,b' ∈ B`. It preserves the ideal
(`span_buchbergerStep`: the new elements are remainders of ideal members) and enlarges the basis
(`subset_buchbergerStep`). The library's `buchbergerStep`. -/
noncomputable abbrev buchberger_step := @DeepWiki.SymbolicIntegration.buchbergerStep

/-- **Buchberger's algorithm — termination + correctness** (§2.6, Buchberger's theorem): over a
field with finitely many variables, iterating `buchbergerStep` from any finite `B` (unit leading
coefficients) reaches a Gröbner basis `G ⊇ B` of `⟨B⟩` with `⟨G⟩ = ⟨B⟩`. Termination is the
Noetherian ascending-chain condition (`WellFoundedGT` on the leading-term ideals `leadTermIdeal`):
each step either fixes `B` — then `B` is a Gröbner basis by `clo_thm_6_buchberger_converse`
(`isGroebnerBasis_of_buchbergerStep_eq`) — or strictly grows `leadTermIdeal`
(`leadTermIdeal_lt_of_ne`), which cannot recur. The library's `buchberger_terminates_correct`. -/
abbrev buchberger_terminates_correct :=
  @DeepWiki.SymbolicIntegration.buchberger_terminates_correct

/-- **Lazard (1985), Lemma 1** (cited in §2.6; J. Symb. Comp. 1, 261–270): in a reduced (minimal)
Gröbner basis of a two-variable ideal `I ⊆ K[x,y]`, distinct elements have *distinct* leading
y-degrees `(m.degree b) 1` — the foundational step of Lazard's bivariate GB structure theorem and
the first stepping stone toward Czichowski's structural lemmas. The library's `lazard_lemma1`
(order sublemma `finsupp_fin_two_le_or_le_of_apply_eq` + minimality extraction
`IsReducedGroebnerBasis.leadingMonomial_not_le`), with injectivity form `lazard_lemma1_injOn`. -/
abbrev lazard_lemma1 := @DeepWiki.SymbolicIntegration.lazard_lemma1

/-- **The `MvPolynomial (Fin 2) K ↔ K[x][y]` representation bridge** (cited in §2.6; Lazard 1985,
the framework step of his bivariate GB structure theory). With the convention `y = variable 0`
(matching `MvPolynomial.finSuccEquiv`, which pulls out variable `0` as the `Polynomial` variable),
`lazardView f = finSuccEquiv K 1 f` is the `K[x][y]` view and `leadingYCoeff f` is Lazard's
leading-y-coefficient `Rₖ ∈ MvPolynomial (Fin 1) K ≃ K[x]`. The y-degree bridge `natDegree_lazardView`
(`(lazardView f).natDegree = degreeOf 0 f`, Mathlib's `natDegree_finSuccEquiv`) plus the dominance
lemma `lex_degree_apply_zero` (lex makes index `0 = y` dominant: `(MonomialOrder.lex.degree f) 0 =
degreeOf 0 f`) give the degree correspondence `degree_apply_zero_eq_natDegree_lazardView`. Satellite
API: `leadingYCoeff_ne_zero`/`leadingYCoeff_eq_zero` and multiplicativity `leadingYCoeff_mul`
(`MvPolynomial (Fin 1) K` is a domain). The library's `leadingYCoeff`. -/
noncomputable abbrev lazard_leadingYCoeff := @DeepWiki.SymbolicIntegration.leadingYCoeff

/-- **The y-degree correspondence of the `K[x][y]` bridge** (cited in §2.6; Lazard 1985): under a
monomial order `m` making `y = variable 0` dominant (`hdom`, satisfied by `MonomialOrder.lex`), the
index-`0` component of the leading monomial `m.degree f` equals the `K[x][y]` view's `natDegree`,
`(m.degree f) 0 = (lazardView f).natDegree`. The library's
`degree_apply_zero_eq_natDegree_lazardView`. -/
abbrev lazard_degree_bridge := @DeepWiki.SymbolicIntegration.degree_apply_zero_eq_natDegree_lazardView

/-- **Toward Lazard (1985), Lemma 2** (cited in §2.6): the `y`-shift toolbox aligning the two ideal
members of Lemma 2's `R_{i+1} ∣ Rᵢ` proof. Multiplying by `y^k = X 0 ^ k` adds `k` to the `y`-degree
(`degreeOf_X_pow_mul`: `degreeOf 0 (X 0 ^ k * f) = degreeOf 0 f + k`) and fixes the leading-`y`-coefficient
(`leadingYCoeff_X_pow_mul`: `leadingYCoeff (X 0 ^ k * f) = leadingYCoeff f`), so the shifted `y^{d_{i+1}−dᵢ}·fᵢ`
matches the `y`-degree `d_{i+1}` of `f_{i+1}` while keeping `Rᵢ`. The library's `leadingYCoeff_yShift_eq`. -/
noncomputable abbrev lazard_lemma2_yShift := @DeepWiki.SymbolicIntegration.leadingYCoeff_yShift_eq

/-- **Lazard (1985), Lemma 2** (cited in §2.6; J. Symb. Comp. 1, 261–270, p.263): the
leading-`y`-coefficient (in `K[x]`) of the highest power of `y` in `f_{i+1}` divides that in `fᵢ`,
along a reduced bivariate Gröbner basis ordered by increasing `y`-degree. The library's
`lazard_lemma2`, via the transferred GCD/Bézout structure on `MvPolynomial (Fin 1) K`
(`gcdMonoidMvPolynomialFinOne`, `exists_mul_add_mul_eq_gcd`), the gcd construction
`lazard_gcd_construction` (`P ∈ I` of `y`-degree `d_{i+1}` with `leadingYCoeff P = gcd(Rᵢ,R_{i+1})`),
and the `x`-degree bridge `lex_degree_apply_one` driving the minimality contradiction. -/
abbrev lazard_lemma2 := @DeepWiki.SymbolicIntegration.lazard_lemma2

/-! ## §2.7 Newton–Leibniz–Bernoulli Revisited -/

/-- **Example 2.7.2** (§2.7, p.58), `FullPartialFraction` of `f = 36/(x⁵−2x⁴−2x³+4x²+x−2)`
(denominator `(x−1)²(x+1)²(x−2)`): the full partial-fraction decomposition (eq 2.13) is
`36/D = (Σ_{α²−1=0} (−3α−6)/(x−α)²) − 4/(x+1) + 4/(x−2)`. Here `α²−1=0` gives `α = ±1` (rational), so the
sum is `−9/(x−1)² − 3/(x+1)²`, and the decomposition is the field identity below. -/
abbrev ex_2_7_2 := @DeepWiki.SymbolicIntegration.fullPartialFraction_example

/-- **Example 2.7.3** (§2.7, p.59), `IntegrateRationalFunction` (full-partial-fraction form) of
`f = 36/(x⁵−2x⁴−2x³+4x²+x−2)`: from the decomposition (eq 2.13), `∫ f = 4·log(x−2) − 4·log(x+1) +
Σ_{α²−1=0} (3α+6)/(x−α)`, i.e. rational part `9/(x−1) + 3/(x+1)` plus logs `4·log(x−2) − 4·log(x+1)`.
Verified as the differential-field identity `(9/(x−1) + 3/(x+1))′ + (4/(x−2) − 4/(x+1)) = f` (the bracket
is the log part's integrand `4·logDeriv(x−2) − 4·logDeriv(x+1)`). -/
abbrev ex_2_7_3 := @DeepWiki.SymbolicIntegration.integrateRational_example

end DeepWiki.Si
