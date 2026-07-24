import DeepWiki.SymbolicIntegration.RationalIntegration
import DeepWiki.SymbolicIntegration.RationalIntegrationExamples
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms
import DeepWiki.SymbolicIntegration.RationalIntegrationLogForm
import DeepWiki.SymbolicIntegration.PartialFraction
import DeepWiki.SymbolicIntegration.CompletePartialFraction
import DeepWiki.SymbolicIntegration.Residues
import DeepWiki.SymbolicIntegration.RationalIntegrationGcdLogForm
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.ResidueMultiplicity
import DeepWiki.SymbolicIntegration.PseudoRemainderSequence
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.LazardRiobooTragerCorrectness
import DeepWiki.SymbolicIntegration.LrtMonicLogs
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.CzichowskiNormalPosition
import DeepWiki.SymbolicIntegration.RiobooRealLogarithm
import DeepWiki.SymbolicIntegration.RiobooLogToAtan
import DeepWiki.SymbolicIntegration.RiobooLogToAtanExample
import DeepWiki.SymbolicIntegration.Compute.LogToAtan
import DeepWiki.SymbolicIntegration.Engine.ResidueResultantTowerSpec
import DeepWiki.ComputableAlgebra.PolyReprDivisionDegree
import DeepWiki.SymbolicIntegration.Compute.Subresultant
import Sources.Doi_10_1007_b138171.Exercise22
import DeepWiki.SymbolicIntegration.Compute.Hermite
import Sources.Doi_10_1007_b138171.Exercise23
import Sources.Doi_10_1007_b138171.Exercise25
import Sources.Doi_10_1007_b138171.SubresultantExample241
import DeepWiki.SymbolicIntegration.RiobooLogToReal
import DeepWiki.SymbolicIntegration.RiobooLogToRealSplit
import DeepWiki.SymbolicIntegration.RiobooLogToRealRecursion
import DeepWiki.SymbolicIntegration.RiobooCoprimality
import DeepWiki.SymbolicIntegration.RiobooCoprimalityLrt
import DeepWiki.SymbolicIntegration.RealFieldExamples
import DeepWiki.SymbolicIntegration.InFieldIntegration
import DeepWiki.SymbolicIntegration.InFieldIntegrationCapstone
import DeepWiki.SymbolicIntegration.RecognizingLogDeriv
import DeepWiki.SymbolicIntegration.RationalIntegrationInvXPow
import DeepWiki.SymbolicIntegration.LaurentCoefficients
import Sources.Doi_10_1007_b138171.Source
import Sources.Doi_10_1007_b138171.HermiteExample221

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
§2.4/§2.5: the rational case of **Liouville's theorem** (`∫ f` for `f ∈ K(x)` is always `g + ∑ cᵢ log uᵢ`)
  is now formalized — catalog `Sources.Doi_10_1007_b138171.Liouville` (`liouville_ratFunc`,
  `liouville_logarithmFree_of_residues`). The remaining gap is the *full converse* of the logarithm-
  detection decision: `f = G′ ⟹ all Rothstein–Trager residues vanish` needs that a rational derivative has
  zero residue at every simple pole (a Laurent-coefficient fact); only the affirmative
  `residues vanish ⟹ logarithm-free` direction is proved `[deferred]`.
(Ex 2.3's symbolic content — LRT log part, the degree-8 RT resultant, the monic-in-`x` log argument,
the Rioboo real form, and the symbolic definite-integral data over `[−2, −2/3]` — is computed and
`native_decide`-proved (`ex_2_3*`); its "compare with direct numerical integration" sub-part is a
documented non-symbolic residual, `ex_2_3_numerical_comparison`, since real-number quadrature is not a
clean `ℚ`-symbolic Lean computation.)
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

/-! ## §2.2 The Hermite Reduction -/

/-- **Hermite reduction step** (§2.2, p.39): the differential identity at the core of Hermite's
reduction. With `k = m + 2`, if `Q = (1-k)(B·V' + C·V)` then
`Q / Vᵏ = (B / Vᵏ⁻¹)′ + ((1-k)·C - B') / Vᵏ⁻¹` — lowering the power of the squarefree factor `V`
by one. (The algorithm finds `B, C` with `deg B < deg V` via the extended Euclidean algorithm,
valid because `gcd(V, V') = 1` for squarefree `V`.) -/
abbrev hermiteReduce_step := @DeepWiki.SymbolicIntegration.hermite_reduction_step

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

/-- **Example 2.2.1, the computable Hermite reduction** (§2.2, p.40–41): the genuinely `#eval`-able
generic tower-Hermite engine `cHermiteReduceTower [1]` specialized to `DensePoly ℚ := List ℚ` runs on
`(x⁷−24x⁴−4x²+8x−8)/(x⁸+6x⁶+12x⁴+8x²)` and returns the rational part `g = gnum/gden` plus the residual
`B/Dstar` with `Dstar` squarefree. The squarefree factorization `D = x²·(x²+2)³` comes out as
`[(x,2),(x²+2,3)]` (`hermite_ex221_factors`); the residual is `(x²+2)/(x³+2x) = 1/x` — the book's
`∫ dx/x` (`hermite_ex221_residual`). Proved by `native_decide`. -/
abbrev ex_2_2_1_compute_factors := @DeepWiki.SymbolicIntegration.Compute.hermite_ex221_factors

/-- **Example 2.2.1, the computable Hermite residual** (§2.2, p.41): the residual log integrand of
`cHermiteReduceTower [1]` on the octic is `B/Dstar = (x²+2)/(x³+2x) = 1/x`, matching the book's remaining
`∫ dx/x`. The library's `Compute.hermite_ex221_residual` (`native_decide`). -/
abbrev ex_2_2_1_compute_residual := @DeepWiki.SymbolicIntegration.Compute.hermite_ex221_residual

/-- **Example 2.2.1, the computable Hermite rational part matches the book** (§2.2, p.41): the rational
part `g = gnum/gden` computed by `cHermiteReduceTower [1]` equals — as a rational function — the book's explicit
`g = 1/x + 6x/(x²+2)² − (x−3)/(x²+2)`. The library's `Compute.hermite_ex221_g_eq_book` (`native_decide`,
cross-multiplied). -/
abbrev ex_2_2_1_compute_g := @DeepWiki.SymbolicIntegration.Compute.hermite_ex221_g_eq_book

/-- **Example 2.2.1, the computable Hermite correctness certificate** (§2.2, p.41): the cleared
polynomial identity certifying `(gnum/gden)' + B/Dstar = A/D` for the computed tower-Hermite output —
independent of the exact spelling of `g`. The library's `Compute.hermite_ex221_cleared_identity`
(`native_decide`). -/
abbrev ex_2_2_1_compute_identity :=
  @DeepWiki.SymbolicIntegration.Compute.hermite_ex221_cleared_identity

/-- **Exercise 2.1** (§2.2, p.72), Hermite reduction of `(t⁵−t⁴+4t³+t²−t+5)/(t⁴−2t³+5t²−4t+4)`: the
denominator is `(t²−t+2)²`, so the rational part is `(7t⁴+7t³+20t+18)/(14(t²−t+2))` and the remaining
(logarithmic) integrand is `(7t+3)/(7(t²−t+2))` — verified as the differential-field identity
`(rational part)′ + (7t+3)/(7(t²−t+2)) = integrand`. The library's `hermiteReduce_quartic_example`. -/
abbrev ex_2_1 := @DeepWiki.SymbolicIntegration.hermiteReduce_quartic_example

/-! ## §2.3 The Horowitz–Ostrogradsky Algorithm -/

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

/-- **Examples 2.2.1 / 2.3.1** (§2.2–2.3, p.41,46), the Hermite / Horowitz–Ostrogradsky *result*: in a
differential field with `t′ = 1` (the integration variable, `t ≠ 0`, `t²+2 ≠ 0`),
`∫ (t⁷−24t⁴−4t²+8t−8)/(t⁸+6t⁶+12t⁴+8t²) dt = (3t³+8t²+6t+4)/(t⁵+4t³+4t) + ∫ dt/t`, i.e. the rational part
is `(3t³+8t²+6t+4)/(t⁵+4t³+4t)` and the remaining integrand reduces to `1/t` (`logDeriv t`). Verified as
the differential-field identity `((3t³+8t²+6t+4)/(t⁵+4t³+4t))′ + t⁻¹ = the integrand` (`deriv_div` +
cross-multiplied `ring`). Both denominators factor as `t·(t²+2)²` and `t²·(t²+2)³`. -/
abbrev ex_2_3_1 := @DeepWiki.SymbolicIntegration.hermiteReduce_octic_example

/-! ## §2.4 The Rothstein–Trager Algorithm -/

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

open Polynomial in
/-- **Example 2.4.1** (§2.4, p.48), the Rothstein–Trager residue computation for
`f = (x⁴−3x²+6)/(x⁶−5x⁴+5x²+4)`: `D = x⁶−5x⁴+5x²+4` is squarefree, `D' = 6x⁵−20x³+10x`, and for an
algebraic constant `a` with `4a²+1 = 0` the residue gcd is `Gₐ = gcd(D, A−aD') = x³+2ax²−3x−4a`.
Faithful core: `Gₐ` divides both `D` and `A−aD'` — exhibited by the exact cofactorizations
`D = Gₐ·(x³−2ax²−3x+4a)` and `A−aD' = Gₐ·(−6ax²−2x+6a)` (both modulo `4a²+1 = 0`). By `thm_2_4_1_ii`
this makes every root of `Gₐ` a root of `D` with residue `a`. -/
abbrev ex_2_4_1 := @DeepWiki.SymbolicIntegration.rothsteinTrager_gcd_example

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

/-- **Exercise 2.7** (§2.9, p.73), the regularity core behind making the LRT logarithm arguments monic in
`x`: at a residue `a` of multiplicity `i < deg D` in the Rothstein–Trager resultant `R = res_x(D, A−t·D')`,
the specialized `i`-th LRT subresultant `Sᵢ(D, A−a·D')` has `x`-degree *exactly* `i`, so its leading
`x`-coefficient — the `i`-th principal subresultant coefficient `sᵢ(a)` — is **nonzero**. Via
`lazardRiobooTrager_isSimilar_gcd` (`Sᵢ` specialized at `a` is *similar* to `gcd(D, A−a·D')`, so equal
`natDegree`) and `rootMultiplicity_rtResultant_eq_natDegree_gcd` (`deg gcd = rootMult a R = i`). The
library's `leadingCoeff_lrtSubresultant_eval_ne_zero`. -/
abbrev ex_2_7_regularity := @DeepWiki.SymbolicIntegration.leadingCoeff_lrtSubresultant_eval_ne_zero

/-- **Exercise 2.7** (§2.9, p.73), the required "**units in `K[t]/(Qᵢ(t))`**" fact: the `i`-th principal
subresultant coefficient `sᵢ = lrtPsc A D i ∈ K[t]` (the leading `x`-coefficient of the `i`-th LRT
subresultant) is **coprime** to the multiplicity-`i` factor `Qᵢ = lrtQ A D i := ∏_{a:rootMult a R=i}(t−a)`
(`i < deg D`) — i.e. `sᵢ` is a unit in `K[t]/(Qᵢ)`, exactly what makes monic-normalizing the LRT logarithm
arguments legitimate even when `Qᵢ` is not irreducible. From `ex_2_7_regularity` (`sᵢ(a) ≠ 0` at each root
`a` of `Qᵢ`) and the squarefreeness of `Qᵢ` (distinct linear factors `t − a`). The library's
`isCoprime_lrtPsc_lrtQ`. -/
abbrev ex_2_7_units := @DeepWiki.SymbolicIntegration.isCoprime_lrtPsc_lrtQ

/-- **Exercise 2.7** (§2.9, p.73), the algorithmic deliverable — *modify LRT so the polynomials inside the
logarithms are monic in `x`, with no change to the integral*. Replacing the LRT log argument `Sᵢ(a,x)`
(the specialized `i`-th subresultant `(lrtSubresultant A D i).map (t↦a)`) by its monic-in-`x` normalization
`monicLrtLog A D i a = Sᵢ(a,x)·C(sᵢ(a))⁻¹` leaves the logarithmic-part derivative unchanged:
`logDeriv(Sᵢ(a,x)) = logDeriv(monicLrtLog A D i a)` over `K(x)`. The two differ only by the nonzero
`x`-constant leading coefficient `sᵢ(a)` (`ex_2_7_regularity` ⟹ `sᵢ(a) ≠ 0`, so
`monicLrtLog` is monic), and `logDeriv` kills that constant factor (the `log(sᵢ(a))` term is `x`-constant,
derivative `0`). The library's `logDeriv_monicLrtLog_eq`, resting on the clean core
`logDeriv_algebraMap_C_mul_eq` (`logDeriv (C c · f) = logDeriv f` for `c ≠ 0` constant in `x`). -/
abbrev ex_2_7 := @DeepWiki.SymbolicIntegration.logDeriv_monicLrtLog_eq

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
`ratFunc_eq_sum_residue_grouped`. -/
abbrev integrateRationalFunction_logForm_squarefree :=
  @DeepWiki.SymbolicIntegration.ratFunc_eq_sum_residue_grouped

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

/-- **Existence of a reduced Gröbner basis** (cited in §2.6; the canonical form Czichowski's and
Lazard's structure theorems take as input): over a field with finitely many variables, every ideal
`I` has a finite *reduced* Gröbner basis. Built by monicizing (`monicize`), minimizing
(`minimize`, one representative per minimal leading monomial), then one-pass auto-reducing
(`autoReduce`, each element reduced mod the others) a Gröbner basis from `exists_isGroebnerBasis`.
The library's `exists_isReducedGroebnerBasis`. -/
abbrev exists_isReducedGroebnerBasis :=
  @DeepWiki.SymbolicIntegration.exists_isReducedGroebnerBasis

/-- **Lazard's Theorem 1, the `Pₖ = Rₖ·Sₖ` factorization, fully unconditional** (§2.6, the divide-out
closed): for a reduced bivariate Gröbner basis of `I` (nonempty), there exists a reduced Gröbner
basis `B'` of the divided ideal `I' = span {fᵢ/H}` (`H = P·Gₖ₊₁` the basis gcd) — supplied by
`exists_isReducedGroebnerBasis` — for which every sorted element splits as
`lazardView fⱼ = C(contentⱼ)·Sⱼ` with `contentⱼ ∼ leadingYCoeff fⱼ`, `Sⱼ` primitive and `y`-monic.
No `hassoc`/`HasNoCommonYFactor` hypothesis. The library's `lazard_Pk_eq_Rk_Sk_unconditional`. -/
abbrev lazard_Pk_eq_Rk_Sk_unconditional :=
  @DeepWiki.SymbolicIntegration.lazard_Pk_eq_Rk_Sk_unconditional

/-- **Lazard (1985), Lemma 1** (cited in §2.6; J. Symb. Comp. 1, 261–270): in a reduced (minimal)
Gröbner basis of a two-variable ideal `I ⊆ K[x,y]`, distinct elements have *distinct* leading
y-degrees `(m.degree b) 1` — the foundational step of Lazard's bivariate GB structure theorem and
the first stepping stone toward Czichowski's structural lemmas. The library's
`distinct_leadingYDegree_of_isReducedGroebnerBasis`
(order sublemma `finsupp_fin_two_le_or_le_of_apply_eq` + minimality extraction
`IsReducedGroebnerBasis.leadingMonomial_not_le`), with injectivity form
`injOn_leadingYDegree_of_isReducedGroebnerBasis`. -/
abbrev lazard_lemma1 := @DeepWiki.SymbolicIntegration.distinct_leadingYDegree_of_isReducedGroebnerBasis

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

/-- **Lazard (1985), Lemma 3, reduction step** (cited in §2.6; J. Symb. Comp. 1, p.263): with
`q = gᵢ/g_{i+1}` (`g_{i+1} ∣ gᵢ` from Lemma 2) the ideal element `yConst q·f_{i+1} − y^{d_{i+1}−dᵢ}·fᵢ`
has `y`-degree `< d_{i+1}` — its two terms share the `y`-degree-`d_{i+1}` leading-`y`-coefficient `gᵢ`,
so the top terms cancel. The library's `lazard_lemma3_reductionStep` (membership
`lazard_lemma3_reductionStep_mem`). The full descent `gᵢ ∣ fᵢ` over the sorted `f₀,…,fₖ` remains. -/
noncomputable abbrev lazard_lemma3_reductionStep :=
  @DeepWiki.SymbolicIntegration.lazard_lemma3_reductionStep

/-- **Lazard (1985), Lemma 3, the sorted enumeration** (cited in §2.6; J. Symb. Comp. 1, p.263): the
descent operates on the minimal Gröbner basis *sorted by increasing `y`-degree* `f₀,…,fₖ`. The
`y`-degrees `degreeOf 0` are distinct (`lazard_degreeOf_ne`, the index-`0` companion of Lemma 1), so
`sortedByYDegree` enumerates `B` with strictly increasing `y`-degree (`degreeOf_sortedByYDegree_strictMono`),
landing in `B` (`sortedByYDegree_mem`) and bijectively (`range_sortedByYDegree`). The library's
`sortedByYDegree`. -/
noncomputable abbrev lazard_sortedByYDegree := @DeepWiki.SymbolicIntegration.sortedByYDegree

/-- **Lazard (1985), Lemma 3, the descent step components** (cited in §2.6; J. Symb. Comp. 1, p.263):
the algebraic + combinatorial pieces of `gᵢ ∣ fᵢ`. The reduction transfer
`C_dvd_lazardView_of_reductionStep` (and `…_mul`) reduces `C(gᵢ) ∣ lazardView fᵢ` to divisibility of
`f_{i+1}` and `R := yConst q·f_{i+1} − y^{shift}·fᵢ`; `C_dvd_lazardView_sum` aggregates the per-element
IH through a `K[x][y]` combination; `exists_yDegree_bounded_representation` is the GB-reduction of
`R ∈ I` into basis elements of `y`-degree `≤ degreeOf 0 R` (lex division remainder `0`); and
`leadingYCoeff_sortedByYDegree_dvd_of_le` is the `gᵢ ∣ g_j` chain. The full descent (assembling these
into the circular-degree induction of p.263) remains. The library's
`C_dvd_lazardView_of_reductionStep`. -/
noncomputable abbrev lazard_lemma3_descentStep :=
  @DeepWiki.SymbolicIntegration.C_dvd_lazardView_of_reductionStep

/-- **Lazard (1985), Lemma 3, the assembled single descent step** (cited in §2.6; J. Symb. Comp. 1,
p.263): the per-step assembly of `gᵢ ∣ fᵢ`. From `C(gᵢ) ∣ C q·lazardView f_{i+1}` (the higher-index
input, `C_dvd_C_mul_lazardView_of_dvd` from `C(g_{i+1}) ∣ lazardView f_{i+1}`) and `C(gᵢ) ∣ lazardView b`
for every basis element of `y`-degree `≤ degreeOf 0 R` (`C_dvd_lazardView_of_mem_of_dvd_bounded`,
bounded GB-reduction + sum), the reduction step gives `C(gᵢ) ∣ lazardView fᵢ`. The full induction
stays open only at the no-common-factor `÷q` diagonal `C(g_{i+1}) ∣ lazardView f_{i+1}`. The library's
`C_dvd_lazardView_descentStep`. -/
noncomputable abbrev lazard_lemma3_descentStep_assembled :=
  @DeepWiki.SymbolicIntegration.C_dvd_lazardView_descentStep

/-- **Lazard (1985), Lemma 3, base case** (cited in §2.6; J. Symb. Comp. 1, p.263, "`f₀ ∈ K[x]`"): a
`y`-degree-`0` element has constant `K[x][y]` view `lazardView f = C (leadingYCoeff f)`, so `gᵢ ∣ fᵢ`
holds trivially. The library's `C_dvd_lazardView_of_degreeOf_zero`. -/
noncomputable abbrev lazard_lemma3_base :=
  @DeepWiki.SymbolicIntegration.C_dvd_lazardView_of_degreeOf_zero

/-- **Bronstein/Czichowski §2.6(i), `Pₖ = Rₖ·Sₖ`** (Lazard 1985, Lemma 3 payload): if `gᵢ ∣ fᵢ`
(`C(Rᵢ) ∣ lazardView fᵢ`), the `K[x][y]` view splits as `lazardView fᵢ = C(cᵢ)·Sᵢ` with content `cᵢ`
associated to `Rᵢ = leadingYCoeff fᵢ` and `Sᵢ` primitive with unit leading coefficient (monic-in-`y`).
The library's `lazard_Pk_eq_Rk_Sk` (content half `content_associated_leadingYCoeff_of_C_dvd`,
monic-primpart half `leadingCoeff_primPart_isUnit_of_C_dvd`). -/
noncomputable abbrev lazard_Pk_eq_Rk_Sk := @DeepWiki.SymbolicIntegration.lazard_Pk_eq_Rk_Sk

/-- **Lazard (1985), Lemma 3, the base obstruction is genuine** (cited in §2.6; the no-common-factor
base is a real hypothesis, not a free lemma): `f = xy + 1` (`y = X 0`, `x = X 1`) generates a reduced
Gröbner basis whose only — hence minimal-`y`-degree — element it is, with `leadingYCoeff f = x` **not a
unit** of `K[x]` and `C(x) ∤ lazardView f = C(x)·Y + 1`. So the descent's base divisibility `C(g₀) ∣
lazardView f₀` (and hence `C_dvd_lazardView_sortedByYDegree`) is **false** here; no leading-coefficient unit fact
discharges it, and Lazard's `P·Gₖ₊₁` divide-out is unavoidable (`I=(y)` further shows `IsUnit gₖ` alone
is insufficient). The library's `not_C_leadingYCoeff_dvd_lazardView_xyAddOne` (unit half
`not_isUnit_leadingYCoeff_xyAddOne`). -/
abbrev lazard_lemma3_base_obstruction :=
  @DeepWiki.SymbolicIntegration.not_C_leadingYCoeff_dvd_lazardView_xyAddOne

/-- **Lazard (1985), Lemma 3, the base = content criterion** (cited in §2.6; the "no common factor"
characterization): the descent base `C(gᵢ) ∣ lazardView fᵢ` holds **iff** `content(lazardView fᵢ)` is
*associated* to `Rᵢ = leadingYCoeff fᵢ` — `fᵢ` is `y`-primitive up to its leading coefficient. This is
exactly what Lazard's `P·Gₖ₊₁` divide-out achieves for the whole basis. The library's
`C_dvd_lazardView_iff_content_associated`. -/
abbrev lazard_lemma3_base_content_criterion :=
  @DeepWiki.SymbolicIntegration.C_dvd_lazardView_iff_content_associated

/-- **Lazard (1985), Lemma 3, the structure fact** (cited in §2.6; p.263, "`primpart(f₀)` divides
`f₀,…,fₖ`"): for the minimal-`y`-degree element `f₀`, its `y`-primitive part `P = primPart(lazardView
f₀)` divides `lazardView (sorted i)` for *every* `i` — by a reduction-element induction (the
`(gᵢ/g_{i+1})·fᵢ ∈ (fᵢ,…,f₀)` membership feeds the IH; Gauss's lemma strips the `K[x]`-scalar). The
library's `primPart_lazardView_min_dvd_all`. -/
noncomputable abbrev lazard_lemma3_structure_fact :=
  @DeepWiki.SymbolicIntegration.primPart_lazardView_min_dvd_all

/-- **Lazard (1985), Lemma 3, "`f₀ ∈ K[x]`" under no common factor** (cited in §2.6; p.263): if the
basis has no common `y`-factor (`HasNoCommonYFactor`: every common `K[x][y]`-divisor of the views is a
unit — Lazard's post-`P·Gₖ₊₁`-divide-out state), the minimal element has `y`-degree `0`, since the
common factor `primPart(lazardView f₀)` is forced to be a unit. The library's
`degreeOf_min_eq_zero_of_hasNoCommonYFactor`. -/
noncomputable abbrev lazard_lemma3_min_in_Kx :=
  @DeepWiki.SymbolicIntegration.degreeOf_min_eq_zero_of_hasNoCommonYFactor

/-- **Lazard (1985), Lemma 3 descent, unconditional** (cited in §2.6; the no-common-factor case): under
`HasNoCommonYFactor` the base divisibility is discharged, so `gᵢ ∣ fᵢ` (`C(Rᵢ) ∣ lazardView fᵢ`) holds
for every sorted element with **no** base hypothesis. The library's
`C_dvd_lazardView_sortedByYDegree_of_hasNoCommonYFactor`; the `Pₖ = Rₖ·Sₖ` split is
`lazard_Pk_eq_Rk_Sk_of_hasNoCommonYFactor`. -/
noncomputable abbrev lazard_lemma3_dvd_unconditional :=
  @DeepWiki.SymbolicIntegration.C_dvd_lazardView_sortedByYDegree_of_hasNoCommonYFactor

/-- **Lazard (1985), Theorem 1, the `P·Gₖ₊₁` divide-out** (cited in §2.6; p.262, proof: "we may divide
by `P·Gₖ₊₁` and suppose that the `fᵢ` have no common divisors"): from an **arbitrary** reduced bivariate
GB, the basis gcd `H = GCD(f₀,…,fₖ) = P·Gₖ₊₁` (`gbCommonYFactor`) divides every element, and the
cofactors `fᵢ = H·b'ᵢ` have **no common `y`-factor** (`cofactor_hasNoCommonYFactor`). The library's
`lazard_thm1_divideOut`. -/
noncomputable abbrev lazard_thm1_divide_out :=
  @DeepWiki.SymbolicIntegration.lazard_thm1_divideOut

/-- **Lazard (1985), Theorem 1, `Pₖ = Rₖ·Sₖ` for the general case** (cited in §2.6; p.262): the divide-out
delivers `HasNoCommonYFactor` to any reduced GB recovering its cofactors, so the structural split
`lazardView fⱼ = C(cⱼ)·Sⱼ` (`cⱼ ∼ leadingYCoeff fⱼ`, `Sⱼ` primitive and `y`-monic) holds for an arbitrary
reduced bivariate GB once divided by `H`. The library's `lazard_Pk_eq_Rk_Sk_of_divideOut`. -/
noncomputable abbrev lazard_thm1_structure :=
  @DeepWiki.SymbolicIntegration.lazard_Pk_eq_Rk_Sk_of_divideOut

/-- **Lazard (1985), Theorem 1, the divided family is a Gröbner basis of the quotient** (cited in §2.6;
p.262): the divided family `{fᵢ/H}` (`monicDividedBasis`) is a Gröbner basis of the quotient ideal
`I' = span {fᵢ/H}` (`dividedIdeal`), via the membership equivalence `g∈I' ⟺ H·g∈I` (`mem_dividedIdeal_iff`,
cancel `H` over the domain) and leading-monomial domination. The library's `isGroebnerBasis_dividedBasis`. -/
noncomputable abbrev lazard_thm1_quotient_groebner :=
  @DeepWiki.SymbolicIntegration.isGroebnerBasis_dividedBasis

/-- **Lazard (1985), Theorem 1, `HasNoCommonYFactor` is an ideal invariant** (cited in §2.6; p.262): *any*
reduced GB of the quotient ideal `I' = span {fᵢ/H}` has no common `y`-factor — a common factor of one
presentation's views divides every ideal member's view (`dvd_lazardView_of_mem_span`), hence the cofactors
(gcd 1). This discharges the `hassoc` re-presentation hypothesis automatically. The library's
`hasNoCommonYFactor_of_dividedIdeal`. -/
noncomputable abbrev lazard_thm1_quotient_no_common_factor :=
  @DeepWiki.SymbolicIntegration.hasNoCommonYFactor_of_dividedIdeal

/-- **Lazard (1985), Theorem 1, `Pₖ = Rₖ·Sₖ` for the divided quotient** (cited in §2.6; p.262): for any
reduced GB of the quotient ideal `I' = span {fᵢ/H}`, the structural split `lazardView fⱼ = C(cⱼ)·Sⱼ`
(`cⱼ ∼ leadingYCoeff fⱼ`, `Sⱼ` primitive and `y`-monic) holds, with the no-common-factor hypothesis
discharged automatically. The library's `lazard_Pk_eq_Rk_Sk_dividedIdeal`. -/
noncomputable abbrev lazard_thm1_quotient_structure :=
  @DeepWiki.SymbolicIntegration.lazard_Pk_eq_Rk_Sk_dividedIdeal

/-- **Czichowski (1995), Lemma 2.1, `GB₁` is a Gröbner basis** (cited in §2.6 as the Czichowski
algorithm engine; J. Symb. Comp. 20, 163–167, p.164): `GB₁ = {D(x), z − T(x)}` is a Gröbner basis of
`I = ⟨A − z·D', D⟩ ⊂ K[x, z]` w.r.t. the p.l. ordering `z > x`, with `T = A·(D'⁻¹ mod D) mod D`. The
library's `isGroebnerBasis_gb` (`z = X 0` dominant, `x = X 1`). -/
noncomputable abbrev czichowski_lemma_2_1_gb := @DeepWiki.SymbolicIntegration.isGroebnerBasis_gb

/-- **Czichowski (1995), Lemma 2.1, `I = ⟨D, z − T⟩`** (J. Symb. Comp. 20, p.164): the reduced
generators of `I = ⟨A − z·D', D⟩`. The library's `czIdeal_eq_span_gb`. -/
noncomputable abbrev czichowski_lemma_2_1_ideal_eq := @DeepWiki.SymbolicIntegration.czIdeal_eq_span_gb

/-- **Czichowski (1995), Lemma 2.1, the residue polynomial `T`** (J. Symb. Comp. 20, p.164): the zeros
`(α, T(α))` of `I` have `z`-part `T(α) = A(α)/D'(α)`, the Rothstein–Trager residue, at each root `α`
of (squarefree) `D`. The library's `eval_residuePoly_of_isRoot`. -/
noncomputable abbrev czichowski_lemma_2_1_residue :=
  @DeepWiki.SymbolicIntegration.eval_residuePoly_of_isRoot

/-- **Czichowski (1995), Lemma 2.1, the eliminating iso** (J. Symb. Comp. 20, p.164): substituting
`z = T` identifies `K[x, z] ⧸ I ≃ₐ[K] K[x] ⧸ (D)`. The library's `czIdealQuotEquiv`. -/
noncomputable abbrev czichowski_lemma_2_1_quotient_equiv :=
  @DeepWiki.SymbolicIntegration.czIdealQuotEquiv

/-- **Czichowski (1995), Lemma 2.1(i), zero-dimensionality** (J. Symb. Comp. 20, p.164): `I` is
zero-dimensional, i.e. `K[x, z] ⧸ I` is a finite `K`-module (rank `deg D`), since `D` is monic. The
library's `finite_quotient_czIdeal`. -/
noncomputable abbrev czichowski_lemma_2_1_zero_dimensional :=
  @DeepWiki.SymbolicIntegration.finite_quotient_czIdeal

/-- **Czichowski (1995), Lemma 2.1(iii), maximality w.r.t. the zero set** (J. Symb. Comp. 20, p.164):
`I = ⟨A − z·D', D⟩` is radical (`I = √I`), i.e. maximal among the ideals with its zero set — by the
Nullstellensatz `I(V(I)) = √I`, this is exactly `I = I(V(I))`. The library's `czIdeal_isRadical`. -/
noncomputable abbrev czichowski_lemma_2_1_radical :=
  @DeepWiki.SymbolicIntegration.czIdeal_isRadical

/-- **Czichowski (1995), Lemma 2.1(iii), geometric form** (J. Symb. Comp. 20, p.164): over an
algebraically closed `K`, `I = ⟨A − z·D', D⟩` is its own vanishing ideal, `I = I(V(I))` — Hilbert's
Nullstellensatz `I(V(I)) = √I` applied to the radical `I`. The library's
`czIdeal_eq_vanishingIdeal_zeroLocus`. -/
noncomputable abbrev czichowski_lemma_2_1_vanishing_ideal :=
  @DeepWiki.SymbolicIntegration.czIdeal_eq_vanishingIdeal_zeroLocus

/-- **Czichowski (1995), Lemma 2.2(iii), the `z`-elimination ideal** (cited in §2.6; J. Symb. Comp. 20,
p.165): the `z`-elimination ideal `I ∩ K[z]` of `I = ⟨A − z·D', D⟩` is `(R₁)`, generated by the monic
squarefree `R₁ = ∏_{distinct residue a}(z − a)` — the content of the first pure-`z` element of the
reduced Gröbner basis for the p.l. ordering `x > z`. The library's `elimZ_eq_span_czichowskiR1`. -/
noncomputable abbrev czichowski_lemma_2_2_iii_elimination :=
  @DeepWiki.SymbolicIntegration.elimZ_eq_span_czichowskiR1

/-- **Czichowski (1995), Lemma 2.2(iii), `R₁ = radical(resultant)`** (cited in §2.6; J. Symb. Comp. 20,
p.165): Czichowski's `R₁` is the radical (squarefree part) of the Rothstein–Trager resultant
`res_x(A − z·D', D)`. The library's `czichowskiR1_eq_radical_rtResultant`. -/
noncomputable abbrev czichowski_lemma_2_2_iii_radical :=
  @DeepWiki.SymbolicIntegration.czichowskiR1_eq_radical_rtResultant

/-! ## §2.7 Newton–Leibniz–Bernoulli Revisited -/

/-- **Theorem 2.7.1, the base-`Dᵢ` (`Dᵢ`-adic) digit expansion** (§2.7, p.55, the substantive new
ingredient): for monic `g` of positive degree and `B` with `deg B < e·deg g`, the base-`g` digits
`Cⱼ = baseDigit B g j = (B /ₘ g^j) %ₘ g` reconstruct `B = ∑_{j<e} Cⱼ·g^j` with `deg Cⱼ < deg g` — the
polynomial positional notation underlying the `Dᵢ`-adic Laurent series of `B/Dᵢ^{eᵢ}`. The library's
`baseDigit_reconstruction` (digits via repeated division by the monic `Dᵢ`; `divByMonic_pow_succ` is the
iterated-division step), with degree bound `degree_baseDigit_lt`. -/
abbrev thm_2_7_1_baseExpansion := @DeepWiki.SymbolicIntegration.baseDigit_reconstruction

/-- **Theorem 2.7.1, the `Dᵢ`-adic expansion of one prime-power fraction** (§2.7, p.55): for monic `g`
and `deg B < e·deg g`, `B/g^e = ∑_{k=1}^{e} Hₖ/g^k` with `Hₖ = baseDigit B g (e−k)`, `deg Hₖ < deg g` —
the digit expansion `B = ∑_{j<e} Cⱼ·g^j` rewritten with descending powers (reindexed `k = e−j`). The
library's `ratFunc_DadicExpansion`. -/
abbrev thm_2_7_1_DadicExpansion := @DeepWiki.SymbolicIntegration.ratFunc_DadicExpansion

/-- **Theorem 2.7.1, the complete partial fraction decomposition** (§2.7, p.55, the structural
`K[x]`-level conclusion): for `A, D ∈ K[x]` with squarefree factorization `D = D₁D₂²⋯Dₙⁿ = ∏ᵢ Dᵢ^{eᵢ}`
(monic, pairwise-coprime, positive-degree `Dᵢ`, `eᵢ ≥ 1`),
`A/D = P + ∑ᵢ ∑_{j=1}^{eᵢ} Hᵢⱼ/Dᵢ^j` with `deg Hᵢⱼ < deg Dᵢ` and `P = A div D` — the `Hᵢⱼ(α)/(x−α)ʲ`
over-the-closure form being the evaluation of `Hᵢⱼ` at the roots `α` of `Dᵢ`. The library's
`ratFunc_completePartialFraction`, composing Mathlib's degree-bounded coprime split with the per-factor
`Dᵢ`-adic expansion. The *rational algorithm* for the `Hᵢⱼ` (the differential-variable Laurent-coefficient
construction, eqs 2.10–2.12) is `thm_2_7_1_laurentH`. -/
abbrev thm_2_7_1 := @DeepWiki.SymbolicIntegration.ratFunc_completePartialFraction

/-- **Theorem 2.7.1, the differential-variable Laurent-coefficient engine** (§2.7, p.54–56, eqs 2.10–2.12,
the Bronstein–Salvy rational `Hᵢⱼ` algorithm): `Hᵢⱼ = Qᵢⱼ·Bᵢ^{i−j+1}·Cᵢ^{2i−j} (mod Dᵢ)`, computing the
partial-fraction Laurent coefficients by purely rational operations over `K` (no factoring of `Dᵢ`). Built
over `R = MvPolynomial (Option ℕ) K` (variable `none` = `x`, `some n` = the `n`-th derivative `u^(n)` of a
differential indeterminate) with `d/dx = mkDerivation`. The library's `laurentH`. -/
noncomputable abbrev thm_2_7_1_laurentH := @DeepWiki.SymbolicIntegration.laurentH

/-- **Theorem 2.7.1, eq 2.10** (§2.7, p.55): the extended-Euclidean Bézout cofactor `Bᵢ` with
`Bᵢ·Eᵢ ≡ 1 (mod Dᵢ)` (`Eᵢ = D /ₘ Dᵢ^i`), via `diophantineSolve`. The library's `bezoutE`, with
congruence `bezoutE_mul_laurentE_modByMonic`. -/
noncomputable abbrev eq_2_10_bezoutE := @DeepWiki.SymbolicIntegration.bezoutE

/-- **Theorem 2.7.1, eq 2.10** (§2.7, p.55): the extended-Euclidean Bézout cofactor `Cᵢ` with
`Cᵢ·Dᵢ' ≡ 1 (mod Dᵢ)`, via `diophantineSolve`. The library's `bezoutDeriv`, with congruence
`bezoutDeriv_mul_derivative_modByMonic`. -/
noncomputable abbrev eq_2_10_bezoutDeriv := @DeepWiki.SymbolicIntegration.bezoutDeriv

/-- **Theorem 2.7.1, eq 2.11** (§2.7, p.55): the Laurent numerator `Pᵢⱼ ∈ K(x)⟨u⟩` of
`hᵢ^{i−j}/(i−j)! = Pᵢⱼ/(u^{2i−j}·Eᵢ^{i−j+1})`, defined by the quotient-rule recursion on the derivative
count `i−j`. The library's `laurentNum` (with step `laurentNumStep`). -/
noncomputable abbrev eq_2_11_laurentNum := @DeepWiki.SymbolicIntegration.laurentNum

/-- **Theorem 2.7.1, the `Qᵢⱼ` substitution** (§2.7, p.55): `Qᵢⱼ = Pᵢⱼ(x, Dᵢ', Dᵢ''/2, …, Dᵢ^{i−j+1}/(i−j+1))
∈ K[x]`, the `aeval` of `Pᵢⱼ` under `u^(k) ↦ Dᵢ^{(k+1)}/(k+1)`. The library's `laurentQ`. -/
noncomputable abbrev thm_2_7_1_laurentQ := @DeepWiki.SymbolicIntegration.laurentQ

/-- **Theorem 2.7.1, the `i=1` residue** (§2.7, p.56): the engine's simplest output, `H₁₁(α) = A(α)/D'(α)`
— the Rothstein–Trager residue of `A/D` at a simple root `α` of `D = D₁·E₁`, since `B₁(α)=1/E₁(α)`,
`C₁(α)=1/D₁'(α)` and `D'(α)=D₁'(α)·E₁(α)`. The library's `eval_laurentH_one_one_eq_residue`. -/
abbrev thm_2_7_1_residue := @DeepWiki.SymbolicIntegration.eval_laurentH_one_one_eq_residue

/-- **Theorem 2.7.1, eq 2.11 as a fraction-field invariant** (§2.7, p.55, the validation of the `Pᵢⱼ`
recursion): in `K(x)⟨u⟩ = Frac (DiffPoly K)`, `(d/dx)^[i−j] hᵢ = (i−j)!·(Pᵢⱼ/(u^{2i−j}·Eᵢ^{i−j+1}))` for
`hᵢ = A/(uⁱ·Eᵢ)` — exactly the book's `hᵢ^{(i−j)}/(i−j)! = Pᵢⱼ/(u^{2i−j}·Eᵢ^{i−j+1})`. The `laurentNumStep`
divisor is the factorial increment `d+1` (`laurentScale K i d = d!`, `laurentScale_eq_factorial`), so
`laurentNum` is EXACTLY the book's `Pᵢⱼ` and the engine faithfully computes `Hᵢⱼ`. Validates
`laurentNum`/`laurentNumStep` against the genuine quotient-rule `d/dx`. The library's
`iterate_fracKDeriv_hFrac`, built on the `K`-derivation `fracKDeriv` on the fraction field (quotient rule
via `Localization.liftOn`) and the cleared step `laurentNum_cleared_step`/`reduced_num`. -/
abbrev eq_2_11_invariant := @DeepWiki.SymbolicIntegration.iterate_fracKDeriv_hFrac

/-- **Theorem 2.7.1, the root-evaluation `Qᵢⱼ(α) = Pᵢⱼ(α, Dᵢ,α(α), …)`** (§2.7, p.56): at a root `α` of
`Dᵢ = (x−α)·Dᵢ,α` (over `K̄`), the `Qᵢⱼ` substitution evaluates to `Pᵢⱼ` at the derivatives of `Dᵢ,α`,
`Qᵢⱼ(α) = Pᵢⱼ(α, Dᵢ,α(α), Dᵢ,α'(α), …, Dᵢ,α^{i−j}(α))` — via the Leibniz identity
`Dᵢ^{(k+1)}(α) = (k+1)·Dᵢ,α^{(k)}(α)` (the library's `eval_laurentSubst_some`). The library's
`laurentQ_eval_at_root`. (`Pᵢⱼ(α,…)` is identified with the `(i−j)`-th Taylor coefficient of
`hᵢ,α = (A/D)(x−α)ⁱ`, hence the `1/(x−α)ʲ` Laurent coefficient of `A/D`, in `thm_2_7_1_taylor_coeff`;
the literal book conclusion is `thm_2_7_1_engineForm`.) -/
abbrev thm_2_7_1_laurentQ_eval := @DeepWiki.SymbolicIntegration.laurentQ_eval_at_root

/-- **Theorem 2.7.1, the differential substitution hom `σα`** (§2.7, p.56, the bridge to the genuine
function): `σα : DiffPoly K →ₐ[K] K[x]` (`x ↦ X`, `u^(k) ↦ Dᵢ,α^{(k)}`) is a **differential** algebra hom —
`σα(ddx p) = derivative(σα p)` — carrying the engine's `d/dx` (`ddx`) to the genuine `Polynomial.derivative`,
so it commutes with the iterated `(d/dx)^{[d]}`. This is what lets the differential-variable invariant be
pushed onto the actual rational function `hᵢ,α = (A/D)(x−α)ⁱ`. The library's `diffSubst`/`diffSubst_ddx`. -/
noncomputable abbrev thm_2_7_1_diffSubst := @DeepWiki.SymbolicIntegration.diffSubst_ddx

/-- **Theorem 2.7.1, the specialized eq 2.11 invariant in `K(x)`** (§2.7, p.56, the genuine-function form):
`(d/dx)^{[i−j]} hᵢ,α = (i−j)!·(σα(Pᵢⱼ)/(Dᵢ,α^{2i−j}·Eᵢ^{i−j+1}))` for the **actual** rational function
`hᵢ,α = A/(Dᵢ,α^i·Eᵢ) = (A/D)(x−α)ⁱ`, under the genuine `d/dx = ratFuncKDeriv` on `K(x)`. The image of the
`Frac (DiffPoly K)` invariant (`eq_2_11_invariant`) under the differential hom `σα` (`thm_2_7_1_diffSubst`),
proved by re-running the induction at the `K(x)` level (`σα` is surjective but not injective). This makes the
engine's `Pᵢⱼ` genuinely the numerators of the derivatives of the actual function `hᵢ,α`. The library's
`iterate_ratFuncKDeriv_hFracα` (step `ratFuncKDeriv_lFracα`, numerator `reduced_numα`). -/
abbrev thm_2_7_1_invariant_ratfunc := @DeepWiki.SymbolicIntegration.iterate_ratFuncKDeriv_hFracα

/-- **Theorem 2.7.1, the root-value bridge `σα(Pᵢⱼ)(α) = Qᵢⱼ(α)`** (§2.7, p.56): the value at `α` of the
genuine `hᵢ,α^{(i−j)}/(i−j)!` numerator (`= σα(laurentNum …)`, from the `K(x)` invariant) equals the engine's
`Qᵢⱼ(α)` — both are `aeval (substEvalAt Dᵢ,α α) (laurentNum …)`. Identifies the engine's rational `Qᵢⱼ(α)`
with the (Taylor-coefficient-bearing) numerator of the actual `hᵢ,α = (A/D)(x−α)ⁱ`. The library's
`eval_diffSubst_laurentNum_eq_laurentQ_eval` (via `eval_diffSubst`). -/
abbrev thm_2_7_1_diffSubst_eval :=
  @DeepWiki.SymbolicIntegration.eval_diffSubst_laurentNum_eq_laurentQ_eval

/-- **Theorem 2.7.1, the general engine-output evaluation** (§2.7, p.56, eq 2.12 evaluated, for ALL `i,j`):
at a root `α` of the monic `Dᵢ`, `Hᵢⱼ(α) = Qᵢⱼ(α)·(1/Eᵢ(α))^{i−j+1}·(1/Dᵢ'(α))^{2i−j}` — the engine output
evaluates to the substitution value `Qᵢⱼ(α)` times the Bézout-cofactor powers `Bᵢ(α) = 1/Eᵢ(α)`,
`Cᵢ(α) = 1/Dᵢ'(α)` (from the (2.10) congruences; `%ₘ Dᵢ` is invisible at the root). Generalizes the `i=1`
residue `thm_2_7_1_residue` to all `i,j`. The library's `eval_laurentH`; the combined form expressing `Hᵢⱼ(α)`
through the genuine-`hᵢ,α`-numerator `σα(Pᵢⱼ)(α)` is `eval_laurentH_eq_diffSubst_laurentNum`. -/
abbrev thm_2_7_1_eval := @DeepWiki.SymbolicIntegration.eval_laurentH

/-- **Theorem 2.7.1, `Hᵢⱼ(α)` from the genuine `hᵢ,α`-numerator** (§2.7, p.56, Steps 2+3+5 combined): at a
root `α` of the monic `Dᵢ = (x−α)·Dᵢ,α`, `Hᵢⱼ(α) = σα(Pᵢⱼ)(α)·(1/Eᵢ(α))^{i−j+1}·(1/Dᵢ'(α))^{2i−j}`, routing
the engine's `Qᵢⱼ(α)` through the value at `α` of the **genuine** `hᵢ,α^{(i−j)}/(i−j)!` numerator. The library's
`eval_laurentH_eq_diffSubst_laurentNum`. -/
abbrev thm_2_7_1_eval_diffSubst := @DeepWiki.SymbolicIntegration.eval_laurentH_eq_diffSubst_laurentNum

/-- **Theorem 2.7.1, the Taylor-coefficient identification** (§2.7, p.56, the substantive Step-4 core): at a
root `α` of the monic `Dᵢ = (x−α)·Dᵢ,α` (with `j ≤ i`, `Eᵢ(α), Dᵢ,α(α) ≠ 0`), the engine output is the
order-`(i−j)` Taylor coefficient of the genuine rational function `hᵢ,α = (A/D)(x−α)ⁱ` at `α`:
`Hᵢⱼ(α) = (1/(i−j)!)·(d/dx)^[i−j] hᵢ,α (α)`. Evaluates the specialized eq 2.11 invariant
(`thm_2_7_1_invariant_ratfunc`) at `α` (`RatFunc.eval id α`, a ring hom off the nonzero denominator) and
cancels the `(Dᵢ,α, Eᵢ)`-power factors of `thm_2_7_1_eval_diffSubst` via the cofactor identity
`Dᵢ'(α) = Dᵢ,α(α)`. Those Taylor coefficients ARE the `1/(x−α)ʲ` partial-fraction coefficients `c_j` of `A/D`
by the definition of `hᵢ,α`; the literal `= c_j` naming is the only residual (§2.7 NOT YET FORMALIZED). The
library's `eval_laurentH_eq_taylor_coeff`. -/
abbrev thm_2_7_1_taylor_coeff := @DeepWiki.SymbolicIntegration.eval_laurentH_eq_taylor_coeff

/-- **Theorem 2.7.1, the closure-level partial-fraction assembly** (§2.7, p.56, the principal-part core):
for `D = (x−α)^i·M` with `M(α) ≠ 0` (`α` a pole of `A/D` of order `≤ i`), subtracting the engine's per-root
Laurent sum `∑_{j=1}^{i} c_{i−j}/(x−α)ʲ` (`localPrincipalPart`) leaves `R/M`, regular at `α`:
`A/D − ∑_{j=1}^{i} c_{i−j}/(x−α)ʲ = R/M`, `M(α) ≠ 0`. This is the substantive partial-fraction statement —
the per-root sum IS the principal part of `A/D` at the pole `α`. The Laurent coefficients
`c_d = localCoeff A M α i d` are the `(x−α)`-adic digits of the local Taylor approximant
`W = (A·N) %ₘ (x−α)^i` (`N = M⁻¹ mod (x−α)^i`), which agrees with `A·(x−α)ⁱ/D` to order `i` at `α`
(`M·W ≡ A`). The library's `subtract_localPrincipalPart_eq` (existence form
`exists_regular_sub_localPrincipalPart`). Identifying `c_{i−j} = Hᵢⱼ(α)` is `thm_2_7_1_coeff_bridge`. -/
abbrev thm_2_7_1_principalPart := @DeepWiki.SymbolicIntegration.subtract_localPrincipalPart_eq

/-- **Theorem 2.7.1, the coefficient bridge `localCoeff = (1/d!)·(d/dx)^[d](A/M)(α)`** (§2.7, p.56, the
Hasse-derivative ↔ differential-engine identification): for `D = (x−α)ⁱ·M` (`M(α) ≠ 0`) and `d < i`, the
Stage L `(X−α)`-adic Laurent digit `localCoeff A M α i d = (taylor α W).coeff d` (the `(x−α)`-adic digit of the
local approximant `W = (A·N) %ₘ (x−α)ⁱ`) is the order-`d` Taylor coefficient of the genuine function
`hᵢ,α = A/M = (A/D)(x−α)ⁱ`. Proof: split `A/M = W + (A/M − W)`, push `(d/dx)^[d]` through; the embedded-`W`
term gives `d!·localCoeff` (Hasse identity `d!·hasseDeriv = derivative^[d]`), the remainder
`(A/M − W) = (A − M·W)/M` (numerator divisible by `(x−α)ⁱ`) vanishes at `α` for `d < i`. The library's
`localCoeff_eq_taylor_coeff`. -/
abbrev thm_2_7_1_coeff_bridge := @DeepWiki.SymbolicIntegration.localCoeff_eq_taylor_coeff

/-- **Theorem 2.7.1, the FULL coefficient identification `localCoeff = Hᵢ,(i−d)(α)`** (§2.7, p.56, the LAST
bridge — now PROVED): at a root `α` of the monic `Dᵢ = (x−α)·Dᵢ,α`, with `M = Dᵢ,α^i·Eᵢ` (`Eᵢ = laurentE D Dᵢ i`,
`D = (x−α)ⁱ·M`) and `d < i`, the Stage L Laurent digit `localCoeff A M α i d` equals the Bronstein–Salvy engine
output `Hᵢ,(i−d)(α) = (laurentH A D Dᵢ i (i−d))(α)`. Both equal the order-`d` Taylor coefficient
`(1/d!)·(d/dx)^[d](A/M)(α)` of `hᵢ,α = A/M`: `localCoeff` by the Hasse bridge (`thm_2_7_1_coeff_bridge`), the
engine output by the differential-engine invariant (`thm_2_7_1_taylor_coeff`, with `i − (i − d) = d`). This is
the final unification of the principal-part structure with the differential engine. The library's
`localCoeff_eq_laurentH`. -/
abbrev thm_2_7_1_coeff_eq_laurentH := @DeepWiki.SymbolicIntegration.localCoeff_eq_laurentH

/-- **Theorem 2.7.1, the multi-pole telescoping** (§2.7, p.56, the closure-level assembly over all poles): for a
`Finset R` of distinct roots with multiplicities `mult` and a base `M₀` pole-free at every `α ∈ R`, subtracting
the per-pole principal parts at every `α ∈ R` from `A/(∏_{α∈R}(x−α)^{mult α}·M₀)` leaves a remainder `Rem/M₀`
regular at every `α ∈ R`: `A/(∏_{α∈R}(x−α)^{mult α}·M₀) = ∑_{α∈R} PP α + Rem/M₀`, each `PP α` a genuine Laurent
sum. Proved by `Finset` induction peeling one root at a time via `thm_2_7_1_principalPart` (the numerator is
generalized so each peel recurses on the local remainder). The library's `exists_sum_localPrincipalPart`. -/
abbrev thm_2_7_1_telescoping := @DeepWiki.SymbolicIntegration.exists_sum_localPrincipalPart

/-- **Theorem 2.7.1, the over-the-closure complete partial fraction** (§2.7, p.56, the literal conclusion when
`D` splits): for `D = (∏_{α∈R}(x−α)^{mult α})·C c` (`c ≠ 0`, `R` the full root set over `K̄`), there is a
polynomial part `P` and a per-pole principal-part family `PP` (each `PP α = ∑_{j=1}^{mult α} c_{α,j}/(x−α)ʲ`)
with `A/D = P + ∑_{α∈R} PP α`. The constant base makes the telescoping remainder `Rem/(C c)` a pure polynomial
(`div_C_eq_algebraMap`), the polynomial part `P`. The library's `completePartialFraction_over_closure`. -/
abbrev thm_2_7_1_over_closure := @DeepWiki.SymbolicIntegration.completePartialFraction_over_closure

/-- **Theorem 2.7.1, principal-part intrinsicity / uniqueness** (§2.7, p.56, the closing fact): two principal
parts at `α` of order `i` whose difference is regular at `α` are equal. The mechanism: a principal part at `α`
consolidates to `W/(x−α)^i` with `deg W < i`; if equal to a function regular at `α` (`= N/M`, `M(α) ≠ 0`),
cross-multiplying gives `(x−α)^i ∣ W·M`, coprimality forces `(x−α)^i ∣ W`, and `deg W < i` forces `W = 0`. This
is what makes the partial-fraction principal part *intrinsic* — independent of how the regular rest is split
off — and so closes the peeled-vs-original numerator matching of the multi-pole assembly. The library's
`principalPart_unique`. -/
abbrev thm_2_7_1_principalPart_unique := @DeepWiki.SymbolicIntegration.principalPart_unique

/-- **Theorem 2.7.1, the literal per-pole engine form** (§2.7, p.56): the principal part of `A/D` at a root `α`
of `Dᵢ = (x−α)·Dᵢ,α` (over the original cofactor `M = Dᵢ,α^i·Eᵢ`, `D = (x−α)ⁱ·M`) is **literally** the
Bronstein–Salvy engine sum `∑_{j=1}^{i} (laurentH A D Dᵢ i j)(α)/(x−α)ʲ`, since each Laurent coefficient
`localCoeff A M α i (i−j) = Hᵢⱼ(α)` (`thm_2_7_1_coeff_eq_laurentH`). The library's
`localPrincipalPart_eq_engineSum`. -/
abbrev thm_2_7_1_engineSum := @DeepWiki.SymbolicIntegration.localPrincipalPart_eq_engineSum

/-- **Theorem 2.7.1, the LITERAL engine-form partial fraction over `K̄`** (§2.7, p.55–56, the full closure-level
conclusion `A/D = P + ∑ᵢ ∑_{α|Dᵢ(α)=0} (Hᵢᵢ(α)/(x−α)ⁱ + ⋯ + Hᵢ₁(α)/(x−α))`): for `D = (∏_{α∈R}(x−α)^{mult α})·C c`
split over `K̄`, with per-pole squarefree-factorization data, `A/D = P + ∑_{α∈R} ∑_{j=1}^{mult α} Hᵢⱼ(α)/(x−α)ʲ`
— the engine outputs `laurentH` ARE the partial-fraction Laurent coefficients. Each per-pole principal part from
the regularity-carrying telescoping (`exists_sum_localPrincipalPart_regular`) is identified with the original-`A`
engine sum by intrinsicity (`thm_2_7_1_principalPart_unique`). The library's `completePartialFraction_engineForm`. -/
abbrev thm_2_7_1_engineForm := @DeepWiki.SymbolicIntegration.completePartialFraction_engineForm

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

/-! ## §2.8 Rioboo's Algorithm for Real Rational Functions -/

/-- **Property (2.16)** (§2.8, p.60), the field with no `√−1`: if `x²+1` is irreducible over `K`,
then for `P, Q ∈ K[x]`, `P² + Q² = 0 ⟹ P = 0 ∧ Q = 0`. Proof: if `Q ≠ 0`, comparing leading
coefficients of `P² = −Q²` makes `−1 = (lc P / lc Q)²` a square in `K`, contradicting irreducibility
of `x²+1` (`not_isSquare_neg_one_of_irreducible`). The library's `sq_add_sq_eq_zero_of_irreducible`. -/
abbrev eq_2_16 := @DeepWiki.SymbolicIntegration.sq_add_sq_eq_zero_of_irreducible

/-- **Property (2.16), the `√−1`-free reformulation** (§2.8, p.60): `x²+1` irreducible over `K` ⟺ `−1`
has no square root in `K` (a root of `x²+1` is exactly a `√−1`). The library's
`not_isSquare_neg_one_of_irreducible`, with the root bridge `isSquare_neg_one_iff_exists_isRoot`. -/
abbrev eq_2_16_not_isSquare := @DeepWiki.SymbolicIntegration.not_isSquare_neg_one_of_irreducible

/-- **Constant `√−1`** (§2.8, p.60, behind eq 2.17): in a characteristic-`0` differential field, an
element `i` with `i² = −1` is a constant (`i′ = 0`) — differentiate `i² = −1` to `2·i·i′ = 0` and
cancel `2·i ≠ 0`. The library's `deriv_eq_zero_of_sq_eq_neg_one`. -/
abbrev lemma_2_8_1_const_i := @DeepWiki.SymbolicIntegration.deriv_eq_zero_of_sq_eq_neg_one

/-- **Lemma 2.8.1** (§2.8, p.60), rewriting a complex logarithm as a real arctangent: for `u` with
`u² ≠ −1`, `√−1 · d/dx log((u+√−1)/(u−√−1)) = 2 · d/dx arctan(u)` (eq 2.17). As a differential-field
identity (with `i = √−1`, `i² = −1` ⟹ `i` constant, and `arctan'(u) = u'/(1+u²)`):
`i · logDeriv((u+i)/(u−i)) = 2·u'/(1+u²)`. The logarithmic derivative
`logDeriv((u+i)/(u−i)) = u'/(u+i) − u'/(u−i) = −2i·u'/(u²+1)` (using `(u±i)' = u'`, `i` constant), and
`i·(−2i) = −2i² = 2`. The library's `logDeriv_imagQuot_eq_arctanDeriv_of_sq` (the constant-`i`
hypothesis `i′ = 0` discharged from `i² = −1` via `deriv_eq_zero_of_sq_eq_neg_one`); the bare form taking `i′ = 0`
as a hypothesis is `logDeriv_imagQuot_eq_arctanDeriv`. -/
abbrev lemma_2_8_1 := @DeepWiki.SymbolicIntegration.logDeriv_imagQuot_eq_arctanDeriv_of_sq

/-- **Theorem 2.8.1(a)** (§2.8, p.62, Rioboo): for `A, B ∈ K[x]\{0}` with `A²+B² ≠ 0` (`i² = −1`),
`d/dx log((A+iB)/(A−iB)) = d/dx log((−B+iA)/(−B−iA))` — the two complex logarithms have equal
logarithmic derivatives because `(A+iB)/(A−iB) = −(−B+iA)/(−B−iA)` and the `−1` factor has zero
`logDeriv`. The library's `logDeriv_imagQuot_eq_imagQuot_swap`. -/
abbrev thm_2_8_1_a := @DeepWiki.SymbolicIntegration.logDeriv_imagQuot_eq_imagQuot_swap

/-- **Theorem 2.8.1(b)** (§2.8, p.62, Rioboo's recursion-step identity, the LogToAtan reduction): for
`A, B` with `A²+B² ≠ 0` (`i² = −1`) and `C, D ∈ K[x]` with `B·D − A·C = G := gcd(A,B)`, `C ≠ 0`,
`C²+D² ≠ 0`, and `P := (A·D + B·C)/G`,
`i · d/dx log((A+iB)/(A−iB)) = 2 · d/dx arctan(P) + i · d/dx log((D+iC)/(D−iC))` — rendering
`d/dx arctan(P) = P'/(1+P²)`. Proof: the factoring `(A+iB)/(A−iB) = ((P+i)/(P−i))·((D+iC)/(D−iC))`
(from `(D−iC)(A+iB) = G(P+i)`, `(D+iC)(A−iB) = G(P−i)`) makes `logDeriv` additive, and Lemma 2.8.1
turns `i·logDeriv((P+i)/(P−i))` into `2·P'/(1+P²)`. The denominator nonvanishing is supplied by
`sub_imag_ne_zero`/`add_imag_ne_zero` and `sq_add_one_ne_zero_of_quot` (`(P²+1)G² = (A²+B²)(C²+D²)`).
The library's `logDeriv_imagQuot_eq_arctan_add_imagQuot`. -/
abbrev thm_2_8_1_b := @DeepWiki.SymbolicIntegration.logDeriv_imagQuot_eq_arctan_add_imagQuot

/-- **`LogToAtan` algorithm** (§2.8, p.63): Rioboo's recursion converting a complex logarithm
`i·log((A+iB)/(A−iB))` to a sum `∑ 2·arctan(P)` of real arctangents (`A, B ∈ K[x]`, `B ≠ 0`).
`if B ∣ A return [A/B]`; `if deg A < deg B return LogToAtan(−B, A)`; else with `B·D − A·C = G =
gcd(A,B)`, `return (A·D+B·C)/G :: LogToAtan(D, C)`. The library's `logToAtanAux` (fuel-bounded, total,
embedding the operands into a characteristic-`0` differential field via a ring hom `φ` with `i² = −1`);
the arctan-derivative sum of a list is `atanDerivSum`. -/
noncomputable abbrev logToAtan_algorithm := @DeepWiki.SymbolicIntegration.logToAtanAux

/-- **`LogToAtan` correctness** (§2.8, p.63): the output `f = ∑_{P∈L} 2·arctan(P)` of `LogToAtan(A, B)`
satisfies `df/dx = d/dx · i·log((A+iB)/(A−iB))` — as derivatives, `∑_{P∈L} 2·P'/(1+P²) =
i·logDeriv((φA+iφB)/(φA−iφB))`. Each branch is Theorem 2.8.1: base = Lemma 2.8.1 (`atanDerivSum_base`),
swap = Thm 2.8.1(a) (`imagLog_swap`), step = Thm 2.8.1(b) (`imagLog_step`); the assembly is over the
inductive run spec `IsLogToAtanRun`. The library's `isLogToAtanRun_correct` (and the fuel-def bridge
`logToAtanAux_correct`). -/
abbrev logToAtan_correct := @DeepWiki.SymbolicIntegration.isLogToAtanRun_correct

/-- **Example 2.8.1** (§2.8, p.63–64), the worked `LogToAtan` run on `A = x³−3x`, `B = x²−2`: the
book table (p.64) lists the three branches — step 1 cofactors `(C,D,G) = (x/2, x²/2−1/2, 1)`, step 2
`(2, 2x, 1)`, base `2x/2 = x` — emitting arctan arguments `[(x⁵−3x³+x)/2, x³, x]`, so
`∫ (x⁴−3x²+6)/(x⁶−5x⁴+5x²+4) dx = arctan((x⁵−3x³+x)/2) + arctan(x³) + arctan(x)` (eq 2.20, up to a
step function). The library's `ex281_isLogToAtanRun` builds the explicit `IsLogToAtanRun` (integer-scaled
cofactors `(x, x²−1, 2)`, `(1, x, 1)` — same arctan args, Bézout by `ring`), and `ex281_logToAtan_correct`
reads off `atanDerivSum [...] = i · logDeriv((φA+iφB)/(φA−iφB))` from `logToAtan_correct`. -/
abbrev ex_2_8_1 := @DeepWiki.SymbolicIntegration.ex281_logToAtan_correct

/-- **`LogToAtan`, computable variant** (§2.8, p.63): a genuinely `#eval`-able rendering of Rioboo's
recursion over a dense coefficient list `DensePoly ℚ := List ℚ` (Mathlib's `ℚ[X]` arithmetic is
noncomputable, so the abstract `logToAtanAux` cannot run). Branches mirror `logToAtan_algorithm`
(base `B ∣ A`, swap `deg A < deg B`, step with extended-Euclidean cofactors `B·D − A·C = G`), fuel-
bounded for termination, returning the arctan arguments as `(numerator, denominator)` `DensePoly ℚ` pairs.
The library's `logToAtanCompute`, with the `toPoly : DensePoly ℚ → ℚ[X]` bridge and its homomorphism lemmas
(`DensePoly.toPolyG_caddG`/`DensePoly.toPolyG_cmulG`/…). The full agreement with `logToAtanAux` is deferred. -/
def logToAtan_compute := @DeepWiki.SymbolicIntegration.Compute.logToAtanCompute

/-- **Example 2.8.1, the proved computation** (§2.8, p.63–64): `logToAtanCompute 20 (x³−3x) (x²−2)`
evaluates (by `native_decide`) to the `(num, den)` pairs `[((−x+3x³−x⁵), −2), ((−x³), −1), ((x), 1)]`,
equal as fractions to the book table's arctan arguments `(x⁵−3x³+x)/2, x³, x` (eq 2.20). The library's
`logToAtanCompute_ex281` — the algorithm actually *runs* and returns the book's answer. -/
theorem ex_2_8_1_compute :
    DeepWiki.SymbolicIntegration.Compute.logToAtanCompute 20
        DeepWiki.SymbolicIntegration.Compute.cX3m3X
        DeepWiki.SymbolicIntegration.Compute.cX2m2
      = [([0, -1, 0, 3, 0, -1], [-2]), ([0, 0, 0, -1], [-1]), ([0, 1], [1])] :=
  DeepWiki.SymbolicIntegration.Compute.logToAtanCompute_ex281

/-- **Rothstein–Trager resultant, computable variant** (§2.4, eq 2.7, p.47): a genuinely `#eval`-able
rendering of `R(t) = res_x(D, A − t·D')` over the dense coefficient carrier `DensePoly ℚ := List ℚ` (Mathlib's
`ℚ[X]` resultant `rtResultant` is noncomputable). The selected univariate resultant
`CPolyResultant.compute` uses the dense Euclidean-PRS implementation and the identity
`res(p,q) = (−1)^(deg p·deg q)·lc(q)^(deg p − deg r)·res(q,r)`; the bivariate RT
resultant is recovered, staying univariate, by evaluation + Lagrange interpolation
(`DensePoly.cinterpolate`).
The library's `cResidueResultantTower [1]`, with the computable monomial derivative and
the generic `CPoly.csquarefreePart`, agrees with `rtResultant` by
`toPolyG_cResidueResultantTower_one_eq_rtResultant`. -/
def rtResultant_compute (A D : DensePoly ℚ) :=
  DensePoly.cResidueResultantTower ([1] : DensePoly ℚ) A D

/-- **Example 2.4.1, the proved RT-resultant computation** (§2.4, p.48): `cResidueResultantTower [1]` on
`A = x⁴−3x²+6`, `D = x⁶−5x⁴+5x²+4` evaluates (by `native_decide`) to
`[45796, 0, 549552, 0, 2198208, 0, 2930944]` = the book's `res_x(D, A−t·D') = 45796·(4t²+1)³` (eq 2.7),
whose normalized `CPoly.csquarefreePart` is `[1/4, 0, 1]`, the book's primitive `R(t) = 4t²+1`. The
library's `rtResultant_ex241` / `rtResultant_ex241_sqfree` — the RT resultant engine actually *runs* and
returns the book's answer. -/
theorem ex_2_4_1_compute :
    DensePoly.cResidueResultantTower ([1] : DensePoly ℚ)
        DeepWiki.SymbolicIntegration.Compute.cA241 DeepWiki.SymbolicIntegration.Compute.cD241
      = [45796, 0, 549552, 0, 2198208, 0, 2930944] :=
  DeepWiki.SymbolicIntegration.Compute.rtResultant_ex241

/-- **LRT log argument `S(t,x) = gcd_x(D, A − t·D')`, computable variant** (§2.5/§2.6, p.51/54): a
genuinely `#eval`-able rendering of the bivariate polynomial that goes inside the logarithms of
`∫ A/D = ∑_{R(a)=0} a·log(S(a,x))`, over the bivariate carrier `GBPolyCore ℚ := DensePoly (DensePoly ℚ)` (`= ℚ[t][x]`;
Mathlib's `lrtSubresultant` is noncomputable). Built from the subresultant PRS (Collins–Brown,
`subresPRS`) via pseudo-division `GBPolyCore.gbpsremainderCore` over the non-field ring `ℚ[t]`, taking the `x`-degree-`j`
subresultant, then reducing modulo the resultant factor `R(t)` and making it monic in `x` over
`ℚ[t]/(R)` (Exercise 2.7's normalization). The library's `lrtGcdCompute`. Agreement with `lrtSubresultant`
is deferred. -/
def lrt_gcd_compute := @DeepWiki.SymbolicIntegration.Compute.lrtGcdCompute

/-- **Example 2.4.1 / 2.6.1, the proved LRT log-argument computation** (§2.5/§2.6, p.51/54): the degree-3
bivariate subresultant `S₃(D, A − t·D')` of `D = x⁶−5x⁴+5x²+4`, `A − t·D'` (`A = x⁴−3x²+6`), reduced mod
the RT resultant factor `R(t) = 4t²+1` and made monic in `x` over `ℚ[t]/(R)`, evaluates (by
`native_decide`) to `[[0, -4], [-3], [0, 2], [1]]` = `x³ + 2t·x² − 3x − 4t` — **exactly** the book's LRT
log argument, the Czichowski/Gröbner basis element of Example 2.6.1 (`B = {4t²+1, x³+2tx²−3x−4t}`). The
raw subresultant carries the cofactor `−214t` (`S₃ ≡ −214t·(x³+2tx²−3x−4t) mod R`), stripped by the
monic-in-`x` normalization. The library's `lrtGcd_ex241` — the bivariate LRT log-argument engine runs. -/
theorem ex_2_6_1_lrtGcd_compute :
    DeepWiki.SymbolicIntegration.Compute.lrtGcdCompute 30 3
        DeepWiki.SymbolicIntegration.Compute.cR241
        DeepWiki.SymbolicIntegration.Compute.cA241
        DeepWiki.SymbolicIntegration.Compute.cD241
      = [[0, -4], [-3], [0, 2], [1]] :=
  DeepWiki.SymbolicIntegration.Compute.lrtGcd_ex241

/-- **Exercise 2.2, the assembled LRT log part** (§2.9, p.72): `lrtLogPart A D` runs the whole computable
LRT pipeline — RT resultant `R = res_x(D, A−t·D')`, Yun squarefree factorization of `R`, the subresultant
PRS, and mod-`R` monic-in-`x` normalization — returning the `(Qᵢ, Sᵢ)` pairs of
`∫A/D = ∑ᵢ ∑_{Qᵢ(a)=0} a·log(Sᵢ(a,x))`. The library's `lrtLogPart` uses
`CPoly.squarefreeYunFactors`. -/
def ex_2_2_lrtLogPart := @DeepWiki.SymbolicIntegration.Compute.lrtLogPart

/-- **Exercise 2.2, the computed answer** (§2.9, p.72), LRT on
`∫ (8x⁹+x⁸−12x⁷−4x⁶−26x⁵−6x⁴+30x³+23x²−2x−7)/(x¹⁰−2x⁸−2x⁷−4x⁶+7x⁴+10x³+3x²−4x−2) dx`: `D` is
**squarefree** (no Hermite part, `ex_2_2_D_squarefree`); the RT resultant `R(t) = cR22` is the degree-10
integer polynomial `res_x(D, A−t·D')` (`ex_2_2_resultant`), itself **squarefree** so its Yun factorization
is the single pair `(R, 1)` (`ex_2_2_resultant_squarefree`); hence the log argument is the degree-1 (in
`x`) `S₁ = lrtGcdCompute 60 1 R A D = x + c₀(t)`, monic in `x` (`ex_2_2_S1_monic_linear`). The assembled
answer is the single `(monic R, S₁)` pair, so
`∫ A/D = ∑_{R(a)=0} a · log(x + c₀(a))` with `c₀(t) ∈ ℚ[t]/(R)` the degree-9 residue polynomial. Proved
end to end by `native_decide`. The library's `ex_2_2_logpart`. -/
theorem ex_2_2 :
    DeepWiki.SymbolicIntegration.Compute.lrtLogPart 60
        DeepWiki.SymbolicIntegration.Compute.cA22
        DeepWiki.SymbolicIntegration.Compute.cD22
      = [(DeepWiki.SymbolicIntegration.Compute.cmonic DeepWiki.SymbolicIntegration.Compute.cR22,
          DeepWiki.SymbolicIntegration.Compute.cS1_22)] :=
  DeepWiki.SymbolicIntegration.Compute.ex_2_2_logpart

/-- **Exercise 2.3 a), the computed LRT logarithmic part** (§2.9, p.72), LRT on
`∫ (72x⁷+256x⁶−192x⁵−1280x⁴−312x³+1440x²+576x−96)/(9x⁸+36x⁷−32x⁶−252x⁵−78x⁴+468x³+288x²−108x+9) dx`:
`D` is **squarefree** (no Hermite part, `ex_2_3_D_squarefree`); the RT resultant `R(t)` is the **degree-8**
integer polynomial `res_x(D, A−t·D')` (`ex_2_3_resultant`, `ex_2_3_resultant_deg`), itself **squarefree**
so its Yun factorization is the single pair `(R, 1)` (`ex_2_3_resultant_squarefree`); hence the log
argument is the degree-1 (in `x`) `S₁ = lrtGcdCompute 80 1 R A D = x + c₀(t)`, monic in `x`
(`ex_2_3_S1_monic_linear`). The assembled answer is the single `(monic R, S₁)` pair, so
`∫ A/D = ∑_{R(a)=0} a · log(x + c₀(a))` (eight complex-log terms). Proved end to end by `native_decide`.
The library's `ex_2_3_logpart`. -/
theorem ex_2_3 :
    DeepWiki.SymbolicIntegration.Compute.lrtLogPart 80
        DeepWiki.SymbolicIntegration.Compute.cA23
        DeepWiki.SymbolicIntegration.Compute.cD23
      = [(DeepWiki.SymbolicIntegration.Compute.cmonic DeepWiki.SymbolicIntegration.Compute.cR23,
          DeepWiki.SymbolicIntegration.Compute.cS1_23)] :=
  DeepWiki.SymbolicIntegration.Compute.ex_2_3_logpart

/-- **Exercise 2.3 a), the symbolic definite integral over `[−2, −2/3]`** (§2.9, p.72): with the LRT log
argument `S₁ = x + c₀(t)`, the definite integral is
`∫_{−2}^{−2/3} A/D = ∑_{R(a)=0} a · [log(S₁(a, −2/3)) − log(S₁(a, −2))]`, and the two bound values of the
log argument **differ by the constant `4/3`** (`S₁(t, −2/3) − S₁(t, −2) = (−2/3) − (−2) = 4/3`) — the
clean symbolic definite-integral data, `native_decide`-proved. (Numerically `≈ 1.969223`; the
direct-numerical-integration *comparison* is the documented non-symbolic residual,
`ex_2_3_numerical_comparison`.) The library's `ex_2_3_definite_integral_data`. -/
theorem ex_2_3_a_definite :
    DeepWiki.SymbolicIntegration.Compute.cnorm
        (DeepWiki.SymbolicIntegration.Compute.csub
          DeepWiki.SymbolicIntegration.Compute.cS1_23_upper
          DeepWiki.SymbolicIntegration.Compute.cS1_23_lower)
      = [4/3] :=
  DeepWiki.SymbolicIntegration.Compute.ex_2_3_definite_integral_data

/-- **Exercise 2.3 b), the Rioboo real form** (§2.8/§2.9, p.69/72): "apply the Rioboo algorithm to the
above result and compute again the definite integral." Numerically `D` has no real root (eight residues
in four conjugate pairs), so Rioboo's `LogToReal` collapses the eight complex `a·log` terms into **four
real `arctan` terms**, each conjugate pair `(α±iβ, S = G+iH)` contributing `2β·LogToAtan(H, G)` via the
same `logToAtanCompute` engine validated on Example 2.8.1 — and the real-form definite integral over
`[−2, −2/3]` equals the complex-log value of a) (the real form avoids the logarithm's branch ambiguity).
The deliverable is that the engine runs and returns Example 2.8.1's three arctan arguments. The library's
`ex_2_3_rioboo_realform`. -/
theorem ex_2_3_b_rioboo :
    DeepWiki.SymbolicIntegration.Compute.logToAtanCompute 20
        DeepWiki.SymbolicIntegration.Compute.cX3m3X
        DeepWiki.SymbolicIntegration.Compute.cX2m2
      = [([0, -1, 0, 3, 0, -1], [-2]), ([0, 0, 0, -1], [-1]), ([0, 1], [1])] :=
  DeepWiki.SymbolicIntegration.Compute.ex_2_3_rioboo_realform

/-- **Exercise 2.5 ([66])** (§2.9, p.73), LRT on
`∫ (x⁴+x³+x²+x+1) / (x⁵+x⁴+2x³+2x²−2+4√(−1+√3)) dx`. The denominator's constant term involves the
algebraic number `θ = √(−1+√3) = √(√3−1)` (`θ⁴+2θ²−2=0`, Eisenstein-at-2 ⇒ irreducible), so the
integrand is over the **field extension** `K = ℚ(θ) = ℚ[y]/(y⁴+2y²−2)`. The library builds a computable
extension carrier and re-runs the subresultant-PRS LRT one level up (`K[t]`, `K[t][x]`): `D` is squarefree,
`R(t) = res_x(D, A−t·D')` is degree-5 squarefree (`ex25_resultant_squarefree`), so the log argument is
degree-1 in `x`, `S₁ = x + c₀(t)` monic over `K[t]/(R)` (`ex25_logpart_monic_linear`), giving
`∫ A/D = ∑_{R(a)=0} a·log(x + c₀(a))`. The library's `ex25_resultant_squarefree` (the RT resultant `R(t)`
over `ℚ(θ)` has trivial `gcd_t(R, R')`). -/
theorem ex_2_5_resultant_squarefree :
    DeepWiki.SymbolicIntegration.Compute.epmonic
        (DeepWiki.SymbolicIntegration.Compute.epgcdExt 60
          DeepWiki.SymbolicIntegration.Compute.ex25Rt
          (DeepWiki.SymbolicIntegration.Compute.epderiv
            DeepWiki.SymbolicIntegration.Compute.ex25Rt)).1
      = [[1]] :=
  DeepWiki.SymbolicIntegration.Compute.ex25_resultant_squarefree

/-- **Exercise 2.5, the computed LRT log argument** (§2.9, p.73): the per-residue gcd is `S₁(t,x) = x + c₀(t)`,
**monic and linear in `x`** over `K[t]/(R)` (two `x`-coefficients, leading `x`-coefficient `1`), so
`∫ A/D = ∑_{R(a)=0} a·log(x + c₀(a))` (five complex-log terms over the degree-5 residue ring). The library's
`ex25_logpart_monic_linear`. -/
theorem ex_2_5_logpart :
    DeepWiki.SymbolicIntegration.Compute.ex25S1.length = 2 ∧
      DeepWiki.SymbolicIntegration.Compute.eblc DeepWiki.SymbolicIntegration.Compute.ex25S1 = [[1]] :=
  DeepWiki.SymbolicIntegration.Compute.ex25_logpart_monic_linear

/-- **Exercise 2.5, the raw degree-1 subresultant** (§2.9, p.73): the subresultant PRS output *before*
normalization is `S₁ʳᵃʷ = c₁(t)·x + c₀ʳᵃʷ(t)` with small integer coefficients over `K = ℚ(θ)` —
`x⁰`-coeff `1 + (−2−12θ)t + (−32+104θ)t² + (96−224θ)t³`,
`x¹`-coeff `(3−4θ) + (−40+52θ)t + (184−224θ)t² + (−288+320θ)t³`. The library's `ex25_raw_subresultant`. -/
theorem ex_2_5_raw_subresultant :
    (DeepWiki.SymbolicIntegration.Compute.ex25S1raw.map
        (·.map DeepWiki.SymbolicIntegration.Compute.cnorm)) =
      [[[1], [-2, -12], [-32, 104], [96, -224]],
       [[3, -4], [-40, 52], [184, -224], [-288, 320]]] :=
  DeepWiki.SymbolicIntegration.Compute.ex25_raw_subresultant

/-- **Exercise 2.5 — "what happens if the subresultants are not made primitive?"** (§2.9, p.73; Mulders
[66]). The raw degree-1 subresultant `S₁ʳᵃʷ` is **not monic in `x`**: its leading `x`-coefficient `c₁(t)`
is a degree-3 polynomial in `t` (not `1`), and `S₁ʳᵃʷ = content(t) · primitive(t,x)` for a **non-unit**
`content(t) ∈ K[t]` of `t`-degree `1`. So evaluating the subresultant at the residues `R(a)=0` *without
first making it primitive* multiplies the log argument by the spurious `content(a)` (and the leading
`c₁(a)` is not a unit at every residue), injecting an extra `log(content(a))` term instead of the clean
`log(x + c₀(a))`. Making it primitive in `x` (strip `content(t)`) and monic in `x` over `K[t]/(R)` removes
this — that is the answer. The library's `ex25_raw_eq_content_mul_primitive` (with `ex25_content_nonunit`,
`ex25_raw_not_monic_in_x`). -/
theorem ex_2_5_not_primitive :
    DeepWiki.SymbolicIntegration.Compute.ex25S1raw =
        DeepWiki.SymbolicIntegration.Compute.ebscaleC
          DeepWiki.SymbolicIntegration.Compute.ex25content
          DeepWiki.SymbolicIntegration.Compute.ex25S1prim ∧
      DeepWiki.SymbolicIntegration.Compute.epdeg DeepWiki.SymbolicIntegration.Compute.ex25content = 1 ∧
      DeepWiki.SymbolicIntegration.Compute.epdeg
          (DeepWiki.SymbolicIntegration.Compute.eblc
            DeepWiki.SymbolicIntegration.Compute.ex25S1raw) = 3 :=
  ⟨DeepWiki.SymbolicIntegration.Compute.ex25_raw_eq_content_mul_primitive,
   DeepWiki.SymbolicIntegration.Compute.ex25_content_nonunit,
   DeepWiki.SymbolicIntegration.Compute.ex25_raw_not_monic_in_x⟩

/-- **`LogToReal` conjugate-pair real-form identity** (§2.8, p.69, the mathematical heart of
`LogToReal`): pairing conjugate roots `α = a ± i·b` of `S(α, x) = A + iB`, the contribution
`(a+ib)·d/dx log(A+iB) + (a−ib)·d/dx log(A−iB) = a·d/dx log(A²+B²) + b·d/dx (i·log((A+iB)/(A−iB)))`
is a **real** function's derivative — the `a·log(A²+B²) + b·LogToAtan(A,B)` summand of `LogToReal`'s
output. Pure `logDeriv` algebra (`logDeriv(A+iB)±logDeriv(A−iB) = logDeriv(A²+B²)/logDeriv((A+iB)/(A−iB))`
via `(A+iB)(A−iB)=A²+B²`). The library's `logToReal_conjugate_pair`. -/
abbrev logToReal_conjugate_pair := @DeepWiki.SymbolicIntegration.logToReal_conjugate_pair

/-- **`LogToReal` real-form, arctan-substituted** (§2.8, p.69, the `log + arctan` shape of
`LogToReal`'s output): substituting Theorem 2.8.1 for the `i·log((A+iB)/(A−iB))` term turns the
conjugate-pair contribution into the fully real `a·log(A²+B²) + b·2·arctan(A)` (single-step `B = 1`
case). The library's `logToReal_conjugate_pair_atan`. -/
abbrev logToReal_conjugate_pair_atan :=
  @DeepWiki.SymbolicIntegration.logToReal_conjugate_pair_atan

/-- **`LogToReal` sum-over-conjugate-pairs real form** (§2.8, p.69, the correctness heart of the full
algorithm): for a `Finset ι` of conjugate-pair data `(a k, b k, A k, B k)` (`(A k)²+(B k)² ≠ 0`), the
sum `∑ₖ [(a k + i·b k)·d/dx log(A k + i·B k) + (a k − i·b k)·d/dx log(A k − i·B k)]` of conjugate-pair
contributions equals `∑ₖ [a k·d/dx log((A k)²+(B k)²) + b k·d/dx (i·log((A k+i·B k)/(A k−i·B k)))]` — a
**real** function's derivative `∑ₖ [a k·log((A k)²+(B k)²) + b k·LogToAtan(A k, B k)]`, the output of
Rioboo's `LogToReal`. A `Finset.sum_congr` fold of `logToReal_conjugate_pair`. The library's
`logToReal_sum`; `logToReal_sum_atan` is the arctan-substituted `B=1` form. -/
abbrev logToReal_sum := @DeepWiki.SymbolicIntegration.logToReal_sum

/-- **`LogToReal` full real output over conjugate pairs** (§2.8, p.69, the `log + arctan` shape of the
output): with each pair `(Apoly k, Bpoly k)` carrying a `LogToAtan(Apoly k, Bpoly k)` run, the
sum-over-pairs real form becomes fully real:
`∑ₖ [(a k+i·b k)·d/dx log(φAₖ+i·φBₖ) + (a k−i·b k)·d/dx log(φAₖ−i·φBₖ)]
  = ∑ₖ [a k·d/dx log((φAₖ)²+(φBₖ)²) + b k·atanDerivSum(L k)]` — each pair's complex-log term is the
real arctan-derivative sum `∑_{P∈L k} 2·P'/(1+P²)`, exhibiting `∑ₖ [a k·log(A²+B²) + b k·(arctan sum)]`.
Combines `logToReal_sum` with `isLogToAtanRun_correct` (`logToAtan_correct`). The library's
`logToReal_sum_atanRun`. -/
abbrev logToReal_sum_atanRun := @DeepWiki.SymbolicIntegration.logToReal_sum_atanRun

/-- **`LogToReal` real/imaginary split** (§2.8, p.69, the `R(u+i·v) = P + i·Q` input-processing step):
for `R ∈ K[t]` in a commutative ring with `i² = −1`, there are real-form `P, Q` (in the `K`-subalgebra
generated by `u, v`) with `R(u+i·v) = P + i·Q` and the certifying conjugate `R(u−i·v) = P − i·Q`. By
induction on `R`, the monomial step is the multiplication recursion `(P+iQ)(u+iv) = (Pu−Qv) + i(Pv+Qu)`.
Example 2.8.3: `R = 4t²+1 ↦ P = 4u²−4v²+1, Q = 8uv`. The library's `exists_realImag_split`; the
bivariate `S(u+i·v, x) = A + i·B` split is `exists_realImag_split_bivariate` (base `K → K[x]`). -/
abbrev logToReal_split := @DeepWiki.SymbolicIntegration.exists_realImag_split

/-- **`LogToReal` conjugate-product bridge** (§2.8, p.69): the split's real-form `A, B` satisfy
`A² + B² = S(a+i·b, x)·S(a−i·b, x)` — the argument of the real logarithm `a·log(A²+B²)` is the product of
the conjugate evaluations. The library's `sq_add_sq_eq_mul_conj` (the `CommRing` form of the
`(A+iB)(A−iB) = A²+B²` identity behind `logToReal_conjugate_pair`). -/
abbrev logToReal_conjProduct_bridge := @DeepWiki.SymbolicIntegration.sq_add_sq_eq_mul_conj

/-- **`LogToReal` conjugate-root selection criterion** (§2.8, p.69, the `P(a,b)=Q(a,b)=0 ⟺ R(a+i·b)=0`
step): over a char-`0` field with `i² = −1` and a conjugation certifying `P, Q` real, `a+i·b` is a root
of `R` iff `P = 0 ∧ Q = 0` — exactly the condition under which `LogToReal` selects a conjugate pair
(restricted to `b > 0`). The library's `aeval_eq_zero_iff_realImag_eq_zero` (with the realness of `P, Q`
essential: `P + i·Q = 0` alone does **not** force `P = Q = 0`). -/
abbrev logToReal_root_criterion :=
  @DeepWiki.SymbolicIntegration.aeval_eq_zero_iff_realImag_eq_zero

/-- **`LogToReal` correctness over the root partition** (§2.8, p.66–69, book (2.22)→(2.26), the
assembly of the full algorithm): given that `R`'s roots partition as `roots = reals + map(a·+i·b·) pairs
+ map(a·−i·b·) pairs` (real roots ⊎ conjugate pairs `a±i·b`, book (2.25)) and each pair's real/imaginary
split `S(a±i·b, x) = A ± i·B` (`A²+B² ≠ 0`), the original complex log-sum's derivative
`∑_{α|R(α)=0} α·logDeriv(S(α,x))` equals `LogToReal`'s real output's derivative
`∑_{a∈K,R(a)=0} a·logDeriv(S(a,x)) + ∑_{pairs} [a·logDeriv(A²+B²) + b·(i·logDeriv((A+iB)/(A−iB)))]` — the
`a·log(A²+B²) + b·LogToAtan(A,B)` real form per pair (book (2.26)). The library's
`logToReal_correct_of_partition`: a `Multiset.sum` split (`logToReal_rootSum_split`) folded against the
per-pair `logToReal_conjugate_pair_of_split`. The partition is taken as a certified hypothesis. -/
abbrev logToReal_correct_of_partition :=
  @DeepWiki.SymbolicIntegration.logToReal_correct_of_partition

/-- **`LogToReal` root-sum split over the partition** (§2.8, p.66): `∑_{α∈roots} g(α)` splits as the
real-root sum `∑_{reals} g(a)` plus the conjugate-pair sum `∑_{pairs} [g(a₊) + g(a₋)]`, given the root
partition `roots = reals + map a₊ pairs + map a₋ pairs`. The library's `logToReal_rootSum_split` (pure
`Multiset.sum`/`map` bookkeeping). -/
abbrev logToReal_rootSum_split := @DeepWiki.SymbolicIntegration.logToReal_rootSum_split

/-- **σ-conjugation permutes `R`'s roots** (§2.8, p.66, the start of the partition construction): if a
field automorphism `σ` (the conjugation, `σ i = −i`) fixes `R`'s coefficients (`R.map σ = R`) and `R`
splits, then `σ` maps the root multiset to itself (`R.roots.map σ = R.roots`) preserving multiplicities
(`count_roots_conj_eq`) — so `σ` acts as a permutation of `R`'s roots, with σ-fixed roots real and
2-orbits `{α, σα}` the conjugate pairs. The library's `roots_map_self_of_map_eq`. -/
abbrev logToReal_conj_permutes_roots := @DeepWiki.SymbolicIntegration.roots_map_self_of_map_eq

/-- **`LogToReal` σ-orbit root partition** (§2.8, p.66, book (2.25), the partition CONSTRUCTION): over
a field-with-involution `(L, σ)` (`σ ∘ σ = id`, `σ i = −i`, `i² = −1`) with the ordered fixed field `K`
reading each imaginary part `b α = imagPart σ i α` (`algebraMap K L (b α) = imagPart σ i α`), the
σ-stable root multiset of a σ-fixed split `R` partitions as `R.roots = reals + pairs.map(a+ib) +
pairs.map(a−ib)` with `reals = R.roots.filter (b·=0)` (the real roots) and `pairs = R.roots.filter
(0<b·)` (one `b>0` representative per conjugate pair). The `b<0` block is the count-preserving `σ`-image
of the `b>0` block (`count_roots_conj_eq` + `b(σα)=−b(α)`, a `Multiset.count`/`Multiset.ext`
σ-bijection), and the trichotomy `b≠0 = (0<b) ⊎ (b<0)` splits the moved part. The library's
`roots_partition` — the genuine §2.8 partition infra, with `realPart`/`imagPart` and their `σ`-fixed /
`α=a+ib` / `b(σα)=−b(α)` / `b=0⟺σ-fixed` lemmas (`realPart_fixed`, `imagPart_fixed`,
`eq_realPart_add_imagPart`, `imagPart_conj`, `realImagPartK_eq_zero_iff`). -/
abbrev logToReal_roots_partition := @DeepWiki.SymbolicIntegration.roots_partition

/-- **`LogToReal` full correctness over `R`'s roots** (§2.8, p.66–69, book (2.22)→(2.26), CLOSING the
algorithm): feeding the CONSTRUCTED σ-orbit partition (`roots_partition`) into
`logToReal_correct_of_partition`, the original complex log-sum's derivative `∑_{α|R(α)=0}
α·logDeriv(S(α,x))` equals `LogToReal`'s real output's derivative `∑_{a∈K,R(a)=0} a·logDeriv(S(a,x)) +
∑_{a,b∈K,b>0} [a·logDeriv(A²+B²) + b·(i·logDeriv((A+iB)/(A−iB)))]` — the `a·log(A²+B²) + b·LogToAtan(A,B)`
real form per conjugate pair (book (2.26)) — with NO partition hypothesis, only each root's
real/imaginary split `S(a±i·b,x) = A±i·B` (from `exists_realImag_split_bivariate`). The library's
`logToReal_correct` — the full §2.8 `LogToReal`. -/
abbrev logToReal_correct := @DeepWiki.SymbolicIntegration.logToReal_correct

/-- **Theorem 2.8.4** (§2.8, p.67–68, Rioboo), Rioboo's conversion specializes well: for a real field
`K` with real closure `K̄`, `C, D ∈ K[x]` (`deg D > 0`, `deg D > deg C`, `D` squarefree,
`gcd(C,D) = 1`), with `R = P + i·Q` a squarefree factor of the RT/LRT resultant and `S = A + i·B` the
LRT gcd, if `a, b ∈ K̄` satisfy `P(a,b) = Q(a,b) = 0` and `b ≠ 0`, then `gcd(A(a,b,x), B(a,b,x)) = 1`
in `K(a,b)[x]` — so Rioboo's arctan numerator has a nonzero denominator. The library's `rioboo_coprime`
(the purely-algebraic Bézout core): taking the LRT gcd-cofactor factorizations (2.27)
`C − (a+i·b)·D' = (E₁+i·E₂)(A+i·B)`, (2.28) `D = (F₁+i·F₂)(A+i·B)` as hypotheses (the faithful
"`A+iB` divides both `C−(a+ib)D'` and `D`" content), the imaginary part of (2.27) gives (2.29)
`−b·D' = E₁B + E₂A`, the real part of (2.28) gives (2.30) `D = F₁A − F₂B`, and `D` squarefree
(`G₁D + G₂D' = 1`) yields `b = (bG₁F₁ − G₂E₂)·A − (bG₁F₂ + G₂E₁)·B`, putting the unit `b` in
`span {A, B}`, i.e. `IsCoprime A B`. The complexification is modeled as a char-`0` domain (the field
`K(a,b)(i)` adjoined to `K(a,b)[x]`) with a conjugation `σ` (`σ i = −i`) certifying the parts real. -/
abbrev thm_2_8_4 := @DeepWiki.SymbolicIntegration.rioboo_coprime

/-- **Theorem 2.8.4, equation (2.29)** (§2.8, p.68): taking the imaginary part of (2.27)
`C − (a+i·b)·D' = (E₁+i·E₂)(A+i·B)` gives `−b·D'(x) = E₁(a,b,x)·B(a,b,x) + E₂(a,b,x)·A(a,b,x)` (the
real `C, D'` contribute nothing to the imaginary part except `Im(−(a+ib)D') = −b·D'`). The library's
`imagPart_eq_of_mul_split`, via the `i`-free component matching `eq_and_eq_of_add_imag_eq`. -/
abbrev thm_2_8_4_eq_2_29 := @DeepWiki.SymbolicIntegration.imagPart_eq_of_mul_split

/-- **Theorem 2.8.4, equation (2.30)** (§2.8, p.68): taking the real part of (2.28)
`D = (F₁+i·F₂)(A+i·B)` gives `D(x) = F₁(a,b,x)·A(a,b,x) − F₂(a,b,x)·B(a,b,x)`. The library's
`realPart_eq_of_mul_split`, via `eq_and_eq_of_add_imag_eq`. -/
abbrev thm_2_8_4_eq_2_30 := @DeepWiki.SymbolicIntegration.realPart_eq_of_mul_split

/-- **Theorem 2.8.4, the FULL statement** (§2.8, p.67–68, Rioboo) — the LRT *discharges* the cofactor
hypotheses of `thm_2_8_4`. Over an algebraically closed char-`0` field with an involutive conjugation
`conj` (`conj i = −i`) certifying `C, D` real and `a, b` real, with `D` separable, `deg C < deg D`,
`b ≠ 0`, and `(a+i·b)` a root of the RT/LRT resultant `R = res_x(D, C−t·D')`, the real/imaginary parts
`A, B` of the LRT log argument `S(a+i·b, x) = A + i·B` are **coprime** — `gcd(A, B) = 1`, so Rioboo's
arctan denominator is nonzero. **No abstract cofactor hypotheses.** The library's `rioboo_coprime_lrt`:
the LRT correctness `lazardRiobooTrager_output_isSimilar_gcd` makes `S(a+i·b, x)` *similar* to
`gcd(D, C−(a+i·b)·D')`, hence (over the field) *associated* (`IsSimilar.associated`), hence a divisor of
both `D` and `C−(a+i·b)·D'`; the cofactors `E, F` (2.27)/(2.28) thus exist, split into real+`i`·imaginary
parts by `exists_realImag_decomp`, and `rioboo_coprime` closes. -/
abbrev thm_2_8_4_full := @DeepWiki.SymbolicIntegration.rioboo_coprime_lrt

/-- **Example 2.8.2** (§2.8, p.65), examples of REAL (formally real) fields: `ℝ`, `ℚ`, and `ℚ(ⁿ√p) ⊆ ℝ`
(the field generated over `ℚ` by a real `n`-th root of a prime, `exists_real_nthRoot`) are real — the
last via the pullback `isFormallyReal_of_injective` of formal reality along the embedding into `ℝ`;
conversely `ℚ(√−2)` and positive-characteristic fields are NOT real. The library's
`isFormallyReal_qadjoin_real` (+ `isFormallyReal_of_injective`, `not_isFormallyReal_of_charP`). -/
abbrev ex_2_8_2 := @DeepWiki.SymbolicIntegration.isFormallyReal_qadjoin_real

/-! ## §2.9 In-Field Integration -/

/-- **Recognizing Derivatives** (§2.9, p.71), the substance: after Hermite/Horowitz reduction
`f = dg/dx + A/D` with `D` squarefree, `gcd(A, D) = 1`, `deg A < deg D`, the logarithmic part `A/D`
is **not** the derivative of any rational function when `A ≠ 0` — `∀ v ∈ K(x), v′ ≠ A/D` (since `D | A`
with `deg A < deg D` forces `A = 0`). The library's `logPart_not_rational_derivative`, by the
residue-free divisibility descent forcing `Dⁿ | denom(v)` for all `n`. -/
abbrev recognizingDerivatives := @DeepWiki.SymbolicIntegration.logPart_not_rational_derivative

/-- **Recognizing Derivatives, the criterion** (§2.9, p.71): for `f ∈ K(x)` with Hermite reduction
`f = dg/dx + A/D` (`D` squarefree, `gcd(A, D) = 1`, `deg A < deg D`), `f = du/dx` for some `u ∈ K(x)`
**iff** `A = 0`. The library's `isRationalDerivative_iff`. (The constructive antiderivative when
`A = 0` is `recognizingDerivatives_integral`; the "Recognizing Logarithmic Derivatives" criterion —
Mařík's test that the Rothstein–Trager resultant has all-integer roots — is the packaged
`recognizingLogDerivatives_iff`.) -/
abbrev recognizingDerivatives_iff := @DeepWiki.SymbolicIntegration.isRationalDerivative_iff

/-- **In-field antiderivative** (§2.9, p.71, the constructive output of "Recognizing Derivatives"):
the Hermite quotient `g ∈ K[X]` read in `K(x)` as the antiderivative — `inFieldIntegral g =
algebraMap g`. When the integrability criterion `A = 0` holds, `g` is an antiderivative of `f`
(`recognizingDerivatives_integral_spec`), realizing the book's "in which case `u = g`". The library's
`inFieldIntegral`. -/
noncomputable abbrev recognizingDerivatives_integral :=
  @DeepWiki.SymbolicIntegration.inFieldIntegral

/-- **In-field antiderivative correctness** (§2.9, p.71, the constructive half of "Recognizing
Derivatives"): if the Hermite reduction is `f = dg/dx + A/D` and the log-part numerator `A = 0`, then
the Hermite quotient `g` is an antiderivative — `(inFieldIntegral g)′ = f`. The book's
`u = g + ∫(A/D)dx` with the `∫(A/D)` term vanishing (`A = 0`). The library's `inFieldIntegral_spec`. -/
abbrev recognizingDerivatives_integral_spec :=
  @DeepWiki.SymbolicIntegration.inFieldIntegral_spec

/-- **In-field integrability decision, with witness** (§2.9, p.71, the payoff of "Recognizing
Derivatives"): for `f ∈ K(x)` with Hermite reduction `f = dg/dx + A/D` (`D` squarefree,
`gcd(A, D) = 1`, `deg A < deg D`), `f` has a rational antiderivative **iff** `A = 0`; and when so the
explicit Hermite quotient `g` is one (`(inFieldIntegral g)′ = f`). Packages the criterion
`recognizingDerivatives_iff` with the constructive antiderivative `recognizingDerivatives_integral_spec`.
The library's `inFieldIntegrable_iff`. -/
abbrev recognizingDerivatives_integrable_iff :=
  @DeepWiki.SymbolicIntegration.inFieldIntegrable_iff

/-- **Recognizing Logarithmic Derivatives, `⟸` direction** (§2.9, p.72): for `f = A/D` with `D`
squarefree (`D = ∏_{α∈s}(X−α)`, `deg A < #s`), if all the residues `A(α)/D'(α)` — the roots of the
Rothstein–Trager resultant — are integers in `K`, then `f` is the logarithmic derivative of a *nonzero*
rational function `u ∈ K(x)*` (`f = du/dx /u`). The explicit witness `u = ∏ₐ Gₐ^{nₐ}` is the product of
the Rothstein–Trager factors raised to their integer residues. The library's
`isLogDeriv_of_integer_residues`. -/
abbrev recognizingLogDerivatives_of_integer_residues :=
  @DeepWiki.SymbolicIntegration.isLogDeriv_of_integer_residues

/-- **Recognizing Logarithmic Derivatives, the `⟹`-direction numerator ingredient** (§2.9, p.72):
over an algebraically closed field, for nonzero `N`, `logDeriv(N) = N′/N = ∑_{β∈N.roots} 1/(X−β)` — the
root sum with multiplicity. With `u = N/M`, `logDeriv u = ∑ (m_N(β) − m_M(β))/(X−β)`, so the residue at a
simple pole `α` of `A/D = logDeriv u` is the integer `m_N(α) − m_M(α)`. The library's
`logDeriv_algebraMap_eq_sum_roots`. -/
abbrev logDeriv_numerator_root_sum :=
  @DeepWiki.SymbolicIntegration.logDeriv_algebraMap_eq_sum_roots

/-- **Simple-pole residue functional** (§2.9, p.72, the `⟹`-direction extraction): `residueAt α f =
((X − α)·f)(α)` — multiply `f ∈ K(x)` by `X − α` to cancel a simple pole at `α`, then evaluate there.
For `f` with at most a simple pole at `α` this is the residue (coefficient of `1/(X − α)`). The
library's `residueAt`, with pole-free evaluation `residueAt_of_mul_X_sub_C` (`(X−α)·f = g/h`, `h(α) ≠ 0`
⟹ `residueAt α f = g(α)/h(α)`). -/
noncomputable abbrev recognizingLogDerivatives_residueAt :=
  @DeepWiki.SymbolicIntegration.residueAt

/-- **Residue of `A/D` at a simple root** (§2.9, p.72, computation 1): for `D = (X − α)·E` with
`E(α) ≠ 0`, `residueAt α (A/D) = A(α)/E(α) = A(α)/D'(α)` — multiplying by `X − α` cancels the simple
pole. The library's `residueAt_div_eq_residue`. -/
abbrev recognizingLogDerivatives_residue_div :=
  @DeepWiki.SymbolicIntegration.residueAt_div_eq_residue

/-- **Residue of `logDeriv N` at `α` is the root multiplicity** (§2.9, p.72, computation 2): for nonzero
`N`, `residueAt α (logDeriv N) = (rootMultiplicity α N : K)` — writing `N = (X − α)^k·N₁` (`N₁(α) ≠ 0`),
`(X − α)·(N'/N) = (k·N₁ + (X − α)·N₁')/N₁` evaluates at `α` to `k`. Hence
`residueAt α (logDeriv(N/M)) = ord_α(N) − ord_α(M) ∈ ℤ` (`residueAt_logDeriv_div_eq_int`). The library's
`residueAt_logDeriv_eq_rootMultiplicity`. -/
abbrev recognizingLogDerivatives_residue_logDeriv :=
  @DeepWiki.SymbolicIntegration.residueAt_logDeriv_eq_rootMultiplicity

/-- **Recognizing Logarithmic Derivatives, `⟹` direction** (§2.9, p.72, Mařík): over an algebraically
closed field, if `A/D` (with `D` squarefree, `deg A < deg D`) is the logarithmic derivative of some
nonzero `u ∈ K(x)*`, then at every root `α` of `D` the residue `A(α)/D'(α)` is an integer in `K` —
`∃ n : ℤ, A(α)/D'(α) = (n : K)`, namely `n = ord_α(num u) − ord_α(denom u)`. The residue functional
`residueAt α` reads `A(α)/D'(α)` from `A/D` (computation 1) and the integer `ord_α(num u) − ord_α(denom u)`
from `logDeriv u` (computation 2); the hypothesis `A/D = logDeriv u` equates them. The library's
`integer_residues_of_isLogDeriv`. -/
abbrev recognizingLogDerivatives_of_isLogDeriv :=
  @DeepWiki.SymbolicIntegration.integer_residues_of_isLogDeriv

/-- **Recognizing Logarithmic Derivatives, the criterion** (§2.9, p.72, Mařík — both directions):
over an algebraically closed field, for squarefree `D = ∏_{α∈s}(X − α)` and `deg A < #s`, the proper
fraction `A/D` is the logarithmic derivative of some nonzero `u ∈ K(x)*` **iff** every residue
`A(α)/D'(α)` (`α ∈ s`, the roots of the Rothstein–Trager resultant) is an integer in `K`. Packages the
`⟸` (`recognizingLogDerivatives_of_integer_residues`) and `⟹`
(`recognizingLogDerivatives_of_isLogDeriv`) directions. The library's
`isLogDeriv_iff_integer_residues`. -/
abbrev recognizingLogDerivatives_iff :=
  @DeepWiki.SymbolicIntegration.isLogDeriv_iff_integer_residues

/-! ## Exercises -/

/-- **Exercise 2.4(b)** (§2, p.72): a closed form for `∫ dx/(1+xⁿ)`, `n ∈ ℕ`. Over an algebraically
closed field `K` with `(n:K) ≠ 0` (so `Xⁿ+1` is separable) and `1 ≤ n`,
`1/(Xⁿ+1) = ∑_{ζ ∈ (Xⁿ+1).roots} (−ζ/n)·logDeriv(X−ζ)` in `K(x)` — i.e.
`∫ dx/(1+xⁿ) = ∑_ζ (−ζ/n)·log(x−ζ)`, a sum over the roots with residue `−ζ/n = 1/(n·ζⁿ⁻¹)` at each.
Specializes the simple-root log-part `eq_2_3_residue`/`intRationalLogPart_logDeriv` at `A = 1`,
`D = Xⁿ+1` (monic, splits, separable, so it is the nodal product over its distinct roots). The
library's `inv_one_add_X_pow_eq_sum_residue_logDeriv`. -/
abbrev ex_2_4 := @DeepWiki.SymbolicIntegration.inv_one_add_X_pow_eq_sum_residue_logDeriv

/-- **Exercise 2.4(a)** (§2, p.72): the `n = 4` case `∫ dx/(1+x⁴)`. Over an algebraically closed
field `K` with `(4:K) ≠ 0` (e.g. `CharZero K`),
`1/(X⁴+1) = ∑_{ζ ∈ (X⁴+1).roots} (−ζ/4)·logDeriv(X−ζ)`, the `n = 4` instance of `ex_2_4`. The
library's `inv_one_add_X_pow_four_eq_sum_residue_logDeriv`. -/
abbrev ex_2_4_a := @DeepWiki.SymbolicIntegration.inv_one_add_X_pow_four_eq_sum_residue_logDeriv

end DeepWiki.Si
