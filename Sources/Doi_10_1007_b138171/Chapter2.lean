import DeepWiki.SymbolicIntegration.RationalIntegration
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms
import DeepWiki.SymbolicIntegration.RationalIntegrationExamples
import DeepWiki.SymbolicIntegration.PartialFraction
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
§2.2: DONE. The `HermiteReduce` algorithm is fully formalized — reduction step (`hermiteReduce_step` /
  `hermiteReduce_step_ratFunc`), prime-power inner loop (`hermiteReducePower` / `hermiteReducePower_spec`),
  two-factor and multi-factor partial fractions (`ratFunc_partialFraction_coprime` /
  `ratFunc_partialFraction_prod`), and the complete outer algorithm `hermiteReduce_full`
  (`A/D = g′ + ∑ᵢ rᵢ/Dᵢ` for `D = ∏ Dᵢ^{eᵢ}`) — and all three worked traces on the octic example are
  verified: `ex_2_2_1` (original/partial-fraction), `ex_2_2_2` (quadratic), `ex_2_2_3` (Mack's linear),
  sharing result `ex_2_3_1`.
§2.3: the *functional linear solve* for the degree-bounded `B, C` (set up and solve the linear system
  `B′·D* − B·E + C·D⁻ = A` over `K`) [functional/infra: needs a linear-system solver layer]. Done: the
  denominator split `horowitzOstrogradsky_split` (= `hoSplit`, `(gcd(D,D'), D/gcd(D,D'))`) with
  `hoSplit_mul` (`D⁻·D* = D`) and `hoSplit_snd_squarefree` (`D*` squarefree radical); the key divisibility
  `horowitzOstrogradsky_dvd` (`D⁻ ∣ D⁻′·D*`, so the Horowitz `E` exists); and the reduction identity
  `horowitzReduce_step_ratFunc` (`A/(D⁻·D*) = (B/D⁻)′ + C/D*` given a solution; abstract form
  `horowitz_reduction_step`). (Ex 2.3.1's *result* — shared with Ex 2.2.1 — is `ex_2_3_1`.)
§2.4: Thm 2.4.1(iii) [external: splitting-field minimality, proved in Chaps 4/5]; the Rothstein–Trager
  algorithm's *residue-grouped* log-sum `∑_{a|R(a)=0} a·log(Gₐ)` (combining equal-residue roots via the
  per-residue `Gₐ`) [functional: needs the residue partition]. Parts (i),(ii) are PROVED: `thm_2_4_1_i`
  (= `residue_iff_resultant_eq_zero`) and `thm_2_4_1_ii` (= `isRoot_gcd_iff_residue`); the two primitives
  are functional defs `intRationalLogPart_resultant`/`_gcd`; and the *simple-root* logarithmic part is now
  explicit — `intRationalLogPart_logDeriv` (`A/D = ∑_{α|D=0} (A(α)/D'(α))·logDeriv(X−α)`).
§2.5: Thm 2.5.1 [research: subresultant-multiplicity proof, rests on Thms 1.4.1/1.4.3/1.5.1/1.5.2];
  the Lazard–Rioboo–Trager algorithm [functional].
§2.6: Thm 2.6.1 [infra: Gröbner bases in K[x,t], not in Mathlib]; the Czichowski algorithm
  [infra: Gröbner bases].
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

/-- **Logarithmic part as a `logDeriv` sum** (§2.4, the integral exhibited as logarithms): for squarefree
`D = ∏_{α∈s}(X−α)` and `deg A < #s`, `A/D = ∑_{α∈s} (A(α)/D'(α))·logDeriv(X−α)` in `K(x)`, so
`∫ A/D = ∑ (A(α)/D'(α))·log(X−α)` — the explicit (simple-root) Rothstein–Trager logarithmic part, each
`1/(X−α)` being `logDeriv(X−α)`. The library's `ratFunc_eq_sum_residue_logDeriv`. -/
abbrev intRationalLogPart_logDeriv :=
  @DeepWiki.SymbolicIntegration.ratFunc_eq_sum_residue_logDeriv

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

/-! ## §2.5 The Lazard–Rioboo–Trager Algorithm -/

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
