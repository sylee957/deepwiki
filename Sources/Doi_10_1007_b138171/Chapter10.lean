import DeepWiki.SymbolicIntegration.Engine.Parallel
import Sources.Doi_10_1007_b138171.Source

/-! # Symbolic Integration catalog — Chapter 10: Parallel Integration
The parallel (Risch–Norman) integration method added in the second edition: instead of peeling off one
transcendental generator at a time, it integrates *all generators at once* by guessing the log arguments
and the rational-part shape and solving an inhomogeneous **linear system over the constants** (the strong
Liouville form `f = Dv + Σ cᵢ Duᵢ/uᵢ`, eq. 10.1). The §10.3 `ParallelIntegrate(f, D)` box is now rendered
as a **computable** algorithm over the base monomial field `k = ℚ`, the field `ℚ(t)`
(`DeepWiki.SymbolicIntegration.Engine.Parallel`): Yun squarefree factorization (the candidate log
arguments), the eq. 10.6 linear system, and the particular-solution solve, validated on `t = x`,
`t = exp x` integrands and on the documented **heuristic failure**.

**Computable-vs-abstract.** Each algorithm below is a computable function over `CPoly ℚ` (= ℚ(t))
validated by `native_decide` on a worked integrand (checking the returned `∫f = b/s + Σ cⱼ log pⱼ`
*actually satisfies* `D(∫f) = f` via the cleared identity `num·d − a·den = 0`); abstract correctness
(that a returned ansatz solution satisfies (10.1)) is **NOT** proved. The method is **heuristic, not
algorithmic** — `none` means "no elementary integral *in this guess*", not a proof of non-elementarity
(book p.298). The genuine multivariate tower `ℚ(x)[t]` (the special-polynomial list `S^irr_{K:F}` +
irreducible factorization over `F̄`, Thm 10.2.1/10.2.2), §10.1 multivariate `SplitFactor`, and §10.4
simple-differential-field exponent bounds remain deferred.

## NOT YET FORMALIZED (audit 2026-06-24)
§10.1 Derivations of Polynomial Rings: Thm 10.1.1, Thm 10.1.2; Lemma 10.1.1;
  Ex 10.1.1, Ex 10.1.2. (`Differential.implicitDeriv` / `Derivation.mapCoeffs` are the relevant
  Mathlib foundation, already used in §3.4. The multivariate `SplitFactor`/`SplitSquarefreeFactor` of
  this section is out of scope of the base-field engine.)
§10.2 Structure of Elementary Antiderivatives: Thm 10.2.1, Thm 10.2.2; Lemma 10.2.1 (the eq. 10.2 shape
  of an elementary integral and the special-polynomial list `S^irr_{K:F}` for monomial towers — needed
  for the genuine tower; the base-field guess `s = ∏ dⱼ^{j-1}` + squarefree-factor log candidates is
  realized below).
§10.3 The Integration Method: Ex 10.3.2, Ex 10.3.4 (the genuine-tower worked examples; the heuristic
  parallel algorithm `ParallelIntegrate(f, D)` is now computable + native_decide-validated over the base
  monomial field `k = ℚ` on the Examples 10.3.1/10.3.3-style integrands, see
  `alg_10_3_parallelIntegrate`/`alg_10_3_squarefreeFactors`/`alg_10_3_parallelIntegrateTower`/
  `ex_10_3_log`/`ex_10_3_exp`/`ex_10_3_mixed`/`ex_10_3_failure`).
§10.4 Simple Differential Fields: Def 10.4.1; Thm 10.4.1; Cor 10.4.1; Lemma 10.4.1 (the
  simple-differential-field exponent bounds — out of scope of the base-field engine). -/

open DeepWiki.SymbolicIntegration DeepWiki.SymbolicIntegration.CPoly

namespace DeepWiki.Si

/-! ## §10.3 The Integration Method `ParallelIntegrate` — computable + validated -/

/-- **Yun squarefree factorization over `ℚ[t]`** (§10.3 step 2, the `(d₁,…,dₑ)` of the candidate log
arguments): the computable `cSquarefreeFactorsQ p = [(d₁,1),…,(dₑ,e)]`, the monic squarefree factors
of `p` with their multiplicities, `p ~ ∏ⱼ dⱼ^j`, pairwise coprime and squarefree. -/
def alg_10_3_squarefreeFactors := @cSquarefreeFactorsQ

/-- **Parallel (Risch–Norman) integration over `ℚ(t)`** (§10.3, the `ParallelIntegrate(f, D)` box, book
p.309): the computable `cParallelIntegrate Dt a d` over `k = ℚ`, the monomial `t` with derivative
`Dt ∈ ℚ[t]`, `D = Dt·d/dt`. For `f = a/d ∈ ℚ(t)` it builds the ansatz `∫f = b/s + Σⱼ cⱼ log(pⱼ)`
(`{pⱼ}` = squarefree factors of `d`, `s = ∏ dⱼ^{j-1}`, `b` a bounded-degree undetermined numerator),
forms the eq. 10.6 inhomogeneous linear system and solves it (`cConstSolveAnyQ`). Returns
`some ((b, s), [(cⱼ, pⱼ)])` or `none` (`"failed"` — the guess does not capture an elementary integral;
heuristic, so `none` is *not* a non-elementarity proof). Computable + `native_decide`-validated; abstract
correctness deferred. -/
def alg_10_3_parallelIntegrate := @cParallelIntegrate

/-- **Parallel integration over the tower `ℚ(x)[t]`** (§10.3, the genuine-tower signature): the
computable `cParallelIntegrateTower Dt a d` over `a d : CPoly (QFunNZ ℚ)`. The base-field case (`Dt, a,
d` all with `ℚ`-constant coefficients, so `k = ℚ`) is routed through `cParallelIntegrate` and lifted back
to `QFunNZ ℚ` coefficients; a genuine `x`-dependent coefficient (the full tower, needing the §10.2
special-polynomial list + `F̄`-factorization) returns `none` — the documented continuation. -/
def alg_10_3_parallelIntegrateTower := @cParallelIntegrateTower

/-- **Example (§10.3, book p.309)**, pure log, `t = x` (`Dt = 1`): `cParallelIntegrate` on
`∫ 2t/(t²+1) dt` over `ℚ(t)` returns `some res` whose reconstructed `∫f = b/s + Σ cⱼ log pⱼ` is verified
to **actually satisfy** `D(res) = 2t/(t²+1)` by the cleared identity `cParallelCheckQ`; the ansatz
recovers `log(t²+1)`, `native_decide`. -/
abbrev ex_10_3_log := @parallelIntegrate_log_example

/-- **Example (§10.3, book p.309)**, transcendental, `t = exp x` (`Dt = t`): `cParallelIntegrate` on
`∫ exp(x)/(exp(x)+1)² dx` (`f = t/(t+1)²` over `ℚ(exp x)`) returns the rational part `−1/(t+1)`, verified
to **actually satisfy** `D(res) = t/(t+1)²` by `cParallelCheckQ` — the parallel virtue of handling the
generator `t = exp x` directly (`Dt ≠ 1`), `native_decide`. -/
abbrev ex_10_3_exp := @parallelIntegrate_exp_example

/-- **Example (§10.3, book p.309)**, mixed rational + log, `t = exp x` (`Dt = t`): `cParallelIntegrate`
on `∫ (exp(x)²+2exp(x))/(exp(x)+1)² dx` (`f = (t²+2t)/(t+1)²`) produces in one linear solve **both** the
rational part `−1/(t+1)` and the log `log(t+1)`, verified to **actually satisfy** `D(res) =
(t²+2t)/(t+1)²` by `cParallelCheckQ` — the full Liouville shape (10.1) recovered in one parallel step,
`native_decide`. -/
abbrev ex_10_3_mixed := @parallelIntegrate_mixed_example

/-- **Example (§10.3, book p.298)**, the heuristic *fails*: `cParallelIntegrate` on `∫ 1/(exp(x)+1) dx`
returns `none` — the antiderivative `x − log(exp x+1)` needs the generator `x = ∫1` outside `ℚ(exp x)`,
so the eq. 10.6 system is inconsistent (`native_decide`). The chapter's key caveat: the method is
*heuristic*, and `none` means "no elementary integral **in this guess**", not a non-elementarity proof. -/
abbrev ex_10_3_failure := @parallelIntegrate_failure_example

end DeepWiki.Si
