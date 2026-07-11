import DeepWiki.SymbolicIntegration.Engine.Parametric
import DeepWiki.ComputableAlgebra.LinearAlgebraRatCorrect
import Sources.Doi_10_1007_b138171.Source

/-! # Symbolic Integration catalog — Chapter 7: Parametric Problems
The parametric Risch differential equation, the limited-integration problem, and the parametric
logarithmic-derivative problem (used for coupled systems and for deciding elementarity). The three
boxes of this chapter are now rendered as **computable** algorithms over the base monomial ℚ[t] / the
tower (`DeepWiki.SymbolicIntegration.Engine.Parametric`), each with `ccompute` evidence on a
worked book example.

**Computable-vs-abstract.** Each algorithm below is a computable function (the parametric solve
reducing to a constant linear system over `Const(k) = ℚ` via `CLinearSolve.nullspaceBasis`), validated by
`ccompute` on the book's example (matching the book's constraint matrix / kernel, or checking the
returned constant tuple *actually satisfies* the eq. 7.6 constraint); the *abstract* correctness
theorems (`Dy + fy = Σ cᵢgᵢ ↔ …`, Thm 7.1.1/7.1.2, Cor 7.2.1, Lemma 7.3.1) are **NOT** proved. The
full §7.3 logarithmic-derivative-of-a-radical construction (the witness `v`), the §7.1
hypertangent/nonlinear cancellation cases (needing the Ch. 8 coupled system), and the §7.2 Corollary
7.2.1 back-substitution remain deferred.

## NOT YET FORMALIZED (audit 2026-06-24)
§7.1 The Parametric Risch Differential Equation: Thm 7.1.1, Thm 7.1.2; Cor 7.1.1; Lemma 7.1.1,
  Lemma 7.1.2; Ex 7.1.2, Ex 7.1.3, Ex 7.1.4, Ex 7.1.5, Ex 7.1.6 (abstract correctness; the algorithm
  `ParamRDE` — `LinearConstraints` + the constant linear solve `ConstantSystem` — is now computable +
  ccompute-validated on Ex 7.1.1, see `alg_7_1_paramRischDE`/`ex_7_1_1`). The genuine-tower case
  (matrix entries in ℚ(x), Lemma 7.1.2's row-differentiation reduction to ℚ) and the
  hypertangent/nonlinear cancellation cases are deferred.
§7.2 The Limited Integration Problem: Thm 7.2.1; Cor 7.2.1; Ex 7.2.1, Ex 7.2.2 (abstract correctness +
  the Cor 7.2.1 back-substitution; the algorithm `LimitedIntegrate` is now computable +
  ccompute-validated as the `gᵢ = Dwᵢ/wᵢ` specialization of `ParamRDE`, see
  `alg_7_2_limitedIntegrate`/`ex_7_2_limitedIntegrate`).
§7.3 The Parametric Logarithmic Derivative Problem: Lemma 7.3.1; Ex 7.3.1 (abstract correctness + the
  full logarithmic-derivative-of-a-radical construction; the recognizer
  `ParametricLogarithmicDerivative` is now computable + ccompute-validated on Ex 7.3.2, see
  `alg_7_3_paramLogDeriv`/`ex_7_3_2` — the reachable base-field case decided directly, the radical
  witness `v` deferred).
Exercise 7.1.

The remaining gaps are the **abstract correctness theorems** (the parametric solvers are
computationally rendered and example-validated but not proved correct), the full §7.3 radical-witness
construction, the genuine-tower §7.1 case and its hypertangent/nonlinear cancellation, and the §7.2
Corollary 7.2.1 back-substitution to a nonparametric RDE. -/

open DeepWiki.SymbolicIntegration DeepWiki.SymbolicIntegration.DensePoly

namespace DeepWiki.Si

/-! ## §7.1 The Parametric Risch Differential Equation — computable + validated -/

/-- **Algorithm `ParamRDE`** (§7.1, the `ParamRischDE(f, [g₁,…,gₘ], D)` pipeline, p.217), base case:
the computable `CPoly.paramRischDE fuel gnums gdens` over the base monomial ℚ[t] (`D = d/dt`,
`Const(k) = ℚ`), returning a **basis** of the ℚ-linear subspace of constant tuples `(c₁,…,cₘ)` for
which `Dp = Σᵢ cᵢ·gᵢ` has a polynomial solution — via `LinearConstraints` (eq. 7.6) and the constant
linear solve `CLinearSolve.nullspaceBasis` (`ConstantSystem`, Lemma 7.1.2). Computable + `ccompute`-validated;
abstract correctness deferred. -/
def alg_7_1_paramRischDE := @CPoly.paramRischDE

/-- **Example 7.1.1** (§7.1, the `LinearConstraints`/`ConstantSystem` boxes, p.223/224): for
`Dp = c₁·(2t³+3t+1)/(t²−1) + c₂/(t−1) + c₃/(t+1)`, `CPoly.linearConstraintsQ` returns the homogeneous matrix
`[[5,1,1],[1,1,-1]]` (eq. 7.10) and `CPoly.paramRischDE` returns a one-vector kernel basis proportional to
`(1,−3,−2)`, each verified to satisfy the eq. 7.6 constraint (`ccompute`). -/
abbrev ex_7_1_1 := @paramRischDE_example

/-! ## §7.2 The Limited Integration Problem — computable + validated -/

/-- **Algorithm `LimitedIntegrate`** (§7.2, the `LimitedIntegrate(f, [w₁,…,wₘ], D)` problem, p.245):
the computable `CPoly.limitedIntegrate fuel fnum fden wnums wdens` over the base monomial ℚ[t], deciding
`f = Dv + Σᵢ cᵢ·log(wᵢ)` as the `gᵢ = Dwᵢ/wᵢ` specialization of `CPoly.paramRischDE` (with `f` the forced
generator), returning the basis of admissible constant tuples. Computable + `ccompute`-validated;
abstract correctness and the Cor 7.2.1 back-substitution deferred. -/
def alg_7_2_limitedIntegrate := @CPoly.limitedIntegrate

/-- **Example (§7.2, p.245)**: for `f = 1/t`, `w₁ = t`, `w₂ = t+1`, `CPoly.limitedIntegrate` returns a
nonempty constant kernel basis, each satisfying the eq. 7.6 constraint, finding the relation
`f = log(t)` — the limited-integral certificate that `∫ f = log(t)` (`ccompute`). -/
abbrev ex_7_2_limitedIntegrate := @limitedIntegrate_example

/-! ## §7.3 The Parametric Logarithmic Derivative Problem — computable + validated -/

/-- **Algorithm `ParametricLogarithmicDerivative`** (§7.3, p.253): the computable
`CFrac.paramLogDeriv fuel fval θlogderiv` over the base field — deciding `n·f = Dv/v + m·Dθ/θ` for integers
`n ≠ 0, m` and `v ∈ k(t)*`, returning `(n, m, v)` data or `none` via Lemma 7.3.1's candidate-`c = m/n`
heuristic. The reachable base-field/constant case is decided directly; the full radical witness `v`
(the §5.12 construction) is the documented continuation. Computable + `ccompute`-validated;
abstract correctness deferred. -/
noncomputable abbrev alg_7_3_paramLogDeriv := @CFrac.paramLogDeriv

/-- **Example 7.3.2** (§7.3, the `ParametricLogarithmicDerivative` box, p.253/254): for
`11 = Dv/v + m·Dθ/θ` with `Dθ/θ = 1` (`θ = eᵗ`) over `k = ℚ`, `CFrac.paramLogDeriv` returns `(n, m, v) =
(1, 11, 1)`, verified to actually satisfy `n·f = Dv/v + m·(Dθ/θ)` by the cleared difference
(`ccompute`). -/
abbrev ex_7_3_2 := @paramLogDeriv_example

/-! ## The constant linear solve `ConstantSystem` (Lemma 7.1.2 over `Const(k) = ℚ`) — abstract correctness -/

/-- **`ConstantSystem` solve correctness** (§7.1, Lemma 7.1.2 specialized to the base constants
`Const(k) = ℚ`, where the row-echelon reduction is ordinary ℚ-Gaussian elimination): the unique-solution
solver `cConstSolveUniqueQ Arows urhs ncols` (the `crref` Gauss–Jordan + back-substitution) is **abstractly
correct** — if it returns `some x` then `x` solves the ℚ-linear system `A·x = b` rowwise. Proved
`ccompute`-free via the solution-preserving and reduced-echelon `crref` invariants
(`ComputableLinearSolveCorrect`). The solution-set correctness underlying the §7.1/§7.3 constant solve. -/
abbrev alg_7_1_constSystem_solve_sound := @LawfulCLinearSolve.solveUnique_sound

end DeepWiki.Si
