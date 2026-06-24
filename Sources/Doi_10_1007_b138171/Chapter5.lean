import DeepWiki.SymbolicIntegration.ComputableHermiteTower
import DeepWiki.SymbolicIntegration.ComputablePolyPartTower
import DeepWiki.SymbolicIntegration.ComputableLogPartTower
import Sources.Doi_10_1007_b138171.Source

/-! # Symbolic Integration catalog — Chapter 5: Integration of Transcendental Functions
The core Risch integration algorithm for a single transcendental monomial extension. The
**degree- and multiplicity-lowering reductions** of this chapter — Hermite (§5.3), the polynomial
reduction (§5.4), the residue-criterion logarithmic part (§5.6), and the primitive-case reduced
integration (§5.8) — are now rendered as **computable** algorithms over the monomial tower ℚ(x)[t]
(`DeepWiki.SymbolicIntegration.Computable*`), each with `native_decide` evidence on a worked book
example. The chapter rests on Chapters 3–4 (differential/monomial extensions, the order function and
the Rothstein–Trager resultant) and is the heart of the book.

**Computable-vs-abstract.** Each algorithm below is a computable function over `CPolyG QFunNZ`
(= ℚ(x)[t]) validated by `native_decide` on the book's example (the cleared reduction identity
`D(g) + h = f` etc.); the *abstract* correctness theorems (that `g` is the integral's rational part,
Theorems 5.3.1/5.4.1/5.6.1/5.8.1) are **NOT** proved. Liouville's theorem (§5.5), the full
hyperexponential case (§5.9), the hypertangent case (§5.10), and the structural §5.7/§5.11/§5.12
theory remain unformalized.

## NOT YET FORMALIZED (audit 2026-06-24)
§5.1 Elementary and Liouvillian Extensions: Def 5.1.1 (elementary/primitive/hyperexponential
  monomial), Def 5.1.2 (Liouvillian), Def 5.1.3, Def 5.1.4; Thm 5.1.1, Thm 5.1.2; Lemma 5.1.2.
§5.2 Outline and Scope of the Integration Algorithm: Ex 5.2.1, Ex 5.2.2.
§5.3 The Hermite Reduction (transcendental): Thm 5.3.1 (abstract correctness; the algorithm
  `HermiteReduce` is now computable + native_decide-validated, see `alg_5_3_hermiteReduce`/`ex_5_3_1`).
§5.4 The Polynomial Reduction: Thm 5.4.2 (abstract correctness; Thm 5.4.1 + algorithm
  `PolynomialReduce` now computable + native_decide-validated, see `alg_5_4_polynomialReduce`/`ex_5_4_1`).
§5.5 Liouville's Theorem: Thm 5.5.1, Thm 5.5.2, Thm 5.5.3.
§5.6 The Residue Criterion: Thm 5.6.1 (abstract correctness); Lemma 5.6.1, Lemma 5.6.2; Ex 5.6.1,
  Ex 5.6.3 (the algorithm `ResidueReduce` / the residue resultant + log argument are now computable +
  native_decide-validated on Ex 5.6.2, see `alg_5_6_residueResultant`/`alg_5_6_logArg`/`ex_5_6_2`).
§5.7 Integration of Reduced Functions: Thm 5.7.1, Thm 5.7.2.
§5.8 The Primitive Case: Thm 5.8.1 (abstract correctness; the algorithm `IntegratePrimitive`
  degree-lowering loop, constant-coefficient sub-case, is now computable + native_decide-validated,
  see `alg_5_8_primitivePolyIntegrate`/`ex_5_8_primitive`). The full `LimitedIntegrate` solve for the
  coefficient antiderivatives is the deferred Chapter-7 oracle.
§5.9 The Hyperexponential Case: Thm 5.9.1; Lemma 5.9.1; algorithm `IntegrateHyperexponential`.
§5.10 The Hypertangent Case: Def 5.10.1; Thm 5.10.1, Thm 5.10.2; Lemma 5.10.1;
  Ex 5.10.1, Ex 5.10.2, Ex 5.10.3; algorithm `IntegrateHypertangent`.
§5.11 The Nonlinear Case with no Specials: Cor 5.11.1; Ex 5.11.1, Ex 5.11.2.
§5.12 In-Field Integration: Lemma 5.12.1.
Exercises: Ex 5.1, Ex 5.2, Ex 5.3, Ex 5.4, Ex 5.5, Ex 5.6.

The remaining gaps are the **abstract correctness theorems** (the reductions above are computationally
rendered but not proved correct), Liouville's structure theory (§5.5), the full hyperexponential/
hypertangent integration (§5.9–§5.10), and the structural §5.7/§5.11/§5.12 results. -/

open DeepWiki.SymbolicIntegration DeepWiki.SymbolicIntegration.CPolyG

namespace DeepWiki.Si

/-! ## §5.3 The Hermite Reduction (transcendental) — computable + validated -/

/-- **Algorithm `HermiteReduce`** (§5.3, p.139, quadratic version): the computable transcendental
Hermite reduction `cHermiteReduceTower Dt fuel a d = ((gnum, gden), (h_num, h_den))` over the tower
ℚ(x)[t], rewriting the normal part `f = a/d` as `D(g) + h` with `h_den` squarefree, for the monomial
derivation `D = κ_D + Dt·d/dt`. Computable + `native_decide`-validated; abstract correctness (Thm
5.3.1) deferred. -/
noncomputable abbrev alg_5_3_hermiteReduce := @cHermiteReduceTower

/-- **Example 5.3.1** (§5.3, p.139): `cHermiteReduceTower` on `f = 1/t²` (`Dt = t²+1`, `t = tan x`)
satisfies the Hermite identity `D(g) + h = f` over ℚ(x)[t] (cleared form, `native_decide`); the
multiplicity-`2` factor `t` is lowered to the squarefree residual denominator `t`. -/
abbrev ex_5_3_1 := @hermiteTower_example

/-! ## §5.4 The Polynomial Reduction — computable + validated -/

/-- **Algorithm `PolynomialReduce`** (§5.4, p.141): the computable polynomial reduction
`cPolyReduceTower Dt fuel p = (q, r)` for a nonlinear monomial `t` (`δ(t) = deg(Dt) ≥ 2`), splitting
`p ∈ k[t]` as `p = D(q) + r` with `deg(r) < δ(t)` by peeling the leading term whose monomial
derivative cancels the top. Computable (generic over `[CField α] [CDiffField α]`) +
`native_decide`-validated (Thm 5.4.1); abstract correctness deferred. -/
noncomputable abbrev alg_5_4_polynomialReduce := @cPolyReduceTower

/-- **Example 5.4.1** (§5.4, p.141): `cPolyReduceTower` reduces `p = t³` (`Dt = t²+1`, `t = tan x`,
`δ = 2`) to `(q, r) = ((1/2)t², −t)` satisfying `D(q) + r = p` with `deg(r) = 1 < δ` over ℚ(x)[t]
(`native_decide`). -/
abbrev ex_5_4_1 := @polyReduceTower_example

/-! ## §5.6 The Residue Criterion — computable + validated -/

/-- **Algorithm `ResidueReduce`** (§5.6, p.151), the residue resultant: the computable
`cResidueResultantTower Dt fuel a d = R(z) = res_t(d, a − z·Dd) ∈ ℚ(x)[z]` over the tower, by the
evaluation + Lagrange-interpolation template, whose roots are the residues of the logarithmic part of
`∫ a/d`. Computable + `native_decide`-validated; abstract correctness (Thm 5.6.1) deferred. -/
noncomputable abbrev alg_5_6_residueResultant := @cResidueResultantTower

/-- **Algorithm `ResidueReduce`** (§5.6, p.151), the log argument: the computable
`cLogArgTower Dt fuel a d c = gcd_t(d, a − c·Dd) ∈ ℚ(x)[t]` over the tower — the polynomial inside
`log` for a residue `c`, so `∑_c c·log(cLogArgTower … c)` is the logarithmic part of `∫ a/d`.
Computable + `native_decide`-validated; abstract correctness deferred. -/
noncomputable abbrev alg_5_6_logArg := @cLogArgTower

/-- **Example 5.6.2** (§5.6, p.151–152): for `∫ (2t²−t−x²)/(t³−x²t) dx`, `t = log x`, `Dt = 1/x`, the
residue resultant `cResidueResultantTower` has monic part `z³−xz²−z/4+x/4` (the book's `r` up to a
ℚ(x) scalar) and the log arguments `cLogArgTower … (±1/2) = t ± x` (the residues `±1/2`), all checked
over ℚ(x)[t] (`native_decide`). -/
abbrev ex_5_6_2 := @logPartTower_example

/-! ## §5.8 The Primitive Case — computable + validated (constant-coefficient sub-case) -/

/-- **Algorithm `IntegratePrimitive`** (§5.8, p.158), the degree-lowering loop: the computable
`cPrimitivePolyIntegrate Dt fuel p = (q, rem)` for a primitive monomial `t` (`Dt ∈ k`, `δ(t) = 0`,
e.g. `t = log x`), integrating `p = ∑ aᵢtⁱ` top-down in the constant-coefficient sub-case (`b = 0`,
`c = aₘ/((m+1)·Dt)`) so `D(q) + rem = p`. The full `LimitedIntegrate` solve for the coefficient
antiderivatives is the deferred Chapter-7 oracle. Computable + `native_decide`-validated; abstract
correctness (Thm 5.8.1) deferred. -/
noncomputable abbrev alg_5_8_primitivePolyIntegrate := @cPrimitivePolyIntegrate

/-- **Example (§5.8, p.158)**, primitive case: `cPrimitivePolyIntegrate` on `p = (log x)²/x = (1/x)·t²`
(`t = log x`, `Dt = 1/x`) returns `q = (1/3)t³` with `rem = 0`, satisfying `D(q) + rem = p` over
ℚ(x)[t] (`native_decide`) — i.e. `∫ (log x)²/x dx = (log x)³/3`. -/
abbrev ex_5_8_primitive := @primitivePolyIntegrate_example

end DeepWiki.Si
