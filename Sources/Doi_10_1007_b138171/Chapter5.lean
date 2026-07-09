import DeepWiki.SymbolicIntegration.Engine.PolyPartTower
import DeepWiki.SymbolicIntegration.Engine.Tower.Integrate
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDE
import DeepWiki.SymbolicIntegration.Engine.IntegratorAssembly
import Sources.Doi_10_1007_b138171.Source

/-! # Symbolic Integration catalog — Chapter 5: Integration of Transcendental Functions
The core Risch integration algorithm for a single transcendental monomial extension. The
**degree- and multiplicity-lowering reductions** of this chapter — Hermite (§5.3), the polynomial
reduction (§5.4), the residue-criterion logarithmic part (§5.6), and the primitive-case reduced
integration (§5.8) — are now rendered as **computable** algorithms over the monomial tower ℚ(x)[t]
(`DeepWiki.SymbolicIntegration.Engine*`), each with `native_decide` evidence on a worked book
example. The chapter rests on Chapters 3–4 (differential/monomial extensions, the order function and
the Rothstein–Trager resultant) and is the heart of the book.

**Computable-vs-abstract.** Each algorithm below is a computable function validated by `native_decide`
on the book's example (the cleared reduction identity `D(g) + h = f` etc.); the *abstract* correctness
theorems (that `g` is the integral's rational part, Theorems 5.3.1/5.4.1/5.6.1/5.8.1) are **NOT**
proved. Liouville's theorem (§5.5) is partly formalized — the transcendental *logarithmic* case
(conditional on the new-monomial condition) and the rational case (§2.4/§2.5) are in catalog
`Sources.Doi_10_1007_b138171.Liouville`; the exp-extension instance and the general structure theorem
remain (see the block below). The full hyperexponential case (§5.9), the hypertangent case (§5.10), and the
structural §5.7/§5.11/§5.12 theory remain unformalized.

**Carrier: the generic ℚ(x).** The §5.3 Hermite and §5.6 residue-criterion reductions are aliased to the
canonical **generic** engine at `α = CFrac ℚ` (the recursive `Frac(ℚ[x])`, every instance bottoming at
ℚ with no hand-built piece), the same carrier as the §6 RDE pipeline. The §5.4 polynomial reduction
(`cPolyReduceTower`) and §5.8 primitive integration (`cPrimitivePolyIntegrate`) are already
`[CField α] [CDiffField α]`-**generic** decls (no separate `…G` rename needed), aliased at the generic
level and instantiable at `CFrac ℚ` like the rest of the engine.

## NOT YET FORMALIZED (audit 2026-06-24)
§5.1 Elementary and Liouvillian Extensions: Def 5.1.1 (elementary/primitive/hyperexponential
  monomial), Def 5.1.2 (Liouvillian), Def 5.1.3, Def 5.1.4; Thm 5.1.1, Thm 5.1.2; Lemma 5.1.2.
§5.2 Outline and Scope of the Integration Algorithm: Ex 5.2.1, Ex 5.2.2.
§5.3 The Hermite Reduction (transcendental): Thm 5.3.1 (abstract correctness; the algorithm
  `HermiteReduce` is now computable + native_decide-validated, see `alg_5_3_hermiteReduce`/`ex_5_3_1`).
§5.4 The Polynomial Reduction: Thm 5.4.2 (abstract correctness; Thm 5.4.1 + algorithm
  `PolynomialReduce` now computable + native_decide-validated, see `alg_5_4_polynomialReduce`/`ex_5_4_1`).
§5.5 Liouville's Theorem: Thm 5.5.2, Thm 5.5.3 (the general structure theorem — every elementary
  antiderivative is `g + ∑ cᵢ log uᵢ`, and the tower-exhaustiveness "no such form ⟹ not elementary" —
  `[research]`); the exp-extension Liouville instance `IsLiouville F F(exp u)` `[external]` (in flight).
  (Thm 5.5.1, the transcendental *logarithmic* case `IsLiouville F F(log u)`, is now formalized
  CONDITIONAL on the new-monomial condition `log u ∉ F` (the necessary transcendence hypothesis), see
  catalog `Sources.Doi_10_1007_b138171.Liouville` `liouville_logExtension`; the rational case §2.4/§2.5 is
  cataloged there too, unconditionally.)
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
rendered but not proved correct), the remainder of Liouville's structure theory (§5.5 — the exp-extension
instance and the general structure theorem; the rational + transcendental-log cases are formalized, the
latter conditional on the new-monomial condition, in `Sources.Doi_10_1007_b138171.Liouville`), the full
hyperexponential/hypertangent integration (§5.9–§5.10), and the structural §5.7/§5.11/§5.12 results. -/

open DeepWiki.SymbolicIntegration DeepWiki.SymbolicIntegration.CPoly

namespace DeepWiki.Si

/-! ### Generic-carrier input builders (catalog-local)

The §5 smoke examples over the generic ℚ(x) = `CFrac ℚ` carrier read their ℚ(x) coefficients as
num/den lists over `CPoly ℚ = List ℚ`. These builders (`qConst5`/`qFrac5`) wrap a num/den pair as a
`CFrac ℚ` element (the `ComputableTowerRefoundProbe` construction). They are catalog infrastructure, not
book items. -/

/-- A ℚ constant `n ∈ ℚ ⊂ ℚ(x)` as a `CFrac ℚ` element (denominator `[1]` nonzero, by
`cisZeroG_one_singleton`, so it holds under a parametric definition). -/
def qConst5 (n : ℚ) : CFrac ℚ := ⟨([n], [(1 : ℚ)]), CFrac.cisZeroG_one_singleton⟩

/-- A ℚ(x) fraction `num/den` as a `CFrac ℚ` element, with `den ≠ 0` discharged by `native_decide`. -/
def qFrac5 (num den : List ℚ) (h : CPoly.cisZero den = false := by native_decide) : CFrac ℚ :=
  ⟨(num, den), h⟩

/-! ## §5.3 The Hermite Reduction (transcendental) — computable + validated -/

/-- **Algorithm `HermiteReduce`** (§5.3, p.139, quadratic version): the fuel-free computable transcendental
Hermite reduction `cHermiteReduceTower Dt a d = ((gnum, gden), (h_num, h_den))` (the canonical generic
engine, here at the generic ℚ(x) = `CFrac ℚ`) over the tower ℚ(x)[t], rewriting the normal part `f = a/d`
as `D(g) + h` with `h_den` squarefree, for the monomial derivation `D = κ_D + Dt·d/dt`. Computable +
`native_decide`-validated; abstract correctness (Thm 5.3.1) deferred. -/
noncomputable abbrev alg_5_3_hermiteReduce := cHermiteReduceTower (α := CFrac ℚ)

/-- **Example 5.3.1** (§5.3, p.139): `cHermiteReduceTower` on `f = 1/t²` (`Dt = t²+1`, `t = tan x`)
satisfies the Hermite identity `D(g) + h = f` over the generic ℚ(x)[t] (cleared form, `native_decide`);
the multiplicity-`2` factor `t` is lowered to the squarefree residual denominator `t`. -/
theorem ex_5_3_1 :
    (let Dt : CPoly (CFrac ℚ) := [qConst5 1, qConst5 0, qConst5 1]      -- `Dt = t²+1`
     let a : CPoly (CFrac ℚ) := [qConst5 1]                           -- `a = 1`
     let d : CPoly (CFrac ℚ) := [qConst5 0, qConst5 0, qConst5 1]       -- `d = t²`
     let res := CPoly.cHermiteReduceTower Dt a d
     let gnum := res.1.1; let gden := res.1.2
     let hNum := res.2.1; let hDen := res.2.2
     let Dgnum := CPoly.cmonomialDeriv Dt gnum
     let Dgden := CPoly.cmonomialDeriv Dt gden
     let gprimeNum := CPoly.csub (CPoly.cmul Dgnum gden) (CPoly.cmul gnum Dgden)
     let gden2 := CPoly.cmul gden gden
     -- `D(g) + h − f = 0` ⟺ `(gprimeNum·h_den + h_num·gden²)·d = a·(gden²·h_den)`
     let lhs := CPoly.cmul
       (CPoly.cadd (CPoly.cmul gprimeNum hDen) (CPoly.cmul hNum gden2)) d
     let rhs := CPoly.cmul a (CPoly.cmul gden2 hDen)
     CPoly.cisZero (CPoly.csub lhs rhs)) = true := by native_decide

/-! ## §5.4 The Polynomial Reduction — computable + validated -/

/-- **Algorithm `PolynomialReduce`** (§5.4, p.141): the computable polynomial reduction
`cPolyReduceTower Dt fuel p = (q, r)` for a nonlinear monomial `t` (`δ(t) = deg(Dt) ≥ 2`), splitting
`p ∈ k[t]` as `p = D(q) + r` with `deg(r) < δ(t)` by peeling the leading term whose monomial
derivative cancels the top. Computable (generic over `[CField α] [CDiffField α]`) +
`native_decide`-validated (Thm 5.4.1); abstract correctness deferred. *(Already a generic decl — no
`…G`-suffixed mirror is needed; here pinned at the generic ℚ(x) = `CFrac ℚ` like the rest of the
engine.)* -/
noncomputable abbrev alg_5_4_polynomialReduce := @cPolyReduceTower (CFrac ℚ)

/-- **Example 5.4.1** (§5.4, p.141): `cPolyReduceTower` reduces `p = t³` (`Dt = t²+1`, `t = tan x`,
`δ = 2`) to `(q, r) = ((1/2)t², −t)` satisfying the §5.4 reduction identity `D(q) + r = p` with the
remainder `t`-degree `deg(r) = 1 < δ = 2` over the generic ℚ(x)[t] (`native_decide`). -/
theorem ex_5_4_1 :
    (let Dt : CPoly (CFrac ℚ) := [qConst5 1, qConst5 0, qConst5 1]       -- `Dt = t²+1`
     let p : CPoly (CFrac ℚ) := [qConst5 0, qConst5 0, qConst5 0, qConst5 1]  -- `p = t³`
     let res := CPoly.cPolyReduceTower Dt 8 p
     let q := res.1; let r := res.2
     let Dq := CPoly.cmonomialDeriv Dt q
     -- `D(q) + r − p = 0` and the reduced remainder has `t`-degree `1 < δ(t) = 2`
     CPoly.cisZero (CPoly.csub (CPoly.cadd Dq r) p) = true
       ∧ CPoly.cdeg r = 1) := by native_decide

/-! ## §5.6 The Residue Criterion — computable + validated -/

/-- **Algorithm `ResidueReduce`** (§5.6, p.151), the residue resultant: the computable
`cResidueResultantTower Dt a d = R(z) = res_t(d, a − z·Dd) ∈ ℚ(x)[z]` (the canonical generic
engine, here at the generic ℚ(x) = `CFrac ℚ`) over the tower, by the evaluation + Lagrange-
interpolation template, whose roots are the residues of the logarithmic part of `∫ a/d`. Computable +
`native_decide`-validated; abstract correctness (Thm 5.6.1) deferred. -/
noncomputable abbrev alg_5_6_residueResultant := cResidueResultantTower (α := CFrac ℚ)

/-- **Algorithm `ResidueReduce`** (§5.6, p.151), the log argument: the computable
`cLogArgTower Dt a d c = gcd_t(d, a − c·Dd) ∈ ℚ(x)[t]` (the generic engine at the generic ℚ(x) =
`CFrac ℚ`) over the tower — the polynomial inside `log` for a residue `c`, so
`∑_c c·log(cLogArgTower … c)` is the logarithmic part of `∫ a/d`. Computable +
`native_decide`-validated; abstract correctness deferred. -/
noncomputable abbrev alg_5_6_logArg := cLogArgTower (α := CFrac ℚ)

/-- **Example 5.6.2** (§5.6, p.151–152): for `∫ (2t²−t−x²)/(t³−x²t) dx`, `t = log x`, `Dt = 1/x`, the
residue resultant `cResidueResultantTower` has monic part `z³−xz²−z/4+x/4` (the book's `r` up to a
ℚ(x) scalar) and the log arguments `cLogArgTower … (±1/2) = t ± x` (the residues `±1/2`), all checked
over the generic ℚ(x)[t] (`native_decide`). -/
theorem ex_5_6_2 :
    (let Dt : CPoly (CFrac ℚ) := [qFrac5 [1] [0, 1]]                       -- `Dt = 1/x`
     let a : CPoly (CFrac ℚ) := [qFrac5 [0, 0, -1] [1], qConst5 (-1), qConst5 2]  -- `a = 2t²−t−x²`
     let d : CPoly (CFrac ℚ) := [qConst5 0, qFrac5 [0, 0, -1] [1], qConst5 0, qConst5 1]  -- `d = t³−x²t`
     let resMonic : CPoly (CFrac ℚ) :=                                    -- `z³−xz²−z/4+x/4`
       [qFrac5 [0, 1] [4], qConst5 (-1/4), qFrac5 [0, -1] [1], qConst5 1]
     let argPlus : CPoly (CFrac ℚ) := [qFrac5 [0, 1] [1], qConst5 1]        -- `t + x`
     let argMinus : CPoly (CFrac ℚ) := [qFrac5 [0, -1] [1], qConst5 1]      -- `t − x`
     CPoly.cisZero (CPoly.csub
         (CPoly.cmonic (CPoly.cResidueResultantTower Dt a d)) resMonic)
     ∧ CPoly.cisZero (CPoly.csub (CPoly.cLogArgTower Dt a d (qConst5 (1/2))) argPlus)
     ∧ CPoly.cisZero (CPoly.csub (CPoly.cLogArgTower Dt a d (qConst5 (-1/2))) argMinus))
    := by native_decide

/-! ## §5.8 The Primitive Case — computable + validated (constant-coefficient sub-case) -/

/-- **Algorithm `IntegratePrimitive`** (§5.8, p.158), the degree-lowering loop: the computable
`cPrimitivePolyIntegrate Dt fuel p = (q, rem)` for a primitive monomial `t` (`Dt ∈ k`, `δ(t) = 0`,
e.g. `t = log x`), integrating `p = ∑ aᵢtⁱ` top-down in the constant-coefficient sub-case (`b = 0`,
`c = aₘ/((m+1)·Dt)`) so `D(q) + rem = p`. The full `LimitedIntegrate` solve for the coefficient
antiderivatives is the deferred Chapter-7 oracle. Computable + `native_decide`-validated; abstract
correctness (Thm 5.8.1) deferred. *(Already a generic `[CField α] [CDiffField α]` decl — no
`…G`-suffixed mirror is needed; here pinned at the generic ℚ(x) = `CFrac ℚ` like the rest of the
engine.)* -/
noncomputable abbrev alg_5_8_primitivePolyIntegrate := @cPrimitivePolyIntegrate (CFrac ℚ)

/-- **Example (§5.8, p.158)**, primitive case: `cPrimitivePolyIntegrate` on `p = (log x)²/x = (1/x)·t²`
(`t = log x`, `Dt = 1/x`) returns `q = (1/3)t³` with `rem = 0`, satisfying `D(q) + rem = p` over the
generic ℚ(x)[t] (`native_decide`) — i.e. `∫ (log x)²/x dx = (log x)³/3`. -/
theorem ex_5_8_primitive :
    (let Dt : CPoly (CFrac ℚ) := [qFrac5 [1] [0, 1]]                       -- `Dt = 1/x`
     let p : CPoly (CFrac ℚ) := [qConst5 0, qConst5 0, qFrac5 [1] [0, 1]]  -- `p = (1/x)·t²`
     let res := CPoly.cPrimitivePolyIntegrate Dt 8 p
     let q := res.1; let rem := res.2
     let Dq := CPoly.cmonomialDeriv Dt q
     CPoly.cisZero (CPoly.csub (CPoly.cadd Dq rem) p)) = true := by native_decide

end DeepWiki.Si
