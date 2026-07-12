import DeepWiki.SymbolicIntegration.Engine.PolyPartTower
import DeepWiki.SymbolicIntegration.Engine.Tower.Integrate
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDE
import DeepWiki.SymbolicIntegration.Engine.CanonicalRepresentationDense
import DeepWiki.SymbolicIntegration.Engine.RischTowerLrtGrounding
import DeepWiki.SymbolicIntegration.Engine.Hyperexp.RischLevel
import DeepWiki.SymbolicIntegration.Engine.CoupledDE.TangentCapability
import Sources.Doi_10_1007_b138171.Source

/-! # Symbolic Integration catalog — Chapter 5: Integration of Transcendental Functions
The core Risch integration algorithm for a single transcendental monomial extension. The
**degree- and multiplicity-lowering reductions** of this chapter — Hermite (§5.3), the polynomial
reduction (§5.4), the residue-criterion logarithmic part (§5.6), and the primitive-case reduced
integration (§5.8) — are now rendered as **computable** algorithms over the monomial tower ℚ(x)[t]
(`DeepWiki.SymbolicIntegration.Engine*`), each with `native_decide` evidence on a worked book
example. The chapter rests on Chapters 3–4 (differential/monomial extensions, the order function and
the Rothstein–Trager resultant) and is the heart of the book.

**Computable-vs-abstract.** Each reduction algorithm below is a computable function validated by
`native_decide` on the book's example (the cleared reduction identity `D(g) + h = f` etc.). Beyond
that validation, the **assembled integrator is now proved a sound-and-complete decision procedure** for
each of the three transcendental monomial cases — `some ⟺ genuinely elementary-integrable`, with a
genuine antiderivative on success — resting only on the necessary Risch new-monomial condition (and, for
the coefficient recursion, the field-RDE completeness): the **primitive** case (Thm 5.5.1 realization,
`thm_5_5_1_soundAndComplete`), the **hyperexponential** §5.9 case (`thm_5_9_1_soundAndComplete`), and the
**hypertangent** §5.10 case (`thm_5_10_soundAndComplete`), all cataloged below and axiom-clean. Liouville's
theorem (§5.5): the transcendental *logarithmic* AND *exponential* cases (each conditional on the
new-monomial condition) and the rational case (§2.4/§2.5) are in catalog
`Sources.Doi_10_1007_b138171.Liouville`; the general structure theorem (Thm 5.5.2/5.5.3) remains. The
per-reduction *abstract correctness* theorems (Thms 5.3.1/5.4.1/5.6.1/5.8.1 in isolation) and the
structural §5.7/§5.11/§5.12 theory remain (see the block below).

**Carrier: the generic ℚ(x).** The §5.3 Hermite and §5.6 residue-criterion reductions are aliased to the
canonical **generic** engine at `α = DenseFrac ℚ` (the recursive `Frac(ℚ[x])`, every instance bottoming at
ℚ with no hand-built piece), the same carrier as the §6 RDE pipeline. The §5.4 polynomial reduction
(`cPolyReduceTower`) and §5.8 primitive integration (`cPrimitivePolyIntegrate`) are already
`[CField α] [CDiffField α]`-**generic** decls (no separate `…G` rename needed), aliased at the generic
level and instantiable at `DenseFrac ℚ` like the rest of the engine.

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
  `[research]`).
  (Thm 5.5.1 is now formalized for BOTH transcendental cases, conditional on the necessary new-monomial
  condition: the *logarithmic* case `IsLiouville F F(log u)` (`log u ∉ F`) and the *exponential* case
  `IsLiouville F F(exp u)` (`exp u ∉ F`), see catalog `Sources.Doi_10_1007_b138171.Liouville`
  `liouville_logExtension`/`liouville_expExtension`; the rational case §2.4/§2.5 is cataloged there too,
  unconditionally. The assembled integrator's **sound-and-complete decision procedure** on the primitive
  domain over ℚ(x) — `some ⟺ elementary` with a genuine antiderivative on success, resting on the
  new-monomial frontier — is cataloged as `thm_5_5_1_soundAndComplete`/`thm_5_5_1_frontier_of_newMonomial`
  above.)
§5.6 The Residue Criterion: Thm 5.6.1 (abstract correctness); Lemma 5.6.1, Lemma 5.6.2; Ex 5.6.1,
  Ex 5.6.3 (the algorithm `ResidueReduce` / the residue resultant + log argument are now computable +
  native_decide-validated on Ex 5.6.2, see `alg_5_6_residueResultant`/`alg_5_6_logArg`/`ex_5_6_2`).
§5.7 Integration of Reduced Functions: Thm 5.7.1, Thm 5.7.2.
§5.8 The Primitive Case: Thm 5.8.1 (abstract correctness; the algorithm `IntegratePrimitive`
  degree-lowering loop, constant-coefficient sub-case, is now computable + native_decide-validated,
  see `alg_5_8_primitivePolyIntegrate`/`ex_5_8_primitive`). The full `LimitedIntegrate` solve for the
  coefficient antiderivatives is the deferred Chapter-7 oracle.
§5.9 The Hyperexponential Case: Lemma 5.9.1 (the Laurent per-term bounds). (Thm 5.9.1 is realized:
  the hyperexponential integrator `IntegrateHyperexponential` is computable + native_decide-validated,
  and the **sound-and-complete decision procedure** — `some ⟺ genuinely elementary-integrable`, resting
  on the field-RDE completeness `CRischFieldComplete` — is cataloged as `thm_5_9_1_soundAndComplete`
  above.)
§5.10 The Hypertangent Case: Def 5.10.1; Lemma 5.10.1; Ex 5.10.1, Ex 5.10.2, Ex 5.10.3. (Thm 5.10.1/
  5.10.2 are realized: the coupled-DE hypertangent integrator `IntegrateHypertangent` is computable +
  native_decide-validated, and the **sound-and-complete decision procedure** — `some ⟺ genuinely
  elementary-integrable` on the certificate-checked domain — is cataloged as `thm_5_10_soundAndComplete`
  above.)
§5.11 The Nonlinear Case with no Specials: Cor 5.11.1; Ex 5.11.1, Ex 5.11.2.
§5.12 In-Field Integration: Lemma 5.12.1.
Exercises: Ex 5.1, Ex 5.2, Ex 5.3, Ex 5.4, Ex 5.5, Ex 5.6.

The remaining gaps are the **abstract correctness theorems** (the reductions above are computationally
rendered but not proved correct), the remainder of Liouville's structure theory (§5.5 — the exp-extension
instance and the general structure theorem; the rational + transcendental-log cases are formalized, the
latter conditional on the new-monomial condition, in `Sources.Doi_10_1007_b138171.Liouville`), the full
hyperexponential/hypertangent integration (§5.9–§5.10), and the structural §5.7/§5.11/§5.12 results. -/

open DeepWiki.SymbolicIntegration DeepWiki.SymbolicIntegration.DensePoly

namespace DeepWiki.Si

/-! ### Generic-carrier input builders (catalog-local)

The §5 smoke examples over the generic ℚ(x) = `DenseFrac ℚ` carrier read their ℚ(x) coefficients as
num/den lists over `DensePoly ℚ = List ℚ`. `CFrac.ofScalar` embeds constants, while
`CFrac.ofFraction` packages an arbitrary numerator and denominator. This is catalog infrastructure,
not a book item. -/

/-! ## §5.3 The Hermite Reduction (transcendental) — computable + validated -/

/-- **Algorithm `HermiteReduce`** (§5.3, p.139, quadratic version): the fuel-free computable transcendental
Hermite reduction `cHermiteReduceTower Dt a d = ((gnum, gden), (h_num, h_den))` (the canonical generic
engine, here at the generic ℚ(x) = `DenseFrac ℚ`) over the tower ℚ(x)[t], rewriting the normal part `f = a/d`
as `D(g) + h` with `h_den` squarefree, for the monomial derivation `D = κ_D + Dt·d/dt`. Computable +
`native_decide`-validated; abstract correctness (Thm 5.3.1) deferred. -/
noncomputable abbrev alg_5_3_hermiteReduce := cHermiteReduceTower (α := DenseFrac ℚ)

/-- **Example 5.3.1** (§5.3, p.139): `cHermiteReduceTower` on `f = 1/t²` (`Dt = t²+1`, `t = tan x`)
satisfies the Hermite identity `D(g) + h = f` over the generic ℚ(x)[t] (cleared form, `native_decide`);
the multiplicity-`2` factor `t` is lowered to the squarefree residual denominator `t`. -/
theorem ex_5_3_1 :
    (let Dt : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1, CFrac.ofScalar 0, CFrac.ofScalar 1]      -- `Dt = t²+1`
     let a : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1]                           -- `a = 1`
     let d : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 0, CFrac.ofScalar 0, CFrac.ofScalar 1]       -- `d = t²`
     let res := DensePoly.cHermiteReduceTower Dt a d
     let gnum := res.1.1; let gden := res.1.2
     let hNum := res.2.1; let hDen := res.2.2
     let Dgnum := CPolyEngine.monomialDeriv Dt gnum
     let Dgden := CPolyEngine.monomialDeriv Dt gden
     let gprimeNum := DensePoly.csub (DensePoly.cmul Dgnum gden) (DensePoly.cmul gnum Dgden)
     let gden2 := DensePoly.cmul gden gden
     -- `D(g) + h − f = 0` ⟺ `(gprimeNum·h_den + h_num·gden²)·d = a·(gden²·h_den)`
     let lhs := DensePoly.cmul
       (DensePoly.cadd (DensePoly.cmul gprimeNum hDen) (DensePoly.cmul hNum gden2)) d
     let rhs := DensePoly.cmul a (DensePoly.cmul gden2 hDen)
     DensePoly.cisZero (DensePoly.csub lhs rhs)) = true := by native_decide

/-! ## §5.4 The Polynomial Reduction — computable + validated -/

/-- **Algorithm `PolynomialReduce`** (§5.4, p.141): the computable polynomial reduction
`cPolyReduceTower Dt fuel p = (q, r)` for a nonlinear monomial `t` (`δ(t) = deg(Dt) ≥ 2`), splitting
`p ∈ k[t]` as `p = D(q) + r` with `deg(r) < δ(t)` by peeling the leading term whose monomial
derivative cancels the top. Computable (generic over `[CField α] [CDiffField α]`) +
`native_decide`-validated (Thm 5.4.1); abstract correctness deferred. *(Already a generic decl — no
`…G`-suffixed mirror is needed; here pinned at the generic ℚ(x) = `DenseFrac ℚ` like the rest of the
engine.)* -/
noncomputable abbrev alg_5_4_polynomialReduce :=
  cPolyReduceTower (P := DensePoly) (α := DenseFrac ℚ)

/-- **Example 5.4.1** (§5.4, p.141): `cPolyReduceTower` reduces `p = t³` (`Dt = t²+1`, `t = tan x`,
`δ = 2`) to `(q, r) = ((1/2)t², −t)` satisfying the §5.4 reduction identity `D(q) + r = p` with the
remainder `t`-degree `deg(r) = 1 < δ = 2` over the generic ℚ(x)[t] (`native_decide`). -/
theorem ex_5_4_1 :
    (let Dt : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1, CFrac.ofScalar 0, CFrac.ofScalar 1]       -- `Dt = t²+1`
     let p : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 0, CFrac.ofScalar 0, CFrac.ofScalar 0, CFrac.ofScalar 1]  -- `p = t³`
     let res := DensePoly.cPolyReduceTower Dt 8 p
     let q := res.1; let r := res.2
     let Dq := CPolyEngine.monomialDeriv Dt q
     -- `D(q) + r − p = 0` and the reduced remainder has `t`-degree `1 < δ(t) = 2`
     DensePoly.cisZero (DensePoly.csub (DensePoly.cadd Dq r) p) = true
       ∧ DensePoly.cdeg r = 1) := by native_decide

/-! ## §5.6 The Residue Criterion — computable + validated -/

/-- **Algorithm `ResidueReduce`** (§5.6, p.151), the residue resultant: the computable
`cResidueResultantTower Dt a d = R(z) = res_t(d, a − z·Dd) ∈ ℚ(x)[z]` (the canonical generic
engine, here at the generic ℚ(x) = `DenseFrac ℚ`) over the tower, by the evaluation + Lagrange-
interpolation template, whose roots are the residues of the logarithmic part of `∫ a/d`. Computable +
`native_decide`-validated; abstract correctness (Thm 5.6.1) deferred. -/
noncomputable abbrev alg_5_6_residueResultant := cResidueResultantTower (α := DenseFrac ℚ)

/-- **Algorithm `ResidueReduce`** (§5.6, p.151), the log argument: the computable
`cLogArgTower Dt a d c = gcd_t(d, a − c·Dd) ∈ ℚ(x)[t]` (the generic engine at the generic ℚ(x) =
`DenseFrac ℚ`) over the tower — the polynomial inside `log` for a residue `c`, so
`∑_c c·log(cLogArgTower … c)` is the logarithmic part of `∫ a/d`. Computable +
`native_decide`-validated; abstract correctness deferred. -/
noncomputable abbrev alg_5_6_logArg := cLogArgTower (α := DenseFrac ℚ)

/-- **Example 5.6.2** (§5.6, p.151–152): for `∫ (2t²−t−x²)/(t³−x²t) dx`, `t = log x`, `Dt = 1/x`, the
residue resultant `cResidueResultantTower` has monic part `z³−xz²−z/4+x/4` (the book's `r` up to a
ℚ(x) scalar) and the log arguments `cLogArgTower … (±1/2) = t ± x` (the residues `±1/2`), all checked
over the generic ℚ(x)[t] (`native_decide`). -/
theorem ex_5_6_2 :
    (let Dt : DensePoly (DenseFrac ℚ) := [CFrac.ofFraction [1] [0, 1] (by cfrac_nonzero)]                       -- `Dt = 1/x`
     let a : DensePoly (DenseFrac ℚ) := [CFrac.ofFraction [0, 0, -1] [1] (by cfrac_nonzero), CFrac.ofScalar (-1), CFrac.ofScalar 2]  -- `a = 2t²−t−x²`
     let d : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 0, CFrac.ofFraction [0, 0, -1] [1] (by cfrac_nonzero), CFrac.ofScalar 0, CFrac.ofScalar 1]  -- `d = t³−x²t`
     let resMonic : DensePoly (DenseFrac ℚ) :=                                    -- `z³−xz²−z/4+x/4`
       [CFrac.ofFraction [0, 1] [4] (by cfrac_nonzero), CFrac.ofScalar (-1/4), CFrac.ofFraction [0, -1] [1] (by cfrac_nonzero), CFrac.ofScalar 1]
     let argPlus : DensePoly (DenseFrac ℚ) := [CFrac.ofFraction [0, 1] [1] (by cfrac_nonzero), CFrac.ofScalar 1]        -- `t + x`
     let argMinus : DensePoly (DenseFrac ℚ) := [CFrac.ofFraction [0, -1] [1] (by cfrac_nonzero), CFrac.ofScalar 1]      -- `t − x`
     DensePoly.cisZero (DensePoly.csub
         (DensePoly.cmonic (DensePoly.cResidueResultantTower Dt a d)) resMonic)
     ∧ DensePoly.cisZero (DensePoly.csub (DensePoly.cLogArgTower Dt a d (CFrac.ofScalar (1/2))) argPlus)
     ∧ DensePoly.cisZero (DensePoly.csub (DensePoly.cLogArgTower Dt a d (CFrac.ofScalar (-1/2))) argMinus))
    := by native_decide

/-! ## §5.8 The Primitive Case — computable + validated (constant-coefficient sub-case) -/

/-- **Algorithm `IntegratePrimitive`** (§5.8, p.158), the degree-lowering loop: the computable
`cPrimitivePolyIntegrate Dt fuel p = (q, rem)` for a primitive monomial `t` (`Dt ∈ k`, `δ(t) = 0`,
e.g. `t = log x`), integrating `p = ∑ aᵢtⁱ` top-down in the constant-coefficient sub-case (`b = 0`,
`c = aₘ/((m+1)·Dt)`) so `D(q) + rem = p`. The full `LimitedIntegrate` solve for the coefficient
antiderivatives is the deferred Chapter-7 oracle. Computable + `native_decide`-validated; abstract
correctness (Thm 5.8.1) deferred. *(Already a generic `[CField α] [CDiffField α]` decl — no
`…G`-suffixed mirror is needed; here pinned at the generic ℚ(x) = `DenseFrac ℚ` like the rest of the
engine.)* -/
noncomputable abbrev alg_5_8_primitivePolyIntegrate :=
  cPrimitivePolyIntegrate (P := DensePoly) (α := DenseFrac ℚ)

/-- **Example (§5.8, p.158)**, primitive case: `cPrimitivePolyIntegrate` on `p = (log x)²/x = (1/x)·t²`
(`t = log x`, `Dt = 1/x`) returns `q = (1/3)t³` with `rem = 0`, satisfying `D(q) + rem = p` over the
generic ℚ(x)[t] (`native_decide`) — i.e. `∫ (log x)²/x dx = (log x)³/3`. -/
theorem ex_5_8_primitive :
    (let Dt : DensePoly (DenseFrac ℚ) := [CFrac.ofFraction [1] [0, 1] (by cfrac_nonzero)]                       -- `Dt = 1/x`
     let p : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 0, CFrac.ofScalar 0, CFrac.ofFraction [1] [0, 1] (by cfrac_nonzero)]  -- `p = (1/x)·t²`
     let res := DensePoly.cPrimitivePolyIntegrate Dt 8 p
     let q := res.1; let rem := res.2
     let Dq := CPolyEngine.monomialDeriv Dt q
     DensePoly.cisZero (DensePoly.csub (DensePoly.cadd Dq rem) p)) = true := by native_decide

/-! ## §5.5 + §5.6 + §6 — the assembled integrator is a sound and complete decision procedure

The abstract-correctness capstone: on the primitive decomposition domain, over the concrete tower
ℚ(x) = `DenseFrac ℚ`, the assembled root-free transcendental integrator `CRischLevelLrt.integrate`
is a **sound and complete decision procedure** for elementary integrability, resting on exactly one
honest hypothesis — the Risch new-monomial condition (Thm 5.5.1: `η = Dt` is not a derivative, so `t`
is a genuine new transcendental). This is the abstract statement behind the `native_decide`-validated
reductions above; the general structure theorem (Thm 5.5.2/5.5.3) and the non-primitive cases (§5.9
hyperexp, §5.10 hypertangent) remain (see the block below). -/

/-- **Sound and complete (Thm 5.5.1 realization), abstract.** On the primitive domain over ℚ(x), the
integrator succeeds **iff** the input is elementary-integrable (completeness), and a guard-passing
success yields a genuine true antiderivative `D(∫f) = f` (soundness). Axiom-clean (no `native_decide`);
rests on the honest new-monomial frontier `PrimitiveFrontierLrt`. -/
abbrev thm_5_5_1_soundAndComplete := @lrtSolver_soundAndComplete_on_tower

/-- **The frontier is the new-monomial condition, not an axiom** (Thm 5.5.1, faithfulness): the
`PrimitiveFrontierLrt` the capstone rests on is *constructible* from the genuine input-independent
condition "`η = Dt` is not a derivative" (`GenuinePrimitiveMonomialLrt`, bundled `LrtReducedGenuineData`)
— the necessary Risch new-monomial hypothesis, `t` a genuine new transcendental. -/
abbrev thm_5_5_1_frontier_of_newMonomial := @primitiveFrontierLrt_of_genuineData

/-- **§5.9 hyperexponential — sound-and-complete decision procedure** (Thm 5.9.1, abstract): the
assembled hyperexponential Risch level (`t′ = η·t`) succeeds **iff** the input is genuinely
elementary-integrable, on the semantic completeness domain. Rests on the field-RDE completeness
`CRischFieldComplete` (the tower recursion hypothesis) — the §5.9 analogue of `thm_5_5_1_soundAndComplete`.
Axiom-clean (no `native_decide`). -/
abbrev thm_5_9_1_soundAndComplete := @hyperexpRischLevel_succeeds_iff_integrable

/-- **§5.10 hypertangent — sound-and-complete decision procedure** (Thm 5.10.1/5.10.2, abstract): the
assembled coupled-DE hypertangent Risch level (`t′ = t²+1`) succeeds **iff** the input is genuinely
elementary-integrable, on the certificate-checked stage domain. The §5.10 analogue of the primitive and
hyperexponential capstones, via the coupled-DE arc. Axiom-clean. -/
abbrev thm_5_10_soundAndComplete := @tangentRischLevel_succeeds_iff_integrable

end DeepWiki.Si
