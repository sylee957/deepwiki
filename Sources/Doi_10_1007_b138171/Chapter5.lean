import DeepWiki.SymbolicIntegration.ComputableHermiteTower
import DeepWiki.SymbolicIntegration.ComputablePolyPartTower
import DeepWiki.SymbolicIntegration.ComputableLogPartTower
import DeepWiki.SymbolicIntegration.ComputableTowerRischDE
import DeepWiki.SymbolicIntegration.ComputableTowerUnify
import Sources.Doi_10_1007_b138171.Source

/-! # Symbolic Integration catalog — Chapter 5: Integration of Transcendental Functions
The core Risch integration algorithm for a single transcendental monomial extension. The
**degree- and multiplicity-lowering reductions** of this chapter — Hermite (§5.3), the polynomial
reduction (§5.4), the residue-criterion logarithmic part (§5.6), and the primitive-case reduced
integration (§5.8) — are now rendered as **computable** algorithms over the monomial tower ℚ(x)[t]
(`DeepWiki.SymbolicIntegration.Computable*`), each with `native_decide` evidence on a worked book
example. The chapter rests on Chapters 3–4 (differential/monomial extensions, the order function and
the Rothstein–Trager resultant) and is the heart of the book.

**Computable-vs-abstract.** Each algorithm below is a computable function validated by `native_decide`
on the book's example (the cleared reduction identity `D(g) + h = f` etc.); the *abstract* correctness
theorems (that `g` is the integral's rational part, Theorems 5.3.1/5.4.1/5.6.1/5.8.1) are **NOT**
proved. Liouville's theorem (§5.5), the full hyperexponential case (§5.9), the hypertangent case
(§5.10), and the structural §5.7/§5.11/§5.12 theory remain unformalized.

**Carrier: the generic ℚ(x).** The §5.3 Hermite and §5.6 residue-criterion reductions are aliased to the
canonical **generic** engine at `α = QFunNZG ℚ` (the recursive `Frac(ℚ[x])`, every instance bottoming at
ℚ with no hand-built piece), the same carrier as the §6 RDE pipeline. The §5.4 polynomial reduction and
§5.8 primitive integration have **no `…G` variant** and stay on the `QFunNZ`-specific decls (so they
still block deleting the QFunNZ engine).

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

/-! ### Generic-carrier input builders (catalog-local)

The §5 smoke examples over the generic ℚ(x) = `QFunNZG ℚ` carrier read their ℚ(x) coefficients as
num/den lists over `CPolyG ℚ = List ℚ`. These builders mirror `QFunNZ.ofConstNZ`/`ofNumDen` one tower
level down (the `ComputableTowerRefoundProbe` construction). They are catalog infrastructure, not book
items. -/

/-- A ℚ constant `n ∈ ℚ ⊂ ℚ(x)` as a `QFunNZG ℚ` element (denominator `[1]` nonzero, by
`cisZeroG_one_singleton`, so it holds under a parametric definition). -/
def qConst5 (n : ℚ) : QFunNZG ℚ := ⟨([n], [(1 : ℚ)]), QFunNZG.cisZeroG_one_singleton⟩

/-- A ℚ(x) fraction `num/den` as a `QFunNZG ℚ` element, with `den ≠ 0` discharged by `native_decide`. -/
def qFrac5 (num den : List ℚ) (h : CPolyG.cisZeroG den = false := by native_decide) : QFunNZG ℚ :=
  ⟨(num, den), h⟩

/-! ## §5.3 The Hermite Reduction (transcendental) — computable + validated -/

/-- **Algorithm `HermiteReduce`** (§5.3, p.139, quadratic version): the computable transcendental
Hermite reduction `cHermiteReduceTowerG Dt fuel a d = ((gnum, gden), (h_num, h_den))` (the canonical
generic engine, here at the generic ℚ(x) = `QFunNZG ℚ`) over the tower ℚ(x)[t], rewriting the normal
part `f = a/d` as `D(g) + h` with `h_den` squarefree, for the monomial derivation `D = κ_D + Dt·d/dt`.
Computable + `native_decide`-validated; abstract correctness (Thm 5.3.1) deferred. -/
noncomputable abbrev alg_5_3_hermiteReduce := cHermiteReduceTowerG (α := QFunNZG ℚ)

/-- **Example 5.3.1** (§5.3, p.139): `cHermiteReduceTowerG` on `f = 1/t²` (`Dt = t²+1`, `t = tan x`)
satisfies the Hermite identity `D(g) + h = f` over the generic ℚ(x)[t] (cleared form, `native_decide`);
the multiplicity-`2` factor `t` is lowered to the squarefree residual denominator `t`. -/
theorem ex_5_3_1 :
    (let Dt : CPolyG (QFunNZG ℚ) := [qConst5 1, qConst5 0, qConst5 1]      -- `Dt = t²+1`
     let a : CPolyG (QFunNZG ℚ) := [qConst5 1]                           -- `a = 1`
     let d : CPolyG (QFunNZG ℚ) := [qConst5 0, qConst5 0, qConst5 1]       -- `d = t²`
     let res := CPolyG.cHermiteReduceTowerG Dt 12 a d
     let gnum := res.1.1; let gden := res.1.2
     let hNum := res.2.1; let hDen := res.2.2
     let Dgnum := CPolyG.cmonomialDeriv Dt gnum
     let Dgden := CPolyG.cmonomialDeriv Dt gden
     let gprimeNum := CPolyG.csubG (CPolyG.cmulG Dgnum gden) (CPolyG.cmulG gnum Dgden)
     let gden2 := CPolyG.cmulG gden gden
     -- `D(g) + h − f = 0` ⟺ `(gprimeNum·h_den + h_num·gden²)·d = a·(gden²·h_den)`
     let lhs := CPolyG.cmulG
       (CPolyG.caddG (CPolyG.cmulG gprimeNum hDen) (CPolyG.cmulG hNum gden2)) d
     let rhs := CPolyG.cmulG a (CPolyG.cmulG gden2 hDen)
     CPolyG.cisZeroG (CPolyG.csubG lhs rhs)) = true := by native_decide

/-! ## §5.4 The Polynomial Reduction — computable + validated -/

/-- **Algorithm `PolynomialReduce`** (§5.4, p.141): the computable polynomial reduction
`cPolyReduceTower Dt fuel p = (q, r)` for a nonlinear monomial `t` (`δ(t) = deg(Dt) ≥ 2`), splitting
`p ∈ k[t]` as `p = D(q) + r` with `deg(r) < δ(t)` by peeling the leading term whose monomial
derivative cancels the top. Computable (generic over `[CField α] [CDiffField α]`) +
`native_decide`-validated (Thm 5.4.1); abstract correctness deferred. *(No `…G`-suffixed mirror exists
yet, so this stays on the `QFunNZ`-specific decl — a remaining QFunNZ-engine deletion blocker.)* -/
noncomputable abbrev alg_5_4_polynomialReduce := @cPolyReduceTower

/-- **Example 5.4.1** (§5.4, p.141): `cPolyReduceTower` reduces `p = t³` (`Dt = t²+1`, `t = tan x`,
`δ = 2`) to `(q, r) = ((1/2)t², −t)` satisfying `D(q) + r = p` with `deg(r) = 1 < δ` over ℚ(x)[t]
(`native_decide`). -/
abbrev ex_5_4_1 := @polyReduceTower_example

/-! ## §5.6 The Residue Criterion — computable + validated -/

/-- **Algorithm `ResidueReduce`** (§5.6, p.151), the residue resultant: the computable
`cResidueResultantTowerG Dt fuel a d = R(z) = res_t(d, a − z·Dd) ∈ ℚ(x)[z]` (the canonical generic
engine, here at the generic ℚ(x) = `QFunNZG ℚ`) over the tower, by the evaluation + Lagrange-
interpolation template, whose roots are the residues of the logarithmic part of `∫ a/d`. Computable +
`native_decide`-validated; abstract correctness (Thm 5.6.1) deferred. -/
noncomputable abbrev alg_5_6_residueResultant := cResidueResultantTowerG (α := QFunNZG ℚ)

/-- **Algorithm `ResidueReduce`** (§5.6, p.151), the log argument: the computable
`cLogArgTowerG Dt fuel a d c = gcd_t(d, a − c·Dd) ∈ ℚ(x)[t]` (the generic engine at the generic ℚ(x) =
`QFunNZG ℚ`) over the tower — the polynomial inside `log` for a residue `c`, so
`∑_c c·log(cLogArgTowerG … c)` is the logarithmic part of `∫ a/d`. Computable +
`native_decide`-validated; abstract correctness deferred. -/
noncomputable abbrev alg_5_6_logArg := cLogArgTowerG (α := QFunNZG ℚ)

/-- **Example 5.6.2** (§5.6, p.151–152): for `∫ (2t²−t−x²)/(t³−x²t) dx`, `t = log x`, `Dt = 1/x`, the
residue resultant `cResidueResultantTowerG` has monic part `z³−xz²−z/4+x/4` (the book's `r` up to a
ℚ(x) scalar) and the log arguments `cLogArgTowerG … (±1/2) = t ± x` (the residues `±1/2`), all checked
over the generic ℚ(x)[t] (`native_decide`). -/
theorem ex_5_6_2 :
    (let Dt : CPolyG (QFunNZG ℚ) := [qFrac5 [1] [0, 1]]                       -- `Dt = 1/x`
     let a : CPolyG (QFunNZG ℚ) := [qFrac5 [0, 0, -1] [1], qConst5 (-1), qConst5 2]  -- `a = 2t²−t−x²`
     let d : CPolyG (QFunNZG ℚ) := [qConst5 0, qFrac5 [0, 0, -1] [1], qConst5 0, qConst5 1]  -- `d = t³−x²t`
     let resMonic : CPolyG (QFunNZG ℚ) :=                                    -- `z³−xz²−z/4+x/4`
       [qFrac5 [0, 1] [4], qConst5 (-1/4), qFrac5 [0, -1] [1], qConst5 1]
     let argPlus : CPolyG (QFunNZG ℚ) := [qFrac5 [0, 1] [1], qConst5 1]        -- `t + x`
     let argMinus : CPolyG (QFunNZG ℚ) := [qFrac5 [0, -1] [1], qConst5 1]      -- `t − x`
     CPolyG.cisZeroG (CPolyG.csubG
         (CPolyG.cmonicG (CPolyG.cResidueResultantTowerG Dt 30 a d)) resMonic)
     ∧ CPolyG.cisZeroG (CPolyG.csubG (CPolyG.cLogArgTowerG Dt 30 a d (qConst5 (1/2))) argPlus)
     ∧ CPolyG.cisZeroG (CPolyG.csubG (CPolyG.cLogArgTowerG Dt 30 a d (qConst5 (-1/2))) argMinus))
    := by native_decide

/-! ## §5.8 The Primitive Case — computable + validated (constant-coefficient sub-case) -/

/-- **Algorithm `IntegratePrimitive`** (§5.8, p.158), the degree-lowering loop: the computable
`cPrimitivePolyIntegrate Dt fuel p = (q, rem)` for a primitive monomial `t` (`Dt ∈ k`, `δ(t) = 0`,
e.g. `t = log x`), integrating `p = ∑ aᵢtⁱ` top-down in the constant-coefficient sub-case (`b = 0`,
`c = aₘ/((m+1)·Dt)`) so `D(q) + rem = p`. The full `LimitedIntegrate` solve for the coefficient
antiderivatives is the deferred Chapter-7 oracle. Computable + `native_decide`-validated; abstract
correctness (Thm 5.8.1) deferred. *(No `…G`-suffixed mirror exists yet, so this stays on the
`QFunNZ`-specific decl — a remaining QFunNZ-engine deletion blocker.)* -/
noncomputable abbrev alg_5_8_primitivePolyIntegrate := @cPrimitivePolyIntegrate

/-- **Example (§5.8, p.158)**, primitive case: `cPrimitivePolyIntegrate` on `p = (log x)²/x = (1/x)·t²`
(`t = log x`, `Dt = 1/x`) returns `q = (1/3)t³` with `rem = 0`, satisfying `D(q) + rem = p` over
ℚ(x)[t] (`native_decide`) — i.e. `∫ (log x)²/x dx = (log x)³/3`. -/
abbrev ex_5_8_primitive := @primitivePolyIntegrate_example

end DeepWiki.Si
