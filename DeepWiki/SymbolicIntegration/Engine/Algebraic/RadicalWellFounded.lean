import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalRationalDriver
import DeepWiki.SymbolicIntegration.Engine.FuelFreeDiophantine
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalAssembly
import DeepWiki.ComputableAlgebra.LinearAlgebraRat

/-! # Well-founded algebraic simple-radical integration

The three Hermite descents of the simple-radical rational part (`radReduceCase{1,2,3}IterateWf`), the
multi-case dispatch `radIntegrateRationalWf`, and the unified integrator `cIntegrateAlgebraicWf`, by
well-founded recursion on the multiplicity `k` (Cases 1–2) and the degree of `C` (Case 3). Everything
is `[CField α]`-only, so the whole arc reduces in compiled code over the noncomputable `ℚ(x)` tower. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem DensePoly

namespace DensePoly

variable {α : Type*} [CField α]

/-! ## The Case-1 Hermite descent `radReduceCase1IterateWf`

The `C/(Vᵏy)` Hermite step `k → k−1`, `V` coprime to the radicand; termination is by the
multiplicity `k`. -/

/-- Iterated Case-1 Hermite reduction `radReduceCase1IterateWf der V Df f g k0 k C vNum =
(Crem, vNumOut)`: at `k ≥ 2` solve the cofactor `B = CPoly.radCase1Cofactor`, form the residual
`D = CPoly.radCase1Residual`, accumulate `B·f·V^{k0−k}` into `vNum`, and recurse on `−D` at `k − 1`;
bottom at `k ≤ 1` returning `(C, vNum)`. Well-founded on `k`; `[CField α]`-only. -/
def radReduceCase1IterateWf (der : DensePoly α → DensePoly α) (V Df f g : DensePoly α) (k0 : ℕ) :
    ℕ → DensePoly α → DensePoly α → DensePoly α × DensePoly α
  | k, C, vNum =>
    if hk : k ≤ 1 then (C, vNum)
    else
      let B := CPoly.radCase1Cofactor k V Df f C
      let Bder := der B
      let D := CPoly.radCase1Residual k V Df f g B C Bder
      let contrib := cmul (cmul B f) (cpow V (k0 - k))
      radReduceCase1IterateWf der V Df f g k0 (k - 1) (cneg D) (cadd vNum contrib)
termination_by k => k
decreasing_by exact Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.lt_of_not_le hk).le) Nat.zero_lt_one

/-- Case-1 simple-radical rational-part driver `radIntegrateCase1Wf der V f g k0 C = (Crem, vNum)`:
run `radReduceCase1IterateWf` with `Df = der V` from multiplicity `k0` down to `1`. Master identity
`∫ C/(V^{k0}y) = vNum/(V^{k0−1}y) + ∫ Crem/(Vy)`. -/
def radIntegrateCase1Wf (der : DensePoly α → DensePoly α) (V f g : DensePoly α) (k0 : ℕ) (C : DensePoly α) :
    DensePoly α × DensePoly α :=
  radReduceCase1IterateWf der V (der V) f g k0 k0 C []

/-! ## The Case-2 Hermite descent `radReduceCase2IterateWf`

The branch-place (`W ∣ ρ`) Hermite step `k → k−1`; same multiplicity measure as Case 1, with the
contribution scaled by `W^{k0−k}` over the common denominator `W^{k0}·y`. -/

/-- Iterated Case-2 Hermite reduction `radReduceCase2IterateWf W h ρ k0 k C vNum = (Crem, vNumOut)`:
at `k ≥ 2` solve the cofactor `B = CPoly.radCase2Cofactor`, form the residual `D = CPoly.radCase2Residual`,
accumulate `B·ρ·W^{k0−k}` into `vNum`, and recurse on `−D` at `k − 1`; bottom at `k ≤ 1` returning
`(C, vNum)`. `W` a squarefree factor of the radicand `ρ`, `h = ρ/W`. Well-founded on `k`;
`[CField α]`-only. -/
def radReduceCase2IterateWf (W h ρ : DensePoly α) (k0 : ℕ) :
    ℕ → DensePoly α → DensePoly α → DensePoly α × DensePoly α
  | k, C, vNum =>
    if hk : k ≤ 1 then (C, vNum)
    else
      let B := CPoly.radCase2Cofactor k W h C
      let D := CPoly.radCase2Residual k W h C B
      let contrib := cmul (cmul B ρ) (cpow W (k0 - k))
      radReduceCase2IterateWf W h ρ k0 (k - 1) (cneg D) (cadd vNum contrib)
termination_by k => k
decreasing_by exact Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.lt_of_not_le hk).le) Nat.zero_lt_one

/-- Case-2 simple-radical rational-part driver `radIntegrateCase2Wf W ρ k0 C = (Crem, vNum)`: run
`radReduceCase2IterateWf` with `h = CPolyEuclidean.div ρ W` from multiplicity `k0` down to `1`. Master identity
`∫ C/(W^{k0}y) = vNum/(W^{k0}y) + ∫ Crem/(Wy)`. -/
def radIntegrateCase2Wf (W ρ : DensePoly α) (k0 : ℕ) (C : DensePoly α) : DensePoly α × DensePoly α :=
  radReduceCase2IterateWf W (CPolyEuclidean.div ρ W) ρ k0 k0 C []

/-! ## The Case-3 (`C/y`) degree-lowering `radReduceCase3IterateWf`

Termination is by `(cnorm C).length`; unlike Cases 1–2 the degree drop is data-driven, so the
recursion is taken only under a structural length-drop guard. -/

/-- Iterated Case-3 reduction `radReduceCase3IterateWf der f g C vNum = (Crem, vNumOut)`: while
`deg C ≥ deg f`, cancel the leading term with `B = CPoly.radCase3Cofactor`, form the residual
`D = CPoly.radCase3Residual`, accumulate `B·f` into `vNum`, and recurse on `−D`; bottom at `deg C < deg f`
(or `C = 0`) returning `(C, vNum)`. Well-founded on `(cnorm C).length` under the structural
length-drop guard (on a real run the leading term cancels, so the guard always holds). `der` the base
derivation, `f` the radicand, `g` from `(f/y)' = g/y`. `[CField α]`-only. -/
def radReduceCase3IterateWf (der : DensePoly α → DensePoly α) (f g : DensePoly α) :
    DensePoly α → DensePoly α → DensePoly α × DensePoly α
  | C, vNum =>
    if cisZero C || cdeg C < cdeg f then (C, vNum)
    else
      let B := CPoly.radCase3Cofactor f g C
      let D := CPoly.radCase3Residual f g B C (der B)
      if (cnorm (cneg D) : List α).length < (cnorm C : List α).length then
        radReduceCase3IterateWf der f g (cneg D) (cadd vNum (cmul B f))
      else (C, vNum)   -- unreachable on a real run (the leading term cancels, `deg D < deg C`)
termination_by C => (cnorm C : List α).length
decreasing_by assumption

/-- Case-3 simple-radical rational-part driver `radIntegrateCase3Wf der f g C = (Crem, vNum)`: the
`C/y` degree-lowering from an empty accumulator. Master identity `∫ C/y = vNum/y + ∫ Crem/y`. -/
def radIntegrateCase3Wf (der : DensePoly α → DensePoly α) (f g C : DensePoly α) : DensePoly α × DensePoly α :=
  radReduceCase3IterateWf der f g C []

/-! ## The multi-case dispatch `radIntegrateRationalWf` -/

/-- Multi-case simple-radical rational-part driver `radIntegrateRationalWf ρ R B` over `y² = ρ`,
denominator `B` monic, numerator `R` proper: squarefree-decompose `B` (`CPoly.squarefreeYun`), split each
factor into its `V`-part / `W`-part (`CPolyEuclidean.gcdExt`/`CPolyEuclidean.div` against `ρ`), partial-fraction `R`
(`radPartialFractionCoprime`), and dispatch each summand to the Case-1 / Case-2 Hermite descent.
Returns the per-factor reductions `(isV, Bᵢ, eᵢ, Nᵢ, vNumᵢ, Cremᵢ)`. Squarefree factorization is selected
through `CPolySquarefree`. -/
def radIntegrateRationalWf [CPolySquarefree DensePoly α] (ρ R B : DensePoly α) :
    List (Bool × DensePoly α × ℕ × DensePoly α × DensePoly α × DensePoly α) :=
  let g : DensePoly α := cscale (CField.div CCommRing.one (CField.natCast 2)) (cderiv ρ)   -- `½·ρ'` (n = 2)
  let factored : List (DensePoly α × ℕ) :=
    (CPoly.squarefreeYun B).zipIdx.filterMap (fun (Bi, i) =>
      if cdeg Bi = 0 then none else some (Bi, i + 1))
  let split : List (Bool × DensePoly α × ℕ) :=
    factored.flatMap (fun (Bi, e) =>
      let Wi := cmonic (CPolyEuclidean.gcdExt Bi ρ).1
      let Vi := CPolyEuclidean.div Bi Wi
      (if cdeg Vi = 0 then [] else [(true, Vi, e)]) ++
      (if cdeg Wi = 0 then [] else [(false, Wi, e)]))
  let primePowers : List (DensePoly α) := split.map (fun (_, fi, e) => cpow fi e)
  let nums : List (DensePoly α) := radPartialFractionCoprime R primePowers
  (split.zip nums).map (fun ((isV, fi, e), Ni) =>
    if isV then
      let (Crem, vNum) := radReduceCase1IterateWf cderiv fi (cderiv fi) ρ g e e Ni []
      (true, fi, e, Ni, vNum, Crem)
    else
      let (Crem, vNum) :=
        radReduceCase2IterateWf fi (CPolyEuclidean.div ρ fi) ρ e e Ni []
      (false, fi, e, Ni, vNum, Crem))

end DensePoly

/-! ### The unified algebraic integrator `cIntegrateAlgebraicWf` (radical top-level) -/

/-- Unified algebraic integrator `cIntegrateAlgebraicWf ρ R B residual c D degBound` over `y² = ρ`:
`∫ R/(B·y) dx = v + c·log u` (principal case). Computes the rational part `v` by the multi-case
dispatch (`radIntegrateRationalWf` + `radAssembleRatPart`), then solves the log argument on
`residual` (`radLogArgSolve ρ residual D degBound`); on `none` returns just the rational part. -/
def cIntegrateAlgebraicWf (ρ : DenseFrac ℚ) (R B : DensePoly ℚ)
    (residual : RadElem (DenseFrac ℚ)) (c : DenseFrac ℚ) (D : DensePoly ℚ) (degBound : ℕ) :
    AlgIntegralResult (DenseFrac ℚ) :=
  let ρpoly : DensePoly ℚ := CFrac.num ρ
  let runs := DensePoly.radIntegrateRationalWf ρpoly R B
  let v := radAssembleRatPart ρ runs
  match radLogArgSolve ρ residual D degBound with
  | none => ⟨v, []⟩
  | some N =>
    let Dq : DenseFrac ℚ := CFrac.ofPoly D
    let u : RadElem (DenseFrac ℚ) := N.map (fun z => CField.div z Dq)
    ⟨v, [(c, u)]⟩

end DeepWiki.SymbolicIntegration
