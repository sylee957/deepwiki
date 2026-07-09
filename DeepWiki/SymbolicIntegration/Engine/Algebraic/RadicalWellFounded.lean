import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalRationalDriver
import DeepWiki.SymbolicIntegration.Engine.FuelFreeDiophantine
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalAssembly

/-! # Well-founded algebraic simple-radical integration

The three Hermite descents of the simple-radical rational part (`radReduceCase{1,2,3}IterateWf`), the
multi-case dispatch `radIntegrateRationalWf`, and the unified integrator `cIntegrateAlgebraicWf`, by
well-founded recursion on the multiplicity `k` (Cases 1–2) and the degree of `C` (Case 3). Everything
is `[CField α]`-only, so the whole arc reduces in compiled code over the noncomputable `ℚ(x)` tower. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPolyG

namespace CPolyG

variable {α : Type*} [CField α]

/-! ## The Case-1 Hermite descent `radReduceCase1IterateWf`

The `C/(Vᵏy)` Hermite step `k → k−1`, `V` coprime to the radicand; termination is by the
multiplicity `k`. -/

/-- Iterated Case-1 Hermite reduction `radReduceCase1IterateWf der V Df f g k0 k C vNum =
(Crem, vNumOut)`: at `k ≥ 2` solve the cofactor `B = radCase1Cofactor`, form the residual
`D = radCase1Residual`, accumulate `B·f·V^{k0−k}` into `vNum`, and recurse on `−D` at `k − 1`;
bottom at `k ≤ 1` returning `(C, vNum)`. Well-founded on `k`; `[CField α]`-only. -/
def radReduceCase1IterateWf (der : CPolyG α → CPolyG α) (V Df f g : CPolyG α) (k0 : ℕ) :
    ℕ → CPolyG α → CPolyG α → CPolyG α × CPolyG α
  | k, C, vNum =>
    if hk : k ≤ 1 then (C, vNum)
    else
      let B := radCase1Cofactor k V Df f C
      let Bder := der B
      let D := radCase1Residual k V Df f g B C Bder
      let contrib := cmulG (cmulG B f) (cpowG V (k0 - k))
      radReduceCase1IterateWf der V Df f g k0 (k - 1) (cnegG D) (caddG vNum contrib)
termination_by k => k
decreasing_by exact Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.lt_of_not_le hk).le) Nat.zero_lt_one

/-- Case-1 simple-radical rational-part driver `radIntegrateCase1Wf der V f g k0 C = (Crem, vNum)`:
run `radReduceCase1IterateWf` with `Df = der V` from multiplicity `k0` down to `1`. Master identity
`∫ C/(V^{k0}y) = vNum/(V^{k0−1}y) + ∫ Crem/(Vy)`. -/
def radIntegrateCase1Wf (der : CPolyG α → CPolyG α) (V f g : CPolyG α) (k0 : ℕ) (C : CPolyG α) :
    CPolyG α × CPolyG α :=
  radReduceCase1IterateWf der V (der V) f g k0 k0 C []

/-! ## The Case-2 Hermite descent `radReduceCase2IterateWf`

The branch-place (`W ∣ ρ`) Hermite step `k → k−1`; same multiplicity measure as Case 1, with the
contribution scaled by `W^{k0−k}` over the common denominator `W^{k0}·y`. -/

/-- Iterated Case-2 Hermite reduction `radReduceCase2IterateWf W h ρ k0 k C vNum = (Crem, vNumOut)`:
at `k ≥ 2` solve the cofactor `B = radCase2CofactorC`, form the residual `D = radCase2ResidualC`,
accumulate `B·ρ·W^{k0−k}` into `vNum`, and recurse on `−D` at `k − 1`; bottom at `k ≤ 1` returning
`(C, vNum)`. `W` a squarefree factor of the radicand `ρ`, `h = ρ/W`. Well-founded on `k`;
`[CField α]`-only. -/
def radReduceCase2IterateWf (W h ρ : CPolyG α) (k0 : ℕ) :
    ℕ → CPolyG α → CPolyG α → CPolyG α × CPolyG α
  | k, C, vNum =>
    if hk : k ≤ 1 then (C, vNum)
    else
      let B := radCase2CofactorC k W h C
      let D := radCase2ResidualC k W h C B
      let contrib := cmulG (cmulG B ρ) (cpowG W (k0 - k))
      radReduceCase2IterateWf W h ρ k0 (k - 1) (cnegG D) (caddG vNum contrib)
termination_by k => k
decreasing_by exact Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.lt_of_not_le hk).le) Nat.zero_lt_one

/-- Case-2 simple-radical rational-part driver `radIntegrateCase2Wf W ρ k0 C = (Crem, vNum)`: run
`radReduceCase2IterateWf` with `h = cdivWf ρ W` from multiplicity `k0` down to `1`. Master identity
`∫ C/(W^{k0}y) = vNum/(W^{k0}y) + ∫ Crem/(Wy)`. -/
def radIntegrateCase2Wf (W ρ : CPolyG α) (k0 : ℕ) (C : CPolyG α) : CPolyG α × CPolyG α :=
  radReduceCase2IterateWf W (cdivWf ρ W) ρ k0 k0 C []

/-! ## The Case-3 (`C/y`) degree-lowering `radReduceCase3IterateWf`

Termination is by `(cnormG C).length`; unlike Cases 1–2 the degree drop is data-driven, so the
recursion is taken only under a structural length-drop guard. -/

/-- Iterated Case-3 reduction `radReduceCase3IterateWf der f g C vNum = (Crem, vNumOut)`: while
`deg C ≥ deg f`, cancel the leading term with `B = radCase3Cofactor`, form the residual
`D = radCase3Residual`, accumulate `B·f` into `vNum`, and recurse on `−D`; bottom at `deg C < deg f`
(or `C = 0`) returning `(C, vNum)`. Well-founded on `(cnormG C).length` under the structural
length-drop guard (on a real run the leading term cancels, so the guard always holds). `der` the base
derivation, `f` the radicand, `g` from `(f/y)' = g/y`. `[CField α]`-only. -/
def radReduceCase3IterateWf (der : CPolyG α → CPolyG α) (f g : CPolyG α) :
    CPolyG α → CPolyG α → CPolyG α × CPolyG α
  | C, vNum =>
    if cisZeroG C || cdegG C < cdegG f then (C, vNum)
    else
      let B := radCase3Cofactor f g C
      let D := radCase3Residual f g B C (der B)
      if (cnormG (cnegG D) : List α).length < (cnormG C : List α).length then
        radReduceCase3IterateWf der f g (cnegG D) (caddG vNum (cmulG B f))
      else (C, vNum)   -- unreachable on a real run (the leading term cancels, `deg D < deg C`)
termination_by C => (cnormG C : List α).length
decreasing_by assumption

/-- Case-3 simple-radical rational-part driver `radIntegrateCase3Wf der f g C = (Crem, vNum)`: the
`C/y` degree-lowering from an empty accumulator. Master identity `∫ C/y = vNum/y + ∫ Crem/y`. -/
def radIntegrateCase3Wf (der : CPolyG α → CPolyG α) (f g C : CPolyG α) : CPolyG α × CPolyG α :=
  radReduceCase3IterateWf der f g C []

/-! ## The multi-case dispatch `radIntegrateRationalWf` -/

/-- Multi-case simple-radical rational-part driver `radIntegrateRationalWf ρ R B` over `y² = ρ`,
denominator `B` monic, numerator `R` proper: squarefree-decompose `B` (`cSqfreeYunFFGWf`), split each
factor into its `V`-part / `W`-part (`cgcdWf`/`cdivWf` against `ρ`), partial-fraction `R`
(`radPartialFractionCoprime`), and dispatch each summand to the Case-1 / Case-2 Hermite descent.
Returns the per-factor reductions `(isV, Bᵢ, eᵢ, Nᵢ, vNumᵢ, Cremᵢ)`. `[CFracGcdCoreWf α]` supplies
the squarefree factorization. -/
def radIntegrateRationalWf [CFracGcdCoreWf α] (ρ R B : CPolyG α) :
    List (Bool × CPolyG α × ℕ × CPolyG α × CPolyG α × CPolyG α) :=
  let g : CPolyG α := cscaleG (CField.div CField.one (cnatCastG 2)) (cderivG ρ)   -- `½·ρ'` (n = 2)
  let factored : List (CPolyG α × ℕ) :=
    (cSqfreeYunFFGWf B).zipIdx.filterMap (fun (Bi, i) =>
      if cdegG Bi = 0 then none else some (Bi, i + 1))
  let split : List (Bool × CPolyG α × ℕ) :=
    factored.flatMap (fun (Bi, e) =>
      let Wi := cmonicG (cgcdWf Bi ρ).1
      let Vi := cdivWf Bi Wi
      (if cdegG Vi = 0 then [] else [(true, Vi, e)]) ++
      (if cdegG Wi = 0 then [] else [(false, Wi, e)]))
  let primePowers : List (CPolyG α) := split.map (fun (_, fi, e) => cpowG fi e)
  let nums : List (CPolyG α) := radPartialFractionCoprime R primePowers
  (split.zip nums).map (fun ((isV, fi, e), Ni) =>
    if isV then
      let (Crem, vNum) := radReduceCase1IterateWf cderivG fi (cderivG fi) ρ g e e Ni []
      (true, fi, e, Ni, vNum, Crem)
    else
      let (Crem, vNum) := radReduceCase2IterateWf fi (cdivWf ρ fi) ρ e e Ni []
      (false, fi, e, Ni, vNum, Crem))

end CPolyG

/-! ### The unified algebraic integrator `cIntegrateAlgebraicWf` (radical top-level) -/

/-- Unified algebraic integrator `cIntegrateAlgebraicWf ρ R B residual c D degBound` over `y² = ρ`:
`∫ R/(B·y) dx = v + c·log u` (principal case). Computes the rational part `v` by the multi-case
dispatch (`radIntegrateRationalWf` + `radAssembleRatPart`), then solves the log argument on
`residual` (`radLogArgSolve ρ residual D degBound`); on `none` returns just the rational part. -/
def cIntegrateAlgebraicWf (ρ : QFunNZG ℚ) (R B : CPolyG ℚ)
    (residual : RadElem (QFunNZG ℚ)) (c : QFunNZG ℚ) (D : CPolyG ℚ) (degBound : ℕ) :
    AlgIntegralResult :=
  let ρpoly : CPolyG ℚ := qxNum ρ
  let runs := CPolyG.radIntegrateRationalWf ρpoly R B
  let v := radAssembleRatPart ρ runs
  match radLogArgSolve ρ residual D degBound with
  | none => ⟨v, []⟩
  | some N =>
    let Dq : QFunNZG ℚ := qxOfNum D
    let u : RadElem (QFunNZG ℚ) := N.map (fun z => CField.div z Dq)
    ⟨v, [(c, u)]⟩

end DeepWiki.SymbolicIntegration
