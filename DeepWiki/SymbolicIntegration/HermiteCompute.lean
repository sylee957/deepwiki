import DeepWiki.SymbolicIntegration.Exercise22Compute

/-! # Computable Hermite reduction over `ℚ` (Bronstein §2.2, Example 2.2.1, p.40–41)
Hermite reduction computes the **rational part** of `∫ A/D`: it returns `(g, B, D*)` with
`∫ A/D = g + ∫ B/D*` and `D*` squarefree, so the remaining `∫ B/D*` is purely logarithmic (the LRT
engine of `Exercise22Compute`/`RtResultantCompute` handles it). Mathlib's `ℚ[X]` arithmetic is
**noncomputable**, so the abstract `hermiteReducePower` (in `RationalIntegrationAlgorithms`) cannot
`#eval`. Here we give a genuinely **computable**, `#eval`-able rendering on the dense coefficient
carrier `CPoly := List ℚ` (from `LogToAtanCompute`), running the §2.2 *quadratic* Hermite reduction:
squarefree-factor `D = ∏ Dᵢ^i` (`csqfreeFactor`), and for each factor `(V, i)` with `i ≥ 2`, peel the
rational pieces `B/V^j` (`j = i−1 … 1`) into `g` via the Bézout solve `B·(U·V') + C·V = −A/j`, lowering
the multiplicity until only squarefree denominators remain. The engine is `native_decide`-validated on
**Example 2.2.1** `f = (x⁷−24x⁴−4x²+8x−8)/(x⁸+6x⁶+12x⁴+8x²)`, book answer
`∫ f = 1/x + 6x/(x²+2)² − (x−3)/(x²+2) + ∫ dx/x` — the worked-example witnesses (pinned output and the
cleared correctness identity `g' + B/D* = A/D`) live in the source catalog (`Sources/`). A
`ratIntegrate` wires `hermiteReduce` into `lrtLogPart` for the full
`∫A/D = rational part + log part`. Correctness against the noncomputable Hermite theory is **proven**
in `HermiteCorrectness`. -/

namespace DeepWiki.SymbolicIntegration

namespace Compute

/-! ### Rational-function arithmetic on `CPoly × CPoly` (numerator, denominator) -/

/-- **Rational function** as a `(numerator, denominator)` pair of `CPoly`s; `qzero = 0/1`. -/
abbrev QFun := CPoly × CPoly

/-- **Zero rational function** `0/1`. -/
def qzero : QFun := ([], [1])

/-- **Addition of rational functions** `a/b + c/d = (a·d + c·b)/(b·d)` (no gcd reduction; fractions stay
unreduced — fine for the exact-`ℚ` `native_decide` checks). -/
def qadd (x y : QFun) : QFun :=
  let (a, b) := x
  let (c, d) := y
  (cadd (cmul a d) (cmul c b), cmul b d)

/-! ### Computable Bézout / Diophantine solver on `CPoly` -/

/-- **Diophantine/Bézout solver** `cdiophantine fuel p q rhs = (B, C)` solving `B·p + C·q = rhs` with
`deg B < deg q`, for **coprime** `p, q` (so `gcd(p,q)` is a nonzero constant). From `cgcdExt p q =
(g, s, t)` with `s·p + t·q = g`: scale `(s,t)` by `rhs/g` (`g` constant), then reduce the first cofactor
mod `q` (`S = quo·q + B`, `deg B < deg q`) and absorb `quo·p` into the second (`C = T + quo·p`). Mirrors
the noncomputable `diophantineSolveReduced`. -/
def cdiophantine (fuel : ℕ) (p q rhs : CPoly) : CPoly × CPoly :=
  let (g, s, t) := cgcdExt fuel p q
  let gc : ℚ := clead g
  let S := cscale gc⁻¹ (cmul rhs s)
  let T := cscale gc⁻¹ (cmul rhs t)
  let (quo, B) := cdivmod fuel S q
  let C := cadd T (cmul quo p)
  (cnorm B, cnorm C)

/-! ### The computable quadratic Hermite reduction (per squarefree factor) -/

/-- **Inner Hermite loop** over one squarefree factor `V` of multiplicity `i` (§2.2, quadratic version,
p.41). With `U = D/Vⁱ` fixed, iterate `j = i−1, …, 1` (driven by a `ℕ` counter `j`): solve
`B·(U·V') + C·V = −A/j` with `deg B < deg V` (`cdiophantine`), accumulate the rational summand `B/Vʲ`
into `g` (`qadd`), and update `A ← −j·C − U·B'`. Returns the accumulated rational part `g` and the
final numerator `A` (over the deflated denominator). Fuel = the counter `j` itself. -/
def hermiteInner (fuel : ℕ) (V U : CPoly) : ℕ → CPoly → QFun → QFun × CPoly
  | 0, A, g => (g, A)
  | j + 1, A, g =>
    let jval : ℚ := (j : ℚ) + 1
    let Vderiv := cderiv V
    let p := cmul U Vderiv
    let rhs := cscale (-jval⁻¹) A                         -- `−A/j`
    let (B, C) := cdiophantine fuel p V rhs
    -- summand `B/Vʲ`: denominator is `V` raised to power `j+1`.
    let Vpow := (List.range (j + 1)).foldl (fun acc _ => cmul acc V) [1]
    let g' := qadd g (B, Vpow)
    let A' := csub (cscale (-jval) C) (cmul U (cderiv B))  -- `A ← −j·C − U·B'`
    hermiteInner fuel V U j A' g'

/-- **Quadratic Hermite reduction** `hermiteReduce fuel A D = ((gnum, gden), (B, Dstar))` (§2.2, p.41):
returns the rational part `g = gnum/gden ∈ ℚ(x)` (already-integrated) and the reduced integrand
`B/Dstar` with `Dstar` squarefree, so `∫ A/D = g + ∫ B/Dstar`. Algorithm: squarefree-factor `D` (Yun,
`csqfreeFactor`); the squarefree radical `Dstar = ∏ᵢ Vᵢ` is the final denominator. For each factor
`(V, i)` of multiplicity `i ≥ 2`, run `hermiteInner` (peeling `B/Vʲ` for `j = i−1 … 1` against the full
current numerator `A` over the global denominator `D`), accumulating each `B/Vʲ` into the rational part
`g`. The residual log-part numerator `B` over `Dstar` is then recovered exactly from the defining
identity `A/D = g' + B/Dstar` by clearing denominators and dividing. Pure functional `def` — it `#eval`s. -/
def hermiteReduce (fuel : ℕ) (A D : CPoly) : QFun × QFun :=
  let factors := csqfreeFactor fuel D
  let Dstar := factors.foldl (fun acc (Vi, _) => cmul acc Vi) [1]
  -- Accumulate the rational part `g`. Each factor of multiplicity `i ≥ 2` contributes via `hermiteInner`
  -- against the global numerator `A` over `D` (the inner solve uses `U = D/Vⁱ`, so `B/Vʲ` is correctly
  -- scaled relative to the full `A/D`).
  let g : QFun := factors.foldl
    (fun (gAcc : QFun) (Vi, i) =>
      if i ≤ 1 then gAcc
      else
        let Vi_pow := (List.range i).foldl (fun acc _ => cmul acc Vi) [1]
        let U := cdiv fuel D Vi_pow
        let (gloc, _) := hermiteInner fuel Vi U (i - 1) A qzero
        qadd gAcc gloc)
    qzero
  let (gnum, gden) := g
  -- residual numerator `B` over `Dstar`, from `A/D − g' = B/Dstar`:
  -- `(A·gden² − D·(gnum'·gden − gnum·gden'))·Dstar / (D·gden²)` (exact division to a polynomial).
  let gprimeNum := csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))
  let gden2 := cmul gden gden
  let resNum := csub (cmul A gden2) (cmul D gprimeNum)
  let resDen := cmul D gden2
  let Bres := cdiv fuel (cmul resNum Dstar) resDen
  ((cnorm gnum, cnorm gden), (cnorm Bres, cnorm Dstar))

/-! ### Full rational integrator: Hermite rational part + LRT log part -/

/-- **Full rational-function integrator** `ratIntegrate fuel A D = ((gnum, gden), logpart)`: combine the
Hermite rational part `g = gnum/gden` of `∫A/D` (from `hermiteReduce`) with the LRT logarithmic part of
the residual `∫B/Dstar` (from `lrtLogPart` on the squarefree `Dstar`). So
`∫ A/D = gnum/gden + ∑ᵢ ∑_{Qᵢ(a)=0} a·log(Sᵢ(a,x))`, the complete in-field-plus-logarithms integral. -/
def ratIntegrate (fuel : ℕ) (A D : CPoly) : QFun × List (CPoly × BPoly) :=
  let ((gnum, gden), (B, Dstar)) := hermiteReduce fuel A D
  ((gnum, gden), lrtLogPart fuel B Dstar)

/-! ### Correctness against the noncomputable Hermite theory — PROVEN in `HermiteCorrectness`
Under the `toPoly` bridge, the computable `hermiteReduce` produces a valid Hermite reduction on **all**
inputs: `hermiteReduce_residual_correct_uncond'` (with `hermiteInner_spec` for the inner step) certifies
the residual identity `g' + B/Dstar = A/D` as rational functions, with the rational part `g` unique up
to an additive constant absorbed into the log part. Every piece the algorithm relies on is in place:
`toPoly_cdiophantine_eq` aligns `cdiophantine`'s Bézout cofactors with `diophantineSolveReduced` (the
`gcd`-normalizing unit cancels in the fraction `B/Vʲ`); `csqfreeFactor_squarefree`,
`csqfreeFactor_pairwise_isRelPrime`, and `csqfreeFactor_factor_assoc` match `csqfreeFactor` to the
abstract Yun/Musser squarefree factorization; and `total_fold_residual_over_D` sums the per-factor
multi-fold residual (the interference `W ∣ R` discharged via the `IsQRegular` localization). -/

end Compute

end DeepWiki.SymbolicIntegration
