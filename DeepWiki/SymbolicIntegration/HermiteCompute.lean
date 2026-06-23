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
the multiplicity until only squarefree denominators remain. We `native_decide`-validate it on
**Example 2.2.1** `f = (x⁷−24x⁴−4x²+8x−8)/(x⁸+6x⁶+12x⁴+8x²)`, whose book answer is
`∫ f = 1/x + 6x/(x²+2)² − (x−3)/(x²+2) + ∫ dx/x`: we pin the computed output and the correctness
identity `g' + B/D* = A/D` (cleared of denominators) by `native_decide` (kernel `decide` stalls on
GMP-backed `ℚ`). A `ratIntegrate` wires `hermiteReduce` into `lrtLogPart` for the full
`∫A/D = rational part + log part`. Agreement with the noncomputable `hermiteReducePower` is deferred. -/

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

/-! ### Example 2.2.1 (§2.2, p.40–41):
`f = (x⁷−24x⁴−4x²+8x−8)/(x⁸+6x⁶+12x⁴+8x²)`, `D = x²(x²+2)³`,
`∫ f = 1/x + 6x/(x²+2)² − (x−3)/(x²+2) + ∫ dx/x` -/

/-- **`A = x⁷ − 24x⁴ − 4x² + 8x − 8`** as a `CPoly` (Example 2.2.1 numerator), coefficients low→high:
`[−8, 8, −4, 0, −24, 0, 0, 1]`. -/
def cA221 : CPoly := [-8, 8, -4, 0, -24, 0, 0, 1]

/-- **`D = x⁸ + 6x⁶ + 12x⁴ + 8x² = x²(x²+2)³`** as a `CPoly` (Example 2.2.1 denominator),
coefficients low→high: `[0, 0, 8, 0, 12, 0, 6, 0, 1]`. -/
def cD221 : CPoly := [0, 0, 8, 0, 12, 0, 6, 0, 1]

-- **Example 2.2.1, the squarefree factorization** `D = x²·(x²+2)³`: Yun returns `[(x, 2), (x²+2, 3)]`.
#eval csqfreeFactor 40 cD221

-- **Example 2.2.1, the computed Hermite reduction** `((gnum, gden), (B, Dstar))`. Book answer:
-- `g = 1/x + 6x/(x²+2)² − (x−3)/(x²+2)`, residual `B/Dstar = 1/x` (so `∫ dx/x`),
-- `Dstar = x·(x²+2) = x³+2x`.
#eval hermiteReduce 40 cA221 cD221

/-- **Example 2.2.1: `D` factors as `x²·(x²+2)³`** (§2.2, p.40): the Yun squarefree factorization of
`D = x⁸+6x⁶+12x⁴+8x²` is `[(x, 2), (x²+2, 3)]` — the factor `x` of multiplicity `2` and `x²+2` of
multiplicity `3`. Proved by `native_decide`. -/
theorem hermite_ex221_factors :
    csqfreeFactor 40 cD221 = [([0, 1], 2), ([2, 0, 1], 3)] := by native_decide

/-- **Example 2.2.1: the residual log integrand is `(x²+2)/(x³+2x) = 1/x`** (§2.2, p.41): the squarefree
radical computed is `Dstar = x³ + 2x = x·(x²+2)` (`[0, 2, 0, 1]`) and the residual numerator is
`B = x² + 2` (`[2, 0, 1]`), so `B/Dstar = (x²+2)/(x(x²+2)) = 1/x` — exactly the book's remaining
`∫ dx/x`. Proved by `native_decide`. -/
theorem hermite_ex221_residual :
    (hermiteReduce 40 cA221 cD221).2 = ([2, 0, 1], [0, 2, 0, 1]) := by native_decide

/-- **Example 2.2.1: the Hermite reduction is correct** (§2.2, p.41) — the polynomial **correctness
certificate** for `∫ A/D = (gnum/gden) + ∫ B/Dstar`. As rational functions `(gnum/gden)' + B/Dstar =
A/D`; clearing the common denominator `D·gden²` (using `Dstar ∣ D`) gives the polynomial identity
`(A·gden² − D·(gnum'·gden − gnum·gden'))·Dstar = B·(D·gden²)`. This certifies, **independently of the
exact spelling of `g`**, that the computed `g = gnum/gden` is the rational part of `∫A/D` and `B/Dstar`
the residual purely-logarithmic part. Proved by `native_decide`. -/
theorem hermite_ex221_cleared_identity :
    let ((gnum, gden), (B, Dstar)) := hermiteReduce 40 cA221 cD221
    let gprimeNum := csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))
    let gden2 := cmul gden gden
    cnorm (cmul (csub (cmul cA221 gden2) (cmul cD221 gprimeNum)) Dstar)
      = cnorm (cmul B (cmul cD221 gden2)) := by native_decide

/-- **The book's rational part `g = 1/x + 6x/(x²+2)² − (x−3)/(x²+2)`** over the common denominator
`x·(x²+2)² = x⁵+4x³+4x`: numerator `3x³+8x²+6x+4` (`[4, 6, 8, 3]`), denominator `[0, 4, 0, 4, 0, 1]`. -/
def cBookG221 : QFun := ([4, 6, 8, 3], [0, 4, 0, 4, 0, 1])

/-- **Example 2.2.1: the computed rational part equals the book's `g`** (§2.2, p.41): the computed
`g = gnum/gden` from `hermiteReduce` equals — *as a rational function* — the book's explicit
`g = 1/x + 6x/(x²+2)² − (x−3)/(x²+2)` (`cBookG221`). Cross-multiplied: `gnum·(book den) = (book num)·gden`.
Proved by `native_decide` — the computed Hermite rational part matches the book exactly. -/
theorem hermite_ex221_g_eq_book :
    let ((gnum, gden), _) := hermiteReduce 40 cA221 cD221
    let (bn, bd) := cBookG221
    cnorm (cmul gnum bd) = cnorm (cmul bn gden) := by native_decide

/-! ### Full rational integrator: Hermite rational part + LRT log part -/

/-- **Full rational-function integrator** `ratIntegrate fuel A D = ((gnum, gden), logpart)`: combine the
Hermite rational part `g = gnum/gden` of `∫A/D` (from `hermiteReduce`) with the LRT logarithmic part of
the residual `∫B/Dstar` (from `lrtLogPart` on the squarefree `Dstar`). So
`∫ A/D = gnum/gden + ∑ᵢ ∑_{Qᵢ(a)=0} a·log(Sᵢ(a,x))`, the complete in-field-plus-logarithms integral.
`#eval`-demonstrated below. -/
def ratIntegrate (fuel : ℕ) (A D : CPoly) : QFun × List (CPoly × BPoly) :=
  let ((gnum, gden), (B, Dstar)) := hermiteReduce fuel A D
  ((gnum, gden), lrtLogPart fuel B Dstar)

-- **Example 2.2.1 via `ratIntegrate`**: the rational part `g = gnum/gden` plus the LRT log part of the
-- residual `B/Dstar = 1/x`. The residual `∫ dx/x = log(x)` gives a single residue `1` with argument
-- `x`. Prints the full integral data `((gnum, gden), logpart)`.
#eval ratIntegrate 40 cA221 cD221

/-! ### Agreement with the noncomputable `hermiteReducePower` — DEFERRED
Under the `toPoly` bridge, the computable `hermiteReduce` should agree (as rational functions) with the
noncomputable `hermiteReducePower`/`hermiteReduce_full` of `RationalIntegrationAlgorithms`: both return
`(g, B, Dstar)` with `∫A/D = g + ∫B/Dstar` and `Dstar` squarefree, the rational part `g` unique up to an
additive constant absorbed into the log part. Proving this requires aligning `cdiophantine`'s Bézout
cofactors with `diophantineSolveReduced` (agreement up to the `gcd`-normalizing unit, which cancels in
the fraction `B/Vʲ`), matching `csqfreeFactor` to Mathlib's squarefree factorization, and reconciling
the per-factor quadratic loop with `hermiteReducePower`'s prime-power recursion. The validated
`native_decide` computation on Example 2.2.1 (`hermite_ex221_residual`, `hermite_ex221_cleared_identity`)
— the *correctness identity* `g' + B/Dstar = A/D` certified directly — is the primary deliverable; this
agreement is the stretch and is left for a follow-up. -/

end Compute

end DeepWiki.SymbolicIntegration
