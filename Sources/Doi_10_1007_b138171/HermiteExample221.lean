import DeepWiki.SymbolicIntegration.Compute.Hermite.ResidualCorrectness
import DeepWiki.SymbolicIntegration.Engine.YunSquarefreeDecomposition

/-! # Bronstein Example 2.2.1 — Hermite reduction worked example

The `ccompute`-validated run of the generic tower Hermite engine specialized to `ℚ[x]` on
Bronstein §2.2, Example 2.2.1 (p.40–41):
`f = (x⁷−24x⁴−4x²+8x−8)/(x⁸+6x⁶+12x⁴+8x²)`, `D = x²(x²+2)³`,
`∫ f = 1/x + 6x/(x²+2)² − (x−3)/(x²+2) + ∫ dx/x`. The general algorithm and its abstract
correctness lives in the generic `Engine/Hermite` development;
this catalog file carries the book-specific concrete witnesses (the pinned output, the cleared
polynomial certificate, and the upgraded `RatFunc ℚ` correctness identities). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### Example 2.2.1 (§2.2, p.40–41):
`f = (x⁷−24x⁴−4x²+8x−8)/(x⁸+6x⁶+12x⁴+8x²)`, `D = x²(x²+2)³`,
`∫ f = 1/x + 6x/(x²+2)² − (x−3)/(x²+2) + ∫ dx/x` -/

/-- **`A = x⁷ − 24x⁴ − 4x² + 8x − 8`** as a `DensePoly ℚ` (Example 2.2.1 numerator), coefficients low→high:
`[−8, 8, −4, 0, −24, 0, 0, 1]`. -/
def cA221 : DensePoly ℚ := [-8, 8, -4, 0, -24, 0, 0, 1]

/-- **`D = x⁸ + 6x⁶ + 12x⁴ + 8x² = x²(x²+2)³`** as a `DensePoly ℚ` (Example 2.2.1 denominator),
coefficients low→high: `[0, 0, 8, 0, 12, 0, 6, 0, 1]`. -/
def cD221 : DensePoly ℚ := [0, 0, 8, 0, 12, 0, 6, 0, 1]

-- **Example 2.2.1, the squarefree factorization** `D = x²·(x²+2)³`: Yun returns `[(x, 2), (x²+2, 3)]`.
#eval CPoly.squarefreeYunFactors cD221

-- **Example 2.2.1, the computed Hermite reduction** `((gnum, gden), (B, Dstar))`. Book answer:
-- `g = 1/x + 6x/(x²+2)² − (x−3)/(x²+2)`, residual `B/Dstar = 1/x` (so `∫ dx/x`),
-- `Dstar = x·(x²+2) = x³+2x`.
#eval DensePoly.cHermiteReduceTower ([1] : DensePoly ℚ) cA221 cD221

/-- **Example 2.2.1: `D` factors as `x²·(x²+2)³`** (§2.2, p.40): the Yun squarefree factorization of
`D = x⁸+6x⁶+12x⁴+8x²` is `[(x, 2), (x²+2, 3)]` — the factor `x` of multiplicity `2` and `x²+2` of
multiplicity `3`. Proved by `ccompute`. -/
theorem hermite_ex221_factors :
    CPoly.squarefreeYunFactors cD221 = [([0, 1], 2), ([2, 0, 1], 3)] := by ccompute

/-- **Example 2.2.1: the residual log integrand is `(x²+2)/(x³+2x) = 1/x`** (§2.2, p.41): the squarefree
radical computed is `Dstar = x³ + 2x = x·(x²+2)` (`[0, 2, 0, 1]`) and the residual numerator is
`B = x² + 2` (`[2, 0, 1]`), so `B/Dstar = (x²+2)/(x(x²+2)) = 1/x` — exactly the book's remaining
`∫ dx/x`. Proved by `ccompute`. -/
theorem hermite_ex221_residual :
    (DensePoly.cHermiteReduceTower ([1] : DensePoly ℚ) cA221 cD221).2 =
      ([2, 0, 1], [0, 2, 0, 1]) := by ccompute

/-- **Example 2.2.1: the Hermite reduction is correct** (§2.2, p.41) — the polynomial **correctness
certificate** for `∫ A/D = (gnum/gden) + ∫ B/Dstar`. As rational functions `(gnum/gden)' + B/Dstar =
A/D`; clearing the common denominator `D·gden²` (using `Dstar ∣ D`) gives the polynomial identity
`(A·gden² − D·(gnum'·gden − gnum·gden'))·Dstar = B·(D·gden²)`. This certifies, **independently of the
exact spelling of `g`**, that the computed `g = gnum/gden` is the rational part of `∫A/D` and `B/Dstar`
the residual purely-logarithmic part. Proved by `ccompute`. -/
theorem hermite_ex221_cleared_identity :
    let ((gnum, gden), (B, Dstar)) :=
      DensePoly.cHermiteReduceTower ([1] : DensePoly ℚ) cA221 cD221
    let gprimeNum := csub (cmul (cderiv gnum) gden) (cmul gnum (cderiv gden))
    let gden2 := cmul gden gden
    cnorm (cmul (csub (cmul cA221 gden2) (cmul cD221 gprimeNum)) Dstar)
      = cnorm (cmul B (cmul cD221 gden2)) := by ccompute

/-- **The book's rational part `g = 1/x + 6x/(x²+2)² − (x−3)/(x²+2)`** over the common denominator
`x·(x²+2)² = x⁵+4x³+4x`: numerator `3x³+8x²+6x+4` (`[4, 6, 8, 3]`), denominator `[0, 4, 0, 4, 0, 1]`. -/
def cBookG221 : DenseFrac ℚ :=
  CFrac.ofFraction ([4, 6, 8, 3] : DensePoly ℚ) ([0, 4, 0, 4, 0, 1] : DensePoly ℚ)
    (by ccompute)

/-- **Example 2.2.1: the computed rational part equals the book's `g`** (§2.2, p.41): the computed
`g = gnum/gden` from `cHermiteReduceTower [1]` equals — *as a rational function* — the book's explicit
`g = 1/x + 6x/(x²+2)² − (x−3)/(x²+2)` (`cBookG221`). Cross-multiplied: `gnum·(book den) = (book num)·gden`.
Proved by `ccompute` — the computed Hermite rational part matches the book exactly. -/
theorem hermite_ex221_g_eq_book :
    let ((gnum, gden), _) :=
      DensePoly.cHermiteReduceTower ([1] : DensePoly ℚ) cA221 cD221
    cnorm (cmul gnum (CFrac.den cBookG221)) =
      cnorm (cmul (CFrac.num cBookG221) gden) := by ccompute

-- **Example 2.2.1 via `ratIntegrate`**: the rational part `g = gnum/gden` plus the LRT log part of the
-- residual `B/Dstar = 1/x`. The residual `∫ dx/x = log(x)` gives a single residue `1` with argument
-- `x`. Prints the full integral data `((gnum, gden), logpart)`.
#eval (ratIntegrate 40 cA221 cD221).1.isSome

/-! ### Example 2.2.1: the certificate is real

The exact-division certificate `hexact` is not vacuous: on Example 2.2.1 the residual `CPolyEuclidean.div`
divides exactly (`hermite_ex221_exact_division`, `ccompute`). Feeding it to
`hermiteReduce_residual_correct` gives the *rational-function* correctness identity
`am A/am D = (ratFuncOfPair g)′ + am Bres/am Dstar` for the concrete computed reduction — upgrading the
`ccompute` polynomial cleared identity to an honest `RatFunc ℚ` equality. -/

/-- **Example 2.2.1: the residual division is exact** — the remainder of `(resNum·Dstar)` by
`(D·gden²)` reads to `0` (`cnorm … = []`), so `Bres = CPolyEuclidean.div …` is honest `ℚ[X]` division. The
computed rational part is `gnum = [8,12,20,12,8,3]`, `gden = [0,8,0,12,0,6,0,1]`, and the squarefree
radical `Dstar = [0,2,0,1] = x³+2x`. Proved by `ccompute`. -/
theorem hermite_ex221_exact_division :
    cnorm (CPolyEuclidean.mod
      (cmul (csub (cmul cA221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))
          (cmul cD221 (csub (cmul (cderiv [8, 12, 20, 12, 8, 3]) [0, 8, 0, 12, 0, 6, 0, 1])
            (cmul [8, 12, 20, 12, 8, 3] (cderiv [0, 8, 0, 12, 0, 6, 0, 1]))))) [0, 2, 0, 1])
      (cmul cD221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))) = [] := by
  ccompute

open scoped Differential in
/-- **Example 2.2.1: the Hermite reduction is correct as a `RatFunc ℚ` identity** (§2.2, p.41):
`am A/am D = (ratFuncOfPair (gnum,gden))′ + am Bres/am Dstar` for the concrete computed `gnum, gden, Dstar`
of Example 2.2.1, with `Bres = CPolyEuclidean.div … (resNum·Dstar) (D·gden²)`. Honest `ℚ(x)` equality (not just the
cleared polynomial certificate), obtained from `hermiteReduce_residual_correct` with the exact-division
certificate discharged by `hermite_ex221_exact_division`. The nonzero hypotheses (`D, gden, Dstar`)
hold since their `toPoly`/`cnorm` are nonzero (checked by `ccompute`/`decide`). -/
example :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly cA221) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly cD221)
      = (ratFuncOfPair ([8, 12, 20, 12, 8, 3], [0, 8, 0, 12, 0, 6, 0, 1]))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (CPolyEuclidean.div
              (cmul (csub (cmul cA221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))
                  (cmul cD221 (csub (cmul (cderiv [8, 12, 20, 12, 8, 3]) [0, 8, 0, 12, 0, 6, 0, 1])
                    (cmul [8, 12, 20, 12, 8, 3] (cderiv [0, 8, 0, 12, 0, 6, 0, 1]))))) [0, 2, 0, 1])
              (cmul cD221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly ([0, 2, 0, 1] : DensePoly ℚ)) := by
  have hD : CPoly.toPoly cD221 ≠ 0 :=
    CPolyEngine.toPoly_ne_zero_of_cisZero_eq_false (p := cD221) (by decide)
  have hgden : CPoly.toPoly ([0, 8, 0, 12, 0, 6, 0, 1] : DensePoly ℚ) ≠ 0 :=
    CPolyEngine.toPoly_ne_zero_of_cisZero_eq_false (p :=
      ([0, 8, 0, 12, 0, 6, 0, 1] : DensePoly ℚ)) (by decide)
  have hDstar : CPoly.toPoly ([0, 2, 0, 1] : DensePoly ℚ) ≠ 0 :=
    CPolyEngine.toPoly_ne_zero_of_cisZero_eq_false (p :=
      ([0, 2, 0, 1] : DensePoly ℚ)) (by decide)
  have hexact : toPoly (CPolyEuclidean.mod
      (cmul (csub (cmul cA221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))
          (cmul cD221 (csub (cmul (cderiv [8, 12, 20, 12, 8, 3]) [0, 8, 0, 12, 0, 6, 0, 1])
            (cmul [8, 12, 20, 12, 8, 3] (cderiv [0, 8, 0, 12, 0, 6, 0, 1]))))) [0, 2, 0, 1])
      (cmul cD221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))) = 0 := by
    rw [← DensePoly.cnormG_eq_nil_iff, hermite_ex221_exact_division]
  have hexact' : CPoly.toPoly (CPolyEuclidean.mod
      (CPolyEngine.mul
        (CPolyEngine.sub
          (CPolyEngine.mul cA221
            (CPolyEngine.mul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))
          (CPolyEngine.mul cD221
            (CPolyEngine.sub
              (CPolyEngine.mul (CPolyEngine.deriv [8, 12, 20, 12, 8, 3])
                [0, 8, 0, 12, 0, 6, 0, 1])
              (CPolyEngine.mul [8, 12, 20, 12, 8, 3]
                (CPolyEngine.deriv [0, 8, 0, 12, 0, 6, 0, 1])))))
        [0, 2, 0, 1])
      (CPolyEngine.mul cD221
        (CPolyEngine.mul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))) = 0 := by
    simpa only [CPolyEuclidean.mod_dense_eq, CPolyEngine.mul_dense_eq,
      CPolyEngine.sub_dense_eq, CPolyEngine.deriv_dense_eq, toPoly_list_eq] using hexact
  simpa only [CPolyEuclidean.div_dense_eq, CPolyEngine.mul_dense_eq,
    CPolyEngine.sub_dense_eq, CPolyEngine.deriv_dense_eq, toPoly_list_eq] using
    (hermiteReduce_residual_correct cA221 cD221 [8, 12, 20, 12, 8, 3]
      [0, 8, 0, 12, 0, 6, 0, 1] [0, 2, 0, 1] ⟨hD, hgden, hDstar⟩ hexact')

/-! ### Example 2.2.1: the unconditional wrapper, certificate `ccompute`d

The decidable residual-honesty bundle `HermiteResComp` holds on Example 2.2.1 (`ccompute`), so the
**unconditional** wrapper applies with *no* exact-division hypothesis supplied: the certificate is the
engine's own `cmod`-computation, checked by `ccompute`. This is the honest `RatFunc ℚ` correctness
of the computed Hermite reduction for `f = (x⁷−24x⁴−4x²+8x−8)/(x⁸+6x⁶+12x⁴+8x²)` with the certificate
fully internal. -/

/-- **Example 2.2.1: the residual-honesty bundle holds** (`ccompute`): both split `cmod`-remainders
of the computed `(gnum, gden, Dstar) = ([8,12,20,12,8,3], [0,8,0,12,0,6,0,1], [0,2,0,1])` vanish, so
`HermiteResComp cA221 cD221 gnum gden Dstar` — the engine certifies its own residual recovery. -/
theorem hermite_ex221_resComp :
    HermiteResComp cA221 cD221 [8, 12, 20, 12, 8, 3] [0, 8, 0, 12, 0, 6, 0, 1] [0, 2, 0, 1] := by
  ccompute

open scoped Differential in
/-- **Example 2.2.1: the unconditional Hermite reduction is correct as a `RatFunc ℚ` identity** (§2.2,
p.41): `am A/am D = (ratFuncOfPair (gnum,gden))′ + am Bres/am Dstar` for the computed `gnum, gden, Dstar` of
Example 2.2.1, with **no** exact-division certificate as a hypothesis — the certificate is discharged by
the `ccompute`'d residual-honesty bundle `hermite_ex221_resComp` through
`hermiteReduce_residual_correct_uncond`. The nonzero hypotheses hold by `decide`. -/
example :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly cA221) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly cD221)
      = (ratFuncOfPair ([8, 12, 20, 12, 8, 3], [0, 8, 0, 12, 0, 6, 0, 1]))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (CPolyEuclidean.div
              (cmul (csub (cmul cA221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))
                  (cmul cD221 (csub (cmul (cderiv [8, 12, 20, 12, 8, 3]) [0, 8, 0, 12, 0, 6, 0, 1])
                    (cmul [8, 12, 20, 12, 8, 3] (cderiv [0, 8, 0, 12, 0, 6, 0, 1]))))) [0, 2, 0, 1])
              (cmul cD221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly ([0, 2, 0, 1] : DensePoly ℚ)) := by
  have hD : CPoly.toPoly cD221 ≠ 0 :=
    CPolyEngine.toPoly_ne_zero_of_cisZero_eq_false (p := cD221) (by decide)
  have hgden : CPoly.toPoly ([0, 8, 0, 12, 0, 6, 0, 1] : DensePoly ℚ) ≠ 0 :=
    CPolyEngine.toPoly_ne_zero_of_cisZero_eq_false (p :=
      ([0, 8, 0, 12, 0, 6, 0, 1] : DensePoly ℚ)) (by decide)
  have hDstar : CPoly.toPoly ([0, 2, 0, 1] : DensePoly ℚ) ≠ 0 :=
    CPolyEngine.toPoly_ne_zero_of_cisZero_eq_false (p :=
      ([0, 2, 0, 1] : DensePoly ℚ)) (by decide)
  simpa only [CPolyEuclidean.div_dense_eq, CPolyEngine.mul_dense_eq,
    CPolyEngine.sub_dense_eq, CPolyEngine.deriv_dense_eq, toPoly_list_eq] using
    (hermiteReduce_residual_correct_uncond cA221 cD221 [8, 12, 20, 12, 8, 3]
      [0, 8, 0, 12, 0, 6, 0, 1] [0, 2, 0, 1]
      ⟨hD, hgden, hDstar⟩ hermite_ex221_resComp)

/-! ### Example 2.2.1 via the radical wrapper: `Dstar ∣ D` from the proven Yun radical clause

The radical wrapper `hermiteReduce_residual_correct_of_radical` consumes `Dstar ∣ D` as a hypothesis,
which for Example 2.2.1 follows from the generic fuel-free Yun radical-divides theorem, transported to
the literal radical `[0,2,0,1]` by the computed fold equality. -/

/-- **Example 2.2.1: the radical `[0,2,0,1]` divides `D`** by generic Yun correctness. -/
theorem hermite_ex221_Dstar_dvd : toPoly ([0, 2, 0, 1] : DensePoly ℚ) ∣ toPoly cD221 := by
  have hfold : (DensePoly.cSqfreeYunFF cD221).foldl (fun acc vi => cmul acc vi) [1]
      = [0, 2, 0, 1] := by ccompute
  have hD : toPoly cD221 ≠ 0 := by
    intro h
    have : cnorm cD221 = [] := (DensePoly.cnormG_eq_nil_iff cD221).mpr h
    revert this
    decide
  have hdiv := prod_map_cSqfreeYunFFG_dvd cgcdFFCoreWf_correct_Q cD221
    (by exact hD)
  have hread := toPolyG_foldl_cmulG_plainList ([1] : DensePoly ℚ)
    (DensePoly.cSqfreeYunFF cD221)
  have hfoldDiv :
      DensePoly.toPoly ((DensePoly.cSqfreeYunFF cD221).foldl (fun acc vi => cmul acc vi) [1])
        ∣ DensePoly.toPoly cD221 := by
    rw [hread]
    simpa [DensePoly.toPolyG_cons] using hdiv
  rw [hfold] at hfoldDiv
  exact hfoldDiv

open scoped Differential in
/-- **Example 2.2.1: the unconditional Hermite reduction via the radical wrapper** (§2.2, p.41):
`am A/am D = (ratFuncOfPair (gnum,gden))′ + am Bres/am Dstar` with the radical clause `Dstar ∣ D` discharged
by the *proven* `hermite_ex221_Dstar_dvd` (Yun radical-divides), and only the single residual cert
`ccompute`'d. The cleanest split — abstract radical content proven, one residual cert checked. -/
example :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly cA221) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly cD221)
      = (ratFuncOfPair ([8, 12, 20, 12, 8, 3], [0, 8, 0, 12, 0, 6, 0, 1]))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (CPolyEuclidean.div
              (cmul (csub (cmul cA221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))
                  (cmul cD221 (csub (cmul (cderiv [8, 12, 20, 12, 8, 3]) [0, 8, 0, 12, 0, 6, 0, 1])
                    (cmul [8, 12, 20, 12, 8, 3] (cderiv [0, 8, 0, 12, 0, 6, 0, 1]))))) [0, 2, 0, 1])
              (cmul cD221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly ([0, 2, 0, 1] : DensePoly ℚ)) := by
  have hD : CPoly.toPoly cD221 ≠ 0 :=
    CPolyEngine.toPoly_ne_zero_of_cisZero_eq_false (p := cD221) (by decide)
  have hgden : CPoly.toPoly ([0, 8, 0, 12, 0, 6, 0, 1] : DensePoly ℚ) ≠ 0 :=
    CPolyEngine.toPoly_ne_zero_of_cisZero_eq_false (p :=
      ([0, 8, 0, 12, 0, 6, 0, 1] : DensePoly ℚ)) (by decide)
  have hDstar : CPoly.toPoly ([0, 2, 0, 1] : DensePoly ℚ) ≠ 0 :=
    CPolyEngine.toPoly_ne_zero_of_cisZero_eq_false (p :=
      ([0, 2, 0, 1] : DensePoly ℚ)) (by decide)
  have hWgd : toPoly (CPolyEuclidean.mod
      (csub (cmul cA221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))
        (cmul cD221 (csub (cmul (cderiv [8, 12, 20, 12, 8, 3]) [0, 8, 0, 12, 0, 6, 0, 1])
          (cmul [8, 12, 20, 12, 8, 3] (cderiv [0, 8, 0, 12, 0, 6, 0, 1])))))
      (cmul (CPolyEuclidean.div cD221 [0, 2, 0, 1])
        (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))) = 0 := by
    rw [← DensePoly.cnormG_eq_nil_iff]; ccompute
  simpa only [CPolyEuclidean.div_dense_eq, CPolyEngine.mul_dense_eq,
    CPolyEngine.sub_dense_eq, CPolyEngine.deriv_dense_eq, toPoly_list_eq] using
    (hermiteReduce_residual_correct_of_radical cA221 cD221 [8, 12, 20, 12, 8, 3]
      [0, 8, 0, 12, 0, 6, 0, 1] [0, 2, 0, 1] ⟨hD, hgden, hDstar⟩
      (by simpa only [toPoly_list_eq] using hermite_ex221_Dstar_dvd)
      (by simpa only [CPolyEuclidean.mod_dense_eq, CPolyEuclidean.div_dense_eq,
        CPolyEngine.mul_dense_eq, CPolyEngine.sub_dense_eq, CPolyEngine.deriv_dense_eq,
        toPoly_list_eq] using hWgd))

end DeepWiki.SymbolicIntegration.Compute
