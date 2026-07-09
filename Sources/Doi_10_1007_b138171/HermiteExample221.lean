import DeepWiki.SymbolicIntegration.HermiteCorrectness

/-! # Bronstein Example 2.2.1 — Hermite reduction worked example

The `native_decide`-validated run of the computable Hermite engine (`HermiteCompute`) on
Bronstein §2.2, Example 2.2.1 (p.40–41):
`f = (x⁷−24x⁴−4x²+8x−8)/(x⁸+6x⁶+12x⁴+8x²)`, `D = x²(x²+2)³`,
`∫ f = 1/x + 6x/(x²+2)² − (x−3)/(x²+2) + ∫ dx/x`. The general algorithm and its abstract
correctness live in `DeepWiki/SymbolicIntegration/` (`HermiteCompute`, `HermiteCorrectness`);
this catalog file carries the book-specific concrete witnesses (the pinned output, the cleared
polynomial certificate, and the upgraded `RatFunc ℚ` correctness identities). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### Example 2.2.1 (§2.2, p.40–41):
`f = (x⁷−24x⁴−4x²+8x−8)/(x⁸+6x⁶+12x⁴+8x²)`, `D = x²(x²+2)³`,
`∫ f = 1/x + 6x/(x²+2)² − (x−3)/(x²+2) + ∫ dx/x` -/

/-- **`A = x⁷ − 24x⁴ − 4x² + 8x − 8`** as a `CPolyQ` (Example 2.2.1 numerator), coefficients low→high:
`[−8, 8, −4, 0, −24, 0, 0, 1]`. -/
def cA221 : CPolyQ := [-8, 8, -4, 0, -24, 0, 0, 1]

/-- **`D = x⁸ + 6x⁶ + 12x⁴ + 8x² = x²(x²+2)³`** as a `CPolyQ` (Example 2.2.1 denominator),
coefficients low→high: `[0, 0, 8, 0, 12, 0, 6, 0, 1]`. -/
def cD221 : CPolyQ := [0, 0, 8, 0, 12, 0, 6, 0, 1]

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

-- **Example 2.2.1 via `ratIntegrate`**: the rational part `g = gnum/gden` plus the LRT log part of the
-- residual `B/Dstar = 1/x`. The residual `∫ dx/x = log(x)` gives a single residue `1` with argument
-- `x`. Prints the full integral data `((gnum, gden), logpart)`.
#eval ratIntegrate 40 cA221 cD221

/-! ### Example 2.2.1: the certificate is real

The exact-division certificate `hexact` is not vacuous: on Example 2.2.1 the residual `cdiv`
divides exactly (`hermite_ex221_exact_division`, `native_decide`). Feeding it to
`hermiteReduce_residual_correct` gives the *rational-function* correctness identity
`am A/am D = (toQFun g)′ + am Bres/am Dstar` for the concrete computed reduction — upgrading the
`native_decide` polynomial cleared identity to an honest `RatFunc ℚ` equality. -/

/-- **Example 2.2.1: the residual division is exact** — the remainder of `(resNum·Dstar)` by
`(D·gden²)` reads to `0` (`cnorm … = []`), so `Bres = cdiv …` is honest `ℚ[X]` division. The
computed rational part is `gnum = [8,12,20,12,8,3]`, `gden = [0,8,0,12,0,6,0,1]`, and the squarefree
radical `Dstar = [0,2,0,1] = x³+2x`. Proved by `native_decide`. -/
theorem hermite_ex221_exact_division :
    cnorm (cmod 40
      (cmul (csub (cmul cA221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))
          (cmul cD221 (csub (cmul (cderiv [8, 12, 20, 12, 8, 3]) [0, 8, 0, 12, 0, 6, 0, 1])
            (cmul [8, 12, 20, 12, 8, 3] (cderiv [0, 8, 0, 12, 0, 6, 0, 1]))))) [0, 2, 0, 1])
      (cmul cD221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))) = [] := by
  native_decide

open scoped Differential in
/-- **Example 2.2.1: the Hermite reduction is correct as a `RatFunc ℚ` identity** (§2.2, p.41):
`am A/am D = (toQFun (gnum,gden))′ + am Bres/am Dstar` for the concrete computed `gnum, gden, Dstar`
of Example 2.2.1, with `Bres = cdiv … (resNum·Dstar) (D·gden²)`. Honest `ℚ(x)` equality (not just the
cleared polynomial certificate), obtained from `hermiteReduce_residual_correct` with the exact-division
certificate discharged by `hermite_ex221_exact_division`. The nonzero hypotheses (`D, gden, Dstar`)
hold since their `toPoly`/`cnorm` are nonzero (checked by `native_decide`/`decide`). -/
example :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly cA221) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly cD221)
      = (toQFun ([8, 12, 20, 12, 8, 3], [0, 8, 0, 12, 0, 6, 0, 1]))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (cdiv 40
              (cmul (csub (cmul cA221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))
                  (cmul cD221 (csub (cmul (cderiv [8, 12, 20, 12, 8, 3]) [0, 8, 0, 12, 0, 6, 0, 1])
                    (cmul [8, 12, 20, 12, 8, 3] (cderiv [0, 8, 0, 12, 0, 6, 0, 1]))))) [0, 2, 0, 1])
              (cmul cD221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly [0, 2, 0, 1]) := by
  have hD : toPoly cD221 ≠ 0 := fun h => by
    have : cnorm cD221 = [] := (cnorm_eq_nil_iff cD221).mpr h
    revert this; decide
  have hgden : toPoly [0, 8, 0, 12, 0, 6, 0, 1] ≠ 0 := fun h => by
    have : cnorm [0, 8, 0, 12, 0, 6, 0, 1] = [] := (cnorm_eq_nil_iff _).mpr h
    revert this; decide
  have hDstar : cnorm [0, 2, 0, 1] ≠ [] := by decide
  have hexact : toPoly (cmod 40
      (cmul (csub (cmul cA221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))
          (cmul cD221 (csub (cmul (cderiv [8, 12, 20, 12, 8, 3]) [0, 8, 0, 12, 0, 6, 0, 1])
            (cmul [8, 12, 20, 12, 8, 3] (cderiv [0, 8, 0, 12, 0, 6, 0, 1]))))) [0, 2, 0, 1])
      (cmul cD221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))) = 0 := by
    rw [← cnorm_eq_nil_iff, hermite_ex221_exact_division]
  exact hermiteReduce_residual_correct 40 cA221 cD221 [8, 12, 20, 12, 8, 3]
    [0, 8, 0, 12, 0, 6, 0, 1] [0, 2, 0, 1] ⟨hD, hgden, hDstar⟩ hexact

/-- **Example 2.2.1: the engine-honesty bundle holds** (`native_decide`): every `cmod`-remainder in the
Yun factorization of `D = x²(x²+2)³` vanishes, so `SqfreeExactComp 40 cD221` — and hence (via
`SqfreeExactComp_to_SqfreeExact`) the `toPoly` bundle `SqfreeExact 40 cD221` — holds. -/
theorem hermite_ex221_sqfreeExactComp : SqfreeExactComp 40 cD221 := by native_decide

/-- **Example 2.2.1: the Yun radical divides `D`** — the radical `Dstar = x(x²+2) = x³+2x` of
`csqfreeFactor 40 cD221` divides `D = x²(x²+2)³` in `ℚ[X]`. A concrete, non-vacuous instance of
`toPoly_Dstar_dvd_D`, discharged through the `native_decide`'d computable bundle
`hermite_ex221_sqfreeExactComp`. -/
example :
    toPoly ((csqfreeFactor 40 cD221).foldl (fun acc (vi : CPolyQ × ℕ) => cmul acc vi.1) [1])
      ∣ toPoly cD221 :=
  toPoly_Dstar_dvd_D 40 cD221 (SqfreeExactComp_to_SqfreeExact 40 cD221 hermite_ex221_sqfreeExactComp)

/-! ### Example 2.2.1: the unconditional wrapper, certificate `native_decide`d

The decidable residual-honesty bundle `HermiteResComp` holds on Example 2.2.1 (`native_decide`), so the
**unconditional** wrapper applies with *no* exact-division hypothesis supplied: the certificate is the
engine's own `cmod`-computation, checked by `native_decide`. This is the honest `RatFunc ℚ` correctness
of the computed Hermite reduction for `f = (x⁷−24x⁴−4x²+8x−8)/(x⁸+6x⁶+12x⁴+8x²)` with the certificate
fully internal. -/

/-- **Example 2.2.1: the residual-honesty bundle holds** (`native_decide`): both split `cmod`-remainders
of the computed `(gnum, gden, Dstar) = ([8,12,20,12,8,3], [0,8,0,12,0,6,0,1], [0,2,0,1])` vanish, so
`HermiteResComp 40 cA221 cD221 gnum gden Dstar` — the engine certifies its own residual recovery. -/
theorem hermite_ex221_resComp :
    HermiteResComp 40 cA221 cD221 [8, 12, 20, 12, 8, 3] [0, 8, 0, 12, 0, 6, 0, 1] [0, 2, 0, 1] := by
  native_decide

open scoped Differential in
/-- **Example 2.2.1: the unconditional Hermite reduction is correct as a `RatFunc ℚ` identity** (§2.2,
p.41): `am A/am D = (toQFun (gnum,gden))′ + am Bres/am Dstar` for the computed `gnum, gden, Dstar` of
Example 2.2.1, with **no** exact-division certificate as a hypothesis — the certificate is discharged by
the `native_decide`'d residual-honesty bundle `hermite_ex221_resComp` through
`hermiteReduce_residual_correct_uncond`. The nonzero hypotheses hold by `decide`; the fuel bound by
`native_decide`. -/
example :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly cA221) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly cD221)
      = (toQFun ([8, 12, 20, 12, 8, 3], [0, 8, 0, 12, 0, 6, 0, 1]))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (cdiv 40
              (cmul (csub (cmul cA221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))
                  (cmul cD221 (csub (cmul (cderiv [8, 12, 20, 12, 8, 3]) [0, 8, 0, 12, 0, 6, 0, 1])
                    (cmul [8, 12, 20, 12, 8, 3] (cderiv [0, 8, 0, 12, 0, 6, 0, 1]))))) [0, 2, 0, 1])
              (cmul cD221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly [0, 2, 0, 1]) := by
  have hD : toPoly cD221 ≠ 0 := fun h => by
    have : cnorm cD221 = [] := (cnorm_eq_nil_iff cD221).mpr h
    revert this; decide
  have hgden : toPoly [0, 8, 0, 12, 0, 6, 0, 1] ≠ 0 := fun h => by
    have : cnorm [0, 8, 0, 12, 0, 6, 0, 1] = [] := (cnorm_eq_nil_iff _).mpr h
    revert this; decide
  have hDstar : cnorm [0, 2, 0, 1] ≠ [] := by decide
  have hfuel : (cnorm (cmul (csub (cmul cA221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))
      (cmul cD221 (csub (cmul (cderiv [8, 12, 20, 12, 8, 3]) [0, 8, 0, 12, 0, 6, 0, 1])
        (cmul [8, 12, 20, 12, 8, 3] (cderiv [0, 8, 0, 12, 0, 6, 0, 1]))))) [0, 2, 0, 1])).length ≤ 40 := by
    native_decide
  exact hermiteReduce_residual_correct_uncond 40 cA221 cD221 [8, 12, 20, 12, 8, 3]
    [0, 8, 0, 12, 0, 6, 0, 1] [0, 2, 0, 1] ⟨hD, hgden, hDstar⟩ hfuel hermite_ex221_resComp

/-! ### Example 2.2.1 via the radical wrapper: `Dstar ∣ D` from the proven Yun radical clause

The radical wrapper `hermiteReduce_residual_correct_of_radical` consumes `Dstar ∣ D` as a hypothesis,
which for Example 2.2.1 is discharged not by `native_decide` but by the **proven** Yun radical-divides
theorem `toPoly_Dstar_dvd_D` (through the `native_decide`'d honesty bundle `hermite_ex221_sqfreeExactComp`),
transported to the literal radical `[0,2,0,1]` by the computed fold equality. Only the *single* residual
cert remains `native_decide`'d — the abstract radical content is genuinely proven. -/

/-- **Example 2.2.1: the radical `[0,2,0,1]` divides `D`** with the *proven* Yun radical clause: the
computed radical `Dstar = x³+2x` (the `csqfreeFactor 40 cD221` fold) divides `D`, transported to the
literal `[0,2,0,1]` (`native_decide` fold-equality + `toPoly_Dstar_dvd_D`). -/
theorem hermite_ex221_Dstar_dvd : toPoly [0, 2, 0, 1] ∣ toPoly cD221 := by
  have hfold : ((csqfreeFactor 40 cD221).foldl (fun acc (vi : CPolyQ × ℕ) => cmul acc vi.1) [1])
      = [0, 2, 0, 1] := by native_decide
  have := toPoly_Dstar_dvd_D 40 cD221
    (SqfreeExactComp_to_SqfreeExact 40 cD221 hermite_ex221_sqfreeExactComp)
  rwa [hfold] at this

open scoped Differential in
/-- **Example 2.2.1: the unconditional Hermite reduction via the radical wrapper** (§2.2, p.41):
`am A/am D = (toQFun (gnum,gden))′ + am Bres/am Dstar` with the radical clause `Dstar ∣ D` discharged
by the *proven* `hermite_ex221_Dstar_dvd` (Yun radical-divides), and only the single residual cert
`native_decide`'d. The cleanest split — abstract radical content proven, one residual cert checked. -/
example :
    algebraMap ℚ[X] (RatFunc ℚ) (toPoly cA221) / algebraMap ℚ[X] (RatFunc ℚ) (toPoly cD221)
      = (toQFun ([8, 12, 20, 12, 8, 3], [0, 8, 0, 12, 0, 6, 0, 1]))′
        + algebraMap ℚ[X] (RatFunc ℚ)
            (toPoly (cdiv 40
              (cmul (csub (cmul cA221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))
                  (cmul cD221 (csub (cmul (cderiv [8, 12, 20, 12, 8, 3]) [0, 8, 0, 12, 0, 6, 0, 1])
                    (cmul [8, 12, 20, 12, 8, 3] (cderiv [0, 8, 0, 12, 0, 6, 0, 1]))))) [0, 2, 0, 1])
              (cmul cD221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPoly [0, 2, 0, 1]) := by
  have hD : toPoly cD221 ≠ 0 := fun h => by
    have : cnorm cD221 = [] := (cnorm_eq_nil_iff cD221).mpr h
    revert this; decide
  have hgden : toPoly [0, 8, 0, 12, 0, 6, 0, 1] ≠ 0 := fun h => by
    have : cnorm [0, 8, 0, 12, 0, 6, 0, 1] = [] := (cnorm_eq_nil_iff _).mpr h
    revert this; decide
  have hDstar : cnorm [0, 2, 0, 1] ≠ [] := by decide
  have hfuel : (cnorm (cmul (csub (cmul cA221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))
      (cmul cD221 (csub (cmul (cderiv [8, 12, 20, 12, 8, 3]) [0, 8, 0, 12, 0, 6, 0, 1])
        (cmul [8, 12, 20, 12, 8, 3] (cderiv [0, 8, 0, 12, 0, 6, 0, 1]))))) [0, 2, 0, 1])).length ≤ 40 := by
    native_decide
  have hfuelD : (cnorm cD221).length ≤ 40 := by decide
  have hWgd : toPoly (cmod 40
      (csub (cmul cA221 (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))
        (cmul cD221 (csub (cmul (cderiv [8, 12, 20, 12, 8, 3]) [0, 8, 0, 12, 0, 6, 0, 1])
          (cmul [8, 12, 20, 12, 8, 3] (cderiv [0, 8, 0, 12, 0, 6, 0, 1])))))
      (cmul (cdiv 40 cD221 [0, 2, 0, 1]) (cmul [0, 8, 0, 12, 0, 6, 0, 1] [0, 8, 0, 12, 0, 6, 0, 1]))) = 0 := by
    rw [← cnorm_eq_nil_iff]; native_decide
  exact hermiteReduce_residual_correct_of_radical 40 cA221 cD221 [8, 12, 20, 12, 8, 3]
    [0, 8, 0, 12, 0, 6, 0, 1] [0, 2, 0, 1] ⟨hD, hgden, hDstar⟩ hfuel hfuelD
    hermite_ex221_Dstar_dvd hWgd

end DeepWiki.SymbolicIntegration.Compute
