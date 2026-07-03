# Laurent soundness — plan (discharging the hyperexp `hLaurField`)

Goal: prove `cIntegrateHyperexpLaurentG` correct, so the hyperexp assembler's `hLaurField`
(`D(lnum/lden) = ⟦Laurent integrand⟧`) is discharged and the hyperexp case reaches the same
frontier-only footing as the primitive case (see `risch-typeclass-architecture.md`).

## The target

`cIntegrateHyperexpLaurentG η pos neg = some (num, den)` integrates `∑ⱼ aⱼ tʲ` term by term: each `qⱼ`
solves the base RDE `Dqⱼ + (j·η)·qⱼ = aⱼ` via `CRischField.crischDESolve`, and the result is `num/den`
with `den = tᵐ` (`m = neg.length`), `num[j+m] = qⱼ`. Correctness:

    D_tower(num/den) = ⟦∑ⱼ aⱼ tʲ⟧    over RatFunc (CFieldSpec.K α)

where `D_tower = towerFractionFieldDerivG Dt`, `Dt = η·t` (hyperexp monomial).

## Available machinery (do NOT rebuild)

- `CRischFieldSpec.crischDESolve_spec` — base-level RDE soundness `(toK y)′ + toK b·toK y = toK g`.
- `towerFractionFieldDerivG` is a `Derivation ℤ (RatFunc K) (RatFunc K)` — `map_add`, `leibniz`.
- `towerFractionFieldDerivG_div` — quotient rule on `amG gnum / amG gden`.
- `toPolyG_cmonomialDeriv` (`@[denote]`) — the computable `cmonomialDeriv` = the polynomial derivation.
- `towerFractionFieldDerivG_amG_fracAccG` / the telescope lemmas (NormalPartSoundness) — fraction-sum
  derivative bookkeeping, reusable for the term sum.

## Milestones

### M1 — the derivation kernel (base↔tower bridge + `D(tʲ)`)
Two reusable lemmas, no Laurent structure yet:
- **`towerFractionFieldDerivG_amG_poly`**: `D_tower(amG (toPolyG p)) = amG (toPolyG (cmonomialDeriv Dt p))`
  — the polynomial-image tower derivative (from `towerFractionFieldDerivG_div` at `den = 1`, +
  `toPolyG_cmonomialDeriv`). Grounds everything at the polynomial level.
- **`towerFractionFieldDerivG_t_pow`**: `D_tower(⟦tᵏ⟧) = k·⟦η⟧·⟦tᵏ⟧` (and the negative-power version
  `D_tower(⟦t^{-i}⟧) = -i·⟦η⟧·⟦t^{-i}⟧`), for `Dt = η·t`. From the power rule + `D_tower(⟦t⟧) = ⟦η·t⟧`.

Deliverable: both lemmas gate-green. This is the tractable first commit.

### M2 — the single-term identity
- **`cLaurentIntCoeff_tower_term`**: if `cLaurentIntCoeffG η j aⱼ = some qⱼ` then
  `D_tower(⟦qⱼ⟧ · ⟦tʲ⟧) = ⟦aⱼ⟧ · ⟦tʲ⟧`. Product rule (M1) splits it into `(qⱼ)′·tʲ + qⱼ·jη·tʲ`;
  `crischDESolve_spec` + the base↔tower bridge (M1) collapses `(qⱼ)′ + jη·qⱼ` to `aⱼ`.
  Needs: the coefficient derivative `D_tower(⟦qⱼ⟧)` (a "constant in t") = `⟦base-deriv qⱼ⟧`, bridged to `′`.

### M3 — the sum assembly (the bookkeeping)
- `num/den = ∑ⱼ ⟦qⱼ⟧·⟦tʲ⟧` from `num = negCoeffs.reverse ++ posCoeffs`, `den = tᵐ` (index arithmetic
  `num[j+m] = qⱼ`, negative powers via the `tᵐ` denominator).
- Sum the M2 identities over the `Option`-`foldr` structure (`negQ`/`posQ`) → `D_tower(num/den) = ∑ⱼ ⟦aⱼ tʲ⟧`.
- Relate `∑ⱼ ⟦aⱼ tʲ⟧` to `⟦fpPart⟧` (the Laurent integrand `fp + b/dₛ`), discharging `hLaurField`.

This is the painful part (foldr + reversed lists + negative-index arithmetic); isolated in M3 so M1/M2 land first.

## Status

- [x] **M1 — polynomial-image bridge DONE** (`towerFractionFieldDerivG_amG_poly`, commit a5033ae5):
  `D_tower(⟦p⟧) = ⟦cmonomialDeriv Dt p⟧` in three rewrites (`towerFractionFieldDerivG`,
  `extendDeriv_algebraMap`, `toPolyG_cmonomialDeriv`).
- [x] **M2 — single-term identity DONE for BOTH signs** (commits f43a297b, d5a61c32):
  - `cIntegrateHyperexpLaurent_pos_term` (`k : ℕ`): `D_tower(⟦qₖtᵏ⟧) = ⟦aₖtᵏ⟧` — M1 bridge →
    `Derivation.leibniz`/`leibniz_pow` + `implicitDeriv_C`/`_X` + `crischDESolve_spec`, closed by
    `cases k` + `pow_succ` + `push_cast`/`ring`.
  - `cIntegrateHyperexpLaurent_neg_term` (`-(i+1)`): `D_tower(⟦q·t^{-(i+1)}⟧) = ⟦a·t^{-(i+1)}⟧` — the
    fraction case via `towerFractionFieldDerivG_div` (quotient rule) + `implicitDeriv` on `C`/`X^(i+1)` +
    the negative-shift RDE, closed by `field_simp`/`push_cast`/`ring`.
  - Supporting: `toK_cnatCastG_laurent` (inline), `toK_cLaurentShiftG_{nat,neg}Cast`.
  Both take the `Dt = C(toK η)·X` hypothesis (the hyperexp monomial).
- [~] M3 — sum assembly.
  - [x] **Kernel DONE** (`towerFractionFieldDerivG_laurent_pos_sum`, commit 8a9c074a): `D_tower` distributes
    over a solved-term list, `D_tower(∑ₖ ⟦qₖtᵏ⟧) = ∑ₖ ⟦aₖtᵏ⟧` (`map_list_sum` + `List.map_congr_left` +
    M2). The reusable assembly mechanism.
  - [ ] **num/den plumbing remaining** (the tedious, math-free part): (1) a `posQ`/`negQ` foldr spec —
    from `posQ pos = some posCoeffs`, extract `∀ k, cLaurentIntCoeffG η k pos[k] = some posCoeffs[k]` and
    `length`; (2) a Horner decomposition `amG(toPolyG p) = ∑ₖ amG(toPolyG(cshiftG k [p.getD k 0]))`;
    (3) assemble `⟦num/den⟧ = ∑ⱼ ⟦qⱼtʲ⟧` (neg via `reverse`/`den = tᵐ`) and apply the kernel + neg-term M2,
    landing `hLaurField`. All three are list inductions — no new mathematics.
