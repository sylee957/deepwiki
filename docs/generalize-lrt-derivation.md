# Generalizing the abstract LRT theory from `derivative` to an arbitrary derivation

**Goal.** The repo's abstract Lazard–Rioboo–Trager (LRT) / Rothstein–Trager theory
(`rtResultant`, `lrtSubresultant`, `lazardRiobooTrager`, `..._output_isSimilar_gcd`,
`ratFunc_eq_sum_residue_gcd`) is stated for the **plain polynomial `derivative D`**. The computable
tower engine (`cResidueResultantTowerG`, `cLrtLogArgG`) uses the **tower derivation**:
`toPolyG (cmonomialDeriv Dt p) = Differential.implicitDeriv (toPolyG Dt) (toPolyG p)` (`@[denote]`,
`MonomialDeriv.lean`). They coincide only when `Dt = 1` + constant coefficients (the pure rational
case). To close `hreduced` via the **root-free LRT path** for the primitive *tower* case, the abstract
LRT must be generalized from `derivative D` to an arbitrary `B` (which will be `implicitDeriv Dt Dstar`,
`deg B ≤ deg D`).

## The mathematical structure (what generalizes, and how)

Write `D` for the squarefree denominator (`Dstar`), `A` for the numerator (`hNum`), and `B` for the
derivation image `implicitDeriv Dt D`. The residue resultant becomes `Res_t(D, A − z·B)`; residues are
`c = A(β)/B(β)` at roots `β` of `D`.

**The one substitution that carries the whole algebraic chain:** every place the current proofs use
`D.Separable → (derivative D).eval α ≠ 0` at a root `α` (the residue denominator is nonzero) becomes a
hypothesis `hB : ∀ α, D.IsRoot α → B.eval α ≠ 0`. That hypothesis is exactly **normality**:
`isCoprime_X_sub_C_implicitDeriv_iff` (`MonomialExtensions.lean`) gives
`IsCoprime (X − C a) (implicitDeriv v (X − C a)) ↔ v.eval a ≠ a′`, i.e. `B(β) ≠ 0` ⟺ the residue at `β`
is normal (not special). `D` itself stays separable/squarefree (that's about `D`, not `B`).

**Confirmed mechanical (no `derivative`-specific step; only `A − z·B` linear in `z`):**
- `natDegree_coeff_rtResultant_g_le` / `natDegree_rtResultant_le` (`RtResultantCorrectness.lean:233,245`)
  — the `z`-degree bound `≤ deg D`. Uses only that `(A − z·B).coeff k = A.coeff k − z·B.coeff k` is
  `z`-linear. **Generalizes verbatim** with `B`.
- `rtResultant` / `rtResultant_eval` (`RationalIntegrationAlgorithms.lean:73,79`) — `B` appears only
  syntactically in `A.map C − C X · B.map C`. **Generalizes verbatim.**

**Mechanical + the `hB` normality hypothesis (separability used only for `D'(α) ≠ 0`):**
- `gcd_nodal_eq_prod_residue` (`RationalIntegrationGcdLogForm.lean:19`) — the proof's only use of
  separability is `hd : D.IsRoot α → (derivative D).eval α ≠ 0`; replace with `hB`.
- `rootMultiplicity_rtResultant_eq_natDegree_gcd` (`ResidueMultiplicity.lean:150`) —
  `= roots_rtResultant + natDegree_gcd_eq_count_residue`; both localize the separability to the
  residue-denominator-nonzero fact. [confirm exact uses via the proof-chain map]

**The analytic identity — REUSE the candidate route, do NOT reprove.**
`ratFunc_eq_sum_residue_gcd` (`RationalIntegrationGcdLogForm.lean:77`) is the K(x)-with-`d/dx` analytic
identity. Rather than lift it to the tower differential field from scratch (Bronstein Thm 5.6.1's
analytic content), **reuse the candidate route's already-proven tower per-root identity**
(`residue_gcd_eq_linear_factor` / `cIntegrateReducedG_logs_eq_per_root`, `LogPartTowerSoundness.lean` /
`OneShotAssembly.lean` — the tower-derivation residue↔linear-factor + per-root log-sum = the reduced
integrand). The generalized *algebraic* LRT (below) connects the **symbolic** LRT output
`[(Rᵢ, Sᵢ)]` to those **enumerated** per-root residues (Rᵢ's roots ARE the residues; `Sᵢ` at a root IS
the gcd log-argument). So the LRT path's soundness = (generalized algebraic residue↔root) ∘ (candidate
route's tower analytic identity).

## Reuse asset already in the repo (the "suitable mathematics")

`MonomialExtensions.lean` already has the **general-derivation** (`implicitDeriv`) gcd/residue theory:
- `isCoprime_X_sub_C_implicitDeriv_iff` — normality criterion `v.eval a ≠ a′`.
- `gcd_prod_X_sub_C_implicitDeriv` / `_pow_` — residue gcd over split `D`, `~ ∏_{v(a)=a′}(X−a)`.
- `gcd_implicitDeriv_associated_gcd_derivative_mul_special` — the **`implicitDeriv` ↔ `derivative` gcd
  bridge** (`gcd(D, implicitDeriv v D) ~ gcd(D, D') · special part`).
- `natDegree_implicitDeriv_le/eq`, `implicitDeriv_X_sub_C`, `isCoprime_splitting_parts`.

## Phase plan (each its own gate-green commit)

- **G1 ✅ DONE** (`LrtGeneralDerivation.lean`) — `rtResultantGen A D B`, `lrtSubresultantGen A D B j`,
  their `_eval` lemmas, and the `derivative`-case bridges (`rtResultantGen A D (derivative D) =
  rtResultant A D`, `rfl`). The resultant/subresultant defs treat `B` opaquely, so verbatim.
- **G2 ✅ DONE** — the residue↔root theory under normality `hB : ∀ α ∈ D.roots, B.eval α ≠ 0`:
  `residue_eq_iff_isRoot_sub_gen`, `isRoot_gcd_iff_residue_gen`, `rtResultantGen_eq_prod_roots`,
  `linearFactor_eq_residue_gen`, `roots_rtResultantGen`, `natDegree_gcd_eq_count_residue_gen`, and the
  headline **`rootMultiplicity_rtResultantGen_eq_natDegree_gcd`** (RT residue-multiplicity for arbitrary
  `B`). `D` stays `Separable` for nodup-roots; `hB` (`deg B ≤ deg D − 1` too) replaces separability's
  `D'(α) ≠ 0`.
- **G3 ✅ DONE** — the LRT subresultant-similarity chain: `isSimilar_lrtSubresultant_eval_gcd_gen` /
  `_top_gen`, `lazardRiobooTrager_isSimilar_gcd_gen`, and the unified capstone
  **`lazardRiobooTrager_output_isSimilar_gcd_gen`**. The PRS engine is already `derivative`-agnostic; `B`
  enters only via the opaque `E := A − a·B` + the degree bound. **The abstract LRT residue theory now
  holds for ANY derivation image `B`.**
- **G4a ✅ DONE** — `natDegree_rtResultantGen_le` (the `z`-degree bound `≤ deg D`, over any field `K`) +
  `natDegree_det_le_sum_col_gen`; and `natDegree_implicitDeriv_le_of_monic` (the tight `deg B ≤ deg D − 1`
  for monic `D` + constant `Dt` — the primitive case).
- **G4b ✅ DONE** (`Computable/ResidueResultantTowerSpec.lean`) — **`toPolyG_cResidueResultantTowerG`**:
  the computable tower residue resultant equals `rtResultantGen (toPolyG a) (toPolyG d) (implicitDeriv
  (toPolyG Dt) (toPolyG d))` for monic `d` + constant `Dt` + proper `a`. Via the sample-agreement lemma
  `toK_cresultantWf_cAmcDdG_eq_eval` (`Polynomial.resultant_add_right_deg` reconciles the engine's
  actual-degree resultant with `rtResultantGen`'s formal degree) + interpolation uniqueness
  (`eq_of_degrees_lt_of_eval_index_eq`, `toK_cnatCastG`). **The computable residue resultant IS the object
  G3 reasons about.**
- **G4c ✅ DONE** (`Computable/SubresultantTowerSpec.lean`):
  - `toK_cSubresultantG_getD_eq_coeff` (+ `_monomial`) — the **per-value** subresultant agreement (clean
    from L4b + `csubG`/`cscaleG`/`cmonomialDeriv` bridges).
  - `natDegree_coeff_lrtSubresultantGen_le` (`LrtGeneralDerivation.lean`) — the **bivariate `z`-degree
    bound** (each `t`-coefficient of `lrtSubresultantGen` has `z`-degree `≤ deg D + (deg D−1) < N`), via
    `natDegree_det_le_sum_col_gen` (every Sylvester entry is `z`-degree `≤ 1`).
  - **`toPolyG_cSubresultantParam_getD`** — the capstone: the `k`-th entry of the engine's parametric log
    argument `cSubresultantParam` equals the `k`-th `t`-coefficient of `lrtSubresultantGen (toPolyG A)
    (toPolyG Dstar) (toPolyG Dd) j` (for `deg Dd = deg Dstar − 1`), via interpolation uniqueness (degree
    bound + node agreement + coeff/eval commutation + `lrtSubresultantGen_eval`).
  **⟹ the entire computable→abstract LRT connection is certified: residue resultant (G4b) + parametric
  subresultant (G4c).**
- **G5** — assemble with the candidate route's tower per-root analytic identity
  (`residue_gcd_eq_linear_factor` / `cIntegrateReducedG_logs_eq_per_root`) into a symbolic-log soundness
  `IsIntegralResultLrtG` for `cIntegrateReducedLrtG`; swap the primitive base (closes `hreduced` **without**
  the rational-residue restriction).

**Bottom line:** ✅ **the mathematical core is DONE** (G1–G3, gate-clean) — the abstract LRT residue theory
is generalized from `derivative D` to an arbitrary derivation image `B`, exactly a parametrization plus one
honest normality hypothesis (already characterized by `isCoprime_X_sub_C_implicitDeriv_iff`). What remains
(G4/G5) is *connecting* the computable tower engine to it — engineering of the same flavor as the L4b
subresultant certification, not new mathematics.
