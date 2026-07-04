# Generalizing the abstract LRT theory from `derivative` to an arbitrary derivation

**Goal.** The repo's abstract Lazard–Rioboo–Trager (LRT) / Rothstein–Trager theory
(`rtResultant`, `lrtSubresultant`, `lazardRiobooTrager`, `..._output_isSimilar_gcd`,
`ratFunc_eq_sum_residue_gcd`) is stated for the **plain polynomial `derivative D`**. The computable
tower engine (`cResidueResultantTowerGWf`, `cLrtLogArgG`) uses the **tower derivation**:
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
(`residue_gcd_eq_linear_factor` / `cIntegrateReducedGWf_logs_eq_per_root`, `LogPartTowerSoundness.lean` /
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

- **G1** — `rtResultantGen A D B := resultant(D.map C, A.map C − C X · B.map C) deg D (deg D − 1)`;
  `rtResultantGen_eval`, `natDegree_rtResultantGen_le`, and the bridge `rtResultant A D =
  rtResultantGen A D (derivative D)`. (Mechanical; a new abstract file `LrtGeneralDerivation.lean`.)
- **G2** — `roots_rtResultantGen` / `rootMultiplicity_rtResultantGen_eq_natDegree_gcd` /
  `gcd_nodal_eq_prod_residue_gen` under `hB` normality. (Mechanical + `hB`.)
- **G3** — `lrtSubresultantGen` + `lazardRiobooTrager_output_isSimilar_gcd_gen` (subresultant
  similarity with `B`).
- **G4** — connect `cResidueResultantTowerGWf` / `cSubresultantParam` / `cLrtLogArgG` (`implicitDeriv`)
  to G1–G3 via `toPolyG_cmonomialDeriv` + `toPolyG_cSubresultantG` (L4b) + `toPoly_rtResultantCompute`
  interpolation (already done for `derivative`; re-do for `B`).
- **G5** — assemble with the candidate route's tower per-root analytic identity into a symbolic-log
  soundness `IsIntegralResultLrtG` for `cIntegrateReducedLrtG`; swap the primitive base (closes
  `hreduced` without the rational-residue restriction).

**Bottom line:** the generalization is a *parametrization* (`derivative D → B`) plus one honest
hypothesis (`hB` normality, already characterized by `isCoprime_X_sub_C_implicitDeriv_iff`), reusing the
repo's `implicitDeriv` gcd theory and the candidate route's tower analytic identity. Not new deep math —
a substantial but bounded refactor-and-connect.
