import DeepWiki.Algebra.SubresultantSpec
import DeepWiki.Algebra.SubresultantPRS
import Sources.Doi_10_1145_321371_321381.Source

/-! # Collins subresultant theory — catalog
Pointers to the `DeepWiki.SymbolicIntegration` subresultant machinery formalizing this paper.
The single-division-step **Lemma 1** and its telescoped iterate **Lemma 2** (the engine of the
paper) are formalized; the closed-form **Theorem 1** and the generalized **Lemma 3 / Theorem 2**
(the subresultant-p.r.s. result, = Bronstein's Thm 1.5.3) rest on elementary `(-1)`-exponent
arithmetic over those, and are tracked below.

## NOT YET FORMALIZED (subtractive — delete each item once it is formalized)
Reduced p.r.s. (§p.131, the coefficient choice the closed forms specialize): `cᵢ = lc Pᵢ`,
  `δᵢ = nᵢ − nᵢ₊₁`, `δ₀ = −1`, and `c_{i+1}^(δᵢ+1)·Pᵢ = P_{i+1}·Qᵢ + cᵢ^(δ_{i-1}+1)·P_{i+2}` (so `i=1`
  divides by `c₁⁰=1`, i.e. `P₃ = prem(P₁,P₂)`). In the `DeepWiki` abstract PRS (relation
  `C αₗ·Fₗ = C βₗ·F_{l+2} + F_{l+1}·Qₗ`, with `Pᵢ = F_{i-1}`): `αₗ = (lc F_{l+1})^(δₗ+1)`,
  `βₗ = (lc Fₗ)^(δ_{l-1}+1)`. The remaining closed-form items substitute these into
  `subresultant_prs_closed_top` (`thm_1b_closed`) and match the two product sides.
Lemma 2 (§p.132): the reduced-p.r.s.-specialized telescope `Sⱼ(P₁,P₂) = (-1)^σᵣ·[∏ᵢ cᵢ^(-δᵢ₋₁(δᵢ-1))]·
  c_r^(-(δᵣ₋₁+1)(n_{r+1}-j))·Sⱼ(Pᵣ,P_{r+1})`, `σᵣ = ∑(nᵢ-j)(n_{i+1}-j)` [external]: the abstract
  `subresultant_prs_telescope_explicit` with `αₗ,βₗ` above substituted and the `c`-powers collected (negative
  exponents ⇒ over `Frac`).
Theorem 1(a) (§p.133): `S_{nₖ}(P₁,P₂) = (-1)^σₖ·[∏ᵢ cᵢ^(-δᵢ₋₁(δᵢ-1))]·cₖ^(δₖ₋₁-1)·Pₖ` for a reduced
  p.r.s. [external]: combine the telescoped Lemma 2 (`subresultant_prs_telescope_explicit`) with
  Lemma 1(a) (`subresultant_rem_eq_13`) and reduce the exponent `α ≡ σₖ (mod 2)`.
Corollary 1.1 (§p.134); Corollary 1.2 (§p.135); Corollary 1.3 (§p.135); Corollary 1.4 (§p.135) [external].
Lemma 3 (§p.135): for an *arbitrary* p.r.s. (coefficient choices `eᵢ, fᵢⱼ`), `Pₖ = (-1)^gₖ·[∏ᵢ cᵢ^hᵢₖ]·Sₖ`
  [external]: generalizes Lemma 1 to an arbitrary p.r.s. (eq 2) and iterates.
Theorem 2 (§p.136): the direct subresultant-p.r.s. algorithm [external/infra]: needs the operational form.
-/

namespace DeepWiki.Col

open DeepWiki.SymbolicIntegration

/-- **Lemma 1**, the single-division-step relation (§p.131): for `P_{i+2} = R(Pᵢ,P_{i+1})` the remainder,
the subresultants `Sⱼ(Pᵢ,P_{i+1})` are expressed through `S(P_{i+1},P_{i+2})` and powers of leading
coefficients. The case `0 ≤ j < deg P_{i+2}` — the library's `subresultant_rem_lt` (also Brown–Traub's
Lemma 1, eq 12). -/
abbrev lemma_1 := @subresultant_rem_lt

/-- **Lemma 1(c)** at `j = deg P_{i+1} − 1` (§p.131): `S_{γ-1} = (-1)^…·(lc)^…·P_{i+2}`. The library's
`subresultant_rem_eq_15`. -/
abbrev lemma_1_top := @subresultant_rem_eq_15

/-- **Lemma 1(a)** at `j = deg P_{i+2}` (§p.131): the regular-index value. The library's
`subresultant_rem_eq_13`. -/
abbrev lemma_1_reg := @subresultant_rem_eq_13

/-- **Lemma 1(d)**, the vanishing (gap) subresultants (§p.131): `Sⱼ = 0` for the defective range.
The library's `subresultant_rem_eq_14`. -/
abbrev lemma_1_gap := @subresultant_rem_eq_14

/-- **Lemma 2**, the telescoped iterate of Lemma 1 (§p.132): the exact-constant relation between
`Sⱼ(P₁,P₂)` and `Sⱼ(Pᵣ,P_{r+1})` along the p.r.s. The library's `subresultant_prs_telescope_explicit`
(stated for an abstract PRS with coefficients `αₗ, βₗ`; Collins specializes to the reduced p.r.s.). -/
abbrev lemma_2 := @subresultant_prs_telescope_explicit

/-- **Theorem 1(b) / Lemma 3, explicit closed form at the η-index** (§p.133): the exact equation that
the `ηᵢ = 1` claim specializes — `Sⱼ(F₀,F₁)·(αₘ-product) = (sign·lc^·βₘ·F_{m+2})·(rhs-product)` at
`j = deg F_{m+1} − 1`, combining Lemma 2 (telescope) with Lemma 1(c) (the endpoint). Collins's Theorem 1(b)
is this with the two products shown equal (the reduced/subresultant p.r.s. coefficient choice). The
library's `subresultant_prs_closed_top`. -/
abbrev thm_1b_closed := @subresultant_prs_closed_top

/-- **Theorem 1 normal-case keystone** (§p.133, the `lc`-power collapse forcing `ηᵢ = 1`): with the normal
reduced/subresultant p.r.s. coefficients substituted and the signs cancelled, the `αₘ`-product equals the
`(lc²·βₗ)`-product in `subresultant_prs_closed_top`. The library's `lc_prod_collapse_normal`. -/
abbrev thm_1_normal_collapse := @lc_prod_collapse_normal

/-- **Theorem 1(b) defective-case keystone** (§p.133, the general-δ `lc`-power collapse): the `αₘ`-product
equals the `(βₘ·lc·β)`-product times Collins's coefficient `∏ cᵢ^(δᵢ₋₁(δᵢ-1))`. The library's
`lc_collapse_defective` (with helpers `shift_prod`, `beta_fold`). -/
abbrev thm_1_defective_collapse := @lc_collapse_defective

/-- **Theorem 1(b), defective closed form** (§p.133): `(∏cᵢ^(δᵢ₋₁(δᵢ-1)))·Sⱼ = SIGN·Pₖ` for a reduced
p.r.s. with arbitrary gaps — the full Collins coefficient identified. The library's
`subresultant_prs_defective_eq`. -/
abbrev thm_1b_defective := @subresultant_prs_defective_eq

end DeepWiki.Col
