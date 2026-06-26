import DeepWiki.SymbolicIntegration.ComputableRadicalLogSoundness
import DeepWiki.SymbolicIntegration.ComputableGeneralLogSoundness
import Sources.Doi_10_1016_S0747_7171_08_80027_2.Source

/-! # Bronstein-1990 catalog — soundness pointer (the correctness of the algebraic arc beneath the tower)
Bronstein's 1990 decision procedure integrates an elementary function over an algebraic extension of a
liouvillian ground field; its **algebraic** core (the simple-radical / general-curve integral) is exactly
Trager's algorithm (handle `1721.1/15391`). The **correctness** `D(∫f) = f` of that algebraic core is proven
abstractly (axiom-clean, no `native_decide`) in the `DeepWiki.SymbolicIntegration` library and cataloged
primarily under `Sources.Hdl_1721_1_15391.Soundness`. Per the "double reference" rule, this per-paper
pointer records that the same soundness underwrites the algebraic-over-tower integration Bronstein 1990
describes — the radical/general capstones are the correctness of the algebraic step beneath the combined
elementary procedure (`ElementaryIntegration` / `ElementaryIntegrationFull`).

The COMBINED elementary-over-algebraic soundness (the general Thm 1/2 recursion over arbitrary towers) is
research-grade and deferred — see the `## NOT YET FORMALIZED` block of
`Sources.Doi_10_1016_S0747_7171_08_80027_2.Coverage`. -/

open DeepWiki.SymbolicIntegration

namespace DeepWiki.Bie

/-- **★★ The algebraic-step capstone `D(∫f) = f` (simple radical)** `isAlgebraicIntegral_of_parts`
(Bronstein 1990, §2–§5, the algebraic core ≡ Trager thesis App. A + Ch. 5): the unified simple-radical
integrator's output `v + Σ cᵢ log uᵢ` differentiates back to `f` in the carrier quotient — the correctness of
the algebraic integration step Bronstein's combined elementary procedure runs over a tower base. Cataloged
primarily as `DeepWiki.Tiaf.sound_radCapstone` (`Sources.Hdl_1721_1_15391.Soundness`). -/
abbrev bie_algebraicCapstone := @RadElem.isAlgebraicIntegral_of_parts

/-- **★★ The algebraic-step capstone `D(∫g) = g` (general curve)** `isGeneralAlgebraicIntegral_of_parts`
(Bronstein 1990, §2–§5, the general-curve algebraic core ≡ Trager thesis Ch. 4 + Ch. 5): the unified
general-curve integrator's output differentiates back to `g` over `K(x)[y]/(f)` — the correctness of the
algebraic step for an arbitrary (non-radical) curve beneath the elementary tower. Cataloged primarily as
`DeepWiki.Tiaf.sound_genCapstone` (`Sources.Hdl_1721_1_15391.Soundness`). -/
abbrev bie_generalAlgebraicCapstone := @CPolyG.isGeneralAlgebraicIntegral_of_parts

end DeepWiki.Bie
