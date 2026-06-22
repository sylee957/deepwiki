import DeepWiki.SymbolicIntegration.RationalIntegrationGcdLogForm
import Sources.Doi_10_1006_jsco_1995_1043.Source

/-! # Czichowski catalog — the integral connection (Lemma 2.3 + part (iii))
Pointers to the library theorems realizing Czichowski's integral *connection*: his Gröbner-basis
logarithms `S(x,c) = gcd(D, A − c·D')` are exactly the Rothstein–Trager gcds (Lemma 2.3), so his integral
`∫ A/D = ∑ c·log(gcd(D, A − c·D'))` is the same logarithmic part as the §2.4/§2.5 RT/LRT result.

## NOT YET FORMALIZED (subtractive — delete each item once it is formalized)
The Gröbner-basis *structure* — the reduced-GB factorization `Pₖ = Rₖ·Sₖ`, `R_{k+1} ∣ Rₖ`,
`R₁ = radical(resultant)`, and the reduced-Gröbner-basis definition/existence — [infra: reduced Gröbner
bases]. -/

open scoped Classical

namespace DeepWiki.Czi

/-- **Lemma 2.3** (p.165), Czichowski's logs are the Rothstein–Trager gcds: for split squarefree
`D = ∏_{α∈s}(X−α)`, `gcd(D, A − a·D') = ∏_{α∈s, A(α)/D'(α)=a}(X−α)` — the Gröbner-basis primitive part
`S(x,a)` at a residue `a` equals the Rothstein–Trager `Gₐ`. The library's `gcd_nodal_eq_prod_residue`. -/
abbrev lemma_2_3_gcd := @DeepWiki.SymbolicIntegration.gcd_nodal_eq_prod_residue

/-- **Czichowski part (iii)** (p.165, the integral): for `deg A < #s` over split squarefree
`D = ∏_{α∈s}(X−α)`, `∫ A/D = ∑_a a·log(gcd(D, A − a·D'))` — the same logarithmic part as Rothstein–Trager /
Lazard–Rioboo–Trager (§2.4/§2.5), with the RT gcd as the log argument. The library's
`ratFunc_eq_sum_residue_gcd`. -/
abbrev integral_logForm_gcd := @DeepWiki.SymbolicIntegration.ratFunc_eq_sum_residue_gcd

end DeepWiki.Czi
