/-! # Source (paper): A Note on Gröbner Bases and Integration of Rational Functions
Günter Czichowski's note — the reference Bronstein defers to for **Theorem 2.6.1** (the Czichowski
algorithm, §2.6), which states *without proof* that the Rothstein–Trager / Lazard–Rioboo–Trager logarithmic
part of `∫ A/D` can be read off a reduced **Gröbner basis** of the ideal `⟨A − z·D', D⟩ ⊂ K[x, z]`
(pure-lex `x > z`).

The key bridge (Czichowski's Lemma 2.3): for the reduced Gröbner basis `{P₁, …, Pₘ}` with
`Pₖ = Rₖ(z)·Sₖ(x, z)` (content/primitive-part split in `x`), at a zero `c` of `Qₖ = Rₖ/R_{k+1}` one has
`S_{k+1}(x, c) = GCD(A − c·D', D)` — i.e. the Gröbner-basis primitive parts evaluated at a residue are
exactly the Rothstein–Trager gcds `Gₐ`. Hence the integral `∫ A/D = ∑ₖ ∑_{Qₖ(c)=0} c·log(S_{k+1}(x, c))`
is the **same** logarithmic part as Rothstein–Trager / LRT (formalized in `DeepWiki.SymbolicIntegration`,
§2.4/§2.5). The new content is the Gröbner-basis *structure* (`Pₖ = Rₖ·Sₖ`, `R_{k+1} ∣ Rₖ`,
`R₁ = radical(resultant)`), which rests on reduced-Gröbner-basis theory (Mathlib has the monomial-order
division foundation but not reduced bases / Buchberger). This catalog records the integral *connection*
(Czichowski's logs = the RT gcds), reusing the §2.5 log-sum. -/

namespace DeepWiki.Czi

/-- DOI of the source paper. -/
def doi : String := "10.1006/jsco.1995.1043"

/-- Title of the source paper. -/
def title : String := "A Note on Gröbner Bases and Integration of Rational Functions"

/-- Reference of the source paper. -/
def reference : String := "Journal of Symbolic Computation 20 (1995), 163–167"

/-- Author of the source paper. -/
def authors : List String := ["Günter Czichowski"]

end DeepWiki.Czi
