import Sources.Doi_10_1007_b138171.Source

/-! # Symbolic Integration catalog — Chapter 5: Integration of Transcendental Functions
The core Risch integration algorithm for a single transcendental monomial extension. This chapter
is **entirely unformalized** — none of its definitions, theorems, examples, or algorithms have a
`DeepWiki.SymbolicIntegration` counterpart yet. It rests on Chapters 3–4 (differential/monomial
extensions, the order function and the Rothstein–Trager resultant) and is the heart of the book.

## NOT YET FORMALIZED (complete inventory — audit 2026-06-21)
§5.1 Elementary and Liouvillian Extensions: Def 5.1.1 (elementary/primitive/hyperexponential
  monomial), Def 5.1.2 (Liouvillian), Def 5.1.3, Def 5.1.4; Thm 5.1.1, Thm 5.1.2; Lemma 5.1.2.
§5.2 Outline and Scope of the Integration Algorithm: Ex 5.2.1, Ex 5.2.2.
§5.3 The Hermite Reduction (transcendental): Thm 5.3.1; Ex 5.3.1; algorithm `HermiteReduce`.
§5.4 The Polynomial Reduction: Thm 5.4.1, Thm 5.4.2; algorithm `PolynomialReduce`.
§5.5 Liouville's Theorem: Thm 5.5.1, Thm 5.5.2, Thm 5.5.3.
§5.6 The Residue Criterion: Thm 5.6.1; Lemma 5.6.1, Lemma 5.6.2; Ex 5.6.1, Ex 5.6.3;
  algorithm `ResidueReduce` (Rothstein–Trager / Lazard–Rioboo–Trager logarithmic part).
§5.7 Integration of Reduced Functions: Thm 5.7.1, Thm 5.7.2.
§5.8 The Primitive Case: Thm 5.8.1; algorithm `IntegratePrimitive`.
§5.9 The Hyperexponential Case: Thm 5.9.1; Lemma 5.9.1; algorithm `IntegrateHyperexponential`.
§5.10 The Hypertangent Case: Def 5.10.1; Thm 5.10.1, Thm 5.10.2; Lemma 5.10.1;
  Ex 5.10.1, Ex 5.10.2, Ex 5.10.3; algorithm `IntegrateHypertangent`.
§5.11 The Nonlinear Case with no Specials: Cor 5.11.1; Ex 5.11.1, Ex 5.11.2.
§5.12 In-Field Integration: Lemma 5.12.1.
Exercises 5.1–5.6.

Most of this chapter is **procedural** (the integration algorithms) and would need the
operational-semantics treatment noted in `Source.lean`. -/

namespace DeepWiki.Si

end DeepWiki.Si
