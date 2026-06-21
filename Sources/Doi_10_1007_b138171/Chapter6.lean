import Sources.Doi_10_1007_b138171.Source

/-! # Symbolic Integration catalog — Chapter 6: The Risch Differential Equation
Solving `Dy + f·y = g` for `y` in a monomial extension — the engine of the exponential case of
the integration algorithm. This chapter is **entirely unformalized**.

## NOT YET FORMALIZED (complete inventory — audit 2026-06-21)
§6.1 The Normal Part of the Denominator: Def 6.1.1; Thm 6.1.2; Cor 6.1.1; Lemma 6.1.1;
  Ex 6.1.1, Ex 6.1.2.
§6.2 The Special Part of the Denominator: Lemma 6.2.1, Lemma 6.2.2, Lemma 6.2.4;
  Ex 6.2.1, Ex 6.2.2.
§6.3 Degree Bounds: Cor 6.3.1; Lemma 6.3.1, Lemma 6.3.2, Lemma 6.3.3, Lemma 6.3.4, Lemma 6.3.5;
  Ex 6.3.1, Ex 6.3.2, Ex 6.3.3, Ex 6.3.4.
§6.4 The SPDE Algorithm: Thm 6.4.1; algorithm `SPDE` (Rothstein's sub-resultant PDE).
§6.5 The Non-Cancellation Cases: Lemma 6.5.1; Ex 6.5.1, Ex 6.5.2, Ex 6.5.3; algorithm `PolyDESolve`
  (non-cancellation degree-bounded solver).
§6.6 The Cancellation Cases: Ex 6.6.1; the cancellation-case solvers (`RdeSpecial` and the
  primitive/hyperexponential/hypertangent cancellation subroutines).
Exercise 6.1.

Almost entirely **procedural** — the RischDE solver and its case subroutines need an
operational-semantics treatment. -/

namespace DeepWiki.Si

end DeepWiki.Si
