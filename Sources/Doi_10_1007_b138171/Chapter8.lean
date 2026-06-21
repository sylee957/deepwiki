import Sources.Doi_10_1007_b138171.Source

/-! # Symbolic Integration catalog — Chapter 8: The Coupled Differential System
Solving the coupled system `Dy₁ + f·y₁ − g·y₂ = h₁`, `Dy₂ + g·y₁ + f·y₂ = h₂` (the real/imaginary
split of a complex Risch DE), case by case. This chapter is **entirely unformalized**.

## NOT YET FORMALIZED (complete inventory — audit 2026-06-21)
§8.1 The Primitive Case — coupled solver, primitive monomial.
§8.2 The Hyperexponential Case — coupled solver, hyperexponential monomial.
§8.3 The Nonlinear Case — coupled solver, nonlinear monomial.
§8.4 The Hypertangent Case — coupled solver, hypertangent monomial (`Dt = η·(t² + 1)`).
(The chapter is algorithm-driven with few separately-numbered results; it reduces the coupled
system to the parametric problems of Chapter 7.)

Entirely **procedural** — needs operational semantics. -/

namespace DeepWiki.Si

end DeepWiki.Si
