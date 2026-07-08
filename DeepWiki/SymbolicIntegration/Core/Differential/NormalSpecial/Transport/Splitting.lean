import DeepWiki.SymbolicIntegration.Core.Differential.NormalSpecial.Core

/-! # Splitting-factorization transport for normal and special elements

The basic split of an element into special and normal factors.
-/

open scoped Differential

namespace DeepWiki.SymbolicIntegration

/-- A *splitting factorization* of `p` is `p = ps * pn` with `ps` special and `pn` normal. -/
def IsSplittingFactorization {R : Type*} [CommRing R] [Differential R] (p ps pn : R) : Prop :=
  p = ps * pn ∧ IsSpecial ps ∧ IsNormal pn

/-- A special polynomial splits as `(p, 1)`. -/
theorem IsSpecial.splittingFactorization {R : Type*} [CommRing R] [Differential R] {p : R}
    (hp : IsSpecial p) : IsSplittingFactorization p p 1 :=
  ⟨(mul_one p).symm, hp, isNormal_one⟩

/-- A normal polynomial splits as `(1, p)`. -/
theorem IsNormal.splittingFactorization {R : Type*} [CommRing R] [Differential R] {p : R}
    (hp : IsNormal p) : IsSplittingFactorization p 1 p :=
  ⟨(one_mul p).symm, isSpecial_one, hp⟩

end DeepWiki.SymbolicIntegration
