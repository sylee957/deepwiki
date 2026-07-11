import DeepWiki.SymbolicIntegration.CanonicalRepresentation.Classify
import DeepWiki.ComputableAlgebra.PolySquarefreeTheory

/-! # Squarefree-normal splitting predicates

Book-faithful normality predicates for denominator splitting. -/

namespace DeepWiki.SymbolicIntegration

section BookFaithfulNormal
variable {R : Type*} [CommRing R] [Differential R]

/-- `pn` has every squarefree factor normal. Strictly weaker than `IsNormal pn` (which forces
`pn` squarefree): a normal prime power `π²` satisfies `IsNormalSqfree` but not `IsNormal`. -/
def IsNormalSqfree (pn : R) : Prop := ∀ q : R, Squarefree q → q ∣ pn → IsNormal q

/-- General splitting factorization: `p = pₛ·pₙ` with `pₛ` special and every squarefree factor of
`pₙ` normal (weaker than `IsSplittingFactorization`, which demands `pₙ` itself `IsNormal`, hence
squarefree). -/
def IsSplittingFactorizationGen (p ps pn : R) : Prop :=
  p = ps * pn ∧ IsSpecial ps ∧ IsNormalSqfree pn

/-- `IsNormal pn` implies `IsNormalSqfree pn`: squarefree factors of a normal polynomial are
normal (`IsNormal.of_dvd`). -/
theorem IsNormal.isNormalSqfree {pn : R} (h : IsNormal pn) : IsNormalSqfree pn :=
  fun _ _ hq => h.of_dvd hq

/-- An `IsSplittingFactorization` is an `IsSplittingFactorizationGen`. -/
theorem IsSplittingFactorization.toGen {p ps pn : R}
    (h : IsSplittingFactorization p ps pn) : IsSplittingFactorizationGen p ps pn :=
  ⟨h.1, h.2.1, h.2.2.isNormalSqfree⟩

/-- On a *squarefree* `pn` the two normality notions agree: `IsNormalSqfree pn ↔ IsNormal pn`
(a squarefree polynomial is its own squarefree factor). -/
theorem isNormalSqfree_iff_isNormal_of_squarefree {pn : R} (hsf : Squarefree pn) :
    IsNormalSqfree pn ↔ IsNormal pn :=
  ⟨fun h => h pn hsf dvd_rfl, IsNormal.isNormalSqfree⟩

end BookFaithfulNormal

end DeepWiki.SymbolicIntegration
