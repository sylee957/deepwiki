import DeepWiki.SymbolicIntegration.Engine.LiouvilleLogTower
import DeepWiki.SymbolicIntegration.LiouvilleStructure.Core

/-! # The general structure theorem over a Liouville tower (Thm 5.5.2 / 5.5.3)

`IsElementary F a` — a base element `a : F` has an elementary antiderivative — is captured, following
Liouville's theorem, as: `a` has a Liouville form `∑ cᵢ log uᵢ + v′` in **some** finite tower of
Liouville extensions of `F` (a `LiouvilleStage F`, i.e. a differential field reached from `F` by a
finite chain of Liouville steps — the log tower is the built instance; exp/algebraic layers extend the
same `LiouvilleStage` scaffold). The **structure theorem** is the descent: `a` is elementary **iff** it
already has a Liouville form over the base `F` itself.

This is the abstract counterpart of Bronstein Thm 5.5.2 (every elementary antiderivative has the
Liouville form) and Thm 5.5.3 (its contrapositive: no such base form ⟹ not elementary), built on the
Mathlib differential-Liouville structure theorem (`IsLiouville.isLiouville`) via the tower's
`IsLiouville F (tower n).carrier` (`LiouvilleStage.isLiouvilleF`). It does not decide the new-monomial
conditions of the stages — those are the necessary hypotheses each `LiouvilleStage` step carries. -/

open DeepWiki.SymbolicIntegration.LiouvilleTower
open DeepWiki.SymbolicIntegration.LiouvilleStructure

namespace DeepWiki.SymbolicIntegration.LiouvilleStructure

variable (F : Type) [Field F] [Differential F] [CharZero F]

/-- **Elementary integrability over a Liouville tower.** `a : F` has an elementary antiderivative when it
has a Liouville form `∑ cᵢ log uᵢ + v′` in **some** Liouville-stage extension of `F` — a differential
field reached from `F` by a finite chain of Liouville steps (`LiouvilleStage F`). The abstract
`IsElementary` predicate Bronstein's Thm 5.5.2/5.5.3 quantify over. -/
def IsElementary (a : F) : Prop :=
  ∃ S : LiouvilleStage F, HasWeakLiouvilleForm F S.carrier a

variable {F}

/-- Any base Liouville form makes `a` elementary (take the base stage `F` itself). -/
theorem IsElementary.of_hasWeakLiouvilleForm {a : F} (h : HasWeakLiouvilleForm F F a) :
    IsElementary F a :=
  ⟨LiouvilleStage.base, h⟩

/-- **The general structure theorem (Thm 5.5.2 / 5.5.3).** A base element is elementary over some
Liouville tower **iff** it already has a Liouville form over the base field `F`. Forward is the descent:
every stage is a Liouville extension (`S.isLiouvilleF`), so its Liouville form descends to `F` by the
Mathlib structure theorem (`weakLiouville_descend`). Backward is the base stage. -/
theorem isElementary_iff (a : F) :
    IsElementary F a ↔ HasWeakLiouvilleForm F F a := by
  constructor
  · rintro ⟨S, hS⟩
    haveI : IsLiouville F S.carrier := S.isLiouvilleF
    exact weakLiouville_descend F S.carrier a hS
  · exact IsElementary.of_hasWeakLiouvilleForm

/-- **Thm 5.5.3 (contrapositive form): no base Liouville form ⟹ not elementary.** If `a : F` has no
Liouville form over the base field, then it is not elementary over any Liouville tower — the citable
non-elementarity criterion. -/
theorem not_isElementary_of_not_hasWeakLiouvilleForm (a : F)
    (h : ¬ HasWeakLiouvilleForm F F a) : ¬ IsElementary F a :=
  fun hel => h ((isElementary_iff a).mp hel)

end DeepWiki.SymbolicIntegration.LiouvilleStructure
