import DeepWiki.SymbolicIntegration.Engine.LiouvilleLogTower
import DeepWiki.SymbolicIntegration.LiouvilleStructure.Core
import DeepWiki.SymbolicIntegration.DifferentialAlgebra

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

/-! ## Assembly: the antiderivative as a tower element -/

section Assembly

open DeepWiki.SymbolicIntegration.LiouvilleLog Differential Polynomial
open scoped Differential

omit [CharZero F] in
/-- Assembly auxiliary: a stage-level identity `↑g = ∑ ↑cᵢ · logDeriv ↑uᵢ + v′` yields an
antiderivative element in a further stage — induction over the log family, adjoining each
nondegenerate log via `LiouvilleStage.extend` and absorbing each degenerate one into `v`. -/
private theorem exists_antideriv_aux {ι : Type} (c u : ι → F) (hc : ∀ x, (c x)′ = 0)
    (g : F) (s : Finset ι) :
    ∀ (S : LiouvilleStage F) (v : S.carrier),
      algebraMap F S.carrier g
        = (∑ x ∈ s, algebraMap F S.carrier (c x)
            * logDeriv (algebraMap F S.carrier (u x))) + v′ →
      ∃ (S' : LiouvilleStage F) (w : S'.carrier), algebraMap F S'.carrier g = w′ := by
  induction s using Finset.cons_induction with
  | empty =>
      intro S v hv
      exact ⟨S, v, by simpa using hv⟩
  | cons a s ha ih =>
      intro S v hv
      rw [Finset.sum_cons] at hv
      by_cases hnd : NondegenerateLog (algebraMap F S.carrier (u a))
      · -- adjoin `t = log ↑(u a)`: the head becomes `(↑(c a)·t)′`
        letI dR : Differential (RatFunc S.carrier) :=
          logDifferential (algebraMap F S.carrier (u a))
        letI dAR : DifferentialAlgebra S.carrier (RatFunc S.carrier) :=
          logDifferentialAlgebra (algebraMap F S.carrier (u a))
        set t : RatFunc S.carrier :=
          algebraMap (Polynomial S.carrier) (RatFunc S.carrier) X with hT
        have hT' : t′ = algebraMap S.carrier (RatFunc S.carrier)
            (logDeriv (algebraMap F S.carrier (u a))) := by
          rw [hT, derivExtends, logDerivPoly_X,
            IsScalarTower.algebraMap_eq S.carrier (Polynomial S.carrier)
              (RatFunc S.carrier)]
          simp [Polynomial.algebraMap_eq]
        have hlog : ∀ y : S.carrier,
            algebraMap S.carrier (RatFunc S.carrier) (logDeriv y)
              = logDeriv (algebraMap S.carrier (RatFunc S.carrier) y) := fun y => by
          unfold Differential.logDeriv
          rw [deriv_algebraMap, map_div₀]
        have hcconst : (algebraMap F (RatFunc S.carrier) (c a))′ = 0 := by
          rw [IsScalarTower.algebraMap_apply F S.carrier (RatFunc S.carrier),
            deriv_algebraMap, deriv_algebraMap, hc a, map_zero, map_zero]
        have hhead : (algebraMap F (RatFunc S.carrier) (c a) * t)′
            = algebraMap F (RatFunc S.carrier) (c a)
              * logDeriv (algebraMap F (RatFunc S.carrier) (u a)) := by
          rw [deriv_const_mul t hcconst, hT', hlog,
            ← IsScalarTower.algebraMap_apply F S.carrier (RatFunc S.carrier)]
        have hmap := congrArg (algebraMap S.carrier (RatFunc S.carrier)) hv
        simp only [map_add, map_mul, map_sum, hlog, ← deriv_algebraMap,
          ← IsScalarTower.algebraMap_apply F S.carrier (RatFunc S.carrier)] at hmap
        refine ih (S.extend (algebraMap F S.carrier (u a)) hnd)
          (algebraMap F (RatFunc S.carrier) (c a) * t
            + algebraMap S.carrier (RatFunc S.carrier) v) ?_
        show algebraMap F (RatFunc S.carrier) g
            = (∑ x ∈ s, algebraMap F (RatFunc S.carrier) (c x)
                * logDeriv (algebraMap F (RatFunc S.carrier) (u x)))
              + (algebraMap F (RatFunc S.carrier) (c a) * t
                  + algebraMap S.carrier (RatFunc S.carrier) v)′
        rw [map_add, hhead, hmap]
        ring
      · -- degenerate log: absorb its antiderivative into `v`
        obtain ⟨w0, hw0⟩ := exists_antideriv_of_not_nondegenerateLog _ hnd
        refine ih S (algebraMap F S.carrier (c a) * w0 + v) ?_
        have hcconst : (algebraMap F S.carrier (c a))′ = 0 := by
          rw [deriv_algebraMap, hc a, map_zero]
        rw [map_add, deriv_const_mul w0 hcconst, hw0, hv]
        ring

/-- **Assembly — the converse direction of the structure theorem**: a base weak Liouville
form yields an actual antiderivative element in a Liouville (log-tower) stage:
`∃ S v, ↑g = v′`. Nondegenerate logs are adjoined via `LiouvilleStage.extend`; degenerate
ones already have base antiderivatives and fold into `v`. -/
theorem hasWeakLiouvilleForm_exists_antiderivative {g : F}
    (h : HasWeakLiouvilleForm F F g) :
    ∃ (S : LiouvilleStage F) (v : S.carrier), algebraMap F S.carrier g = v′ := by
  obtain ⟨ι, fι, c, hc, u, v, hform⟩ := h
  refine exists_antideriv_aux c u hc g (@Finset.univ ι fι) LiouvilleStage.base v ?_
  show algebraMap F F g
      = (∑ x ∈ @Finset.univ ι fι,
          algebraMap F F (c x) * logDeriv (algebraMap F F (u x))) + v′
  simpa using hform

end Assembly

end DeepWiki.SymbolicIntegration.LiouvilleStructure
