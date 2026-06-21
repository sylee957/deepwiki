import DeepWiki.ReactiveSystems.TimedHmlRecursion
import Mathlib.Order.FixedPoints

/-! # Mutual recursion in Hennessy–Milner logic with time (equation systems)
The single-variable `MtR` (`TimedHmlRecursion`) can characterise only a
*single-location* timed system, since its one greatest-fixed-point variable reads
the lone behavioural class off the formula clocks. Characterising an arbitrary
(multi-location) timed automaton needs **mutual** recursion: an *equation system*
`{Xᵢ =ν Fᵢ}ᵢ` with one variable per behavioural class. We index variables by `ι`,
interpret a formula in a variable environment `ρ : ι → Set (extended states)`, and
take the system's meaning to be the greatest fixed point of the induced monotone
operator on the product lattice `ι → Set (extended states)`. Specialising `ι` to a
finite class set recovers the characteristic-formula construction for a finite-state
(e.g. region-graph) timed system. -/

namespace DeepWiki.ReactiveSystems

/-- Timed HML with a family of recursion variables indexed by `ι` (`var i` is `Xᵢ`):
otherwise the constructs of `MtR` — `Mt` plus the all-action box/diamond
`boxAll`/`diaAll`. -/
inductive MtRSys (ι Act D : Type*)
  | var : ι → MtRSys ι Act D
  | tt : MtRSys ι Act D
  | ff : MtRSys ι Act D
  | and : MtRSys ι Act D → MtRSys ι Act D → MtRSys ι Act D
  | or : MtRSys ι Act D → MtRSys ι Act D → MtRSys ι Act D
  | dia : Act → MtRSys ι Act D → MtRSys ι Act D
  | box : Act → MtRSys ι Act D → MtRSys ι Act D
  | diaAll : MtRSys ι Act D → MtRSys ι Act D
  | boxAll : MtRSys ι Act D → MtRSys ι Act D
  | existsDelay : MtRSys ι Act D → MtRSys ι Act D
  | forallDelay : MtRSys ι Act D → MtRSys ι Act D
  | reset : D → MtRSys ι Act D → MtRSys ι Act D
  | guard : ClockConstraint D → MtRSys ι Act D

namespace TLTS

variable {Proc Act D ι : Type*}

/-- `⟦F⟧ρ`: the extended states `(p, u)` satisfying `F` when each variable `Xᵢ` is
interpreted as the set `ρ i`. Mirrors `denotMtR`, with `var i ↦ ρ i`. -/
def denotSys (T : TLTS Proc Act) :
    MtRSys ι Act D → (ι → Set (Proc × Valuation D)) → Set (Proc × Valuation D)
  | .var i => fun ρ => ρ i
  | .tt => fun _ => Set.univ
  | .ff => fun _ => ∅
  | .and F G => fun ρ => denotSys T F ρ ∩ denotSys T G ρ
  | .or F G => fun ρ => denotSys T F ρ ∪ denotSys T G ρ
  | .dia a F => fun ρ => {q | ∃ p', T.act q.1 a p' ∧ (p', q.2) ∈ denotSys T F ρ}
  | .box a F => fun ρ => {q | ∀ p', T.act q.1 a p' → (p', q.2) ∈ denotSys T F ρ}
  | .diaAll F => fun ρ => {q | ∃ a p', T.act q.1 a p' ∧ (p', q.2) ∈ denotSys T F ρ}
  | .boxAll F => fun ρ => {q | ∀ a p', T.act q.1 a p' → (p', q.2) ∈ denotSys T F ρ}
  | .existsDelay F => fun ρ => {q | ∃ d p', T.delay q.1 d p' ∧ (p', q.2.add d) ∈ denotSys T F ρ}
  | .forallDelay F => fun ρ => {q | ∀ d p', T.delay q.1 d p' → (p', q.2.add d) ∈ denotSys T F ρ}
  | .reset x F => fun ρ => {q | (q.1, Valuation.reset {x} q.2) ∈ denotSys T F ρ}
  | .guard g => fun _ => {q | satisfies q.2 g}

/-- Each formula's denotation is monotone in the variable environment, so the
equation system's operator has greatest and least fixed points (Tarski). -/
theorem denotSys_mono (T : TLTS Proc Act) (F : MtRSys ι Act D) : Monotone (denotSys T F) := by
  intro ρ ρ' h
  induction F with
  | var i => exact h i
  | tt => exact le_refl _
  | ff => exact le_refl _
  | and F G ihF ihG => exact Set.inter_subset_inter ihF ihG
  | or F G ihF ihG => exact Set.union_subset_union ihF ihG
  | dia a F ihF => exact fun q ⟨p', hs, hp'⟩ => ⟨p', hs, ihF hp'⟩
  | box a F ihF => exact fun q hq p' hs => ihF (hq p' hs)
  | diaAll F ihF => exact fun q ⟨a, p', hs, hp'⟩ => ⟨a, p', hs, ihF hp'⟩
  | boxAll F ihF => exact fun q hq a p' hs => ihF (hq a p' hs)
  | existsDelay F ihF => exact fun q ⟨d, p', hs, hp'⟩ => ⟨d, p', hs, ihF hp'⟩
  | forallDelay F ihF => exact fun q hq d p' hs => ihF (hq d p' hs)
  | reset x F ihF => exact fun q hq => ihF hq
  | guard g => exact le_refl _

/-- The monotone operator on the product lattice `ι → Set (extended states)` induced
by an equation system `E` (`E i` is the body `Fᵢ` of variable `Xᵢ`): it maps an
environment `ρ` to `i ↦ ⟦Fᵢ⟧ρ`. -/
def sysOp (T : TLTS Proc Act) (E : ι → MtRSys ι Act D) :
    (ι → Set (Proc × Valuation D)) →o (ι → Set (Proc × Valuation D)) where
  toFun ρ := fun i => denotSys T (E i) ρ
  monotone' := by intro ρ ρ' h i; exact denotSys_mono T (E i) h

/-- Meaning of the equation system `{Xᵢ =ν Fᵢ}`: the greatest fixed point of `sysOp`,
a family `ι → Set (extended states)` assigning each variable its largest solution. -/
def recMaxSys (T : TLTS Proc Act) (E : ι → MtRSys ι Act D) : ι → Set (Proc × Valuation D) :=
  (sysOp T E).gfp

/-- The system meaning is a fixed point: `sysOp` maps `recMaxSys` to itself. -/
theorem sysOp_recMaxSys (T : TLTS Proc Act) (E : ι → MtRSys ι Act D) :
    sysOp T E (recMaxSys T E) = recMaxSys T E := (sysOp T E).map_gfp

/-- **Fixed-point unfolding (per variable).** Each variable equals the denotation of
its body under the whole solution: `⟦Xᵢ⟧ = ⟦Fᵢ⟧(recMaxSys)`. This is the mutual
analogue of `denotMtR_recMax`, and the equation that the characteristic formula of a
multi-location system relies on. -/
theorem recMaxSys_unfold (T : TLTS Proc Act) (E : ι → MtRSys ι Act D) (i : ι) :
    recMaxSys T E i = denotSys T (E i) (recMaxSys T E) :=
  (congrFun (sysOp_recMaxSys T E) i).symm

/-- **Coinduction for equation systems.** Any family `R` that is *post-fixed* — each
`R i` lies inside its body's denotation under `R` — is contained, componentwise, in
the greatest solution. This is the soundness engine for characteristic formulae:
the timed-bisimilarity classes form such a post-fixed family. -/
theorem recMaxSys_coinduction (T : TLTS Proc Act) (E : ι → MtRSys ι Act D)
    {R : ι → Set (Proc × Valuation D)} (h : ∀ i, R i ⊆ denotSys T (E i) R) (i : ι) :
    R i ⊆ recMaxSys T E i :=
  (sysOp T E).le_gfp h i

end TLTS

end DeepWiki.ReactiveSystems
