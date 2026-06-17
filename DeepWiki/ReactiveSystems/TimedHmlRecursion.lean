import DeepWiki.ReactiveSystems.TimedHmlClocks
import Mathlib.Order.FixedPoints

/-! # Recursion in Hennessy–Milner logic with time
Extending the timed logic `Mt` with a recursion variable `X` lets formulae
express ongoing real-time properties. A formula `F` with one variable induces a
monotone semantic function `O_F` on the powerset lattice of *extended states*
`(p, u)`; the meaning of `X =ν F` (resp. `X =μ F`) is the
greatest (resp. least) fixed point of `O_F`, which exists by Tarski. We add a
box/diamond over *all* actions (the book's `[Act]`/`⟨Act⟩`) and embed the
recursion-free logic `Mt`, then define the derived real-time operators `Inv`
and `until` as largest fixed points. -/

namespace DeepWiki.ReactiveSystems

/-- Timed HML with one recursion variable `X` (`var`): `Mt` plus the
box/diamond over *all* actions (`boxAll`/`diaAll`, the book's
`[Act]`/`⟨Act⟩`). -/
inductive MtR (Act D : Type*)
  | var : MtR Act D
  | tt : MtR Act D
  | ff : MtR Act D
  | and : MtR Act D → MtR Act D → MtR Act D
  | or : MtR Act D → MtR Act D → MtR Act D
  | dia : Act → MtR Act D → MtR Act D
  | box : Act → MtR Act D → MtR Act D
  | diaAll : MtR Act D → MtR Act D
  | boxAll : MtR Act D → MtR Act D
  | existsDelay : MtR Act D → MtR Act D
  | forallDelay : MtR Act D → MtR Act D
  | reset : D → MtR Act D → MtR Act D
  | guard : ClockConstraint D → MtR Act D

/-- Embed a recursion-free `Mt` formula into `MtR`. -/
def Mt.toMtR {Act D : Type*} : Mt Act D → MtR Act D
  | .tt => .tt
  | .ff => .ff
  | .and F G => .and F.toMtR G.toMtR
  | .or F G => .or F.toMtR G.toMtR
  | .dia a F => .dia a F.toMtR
  | .box a F => .box a F.toMtR
  | .existsDelay F => .existsDelay F.toMtR
  | .forallDelay F => .forallDelay F.toMtR
  | .reset x F => .reset x F.toMtR
  | .guard g => .guard g

namespace TLTS

variable {Proc Act D : Type*}

/-- `O_F(S)`: the set of extended states `(p, u)` satisfying `F` when the
recursion variable `X` is interpreted as the set `S`. Action modalities keep
the formula clocks, delay modalities advance them, `x in F` resets `x`, and `g`
reads the formula-clock valuation. -/
def denotMtR (T : TLTS Proc Act) : MtR Act D → Set (Proc × Valuation D) → Set (Proc × Valuation D)
  | .var => fun S => S
  | .tt => fun _ => Set.univ
  | .ff => fun _ => ∅
  | .and F G => fun S => denotMtR T F S ∩ denotMtR T G S
  | .or F G => fun S => denotMtR T F S ∪ denotMtR T G S
  | .dia a F => fun S => {q | ∃ p', T.act q.1 a p' ∧ (p', q.2) ∈ denotMtR T F S}
  | .box a F => fun S => {q | ∀ p', T.act q.1 a p' → (p', q.2) ∈ denotMtR T F S}
  | .diaAll F => fun S => {q | ∃ a p', T.act q.1 a p' ∧ (p', q.2) ∈ denotMtR T F S}
  | .boxAll F => fun S => {q | ∀ a p', T.act q.1 a p' → (p', q.2) ∈ denotMtR T F S}
  | .existsDelay F => fun S => {q | ∃ d p', T.delay q.1 d p' ∧ (p', q.2.add d) ∈ denotMtR T F S}
  | .forallDelay F => fun S => {q | ∀ d p', T.delay q.1 d p' → (p', q.2.add d) ∈ denotMtR T F S}
  | .reset x F => fun S => {q | (q.1, Valuation.reset {x} q.2) ∈ denotMtR T F S}
  | .guard g => fun _ => {q | satisfies q.2 g}

/-- `O_F` is monotone in `S`, so by Tarski its least and greatest fixed points
exist. -/
theorem denotMtR_mono (T : TLTS Proc Act) (F : MtR Act D) : Monotone (denotMtR T F) := by
  intro S S' hSS'
  induction F with
  | var => exact hSS'
  | tt => exact le_refl _
  | ff => exact le_refl _
  | and F G ihF ihG => exact Set.inter_subset_inter ihF ihG
  | or F G ihF ihG => exact Set.union_subset_union ihF ihG
  | dia a F ihF => exact fun q ⟨p', hstep, hp'⟩ => ⟨p', hstep, ihF hp'⟩
  | box a F ihF => exact fun q hq p' hstep => ihF (hq p' hstep)
  | diaAll F ihF => exact fun q ⟨a, p', hstep, hp'⟩ => ⟨a, p', hstep, ihF hp'⟩
  | boxAll F ihF => exact fun q hq a p' hstep => ihF (hq a p' hstep)
  | existsDelay F ihF => exact fun q ⟨d, p', hstep, hp'⟩ => ⟨d, p', hstep, ihF hp'⟩
  | forallDelay F ihF => exact fun q hq d p' hstep => ihF (hq d p' hstep)
  | reset x F ihF => exact fun q hq => ihF hq
  | guard g => exact le_refl _

/-- The recursion-free embedding satisfies `(p, u) ∈ O_{ofMt F}(S) ↔ (p, u) ⊨ F`,
independently of `S`: the recursion semantics extends the plain `Mt` semantics. -/
theorem mem_denotMtR_toMtR (T : TLTS Proc Act) (F : Mt Act D) (S : Set (Proc × Valuation D))
    (q : Proc × Valuation D) : q ∈ denotMtR T F.toMtR S ↔ T.MtSat q.1 q.2 F := by
  induction F generalizing q with
  | tt => simp [Mt.toMtR, denotMtR, MtSat]
  | ff => simp [Mt.toMtR, denotMtR, MtSat]
  | and F G ihF ihG => simp only [Mt.toMtR, denotMtR, MtSat, Set.mem_inter_iff, ihF, ihG]
  | or F G ihF ihG => simp only [Mt.toMtR, denotMtR, MtSat, Set.mem_union, ihF, ihG]
  | dia a F ihF => simp only [Mt.toMtR, denotMtR, MtSat, Set.mem_setOf_eq, ihF]
  | box a F ihF => simp only [Mt.toMtR, denotMtR, MtSat, Set.mem_setOf_eq, ihF]
  | existsDelay F ihF => simp only [Mt.toMtR, denotMtR, MtSat, Set.mem_setOf_eq, ihF]
  | forallDelay F ihF => simp only [Mt.toMtR, denotMtR, MtSat, Set.mem_setOf_eq, ihF]
  | reset x F ihF => simp only [Mt.toMtR, denotMtR, MtSat, Set.mem_setOf_eq, ihF]
  | guard g => simp [Mt.toMtR, denotMtR, MtSat]

/-- The recursion-free embedding `O_{ofMt F}(S)` is the satisfaction set of `F`. -/
theorem denotMtR_toMtR (T : TLTS Proc Act) (F : Mt Act D) (S : Set (Proc × Valuation D)) :
    denotMtR T F.toMtR S = {q | T.MtSat q.1 q.2 F} :=
  Set.ext fun q => mem_denotMtR_toMtR T F S q

/-- `O_F` bundled as a monotone map on the powerset lattice of extended states. -/
def denotMtRHom (T : TLTS Proc Act) (F : MtR Act D) :
    Set (Proc × Valuation D) →o Set (Proc × Valuation D) :=
  ⟨denotMtR T F, denotMtR_mono T F⟩

/-- Meaning of `X =ν F`: the greatest fixed point of `O_F`. -/
def recMax (T : TLTS Proc Act) (F : MtR Act D) : Set (Proc × Valuation D) :=
  (denotMtRHom T F).gfp

/-- Meaning of `X =μ F`: the least fixed point of `O_F`. -/
def recMin (T : TLTS Proc Act) (F : MtR Act D) : Set (Proc × Valuation D) :=
  (denotMtRHom T F).lfp

/-- `X =ν F` is a fixed point: `O_F(⟦X⟧) = ⟦X⟧`. -/
theorem denotMtR_recMax (T : TLTS Proc Act) (F : MtR Act D) :
    denotMtR T F (recMax T F) = recMax T F := (denotMtRHom T F).map_gfp

/-- `X =μ F` is a fixed point: `O_F(⟦X⟧) = ⟦X⟧`. -/
theorem denotMtR_recMin (T : TLTS Proc Act) (F : MtR Act D) :
    denotMtR T F (recMin T F) = recMin T F := (denotMtRHom T F).map_lfp

/-! ## Real-time temporal operators -/

/-- The invariant body `F ∧ [Act]X ∧ ∀∀X`; `Inv(F) =ν` this. -/
def mtInvBody (F : Mt Act D) : MtR Act D :=
  .and F.toMtR (.and (.boxAll .var) (.forallDelay .var))

/-- `Inv(F)` (always `F`): the greatest fixed point of `F ∧ [Act]X ∧
∀∀X` — `F` holds now, and persists after every action and every delay. -/
def mtInv (T : TLTS Proc Act) (F : Mt Act D) : Set (Proc × Valuation D) :=
  recMax T (mtInvBody F)

/-- The weak-until body `G ∨ (F ∧ [Act]X ∧ ∀∀X)`; `F until G =ν` this. -/
def mtUntilBody (F G : Mt Act D) : MtR Act D :=
  .or G.toMtR (.and F.toMtR (.and (.boxAll .var) (.forallDelay .var)))

/-- `F until G` (a *weak* until): the greatest fixed point of
`G ∨ (F ∧ [Act](F until G) ∧ ∀∀(F until G))` — `F` holds at least until `G`,
through every action and delay. -/
def mtUntil (T : TLTS Proc Act) (F G : Mt Act D) : Set (Proc × Valuation D) :=
  recMax T (mtUntilBody F G)

/-- Fixed-point unfolding of `Inv(F)`: an extended state is invariant for `F` iff
it satisfies `F` now, every action successor (clocks kept) is invariant, and every
delay successor (clocks advanced) is invariant. -/
theorem mtInv_unfold (T : TLTS Proc Act) (F : Mt Act D) (q : Proc × Valuation D) :
    q ∈ mtInv T F ↔
      T.MtSat q.1 q.2 F ∧
      (∀ a p', T.act q.1 a p' → (p', q.2) ∈ mtInv T F) ∧
      (∀ d p', T.delay q.1 d p' → (p', q.2.add d) ∈ mtInv T F) := by
  have h : mtInv T F = denotMtR T (mtInvBody F) (mtInv T F) :=
    (denotMtR_recMax T (mtInvBody F)).symm
  conv_lhs => rw [h]
  simp only [mtInvBody, denotMtR, Set.mem_inter_iff, Set.mem_setOf_eq, mem_denotMtR_toMtR]

end TLTS

end DeepWiki.ReactiveSystems
