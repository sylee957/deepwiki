import DeepWiki.ReactiveSystems.TimedTransitionSystems

/-! # Hennessy–Milner logic with time (basic logic)
The basic timed logic adds to HML two *delay quantifiers*: `∃∃F` (the process can
delay for some amount of time to a state satisfying `F`) and `∀∀F` (after every
delay the resulting state satisfies `F`), alongside the usual action modalities.
Timed-bisimilar states satisfy the same timed formulae — the soundness half of
the timed Hennessy–Milner theorem; it holds for every TLTS (the converse needs
the region abstraction, since delay-branching is uncountable). -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- Basic Hennessy–Milner logic with time: HML over actions together with
the delay quantifiers `∃∃` and `∀∀`. -/
inductive TimedHML (Act : Type*)
  | tt : TimedHML Act
  | ff : TimedHML Act
  | and : TimedHML Act → TimedHML Act → TimedHML Act
  | or : TimedHML Act → TimedHML Act → TimedHML Act
  | dia : Act → TimedHML Act → TimedHML Act
  | box : Act → TimedHML Act → TimedHML Act
  | existsDelay : TimedHML Act → TimedHML Act
  | forallDelay : TimedHML Act → TimedHML Act

namespace TLTS

variable {Proc Act : Type*}

/-- Satisfaction of a basic timed formula in a TLTS: `⟨a⟩`/`[a]` quantify
over `a`-transitions, `∃∃`/`∀∀` over time-delay transitions. -/
def TSat (T : TLTS Proc Act) (p : Proc) : TimedHML Act → Prop
  | .tt => True
  | .ff => False
  | .and F G => TSat T p F ∧ TSat T p G
  | .or F G => TSat T p F ∨ TSat T p G
  | .dia a F => ∃ p', T.act p a p' ∧ TSat T p' F
  | .box a F => ∀ p', T.act p a p' → TSat T p' F
  | .existsDelay F => ∃ d p', T.delay p d p' ∧ TSat T p' F
  | .forallDelay F => ∀ d p', T.delay p d p' → TSat T p' F

@[inherit_doc] scoped notation:40 p:41 " ⊨ₜ[" T "] " F:41 => TLTS.TSat T p F

/-- `p ⊨ₜ tt` always holds. -/
@[simp] theorem tsat_tt (T : TLTS Proc Act) (p : Proc) : (p ⊨ₜ[T] TimedHML.tt) ↔ True := Iff.rfl
/-- `p ⊨ₜ ff` never holds. -/
@[simp] theorem tsat_ff (T : TLTS Proc Act) (p : Proc) : (p ⊨ₜ[T] TimedHML.ff) ↔ False := Iff.rfl
/-- `p ⊨ₜ F ∧ G` unfolds to satisfying both conjuncts. -/
@[simp] theorem tsat_and (T : TLTS Proc Act) (p : Proc) (F G : TimedHML Act) :
    (p ⊨ₜ[T] F.and G) ↔ (p ⊨ₜ[T] F) ∧ (p ⊨ₜ[T] G) := Iff.rfl
/-- `p ⊨ₜ F ∨ G` unfolds to satisfying either disjunct. -/
@[simp] theorem tsat_or (T : TLTS Proc Act) (p : Proc) (F G : TimedHML Act) :
    (p ⊨ₜ[T] F.or G) ↔ (p ⊨ₜ[T] F) ∨ (p ⊨ₜ[T] G) := Iff.rfl
/-- `p ⊨ₜ ⟨a⟩F` unfolds to some `a`-successor satisfying `F`. -/
@[simp] theorem tsat_dia (T : TLTS Proc Act) (p : Proc) (a : Act) (F : TimedHML Act) :
    (p ⊨ₜ[T] TimedHML.dia a F) ↔ ∃ p', T.act p a p' ∧ (p' ⊨ₜ[T] F) := Iff.rfl
/-- `p ⊨ₜ [a]F` unfolds to every `a`-successor satisfying `F`. -/
@[simp] theorem tsat_box (T : TLTS Proc Act) (p : Proc) (a : Act) (F : TimedHML Act) :
    (p ⊨ₜ[T] TimedHML.box a F) ↔ ∀ p', T.act p a p' → (p' ⊨ₜ[T] F) := Iff.rfl
/-- `p ⊨ₜ ∃∃F` unfolds to some delay reaching a state satisfying `F`. -/
@[simp] theorem tsat_existsDelay (T : TLTS Proc Act) (p : Proc) (F : TimedHML Act) :
    (p ⊨ₜ[T] TimedHML.existsDelay F) ↔ ∃ d p', T.delay p d p' ∧ (p' ⊨ₜ[T] F) := Iff.rfl
/-- `p ⊨ₜ ∀∀F` unfolds to every delay reaching a state satisfying `F`. -/
@[simp] theorem tsat_forallDelay (T : TLTS Proc Act) (p : Proc) (F : TimedHML Act) :
    (p ⊨ₜ[T] TimedHML.forallDelay F) ↔ ∀ d p', T.delay p d p' → (p' ⊨ₜ[T] F) := Iff.rfl

/-- Two states are timed-HML equivalent when they satisfy the same timed
formulae. -/
def TimedHMLEquiv (T : TLTS Proc Act) (p q : Proc) : Prop := ∀ F, (p ⊨ₜ[T] F) ↔ (q ⊨ₜ[T] F)

/-- Timed-bisimilar states satisfy the same timed formula (one implication). -/
theorem timedBisimilar_tsat {T : TLTS Proc Act} (F : TimedHML Act) :
    ∀ {p q}, TimedBisimilar T p q → TSat T p F → TSat T q F := by
  induction F with
  | tt => exact fun _ _ => trivial
  | ff => exact fun _ h => h
  | and F G ihF ihG => exact fun hb hp => ⟨ihF hb hp.1, ihG hb hp.2⟩
  | or F G ihF ihG => exact fun hb hp => hp.imp (ihF hb) (ihG hb)
  | dia a F ihF =>
      intro p q hb hp
      obtain ⟨p', hstep, hsat⟩ := hp
      obtain ⟨q', hq', hb'⟩ := ((timedBisimilar_iff T p q).mp hb).1 a p' hstep
      exact ⟨q', hq', ihF hb' hsat⟩
  | box a F ihF =>
      intro p q hb hp q' hq'
      obtain ⟨p', hp', hb'⟩ := ((timedBisimilar_iff T p q).mp hb).2.1 a q' hq'
      exact ihF hb' (hp p' hp')
  | existsDelay F ihF =>
      intro p q hb hp
      obtain ⟨d, p', hstep, hsat⟩ := hp
      obtain ⟨q', hq', hb'⟩ := ((timedBisimilar_iff T p q).mp hb).2.2.1 d p' hstep
      exact ⟨d, q', hq', ihF hb' hsat⟩
  | forallDelay F ihF =>
      intro p q hb hp d q' hq'
      obtain ⟨p', hp', hb'⟩ := ((timedBisimilar_iff T p q).mp hb).2.2.2 d q' hq'
      exact ihF hb' (hp d p' hp')

/-- **Soundness of the timed Hennessy–Milner theorem.** Timed-bisimilar
states are timed-HML equivalent (this direction holds for every TLTS; the
converse uses the region abstraction). -/
theorem timedBisimilar_timedHmlEquiv {T : TLTS Proc Act} {p q : Proc}
    (h : TimedBisimilar T p q) : TimedHMLEquiv T p q :=
  fun F => ⟨timedBisimilar_tsat F h, timedBisimilar_tsat F h.symm⟩

end TLTS

end DeepWiki.ReactiveSystems
