import DeepWiki.ReactiveSystems.Bisimulation
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Choose

/-! # Hennessy–Milner logic
A modal logic whose formulae describe the step-by-step capabilities of a
process. Its key property (the Hennessy–Milner theorem) is that, over an
image-finite LTS, logical equivalence in HML coincides with strong bisimilarity:
two states satisfy the same formulae iff they are bisimilar. -/

namespace DeepWiki.ReactiveSystems

/-- Hennessy–Milner logic formulae over actions `Act`:
`tt`, `ff`, conjunction, disjunction, and the modalities `⟨a⟩` and `[a]`. -/
inductive HML (Act : Type*)
  | tt : HML Act
  | ff : HML Act
  | and : HML Act → HML Act → HML Act
  | or : HML Act → HML Act → HML Act
  | dia : Act → HML Act → HML Act
  | box : Act → HML Act → HML Act

instance {Act : Type*} : Inhabited (HML Act) := ⟨.tt⟩

namespace LTS

variable {Proc Act : Type*}

/-- Satisfaction `p ⊨ F`: when state `p` of `L` satisfies the
HML formula `F`. `⟨a⟩F` needs some `a`-successor satisfying `F`; `[a]F` needs all
of them to. -/
def Sat (L : LTS Proc Act) (p : Proc) : HML Act → Prop
  | .tt => True
  | .ff => False
  | .and F G => Sat L p F ∧ Sat L p G
  | .or F G => Sat L p F ∨ Sat L p G
  | .dia a F => ∃ p', L.step p a p' ∧ Sat L p' F
  | .box a F => ∀ p', L.step p a p' → Sat L p' F

@[inherit_doc] scoped notation:40 p:41 " ⊨[" L "] " F:41 => LTS.Sat L p F

/-- `p ⊨ tt` always holds. -/
@[simp] theorem sat_tt (L : LTS Proc Act) (p : Proc) : (p ⊨[L] HML.tt) ↔ True := Iff.rfl
/-- `p ⊨ ff` never holds. -/
@[simp] theorem sat_ff (L : LTS Proc Act) (p : Proc) : (p ⊨[L] HML.ff) ↔ False := Iff.rfl
/-- `p ⊨ F.and G ↔ p ⊨ F ∧ p ⊨ G`. -/
@[simp] theorem sat_and (L : LTS Proc Act) (p : Proc) (F G : HML Act) :
    (p ⊨[L] F.and G) ↔ (p ⊨[L] F) ∧ (p ⊨[L] G) := Iff.rfl
/-- `p ⊨ F.or G ↔ p ⊨ F ∨ p ⊨ G`. -/
@[simp] theorem sat_or (L : LTS Proc Act) (p : Proc) (F G : HML Act) :
    (p ⊨[L] F.or G) ↔ (p ⊨[L] F) ∨ (p ⊨[L] G) := Iff.rfl
/-- `p ⊨ ⟨a⟩F` iff some `a`-successor `p'` satisfies `F`. -/
@[simp] theorem sat_dia (L : LTS Proc Act) (p : Proc) (a : Act) (F : HML Act) :
    (p ⊨[L] HML.dia a F) ↔ ∃ p', (L ⊢ p ⟶[a] p') ∧ (p' ⊨[L] F) := Iff.rfl
/-- `p ⊨ [a]F` iff every `a`-successor `p'` satisfies `F`. -/
@[simp] theorem sat_box (L : LTS Proc Act) (p : Proc) (a : Act) (F : HML Act) :
    (p ⊨[L] HML.box a F) ↔ ∀ p', (L ⊢ p ⟶[a] p') → (p' ⊨[L] F) := Iff.rfl

/-- `⟨a⟩tt` says a state can perform an `a`-action. -/
theorem sat_dia_tt (L : LTS Proc Act) (p : Proc) (a : Act) :
    (p ⊨[L] HML.dia a HML.tt) ↔ ∃ p', L.step p a p' := by simp

/-- `[a]ff` says a state can perform no `a`-action (refuses `a`). -/
theorem sat_box_ff (L : LTS Proc Act) (p : Proc) (a : Act) :
    (p ⊨[L] HML.box a HML.ff) ↔ L.Refuses p a := Iff.rfl

/-- `⟦F⟧`: the set of states of `L` satisfying `F`. -/
def denot (L : LTS Proc Act) (F : HML Act) : Set Proc := {p | p ⊨[L] F}

/-- Two states are HML-equivalent when they satisfy exactly the same formulae. -/
def HMLEquiv (L : LTS Proc Act) (p q : Proc) : Prop := ∀ F, (p ⊨[L] F) ↔ (q ⊨[L] F)

/-! ## The negation dual of an HML formula -/

/-- The De Morgan dual `F̄` of an HML formula (semantic negation). -/
def _root_.DeepWiki.ReactiveSystems.HML.neg {Act : Type*} : HML Act → HML Act
  | .tt => .ff
  | .ff => .tt
  | .and F G => .or (HML.neg F) (HML.neg G)
  | .or F G => .and (HML.neg F) (HML.neg G)
  | .dia a F => .box a (HML.neg F)
  | .box a F => .dia a (HML.neg F)

/-- The dual negates satisfaction: `p ⊨ F̄ ↔ ¬ p ⊨ F`. -/
theorem sat_neg (L : LTS Proc Act) (p : Proc) (F : HML Act) :
    (p ⊨[L] F.neg) ↔ ¬ (p ⊨[L] F) := by
  induction F generalizing p with
  | tt => show (p ⊨[L] HML.ff) ↔ ¬ (p ⊨[L] HML.tt); simp
  | ff => show (p ⊨[L] HML.tt) ↔ ¬ (p ⊨[L] HML.ff); simp
  | and F G ihF ihG =>
      show ((p ⊨[L] F.neg) ∨ (p ⊨[L] G.neg)) ↔ ¬ ((p ⊨[L] F) ∧ (p ⊨[L] G))
      rw [ihF p, ihG p, not_and_or]
  | or F G ihF ihG =>
      show ((p ⊨[L] F.neg) ∧ (p ⊨[L] G.neg)) ↔ ¬ ((p ⊨[L] F) ∨ (p ⊨[L] G))
      rw [ihF p, ihG p, not_or]
  | dia a F ihF =>
      constructor
      · rintro h ⟨p', hstep, hsat⟩; exact ((ihF p').mp (h p' hstep)) hsat
      · intro h p' hstep; exact (ihF p').mpr fun hsat => h ⟨p', hstep, hsat⟩
  | box a F ihF =>
      constructor
      · rintro ⟨p', hstep, hsat⟩ hbox; exact ((ihF p').mp hsat) (hbox p' hstep)
      · intro h
        by_contra hcon
        exact h fun p' hstep => by
          by_contra hsat; exact hcon ⟨p', hstep, (ihF p').mpr hsat⟩

/-- The dual's denotation is the complement: `⟦F̄⟧ = ⟦F⟧ᶜ`. -/
theorem denot_neg (L : LTS Proc Act) (F : HML Act) : denot L F.neg = (denot L F)ᶜ := by
  ext p; simp [denot, sat_neg]

/-! ## Finite conjunction -/

/-- The conjunction of a list of HML formulae. -/
def _root_.DeepWiki.ReactiveSystems.HML.bigAnd {Act : Type*} : List (HML Act) → HML Act
  | [] => .tt
  | F :: Fs => .and F (HML.bigAnd Fs)

/-- `p ⊨ bigAnd Fs` iff `p` satisfies every formula in the list `Fs`. -/
@[simp] theorem sat_bigAnd (L : LTS Proc Act) (p : Proc) (Fs : List (HML Act)) :
    (p ⊨[L] HML.bigAnd Fs) ↔ ∀ F ∈ Fs, (p ⊨[L] F) := by
  induction Fs with
  | nil => simp [HML.bigAnd]
  | cons F Fs ih => simp [HML.bigAnd, ih]

/-! ## Easy direction: bisimilar states are HML-equivalent (any LTS) -/

/-- Bisimilar states satisfy the same formulae (one implication). -/
theorem bisimilar_sat {L : LTS Proc Act} (F : HML Act) :
    ∀ {p q}, Bisimilar L p q → (p ⊨[L] F) → (q ⊨[L] F) := by
  induction F with
  | tt => exact fun _ _ => trivial
  | ff => exact fun _ h => h
  | and F G ihF ihG => exact fun hb hp => ⟨ihF hb hp.1, ihG hb hp.2⟩
  | or F G ihF ihG => exact fun hb hp => hp.imp (ihF hb) (ihG hb)
  | dia a F ihF =>
      intro p q hb hp
      obtain ⟨p', hstep, hsat⟩ := hp
      obtain ⟨q', hq', hb'⟩ := ((bisimilar_iff p q).mp hb).1 a p' hstep
      exact ⟨q', hq', ihF hb' hsat⟩
  | box a F ihF =>
      intro p q hb hp q' hq'
      obtain ⟨p', hp', hb'⟩ := ((bisimilar_iff p q).mp hb).2 a q' hq'
      exact ihF hb' (hp p' hp')

/-- **Easy direction.** Strongly bisimilar states are HML-equivalent. -/
theorem bisimilar_hmlEquiv {L : LTS Proc Act} {p q : Proc} (h : Bisimilar L p q) :
    HMLEquiv L p q := fun F => ⟨bisimilar_sat F h, bisimilar_sat F h.symm⟩

/-! ## Hard direction: HML-equivalence is a bisimulation on image-finite LTSs -/

/-- An LTS is image finite when every state has finitely many
`a`-successors, for each action `a`. -/
def ImageFinite (L : LTS Proc Act) : Prop := ∀ (p : Proc) (a : Act), {p' | L.step p a p'}.Finite

/-- Any LTS over a finite state type is image finite. -/
theorem imageFinite_of_finite [Finite Proc] (L : LTS Proc Act) : ImageFinite L :=
  fun _ _ => Set.toFinite _

/-- If two states are not HML-equivalent, a formula holds of the first and fails
of the second (orienting via the dual). -/
theorem exists_distinguish {L : LTS Proc Act} {p q : Proc}
    (h : ¬ HMLEquiv L p q) : ∃ G, (p ⊨[L] G) ∧ ¬ (q ⊨[L] G) := by
  simp only [HMLEquiv, not_forall] at h
  obtain ⟨F, hF⟩ := h
  by_cases hp : (p ⊨[L] F)
  · exact ⟨F, hp, fun hq => hF ⟨fun _ => hq, fun _ => hp⟩⟩
  · have hq : (q ⊨[L] F) := by
      by_contra hq; exact hF ⟨fun h => absurd h hp, fun h => absurd h hq⟩
    exact ⟨F.neg, (sat_neg L p F).mpr hp, fun hcon => (sat_neg L q F).mp hcon hq⟩

/-- **Hard direction.** On an image-finite LTS, HML-equivalence is a strong
bisimulation: an unmatched move would be exposed by `⟨a⟩` of the finite
conjunction of distinguishing formulae. -/
theorem hmlEquiv_isBisimulation {L : LTS Proc Act} (hfin : ImageFinite L) :
    IsBisimulation L (HMLEquiv L) := by
  have key : ∀ {p q}, HMLEquiv L p q → ∀ {a p'}, L.step p a p' →
      ∃ q', L.step q a q' ∧ HMLEquiv L p' q' := by
    intro p q h a p' hstep
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    have hd : ∀ q', L.step q a q' → ∃ G, (p' ⊨[L] G) ∧ ¬ (q' ⊨[L] G) :=
      fun q' hq' => exists_distinguish (hcon q' hq')
    choose! g hg1 hg2 using hd
    have hΦp : p ⊨[L] HML.dia a (HML.bigAnd (((hfin q a).toFinset).toList.map g)) := by
      refine ⟨p', hstep, ?_⟩
      rw [sat_bigAnd]
      intro G hG
      rw [List.mem_map] at hG
      obtain ⟨q', hq'mem, rfl⟩ := hG
      rw [Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hq'mem
      exact hg1 q' hq'mem
    obtain ⟨q'', hstep'', hsat''⟩ := (h _).mp hΦp
    rw [sat_bigAnd] at hsat''
    refine hg2 q'' hstep'' (hsat'' (g q'') ?_)
    rw [List.mem_map]
    exact ⟨q'', by rw [Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact hstep'', rfl⟩
  intro p q h
  refine ⟨fun a p' hstep => key h hstep, fun a q' hstep => ?_⟩
  obtain ⟨p', hp', hb⟩ := key (fun F => (h F).symm) hstep
  exact ⟨p', hp', fun F => (hb F).symm⟩

/-- **Hard direction.** On an image-finite LTS, HML-equivalent states are
strongly bisimilar. -/
theorem hmlEquiv_bisimilar {L : LTS Proc Act} (hfin : ImageFinite L) {p q : Proc}
    (h : HMLEquiv L p q) : Bisimilar L p q :=
  (hmlEquiv_isBisimulation hfin).le_bisimilar h

/-- Hennessy–Milner theorem. On an image-finite LTS, strong
bisimilarity coincides with HML-equivalence: `p ~ q` iff `p` and `q` satisfy
exactly the same Hennessy–Milner formulae. -/
theorem hennessyMilner {L : LTS Proc Act} (hfin : ImageFinite L) (p q : Proc) :
    Bisimilar L p q ↔ HMLEquiv L p q :=
  ⟨bisimilar_hmlEquiv, hmlEquiv_bisimilar hfin⟩

end LTS

end DeepWiki.ReactiveSystems
