import DeepWiki.ReactiveSystems.Ccs
import DeepWiki.ReactiveSystems.TimedTransitionSystems

/-! # Timed CCS (TCCS): syntax and SOS rules
Timed CCS (Wang Yi's TCCS) extends CCS with a single new construct, the
*delay-prefix* `ε(d).P` (wait `d` time units, then behave as `P`); `P` is
identified with `ε(0).P`. Its operational semantics is a TLTS: the **action**
transitions are the CCS rules (with `ε(0).P —α→ P'` whenever `P —α→ P'`), and the
**delay** transitions are: a delay-prefix counts down
(`ε(d).P —d'→ ε(d−d').P`, `d' ≤ d`) and then lets its body proceed
(`ε(d).P —d+d'→ P'` when `P —d'→ P'`); an action-prefix `α.P` idles patiently for
`α ≠ τ` (maximal progress makes `τ` urgent); choice, restriction and relabelling
delay componentwise (so a choice persists through a delay — delays are
deterministic). We model the fragment without parallel composition (added with a
maximal-progress side condition). -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- Timed CCS expressions: CCS extended with the delay-prefix `eps d P = ε(d).P`. -/
inductive TCCS (Name K : Type*)
  | nil : TCCS Name K
  | const : K → TCCS Name K
  | pre : Act Name → TCCS Name K → TCCS Name K
  | eps : ℝ≥0 → TCCS Name K → TCCS Name K
  | choice : TCCS Name K → TCCS Name K → TCCS Name K
  | restrict : TCCS Name K → Set (Act Name) → TCCS Name K
  | relabel : TCCS Name K → (Act Name → Act Name) → TCCS Name K

variable {Name K : Type*}

/-- An occurrence of a constant in a TCCS
expression is *guarded* if it lies within an action prefix `α.Q` or a positive
delay prefix `ε(d).Q` (`d > 0`). `IsGuarded P` holds when every constant
occurrence in `P` is guarded (a top-level bare constant is *not* guarded). -/
def IsGuarded : TCCS Name K → Prop
  | .nil => True
  | .const _ => False
  | .pre _ _ => True
  | .eps d P => 0 < d ∨ IsGuarded P
  | .choice P Q => IsGuarded P ∧ IsGuarded Q
  | .restrict P _ => IsGuarded P
  | .relabel P _ => IsGuarded P

/-- A TCCS definition environment is *guarded*
when every defining equation's body has only guarded constant occurrences. -/
def IsGuardedDefn (defn : K → TCCS Name K) : Prop := ∀ K0, IsGuarded (defn K0)

/-- **Action SOS for TCCS**: the CCS action rules, plus the transparency of
a zero delay `ε(0).P —α→ P'` (since `ε(0).P` is identified with `P`). A
delay-prefix `ε(d).P` with `d > 0` has no action transition — time must pass
first. -/
inductive TAct (defn : K → TCCS Name K) : TCCS Name K → Act Name → TCCS Name K → Prop
  /-- `α.P —α→ P`. -/
  | act (α : Act Name) (P : TCCS Name K) : TAct defn (.pre α P) α P
  /-- `ε(0).P` behaves as `P` for actions. -/
  | eps0 {P : TCCS Name K} {α : Act Name} {P' : TCCS Name K} :
      TAct defn P α P' → TAct defn (.eps 0 P) α P'
  /-- Left summand. -/
  | suml {P P' Q : TCCS Name K} {α : Act Name} : TAct defn P α P' → TAct defn (.choice P Q) α P'
  /-- Right summand. -/
  | sumr {P Q Q' : TCCS Name K} {α : Act Name} : TAct defn Q α Q' → TAct defn (.choice P Q) α Q'
  /-- Restriction (`α, ᾱ ∉ L`). -/
  | res {P P' : TCCS Name K} {α : Act Name} {L : Set (Act Name)} :
      α ∉ L → α.co ∉ L → TAct defn P α P' → TAct defn (.restrict P L) α (.restrict P' L)
  /-- Relabelling. -/
  | rel {P P' : TCCS Name K} {α : Act Name} {f : Act Name → Act Name} :
      TAct defn P α P' → TAct defn (.relabel P f) (f α) (.relabel P' f)
  /-- A constant moves as its body. -/
  | con {Kc : K} {α : Act Name} {P' : TCCS Name K} :
      TAct defn (defn Kc) α P' → TAct defn (.const Kc) α P'

/-- **Delay SOS for TCCS**: the time-delay transitions. -/
inductive TDelay (defn : K → TCCS Name K) : TCCS Name K → ℝ≥0 → TCCS Name K → Prop
  /-- After waiting out the whole prefix, the body proceeds: `ε(d).P —d+d'→ P'` if
  `P —d'→ P'`. -/
  | epsConsume {d : ℝ≥0} {P : TCCS Name K} {d' : ℝ≥0} {P' : TCCS Name K} :
      TDelay defn P d' P' → TDelay defn (.eps d P) (d + d') P'
  /-- A delay-prefix counts down: `ε(d).P —d'→ ε(d−d').P` for `d' ≤ d`. -/
  | epsPartial {d d' : ℝ≥0} {P : TCCS Name K} (h : d' ≤ d) :
      TDelay defn (.eps d P) d' (.eps (d - d') P)
  /-- A constant delays as its body. -/
  | con {Kc : K} {d : ℝ≥0} {P' : TCCS Name K} :
      TDelay defn (defn Kc) d P' → TDelay defn (.const Kc) d P'
  /-- An action-prefix idles patiently — for `α ≠ τ` (maximal progress: `τ` is
  urgent). -/
  | prePatient {α : Act Name} {P : TCCS Name K} (h : α ≠ Act.tau) (d : ℝ≥0) :
      TDelay defn (.pre α P) d (.pre α P)
  /-- A choice delays componentwise, persisting (delays are deterministic). -/
  | choice {P P' Q Q' : TCCS Name K} {d : ℝ≥0} :
      TDelay defn P d P' → TDelay defn Q d Q' → TDelay defn (.choice P Q) d (.choice P' Q')
  /-- Delay through restriction. -/
  | res {P P' : TCCS Name K} {d : ℝ≥0} {L : Set (Act Name)} :
      TDelay defn P d P' → TDelay defn (.restrict P L) d (.restrict P' L)
  /-- Delay through relabelling. -/
  | rel {P P' : TCCS Name K} {d : ℝ≥0} {f : Act Name → Act Name} :
      TDelay defn P d P' → TDelay defn (.relabel P f) d (.relabel P' f)

/-- The timed LTS generated by a TCCS definition environment:
states are TCCS expressions, action labels carry `TAct` and delay labels carry
`TDelay`. -/
def tccsTLTS (defn : K → TCCS Name K) : TLTS (TCCS Name K) (Act Name) :=
  ⟨fun P l Q => match l with
    | .inl α => TAct defn P α Q
    | .inr d => TDelay defn P d Q⟩

/-- An action step of `tccsTLTS defn` unfolds to `TAct defn P α Q`. -/
@[simp] theorem tccsTLTS_act (defn : K → TCCS Name K) (P : TCCS Name K) (α : Act Name)
    (Q : TCCS Name K) : (tccsTLTS defn).act P α Q ↔ TAct defn P α Q := Iff.rfl

/-- A delay step of `tccsTLTS defn` unfolds to `TDelay defn P d Q`. -/
@[simp] theorem tccsTLTS_delay (defn : K → TCCS Name K) (P : TCCS Name K) (d : ℝ≥0)
    (Q : TCCS Name K) : (tccsTLTS defn).delay P d Q ↔ TDelay defn P d Q := Iff.rfl

/-- A delay-prefix can wait out exactly its whole delay, reaching `ε(0).P`. -/
theorem TDelay.eps_full (defn : K → TCCS Name K) (d : ℝ≥0) (P : TCCS Name K) :
    TDelay defn (.eps d P) d (.eps 0 P) := by
  have h := TDelay.epsPartial (defn := defn) (d := d) (d' := d) (P := P) le_rfl
  rwa [tsub_self] at h

/-- An action-prefix `α.P` (`α ≠ τ`) idles for any delay, staying put — the
patience rule. -/
theorem TDelay.pre_idle (defn : K → TCCS Name K) {α : Act Name} (hα : α ≠ Act.tau)
    (P : TCCS Name K) (d : ℝ≥0) : TDelay defn (.pre α P) d (.pre α P) :=
  TDelay.prePatient hα d

/-- The book's `Light` step shape: the delay-prefixed
guard `ε(t).P` can let any `d ≤ t` elapse, decrementing the prefix. -/
theorem light_delay (defn : K → TCCS Name K) (t d : ℝ≥0) (h : d ≤ t) (P : TCCS Name K) :
    (tccsTLTS defn).delay (.eps t P) d (.eps (t - d) P) :=
  TDelay.epsPartial h

/-- A `τ`-prefix is **urgent**: `τ.P` cannot let any time elapse (the patience
rule excludes `τ`). This is the maximal-progress assumption at its source. -/
theorem TDelay.tau_urgent (defn : K → TCCS Name K) (P : TCCS Name K) (d : ℝ≥0)
    (Q : TCCS Name K) : ¬ TDelay defn (.pre Act.tau P) d Q := by
  rintro h
  cases h with
  | prePatient hne _ => exact hne rfl

/-- `τ.P` can perform its silent action. -/
theorem TAct.tau_pre (defn : K → TCCS Name K) (P : TCCS Name K) :
    TAct defn (.pre Act.tau P) Act.tau P := TAct.act _ _

/-- The silent prefix `τ.P` witnesses the maximal-progress assumption: it can do
`τ` yet cannot delay any positive amount of time. -/
theorem tccs_tau_maximalProgress (defn : K → TCCS Name K) (P : TCCS Name K) (d : ℝ≥0)
    (_hd : 0 < d) : ¬ ∃ Q, (tccsTLTS defn).delay (.pre Act.tau P) d Q := by
  rintro ⟨Q, hQ⟩
  exact TDelay.tau_urgent defn P d Q hQ

/-! ## Inversion lemmas for delay transitions -/

section Inversion
variable {Name K : Type*} {defn : K → TCCS Name K}

/-- Inversion for a delay of a delay-prefix: either the prefix counts down (`t ≤ d`,
reaching `ε(d−t).P`), or it is fully consumed and the body proceeds (`t = d + d'`). -/
theorem tDelay_eps_iff {d t : ℝ≥0} {P Q : TCCS Name K} :
    TDelay defn (.eps d P) t Q ↔
      (t ≤ d ∧ Q = .eps (d - t) P) ∨ (∃ d', t = d + d' ∧ TDelay defn P d' Q) := by
  constructor
  · intro h
    cases h with
    | epsConsume hP => exact Or.inr ⟨_, rfl, hP⟩
    | epsPartial hle => exact Or.inl ⟨hle, rfl⟩
  · rintro (⟨hle, rfl⟩ | ⟨d', rfl, hP⟩)
    · exact TDelay.epsPartial hle
    · exact TDelay.epsConsume hP

/-- Inversion for a delay of a choice: both summands delay by the same amount. -/
theorem tDelay_choice_iff {P Q R : TCCS Name K} {t : ℝ≥0} :
    TDelay defn (.choice P Q) t R ↔
      ∃ P' Q', TDelay defn P t P' ∧ TDelay defn Q t Q' ∧ R = .choice P' Q' := by
  constructor
  · intro h; cases h with | choice hP hQ => exact ⟨_, _, hP, hQ, rfl⟩
  · rintro ⟨P', Q', hP, hQ, rfl⟩; exact TDelay.choice hP hQ

/-- Inversion for a delay of a constant: it delays exactly as its body. -/
theorem tDelay_const_iff {Kc : K} {t : ℝ≥0} {Q : TCCS Name K} :
    TDelay defn (.const Kc) t Q ↔ TDelay defn (defn Kc) t Q := by
  constructor
  · intro h; cases h with | con hP => exact hP
  · exact TDelay.con

/-- Inversion for a delay of an action-prefix: only non-`τ` prefixes delay, and they
idle in place (maximal progress makes `τ` urgent). -/
theorem tDelay_pre_iff {α : Act Name} {P Q : TCCS Name K} {t : ℝ≥0} :
    TDelay defn (.pre α P) t Q ↔ α ≠ Act.tau ∧ Q = .pre α P := by
  constructor
  · intro h; cases h with | prePatient hα _ => exact ⟨hα, rfl⟩
  · rintro ⟨hα, rfl⟩; exact TDelay.prePatient hα t

/-- Inversion for a delay through restriction: the body delays and the restriction
persists. -/
theorem tDelay_restrict_iff {P Q : TCCS Name K} {L : Set (Act Name)} {t : ℝ≥0} :
    TDelay defn (.restrict P L) t Q ↔ ∃ P', TDelay defn P t P' ∧ Q = .restrict P' L := by
  constructor
  · intro h; cases h with | res hP => exact ⟨_, hP, rfl⟩
  · rintro ⟨P', hP, rfl⟩; exact TDelay.res hP

/-- Inversion for a delay through relabelling: the body delays and the relabelling
persists. -/
theorem tDelay_relabel_iff {P Q : TCCS Name K} {f : Act Name → Act Name} {t : ℝ≥0} :
    TDelay defn (.relabel P f) t Q ↔ ∃ P', TDelay defn P t P' ∧ Q = .relabel P' f := by
  constructor
  · intro h; cases h with | rel hP => exact ⟨_, hP, rfl⟩
  · rintro ⟨P', hP, rfl⟩; exact TDelay.rel hP

/-- Inversion for a delay of `nil`: `nil` has no delay transition (it is
time-stuck). -/
theorem tDelay_nil_iff {Q : TCCS Name K} {t : ℝ≥0} :
    TDelay defn .nil t Q ↔ False := by
  constructor
  · intro h; cases h
  · exact False.elim

end Inversion

end DeepWiki.ReactiveSystems
