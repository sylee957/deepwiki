import DeepWiki.ReactiveSystems.Bisimulation

/-! # Traces and trace equivalence
A trace of a process is a sequence of actions it can perform. Trace equivalence
identifies processes with equal trace sets — a first, and too coarse, attempt at
behavioural equivalence: strong bisimilarity implies trace equivalence but not
conversely. -/

namespace DeepWiki.ReactiveSystems

namespace LTS

variable {Proc Act : Type*}

/-- A finite labelled path `p —s→ q` following the action sequence `s`. -/
inductive Path (L : LTS Proc Act) : Proc → List Act → Proc → Prop
  | nil (p : Proc) : Path L p [] p
  | cons {p p' q : Proc} {a : Act} {s : List Act} :
      L.step p a p' → Path L p' s q → Path L p (a :: s) q

/-- `Traces L p`: the set of action sequences `p` can perform (§3.2). -/
def Traces (L : LTS Proc Act) (p : Proc) : Set (List Act) := {s | ∃ q, Path L p s q}

/-- Trace equivalence (Definition 3.1): `p` and `q` have equal trace sets. -/
def TraceEquiv (L : LTS Proc Act) (p q : Proc) : Prop := Traces L p = Traces L q

theorem mem_traces {L : LTS Proc Act} {p : Proc} {s : List Act} :
    s ∈ Traces L p ↔ ∃ q, Path L p s q := Iff.rfl

/-- Bisimilar states can mirror any labelled path, staying bisimilar. -/
theorem Bisimilar.path_forward {L : LTS Proc Act} {p : Proc} {s : List Act} {p' : Proc}
    (hp : Path L p s p') : ∀ {q}, Bisimilar L p q → ∃ q', Path L q s q' ∧ Bisimilar L p' q' := by
  induction hp with
  | nil p => exact fun {q} h => ⟨q, Path.nil q, h⟩
  | @cons p p₁ pe a s hstep _ ih =>
      intro q h
      obtain ⟨q₁, hq₁, hb₁⟩ := ((bisimilar_iff p q).mp h).1 a p₁ hstep
      obtain ⟨q', hpath, hb'⟩ := ih hb₁
      exact ⟨q', Path.cons hq₁ hpath, hb'⟩

/-- Strong bisimilarity implies equal trace sets. -/
theorem Bisimilar.traces_eq {L : LTS Proc Act} {p q : Proc} (h : Bisimilar L p q) :
    Traces L p = Traces L q := by
  ext s
  constructor
  · rintro ⟨p', hp⟩; obtain ⟨q', hq, _⟩ := h.path_forward hp; exact ⟨q', hq⟩
  · rintro ⟨q', hq⟩; obtain ⟨p', hp, _⟩ := h.symm.path_forward hq; exact ⟨p', hp⟩

/-- Strong bisimilarity implies trace equivalence (the converse fails). -/
theorem Bisimilar.traceEquiv {L : LTS Proc Act} {p q : Proc} (h : Bisimilar L p q) :
    TraceEquiv L p q := h.traces_eq

end LTS

end DeepWiki.ReactiveSystems
