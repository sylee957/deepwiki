import DeepWiki.ReactiveSystems.TimedCcs

/-! # TCCS: determinacy of delay and persistency of action (Exercise 9.3)
The book identifies `P` with `ε(0).P` (p.166: "we shall not distinguish the terms
`P` and `ε(0).P`"). Under that identification delay transitions are *deterministic*
— but as literal Lean terms they are not: `ε(d).P` delays `d` both to `ε(0).P`
(count-down) and to `P`'s own zero-delay successor (the prefix fully consumed), and
these are equal only up to `ε(0).P = P`. We model the identification by the normal
form `epsNorm` (strip every zero delay-prefix) and the induced congruence `EpsCong`,
then prove, for constant-free terms (the fragment the exercise restricts to):

* **Determinacy of delay**: `P —d→ P'` and `P —d→ P''` give `EpsCong P' P''`.
* **Persistency of action**: if `P` can perform `a` and `P —d→ Q`, then `Q` can still
  perform `a` (delays do not disable visible actions). -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

variable {Name K : Type*}

/-- A TCCS term is *constant-free* when no process constant occurs in it — the
fragment Exercise 9.3 restricts to (so the delay/action induction is structural). -/
def IsConstantFree : TCCS Name K → Prop
  | .nil => True
  | .const _ => False
  | .pre _ P => IsConstantFree P
  | .eps _ P => IsConstantFree P
  | .choice P Q => IsConstantFree P ∧ IsConstantFree Q
  | .restrict P _ => IsConstantFree P
  | .relabel P _ => IsConstantFree P

/-- Normal form under the book's identification `ε(0).P = P`: strip every
zero-delay prefix (recursively). -/
noncomputable def epsNorm : TCCS Name K → TCCS Name K
  | .nil => .nil
  | .const Kc => .const Kc
  | .pre α P => .pre α (epsNorm P)
  | .eps d P => if d = 0 then epsNorm P else .eps d (epsNorm P)
  | .choice P Q => .choice (epsNorm P) (epsNorm Q)
  | .restrict P L => .restrict (epsNorm P) L
  | .relabel P f => .relabel (epsNorm P) f

/-- `ε(0).P` and `P` have the same normal form (the generating identification). -/
@[simp] theorem epsNorm_eps_zero (P : TCCS Name K) : epsNorm (.eps 0 P) = epsNorm P := by
  simp [epsNorm]

/-- **The `ε(0)`-congruence**: two TCCS terms are identified iff they have the same
normal form — the formal reading of "we shall not distinguish `P` and `ε(0).P`". -/
def EpsCong (P Q : TCCS Name K) : Prop := epsNorm P = epsNorm Q

/-- `EpsCong` is reflexive. -/
@[refl] theorem EpsCong.refl (P : TCCS Name K) : EpsCong P P := rfl

/-- `EpsCong` is symmetric. -/
theorem EpsCong.symm {P Q : TCCS Name K} (h : EpsCong P Q) : EpsCong Q P := Eq.symm h

/-- `EpsCong` is transitive. -/
theorem EpsCong.trans {P Q R : TCCS Name K} (h₁ : EpsCong P Q) (h₂ : EpsCong Q R) :
    EpsCong P R := Eq.trans h₁ h₂

/-- `EpsCong` is an equivalence relation. -/
theorem epsCong_equivalence : Equivalence (EpsCong : TCCS Name K → TCCS Name K → Prop) :=
  ⟨EpsCong.refl, EpsCong.symm, EpsCong.trans⟩

/-- The generating identification `ε(0).P ≡ P`. -/
theorem epsCong_eps_zero (P : TCCS Name K) : EpsCong (.eps 0 P) P := epsNorm_eps_zero P

/-- `EpsCong` is a congruence for the action prefix. -/
theorem EpsCong.pre {P P' : TCCS Name K} (α : Act Name) (h : EpsCong P P') :
    EpsCong (.pre α P) (.pre α P') := by
  show epsNorm (.pre α P) = epsNorm (.pre α P'); simp only [epsNorm]; rw [h]

/-- `EpsCong` is a congruence for the delay prefix. -/
theorem EpsCong.eps {P P' : TCCS Name K} (d : ℝ≥0) (h : EpsCong P P') :
    EpsCong (.eps d P) (.eps d P') := by
  show epsNorm (.eps d P) = epsNorm (.eps d P'); simp only [epsNorm]; rw [h]

/-- `EpsCong` is a congruence for choice. -/
theorem EpsCong.choice {P P' Q Q' : TCCS Name K} (hP : EpsCong P P') (hQ : EpsCong Q Q') :
    EpsCong (.choice P Q) (.choice P' Q') := by
  show epsNorm (.choice P Q) = epsNorm (.choice P' Q'); simp only [epsNorm]; rw [hP, hQ]

/-- `EpsCong` is a congruence for restriction. -/
theorem EpsCong.restrict {P P' : TCCS Name K} (L : Set (Act Name)) (h : EpsCong P P') :
    EpsCong (.restrict P L) (.restrict P' L) := by
  show epsNorm (.restrict P L) = epsNorm (.restrict P' L); simp only [epsNorm]; rw [h]

/-- `EpsCong` is a congruence for relabelling. -/
theorem EpsCong.relabel {P P' : TCCS Name K} (f : Act Name → Act Name) (h : EpsCong P P') :
    EpsCong (.relabel P f) (.relabel P' f) := by
  show epsNorm (.relabel P f) = epsNorm (.relabel P' f); simp only [epsNorm]; rw [h]

/-! ## Delay preserves the normal form at duration `0` -/

/-- A zero delay keeps the normal form: if `P —0→ P'` then `P'` and `P` are
`ε(0)`-congruent (the dynamic form of `ε(0).P = P`). -/
theorem epsNorm_eq_of_tDelay_zero {defn : K → TCCS Name K} :
    ∀ {P : TCCS Name K}, IsConstantFree P → ∀ {P' : TCCS Name K},
      TDelay defn P 0 P' → epsNorm P' = epsNorm P := by
  intro P
  induction P with
  | nil => intro _ P' h; rw [tDelay_nil_iff] at h; exact h.elim
  | const Kc => intro hcf; exact absurd hcf (by simp [IsConstantFree])
  | pre α S _ =>
      intro _ P' h
      rw [tDelay_pre_iff] at h
      obtain ⟨_, rfl⟩ := h; rfl
  | eps e S ih =>
      intro hcf P' h
      rw [tDelay_eps_iff] at h
      rcases h with ⟨_, rfl⟩ | ⟨d', heq, hS⟩
      · rw [tsub_zero]
      · obtain ⟨he, hd'⟩ := add_eq_zero.mp heq.symm
        subst he; subst hd'
        rw [epsNorm_eps_zero]; exact ih hcf hS
  | choice S T ihS ihT =>
      intro hcf P' h
      rw [tDelay_choice_iff] at h
      obtain ⟨S', T', hS, hT, rfl⟩ := h
      simp only [epsNorm]
      rw [ihS hcf.1 hS, ihT hcf.2 hT]
  | restrict S L ih =>
      intro hcf P' h
      rw [tDelay_restrict_iff] at h
      obtain ⟨S', hS, rfl⟩ := h
      simp only [epsNorm]; rw [ih hcf hS]
  | relabel S f ih =>
      intro hcf P' h
      rw [tDelay_relabel_iff] at h
      obtain ⟨S', hS, rfl⟩ := h
      simp only [epsNorm]; rw [ih hcf hS]

/-! ## Exercise 9.3: determinacy of delay transitions -/

/-- **Determinacy of delay (Exercise 9.3)**: a constant-free TCCS term has, up to the
identification `ε(0).P = P`, at most one `d`-delay successor — if `P —d→ P'` and
`P —d→ P''` then `EpsCong P' P''`. -/
theorem tDelay_determinacy_epsCong {defn : K → TCCS Name K} :
    ∀ {P : TCCS Name K}, IsConstantFree P → ∀ {d : ℝ≥0} {P' P'' : TCCS Name K},
      TDelay defn P d P' → TDelay defn P d P'' → EpsCong P' P'' := by
  intro P
  induction P with
  | nil => intro _ d P' P'' h _; rw [tDelay_nil_iff] at h; exact h.elim
  | const Kc => intro hcf; exact absurd hcf (by simp [IsConstantFree])
  | pre α S _ =>
      intro _ d P' P'' h1 h2
      rw [tDelay_pre_iff] at h1 h2
      obtain ⟨_, rfl⟩ := h1; obtain ⟨_, rfl⟩ := h2; rfl
  | eps e S ih =>
      intro hcf d P' P'' h1 h2
      rw [tDelay_eps_iff] at h1 h2
      rcases h1 with ⟨hle1, rfl⟩ | ⟨d1, heq1, hS1⟩ <;>
        rcases h2 with ⟨hle2, rfl⟩ | ⟨d2, heq2, hS2⟩
      · rfl
      · -- P' = ε(e−d).S (partial), P'' from S —d2→ (consume), d = e + d2 ≤ e ⟹ d = e, d2 = 0
        have hd2 : d2 = 0 := by
          have : e + d2 = e := le_antisymm (heq2 ▸ hle1) le_self_add
          simpa using this
        subst hd2
        have hde : d = e := by rw [heq2, add_zero]
        subst hde
        -- P' = ε(d−d).S = ε(0).S, and S —0→ P'' so epsNorm P'' = epsNorm S = epsNorm (ε(0).S)
        have hcfS : IsConstantFree S := hcf
        have : epsNorm S = epsNorm P'' :=
          (epsNorm_eq_of_tDelay_zero (P := S) hcfS hS2).symm
        show epsNorm (.eps (d - d) S) = epsNorm P''
        rw [tsub_self, epsNorm_eps_zero, this]
      · -- symmetric to the previous case
        have hd1 : d1 = 0 := by
          have : e + d1 = e := le_antisymm (heq1 ▸ hle2) le_self_add
          simpa using this
        subst hd1
        have hde : d = e := by rw [heq1, add_zero]
        subst hde
        have hcfS : IsConstantFree S := hcf
        have : epsNorm P' = epsNorm S := epsNorm_eq_of_tDelay_zero (P := S) hcfS hS1
        show epsNorm P' = epsNorm (.eps (d - d) S)
        rw [tsub_self, epsNorm_eps_zero, this]
      · -- both consume: same residual delay d1 = d2, apply IH on S
        have : d1 = d2 := add_left_cancel (heq1 ▸ heq2)
        subst this
        exact ih hcf hS1 hS2
  | choice S T ihS ihT =>
      intro hcf d P' P'' h1 h2
      rw [tDelay_choice_iff] at h1 h2
      obtain ⟨S1, T1, hS1, hT1, rfl⟩ := h1
      obtain ⟨S2, T2, hS2, hT2, rfl⟩ := h2
      show epsNorm (.choice S1 T1) = epsNorm (.choice S2 T2)
      simp only [epsNorm]
      rw [ihS hcf.1 hS1 hS2, ihT hcf.2 hT1 hT2]
  | restrict S L ih =>
      intro hcf d P' P'' h1 h2
      rw [tDelay_restrict_iff] at h1 h2
      obtain ⟨S1, hS1, rfl⟩ := h1
      obtain ⟨S2, hS2, rfl⟩ := h2
      show epsNorm (.restrict S1 L) = epsNorm (.restrict S2 L)
      simp only [epsNorm]; rw [ih hcf hS1 hS2]
  | relabel S f ih =>
      intro hcf d P' P'' h1 h2
      rw [tDelay_relabel_iff] at h1 h2
      obtain ⟨S1, hS1, rfl⟩ := h1
      obtain ⟨S2, hS2, rfl⟩ := h2
      show epsNorm (.relabel S1 f) = epsNorm (.relabel S2 f)
      simp only [epsNorm]; rw [ih hcf hS1 hS2]

/-! ## Exercise 9.3: persistency of action transitions -/

/-- **Persistency of action (Exercise 9.3)**: for a constant-free TCCS term, if `P`
can perform the action `a` and `P —d→ Q`, then `Q` can still perform `a` — a time
delay never disables a visible action. -/
theorem tAct_persistent_through_delay {defn : K → TCCS Name K} :
    ∀ {P : TCCS Name K}, IsConstantFree P → ∀ {a : Act Name} {Q : TCCS Name K} {d : ℝ≥0},
      (∃ P', TAct defn P a P') → TDelay defn P d Q → ∃ Q', TAct defn Q a Q' := by
  intro P
  induction P with
  | nil => intro _ a Q d ⟨P', hact⟩ _; cases hact
  | const Kc => intro hcf; exact absurd hcf (by simp [IsConstantFree])
  | pre α S _ =>
      intro _ a Q d ⟨P', hact⟩ hdel
      cases hact with
      | act =>
          rw [tDelay_pre_iff] at hdel
          obtain ⟨_, rfl⟩ := hdel
          exact ⟨_, TAct.act _ _⟩
  | eps e S ih =>
      intro hcf a Q d ⟨P', hact⟩ hdel
      cases hact with
      | eps0 hS =>
          rw [tDelay_eps_iff] at hdel
          rcases hdel with ⟨_, rfl⟩ | ⟨d', rfl, hSdel⟩
          · refine ⟨P', ?_⟩; rw [zero_tsub]; exact TAct.eps0 hS
          · exact ih hcf ⟨P', hS⟩ hSdel
  | choice S T ihS ihT =>
      intro hcf a Q d ⟨P', hact⟩ hdel
      rw [tDelay_choice_iff] at hdel
      obtain ⟨S', T', hSdel, hTdel, rfl⟩ := hdel
      cases hact with
      | suml hS => obtain ⟨Q', hQ'⟩ := ihS hcf.1 ⟨_, hS⟩ hSdel; exact ⟨Q', TAct.suml hQ'⟩
      | sumr hT => obtain ⟨Q', hQ'⟩ := ihT hcf.2 ⟨_, hT⟩ hTdel; exact ⟨Q', TAct.sumr hQ'⟩
  | restrict S L ih =>
      intro hcf a Q d ⟨P', hact⟩ hdel
      rw [tDelay_restrict_iff] at hdel
      obtain ⟨S', hSdel, rfl⟩ := hdel
      cases hact with
      | res haL hcoL hS =>
          obtain ⟨Q', hQ'⟩ := ih hcf ⟨_, hS⟩ hSdel
          exact ⟨_, TAct.res haL hcoL hQ'⟩
  | relabel S f ih =>
      intro hcf a Q d ⟨P', hact⟩ hdel
      rw [tDelay_relabel_iff] at hdel
      obtain ⟨S', hSdel, rfl⟩ := hdel
      cases hact with
      | rel hS =>
          obtain ⟨Q', hQ'⟩ := ih hcf ⟨_, hS⟩ hSdel
          exact ⟨_, TAct.rel hQ'⟩

end DeepWiki.ReactiveSystems
