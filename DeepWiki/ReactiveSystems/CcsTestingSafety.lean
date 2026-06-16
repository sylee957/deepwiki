import DeepWiki.ReactiveSystems.CcsTesting

/-! # Testability of safety HML (Exercise 7.15 / Theorem 7.1)
The *positive* counterpart to Proposition 7.3: every formula in *recursion-free
safety HML* (`tt`, `ff`, `∧`, `[a]` — no `∨`, no `⟨a⟩`, no recursion) is testable.
A test is built by structural induction — `tt ↦ 0`, `ff ↦ bad̄.0`, `F ∧ G ↦
T_F + T_G`, `[a]F ↦ ā.T_F` (Example 7.1) — and a *bad-free* process weakly
satisfies `F` iff it passes `T_F` (`testOf_correct`). Each operator needs a
weak-transition decomposition of the composite `(s ∣ T_F) ∖ L`: the `0`/`bad̄.0`
base cases here, the `ā.T_F` sync decomposition and the `T_F + T_G` choice
decomposition for the inductive cases. -/

namespace DeepWiki.ReactiveSystems

namespace LTS

variable {Name K : Type*}

/-- Recursion-free **safety HML**: `tt`, `ff`, `∧`, `[a]` (no `∨`, no `⟨a⟩`, no
recursion) — exactly the fragment Exercise 7.15 builds tests for. -/
inductive SafetyF (Name : Type*)
  | tt : SafetyF Name
  | ff : SafetyF Name
  | and : SafetyF Name → SafetyF Name → SafetyF Name
  | box : Name → SafetyF Name → SafetyF Name

/-- A safety formula as an ordinary HML formula (over actions `Act Name`). -/
def SafetyF.toHML : SafetyF Name → HML (Act Name)
  | .tt => .tt
  | .ff => .ff
  | .and F G => .and F.toHML G.toHML
  | .box a F => .box (Act.name a) F.toHML

/-- The **test** built from a safety formula (Exercise 7.15): `tt ↦ 0`,
`ff ↦ bad̄.0`, `F ∧ G ↦ T_F + T_G`, `[a]F ↦ ā.T_F`. -/
def testOf (bad : Name) : SafetyF Name → CCS Name K
  | .tt => CCS.nil
  | .ff => CCS.pre (Act.coname bad) CCS.nil
  | .and F G => CCS.choice (testOf bad F) (testOf bad G)
  | .box a F => CCS.pre (Act.coname a) (testOf bad F)

/-- `s` is **bad-free**: no state reachable from `s` performs the reject action
`bad̄` (the tested process is over the real actions, with `bad` reserved). -/
def BadFree (defn : K → CCS Name K) (bad : Name) (s : CCS Name K) : Prop :=
  ∀ s', (ccsLTS defn).Reachable s s' → ∀ q, ¬ Step defn s' (Act.coname bad) q

/-- Bad-freeness is preserved by transitions. -/
theorem BadFree.step {defn : K → CCS Name K} {bad : Name} {s s' : CCS Name K} {μ : Act Name}
    (h : BadFree defn bad s) (hstep : Step defn s μ s') : BadFree defn bad s' := by
  intro s'' hreach q hq
  exact h s'' (Relation.ReflTransGen.head ⟨μ, hstep⟩ hreach) q hq

/-- **Exercise 7.15, `ff` case.** `bad̄.0` tests for `ff`: every process fails it
(the test rejects immediately), and no process satisfies `ff`. -/
theorem tests_ff (defn : K → CCS Name K) (bad : Name) (s : CCS Name K) :
    WSat (ccsLTS defn) Act.tau s SafetyF.ff.toHML ↔
      Passes defn bad s (testOf bad SafetyF.ff) := by
  rw [SafetyF.toHML]
  simp only [wsat_ff, false_iff]
  rw [Passes]
  push Not
  -- the composite `(s | bad̄.0) ∖ L` performs `bad̄` immediately
  refine ⟨interact bad s CCS.nil, ?_⟩
  refine Or.inr ⟨by simp, interact bad s (CCS.pre (Act.coname bad) CCS.nil),
    interact bad s CCS.nil, tauStar_refl _ _ _, ?_, tauStar_refl _ _ _⟩
  exact Step.res (conameBad_not_restrictNonBad bad) (nameBad_not_restrictNonBad bad)
    (Step.com2 (Step.act _ _))

/-- A silent run of `(s ∣ 0) ∖ L` mirrors a reachability run of `s` (the `0` never
moves). -/
theorem interact_nil_tauStar {defn : K → CCS Name K} {bad : Name} {s Z : CCS Name K}
    (h : tauStar (ccsLTS defn) Act.tau (interact bad s CCS.nil) Z) :
    ∃ s', Z = interact bad s' CCS.nil ∧ (ccsLTS defn).Reachable s s' := by
  induction h with
  | refl => exact ⟨s, rfl, Relation.ReflTransGen.refl⟩
  | @tail Zmid Z _ hstep ih =>
      obtain ⟨s', rfl, hreach⟩ := ih
      rw [ccsLTS_step, interact, step_restrict_iff] at hstep
      obtain ⟨Y, _, _, hpar, rfl⟩ := hstep
      rw [step_par_iff] at hpar
      rcases hpar with ⟨s'', hs, rfl⟩ | ⟨q', hn, rfl⟩ | ⟨ℓ, P', Q', _, _, _, hn, rfl⟩
      · exact ⟨s'', rfl, hreach.tail ⟨Act.tau, hs⟩⟩
      · cases hn
      · cases hn

/-- A `bad̄`-step of `(s ∣ 0) ∖ L` comes from `s` itself. -/
theorem interact_nil_cobad {defn : K → CCS Name K} {bad : Name} {s' W : CCS Name K}
    (h : Step defn (interact bad s' CCS.nil) (Act.coname bad) W) :
    ∃ q, Step defn s' (Act.coname bad) q := by
  rw [interact, step_restrict_iff] at h
  obtain ⟨Y, _, _, hpar, rfl⟩ := h
  rw [step_par_iff] at hpar
  rcases hpar with ⟨q, hs, rfl⟩ | ⟨q', hn, rfl⟩ | ⟨ℓ, P', Q', heq, _, _, _, rfl⟩
  · exact ⟨q, hs⟩
  · cases hn
  · exact absurd heq (by simp)

/-- **Exercise 7.15, `tt` case.** `0` tests for `tt`: every bad-free process passes
(it can never reject), and every process satisfies `tt`. -/
theorem tests_tt (defn : K → CCS Name K) (bad : Name) (s : CCS Name K)
    (hbf : BadFree defn bad s) :
    WSat (ccsLTS defn) Act.tau s SafetyF.tt.toHML ↔
      Passes defn bad s (testOf bad SafetyF.tt) := by
  simp only [SafetyF.toHML, testOf, wsat_tt, true_iff]
  intro X hX
  rcases hX with ⟨heq, _⟩ | ⟨_, Z1, Z2, htau, hstep, _⟩
  · simp at heq
  · obtain ⟨s', rfl, hreach⟩ := interact_nil_tauStar htau
    obtain ⟨q, hq⟩ := interact_nil_cobad hstep
    exact hbf s' hreach q hq

end LTS

end DeepWiki.ReactiveSystems
