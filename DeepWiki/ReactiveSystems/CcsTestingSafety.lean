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

/-! ### Reachability/bad-freeness transport along weak transitions -/

/-- A silent run is a reachability run. -/
theorem tauStar_reachable {defn : K → CCS Name K} {p q : CCS Name K}
    (h : tauStar (ccsLTS defn) Act.tau p q) : (ccsLTS defn).Reachable p q := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hstep ih => exact ih.tail ⟨Act.tau, hstep⟩

/-- A weak transition is a reachability run. -/
theorem weakStep_reachable {defn : K → CCS Name K} {p : CCS Name K} {α : Act Name}
    {q : CCS Name K} (h : (ccsLTS defn) ⊢ p =[α]⇒[Act.tau] q) : (ccsLTS defn).Reachable p q := by
  rcases h with ⟨_, hts⟩ | ⟨_, p1, p2, h1, hstep, h2⟩
  · exact tauStar_reachable hts
  · exact ((tauStar_reachable h1).tail ⟨α, hstep⟩).trans (tauStar_reachable h2)

/-- Bad-freeness is preserved along reachability. -/
theorem BadFree.reachable {defn : K → CCS Name K} {bad : Name} {s s' : CCS Name K}
    (h : BadFree defn bad s) (hr : (ccsLTS defn).Reachable s s') : BadFree defn bad s' :=
  fun s'' hr'' q hq => h s'' (hr.trans hr'') q hq

/-- A silent run of `s` lifts to `(s ∣ T) ∖ L` with the test `T` fixed (via the
left component). -/
theorem interact_com1_tauStar {defn : K → CCS Name K} {bad : Name} {s s' : CCS Name K}
    (test : CCS Name K) (h : tauStar (ccsLTS defn) Act.tau s s') :
    tauStar (ccsLTS defn) Act.tau (interact bad s test) (interact bad s' test) := by
  induction h with
  | refl => exact tauStar_refl _ _ _
  | @tail b c _ hstep ih =>
      refine tauStar_trans ih (tauStar_single ?_)
      rw [ccsLTS_step] at hstep ⊢
      exact Step.res (tau_not_restrictNonBad bad) (tau_not_restrictNonBad bad) (Step.com1 hstep)

/-! ### Modal case: the test `ā.T_G` -/

/-- **Forward sync decomposition.** A reject of `(s ∣ ā.T_G) ∖ L` (for bad-free
`s`, `a ≠ bad`) factors through a weak `a`-move of `s` reaching a reject of
`(s' ∣ T_G) ∖ L`: the test can only fire its guard `ā` by synchronising with `s`'s
`a`. -/
theorem box_forward {defn : K → CCS Name K} {bad a : Name} {s TG : CCS Name K}
    (hbf : BadFree defn bad s) (hab : a ≠ bad)
    (h : CanRej defn bad (interact bad s (CCS.pre (Act.coname a) TG))) :
    ∃ s', ((ccsLTS defn) ⊢ s =[Act.name a]⇒[Act.tau] s') ∧
      CanRej defn bad (interact bad s' TG) := by
  obtain ⟨Y, W, htau, hstep⟩ := h
  refine Relation.ReflTransGen.head_induction_on htau
    (motive := fun Z _ => ∀ t, Z = interact bad t (CCS.pre (Act.coname a) TG) →
      BadFree defn bad t → ∃ s', ((ccsLTS defn) ⊢ t =[Act.name a]⇒[Act.tau] s') ∧
        CanRej defn bad (interact bad s' TG))
    ?refl ?head s rfl hbf
  case refl =>
    rintro t rfl hbft
    -- the reject step `hstep` cannot fire while the test is still `ā.T_G`
    rw [interact, step_restrict_iff] at hstep
    obtain ⟨Y', _, _, hpar, _⟩ := hstep
    rw [step_par_iff] at hpar
    rcases hpar with ⟨q, ht, _⟩ | ⟨q', hT, _⟩ | ⟨ℓ, _, _, heq, _, _, _, _⟩
    · exact absurd ht (hbft t Relation.ReflTransGen.refl q)
    · rw [step_pre_iff] at hT; exact absurd (Act.coname.inj hT.1).symm hab
    · exact absurd heq (by simp)
  case head =>
    rintro Z c h' hc ih t rfl hbft
    rw [ccsLTS_step, interact, step_restrict_iff] at h'
    obtain ⟨Y', _, _, hpar, rfl⟩ := h'
    rw [step_par_iff] at hpar
    rcases hpar with ⟨t', ht, rfl⟩ | ⟨q', hT, rfl⟩ | ⟨ℓ, t', q', _, _, ht, hT, rfl⟩
    · -- `t` does τ alone: recurse, extend the weak `a` by a leading τ
      obtain ⟨s', hws, hcr⟩ := ih t' rfl (hbft.step ht)
      exact ⟨s', weakStep_tau_prefix (by simp) ht hws, hcr⟩
    · rw [step_pre_iff] at hT; exact absurd hT.1 (by simp)
    · -- synchronisation: `t —a→ t'`, the test becomes `T_G`
      rw [step_pre_iff] at hT
      obtain ⟨hℓco, rfl⟩ := hT
      cases ℓ with
      | tau => exact absurd hℓco (by simp [Act.co])
      | name c =>
          simp only [Act.co] at hℓco
          obtain rfl := Act.coname.inj hℓco
          exact ⟨t', step_weakStep ht, Y, W, hc, hstep⟩
      | coname c => exact absurd hℓco (by simp [Act.co])

/-- **Backward sync construction.** A weak `a`-move of `s` to a reject of
`(s' ∣ T_G) ∖ L` yields a reject of `(s ∣ ā.T_G) ∖ L`. -/
theorem box_backward {defn : K → CCS Name K} {bad a : Name} {s s' TG : CCS Name K}
    (hws : (ccsLTS defn) ⊢ s =[Act.name a]⇒[Act.tau] s')
    (hcr : CanRej defn bad (interact bad s' TG)) :
    CanRej defn bad (interact bad s (CCS.pre (Act.coname a) TG)) := by
  obtain ⟨Y, W, htauY, hstepW⟩ := hcr
  rcases hws with ⟨heq, _⟩ | ⟨_, s0, s1, h1, hastep, h2⟩
  · exact absurd heq (by simp)
  · refine ⟨Y, W, ?_, hstepW⟩
    have hsync : Step defn (interact bad s0 (CCS.pre (Act.coname a) TG)) Act.tau
        (interact bad s1 TG) := interact_sync hastep (Step.act _ _)
    refine tauStar_trans (interact_com1_tauStar (CCS.pre (Act.coname a) TG) h1) ?_
    refine tauStar_trans (tauStar_single hsync) ?_
    exact tauStar_trans (interact_com1_tauStar TG h2) htauY

/-- **Exercise 7.15, `[a]` case.** Given the test `T_G` tests for `G`, the test
`ā.T_G` tests for `[a]G` (for bad-free processes, `a ≠ bad`). -/
theorem tests_box {defn : K → CCS Name K} {bad a : Name} {TG : CCS Name K} {G : SafetyF Name}
    (hTG : ∀ s', BadFree defn bad s' →
      (WSat (ccsLTS defn) Act.tau s' G.toHML ↔ Passes defn bad s' TG))
    (hab : a ≠ bad) (s : CCS Name K) (hbf : BadFree defn bad s) :
    WSat (ccsLTS defn) Act.tau s (SafetyF.box a G).toHML ↔
      Passes defn bad s (CCS.pre (Act.coname a) TG) := by
  rw [SafetyF.toHML, wsat_box]
  constructor
  · -- `WSat s [a]G → Passes s (ā.T_G)`
    intro hall
    by_contra hnp
    obtain ⟨s', hws, hcr⟩ := box_forward hbf hab ((not_passes_iff_canRej defn bad s _).mp hnp)
    have hbf' := hbf.reachable (weakStep_reachable hws)
    exact (not_passes_iff_canRej defn bad s' TG).mpr hcr ((hTG s' hbf').mp (hall s' hws))
  · -- `Passes s (ā.T_G) → WSat s [a]G`
    intro hp s' hws
    have hbf' := hbf.reachable (weakStep_reachable hws)
    rw [hTG s' hbf']
    by_contra hnp
    exact (not_passes_iff_canRej defn bad s _).mpr
      (box_backward hws ((not_passes_iff_canRej defn bad s' TG).mp hnp)) hp

end LTS

end DeepWiki.ReactiveSystems
