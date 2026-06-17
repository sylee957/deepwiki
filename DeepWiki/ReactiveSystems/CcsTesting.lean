import DeepWiki.ReactiveSystems.Ccs
import DeepWiki.ReactiveSystems.Hml
import DeepWiki.ReactiveSystems.HmlWeak
import DeepWiki.ReactiveSystems.BisimulationWeak

/-! # Testing and testable formulae
A *test* is a (regular CCS) process over the actions plus a distinguished reject
channel `bad`. A process `s` *passes* a test `T` when the
composite `(s ∣ T) ∖ L` — hiding every observable channel except `bad` — cannot
perform a weak `bad`-transition; `T` *tests for* a formula `F` (and `F` is
*testable*) when passing `T` coincides with satisfying `F`, for every process.
Two *negative* results: the very simple
HML formulae `⟨a⟩tt` and `[a]ff ∨ [b]ff` are **not** testable — the testing
preorder cannot see existential or disjunctive branching the way HML can. -/

namespace DeepWiki.ReactiveSystems

namespace LTS

variable {Name K : Type*}

/-- The observable actions on channels other than `bad`; the composite `(s ∣ T)`
is restricted by exactly this set (`∖ L`), so only `bad`, `bad̄` and `τ` survive. -/
def restrictNonBad (bad : Name) : Set (Act Name) :=
  {α | ∃ c, c ≠ bad ∧ (α = Act.name c ∨ α = Act.coname c)}

/-- `τ` is never hidden by `∖ L` (it is neither a name nor a coname). -/
theorem tau_not_restrictNonBad (bad : Name) : (Act.tau : Act Name) ∉ restrictNonBad bad := by
  rintro ⟨c, _, h | h⟩ <;> simp at h

/-- The coname `bad̄` is never hidden by `∖ L`, so the reject signal survives. -/
theorem conameBad_not_restrictNonBad (bad : Name) :
    (Act.coname bad : Act Name) ∉ restrictNonBad bad := by
  rintro ⟨c, hc, h | h⟩
  · simp at h
  · exact hc (Act.coname.inj h).symm

/-- The name `bad` is never hidden by `∖ L` (so `bad̄.co = bad` survives too). -/
theorem nameBad_not_restrictNonBad (bad : Name) :
    (Act.name bad : Act Name) ∉ restrictNonBad bad := by
  rintro ⟨c, hc, h | h⟩
  · exact hc (Act.name.inj h).symm
  · simp at h

/-- The composite `(s ∣ T) ∖ L` of a process `s` with a test
`T`, hiding every observable channel except the reject channel `bad`. -/
def interact (bad : Name) (s test : CCS Name K) : CCS Name K :=
  CCS.restrict (CCS.par s test) (restrictNonBad bad)

/-- `s` *passes* test `T`: the composite `(s ∣ T) ∖ L` cannot
perform a weak `bad̄`-transition (the test never reaches its reject signal). -/
def Passes (defn : K → CCS Name K) (bad : Name) (s test : CCS Name K) : Prop :=
  ∀ X, ¬ ((ccsLTS defn) ⊢ interact bad s test =[Act.coname bad]⇒[Act.tau] X)

/-- Test `T` *tests for* `F` (so `F` is *testable*): a process
*weakly* satisfies `F` iff it passes `T`. (Satisfaction is the weak/observational
reading `WSat`, since testing observes behaviour up to `τ` — e.g. `[a]ff` holds of
the processes affording no weak `=a⇒` transition.) -/
def Tests (defn : K → CCS Name K) (bad : Name) (test : CCS Name K) (F : HML (Act Name)) : Prop :=
  ∀ s, WSat (ccsLTS defn) Act.tau s F ↔ Passes defn bad s test

/-- A weak `α`-transition (`α ≠ τ`) can be prefixed by one concrete `τ`-step. -/
theorem weakStep_tau_prefix {defn : K → CCS Name K} {X Y Z : CCS Name K} {α : Act Name}
    (hα : α ≠ Act.tau) (hxy : Step defn X Act.tau Y)
    (h : (ccsLTS defn) ⊢ Y =[α]⇒[Act.tau] Z) : (ccsLTS defn) ⊢ X =[α]⇒[Act.tau] Z := by
  rcases h with ⟨heq, _⟩ | ⟨_, p1, p2, hY1, hstep, h2⟩
  · exact absurd heq hα
  · exact Or.inr ⟨hα, p1, p2, tauStar_trans (tauStar_single hxy) hY1, hstep, h2⟩

/-! ## Two negative results -/

/-- For every action `a` (in particular
every observable `a ≠ bad`), the formula `⟨a⟩tt` is **not testable**: no test `T`
over any process system tests for it. The witnesses are `0` (fails `⟨a⟩tt`, so the
composite can reject) and `a.0 + τ.0` (satisfies `⟨a⟩tt`, yet `τ`-reduces to
`0 ∣ T`, so it can reject too) — a process cannot be required to *pass* `T` while a
`τ`-successor *fails*. -/
theorem dia_tt_not_testable (a bad : Name)
    (defn : K → CCS Name K) (test : CCS Name K)
    (h : Tests defn bad test (HML.dia (Act.name a) HML.tt)) : False := by
  -- `0` does not weakly satisfy `⟨a⟩tt`, so `0` fails the test: a weak reject exists.
  have hnil : ¬ WSat (ccsLTS defn) Act.tau (CCS.nil : CCS Name K)
      (HML.dia (Act.name a) HML.tt) := by
    rw [wsat_dia_tt]
    rintro ⟨p', hp'⟩
    rcases hp' with ⟨heq, _⟩ | ⟨_, p1, p2, htau, hstep, _⟩
    · simp at heq
    · obtain rfl := tauStar_eq_of_no_tau (fun q hq => by rw [ccsLTS_step] at hq; cases hq) htau
      rw [ccsLTS_step] at hstep; cases hstep
  have hnilFail : ¬ Passes defn bad CCS.nil test := fun hp => hnil ((h CCS.nil).2 hp)
  -- extract the witnessing weak reject of `(0 ∣ T) ∖ L`
  simp only [Passes, not_forall, not_not] at hnilFail
  obtain ⟨X, hX⟩ := hnilFail
  -- `a.0 + τ.0` weakly satisfies `⟨a⟩tt`, so it must pass the test
  set P : CCS Name K := CCS.choice (CCS.pre (Act.name a) CCS.nil) (CCS.pre Act.tau CCS.nil) with hP
  have hPsat : WSat (ccsLTS defn) Act.tau P (HML.dia (Act.name a) HML.tt) := by
    rw [wsat_dia_tt]
    refine ⟨CCS.nil, step_weakStep ?_⟩
    rw [hP, ccsLTS_step]; exact Step.suml (Step.act _ _)
  have hPpass : Passes defn bad P test := (h P).1 hPsat
  -- but `(P ∣ T) ∖ L —τ→ (0 ∣ T) ∖ L`, so the reject of `0` lifts to `P`
  have hτ : Step defn (interact bad P test) Act.tau (interact bad CCS.nil test) := by
    refine Step.res (tau_not_restrictNonBad bad) ?_ (Step.com1 ?_)
    · rw [Act.co_tau]; exact tau_not_restrictNonBad bad
    · rw [hP]; exact Step.sumr (Step.act _ _)
  have hne : (Act.coname bad : Act Name) ≠ Act.tau := by simp
  exact hPpass X (weakStep_tau_prefix hne hτ hX)

/-! ## `[a]ff ∨ [b]ff` is not testable -/

/-- `Z` can weakly reach a state that performs the reject action `bad̄`. -/
def CanRej (defn : K → CCS Name K) (bad : Name) (Z : CCS Name K) : Prop :=
  ∃ Y W, tauStar (ccsLTS defn) Act.tau Z Y ∧ Step defn Y (Act.coname bad) W

/-- Failing a test (not passing) is exactly being able to reject. -/
theorem not_passes_iff_canRej (defn : K → CCS Name K) (bad : Name) (s test : CCS Name K) :
    ¬ Passes defn bad s test ↔ CanRej defn bad (interact bad s test) := by
  rw [Passes]
  push Not
  constructor
  · rintro ⟨X, hX⟩
    rcases hX with ⟨heq, _⟩ | ⟨_, Y, W, h1, hstep, _⟩
    · exact absurd heq (by simp)
    · exact ⟨Y, W, h1, hstep⟩
  · rintro ⟨Y, W, h1, hstep⟩
    exact ⟨W, Or.inr ⟨by simp, Y, W, h1, hstep, tauStar_refl _ _ _⟩⟩

/-- Prefix a `τ`-step to a reject capability. -/
theorem CanRej.tau_prefix {defn : K → CCS Name K} {bad : Name} {Z Z' : CCS Name K}
    (hstep : Step defn Z Act.tau Z') (h : CanRej defn bad Z') : CanRej defn bad Z := by
  obtain ⟨Y, W, h1, h2⟩ := h
  exact ⟨Y, W, tauStar_trans (tauStar_single hstep) h1, h2⟩

/-- `a.0 + b.0` steps only on `a` or `b`, each to `0`. -/
theorem step_twoSum_iff {a b : Name} {μ : Act Name} {R : CCS Name K} {defn : K → CCS Name K} :
    Step defn (CCS.choice (CCS.pre (Act.name a) CCS.nil) (CCS.pre (Act.name b) CCS.nil)) μ R ↔
      (μ = Act.name a ∧ R = CCS.nil) ∨ (μ = Act.name b ∧ R = CCS.nil) := by
  rw [step_choice_iff, step_pre_iff, step_pre_iff]

/-- A `bad̄`-step of `(a.0+b.0 ∣ T) ∖ L` comes from the test `T` (the left summand
cannot perform `bad̄`). -/
theorem cobad_step_inv {a b bad : Name} {T Z : CCS Name K} {defn : K → CCS Name K}
    (h : Step defn (interact bad
        (CCS.choice (CCS.pre (Act.name a) CCS.nil) (CCS.pre (Act.name b) CCS.nil)) T)
      (Act.coname bad) Z) :
    ∃ T', Step defn T (Act.coname bad) T' ∧ Z = interact bad
      (CCS.choice (CCS.pre (Act.name a) CCS.nil) (CCS.pre (Act.name b) CCS.nil)) T' := by
  rw [interact, step_restrict_iff] at h
  obtain ⟨Y, _, _, hpar, rfl⟩ := h
  rw [step_par_iff] at hpar
  rcases hpar with ⟨P', hP, rfl⟩ | ⟨T', hT, rfl⟩ | ⟨ℓ, P', T', heq, _, _, _, rfl⟩
  · rw [step_twoSum_iff] at hP; rcases hP with ⟨h, _⟩ | ⟨h, _⟩ <;> simp at h
  · exact ⟨T', hT, rfl⟩
  · exact absurd heq (by simp)

/-- A `τ`-step of `(a.0+b.0 ∣ T) ∖ L` is either a `τ`-move of `T` (summand
unchanged) or a synchronisation on `a` or `b` (the summand collapses to `0`). -/
theorem tau_step_inv {a b bad : Name} {T Z : CCS Name K} {defn : K → CCS Name K}
    (h : Step defn (interact bad
        (CCS.choice (CCS.pre (Act.name a) CCS.nil) (CCS.pre (Act.name b) CCS.nil)) T)
      Act.tau Z) :
    (∃ T', Step defn T Act.tau T' ∧ Z = interact bad
        (CCS.choice (CCS.pre (Act.name a) CCS.nil) (CCS.pre (Act.name b) CCS.nil)) T') ∨
    (∃ T', Step defn T (Act.coname a) T' ∧ Z = interact bad CCS.nil T') ∨
    (∃ T', Step defn T (Act.coname b) T' ∧ Z = interact bad CCS.nil T') := by
  rw [interact, step_restrict_iff] at h
  obtain ⟨Y, _, _, hpar, rfl⟩ := h
  rw [step_par_iff] at hpar
  rcases hpar with ⟨P', hP, rfl⟩ | ⟨T', hT, rfl⟩ | ⟨ℓ, P', T', _, _, hP, hT, rfl⟩
  · rw [step_twoSum_iff] at hP; rcases hP with ⟨h, _⟩ | ⟨h, _⟩ <;> simp at h
  · exact Or.inl ⟨T', hT, rfl⟩
  · rw [step_twoSum_iff] at hP
    rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨T', hT, rfl⟩)
    · exact Or.inr (Or.inr ⟨T', hT, rfl⟩)

/-- A `bad̄`-reject of the test gives a reject of `(a.0 ∣ T) ∖ L`. -/
theorem canRej_single_of_cobad {a bad : Name} {T T' : CCS Name K} {defn : K → CCS Name K}
    (h : Step defn T (Act.coname bad) T') :
    CanRej defn bad (interact bad (CCS.pre (Act.name a) CCS.nil) T) :=
  ⟨interact bad (CCS.pre (Act.name a) CCS.nil) T,
    interact bad (CCS.pre (Act.name a) CCS.nil) T', tauStar_refl _ _ _,
    Step.res (conameBad_not_restrictNonBad bad) (nameBad_not_restrictNonBad bad) (Step.com2 h)⟩

/-- A `τ`-move of the test lifts to `(s ∣ T) ∖ L` with `s` unchanged. -/
theorem interact_com2_tau {bad : Name} {s test test' : CCS Name K} {defn : K → CCS Name K}
    (h : Step defn test Act.tau test') :
    Step defn (interact bad s test) Act.tau (interact bad s test') :=
  Step.res (tau_not_restrictNonBad bad) (tau_not_restrictNonBad bad) (Step.com2 h)

/-- A synchronisation of `s` (on `a`) with the test (on `ā`) is a `τ`-move of
`(s ∣ T) ∖ L`. -/
theorem interact_sync {a bad : Name} {s s' test test' : CCS Name K} {defn : K → CCS Name K}
    (h1 : Step defn s (Act.name a) s') (h2 : Step defn test (Act.coname a) test') :
    Step defn (interact bad s test) Act.tau (interact bad s' test') :=
  Step.res (tau_not_restrictNonBad bad) (tau_not_restrictNonBad bad)
    (Step.com3 (by simp [Act.IsLabel]) h1 h2)

/-- **Key decomposition.** If `(a.0+b.0 ∣ T) ∖ L` can reject, then `(a.0 ∣ T) ∖ L`
or `(b.0 ∣ T) ∖ L` can reject: along the weak reject path the summand `a.0+b.0`
either never participates (the test rejects, replicated by both `a.0` and `b.0`)
or synchronises once on `a` (giving `a.0`'s reject) or on `b` (giving `b.0`'s
reject). Proved by head-induction on the `τ`-chain. -/
theorem reject_decomp {a b bad : Name} (defn : K → CCS Name K) (test : CCS Name K)
    (h : CanRej defn bad (interact bad
      (CCS.choice (CCS.pre (Act.name a) CCS.nil) (CCS.pre (Act.name b) CCS.nil)) test)) :
    CanRej defn bad (interact bad (CCS.pre (Act.name a) CCS.nil) test) ∨
    CanRej defn bad (interact bad (CCS.pre (Act.name b) CCS.nil) test) := by
  obtain ⟨Y, W, htau, hstep⟩ := h
  refine Relation.ReflTransGen.head_induction_on htau
    (motive := fun Z _ => ∀ t, Z = interact bad
        (CCS.choice (CCS.pre (Act.name a) CCS.nil) (CCS.pre (Act.name b) CCS.nil)) t →
      CanRej defn bad (interact bad (CCS.pre (Act.name a) CCS.nil) t) ∨
      CanRej defn bad (interact bad (CCS.pre (Act.name b) CCS.nil) t))
    ?refl ?head test rfl
  case refl =>
    intro t hY; subst hY
    obtain ⟨T', hT, _⟩ := cobad_step_inv hstep
    exact Or.inl (canRej_single_of_cobad hT)
  case head =>
    rintro Z c h' hc ih t rfl
    rw [ccsLTS_step] at h'
    rcases tau_step_inv h' with ⟨T', hT, rfl⟩ | ⟨T', hT, rfl⟩ | ⟨T', hT, rfl⟩
    · rcases ih T' rfl with hA | hB
      · exact Or.inl (hA.tau_prefix (interact_com2_tau hT))
      · exact Or.inr (hB.tau_prefix (interact_com2_tau hT))
    · exact Or.inl (CanRej.tau_prefix (interact_sync (Step.act _ _) hT) ⟨Y, W, hc, hstep⟩)
    · exact Or.inr (CanRej.tau_prefix (interact_sync (Step.act _ _) hT) ⟨Y, W, hc, hstep⟩)

/-- For distinct actions `a ≠ b`, the
formula `[a]ff ∨ [b]ff` is **not testable**. The witness `a.0 + b.0` fails it (it
can do both `a` and `b`) so it can reject; by `reject_decomp` either `a.0` or
`b.0` can then reject — yet `a.0 ⊨ [b]ff` and `b.0 ⊨ [a]ff`, so both satisfy the
formula and must pass. Contradiction. -/
theorem boxff_or_not_testable (a b bad : Name) (hab : a ≠ b)
    (defn : K → CCS Name K) (test : CCS Name K)
    (h : Tests defn bad test
      (HML.or (HML.box (Act.name a) HML.ff) (HML.box (Act.name b) HML.ff))) : False := by
  set F : HML (Act Name) :=
    HML.or (HML.box (Act.name a) HML.ff) (HML.box (Act.name b) HML.ff) with hF
  set P2 : CCS Name K :=
    CCS.choice (CCS.pre (Act.name a) CCS.nil) (CCS.pre (Act.name b) CCS.nil) with hP2
  have hP2F : ¬ WSat (ccsLTS defn) Act.tau P2 F := by
    rw [hF]
    simp only [wsat_or, wsat_box_ff, not_or, not_forall, not_not]
    refine ⟨⟨CCS.nil, step_weakStep ?_⟩, ⟨CCS.nil, step_weakStep ?_⟩⟩
    · rw [hP2, ccsLTS_step]; exact Step.suml (Step.act _ _)
    · rw [hP2, ccsLTS_step]; exact Step.sumr (Step.act _ _)
  have hCanRej : CanRej defn bad (interact bad P2 test) :=
    (not_passes_iff_canRej defn bad P2 test).mp (fun hpass => hP2F ((h P2).2 hpass))
  rcases reject_decomp defn test hCanRej with hA | hB
  · have hSaF : WSat (ccsLTS defn) Act.tau (CCS.pre (Act.name a) CCS.nil) F := by
      rw [hF, wsat_or]; right
      rw [wsat_box_ff]
      rintro p' (⟨heq, _⟩ | ⟨_, p1, p2, htau, hstep, _⟩)
      · simp at heq
      · obtain rfl := tauStar_eq_of_no_tau
          (fun q hq => by rw [ccsLTS_step, step_pre_iff] at hq; simp at hq) htau
        rw [ccsLTS_step, step_pre_iff] at hstep
        exact hab (Act.name.inj hstep.1).symm
    exact (not_passes_iff_canRej _ _ _ _).mpr hA ((h _).1 hSaF)
  · have hSbF : WSat (ccsLTS defn) Act.tau (CCS.pre (Act.name b) CCS.nil) F := by
      rw [hF, wsat_or]; left
      rw [wsat_box_ff]
      rintro p' (⟨heq, _⟩ | ⟨_, p1, p2, htau, hstep, _⟩)
      · simp at heq
      · obtain rfl := tauStar_eq_of_no_tau
          (fun q hq => by rw [ccsLTS_step, step_pre_iff] at hq; simp at hq) htau
        rw [ccsLTS_step, step_pre_iff] at hstep
        exact hab (Act.name.inj hstep.1)
    exact (not_passes_iff_canRej _ _ _ _).mpr hB ((h _).1 hSbF)

end LTS

end DeepWiki.ReactiveSystems
