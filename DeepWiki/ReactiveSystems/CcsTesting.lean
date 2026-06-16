import DeepWiki.ReactiveSystems.Ccs
import DeepWiki.ReactiveSystems.HennessyMilner
import DeepWiki.ReactiveSystems.BisimulationWeak

/-! # Testing and testable formulae (§7.3)
A *test* is a (regular CCS) process over the actions plus a distinguished reject
channel `bad` (Definition 7.3). A process `s` *passes* a test `T` when the
composite `(s ∣ T) ∖ L` — hiding every observable channel except `bad` — cannot
perform a weak `bad`-transition; `T` *tests for* a formula `F` (and `F` is
*testable*) when passing `T` coincides with satisfying `F`, for every process
(Definition 7.4). Proposition 7.3 gives two *negative* results: the very simple
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

/-- **Definition 7.4.** The composite `(s ∣ T) ∖ L` of a process `s` with a test
`T`, hiding every observable channel except the reject channel `bad`. -/
def interact (bad : Name) (s test : CCS Name K) : CCS Name K :=
  CCS.restrict (CCS.par s test) (restrictNonBad bad)

/-- **Definition 7.4.** `s` *passes* test `T`: the composite `(s ∣ T) ∖ L` cannot
perform a weak `bad̄`-transition (the test never reaches its reject signal). -/
def Passes (defn : K → CCS Name K) (bad : Name) (s test : CCS Name K) : Prop :=
  ∀ X, ¬ ((ccsLTS defn) ⊢ interact bad s test =[Act.coname bad]⇒[Act.tau] X)

/-- **Definition 7.4.** Test `T` *tests for* `F` (so `F` is *testable*): a process
satisfies `F` iff it passes `T`. -/
def Tests (defn : K → CCS Name K) (bad : Name) (test : CCS Name K) (F : HML (Act Name)) : Prop :=
  ∀ s, (s ⊨[ccsLTS defn] F) ↔ Passes defn bad s test

/-- A weak `α`-transition (`α ≠ τ`) can be prefixed by one concrete `τ`-step. -/
theorem weakStep_tau_prefix {defn : K → CCS Name K} {X Y Z : CCS Name K} {α : Act Name}
    (hα : α ≠ Act.tau) (hxy : Step defn X Act.tau Y)
    (h : (ccsLTS defn) ⊢ Y =[α]⇒[Act.tau] Z) : (ccsLTS defn) ⊢ X =[α]⇒[Act.tau] Z := by
  rcases h with ⟨heq, _⟩ | ⟨_, p1, p2, hY1, hstep, h2⟩
  · exact absurd heq hα
  · exact Or.inr ⟨hα, p1, p2, tauStar_trans (tauStar_single hxy) hY1, hstep, h2⟩

/-! ## Proposition 7.3: two negative results -/

/-- **Proposition 7.3(1)** (§7.3, p.157). For every action `a` (in particular
every observable `a ≠ bad`), the formula `⟨a⟩tt` is **not testable**: no test `T`
over any process system tests for it. The witnesses are `0` (fails `⟨a⟩tt`, so the
composite can reject) and `a.0 + τ.0` (satisfies `⟨a⟩tt`, yet `τ`-reduces to
`0 ∣ T`, so it can reject too) — a process cannot be required to *pass* `T` while a
`τ`-successor *fails*. -/
theorem dia_tt_not_testable (a bad : Name)
    (defn : K → CCS Name K) (test : CCS Name K)
    (h : Tests defn bad test (HML.dia (Act.name a) HML.tt)) : False := by
  -- `0` does not satisfy `⟨a⟩tt`, so `0` fails the test: a weak reject exists.
  have hnil : ¬ ((CCS.nil : CCS Name K) ⊨[ccsLTS defn] HML.dia (Act.name a) HML.tt) := by
    rw [sat_dia_tt]; rintro ⟨p', hp'⟩; rw [ccsLTS_step] at hp'; cases hp'
  have hnilFail : ¬ Passes defn bad CCS.nil test := fun hp => hnil ((h CCS.nil).2 hp)
  -- extract the witnessing weak reject of `(0 ∣ T) ∖ L`
  simp only [Passes, not_forall, not_not] at hnilFail
  obtain ⟨X, hX⟩ := hnilFail
  -- `a.0 + τ.0` satisfies `⟨a⟩tt`, so it must pass the test
  set P : CCS Name K := CCS.choice (CCS.pre (Act.name a) CCS.nil) (CCS.pre Act.tau CCS.nil) with hP
  have hPsat : P ⊨[ccsLTS defn] HML.dia (Act.name a) HML.tt := by
    rw [sat_dia_tt]; exact ⟨CCS.nil, by rw [ccsLTS_step, hP]; exact Step.suml (Step.act _ _)⟩
  have hPpass : Passes defn bad P test := (h P).1 hPsat
  -- but `(P ∣ T) ∖ L —τ→ (0 ∣ T) ∖ L`, so the reject of `0` lifts to `P`
  have hτ : Step defn (interact bad P test) Act.tau (interact bad CCS.nil test) := by
    refine Step.res (tau_not_restrictNonBad bad) ?_ (Step.com1 ?_)
    · rw [Act.co_tau]; exact tau_not_restrictNonBad bad
    · rw [hP]; exact Step.sumr (Step.act _ _)
  have hne : (Act.coname bad : Act Name) ≠ Act.tau := by simp
  exact hPpass X (weakStep_tau_prefix hne hτ hX)

end LTS

end DeepWiki.ReactiveSystems
