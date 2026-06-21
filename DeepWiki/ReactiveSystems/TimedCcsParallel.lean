import DeepWiki.ReactiveSystems.Ccs
import DeepWiki.ReactiveSystems.TimedTransitionSystems

/-! # Timed CCS with parallel composition and maximal progress (§9.4)
Parallel composition is the construct that forces the *maximal-progress assumption*: a process that can
perform an internal `τ` (the only action fully under its control — e.g. a synchronisation) must do so
without letting time pass. The book states this both globally ("if `P —τ→` then `P —d↛` for `d > 0`")
and via two SOS rules, where the parallel delay rule carries a side condition `NoSync(P,Q,d)` (no
synchronisation becomes available by delaying less than `d`).

That `NoSync` side condition is a **negative premise quantifying over intermediate delays** — it cannot
be a strictly-positive `inductive`, and the `const` recursion blocks structural recursion. We use the
equivalent **stratified** reformulation: a *raw* delay relation `RawDelay` (an ordinary inductive — time
passes componentwise, parallel delays both sides unconditionally), then the real delay
`PDelay = RawDelay` **filtered** by maximal progress (no intermediate state reachable by delaying `< d`
is `τ`-urgent). This `def`-over-relations sidesteps both obstacles and is equivalent to the book's rule. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- Timed CCS with parallel composition (§9.4): CCS-with-delay extended with the parallel operator. -/
inductive PTCCS (Name K : Type*)
  /-- The inactive process `0`. -/
  | nil : PTCCS Name K
  /-- A process constant. -/
  | const : K → PTCCS Name K
  /-- Action prefix `α.P`. -/
  | pre : Act Name → PTCCS Name K → PTCCS Name K
  /-- Delay prefix `ε(d).P`. -/
  | eps : ℝ≥0 → PTCCS Name K → PTCCS Name K
  /-- Choice `P + Q`. -/
  | choice : PTCCS Name K → PTCCS Name K → PTCCS Name K
  /-- Parallel composition `P | Q`. -/
  | par : PTCCS Name K → PTCCS Name K → PTCCS Name K
  /-- Restriction `P \ L`. -/
  | restrict : PTCCS Name K → Set (Act Name) → PTCCS Name K
  /-- Relabelling `P[f]`. -/
  | relabel : PTCCS Name K → (Act Name → Act Name) → PTCCS Name K

variable {Name K : Type*}

/-- **Action SOS** for parallel timed CCS: the CCS action rules — including interleaving (`com1`/`com2`)
and synchronisation (`com3`) — plus zero-delay transparency `ε(0).P —α→ P'`. -/
inductive PAct (defn : K → PTCCS Name K) : PTCCS Name K → Act Name → PTCCS Name K → Prop
  /-- `α.P —α→ P`. -/
  | act (α : Act Name) (P : PTCCS Name K) : PAct defn (.pre α P) α P
  /-- `ε(0).P` behaves as `P` for actions. -/
  | eps0 {P α P'} : PAct defn P α P' → PAct defn (.eps 0 P) α P'
  /-- Left summand of a choice. -/
  | suml {P P' Q α} : PAct defn P α P' → PAct defn (.choice P Q) α P'
  /-- Right summand of a choice. -/
  | sumr {P Q Q' α} : PAct defn Q α Q' → PAct defn (.choice P Q) α Q'
  /-- COM1: the left component moves on its own. -/
  | com1 {P P' Q α} : PAct defn P α P' → PAct defn (.par P Q) α (.par P' Q)
  /-- COM2: the right component moves on its own. -/
  | com2 {P Q Q' α} : PAct defn Q α Q' → PAct defn (.par P Q) α (.par P Q')
  /-- COM3: complementary labels synchronise into a `τ`. -/
  | com3 {P P' Q Q' ℓ} : Act.IsLabel ℓ → PAct defn P ℓ P' → PAct defn Q ℓ.co Q' →
      PAct defn (.par P Q) Act.tau (.par P' Q')
  /-- Restriction (`α, ᾱ ∉ L`). -/
  | res {P P' α L} : α ∉ L → α.co ∉ L → PAct defn P α P' → PAct defn (.restrict P L) α (.restrict P' L)
  /-- Relabelling. -/
  | rel {P P' α f} : PAct defn P α P' → PAct defn (.relabel P f) (f α) (.relabel P' f)
  /-- A constant moves as its body. -/
  | con {Kc α P'} : PAct defn (defn Kc) α P' → PAct defn (.const Kc) α P'

/-- **Raw delay** (pre-maximal-progress): time passes componentwise, and parallel delays *both* sides
**unconditionally** (`par`); a zero delay is the identity (`refl0`). The maximal-progress side condition
is imposed separately in `PDelay`. An ordinary inductive — `const` recursion and parallel are handled by
its least-fixed-point, with no negative premise. -/
inductive RawDelay (defn : K → PTCCS Name K) : PTCCS Name K → ℝ≥0 → PTCCS Name K → Prop
  /-- A zero delay is the identity. -/
  | refl0 (P : PTCCS Name K) : RawDelay defn P 0 P
  /-- After waiting out the whole prefix, the body proceeds: `ε(d).P —d+d'→ P'` if `P —d'→ P'`. -/
  | epsConsume {d P d' P'} : RawDelay defn P d' P' → RawDelay defn (.eps d P) (d + d') P'
  /-- A delay-prefix counts down: `ε(d).P —d'→ ε(d−d').P` for `d' ≤ d`. -/
  | epsPartial {d d' P} (h : d' ≤ d) : RawDelay defn (.eps d P) d' (.eps (d - d') P)
  /-- A constant delays as its body. -/
  | con {Kc d P'} : RawDelay defn (defn Kc) d P' → RawDelay defn (.const Kc) d P'
  /-- An action-prefix idles patiently — for `α ≠ τ`. -/
  | prePatient {α P} (h : α ≠ Act.tau) (d : ℝ≥0) : RawDelay defn (.pre α P) d (.pre α P)
  /-- A choice delays componentwise. -/
  | choice {P P' Q Q' d} : RawDelay defn P d P' → RawDelay defn Q d Q' →
      RawDelay defn (.choice P Q) d (.choice P' Q')
  /-- A parallel composition delays componentwise (raw — the maximal-progress check is in `PDelay`). -/
  | par {P P' Q Q' d} : RawDelay defn P d P' → RawDelay defn Q d Q' →
      RawDelay defn (.par P Q) d (.par P' Q')
  /-- Delay through restriction. -/
  | res {P P' d L} : RawDelay defn P d P' → RawDelay defn (.restrict P L) d (.restrict P' L)
  /-- Delay through relabelling. -/
  | rel {P P' d f} : RawDelay defn P d P' → RawDelay defn (.relabel P f) d (.relabel P' f)

/-- A process `R` is **`τ`-urgent** when it can perform a `τ` action now. -/
def CanTau (defn : K → PTCCS Name K) (R : PTCCS Name K) : Prop := ∃ R', PAct defn R Act.tau R'

/-- **Maximal-progress delay** (§9.4): a raw delay `P —d→ Q` that additionally respects maximal
progress — no intermediate state reached by delaying `< d` is `τ`-urgent (no synchronisation becomes
available before `d`). The stratified reading of the book's `NoSync(P,Q,d)` side condition. -/
def PDelay (defn : K → PTCCS Name K) (P : PTCCS Name K) (d : ℝ≥0) (Q : PTCCS Name K) : Prop :=
  RawDelay defn P d Q ∧ ∀ d' R, d' < d → RawDelay defn P d' R → ¬ CanTau defn R

/-- **The maximal-progress assumption** (book p.170): if `P` can perform `τ` then `P` cannot delay by
any positive amount. -/
theorem pdelay_maximalProgress (defn : K → PTCCS Name K) {P : PTCCS Name K} {d : ℝ≥0} (hd : 0 < d)
    {Q : PTCCS Name K} (htau : CanTau defn P) : ¬ PDelay defn P d Q := by
  rintro ⟨_, hfilter⟩
  exact hfilter 0 P hd (RawDelay.refl0 P) htau

/-- **Immediate synchronisation blocks delay**: if the parallel components offer complementary labels
now, the composition is `τ`-urgent and cannot delay by any positive amount. -/
theorem par_sync_no_delay (defn : K → PTCCS Name K) {P P' Q Q' : PTCCS Name K} {ℓ : Act Name}
    (hℓ : Act.IsLabel ℓ) (hP : PAct defn P ℓ P') (hQ : PAct defn Q ℓ.co Q')
    {d : ℝ≥0} (hd : 0 < d) {R : PTCCS Name K} : ¬ PDelay defn (.par P Q) d R :=
  pdelay_maximalProgress defn hd ⟨_, PAct.com3 hℓ hP hQ⟩

/-! ## Exercise 9.5 (the light switch and a user), over `Name = Unit` -/

/-- The label `press`. -/
abbrev press : Act Unit := Act.name ()
/-- The co-label `press̄`. -/
abbrev presso : Act Unit := Act.coname ()
/-- The restriction set `\press` (both `press` and `press̄`). -/
abbrev noPress : Set (Act Unit) := {Act.name (), Act.coname ()}
/-- The empty constant environment (the recursive tails are guarded and never unfolded here). -/
def ed : Empty → PTCCS Unit Empty := fun e => e.elim

/-- `((press̄.P) | (ε(t).τ.press.Q + press.R)) \ press` can synchronise immediately, so by maximal
progress it cannot delay by any positive amount (Exercise 9.5, second expression). -/
theorem parRestrict_immediateSync_noDelay (P Q R : PTCCS Unit Empty) (t : ℝ≥0) {d : ℝ≥0} (hd : 0 < d)
    (S : PTCCS Unit Empty) :
    ¬ PDelay ed
      (.restrict (.par (.pre presso P)
        (.choice (.eps t (.pre Act.tau (.pre press Q))) (.pre press R))) noPress) d S := by
  apply pdelay_maximalProgress ed hd
  exact ⟨_, PAct.res (by simp [noPress]) (by simp [noPress])
    (PAct.com3 (ℓ := presso) (by simp [Act.IsLabel]) (PAct.act _ _) (PAct.sumr (PAct.act _ _)))⟩

/-- `((ε(t₁).press̄.P) | (ε(t₃).τ.press.Q + press.R)) \ press` cannot delay by `t₂` when `t₁ < t₂` and
`t₁ ≤ t₃`: at the intermediate time `t₁` the guard `ε(t₁)` expires and a `press̄`/`press`
synchronisation becomes available (Exercise 9.5, first expression, general form). -/
theorem parRestrict_guardExpiry_noDelay (P Q R : PTCCS Unit Empty) {t₁ t₂ t₃ : ℝ≥0}
    (h12 : t₁ < t₂) (h13 : t₁ ≤ t₃) (S : PTCCS Unit Empty) :
    ¬ PDelay ed
      (.restrict (.par (.eps t₁ (.pre presso P))
        (.choice (.eps t₃ (.pre Act.tau (.pre press Q))) (.pre press R))) noPress) t₂ S := by
  rintro ⟨_, hfilter⟩
  refine hfilter t₁ _ h12
    (RawDelay.res (RawDelay.par (RawDelay.epsPartial (le_refl t₁))
      (RawDelay.choice (RawDelay.epsPartial h13) (RawDelay.prePatient (by simp) t₁)))) ?_
  rw [show t₁ - t₁ = 0 from tsub_self t₁]
  exact ⟨_, PAct.res (by simp [noPress]) (by simp [noPress])
    (PAct.com3 (ℓ := presso) (by simp [Act.IsLabel]) (PAct.eps0 (PAct.act _ _)) (PAct.sumr (PAct.act _ _)))⟩

/-- `ε(t).τ.0 + a.0` **cannot** delay by more than `t` — past the guard the body `τ.0` is urgent, so no
`d > t` delay exists. (With `parRestrict`'s patience giving every `d ≤ t`, the answer to Exercise 9.5's
closing question "how long can it delay?" is: exactly up to `t`.) -/
theorem epsChoice_noDelay_gt (t : ℝ≥0) (a : Unit) {d : ℝ≥0} (hgt : t < d) (S : PTCCS Unit Empty) :
    ¬ PDelay ed (.choice (.eps t (.pre Act.tau .nil)) (.pre (Act.name a) .nil)) d S := by
  rintro ⟨hraw, _⟩
  cases hraw with
  | refl0 => simp at hgt
  | choice hA _ =>
    cases hA with
    | refl0 => simp at hgt
    | epsPartial hle => exact absurd hle (not_le.mpr hgt)
    | epsConsume hB =>
      cases hB with
      | refl0 => simp at hgt
      | prePatient hne _ => exact hne rfl

end DeepWiki.ReactiveSystems
