import DeepWiki.ReactiveSystems.TimedAutomataFinite
import DeepWiki.ReactiveSystems.TimedRegionCode
import DeepWiki.ReactiveSystems.SymbolicModelChecking
import DeepWiki.ReactiveSystems.TimedHmlIntervalDelay

/-! # Executable timed model checking (delay-free fragment)
The executable decision procedure `SymSatCode` mirrors symbolic satisfaction `SymSat`
on a region *code* (`RegionCode`) rather than a real valuation, so it is `#eval`-able.
This file establishes the supporting pieces: the delay-free fragment of `Mt`
(`Mt.DelayFree`), the boundedness transport along clock renamings
(`boundedBy_mapClock`), and the all-zero initial region code `RegionCode.initial` with
its agreement to `regionFingerprint` of the zero valuation — the computable starting
point of a model-checking run. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-! ## The delay-free fragment -/

variable {Act D : Type*}

/-- The **delay-free fragment** of `Mt`: no `∃∃`/`∀∀` delay quantifiers (whose decision
needs the region time-successor graph). Everything else is allowed. -/
def Mt.DelayFree : Mt Act D → Prop
  | .tt => True
  | .ff => True
  | .and F G => F.DelayFree ∧ G.DelayFree
  | .or F G => F.DelayFree ∧ G.DelayFree
  | .dia _ F => F.DelayFree
  | .box _ F => F.DelayFree
  | .existsDelay _ => False
  | .forallDelay _ => False
  | .reset _ F => F.DelayFree
  | .guard _ => True

/-! ## Boundedness transports along a clock renaming -/

/-- A renamed constraint is bounded by `cmax'` exactly when the original is bounded by
the pulled-back clamp `cmax' ∘ f`. -/
theorem ClockConstraint.boundedBy_mapClock {C C' : Type*} (f : C → C') (cmax' : C' → ℕ) :
    ∀ {g : ClockConstraint C}, (g.mapClock f).BoundedBy cmax' ↔ g.BoundedBy (cmax' ∘ f) := by
  intro g
  induction g with
  | true_ => exact Iff.rfl
  | atom x c n => exact Iff.rfl
  | and g₁ g₂ ih₁ ih₂ => exact and_congr ih₁ ih₂

/-! ## The all-zero initial region code -/

variable {C : Type*}

/-- The region code of the all-zero valuation: every clamped floor `0`, every clock
frac-zero, every frac-order bit set. A computable constant. -/
def RegionCode.initial (cmax : C → ℕ) : RegionCode cmax :=
  (fun _ => ⟨0, by omega⟩, fun _ => true, fun _ _ => true)

open Classical in
/-- **Initial-code agreement.** The fingerprint of the all-zero valuation is the
computable `RegionCode.initial` — so a model-checking run starts from a constant code
without ever evaluating the `noncomputable` `regionFingerprint`. -/
theorem initial_fingerprint {cmax : C → ℕ} :
    regionFingerprint cmax (fun _ => (0 : ℝ≥0)) = RegionCode.initial cmax := by
  rw [Prod.ext_iff, Prod.ext_iff]
  refine ⟨funext fun x => ?_, funext fun x => ?_, funext fun x => funext fun y => ?_⟩
  · apply Fin.ext
    rw [regionFingerprint_floor]
    show regionFloor cmax (fun _ => (0 : ℝ≥0)) x = 0
    unfold regionFloor; simp
  · rw [regionFingerprint_fracZero]
    exact decide_eq_true_iff.mpr ⟨zero_le', fracPart_zero⟩
  · rw [regionFingerprint_fracOrder]
    exact decide_eq_true_iff.mpr ⟨zero_le', zero_le', le_refl _⟩

/-! ## The executable decision procedure -/

variable {Loc : Type*} [DecidableEq Loc] [DecidableEq Act] [DecidableEq C] [DecidableEq D]

/-- The reset predicate of an edge: reset the automaton clocks listed in `rl`
(the `C`-component), leaving the formula clocks (`D`-component) untouched. -/
def edgeResetP (rl : List C) : C ⊕ D → Bool :=
  Sum.elim (fun c => decide (c ∈ rl)) (fun _ => false)

/-- The reset predicate of a formula-clock reset `x in F`: reset only `Sum.inr x`. -/
def formulaResetP (x : D) : C ⊕ D → Bool := fun z => decide (z = Sum.inr x)

/-- **Executable symbolic satisfaction.** The Bool decision procedure mirroring `SymSat`
on a region *code* `γ` instead of a real valuation: guards/modalities decide via the
region-code leaf check and edge-list iteration; clock resets transform the code
(`RegionCode.reset`). Delay quantifiers are out of this (delay-free) fragment. -/
def SymSatCode (A : FinAutomaton Loc Act C) (cmax : C ⊕ D → ℕ) :
    Loc → RegionCode cmax → Mt Act D → Bool
  | _, _, .tt => true
  | _, _, .ff => false
  | ℓ, γ, .and F G => SymSatCode A cmax ℓ γ F && SymSatCode A cmax ℓ γ G
  | ℓ, γ, .or F G => SymSatCode A cmax ℓ γ F || SymSatCode A cmax ℓ γ G
  | _, γ, .guard g => RegionCode.satisfies γ (g.mapClock Sum.inr)
  | ℓ, γ, .reset x F =>
      SymSatCode A cmax ℓ (RegionCode.reset (formulaResetP x) γ) F
  | ℓ, γ, .dia a F => A.edges.any fun e =>
      decide (e.1 = ℓ) && decide (e.2.2.1 = a) &&
        RegionCode.satisfies γ (e.2.1.mapClock Sum.inl) &&
        RegionCode.satisfies (RegionCode.reset (edgeResetP e.2.2.2.1) γ)
          ((A.inv e.2.2.2.2).mapClock Sum.inl) &&
        SymSatCode A cmax e.2.2.2.2 (RegionCode.reset (edgeResetP e.2.2.2.1) γ) F
  | ℓ, γ, .box a F => A.edges.all fun e =>
      !(decide (e.1 = ℓ) && decide (e.2.2.1 = a) &&
        RegionCode.satisfies γ (e.2.1.mapClock Sum.inl) &&
        RegionCode.satisfies (RegionCode.reset (edgeResetP e.2.2.2.1) γ)
          ((A.inv e.2.2.2.2).mapClock Sum.inl)) ||
        SymSatCode A cmax e.2.2.2.2 (RegionCode.reset (edgeResetP e.2.2.2.1) γ) F
  | _, _, .existsDelay _ => false
  | _, _, .forallDelay _ => false

/-! ## Agreement bridges -/

omit [DecidableEq Loc] [DecidableEq Act] [DecidableEq C] [DecidableEq D] in
/-- The leaf check on a `C`-clock guard (lifted via `Sum.inl`) decides the real guard on
the `C`-component, for a guard bounded by the automaton clamp. -/
theorem regionCode_satisfies_inl_iff {cmax : C ⊕ D → ℕ} (w : Valuation (C ⊕ D))
    {g : ClockConstraint C} (hg : g.BoundedBy (cmax ∘ Sum.inl)) :
    RegionCode.satisfies (regionFingerprint cmax w) (g.mapClock Sum.inl) = true
      ↔ satisfies (fun c => w (Sum.inl c)) g := by
  rw [regionCode_satisfies_iff w ((ClockConstraint.boundedBy_mapClock Sum.inl cmax).mpr hg),
    satisfies_mapClock]

omit [DecidableEq Loc] [DecidableEq Act] [DecidableEq C] [DecidableEq D] in
/-- The leaf check on a `D`-clock guard (lifted via `Sum.inr`) decides the real guard on
the `D`-component, for a guard bounded by the formula clamp. -/
theorem regionCode_satisfies_inr_iff {cmax : C ⊕ D → ℕ} (w : Valuation (C ⊕ D))
    {g : ClockConstraint D} (hg : g.BoundedBy (cmax ∘ Sum.inr)) :
    RegionCode.satisfies (regionFingerprint cmax w) (g.mapClock Sum.inr) = true
      ↔ satisfies (fun d => w (Sum.inr d)) g := by
  rw [regionCode_satisfies_iff w ((ClockConstraint.boundedBy_mapClock Sum.inr cmax).mpr hg),
    satisfies_mapClock]

omit [DecidableEq Loc] [DecidableEq Act] [DecidableEq D] in
/-- The edge-reset predicate cuts out exactly the automaton clocks `Sum.inl '' {c | c ∈ rl}`. -/
theorem edgeResetP_set (rl : List C) :
    {z : C ⊕ D | edgeResetP rl z = true} = Sum.inl '' {c | c ∈ rl} := by
  ext z
  cases z with
  | inl c => simp [edgeResetP, Set.mem_image]
  | inr d => simp [edgeResetP, Set.mem_image]

/-- The formula-reset predicate cuts out exactly `{Sum.inr x}`. -/
theorem formulaResetP_set (x : D) :
    {z : C ⊕ D | formulaResetP x z = true} = {Sum.inr x} := by
  ext z; simp [formulaResetP, Set.mem_singleton_iff]

/-! ## Agreement of the executable procedure with the real semantics -/

/-- **Executable model-checking agreement.** On the delay-free fragment, the Bool
decision `SymSatCode` on the region code of `w` agrees with symbolic satisfaction
`SymSat` on `w` — for a well-formed automaton (clamp `cmax ∘ Sum.inl`) and a formula
bounded by `cmax ∘ Sum.inr`. Proved by induction on `F`: guards/resets via the leaf and
reset agreements, the action modalities by matching the finite edge list against the
`SymSat` existential/universal over edges. -/
theorem symSatCode_iff (A : FinAutomaton Loc Act C) {cmax : C ⊕ D → ℕ}
    (wf : A.toTimedAutomaton.WellFormed (cmax ∘ Sum.inl)) :
    ∀ {F : Mt Act D}, F.DelayFree → F.BoundedByD (cmax ∘ Sum.inr) →
      ∀ {ℓ : Loc} {w : Valuation (C ⊕ D)},
        SymSatCode A cmax ℓ (regionFingerprint cmax w) F = true
          ↔ SymSat A.toTimedAutomaton ℓ w F := by
  intro F
  induction F with
  | tt => intro _ _ _ _; simp [SymSatCode, SymSat]
  | ff => intro _ _ _ _; simp [SymSatCode, SymSat]
  | and F G ihF ihG =>
      intro hdf hbd _ _
      simp only [SymSatCode, SymSat, Bool.and_eq_true]
      exact and_congr (ihF hdf.1 hbd.1) (ihG hdf.2 hbd.2)
  | or F G ihF ihG =>
      intro hdf hbd _ _
      simp only [SymSatCode, SymSat, Bool.or_eq_true]
      exact or_congr (ihF hdf.1 hbd.1) (ihG hdf.2 hbd.2)
  | guard g => intro _ hbd _ w; exact regionCode_satisfies_inr_iff w hbd
  | reset x F ihF =>
      intro hdf hbd ℓ w
      show SymSatCode A cmax ℓ (RegionCode.reset (formulaResetP x) (regionFingerprint cmax w)) F
        = true ↔ _
      rw [reset_fingerprint, formulaResetP_set]
      exact ihF hdf hbd
  | dia a F ihF =>
      intro hdf hbd ℓ w
      constructor
      · intro h
        simp only [SymSatCode, List.any_eq_true] at h
        obtain ⟨e, hmem, hbody⟩ := h
        obtain ⟨ℓ₀, g, a₀, rl, ℓ'⟩ := e
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hbody
        obtain ⟨⟨⟨⟨hℓ, ha⟩, hgc⟩, hic⟩, hrec⟩ := hbody
        subst hℓ; subst ha
        have hedge : A.toTimedAutomaton.edge ℓ₀ g a₀ {x | x ∈ rl} ℓ' := ⟨rl, hmem, rfl⟩
        have hres : RegionCode.reset (edgeResetP rl) (regionFingerprint cmax w)
            = regionFingerprint cmax (Valuation.reset (Sum.inl '' {x | x ∈ rl}) w) := by
          rw [reset_fingerprint, edgeResetP_set]
        rw [hres] at hic hrec
        exact ⟨ℓ', g, {x | x ∈ rl}, hedge,
          (regionCode_satisfies_inl_iff w (wf.1 _ _ _ _ _ hedge)).mp hgc,
          (regionCode_satisfies_inl_iff _ (wf.2 ℓ')).mp hic, (ihF hdf hbd).mp hrec⟩
      · rintro ⟨ℓ', g, r, hedge, hgsat, hinvsat, hrec⟩
        rw [FinAutomaton.edge_iff] at hedge
        obtain ⟨rl, hmem, rfl⟩ := hedge
        have hedge : A.toTimedAutomaton.edge ℓ g a {x | x ∈ rl} ℓ' := ⟨rl, hmem, rfl⟩
        have hres : RegionCode.reset (edgeResetP rl) (regionFingerprint cmax w)
            = regionFingerprint cmax (Valuation.reset (Sum.inl '' {x | x ∈ rl}) w) := by
          rw [reset_fingerprint, edgeResetP_set]
        simp only [SymSatCode, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨(ℓ, g, a, rl, ℓ'), hmem, ⟨⟨⟨⟨rfl, rfl⟩,
          (regionCode_satisfies_inl_iff w (wf.1 _ _ _ _ _ hedge)).mpr hgsat⟩, ?_⟩, ?_⟩⟩
        · rw [hres]; exact (regionCode_satisfies_inl_iff _ (wf.2 ℓ')).mpr hinvsat
        · rw [hres]; exact (ihF hdf hbd).mpr hrec
  | box a F ihF =>
      intro hdf hbd ℓ w
      constructor
      · intro h ℓ' g r hedge hgsat hinvsat
        rw [FinAutomaton.edge_iff] at hedge
        obtain ⟨rl, hmem, rfl⟩ := hedge
        have hedge : A.toTimedAutomaton.edge ℓ g a {x | x ∈ rl} ℓ' := ⟨rl, hmem, rfl⟩
        have hres : RegionCode.reset (edgeResetP rl) (regionFingerprint cmax w)
            = regionFingerprint cmax (Valuation.reset (Sum.inl '' {x | x ∈ rl}) w) := by
          rw [reset_fingerprint, edgeResetP_set]
        have hgc : RegionCode.satisfies (regionFingerprint cmax w) (g.mapClock Sum.inl) = true :=
          (regionCode_satisfies_inl_iff w (wf.1 _ _ _ _ _ hedge)).mpr hgsat
        have hic : RegionCode.satisfies (RegionCode.reset (edgeResetP rl) (regionFingerprint cmax w))
            ((A.inv ℓ').mapClock Sum.inl) = true := by
          rw [hres]; exact (regionCode_satisfies_inl_iff _ (wf.2 ℓ')).mpr hinvsat
        have hb := (List.all_eq_true.mp (by simpa only [SymSatCode] using h)) (ℓ, g, a, rl, ℓ') hmem
        simp only [hgc, hic, Bool.and_true, Bool.not_true, Bool.false_or, decide_true] at hb
        rw [hres] at hb
        exact (ihF hdf hbd).mp hb
      · intro h
        simp only [SymSatCode, List.all_eq_true]
        rintro ⟨ℓ₀, g, a₀, rl, ℓ'⟩ hmem
        rw [Bool.or_eq_true, Bool.not_eq_true']
        by_cases hm : (decide (ℓ₀ = ℓ) && decide (a₀ = a) &&
            RegionCode.satisfies (regionFingerprint cmax w) (g.mapClock Sum.inl) &&
            RegionCode.satisfies (RegionCode.reset (edgeResetP rl) (regionFingerprint cmax w))
              ((A.inv ℓ').mapClock Sum.inl)) = true
        · refine Or.inr ?_
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
          obtain ⟨⟨⟨hℓ, ha⟩, hgc⟩, hic⟩ := hm
          subst hℓ; subst ha
          have hedge : A.toTimedAutomaton.edge ℓ₀ g a₀ {x | x ∈ rl} ℓ' := ⟨rl, hmem, rfl⟩
          have hres : RegionCode.reset (edgeResetP rl) (regionFingerprint cmax w)
              = regionFingerprint cmax (Valuation.reset (Sum.inl '' {x | x ∈ rl}) w) := by
            rw [reset_fingerprint, edgeResetP_set]
          rw [hres] at hic ⊢
          exact (ihF hdf hbd).mpr (h ℓ' g {x | x ∈ rl} hedge
            ((regionCode_satisfies_inl_iff w (wf.1 _ _ _ _ _ hedge)).mp hgc)
            ((regionCode_satisfies_inl_iff _ (wf.2 ℓ')).mp hic))
        · exact Or.inl (by simpa using hm)
  | existsDelay F _ => intro hdf; simp [Mt.DelayFree] at hdf
  | forallDelay F _ => intro hdf; simp [Mt.DelayFree] at hdf

/-! ## The executable model-checking decision

For a finite automaton and a delay-free formula, satisfaction `A ⊨ F` reduces to the
Bool computation `SymSatCode` on the all-zero initial region code — an actual executable
decision procedure (Theorem 12.2, delay-free fragment). -/

/-- **Executable model checking.** `A.toTimedAutomaton ⊨ F` (delay-free `F`) iff the Bool
decision `SymSatCode` evaluates to `true` on the initial region code, using the combined
clamp `Sum.elim A.cmax F.formulaCmax`. The right-hand side is `#eval`-able. -/
theorem satisfiesMt_iff_decide [Fintype Loc] (A : FinAutomaton Loc Act C) (F : Mt Act D)
    (hF : F.DelayFree) :
    A.toTimedAutomaton.SatisfiesMt F
      ↔ SymSatCode A (Sum.elim A.cmax F.formulaCmax) A.initial (RegionCode.initial _) F = true := by
  rw [TimedAutomaton.SatisfiesMt, satisfiesMtState_iff_symSat, combineVal_zero,
    ← initial_fingerprint (cmax := Sum.elim A.cmax F.formulaCmax)]
  exact (symSatCode_iff A (cmax := Sum.elim A.cmax F.formulaCmax) A.wellFormed hF
    (Mt.boundedByD_formulaCmax F)).symm

/-- **Decidability of timed model checking (delay-free fragment).** A constructive
`Decidable` instance for `A ⊨ F`, by reduction to the `SymSatCode` Bool computation. -/
def decSatisfiesMt [Fintype Loc] (A : FinAutomaton Loc Act C) (F : Mt Act D) (hF : F.DelayFree) :
    Decidable (A.toTimedAutomaton.SatisfiesMt F) :=
  decidable_of_iff _ (satisfiesMt_iff_decide A F hF).symm

/-! ## Worked example -/

/-- A one-location, one-clock automaton with a self-loop `a` guarded `x ≤ 1`, resetting
`x`, under invariant `x ≤ 2`. -/
def demoAuto : FinAutomaton (Fin 1) Unit (Fin 1) where
  initial := 0
  edges := [(0, ClockConstraint.atom 0 Cmp.le 1, (), [0], 0)]
  inv := fun _ => ClockConstraint.atom 0 Cmp.le 2

/-- `⟨a⟩tt`: an `a`-action is enabled at the initial state (`x = 0` satisfies the guard
`x ≤ 1`) — the decision procedure evaluates to `true`. -/
example : demoAuto.toTimedAutomaton.SatisfiesMt (Mt.dia () Mt.tt : Mt Unit (Fin 1)) := by
  rw [satisfiesMt_iff_decide demoAuto _ (by simp [Mt.DelayFree])]; decide

/-- `[a]ff`: it is *not* the case that every `a`-successor satisfies `ff`, since `a` is
enabled — the decision procedure evaluates to `false`, refuting satisfaction. -/
example : ¬ demoAuto.toTimedAutomaton.SatisfiesMt (Mt.box () Mt.ff : Mt Unit (Fin 1)) := by
  rw [satisfiesMt_iff_decide demoAuto _ (by simp [Mt.DelayFree])]; decide

end DeepWiki.ReactiveSystems
