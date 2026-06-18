import DeepWiki.ReactiveSystems.SymbolicModelCheckingExecutable

/-! # Executable timed model checking — full logic, modulo a region successor
The delay-free decision `SymSatCode` extends to the **full** `Mt` logic (with the delay
quantifiers `∃∃`/`∀∀`) once it is given a *region time-successor enumerator*
`succ : RegionCode → List RegionCode` listing the region codes reachable by a delay. The
extended procedure `SymSatCodeFull` decides the delay quantifiers by iterating `succ`, and
`symSatCodeFull_iff` proves it faithful to `SymSat` for **every** formula — *conditional on*
`succ` being sound (`SuccSound`: every listed code is realized by some delay) and complete
(`SuccComplete`: every delay's code is listed). This isolates the one remaining piece for an
unconditional executable full model checker: a constructive, correct region successor (the
Alur–Dill construction; the library currently provides only its *classical existence*,
`timeSuccessor_of_fintype`). -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

variable {Loc Act C D : Type*} [DecidableEq Loc] [DecidableEq Act] [DecidableEq C] [DecidableEq D]

/-- `succ` is **sound**: every code it lists for `⟦w⟧` is the code of `w` after some delay. -/
def SuccSound {cmax : C ⊕ D → ℕ} (succ : RegionCode cmax → List (RegionCode cmax)) : Prop :=
  ∀ (w : Valuation (C ⊕ D)) (γ' : RegionCode cmax),
    γ' ∈ succ (regionFingerprint cmax w) → ∃ t : ℝ≥0, regionFingerprint cmax (w.add t) = γ'

/-- `succ` is **complete**: every code reachable by a delay from `w` is listed for `⟦w⟧`. -/
def SuccComplete {cmax : C ⊕ D → ℕ} (succ : RegionCode cmax → List (RegionCode cmax)) : Prop :=
  ∀ (w : Valuation (C ⊕ D)) (t : ℝ≥0),
    regionFingerprint cmax (w.add t) ∈ succ (regionFingerprint cmax w)

/-- **Full executable symbolic satisfaction.** Like `SymSatCode`, but the delay quantifiers
`∃∃`/`∀∀` are decided by iterating the region successor `succ` (with the location invariant
required before and after the delay). -/
def SymSatCodeFull (A : FinAutomaton Loc Act C) {cmax : C ⊕ D → ℕ}
    (succ : RegionCode cmax → List (RegionCode cmax)) :
    Loc → RegionCode cmax → Mt Act D → Bool
  | _, _, .tt => true
  | _, _, .ff => false
  | ℓ, γ, .and F G => SymSatCodeFull A succ ℓ γ F && SymSatCodeFull A succ ℓ γ G
  | ℓ, γ, .or F G => SymSatCodeFull A succ ℓ γ F || SymSatCodeFull A succ ℓ γ G
  | _, γ, .guard g => RegionCode.satisfies γ (g.mapClock Sum.inr)
  | ℓ, γ, .reset x F => SymSatCodeFull A succ ℓ (RegionCode.reset (formulaResetP x) γ) F
  | ℓ, γ, .dia a F => A.edges.any fun e =>
      decide (e.1 = ℓ) && decide (e.2.2.1 = a) &&
        RegionCode.satisfies γ (e.2.1.mapClock Sum.inl) &&
        RegionCode.satisfies (RegionCode.reset (edgeResetP e.2.2.2.1) γ)
          ((A.inv e.2.2.2.2).mapClock Sum.inl) &&
        SymSatCodeFull A succ e.2.2.2.2 (RegionCode.reset (edgeResetP e.2.2.2.1) γ) F
  | ℓ, γ, .box a F => A.edges.all fun e =>
      !(decide (e.1 = ℓ) && decide (e.2.2.1 = a) &&
        RegionCode.satisfies γ (e.2.1.mapClock Sum.inl) &&
        RegionCode.satisfies (RegionCode.reset (edgeResetP e.2.2.2.1) γ)
          ((A.inv e.2.2.2.2).mapClock Sum.inl)) ||
        SymSatCodeFull A succ e.2.2.2.2 (RegionCode.reset (edgeResetP e.2.2.2.1) γ) F
  | ℓ, γ, .existsDelay F =>
      RegionCode.satisfies γ ((A.inv ℓ).mapClock Sum.inl) &&
        (succ γ).any fun γ' =>
          RegionCode.satisfies γ' ((A.inv ℓ).mapClock Sum.inl) && SymSatCodeFull A succ ℓ γ' F
  | ℓ, γ, .forallDelay F =>
      !RegionCode.satisfies γ ((A.inv ℓ).mapClock Sum.inl) ||
        (succ γ).all fun γ' =>
          !RegionCode.satisfies γ' ((A.inv ℓ).mapClock Sum.inl) || SymSatCodeFull A succ ℓ γ' F

/-- **Full executable model-checking agreement (conditional).** For a sound and complete
region successor `succ`, the full procedure `SymSatCodeFull` agrees with `SymSat` on the
*entire* `Mt` logic. Proved by induction on `F`; the delay cases use `SuccSound`/`SuccComplete`
to turn the `∃ t : ℝ≥0` / `∀ t : ℝ≥0` quantifier into a finite iteration over `succ`. -/
theorem symSatCodeFull_iff (A : FinAutomaton Loc Act C) {cmax : C ⊕ D → ℕ}
    (wf : A.toTimedAutomaton.WellFormed (cmax ∘ Sum.inl))
    (succ : RegionCode cmax → List (RegionCode cmax))
    (hsound : SuccSound succ) (hcomplete : SuccComplete succ) :
    ∀ {F : Mt Act D}, F.BoundedByD (cmax ∘ Sum.inr) →
      ∀ {ℓ : Loc} {w : Valuation (C ⊕ D)},
        SymSatCodeFull A succ ℓ (regionFingerprint cmax w) F = true
          ↔ SymSat A.toTimedAutomaton ℓ w F := by
  intro F
  induction F with
  | tt => intro _ _ _; simp [SymSatCodeFull, SymSat]
  | ff => intro _ _ _; simp [SymSatCodeFull, SymSat]
  | and F G ihF ihG =>
      intro hbd _ _
      simp only [SymSatCodeFull, SymSat, Bool.and_eq_true]
      exact and_congr (ihF hbd.1) (ihG hbd.2)
  | or F G ihF ihG =>
      intro hbd _ _
      simp only [SymSatCodeFull, SymSat, Bool.or_eq_true]
      exact or_congr (ihF hbd.1) (ihG hbd.2)
  | guard g => intro hbd _ w; exact regionCode_satisfies_inr_iff w hbd
  | reset x F ihF =>
      intro hbd ℓ w
      show SymSatCodeFull A succ ℓ (RegionCode.reset (formulaResetP x) (regionFingerprint cmax w)) F
        = true ↔ _
      rw [reset_fingerprint, formulaResetP_set]
      exact ihF hbd
  | dia a F ihF =>
      intro hbd ℓ w
      constructor
      · intro h
        simp only [SymSatCodeFull, List.any_eq_true] at h
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
          (regionCode_satisfies_inl_iff _ (wf.2 ℓ')).mp hic, (ihF hbd).mp hrec⟩
      · rintro ⟨ℓ', g, r, hedge, hgsat, hinvsat, hrec⟩
        rw [FinAutomaton.edge_iff] at hedge
        obtain ⟨rl, hmem, rfl⟩ := hedge
        have hedge : A.toTimedAutomaton.edge ℓ g a {x | x ∈ rl} ℓ' := ⟨rl, hmem, rfl⟩
        have hres : RegionCode.reset (edgeResetP rl) (regionFingerprint cmax w)
            = regionFingerprint cmax (Valuation.reset (Sum.inl '' {x | x ∈ rl}) w) := by
          rw [reset_fingerprint, edgeResetP_set]
        simp only [SymSatCodeFull, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨(ℓ, g, a, rl, ℓ'), hmem, ⟨⟨⟨⟨rfl, rfl⟩,
          (regionCode_satisfies_inl_iff w (wf.1 _ _ _ _ _ hedge)).mpr hgsat⟩, ?_⟩, ?_⟩⟩
        · rw [hres]; exact (regionCode_satisfies_inl_iff _ (wf.2 ℓ')).mpr hinvsat
        · rw [hres]; exact (ihF hbd).mpr hrec
  | box a F ihF =>
      intro hbd ℓ w
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
        have hb := (List.all_eq_true.mp (by simpa only [SymSatCodeFull] using h)) (ℓ, g, a, rl, ℓ') hmem
        simp only [hgc, hic, Bool.and_true, Bool.not_true, Bool.false_or, decide_true] at hb
        rw [hres] at hb
        exact (ihF hbd).mp hb
      · intro h
        simp only [SymSatCodeFull, List.all_eq_true]
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
          exact (ihF hbd).mpr (h ℓ' g {x | x ∈ rl} hedge
            ((regionCode_satisfies_inl_iff w (wf.1 _ _ _ _ _ hedge)).mp hgc)
            ((regionCode_satisfies_inl_iff _ (wf.2 ℓ')).mp hic))
        · exact Or.inl (by simpa using hm)
  | existsDelay F ihF =>
      intro hbd ℓ w
      constructor
      · intro h
        simp only [SymSatCodeFull, Bool.and_eq_true, List.any_eq_true] at h
        obtain ⟨hpre, γ', hmem, hpost, hrec⟩ := h
        obtain ⟨t, rfl⟩ := hsound w γ' hmem
        exact ⟨t, (regionCode_satisfies_inl_iff w (wf.2 ℓ)).mp hpre,
          (regionCode_satisfies_inl_iff (w.add t) (wf.2 ℓ)).mp hpost, (ihF hbd).mp hrec⟩
      · rintro ⟨t, hpre, hpost, hsym⟩
        simp only [SymSatCodeFull, Bool.and_eq_true, List.any_eq_true]
        exact ⟨(regionCode_satisfies_inl_iff w (wf.2 ℓ)).mpr hpre,
          regionFingerprint cmax (w.add t), hcomplete w t,
          (regionCode_satisfies_inl_iff (w.add t) (wf.2 ℓ)).mpr hpost, (ihF hbd).mpr hsym⟩
  | forallDelay F ihF =>
      intro hbd ℓ w
      constructor
      · intro h t hpre hpost
        have hpreC : RegionCode.satisfies (regionFingerprint cmax w) ((A.inv ℓ).mapClock Sum.inl)
            = true := (regionCode_satisfies_inl_iff w (wf.2 ℓ)).mpr hpre
        have hpostC : RegionCode.satisfies (regionFingerprint cmax (w.add t))
            ((A.inv ℓ).mapClock Sum.inl) = true :=
          (regionCode_satisfies_inl_iff (w.add t) (wf.2 ℓ)).mpr hpost
        simp only [SymSatCodeFull, hpreC, Bool.not_true, Bool.false_or, List.all_eq_true] at h
        have hb := h (regionFingerprint cmax (w.add t)) (hcomplete w t)
        simp only [hpostC, Bool.not_true, Bool.false_or] at hb
        exact (ihF hbd).mp hb
      · intro h
        simp only [SymSatCodeFull, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true]
        by_cases hpreC : RegionCode.satisfies (regionFingerprint cmax w)
            ((A.inv ℓ).mapClock Sum.inl) = true
        · refine Or.inr fun γ' hmem => ?_
          by_cases hpostC : RegionCode.satisfies γ' ((A.inv ℓ).mapClock Sum.inl) = true
          · refine Or.inr ?_
            obtain ⟨t, rfl⟩ := hsound w γ' hmem
            exact (ihF hbd).mpr (h t ((regionCode_satisfies_inl_iff w (wf.2 ℓ)).mp hpreC)
              ((regionCode_satisfies_inl_iff (w.add t) (wf.2 ℓ)).mp hpostC))
          · exact Or.inl (by simpa using hpostC)
        · exact Or.inl (by simpa using hpreC)

/-- **Executable full model checking (conditional).** Given a sound and complete region
successor `succ`, `A ⊨ F` (any `F`) iff the full Bool decision `SymSatCodeFull` is `true` on
the initial region code. With such a `succ` this is an executable decision procedure for the
full timed logic; `succ`'s existence is classical (`timeSuccessor_of_fintype`), a constructive
one (the Alur–Dill successor) is the sole remaining step. -/
theorem satisfiesMt_iff_decideFull [Fintype Loc] (A : FinAutomaton Loc Act C) (F : Mt Act D)
    (succ : RegionCode (Sum.elim A.cmax F.formulaCmax) → List (RegionCode (Sum.elim A.cmax F.formulaCmax)))
    (hsound : SuccSound succ) (hcomplete : SuccComplete succ) :
    A.toTimedAutomaton.SatisfiesMt F
      ↔ SymSatCodeFull A succ A.initial (RegionCode.initial _) F = true := by
  rw [TimedAutomaton.SatisfiesMt, satisfiesMtState_iff_symSat, combineVal_zero,
    ← initial_fingerprint (cmax := Sum.elim A.cmax F.formulaCmax)]
  exact (symSatCodeFull_iff A (cmax := Sum.elim A.cmax F.formulaCmax) A.wellFormed succ hsound
    hcomplete (Mt.boundedByD_formulaCmax F)).symm

end DeepWiki.ReactiveSystems
