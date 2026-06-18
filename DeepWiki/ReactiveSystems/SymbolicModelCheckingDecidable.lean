import DeepWiki.ReactiveSystems.SymbolicModelChecking

/-! # Decidability of symbolic model checking (Theorem 12.2)
Symbolic satisfaction `[ℓ, γ] ⊢ F` is invariant under region equivalence of the
combined valuation *at a finite clamp* `cmax` that bounds both the automaton (all
guards and invariants — `A.WellFormed (cmax ∘ Sum.inl)`) and the formula (all its
clock guards — `F.BoundedByD (cmax ∘ Sum.inr)`). Because the bounded region quotient
`Region cmax` is **finite** (`Region.finite`), symbolic satisfaction descends to a
predicate on a finite set of regions, so model checking a fixed formula reduces to a
finite question — Theorem 12.2. The finite clamp always exists: `cmax ∘ Sum.inr` can
be taken to be `F.formulaCmax`, the per-formula-clock maximum constant. This is the
symbolic-logic counterpart of the region-graph finiteness already used for untimed
bisimilarity and reachability decidability. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

variable {Loc Act C D : Type*}

/-! ## Per-constraint and per-formula clock clamps

A constructive clamp dominating a constraint (`ClockConstraint.bound`) and a formula
(`Mt.formulaCmax`), with the domination lemmas. The clamp is *uniform per atom* — an
atom `x ⋈ n` contributes `n` to every clock — which over-approximates but stays
constructive (no `DecidableEq` on the clock set) and is all finiteness needs. -/

/-- A constructive clamp dominating a clock constraint: each atom `x ⋈ n` contributes
its constant `n` (uniformly), conjunctions take the pointwise `max`. -/
def ClockConstraint.bound : ClockConstraint C → (C → ℕ)
  | .true_ => fun _ => 0
  | .atom _ _ n => fun _ => n
  | .and g₁ g₂ => fun x => max (g₁.bound x) (g₂.bound x)

/-- `g` is bounded by its own clamp `g.bound`. -/
theorem ClockConstraint.boundedBy_bound (g : ClockConstraint C) : g.BoundedBy g.bound := by
  induction g with
  | true_ => exact trivial
  | atom x cmp n => exact le_refl n
  | and g₁ g₂ ih₁ ih₂ =>
      exact ⟨ClockConstraint.boundedBy_mono (fun x => le_max_left _ _) ih₁,
             ClockConstraint.boundedBy_mono (fun x => le_max_right _ _) ih₂⟩

/-- `F.BoundedByD cmax`: every clock guard `g` occurring in the formula `F` is
`BoundedBy cmax` (the formula-clock analogue of `WellFormed`'s guard clause). -/
def Mt.BoundedByD : Mt Act D → (D → ℕ) → Prop
  | .tt, _ => True
  | .ff, _ => True
  | .and F G, c => F.BoundedByD c ∧ G.BoundedByD c
  | .or F G, c => F.BoundedByD c ∧ G.BoundedByD c
  | .dia _ F, c => F.BoundedByD c
  | .box _ F, c => F.BoundedByD c
  | .existsDelay F, c => F.BoundedByD c
  | .forallDelay F, c => F.BoundedByD c
  | .reset _ F, c => F.BoundedByD c
  | .guard g, c => g.BoundedBy c

/-- A constructive clamp dominating every clock guard of a formula. -/
def Mt.formulaCmax : Mt Act D → (D → ℕ)
  | .tt => fun _ => 0
  | .ff => fun _ => 0
  | .and F G => fun d => max (F.formulaCmax d) (G.formulaCmax d)
  | .or F G => fun d => max (F.formulaCmax d) (G.formulaCmax d)
  | .dia _ F => F.formulaCmax
  | .box _ F => F.formulaCmax
  | .existsDelay F => F.formulaCmax
  | .forallDelay F => F.formulaCmax
  | .reset _ F => F.formulaCmax
  | .guard g => g.bound

/-- `BoundedByD` is monotone in the clamp. -/
theorem Mt.boundedByD_mono {c c' : D → ℕ} (hle : ∀ x, c x ≤ c' x) :
    ∀ {F : Mt Act D}, F.BoundedByD c → F.BoundedByD c' := by
  intro F
  induction F with
  | tt => exact fun _ => trivial
  | ff => exact fun _ => trivial
  | and F G ihF ihG => exact fun h => ⟨ihF h.1, ihG h.2⟩
  | or F G ihF ihG => exact fun h => ⟨ihF h.1, ihG h.2⟩
  | dia _ F ihF => exact fun h => ihF h
  | box _ F ihF => exact fun h => ihF h
  | existsDelay F ihF => exact fun h => ihF h
  | forallDelay F ihF => exact fun h => ihF h
  | reset _ F ihF => exact fun h => ihF h
  | guard g => exact fun h => ClockConstraint.boundedBy_mono hle h

/-- Every formula is bounded by its own clamp `F.formulaCmax`. -/
theorem Mt.boundedByD_formulaCmax : ∀ F : Mt Act D, F.BoundedByD F.formulaCmax := by
  intro F
  induction F with
  | tt => exact trivial
  | ff => exact trivial
  | and F G ihF ihG =>
      exact ⟨Mt.boundedByD_mono (fun _ => le_max_left _ _) ihF,
             Mt.boundedByD_mono (fun _ => le_max_right _ _) ihG⟩
  | or F G ihF ihG =>
      exact ⟨Mt.boundedByD_mono (fun _ => le_max_left _ _) ihF,
             Mt.boundedByD_mono (fun _ => le_max_right _ _) ihG⟩
  | dia _ F ihF => exact ihF
  | box _ F ihF => exact ihF
  | existsDelay F ihF => exact ihF
  | forallDelay F ihF => exact ihF
  | reset _ F ihF => exact ihF
  | guard g => exact ClockConstraint.boundedBy_bound g

/-! ## Symbolic satisfaction is invariant under bounded region equivalence

The bounded refinement of `symSat_congr`: region equivalence at the *finite* clamp
`cmax` (rather than at every clamp) already determines symbolic satisfaction, provided
`cmax` bounds the automaton's guards and invariants (`A.WellFormed (cmax ∘ Sum.inl)`)
and the formula's clock guards (`F.BoundedByD (cmax ∘ Sum.inr)`). This is what makes
the *finite* region quotient `Region cmax` enough to decide model checking. -/

variable [Fintype C] [Fintype D]

/-- **`SymSat` is invariant under bounded region equivalence.** If the combined clamp
`cmax` bounds the automaton (`A.WellFormed (cmax ∘ Sum.inl)`) and the formula
(`F.BoundedByD (cmax ∘ Sum.inr)`), then region-equivalent combined valuations *at that
single clamp* satisfy `F` symbolically alike. The guard/invariant clauses use
`regionEq_satisfies` with the boundedness witnesses (`wfg`/`wfi`/`hF`) restricted to
the `C`/`D` component via `RegionEq.precomp`; the delay clauses use the finite-clock
time-successor `timeSuccessor_of_fintype` to match each delay region-preservingly. -/
theorem symSat_congr_bounded (A : TimedAutomaton Loc Act C) {cmax : C ⊕ D → ℕ}
    (wf : A.WellFormed (cmax ∘ Sum.inl)) (F : Mt Act D) :
    F.BoundedByD (cmax ∘ Sum.inr) → ∀ {ℓ : Loc} {w w' : Valuation (C ⊕ D)},
      RegionEq cmax w w' → (SymSat A ℓ w F ↔ SymSat A ℓ w' F) := by
  obtain ⟨wfg, wfi⟩ := wf
  induction F with
  | tt => intro _ _ _ _ _; exact Iff.rfl
  | ff => intro _ _ _ _ _; exact Iff.rfl
  | and F G ihF ihG => intro hF _ _ _ h; exact and_congr (ihF hF.1 h) (ihG hF.2 h)
  | or F G ihF ihG => intro hF _ _ _ h; exact or_congr (ihF hF.1 h) (ihG hF.2 h)
  | guard g => intro hF _ _ _ h; exact regionEq_satisfies (RegionEq.precomp Sum.inr h) hF
  | reset x F ihF => intro hF _ _ _ h; exact ihF hF (RegionEq.reset {Sum.inr x} h)
  | dia a F ihF =>
      intro hF ℓ w w' h
      constructor
      · rintro ⟨ℓ', g, r, hedge, hg, hinv, hsym⟩
        exact ⟨ℓ', g, r, hedge,
          (regionEq_satisfies (RegionEq.precomp Sum.inl h) (wfg ℓ g a r ℓ' hedge)).mp hg,
          (regionEq_satisfies (RegionEq.precomp Sum.inl (RegionEq.reset (Sum.inl '' r) h))
            (wfi ℓ')).mp hinv,
          (ihF hF (RegionEq.reset (Sum.inl '' r) h)).mp hsym⟩
      · rintro ⟨ℓ', g, r, hedge, hg, hinv, hsym⟩
        exact ⟨ℓ', g, r, hedge,
          (regionEq_satisfies (RegionEq.precomp Sum.inl h) (wfg ℓ g a r ℓ' hedge)).mpr hg,
          (regionEq_satisfies (RegionEq.precomp Sum.inl (RegionEq.reset (Sum.inl '' r) h))
            (wfi ℓ')).mpr hinv,
          (ihF hF (RegionEq.reset (Sum.inl '' r) h)).mpr hsym⟩
  | box a F ihF =>
      intro hF ℓ w w' h
      constructor
      · intro hbox ℓ' g r hedge hg hinv
        refine (ihF hF (RegionEq.reset (Sum.inl '' r) h)).mp (hbox ℓ' g r hedge ?_ ?_)
        · exact (regionEq_satisfies (RegionEq.precomp Sum.inl h) (wfg ℓ g a r ℓ' hedge)).mpr hg
        · exact (regionEq_satisfies (RegionEq.precomp Sum.inl (RegionEq.reset (Sum.inl '' r) h))
            (wfi ℓ')).mpr hinv
      · intro hbox ℓ' g r hedge hg hinv
        refine (ihF hF (RegionEq.reset (Sum.inl '' r) h)).mpr (hbox ℓ' g r hedge ?_ ?_)
        · exact (regionEq_satisfies (RegionEq.precomp Sum.inl h) (wfg ℓ g a r ℓ' hedge)).mp hg
        · exact (regionEq_satisfies (RegionEq.precomp Sum.inl (RegionEq.reset (Sum.inl '' r) h))
            (wfi ℓ')).mp hinv
  | existsDelay F ihF =>
      intro hF ℓ w w' h
      constructor
      · rintro ⟨t, hpre, hpost, hsym⟩
        obtain ⟨t', ht'⟩ := timeSuccessor_of_fintype cmax h t
        exact ⟨t', (regionEq_satisfies (RegionEq.precomp Sum.inl h) (wfi ℓ)).mp hpre,
          (regionEq_satisfies (RegionEq.precomp Sum.inl ht') (wfi ℓ)).mp hpost,
          (ihF hF ht').mp hsym⟩
      · rintro ⟨t', hpre, hpost, hsym⟩
        obtain ⟨t, ht⟩ := timeSuccessor_of_fintype cmax ((regionEq_equivalence cmax).symm h) t'
        exact ⟨t, (regionEq_satisfies (RegionEq.precomp Sum.inl h) (wfi ℓ)).mpr hpre,
          (regionEq_satisfies (RegionEq.precomp Sum.inl ht) (wfi ℓ)).mp hpost,
          (ihF hF ht).mp hsym⟩
  | forallDelay F ihF =>
      intro hF ℓ w w' h
      constructor
      · intro hall t' hpre hpost
        obtain ⟨t, ht⟩ := timeSuccessor_of_fintype cmax ((regionEq_equivalence cmax).symm h) t'
        exact (ihF hF ht).mpr (hall t
          ((regionEq_satisfies (RegionEq.precomp Sum.inl h) (wfi ℓ)).mpr hpre)
          ((regionEq_satisfies (RegionEq.precomp Sum.inl ht) (wfi ℓ)).mp hpost))
      · intro hall t hpre hpost
        obtain ⟨t', ht'⟩ := timeSuccessor_of_fintype cmax h t
        exact (ihF hF ht').mpr (hall t'
          ((regionEq_satisfies (RegionEq.precomp Sum.inl h) (wfi ℓ)).mp hpre)
          ((regionEq_satisfies (RegionEq.precomp Sum.inl ht') (wfi ℓ)).mp hpost))

/-! ## The finite bounded-region quotient — Theorem 12.2

`symSat_congr_bounded` lets symbolic satisfaction descend to the **finite** region
quotient `Region cmax` (finite by `Region.finite` for finitely many clocks). A fixed
formula `F` is thus checked against finitely many region classes — the finiteness that
makes timed model checking decidable. -/

/-- **Definition 12.5, bounded-region form.** Symbolic satisfaction `[ℓ, γ] ⊢ F` with
`γ` a class of the *finite* bounded region quotient `Region cmax`, well-defined by
`symSat_congr_bounded`. -/
def SymSatBoundedRegion (A : TimedAutomaton Loc Act C) {cmax : C ⊕ D → ℕ}
    (wf : A.WellFormed (cmax ∘ Sum.inl)) (F : Mt Act D)
    (hF : F.BoundedByD (cmax ∘ Sum.inr)) (ℓ : Loc) (γ : Region cmax) : Prop :=
  Quotient.liftOn γ (fun w => SymSat A ℓ w F)
    (fun _ _ h => propext (symSat_congr_bounded A wf F hF h))

/-- `[ℓ, [w]_≡] ⊢ F` on a bounded region reduces to `SymSat` on the representative. -/
@[simp] theorem symSatBoundedRegion_region (A : TimedAutomaton Loc Act C) {cmax : C ⊕ D → ℕ}
    (wf : A.WellFormed (cmax ∘ Sum.inl)) (F : Mt Act D)
    (hF : F.BoundedByD (cmax ∘ Sum.inr)) (ℓ : Loc) (w : Valuation (C ⊕ D)) :
    SymSatBoundedRegion A wf F hF ℓ (region cmax w) ↔ SymSat A ℓ w F :=
  Iff.rfl

/-- **Theorem 12.1 / 12.2, bounded-region form.** Concrete satisfaction `((ℓ,v),u) ⊨ F`
agrees with bounded-region symbolic satisfaction `[ℓ, [vu]_≡] ⊢ F` — and since
`Region cmax` is finite, the right side ranges over a finite set of classes. -/
theorem mtSat_iff_symSatBoundedRegion (A : TimedAutomaton Loc Act C) {cmax : C ⊕ D → ℕ}
    (wf : A.WellFormed (cmax ∘ Sum.inl)) (F : Mt Act D)
    (hF : F.BoundedByD (cmax ∘ Sum.inr)) (ℓ : Loc) (v : Valuation C) (u : Valuation D) :
    A.tlts.MtSat (ℓ, v) u F ↔
      SymSatBoundedRegion A wf F hF ℓ (region cmax (combineVal v u)) :=
  mtSat_iff_symSat A F ℓ v u

/-- The bounded region quotient over the combined clock set `C ⊕ D` is finite — the
finiteness underlying decidability of timed model checking. -/
example (cmax : C ⊕ D → ℕ) : Finite (Region cmax) := Region.finite cmax

/-- **Theorem 12.2 (a finite clamp always exists).** For any timed automaton `A`
well-formed for `cmaxC` and any formula `F`, the combined clamp
`Sum.elim cmaxC F.formulaCmax` bounds both sides, so concrete satisfaction agrees with
symbolic satisfaction on the **finite** bounded region quotient `Region`. Model
checking `F` against `A` therefore reduces to a finite question — Theorem 12.2. -/
theorem mtSat_iff_symSatBoundedRegion_formulaCmax (A : TimedAutomaton Loc Act C)
    {cmaxC : C → ℕ} (wf : A.WellFormed cmaxC) (F : Mt Act D) (ℓ : Loc)
    (v : Valuation C) (u : Valuation D) :
    A.tlts.MtSat (ℓ, v) u F ↔
      SymSatBoundedRegion A (cmax := Sum.elim cmaxC F.formulaCmax) wf F
        (Mt.boundedByD_formulaCmax F) ℓ (region _ (combineVal v u)) :=
  mtSat_iff_symSat A F ℓ v u

end DeepWiki.ReactiveSystems
