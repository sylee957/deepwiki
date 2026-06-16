import DeepWiki.ReactiveSystems.BisimulationQuotient
import DeepWiki.ReactiveSystems.TimedRegionsBisimulation

/-! # The region graph and decidability (§11.4)
The *region graph* `Tᵣ(A)` (Definition 11.14) is the quotient of the untimed
transition system `Tᵤ(A)` by region equivalence on configurations: symbolic
states are classes `⟦(ℓ,v)⟧ = (ℓ,[v]_≡)`, with action transitions lifted from
`Tᵤ(A)` and a single `ε`-label for "some delay". Because region equivalence is a
strong bisimulation on `Tᵤ(A)` (Theorem 11.3), the generic quotient machinery
(`crossBisimilar_quot`, `bisimilar_quot_iff`, `reachable_quot_iff`) gives the
chapter's headline results for free: every configuration is strongly bisimilar to
its symbolic state (**Theorem 11.4**), and the region graph is finite, so untimed
bisimilarity (**Corollary 11.1**) and reachability (**Lemma 11.2**, **Corollary
11.2**) both reduce to decidable questions on a finite graph. All are stated
unconditionally for the finitely-many-clocks case via `timeSuccessor_of_fintype`. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal
open LTS

variable {Loc Act C : Type*}

/-! ## The region-equivalence setoid on configurations -/

/-- The **region-equivalence setoid on configurations**: `(ℓ,v) ≈ (ℓ',v')` iff the
locations agree and the valuations are region equivalent. This is exactly the
relation shown to be an untimed bisimulation in Theorem 11.3. -/
def regionConfigSetoid (cmax : C → ℕ) : Setoid (Loc × Valuation C) where
  r s₁ s₂ := s₁.1 = s₂.1 ∧ RegionEq cmax s₁.2 s₂.2
  iseqv :=
    ⟨fun s => ⟨rfl, (regionEq_equivalence cmax).refl s.2⟩,
     fun ⟨h1, h2⟩ => ⟨h1.symm, (regionEq_equivalence cmax).symm h2⟩,
     fun ⟨h1, h2⟩ ⟨h1', h2'⟩ => ⟨h1.trans h1', (regionEq_equivalence cmax).trans h2 h2'⟩⟩

/-- The configuration setoid relation is exactly the untimed bisimulation of
Theorem 11.3, so it is a strong bisimulation on `Tᵤ(A)` (given the region
time-successor property). -/
theorem isBisimulation_regionConfigSetoid (A : TimedAutomaton Loc Act C) {cmax : C → ℕ}
    (wf : A.WellFormed cmax) (hts : TimeSuccessor cmax) :
    LTS.IsBisimulation A.tlts.untimedLTS (regionConfigSetoid cmax).r :=
  regionEq_untimedBisimulation A wf hts

/-! ## Definition 11.14: the region graph -/

/-- **Definition 11.14.** The *region graph* `Tᵣ(A)` of a timed automaton: the
quotient of the untimed transition system `Tᵤ(A)` by region equivalence on
configurations. Symbolic states are classes `⟦(ℓ,v)⟧ = (ℓ,[v]_≡)`; for an action
`a`, `⟦(ℓ,v)⟧ —a→ ⟦(ℓ',v')⟧` iff `(ℓ,v) —a→ (ℓ',v')`, and the `ε`-label (`none`)
abstracts "some delay". -/
noncomputable def TimedAutomaton.regionGraph (A : TimedAutomaton Loc Act C) (cmax : C → ℕ) :
    LTS (Quotient (regionConfigSetoid (Loc := Loc) cmax)) (Option Act) :=
  A.tlts.untimedLTS.quot (regionConfigSetoid cmax)

/-- A configuration's symbolic state `(ℓ,[v]_≡)`, the region graph state for `(ℓ,v)`. -/
def symbolicState (cmax : C → ℕ) (c : Loc × Valuation C) :
    Quotient (regionConfigSetoid (Loc := Loc) cmax) :=
  Quotient.mk (regionConfigSetoid cmax) c

/-! ## Theorem 11.4: the region graph is finite and bisimilar to the untimed system -/

/-- The map `(ℓ,[v]_≡) ↦ (ℓ, [v]_≡)` sending a symbolic state to a
location/region pair (well defined on the quotient). -/
def regionConfigSymbolic (cmax : C → ℕ) :
    Quotient (regionConfigSetoid (Loc := Loc) cmax) → Loc × Region cmax :=
  Quotient.lift (fun s => (s.1, region cmax s.2))
    (fun _ _ ⟨h1, h2⟩ => Prod.ext h1 (region_eq_iff.mpr h2))

/-- Distinct symbolic states have distinct location/region pairs. -/
theorem regionConfigSymbolic_injective (cmax : C → ℕ) :
    Function.Injective (regionConfigSymbolic (Loc := Loc) cmax) := by
  intro x y
  induction x using Quotient.ind with | _ a =>
  induction y using Quotient.ind with | _ b =>
  intro h
  simp only [regionConfigSymbolic, Quotient.lift_mk, Prod.mk.injEq] at h
  exact Quotient.sound ⟨h.1, region_eq_iff.mp h.2⟩

/-- **Theorem 11.4** (finiteness part). For a timed automaton with finitely many
locations and clocks, the region graph has finitely many (symbolic) states. -/
instance regionGraph_finite [Finite Loc] [Finite C] (cmax : C → ℕ) :
    Finite (Quotient (regionConfigSetoid (Loc := Loc) cmax)) :=
  Finite.of_injective _ (regionConfigSymbolic_injective cmax)

/-- **Theorem 11.4** (bisimilarity part), modular form. In a well-formed timed
automaton with the region time-successor property, a configuration `(ℓ,v)` of the
untimed transition system is strongly bisimilar to its symbolic state `(ℓ,[v]_≡)`
in the region graph. -/
theorem TimedAutomaton.regionGraph_crossBisimilar (A : TimedAutomaton Loc Act C)
    {cmax : C → ℕ} (wf : A.WellFormed cmax) (hts : TimeSuccessor cmax)
    (c : Loc × Valuation C) :
    LTS.CrossBisimilar A.tlts.untimedLTS (A.regionGraph cmax) c
      (symbolicState cmax c) :=
  crossBisimilar_quot A.tlts.untimedLTS (regionConfigSetoid cmax)
    (isBisimulation_regionConfigSetoid A wf hts) c

/-- **Theorem 11.4** (bisimilarity part), **unconditional for finite clock sets**.
Every configuration is strongly bisimilar to its symbolic state — no extra
hypothesis, since the region time-successor property holds for finitely many
clocks (`timeSuccessor_of_fintype`). -/
theorem TimedAutomaton.regionGraph_crossBisimilar_fintype [Fintype C]
    (A : TimedAutomaton Loc Act C) {cmax : C → ℕ} (wf : A.WellFormed cmax)
    (c : Loc × Valuation C) :
    LTS.CrossBisimilar A.tlts.untimedLTS (A.regionGraph cmax) c
      (symbolicState cmax c) :=
  A.regionGraph_crossBisimilar wf (timeSuccessor_of_fintype cmax) c

/-! ## Corollary 11.1: untimed bisimilarity is decidable -/

/-- **Corollary 11.1** (§11.4), reduction form. Two configurations are *untimed
bisimilar* in `Tᵤ(A)` iff their symbolic states are *strongly bisimilar* in the
region graph `Tᵣ(A)`. Since the region graph is finite (Theorem 11.4), strong
bisimilarity there is decidable — hence untimed bisimilarity is decidable. -/
theorem TimedAutomaton.untimedBisimilar_iff_regionGraph (A : TimedAutomaton Loc Act C)
    {cmax : C → ℕ} (wf : A.WellFormed cmax) (hts : TimeSuccessor cmax)
    (c₁ c₂ : Loc × Valuation C) :
    A.tlts.UntimedBisimilar c₁ c₂ ↔
      LTS.Bisimilar (A.regionGraph cmax) (symbolicState cmax c₁) (symbolicState cmax c₂) :=
  (bisimilar_quot_iff A.tlts.untimedLTS (regionConfigSetoid cmax)
    (isBisimulation_regionConfigSetoid A wf hts) c₁ c₂).symm

/-- **Corollary 11.1**, **unconditional for finite clock sets**. -/
theorem TimedAutomaton.untimedBisimilar_iff_regionGraph_fintype [Fintype C]
    (A : TimedAutomaton Loc Act C) {cmax : C → ℕ} (wf : A.WellFormed cmax)
    (c₁ c₂ : Loc × Valuation C) :
    A.tlts.UntimedBisimilar c₁ c₂ ↔
      LTS.Bisimilar (A.regionGraph cmax) (symbolicState cmax c₁) (symbolicState cmax c₂) :=
  A.untimedBisimilar_iff_regionGraph wf (timeSuccessor_of_fintype cmax) c₁ c₂

/-! ## Lemma 11.2 and Corollary 11.2: the reachability problem is decidable -/

/-- Forward direction of **Lemma 11.2**: a reachability run of `A` lifts to a run
in the region graph (no well-formedness needed). -/
theorem TimedAutomaton.regionGraph_reachable_of (A : TimedAutomaton Loc Act C) (cmax : C → ℕ)
    {c c' : Loc × Valuation C} (h : A.tlts.untimedLTS.Reachable c c') :
    (A.regionGraph cmax).Reachable (symbolicState cmax c) (symbolicState cmax c') :=
  reachable_quot_mk A.tlts.untimedLTS (regionConfigSetoid cmax) h

/-- **Lemma 11.2** (§11.4), reduction form. A symbolic state `t` is reachable from
`⟦c₀⟧` in the region graph iff `A` can reach some configuration in the region
class `t` from `c₀`. Reachability in `A` thus reduces to reachability in the
finite region graph. -/
theorem TimedAutomaton.reachable_iff_regionGraph (A : TimedAutomaton Loc Act C)
    {cmax : C → ℕ} (wf : A.WellFormed cmax) (hts : TimeSuccessor cmax)
    (c₀ : Loc × Valuation C) (t : Quotient (regionConfigSetoid cmax)) :
    (A.regionGraph cmax).Reachable (symbolicState cmax c₀) t ↔
      ∃ c, symbolicState cmax c = t ∧ A.tlts.untimedLTS.Reachable c₀ c :=
  reachable_quot_iff A.tlts.untimedLTS (regionConfigSetoid cmax)
    (isBisimulation_regionConfigSetoid A wf hts)

/-- **Lemma 11.2 / Corollary 11.2**, **unconditional for finite clock sets**.
Reachability in the timed automaton reduces to reachability in the *finite*
region graph, which is decidable — so the reachability problem is decidable. -/
theorem TimedAutomaton.reachable_iff_regionGraph_fintype [Fintype C]
    (A : TimedAutomaton Loc Act C) {cmax : C → ℕ} (wf : A.WellFormed cmax)
    (c₀ : Loc × Valuation C) (t : Quotient (regionConfigSetoid cmax)) :
    (A.regionGraph cmax).Reachable (symbolicState cmax c₀) t ↔
      ∃ c, symbolicState cmax c = t ∧ A.tlts.untimedLTS.Reachable c₀ c :=
  A.reachable_iff_regionGraph wf (timeSuccessor_of_fintype cmax) c₀ t

end DeepWiki.ReactiveSystems
