import DeepWiki.ReactiveSystems.BisimulationFixedPoint
import DeepWiki.ReactiveSystems.BisimulationApprox
import DeepWiki.ReactiveSystems.WeakBisimulationFixedPoint
import DeepWiki.ReactiveSystems.FiniteLatticeIterate
import DeepWiki.ReactiveSystems.Chapter4Examples
import Sources.Doi_10_1017_CBO9780511814105.Source
import Mathlib.Order.FixedPoints
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Iterate
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Set.Insert
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.FinCases

/-! # Reactive Systems catalog — Chapter 4: Theory of fixed points and bisimulation
Book-numbered restatements for Chapter 4. The order-theoretic background
(§4.1–4.2) reuses Mathlib directly; §4.3 (bisimulation as a fixed point) is
discharged by the `DeepWiki.ReactiveSystems` library. -/

namespace DeepWiki.Rs

open DeepWiki.ReactiveSystems
open scoped ENNReal

/-! ## §4.1 Posets and complete lattices -/

/-- **§4.1** (p.75). A partially ordered set. Reuses Mathlib's `PartialOrder`. -/
abbrev poset := @PartialOrder

/-- **§4.1** (p.76). A complete lattice: every subset has a least upper bound and
a greatest lower bound. Reuses Mathlib's `CompleteLattice`. -/
abbrev complete_lattice := @CompleteLattice

/-! ## §4.2 Tarski's fixed point theorem -/

/-- **Theorem 4.1** (Tarski's fixed point theorem, §4.2, p.80), greatest fixed
point `⊔{x | x ≤ f x}` of a monotone map on a complete lattice. Reuses Mathlib's
`OrderHom.gfp`. -/
abbrev thm_4_1_gfp := @OrderHom.gfp

/-- **Theorem 4.1** (Tarski's fixed point theorem, §4.2, p.80), least fixed point
`⊓{x | f x ≤ x}`. Reuses Mathlib's `OrderHom.lfp`. -/
abbrev thm_4_1_lfp := @OrderHom.lfp

/-- **Theorem 4.1** (§4.2, p.80). `gfp f` is the greatest fixed point of `f`. -/
alias thm_4_1_isGreatest_gfp := OrderHom.isGreatest_gfp

/-- **Theorem 4.1** (§4.2, p.80). `lfp f` is the least fixed point of `f`. -/
alias thm_4_1_isLeast_lfp := OrderHom.isLeast_lfp

/-! ## §4.3 Bisimulation as a fixed point -/

/-- **§4.3** (p.85), the bisimulation functional `F` on the complete lattice of
relations over an LTS's states. The library's `LTS.bisimFunctional`. -/
abbrev bisimFunctional := @LTS.bisimFunctional

/-- **§4.3** (p.85). A relation is a strong bisimulation iff it is a post-fixed
point of `F`: `R` is a bisimulation iff `R ⊆ F(R)`. -/
alias bisim_iff_post_fixed := LTS.isBisimulation_iff_le_bisimFunctional

/-- **§4.3** (p.86). Strong bisimilarity `~` is the greatest fixed point of the
bisimulation functional `F`. -/
alias bisimilar_eq_gfp := LTS.bisimilar_eq_gfp

/-! ## Solved exercises -/

/-- **Kleene's fixed-point theorem** (§4.2, p.83). The continuous strengthening of
Theorem 4.2: for an ω-(Scott-)continuous monotone map on a complete lattice the
least fixed point is `⨆ₙ fⁿ(⊥)`. (Not a separately-numbered book item; the §4.2
iterative algorithm.) Reuses Mathlib's `fixedPoints.lfp_eq_sSup_iterate`. -/
alias kleene_lfp_eq_iSup_iterate := fixedPoints.lfp_eq_sSup_iterate

/-- **Exercise 4.10(3a)** (§4.2, p.84). The supremum of a set of post-fixed
points (`x ≤ f x`) of a monotone map is again a post-fixed point. -/
theorem ex_4_10_3a {D : Type*} [CompleteLattice D] (f : D →o D) (X : Set D)
    (hX : ∀ x ∈ X, x ≤ f x) : sSup X ≤ f (sSup X) :=
  sSup_le fun x hx => (hX x hx).trans (f.mono (le_sSup hx))

/-- **Exercise 4.10(4a)** (§4.2, p.84). The infimum of a set of pre-fixed points
(`f x ≤ x`) of a monotone map is again a pre-fixed point. -/
theorem ex_4_10_4a {D : Type*} [CompleteLattice D] (f : D →o D) (X : Set D)
    (hX : ∀ x ∈ X, f x ≤ x) : f (sInf X) ≤ sInf X :=
  le_sInf fun x hx => (f.mono (sInf_le hx)).trans (hX x hx)

/-- **Exercise 4.10(3b)** (§4.2, p.84). The dual of 3(a) fails: the *infimum* of a
set of post-fixed points of a monotone map need not be post-fixed. Witness:
`ℝ≥0∞` with the monotone `f x = if x ≤ 1 then 0 else x`; every `x > 1` is
post-fixed, but `⨅ (Ioi 1) = 1` is not (`f 1 = 0 < 1`). -/
theorem ex_4_10_3b : ∃ (D : Type) (_ : CompleteLattice D) (f : D →o D) (X : Set D),
    (∀ x ∈ X, x ≤ f x) ∧ ¬ (sInf X ≤ f (sInf X)) := by
  refine ⟨ℝ≥0∞, inferInstance, ⟨fun x => if x ≤ 1 then 0 else x, ?_⟩, Set.Ioi 1, ?_, ?_⟩
  · intro x y hxy
    by_cases hy : y ≤ 1
    · simp [le_trans hxy hy, hy]
    · by_cases hx : x ≤ 1 <;> simp [hx, hy, hxy]
  · intro x hx
    rw [Set.mem_Ioi] at hx
    simp [not_le.mpr hx]
  · have hinf : sInf (Set.Ioi (1 : ℝ≥0∞)) = 1 := by
      apply le_antisymm
      · by_contra h
        push Not at h
        obtain ⟨z, h1z, hzs⟩ := exists_between h
        exact absurd (sInf_le (Set.mem_Ioi.mpr h1z)) (not_le.mpr hzs)
      · exact le_sInf (fun x hx => le_of_lt hx)
    rw [hinf]; simp

/-- **Exercise 4.10(4b)** (§4.2, p.84). Dually, the *supremum* of a set of
pre-fixed points of a monotone map need not be pre-fixed. Witness: `ℝ≥0∞` with
`f x = if 1 ≤ x then ⊤ else x`; every `x < 1` is pre-fixed, but
`⨆ (Iio 1) = 1` is not (`f 1 = ⊤ > 1`). -/
theorem ex_4_10_4b : ∃ (D : Type) (_ : CompleteLattice D) (f : D →o D) (X : Set D),
    (∀ x ∈ X, f x ≤ x) ∧ ¬ (f (sSup X) ≤ sSup X) := by
  refine ⟨ℝ≥0∞, inferInstance, ⟨fun x => if 1 ≤ x then ⊤ else x, ?_⟩, Set.Iio 1, ?_, ?_⟩
  · intro x y hxy
    by_cases hx : 1 ≤ x
    · simp [hx, le_trans hx hxy]
    · by_cases hy : 1 ≤ y <;> simp [hx, hy, hxy]
  · intro x hx
    rw [Set.mem_Iio] at hx
    simp [not_le.mpr hx]
  · have hsup : sSup (Set.Iio (1 : ℝ≥0∞)) = 1 := by
      apply le_antisymm
      · exact sSup_le (fun x hx => le_of_lt hx)
      · by_contra h
        push Not at h
        obtain ⟨z, hsz, hz1⟩ := exists_between h
        exact absurd (le_sSup (Set.mem_Iio.mpr hz1)) (not_le.mpr hsz)
    rw [hsup]; simp

/-- **Exercise 4.10(5)** (§4.2, p.84). The monotone self-maps of a complete
lattice, ordered pointwise, again form a complete lattice. -/
theorem ex_4_10_5 (D : Type*) [CompleteLattice D] : Nonempty (CompleteLattice (D →o D)) :=
  ⟨inferInstance⟩

/-! ## Order-theoretic gaps and the bisimilarity approximants -/

/-- **Definition 4.2** (§4.1, p.77), least upper bound. Reuses Mathlib's `IsLUB`. -/
abbrev def_4_2_lub := @IsLUB

/-- **Definition 4.2** (§4.1, p.77), greatest lower bound. Reuses Mathlib's `IsGLB`. -/
abbrev def_4_2_glb := @IsGLB

/-- **Definition 4.5** (§4.2, p.82), function iteration `fⁿ` (`f^[n]`). Reuses
Mathlib's `Nat.iterate`. -/
abbrev def_4_5 := @Nat.iterate

/-- **Theorem 4.1** (§4.2, p.80), other half: the fixed points of a monotone map
on a complete lattice themselves form a complete lattice (Knaster–Tarski).
Reuses Mathlib's `fixedPoints.completeLattice`. -/
abbrev thm_4_1_fixedPoints_lattice := @fixedPoints.completeLattice

/-- **Exercise 4.3** (§4.1). A least upper bound is unique. -/
alias ex_4_3 := IsLUB.unique

/-- **Kleene's fixed-point theorem** (§4.2, dual). The continuous strengthening of
Theorem 4.2: on a complete lattice the greatest fixed point of a monotone map is
`⨅ₙ fⁿ(⊤)`. (Not a separately-numbered book item; the §4.2 iterative algorithm.)
Reuses Mathlib's `fixedPoints.gfp_eq_sInf_iterate`. -/
alias kleene_gfp_eq_iInf_iterate := fixedPoints.gfp_eq_sInf_iterate

/-- **Exercise 4.14** (§4.2). The bisimilarity approximants `∼ᵢ = Fⁱ(⊤)`. The
library's `LTS.bisimApprox`. -/
abbrev ex_4_14 := @LTS.bisimApprox

/-- **Exercise 4.14** (§4.2). Each approximant `∼ᵢ` is an equivalence relation. -/
theorem ex_4_14_equivalence {Proc Act : Type*} (L : LTS Proc Act) (i : ℕ) :
    Equivalence (LTS.bisimApprox L i) := LTS.bisimApprox_equivalence L i

/-- **Exercise 4.14** (§4.2). The approximants form a decreasing chain
`∼_{i+1} ⊆ ∼ᵢ`. -/
theorem ex_4_14_antitone {Proc Act : Type*} (L : LTS Proc Act) (i : ℕ) :
    LTS.bisimApprox L (i + 1) ≤ LTS.bisimApprox L i := LTS.bisimApprox_antitone L i

/-- **Exercise 4.14** (§4.2). Strong bisimilarity refines every approximant
`∼ ⊆ ∼ᵢ`. -/
theorem ex_4_14_bisimilar_le {Proc Act : Type*} (L : LTS Proc Act) (i : ℕ) :
    LTS.Bisimilar L ≤ LTS.bisimApprox L i := LTS.bisimilar_le_bisimApprox L i

/-- **Definition 4.4** (§4.2, p.79). A *monotonic* function `f : D → D`
(`d ≼ d' ⇒ f d ≼ f d'`). Reuses Mathlib's bundled `OrderHom` (`D →o D`). -/
abbrev def_4_4_monotonic := @OrderHom

/-- **Definition 4.4** (§4.2, p.79). A *fixed point* of `f` (`d = f d`). Reuses
Mathlib's `Function.IsFixedPt`. -/
abbrev def_4_4_fixedPoint := @Function.IsFixedPt

/-- **Exercise 4.5** (§4.1, p.78). In a complete lattice the join of the empty set
is the bottom element (`sSup ∅ = ⊥`). Reuses Mathlib's `sSup_empty`. -/
alias ex_4_5_sSup := sSup_empty

/-- **Exercise 4.5** (§4.1, p.78). Dually, the meet of the empty set is the top
element (`sInf ∅ = ⊤`). Reuses Mathlib's `sInf_empty`. -/
alias ex_4_5_sInf := sInf_empty

/-- **Exercise 4.6** (§4.2, p.79). The fixed points of `f X = X ∪ {1,2}` on the
powerset `2^ℕ` are exactly the supersets of `{1,2}`: `X ∪ {1,2} = X ↔ {1,2} ⊆ X`.
(So besides `{1,2}` itself, e.g. `univ` is a fixed point.) -/
theorem ex_4_6 (X : Set ℕ) : X ∪ {1, 2} = X ↔ {1, 2} ⊆ X := Set.union_eq_left

/-- Exercise 4.7's variant of `f X = X ∪ {1,2}`: identical except it sends `{2}`
to `{1,2,3}`. -/
noncomputable def g47 : Set ℕ → Set ℕ :=
  fun X => if X = {2} then {1, 2, 3} else X ∪ {1, 2}

/-- **Exercise 4.7** (§4.2, p.79). The map `g` (= `f` but `{2} ↦ {1,2,3}`) is **not**
monotonic: `{2} ⊆ {1,2}` yet `g {2} = {1,2,3} ⊄ {1,2} = g {1,2}`. -/
theorem ex_4_7 : ¬ Monotone g47 := fun h => by
  have hsub : ({2} : Set ℕ) ⊆ ({1, 2} : Set ℕ) := by
    intro x hx; simp only [Set.mem_singleton_iff] at hx; subst hx; simp
  have e1 : g47 {2} = {1, 2, 3} := if_pos rfl
  have e2 : g47 ({1, 2} : Set ℕ) = ({1, 2} : Set ℕ) := by
    unfold g47
    rw [if_neg (by intro h2; rw [Set.ext_iff] at h2; simpa using (h2 1).mp (by simp))]
    exact Set.union_self _
  have hle := h hsub
  rw [e1, e2] at hle
  have h3 : (3 : ℕ) ∈ ({1, 2} : Set ℕ) := hle (by simp)
  simp at h3

/-- The monotone map `g X = (X ∩ {1}) ∪ {2}` on `Set (Fin 3)` (Exercise 4.9). -/
def g49 : Set (Fin 3) →o Set (Fin 3) where
  toFun X := (X ∩ {1}) ∪ {2}
  monotone' _ _ h := Set.union_subset_union_left _ (Set.inter_subset_inter_left _ h)

/-- **Exercise 4.9** (§4.2, p.83). The least fixed point of `g X = (X ∩ {1}) ∪ {2}`
is `{2}` (using Theorem 4.2: `g(∅) = {2}`, `g({2}) = {2}`). -/
theorem ex_4_9_lfp : OrderHom.lfp g49 = {2} := by
  apply le_antisymm
  · exact g49.lfp_le (Set.union_subset Set.inter_subset_left (le_refl _))
  · have h : ({2} : Set (Fin 3)) ⊆ g49 (OrderHom.lfp g49) := Set.subset_union_right
    rwa [OrderHom.map_lfp] at h

/-- **Exercise 4.9** (§4.2, p.83). The greatest fixed point of `g X = (X ∩ {1}) ∪ {2}`
is `{1, 2}` (`g({0,1,2}) = {1,2}`, `g({1,2}) = {1,2}`). -/
theorem ex_4_9_gfp : OrderHom.gfp g49 = {1, 2} := by
  apply le_antisymm
  · have h : g49 (OrderHom.gfp g49) ⊆ ({1, 2} : Set (Fin 3)) :=
      Set.union_subset (Set.inter_subset_right.trans (by intro x hx; simp_all))
        (by intro x hx; simp_all)
    rwa [OrderHom.map_gfp] at h
  · refine g49.le_gfp ?_
    show ({1, 2} : Set (Fin 3)) ⊆ (({1, 2} : Set (Fin 3)) ∩ {1}) ∪ {2}
    intro x hx
    fin_cases x <;> simp_all

open Classical in
/-- The witness map for Exercise 4.10(2) on the complete lattice `Set (Fin 3)`:
`f X = univ` once `{0,1} ⊆ X`, else `f X = X` (so `f` is identity below the join
`{0,1}` and jumps to the top on and above it). -/
noncomputable def f410 : Set (Fin 3) →o Set (Fin 3) where
  toFun X := if ({0, 1} : Set (Fin 3)) ⊆ X then Set.univ else X
  monotone' X Y hXY := by
    dsimp only
    by_cases hX : ({0, 1} : Set (Fin 3)) ⊆ X
    · rw [if_pos hX, if_pos (hX.trans hXY)]
    · rw [if_neg hX]
      by_cases hY : ({0, 1} : Set (Fin 3)) ⊆ Y
      · rw [if_pos hY]; exact le_top
      · rw [if_neg hY]; exact hXY

open Classical in
/-- **Exercise 4.10(2)** (§4.2, p.83). On the complete lattice `Set (Fin 3)`, the
monotone `f410` has `{0}` and `{1}` as fixed points, yet their join
`{0} ⊔ {1} = {0,1}` is **not** a fixed point (`f410 {0,1} = univ ≠ {0,1}`): the
join of two fixed points need not be a fixed point. -/
theorem ex_4_10_2 :
    ∃ x y : Set (Fin 3),
      f410 x = x ∧ f410 y = y ∧ f410 (x ⊔ y) ≠ x ⊔ y := by
  refine ⟨{0}, {1}, ?_, ?_, ?_⟩
  · -- f410 {0} = {0}: ¬ {0,1} ⊆ {0}
    show (if ({0, 1} : Set (Fin 3)) ⊆ {0} then Set.univ else {0}) = {0}
    rw [if_neg]
    intro h; have h1 : (1 : Fin 3) ∈ ({0} : Set (Fin 3)) := h (by simp)
    simp only [Set.mem_singleton_iff] at h1; exact absurd h1 (by decide)
  · -- f410 {1} = {1}: ¬ {0,1} ⊆ {1}
    show (if ({0, 1} : Set (Fin 3)) ⊆ {1} then Set.univ else {1}) = {1}
    rw [if_neg]
    intro h; have h0 : (0 : Fin 3) ∈ ({1} : Set (Fin 3)) := h (by simp)
    simp only [Set.mem_singleton_iff] at h0; exact absurd h0 (by decide)
  · -- {0} ⊔ {1} = {0,1}, and f410 {0,1} = univ ≠ {0,1}
    have hjoin : (({0} : Set (Fin 3)) ⊔ {1}) = {0, 1} := by
      ext z
      simp only [Set.sup_eq_union, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [hjoin]
    show (if ({0, 1} : Set (Fin 3)) ⊆ {0, 1} then Set.univ else {0, 1}) ≠ {0, 1}
    rw [if_pos subset_rfl]
    intro h
    have h2 : (2 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) := h ▸ Set.mem_univ 2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h2
    rcases h2 with h2 | h2 <;> exact absurd h2 (by decide)

/-- **Exercise 4.12** (§4.3, p.87). On the Example 3.7 LTS the iterative algorithm
gives `s ≁ t` (the largest bisimulation excludes the pair `(s,t)`): after
`s —a→ s₁ —b→ s₃` the dead `s₃` cannot match `t₁`'s repeated `b`. The library's
`ex_4_12_s_not_bisim_t`. -/
theorem ex_4_12 :
    ¬ LTS.Bisimilar DeepWiki.ReactiveSystems.e37
        DeepWiki.ReactiveSystems.E37S.s DeepWiki.ReactiveSystems.E37S.t :=
  DeepWiki.ReactiveSystems.ex_4_12_s_not_bisim_t

/-- **Exercise 4.11** (§4.3, p.86). The largest bisimulation over `P₁..P₅`
(`P₁=a.P₂`, `P₂=a.P₁`, `P₃=a.P₂+a.P₄`, `P₄=a.P₃+a.P₅`, `P₅=0`) identifies exactly
`P₁` and `P₂`; `P₃, P₄, P₅` are pairwise distinct and distinct from `P₁`. The
library's `ex_4_11`. -/
theorem ex_4_11 :
    LTS.Bisimilar DeepWiki.ReactiveSystems.lts411
        DeepWiki.ReactiveSystems.P411.p1 DeepWiki.ReactiveSystems.P411.p2 ∧
    ¬ LTS.Bisimilar DeepWiki.ReactiveSystems.lts411
        DeepWiki.ReactiveSystems.P411.p1 DeepWiki.ReactiveSystems.P411.p3 ∧
    ¬ LTS.Bisimilar DeepWiki.ReactiveSystems.lts411
        DeepWiki.ReactiveSystems.P411.p1 DeepWiki.ReactiveSystems.P411.p4 ∧
    ¬ LTS.Bisimilar DeepWiki.ReactiveSystems.lts411
        DeepWiki.ReactiveSystems.P411.p1 DeepWiki.ReactiveSystems.P411.p5 ∧
    ¬ LTS.Bisimilar DeepWiki.ReactiveSystems.lts411
        DeepWiki.ReactiveSystems.P411.p3 DeepWiki.ReactiveSystems.P411.p4 ∧
    ¬ LTS.Bisimilar DeepWiki.ReactiveSystems.lts411
        DeepWiki.ReactiveSystems.P411.p3 DeepWiki.ReactiveSystems.P411.p5 ∧
    ¬ LTS.Bisimilar DeepWiki.ReactiveSystems.lts411
        DeepWiki.ReactiveSystems.P411.p4 DeepWiki.ReactiveSystems.P411.p5 :=
  DeepWiki.ReactiveSystems.ex_4_11

/-- **Theorem 4.2** (§4.2, p.82). On a *finite* complete lattice, the least fixed
point of a monotone `f` is reached by finite iteration from `⊥`: `lfp f = fᵐ(⊥)`
for some `m` (the ascending chain `⊥ ≼ f⊥ ≼ f²⊥ ≼ ⋯` is eventually constant, and
its limit is the lfp). -/
theorem thm_4_2_lfp {D : Type*} [CompleteLattice D] [Finite D] (f : D →o D) :
    ∃ m, OrderHom.lfp f = f^[m] ⊥ := DeepWiki.ReactiveSystems.lfp_eq_iterate_bot f

/-- **Theorem 4.2** (§4.2, p.82). Dually, the greatest fixed point is reached by
finite iteration from `⊤`: `gfp f = fᴹ(⊤)` for some `M`. -/
theorem thm_4_2_gfp {D : Type*} [CompleteLattice D] [Finite D] (f : D →o D) :
    ∃ M, OrderHom.gfp f = f^[M] ⊤ := DeepWiki.ReactiveSystems.gfp_eq_iterate_top f

/-- **Exercise 4.15(1)** (§4.3, p.86). The weak (observational) bisimulation
functional `G`, whose post-fixed points are the weak bisimulations. The library's
`LTS.weakBisimFunctional`. -/
abbrev ex_4_15_functional := @LTS.weakBisimFunctional

/-- **Exercise 4.15(1)** (§4.3, p.86). Observational equivalence `≈` is the
greatest fixed point of the weak bisimulation functional `G` (the analogue of
`bisimilar_eq_gfp` for `~`). The library's `LTS.weaklyBisimilar_eq_gfp`. -/
theorem ex_4_15 {Proc Act : Type*} (L : LTS Proc Act) (tau : Act) :
    LTS.WeaklyBisimilar L tau = (LTS.weakBisimFunctional L tau).gfp :=
  LTS.weaklyBisimilar_eq_gfp

end DeepWiki.Rs
