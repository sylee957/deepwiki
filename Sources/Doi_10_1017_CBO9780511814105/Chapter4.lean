import DeepWiki.ReactiveSystems.BisimulationFixedPoint
import DeepWiki.ReactiveSystems.BisimulationApprox
import Sources.Doi_10_1017_CBO9780511814105.Source
import Mathlib.Order.FixedPoints
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.ENNReal.Basic

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

/-- **Exercise 4.10(1)** (Kleene's fixed-point theorem, §4.2, p.83). For an
ω-(Scott-)continuous monotone map on a complete lattice, the least fixed point
is `⨆ₙ fⁿ(⊥)`. Reuses Mathlib's `fixedPoints.lfp_eq_sSup_iterate`. -/
alias ex_4_10_1 := fixedPoints.lfp_eq_sSup_iterate

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

/-- **Exercise 4.10(2)** (§4.2). The greatest fixed point is `⨅ₙ fⁿ(⊤)` (dual of
Kleene's theorem). Reuses Mathlib's `fixedPoints.gfp_eq_sInf_iterate`. -/
alias ex_4_10_2 := fixedPoints.gfp_eq_sInf_iterate

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

end DeepWiki.Rs
