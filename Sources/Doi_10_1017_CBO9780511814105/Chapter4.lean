import DeepWiki.ReactiveSystems.BisimulationFixedPoint
import Sources.Doi_10_1017_CBO9780511814105.Source
import Mathlib.Order.FixedPoints

/-! # Reactive Systems catalog — Chapter 4: Theory of fixed points and bisimulation
Book-numbered restatements for Chapter 4. The order-theoretic background
(§4.1–4.2) reuses Mathlib directly; §4.3 (bisimulation as a fixed point) is
discharged by the `DeepWiki.ReactiveSystems` library. -/

namespace DeepWiki.Rs

open DeepWiki.ReactiveSystems

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

/-- **Exercise 4.10(5)** (§4.2, p.84). The monotone self-maps of a complete
lattice, ordered pointwise, again form a complete lattice. -/
theorem ex_4_10_5 (D : Type*) [CompleteLattice D] : Nonempty (CompleteLattice (D →o D)) :=
  ⟨inferInstance⟩

end DeepWiki.Rs
