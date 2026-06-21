import DeepWiki.ReactiveSystems.TimedBisimulationHmlStrict
import DeepWiki.ReactiveSystems.TimedHmlClocks
import DeepWiki.ReactiveSystems.TimedBisimulationHmlRefined

/-! # The `√2` states are `Mt`-distinguishable (an erratum to Proposition 12.2)

The book (Proposition 12.2, §12.3) claims the `√2`-example states `(A,0)` and `(B,0)` —
where `A d —a→ End` iff `d < √2` (the boundary **open**) and `B d —a→ End` iff `d ≤ √2`
(the boundary **closed**) — satisfy the *same* full-`Mt` formulae, so that timed
bisimilarity would be *strictly* finer than `Mt`-equivalence over TLTSs. The intuition
offered is that `Mt`'s integer clock guards cannot express "on delaying by exactly `√2`
an `a` is possible".

That intuition is **incorrect**, and this file gives a machine-checked counterexample:
a single `Mt` formula `F` with `(A,0) ⊨ F` and `(B,0) ⊭ F`. The device is that the
*outer* `∃∃` may delay by the **irrational** amount `δ₀ = √2 − 1` (delays are arbitrary
reals), after which a freshly reset clock `x` measures `process − δ₀`; the *integer* guard
`x = 1` then pins `process = δ₀ + 1 = √2` without ever naming `√2`. The two conjuncts of
`F` read off the boundary's open/closed nature:

`F = ∃∃ ( x in ( ∀∀((x ≥ 1) ∨ ⟨a⟩tt)  ∧  ∀∀((x ≠ 1) ∨ [a]ff) ) )`.

The first conjunct says "while `x < 1` an `a` stays possible"; the second says "at `x = 1`
no `a` is possible". For `A` both hold exactly at `δ₀ = √2 − 1` (`A √2` is `a`-disabled, so
`[a]ff` holds there); for `B` the two conjuncts have disjoint `δ₀`-ranges (`B √2` is still
`a`-enabled), so no outer delay satisfies both. Hence `(A,0)` and `(B,0)` are
`Mt`-distinguishable — refuting Proposition 12.2 (and the associated Exercise 12.12(3)
auxiliary claim), and confirming that the `Mt`-bisimulation those would require cannot
exist. The same `∃∃`-irrational-delay + integer-clock trick solves Exercise 12.15. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal
open TLTS

/-- `1 ≤ √2` in `ℝ≥0`. -/
theorem one_le_sqrt2NN : (1 : ℝ≥0) ≤ sqrt2NN := by
  rw [← NNReal.coe_le_coe]; push_cast; exact le_of_lt one_lt_sqrt2NN

/-- `(√2 − 1) + 1 = √2` in `ℝ≥0` (genuine subtraction since `1 ≤ √2`). -/
theorem sqrt2NN_sub_one_add_one : (sqrt2NN - 1) + 1 = sqrt2NN :=
  tsub_add_cancel_of_le one_le_sqrt2NN

/-- For the single formula clock `Unit`, resetting it zeroes the whole valuation. -/
theorem reset_unit_eq_zero (v : Valuation Unit) :
    Valuation.reset {()} v = fun _ => 0 := by
  funext x
  cases x
  simp [Valuation.reset]

/-- The distinguishing `Mt` formula
`F = ∃∃ ( x in ( ∀∀((x ≥ 1) ∨ ⟨a⟩tt)  ∧  ∀∀((x < 1 ∨ x > 1) ∨ [a]ff) ) )`. -/
def distinguishingFormula : Mt Sq2Act Unit :=
  .existsDelay (.reset ()
    (.and
      (.forallDelay (.or (.guard (.atom () .ge 1)) (.dia Sq2Act.a .tt)))
      (.forallDelay (.or (.or (.guard (.atom () .lt 1)) (.guard (.atom () .gt 1)))
        (.box Sq2Act.a .ff)))))

/-- `(A,0)` satisfies the distinguishing formula, via the outer delay `δ₀ = √2 − 1`. -/
theorem mtSat_A0_distinguishingFormula :
    MtSat (sq2TLTS sqrt2NN) (Sq2.A 0) (fun _ => 0) distinguishingFormula := by
  -- Outer `∃∃`: delay by `δ₀ = √2 − 1`, reaching `(A, δ₀)`; the reset zeroes the clock.
  refine ⟨sqrt2NN - 1, Sq2.A (0 + (sqrt2NN - 1)), Sq2Step.delA, ?_⟩
  simp only [TLTS.MtSat, reset_unit_eq_zero, Valuation.add_apply,
    zero_add, satisfies, Cmp.holds, Nat.cast_one, sq2_act, sq2_delay, and_true]
  refine ⟨?_, ?_⟩
  · -- conjunct 1: for every further delay `η`, either `η ≥ 1` or `A (δ₀+η)` can do `a`.
    intro η p'' hstep
    cases hstep
    rcases le_or_gt 1 η with hη | hη
    · exact Or.inl hη
    · refine Or.inr ⟨Sq2.End, Sq2Step.aA ?_⟩
      calc (sqrt2NN - 1) + η < (sqrt2NN - 1) + 1 := by gcongr
        _ = sqrt2NN := sqrt2NN_sub_one_add_one
  · -- conjunct 2: for every `η`, either `η ≠ 1` or `A (δ₀+η)` is `a`-disabled.
    intro η p'' hstep
    cases hstep
    rcases le_or_gt 1 η with hη | hη
    · -- `η ≥ 1`: `δ₀+η ≥ √2`, so `A (δ₀+η)` has no `a`-move ⇒ `[a]ff`.
      refine Or.inr ?_
      intro p3 hp3
      cases hp3 with
      | aA h =>
          have : sqrt2NN ≤ (sqrt2NN - 1) + η := by
            calc sqrt2NN = (sqrt2NN - 1) + 1 := sqrt2NN_sub_one_add_one.symm
              _ ≤ (sqrt2NN - 1) + η := by gcongr
          exact absurd h (not_lt.mpr this)
    · exact Or.inl (Or.inl hη)

/-- `(B,0)` does **not** satisfy the distinguishing formula: no outer delay makes both
conjuncts hold, because `B √2` is still `a`-enabled. -/
theorem not_mtSat_B0_distinguishingFormula :
    ¬ MtSat (sq2TLTS sqrt2NN) (Sq2.B 0) (fun _ => 0) distinguishingFormula := by
  rintro ⟨δ₀, p', hdel, hsat⟩
  rw [sq2_delay] at hdel
  cases hdel
  simp only [TLTS.MtSat, reset_unit_eq_zero, Valuation.add_apply,
    zero_add, satisfies, Cmp.holds, Nat.cast_one, sq2_act, sq2_delay, and_true] at hsat
  obtain ⟨hconj1, hconj2⟩ := hsat
  set δ : ℝ≥0 := δ₀ with hδ
  -- From conjunct 2 at `η = 1`: `B (δ+1)` must be `a`-disabled, i.e. `√2 < δ + 1`.
  have hBoundary : sqrt2NN < δ + 1 := by
    have h2 := hconj2 1 (Sq2.B (δ + 1)) Sq2Step.delB
    rcases h2 with (hlt | hgt) | hbox
    · exact absurd hlt (lt_irrefl 1)
    · exact absurd hgt (lt_irrefl 1)
    · by_contra hle
      exact hbox Sq2.End (Sq2Step.aB (not_lt.mp hle))
  -- Choose `η` with `η < 1` and `√2 < δ + η`, contradicting conjunct 1.
  set s : ℝ := (sqrt2NN : ℝ) with hs
  set d : ℝ := (δ : ℝ) with hd
  have hBoundary_r : s < d + 1 := by
    have := hBoundary
    rwa [← NNReal.coe_lt_coe, NNReal.coe_add, NNReal.coe_one] at this
  set M : ℝ := max 0 (s - d) with hM
  set r : ℝ := (M + 1) / 2 with hr
  have hM0 : 0 ≤ M := le_max_left _ _
  have hMsd : s - d ≤ M := le_max_right _ _
  have hM1 : M < 1 := by rw [hM]; exact max_lt one_pos (by linarith)
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hrs : s < d + r := by rw [hr]; linarith
  -- Package `η = r.toNNReal`.
  set η : ℝ≥0 := r.toNNReal with hη_def
  have hη_coe : (η : ℝ) = r := Real.coe_toNNReal r hr0
  have hη_lt1 : η < 1 := by rw [← NNReal.coe_lt_coe, hη_coe, NNReal.coe_one]; exact hr1
  have hδη : sqrt2NN < δ + η := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_add, hη_coe, ← hs, ← hd]; exact hrs
  -- Conjunct 1 at this `η`: either `η ≥ 1` (false) or `B (δ+η)` can do `a` (`δ+η ≤ √2`, false).
  have h1 := hconj1 η (Sq2.B (δ + η)) Sq2Step.delB
  rcases h1 with hge | ⟨p3, hp3⟩
  · have : (1 : ℝ≥0) ≤ η := hge
    exact absurd this (not_le.mpr hη_lt1)
  · cases hp3 with
    | aB hle => exact absurd hle (not_le.mpr hδη)

/-- **Refutation of Proposition 12.2 / Exercise 12.12(3).** In the `√2` TLTS the states
`(A,0)` and `(B,0)` are **not** `Mt`-equivalent: `distinguishingFormula` separates them at
the state level. So full-`Mt` equivalence does *not* hold for these states (and the
`Mt`-bisimulation the book's argument would need cannot exist). -/
theorem sq2_not_mtEquiv :
    ∃ F : Mt Sq2Act Unit,
      MtSatState (sq2TLTS sqrt2NN) (Sq2.A 0) F ∧
      ¬ MtSatState (sq2TLTS sqrt2NN) (Sq2.B 0) F :=
  ⟨distinguishingFormula, mtSat_A0_distinguishingFormula, not_mtSat_B0_distinguishingFormula⟩

end DeepWiki.ReactiveSystems
