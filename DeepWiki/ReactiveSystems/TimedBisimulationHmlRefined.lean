import DeepWiki.ReactiveSystems.TimedBisimulationHmlStrict
import DeepWiki.ReactiveSystems.TimedHmlClocks
import DeepWiki.ReactiveSystems.TimedRegions
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt

/-! # Toward the `√2` example's full-`Mt`-equivalence (Ex 12.12(3) / Prop 12.2) — partial
The `√2` TLTS states `(A,0)` and `(B,0)` are conjectured (book Ex 12.12(3)) to satisfy the same
*full* `Mt` formulae (timed Hennessy–Milner logic with formula clocks and integer guards) even
though they are not timed bisimilar (`not_timedBisimilar_sqrt2`, `TimedBisimulationHmlStrict`).
This file develops the machinery toward an `Mt`-bisimulation witness and discharges most of it,
but the full result is **open** here.

The device: convert the irrational boundary `√2` to an integer cut via the augmented clock
`w = process + (2 − √2)`, so `process < √2 ↔ w < 2`; then the candidate relation `Sq2Rel` is
ordinary region equivalence on `jointValW` (`w` at `none`, formula clocks at `some x`). Four of
the six `IsMtBisimulation` clauses are proved (`Sq2Rel.guard`/`reset`/`act_forth`/`act_back`,
seed `sq2Rel_seed`), and the *generic* delay is matched by the existing region time-successor
(`jointValW_delay_match`).

WHAT IS OPEN: the delay clause's boundary. `w` crosses integers at `process ∈ {√2−1, √2, √2+1, …}`,
so this region has *spurious* thin cuts away from `√2`; at the genuine boundary `process = √2`
(`A` a-disabled, `B` a-enabled — distinguished by `⟨a⟩tt`, so genuinely inequivalent there) the
static region match forces `B` to exactly `√2`, and `Sq2Rel` is not closed. Closing Ex 12.12(3)
needs a region cutting the process clock at `√2` *only* (single irrational cut, not periodic) plus
a coinductive bisimulation finer than any static region relation — genuine research-grade work.
The lemmas below are true regardless and are the reusable scaffold for that construction. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-! ### The boundary `√2` -/

/-- The boundary `√2`, as an `ℝ≥0`. -/
noncomputable def sqrt2NN : ℝ≥0 := (Real.sqrt 2).toNNReal

/-- `(sqrt2NN : ℝ) = √2` (since `√2 ≥ 0`). -/
@[simp] theorem coe_sqrt2NN : (sqrt2NN : ℝ) = Real.sqrt 2 :=
  Real.coe_toNNReal _ (Real.sqrt_nonneg 2)

/-- `√2` (read in `ℝ`) is irrational. -/
theorem irrational_sqrt2NN : Irrational (sqrt2NN : ℝ) := by
  rw [coe_sqrt2NN]; exact irrational_sqrt_two

/-- `1 < √2`. -/
theorem one_lt_sqrt2NN : (1 : ℝ) < sqrt2NN := by rw [coe_sqrt2NN]; exact Real.one_lt_sqrt_two

/-- `√2 < 2`. -/
theorem sqrt2NN_lt_two : (sqrt2NN : ℝ) < 2 := by
  rw [coe_sqrt2NN]; exact Real.sqrt_two_lt_three_halves.trans (by norm_num)

/-- `√2 ≠ 0`, hence `0 < √2`. -/
theorem zero_lt_sqrt2NN : (0 : ℝ≥0) < sqrt2NN := by
  rw [← NNReal.coe_lt_coe, NNReal.coe_zero, coe_sqrt2NN]
  exact lt_trans one_pos Real.one_lt_sqrt_two

/-! ### The joint valuation (process clock + formula clocks) -/

/-- Pack a process-clock value `t` and a formula valuation `u : Valuation D` into a joint
valuation over `Option D`: `none ↦ t` (process clock), `some x ↦ u x`. -/
def jointVal {D : Type*} (t : ℝ≥0) (u : Valuation D) : Valuation (Option D)
  | none => t
  | some x => u x

@[simp] theorem jointVal_none {D : Type*} (t : ℝ≥0) (u : Valuation D) :
    jointVal t u none = t := rfl

@[simp] theorem jointVal_some {D : Type*} (t : ℝ≥0) (u : Valuation D) (x : D) :
    jointVal t u (some x) = u x := rfl

/-- `jointVal` precomposed with `some` recovers the formula valuation. -/
theorem jointVal_comp_some {D : Type*} (t : ℝ≥0) (u : Valuation D) :
    (fun x => jointVal t u (some x)) = u := rfl

/-- Advancing a joint valuation by `δ` advances process and formula clocks together. -/
theorem jointVal_add {D : Type*} (t : ℝ≥0) (u : Valuation D) (δ : ℝ≥0) :
    (jointVal t u).add δ = jointVal (t + δ) (u.add δ) := by
  funext x; cases x <;> simp [jointVal, Valuation.add]

/-- Resetting a formula clock `some x` leaves the process clock `none` untouched. -/
theorem jointVal_reset_some {D : Type*} (t : ℝ≥0) (u : Valuation D) (x : D) :
    Valuation.reset {some x} (jointVal t u) = jointVal t (Valuation.reset {x} u) := by
  funext y
  cases y with
  | none => simp [Valuation.reset, jointVal]
  | some z =>
      simp only [Valuation.reset, jointVal, Set.mem_singleton_iff, Option.some.injEq]
      by_cases h : z = x <;> simp [h]

/-! ### The augmented clock: reducing the irrational `√2` cut to an integer cut

The crux device. The process boundary is the *irrational* `√2`, which integer-valued region
equivalence is blind to. Adding a virtual clock `w = process + (2 − √2)` converts it to an
**integer** cut: `process < √2 ⟺ w < 2`. Since `w` advances at rate 1 with delays (it is the
process clock shifted by a constant) and is untouched by formula-clock resets, the
`√2`-refined region is just the *ordinary* `RegionEqAll` on the valuation carrying `w` at
`none` and the formula clocks at `some x` — so the entire existing region stack (time
successor, reset, guard restriction) applies verbatim. -/

/-- `2 − √2`, a positive `ℝ≥0` shift. -/
noncomputable def twoSubSqrt2NN : ℝ≥0 := 2 - sqrt2NN

/-- `√2 ≤ 2` in `ℝ≥0`. -/
theorem sqrt2NN_le_two : sqrt2NN ≤ 2 := by
  rw [← NNReal.coe_le_coe]; push_cast; exact le_of_lt sqrt2NN_lt_two

/-- `(2 − √2 : ℝ≥0)` reads as `2 − √2` in `ℝ` (exact, since `√2 ≤ 2`). -/
@[simp] theorem coe_twoSubSqrt2NN : (twoSubSqrt2NN : ℝ) = 2 - Real.sqrt 2 := by
  rw [twoSubSqrt2NN, NNReal.coe_sub sqrt2NN_le_two, coe_sqrt2NN]; push_cast; ring

/-- The augmented joint valuation: `none ↦ w = T + (2 − √2)` (the process clock shifted so
its `√2`-crossing is an integer crossing), `some x ↦ u x` (formula clocks). -/
noncomputable def jointValW {D : Type*} (T : ℝ≥0) (u : Valuation D) : Valuation (Option D) :=
  jointVal (T + twoSubSqrt2NN) u

/-- The process clock crosses `√2` exactly when the augmented clock crosses integer `2`:
`T < √2 ↔ jointValW T u none < 2`. -/
theorem jointValW_none_lt_two_iff {D : Type*} (T : ℝ≥0) (u : Valuation D) :
    jointValW T u none < 2 ↔ T < sqrt2NN := by
  rw [jointValW, jointVal_none, ← NNReal.coe_lt_coe, ← NNReal.coe_lt_coe]
  push_cast [coe_twoSubSqrt2NN, coe_sqrt2NN]
  constructor <;> intro h <;> linarith

/-- `jointValW` precomposed with `some` recovers the formula valuation (for guard restriction). -/
theorem jointValW_comp_some {D : Type*} (T : ℝ≥0) (u : Valuation D) :
    (fun x => jointValW T u (some x)) = u := rfl

/-- Advancing the augmented joint valuation by `δ` advances the (shifted) process clock and
the formula clocks together — the key to reusing the ordinary region time-successor. -/
theorem jointValW_add {D : Type*} (T : ℝ≥0) (u : Valuation D) (δ : ℝ≥0) :
    (jointValW T u).add δ = jointValW (T + δ) (u.add δ) := by
  rw [jointValW, jointValW, jointVal_add]; rw [add_right_comm]

/-- Resetting a formula clock leaves the augmented process clock `none` untouched. -/
theorem jointValW_reset_some {D : Type*} (T : ℝ≥0) (u : Valuation D) (x : D) :
    Valuation.reset {some x} (jointValW T u) = jointValW T (Valuation.reset {x} u) := by
  rw [jointValW, jointValW, jointVal_reset_some]

/-- **Delay clause, validated.** A left delay `d` from a pair of `√2`-refined-region-equivalent
augmented states is matched by some right delay `d'` landing again `√2`-refined-region-equivalent
— and this is exactly the *existing* `regionEqAll_timeSuccessor` applied to the augmented
valuation (the irrational cut rides along inside `none`'s integer region). The `√2`-side is
preserved because it *is* `none`'s region (`jointValW_none_lt_two_iff`). -/
theorem jointValW_delay_match {D : Type*} [Fintype D] {TL TR : ℝ≥0} {u u' : Valuation D}
    (h : RegionEqAll (jointValW TL u) (jointValW TR u')) (d : ℝ≥0) :
    ∃ d', RegionEqAll (jointValW (TL + d) (u.add d)) (jointValW (TR + d') (u'.add d')) := by
  obtain ⟨e, he⟩ := regionEqAll_timeSuccessor h d
  rw [jointValW_add, jointValW_add] at he
  exact ⟨e, he⟩

/-! ### The `Mt`-bisimulation relation and its non-delay clauses

The relation for `sq2TLTS √2`: either both states are past the boundary (`a`-disabled, where
behaviour is duration-blind — the `pastRel` regime, needing only `RegionEqAll` on the formula
clocks), or the live shape `(A d) ~ (B e)` with `d, e < √2` and `√2`-refined-region-equivalent
augmented valuations. The guard, reset and action clauses of `IsMtBisimulation` are discharged
here; the delay clause (with its boundary subtlety) is assembled separately. -/

/-- The `Mt`-bisimulation relation for the `√2` example. -/
def Sq2Rel {D : Type*} (p : Sq2) (u : Valuation D) (q : Sq2) (u' : Valuation D) : Prop :=
  (aDisabled sqrt2NN p ∧ aDisabled sqrt2NN q ∧ RegionEqAll u u')
  ∨ (∃ d e : ℝ≥0, p = Sq2.A d ∧ q = Sq2.B e ∧ d < sqrt2NN ∧ e < sqrt2NN ∧
       RegionEqAll (jointValW d u) (jointValW e u'))

/-- Both disjuncts give `RegionEqAll` on the formula clocks (the live one via restriction
along `some`). -/
theorem Sq2Rel.regionEqAll {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2Rel p u q u') : RegionEqAll u u' := by
  rcases h with ⟨_, _, hr⟩ | ⟨d, e, _, _, _, _, hr⟩
  · exact hr
  · have hu := RegionEqAll.precomp (Option.some_injective D) hr
    rwa [jointValW_comp_some, jointValW_comp_some] at hu

/-- **Guard clause.** Related states satisfy the same formula-clock guards. -/
theorem Sq2Rel.guard {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2Rel p u q u') (g : ClockConstraint D) : satisfies u g ↔ satisfies u' g :=
  regionEqAll_satisfies h.regionEqAll g

/-- **Reset clause.** Resetting the same formula clock on both sides preserves the relation. -/
theorem Sq2Rel.reset {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2Rel p u q u') (x : D) :
    Sq2Rel p (Valuation.reset {x} u) q (Valuation.reset {x} u') := by
  rcases h with ⟨hpd, hqd, hr⟩ | ⟨d, e, hp, hq, hd, he, hr⟩
  · exact Or.inl ⟨hpd, hqd, hr.reset {x}⟩
  · refine Or.inr ⟨d, e, hp, hq, hd, he, ?_⟩
    rw [← jointValW_reset_some, ← jointValW_reset_some]
    exact hr.reset {some x}

/-- **Action clause (forth).** If `p` performs `a`, `q` matches it, landing related (both at
`End`, in the past disjunct). -/
theorem Sq2Rel.act_forth {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2Rel p u q u') (α : Sq2Act) (p' : Sq2)
    (hstep : (sq2TLTS sqrt2NN).act p α p') :
    ∃ q', (sq2TLTS sqrt2NN).act q α q' ∧ Sq2Rel p' u q' u' := by
  rw [sq2_act] at hstep
  rcases h with ⟨hpd, _, _⟩ | ⟨d, e, hp, hq, hd, he, hr⟩
  · exact absurd hstep (fun hs => hpd.no_act hs)
  · subst hp; subst hq
    cases hstep with
    | aA _ =>
        refine ⟨Sq2.End, sq2_act.mpr (Sq2Step.aB (le_of_lt he)), Or.inl ⟨trivial, trivial, ?_⟩⟩
        have hu := RegionEqAll.precomp (Option.some_injective D) hr
        rwa [jointValW_comp_some, jointValW_comp_some] at hu

/-- **Action clause (back).** If `q` performs `a`, `p` matches it, landing related. -/
theorem Sq2Rel.act_back {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2Rel p u q u') (α : Sq2Act) (q' : Sq2)
    (hstep : (sq2TLTS sqrt2NN).act q α q') :
    ∃ p', (sq2TLTS sqrt2NN).act p α p' ∧ Sq2Rel p' u q' u' := by
  rw [sq2_act] at hstep
  rcases h with ⟨_, hqd, _⟩ | ⟨d, e, hp, hq, hd, he, hr⟩
  · exact absurd hstep (fun hs => hqd.no_act hs)
  · subst hp; subst hq
    cases hstep with
    | aB _ =>
        refine ⟨Sq2.End, sq2_act.mpr (Sq2Step.aA hd), Or.inl ⟨trivial, trivial, ?_⟩⟩
        have hu := RegionEqAll.precomp (Option.some_injective D) hr
        rwa [jointValW_comp_some, jointValW_comp_some] at hu

/-- The seed: `(A 0)` and `(B 0)` at the all-zero formula valuation are related (live). -/
theorem sq2Rel_seed {D : Type*} :
    Sq2Rel (Sq2.A 0) (fun _ : D => 0) (Sq2.B 0) (fun _ : D => 0) :=
  Or.inr ⟨0, 0, rfl, rfl, zero_lt_sqrt2NN, zero_lt_sqrt2NN, RegionEqAll.refl _⟩

end DeepWiki.ReactiveSystems
