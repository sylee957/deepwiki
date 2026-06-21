import DeepWiki.ReactiveSystems.TimedSqrt2AsymRegion

/-! # The `√2` Mt-bisimulation, step 4c: the augmented relation and its non-delay clauses (Ex 12.12(3))
Assembles the asymmetric single-irrational-cut relation from the foundations. The live regime carries,
besides the formula-clock region equivalence and the `√2`-side, the **asymmetric crossing-value match**
`AsymMatch` on each clock's delay-invariant crossing-value `crossVal d v = v + (√2 − d)` (its value when
the process reaches `√2`) and on the process's own `crossVal d 0 = √2 − d`.

`AsymMatch c c' := ∀ m, (m < c ↔ m ≤ c')` is exactly "A (open threshold) and B (closed) agree on
a-availability at every integer clock value `m`" (`a_avail_iff_lt_crossing`); it forces `⌊c'⌋ = ⌊c⌋`
when `c ∉ ℤ` and `⌊c'⌋ = m−1` when `c = m` — B's crossing-value just below, placing B strictly past `√2`
at the double-coincidence.

This file proves the **reset, guard, action, and seed** clauses. The reset clause is the crux of the
design: resetting a clock sets its crossing-value to `√2 − d`, and the relation's separately-tracked
*process* match `AsymMatch (√2−d) (√2−e)` is exactly what re-supplies the crossing-value match — so the
match is preserved with no delay reasoning. The delay clause (standard time-successor + `√2`-side
window, the crossing-values auto-carried) is the remaining step. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- The crossing-value of a clock with value `v` at process `d`: its value when the process reaches
`√2` (delay-invariant, `clock_at_sqrt2_delay_invariant`). -/
noncomputable def crossVal (d v : ℝ≥0) : ℝ≥0 := v + (sqrt2NN - d)

/-- The asymmetric crossing-value match: A (open threshold `< √2`) and B (closed `≤ √2`) agree on
a-availability at every integer clock value `m`. Forces `⌊c'⌋ = ⌊c⌋` for `c ∉ ℤ`, and `⌊c'⌋ = m − 1`
for `c = m` (B's value just below). -/
def AsymMatch (c c' : ℝ≥0) : Prop := ∀ m : ℕ, ((m : ℝ≥0) < c ↔ (m : ℝ≥0) ≤ c')

/-- An integer cast never equals `√2`. -/
theorem natCast_ne_sqrt2NN (m : ℕ) : (m : ℝ≥0) ≠ sqrt2NN := by
  intro h
  exact irrational_sqrt2NN.ne_nat m (by rw [← h]; push_cast; ring)

/-- `AsymMatch √2 √2` holds (since `√2` is never an integer). -/
theorem asymMatch_sqrt2_self : AsymMatch sqrt2NN sqrt2NN := fun m =>
  ⟨le_of_lt, fun h => lt_of_le_of_ne h (natCast_ne_sqrt2NN m)⟩

/-- **The floor content of `AsymMatch`** (the heart of the straddle): B's crossing-value floor is at
most A's. Since `AsymMatch c c'` forces `⌊c'⌋ = ⌊c⌋` (for `c ∉ ℤ`) or `⌊c'⌋ = ⌊c⌋ − 1` (for `c ∈ ℤ`),
in both cases `⌊c'⌋ ≤ ⌊c⌋` — so wherever A's process reaches `√2` before a clock's next integer (a
crossing-value below that integer), B's does too. This is what makes the clocks-region window straddle
`√2` consistently between A and B. -/
theorem AsymMatch.floor_le {c c' : ℝ≥0} (h : AsymMatch c c') : ⌊c'⌋₊ ≤ ⌊c⌋₊ := by
  have h1 : ((⌊c'⌋₊ : ℕ) : ℝ≥0) ≤ c' := Nat.floor_le zero_le
  have h2 : ((⌊c'⌋₊ : ℕ) : ℝ≥0) < c := (h ⌊c'⌋₊).mpr h1
  exact Nat.le_floor (le_of_lt h2)

/-- **The floor-level straddle (one direction).** If A's crossing-value is below clock `y`'s next
integer (A's process reaches `√2` before clock `y` crosses), then so is B's — by `AsymMatch.floor_le`
plus the clocks-region floor match `⌊u y⌋ = ⌊u' y⌋`. This is what shows B's clocks-region delay window
reaches `√2` whenever A's does, the key to the delay clause's placement. -/
theorem crossVal_lt_next_of {D : Type*} {d e : ℝ≥0} {u u' : Valuation D} {y : D}
    (h : AsymMatch (crossVal d (u y)) (crossVal e (u' y)))
    (hfl : ⌊u y⌋₊ = ⌊u' y⌋₊) (hA : crossVal d (u y) < (⌊u y⌋₊ : ℝ≥0) + 1) :
    crossVal e (u' y) < (⌊u' y⌋₊ : ℝ≥0) + 1 := by
  have hAfloor : ⌊crossVal d (u y)⌋₊ ≤ ⌊u y⌋₊ :=
    Nat.lt_succ_iff.mp ((Nat.floor_lt zero_le).mpr (by exact_mod_cast hA))
  have hBfloor : ⌊crossVal e (u' y)⌋₊ ≤ ⌊u' y⌋₊ := hfl ▸ le_trans h.floor_le hAfloor
  calc crossVal e (u' y) < (⌊crossVal e (u' y)⌋₊ : ℝ≥0) + 1 := Nat.lt_floor_add_one _
    _ ≤ (⌊u' y⌋₊ : ℝ≥0) + 1 := by gcongr

/-- **The process τ-match collapses to a single threshold in the live regime.** Because `√2 − e ≥ 0`
always (truncated subtraction) the `m = 0` clause is vacuous, and because `√2 − d < 2` the `m ≥ 2`
clauses are vacuous; so `AsymMatch (√2−d) (√2−e)` is just the `m = 1` condition — the `√2−1` cut
`d + 1 < √2 ↔ e + 1 ≤ √2`. -/
theorem asymMatch_tau_live {d e : ℝ≥0} (hd : d < sqrt2NN) (he : e ≤ sqrt2NN) :
    AsymMatch (sqrt2NN - d) (sqrt2NN - e) ↔ (d + 1 < sqrt2NN ↔ e + 1 ≤ sqrt2NN) := by
  have e1 : ((1 : ℝ≥0) < sqrt2NN - d) ↔ (d + 1 < sqrt2NN) := by
    rw [← NNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_sub (le_of_lt hd), NNReal.coe_add]
    push_cast; constructor <;> intro <;> linarith
  have e2 : ((1 : ℝ≥0) ≤ sqrt2NN - e) ↔ (e + 1 ≤ sqrt2NN) := by
    rw [← NNReal.coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_sub he, NNReal.coe_add]
    push_cast; constructor <;> intro <;> linarith
  constructor
  · intro h
    have h1 := h 1; rw [Nat.cast_one, e1, e2] at h1; exact h1
  · intro h m
    match m with
    | 0 => rw [Nat.cast_zero]; exact ⟨fun _ => zero_le, fun _ => tsub_pos_of_lt hd⟩
    | 1 => rw [Nat.cast_one, e1, e2]; exact h
    | (n + 2) =>
      have hslt : sqrt2NN < ((n + 2 : ℕ) : ℝ≥0) := by
        rw [← NNReal.coe_lt_coe]; push_cast
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith [sqrt2NN_lt_two]
      exact iff_of_false
        (not_lt.mpr (le_of_lt (lt_of_le_of_lt tsub_le_self hslt)))
        (not_le.mpr (lt_of_le_of_lt tsub_le_self hslt))

/-- `crossVal d 0 = √2 − d`. -/
@[simp] theorem crossVal_zero (d : ℝ≥0) : crossVal d 0 = sqrt2NN - d := by
  simp [crossVal]

/-- **The √2-cut sits at an irrational fractional value.** Within the integer region `(1,2)`,
`p < √2 ⟺ fracPart p < fracPart √2 = √2 − 1`, and `√2 − 1` is *irrational*. So the cut the
construction needs is at an irrational frac — which is exactly why standard integer-frac region theory
does not cover it, and the single-irrational-cut region (with open/closed at this point) is genuinely
new region machinery. -/
theorem irrational_fracPart_sqrt2NN : Irrational (fracPart sqrt2NN) := by
  rw [fracPart_sqrt2NN, ← coe_sqrt2NN]
  simpa using irrational_sqrt2NN.sub_natCast 1

/-- **Process past `√2` ⟺ clock past its crossing-value.** For any clock value `v`, the process (at
`d ≤ √2`) is past `√2` after a delay `δ` exactly when `v`'s post-delay value `v + δ` is past its
crossing-value `crossVal d v`. This reduces the (process-level) `√2`-side condition to a clock-level
comparison, which the clocks-region match and the crossing-value match control. -/
theorem process_past_iff_clock_past_cross {d δ : ℝ≥0} (v : ℝ≥0) (hd : d ≤ sqrt2NN) :
    sqrt2NN < d + δ ↔ crossVal d v < v + δ := by
  rw [crossVal, add_lt_add_iff_left, ← NNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_sub hd,
    NNReal.coe_add]
  constructor <;> intro <;> linarith

/-- Dually, the process is at-or-below `√2` (`B`'s closed side) iff `v + δ ≤ crossVal d v`. -/
theorem process_le_iff_clock_le_cross {d δ : ℝ≥0} (v : ℝ≥0) (hd : d ≤ sqrt2NN) :
    d + δ ≤ sqrt2NN ↔ v + δ ≤ crossVal d v := by
  rw [crossVal, add_le_add_iff_left, ← NNReal.coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_sub hd,
    NNReal.coe_add]
  constructor <;> intro <;> linarith

/-- The **crossing-value valuation** (clock crossings only): `y ↦ u y + (√2 − d)`, the value clock `y`
holds when the process reaches `√2`. This is the delay-invariant object; the process's own τ = `√2 − d`
is *not* invariant and is tracked separately. -/
noncomputable def cv {D : Type*} (d : ℝ≥0) (u : Valuation D) : Valuation D := fun y => u y + (sqrt2NN - d)

@[simp] theorem cv_apply {D : Type*} (d : ℝ≥0) (u : Valuation D) (y : D) :
    cv d u y = u y + (sqrt2NN - d) := rfl

/-- **The crossing-value valuation is delay-invariant** (for live delays `d + δ ≤ √2`): advancing the
process and all clocks together leaves every clock's `√2`-crossing value unchanged. This is what makes
the crossing-value region match auto-preserved under delay — the structural key to the construction. -/
theorem cv_delay_invariant {D : Type*} {d δ : ℝ≥0} {u : Valuation D} (h : d + δ ≤ sqrt2NN) :
    cv (d + δ) (u.add δ) = cv d u := by
  funext y
  simp only [cv_apply, Valuation.add_apply]
  exact TLTS.clock_at_sqrt2_delay_invariant h

/-- **The crossing-value match is auto-preserved under a live delay.** Since both crossing-value
valuations are delay-invariant (for `d+δ ≤ √2`, `e+δ' ≤ √2`), the per-clock `AsymMatch` carries through
unchanged — the delay clause never has to re-establish the crossing match, only the clocks region and the
process side. -/
theorem asymMatch_cv_delay {D : Type*} {d δ e δ' : ℝ≥0} {u u' : Valuation D}
    (h : ∀ y, AsymMatch (cv d u y) (cv e u' y))
    (hd : d + δ ≤ sqrt2NN) (he : e + δ' ≤ sqrt2NN) :
    ∀ y, AsymMatch (cv (d + δ) (u.add δ) y) (cv (e + δ') (u'.add δ') y) := by
  rw [cv_delay_invariant hd, cv_delay_invariant he]; exact h

/-- **The coincidence is past √2 — no asymmetric region needed.** When the symmetric region match
forces B's clock `y` to the integer `m` (because A's crossing-value `cv d u y = m` is an integer, A's
coincidence), `AsymMatch` gives `cv e u' y < m`, which *exactly* means B's process is strictly past `√2`
(`process_past_iff_clock_past_cross`). So B's clock sits on the integer (matching A's frac-0) while B's
process is past `√2` — the clock-frac match and the √2-side are decoupled through the reset offset, and
the standard symmetric region tools suffice. -/
theorem coincidence_past {D : Type*} {e δ' : ℝ≥0} {u' : Valuation D} {y : D} {m : ℕ}
    (hcv : AsymMatch ((m : ℝ≥0)) (cv e u' y)) (hclk : u' y + δ' = (m : ℝ≥0))
    (he : e ≤ sqrt2NN) : sqrt2NN < e + δ' := by
  have hlt : cv e u' y < (m : ℝ≥0) := not_le.mp (fun h => absurd ((hcv m).mpr h) (lt_irrefl _))
  rw [← hclk] at hlt
  rw [process_past_iff_clock_past_cross (u' y) he]
  exact hlt

/-- **The dual: a live coincidence stays at-or-below √2.** When the symmetric region match forces B's
clock `y` to integer `m` and A's crossing-value is strictly above `m` (A still live, `m < cv d u y`),
`AsymMatch` gives `m ≤ cv e u' y`, so B's process is `≤ √2` (B stays live). Companion to
`coincidence_past`. -/
theorem coincidence_live {D : Type*} {e δ' : ℝ≥0} {u' : Valuation D} {y : D} {m : ℕ} {cd : ℝ≥0}
    (hcv : AsymMatch cd (cv e u' y)) (hm : (m : ℝ≥0) < cd) (hclk : u' y + δ' = (m : ℝ≥0))
    (he : e ≤ sqrt2NN) : e + δ' ≤ sqrt2NN := by
  have hle : (m : ℝ≥0) ≤ cv e u' y := (hcv m).mp hm
  rw [process_le_iff_clock_le_cross (u' y) he, hclk]
  exact hle

/-- **Controlled small advance.** Strengthening of `regionEqAll_exists_add_small`: when no clock of `W`
sits on an integer and a real gap `g` is below every clock's distance-to-next-integer (`g < 1 − fracPart
(W x)`), there is an advance `ε > g` landing in a region-equivalent valuation. Used for the delay-clause
nudge: `g = √2 − (e + δ')` (the gap to push B past `√2`) is below each distance by `AsymMatch.floor_le`. -/
theorem regionEqAll_exists_add_above {D : Type*} [Fintype D] (W : Valuation D)
    (hno : ∀ x, fracPart (W x) ≠ 0) (g : ℝ) (hg : ∀ x, g < 1 - fracPart (W x)) :
    ∃ ε : ℝ≥0, g < (ε : ℝ) ∧ RegionEqAll W (W.add ε) := by
  rcases isEmpty_or_nonempty D with hD | hD
  · refine ⟨(max g 0).toNNReal + 1, ?_, regionEqAll_add_small W hno (by positivity) (fun x => (hD.false x).elim)⟩
    have : (0 : ℝ) ≤ max g 0 := le_max_right _ _
    push_cast [Real.coe_toNNReal _ this]
    calc g ≤ max g 0 := le_max_left _ _
      _ < max g 0 + 1 := by linarith
  · obtain ⟨x₀, -, hx₀⟩ := Finset.exists_min_image Finset.univ
      (fun x => (1 : ℝ) - fracPart (W x)) Finset.univ_nonempty
    set b := (1 : ℝ) - fracPart (W x₀) with hb
    have hgb : g < b := hg x₀
    have hb0 : 0 < b := by have := fracPart_lt_one (W x₀); rw [hb]; linarith
    have hlo : max g 0 < b := max_lt hgb hb0
    refine ⟨((max g 0 + b) / 2).toNNReal, ?_, regionEqAll_add_small W hno ?_ ?_⟩
    · rw [Real.coe_toNNReal _ (by have := le_max_right g 0; linarith)]
      calc g ≤ max g 0 := le_max_left _ _
        _ < (max g 0 + b) / 2 := by linarith
    · rw [Real.toNNReal_pos]; have := le_max_right g 0; linarith
    · intro x
      rw [Real.coe_toNNReal _ (by have := le_max_right g 0; linarith)]
      have hxle : b ≤ 1 - fracPart (W x) := by rw [hb]; exact hx₀ x (Finset.mem_univ x)
      linarith

/-- `fracPart` as value minus floor (real-valued). -/
theorem fracPart_eq_sub_floor (v : ℝ≥0) : fracPart v = (v : ℝ) - ((⌊v⌋₊ : ℝ≥0) : ℝ) := by
  have hbridge : (((⌊v⌋₊ : ℝ≥0)) : ℝ) = (⌊(v : ℝ)⌋ : ℝ) := by
    have e1 : ((⌊v⌋₊ : ℝ≥0) : ℝ) = (⌊(v : ℝ)⌋₊ : ℝ) := by push_cast; congr 1
    have e2 : ((⌊(v : ℝ)⌋₊ : ℤ) : ℝ) = (⌊(v : ℝ)⌋ : ℝ) := by
      rw [Int.natCast_floor_eq_floor v.coe_nonneg]
    rw [e1]; push_cast at e2 ⊢; exact e2
  unfold fracPart; rw [Int.fract, hbridge]

/-- Integer parts (`⌊·⌋₊`) agree under region equivalence: at an arbitrarily large `cmax` the clamped
floor `regionFloor` is the bare floor. -/
theorem regionEqAll_floor_eq {D : Type*} {V V' : Valuation D} (h : RegionEqAll V V') (x : D) :
    ⌊V x⌋₊ = ⌊V' x⌋₊ := by
  obtain ⟨h1, _, _⟩ := h (fun y => ⌊V y⌋₊ + ⌊V' y⌋₊ + 1)
  have hVx : V x ≤ ((⌊V x⌋₊ + ⌊V' x⌋₊ + 1 : ℕ) : ℝ≥0) := by
    refine le_of_lt (lt_of_lt_of_le (Nat.lt_floor_add_one (V x)) ?_)
    exact_mod_cast (Nat.le_add_right (⌊V x⌋₊ + 1) (⌊V' x⌋₊)).trans_eq (by ring)
  have hV'x : V' x ≤ ((⌊V x⌋₊ + ⌊V' x⌋₊ + 1 : ℕ) : ℝ≥0) := by
    refine le_of_lt (lt_of_lt_of_le (Nat.lt_floor_add_one (V' x)) ?_)
    exact_mod_cast (Nat.le_add_left (⌊V' x⌋₊ + 1) (⌊V x⌋₊)).trans_eq (by ring)
  have hf := h1 x
  unfold regionFloor at hf
  rw [if_pos hVx, if_pos hV'x] at hf
  exact hf

namespace TLTS

/-- The live regime's coupling: formula-clock region equivalence, the `√2`-side (open/closed), the
process crossing-value match, and the per-clock crossing-value match. -/
def Sq2FRel {D : Type*} (d : ℝ≥0) (u : Valuation D) (e : ℝ≥0) (u' : Valuation D) : Prop :=
  RegionEqAll u u' ∧ d < sqrt2NN ∧ e ≤ sqrt2NN
    ∧ AsymMatch (crossVal d 0) (crossVal e 0)
    ∧ ∀ y, AsymMatch (crossVal d (u y)) (crossVal e (u' y))

/-- The augmented `√2` relation: past regime (both `a`-disabled, formula clocks region-equivalent) or
live regime `(A d) ~ (B e)` with the `Sq2FRel` coupling. -/
def Sq2FullRel {D : Type*} (p : Sq2) (u : Valuation D) (q : Sq2) (u' : Valuation D) : Prop :=
  (aDisabled sqrt2NN p ∧ aDisabled sqrt2NN q ∧ RegionEqAll u u')
  ∨ (∃ d e : ℝ≥0, p = Sq2.A d ∧ q = Sq2.B e ∧ Sq2FRel d u e u')

/-- Both regimes give region-equivalent formula clocks. -/
theorem Sq2FullRel.regionEqAll {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2FullRel p u q u') : RegionEqAll u u' := by
  rcases h with ⟨_, _, hr⟩ | ⟨_, _, _, _, hr, _⟩ <;> exact hr

/-- **Guard clause.** -/
theorem Sq2FullRel.guard {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2FullRel p u q u') (g : ClockConstraint D) : satisfies u g ↔ satisfies u' g :=
  regionEqAll_satisfies h.regionEqAll g

/-- **Reset clause.** Resetting clock `x` preserves the relation: the reset clock's crossing-value
becomes `√2 − d`, supplied by the process match; the others are unchanged. -/
theorem Sq2FullRel.reset {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2FullRel p u q u') (x : D) :
    Sq2FullRel p (Valuation.reset {x} u) q (Valuation.reset {x} u') := by
  rcases h with ⟨hpd, hqd, hr⟩ | ⟨d, e, hp, hq, hr, hd, he, hτ, hcross⟩
  · exact Or.inl ⟨hpd, hqd, hr.reset {x}⟩
  · refine Or.inr ⟨d, e, hp, hq, hr.reset {x}, hd, he, hτ, fun y => ?_⟩
    by_cases hxy : y = x
    · subst hxy
      have hu : Valuation.reset {y} u y = 0 := Valuation.reset_mem (Set.mem_singleton y) u
      have hu' : Valuation.reset {y} u' y = 0 := Valuation.reset_mem (Set.mem_singleton y) u'
      rw [hu, hu']; exact hτ
    · have hu : Valuation.reset {x} u y = u y := by
        simp [Valuation.reset, Set.mem_singleton_iff, hxy]
      have hu' : Valuation.reset {x} u' y = u' y := by
        simp [Valuation.reset, Set.mem_singleton_iff, hxy]
      rw [hu, hu']; exact hcross y

/-- **Action clause (forth).** -/
theorem Sq2FullRel.act_forth {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2FullRel p u q u') (α : Sq2Act) (p' : Sq2)
    (hstep : (sq2TLTS sqrt2NN).act p α p') :
    ∃ q', (sq2TLTS sqrt2NN).act q α q' ∧ Sq2FullRel p' u q' u' := by
  rw [sq2_act] at hstep
  rcases h with ⟨hpd, _, _⟩ | ⟨d, e, hp, hq, hr, hd, he, _, _⟩
  · exact absurd hstep (fun hs => hpd.no_act hs)
  · subst hp; subst hq
    cases hstep with
    | aA _ => exact ⟨Sq2.End, sq2_act.mpr (Sq2Step.aB he), Or.inl ⟨trivial, trivial, hr⟩⟩

/-- **Action clause (back).** -/
theorem Sq2FullRel.act_back {D : Type*} {p q : Sq2} {u u' : Valuation D}
    (h : Sq2FullRel p u q u') (α : Sq2Act) (q' : Sq2)
    (hstep : (sq2TLTS sqrt2NN).act q α q') :
    ∃ p', (sq2TLTS sqrt2NN).act p α p' ∧ Sq2FullRel p' u q' u' := by
  rw [sq2_act] at hstep
  rcases h with ⟨_, hqd, _⟩ | ⟨d, e, hp, hq, hr, hd, he, _, _⟩
  · exact absurd hstep (fun hs => hqd.no_act hs)
  · subst hp; subst hq
    cases hstep with
    | aB _ => exact ⟨Sq2.End, sq2_act.mpr (Sq2Step.aA hd), Or.inl ⟨trivial, trivial, hr⟩⟩

/-- **Delay clause, past regime.** Both `a`-disabled: the formula-clock region time-successor matches a
left delay by a right delay, landing again `a`-disabled and region-equivalent. -/
theorem Sq2FullRel.delay_past {D : Type*} [Fintype D] {p q : Sq2} {u u' : Valuation D}
    (hpd : aDisabled sqrt2NN p) (hqd : aDisabled sqrt2NN q) (hr : RegionEqAll u u')
    (d : ℝ≥0) (p' : Sq2) (hstep : (sq2TLTS sqrt2NN).delay p d p') :
    ∃ d' q', (sq2TLTS sqrt2NN).delay q d' q' ∧ Sq2FullRel p' (u.add d) q' (u'.add d') := by
  rw [sq2_delay] at hstep
  obtain ⟨d', hr'⟩ := regionEqAll_timeSuccessor hr d
  obtain ⟨q', hqstep, hq'd⟩ := hqd.delay_succ d'
  exact ⟨d', q', sq2_delay.mpr hqstep, Or.inl ⟨hpd.delay_pres hstep, hq'd, hr'⟩⟩

/-- The per-clock crossing-values are **auto-carried** under a live delay (`d + δ ≤ √2`): the
crossing-value match needs no re-establishment, only the process τ-match and the clocks region do
(`clock_at_sqrt2_delay_invariant`). -/
theorem crossVal_live_invariant {d δ v : ℝ≥0} (h : d + δ ≤ sqrt2NN) :
    crossVal (d + δ) (v + δ) = crossVal d v :=
  clock_at_sqrt2_delay_invariant h

/-- **Delay clause, exact crossing at a coincidence** (the breakthrough case, previously thought to need
asymmetric region theory). When A delays exactly to `√2` (`d+δ = √2`) and some clock `y` coincides
(`cv d u y = m ∈ ℤ`), the symmetric region time-successor forces B's clock `y` to the integer `m`
(`regionEqAll_satisfies` on `atom y eq m`), and then `coincidence_past` puts B's process strictly past
`√2` — so both land `a`-disabled (the past regime), via standard symmetric region tools. -/
theorem Sq2FullRel.delay_exact_coincidence {D : Type*} [Fintype D] {d e : ℝ≥0} {u u' : Valuation D}
    (hr : RegionEqAll u u') (he : e ≤ sqrt2NN) (hcross : ∀ y, AsymMatch (cv d u y) (cv e u' y))
    (δ : ℝ≥0) (hδ : d + δ = sqrt2NN) (y : D) (m : ℕ) (hcoinc : cv d u y = (m : ℝ≥0)) :
    ∃ δ' q', (sq2TLTS sqrt2NN).delay (Sq2.B e) δ' q' ∧
      Sq2FullRel (Sq2.A (d + δ)) (u.add δ) q' (u'.add δ') := by
  obtain ⟨δ', hr'⟩ := regionEqAll_timeSuccessor hr δ
  have hδeq : δ = sqrt2NN - d := by rw [← hδ, add_tsub_cancel_left]
  have huy : (u.add δ) y = (m : ℝ≥0) := by
    rw [Valuation.add_apply, hδeq, ← cv_apply, hcoinc]
  have huy' : (u'.add δ') y = (m : ℝ≥0) := by
    have hs := regionEqAll_satisfies hr' (ClockConstraint.atom y Cmp.eq m)
    simp only [satisfies, Cmp.holds] at hs
    exact hs.mp huy
  have hpast : sqrt2NN < e + δ' :=
    coincidence_past (hcoinc ▸ hcross y) (by rw [← huy']; rfl) he
  exact ⟨δ', Sq2.B (e + δ'), sq2_delay.mpr Sq2Step.delB,
    Or.inl ⟨le_of_eq hδ.symm, hpast, hr'⟩⟩

/-- **Delay clause, crossing regime** (`√2 ≤ d + δ`): the general past landing. The formula-clock
region time-successor `δ'` is taken; if B is already past `√2` we are done, otherwise no clock sits on an
integer (else `coincidence_past` would put B past `√2`), so a controlled nudge `regionEqAll_exists_add_above`
advances B strictly past `√2` while preserving the region — the nudge gap `√2 − (e+δ')` is below every
clock's distance-to-next-integer by `AsymMatch.floor_le` and the clocks-region floor match. Subsumes
`delay_exact_coincidence`; needs no asymmetric region. -/
theorem Sq2FullRel.delay_cross {D : Type*} [Fintype D] {d e : ℝ≥0} {u u' : Valuation D}
    (hr : RegionEqAll u u') (he : e ≤ sqrt2NN)
    (hcross : ∀ y, AsymMatch (crossVal d (u y)) (crossVal e (u' y)))
    (δ : ℝ≥0) (hδ : sqrt2NN ≤ d + δ) :
    ∃ δ' q', (sq2TLTS sqrt2NN).delay (Sq2.B e) δ' q' ∧
      Sq2FullRel (Sq2.A (d + δ)) (u.add δ) q' (u'.add δ') := by
  obtain ⟨δ', hr'⟩ := regionEqAll_timeSuccessor hr δ
  by_cases hpast : sqrt2NN < e + δ'
  · exact ⟨δ', Sq2.B (e + δ'), sq2_delay.mpr Sq2Step.delB, Or.inl ⟨hδ, hpast, hr'⟩⟩
  · rw [not_lt] at hpast
    -- No clock of `u'.add δ'` sits on an integer (else `coincidence_past` contradicts `hpast`).
    have hno : ∀ z, fracPart ((u'.add δ') z) ≠ 0 := by
      intro z hzero
      set m := ⌊(u'.add δ') z⌋₊ with hm
      have hmval : (m : ℝ≥0) = (u'.add δ') z := (fracPart_eq_zero_iff _).mp hzero
      have huval : (u.add δ) z = (m : ℝ≥0) := by
        have hs := regionEqAll_satisfies hr' (ClockConstraint.atom z Cmp.eq m)
        simp only [satisfies, Cmp.holds] at hs
        exact hs.mpr hmval.symm
      have hAle : crossVal d (u z) ≤ (m : ℝ≥0) := by
        rw [← huval, crossVal, Valuation.add_apply, add_le_add_iff_left, tsub_le_iff_right, add_comm]
        exact hδ
      have hElt : crossVal e (u' z) < (m : ℝ≥0) :=
        not_le.mp (fun hle => absurd ((hcross z m).mpr hle) (not_lt.mpr hAle))
      have hclk : u' z + δ' = (m : ℝ≥0) := by rw [← Valuation.add_apply]; exact hmval.symm
      have : sqrt2NN < e + δ' := by
        rw [process_past_iff_clock_past_cross (u' z) he, hclk]; exact hElt
      exact absurd this (not_lt.mpr hpast)
    -- The nudge gap is below every clock's distance to its next integer.
    have hgbound : ∀ z, (sqrt2NN : ℝ) - (e : ℝ) - (δ' : ℝ) < 1 - fracPart ((u'.add δ') z) := by
      intro z
      have hfeq : ⌊(u.add δ) z⌋₊ = ⌊(u'.add δ') z⌋₊ := regionEqAll_floor_eq hr' z
      have hAle : crossVal d (u z) ≤ (u.add δ) z := by
        rw [crossVal, Valuation.add_apply, add_le_add_iff_left, tsub_le_iff_right, add_comm]; exact hδ
      have hf2 : ⌊crossVal e (u' z)⌋₊ ≤ ⌊(u'.add δ') z⌋₊ := by
        rw [← hfeq]; exact ((hcross z).floor_le).trans (Nat.floor_mono hAle)
      have hlt : crossVal e (u' z) < (⌊(u'.add δ') z⌋₊ : ℝ≥0) + 1 :=
        lt_of_lt_of_le (Nat.lt_floor_add_one _) (by exact_mod_cast Nat.add_le_add_right hf2 1)
      have hltR : (crossVal e (u' z) : ℝ) < ((⌊(u'.add δ') z⌋₊ : ℝ≥0) : ℝ) + 1 := by exact_mod_cast hlt
      have hcvR : (crossVal e (u' z) : ℝ) = (u' z : ℝ) + (sqrt2NN : ℝ) - (e : ℝ) := by
        rw [crossVal]; push_cast [NNReal.coe_sub he]; ring
      have haddR : ((u'.add δ') z : ℝ) = (u' z : ℝ) + (δ' : ℝ) := by
        rw [Valuation.add_apply]; push_cast; ring
      rw [fracPart_eq_sub_floor, haddR]; linarith [hltR, hcvR]
    obtain ⟨ε, hεg, hreg⟩ :=
      regionEqAll_exists_add_above (u'.add δ') hno ((sqrt2NN : ℝ) - (e : ℝ) - (δ' : ℝ)) hgbound
    have hadd : (u'.add δ').add ε = u'.add (δ' + ε) := by
      funext z; simp only [Valuation.add_apply]; ring
    have hrf : RegionEqAll (u.add δ) (u'.add (δ' + ε)) := by rw [← hadd]; exact hr'.trans hreg
    have hgt : sqrt2NN < e + (δ' + ε) := by
      rw [← NNReal.coe_lt_coe]; push_cast; linarith [hεg]
    exact ⟨δ' + ε, Sq2.B (e + (δ' + ε)), sq2_delay.mpr Sq2Step.delB, Or.inl ⟨hδ, hgt, hrf⟩⟩

/-- The seed: `(A 0) ~ (B 0)` at the all-zero formula valuation. -/
theorem sq2FullRel_seed {D : Type*} :
    Sq2FullRel (Sq2.A 0) (fun _ : D => 0) (Sq2.B 0) (fun _ : D => 0) := by
  refine Or.inr ⟨0, 0, rfl, rfl, RegionEqAll.refl _, zero_lt_sqrt2NN, le_of_lt zero_lt_sqrt2NN, ?_, ?_⟩
  · simp only [crossVal_zero, tsub_zero]; exact asymMatch_sqrt2_self
  · intro _; simp only [crossVal, tsub_zero, zero_add]; exact asymMatch_sqrt2_self

end TLTS

end DeepWiki.ReactiveSystems
