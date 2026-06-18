import DeepWiki.ReactiveSystems.TimedBisimulationUntimed

/-! # Four timed automata and their (un)timed bisimilarity (Exercise 11.5)
Four single-action (`a`), single-clock (`y`) timed automata, given as one TLTS over
the disjoint union of their locations (configurations `(ℓ, y)`, free delays):

* `A —a[y≤1, y:=0]→ B —a[y≤1, y:=0]→ C` — resets the clock on each `a`;
* `X —a[y≤2]→ Y —a[y≤2]→ Z` — no resets;
* `U —a[true]→ V —a[y≤2]→ W` — first `a` unguarded;
* `D —a[y≤2]→ E —a[y≤2]→ F` and `D —a[y>2]→ G` — first `a` branches.

The interesting comparisons among the initial states: `U` and `D` are **timed
bisimilar** (their first `a` is always enabled, and the `y≤2`/`y>2` split of `D`
matches `U`'s single successor pointwise); `A` and `X` are untimed but not timed
bisimilar; the remaining pairs are neither (`U`, `D` can always fire `a` while `A`,
`X` cannot after a large enough delay). This file builds the model and the `U ~ D`
result. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-- The locations of the four automata of Exercise 11.5. -/
inductive Loc115
  | A | B | C | X | Y | Z | U | V | W | D | E | F | G
  deriving DecidableEq

/-- The transition relation of the four automata, over configurations `(ℓ, y)`:
free time delays plus the guarded/reset `a`-edges of each automaton. -/
inductive Step115 : Loc115 × ℝ≥0 → (Unit ⊕ ℝ≥0) → Loc115 × ℝ≥0 → Prop
  /-- Time may elapse freely from any configuration. -/
  | delay (ℓ : Loc115) (y d : ℝ≥0) : Step115 (ℓ, y) (.inr d) (ℓ, y + d)
  | aA {y : ℝ≥0} (h : y ≤ 1) : Step115 (.A, y) (.inl ()) (.B, 0)
  | aB {y : ℝ≥0} (h : y ≤ 1) : Step115 (.B, y) (.inl ()) (.C, 0)
  | aX {y : ℝ≥0} (h : y ≤ 2) : Step115 (.X, y) (.inl ()) (.Y, y)
  | aY {y : ℝ≥0} (h : y ≤ 2) : Step115 (.Y, y) (.inl ()) (.Z, y)
  | aU {y : ℝ≥0} : Step115 (.U, y) (.inl ()) (.V, y)
  | aV {y : ℝ≥0} (h : y ≤ 2) : Step115 (.V, y) (.inl ()) (.W, y)
  | aD {y : ℝ≥0} (h : y ≤ 2) : Step115 (.D, y) (.inl ()) (.E, y)
  | aDG {y : ℝ≥0} (h : 2 < y) : Step115 (.D, y) (.inl ()) (.G, y)
  | aE {y : ℝ≥0} (h : y ≤ 2) : Step115 (.E, y) (.inl ()) (.F, y)

/-- The combined TLTS (the union of the four automata's transition systems). -/
def tlts115 : TLTS (Loc115 × ℝ≥0) Unit := ⟨Step115⟩

/-- The timed bisimulation relating `U` and `D`: `U`/`D` step for step, `V`
mirrors `E` (both fire `a` iff `y ≤ 2`), `V` mirrors the dead `G` once `y > 2`, and
the dead `W`/`F` agree. -/
def rUD : Loc115 × ℝ≥0 → Loc115 × ℝ≥0 → Prop := fun p q =>
  (p.1 = .U ∧ q.1 = .D ∧ p.2 = q.2) ∨
  (p.1 = .V ∧ q.1 = .E ∧ p.2 = q.2) ∨
  (p.1 = .V ∧ q.1 = .G ∧ p.2 = q.2 ∧ 2 < p.2) ∨
  (p.1 = .W ∧ q.1 = .F ∧ p.2 = q.2)

/-- `rUD` is a timed bisimulation. -/
theorem isBisimulation_rUD : LTS.IsBisimulation tlts115 rUD := by
  rintro ⟨ℓp, yp⟩ ⟨ℓq, yq⟩ hpq
  obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, h2⟩ | ⟨rfl, rfl, rfl⟩ := hpq
  · -- (U, y) ~ (D, y)
    refine ⟨fun l p' hstep => ?_, fun l q' hstep => ?_⟩
    · cases hstep with
      | delay _ _ d => exact ⟨(.D, yp + d), Step115.delay _ _ d, Or.inl ⟨rfl, rfl, rfl⟩⟩
      | aU =>
          by_cases hy2 : yp ≤ 2
          · exact ⟨(.E, yp), Step115.aD hy2, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
          · exact ⟨(.G, yp), Step115.aDG (not_le.mp hy2),
              Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, not_le.mp hy2⟩))⟩
    · cases hstep with
      | delay _ _ d => exact ⟨(.U, yp + d), Step115.delay _ _ d, Or.inl ⟨rfl, rfl, rfl⟩⟩
      | aD h => exact ⟨(.V, yp), Step115.aU, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
      | aDG h => exact ⟨(.V, yp), Step115.aU, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, h⟩))⟩
  · -- (V, y) ~ (E, y)
    refine ⟨fun l p' hstep => ?_, fun l q' hstep => ?_⟩
    · cases hstep with
      | delay _ _ d => exact ⟨(.E, yp + d), Step115.delay _ _ d, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
      | aV h => exact ⟨(.F, yp), Step115.aE h, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))⟩
    · cases hstep with
      | delay _ _ d => exact ⟨(.V, yp + d), Step115.delay _ _ d, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
      | aE h => exact ⟨(.W, yp), Step115.aV h, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))⟩
  · -- (V, y) ~ (G, y), y > 2
    refine ⟨fun l p' hstep => ?_, fun l q' hstep => ?_⟩
    · cases hstep with
      | delay _ _ d =>
          exact ⟨(.G, yp + d), Step115.delay _ _ d,
            Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, h2.trans_le le_self_add⟩))⟩
      | aV h => exact absurd h (not_le.mpr h2)
    · cases hstep with
      | delay _ _ d =>
          exact ⟨(.V, yp + d), Step115.delay _ _ d,
            Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, h2.trans_le le_self_add⟩))⟩
  · -- (W, y) ~ (F, y)
    refine ⟨fun l p' hstep => ?_, fun l q' hstep => ?_⟩
    · cases hstep with
      | delay _ _ d => exact ⟨(.F, yp + d), Step115.delay _ _ d, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))⟩
    · cases hstep with
      | delay _ _ d => exact ⟨(.W, yp + d), Step115.delay _ _ d, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))⟩

/-- **Exercise 11.5: `U` and `D` are timed bisimilar.** Both can fire `a` after any
delay; `D`'s `y≤2`/`y>2` branch matches `U`'s single `a`-successor at every clock
value. -/
theorem u_timedBisimilar_d :
    TLTS.TimedBisimilar tlts115 (.U, 0) (.D, 0) :=
  isBisimulation_rUD.le_bisimilar (Or.inl ⟨rfl, rfl, rfl⟩)

/-! ## The four "neither" pairs

`U` and `D` can fire `a` after *any* delay (their first `a`-edge is unguarded /
always enabled), whereas `A` refuses `a` once `y > 1` and `X` once `y > 2`. So
delaying past the guard exposes an `a` the other side cannot match — already at the
*untimed* level (a fortiori not timed bisimilar). -/

/-- If `(pℓ, 0)` refuses every `a` after a delay `D` while `(qℓ, ·)` can always fire
`a`, the two are not untimed bisimilar — delaying `p` into its `a`-refusing region
leaves a `q`-action unmatched. -/
private theorem not_untimed_of_refuses {pℓ qℓ : Loc115} (D : ℝ≥0)
    (hpdelay : ¬ ∃ p', tlts115.act (pℓ, (0 : ℝ≥0) + D) () p')
    (hqact : ∀ d' : ℝ≥0, ∃ q', tlts115.act (qℓ, (0 : ℝ≥0) + d') () q') :
    ¬ TLTS.UntimedBisimilar tlts115 (pℓ, 0) (qℓ, 0) := by
  intro h
  rw [TLTS.untimedBisimilar_iff] at h
  obtain ⟨d', q', hq', hb⟩ := h.2.2.1 D (pℓ, 0 + D) (Step115.delay pℓ 0 D)
  cases hq' with
  | delay _ _ _ =>
      rw [TLTS.untimedBisimilar_iff] at hb
      obtain ⟨qa', hqa'⟩ := hqact d'
      obtain ⟨p', hp', _⟩ := hb.2.1 () qa' hqa'
      exact hpdelay ⟨p', hp'⟩

/-- `A` refuses `a` once the clock exceeds `1`. -/
private theorem a_refuses_at_two : ¬ ∃ p', tlts115.act (.A, (0 : ℝ≥0) + 2) () p' := by
  rintro ⟨p', hp'⟩; cases hp' with | aA h => exact absurd h (by norm_num)

/-- `X` refuses `a` once the clock exceeds `2`. -/
private theorem x_refuses_at_three : ¬ ∃ p', tlts115.act (.X, (0 : ℝ≥0) + 3) () p' := by
  rintro ⟨p', hp'⟩; cases hp' with | aX h => exact absurd h (by norm_num)

/-- `U` can fire `a` after any delay. -/
private theorem u_acts (d' : ℝ≥0) : ∃ q', tlts115.act (.U, (0 : ℝ≥0) + d') () q' :=
  ⟨_, Step115.aU⟩

/-- `D` can fire `a` after any delay (to `E` if `y ≤ 2`, else to `G`). -/
private theorem d_acts (d' : ℝ≥0) : ∃ q', tlts115.act (.D, (0 : ℝ≥0) + d') () q' := by
  by_cases h : (0 : ℝ≥0) + d' ≤ 2
  · exact ⟨_, Step115.aD h⟩
  · exact ⟨_, Step115.aDG (not_le.mp h)⟩

/-- **`A` and `U` are not untimed (hence not timed) bisimilar.** -/
theorem a_not_untimedBisimilar_u : ¬ TLTS.UntimedBisimilar tlts115 (.A, 0) (.U, 0) :=
  not_untimed_of_refuses 2 a_refuses_at_two u_acts

/-- **`A` and `D` are not untimed (hence not timed) bisimilar.** -/
theorem a_not_untimedBisimilar_d : ¬ TLTS.UntimedBisimilar tlts115 (.A, 0) (.D, 0) :=
  not_untimed_of_refuses 2 a_refuses_at_two d_acts

/-- **`X` and `U` are not untimed (hence not timed) bisimilar.** -/
theorem x_not_untimedBisimilar_u : ¬ TLTS.UntimedBisimilar tlts115 (.X, 0) (.U, 0) :=
  not_untimed_of_refuses 3 x_refuses_at_three u_acts

/-- **`X` and `D` are not untimed (hence not timed) bisimilar.** -/
theorem x_not_untimedBisimilar_d : ¬ TLTS.UntimedBisimilar tlts115 (.X, 0) (.D, 0) :=
  not_untimed_of_refuses 3 x_refuses_at_three d_acts

/-! ## `A` and `X`: untimed bisimilar but not timed bisimilar -/

/-- **`A` and `X` are not timed bisimilar.** After the *exact* delay `3/2`, `X` can
still fire `a` (clock `≤ 2`) but `A` cannot (clock `> 1`) — and timed bisimilarity
must match delays by the same duration. -/
theorem a_not_timedBisimilar_x : ¬ TLTS.TimedBisimilar tlts115 (.A, 0) (.X, 0) := by
  have hb2 : (0 : ℝ≥0) + 3 / 2 ≤ 2 := by rw [← NNReal.coe_le_coe]; push_cast; norm_num
  have hb1 : ¬ ((0 : ℝ≥0) + 3 / 2 ≤ 1) := by rw [← NNReal.coe_le_coe]; push_cast; norm_num
  intro h
  rw [TLTS.timedBisimilar_iff] at h
  obtain ⟨p', hp', hb⟩ := h.2.2.2 (3 / 2) (.X, 0 + 3 / 2) (Step115.delay .X 0 (3 / 2))
  cases hp' with
  | delay _ _ _ =>
      rw [TLTS.timedBisimilar_iff] at hb
      obtain ⟨a', ha', _⟩ := hb.2.1 () (.Y, 0 + 3 / 2) (Step115.aX hb2)
      cases ha' with | aA h => exact hb1 h

/-- The *untimed* bisimulation relating `A` and `X`: clock durations are forgotten,
so the only thing that matters is whether `a` is currently enabled. `A`/`X` (and
`B`/`Y`) are paired in the "`a`-enabled" region (`y ≤ 1` resp. `y ≤ 2`) and in the
"`a`-disabled" region (`y > 1` resp. `y > 2`); the dead `C`/`Z` agree. -/
def rAX : Loc115 × ℝ≥0 → Loc115 × ℝ≥0 → Prop := fun p q =>
  (p.1 = .A ∧ q.1 = .X ∧ ((p.2 ≤ 1 ∧ q.2 ≤ 2) ∨ (1 < p.2 ∧ 2 < q.2))) ∨
  (p.1 = .B ∧ q.1 = .Y ∧ ((p.2 ≤ 1 ∧ q.2 ≤ 2) ∨ (1 < p.2 ∧ 2 < q.2))) ∨
  (p.1 = .C ∧ q.1 = .Z)

/-- `rAX` is an untimed bisimulation (a bisimulation on the untimed LTS): each `a`
is matched exactly, and each delay is matched by *some* delay landing in the
corresponding region. -/
theorem isBisimulation_rAX : LTS.IsBisimulation tlts115.untimedLTS rAX := by
  rintro ⟨ℓp, yp⟩ ⟨ℓq, yq⟩ hpq
  obtain ⟨rfl, rfl, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩ | ⟨rfl, rfl, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩ | ⟨rfl, rfl⟩ := hpq
  · -- A ~ X, low region (yp ≤ 1, yq ≤ 2)
    refine ⟨fun l p' hstep => ?_, fun l q' hstep => ?_⟩
    · cases l with
      | some _ =>
          cases hstep with
          | aA _ => exact ⟨(.Y, yq), Step115.aX h2, Or.inr (Or.inl ⟨rfl, rfl, Or.inl ⟨zero_le', h2⟩⟩)⟩
      | none =>
          obtain ⟨d, hd⟩ := hstep; cases hd
          by_cases hlow : yp + d ≤ 1
          · exact ⟨(.X, yq), ⟨0, by simpa using Step115.delay .X yq 0⟩, Or.inl ⟨rfl, rfl, Or.inl ⟨hlow, h2⟩⟩⟩
          · exact ⟨(.X, yq + 3), ⟨3, Step115.delay .X yq 3⟩, Or.inl ⟨rfl, rfl, Or.inr ⟨not_le.mp hlow, (by norm_num : (2:ℝ≥0) < 3).trans_le le_add_self⟩⟩⟩
    · cases l with
      | some _ =>
          cases hstep with
          | aX _ => exact ⟨(.B, 0), Step115.aA h1, Or.inr (Or.inl ⟨rfl, rfl, Or.inl ⟨by norm_num, h2⟩⟩)⟩
      | none =>
          obtain ⟨d, hd⟩ := hstep; cases hd
          by_cases hlow : yq + d ≤ 2
          · exact ⟨(.A, yp), ⟨0, by simpa using Step115.delay .A yp 0⟩, Or.inl ⟨rfl, rfl, Or.inl ⟨h1, hlow⟩⟩⟩
          · exact ⟨(.A, yp + 2), ⟨2, Step115.delay .A yp 2⟩, Or.inl ⟨rfl, rfl, Or.inr ⟨(by norm_num : (1:ℝ≥0) < 2).trans_le le_add_self, not_le.mp hlow⟩⟩⟩
  · -- A ~ X, high region (1 < yp, 2 < yq): no `a`, delays stay high
    refine ⟨fun l p' hstep => ?_, fun l q' hstep => ?_⟩
    · cases l with
      | some _ => cases hstep with | aA hle => exact absurd hle (not_le.mpr h1)
      | none =>
          obtain ⟨d, hd⟩ := hstep; cases hd
          exact ⟨(.X, yq), ⟨0, by simpa using Step115.delay .X yq 0⟩,
            Or.inl ⟨rfl, rfl, Or.inr ⟨h1.trans_le le_self_add, h2⟩⟩⟩
    · cases l with
      | some _ => cases hstep with | aX hle => exact absurd hle (not_le.mpr h2)
      | none =>
          obtain ⟨d, hd⟩ := hstep; cases hd
          exact ⟨(.A, yp), ⟨0, by simpa using Step115.delay .A yp 0⟩,
            Or.inl ⟨rfl, rfl, Or.inr ⟨h1, h2.trans_le le_self_add⟩⟩⟩
  · -- B ~ Y, low region
    refine ⟨fun l p' hstep => ?_, fun l q' hstep => ?_⟩
    · cases l with
      | some _ =>
          cases hstep with
          | aB _ => exact ⟨(.Z, yq), Step115.aY h2, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
      | none =>
          obtain ⟨d, hd⟩ := hstep; cases hd
          by_cases hlow : yp + d ≤ 1
          · exact ⟨(.Y, yq), ⟨0, by simpa using Step115.delay .Y yq 0⟩, Or.inr (Or.inl ⟨rfl, rfl, Or.inl ⟨hlow, h2⟩⟩)⟩
          · exact ⟨(.Y, yq + 3), ⟨3, Step115.delay .Y yq 3⟩, Or.inr (Or.inl ⟨rfl, rfl, Or.inr ⟨not_le.mp hlow, (by norm_num : (2:ℝ≥0) < 3).trans_le le_add_self⟩⟩)⟩
    · cases l with
      | some _ =>
          cases hstep with
          | aY _ => exact ⟨(.C, 0), Step115.aB h1, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
      | none =>
          obtain ⟨d, hd⟩ := hstep; cases hd
          by_cases hlow : yq + d ≤ 2
          · exact ⟨(.B, yp), ⟨0, by simpa using Step115.delay .B yp 0⟩, Or.inr (Or.inl ⟨rfl, rfl, Or.inl ⟨h1, hlow⟩⟩)⟩
          · exact ⟨(.B, yp + 2), ⟨2, Step115.delay .B yp 2⟩, Or.inr (Or.inl ⟨rfl, rfl, Or.inr ⟨(by norm_num : (1:ℝ≥0) < 2).trans_le le_add_self, not_le.mp hlow⟩⟩)⟩
  · -- B ~ Y, high region
    refine ⟨fun l p' hstep => ?_, fun l q' hstep => ?_⟩
    · cases l with
      | some _ => cases hstep with | aB hle => exact absurd hle (not_le.mpr h1)
      | none =>
          obtain ⟨d, hd⟩ := hstep; cases hd
          exact ⟨(.Y, yq), ⟨0, by simpa using Step115.delay .Y yq 0⟩,
            Or.inr (Or.inl ⟨rfl, rfl, Or.inr ⟨h1.trans_le le_self_add, h2⟩⟩)⟩
    · cases l with
      | some _ => cases hstep with | aY hle => exact absurd hle (not_le.mpr h2)
      | none =>
          obtain ⟨d, hd⟩ := hstep; cases hd
          exact ⟨(.B, yp), ⟨0, by simpa using Step115.delay .B yp 0⟩,
            Or.inr (Or.inl ⟨rfl, rfl, Or.inr ⟨h1, h2.trans_le le_self_add⟩⟩)⟩
  · -- C ~ Z, both dead
    refine ⟨fun l p' hstep => ?_, fun l q' hstep => ?_⟩
    · cases l with
      | some _ => cases hstep
      | none =>
          obtain ⟨d, hd⟩ := hstep; cases hd
          exact ⟨(.Z, yq + d), ⟨d, Step115.delay .Z yq d⟩, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
    · cases l with
      | some _ => cases hstep
      | none =>
          obtain ⟨d, hd⟩ := hstep; cases hd
          exact ⟨(.C, yp + d), ⟨d, Step115.delay .C yp d⟩, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

/-- **Exercise 11.5: `A` and `X` are untimed bisimilar.** Forgetting delay durations,
both perform "`a` then `a` then deadlock", with the same `a`-enabledness pattern. -/
theorem a_untimedBisimilar_x : TLTS.UntimedBisimilar tlts115 (.A, 0) (.X, 0) :=
  isBisimulation_rAX.le_bisimilar (Or.inl ⟨rfl, rfl, Or.inl ⟨by norm_num, by norm_num⟩⟩)

end DeepWiki.ReactiveSystems
