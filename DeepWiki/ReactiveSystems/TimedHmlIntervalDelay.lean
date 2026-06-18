import DeepWiki.ReactiveSystems.TimedHmlClocks

/-! # Interval-decorated time-delay operators (Exercise 12.7)
A natural variant of `Mt` decorates the delay quantifiers with time intervals:
`∃∃[a,b)F` means "a delay `d` with `a ≤ d < b` is possible, after which `F` holds",
and `∀∀(a,b)F` means "`F` holds after every delay strictly between `a` and `b`".
Such formulae add no expressive power: each is definable in plain `Mt` using one
*fresh formula clock* (here `none`, extending the clock set `D` to `Option D`) that
is reset, then measures the elapsed delay against the interval bounds. We give the
clock-renaming infrastructure (`Mt.mapClock` and its satisfaction-invariance),
define the two operators, and prove they capture exactly the intended interval
semantics. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

/-! ## Clock renaming -/

/-- Relabel the clocks of a constraint along `f`. -/
def ClockConstraint.mapClock {C C' : Type*} (f : C → C') :
    ClockConstraint C → ClockConstraint C'
  | .true_ => .true_
  | .atom x c n => .atom (f x) c n
  | .and g₁ g₂ => .and (g₁.mapClock f) (g₂.mapClock f)

/-- Renaming clocks pulls satisfaction back along `f`. -/
theorem satisfies_mapClock {C C' : Type*} (f : C → C') (v : Valuation C')
    (g : ClockConstraint C) : satisfies v (g.mapClock f) ↔ satisfies (fun x => v (f x)) g := by
  induction g with
  | true_ => rfl
  | atom x c n => rfl
  | and g₁ g₂ ih₁ ih₂ => simp only [ClockConstraint.mapClock, satisfies, ih₁, ih₂]

/-- Relabel the formula clocks of an `Mt` formula along `f`. -/
def Mt.mapClock {Act D D' : Type*} (f : D → D') : Mt Act D → Mt Act D'
  | .tt => .tt
  | .ff => .ff
  | .and F G => .and (F.mapClock f) (G.mapClock f)
  | .or F G => .or (F.mapClock f) (G.mapClock f)
  | .dia a F => .dia a (F.mapClock f)
  | .box a F => .box a (F.mapClock f)
  | .existsDelay F => .existsDelay (F.mapClock f)
  | .forallDelay F => .forallDelay (F.mapClock f)
  | .reset x F => .reset (f x) (F.mapClock f)
  | .guard g => .guard (g.mapClock f)

namespace TLTS

variable {Proc Act D : Type*}

/-- Renaming formula clocks along an *injective* `f` pulls satisfaction back along
`f`: the renamed formula at `v` says exactly what the original says at `v ∘ f`. -/
theorem mtSat_mapClock {D' : Type*} (f : D → D') (hf : Function.Injective f)
    (T : TLTS Proc Act) (F : Mt Act D) :
    ∀ (p : Proc) (v : Valuation D'),
      MtSat T p v (F.mapClock f) ↔ MtSat T p (fun x => v (f x)) F := by
  induction F with
  | tt => intro _ _; rfl
  | ff => intro _ _; rfl
  | and F G ihF ihG => intro p v; simp only [Mt.mapClock, MtSat, ihF, ihG]
  | or F G ihF ihG => intro p v; simp only [Mt.mapClock, MtSat, ihF, ihG]
  | dia a F ihF =>
      intro p v; simp only [Mt.mapClock, MtSat]
      exact exists_congr fun p' => and_congr_right fun _ => ihF p' v
  | box a F ihF =>
      intro p v; simp only [Mt.mapClock, MtSat]
      exact forall_congr' fun p' => imp_congr_right fun _ => ihF p' v
  | existsDelay F ihF =>
      intro p v; simp only [Mt.mapClock, MtSat]
      refine exists_congr fun d => exists_congr fun p' => and_congr_right fun _ => ?_
      rw [ihF p' (v.add d)]
      have : (fun x => (v.add d) (f x)) = Valuation.add (fun x => v (f x)) d := by
        funext x; simp only [Valuation.add_apply]
      rw [this]
  | forallDelay F ihF =>
      intro p v; simp only [Mt.mapClock, MtSat]
      refine forall_congr' fun d => forall_congr' fun p' => imp_congr_right fun _ => ?_
      rw [ihF p' (v.add d)]
      have : (fun x => (v.add d) (f x)) = Valuation.add (fun x => v (f x)) d := by
        funext x; simp only [Valuation.add_apply]
      rw [this]
  | reset x F ihF =>
      intro p v; simp only [Mt.mapClock, MtSat]
      rw [ihF p (Valuation.reset {f x} v)]
      have : (fun y => (Valuation.reset {f x} v) (f y)) = Valuation.reset {x} (fun y => v (f y)) := by
        funext y
        by_cases hy : y = x
        · subst hy; simp [Valuation.reset]
        · have hfy : f y ≠ f x := fun h => hy (hf h)
          rw [Valuation.reset_not_mem (by simpa using hfy), Valuation.reset_not_mem (by simpa using hy)]
      rw [this]
  | guard g => intro p v; simp only [Mt.mapClock, MtSat]; exact satisfies_mapClock f v g

end TLTS

/-! ## The interval-decorated operators -/

/-- `∃∃[a,b)F`: a delay `d` with `a ≤ d < b` is possible, after which `F` holds.
Definable in `Mt` with a fresh clock `none` reset to measure the delay. -/
def Mt.existsInterval {Act D : Type*} (a b : ℕ) (F : Mt Act D) : Mt Act (Option D) :=
  .reset none (.existsDelay
    (.and (.guard (.atom none .ge a))
      (.and (.guard (.atom none .lt b)) (F.mapClock some))))

/-- `∀∀(a,b)F`: `F` holds after every delay strictly between `a` and `b`. Definable
in `Mt` with a fresh clock `none` measuring the delay (the guard `z ≤ a ∨ z ≥ b`
makes the obligation vacuous outside the open interval). -/
def Mt.forallInterval {Act D : Type*} (a b : ℕ) (F : Mt Act D) : Mt Act (Option D) :=
  .reset none (.forallDelay
    (.or (.or (.guard (.atom none .le a)) (.guard (.atom none .ge b)))
      (F.mapClock some)))

namespace TLTS

/-- **Expressibility of `∃∃[a,b)` (Exercise 12.7).** The `Mt` formula
`Mt.existsInterval a b F` holds at `(p, v)` exactly when some delay `d` with
`a ≤ d < b` leads to a state satisfying `F` (the original clocks `v ∘ some`
advancing by `d`). -/
theorem mtSat_existsInterval (a b : ℕ) (F : Mt Act D) (T : TLTS Proc Act) (p : Proc)
    (v : Valuation (Option D)) :
    MtSat T p v (Mt.existsInterval a b F) ↔
      ∃ d p', (a : ℝ≥0) ≤ d ∧ d < b ∧ T.delay p d p' ∧
        MtSat T p' (Valuation.add (fun x => v (some x)) d) F := by
  have hnone : (Valuation.reset {none} v) none = 0 := Valuation.reset_mem rfl v
  simp only [Mt.existsInterval, MtSat, satisfies, Cmp.holds, Valuation.add_apply, hnone, zero_add]
  refine exists_congr fun d => exists_congr fun p' => ?_
  rw [mtSat_mapClock some (Option.some_injective D) T F p' ((Valuation.reset {none} v).add d)]
  have hval : (fun x => ((Valuation.reset {none} v).add d) (some x)) = Valuation.add (fun x => v (some x)) d := by
    funext x; simp only [Valuation.add_apply, Valuation.reset_not_mem (show some x ∉ ({none} : Set (Option D)) by simp)]
  rw [hval]
  tauto

/-- **Expressibility of `∀∀(a,b)` (Exercise 12.7).** The `Mt` formula
`Mt.forallInterval a b F` holds at `(p, v)` exactly when every delay `d` strictly
between `a` and `b` leads to a state satisfying `F`. -/
theorem mtSat_forallInterval (a b : ℕ) (F : Mt Act D) (T : TLTS Proc Act) (p : Proc)
    (v : Valuation (Option D)) :
    MtSat T p v (Mt.forallInterval a b F) ↔
      ∀ d p', (a : ℝ≥0) < d → d < b → T.delay p d p' →
        MtSat T p' (Valuation.add (fun x => v (some x)) d) F := by
  have hnone : (Valuation.reset {none} v) none = 0 := Valuation.reset_mem rfl v
  simp only [Mt.forallInterval, MtSat, satisfies, Cmp.holds, Valuation.add_apply, hnone, zero_add]
  refine forall_congr' fun d => forall_congr' fun p' => ?_
  rw [mtSat_mapClock some (Option.some_injective D) T F p' ((Valuation.reset {none} v).add d)]
  have hval : (fun x => ((Valuation.reset {none} v).add d) (some x)) = Valuation.add (fun x => v (some x)) d := by
    funext x; simp only [Valuation.add_apply, Valuation.reset_not_mem (show some x ∉ ({none} : Set (Option D)) by simp)]
  rw [hval]
  constructor
  · intro h hd1 hd2 hdel
    rcases h hdel with (hle | hge) | hF
    · exact absurd hd1 (not_lt.mpr hle)
    · exact absurd hd2 (not_lt.mpr hge)
    · exact hF
  · intro h hdel
    by_cases h1 : (a : ℝ≥0) < d
    · by_cases h2 : d < (b : ℝ≥0)
      · exact Or.inr (h h1 h2 hdel)
      · exact Or.inl (Or.inr (not_lt.mp h2))
    · exact Or.inl (Or.inl (not_lt.mp h1))

end TLTS

end DeepWiki.ReactiveSystems
