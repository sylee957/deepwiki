import DeepWiki.NetworkCalculus.ConvexConvByLine
import DeepWiki.NetworkCalculus.ConvexSegmentMerge
import DeepWiki.NetworkCalculus.ContainerCanonical

/-! # Breakpoint / rank structure of a convex PWL (§4.4 infra)
The book's Prop 4.4 [4.13] and Def 4.4 finiteness rest on the breakpoint structure of a
convex piecewise-linear curve `f = convexSegEval f0 fs segs`: the abscissae where the slope
changes (the non-differentiable points), the rank `u*` of the last semi-infinite segment, and
the corner values `f` takes there. This file builds that structure on the slope/length
representation: `pwlRank` (the rank `= segLenSum`), `breakpoints` (the cumulative-length
abscissae), and `convexSegEval_at_breakpoint` (the corner value `f0 + Σ slopeᵢ·lengthᵢ`). -/

namespace DeepWiki

open scoped NNReal

/-! ## Rank — the abscissa of the last semi-infinite segment -/

/-- The **rank** of a convex PWL `convexSegEval f0 fs segs`: the abscissa `u*` where the last
(semi-infinite) segment of slope `fs` begins, i.e. the cumulative length of all finite segments
(`= segLenSum segs`). -/
noncomputable def pwlRank (segs : List (ℝ≥0 × ℝ≥0)) : ℝ≥0 := segLenSum segs

@[simp] theorem pwlRank_nil : pwlRank [] = 0 := rfl

@[simp] theorem pwlRank_cons (s ℓ : ℝ≥0) (rest : List (ℝ≥0 × ℝ≥0)) :
    pwlRank ((s, ℓ) :: rest) = ℓ + pwlRank rest := rfl

/-- **Past the rank a convex PWL is its asymptote line.** For `t ≥ pwlRank segs` the finite
segments are exhausted, so the curve continues from the corner `f(u*)` at slope `fs`:
`f t = f(u*) + fs·(t − u*)`. (Restatement of `convexSegEval_past_segs` on `pwlRank`.) -/
theorem convexSegEval_past_rank (f0 fs : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0)) {t : ℝ≥0}
    (ht : pwlRank segs ≤ t) :
    convexSegEval f0 fs segs t
      = convexSegEval f0 fs segs (pwlRank segs) + fs * (t - pwlRank segs) :=
  convexSegEval_past_segs fs segs f0 t ht

/-! ## Breakpoints — the abscissae where the slope changes -/

/-- The **breakpoints** of a convex PWL `convexSegEval f0 fs segs`: the strictly increasing list
of abscissae where the slope changes (the non-differentiable points), namely the cumulative
lengths `segLenSum (segs.take 1), segLenSum (segs.take 2), …, segLenSum segs = pwlRank segs`. -/
noncomputable def breakpoints : List (ℝ≥0 × ℝ≥0) → List ℝ≥0
  | [] => []
  | (_, ℓ) :: rest => ℓ :: (breakpoints rest).map (ℓ + ·)

@[simp] theorem breakpoints_nil : breakpoints [] = [] := rfl

@[simp] theorem breakpoints_cons (s ℓ : ℝ≥0) (rest : List (ℝ≥0 × ℝ≥0)) :
    breakpoints ((s, ℓ) :: rest) = ℓ :: (breakpoints rest).map (ℓ + ·) := rfl

/-- The number of breakpoints equals the number of finite segments. -/
@[simp] theorem breakpoints_length (segs : List (ℝ≥0 × ℝ≥0)) :
    (breakpoints segs).length = segs.length := by
  induction segs with
  | nil => rfl
  | cons hd tl ih => obtain ⟨s, ℓ⟩ := hd; simp [ih]

/-- The `k`-th breakpoint is the cumulative length over the first `k+1` segments:
`(breakpoints segs).get k = segLenSum (segs.take (k+1))`. -/
theorem breakpoints_getElem (segs : List (ℝ≥0 × ℝ≥0)) (k : ℕ)
    (hk : k < (breakpoints segs).length) :
    (breakpoints segs)[k] = segLenSum (segs.take (k + 1)) := by
  induction segs generalizing k with
  | nil => simp at hk
  | cons hd tl ih =>
      obtain ⟨s, ℓ⟩ := hd
      cases k with
      | zero => simp
      | succ k =>
          have hk' : k < (breakpoints tl).length := by
            rw [breakpoints_length] at hk ⊢
            simpa using Nat.lt_of_succ_lt_succ hk
          simp only [breakpoints_cons, List.getElem_cons_succ, List.getElem_map,
            List.take_succ_cons, segLenSum_cons]
          rw [ih k hk']

/-- The last breakpoint is the rank: `(breakpoints segs).getLast = pwlRank segs` (for nonempty
`segs`). The rightmost non-differentiable point is where the asymptote begins. -/
theorem breakpoints_getLast (segs : List (ℝ≥0 × ℝ≥0)) (h : breakpoints segs ≠ []) :
    (breakpoints segs).getLast h = pwlRank segs := by
  have hlen : 0 < (breakpoints segs).length := List.length_pos_iff.mpr h
  rw [List.getLast_eq_getElem,
    breakpoints_getElem segs _ (by omega),
    Nat.sub_add_cancel hlen, breakpoints_length, List.take_length, pwlRank]

/-- Membership in `breakpoints`: every breakpoint is a cumulative length of a nonempty prefix,
`segLenSum (segs.take k)` for some `1 ≤ k ≤ segs.length`. -/
theorem mem_breakpoints (segs : List (ℝ≥0 × ℝ≥0)) {x : ℝ≥0} :
    x ∈ breakpoints segs ↔ ∃ k, 1 ≤ k ∧ k ≤ segs.length ∧ x = segLenSum (segs.take k) := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [breakpoints_length] at hk
    exact ⟨k + 1, Nat.le_add_left 1 k, hk, breakpoints_getElem segs k (by rwa [breakpoints_length])⟩
  · rintro ⟨k, hk1, hk2, rfl⟩
    refine ⟨k - 1, by rw [breakpoints_length]; omega, ?_⟩
    rw [breakpoints_getElem segs (k - 1) (by rw [breakpoints_length]; omega),
      Nat.sub_add_cancel hk1]

/-- The rank is a breakpoint: `pwlRank segs ∈ breakpoints segs` for nonempty `segs`. -/
theorem pwlRank_mem_breakpoints (segs : List (ℝ≥0 × ℝ≥0)) (h : segs ≠ []) :
    pwlRank segs ∈ breakpoints segs := by
  rw [mem_breakpoints]
  refine ⟨segs.length, ?_, le_rfl, ?_⟩
  · rw [Nat.one_le_iff_ne_zero]
    exact fun hc => h (List.length_eq_zero_iff.mp hc)
  · rw [List.take_length, pwlRank]

/-- Cumulative length splits over `++`: `segLenSum (l₁ ++ l₂) = segLenSum l₁ + segLenSum l₂`. -/
theorem segLenSum_append (l₁ l₂ : List (ℝ≥0 × ℝ≥0)) :
    segLenSum (l₁ ++ l₂) = segLenSum l₁ + segLenSum l₂ := by
  induction l₁ with
  | nil => simp
  | cons hd tl ih => obtain ⟨s, ℓ⟩ := hd; simp only [List.cons_append, segLenSum_cons, ih]; ring

/-- Every breakpoint is bounded by the rank: `x ∈ breakpoints segs → x ≤ pwlRank segs`. -/
theorem le_pwlRank_of_mem_breakpoints (segs : List (ℝ≥0 × ℝ≥0)) {x : ℝ≥0}
    (hx : x ∈ breakpoints segs) : x ≤ pwlRank segs := by
  rw [mem_breakpoints] at hx
  obtain ⟨k, _, _, rfl⟩ := hx
  rw [pwlRank]
  calc segLenSum (segs.take k) ≤ segLenSum (segs.take k) + segLenSum (segs.drop k) := le_self_add
    _ = segLenSum segs := by rw [← segLenSum_append, List.take_append_drop]

/-- **The breakpoints are nondecreasing.** The abscissae where the slope changes are listed in
order: `List.Pairwise (· ≤ ·) (breakpoints segs)` (the cumulative lengths increase). -/
theorem breakpoints_pairwise_le (segs : List (ℝ≥0 × ℝ≥0)) :
    List.Pairwise (· ≤ ·) (breakpoints segs) := by
  induction segs with
  | nil => simp
  | cons hd tl ih =>
      obtain ⟨s, ℓ⟩ := hd
      rw [breakpoints_cons, List.pairwise_cons]
      refine ⟨fun x hx => ?_, ?_⟩
      · rw [List.mem_map] at hx
        obtain ⟨y, _, rfl⟩ := hx
        exact le_self_add
      · exact ih.map _ (fun a b hab => by gcongr)

/-- A breakpoint is positive when all segment lengths are positive: every cumulative length of a
nonempty prefix exceeds `0`. -/
theorem pos_of_mem_breakpoints (segs : List (ℝ≥0 × ℝ≥0)) (hpos : ∀ seg ∈ segs, 0 < seg.2)
    {x : ℝ≥0} (hx : x ∈ breakpoints segs) : 0 < x := by
  induction segs generalizing x with
  | nil => simp at hx
  | cons hd tl ih =>
      obtain ⟨s, ℓ⟩ := hd
      have hℓ : 0 < ℓ := hpos (s, ℓ) List.mem_cons_self
      have htl : ∀ seg ∈ tl, 0 < seg.2 := fun seg h => hpos seg (List.mem_cons_of_mem _ h)
      rw [breakpoints_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hℓ
      · rw [List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact lt_of_lt_of_le (ih htl hy) le_add_self

/-- **The breakpoints are strictly increasing when all segment lengths are positive.** With every
finite segment of positive length the non-differentiable points are distinct and ordered:
`List.Pairwise (· < ·) (breakpoints segs)`. -/
theorem breakpoints_pairwise_lt (segs : List (ℝ≥0 × ℝ≥0))
    (hpos : ∀ seg ∈ segs, 0 < seg.2) :
    List.Pairwise (· < ·) (breakpoints segs) := by
  induction segs with
  | nil => simp
  | cons hd tl ih =>
      obtain ⟨s, ℓ⟩ := hd
      have hℓ : 0 < ℓ := hpos (s, ℓ) List.mem_cons_self
      have htl : ∀ seg ∈ tl, 0 < seg.2 := fun seg h => hpos seg (List.mem_cons_of_mem _ h)
      rw [breakpoints_cons, List.pairwise_cons]
      refine ⟨fun x hx => ?_, ?_⟩
      · rw [List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact lt_add_of_pos_right ℓ (pos_of_mem_breakpoints tl htl hy)
      · exact (ih htl).map _ (fun a b hab => by gcongr)

/-! ## Corner values — the curve value at each breakpoint -/

/-- The **corner-value increment** of a segment list: `Σᵢ slopeᵢ · lengthᵢ` (the height gained
over all finite segments). Adding it to the base `f0` gives the value at the rank. -/
noncomputable def cornerSum : List (ℝ≥0 × ℝ≥0) → ℝ≥0
  | [] => 0
  | (s, ℓ) :: rest => s * ℓ + cornerSum rest

@[simp] theorem cornerSum_nil : cornerSum [] = 0 := rfl

@[simp] theorem cornerSum_cons (s ℓ : ℝ≥0) (rest : List (ℝ≥0 × ℝ≥0)) :
    cornerSum ((s, ℓ) :: rest) = s * ℓ + cornerSum rest := rfl

/-- **The value at the rank is the sum of the corner increments.**
`convexSegEval f0 fs segs (pwlRank segs) = f0 + cornerSum segs`: at the last breakpoint the curve
has accrued `f0 + Σᵢ slopeᵢ·lengthᵢ`. -/
theorem convexSegEval_pwlRank (f0 fs : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0)) :
    convexSegEval f0 fs segs (pwlRank segs) = f0 + cornerSum segs := by
  induction segs generalizing f0 with
  | nil => rw [pwlRank_nil, convexSegEval_zero, cornerSum_nil, add_zero]
  | cons hd tl ih =>
      obtain ⟨s, ℓ⟩ := hd
      rw [pwlRank_cons, cornerSum_cons, convexSegEval_cons_peel, ih]
      ring

/-- **The value at the `k`-th breakpoint is the sum of the first `k` corner increments.**
`convexSegEval f0 fs segs (segLenSum (segs.take k)) = f0 + cornerSum (segs.take k)`: at the
breakpoint after `k` segments the curve value is `f0 + Σᵢ₌₀..k₋₁ slopeᵢ·lengthᵢ`. -/
theorem convexSegEval_at_breakpoint (f0 fs : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0)) (k : ℕ) :
    convexSegEval f0 fs segs (segLenSum (segs.take k)) = f0 + cornerSum (segs.take k) := by
  induction segs generalizing f0 k with
  | nil => simp
  | cons hd tl ih =>
      obtain ⟨s, ℓ⟩ := hd
      cases k with
      | zero => simp
      | succ k =>
          rw [List.take_succ_cons, segLenSum_cons, cornerSum_cons,
            convexSegEval_cons_peel, ih]
          ring

/-- Faithfulness check: evaluating the curve at the `k`-th entry of `breakpoints` gives the
corner value over the first `k+1` segments. -/
example (f0 fs : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0)) (k : ℕ)
    (hk : k < (breakpoints segs).length) :
    convexSegEval f0 fs segs ((breakpoints segs)[k])
      = f0 + cornerSum (segs.take (k + 1)) := by
  rw [breakpoints_getElem segs k hk, convexSegEval_at_breakpoint]

/-- Faithfulness check: the value at the rank equals the value at the last breakpoint (nonempty
`segs`), namely `f0 + cornerSum segs`. -/
example (f0 fs : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0)) (h : breakpoints segs ≠ []) :
    convexSegEval f0 fs segs ((breakpoints segs).getLast h) = f0 + cornerSum segs := by
  rw [breakpoints_getLast, convexSegEval_pwlRank]

/-! ## The `Θ`-meet over breakpoints (Prop 4.4 [4.13])

The book's `Θ_f̲ = ⋀ᵢ Θ^{κᵢ}_{τᵢ}` (eq. [4.13]) decomposes the finite part of a convex PWL as
the `(min,+)` meet (dioid `+ = ⊓`) of the container elementary functions `Θ^{κᵢ}_{τᵢ}`
(`DeepWiki.Theta`: `κ` on `[0, τ]`, `⊤` after) pinned at the non-differentiable points `τᵢ` with
corner value `κᵢ = f(τᵢ)`. Each generator caps the curve at a corner; their meet samples `f` at
the breakpoints and is `⊤` past the last (the finite region's lower-envelope construction). -/

/-- The list of `Θ` generators for the breakpoints of `convexSegEval f0 fs segs`: one
`Θ^{κᵢ}_{τᵢ}` per finite segment, with rank `τᵢ` the `i`-th breakpoint and corner value
`κᵢ = ↑(convexSegEval f0 fs segs τᵢ)`. -/
noncomputable def breakpointThetas (f0 fs : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0)) :
    List (ℝ≥0 → EReal) :=
  (breakpoints segs).map (fun τ => Theta ((convexSegEval f0 fs segs τ : ℝ≥0) : EReal) τ)

/-- Pointwise meet of a list of `EReal`-valued spot functions (identity `⊤`); the dioid sum
`⋀ = ⊓` of [4.13]. -/
noncomputable def meetSpots (gs : List (ℝ≥0 → EReal)) : ℝ≥0 → EReal :=
  fun t => (gs.map (fun g => g t)).foldr (· ⊓ ·) ⊤

@[simp] theorem meetSpots_nil : meetSpots [] = fun _ => ⊤ := rfl

@[simp] theorem meetSpots_cons (g : ℝ≥0 → EReal) (gs : List (ℝ≥0 → EReal)) :
    meetSpots (g :: gs) = fun t => g t ⊓ meetSpots gs t := rfl

/-- Each generator dominates the meet: `meetSpots gs t ≤ g t` for `g ∈ gs` (the meet is below
every elementary function). -/
theorem meetSpots_le_of_mem {gs : List (ℝ≥0 → EReal)} {g : ℝ≥0 → EReal} (hg : g ∈ gs)
    (t : ℝ≥0) : meetSpots gs t ≤ g t := by
  induction gs with
  | nil => simp at hg
  | cons hd tl ih =>
      rw [meetSpots_cons]
      rcases List.mem_cons.mp hg with rfl | hg
      · exact inf_le_left
      · exact le_trans inf_le_right (ih hg)

/-- A pointwise lower bound for the meet: if `x ≤ g t` for every `g ∈ gs`, then `x ≤ meetSpots gs t`. -/
theorem le_meetSpots {gs : List (ℝ≥0 → EReal)} {x : EReal} {t : ℝ≥0}
    (h : ∀ g ∈ gs, x ≤ g t) : x ≤ meetSpots gs t := by
  induction gs with
  | nil => simp
  | cons hd tl ih =>
      rw [meetSpots_cons]
      exact le_inf (h hd List.mem_cons_self) (ih (fun g hg => h g (List.mem_cons_of_mem _ hg)))

/-- **The `Θ`-meet is a pointwise upper bound of the curve.** The lifted curve is everywhere below
the meet of its breakpoint generators:
`↑(convexSegEval f0 fs segs t) ≤ meetSpots (breakpointThetas f0 fs segs) t`. (On the finite region
each generator caps at a corner `≥ f(t)` by monotonicity; past the rank every generator is `⊤`.) -/
theorem convexSegEval_le_meet_breakpointThetas (f0 fs : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0))
    (t : ℝ≥0) :
    ((convexSegEval f0 fs segs t : ℝ≥0) : EReal)
      ≤ meetSpots (breakpointThetas f0 fs segs) t := by
  refine le_meetSpots (fun g hg => ?_)
  rw [breakpointThetas, List.mem_map] at hg
  obtain ⟨τ, _, rfl⟩ := hg
  rcases le_or_gt t τ with hle | hlt
  · rw [Theta_of_le hle]
    exact_mod_cast (monotone_convexSegEval fs segs f0) hle
  · -- past this breakpoint the generator is `⊤`, trivially above
    rw [Theta_of_lt hlt]; exact le_top

/-- **The `Θ`-meet samples the curve exactly at each breakpoint.** At a breakpoint `τ ∈ breakpoints`
the meet equals the corner value, `meetSpots (breakpointThetas f0 fs segs) τ = ↑(convexSegEval f0 fs segs τ)`:
[4.13]'s generators pin `Θ_f̲` to the curve at the non-differentiable points. -/
theorem meet_breakpointThetas_eq_at_breakpoint (f0 fs : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0))
    {τ : ℝ≥0} (hτ : τ ∈ breakpoints segs) :
    meetSpots (breakpointThetas f0 fs segs) τ
      = ((convexSegEval f0 fs segs τ : ℝ≥0) : EReal) := by
  refine le_antisymm ?_ (convexSegEval_le_meet_breakpointThetas f0 fs segs τ)
  -- the generator at `τ` itself takes value `κ_τ = f(τ)` there (`Theta_self`)
  have hmem : Theta ((convexSegEval f0 fs segs τ : ℝ≥0) : EReal) τ ∈ breakpointThetas f0 fs segs := by
    rw [breakpointThetas, List.mem_map]; exact ⟨τ, hτ, rfl⟩
  refine le_of_le_of_eq (meetSpots_le_of_mem hmem τ) ?_
  rw [Theta_self]

/-- **The `Θ`-meet is `⊤` past the last breakpoint.** For `pwlRank segs < t` no generator's prefix
covers `t`, so the meet is `⊤` — the breakpoint generators bound only the finite region, and the
asymptote is a separate (sloped) generator. (Hence [4.13]'s meet of *constant* `Θ`'s is not the
full pointwise curve; the asymptote needs an affine generator.) -/
theorem meet_breakpointThetas_eq_top_past_rank (f0 fs : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0))
    {t : ℝ≥0} (ht : pwlRank segs < t) :
    meetSpots (breakpointThetas f0 fs segs) t = ⊤ := by
  rw [eq_top_iff]
  refine le_meetSpots (fun g hg => ?_)
  rw [breakpointThetas, List.mem_map] at hg
  obtain ⟨τ, hτ, rfl⟩ := hg
  rw [Theta_of_lt (lt_of_le_of_lt (le_pwlRank_of_mem_breakpoints segs hτ) ht)]

/-- Faithfulness check: at the rank, the `Θ`-meet equals the corner value `↑(f0 + cornerSum segs)`. -/
example (f0 fs : ℝ≥0) (segs : List (ℝ≥0 × ℝ≥0)) (h : segs ≠ []) :
    meetSpots (breakpointThetas f0 fs segs) (pwlRank segs)
      = (((f0 + cornerSum segs : ℝ≥0) : ℝ) : EReal) := by
  rw [meet_breakpointThetas_eq_at_breakpoint f0 fs segs (pwlRank_mem_breakpoints segs h),
    convexSegEval_pwlRank]
  norm_cast

end DeepWiki
