import DeepWiki.NetworkCalculus.ConvexConvByLine
import DeepWiki.NetworkCalculus.ConvexSegmentMerge

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

end DeepWiki
