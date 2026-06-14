import Book.ServiceCurveWeaklyStrict

/-! # Families of service curves
A system may allow several service curves of one type at once — the
intersection of the trajectory relations. For the weakly strict and
strict types the family collapses to a single curve: the pointwise
supremum, then the type-respecting closure (non-decreasing for
weakly strict, super-additive for strict). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- A family of weakly strict curves is jointly offered iff its
pointwise supremum is: the start-anchored bounds aggregate under
`⨆`. -/
theorem weaklyStrictServiceRel_iSup_iff {ι : Type*} [Nonempty ι]
    {β : ι → ℝ≥0 → ℝ≥0}
    (hbdd : ∀ t, BddAbove (Set.range fun i => β i t)) {A D : Curve} :
    weaklyStrictServiceRel (fun t => ⨆ i, β i t) A D ↔
      ∀ i, weaklyStrictServiceRel (β i) A D := by
  constructor
  · intro hp i
    exact ⟨hp.1, fun t =>
      le_trans (add_le_add le_rfl (le_ciSup (hbdd _) i)) (hp.2 t)⟩
  · intro hp
    refine ⟨(hp (Classical.arbitrary ι)).1, fun t => ?_⟩
    show D (start ⇑A ⇑D t)
        + (⨆ i, β i (t - start ⇑A ⇑D t)) ≤ D t
    exact add_ciSup_le _ _ _ fun i => (hp i).2 t

/-- **Families, weakly strict**: the relation of the pointwise
supremum is the intersection of the relations of the family. -/
theorem weaklyStrictServiceRel_iSup {ι : Type*} [Nonempty ι]
    {β : ι → ℝ≥0 → ℝ≥0}
    (hbdd : ∀ t, BddAbove (Set.range fun i => β i t)) :
    weaklyStrictServiceRel (fun t => ⨆ i, β i t)
      = fun A D => ∀ i, weaklyStrictServiceRel (β i) A D := by
  funext A D
  exact propext (weaklyStrictServiceRel_iSup_iff hbdd)

/-- A family of strict curves is jointly offered iff its pointwise
supremum is: the backlogged-period bounds aggregate under `⨆`. -/
theorem strictServiceRel_iSup_iff {ι : Type*} [Nonempty ι]
    {β : ι → ℝ≥0 → ℝ≥0}
    (hbdd : ∀ t, BddAbove (Set.range fun i => β i t)) {A D : Curve} :
    strictServiceRel (fun t => ⨆ i, β i t) A D ↔
      ∀ i, strictServiceRel (β i) A D := by
  constructor
  · intro hp i
    exact ⟨hp.1, fun s t hst hbl =>
      le_trans (add_le_add le_rfl (le_ciSup (hbdd _) i))
        (hp.2 s t hst hbl)⟩
  · intro hp
    refine ⟨(hp (Classical.arbitrary ι)).1, fun s t hst hbl => ?_⟩
    show D s + (⨆ i, β i (t - s)) ≤ D t
    exact add_ciSup_le _ _ _ fun i => (hp i).2 s t hst hbl

/-- **Families, strict**: the relation of the pointwise supremum is
the intersection of the relations of the family. -/
theorem strictServiceRel_iSup {ι : Type*} [Nonempty ι]
    {β : ι → ℝ≥0 → ℝ≥0}
    (hbdd : ∀ t, BddAbove (Set.range fun i => β i t)) :
    strictServiceRel (fun t => ⨆ i, β i t)
      = fun A D => ∀ i, strictServiceRel (β i) A D := by
  funext A D
  exact propext (strictServiceRel_iSup_iff hbdd)

/-! ## Book restatement (families of service curves)
A system allowing every `βᵢ` of a family as its service curve allows
one equivalent curve: for weakly strict curves the non-decreasing
closure of the pointwise supremum,
`⋂ᵢ S_wstrict(βᵢ) = S_wstrict((supᵢ βᵢ)↑)`, and for strict curves
its super-additive closure,
`⋂ᵢ S_strict(βᵢ) = S_strict((supᵢ βᵢ)*̄)` — stated under the `ℝ≥0`
boundedness side conditions that keep the supremum and the closures
honest (vacuous on the book's extended carrier). The min-plus item
(finite families compare by downward closure) rides `+∞`-valued
arrival witnesses, not representable here; the variable-capacity
item needs one witness capacity shared across the family, which the
book's two-word proof does not construct — both deferred. -/
example {ι : Type*} [Nonempty ι] {β : ι → ℝ≥0 → ℝ≥0}
    (hbdd : ∀ t, BddAbove (Set.range fun i => β i t))
    (hbddNd : ∀ t, BddAbove (Set.range
      (fun u : {u : ℝ≥0 // u ≤ t} => ⨆ i, β i u.1))) :
    weaklyStrictServiceRel (ndClosure (fun t => ⨆ i, β i t))
      = fun A D => ∀ i, weaklyStrictServiceRel (β i) A D := by
  rw [weaklyStrictServiceRel_closure _ hbddNd,
    weaklyStrictServiceRel_iSup hbdd]
example {ι : Type*} [Nonempty ι] {β : ι → ℝ≥0 → ℝ≥0}
    (hbdd : ∀ t, BddAbove (Set.range fun i => β i t))
    (hbddSup : ∀ t, BddAbove (Set.range
      (fun n => maxConvProjPow (fun w => ⨆ i, β i w) n t))) :
    strictServiceRel (superadditiveClosureMax (fun t => ⨆ i, β i t))
      = fun A D => ∀ i, strictServiceRel (β i) A D := by
  rw [strictServiceRel_superadditiveClosureMax _ hbddSup,
    strictServiceRel_iSup hbdd]

/-! ## Min-plus families (the downward-closure criterion, the `⟸` half)
Unlike the weakly-strict/strict families, a min-plus family does *not* collapse to a
single curve: `⋂ᵢ S_mp(βᵢ) = ⋂ⱼ S_mp(β'ⱼ)` holds exactly when the two families have the
same downward closure. The easy direction — mutual domination forces the intersections to
coincide — holds for arbitrary index types (no finiteness): each `β'ⱼ` lies below some
`βᵢ`, so `S_mp(βᵢ) ⊆ S_mp(β'ⱼ)` by min-plus monotony (`A ∗ β'ⱼ ≤ A ∗ βᵢ ≤ D`). The
converse needs the `+∞` staircase / `δ_0` witnesses (`CurveENN`). -/
theorem minimalServiceRel_iInter_eq_of_mutually_dominated {ιβ ιβ' : Type*}
    {β : ιβ → ℝ≥0 → EReal} {β' : ιβ' → ℝ≥0 → EReal}
    (h1 : ∀ j, ∃ i, β' j ≤ β i) (h2 : ∀ i, ∃ j, β i ≤ β' j) :
    (fun A D => ∀ i, minimalServiceRel (β i) A D)
      = (fun A D => ∀ j, minimalServiceRel (β' j) A D) := by
  ext A D
  constructor
  · intro hA j
    obtain ⟨i, hij⟩ := h1 j
    exact ⟨(hA i).1, le_trans (minConv_le_minConv (fun _ => le_rfl) hij) (hA i).2⟩
  · intro hA' i
    obtain ⟨j, hij⟩ := h2 i
    exact ⟨(hA' j).1, le_trans (minConv_le_minConv (fun _ => le_rfl) hij) (hA' j).2⟩

/-- Two families are mutually dominated iff their downward closures (as sets of functions)
agree — pure set theory: each curve lies in its own family's closure, so membership in the
other's closure is exactly domination by one of its members. -/
theorem mutually_dominated_iff_setOf_le_eq {ιβ ιβ' : Type*}
    {β : ιβ → ℝ≥0 → EReal} {β' : ιβ' → ℝ≥0 → EReal} :
    ((∀ j, ∃ i, β' j ≤ β i) ∧ (∀ i, ∃ j, β i ≤ β' j)) ↔
      {f : ℝ≥0 → EReal | ∃ i, f ≤ β i} = {f | ∃ j, f ≤ β' j} := by
  constructor
  · rintro ⟨h1, h2⟩
    ext f
    constructor
    · rintro ⟨i, hfi⟩; obtain ⟨j, hij⟩ := h2 i; exact ⟨j, hfi.trans hij⟩
    · rintro ⟨j, hfj⟩; obtain ⟨i, hij⟩ := h1 j; exact ⟨i, hfj.trans hij⟩
  · intro h
    refine ⟨fun j => ?_, fun i => ?_⟩
    · have hj : β' j ∈ {f : ℝ≥0 → EReal | ∃ j', f ≤ β' j'} := ⟨j, le_refl _⟩
      rw [← h] at hj; exact hj
    · have hi : β i ∈ {f : ℝ≥0 → EReal | ∃ i', f ≤ β i'} := ⟨i, le_refl _⟩
      rw [h] at hi; exact hi

/-- **Min-plus families, the `⟸` half in closure form**: if the two min-plus
families have the same downward closure, their trajectory-set intersections coincide.
(The `⟹` direction needs the `+∞` staircase witness — deferred.) -/
theorem minimalServiceRel_iInter_eq_of_setOf_le_eq {ιβ ιβ' : Type*}
    {β : ιβ → ℝ≥0 → EReal} {β' : ιβ' → ℝ≥0 → EReal}
    (h : {f : ℝ≥0 → EReal | ∃ i, f ≤ β i} = {f | ∃ j, f ≤ β' j}) :
    (fun A D => ∀ i, minimalServiceRel (β i) A D)
      = (fun A D => ∀ j, minimalServiceRel (β' j) A D) :=
  let hmd := mutually_dominated_iff_setOf_le_eq.mpr h
  minimalServiceRel_iInter_eq_of_mutually_dominated hmd.1 hmd.2

end DeepWiki
