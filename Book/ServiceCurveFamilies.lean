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

end DeepWiki
