import DeepWiki.NetworkCalculus.LegendreFenchelConcave
import DeepWiki.NetworkCalculus.Concave
import DeepWiki.NetworkCalculus.Convex
import DeepWiki.NetworkCalculus.ContainerClosure

/-! # The `ℝ≥0∞`-valued convex and concave hulls `CcvENN` / `CvxENN`
The `ℝ≥0∞` mirror of the `EReal` concave hull `Ccv`
(`DeepWiki.NetworkCalculus.LegendreFenchelConcave`), built to canonicalize the
closure bounds of DNC §4.4 Def 4.5 [4.16]/[4.17] over the **`ℝ≥0∞` closure
carrier** (the closure operator `subadditiveClosureENN` and `ContainerNN` are
`ℝ≥0∞`-valued, so the `EReal` `Ccv` does not apply to them directly).

`CcvENN f` is the smallest concave function `≥ f` (the pointwise `⨅` of concave
majorants); `CvxENN f` is the order-dual, the largest convex function `≤ f` (the
pointwise `⨆` of convex minorants). The concavity/convexity predicates
`IsConcaveENN`/`IsConvexENN` are the native `ℝ≥0∞`-valued midpoint-chord
predicates (mirroring `IsConcaveEReal`/`IsConvexEReal`, with weights coerced
`ℝ≥0 → ℝ≥0∞` and `ℝ≥0∞` arithmetic — no `(+∞)+(−∞)` collision arises since
`ℝ≥0∞` has a single infinity). The closing tie-in shows the canonicalized
container-closure bounds `[CvxENN c.lo⋆, CcvENN c.hi⋆]` are convex/concave. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-! ## The `ℝ≥0∞` concavity/convexity predicates -/

/-- A curve `f : ℝ≥0 → ℝ≥0∞` is **concave** when it lies above each of its
chords: for `p ≤ 1`, `↑p * f s + ↑(1 - p) * f t ≤ f (p * s + (1 - p) * t)`, with
weights coerced `ℝ≥0 → ℝ≥0∞` and `ℝ≥0∞` multiplication/addition. -/
def IsConcaveENN (f : ℝ≥0 → ℝ≥0∞) : Prop :=
  ∀ s t : ℝ≥0, ∀ p : ℝ≥0, p ≤ 1 →
    (p : ℝ≥0∞) * f s + ((1 - p : ℝ≥0) : ℝ≥0∞) * f t ≤ f (p * s + (1 - p) * t)

/-- A curve `f : ℝ≥0 → ℝ≥0∞` is **convex** when it lies below each of its chords:
for `p ≤ 1`, `f (p * s + (1 - p) * t) ≤ ↑p * f s + ↑(1 - p) * f t`, with weights
coerced `ℝ≥0 → ℝ≥0∞` and `ℝ≥0∞` multiplication/addition. -/
def IsConvexENN (f : ℝ≥0 → ℝ≥0∞) : Prop :=
  ∀ s t : ℝ≥0, ∀ p : ℝ≥0, p ≤ 1 →
    f (p * s + (1 - p) * t) ≤ (p : ℝ≥0∞) * f s + ((1 - p : ℝ≥0) : ℝ≥0∞) * f t

/-! ## The concave hull `CcvENN` -/

/-- The set of concave curves lying pointwise above `f : ℝ≥0 → ℝ≥0∞`. -/
def concaveMajorantsENN (f : ℝ≥0 → ℝ≥0∞) : Set (ℝ≥0 → ℝ≥0∞) :=
  {g | IsConcaveENN g ∧ f ≤ g}

/-- The constant `⊤` curve is a concave majorant of any `f`, so
`concaveMajorantsENN f` is never empty. -/
theorem top_mem_concaveMajorantsENN (f : ℝ≥0 → ℝ≥0∞) :
    (fun _ : ℝ≥0 => (⊤ : ℝ≥0∞)) ∈ concaveMajorantsENN f := by
  refine ⟨?_, ?_⟩
  · intro s t p _; exact le_top
  · intro x; exact le_top

/-- **The `ℝ≥0∞` concave hull** `CcvENN f`: the pointwise infimum of all concave
curves lying above `f` — the smallest concave function `≥ f` (the `ℝ≥0∞` mirror
of `Ccv`, DNC eq. [4.6]). -/
noncomputable def CcvENN (f : ℝ≥0 → ℝ≥0∞) : ℝ≥0 → ℝ≥0∞ :=
  fun t => ⨅ g : concaveMajorantsENN f, (g : ℝ≥0 → ℝ≥0∞) t

/-- `CcvENN f t = ⨅ g ∈ concaveMajorantsENN f, g t` (the defining infimum). -/
theorem CcvENN_apply (f : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    CcvENN f t = ⨅ g : concaveMajorantsENN f, (g : ℝ≥0 → ℝ≥0∞) t := rfl

/-- Each concave majorant bounds the hull from above: `CcvENN f t ≤ g t` for
every `g ∈ concaveMajorantsENN f`. -/
theorem CcvENN_apply_le {f : ℝ≥0 → ℝ≥0∞} {g : ℝ≥0 → ℝ≥0∞}
    (hg : g ∈ concaveMajorantsENN f) (t : ℝ≥0) : CcvENN f t ≤ g t :=
  iInf_le (fun g : concaveMajorantsENN f => (g : ℝ≥0 → ℝ≥0∞) t) ⟨g, hg⟩

/-- **The `ℝ≥0∞` concave hull majorizes `f`**: `f ≤ CcvENN f`. -/
theorem le_CcvENN (f : ℝ≥0 → ℝ≥0∞) : f ≤ CcvENN f := by
  intro t
  rw [CcvENN_apply]
  exact le_iInf fun g => g.2.2 t

/-- **The `ℝ≥0∞` concave hull is the least concave majorant**: for any concave
`g ≥ f`, `CcvENN f ≤ g` pointwise. -/
theorem CcvENN_le {f g : ℝ≥0 → ℝ≥0∞} (hgc : IsConcaveENN g) (hgf : f ≤ g) :
    CcvENN f ≤ g := fun t => CcvENN_apply_le ⟨hgc, hgf⟩ t

/-- **The `ℝ≥0∞` concave hull is concave**: a pointwise infimum of concave curves
is concave. For each chord, push one majorant `g` through: the two scaled hull
terms are below `g`'s, and `g`'s chord finishes. -/
theorem isConcaveENN_CcvENN (f : ℝ≥0 → ℝ≥0∞) : IsConcaveENN (CcvENN f) := by
  intro s t p hp
  rw [CcvENN_apply]
  refine le_iInf fun g => ?_
  refine le_trans ?_ (g.2.1 s t p hp)
  exact add_le_add
    (mul_le_mul_right (CcvENN_apply_le g.2 s) _)
    (mul_le_mul_right (CcvENN_apply_le g.2 t) _)

/-- **A concave curve is its own `ℝ≥0∞` hull**: `IsConcaveENN f → CcvENN f = f`. -/
theorem CcvENN_eq_self_of_isConcaveENN {f : ℝ≥0 → ℝ≥0∞} (hf : IsConcaveENN f) :
    CcvENN f = f :=
  le_antisymm (CcvENN_le hf le_rfl) (le_CcvENN f)

/-- **Idempotence of the `ℝ≥0∞` concave hull**: `CcvENN (CcvENN f) = CcvENN f`. -/
theorem CcvENN_CcvENN (f : ℝ≥0 → ℝ≥0∞) : CcvENN (CcvENN f) = CcvENN f :=
  CcvENN_eq_self_of_isConcaveENN (isConcaveENN_CcvENN f)

/-- **The `ℝ≥0∞` concave hull is monotone**: `f ≤ g → CcvENN f ≤ CcvENN g`. -/
theorem CcvENN_mono {f g : ℝ≥0 → ℝ≥0∞} (h : f ≤ g) : CcvENN f ≤ CcvENN g :=
  CcvENN_le (isConcaveENN_CcvENN g) (le_trans h (le_CcvENN g))

/-! ## The convex hull `CvxENN` (order-dual of `CcvENN`) -/

/-- The set of convex curves lying pointwise below `f : ℝ≥0 → ℝ≥0∞`. -/
def convexMinorantsENN (f : ℝ≥0 → ℝ≥0∞) : Set (ℝ≥0 → ℝ≥0∞) :=
  {g | IsConvexENN g ∧ g ≤ f}

/-- The constant `⊥ = 0` curve is a convex minorant of any `f`, so
`convexMinorantsENN f` is never empty. -/
theorem bot_mem_convexMinorantsENN (f : ℝ≥0 → ℝ≥0∞) :
    (fun _ : ℝ≥0 => (⊥ : ℝ≥0∞)) ∈ convexMinorantsENN f := by
  refine ⟨?_, ?_⟩
  · intro s t p _; exact bot_le
  · intro x; exact bot_le

/-- **The `ℝ≥0∞` convex hull** `CvxENN f`: the pointwise supremum of all convex
curves lying below `f` — the largest convex function `≤ f` (the order-dual of
`CcvENN`, the `C_vx` piece of DNC §4.4). -/
noncomputable def CvxENN (f : ℝ≥0 → ℝ≥0∞) : ℝ≥0 → ℝ≥0∞ :=
  fun t => ⨆ g : convexMinorantsENN f, (g : ℝ≥0 → ℝ≥0∞) t

/-- `CvxENN f t = ⨆ g ∈ convexMinorantsENN f, g t` (the defining supremum). -/
theorem CvxENN_apply (f : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) :
    CvxENN f t = ⨆ g : convexMinorantsENN f, (g : ℝ≥0 → ℝ≥0∞) t := rfl

/-- Each convex minorant bounds the hull from below: `g t ≤ CvxENN f t` for every
`g ∈ convexMinorantsENN f`. -/
theorem le_CvxENN_apply {f : ℝ≥0 → ℝ≥0∞} {g : ℝ≥0 → ℝ≥0∞}
    (hg : g ∈ convexMinorantsENN f) (t : ℝ≥0) : g t ≤ CvxENN f t :=
  le_iSup (fun g : convexMinorantsENN f => (g : ℝ≥0 → ℝ≥0∞) t) ⟨g, hg⟩

/-- **The `ℝ≥0∞` convex hull is minorized by `f`**: `CvxENN f ≤ f`. -/
theorem CvxENN_le_self (f : ℝ≥0 → ℝ≥0∞) : CvxENN f ≤ f := by
  intro t
  rw [CvxENN_apply]
  exact iSup_le fun g => g.2.2 t

/-- **The `ℝ≥0∞` convex hull is the greatest convex minorant**: for any convex
`g ≤ f`, `g ≤ CvxENN f` pointwise. -/
theorem le_CvxENN {f g : ℝ≥0 → ℝ≥0∞} (hgc : IsConvexENN g) (hgf : g ≤ f) :
    g ≤ CvxENN f := fun t => le_CvxENN_apply ⟨hgc, hgf⟩ t

/-- **The `ℝ≥0∞` convex hull is convex**: a pointwise supremum of convex curves is
convex. For each chord, push one minorant `g` through: `g`'s chord lands below,
and the two scaled hull terms dominate `g`'s. -/
theorem isConvexENN_CvxENN (f : ℝ≥0 → ℝ≥0∞) : IsConvexENN (CvxENN f) := by
  intro s t p hp
  rw [CvxENN_apply]
  refine iSup_le fun g => ?_
  refine le_trans (g.2.1 s t p hp) ?_
  exact add_le_add
    (mul_le_mul_right (le_CvxENN_apply g.2 s) _)
    (mul_le_mul_right (le_CvxENN_apply g.2 t) _)

/-- **A convex curve is its own `ℝ≥0∞` hull**: `IsConvexENN f → CvxENN f = f`. -/
theorem CvxENN_eq_self_of_isConvexENN {f : ℝ≥0 → ℝ≥0∞} (hf : IsConvexENN f) :
    CvxENN f = f :=
  le_antisymm (CvxENN_le_self f) (le_CvxENN hf le_rfl)

/-- **Idempotence of the `ℝ≥0∞` convex hull**: `CvxENN (CvxENN f) = CvxENN f`. -/
theorem CvxENN_CvxENN (f : ℝ≥0 → ℝ≥0∞) : CvxENN (CvxENN f) = CvxENN f :=
  CvxENN_eq_self_of_isConvexENN (isConvexENN_CvxENN f)

/-- **The `ℝ≥0∞` convex hull is monotone**: `f ≤ g → CvxENN f ≤ CvxENN g`. -/
theorem CvxENN_mono {f g : ℝ≥0 → ℝ≥0∞} (h : f ≤ g) : CvxENN f ≤ CvxENN g :=
  le_CvxENN (isConvexENN_CvxENN f) (le_trans (CvxENN_le_self f) h)

/-! ## DNC §4.4 Def 4.5 [4.16]/[4.17] — canonicalized container-closure bounds
The book's canonical closure bound applies the convex hull to the lower closure
bound and the concave hull to the upper one: a container `c` has canonical
closure `[CvxENN c.lo⋆, CcvENN c.hi⋆]`. These canonical bounds are by
construction convex (lower) and concave (upper). -/

/-- **The canonicalized lower closure bound is convex**: `CvxENN c.lo⋆` (the
`C_vx`-canonicalization of the lower closure bound, DNC §4.4 [4.16]/[4.17]). -/
theorem isConvexENN_CvxENN_closure_lo (c : ContainerNN) :
    IsConvexENN (CvxENN c.closure.lo) :=
  isConvexENN_CvxENN c.closure.lo

/-- **The canonicalized upper closure bound is concave**: `CcvENN c.hi⋆` (the
`C_cv`-canonicalization of the upper closure bound, DNC §4.4 [4.16]/[4.17]). -/
theorem isConcaveENN_CcvENN_closure_hi (c : ContainerNN) :
    IsConcaveENN (CcvENN c.closure.hi) :=
  isConcaveENN_CcvENN c.closure.hi

/-- The canonicalized lower bound minorizes the closure's lower bound:
`CvxENN c.lo⋆ ≤ c.lo⋆`. -/
theorem CvxENN_closure_lo_le (c : ContainerNN) :
    CvxENN c.closure.lo ≤ c.closure.lo :=
  CvxENN_le_self c.closure.lo

/-- The canonicalized upper bound majorizes the closure's upper bound:
`c.hi⋆ ≤ CcvENN c.hi⋆`. -/
theorem le_CcvENN_closure_hi (c : ContainerNN) :
    c.closure.hi ≤ CcvENN c.closure.hi :=
  le_CcvENN c.closure.hi

/-! ## Faithfulness checks (anonymous restatements vs the book) -/

-- The concave hull (DNC eq. [4.6], `ℝ≥0∞` carrier): concave, majorizes `f`,
-- least such, fixes concave curves.
example (f : ℝ≥0 → ℝ≥0∞) : IsConcaveENN (CcvENN f) := isConcaveENN_CcvENN f
example (f : ℝ≥0 → ℝ≥0∞) : f ≤ CcvENN f := le_CcvENN f
example {f g : ℝ≥0 → ℝ≥0∞} (hc : IsConcaveENN g) (hfg : f ≤ g) : CcvENN f ≤ g :=
  CcvENN_le hc hfg
example {f : ℝ≥0 → ℝ≥0∞} (hf : IsConcaveENN f) : CcvENN f = f :=
  CcvENN_eq_self_of_isConcaveENN hf

-- The convex hull (order-dual): convex, minorized by `f`, greatest such, fixes
-- convex curves.
example (f : ℝ≥0 → ℝ≥0∞) : IsConvexENN (CvxENN f) := isConvexENN_CvxENN f
example (f : ℝ≥0 → ℝ≥0∞) : CvxENN f ≤ f := CvxENN_le_self f
example {f g : ℝ≥0 → ℝ≥0∞} (hc : IsConvexENN g) (hgf : g ≤ f) : g ≤ CvxENN f :=
  le_CvxENN hc hgf
example {f : ℝ≥0 → ℝ≥0∞} (hf : IsConvexENN f) : CvxENN f = f :=
  CvxENN_eq_self_of_isConvexENN hf

end DeepWiki
