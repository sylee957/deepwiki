import DeepWiki.NetworkCalculus.Closures
import DeepWiki.NetworkCalculus.Containers

/-! # Sub-additive closure inclusion `[⁎]` on containers
The unary sub-additive-closure inclusion function of Definition 4.5 (equations
[4.16]/[4.17], Theorem 4.4 closure case): `subadditiveClosureENN` (`⋆`) is
monotone, so it lifts to a *guaranteed* inclusion on closure-side containers.
Because `⋆` is `ℝ≥0∞`-valued, the container here is the `ℝ≥0∞`-valued
`ContainerNN` (the closure dioid), not the `EReal`-valued `Container`. The
headline is `closure_mem`: `f ∈ c → f⋆ ∈ c.closure`, both bounds discharged by
`subadditiveClosureENN_mono`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-! ## An `ℝ≥0∞`-valued container

The closure operator `subadditiveClosureENN` lands in `ℝ≥0∞`, so its container
interval is built over `ℝ≥0 → ℝ≥0∞` (the closure dioid `MinPlusNN`), mirroring
the `EReal`-valued `Container` API. -/

/-- A **closure-side container**: a function-lattice interval `[lo, hi]` of
`ℝ≥0∞`-valued curves with `lo ≤ hi`. This is the `ℝ≥0∞` analogue of `Container`,
the carrier of the sub-additive closure. -/
structure ContainerNN where
  /-- The lower bound `f̲` of the container. -/
  lo : ℝ≥0 → ℝ≥0∞
  /-- The upper bound `f̄` of the container. -/
  hi : ℝ≥0 → ℝ≥0∞
  /-- The bounds are ordered: `lo ≤ hi`. -/
  le : lo ≤ hi

namespace ContainerNN

/-- Plain membership in a closure-side container: `f ∈ [lo, hi]` iff
`lo ≤ f ≤ hi`. -/
def Mem (c : ContainerNN) (f : ℝ≥0 → ℝ≥0∞) : Prop :=
  c.lo ≤ f ∧ f ≤ c.hi

instance : Membership (ℝ≥0 → ℝ≥0∞) ContainerNN where
  mem c f := c.Mem f

/-- `f ∈ c ↔ c.lo ≤ f ∧ f ≤ c.hi` (unfolds membership). -/
theorem mem_iff (c : ContainerNN) (f : ℝ≥0 → ℝ≥0∞) :
    f ∈ c ↔ c.lo ≤ f ∧ f ≤ c.hi := Iff.rfl

/-- The lower bound is a member: `lo ∈ [lo, hi]`. -/
theorem lo_mem (c : ContainerNN) : c.lo ∈ c := ⟨le_rfl, c.le⟩

/-- The upper bound is a member: `hi ∈ [lo, hi]`. -/
theorem hi_mem (c : ContainerNN) : c.hi ∈ c := ⟨c.le, le_rfl⟩

/-- Membership is squeezed: any member dominates the lower bound, pointwise. -/
theorem lo_le_of_mem {c : ContainerNN} {f : ℝ≥0 → ℝ≥0∞} (h : f ∈ c) : c.lo ≤ f := h.1

/-- Membership is squeezed: any member lies below the upper bound, pointwise. -/
theorem le_hi_of_mem {c : ContainerNN} {f : ℝ≥0 → ℝ≥0∞} (h : f ∈ c) : f ≤ c.hi := h.2

/-- The **singleton container** `[f, f]`: the exact (zero-uncertainty)
container whose only member is `f`. -/
def singleton (f : ℝ≥0 → ℝ≥0∞) : ContainerNN where
  lo := f
  hi := f
  le := le_rfl

/-- `g ∈ singleton f ↔ g = f`: the singleton container pins its single member. -/
theorem mem_singleton_iff (f g : ℝ≥0 → ℝ≥0∞) : g ∈ singleton f ↔ g = f := by
  constructor
  · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
  · rintro rfl; exact ⟨le_rfl, le_rfl⟩

/-- Inclusion of closure-side containers (as sets of curves): `c ⊆ d` iff every
member of `c` is a member of `d`. -/
def Subset (c d : ContainerNN) : Prop := ∀ f, f ∈ c → f ∈ d

/-- A wider interval contains a narrower one: `d.lo ≤ c.lo` and `c.hi ≤ d.hi`
give `c ⊆ d`. -/
theorem subset_of_le {c d : ContainerNN} (hlo : d.lo ≤ c.lo) (hhi : c.hi ≤ d.hi) :
    Subset c d :=
  fun _ hf => ⟨hlo.trans hf.1, hf.2.trans hhi⟩

/-! ## Definition 4.5 [4.16]/[4.17] — the sub-additive closure inclusion `[⁎]`

The closure inclusion `f[⁎]` of a container `f = [f̲, f̄]` applies the
sub-additive closure `⋆ = subadditiveClosureENN` to each bound. The book's
canonical form additionally canonicalizes the bounds with the convex/concave
hulls (`C_vx`/`C_cv`); see the module note. The *soundness* of the inclusion
(Theorem 4.4) is pure monotonicity of `⋆`. -/

/-- **Closure inclusion `f[⁎]`** of a container: apply the sub-additive closure
`⋆` to each bound, `[f̲, f̄] ↦ [f̲⋆, f̄⋆]`. Ordering is `subadditiveClosureENN_mono`
applied to `c.le`. -/
noncomputable def closure (c : ContainerNN) : ContainerNN where
  lo := subadditiveClosureENN c.lo
  hi := subadditiveClosureENN c.hi
  le := fun t => subadditiveClosureENN_mono c.lo c.hi (fun s => c.le s) t

/-- The closure container's lower bound is `f̲⋆`. -/
@[simp] theorem closure_lo (c : ContainerNN) :
    c.closure.lo = subadditiveClosureENN c.lo := rfl

/-- The closure container's upper bound is `f̄⋆`. -/
@[simp] theorem closure_hi (c : ContainerNN) :
    c.closure.hi = subadditiveClosureENN c.hi := rfl

/-! ## Theorem 4.4 (closure case) — inclusion-soundness `f ∈ f → f⋆ ∈ f[⁎]` -/

/-- **Theorem 4.4, sub-additive closure case.** The closure inclusion is sound:
if `f ∈ c` then `f⋆ ∈ c.closure`. Both bounds come from
`subadditiveClosureENN_mono`: `c.lo ≤ f` gives `c.lo⋆ ≤ f⋆`, and `f ≤ c.hi`
gives `f⋆ ≤ c.hi⋆`. -/
theorem closure_mem {c : ContainerNN} {f : ℝ≥0 → ℝ≥0∞} (h : f ∈ c) :
    subadditiveClosureENN f ∈ c.closure :=
  ⟨fun t => subadditiveClosureENN_mono c.lo f (fun s => h.1 s) t,
   fun t => subadditiveClosureENN_mono f c.hi (fun s => h.2 s) t⟩

/-! ## Satellites -/

/-- The closure inclusion is monotone for the bound ordering: widening the
bounds (`d.lo ≤ c.lo`, `c.hi ≤ d.hi`) widens the closure container,
`c.closure ⊆ d.closure`. -/
theorem closure_subset_closure {c d : ContainerNN}
    (hlo : d.lo ≤ c.lo) (hhi : c.hi ≤ d.hi) :
    Subset c.closure d.closure :=
  subset_of_le
    (fun t => subadditiveClosureENN_mono d.lo c.lo (fun s => hlo s) t)
    (fun t => subadditiveClosureENN_mono c.hi d.hi (fun s => hhi s) t)

/-- The closure of a singleton container is the singleton of the plain closure:
`(singleton f).closure = singleton f⋆`. -/
theorem closure_singleton (f : ℝ≥0 → ℝ≥0∞) :
    (singleton f).closure = singleton (subadditiveClosureENN f) := rfl

/-! ## Faithfulness checks (anonymous restatements vs the book) -/

-- Definition 4.5 [4.16]/[4.17] (algebraic core): `f[⁎] = [f̲⋆, f̄⋆]`.
example (c : ContainerNN) :
    c.closure.lo = subadditiveClosureENN c.lo
      ∧ c.closure.hi = subadditiveClosureENN c.hi := ⟨rfl, rfl⟩

-- Theorem 4.4 (closure case): `f ∈ f ⟹ f⋆ ∈ f[⁎]`.
example {c : ContainerNN} {f : ℝ≥0 → ℝ≥0∞} (h : f ∈ c) :
    subadditiveClosureENN f ∈ c.closure := closure_mem h

end ContainerNN

end DeepWiki
