import DeepWiki.NetworkCalculus.LegendreFenchelMoreauConvex
import DeepWiki.NetworkCalculus.FunctionDioids

/-! # Containers of (min,plus) functions
A **container** is a function-lattice interval `[lo, hi]` of curves
`ℝ≥0 → EReal` (`lo ≤ hi`): an explicit lower and upper bound that *contains* a
result in a guaranteed way (Definition 4.2). A container's elements are the
curves squeezed between its bounds, optionally refined to those sharing the
lower bound's Legendre–Fenchel transform (`legendre`).

The Legendre–Fenchel transform `legendre` (the (min,+) `𝓛`) plays the role of
the convex hull: its biconjugate `legendre ∘ legendre` is the least convex
representative of a class of curves with a common transform, and
`sameLegendre` (`legendre f = legendre g`) is the congruence whose classes are
the containers' uncertainty (Propositions 4.2 and 4.3). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-! ## Definition 4.2 — the container datatype -/

/-- A **container**: a function-lattice interval `[lo, hi]` of curves
`ℝ≥0 → EReal` with `lo ≤ hi`. It bounds an uncertain curve between an explicit
lower and upper function. -/
structure Container where
  /-- The lower bound `f̲` of the container. -/
  lo : ℝ≥0 → EReal
  /-- The upper bound `f̄` of the container. -/
  hi : ℝ≥0 → EReal
  /-- The bounds are ordered: `lo ≤ hi`. -/
  le : lo ≤ hi

namespace Container

/-- Plain membership in a container: `f ∈ [lo, hi]` iff `lo ≤ f ≤ hi`. This is
the interval `[f̲, f̄]`, before the Legendre–Fenchel refinement. -/
def Mem (c : Container) (f : ℝ≥0 → EReal) : Prop :=
  c.lo ≤ f ∧ f ≤ c.hi

instance : Membership (ℝ≥0 → EReal) Container where
  mem c f := c.Mem f

/-- `f ∈ c ↔ c.lo ≤ f ∧ f ≤ c.hi` (unfolds membership). -/
theorem mem_iff (c : Container) (f : ℝ≥0 → EReal) :
    f ∈ c ↔ c.lo ≤ f ∧ f ≤ c.hi := Iff.rfl

/-- The lower bound is a member: `lo ∈ [lo, hi]`. -/
theorem lo_mem (c : Container) : c.lo ∈ c := ⟨le_rfl, c.le⟩

/-- The upper bound is a member: `hi ∈ [lo, hi]`. -/
theorem hi_mem (c : Container) : c.hi ∈ c := ⟨c.le, le_rfl⟩

/-- A container is nonempty (it always contains its lower bound). -/
theorem nonempty (c : Container) : ∃ f, f ∈ c := ⟨c.lo, c.lo_mem⟩

/-- The carrier set `{f | lo ≤ f ≤ hi}` of a container. -/
def toSet (c : Container) : Set (ℝ≥0 → EReal) := {f | f ∈ c}

/-- `f ∈ c.toSet ↔ f ∈ c`. -/
theorem mem_toSet (c : Container) (f : ℝ≥0 → EReal) : f ∈ c.toSet ↔ f ∈ c := Iff.rfl

/-- Membership is squeezed: any member lies between the bounds, pointwise. -/
theorem lo_le_of_mem {c : Container} {f : ℝ≥0 → EReal} (h : f ∈ c) : c.lo ≤ f := h.1

/-- Membership is squeezed: any member lies below the upper bound, pointwise. -/
theorem le_hi_of_mem {c : Container} {f : ℝ≥0 → EReal} (h : f ∈ c) : f ≤ c.hi := h.2

/-- The **singleton container** `[f, f]`: the exact (zero-uncertainty)
container whose only member is `f`. -/
def singleton (f : ℝ≥0 → EReal) : Container where
  lo := f
  hi := f
  le := le_rfl

/-- `g ∈ singleton f ↔ g = f`: the singleton container pins its single member. -/
theorem mem_singleton_iff (f g : ℝ≥0 → EReal) : g ∈ singleton f ↔ g = f := by
  constructor
  · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
  · rintro rfl; exact ⟨le_rfl, le_rfl⟩

/-- The **full container** `[⊥, ⊤]`: every curve is a member (the no-information
edge case). -/
noncomputable def univ : Container where
  lo := ⊥
  hi := ⊤
  le := bot_le

/-- The full container's lower bound is `⊥`. -/
@[simp] theorem univ_lo : univ.lo = ⊥ := rfl

/-- The full container's upper bound is `⊤`. -/
@[simp] theorem univ_hi : univ.hi = ⊤ := rfl

/-- Every curve belongs to the full container `[⊥, ⊤]`. -/
theorem mem_univ (f : ℝ≥0 → EReal) : f ∈ univ :=
  (mem_iff univ f).mpr (by rw [univ_lo, univ_hi]; exact ⟨bot_le, le_top⟩)

/-- Inclusion of containers (as sets of curves): `c ⊆ d` iff every member of
`c` is a member of `d`. -/
def Subset (c d : Container) : Prop := ∀ f, f ∈ c → f ∈ d

/-- A wider interval contains a narrower one: `d.lo ≤ c.lo` and `c.hi ≤ d.hi`
give `c ⊆ d`. -/
theorem subset_of_le {c d : Container} (hlo : d.lo ≤ c.lo) (hhi : c.hi ≤ d.hi) :
    Subset c d :=
  fun _ hf => ⟨hlo.trans hf.1, hf.2.trans hhi⟩

/-- Every container is included in the full container `[⊥, ⊤]`. -/
theorem subset_univ (c : Container) : Subset c univ := fun f _ => mem_univ f

/-! ## The Legendre–Fenchel congruence (Proposition 4.3 scaffolding)

Two curves are **equivalent modulo `𝓛`** when they have the same
Legendre–Fenchel transform. This is the congruence `≡_𝓛` of equation [3.13]
underlying the quotient dioid `ℱ↑/𝓛` (Proposition 4.3). -/

/-- The Legendre–Fenchel congruence `f ≡_𝓛 g`: `f` and `g` have the same
transform `legendre f = legendre g`. -/
def SameLegendre (f g : ℝ≥0 → EReal) : Prop := legendre f = legendre g

/-- `SameLegendre f g ↔ legendre f = legendre g` (unfolds the congruence). -/
theorem sameLegendre_iff (f g : ℝ≥0 → EReal) :
    SameLegendre f g ↔ legendre f = legendre g := Iff.rfl

/-- The Legendre–Fenchel congruence is reflexive. -/
@[refl] theorem SameLegendre.refl (f : ℝ≥0 → EReal) : SameLegendre f f := rfl

/-- The Legendre–Fenchel congruence is symmetric. -/
@[symm] theorem SameLegendre.symm {f g : ℝ≥0 → EReal} (h : SameLegendre f g) :
    SameLegendre g f := Eq.symm h

/-- The Legendre–Fenchel congruence is transitive. -/
@[trans] theorem SameLegendre.trans {f g h : ℝ≥0 → EReal}
    (hfg : SameLegendre f g) (hgh : SameLegendre g h) : SameLegendre f h := Eq.trans hfg hgh

/-- The Legendre–Fenchel congruence is an equivalence relation. -/
theorem equivalence_sameLegendre : Equivalence SameLegendre :=
  ⟨SameLegendre.refl, SameLegendre.symm, SameLegendre.trans⟩

/-- The `Setoid` of curves under the Legendre–Fenchel congruence — the setup
for the quotient `ℱ↑/𝓛` (Proposition 4.3). -/
def legendreSetoid : Setoid (ℝ≥0 → EReal) := ⟨SameLegendre, equivalence_sameLegendre⟩

/-! ## The Legendre–Fenchel equivalence class -/

/-- The equivalence class `[f]_𝓛` of `f` modulo the Legendre–Fenchel transform:
all curves with the same transform as `f`. -/
def legendreClass (f : ℝ≥0 → EReal) : Set (ℝ≥0 → EReal) := {g | SameLegendre f g}

/-- `g ∈ [f]_𝓛 ↔ legendre f = legendre g`. -/
theorem mem_legendreClass (f g : ℝ≥0 → EReal) :
    g ∈ legendreClass f ↔ legendre f = legendre g := Iff.rfl

/-- `f` belongs to its own class `[f]_𝓛`. -/
theorem self_mem_legendreClass (f : ℝ≥0 → EReal) : f ∈ legendreClass f := rfl

/-! ## Proposition 4.2 — the biconjugate as least convex representative

The library has no standalone convex-hull operator `Cvx`; its role is played by
the **biconjugate** `legendre ∘ legendre`. In the (min,+) Fenchel–Moreau theory
the biconjugate is the largest convex non-decreasing curve below `f`
(`legendre_legendre_le`), it shares `f`'s transform (`legendre_biconj`), and it
is the *least* representative of `[f]_𝓛` (`biconj_le_of_sameLegendre`) — exactly
the content of Proposition 4.2 with `𝓛(𝓛 ·)` standing for the convex hull. -/

/-- The **biconjugate** `f̂ = 𝓛(𝓛 f)` of a curve — the (min,+) convex-hull /
least-representative operator. -/
noncomputable def biconj (f : ℝ≥0 → EReal) : ℝ≥0 → EReal := legendre (legendre f)

/-- `biconj f = legendre (legendre f)` (unfolds the biconjugate). -/
theorem biconj_apply (f : ℝ≥0 → EReal) : biconj f = legendre (legendre f) := rfl

/-- **The biconjugate lies below the function**: `f̂ ≤ f` pointwise
(`legendre_legendre_le`) — `Cvx f ≤ f`. -/
theorem biconj_le (f : ℝ≥0 → EReal) (u : ℝ≥0) : biconj f u ≤ f u :=
  legendre_legendre_le f u

/-- **The biconjugate has the same transform as `f`**: `𝓛(f̂) = 𝓛 f`. So `f̂` is
a representative of `[f]_𝓛` (it lies in the same equivalence class). -/
theorem legendre_biconj (f : ℝ≥0 → EReal) : legendre (biconj f) = legendre f :=
  legendre_legendre_legendre f

/-- `f̂ ∈ [f]_𝓛`: the biconjugate is a member of `f`'s Legendre–Fenchel class. -/
theorem biconj_mem_legendreClass (f : ℝ≥0 → EReal) : biconj f ∈ legendreClass f :=
  (legendre_biconj f).symm

/-- **Same transform iff same convex hull.** Two curves have the same
Legendre–Fenchel transform iff they have the same biconjugate ("convex hull"):
`legendre f = legendre g ↔ biconj f = biconj g`. Forward: apply `legendre`.
Backward: apply `legendre` and use `legendre (biconj ·) = legendre ·`. -/
theorem sameLegendre_iff_biconj_eq (f g : ℝ≥0 → EReal) :
    legendre f = legendre g ↔ biconj f = biconj g := by
  constructor
  · intro h; unfold biconj; rw [h]
  · intro h
    have := congrArg legendre h
    rwa [legendre_biconj, legendre_biconj] at this

/-- **The biconjugate is the least representative of `[f]_𝓛`**: any curve `g`
with the same transform as `f` dominates `f̂` pointwise, `f̂ ≤ g`. Together with
`biconj_mem_legendreClass` this says `f̂` is the minimum of `[f]_𝓛`
(`∀ f' ∈ [f]_𝓛, Cvx f ≤ f'`). -/
theorem biconj_le_of_sameLegendre {f g : ℝ≥0 → EReal} (h : legendre f = legendre g)
    (u : ℝ≥0) : biconj f u ≤ g u := by
  have : biconj f = biconj g := (sameLegendre_iff_biconj_eq f g).mp h
  rw [this]; exact biconj_le g u

/-- **Equal biconjugates give equal transforms** (the easy half, isolated): if
`Cvx f = Cvx g` then `𝓛 f = 𝓛 g`, because `legendre` factors through the
biconjugate. -/
theorem sameLegendre_of_biconj_eq {f g : ℝ≥0 → EReal} (h : biconj f = biconj g) :
    SameLegendre f g := (sameLegendre_iff_biconj_eq f g).mpr h

/-! ### Proposition 4.2 on convex curves — the biconjugate IS the curve

When `f` is finite, convex and non-decreasing, the Fenchel–Moreau involution
`legendre_legendre_eq_of_isConvexEReal` gives `f̂ = f`, so the biconjugate
"convex hull" of an already-convex curve is itself; two convex curves with the
same transform are then *equal*. -/

/-- For a finite convex non-decreasing curve, the biconjugate is the curve
itself: `f̂ = f` (Fenchel–Moreau involution). -/
theorem biconj_eq_self_of_isConvex {f : ℝ≥0 → EReal}
    (hfin : ∀ x, f x ≠ ⊤ ∧ f x ≠ ⊥) (hcv : IsConvexEReal f) (hmono : Monotone f) :
    biconj f = f :=
  legendre_legendre_eq_of_isConvexEReal hfin hcv hmono

/-- **Injectivity of `𝓛` on convex curves.** Two finite convex non-decreasing
curves with the same Legendre–Fenchel transform are equal — the transform is
injective on the convex representatives, so each `[f]_𝓛` has a unique convex
member. -/
theorem eq_of_sameLegendre_of_isConvex {f g : ℝ≥0 → EReal}
    (hffin : ∀ x, f x ≠ ⊤ ∧ f x ≠ ⊥) (hfcv : IsConvexEReal f) (hfmono : Monotone f)
    (hgfin : ∀ x, g x ≠ ⊤ ∧ g x ≠ ⊥) (hgcv : IsConvexEReal g) (hgmono : Monotone g)
    (h : SameLegendre f g) : f = g := by
  have hf : biconj f = f := biconj_eq_self_of_isConvex hffin hfcv hfmono
  have hg : biconj g = g := biconj_eq_self_of_isConvex hgfin hgcv hgmono
  have := (sameLegendre_iff_biconj_eq f g).mp h
  rw [hf, hg] at this; exact this

/-! ## The Legendre–Fenchel container

A container refined by the Legendre–Fenchel congruence (Definition 4.2's
`[f̲, f̄]_𝓛 = [f̲, f̄] ∩ [f̲]_𝓛`): the curves between the bounds that *also*
share the lower bound's transform. -/

/-- LF-refined membership `f ∈ [lo, hi]_𝓛`: `f` lies in the interval *and*
shares the lower bound's Legendre–Fenchel transform
(`[f̲, f̄]_𝓛 = [f̲, f̄] ∩ [f̲]_𝓛`). -/
def MemL (c : Container) (f : ℝ≥0 → EReal) : Prop :=
  f ∈ c ∧ SameLegendre c.lo f

/-- `c.MemL f ↔ (lo ≤ f ≤ hi) ∧ legendre lo = legendre f`. -/
theorem memL_iff (c : Container) (f : ℝ≥0 → EReal) :
    c.MemL f ↔ (c.lo ≤ f ∧ f ≤ c.hi) ∧ legendre c.lo = legendre f := Iff.rfl

/-- An LF-member is a plain member: `[f̲, f̄]_𝓛 ⊆ [f̲, f̄]`. -/
theorem mem_of_memL {c : Container} {f : ℝ≥0 → EReal} (h : c.MemL f) : f ∈ c := h.1

/-- The lower bound is an LF-member of its own container. -/
theorem lo_memL (c : Container) : c.MemL c.lo := ⟨c.lo_mem, rfl⟩

/-- LF-members are pairwise equivalent: any two members of `[f̲, f̄]_𝓛` have the
same Legendre–Fenchel transform. -/
theorem sameLegendre_of_memL {c : Container} {f g : ℝ≥0 → EReal}
    (hf : c.MemL f) (hg : c.MemL g) : SameLegendre f g := hf.2.symm.trans hg.2

/-- The biconjugate of any LF-member is the common least representative: it
equals the biconjugate of the lower bound. -/
theorem biconj_eq_of_memL {c : Container} {f : ℝ≥0 → EReal} (h : c.MemL f) :
    biconj f = biconj c.lo := (sameLegendre_iff_biconj_eq c.lo f).mp h.2 |>.symm

/-! ## Faithfulness checks (anonymous restatements vs the book) -/

-- Definition 4.2: `[f̲, f̄]_𝓛 = [f̲, f̄] ∩ [f̲]_𝓛 = {f | f̲ ≤ f ≤ f̄, 𝓛 f = 𝓛 f̲}`.
example (c : Container) (f : ℝ≥0 → EReal) :
    c.MemL f ↔ (c.lo ≤ f ∧ f ≤ c.hi) ∧ legendre f = legendre c.lo :=
  ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩

-- Proposition 4.2: `𝓛 f = 𝓛 g ⇔ Cvx f = Cvx g`, with `Cvx = biconj`.
example (f g : ℝ≥0 → EReal) : legendre f = legendre g ↔ biconj f = biconj g :=
  sameLegendre_iff_biconj_eq f g

-- Proposition 4.2 (moreover): `[Cvx f]_𝓛 = [f]_𝓛` and `∀ f' ∈ [f]_𝓛, Cvx f ≤ f'`.
example (f : ℝ≥0 → EReal) : legendre (biconj f) = legendre f := legendre_biconj f
example (f g : ℝ≥0 → EReal) (h : legendre f = legendre g) : biconj f ≤ g :=
  fun u => biconj_le_of_sameLegendre h u

-- Proposition 4.3 scaffolding: `≡_𝓛` is an equivalence relation.
example : Equivalence (SameLegendre) := equivalence_sameLegendre

end Container

end DeepWiki
