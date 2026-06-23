import DeepWiki.NetworkCalculus.Containers
import DeepWiki.NetworkCalculus.ContainerUncertainty
import DeepWiki.NetworkCalculus.FunctionDioids

/-! # Inclusion functions for containers (Definition 4.5, Theorem 4.4)

An operation `⋄` on curves lifts to an **inclusion function** on containers by
applying it to each bound: `[f̲, f̄] ⋄ [g̲, ḡ] = [f̲ ⋄ g̲, f̄ ⋄ ḡ]` (for a
`⋄` monotone in each argument). The defining inclusion property (Theorem 4.4,
§4.4.3, book p. 90–91) is **soundness**: the result container *contains* `f ⋄ g`
for every pair `f ∈ first`, `g ∈ second`.

This file formalizes the two inclusion functions whose lift is pure
monotonicity (Definition 4.5 [4.14]/[4.15]):

* **lifted meet** `Container.inf` — the inclusion function `[∧]` of minimum,
  with `f ⊓ g ∈ inf c d` (Theorem 4.4, minimum case);
* **lifted convolution** `Container.conv` — the inclusion function `[∗]` of
  convolution, with `minConv f g ∈ conv c d` (Theorem 4.4, convolution case).

The bounds live in `ℝ≥0 → EReal`; the meet is the pointwise lattice `⊓` and the
convolution is `minConv` (monotone in both arguments by `minConv_le_minConv`).
The book's canonical forms wrap these lifts in the convex- and concave-hull
canonicalizations `C_vx`/`C_cv` of [4.14]/[4.15], which only narrow the meet's
container (the convex hull lies below, the concave hull above its argument); the
un-canonicalized lift here carries the inclusion content of Theorem 4.4.

(The third inclusion function of Definition 4.5, the **unary** sub- and
super-additive closure `[*]` of [4.16]/[4.17], is a closure of one container and
not a binary lift; it is not formalized here.) -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

namespace Container

/-! ## Lifted meet — inclusion function `[∧]` (Definition 4.5 [4.14]) -/

/-- The **lifted meet** `c [∧] d`: apply the pointwise meet `⊓` to the bounds,
`[f̲ ⊓ g̲, f̄ ⊓ ḡ]`. The bound order survives because `⊓` is monotone
(`inf_le_inf`). This is the inclusion function `[∧]` of Definition 4.5 [4.14],
before the convex- and concave-hull canonicalization. -/
noncomputable def inf (c d : Container) : Container where
  lo := c.lo ⊓ d.lo
  hi := c.hi ⊓ d.hi
  le := inf_le_inf c.le d.le

/-- The lower bound of `c [∧] d` is `c.lo ⊓ d.lo`. -/
@[simp] theorem inf_lo (c d : Container) : (inf c d).lo = c.lo ⊓ d.lo := rfl

/-- The upper bound of `c [∧] d` is `c.hi ⊓ d.hi`. -/
@[simp] theorem inf_hi (c d : Container) : (inf c d).hi = c.hi ⊓ d.hi := rfl

/-- **Theorem 4.4 (minimum case):** the lifted meet is inclusion-sound — for
`f ∈ c` and `g ∈ d`, the meet `f ⊓ g` lies in `c [∧] d`. Both bounds follow
from monotonicity of `⊓` (`inf_le_inf`). -/
theorem inf_mem {c d : Container} {f g : ℝ≥0 → EReal}
    (hf : f ∈ c) (hg : g ∈ d) : (f ⊓ g) ∈ inf c d :=
  ⟨inf_le_inf hf.1 hg.1, inf_le_inf hf.2 hg.2⟩

/-! ## Lifted convolution — inclusion function `[∗]` (Definition 4.5 [4.15]) -/

/-- The **lifted convolution** `c [∗] d`: apply `minConv` to the bounds,
`[f̲ ∗ g̲, f̄ ∗ ḡ]`. The bound order survives because `minConv` is monotone in
both arguments (`minConv_le_minConv`). This is the inclusion function `[∗]` of
Definition 4.5 [4.15]. -/
noncomputable def conv (c d : Container) : Container where
  lo := minConv c.lo d.lo
  hi := minConv c.hi d.hi
  le := fun t => minConv_le_minConv (fun u => c.le u) (fun s => d.le s) t

/-- The lower bound of `c [∗] d` is `minConv c.lo d.lo`. -/
@[simp] theorem conv_lo (c d : Container) : (conv c d).lo = minConv c.lo d.lo := rfl

/-- The upper bound of `c [∗] d` is `minConv c.hi d.hi`. -/
@[simp] theorem conv_hi (c d : Container) : (conv c d).hi = minConv c.hi d.hi := rfl

/-- **Theorem 4.4 (convolution case):** the lifted convolution is
inclusion-sound — for `f ∈ c` and `g ∈ d`, the convolution `minConv f g` lies in
`c [∗] d`. Both bounds follow from monotonicity of `minConv`
(`minConv_le_minConv`). -/
theorem conv_mem {c d : Container} {f g : ℝ≥0 → EReal}
    (hf : f ∈ c) (hg : g ∈ d) : minConv f g ∈ conv c d :=
  ⟨fun t => minConv_le_minConv (fun u => hf.1 u) (fun s => hg.1 s) t,
   fun t => minConv_le_minConv (fun u => hf.2 u) (fun s => hg.2 s) t⟩

/-! ## Satellites: inclusion-monotonicity and singleton reduction -/

/-- Containers with equal bounds are equal (the `le` field is a proof). -/
theorem ext {c d : Container} (hlo : c.lo = d.lo) (hhi : c.hi = d.hi) : c = d := by
  cases c; cases d; cases hlo; cases hhi; rfl

/-- **The lifted meet is inclusion-monotone**: widening both arguments by their
bounds (`c'.lo ≤ c.lo`, `c.hi ≤ c'.hi`, and likewise for `d`) widens `c [∧] d`
into `c' [∧] d'`. -/
theorem inf_subset_inf {c c' d d' : Container}
    (hclo : c'.lo ≤ c.lo) (hchi : c.hi ≤ c'.hi)
    (hdlo : d'.lo ≤ d.lo) (hdhi : d.hi ≤ d'.hi) :
    Subset (inf c d) (inf c' d') :=
  subset_of_le (inf_le_inf hclo hdlo) (inf_le_inf hchi hdhi)

/-- **The lifted convolution is inclusion-monotone**: widening both arguments by
their bounds widens `c [∗] d` into `c' [∗] d'` (`minConv_le_minConv`). -/
theorem conv_subset_conv {c c' d d' : Container}
    (hclo : c'.lo ≤ c.lo) (hchi : c.hi ≤ c'.hi)
    (hdlo : d'.lo ≤ d.lo) (hdhi : d.hi ≤ d'.hi) :
    Subset (conv c d) (conv c' d') :=
  subset_of_le
    (fun t => minConv_le_minConv (fun u => hclo u) (fun s => hdlo s) t)
    (fun t => minConv_le_minConv (fun u => hchi u) (fun s => hdhi s) t)

/-- **On singletons the lifted meet reduces to the plain meet**:
`(singleton f) [∧] (singleton g) = singleton (f ⊓ g)` (zero uncertainty in,
zero uncertainty out). -/
theorem inf_singleton (f g : ℝ≥0 → EReal) :
    inf (singleton f) (singleton g) = singleton (f ⊓ g) :=
  ext rfl rfl

/-- **On singletons the lifted convolution reduces to the plain convolution**:
`(singleton f) [∗] (singleton g) = singleton (minConv f g)`. -/
theorem conv_singleton (f g : ℝ≥0 → EReal) :
    conv (singleton f) (singleton g) = singleton (minConv f g) :=
  ext rfl rfl

/-! ## Faithfulness checks (anonymous restatements vs the book) -/

-- Definition 4.5 [4.14] (un-canonicalized lift): `[∧]` applies `⊓` to the bounds.
example (c d : Container) :
    (inf c d).lo = c.lo ⊓ d.lo ∧ (inf c d).hi = c.hi ⊓ d.hi := ⟨rfl, rfl⟩

-- Definition 4.5 [4.15]: `[∗]` applies `∗` (`minConv`) to the bounds.
example (c d : Container) :
    (conv c d).lo = minConv c.lo d.lo ∧ (conv c d).hi = minConv c.hi d.hi :=
  ⟨rfl, rfl⟩

-- Theorem 4.4 (minimum): `f ∈ f, g ∈ g ⇒ f ∧ g ∈ f[∧]g`.
example {c d : Container} {f g : ℝ≥0 → EReal} (hf : f ∈ c) (hg : g ∈ d) :
    (f ⊓ g) ∈ inf c d := inf_mem hf hg

-- Theorem 4.4 (convolution): `f ∈ f, g ∈ g ⇒ f ∗ g ∈ f[∗]g`.
example {c d : Container} {f g : ℝ≥0 → EReal} (hf : f ∈ c) (hg : g ∈ d) :
    minConv f g ∈ conv c d := conv_mem hf hg

end Container

end DeepWiki
