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

end Container

end DeepWiki
