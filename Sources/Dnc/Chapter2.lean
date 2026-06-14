import Book.ScalarDioids
import Book.FunctionDioids
import Book.DioidFunctions
import Sources.Dnc.Source

/-! # DNC catalog — Chapter 2: The (min,plus) Functions Semi-ring
The book's Chapter 2 builds the algebraic substrate of network calculus:
dioids, the (min,plus) dioid and its completions, the dioid of (min,plus)
functions, and the convolution. Each item is a `SourceRef` carrying the
book's own numbering, linked to the `DeepWiki` library declaration that
formalizes it — with a machine-checked anchor where the item is a theorem
or an instance, and a reference to the library declaration otherwise.

(Library import paths are `Book.…` until the topic rename to
`DeepWiki.NetworkCalculus.…`.) -/

namespace DeepWiki.Dnc

open DeepWiki DeepWiki.Algebra DeepWiki.Catalog
open scoped DeepWiki.Algebra.Bridge NNReal ENNReal

/-! ## §2.1.1 Dioids -/

/-- A monoid `(M, ⊕)`: associative with a neutral element. Foundational;
formalized by Mathlib's `Monoid` / `AddMonoid`. -/
def def_2_1 : SourceRef :=
  { doi := doi, location := "§2.1.1", label := "Definition 2.1", kind := .defn, page := some 16 }

/-- Commutative and idempotent monoids. Formalized by Mathlib's
`CommMonoid` and the idempotency axiom carried by `DeepWiki.Algebra.Dioid`. -/
def def_2_2 : SourceRef :=
  { doi := doi, location := "§2.1.1", label := "Definition 2.2", kind := .defn, page := some 16 }

/-- A semi-ring `(D, ⊕, ⊗)`: a commutative monoid for `⊕` and a monoid for
`⊗` with `⊗` distributing over `⊕` and the zero absorbing. Formalized by
Mathlib's `CommSemiring`, the base of `DeepWiki.Algebra.Dioid`. -/
def def_2_3 : SourceRef :=
  { doi := doi, location := "§2.1.1", label := "Definition 2.3", kind := .defn, page := some 16 }

/-- An idempotent semi-ring (dioid): a semi-ring whose `⊕` is idempotent.
Formalized by `DeepWiki.Algebra.Dioid` (`CommSemiring` + `oplus_idem`),
bridged to Mathlib's `IdemCommSemiring`. -/
def def_2_4 : SourceRef :=
  { doi := doi, location := "§2.1.1", label := "Definition 2.4", kind := .defn, page := some 17 }

/-- The product `⊗` may be omitted and has priority over `⊕`. A notational
remark; `DeepWiki.Algebra` writes `⊗ₒ`/`⊕ₒ` with the usual precedence. -/
def remark_2_1 : SourceRef :=
  { doi := doi, location := "§2.1.1", label := "Remark 2.1", kind := .remark, page := some 17 }

/-- Order relation of a dioid: `a ≼ b ⟺ a ⊕ b = b` is a (partial) order,
and `⊕`, `⊗` are isotone for it. Formalized by the canonical order `≼ₒ`
(`DeepWiki.Algebra.Bridge`) with isotony `Algebra.add_le_add_right`/`_left`
and `Algebra.mul_le_mul_right`/`_left`. -/
def thm_2_1 : SourceRef :=
  { doi := doi, location := "§2.1.1", label := "Theorem 2.1", kind := .thm, page := some 17 }

/-- `≼ₒ` is, by definition, `a ⊕ₒ b = b` — the book's order relation. -/
theorem thm_2_1_order_iff {T : Type*} [Dioid T] (a b : T) :
    (a ≼ₒ b) ↔ (a ⊕ₒ b = b) := Iff.rfl

/-- Isotony of `⊕ₒ` (Theorem 2.1), discharged by `Algebra.add_le_add_right`. -/
theorem thm_2_1_add_isotone {T : Type*} [Dioid T] {a b : T}
    (h : a ≼ₒ b) (c : T) : (a ⊕ₒ c) ≼ₒ (b ⊕ₒ c) :=
  add_le_add_right h c

/-- Isotony of `⊗ₒ` (Theorem 2.1), discharged by `Algebra.mul_le_mul_right`. -/
theorem thm_2_1_mul_isotone {T : Type*} [Dioid T] {a b : T}
    (h : a ≼ₒ b) (c : T) : (a ⊗ₒ c) ≼ₒ (b ⊗ₒ c) :=
  mul_le_mul_right h c

/-- Two definitions of "dioid" appear in the literature (idempotent
semi-ring vs. a semi-ring where the canonical order is an order); for
(min,plus) they coincide. A meta-remark; `DeepWiki.Algebra.Dioid` takes
the idempotent-semi-ring definition. -/
def remark_2_2 : SourceRef :=
  { doi := doi, location := "§2.1.1", label := "Remark 2.2", kind := .remark, page := some 17 }

/-- A complete dioid: closed for infinite sums, with the product
distributing over infinite sums on both sides (hence a top element).
Formalized by `DeepWiki.Algebra.CompleteDioid` (with the lower-semicontinuity
field `mul_iSup`). -/
def def_2_5 : SourceRef :=
  { doi := doi, location := "§2.1.1", label := "Definition 2.5", kind := .defn, page := some 18 }

/-! ## §2.1.2 The (min,plus) dioid -/

/-- The (min,plus) dioid `(ℝ ∪ {+∞}, ∧, +)` is a commutative dioid with
zero `+∞` and unit `0`. Formalized by the carrier `MinPlus` (over
`WithTop ℝ`) and its `Algebra.Dioid` instance. -/
def thm_2_2 : SourceRef :=
  { doi := doi, location := "§2.1.2", label := "Theorem 2.2", kind := .thm, page := some 18 }

/-- `MinPlus` is a dioid (Theorem 2.2). -/
example : Dioid MinPlus := inferInstance

/-- The complete (min,plus) dioid `(ℝ ∪ {±∞}, ∧, +)` is a complete
commutative dioid with top `−∞`, with the absorbing convention
`(+∞) + (−∞) = +∞`. Formalized by the carrier `MinPlusExt` (over
`WithTop (WithBot ℝ)`) and its `Algebra.CompleteDioid` instance. -/
def prop_2_1 : SourceRef :=
  { doi := doi, location := "§2.1.2", label := "Proposition 2.1", kind := .prop, page := some 19 }

/-- `MinPlusExt` is a complete dioid (Proposition 2.1). -/
example : Nonempty (CompleteDioid MinPlusExt) := ⟨inferInstance⟩

/-- `(ℝ≥0 ∪ {+∞}, ∧, +)` is a complete commutative dioid. Formalized by the
carrier `MinPlusNN` (over `ℝ≥0∞`) and its `Algebra.CompleteDioid` instance. -/
def prop_2_2 : SourceRef :=
  { doi := doi, location := "§2.1.2", label := "Proposition 2.2", kind := .prop, page := some 19 }

/-- `MinPlusNN` is a complete dioid (Proposition 2.2). -/
example : Nonempty (CompleteDioid MinPlusNN) := ⟨inferInstance⟩

/-! ## §2.1.3 The dioid of (min,plus) functions -/

/-- The (min,plus) functions `ℱ = {f : ℝ≥0 → ℝ̄min}`. Formalized by the
function space `FminBar := ℝ≥0 → MinPlusExt` (and its non-negative /
non-decreasing sub-dioids `FPlus`, `FNondecr`). -/
def def_2_6 : SourceRef :=
  { doi := doi, location := "§2.1.3", label := "Definition 2.6", kind := .defn, page := some 19 }

/-- The (min,plus) convolution `(f ∗ g)(t) = inf_{0 ≤ s ≤ t} (f(t−s) + g(s))`.
Formalized concretely by `minConv` (`Book.FunctionDioids`) and as the
generic dioid convolution `conv` on the function dioid
(`Book.DioidFunctions`). -/
def def_2_7 : SourceRef :=
  { doi := doi, location := "§2.1.3", label := "Definition 2.7", kind := .defn, page := some 19 }

/-- Properties of the convolution: it is commutative, associative,
distributes over the minimum, and `(f ∗ g) + K = f ∗ (g + K)`. Formalized
by `conv_comm`, `conv_assoc`, `conv_distrib`, `conv_add_const`
(`Book.DioidFunctions`); the concrete `minConv` carries `minConv_comm`,
`minConv_assoc_enn`, `minConv_min`. -/
def lemma_2_1 : SourceRef :=
  { doi := doi, location := "§2.1.3", label := "Lemma 2.1", kind := .lem, page := some 20 }

/-- Convolution is commutative (part of Lemma 2.1), discharged by
`minConv_comm`. -/
theorem lemma_2_1_comm (f g : ℝ≥0 → ℝ≥0∞) : minConv f g = minConv g f :=
  minConv_comm f g

/-! ## Section index -/

/-- The §2.1 portion of the DNC Chapter 2 catalog. -/
def chapter2Section1 : List SourceRef :=
  [def_2_1, def_2_2, def_2_3, def_2_4, remark_2_1, thm_2_1, remark_2_2,
   def_2_5, thm_2_2, prop_2_1, prop_2_2, def_2_6, def_2_7, lemma_2_1]

end DeepWiki.Dnc
