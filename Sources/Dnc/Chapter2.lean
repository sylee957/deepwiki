import Book.ScalarDioids
import Book.FunctionDioids
import Book.DioidFunctions
import Book.Closures
import Book.Additivity
import Book.Deconvolution
import Sources.Dnc.Source

/-! # DNC catalog — Chapter 2: The (min,plus) Functions Semi-ring
Each numbered item of the book's Chapter 2 is one declaration named by its
book number: a `theorem` (the book-faithful statement, discharged by the
`DeepWiki` library) for theorems/propositions/lemmas, and an `abbrev`
aliasing the library declaration for definitions. The book numbering lives
here in the catalog, never in the library; the citation (section, page) is
in each docstring, the source's DOI in `Sources.Dnc.Source`.

(Library import paths are `Book.…` until the topic rename to
`DeepWiki.NetworkCalculus.…`.) -/

namespace DeepWiki.Dnc

open DeepWiki DeepWiki.Algebra
open scoped DeepWiki.Algebra.Bridge NNReal ENNReal

/-! ## §2.1.1 Dioids -/

/-- **Definition 2.1** (§2.1.1, p.16). A monoid `(M, ⊕)`: associative with
a neutral element. Reuses Mathlib's `Monoid`. -/
abbrev def_2_1 := @Monoid

/-- **Definition 2.2** (§2.1.1, p.16). Commutative and idempotent monoids.
Reuses Mathlib's `CommMonoid`; idempotency is the `oplus_idem` axiom of
`DeepWiki.Algebra.Dioid`. -/
abbrev def_2_2 := @CommMonoid

/-- **Definition 2.3** (§2.1.1, p.16). A semi-ring `(D, ⊕, ⊗)`. Reuses
Mathlib's `CommSemiring`, the base of `DeepWiki.Algebra.Dioid`. -/
abbrev def_2_3 := @_root_.CommSemiring

/-- **Definition 2.4** (§2.1.1, p.17). An idempotent semi-ring (dioid).
The library's `DeepWiki.Algebra.Dioid` (`CommSemiring` + `oplus_idem`). -/
abbrev def_2_4 := @Dioid

/-- **Theorem 2.1**, order definition (§2.1.1, p.17). The canonical dioid
order `≼ₒ` is, by definition, `a ⊕ₒ b = b`. -/
theorem thm_2_1_order_iff {T : Type*} [Dioid T] (a b : T) :
    (a ≼ₒ b) ↔ (a ⊕ₒ b = b) := Iff.rfl

/-- **Theorem 2.1**, isotony of `⊕ₒ` (§2.1.1, p.17). Discharged by
`Algebra.add_le_add_right`. -/
theorem thm_2_1_add_isotone {T : Type*} [Dioid T] {a b : T}
    (h : a ≼ₒ b) (c : T) : (a ⊕ₒ c) ≼ₒ (b ⊕ₒ c) :=
  add_le_add_right h c

/-- **Theorem 2.1**, isotony of `⊗ₒ` (§2.1.1, p.17). Discharged by
`Algebra.mul_le_mul_right`. -/
theorem thm_2_1_mul_isotone {T : Type*} [Dioid T] {a b : T}
    (h : a ≼ₒ b) (c : T) : (a ⊗ₒ c) ≼ₒ (b ⊗ₒ c) :=
  mul_le_mul_right h c

/-- **Definition 2.5** (§2.1.1, p.18). A complete dioid: closed for
infinite sums, the product distributing over them. The library's
`DeepWiki.Algebra.CompleteDioid`. -/
abbrev def_2_5 := @CompleteDioid

/-! ## §2.1.2 The (min,plus) dioid -/

/-- **Theorem 2.2** (§2.1.2, p.18). The (min,plus) dioid `(ℝ ∪ {+∞}, ∧, +)`
is a commutative dioid (zero `+∞`, unit `0`): the carrier `MinPlus` has an
`Algebra.Dioid` instance. -/
theorem thm_2_2 : Nonempty (Dioid MinPlus) := ⟨inferInstance⟩

/-- **Proposition 2.1** (§2.1.2, p.19). The complete (min,plus) dioid
`(ℝ ∪ {±∞}, ∧, +)` (top `−∞`, with `(+∞)+(−∞)=+∞`): the carrier
`MinPlusExt` has an `Algebra.CompleteDioid` instance. -/
theorem prop_2_1 : Nonempty (CompleteDioid MinPlusExt) := ⟨inferInstance⟩

/-- **Proposition 2.2** (§2.1.2, p.19). `(ℝ≥0 ∪ {+∞}, ∧, +)` is a complete
commutative dioid: the carrier `MinPlusNN` has an `Algebra.CompleteDioid`
instance. -/
theorem prop_2_2 : Nonempty (CompleteDioid MinPlusNN) := ⟨inferInstance⟩

/-! ## §2.1.3 The dioid of (min,plus) functions -/

/-- **Definition 2.6** (§2.1.3, p.19). The (min,plus) functions
`ℱ = {f : ℝ≥0 → ℝ̄min}`. The library's function space
`FminBar := ℝ≥0 → MinPlusExt`. -/
abbrev def_2_6 := FminBar

/-- **Definition 2.7** (§2.1.3, p.19). The (min,plus) convolution
`(f ∗ g)(t) = inf_{0 ≤ s ≤ t} (f(t−s) + g(s))`. The library's concrete
`minConv` (and the generic dioid convolution `conv`). -/
noncomputable def def_2_7 := @minConv

/-- **Lemma 2.1**, commutativity (§2.1.3, p.20). The convolution is
commutative; discharged by `minConv_comm`. (Lemma 2.1 also states
associativity, distributivity over `∧`, and `(f ∗ g) + K = f ∗ (g + K)`:
`minConv_assoc_enn` / `conv_assoc`, `minConv_min` / `conv_distrib`,
`conv_add_const`.) -/
theorem lemma_2_1_comm (f g : ℝ≥0 → ℝ≥0∞) : minConv f g = minConv g f :=
  minConv_comm f g

/-! ## §2.2.1 Kleene star operator -/

/-- **Definition 2.9** (§2.2.1, p.23). The Kleene star `a⋆ = ⊕_{i≥0} aⁱ` in
a complete dioid. The library's `subadditiveClosure` (`⨆ n, σⁿ`, with the
dioid power `convPow`). -/
noncomputable def def_2_9 := @subadditiveClosure

/-- **Lemma 2.4**, star is monotone (§2.2.1, p.24): `a ≼ b ⟹ a⋆ ≼ b⋆`. -/
alias lemma_2_4_mono := subadditiveClosure_mono

/-- **Lemma 2.4**, star is idempotent (§2.2.1, p.24). -/
alias lemma_2_4_idem := closure_idem

/-- **Lemma 2.4**, power below star (§2.2.1, p.24): `aⁱ ≼ a⋆`. -/
alias lemma_2_4_pow_le := convPow_le_closure

/-! **Theorem 2.3** (Kleene star theorem, §2.2.1, p.24): `a⋆b` is the least
solution of `x = ax ⊕ b`. The library provides the least-solution (`≤`)
direction in feedback-control form (`minConv_subadditiveClosureENN_le_of_inf_le`);
the clean abstract fixpoint statement is not separately formalized. -/

/-! ## §2.2.2 Sub-additive closure -/

/-- **Definition 2.10** (§2.2.2, p.25). A sub-additive function:
`f(s+t) ≤ f(s) + f(t)`. The library's `IsSubadditive`. -/
abbrev def_2_10 := @IsSubadditive

/-- **Proposition 2.4**, convolution (§2.2.2, p.25): the convolution of two
sub-additive functions is sub-additive. (The sum `f + g` is likewise
sub-additive, directly from the definition.) -/
alias prop_2_4_conv := IsSubadditive.minConv

/-- **Definition 2.11** (§2.2.2, p.26). The sub-additive closure
`f* = ⋀_{i≥0} fⁱ`. The library's `subadditiveClosureENN` (over `ℝ≥0∞`;
`subadditiveClosureEReal` over `EReal`). -/
noncomputable def def_2_11 := @subadditiveClosureENN

/-! **Lemma 2.5** (§2.2.2, p.27): a sub-additive `f` with `f(0) < 0` has
`f(0) = −∞` and `f(t) ∈ {−∞, +∞}`. Not separately formalized. -/

/-- **Proposition 2.5**, sub-additivity (§2.2.2, p.27): `f*` is
sub-additive. -/
alias prop_2_5_subadditive := subadditiveClosureENN_subadditive

/-- **Proposition 2.5**, minorant (§2.2.2, p.27): `f* ≼ f`. -/
alias prop_2_5_le := subadditiveClosureENN_le

/-- **Proposition 2.5**, value at the origin (§2.2.2, p.27): `f*(0) = 0`. -/
alias prop_2_5_zero := subadditiveClosureENN_zero_eq

/-! **Lemma 2.6** (§2.2.2, p.27): a sub-additive `f` with `f(0) ≤ 0` equals
its closure, `f = f*`. Not separately formalized (the library gives the
greatest-minorant Theorem 2.4 below). -/

/-- **Theorem 2.4** (§2.2.2, p.27): `f*` is the largest sub-additive
function `≼ f` with `f*(0) ≤ 0`. -/
alias thm_2_4 := le_subadditiveClosureENN_of_isSubadditive

/-- **Proposition 2.6** (§2.2.2, p.28): `(f ∧ g)* = f* ∗ g*`. -/
alias prop_2_6 := subadditiveClosureENN_min

/-! **Corollary 2.1** (efficient sub-additive closure, §2.2.2, p.28):
`f* = (e ∧ f)*`. Not separately formalized. -/

/-! ## §2.3 Deconvolution -/

/-- **§2.3.1 Residuation** (p.29-30): convolution and deconvolution form a
Galois connection, `x ⊗ a ≼ b ⟺ x ≼ b ⊘ a`. The library's
`galoisConnection_minDeconv_minConv` (with `minDeconv_le_iff_le_minConv`). -/
alias residuation := galoisConnection_minDeconv_minConv

/-- **Definition 2.12** (§2.3.2, p.30). The (min,plus) deconvolution
`f ⊘ g (t) = sup_{u≥0} (f(t+u) − g(u))`. The library's `minDeconv`. -/
noncomputable def def_2_12 := @minDeconv

/-! **Propositions 2.7–2.9** (further deconvolution properties, §2.3.2,
pp.31-32): the nine residuation identities of Proposition 2.7 — property 1
(`h ∗ g ≽ f ⟺ h ≽ f ⊘ g`) is the Galois connection `residuation` above;
the others are monotonicity, `f ⊘ (g ∗ h) = (f ⊘ g) ⊘ h`, and
`(f ∗ g) ⊘ h ≼ f ∗ (g ⊘ h)` — together with the decomposition Proposition
2.8 and the `⋆` and `⁺` decomposition Proposition 2.9. Mapped to
`Book.Deconvolution` (`minDeconv_le_iff_le_minConv`, `minDeconv_minConv`,
`monotone_minDeconv`, `minDeconv_minConv_le`) and `Book.Closures`; not
catalogued here as single declarations. -/

/-! ## §2.4 Link with the (max,plus) dioid
The order-dual (max,plus) dioid `(ℝ ∪ {−∞}, ∨, +)` (zero `−∞`, unit `0`)
and its operators — the (max,plus) convolution `f ⊼ g`, the deconvolution
`f ⊘̄ g (t) = inf_{u≥0} (f(t+u) − g(u))`, and the super-additive closure
`fᶠ` — are obtained from the (min,plus) ones by negation (equation [2.13]),
and the canonical-order properties [2.14]-[2.17] are the order-inverted
duals. The library's dual carriers are `MaxPlusNN` / `MaxPlusExt`, with
`maxConv` (`Book.FunctionDioids`) the (max,plus) convolution and `maxDeconv`
the deconvolution. **Proposition 2.10** (p.34),
`(f ∗ g) ⊘ (f' ∗ g') ≼ (f ⊘ f') ∗ (g ⊘ g')`, is the composition bound for
deconvolution. -/

end DeepWiki.Dnc
