import Leanproofs.MinPlus.RbarInstance
import Mathlib.Data.NNReal.Basic

/-!
# The (min,plus) convolution (Definitions 2.6–2.7, Lemmas 2.1–2.2)

The **(min,plus) convolution** is defined over an arbitrary additive index monoid `T` valued in an
arbitrary complete dioid `α`:

  `(f ∗ g)(t) = ⨆_{u + s = t} (f u ⊗ g s)`   (Definition 2.7, [2.3], abstract form).

This is the *generic* statement: `⊗ = *` is the dioid product and `⨆` is the dioid sum `⊕` (the
join in the canonical order). All of **Lemma 2.1** — commutativity, associativity, distributivity
over the dioid sum, and addition by a constant — holds at this generality.

We then **specialize** to the book's setting `F = ℝ⁺ → R̄min` (Definition 2.6): the non-negative
reals `ℝ⁺ = ℝ≥0` into the complete (min,plus) dioid `R̄min` (`Leanproofs.MinPlus.RbarInstance`). The
specialized statements are `conv_eq_sub` (the book's `0 ≤ s ≤ t` form [2.2], via truncated
subtraction on `ℝ≥0`) and **Lemma 2.2** (stated in the *natural* numeric order, via `.toDual`).

## Orientation

In the algebraic interface of a complete dioid, the dioid sum `⊕` is `⊔`/`⨆` (the canonical-order
join — for `R̄min`, the numeric `min`) and the dioid product `⊗` is `*` (for `R̄min`, numeric `+`).
So the book's `inf_{u+s=t} (f u + g s)` is `⨆_{u+s=t} f u * g s`: a least upper bound (`⨆`) of
products (`*`) over the decompositions of `t`.
-/

namespace NetworkCalculus

open scoped Computability NNReal

/-! ## Generic convolution over a complete dioid -/

section Generic

variable {T : Type*} [AddCommMonoid T] {α : Type*} [CompleteDioid α]

/-- **Definition 2.7 — the (min,plus) convolution** ([2.3]), abstract form:
`(f ∗ g)(t) = ⨆_{u + s = t} f u ⊗ g s`. -/
noncomputable def conv (f g : T → α) : T → α :=
  fun t => ⨆ p : {p : T × T // p.1 + p.2 = t}, f p.val.1 * g p.val.2

@[inherit_doc] scoped infixl:70 " ∗ " => conv

theorem conv_apply (f g : T → α) (t : T) :
    (f ∗ g) t = ⨆ p : {p : T × T // p.1 + p.2 = t}, f p.val.1 * g p.val.2 := rfl

/-- Every decomposition `u + s = t` gives a lower bound on the convolution: `f u ⊗ g s ≼ (f ∗ g) t`
(each summand is below the dioid sum `⊕ = ⨆`). -/
theorem conv_ge (f g : T → α) {t u s : T} (h : u + s = t) :
    f u * g s ≤ (f ∗ g) t :=
  le_iSup (fun p : {p : T × T // p.1 + p.2 = t} => f p.val.1 * g p.val.2) ⟨(u, s), h⟩

/-- The convolution is the *least* upper bound of the decomposition values: if every decomposition
`u + s = t` satisfies `f u ⊗ g s ≼ b`, then `(f ∗ g) t ≼ b`. -/
theorem conv_le (f g : T → α) {t : T} {b : α}
    (h : ∀ u s, u + s = t → f u * g s ≤ b) : (f ∗ g) t ≤ b :=
  iSup_le fun p => h p.val.1 p.val.2 p.property

/-! ### Lemma 2.1 — properties of the convolution

Commutativity, associativity, distributivity over the dioid sum `⊕`, and addition by a constant —
all in the dioid order `≼`, over an arbitrary complete dioid. -/

/-- **Lemma 2.1(1): commutativity.** `f ∗ g = g ∗ f` (reindex decompositions `(u,s) ↦ (s,u)` and use
commutativity of `⊗`). -/
theorem conv_comm (f g : T → α) : f ∗ g = g ∗ f := by
  funext t
  apply le_antisymm
  · exact conv_le f g fun u s h => by rw [mul_comm]; exact conv_ge g f (by rw [add_comm]; exact h)
  · exact conv_le g f fun u s h => by rw [mul_comm]; exact conv_ge f g (by rw [add_comm]; exact h)

/-- **Lemma 2.1(3): distributivity over the dioid sum.** `f ∗ (g ⊕ h) = (f ∗ g) ⊕ (f ∗ h)`, where
`⊕ = ⊔` (for `R̄min`, the pointwise minimum `∧`). From binary distributivity of `⊗` over `⊔`
(`CompleteDioid.mul_sup`). -/
theorem conv_sup (f g h : T → α) :
    (f ∗ fun x => g x ⊔ h x) = fun t => (f ∗ g) t ⊔ (f ∗ h) t := by
  funext t
  rw [conv_apply, conv_apply, conv_apply, ← iSup_sup_eq]
  congr 1; funext p
  exact CompleteDioid.mul_sup _ _ _

/-- **Lemma 2.1(4): addition by a constant.** `(f ∗ g) ⊗ K = f ∗ (g ⊗ K)` (the book's `+ K` is
multiplication by the constant `K ∈ α`). -/
theorem conv_mul_const (f g : T → α) (K : α) :
    (fun t => (f ∗ g) t * K) = f ∗ (fun s => g s * K) := by
  funext t
  rw [conv_apply, conv_apply, CompleteDioid.iSup_mul]
  congr 1; funext p
  rw [mul_assoc]

/-! #### Associativity (Lemma 2.1(2))

Both `(f ∗ g) ∗ h` and `f ∗ (g ∗ h)` equal the "ternary convolution"
`⨆_{u+v+w=t} f u ⊗ g v ⊗ h w`; we bound each by the other via the symmetric ternary lower bounds. -/

/-- Any decomposition `u + v + w = t` lower-bounds the left-associated triple `(f ∗ g) ∗ h`. -/
theorem conv_conv_ge (f g h : T → α) {t u v w : T} (e : u + v + w = t) :
    f u * g v * h w ≤ ((f ∗ g) ∗ h) t :=
  le_trans (Dioid.mul_le_mul_right' (conv_ge f g (u := u) (s := v) rfl) _)
    (conv_ge (f ∗ g) h (u := u + v) (s := w) e)

/-- The mirror bound for the right-associated triple `f ∗ (g ∗ h)`. -/
theorem le_conv_conv (f g h : T → α) {t u v w : T} (e : u + (v + w) = t) :
    f u * (g v * h w) ≤ (f ∗ (g ∗ h)) t :=
  le_trans (Dioid.mul_le_mul_left' (conv_ge g h (u := v) (s := w) rfl) _)
    (conv_ge f (g ∗ h) (u := u) (s := v + w) e)

/-- **Lemma 2.1(2): associativity.** `(f ∗ g) ∗ h = f ∗ (g ∗ h)`. -/
theorem conv_assoc (f g h : T → α) : (f ∗ g) ∗ h = f ∗ (g ∗ h) := by
  funext t
  apply le_antisymm
  · apply conv_le
    intro a w haw
    rw [conv_apply (f := f) (g := g), CompleteDioid.iSup_mul]
    refine iSup_le fun p => ?_
    obtain ⟨⟨u, v⟩, huv⟩ := p
    rw [mul_assoc]
    refine le_conv_conv f g h (u := u) (v := v) (w := w) ?_
    rw [← add_assoc, huv, haw]
  · apply conv_le
    intro u b hub
    rw [conv_apply (f := g) (g := h), CompleteDioid.mul_iSup]
    refine iSup_le fun p => ?_
    obtain ⟨⟨v, w⟩, hvw⟩ := p
    rw [← mul_assoc]
    refine conv_conv_ge f g h (u := u) (v := v) (w := w) ?_
    rw [add_assoc, hvw, hub]

end Generic

/-! ## Specialization to `F = ℝ⁺ → R̄min` (Definition 2.6) -/

/-- **Definition 2.6 — the (min,plus) functions.** `F` is the set of functions from the
non-negative reals `ℝ⁺ = ℝ≥0` into the complete (min,plus) dioid `R̄min`. -/
abbrev F := ℝ≥0 → RbarMin

/-- **Book form [2.2].** Re-indexing the convolution by `0 ≤ s ≤ t` via truncated subtraction:
`(f ∗ g)(t) = ⨆_{0 ≤ s ≤ t} (f (t − s) ⊗ g s)`. -/
theorem conv_eq_sub (f g : F) (t : ℝ≥0) :
    (f ∗ g) t = ⨆ s : {s : ℝ≥0 // s ≤ t}, f (t - s.val) * g s.val := by
  apply le_antisymm
  · refine iSup_le fun p => ?_
    obtain ⟨⟨u, s⟩, hus⟩ := p
    refine le_iSup_of_le ⟨s, hus ▸ le_add_self⟩ ?_
    have hu : t - s = u := by rw [← hus, add_tsub_cancel_right]
    rw [hu]
  · refine iSup_le fun p => ?_
    obtain ⟨s, hs⟩ := p
    exact le_iSup_of_le ⟨(t - s, s), tsub_add_cancel_of_le hs⟩ le_rfl

/-! ### Lemma 2.2

The book states Lemma 2.2 in the **natural (numeric) order** (§2.1: "unless otherwise stated, the
term 'order' refers to the natural order"), which on `R̄min` is the *reverse* of the dioid order
`≼`. We express it directly on the underlying numeric values via `.toDual`. -/

/-- **Lemma 2.2 (first part).** If `f(0) ≤ 0` (numerically), then `f ∗ g ≤ g` (numerically,
pointwise). Proof: the decomposition `t = 0 + t` gives `(f ∗ g)(t) ≤ f(0) + g(t) ≤ g(t)`. -/
theorem conv_le_right_of_apply_zero_le {f g : F} (hf : (f 0).toDual ≤ 0) (t : ℝ≥0) :
    ((f ∗ g) t).toDual ≤ (g t).toDual :=
  calc ((f ∗ g) t).toDual ≤ (f 0 * g t).toDual := conv_ge f g (zero_add t)
    _ = (f 0).toDual + (g t).toDual := rfl
    _ ≤ 0 + (g t).toDual := by gcongr
    _ = (g t).toDual := zero_add _

/-- **Lemma 2.2 (second part).** If `f(0) = 0` and `g(0) = 0` (numerically), then
`f ∗ g ≤ f ∧ g` (numerically, pointwise): `(f ∗ g)(t) ≤ min (f(t), g(t))`. Proof: the
decomposition `t = t + 0` bounds it by `f(t)`, and `t = 0 + t` bounds it by `g(t)`. -/
theorem conv_le_inf_of_apply_zero {f g : F} (hf : (f 0).toDual = 0) (hg : (g 0).toDual = 0)
    (t : ℝ≥0) : ((f ∗ g) t).toDual ≤ min ((f t).toDual) ((g t).toDual) := by
  refine le_min ?_ ?_
  · calc ((f ∗ g) t).toDual ≤ (f t * g 0).toDual := conv_ge f g (add_zero t)
      _ = (f t).toDual + (g 0).toDual := rfl
      _ = (f t).toDual := by rw [hg, add_zero]
  · calc ((f ∗ g) t).toDual ≤ (f 0 * g t).toDual := conv_ge f g (zero_add t)
      _ = (f 0).toDual + (g t).toDual := rfl
      _ = (g t).toDual := by rw [hf, zero_add]

end NetworkCalculus
