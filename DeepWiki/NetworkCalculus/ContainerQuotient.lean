import DeepWiki.NetworkCalculus.Containers
import DeepWiki.NetworkCalculus.LegendreFenchelConv

/-! # The quotient dioid `ℱ↑/𝓛` (Proposition 4.3)
The Legendre–Fenchel congruence `SameLegendre` (`𝓛 f = 𝓛 g`, `legendreSetoid`)
is a **dioid congruence**: the function-dioid `⊓` (min) and the inf-convolution
`legendreConv` (`⊗`) descend to the quotient `ℱ↑/𝓛`, because `𝓛` is a dioid
homomorphism (`legendre_inf`: `𝓛(f ⊓ g) = 𝓛 f ⊔ 𝓛 g`; `legendre_legendreConv`:
`𝓛(f ⊗ g) = 𝓛 f + 𝓛 g` for proper curves). These congruence facts are the
well-definedness of operations [4.7]–[4.8] that make `ℱ↑/𝓛` a dioid. -/

namespace DeepWiki

namespace Container

open scoped Classical NNReal ENNReal

/-! ## Proposition 4.3 — the operations respect the congruence

The Legendre–Fenchel transform is a dioid homomorphism, so the function-dioid
operations descend to `ℱ↑/𝓛`. -/

/-- **[4.7] is well-defined: `⊓` respects `≡_𝓛`.** If `f ≡_𝓛 f'` and `g ≡_𝓛 g'`
then `f ⊓ g ≡_𝓛 f' ⊓ g'`, since `𝓛(f ⊓ g) = 𝓛 f ⊔ 𝓛 g = 𝓛 f' ⊔ 𝓛 g' = 𝓛(f' ⊓ g')`
(`legendre_inf`). -/
theorem SameLegendre.inf {f f' g g' : ℝ≥0 → EReal}
    (hf : SameLegendre f f') (hg : SameLegendre g g') :
    SameLegendre (f ⊓ g) (f' ⊓ g') := by
  unfold SameLegendre at hf hg ⊢
  rw [legendre_inf, legendre_inf, hf, hg]

/-- **[4.8] is well-defined: `⊗` respects `≡_𝓛`** (for proper curves). If
`f ≡_𝓛 f'`, `g ≡_𝓛 g'` and all four curves are proper (never `⊥`), then
`f ⊗ g ≡_𝓛 f' ⊗ g'`, since `𝓛(f ⊗ g) = 𝓛 f + 𝓛 g = 𝓛 f' + 𝓛 g' = 𝓛(f' ⊗ g')`
(`legendre_legendreConv`). -/
theorem SameLegendre.legendreConv {f f' g g' : ℝ≥0 → EReal}
    (hf₀ : ∀ u, f u ≠ ⊥) (hf'₀ : ∀ u, f' u ≠ ⊥)
    (hg₀ : ∀ v, g v ≠ ⊥) (hg'₀ : ∀ v, g' v ≠ ⊥)
    (hf : SameLegendre f f') (hg : SameLegendre g g') :
    SameLegendre (legendreConv f g) (legendreConv f' g') := by
  unfold SameLegendre at hf hg ⊢
  rw [legendre_legendreConv hf₀ hg₀, legendre_legendreConv hf'₀ hg'₀, hf, hg]

/-! ## The quotient dioid `ℱ↑/𝓛`

The quotient type and the descended `⊓`; `⊗` cannot descend unconditionally
(it needs properness, which is not preserved by the `Quotient`-erased
representative), so it lives at the representative level via the congruence
lemma above. -/

/-- The quotient `ℱ↑/𝓛`: curves modulo the Legendre–Fenchel congruence
(Proposition 4.3). -/
def FmodL : Type := Quotient legendreSetoid

/-- The class `[f]_𝓛 ∈ ℱ↑/𝓛` of a curve `f`. -/
def FmodL.mk (f : ℝ≥0 → EReal) : FmodL := Quotient.mk legendreSetoid f

/-- `[f]_𝓛 = [g]_𝓛 ↔ 𝓛 f = 𝓛 g`: two curves give the same quotient class iff
they share the Legendre–Fenchel transform. -/
theorem FmodL.mk_eq_mk {f g : ℝ≥0 → EReal} :
    FmodL.mk f = FmodL.mk g ↔ SameLegendre f g :=
  Quotient.eq

/-- **[4.7] on the quotient: the descended `⊓`.** `⊓` lifts to `ℱ↑/𝓛` via
`SameLegendre.inf`, giving the quotient meet. -/
noncomputable def FmodL.inf : FmodL → FmodL → FmodL :=
  Quotient.lift₂ (fun f g => FmodL.mk (f ⊓ g))
    (fun _ _ _ _ hf hg => Quotient.sound (SameLegendre.inf hf hg))

/-- `[f]_𝓛 ⊓ [g]_𝓛 = [f ⊓ g]_𝓛`: the descended meet computes on representatives
(equation [4.7]). -/
@[simp] theorem FmodL.inf_mk (f g : ℝ≥0 → EReal) :
    FmodL.inf (FmodL.mk f) (FmodL.mk g) = FmodL.mk (f ⊓ g) := rfl

/-! ## Faithfulness checks (anonymous restatements vs the book) -/

-- Proposition 4.3 [4.7]: `⊓` is well-defined on `ℱ↑/𝓛` (a dioid congruence).
example {f f' g g' : ℝ≥0 → EReal}
    (hf : legendre f = legendre f') (hg : legendre g = legendre g') :
    legendre (f ⊓ g) = legendre (f' ⊓ g') := SameLegendre.inf hf hg

-- Proposition 4.3 [4.8]: `⊗` is well-defined on `ℱ↑/𝓛` for proper curves.
example {f f' g g' : ℝ≥0 → EReal}
    (hf₀ : ∀ u, f u ≠ ⊥) (hf'₀ : ∀ u, f' u ≠ ⊥)
    (hg₀ : ∀ v, g v ≠ ⊥) (hg'₀ : ∀ v, g' v ≠ ⊥)
    (hf : legendre f = legendre f') (hg : legendre g = legendre g') :
    legendre (legendreConv f g) = legendre (legendreConv f' g') :=
  SameLegendre.legendreConv hf₀ hf'₀ hg₀ hg'₀ hf hg

-- The quotient meet computes on classes: `[f] ⊓ [g] = [f ⊓ g]`.
example (f g : ℝ≥0 → EReal) :
    FmodL.inf (FmodL.mk f) (FmodL.mk g) = FmodL.mk (f ⊓ g) := rfl

end Container

end DeepWiki
