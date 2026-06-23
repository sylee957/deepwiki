import DeepWiki.NetworkCalculus.ContainerQuotient
import DeepWiki.NetworkCalculus.Containers

/-! # Descending `⊗` to the quotient dioid `ℱ↑/𝓛` (Proposition 4.3, completed)
The full quotient `FmodL` carries the descended meet `⊓` [4.7] but not the
inf-convolution `⊗` [4.8]: `SameLegendre.legendreConv` needs all four curves
**proper** (never `⊥`), and properness cannot be recovered from an arbitrary
`Quotient`-erased representative. The fix is the **proper-curve subtype**
`ProperCurve` (curves with `∀ u, f u ≠ ⊥`), its induced congruence
`properSetoid`, and the quotient `FmodLProper`. On `FmodLProper` both
`⊓` [4.7] and `⊗` [4.8] descend, giving the Proposition 4.3 operations together.

Residue: `legendreConv` of two proper curves need **not** be proper — an `EReal`
`iInf` over the infinite slice `{u + v = t}` can fall to `⊥` even when every
term `f u + g v` is `> ⊥` (e.g. `f u = -(t-u)⁻¹`, `g ≡ 0` gives
`(f ⊗ g) t = -∞`). So `⊗` lands in the **full** quotient `FmodL`, not back in
`FmodLProper`; the meet `⊓`, being a pointwise `min` of non-`⊥` values, does
land back in `FmodLProper`. -/

namespace DeepWiki

namespace Container

open scoped Classical NNReal ENNReal

/-! ## The proper-curve subtype and its quotient -/

/-- A **proper curve**: a curve `f : ℝ≥0 → EReal` that never takes the value `⊥`.
The carrier on which the inf-convolution `⊗` [4.8] is well-defined. -/
def ProperCurve : Type := {f : ℝ≥0 → EReal // ∀ u, f u ≠ ⊥}

/-- The underlying curve `f.1` of a proper curve, as a coercion. -/
instance : CoeFun ProperCurve (fun _ => ℝ≥0 → EReal) := ⟨Subtype.val⟩

/-- A proper curve never takes the value `⊥`: `f u ≠ ⊥` for all `u`. -/
theorem ProperCurve.ne_bot (f : ProperCurve) (u : ℝ≥0) : f.1 u ≠ ⊥ := f.2 u

/-- The Legendre–Fenchel congruence restricted to proper curves: `f ≡_𝓛 g`
iff `legendre f = legendre g`. -/
def properSetoid : Setoid ProperCurve where
  r f g := SameLegendre f.1 g.1
  iseqv := ⟨fun f => SameLegendre.refl f.1, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- The quotient `ℱ↑/𝓛` of **proper** curves modulo the Legendre–Fenchel
congruence — the carrier on which both `⊓` [4.7] and `⊗` [4.8] descend. -/
def FmodLProper : Type := Quotient properSetoid

/-- The class `[f]_𝓛 ∈ ℱ↑/𝓛` of a proper curve `f`. -/
def FmodLProper.mk (f : ProperCurve) : FmodLProper := Quotient.mk properSetoid f

/-- `[f]_𝓛 = [g]_𝓛 ↔ 𝓛 f = 𝓛 g`: two proper curves give the same quotient
class iff they share the Legendre–Fenchel transform. -/
theorem FmodLProper.mk_eq_mk {f g : ProperCurve} :
    FmodLProper.mk f = FmodLProper.mk g ↔ SameLegendre f.1 g.1 := Quotient.eq

/-- Every class in `FmodLProper` is `[f]_𝓛` for some proper curve `f`. -/
theorem FmodLProper.mk_surjective : Function.Surjective FmodLProper.mk :=
  Quotient.mk_surjective

/-! ## The descended inf-convolution `⊗` [4.8]

`legendreConv` of proper representatives respects the congruence
(`SameLegendre.legendreConv`), so `⊗` descends — but the result need not be
proper (see the module residue), hence the codomain is the full quotient
`FmodL`. -/

/-- **[4.8] on the quotient: the descended `⊗`.** Inf-convolution lifts from
proper representatives to `FmodLProper`, with well-definedness given by
`SameLegendre.legendreConv`. The result lands in the **full** quotient `FmodL`
(the convolution of proper curves need not be proper). -/
noncomputable def FmodLProper.conv : FmodLProper → FmodLProper → FmodL :=
  Quotient.lift₂ (fun f g => FmodL.mk (legendreConv f.1 g.1))
    (fun f g f' g' hf hg => Quotient.sound
      (SameLegendre.legendreConv f.2 f'.2 g.2 g'.2 hf hg))

/-- `[f]_𝓛 ⊗ [g]_𝓛 = [f ⊗ g]_𝓛`: the descended convolution computes on
representatives (equation [4.8]). -/
@[simp] theorem FmodLProper.conv_mk (f g : ProperCurve) :
    FmodLProper.conv (FmodLProper.mk f) (FmodLProper.mk g)
      = FmodL.mk (legendreConv f.1 g.1) := rfl

/-! ## The descended meet `⊓` [4.7] on the proper subtype

A pointwise `min` of two non-`⊥` curves is non-`⊥`, so `⊓` stays inside the
proper subtype; well-definedness is `SameLegendre.inf` (unconditional). -/

/-- The pointwise meet `f ⊓ g` of two proper curves, again proper: a `min` of
two values `≠ ⊥` is `≠ ⊥`. -/
noncomputable def ProperCurve.inf (f g : ProperCurve) : ProperCurve :=
  ⟨f.1 ⊓ g.1, fun u => by
    rcases min_choice (f.1 u) (g.1 u) with h | h <;> rw [Pi.inf_apply, h]
    · exact f.2 u
    · exact g.2 u⟩

/-- `(f ⊓ g).1 = f.1 ⊓ g.1`: the proper meet is the pointwise meet of carriers. -/
@[simp] theorem ProperCurve.inf_val (f g : ProperCurve) :
    (ProperCurve.inf f g).1 = f.1 ⊓ g.1 := rfl

/-- **[4.7] on the proper subtype: the descended `⊓`.** `⊓` lifts to
`FmodLProper` via `SameLegendre.inf`, landing back in the proper subtype. -/
noncomputable def FmodLProper.inf : FmodLProper → FmodLProper → FmodLProper :=
  Quotient.lift₂ (fun f g => FmodLProper.mk (ProperCurve.inf f g))
    (fun _ _ _ _ hf hg => Quotient.sound (SameLegendre.inf hf hg))

/-- `[f]_𝓛 ⊓ [g]_𝓛 = [f ⊓ g]_𝓛`: the descended meet computes on representatives
(equation [4.7]). -/
@[simp] theorem FmodLProper.inf_mk (f g : ProperCurve) :
    FmodLProper.inf (FmodLProper.mk f) (FmodLProper.mk g)
      = FmodLProper.mk (ProperCurve.inf f g) := rfl

/-! ## Faithfulness checks (anonymous restatements vs the book) -/

-- Proposition 4.3 [4.8]: `⊗` descends to `ℱ↑/𝓛` on proper representatives.
example (f g : ProperCurve) :
    FmodLProper.conv (FmodLProper.mk f) (FmodLProper.mk g)
      = FmodL.mk (legendreConv f.1 g.1) := rfl

-- Proposition 4.3 [4.7]: `⊓` descends to `ℱ↑/𝓛` and stays proper.
example (f g : ProperCurve) :
    FmodLProper.inf (FmodLProper.mk f) (FmodLProper.mk g)
      = FmodLProper.mk (ProperCurve.inf f g) := rfl

-- Well-definedness of `⊗`: congruent proper representatives convolve to the
-- same class (this is what `Quotient.lift₂` consumes).
example {f f' g g' : ProperCurve}
    (hf : SameLegendre f.1 f'.1) (hg : SameLegendre g.1 g'.1) :
    FmodL.mk (legendreConv f.1 g.1) = FmodL.mk (legendreConv f'.1 g'.1) :=
  Quotient.sound (SameLegendre.legendreConv f.2 f'.2 g.2 g'.2 hf hg)

end Container

end DeepWiki
