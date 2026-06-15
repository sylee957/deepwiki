import DeepWiki.NetworkCalculus.LegendreFenchel
import DeepWiki.NetworkCalculus.ERealSupInf

/-! # The Legendre–Fenchel transform of an inf-convolution
For proper curves (never `⊥`), the (min,plus) transform turns the
inf-convolution into a sum: `𝓛(f ⊗ g) = 𝓛(f) + 𝓛(g)`, where
`(f ⊗ g)(t) = ⨅_{u+v=t} (f u + g v)`. The proof splits each affine slice through
the regrouping `↑(s(u+v)) − (f u + g v) = (↑(su) − f u) + (↑(sv) − g v)` (valid
since `f`, `g` avoid `⊥`) and the `EReal` sup/inf-distributivity of
`ERealSupInf`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The (min,plus) inf-convolution of two curves:
`(f ⊗ g)(t) = ⨅_{u+v=t} (f u + g v)`. -/
noncomputable def legendreConv (f g : ℝ≥0 → EReal) : ℝ≥0 → EReal :=
  fun t => ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t}, f p.1.1 + g p.1.2

/-- `(f ⊗ g)(t) = ⨅_{u+v=t} (f u + g v)` (the defining infimum). -/
theorem legendreConv_apply (f g : ℝ≥0 → EReal) (t : ℝ≥0) :
    legendreConv f g t = ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t}, f p.1.1 + g p.1.2 := rfl

/-- **𝓛(f ⊗ g) = 𝓛(f) + 𝓛(g)** for proper curves `f`, `g` (never `⊥`): the
Legendre–Fenchel transform turns inf-convolution into addition. -/
theorem legendre_legendreConv {f g : ℝ≥0 → EReal}
    (hf : ∀ u, f u ≠ ⊥) (hg : ∀ v, g v ≠ ⊥) :
    legendre (legendreConv f g) = legendre f + legendre g := by
  funext s
  -- the affine slice splits: `↑(s(u+v)) = ↑(su) + ↑(sv)`
  have key : ∀ u v : ℝ≥0,
      (((s * (u + v) : ℝ≥0) : ℝ) : EReal)
        = (((s * u : ℝ≥0) : ℝ) : EReal) + (((s * v : ℝ≥0) : ℝ) : EReal) := by
    intro u v
    rw [← EReal.coe_add]
    congr 1
    push_cast
    ring
  rw [Pi.add_apply]
  apply le_antisymm
  · rw [legendre_apply]
    refine iSup_le fun t => ?_
    rw [legendreConv_apply, coe_sub_iInf]
    refine iSup_le fun p => ?_
    obtain ⟨⟨u, v⟩, (huv : u + v = t)⟩ := p
    subst huv
    rw [key u v, coe_add_coe_sub_add (hf u) (hg v)]
    exact add_le_add (le_legendre f s u) (le_legendre g s v)
  · rw [legendre_apply, legendre_apply, iSup_add_iSup]
    refine iSup_le fun u => iSup_le fun v => ?_
    rw [← coe_add_coe_sub_add (hf u) (hg v), ← key u v]
    refine le_trans ?_
      (le_iSup (fun t => (((s * t : ℝ≥0) : ℝ) : EReal) - legendreConv f g t) (u + v))
    refine EReal.sub_le_sub (le_refl _) ?_
    rw [legendreConv_apply]
    exact iInf_le (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = u + v} => f p.1.1 + g p.1.2)
      ⟨(u, v), rfl⟩

end DeepWiki
