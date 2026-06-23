import DeepWiki.NetworkCalculus.LegendreFenchel
import DeepWiki.NetworkCalculus.Concave
import DeepWiki.NetworkCalculus.ConcaveProps

/-! # The concave hull `Ccv`
The **smallest concave function above `f`** (the concave-approximation operator
`𝒞_cv` of DNC §4.4, eq. [4.6], whose defining piece `f_cv` is "the smallest
concave function greater than `f`"). Built directly as the pointwise infimum of
all concave majorants of `f`; this infimum is itself concave (`iInf` of concave
is concave) and majorizes `f`, so it *is* the least concave function `≥ f`. The
satellite API: it is concave (`isConcaveEReal_Ccv`), majorizes (`le_Ccv`), is the
least such (`Ccv_le`), fixes concave curves (`Ccv_eq_self_of_isConcaveEReal`), is
idempotent (`Ccv_Ccv`) and monotone (`Ccv_mono`). The companion `𝒞_vx = 𝓛∘𝓛`
(convex biconjugate) lives in `DeepWiki.NetworkCalculus.LegendreFenchel`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The set of concave curves lying pointwise above `f : ℝ≥0 → EReal`. -/
def concaveMajorants (f : ℝ≥0 → EReal) : Set (ℝ≥0 → EReal) :=
  {g | IsConcaveEReal g ∧ f ≤ g}

/-- The constant `⊤` curve is a concave majorant of any `f`, so
`concaveMajorants f` is never empty. -/
theorem top_mem_concaveMajorants (f : ℝ≥0 → EReal) :
    (fun _ : ℝ≥0 => (⊤ : EReal)) ∈ concaveMajorants f := by
  refine ⟨?_, ?_⟩
  · intro s t p _; exact le_top
  · intro x; exact le_top

/-- **The concave hull** `𝒞_cv f`: the pointwise infimum of all concave curves
lying above `f` — the smallest concave function `≥ f` (DNC eq. [4.6], piece
`f_cv`). -/
noncomputable def Ccv (f : ℝ≥0 → EReal) : ℝ≥0 → EReal :=
  fun t => ⨅ g : concaveMajorants f, (g : ℝ≥0 → EReal) t

/-- `𝒞_cv f t = ⨅ g ∈ concaveMajorants f, g t` (the defining infimum). -/
theorem Ccv_apply (f : ℝ≥0 → EReal) (t : ℝ≥0) :
    Ccv f t = ⨅ g : concaveMajorants f, (g : ℝ≥0 → EReal) t := rfl

/-- Each concave majorant bounds the hull from above: `𝒞_cv f t ≤ g t` for every
`g ∈ concaveMajorants f`. -/
theorem Ccv_apply_le {f : ℝ≥0 → EReal} {g : ℝ≥0 → EReal}
    (hg : g ∈ concaveMajorants f) (t : ℝ≥0) : Ccv f t ≤ g t :=
  iInf_le (fun g : concaveMajorants f => (g : ℝ≥0 → EReal) t) ⟨g, hg⟩

/-- **The concave hull majorizes `f`**: `f ≤ 𝒞_cv f` (DNC: `𝒞_cv f ≥ f`). Each
concave majorant `g` satisfies `f t ≤ g t`, and the infimum over all of them
stays `≥ f t`. -/
theorem le_Ccv (f : ℝ≥0 → EReal) : f ≤ Ccv f := by
  intro t
  rw [Ccv_apply]
  exact le_iInf fun g => g.2.2 t

/-- **The concave hull is the least concave majorant**: for any concave `g ≥ f`,
`𝒞_cv f ≤ g` pointwise. -/
theorem Ccv_le {f g : ℝ≥0 → EReal} (hgc : IsConcaveEReal g) (hgf : f ≤ g) :
    Ccv f ≤ g := fun t => Ccv_apply_le ⟨hgc, hgf⟩ t

/-- **The concave hull is concave**: a pointwise infimum of concave curves is
concave. For each chord, the right `iInf` is reached by `le_iInf`; pushing one
majorant `g` through, the two scaled hull terms are below `g`'s, and `g`'s chord
finishes. -/
theorem isConcaveEReal_Ccv (f : ℝ≥0 → EReal) : IsConcaveEReal (Ccv f) := by
  intro s t p hp
  have hp0 : (0 : EReal) ≤ ((p : ℝ) : EReal) := by exact_mod_cast p.coe_nonneg
  have hq0 : (0 : EReal) ≤ (((1 - p : ℝ≥0) : ℝ) : EReal) := by
    exact_mod_cast (1 - p : ℝ≥0).coe_nonneg
  rw [Ccv_apply]
  refine le_iInf fun g => ?_
  refine le_trans ?_ (g.2.1 s t p hp)
  exact add_le_add
    (mul_le_mul_of_nonneg_left (Ccv_apply_le g.2 s) hp0)
    (mul_le_mul_of_nonneg_left (Ccv_apply_le g.2 t) hq0)

/-- **A concave curve is its own hull**: `IsConcaveEReal f → 𝒞_cv f = f`. `f`
is a concave majorant of itself, so `𝒞_cv f ≤ f`; `le_Ccv` gives `f ≤ 𝒞_cv f`. -/
theorem Ccv_eq_self_of_isConcaveEReal {f : ℝ≥0 → EReal} (hf : IsConcaveEReal f) :
    Ccv f = f :=
  le_antisymm (Ccv_le hf le_rfl) (le_Ccv f)

/-- **Idempotence of the concave hull**: `𝒞_cv (𝒞_cv f) = 𝒞_cv f` — `𝒞_cv f`
is concave, hence fixed by `𝒞_cv`. -/
theorem Ccv_Ccv (f : ℝ≥0 → EReal) : Ccv (Ccv f) = Ccv f :=
  Ccv_eq_self_of_isConcaveEReal (isConcaveEReal_Ccv f)

/-- **The concave hull is monotone**: `f ≤ g → 𝒞_cv f ≤ 𝒞_cv g`. `𝒞_cv g` is a
concave majorant of `g` hence of `f`, so the least concave majorant of `f` lies
below it. -/
theorem Ccv_mono {f g : ℝ≥0 → EReal} (h : f ≤ g) : Ccv f ≤ Ccv g :=
  Ccv_le (isConcaveEReal_Ccv g) (le_trans h (le_Ccv g))

end DeepWiki
