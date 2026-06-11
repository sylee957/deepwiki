import Book.Additivity
import Book.FunctionDioids

/-! # Deconvolution
Algebra of the (min,+) deconvolution over `ℝ≥0∞`: the residuation
`f ⊘ g ≤ h ↔ f ≤ h ∗ g` (deconvolution is the lower Galois adjoint of the
convolution), the composition bound `(f ∗ g) ⊘ h ≤ f ∗ (g ⊘ h)`, and for
sub-additive `f` the self-bound `f ⊘ f ≤ f` and the origin-shift bound
`(f ⊘ g) d ≤ f d + (f ⊘ g) 0`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **Deconvolution is the residual of the convolution**:
`f ⊘ g ≤ h ↔ f ≤ h ∗ g` on `ℝ≥0∞` curves. -/
theorem minDeconv_le_iff_le_minConv {f g h : ℝ≥0 → ℝ≥0∞} :
    minDeconv f g ≤ h ↔ f ≤ minConv h g := by
  constructor
  · intro hle t
    refine le_minConv fun u v huv => ?_
    calc f t = f (u + v) := by rw [huv]
      _ ≤ minDeconv f g u + g v :=
          le_tsub_add.trans (add_le_add (sub_le_minDeconv f g u v) le_rfl)
      _ ≤ h u + g v := add_le_add (hle u) le_rfl
  · intro hle t
    refine minDeconv_le fun s => ?_
    rw [tsub_le_iff_right]
    exact le_trans (hle (t + s)) (minConv_le_add h g rfl)

/-- The deconvolution–convolution Galois connection on `ℝ≥0∞` curves:
`(· ⊘ g)` is left adjoint to `(· ∗ g)`. -/
theorem galoisConnection_minDeconv_minConv (g : ℝ≥0 → ℝ≥0∞) :
    GaloisConnection (fun f : ℝ≥0 → ℝ≥0∞ => minDeconv f g)
      (fun h : ℝ≥0 → ℝ≥0∞ => minConv h g) :=
  fun _ _ => minDeconv_le_iff_le_minConv

/-- Deconvolution composes into a convolution:
`(f ⊘ g) ⊘ h = f ⊘ (g ∗ h)` on `ℝ≥0∞` curves — the two sides are left
adjoints of the same map, by associativity and commutativity. -/
theorem minDeconv_minDeconv (f g h : ℝ≥0 → ℝ≥0∞) :
    minDeconv (minDeconv f g) h = minDeconv f (minConv g h) := by
  apply le_antisymm
  · rw [minDeconv_le_iff_le_minConv, minDeconv_le_iff_le_minConv,
      minConv_assoc_enn, minConv_comm h g]
    exact minDeconv_le_iff_le_minConv.mp le_rfl
  · rw [minDeconv_le_iff_le_minConv]
    calc f ≤ minConv (minDeconv f g) g :=
          minDeconv_le_iff_le_minConv.mp le_rfl
      _ ≤ minConv (minConv (minDeconv (minDeconv f g) h) h) g := fun t =>
          minConv_le_minConv
            (fun s => minDeconv_le_iff_le_minConv.mp le_rfl s)
            (fun _ => le_rfl) t
      _ = minConv (minDeconv (minDeconv f g) h) (minConv h g) :=
          minConv_assoc_enn _ _ _
      _ = minConv (minDeconv (minDeconv f g) h) (minConv g h) := by
          rw [minConv_comm h g]

/-- Deconvolving a convolution: `(f ∗ g) ⊘ h ≤ f ∗ (g ⊘ h)` on `ℝ≥0∞`. -/
theorem minDeconv_minConv_le (f g h : ℝ≥0 → ℝ≥0∞) :
    minDeconv (minConv f g) h ≤ minConv f (minDeconv g h) := by
  intro t
  refine minDeconv_le fun s => ?_
  refine le_minConv fun u v huv => ?_
  rw [tsub_le_iff_right]
  calc minConv f g (t + s)
      ≤ f u + g (v + s) :=
        minConv_le_add f g (by rw [← add_assoc, huv])
    _ ≤ f u + (minDeconv g h v + h s) :=
        add_le_add le_rfl (le_tsub_add.trans
          (add_le_add (sub_le_minDeconv g h v s) le_rfl))
    _ = f u + minDeconv g h v + h s := (add_assoc _ _ _).symm

/-- A sub-additive `f` bounds its own deconvolution: `f ⊘ f ≤ f` on `ℝ≥0∞`. -/
theorem minDeconv_self_le_of_isSubadditive {f : ℝ≥0 → ℝ≥0∞}
    (hsub : IsSubadditive f) : minDeconv f f ≤ f := fun t =>
  minDeconv_le fun s => tsub_le_iff_right.mpr (hsub t s)

/-- For sub-additive `f`, the deconvolution exceeds its origin value by at
most `f`: `(f ⊘ g) d ≤ f d + (f ⊘ g) 0` on `ℝ≥0∞`. -/
theorem minDeconv_le_add_minDeconv_zero {f : ℝ≥0 → ℝ≥0∞} (g : ℝ≥0 → ℝ≥0∞)
    (hsub : IsSubadditive f) (d : ℝ≥0) :
    minDeconv f g d ≤ f d + minDeconv f g 0 := by
  refine minDeconv_le fun u => ?_
  calc f (d + u) - g u
      ≤ (f d + f u) - g u := tsub_le_tsub_right (hsub d u) _
    _ ≤ f d + (f u - g u) := add_tsub_le_assoc
    _ ≤ f d + minDeconv f g 0 :=
        add_le_add le_rfl (le_iSup_of_le u (by rw [zero_add]))

end DeepWiki
