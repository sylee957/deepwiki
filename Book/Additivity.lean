import Book.FunctionDioids

/-! # Additivity
Sub- and super-additivity predicates (natural numeric order) and the
stability of (min,plus)/(max,plus) self-convolution under them. -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge

/-- `g` is subadditive: `g (u + s) ≤ g u + g s`. -/
def IsSubadditive {D T : Type*} [Add D]
    [_root_.Add T] [LE T] (g : D → T) : Prop :=
  ∀ u s : D, g (u + s) ≤ g u + g s

/-- `g` is superadditive: `g u + g s ≤ g (u + s)`. -/
def IsSuperadditive {D T : Type*} [Add D]
    [_root_.Add T] [LE T] (g : D → T) : Prop :=
  ∀ u s : D, g u + g s ≤ g (u + s)

/-- Subadditive `g` with `g 0 = 0` is a `minConv` fixed point. -/
theorem minConv_self_of_subadditive {D T : Type*}
    [_root_.AddCommMonoid D] [CompleteLattice T]
    [_root_.AddCommMonoid T] [IsOrderedAddMonoid T]
    (g : D → T)
    (hsub : IsSubadditive g) (h0 : g 0 = 0) :
    minConv g g = g := by
  funext t
  unfold minConv
  apply le_antisymm
  · refine iInf_le_of_le ⟨(0, t), by simp⟩ ?_
    simp [h0]
  · refine le_iInf ?_
    rintro ⟨⟨u, s⟩, hus⟩
    simp only
    calc g t = g (u + s) := by rw [hus]
      _ ≤ g u + g s := hsub u s

/-- Superadditive `g` with `g 0 = 0` is a `maxConv` fixed point. -/
theorem maxConv_self_of_superadditive {D T : Type*}
    [_root_.AddCommMonoid D] [CompleteLattice T]
    [_root_.AddCommMonoid T] [IsOrderedAddMonoid T]
    (g : D → T)
    (hsup : IsSuperadditive g) (h0 : g 0 = 0) :
    maxConv g g = g := by
  funext t
  unfold maxConv
  apply le_antisymm
  · refine iSup_le ?_
    rintro ⟨⟨u, s⟩, hus⟩
    simp only
    calc g u + g s ≤ g (u + s) := hsup u s
      _ = g t := by rw [hus]
  · exact le_iSup_of_le ⟨(0, t), by simp⟩ (by simp [h0])

/-- Lift an `ℝ≥0∞`-valued function into `MinPlusNN` pointwise. -/
def toF {D : Type} (g : D → ℝ≥0∞) : D → MinPlusNN :=
  fun s => ⟨g s⟩

/-- `conv` of `toF` lifts, read back via `toVal`, equals `minConv`. -/
theorem conv_toF_apply {D : Type} [_root_.AddCommMonoid D]
    (g h : D → ℝ≥0∞) (t : D) :
    ((conv (toF g) (toF h) t : MinPlusNN) : ℝ≥0∞)
      = minConv g h t := by
  apply le_antisymm
  · refine le_iInf ?_
    rintro ⟨⟨u, s⟩, hus⟩
    have hle := CompleteDioid.le_sSup _ _
      (show (toF g u ⊗ₒ toF h s)
          ∈ {x | ∃ u s, u + s = t
              ∧ x = toF g u ⊗ₒ toF h s}
        from ⟨u, s, hus, rfl⟩)
    rw [← conv_apply] at hle
    exact (MinPlusNN.le_iff _ _).mp hle
  · rw [conv_apply, ← MinPlusNN.le_iff]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, s, hus, rfl⟩
    rw [MinPlusNN.le_iff]
    exact iInf_le_of_le ⟨(u, s), hus⟩ (le_refl _)

/-- `conv (toF g) (toF h) = toF (minConv g h)`. -/
theorem conv_toF {D : Type} [_root_.AddCommMonoid D]
    (g h : D → ℝ≥0∞) :
    conv (toF g) (toF h) = toF (minConv g h) := by
  funext t
  apply MinPlusNN.ext
  exact conv_toF_apply g h t

/-- `toF` is injective. -/
theorem toF_inj {D : Type} {g h : D → ℝ≥0∞}
    (H : toF g = toF h) : g = h := by
  funext t
  exact congrArg MinPlusNN.toVal (congrFun H t)

/-- `minConv` is commutative on `ℝ≥0∞`-valued functions. -/
theorem minConvE_comm {D : Type} [_root_.AddCommMonoid D]
    (g h : D → ℝ≥0∞) :
    minConv g h = minConv h g := by
  apply toF_inj
  rw [← conv_toF, ← conv_toF, conv_comm]

/-- `minConv` is associative on `ℝ≥0∞`-valued functions. -/
theorem minConvE_assoc {D : Type} [_root_.AddCommMonoid D]
    (f g h : D → ℝ≥0∞) :
    minConv (minConv f g) h
      = minConv f (minConv g h) := by
  apply toF_inj
  rw [← conv_toF, ← conv_toF, ← conv_toF, ← conv_toF,
    conv_assoc]

/-- If `f ⊓ g` is subadditive (and both fix 0), `minConv f g = f ⊓ g`. -/
theorem minConv_eq_inf_of_subadditive {D T : Type*}
    [_root_.AddCommMonoid D] [CompleteLattice T]
    [_root_.AddCommMonoid T] [IsOrderedAddMonoid T]
    (f g : D → T)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hinf : IsSubadditive (f ⊓ g)) :
    minConv f g = f ⊓ g := by
  funext t
  apply le_antisymm
  · refine le_inf ?_ ?_
    · unfold minConv
      refine iInf_le_of_le ⟨(t, 0), by simp⟩ ?_
      simp only; rw [hg0, add_zero]
    · unfold minConv
      refine iInf_le_of_le ⟨(0, t), by simp⟩ ?_
      simp only; rw [hf0, zero_add]
  · unfold minConv
    refine le_iInf ?_
    rintro ⟨⟨u, s⟩, (huv : u + s = t)⟩
    simp only
    calc (f ⊓ g) t = (f ⊓ g) (u + s) := by rw [huv]
      _ ≤ (f ⊓ g) u + (f ⊓ g) s := hinf u s
      _ ≤ f u + g s :=
          add_le_add inf_le_left inf_le_right

/-- Subadditive `g` with `g 0 = 0` is a `conv`-self fixed point in `toF`. -/
theorem conv_self_toF_of_subadditive
    {D : Type} [_root_.AddCommMonoid D]
    (g : D → ℝ≥0∞)
    (hsub : IsSubadditive g) (h0 : g 0 = 0) :
    conv (toF g) (toF g) = toF g := by
  rw [conv_toF, minConv_self_of_subadditive g hsub h0]

end DeepWiki
