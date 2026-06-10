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

/-- Sub-additivity iterated through a multiple:
`g (q • s + r) ≤ q • g s + g r`. -/
theorem IsSubadditive.apply_nsmul_add_le {D T : Type*}
    [_root_.AddCommMonoid D] [_root_.AddCommMonoid T] [PartialOrder T]
    [IsOrderedAddMonoid T] {g : D → T}
    (hsub : IsSubadditive g) (q : ℕ) (s r : D) :
    g (q • s + r) ≤ q • g s + g r := by
  induction q with
  | zero => simp
  | succ k ih =>
      calc g ((k + 1) • s + r)
          = g (s + (k • s + r)) := by
            rw [succ_nsmul, add_comm (k • s) s, add_assoc]
        _ ≤ g s + g (k • s + r) := hsub s _
        _ ≤ g s + (k • g s + g r) := add_le_add le_rfl ih
        _ = (k + 1) • g s + g r := by
            rw [succ_nsmul, add_comm (k • g s) (g s), add_assoc]

/-- Super-additivity iterated through a multiple:
`q • g s + g r ≤ g (q • s + r)`. -/
theorem IsSuperadditive.le_apply_nsmul_add {D T : Type*}
    [_root_.AddCommMonoid D] [_root_.AddCommMonoid T] [PartialOrder T]
    [IsOrderedAddMonoid T] {g : D → T}
    (hsup : IsSuperadditive g) (q : ℕ) (s r : D) :
    q • g s + g r ≤ g (q • s + r) := by
  induction q with
  | zero => simp
  | succ k ih =>
      calc (k + 1) • g s + g r
          = g s + (k • g s + g r) := by
            rw [succ_nsmul, add_comm (k • g s) (g s), add_assoc]
        _ ≤ g s + g (k • s + r) := add_le_add le_rfl ih
        _ ≤ g (s + (k • s + r)) := hsup s _
        _ = g ((k + 1) • s + r) := by
            rw [succ_nsmul, add_comm (k • s) s, add_assoc]

/-- Subadditive `g` with `g 0 = 0` is a `minConv` fixed point. -/
theorem minConv_self_of_subadditive {D T : Type*}
    [_root_.AddCommMonoid D] [CompleteLattice T]
    [_root_.AddCommMonoid T] [IsOrderedAddMonoid T]
    (g : D → T)
    (hsub : IsSubadditive g) (h0 : g 0 = 0) :
    minConv g g = g := by
  funext t
  exact le_antisymm
    ((minConv_le_add g g (zero_add t)).trans_eq (by rw [h0, zero_add]))
    (le_minConv fun u s hus => hus ▸ hsub u s)

/-- Superadditive `g` with `g 0 = 0` is a `maxConv` fixed point. -/
theorem maxConv_self_of_superadditive {D T : Type*}
    [_root_.AddCommMonoid D] [CompleteLattice T]
    [_root_.AddCommMonoid T] [IsOrderedAddMonoid T]
    (g : D → T)
    (hsup : IsSuperadditive g) (h0 : g 0 = 0) :
    maxConv g g = g := by
  funext t
  exact le_antisymm
    (maxConv_le fun u s hus => hus ▸ hsup u s)
    (le_trans (by rw [h0, zero_add]) (add_le_maxConv g g (zero_add t)))

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
  · exact le_inf
      ((minConv_le_add f g (add_zero t)).trans_eq (by rw [hg0, add_zero]))
      ((minConv_le_add f g (zero_add t)).trans_eq (by rw [hf0, zero_add]))
  · refine le_minConv fun u s hus => ?_
    calc (f ⊓ g) t = (f ⊓ g) (u + s) := by rw [hus]
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
