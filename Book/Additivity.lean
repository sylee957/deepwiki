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

/-- Build `IsSubadditive g` from `g 0 = 0` and sub-additivity restricted to
nonzero arguments. -/
theorem IsSubadditive.of_ne_zero {D T : Type*} [AddZeroClass D]
    [AddZeroClass T] [Preorder T] {g : D → T} (h0 : g 0 = 0)
    (hsub : ∀ u s : D, u ≠ 0 → s ≠ 0 → g (u + s) ≤ g u + g s) :
    IsSubadditive g := by
  intro u s
  rcases eq_or_ne u 0 with rfl | hu
  · rw [zero_add, h0, zero_add]
  · rcases eq_or_ne s 0 with rfl | hs
    · rw [add_zero, h0, add_zero]
    · exact hsub u s hu hs

/-- Build `IsSuperadditive g` from `g 0 = 0` and super-additivity restricted to
nonzero arguments. -/
theorem IsSuperadditive.of_ne_zero {D T : Type*} [AddZeroClass D]
    [AddZeroClass T] [Preorder T] {g : D → T} (h0 : g 0 = 0)
    (hsup : ∀ u s : D, u ≠ 0 → s ≠ 0 → g u + g s ≤ g (u + s)) :
    IsSuperadditive g := by
  intro u s
  rcases eq_or_ne u 0 with rfl | hu
  · rw [zero_add, h0, zero_add]
  · rcases eq_or_ne s 0 with rfl | hs
    · rw [add_zero, h0, add_zero]
    · exact hsup u s hu hs

/-- Sub-additivity transports through the real coercion: `fun t => (g t : ℝ)`
is sub-additive when `g : ℝ≥0 → ℝ≥0` is. -/
theorem IsSubadditive.coe_real {g : ℝ≥0 → ℝ≥0} (hsub : IsSubadditive g) :
    IsSubadditive (fun t => (g t : ℝ)) :=
  fun u s => by exact_mod_cast hsub u s

/-- Super-additivity transports through the real coercion: `fun t => (g t : ℝ)`
is super-additive when `g : ℝ≥0 → ℝ≥0` is. -/
theorem IsSuperadditive.coe_real {g : ℝ≥0 → ℝ≥0} (hsup : IsSuperadditive g) :
    IsSuperadditive (fun t => (g t : ℝ)) :=
  fun u s => by exact_mod_cast hsup u s

/-- A super-additive function into a canonically ordered monoid is
monotone: `g a ≤ g a + g (b - a) ≤ g (a + (b - a)) = g b`. -/
theorem IsSuperadditive.monotone {D T : Type*}
    [_root_.AddCommMonoid D] [PartialOrder D] [ExistsAddOfLE D]
    [Sub D] [OrderedSub D] [AddLeftMono D]
    [_root_.AddCommMonoid T] [PartialOrder T] [CanonicallyOrderedAdd T]
    {g : D → T} (hsup : IsSuperadditive g) : Monotone g := by
  intro a b hab
  calc g a ≤ g a + g (b - a) := le_self_add
    _ ≤ g (a + (b - a)) := hsup a (b - a)
    _ = g b := by rw [add_tsub_cancel_of_le hab]

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
def liftMinPlusNN {D : Type} (g : D → ℝ≥0∞) : D → MinPlusNN :=
  fun s => ⟨g s⟩

/-- `conv` of `liftMinPlusNN` lifts, read back via `toVal`, equals `minConv`. -/
theorem conv_liftMinPlusNN_apply {D : Type} [_root_.AddCommMonoid D]
    (g h : D → ℝ≥0∞) (t : D) :
    ((conv (liftMinPlusNN g) (liftMinPlusNN h) t : MinPlusNN) : ℝ≥0∞)
      = minConv g h t := by
  rw [conv_apply, MinPlusNN.toVal_sSup]
  apply le_antisymm
  · refine le_iInf (fun p => ?_)
    exact iInf_le_of_le ⟨_, p.1.1, p.1.2, p.2, rfl⟩ le_rfl
  · refine le_iInf (fun x => ?_)
    obtain ⟨u, s, hus, hx⟩ := x.2
    rw [hx]
    exact iInf_le_of_le ⟨(u, s), hus⟩ le_rfl

/-- `conv (liftMinPlusNN g) (liftMinPlusNN h) = liftMinPlusNN (minConv g h)`. -/
theorem conv_liftMinPlusNN {D : Type} [_root_.AddCommMonoid D]
    (g h : D → ℝ≥0∞) :
    conv (liftMinPlusNN g) (liftMinPlusNN h) = liftMinPlusNN (minConv g h) := by
  funext t
  apply MinPlusNN.ext
  exact conv_liftMinPlusNN_apply g h t

/-- `liftMinPlusNN` is injective. -/
theorem liftMinPlusNN_inj {D : Type} {g h : D → ℝ≥0∞}
    (H : liftMinPlusNN g = liftMinPlusNN h) : g = h := by
  funext t
  exact congrArg MinPlusNN.toVal (congrFun H t)

/-- `minConv` is associative on `ℝ≥0∞`-valued functions. -/
theorem minConvE_assoc {D : Type} [_root_.AddCommMonoid D]
    (f g h : D → ℝ≥0∞) :
    minConv (minConv f g) h
      = minConv f (minConv g h) := by
  apply liftMinPlusNN_inj
  rw [← conv_liftMinPlusNN, ← conv_liftMinPlusNN, ← conv_liftMinPlusNN, ← conv_liftMinPlusNN,
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

/-- Subadditive `g` with `g 0 = 0` is a `conv`-self fixed point in `liftMinPlusNN`. -/
theorem conv_self_liftMinPlusNN_of_subadditive
    {D : Type} [_root_.AddCommMonoid D]
    (g : D → ℝ≥0∞)
    (hsub : IsSubadditive g) (h0 : g 0 = 0) :
    conv (liftMinPlusNN g) (liftMinPlusNN g) = liftMinPlusNN g := by
  rw [conv_liftMinPlusNN, minConv_self_of_subadditive g hsub h0]

/-- The (min,+) convolution of `ℝ≥0∞` curves is associative (the truncated
subtraction adjunction routes the splits, no infimum distribution needed). -/
theorem minConv_assoc_enn {D : Type} [_root_.AddCommMonoid D]
    (f g h : D → ℝ≥0∞) :
    minConv (minConv f g) h = minConv f (minConv g h) := by
  funext t
  apply le_antisymm
  · refine le_minConv fun u v huv => ?_
    rw [← tsub_le_iff_left]
    refine le_minConv fun p q hpq => ?_
    rw [tsub_le_iff_left]
    calc minConv (minConv f g) h t
        ≤ minConv f g (u + p) + h q :=
          minConv_le_add _ _ (by rw [add_assoc, hpq, huv])
      _ ≤ (f u + g p) + h q :=
          add_le_add_left (minConv_le_add f g rfl) _
      _ = f u + (g p + h q) := add_assoc _ _ _
  · refine le_minConv fun u v huv => ?_
    rw [← tsub_le_iff_right]
    refine le_minConv fun p q hpq => ?_
    rw [tsub_le_iff_right]
    calc minConv f (minConv g h) t
        ≤ f p + minConv g h (q + v) :=
          minConv_le_add _ _ (by rw [← add_assoc, hpq, huv])
      _ ≤ f p + (g q + h v) :=
          add_le_add_right (minConv_le_add g h rfl) _
      _ = (f p + g q) + h v := (add_assoc _ _ _).symm

/-- Convolving with a subadditive curve is shift-subadditive:
`(f ∗ g) (u + v) ≤ (f ∗ g) u + g v`. -/
theorem minConv_apply_add_le_of_isSubadditive {D : Type}
    [_root_.AddCommMonoid D] {f g : D → ℝ≥0∞}
    (hsub : IsSubadditive g) (u v : D) :
    minConv f g (u + v) ≤ minConv f g u + g v := by
  rw [← tsub_le_iff_right]
  refine le_minConv fun p q hpq => ?_
  rw [tsub_le_iff_right]
  calc minConv f g (u + v)
      ≤ f p + g (q + v) := minConv_le_add f g (by rw [← add_assoc, hpq])
    _ ≤ f p + (g q + g v) := add_le_add_right (hsub q v) _
    _ = (f p + g q) + g v := (add_assoc _ _ _).symm

end DeepWiki
