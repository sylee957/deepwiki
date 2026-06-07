import Book.FunctionDioids
import Book.Additivity

/-! # Closures
Kleene-star (sub-additive) closure `σ⋆ = ⨆ n, σⁿ` and its identities:
idempotence, sub/super-additivity, monotonicity, fixed points. -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge

/-- `n`-fold convolution power `σⁿ`; `σ⁰ = convUnit`. -/
noncomputable def convPow {D : Type}
    [_root_.AddCommMonoid D]
    {T : Type} [CompleteDioid T]
    (sigma : D → T) : ℕ → (D → T)
  | 0 => convUnit
  | n + 1 => conv (convPow sigma n) sigma

/-- Kleene star `σ⋆ = ⨆ n, σⁿ`, the sub-additive closure. -/
noncomputable def subadditiveClosure
    {D : Type} [_root_.AddCommMonoid D]
    {T : Type} [CompleteDioid T]
    (sigma : D → T) : D → T :=
  fun t =>
    CompleteDioid.iSup
      (fun n : ℕ => convPow sigma n t)

/-- `σ⋆` notation for `subadditiveClosure σ`. -/
scoped notation:max sigma:90 "⋆" =>
  subadditiveClosure sigma

/-- `σ¹ = σ`. -/
theorem convPow_one {D : Type} [_root_.AddCommMonoid D]
    {T : Type} [CompleteDioid T]
    (sigma : D → T) :
    convPow sigma 1 = sigma := by
  change conv convUnit sigma = sigma
  exact convUnit_left sigma

/-- Each power is below the closure: `σᵏ t ≼ σ⋆ t`. -/
theorem convPow_le_closure {D : Type}
    [_root_.AddCommMonoid D]
    {T : Type} [CompleteDioid T]
    (sigma : D → T) (k : ℕ) (t : D) :
    convPow sigma k t ≼ₒ subadditiveClosure sigma t :=
  CompleteDioid.le_iSup
    (fun n : ℕ => convPow sigma n t) k

/-- Power additivity: `σᵐ ∗ σⁿ = σᵐ⁺ⁿ`. -/
theorem convPow_add {D : Type} [_root_.AddCommMonoid D]
    {T : Type} [CompleteDioid T]
    (sigma : D → T) (m n : ℕ) :
    conv (convPow sigma m) (convPow sigma n)
      = convPow sigma (m + n) := by
  induction n with
  | zero =>
      show conv (convPow sigma m) convUnit
          = convPow sigma (m + 0)
      rw [convUnit_right, Nat.add_zero]
  | succ n ih =>
      show conv (convPow sigma m)
              (conv (convPow sigma n) sigma)
          = convPow sigma (m + (n + 1))
      rw [← conv_assoc, ih]
      show convPow sigma (m + n + 1) = _
      ring_nf

/-- `σᵐ u ⊗ σⁿ s ≼ σ⋆ (u + s)`. -/
theorem convPow_term_le_closure {D : Type}
    [_root_.AddCommMonoid D]
    {T : Type} [CompleteDioid T]
    (sigma : D → T) (m n : ℕ) (u s : D) :
    convPow sigma m u ⊗ₒ convPow sigma n s
      ≼ₒ subadditiveClosure sigma (u + s) := by
  refine le_trans ?_
    (CompleteDioid.le_iSup
      (fun k => convPow sigma k (u + s)) (m + n))
  rw [← convPow_add, conv_apply]
  exact CompleteDioid.le_sSup _ _ ⟨u, s, rfl, rfl⟩

/-- Idempotence of the closure: `σ⋆ ∗ σ⋆ = σ⋆`. -/
theorem closure_idem {D : Type} [_root_.AddCommMonoid D]
    {T : Type} [CompleteDioid T]
    (sigma : D → T) :
    conv (subadditiveClosure sigma)
        (subadditiveClosure sigma)
      = subadditiveClosure sigma := by
  funext t
  apply le_antisymm
  · rw [conv_apply]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, s, hus, rfl⟩
    show subadditiveClosure sigma u
        ⊗ₒ subadditiveClosure sigma s
      ≼ₒ subadditiveClosure sigma t
    dsimp only [subadditiveClosure]
    rw [CompleteDioid.mul_iSup]
    refine CompleteDioid.iSup_le _ _ (fun m => ?_)
    rw [mul_comm, CompleteDioid.mul_iSup]
    refine CompleteDioid.iSup_le _ _ (fun n => ?_)
    rw [mul_comm, ← hus]
    exact convPow_term_le_closure sigma n m u s
  · rw [conv_apply]
    refine le_trans ?_
      (CompleteDioid.le_sSup _ _
        ⟨t, 0, add_zero t, rfl⟩)
    show subadditiveClosure sigma t
      ≼ₒ subadditiveClosure sigma t
          ⊗ₒ subadditiveClosure sigma 0
    have he : eₒ ≼ₒ subadditiveClosure sigma 0 := by
      have h00 : convPow sigma 0 0 = eₒ := by
        show convUnit 0 = eₒ
        rw [convUnit, if_pos rfl]
      rw [← h00]
      exact CompleteDioid.le_iSup
        (fun n => convPow sigma n 0) 0
    calc subadditiveClosure sigma t
        = subadditiveClosure sigma t ⊗ₒ eₒ :=
          (MulMonoid.otimes_one _).symm
      _ ≼ₒ subadditiveClosure sigma t
            ⊗ₒ subadditiveClosure sigma 0 :=
          mul_le_mul_left he _

/-- Closure is sub-additive: `σ⋆ u ⊗ σ⋆ s ≼ σ⋆ (u + s)`. -/
theorem closure_subadditive {D : Type}
    [_root_.AddCommMonoid D]
    {T : Type} [CompleteDioid T]
    (sigma : D → T) (u s : D) :
    subadditiveClosure sigma u
        ⊗ₒ subadditiveClosure sigma s
      ≼ₒ subadditiveClosure sigma (u + s) := by
  have hterm :
      subadditiveClosure sigma u
          ⊗ₒ subadditiveClosure sigma s
        ≼ₒ conv (subadditiveClosure sigma)
            (subadditiveClosure sigma) (u + s) := by
    rw [conv_apply]
    exact CompleteDioid.le_sSup _ _ ⟨u, s, rfl, rfl⟩
  rwa [closure_idem sigma] at hterm

/-- A sub-complete-dioid predicate is closed under `σ⋆`. -/
theorem Algebra.IsSubCompleteDioid.closure {D : Type}
    [_root_.AddCommMonoid D]
    {T : Type} [CompleteDioid T] {P : (D → T) → Prop}
    (h : IsSubCompleteDioid P) {sigma : D → T}
    (hs : P sigma) : P (subadditiveClosure sigma) := by
  have hpow : ∀ n, P (convPow sigma n) := by
    intro n
    induction n with
    | zero => exact h.one
    | succ n ih => exact h.mul ih hs
  exact h.iSup (fun n => convPow sigma n) hpow

/-- Closure preserves non-negativity and monotonicity. -/
theorem closure_mem_FNondecr (a : FminBar)
    (hn : IsNonneg (fun t => (a t).toVal))
    (hm : Monotone (fun t => (a t).toVal)) :
    IsNonneg (fun t => (subadditiveClosure a t).toVal)
      ∧ Monotone
          (fun t => (subadditiveClosure a t).toVal) :=
  isSubCompleteDioid_FNondecr.closure ⟨hn, hm⟩

/-- If `σ` is idempotent with unit below it, `σⁿ ≼ σ`. -/
theorem convPow_le_self {D : Type} [_root_.AddCommMonoid D]
    {T : Type} [CompleteDioid T]
    (sigma : D → T) (hidem : conv sigma sigma = sigma)
    (hunit : ∀ t, convUnit (T := T) t ≼ₒ sigma t)
    (n : ℕ) (t : D) :
    convPow sigma n t ≼ₒ sigma t := by
  induction n generalizing t with
  | zero => exact hunit t
  | succ k ih =>
      show conv (convPow sigma k) sigma t ≼ₒ sigma t
      rw [conv_apply]
      refine CompleteDioid.sSup_le _ _ ?_
      rintro x ⟨u, s, hus, rfl⟩
      calc convPow sigma k u ⊗ₒ sigma s
          ≼ₒ sigma u ⊗ₒ sigma s := mul_le_mul_right (ih u) _
        _ ≼ₒ conv sigma sigma t := by
            rw [conv_apply, ← hus]
            exact CompleteDioid.le_sSup _ _ ⟨u, s, rfl, rfl⟩
        _ = sigma t := by rw [hidem]

/-- Closure is a fixed point: idempotent `σ ≽ unit` gives `σ⋆ = σ`. -/
theorem subadditiveClosure_eq_self {D : Type}
    [_root_.AddCommMonoid D]
    {T : Type} [CompleteDioid T] (sigma : D → T)
    (hidem : conv sigma sigma = sigma)
    (hunit : ∀ t, convUnit (T := T) t ≼ₒ sigma t) :
    subadditiveClosure sigma = sigma := by
  funext t
  apply le_antisymm
  · exact CompleteDioid.iSup_le _ _
      (fun n => convPow_le_self sigma hidem hunit n t)
  · have := convPow_le_closure sigma 1 t
    rwa [convPow_one] at this

/-- Monotonicity of powers: `σ ≼ τ` implies `σⁿ ≼ τⁿ`. -/
theorem convPow_mono {D : Type} [_root_.AddCommMonoid D]
    {T : Type} [CompleteDioid T]
    (sigma tau : D → T)
    (h : ∀ r, sigma r ≼ₒ tau r) (n : ℕ) (t : D) :
    convPow sigma n t ≼ₒ convPow tau n t := by
  induction n generalizing t with
  | zero => exact le_refl _
  | succ k ih =>
      show conv (convPow sigma k) sigma t
          ≼ₒ conv (convPow tau k) tau t
      rw [conv_apply, conv_apply]
      refine CompleteDioid.sSup_le _ _ ?_
      rintro x ⟨u, s, hus, rfl⟩
      exact le_trans (mul_le_mul' (ih u) (h s))
        (CompleteDioid.le_sSup _ _ ⟨u, s, hus, rfl⟩)

/-- Monotonicity of closure: `σ ≼ τ` implies `σ⋆ ≼ τ⋆`. -/
theorem subadditiveClosure_mono {D : Type}
    [_root_.AddCommMonoid D]
    {T : Type} [CompleteDioid T] (sigma tau : D → T)
    (h : ∀ r, sigma r ≼ₒ tau r) (t : D) :
    subadditiveClosure sigma t
      ≼ₒ subadditiveClosure tau t :=
  CompleteDioid.iSup_le _ _ (fun n =>
    le_trans (convPow_mono sigma tau h n t)
      (convPow_le_closure tau n t))

/-- Closure on numeric `ℝ≥0∞` values via the `MinPlusNN` carrier. -/
noncomputable def subadditiveClosureE {D : Type}
    [_root_.AddCommMonoid D]
    (g : D → ℝ≥0∞) : D → ℝ≥0∞ :=
  fun t => (subadditiveClosure (toF g) t).toVal

/-- `toF` transports `subadditiveClosureE` to `subadditiveClosure`. -/
theorem toF_subadditiveClosureE {D : Type}
    [_root_.AddCommMonoid D] (g : D → ℝ≥0∞) :
    toF (subadditiveClosureE g)
      = subadditiveClosure (toF g) := by
  funext t; apply MinPlusNN.ext; rfl

/-- Closure lies below the original: `g⋆ t ≤ g t` (numeric). -/
theorem subadditiveClosureE_le {D : Type}
    [_root_.AddCommMonoid D] (g : D → ℝ≥0∞)
    (t : D) : subadditiveClosureE g t ≤ g t := by
  have h := convPow_le_closure (toF g) 1 t
  rw [convPow_one, MinPlusNN.le_iff] at h
  exact h

/-- Numeric closure is idempotent under `minConv`. -/
theorem subadditiveClosureE_idem {D : Type}
    [_root_.AddCommMonoid D] (g : D → ℝ≥0∞) :
    minConv (subadditiveClosureE g)
        (subadditiveClosureE g)
      = subadditiveClosureE g := by
  have h := closure_idem (toF g)
  rw [← toF_subadditiveClosureE, conv_toF] at h
  funext t
  exact congrArg MinPlusNN.toVal (congrFun h t)

/-- Numeric closure is sub-additive. -/
theorem subadditiveClosureE_subadditive {D : Type}
    [_root_.AddCommMonoid D] (g : D → ℝ≥0∞) :
    IsSubadditive (subadditiveClosureE g) := by
  intro u s
  have h := closure_subadditive (toF g) u s
  rw [MinPlusNN.le_iff] at h
  calc subadditiveClosureE g (u + s)
      = (subadditiveClosure (toF g) (u + s)).toVal := rfl
    _ ≤ (subadditiveClosure (toF g) u
          ⊗ₒ subadditiveClosure (toF g) s).toVal := h
    _ = subadditiveClosureE g u
          + subadditiveClosureE g s := rfl

/-- Sub-additive `g` with `g 0 = 0` is its own closure. -/
theorem subadditiveClosureE_eq_self {D : Type}
    [_root_.AddCommMonoid D] (g : D → ℝ≥0∞)
    (hsub : IsSubadditive g) (h0 : g 0 = 0) :
    subadditiveClosureE g = g := by
  have hidem : conv (toF g) (toF g) = toF g := by
    rw [conv_toF, minConvE_self_of_subadditive g hsub h0]
  have hunit : ∀ t,
      convUnit (T := MinPlusNN) t ≼ₒ toF g t := by
    intro t
    rcases eq_or_ne t 0 with ht | ht
    · subst ht
      rw [convUnit, if_pos rfl, MinPlusNN.le_iff]
      show (toF g 0).toVal ≤ (eₒ : MinPlusNN).toVal
      simp [toF, h0]
    · rw [convUnit, if_neg ht]; exact OrderBot.bot_le _
  have hself :=
    subadditiveClosure_eq_self (toF g) hidem hunit
  funext t
  show (subadditiveClosure (toF g) t).toVal = g t
  rw [hself]; rfl

/-- Numeric closure is monotone in `g`. -/
theorem subadditiveClosureE_mono {D : Type}
    [_root_.AddCommMonoid D] (g h : D → ℝ≥0∞)
    (hgh : ∀ t, g t ≤ h t) (t : D) :
    subadditiveClosureE g t ≤ subadditiveClosureE h t := by
  show (subadditiveClosure (toF g) t).toVal
      ≤ (subadditiveClosure (toF h) t).toVal
  rw [← MinPlusNN.le_iff]
  refine subadditiveClosure_mono (toF h) (toF g) ?_ t
  intro r; rw [MinPlusNN.le_iff]; exact hgh r

/-- Wrap a numeric `g` into the `MaxPlusNN` function `Fmax`. -/
def toFmax (g : ℝ≥0 → WithBot ℝ≥0∞) : Fmax :=
  fun s => ⟨g s⟩

/-- Super-additive closure: the (max,plus)-dual of `subadditiveClosureE`. -/
noncomputable def superadditiveClosure
    (g : ℝ≥0 → WithBot ℝ≥0∞) : ℝ≥0 → WithBot ℝ≥0∞ :=
  fun t => (subadditiveClosure (toFmax g) t).toVal

/-- `toFmax` transports `superadditiveClosure` to `subadditiveClosure`. -/
theorem toFmax_superadditiveClosure
    (g : ℝ≥0 → WithBot ℝ≥0∞) :
    toFmax (superadditiveClosure g)
      = subadditiveClosure (toFmax g) := by
  funext t; apply MaxPlusNN.ext; rfl

/-- Super-additive closure lies above the original: `g t ≤ g⋆ t`. -/
theorem le_superadditiveClosure
    (g : ℝ≥0 → WithBot ℝ≥0∞) (t : ℝ≥0) :
    g t ≤ superadditiveClosure g t := by
  have h := convPow_le_closure (toFmax g) 1 t
  rw [convPow_one, MaxPlusNN.le_iff] at h
  exact h

/-- Idempotence of the super-additive closure. -/
theorem superadditiveClosure_idem
    (g : ℝ≥0 → WithBot ℝ≥0∞) :
    conv (subadditiveClosure (toFmax g))
        (subadditiveClosure (toFmax g))
      = subadditiveClosure (toFmax g) :=
  closure_idem (toFmax g)

/-- Super-additive closure is super-additive. -/
theorem superadditiveClosure_superadditive
    (g : ℝ≥0 → WithBot ℝ≥0∞) (u s : ℝ≥0) :
    superadditiveClosure g u + superadditiveClosure g s
      ≤ superadditiveClosure g (u + s) := by
  have h := closure_subadditive (toFmax g) u s
  rw [MaxPlusNN.le_iff] at h
  exact h

/-- `g` is super-additive: `g u + g s ≤ g (u + s)` on `WithBot ℝ≥0∞`. -/
def IsSuperadditiveW (g : ℝ≥0 → WithBot ℝ≥0∞) : Prop :=
  ∀ u s : ℝ≥0, g u + g s ≤ g (u + s)

/-- Super-additive `g` with `g 0 = 0` is convolution-idempotent. -/
theorem conv_toFmax_self (g : ℝ≥0 → WithBot ℝ≥0∞)
    (hsup : IsSuperadditiveW g) (h0 : g 0 = 0) :
    conv (toFmax g) (toFmax g) = toFmax g := by
  funext t
  apply MaxPlusNN.ext
  show ((conv (toFmax g) (toFmax g) t : MaxPlusNN)
      : WithBot ℝ≥0∞) = g t
  rw [conv_apply]
  apply le_antisymm
  · rw [← MaxPlusNN.le_iff]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, s, hus, rfl⟩
    rw [MaxPlusNN.le_iff]
    show g u + g s ≤ g t
    rw [← hus]; exact hsup u s
  · rw [← MaxPlusNN.le_iff]
    refine le_trans ?_
      (CompleteDioid.le_sSup _ _ ⟨0, t, zero_add t, rfl⟩)
    rw [MaxPlusNN.le_iff]
    show g t ≤ g 0 + g t
    rw [h0, zero_add]

/-- Super-additive `g` with `g 0 = 0` is its own super-additive closure. -/
theorem superadditiveClosure_eq_self
    (g : ℝ≥0 → WithBot ℝ≥0∞)
    (hsup : IsSuperadditiveW g) (h0 : g 0 = 0) :
    superadditiveClosure g = g := by
  have hidem := conv_toFmax_self g hsup h0
  have hunit : ∀ t,
      convUnit (T := MaxPlusNN) t ≼ₒ toFmax g t := by
    intro t
    rcases eq_or_ne t 0 with ht | ht
    · subst ht
      rw [convUnit, if_pos rfl, MaxPlusNN.le_iff]
      show (eₒ : MaxPlusNN).toVal ≤ (toFmax g 0).toVal
      show (eₒ : MaxPlusNN).toVal ≤ g 0
      rw [h0]
      show (eₒ : MaxPlusNN).toVal ≤ (0 : WithBot ℝ≥0∞)
      rfl
    · rw [convUnit, if_neg ht]; exact OrderBot.bot_le _
  have hself :=
    subadditiveClosure_eq_self (toFmax g) hidem hunit
  funext t
  show (subadditiveClosure (toFmax g) t).toVal = g t
  rw [hself]; rfl

end DeepWiki
