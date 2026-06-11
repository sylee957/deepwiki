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

/-- `n`-fold (min,+) convolution power on numeric `ℝ≥0∞` values; `g⁰` is the
unit (`0` at the origin, `⊤` elsewhere). -/
noncomputable def minConvPow {D : Type}
    [_root_.AddCommMonoid D]
    (g : D → ℝ≥0∞) : ℕ → (D → ℝ≥0∞)
  | 0 => fun t => if t = 0 then 0 else ⊤
  | n + 1 => minConv (minConvPow g n) g

/-- `minConvPow g 0 t` is `0` at the origin and `⊤` elsewhere. -/
theorem minConvPow_zero {D : Type} [_root_.AddCommMonoid D]
    (g : D → ℝ≥0∞) (t : D) :
    minConvPow g 0 t = if t = 0 then 0 else ⊤ := rfl

/-- `minConvPow g (n + 1) = minConv (minConvPow g n) g`. -/
theorem minConvPow_succ {D : Type} [_root_.AddCommMonoid D]
    (g : D → ℝ≥0∞) (n : ℕ) :
    minConvPow g (n + 1) = minConv (minConvPow g n) g := rfl

/-- The `MinPlusNN` dioid power read back via `toVal` is `minConvPow`:
`((convPow (toF g) n t : MinPlusNN) : ℝ≥0∞) = minConvPow g n t`. -/
theorem convPow_toF_apply {D : Type} [_root_.AddCommMonoid D]
    (g : D → ℝ≥0∞) (n : ℕ) (t : D) :
    ((convPow (toF g) n t : MinPlusNN) : ℝ≥0∞) = minConvPow g n t := by
  induction n generalizing t with
  | zero =>
      rw [show ((convPow (toF g) 0 t : MinPlusNN) : ℝ≥0∞)
          = (convUnit (T := MinPlusNN) t).toVal from rfl,
        MinPlusNN.convUnit_toVal, minConvPow_zero]
  | succ n ih =>
      calc ((convPow (toF g) (n + 1) t : MinPlusNN) : ℝ≥0∞)
          = minConv
              (fun u => ((convPow (toF g) n u : MinPlusNN) : ℝ≥0∞)) g t :=
            conv_toF_apply _ g t
        _ = minConv (minConvPow g n) g t := by simp only [ih]
        _ = minConvPow g (n + 1) t := rfl

/-- `convPow (toF g) n = toF (minConvPow g n)`: the dioid power of the lift
is the lift of the numeric power. -/
theorem convPow_toF {D : Type} [_root_.AddCommMonoid D]
    (g : D → ℝ≥0∞) (n : ℕ) :
    convPow (toF g) n = toF (minConvPow g n) := by
  funext t
  apply MinPlusNN.ext
  exact convPow_toF_apply g n t

/-- Each (min,+) power of a monotone `ℝ≥0∞` curve is monotone: the unit power
is monotone and `minConv` preserves monotonicity. -/
theorem monotone_minConvPow {g : ℝ≥0 → ℝ≥0∞} (hmono : Monotone g)
    (n : ℕ) : Monotone (minConvPow g n) := by
  induction n with
  | zero =>
      intro a b hab
      rw [minConvPow_zero, minConvPow_zero]
      split_ifs with ha hb hb
      · exact le_rfl
      · exact le_top
      · exact absurd (le_antisymm (hb ▸ hab) zero_le') ha
      · exact le_rfl
  | succ n ih => exact monotone_minConv ih hmono

/-- Closure on numeric `ℝ≥0∞` values via the `MinPlusNN` carrier. -/
noncomputable def subadditiveClosureE {D : Type}
    [_root_.AddCommMonoid D]
    (g : D → ℝ≥0∞) : D → ℝ≥0∞ :=
  fun t => (subadditiveClosure (toF g) t).toVal

/-- `subadditiveClosureE g t` is the numeric infimum of the convolution
powers: `⨅ n, minConvPow g n t`. -/
theorem subadditiveClosureE_eq_iInf {D : Type}
    [_root_.AddCommMonoid D] (g : D → ℝ≥0∞) (t : D) :
    subadditiveClosureE g t
      = ⨅ n : ℕ, minConvPow g n t :=
  iInf_congr fun n => convPow_toF_apply g n t

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

/-- The numeric closure of a monotone `ℝ≥0∞` curve is monotone: each
`minConvPow` power is. -/
theorem monotone_subadditiveClosureE {g : ℝ≥0 → ℝ≥0∞}
    (hmono : Monotone g) : Monotone (subadditiveClosureE g) := by
  intro a b hab
  rw [subadditiveClosureE_eq_iInf, subadditiveClosureE_eq_iInf]
  exact iInf_mono fun n => monotone_minConvPow hmono n hab

/-- Sub-additive `g` with `g 0 = 0` is its own closure. -/
theorem subadditiveClosureE_eq_self {D : Type}
    [_root_.AddCommMonoid D] (g : D → ℝ≥0∞)
    (hsub : IsSubadditive g) (h0 : g 0 = 0) :
    subadditiveClosureE g = g := by
  have hidem : conv (toF g) (toF g) = toF g := by
    rw [conv_toF, minConv_self_of_subadditive g hsub h0]
  have hunit : ∀ t,
      convUnit (T := MinPlusNN) t ≼ₒ toF g t :=
    convUnit_le (by
      rw [MinPlusNN.le_iff]
      show (toF g 0).toVal ≤ (eₒ : MinPlusNN).toVal
      simp [toF, h0])
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

/-- `conv` of `toFmax` lifts, read back via `toVal`, equals `maxConv`. -/
theorem conv_toFmax_apply
    (g h : ℝ≥0 → WithBot ℝ≥0∞) (t : ℝ≥0) :
    ((conv (toFmax g) (toFmax h) t : MaxPlusNN)
        : WithBot ℝ≥0∞)
      = maxConv g h t := by
  rw [conv_apply, MaxPlusNN.toVal_sSup]
  apply le_antisymm
  · refine iSup_le (fun x => ?_)
    obtain ⟨u, s, hus, hx⟩ := x.2
    rw [hx]
    exact le_iSup_of_le ⟨(u, s), hus⟩ le_rfl
  · refine iSup_le (fun p => ?_)
    exact le_iSup_of_le ⟨_, p.1.1, p.1.2, p.2, rfl⟩ le_rfl

/-- `conv (toFmax g) (toFmax h) = toFmax (maxConv g h)`. -/
theorem conv_toFmax (g h : ℝ≥0 → WithBot ℝ≥0∞) :
    conv (toFmax g) (toFmax h) = toFmax (maxConv g h) := by
  funext t
  apply MaxPlusNN.ext
  exact conv_toFmax_apply g h t

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

/-- Super-additive `g` with `g 0 = 0` is convolution-idempotent. -/
theorem conv_toFmax_self (g : ℝ≥0 → WithBot ℝ≥0∞)
    (hsup : IsSuperadditive g) (h0 : g 0 = 0) :
    conv (toFmax g) (toFmax g) = toFmax g := by
  rw [conv_toFmax, maxConv_self_of_superadditive g hsup h0]

/-- Super-additive `g` with `g 0 = 0` is its own super-additive closure. -/
theorem superadditiveClosure_eq_self
    (g : ℝ≥0 → WithBot ℝ≥0∞)
    (hsup : IsSuperadditive g) (h0 : g 0 = 0) :
    superadditiveClosure g = g := by
  have hidem := conv_toFmax_self g hsup h0
  have hunit : ∀ t,
      convUnit (T := MaxPlusNN) t ≼ₒ toFmax g t :=
    convUnit_le (by
      rw [MaxPlusNN.le_iff]
      show (eₒ : MaxPlusNN).toVal ≤ g 0
      rw [h0]; rfl)
  have hself :=
    subadditiveClosure_eq_self (toFmax g) hidem hunit
  funext t
  show (subadditiveClosure (toFmax g) t).toVal = g t
  rw [hself]; rfl

end DeepWiki
