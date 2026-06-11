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

/-- `minConvPow g 1 = g`: the unit is neutral. -/
theorem minConvPow_one {D : Type} [_root_.AddCommMonoid D]
    (g : D → ℝ≥0∞) :
    minConvPow g 1 = g := by
  have h1 : minConvPow g 1 = minConv (minConvPow g 0) g := rfl
  rw [h1]
  funext t
  apply le_antisymm
  · refine le_trans (minConv_le_add _ _ (zero_add t)) ?_
    rw [minConvPow_zero, if_pos rfl, zero_add]
  · refine le_minConv fun u v huv => ?_
    rw [minConvPow_zero]
    by_cases hu : u = 0
    · rw [if_pos hu, zero_add]
      rw [hu, zero_add] at huv
      rw [huv]
    · rw [if_neg hu, top_add]
      exact le_top

/-- Convolution powers split across a convolution: `(f ∗ g)ⁿ = fⁿ ∗ gⁿ`
(commutativity and associativity reshuffle the factors). -/
theorem minConvPow_minConv {D : Type} [_root_.AddCommMonoid D]
    (f g : D → ℝ≥0∞) (n : ℕ) :
    minConvPow (minConv f g) n
      = minConv (minConvPow f n) (minConvPow g n) := by
  induction n with
  | zero =>
      funext t
      rw [minConvPow_zero]
      symm
      apply le_antisymm
      · refine le_trans (minConv_le_add _ _ (zero_add t)) ?_
        rw [minConvPow_zero, minConvPow_zero, if_pos rfl, zero_add]
      · refine le_minConv fun p q hpq => ?_
        rw [minConvPow_zero, minConvPow_zero]
        by_cases hp : p = 0
        · by_cases hq : q = 0
          · rw [if_pos hp, if_pos hq,
              if_pos (by rw [← hpq, hp, hq, add_zero]), add_zero]
          · rw [if_neg hq, add_top]
            exact le_top
        · rw [if_neg hp, top_add]
          exact le_top
  | succ n ih =>
      rw [minConvPow_succ, ih, minConvPow_succ, minConvPow_succ,
        minConv_assoc_enn,
        ← minConv_assoc_enn (minConvPow g n) f g,
        minConv_comm (minConvPow g n) f,
        minConv_assoc_enn f (minConvPow g n) g,
        ← minConv_assoc_enn (minConvPow f n) f
          (minConv (minConvPow g n) g)]

/-- Uniform lower bounds add up through convolution powers:
`n • c ≤ (minConvPow w n) t` when `c ≤ w` everywhere. -/
theorem nsmul_le_minConvPow {D : Type} [_root_.AddCommMonoid D]
    {w : D → ℝ≥0∞} {c : ℝ≥0∞} (hlb : ∀ s, c ≤ w s) (n : ℕ) (t : D) :
    n • c ≤ minConvPow w n t := by
  induction n generalizing t with
  | zero =>
      rw [zero_smul]
      exact zero_le'
  | succ n ih =>
      rw [minConvPow_succ]
      refine le_minConv fun u v huv => ?_
      rw [succ_nsmul]
      exact add_le_add (ih u) (hlb v)

/-- The `MinPlusNN` dioid power read back via `toVal` is `minConvPow`:
`((convPow (liftMinPlusNN g) n t : MinPlusNN) : ℝ≥0∞) = minConvPow g n t`. -/
theorem convPow_liftMinPlusNN_apply {D : Type} [_root_.AddCommMonoid D]
    (g : D → ℝ≥0∞) (n : ℕ) (t : D) :
    ((convPow (liftMinPlusNN g) n t : MinPlusNN) : ℝ≥0∞) = minConvPow g n t := by
  induction n generalizing t with
  | zero =>
      rw [show ((convPow (liftMinPlusNN g) 0 t : MinPlusNN) : ℝ≥0∞)
          = (convUnit (T := MinPlusNN) t).toVal from rfl,
        MinPlusNN.convUnit_toVal, minConvPow_zero]
  | succ n ih =>
      calc ((convPow (liftMinPlusNN g) (n + 1) t : MinPlusNN) : ℝ≥0∞)
          = minConv
              (fun u => ((convPow (liftMinPlusNN g) n u : MinPlusNN) : ℝ≥0∞)) g t :=
            conv_liftMinPlusNN_apply _ g t
        _ = minConv (minConvPow g n) g t := by simp only [ih]
        _ = minConvPow g (n + 1) t := rfl

/-- `convPow (liftMinPlusNN g) n = liftMinPlusNN (minConvPow g n)`: the dioid power of the lift
is the lift of the numeric power. -/
theorem convPow_liftMinPlusNN {D : Type} [_root_.AddCommMonoid D]
    (g : D → ℝ≥0∞) (n : ℕ) :
    convPow (liftMinPlusNN g) n = liftMinPlusNN (minConvPow g n) := by
  funext t
  apply MinPlusNN.ext
  exact convPow_liftMinPlusNN_apply g n t

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
noncomputable def subadditiveClosureENN {D : Type}
    [_root_.AddCommMonoid D]
    (g : D → ℝ≥0∞) : D → ℝ≥0∞ :=
  fun t => (subadditiveClosure (liftMinPlusNN g) t).toVal

/-- `subadditiveClosureENN g t` is the numeric infimum of the convolution
powers: `⨅ n, minConvPow g n t`. -/
theorem subadditiveClosureENN_eq_iInf {D : Type}
    [_root_.AddCommMonoid D] (g : D → ℝ≥0∞) (t : D) :
    subadditiveClosureENN g t
      = ⨅ n : ℕ, minConvPow g n t :=
  iInf_congr fun n => convPow_liftMinPlusNN_apply g n t

/-- `liftMinPlusNN` transports `subadditiveClosureENN` to `subadditiveClosure`. -/
theorem liftMinPlusNN_subadditiveClosureENN {D : Type}
    [_root_.AddCommMonoid D] (g : D → ℝ≥0∞) :
    liftMinPlusNN (subadditiveClosureENN g)
      = subadditiveClosure (liftMinPlusNN g) := by
  funext t; apply MinPlusNN.ext; rfl

/-- Closure lies below the original: `g⋆ t ≤ g t` (numeric). -/
theorem subadditiveClosureENN_le {D : Type}
    [_root_.AddCommMonoid D] (g : D → ℝ≥0∞)
    (t : D) : subadditiveClosureENN g t ≤ g t := by
  have h := convPow_le_closure (liftMinPlusNN g) 1 t
  rw [convPow_one, MinPlusNN.le_iff] at h
  exact h

/-- The closure vanishes at the origin: `g⋆ 0 = 0` (the zeroth power is
the convolution unit). -/
theorem subadditiveClosureENN_zero_eq {D : Type}
    [_root_.AddCommMonoid D] (g : D → ℝ≥0∞) :
    subadditiveClosureENN g 0 = 0 :=
  le_antisymm (by
    rw [subadditiveClosureENN_eq_iInf]
    exact iInf_le_of_le 0 (by rw [minConvPow_zero, if_pos rfl]))
    zero_le'

/-- Convolving with a closure stays below the curve: `(f ∗ g⋆) t ≤ f t`
(the closure vanishes at the origin). -/
theorem minConv_subadditiveClosureENN_le {D : Type}
    [_root_.AddCommMonoid D] (f g : D → ℝ≥0∞) (t : D) :
    minConv f (subadditiveClosureENN g) t ≤ f t :=
  (minConv_le_add f _ (add_zero t)).trans_eq
    (by rw [subadditiveClosureENN_zero_eq, add_zero])

/-- A curve lies below the closure iff it lies below every convolution
power: `y ≤ g⋆ ↔ ∀ n, y ≤ gⁿ`. -/
theorem le_subadditiveClosureENN_iff {D : Type}
    [_root_.AddCommMonoid D] {g y : D → ℝ≥0∞} :
    y ≤ subadditiveClosureENN g ↔ ∀ n, y ≤ minConvPow g n := by
  constructor
  · intro h n t
    refine (h t).trans ?_
    rw [subadditiveClosureENN_eq_iInf]
    exact iInf_le _ n
  · intro h t
    rw [subadditiveClosureENN_eq_iInf]
    exact le_iInf fun n => h n t

/-- Numeric closure is idempotent under `minConv`. -/
theorem subadditiveClosureENN_idem {D : Type}
    [_root_.AddCommMonoid D] (g : D → ℝ≥0∞) :
    minConv (subadditiveClosureENN g)
        (subadditiveClosureENN g)
      = subadditiveClosureENN g := by
  have h := closure_idem (liftMinPlusNN g)
  rw [← liftMinPlusNN_subadditiveClosureENN, conv_liftMinPlusNN] at h
  funext t
  exact congrArg MinPlusNN.toVal (congrFun h t)

/-- Numeric closure is sub-additive. -/
theorem subadditiveClosureENN_subadditive {D : Type}
    [_root_.AddCommMonoid D] (g : D → ℝ≥0∞) :
    IsSubadditive (subadditiveClosureENN g) := by
  intro u s
  have h := closure_subadditive (liftMinPlusNN g) u s
  rw [MinPlusNN.le_iff] at h
  calc subadditiveClosureENN g (u + s)
      = (subadditiveClosure (liftMinPlusNN g) (u + s)).toVal := rfl
    _ ≤ (subadditiveClosure (liftMinPlusNN g) u
          ⊗ₒ subadditiveClosure (liftMinPlusNN g) s).toVal := h
    _ = subadditiveClosureENN g u
          + subadditiveClosureENN g s := rfl

/-- The numeric closure of a monotone `ℝ≥0∞` curve is monotone: each
`minConvPow` power is. -/
theorem monotone_subadditiveClosureENN {g : ℝ≥0 → ℝ≥0∞}
    (hmono : Monotone g) : Monotone (subadditiveClosureENN g) := by
  intro a b hab
  rw [subadditiveClosureENN_eq_iInf, subadditiveClosureENN_eq_iInf]
  exact iInf_mono fun n => monotone_minConvPow hmono n hab

/-- Sub-additive `g` with `g 0 = 0` is its own closure. -/
theorem subadditiveClosureENN_eq_self {D : Type}
    [_root_.AddCommMonoid D] (g : D → ℝ≥0∞)
    (hsub : IsSubadditive g) (h0 : g 0 = 0) :
    subadditiveClosureENN g = g := by
  have hidem : conv (liftMinPlusNN g) (liftMinPlusNN g) = liftMinPlusNN g := by
    rw [conv_liftMinPlusNN, minConv_self_of_subadditive g hsub h0]
  have hunit : ∀ t,
      convUnit (T := MinPlusNN) t ≼ₒ liftMinPlusNN g t :=
    convUnit_le (by
      rw [MinPlusNN.le_iff]
      show (liftMinPlusNN g 0).toVal ≤ (eₒ : MinPlusNN).toVal
      simp [liftMinPlusNN, h0])
  have hself :=
    subadditiveClosure_eq_self (liftMinPlusNN g) hidem hunit
  funext t
  show (subadditiveClosure (liftMinPlusNN g) t).toVal = g t
  rw [hself]; rfl

/-- Numeric closure is monotone in `g`. -/
theorem subadditiveClosureENN_mono {D : Type}
    [_root_.AddCommMonoid D] (g h : D → ℝ≥0∞)
    (hgh : ∀ t, g t ≤ h t) (t : D) :
    subadditiveClosureENN g t ≤ subadditiveClosureENN h t := by
  show (subadditiveClosure (liftMinPlusNN g) t).toVal
      ≤ (subadditiveClosure (liftMinPlusNN h) t).toVal
  rw [← MinPlusNN.le_iff]
  refine subadditiveClosure_mono (liftMinPlusNN h) (liftMinPlusNN g) ?_ t
  intro r; rw [MinPlusNN.le_iff]; exact hgh r

/-- The numeric closure is the greatest sub-additive minorant: a
sub-additive `f` with `f 0 = 0` lying below `g` lies below
`subadditiveClosureENN g`. -/
theorem le_subadditiveClosureENN_of_isSubadditive {D : Type}
    [_root_.AddCommMonoid D] {f g : D → ℝ≥0∞}
    (hsub : IsSubadditive f) (h0 : f 0 = 0) (hfg : ∀ t, f t ≤ g t)
    (t : D) : f t ≤ subadditiveClosureENN g t :=
  calc f t = subadditiveClosureENN f t := by
        rw [subadditiveClosureENN_eq_self f hsub h0]
    _ ≤ subadditiveClosureENN g t := subadditiveClosureENN_mono f g hfg t

/-- Lift a `WithBot ℝ≥0∞`-valued function into `MaxPlusNN` pointwise. -/
def liftMaxPlusNN (g : ℝ≥0 → WithBot ℝ≥0∞) : Fmax :=
  fun s => ⟨g s⟩

/-- `conv` of `liftMaxPlusNN` lifts, read back via `toVal`, equals `maxConv`. -/
theorem conv_liftMaxPlusNN_apply
    (g h : ℝ≥0 → WithBot ℝ≥0∞) (t : ℝ≥0) :
    ((conv (liftMaxPlusNN g) (liftMaxPlusNN h) t : MaxPlusNN)
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

/-- `conv (liftMaxPlusNN g) (liftMaxPlusNN h) = liftMaxPlusNN (maxConv g h)`. -/
theorem conv_liftMaxPlusNN (g h : ℝ≥0 → WithBot ℝ≥0∞) :
    conv (liftMaxPlusNN g) (liftMaxPlusNN h) = liftMaxPlusNN (maxConv g h) := by
  funext t
  apply MaxPlusNN.ext
  exact conv_liftMaxPlusNN_apply g h t

/-- Super-additive closure: the (max,plus)-dual of `subadditiveClosureENN`. -/
noncomputable def superadditiveClosure
    (g : ℝ≥0 → WithBot ℝ≥0∞) : ℝ≥0 → WithBot ℝ≥0∞ :=
  fun t => (subadditiveClosure (liftMaxPlusNN g) t).toVal

/-- `liftMaxPlusNN` transports `superadditiveClosure` to `subadditiveClosure`. -/
theorem liftMaxPlusNN_superadditiveClosure
    (g : ℝ≥0 → WithBot ℝ≥0∞) :
    liftMaxPlusNN (superadditiveClosure g)
      = subadditiveClosure (liftMaxPlusNN g) := by
  funext t; apply MaxPlusNN.ext; rfl

/-- Super-additive closure lies above the original: `g t ≤ g⋆ t`. -/
theorem le_superadditiveClosure
    (g : ℝ≥0 → WithBot ℝ≥0∞) (t : ℝ≥0) :
    g t ≤ superadditiveClosure g t := by
  have h := convPow_le_closure (liftMaxPlusNN g) 1 t
  rw [convPow_one, MaxPlusNN.le_iff] at h
  exact h

/-- Idempotence of the super-additive closure. -/
theorem superadditiveClosure_idem
    (g : ℝ≥0 → WithBot ℝ≥0∞) :
    conv (subadditiveClosure (liftMaxPlusNN g))
        (subadditiveClosure (liftMaxPlusNN g))
      = subadditiveClosure (liftMaxPlusNN g) :=
  closure_idem (liftMaxPlusNN g)

/-- Super-additive closure is super-additive. -/
theorem superadditiveClosure_superadditive
    (g : ℝ≥0 → WithBot ℝ≥0∞) (u s : ℝ≥0) :
    superadditiveClosure g u + superadditiveClosure g s
      ≤ superadditiveClosure g (u + s) := by
  have h := closure_subadditive (liftMaxPlusNN g) u s
  rw [MaxPlusNN.le_iff] at h
  exact h

/-- Super-additive `g` with `g 0 = 0` is convolution-idempotent. -/
theorem conv_liftMaxPlusNN_self (g : ℝ≥0 → WithBot ℝ≥0∞)
    (hsup : IsSuperadditive g) (h0 : g 0 = 0) :
    conv (liftMaxPlusNN g) (liftMaxPlusNN g) = liftMaxPlusNN g := by
  rw [conv_liftMaxPlusNN, maxConv_self_of_superadditive g hsup h0]

/-- Super-additive `g` with `g 0 = 0` is its own super-additive closure. -/
theorem superadditiveClosure_eq_self
    (g : ℝ≥0 → WithBot ℝ≥0∞)
    (hsup : IsSuperadditive g) (h0 : g 0 = 0) :
    superadditiveClosure g = g := by
  have hidem := conv_liftMaxPlusNN_self g hsup h0
  have hunit : ∀ t,
      convUnit (T := MaxPlusNN) t ≼ₒ liftMaxPlusNN g t :=
    convUnit_le (by
      rw [MaxPlusNN.le_iff]
      show (eₒ : MaxPlusNN).toVal ≤ g 0
      rw [h0]; rfl)
  have hself :=
    subadditiveClosure_eq_self (liftMaxPlusNN g) hidem hunit
  funext t
  show (subadditiveClosure (liftMaxPlusNN g) t).toVal = g t
  rw [hself]; rfl

end DeepWiki
