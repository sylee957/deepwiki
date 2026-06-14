import Book.ClosuresNd
import Book.Additivity
import Book.FunctionDioids
import Mathlib.Data.EReal.Operations

/-! # Closure on `EReal` curves
The (min,+) sub-additive (Kleene-star) closure `⨅ₙ gⁿ` for curves
`g : ℝ≥0 → EReal`, built from raw `minConv`.  `EReal` is not a
`CompleteDioid` (its native `+` is bot-absorbing, the wrong convention),
so the good properties are gated on `IsNeverBot g` (never `−∞`). Also the
`EReal` specialization of `ndClosure`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- `g` is never `⊥ = −∞`: the restriction making `EReal` `+` behave. -/
def IsNeverBot (g : ℝ≥0 → EReal) : Prop := ∀ t, g t ≠ ⊥

/-- `g` is bounded below by a real constant: `∃ c : ℝ, ∀ t, (c : EReal) ≤ g t`.
Strengthens `IsNeverBot`; the property `minConv`/powers actually preserve. -/
def IsBddBelowReal (g : ℝ≥0 → EReal) : Prop := ∃ c : ℝ, ∀ t, (c : EReal) ≤ g t

/-- A nonnegative `EReal` value is not `⊥`. -/
theorem ne_bot_of_nonneg {x : EReal} (hx : 0 ≤ x) : x ≠ ⊥ :=
  (hx.trans_lt' EReal.bot_lt_zero).ne'

/-- `IsBddBelowReal g` implies `IsNeverBot g`. -/
theorem IsBddBelowReal.isNeverBot {g : ℝ≥0 → EReal} (hg : IsBddBelowReal g) :
    IsNeverBot g := by
  obtain ⟨c, hc⟩ := hg
  intro t hbot
  have := hc t
  rw [hbot, le_bot_iff] at this
  exact (EReal.coe_ne_bot c) this

/-- The (min,+) unit on `EReal`: `0` at the origin, `⊤ = +∞` elsewhere. -/
noncomputable def convUnitEReal : ℝ≥0 → EReal :=
  fun t => if t = 0 then 0 else ⊤

/-- For `IsNeverBot f`, the unit increment bound
`f (u + s) ≤ f u + convUnitEReal s`. -/
theorem IsNeverBot.increment_convUnitEReal {f : ℝ≥0 → EReal}
    (hf : IsNeverBot f) (u s : ℝ≥0) :
    f (u + s) ≤ f u + convUnitEReal s := by
  rcases eq_or_ne s 0 with hs | hs
  · subst hs
    rw [add_zero, convUnitEReal, if_pos rfl, add_zero]
  · rw [convUnitEReal, if_neg hs, EReal.add_top_of_ne_bot (hf u)]
    exact le_top

/-- `n`-fold (min,+) convolution power `gⁿ`; `g⁰ = convUnitEReal`. -/
noncomputable def convPowEReal (g : ℝ≥0 → EReal) : ℕ → (ℝ≥0 → EReal)
  | 0 => convUnitEReal
  | n + 1 => minConv (convPowEReal g n) g

/-- The (min,+) sub-additive closure `g⋆ t = ⨅ₙ gⁿ t` (numeric `iInf`). -/
noncomputable def subadditiveClosureEReal (g : ℝ≥0 → EReal) : ℝ≥0 → EReal :=
  fun t => ⨅ n : ℕ, convPowEReal g n t

/-- For `IsNeverBot g`, `convUnitEReal` is a left unit: `convUnitEReal ∗ g = g`. -/
theorem minConv_convUnitEReal_left (g : ℝ≥0 → EReal) (hg : IsNeverBot g) :
    minConv convUnitEReal g = g := by
  funext t
  apply le_antisymm
  · refine le_trans (minConv_le_add convUnitEReal g (zero_add t)) ?_
    rw [convUnitEReal, if_pos rfl, zero_add]
  · refine le_minConv fun u s hus => ?_
    rcases eq_or_ne u 0 with hu | hu
    · subst hu
      rw [convUnitEReal, if_pos rfl, zero_add]
      rw [zero_add] at hus; rw [hus]
    · rw [convUnitEReal, if_neg hu, EReal.top_add_of_ne_bot (hg s)]
      exact le_top

/-- For `IsNeverBot g`, the first power is `g` itself: `g¹ = g`. -/
theorem convPowEReal_one (g : ℝ≥0 → EReal) (hg : IsNeverBot g) :
    convPowEReal g 1 = g := by
  change minConv convUnitEReal g = g
  exact minConv_convUnitEReal_left g hg

/-- For `IsNeverBot g`, the closure lies below `g`: `g⋆ t ≤ g t` (numeric). -/
theorem subadditiveClosureEReal_le (g : ℝ≥0 → EReal) (hg : IsNeverBot g)
    (t : ℝ≥0) : subadditiveClosureEReal g t ≤ g t := by
  have h := iInf_le (fun n : ℕ => convPowEReal g n t) 1
  rwa [convPowEReal_one g hg] at h

/-- `convPowEReal` is monotone in `g` (pointwise, numeric). -/
theorem convPowEReal_mono (g h : ℝ≥0 → EReal)
    (hgh : ∀ t, g t ≤ h t) (n : ℕ) (t : ℝ≥0) :
    convPowEReal g n t ≤ convPowEReal h n t := by
  induction n generalizing t with
  | zero => exact le_refl _
  | succ k ih => exact minConv_le_minConv ih hgh t

/-- The closure is monotone in `g` (pointwise, numeric). -/
theorem subadditiveClosureEReal_mono (g h : ℝ≥0 → EReal)
    (hgh : ∀ t, g t ≤ h t) (t : ℝ≥0) :
    subadditiveClosureEReal g t ≤ subadditiveClosureEReal h t := by
  refine le_iInf ?_
  intro n
  exact le_trans (iInf_le _ n) (convPowEReal_mono g h hgh n t)

/-- `convUnitEReal` is bounded below by `0`. -/
theorem isBddBelowReal_convUnitEReal : IsBddBelowReal convUnitEReal := by
  refine ⟨0, fun t => ?_⟩
  rcases eq_or_ne t 0 with ht | ht
  · rw [convUnitEReal, if_pos ht]; exact le_rfl
  · rw [convUnitEReal, if_neg ht]; exact le_top

/-- `minConv` preserves a real lower bound: bound `c, d` gives bound `c + d`. -/
theorem coe_add_le_minConv {g h : ℝ≥0 → EReal} {c d : ℝ}
    (hc : ∀ t, (c : EReal) ≤ g t) (hd : ∀ t, (d : EReal) ≤ h t) (t : ℝ≥0) :
    ((c + d : ℝ) : EReal) ≤ minConv g h t :=
  le_minConv fun u s _ =>
    (EReal.coe_add c d).trans_le (add_le_add (hc u) (hd s))

/-- Every power `gⁿ` is bounded below by a real when `g` is. -/
theorem IsBddBelowReal.convPowEReal {g : ℝ≥0 → EReal}
    (hg : IsBddBelowReal g) (n : ℕ) : IsBddBelowReal (convPowEReal g n) := by
  induction n with
  | zero => exact isBddBelowReal_convUnitEReal
  | succ k ih =>
      obtain ⟨ck, hck⟩ := ih
      obtain ⟨c, hc⟩ := hg
      exact ⟨ck + c, fun t => coe_add_le_minConv hck hc t⟩

/-- `⨅ᵢ (a + f i) ≤ a + ⨅ᵢ f i` for `a ≠ ⊥` and `⨅ᵢ f i ≠ ⊥`.  The bot-
collision blocks full distribution, but this `≥`-direction holds and is all
sub-additivity needs. -/
theorem iInf_add_le_add_iInf {ι : Type*} [Nonempty ι] {a : EReal}
    (ha : a ≠ ⊥) {f : ι → EReal} (hbot : (⨅ i, f i) ≠ ⊥) :
    (⨅ i, a + f i) ≤ a + ⨅ i, f i := by
  induction a with
  | bot => exact absurd rfl ha
  | top =>
      rw [EReal.top_add_of_ne_bot hbot]
      exact le_top
  | coe a =>
      rw [add_comm]
      refine (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot a))
        (Or.inl (EReal.coe_ne_top a))).mp ?_
      refine le_iInf ?_
      intro i
      refine (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot a))
        (Or.inl (EReal.coe_ne_top a))).mpr ?_
      rw [add_comm]
      exact iInf_le _ i

/-- Intro with a leading constant, on `EReal`: `x ≤ a + minConv g h t` from the
per-split bounds `x ≤ a + (g u + h s)`, for `a ≠ ⊥` and a non-`⊥` convolution
(the constant pushes through the defining infimum). -/
theorem le_add_minConv_of_ne_bot {g h : ℝ≥0 → EReal} {a x : EReal} {t : ℝ≥0}
    (ha : a ≠ ⊥) (hbot : minConv g h t ≠ ⊥)
    (hle : ∀ u s, u + s = t → x ≤ a + (g u + h s)) :
    x ≤ a + minConv g h t :=
  le_trans
    (le_iInf fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
      hle p.1.1 p.1.2 p.2)
    (iInf_add_le_add_iInf ha hbot)

/-- Term bound `gᵐ⁺ⁿ (u+s) ≤ gᵐ u + gⁿ s`, the heart of sub-additivity.
Needs `IsBddBelowReal` so the `⊤ + (·)` / inner-`iInf` steps stay non-`⊥`. -/
theorem convPowEReal_term_le {g : ℝ≥0 → EReal} (hg : IsBddBelowReal g)
    (m n : ℕ) (u s : ℝ≥0) :
    convPowEReal g (m + n) (u + s)
      ≤ convPowEReal g m u + convPowEReal g n s := by
  induction n generalizing s with
  | zero =>
      rw [Nat.add_zero]
      exact (hg.convPowEReal m).isNeverBot.increment_convUnitEReal
        u s
  | succ k ih =>
      obtain ⟨ck, hck⟩ := hg.convPowEReal k
      obtain ⟨c, hc⟩ := id hg
      show convPowEReal g (m + k + 1) (u + s)
          ≤ convPowEReal g m u + minConv (convPowEReal g k) g s
      refine le_add_minConv_of_ne_bot
        ((hg.convPowEReal m).isNeverBot u)
        (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _)
          (coe_add_le_minConv hck hc s)) fun a b hab => ?_
      show minConv (convPowEReal g (m + k)) g (u + s) ≤ _
      refine le_trans (minConv_le_add (convPowEReal g (m + k)) g
        (show (u + a) + b = u + s by rw [add_assoc, hab])) ?_
      rw [← add_assoc]
      exact add_le_add (ih a) le_rfl

/-- `convUnitEReal` is non-negative. -/
theorem isNonneg_convUnitEReal : IsNonneg convUnitEReal := by
  intro t
  rcases eq_or_ne t 0 with ht | ht
  · rw [convUnitEReal, if_pos ht]
  · rw [convUnitEReal, if_neg ht]; exact le_top

/-- Every power `gⁿ` is non-negative when `g` is. -/
theorem convPowEReal_isNonneg {g : ℝ≥0 → EReal}
    (hg : IsNonneg g) (n : ℕ) : IsNonneg (convPowEReal g n) := by
  induction n with
  | zero => exact isNonneg_convUnitEReal
  | succ k ih => exact IsNonneg.conv ih hg

/-- A non-negative `g` is `IsBddBelowReal` (witness `0`). -/
theorem IsNonneg.isBddBelowReal {g : ℝ≥0 → EReal} (hg : IsNonneg g) :
    IsBddBelowReal g := ⟨0, fun t => by simpa using hg t⟩

/-- The closure of a non-negative `g` is non-negative. -/
theorem subadditiveClosureEReal_isNonneg {g : ℝ≥0 → EReal}
    (hg : IsNonneg g) : IsNonneg (subadditiveClosureEReal g) :=
  fun t => le_iInf (fun n => convPowEReal_isNonneg hg n t)

/-- The closure of a non-negative `g` is never `⊥`. -/
theorem subadditiveClosureEReal_isNeverBot {g : ℝ≥0 → EReal}
    (hg : IsNonneg g) : IsNeverBot (subadditiveClosureEReal g) :=
  fun t => ne_bot_of_nonneg (subadditiveClosureEReal_isNonneg hg t)

/-- For non-negative `g`, the closure is sub-additive:
`g⋆ (u+s) ≤ g⋆ u + g⋆ s`.  `IsNeverBot` alone is insufficient (the powers,
and the closure, can drop to `⊥`); non-negativity is the clean restriction
that keeps every value `≥ 0`, so the inner infima stay `≠ ⊥`. -/
theorem subadditiveClosureEReal_subadditive {g : ℝ≥0 → EReal}
    (hg : IsNonneg g) : IsSubadditive (subadditiveClosureEReal g) := by
  intro u s
  have hbdd := hg.isBddBelowReal
  have hCs : (⨅ n : ℕ, convPowEReal g n s) ≠ ⊥ :=
    subadditiveClosureEReal_isNeverBot hg s
  -- For each m, the closure at u+s is ≤ gᵐ u + closure s.
  have hrow : ∀ m : ℕ,
      subadditiveClosureEReal g (u + s)
        ≤ convPowEReal g m u + subadditiveClosureEReal g s := by
    intro m
    refine le_trans ?_
      (iInf_add_le_add_iInf
        (ne_bot_of_nonneg (convPowEReal_isNonneg hg m u))
        (f := fun n : ℕ => convPowEReal g n s) hCs)
    refine le_iInf (fun n => ?_)
    refine le_trans (iInf_le _ (m + n)) ?_
    exact convPowEReal_term_le hbdd m n u s
  -- Pull the closure-at-u out of the infimum over m.
  have hCu : (⨅ m : ℕ, convPowEReal g m u) ≠ ⊥ :=
    subadditiveClosureEReal_isNeverBot hg u
  calc subadditiveClosureEReal g (u + s)
      ≤ ⨅ m : ℕ, convPowEReal g m u + subadditiveClosureEReal g s :=
        le_iInf hrow
    _ = ⨅ m : ℕ, subadditiveClosureEReal g s + convPowEReal g m u := by
        simp_rw [add_comm]
    _ ≤ subadditiveClosureEReal g s + ⨅ m : ℕ, convPowEReal g m u := by
        exact iInf_add_le_add_iInf (f := fun m : ℕ => convPowEReal g m u)
          hCs hCu
    _ = subadditiveClosureEReal g u + subadditiveClosureEReal g s :=
        add_comm _ _

/-- Under `IsNeverBot`, a subadditive `g` with `g 0 = 0` collapses every power
to `g`: `gⁿ = g` for `n ≥ 1`. -/
theorem convPowEReal_succ_of_subadditive (g : ℝ≥0 → EReal)
    (hg : IsNeverBot g) (hsub : IsSubadditive g) (h0 : g 0 = 0) (n : ℕ) :
    convPowEReal g (n + 1) = g := by
  induction n with
  | zero => exact convPowEReal_one g hg
  | succ k ih =>
      show minConv (convPowEReal g (k + 1)) g = g
      rw [ih, minConv_self_of_subadditive g hsub h0]

/-- Under `IsNeverBot`, a subadditive `g` with `g 0 = 0` is its own closure. -/
theorem subadditiveClosureEReal_eq_self (g : ℝ≥0 → EReal)
    (hg : IsNeverBot g) (hsub : IsSubadditive g) (h0 : g 0 = 0) :
    subadditiveClosureEReal g = g := by
  funext t
  apply le_antisymm
  · exact subadditiveClosureEReal_le g hg t
  · refine le_iInf ?_
    intro n
    cases n with
    | zero =>
        show g t ≤ convUnitEReal t
        rcases eq_or_ne t 0 with ht | ht
        · subst ht; rw [convUnitEReal, if_pos rfl, h0]
        · rw [convUnitEReal, if_neg ht]; exact le_top
    | succ k =>
        rw [convPowEReal_succ_of_subadditive g hg hsub h0]

/-- The closure vanishes at the origin: `g⋆ 0 = 0` (the zeroth power is the
unit, `0` at the origin), for non-negative `g`. -/
theorem subadditiveClosureEReal_zero_eq {g : ℝ≥0 → EReal} (hg : IsNonneg g) :
    subadditiveClosureEReal g 0 = 0 := by
  refine le_antisymm ?_ (subadditiveClosureEReal_isNonneg hg 0)
  refine le_trans (iInf_le (fun n : ℕ => convPowEReal g n 0) 0) (le_of_eq ?_)
  show convUnitEReal 0 = 0
  rw [convUnitEReal, if_pos rfl]

/-- The `(min,+)` convolution of two sub-additive non-negative `EReal` curves is
sub-additive (non-negativity keeps the values `≠ ⊥`, so `EReal` `+` behaves). -/
theorem isSubadditive_minConv_ereal {f g : ℝ≥0 → EReal}
    (hf : IsSubadditive f) (hg : IsSubadditive g)
    (hfn : IsNonneg f) (hgn : IsNonneg g) :
    IsSubadditive (minConv f g) := by
  have hconv : IsNonneg (minConv f g) := hfn.conv hgn
  intro aa bb
  refine le_add_minConv_of_ne_bot (ne_bot_of_nonneg (hconv aa))
    (ne_bot_of_nonneg (hconv bb)) fun v w hvw => ?_
  rw [add_comm (minConv f g aa) (f v + g w)]
  refine le_add_minConv_of_ne_bot (ne_bot_of_nonneg (add_nonneg (hfn v) (hgn w)))
    (ne_bot_of_nonneg (hconv aa)) fun u s hus => ?_
  calc minConv f g (aa + bb)
      ≤ f (u + v) + g (s + w) :=
        minConv_le_add f g (by rw [← hus, ← hvw]; exact add_add_add_comm u v s w)
    _ ≤ (f u + f v) + (g s + g w) := add_le_add (hf u v) (hg s w)
    _ = (f u + g s) + (f v + g w) := add_add_add_comm _ _ _ _
    _ = (f v + g w) + (f u + g s) := add_comm _ _

/-- The greatest sub-additive minorant property on `EReal`: a sub-additive
never-`⊥` `f` with `f 0 = 0` lying below `g` lies below `g⋆`. -/
theorem le_subadditiveClosureEReal_of_isSubadditive {f g : ℝ≥0 → EReal}
    (hsub : IsSubadditive f) (hnb : IsNeverBot f) (h0 : f 0 = 0)
    (hfg : ∀ t, f t ≤ g t) (t : ℝ≥0) :
    f t ≤ subadditiveClosureEReal g t :=
  calc f t = subadditiveClosureEReal f t :=
        (congrFun (subadditiveClosureEReal_eq_self f hnb hsub h0) t).symm
    _ ≤ subadditiveClosureEReal g t := subadditiveClosureEReal_mono f g hfg t

/-- **Star of a meet on `EReal`**: for non-negative `σ`, `τ`, the closure of
their pointwise minimum is the convolution of the closures,
`(σ ⊓ τ)⋆ = σ⋆ ∗ τ⋆` — the `EReal` (min,+) Kleene-star-of-meet identity. -/
theorem subadditiveClosureEReal_min {σ τ : ℝ≥0 → EReal}
    (hσ : IsNonneg σ) (hτ : IsNonneg τ) :
    subadditiveClosureEReal (fun t => min (σ t) (τ t))
      = minConv (subadditiveClosureEReal σ) (subadditiveClosureEReal τ) := by
  have hinf : IsNonneg (fun t => min (σ t) (τ t)) := fun t => le_min (hσ t) (hτ t)
  funext t
  apply le_antisymm
  · refine le_minConv fun u s hus => ?_
    subst hus
    calc subadditiveClosureEReal (fun t => min (σ t) (τ t)) (u + s)
        ≤ subadditiveClosureEReal (fun t => min (σ t) (τ t)) u
            + subadditiveClosureEReal (fun t => min (σ t) (τ t)) s :=
          subadditiveClosureEReal_subadditive hinf u s
      _ ≤ subadditiveClosureEReal σ u + subadditiveClosureEReal τ s :=
          add_le_add
            (subadditiveClosureEReal_mono _ σ (fun _ => min_le_left _ _) u)
            (subadditiveClosureEReal_mono _ τ (fun _ => min_le_right _ _) s)
  · have h0σ : subadditiveClosureEReal σ 0 = 0 := subadditiveClosureEReal_zero_eq hσ
    have h0τ : subadditiveClosureEReal τ 0 = 0 := subadditiveClosureEReal_zero_eq hτ
    refine le_subadditiveClosureEReal_of_isSubadditive
      (isSubadditive_minConv_ereal
        (subadditiveClosureEReal_subadditive hσ) (subadditiveClosureEReal_subadditive hτ)
        (subadditiveClosureEReal_isNonneg hσ) (subadditiveClosureEReal_isNonneg hτ))
      (fun r => ne_bot_of_nonneg
        (IsNonneg.conv (subadditiveClosureEReal_isNonneg hσ)
          (subadditiveClosureEReal_isNonneg hτ) r))
      (by rw [minConv_apply_zero, h0σ, h0τ, add_zero]) (fun r => le_min
        ((minConv_le_left _ h0τ r).trans
          (subadditiveClosureEReal_le σ (fun t => ne_bot_of_nonneg (hσ t)) r))
        ((minConv_le_right h0σ _ r).trans
          (subadditiveClosureEReal_le τ (fun t => ne_bot_of_nonneg (hτ t)) r))) t

/-! ## Non-decreasing closure over `EReal` -/

/-- Over `EReal` every `f` satisfies `ClosureBddAbove`. -/
theorem ndClosure_ereal_bdd (f : ℝ≥0 → EReal) : ClosureBddAbove f :=
  fun _ => OrderTop.bddAbove _

/-- `le_ndClosure` specialized to `EReal`: the closure dominates `f`. -/
theorem le_ndClosure_ereal (f : ℝ≥0 → EReal) (t : ℝ≥0) :
    f t ≤ ndClosure f t :=
  le_ndClosure f (ndClosure_ereal_bdd f) t

/-- `ndClosure_mono` specialized to `EReal`: the closure is non-decreasing. -/
theorem monotone_ndClosure_ereal (f : ℝ≥0 → EReal) :
    Monotone (ndClosure f) :=
  fun _ _ hxy => ndClosure_mono f (ndClosure_ereal_bdd f) hxy

/-- `ndClosure_le` specialized to `EReal`: the closure is the least
non-decreasing majorant. -/
theorem ndClosure_ereal_le {f g : ℝ≥0 → EReal} (hg : Monotone g)
    (hfg : ∀ t, f t ≤ g t) (t : ℝ≥0) :
    ndClosure f t ≤ g t :=
  ndClosure_le hg hfg t

/-! ## Convolution distributes over a finite `inf'` -/

/-- `+ y` distributes through a finite `inf'` over `EReal` (`+ y` is monotone and the inf is
attained). -/
theorem inf'_add_ereal {κ : Type*} {s : Finset κ} (hne : s.Nonempty) (x : κ → EReal) (y : EReal) :
    s.inf' hne x + y = s.inf' hne (fun j => x j + y) := by
  obtain ⟨j₀, hj₀, hxj₀⟩ := Finset.exists_mem_eq_inf' hne x
  refine le_antisymm (Finset.le_inf' _ _ (fun j hj => ?_)) ?_
  · gcongr
    exact Finset.inf'_le _ hj
  · calc s.inf' hne (fun j => x j + y) ≤ x j₀ + y := Finset.inf'_le _ hj₀
      _ = s.inf' hne x + y := by rw [hxj₀]

/-- **Min-plus convolution distributes over a finite `inf'` of arrivals**:
`(⨅ⱼ fⱼ) ∗ g = ⨅ⱼ (fⱼ ∗ g)`. The keystone that turns the inf-staircase arrival's convolution
into a finite inf of single-step convolutions (each piecewise-continuous). -/
theorem minConv_finset_inf' {κ : Type*} {s : Finset κ} (hne : s.Nonempty)
    (f : κ → ℝ≥0 → EReal) (g : ℝ≥0 → EReal) (t : ℝ≥0) :
    minConv (fun u => s.inf' hne (fun j => f j u)) g t
      = s.inf' hne (fun j => minConv (f j) g t) := by
  simp only [minConv, inf'_add_ereal]
  exact le_antisymm
    (Finset.le_inf' _ _ (fun j hj => le_iInf (fun p => (iInf_le _ p).trans (Finset.inf'_le _ hj))))
    (le_iInf (fun p => Finset.le_inf' _ _ (fun j hj => (Finset.inf'_le _ hj).trans (iInf_le _ p))))

end DeepWiki
