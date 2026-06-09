import Book.ConvolutionMinimum
import Book.NdClosure
import Book.ConvolutionMinimumExt
import Book.Additivity
import Book.FunctionDioids
import Mathlib.Data.EReal.Operations

/-! # Closure on `EReal` curves
The (min,+) sub-additive (Kleene-star) closure `⨅ₙ gⁿ` for curves
`g : ℝ≥0 → EReal`, built from raw `minConv`.  `EReal` is not a
`CompleteDioid` (its native `+` is bot-absorbing, the wrong convention),
so the good properties are gated on `NeverBot g` (never `−∞`). Also the
`EReal` specializations of `minConv` monotonicity and `ndClosure`. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- `g` is never `⊥ = −∞`: the restriction making `EReal` `+` behave. -/
def NeverBot (g : ℝ≥0 → EReal) : Prop := ∀ t, g t ≠ ⊥

/-- `g` is bounded below by a real constant: `∃ c : ℝ, ∀ t, (c : EReal) ≤ g t`.
Strengthens `NeverBot`; the property `minConv`/powers actually preserve. -/
def BddBelowReal (g : ℝ≥0 → EReal) : Prop := ∃ c : ℝ, ∀ t, (c : EReal) ≤ g t

/-- A nonnegative `EReal` value is not `⊥`. -/
theorem ne_bot_of_nonneg {x : EReal} (hx : 0 ≤ x) : x ≠ ⊥ :=
  (hx.trans_lt' EReal.bot_lt_zero).ne'

/-- `BddBelowReal g` implies `NeverBot g`. -/
theorem BddBelowReal.neverBot {g : ℝ≥0 → EReal} (hg : BddBelowReal g) :
    NeverBot g := by
  obtain ⟨c, hc⟩ := hg
  intro t hbot
  have := hc t
  rw [hbot, le_bot_iff] at this
  exact (EReal.coe_ne_bot c) this

/-- The (min,+) unit on `EReal`: `0` at the origin, `⊤ = +∞` elsewhere. -/
noncomputable def convUnitEReal : ℝ≥0 → EReal :=
  fun t => if t = 0 then 0 else ⊤

/-- `n`-fold (min,+) convolution power `gⁿ`; `g⁰ = convUnitEReal`. -/
noncomputable def convPowEReal (g : ℝ≥0 → EReal) : ℕ → (ℝ≥0 → EReal)
  | 0 => convUnitEReal
  | n + 1 => minConv (convPowEReal g n) g

/-- The (min,+) sub-additive closure `g⋆ t = ⨅ₙ gⁿ t` (numeric `iInf`). -/
noncomputable def subadditiveClosureEReal (g : ℝ≥0 → EReal) : ℝ≥0 → EReal :=
  fun t => ⨅ n : ℕ, convPowEReal g n t

/-- For `NeverBot g`, `convUnitEReal` is a left unit: `convUnitEReal ∗ g = g`. -/
theorem minConv_convUnitEReal_left (g : ℝ≥0 → EReal) (hg : NeverBot g) :
    minConv convUnitEReal g = g := by
  funext t
  unfold minConv
  apply le_antisymm
  · refine iInf_le_of_le ⟨(0, t), by simp⟩ ?_
    show convUnitEReal 0 + g t ≤ g t
    rw [convUnitEReal, if_pos rfl, zero_add]
  · refine le_iInf ?_
    rintro ⟨⟨u, s⟩, (hus : u + s = t)⟩
    show g t ≤ convUnitEReal u + g s
    rcases eq_or_ne u 0 with hu | hu
    · subst hu
      rw [convUnitEReal, if_pos rfl, zero_add]
      rw [zero_add] at hus; rw [hus]
    · rw [convUnitEReal, if_neg hu, EReal.top_add_of_ne_bot (hg s)]
      exact le_top

/-- For `NeverBot g`, the first power is `g` itself: `g¹ = g`. -/
theorem convPowEReal_one (g : ℝ≥0 → EReal) (hg : NeverBot g) :
    convPowEReal g 1 = g := by
  change minConv convUnitEReal g = g
  exact minConv_convUnitEReal_left g hg

/-- For `NeverBot g`, the closure lies below `g`: `g⋆ t ≤ g t` (numeric). -/
theorem subadditiveClosureEReal_le (g : ℝ≥0 → EReal) (hg : NeverBot g)
    (t : ℝ≥0) : subadditiveClosureEReal g t ≤ g t := by
  have h := iInf_le (fun n : ℕ => convPowEReal g n t) 1
  rwa [convPowEReal_one g hg] at h

/-- `minConv` is monotone in both arguments (pointwise). -/
theorem minConv_le_minConv {g g' h h' : ℝ≥0 → EReal}
    (hg : ∀ t, g t ≤ g' t) (hh : ∀ t, h t ≤ h' t) (t : ℝ≥0) :
    minConv g h t ≤ minConv g' h' t := by
  unfold minConv
  refine le_iInf ?_
  rintro ⟨⟨u, s⟩, (hus : u + s = t)⟩
  refine iInf_le_of_le ⟨(u, s), hus⟩ ?_
  exact add_le_add (hg u) (hh s)

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
theorem bddBelowReal_convUnitEReal : BddBelowReal convUnitEReal := by
  refine ⟨0, fun t => ?_⟩
  rcases eq_or_ne t 0 with ht | ht
  · rw [convUnitEReal, if_pos ht]; exact le_rfl
  · rw [convUnitEReal, if_neg ht]; exact le_top

/-- `minConv` preserves a real lower bound: bound `c, d` gives bound `c + d`. -/
theorem minConv_bddBelowReal {g h : ℝ≥0 → EReal} {c d : ℝ}
    (hc : ∀ t, (c : EReal) ≤ g t) (hd : ∀ t, (d : EReal) ≤ h t) (t : ℝ≥0) :
    ((c + d : ℝ) : EReal) ≤ minConv g h t := by
  unfold minConv
  refine le_iInf ?_
  rintro ⟨⟨u, s⟩, _⟩
  rw [EReal.coe_add]
  exact add_le_add (hc u) (hd s)

/-- Every power `gⁿ` is bounded below by a real when `g` is. -/
theorem convPowEReal_bddBelowReal {g : ℝ≥0 → EReal}
    (hg : BddBelowReal g) (n : ℕ) : BddBelowReal (convPowEReal g n) := by
  induction n with
  | zero => exact bddBelowReal_convUnitEReal
  | succ k ih =>
      obtain ⟨ck, hck⟩ := ih
      obtain ⟨c, hc⟩ := hg
      exact ⟨ck + c, fun t => minConv_bddBelowReal hck hc t⟩

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

/-- Term bound `gᵐ⁺ⁿ (u+s) ≤ gᵐ u + gⁿ s`, the heart of sub-additivity.
Needs `BddBelowReal` so the `⊤ + (·)` / inner-`iInf` steps stay non-`⊥`. -/
theorem convPowEReal_term_le {g : ℝ≥0 → EReal} (hg : BddBelowReal g)
    (m n : ℕ) (u s : ℝ≥0) :
    convPowEReal g (m + n) (u + s)
      ≤ convPowEReal g m u + convPowEReal g n s := by
  induction n generalizing s with
  | zero =>
      rw [Nat.add_zero]
      rcases eq_or_ne s 0 with hs | hs
      · subst hs
        rw [add_zero]
        show convPowEReal g m u ≤ convPowEReal g m u + convUnitEReal 0
        rw [convUnitEReal, if_pos rfl, add_zero]
      · show convPowEReal g m (u + s)
            ≤ convPowEReal g m u + convUnitEReal s
        rw [convUnitEReal, if_neg hs,
          EReal.add_top_of_ne_bot
            ((convPowEReal_bddBelowReal hg m).neverBot u)]
        exact le_top
  | succ k ih =>
      obtain ⟨ck, hck⟩ := convPowEReal_bddBelowReal hg k
      obtain ⟨c, hc⟩ := id hg
      show convPowEReal g (m + k + 1) (u + s)
          ≤ convPowEReal g m u + minConv (convPowEReal g k) g s
      have hstep :
          convPowEReal g m u
              + minConv (convPowEReal g k) g s
            ≥ ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = s},
                convPowEReal g m u
                  + (convPowEReal g k p.1.1 + g p.1.2) := by
        refine iInf_add_le_add_iInf
          ((convPowEReal_bddBelowReal hg m).neverBot u)
          (f := fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = s} =>
            convPowEReal g k p.1.1 + g p.1.2) ?_
        have hd : ((ck + c : ℝ) : EReal)
            ≤ ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = s},
                convPowEReal g k p.1.1 + g p.1.2 := by
          refine le_iInf (fun p => ?_)
          rw [EReal.coe_add]; exact add_le_add (hck _) (hc _)
        exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hd
      refine le_trans ?_ hstep
      show minConv (convPowEReal g (m + k)) g (u + s)
          ≤ _
      unfold minConv
      refine le_iInf ?_
      rintro ⟨⟨a, b⟩, (hab : a + b = s)⟩
      simp only
      refine iInf_le_of_le
        ⟨(u + a, b), show (u + a) + b = u + s by rw [add_assoc, hab]⟩ ?_
      show convPowEReal g (m + k) (u + a) + g b
          ≤ convPowEReal g m u + (convPowEReal g k a + g b)
      rw [← add_assoc]
      exact add_le_add (ih a) le_rfl

/-- `convUnitEReal` is non-negative. -/
theorem isNonneg_convUnitEReal : IsNonneg convUnitEReal := by
  intro t
  rcases eq_or_ne t 0 with ht | ht
  · rw [convUnitEReal, if_pos ht]
  · rw [convUnitEReal, if_neg ht]; exact le_top

/-- `minConv` preserves non-negativity. -/
theorem minConv_isNonneg {g h : ℝ≥0 → EReal}
    (hg : IsNonneg g) (hh : IsNonneg h) : IsNonneg (minConv g h) := by
  intro t
  unfold minConv
  refine le_iInf ?_
  rintro ⟨⟨u, s⟩, _⟩
  calc (0 : EReal) = 0 + 0 := by simp
    _ ≤ g u + h s := add_le_add (hg u) (hh s)

/-- Every power `gⁿ` is non-negative when `g` is. -/
theorem convPowEReal_isNonneg {g : ℝ≥0 → EReal}
    (hg : IsNonneg g) (n : ℕ) : IsNonneg (convPowEReal g n) := by
  induction n with
  | zero => exact isNonneg_convUnitEReal
  | succ k ih => exact minConv_isNonneg ih hg

/-- A non-negative `g` is `BddBelowReal` (witness `0`). -/
theorem IsNonneg.bddBelowReal {g : ℝ≥0 → EReal} (hg : IsNonneg g) :
    BddBelowReal g := ⟨0, fun t => by simpa using hg t⟩

/-- The closure of a non-negative `g` is non-negative (hence `≠ ⊥`). -/
theorem subadditiveClosureEReal_isNonneg {g : ℝ≥0 → EReal}
    (hg : IsNonneg g) : IsNonneg (subadditiveClosureEReal g) :=
  fun t => le_iInf (fun n => convPowEReal_isNonneg hg n t)

/-- For non-negative `g`, the closure is sub-additive:
`g⋆ (u+s) ≤ g⋆ u + g⋆ s`.  `NeverBot` alone is insufficient (the powers,
and the closure, can drop to `⊥`); non-negativity is the clean restriction
that keeps every value `≥ 0`, so the inner infima stay `≠ ⊥`. -/
theorem subadditiveClosureEReal_subadditive {g : ℝ≥0 → EReal}
    (hg : IsNonneg g) : IsSubadditive (subadditiveClosureEReal g) := by
  intro u s
  have hbdd := hg.bddBelowReal
  have hCs : (⨅ n : ℕ, convPowEReal g n s) ≠ ⊥ :=
    ne_bot_of_nonneg (le_iInf (fun n => convPowEReal_isNonneg hg n s))
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
    ne_bot_of_nonneg (le_iInf (fun n => convPowEReal_isNonneg hg n u))
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

/-- Under `NeverBot`, a subadditive `g` with `g 0 = 0` collapses every power
to `g`: `gⁿ = g` for `n ≥ 1`. -/
theorem convPowEReal_succ_of_subadditive (g : ℝ≥0 → EReal)
    (hg : NeverBot g) (hsub : IsSubadditive g) (h0 : g 0 = 0) (n : ℕ) :
    convPowEReal g (n + 1) = g := by
  induction n with
  | zero => exact convPowEReal_one g hg
  | succ k ih =>
      show minConv (convPowEReal g (k + 1)) g = g
      rw [ih, minConvE_self_of_subadditive g hsub h0]

/-- Under `NeverBot`, a subadditive `g` with `g 0 = 0` is its own closure. -/
theorem subadditiveClosureEReal_eq_self (g : ℝ≥0 → EReal)
    (hg : NeverBot g) (hsub : IsSubadditive g) (h0 : g 0 = 0) :
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

end DeepWiki
