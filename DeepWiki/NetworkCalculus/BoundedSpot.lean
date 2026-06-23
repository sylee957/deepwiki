import DeepWiki.NetworkCalculus.FunctionDioids
import Mathlib.Data.EReal.Operations

/-! # Spots: singleton-support building block
A *spot* `spotE a c` is the `EReal` curve carrying value `c` at the single
point `a` and `⊤ = +∞` everywhere else (singleton support) — the elementary
piece of the bounded-support / ultimately-pseudo-periodic representation.
The origin spot `spotE 0 0` is the (min,+) convolution unit `δ₀`; two spots
convolve to a spot (`spotE (a+b) (c+d)`); a spot convolves a general curve to
a right shift by `a` lifted by `c`. The good properties are gated on values
never being `⊥ = −∞` (so `EReal`'s bot-absorbing `+` behaves). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- `g` is never `⊥ = −∞` (local copy of the never-bot restriction). -/
def SpotNeverBot (g : ℝ≥0 → EReal) : Prop := ∀ t, g t ≠ ⊥

/-- The spot at `a` with value `c`: `c` at `a`, `⊤ = +∞` elsewhere. -/
noncomputable def spotE (a : ℝ≥0) (c : EReal) : ℝ≥0 → EReal :=
  fun t => if t = a then c else ⊤

/-- Pointwise reading of `spotE`: `c` at `a`, `⊤` off `a`. -/
@[simp]
theorem spotE_apply (a : ℝ≥0) (c : EReal) (t : ℝ≥0) :
    spotE a c t = if t = a then c else ⊤ := rfl

/-- `spotE a c a = c`: the spot's on-support value. -/
@[simp]
theorem spotE_self (a : ℝ≥0) (c : EReal) : spotE a c a = c := by
  simp [spotE]

/-- `t ≠ a → spotE a c t = ⊤`: off-support is `+∞`. -/
theorem spotE_of_ne {a t : ℝ≥0} (h : t ≠ a) (c : EReal) :
    spotE a c t = ⊤ := by
  simp [spotE, h]

/-- The origin spot `spotE 0 0` is the (min,+) convolution unit `convUnitEReal`. -/
theorem spotE_zero_zero (t : ℝ≥0) :
    spotE 0 0 t = if t = 0 then 0 else ⊤ := rfl

/-- A spot with a non-`⊥` value is itself never `⊥`. -/
theorem spotE_neverBot {a : ℝ≥0} {c : EReal} (hc : c ≠ ⊥) :
    SpotNeverBot (spotE a c) := by
  intro t
  rcases eq_or_ne t a with h | h
  · subst h; rwa [spotE_self]
  · rw [spotE_of_ne h]; exact (top_ne_bot)

/-- For never-`⊥` `f`, the origin spot is a right unit: `minConv f (spotE 0 0) = f`.
Every split `u + s = t` with `s ≠ 0` contributes `f u + ⊤ = ⊤`, so the `s = 0`
term `f t + 0` wins. -/
theorem minConv_spotE_zero_zero_right (f : ℝ≥0 → EReal) (hf : SpotNeverBot f) :
    minConv f (spotE 0 0) = f := by
  funext t
  apply le_antisymm
  · refine le_trans (minConv_le_add f (spotE 0 0) (add_zero t)) ?_
    rw [spotE_self, add_zero]
  · refine le_minConv fun u s hus => ?_
    rcases eq_or_ne s 0 with hs | hs
    · subst hs
      rw [spotE_self, add_zero]
      rw [add_zero] at hus; rw [hus]
    · rw [spotE_of_ne hs, EReal.add_top_of_ne_bot (hf u)]
      exact le_top

/-- For never-`⊥` `f`, the origin spot is a left unit: `minConv (spotE 0 0) f = f`. -/
theorem minConv_spotE_zero_zero_left (f : ℝ≥0 → EReal) (hf : SpotNeverBot f) :
    minConv (spotE 0 0) f = f := by
  rw [minConv_comm]; exact minConv_spotE_zero_zero_right f hf

/-- Convolution of two spots (with non-`⊥` values) is a spot:
`minConv (spotE a c) (spotE b d) = spotE (a + b) (c + d)`. The only finite split
of `t = a + b` through the two singletons is `(a, b)`. -/
theorem minConv_spotE_spotE {a b : ℝ≥0} {c d : EReal} (hc : c ≠ ⊥) (hd : d ≠ ⊥) :
    minConv (spotE a c) (spotE b d) = spotE (a + b) (c + d) := by
  funext t
  rcases eq_or_ne t (a + b) with ht | ht
  · rw [ht, spotE_self]
    apply le_antisymm
    · refine le_of_le_of_eq (minConv_le_add (spotE a c) (spotE b d) rfl) ?_
      rw [spotE_self, spotE_self]
    · refine le_minConv fun u s hus => ?_
      rcases eq_or_ne u a with hu | hu
      · -- u = a, a + s = a + b ⇒ s = b
        have hs : s = b := by rw [hu, add_right_inj] at hus; exact hus
        rw [hu, hs, spotE_self, spotE_self]
      · rw [spotE_of_ne hu, EReal.top_add_of_ne_bot (by
          rcases eq_or_ne s b with hs | hs
          · rw [hs, spotE_self]; exact hd
          · rw [spotE_of_ne hs]; exact top_ne_bot)]
        exact le_top
  · rw [spotE_of_ne ht]
    -- no split of t hits both singletons: any split is off at least one spot
    refine le_antisymm le_top (le_minConv fun u s hus => ?_)
    rcases eq_or_ne u a with hu | hu
    · -- u = a forces s ≠ b (else t = a + b)
      have hs : s ≠ b := by
        rintro rfl; exact ht (by rw [← hus, hu])
      rw [hu, spotE_of_ne hs, EReal.add_top_of_ne_bot (by rw [spotE_self]; exact hc)]
    · rw [spotE_of_ne hu, EReal.top_add_of_ne_bot (by
        rcases eq_or_ne s b with hs | hs
        · rw [hs, spotE_self]; exact hd
        · rw [spotE_of_ne hs]; exact top_ne_bot)]

/-- Spot convolves a curve to a right shift lifted by `c`, on its support
`t ≥ a`: `minConv (spotE a c) f t = c + f (t - a)`. The only on-support split is
`(a, t - a)`; every other split hits the spot's `⊤`. -/
theorem minConv_spotE_apply_of_le {a : ℝ≥0} {c : EReal}
    (f : ℝ≥0 → EReal) (hf : SpotNeverBot f) {t : ℝ≥0} (ht : a ≤ t) :
    minConv (spotE a c) f t = c + f (t - a) := by
  apply le_antisymm
  · refine le_of_le_of_eq (minConv_le_add (spotE a c) f
      (add_tsub_cancel_of_le ht)) ?_
    rw [spotE_self]
  · refine le_minConv fun u s hus => ?_
    rcases eq_or_ne u a with hu | hu
    · -- u = a and a + s = t ⇒ s = t - a
      have hs : s = t - a := by rw [← hus, hu, add_tsub_cancel_left]
      rw [hu, hs, spotE_self]
    · rw [spotE_of_ne hu, EReal.top_add_of_ne_bot (hf s)]
      exact le_top

/-- Below its support `t < a`, the spot convolution is `⊤`: no split `u + s = t`
can place `u = a` (that needs `a ≤ t`), so every split hits the spot's `⊤`. -/
theorem minConv_spotE_apply_of_lt {a : ℝ≥0} {c : EReal}
    (f : ℝ≥0 → EReal) (hf : SpotNeverBot f) {t : ℝ≥0} (ht : t < a) :
    minConv (spotE a c) f t = ⊤ := by
  refine le_antisymm le_top (le_minConv fun u s hus => ?_)
  have hu : u ≠ a := by
    rintro rfl
    exact absurd (le_self_add.trans hus.le) (not_le.mpr ht)
  rw [spotE_of_ne hu, EReal.top_add_of_ne_bot (hf s)]

end DeepWiki
