import DeepWiki.NetworkCalculus.Closures
import DeepWiki.NetworkCalculus.UltimatelyPseudoPeriodic

/-! # Sub-additive closure of a spot is UPP
A **spot** `spotNN d c` carries value `c` at the single point `d` and `+∞` (= `⊤`)
elsewhere, over the `ℝ≥0∞` (`MinPlusNN`) carrier where the closure machinery lives.
Its `n`-fold (min,+) convolution is the spot at `n·d` with value `n·c`, so the
sub-additive closure is the arithmetic-progression staircase
`k·c` at `t = k·d` and `⊤` off the lattice. That staircase is **ultimately
pseudo-periodic** with rank `0`, period `d`, increment `c`: shifting time by `d`
raises the closure by `c` everywhere. -/

namespace DeepWiki

open scoped NNReal ENNReal

/-- A **spot** over `ℝ≥0∞`: value `c` at the single point `d`, `⊤` (= `+∞`) off it. -/
noncomputable def spotNN (d : ℝ≥0) (c : ℝ≥0∞) : ℝ≥0 → ℝ≥0∞ :=
  fun t => if t = d then c else ⊤

/-- Pointwise reading of `spotNN`: `c` at `d`, `⊤` elsewhere. -/
@[simp]
theorem spotNN_apply (d : ℝ≥0) (c : ℝ≥0∞) (t : ℝ≥0) :
    spotNN d c t = if t = d then c else ⊤ := rfl

/-- `spotNN d c d = c`: the spot's on-support value. -/
@[simp]
theorem spotNN_self (d : ℝ≥0) (c : ℝ≥0∞) : spotNN d c d = c := by
  simp [spotNN]

/-- `t ≠ d → spotNN d c t = ⊤`: off-support is `+∞`. -/
theorem spotNN_of_ne {d t : ℝ≥0} (h : t ≠ d) (c : ℝ≥0∞) :
    spotNN d c t = ⊤ := by
  simp [spotNN, h]

/-- The origin spot `spotNN 0 0` is the (min,+) convolution unit `δ₀`
(`minConvPow _ 0`). -/
theorem spotNN_zero_zero (t : ℝ≥0) :
    spotNN 0 0 t = if t = 0 then 0 else ⊤ := rfl

/-- Convolution of two spots is a spot:
`minConv (spotNN a c) (spotNN b e) = spotNN (a + b) (c + e)`. The only finite split
of `t = a + b` through the two singletons is `(a, b)`; every other split hits a `⊤`
(which is absorbing on `ℝ≥0∞`). -/
theorem minConv_spotNN_spotNN {a b : ℝ≥0} {c e : ℝ≥0∞} :
    minConv (spotNN a c) (spotNN b e) = spotNN (a + b) (c + e) := by
  funext t
  rcases eq_or_ne t (a + b) with ht | ht
  · rw [ht, spotNN_self]
    apply le_antisymm
    · refine le_of_le_of_eq (minConv_le_add (spotNN a c) (spotNN b e) rfl) ?_
      rw [spotNN_self, spotNN_self]
    · refine le_minConv fun u s hus => ?_
      rcases eq_or_ne u a with hu | hu
      · -- u = a, a + s = a + b ⇒ s = b
        have hs : s = b := by rw [hu, add_right_inj] at hus; exact hus
        rw [hu, hs, spotNN_self, spotNN_self]
      · rw [spotNN_of_ne hu, top_add]
        exact le_top
  · rw [spotNN_of_ne ht]
    -- no split of `t` hits both singletons: any split is off at least one spot
    refine le_antisymm le_top (le_minConv fun u s hus => ?_)
    rcases eq_or_ne u a with hu | hu
    · -- u = a forces s ≠ b (else t = a + b)
      have hs : s ≠ b := by
        rintro rfl; exact ht (by rw [← hus, hu])
      rw [hu, spotNN_of_ne hs, add_top]
    · rw [spotNN_of_ne hu, top_add]

/-- The `n`-fold convolution power of a spot is the spot at `n·d` with value `n·c`:
`minConvPow (spotNN d c) n = spotNN (n • d) (n • c)`. The only finite split of `n·d`
through the singletons is the diagonal. -/
theorem minConvPow_spotNN (d : ℝ≥0) (c : ℝ≥0∞) (n : ℕ) :
    minConvPow (spotNN d c) n = spotNN (n • d) (n • c) := by
  induction n with
  | zero =>
      funext t
      rw [minConvPow_zero, zero_smul, zero_smul, spotNN_zero_zero]
      congr 1
  | succ n ih =>
      rw [minConvPow_succ, ih, minConv_spotNN_spotNN, succ_nsmul, succ_nsmul]

/-- The single index of the closure iInf that is finite at `t = (n+1)•d`:
the `(n+1)`-th spot there equals the `n`-th spot at `t` raised by `c`,
`spotNN ((n+1)•d) ((n+1)•c) (t + d) = spotNN (n•d) (n•c) t + c`, since
`t + d = (n+1)•d ⟺ t = n•d`. -/
theorem spotNN_succ_shift (d : ℝ≥0) (c : ℝ≥0∞) (n : ℕ) (t : ℝ≥0) :
    spotNN ((n + 1) • d) ((n + 1) • c) (t + d)
      = spotNN (n • d) (n • c) t + c := by
  rw [succ_nsmul d, succ_nsmul c]
  rcases eq_or_ne t (n • d) with ht | ht
  · -- t = n•d, so t + d = n•d + d hits the (shifted) support; both sides are `n•c + c`
    rw [ht, spotNN_self, spotNN_self]
  · -- t ≠ n•d, so t + d ≠ n•d + d; both sides are `⊤`
    have ht' : t + d ≠ n • d + d := by
      intro h; exact ht (by rwa [add_left_inj] at h)
    rw [spotNN_of_ne ht', spotNN_of_ne ht, top_add]

/-- **Periodicity step.** Advancing the closure of a spot by its period `d`
raises it by the increment `c` everywhere:
`subadditiveClosureENN (spotNN d c) (t + d) = subadditiveClosureENN (spotNN d c) t + c`.
(`d > 0` makes the `n = 0` term `⊤` at `t + d`, so it never controls the infimum.) -/
theorem subadditiveClosureENN_spotNN_shift (d : ℝ≥0) (c : ℝ≥0∞) (hd : 0 < d)
    (t : ℝ≥0) :
    subadditiveClosureENN (spotNN d c) (t + d)
      = subadditiveClosureENN (spotNN d c) t + c := by
  rw [subadditiveClosureENN_eq_iInf, subadditiveClosureENN_eq_iInf, ENNReal.iInf_add]
  simp only [minConvPow_spotNN]
  apply le_antisymm
  · -- LHS ≤ each shifted term: pick index `n + 1` on the left to match index `n` on the right
    refine le_iInf fun n => ?_
    refine le_trans (iInf_le _ (n + 1)) ?_
    rw [spotNN_succ_shift]
  · -- each LHS term `spotNN (n•d)(n•c)(t+d)` ≥ RHS:
    -- for `n = 0` it is `⊤` (since `d > 0`), for `n = m+1` it matches the `m`-th right term
    refine le_iInf fun n => ?_
    cases n with
    | zero =>
        -- `spotNN 0 0 (t + d) = ⊤` because `t + d ≠ 0` (as `d > 0`)
        rw [zero_smul, zero_smul]
        have : t + d ≠ 0 := (lt_of_lt_of_le hd (le_add_self)).ne'
        rw [spotNN_of_ne this]
        exact le_top
    | succ m =>
        rw [spotNN_succ_shift]
        exact iInf_le _ m

/-- **DNC Lemma 4.8.** The sub-additive closure of a spot `spotNN d c` (with `d > 0`)
is ultimately pseudo-periodic with rank `0`, period `d`, increment `c`. -/
theorem spotClosure_isUPPWith (d : ℝ≥0) (c : ℝ≥0∞) (hd : 0 < d) :
    IsUPPWith (subadditiveClosureENN (spotNN d c)) 0 d c :=
  ⟨hd, fun t _ => subadditiveClosureENN_spotNN_shift d c hd t⟩

/-- **DNC Lemma 4.8.** The sub-additive closure of a spot is UPP. -/
theorem spotClosure_isUPP (d : ℝ≥0) (c : ℝ≥0∞) (hd : 0 < d) :
    IsUPP (subadditiveClosureENN (spotNN d c)) :=
  (spotClosure_isUPPWith d c hd).isUPP

end DeepWiki
