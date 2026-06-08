import Book.FunctionDioids
import Book.Continuity

/-! # Arrival curves
For a cumulative function `A` (taken as a plain `ℝ≥0 → ℝ≥0` function), a
non-decreasing function `α` is:

* a **maximal** (upper) arrival curve when `A ≤ A ∗ α` (`∗` = min-plus
  convolution `minConv`): `A` is dominated by its min-plus self-convolution.
* a **minimal** (lower) arrival curve when `A ≥ A ⊼ α` (`⊼` = max-plus
  convolution `maxConv`): `A` dominates its max-plus self-convolution.

Each has an equivalent **increment** characterization: `A (t + d) ≤ A t + α d`
for the maximal curve, and `A t + α d ≤ A (t + d)` for the minimal one. -/

namespace DeepWiki

open scoped Classical NNReal

/-- `α` is a maximal (upper) arrival curve for `A`: `A t ≤ (A ∗ α) t` for all
`t`, the natural-order form of `A ≤ A ∗ α` with `∗` the min-plus convolution. -/
def IsMaximalArrivalCurve (A α : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ t : ℝ≥0, A t ≤ minConv A α t

/-- `α` is a minimal (lower) arrival curve for `A`: `(A ⊼ α) t ≤ A t` for all
`t`, the natural-order form of `A ≥ A ⊼ α` with `⊼` the max-plus convolution. -/
def IsMinimalArrivalCurve (A α : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ t : ℝ≥0, maxConv A α t ≤ A t

/-- Equivalent definition of a maximal arrival curve: `A ≤ A ∗ α` holds iff the
increment bound `A (t + d) ≤ A t + α d` holds for all `t, d`. -/
theorem isMaximalArrivalCurve_iff_increment (A α : ℝ≥0 → ℝ≥0) :
    IsMaximalArrivalCurve A α ↔ ∀ t d : ℝ≥0, A (t + d) ≤ A t + α d := by
  constructor
  · -- `A (t + d) ≤ ⨅ {A u + α s | u + s = t + d} ≤ A t + α d`
    intro h t d
    refine le_trans (h (t + d)) ?_
    show (⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t + d}, A p.1.1 + α p.1.2)
        ≤ A t + α d
    exact ciInf_le (OrderBot.bddBelow _)
      (⟨(t, d), rfl⟩ : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t + d})
  · -- each split `u + s = t` gives `A t = A (u + s) ≤ A u + α s`, so `A t ≤ ⨅`
    intro h t
    show A t ≤ ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t}, A p.1.1 + α p.1.2
    refine le_ciInf ?_
    rintro ⟨⟨u, s⟩, rfl⟩
    exact h u s

/-! ## Properties of a maximal arrival curve
The maximal arrival curves of `A` are closed under pointwise `min`, under the
sub-additive closure, and upward-closed; the deconvolution `A ⊘ A` is the least
one. -/

/-- The pointwise minimum of two maximal arrival curves is a maximal arrival
curve: if `A ≤ A ∗ α` and `A ≤ A ∗ α'` then `A ≤ A ∗ (α ⊓ α')`. -/
theorem IsMaximalArrivalCurve.inf {A α α' : ℝ≥0 → ℝ≥0}
    (h : IsMaximalArrivalCurve A α) (h' : IsMaximalArrivalCurve A α') :
    IsMaximalArrivalCurve A (α ⊓ α') := by
  rw [isMaximalArrivalCurve_iff_increment] at h h' ⊢
  intro t d
  rw [Pi.inf_apply, ← min_add_add_left]
  exact le_min (h t d) (h' t d)

/-- Any function above a maximal arrival curve is again a maximal arrival curve:
if `A ≤ A ∗ α` and `α ≤ α'` then `A ≤ A ∗ α'`. -/
theorem IsMaximalArrivalCurve.mono {A α α' : ℝ≥0 → ℝ≥0}
    (h : IsMaximalArrivalCurve A α) (hle : α ≤ α') :
    IsMaximalArrivalCurve A α' := by
  rw [isMaximalArrivalCurve_iff_increment] at h ⊢
  intro t d
  refine le_trans (h t d) ?_
  gcongr
  exact hle d

/-- The deconvolution `A ⊘ A` is below every maximal arrival curve: if `α` is a
maximal arrival curve for `A` then `(A ⊘ A) d ≤ α d` for all `d`. This is the
"`A ⊘ A` is the best (least) maximal arrival curve" bound. -/
theorem deconv_self_le_of_isMaximalArrivalCurve {A α : ℝ≥0 → ℝ≥0}
    (h : IsMaximalArrivalCurve A α) (d : ℝ≥0) :
    deconv A A d ≤ α d := by
  rw [isMaximalArrivalCurve_iff_increment] at h
  refine ciSup_le (fun s => ?_)
  -- `A (d + s) - A s ≤ α d` since `A (d + s) ≤ A s + α d` (increment at `s, d`)
  rw [tsub_le_iff_right, add_comm d s, add_comm (α d) (A s)]
  exact h s d

/-- When `A ⊘ A` is well-defined (the deconvolution supremum is bounded above),
it is itself a maximal arrival curve for `A`. Together with
`deconv_self_le_of_isMaximalArrivalCurve` this makes `A ⊘ A` the least maximal
arrival curve, and `α ≥ A ⊘ A` an equivalent definition of a maximal curve. -/
theorem isMaximalArrivalCurve_deconv_self {A : ℝ≥0 → ℝ≥0}
    (hbdd : ∀ d : ℝ≥0, BddAbove (Set.range (fun s : ℝ≥0 => A (d + s) - A s))) :
    IsMaximalArrivalCurve A (deconv A A) := by
  rw [isMaximalArrivalCurve_iff_increment]
  intro t d
  -- `A (t + d) - A t ≤ (A ⊘ A) d`, the `s = t` term of the supremum
  have hterm : A (t + d) - A t ≤ deconv A A d :=
    le_ciSup_of_le (hbdd d) t (by rw [add_comm d t])
  rw [tsub_le_iff_right, add_comm (deconv A A d) (A t)] at hterm
  exact hterm

/-- A sufficient increment condition for a minimal arrival curve: if
`A t + α d ≤ A (t + d)` for all `t, d`, then `A ≥ A ⊼ α`. This direction holds
unconditionally on `ℝ≥0`; the converse needs `MaxConvBddAbove` (see
`isMinimalArrivalCurve_iff_increment_of_bddAbove`), since otherwise the `ℝ≥0`
supremum is junk `0` and `A ≥ A ⊼ α` holds vacuously while the increment bound
may fail. -/
theorem isMinimalArrivalCurve_of_increment (A α : ℝ≥0 → ℝ≥0)
    (h : ∀ t d : ℝ≥0, A t + α d ≤ A (t + d)) :
    IsMinimalArrivalCurve A α := by
  -- each split `u + s = t` gives `A u + α s ≤ A (u + s) = A t`, so `⨆ ≤ A t`
  intro t
  refine ciSup_le ?_
  rintro ⟨⟨u, s⟩, rfl⟩
  exact h u s

/-- The max-plus convolution family `{A u + α s | u + s = t}` is bounded above
for every `t` — the condition making the `ℝ≥0` supremum `A ⊼ α` well-defined
(not junk), needed for the converse of the increment characterization. -/
def MaxConvBddAbove (A α : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ t : ℝ≥0, BddAbove (Set.range
    (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} => A p.1.1 + α p.1.2))

/-- Equivalent definition of a minimal arrival curve, under `MaxConvBddAbove`:
`A ≥ A ⊼ α` holds iff the increment bound `A t + α d ≤ A (t + d)` holds for all
`t, d`. The bound on the convolution family makes the supremum well-defined, so
each term lies below it. -/
theorem isMinimalArrivalCurve_iff_increment_of_bddAbove
    (A α : ℝ≥0 → ℝ≥0) (hbdd : MaxConvBddAbove A α) :
    IsMinimalArrivalCurve A α ↔ ∀ t d : ℝ≥0, A t + α d ≤ A (t + d) := by
  refine ⟨fun h t d => ?_, isMinimalArrivalCurve_of_increment A α⟩
  -- `A t + α d` is the `(t, d)`-split term, so it is `≤` the supremum `≤ A (t+d)`
  refine le_trans ?_ (h (t + d))
  exact le_ciSup_of_le (hbdd (t + d))
    (⟨(t, d), rfl⟩ : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t + d}) le_rfl

/-- When `A` and `α` are non-decreasing, the max-plus convolution family at `t`
is bounded above by `A t + α t` (each split has `u, s ≤ t`). Cumulative `A` and
`α ∈ ℱ↑` are non-decreasing, so this holds in the book's setting. -/
theorem maxConvBddAbove_of_monotone (A α : ℝ≥0 → ℝ≥0)
    (hA : Monotone A) (hα : Monotone α) : MaxConvBddAbove A α := by
  intro t
  refine ⟨A t + α t, ?_⟩
  rintro x ⟨⟨⟨u, s⟩, rfl⟩, rfl⟩
  exact add_le_add (hA (le_add_right le_rfl)) (hα (le_add_left le_rfl))

/-- Equivalent definition of a minimal arrival curve for non-decreasing `A`, `α`:
`A ≥ A ⊼ α` holds iff `A t + α d ≤ A (t + d)` for all `t, d`. Monotonicity bounds
the max-plus convolution, discharging `MaxConvBddAbove`. -/
theorem isMinimalArrivalCurve_iff_increment_of_monotone
    (A α : ℝ≥0 → ℝ≥0) (hA : Monotone A) (hα : Monotone α) :
    IsMinimalArrivalCurve A α ↔ ∀ t d : ℝ≥0, A t + α d ≤ A (t + d) :=
  isMinimalArrivalCurve_iff_increment_of_bddAbove A α
    (maxConvBddAbove_of_monotone A α hA hα)

/-! ## Sub-additive closure of a maximal arrival curve
The (min,+) self-convolution powers of `α` and their pointwise infimum (the
(min,+) sub-additive closure `α⋆`) are again maximal arrival curves for `A`,
and `α⋆ ≤ α`. Powers are indexed from `1` (`convPowNN α 0 = α`), avoiding the
`+∞`-valued (min,+) unit `δ₀` that `ℝ≥0` cannot represent. -/

/-- `n`-fold (min,+) self-convolution of `α`, indexed from `1`:
`convPowNN α 0 = α` and `convPowNN α (n+1) = α ∗ (convPowNN α n)`. -/
noncomputable def convPowNN (α : ℝ≥0 → ℝ≥0) : ℕ → (ℝ≥0 → ℝ≥0)
  | 0 => α
  | n + 1 => minConvProj α (convPowNN α n)

/-- The (min,+) sub-additive closure `α⋆ t = ⨅ₙ (convPowNN α n) t`, the
pointwise infimum of the self-convolution powers (`ℝ≥0` infimum). -/
noncomputable def subadditiveClosureNN (α : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun t => ⨅ n : ℕ, convPowNN α n t

/-- The closure is below `α`: `α⋆ t ≤ α t`, as the `n = 0` term of the
infimum `⨅ₙ (convPowNN α n) t`. -/
theorem subadditiveClosureNN_le (α : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    subadditiveClosureNN α t ≤ α t :=
  ciInf_le (OrderBot.bddBelow _) 0

/-- The increment bound iterated through the (min,+) powers: if `α` is a
maximal arrival curve for `A`, then `A (t + d) ≤ A t + (convPowNN α n) d` for
every power `n`. -/
theorem increment_convPowNN_of_isMaximalArrivalCurve {A α : ℝ≥0 → ℝ≥0}
    (h : IsMaximalArrivalCurve A α) (n : ℕ) (t d : ℝ≥0) :
    A (t + d) ≤ A t + convPowNN α n d := by
  rw [isMaximalArrivalCurve_iff_increment] at h
  induction n generalizing t d with
  | zero => exact h t d
  | succ n ih =>
    -- `convPowNN α (n+1) d = ⨅_{u+s=d} α u + (convPowNN α n) s`
    show A (t + d) ≤ A t + minConvProj α (convPowNN α n) d
    rw [minConvProj_eq, add_comm (A t), ← tsub_le_iff_right]
    refine le_ciInf ?_
    rintro ⟨⟨u, s⟩, (hus : u + s = d)⟩
    -- `A (t+d) = A ((t+u)+s) ≤ A (t+u) + (convPowNN α n) s`, and
    -- `A (t+u) ≤ A t + α u`, so `A (t+d) - A t ≤ α u + (convPowNN α n) s`
    rw [tsub_le_iff_right]
    calc A (t + d) = A ((t + u) + s) := by rw [add_assoc, hus]
      _ ≤ A (t + u) + convPowNN α n s := ih (t + u) s
      _ ≤ (A t + α u) + convPowNN α n s := by gcongr; exact h t u
      _ = A t + (α u + convPowNN α n s) := by ring
      _ = (α u + convPowNN α n s) + A t := by ring

/-- Each self-convolution power of a maximal arrival curve is again a maximal
arrival curve: if `A ≤ A ∗ α` then `A ≤ A ∗ (convPowNN α n)`. -/
theorem isMaximalArrivalCurve_convPowNN_of_isMaximalArrivalCurve
    {A α : ℝ≥0 → ℝ≥0} (h : IsMaximalArrivalCurve A α) (n : ℕ) :
    IsMaximalArrivalCurve A (convPowNN α n) := by
  rw [isMaximalArrivalCurve_iff_increment]
  exact fun t d => increment_convPowNN_of_isMaximalArrivalCurve h n t d

/-- The (min,+) sub-additive closure of a maximal arrival curve is again a
maximal arrival curve: if `A ≤ A ∗ α` then `A ≤ A ∗ α⋆`, with `α⋆ ≤ α`. The
increment bound through every power `A (t+d) ≤ A t + (convPowNN α n) d` passes
to the infimum `α⋆ d = ⨅ₙ (convPowNN α n) d`. -/
theorem IsMaximalArrivalCurve.subadditiveClosure {A α : ℝ≥0 → ℝ≥0}
    (h : IsMaximalArrivalCurve A α) :
    IsMaximalArrivalCurve A (subadditiveClosureNN α) := by
  rw [isMaximalArrivalCurve_iff_increment]
  intro t d
  -- `A (t+d) - A t ≤ (convPowNN α n) d` for every `n`, so `≤ ⨅ₙ = α⋆ d`
  rw [show subadditiveClosureNN α d = ⨅ n : ℕ, convPowNN α n d from rfl,
    add_comm (A t), ← tsub_le_iff_right]
  refine le_ciInf (fun n => ?_)
  rw [tsub_le_iff_right, add_comm (convPowNN α n d)]
  exact increment_convPowNN_of_isMaximalArrivalCurve h n t d

/-! ## Left-continuous extension of a maximal arrival curve
The left limit `αₗ x = sSup (α '' Iio x)` of a non-decreasing `α` is again a
maximal arrival curve when the cumulative function `A` is left-continuous. -/

open Set Filter Topology

/-- Left limit of `α` at `x`: `sSup (α '' Iio x)`, the supremum of `α` over the
left interval `Iio x`. For monotone `α` this is `lim_{y → x⁻} α y`. -/
noncomputable def alphaLeftLim (α : ℝ≥0 → ℝ≥0) (x : ℝ≥0) : ℝ≥0 :=
  sSup (α '' Set.Iio x)

/-- For monotone `α`, the family `α '' Iio x` is bounded above by `α x`. -/
theorem bddAbove_image_Iio_of_monotone {α : ℝ≥0 → ℝ≥0}
    (hα : Monotone α) (x : ℝ≥0) : BddAbove (α '' Set.Iio x) := by
  refine ⟨α x, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact hα (le_of_lt hz)

/-- For monotone `α`, each value `α y` with `y < x` is `≤ alphaLeftLim α x`. -/
theorem le_alphaLeftLim_of_lt {α : ℝ≥0 → ℝ≥0} (hα : Monotone α)
    {y x : ℝ≥0} (hyx : y < x) : α y ≤ alphaLeftLim α x :=
  le_csSup (bddAbove_image_Iio_of_monotone hα x) ⟨y, hyx, rfl⟩

/-- The left limit is `≤` the function value: `alphaLeftLim α x ≤ α x` for
monotone `α` (each `α y`, `y < x`, lies below `α x`). -/
theorem alphaLeftLim_le_self {α : ℝ≥0 → ℝ≥0} (hα : Monotone α)
    (x : ℝ≥0) : alphaLeftLim α x ≤ α x := by
  rcases Set.eq_empty_or_nonempty (α '' Set.Iio x) with he | hne
  · rw [alphaLeftLim, he, csSup_empty]; exact bot_le
  · refine csSup_le hne ?_
    rintro y ⟨z, hz, rfl⟩
    exact hα (le_of_lt hz)

/-- Left-continuous `A` has `A` as the left limit at each `t`:
`Tendsto A (𝓝[<] t) (𝓝 (A t))`. -/
theorem tendsto_nhdsWithin_Iio_of_leftContinuous {A : ℝ≥0 → ℝ≥0}
    (hA : IsLeftContinuous A) (t : ℝ≥0) :
    Tendsto A (𝓝[<] t) (𝓝 (A t)) :=
  (hA t).tendsto

/-- Left-continuous extension of a maximal arrival curve is maximal: if `A` is
left-continuous, `α` non-decreasing, and `α` a maximal arrival curve for `A`,
then `alphaLeftLim α` is a maximal arrival curve for `A`. -/
theorem isMaximalArrivalCurve_alphaLeftLim_of_leftContinuous
    {A α : ℝ≥0 → ℝ≥0} (hA : IsLeftContinuous A) (hα : Monotone α)
    (h : IsMaximalArrivalCurve A α) :
    IsMaximalArrivalCurve A (alphaLeftLim α) := by
  rw [isMaximalArrivalCurve_iff_increment] at h ⊢
  intro t d
  -- Edge case `d = 0`: `A (t + 0) = A t ≤ A t + αₗ 0`.
  rcases eq_or_lt_of_le (zero_le' (a := d)) with hd | hd
  · rw [← hd, add_zero]; exact le_self_add
  -- For `s ∈ (t, t + d)` (eventually within `Iio (t+d)`), bound
  -- `A s ≤ A t + αₗ d`, then pass to the left limit `A s → A (t+d)`.
  have hlim : Tendsto A (𝓝[<] (t + d)) (𝓝 (A (t + d))) :=
    tendsto_nhdsWithin_Iio_of_leftContinuous hA (t + d)
  have htlt : t < t + d := lt_add_of_pos_right t hd
  haveI : (𝓝[<] (t + d)).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨t, htlt⟩
  have hev : ∀ᶠ s in 𝓝[<] (t + d), A s ≤ A t + alphaLeftLim α d := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioi_mem_nhds htlt] with s hts hslt
    -- `s = t + (s - t)`, `s - t < d`, so `α (s - t) ≤ αₗ d`.
    have hslt' : s < t + d := hslt
    have hsub : t + (s - t) = s := by
      rw [add_tsub_cancel_of_le (le_of_lt hts)]
    have hltd : s - t < d := by
      rw [tsub_lt_iff_left (le_of_lt hts)]
      exact hslt'
    have key : A s ≤ A t + α (s - t) := by
      have := h t (s - t)
      rwa [hsub] at this
    refine le_trans key ?_
    gcongr
    exact le_alphaLeftLim_of_lt hα hltd
  -- Pass the closed condition `A s ≤ c` to the limit.
  exact le_of_tendsto hlim hev

end DeepWiki
