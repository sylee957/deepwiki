import Book.ServersResidualPmoo

/-! # Pay multiplexing only once along a chain
The multi-dimensional PMOO operator, in its all-crossing form: along
a tandem of `n + 1` strict servers the tagged flow gains
`(β₀ ∗ ⋯ ∗ βₙ − ∑_{j≠i} αⱼ)⁺` from the fully cascaded start — the
per-server starts cascade downwards, the strict bounds telescope
across the stage windows, and each cross flow pays its arrival curve
once over the whole window. The book's general operator additionally
lets flows enter and leave mid-tandem; here every flow crosses every
server. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The cascaded start of a chain of stages: descend one hop by the
backlogged-period start of its pair, then recurse on the lower
chain. -/
noncomputable def chainStart {ι : Type*} [Fintype ι]
    (F : ℕ → ι → Curve) : ℕ → ℝ≥0 → ℝ≥0
  | 0, t => t
  | n + 1, t => chainStart F n
      (start (fun x => ∑ j, (F n j) x) (fun x => ∑ j, (F (n + 1) j) x) t)

/-- `chainStart` at no hops is the time itself. -/
theorem chainStart_zero {ι : Type*} [Fintype ι] (F : ℕ → ι → Curve)
    (t : ℝ≥0) : chainStart F 0 t = t := rfl

/-- `chainStart` descends the top hop, then recurses. -/
theorem chainStart_succ {ι : Type*} [Fintype ι] (F : ℕ → ι → Curve)
    (n : ℕ) (t : ℝ≥0) :
    chainStart F (n + 1) t = chainStart F n
      (start (fun x => ∑ j, (F n j) x)
        (fun x => ∑ j, (F (n + 1) j) x) t) := rfl

/-- The cascaded start sits at or before its time. -/
theorem chainStart_le {ι : Type*} [Fintype ι] (F : ℕ → ι → Curve)
    (n : ℕ) : ∀ t, chainStart F n t ≤ t := by
  induction n with
  | zero => exact fun t => le_rfl
  | succ n ih => exact fun t => le_trans (ih _) (start_le _ _ t)

/-- The cascaded start is monotone in its time. -/
theorem chainStart_mono {ι : Type*} [Fintype ι] (F : ℕ → ι → Curve)
    (n : ℕ) : ∀ {t t' : ℝ≥0}, t ≤ t' →
      chainStart F n t ≤ chainStart F n t' := by
  induction n with
  | zero => exact fun h => h
  | succ n ih => exact fun h => ih (start_mono _ _ h)

/-- The convolution of the chain's curves, hop `0` through hop `n`:
indexed from `β 0` to stay `ℝ≥0`-valued. -/
noncomputable def chainConv (β : ℕ → ℝ≥0 → ℝ≥0) : ℕ → ℝ≥0 → ℝ≥0
  | 0 => β 0
  | n + 1 => minConvProj (chainConv β n) (β (n + 1))

/-- `chainConv` at one hop is that hop's curve. -/
theorem chainConv_zero (β : ℕ → ℝ≥0 → ℝ≥0) : chainConv β 0 = β 0 :=
  rfl

/-- `chainConv` convolves the next hop's curve onto the fold. -/
theorem chainConv_succ (β : ℕ → ℝ≥0 → ℝ≥0) (n : ℕ) :
    chainConv β (n + 1) = minConvProj (chainConv β n) (β (n + 1)) :=
  rfl

/-- The chain convolution at the origin is the sum of the hops'
origin values. -/
theorem chainConv_zero_eq (β : ℕ → ℝ≥0 → ℝ≥0) (n : ℕ) :
    chainConv β n 0 = ∑ h ∈ Finset.range (n + 1), β h 0 := by
  induction n with
  | zero => exact (Finset.sum_range_one (f := fun h => β h 0)).symm
  | succ n ih =>
    rw [chainConv_succ, minConvProj_zero_eq, ih,
      Finset.sum_range_succ (f := fun h => β h 0) (n + 1)]

/-- **The telescope**: along a chain of `n + 1` strict servers, the
aggregate output at `t` dominates the aggregate input at the fully
cascaded start plus the chain convolution of the gap — each hop's
strict bound runs on its own start window, every flow is fully
served at each cascaded start, and the convolution splits across the
stage windows. -/
theorem sum_add_chainConv_le_of_strict_chain {ι : Type*} [Fintype ι]
    {F : ℕ → ι → Curve} {β : ℕ → ℝ≥0 → ℝ≥0} {n : ℕ}
    (hc : ∀ h, h ≤ n → ∀ j, F (h + 1) j ≤ F h j)
    (hstrict : ∀ h, h ≤ n → ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (F h j) x)
        (fun x => ∑ j, (F (h + 1) j) x) (Set.Ioc s t) →
      (∑ j, (F (h + 1) j) s) + β h (t - s) ≤ ∑ j, (F (h + 1) j) t)
    (t : ℝ≥0) :
    (∑ j, (F 0 j) (chainStart F (n + 1) t))
      + chainConv β n (t - chainStart F (n + 1) t)
      ≤ ∑ j, (F (n + 1) j) t := by
  induction n generalizing t with
  | zero =>
    set s := start (fun x => ∑ j, (F 0 j) x)
      (fun x => ∑ j, (F 1 j) x) t with hs
    have hst : s ≤ t := start_le _ _ t
    have heq : (∑ j, (F 1 j) s) = ∑ j, (F 0 j) s :=
      Finset.sum_congr rfl fun j _ =>
        Curve.apply_start_sum_eq (fun j => hc 0 le_rfl j) t j
    have htop := hstrict 0 le_rfl s t hst (isBacklogged_Ioc_start
      (fun x => Finset.sum_le_sum fun j _ => hc 0 le_rfl j x) t)
    show (∑ j, (F 0 j) s) + β 0 (t - s) ≤ ∑ j, (F 1 j) t
    rw [← heq]
    exact htop
  | succ n ih =>
    set s := start (fun x => ∑ j, (F (n + 1) j) x)
      (fun x => ∑ j, (F (n + 2) j) x) t with hs
    have hst : s ≤ t := start_le _ _ t
    have hcs : chainStart F (n + 1) s ≤ s := chainStart_le F (n + 1) s
    have htop := hstrict (n + 1) le_rfl s t hst
      (isBacklogged_Ioc_start
        (fun x => Finset.sum_le_sum fun j _ =>
          hc (n + 1) le_rfl j x) t)
    have heq : (∑ j, (F (n + 2) j) s) = ∑ j, (F (n + 1) j) s :=
      Finset.sum_congr rfl fun j _ =>
        Curve.apply_start_sum_eq (fun j => hc (n + 1) le_rfl j) t j
    have hih := ih (fun h hh => hc h (hh.trans (Nat.le_succ n)))
      (fun h hh => hstrict h (hh.trans (Nat.le_succ n))) s
    have hconv : chainConv β (n + 1) (t - chainStart F (n + 1) s)
        ≤ chainConv β n (s - chainStart F (n + 1) s) + β (n + 1) (t - s) :=
      minConvProj_le_add (by
        rw [add_comm]
        exact tsub_add_tsub_cancel hst hcs)
    show (∑ j, (F 0 j) (chainStart F (n + 1) s))
        + chainConv β (n + 1) (t - chainStart F (n + 1) s)
        ≤ ∑ j, (F (n + 2) j) t
    calc (∑ j, (F 0 j) (chainStart F (n + 1) s))
        + chainConv β (n + 1) (t - chainStart F (n + 1) s)
        ≤ (∑ j, (F 0 j) (chainStart F (n + 1) s))
          + (chainConv β n (s - chainStart F (n + 1) s)
            + β (n + 1) (t - s)) := add_le_add le_rfl hconv
      _ = ((∑ j, (F 0 j) (chainStart F (n + 1) s))
          + chainConv β n (s - chainStart F (n + 1) s))
          + β (n + 1) (t - s) := (add_assoc _ _ _).symm
      _ ≤ (∑ j, (F (n + 1) j) s) + β (n + 1) (t - s) :=
          add_le_add hih le_rfl
      _ = (∑ j, (F (n + 2) j) s) + β (n + 1) (t - s) := by rw [heq]
      _ ≤ ∑ j, (F (n + 2) j) t := htop

/-- Causality folds along the chain: the final output never exceeds
the initial input. -/
theorem chain_apply_le {ι : Type*} [Fintype ι]
    {F : ℕ → ι → Curve} {n : ℕ}
    (hc : ∀ h, h ≤ n → ∀ j, F (h + 1) j ≤ F h j) (j : ι) (x : ℝ≥0) :
    (F (n + 1) j) x ≤ (F 0 j) x := by
  induction n with
  | zero => exact hc 0 le_rfl j x
  | succ n ih =>
    exact le_trans (hc (n + 1) le_rfl j x)
      (ih (fun h hh => hc h (hh.trans (Nat.le_succ n))))

/-- The per-flow floor: each flow's initial input at the fully
cascaded start is below its final output — full service at each
cascaded start, monotonicity across each stage window. -/
theorem apply_chainStart_le_chain {ι : Type*} [Fintype ι]
    {F : ℕ → ι → Curve} {n : ℕ}
    (hc : ∀ h, h ≤ n → ∀ j, F (h + 1) j ≤ F h j) (i : ι) (t : ℝ≥0) :
    (F 0 i) (chainStart F (n + 1) t) ≤ (F (n + 1) i) t := by
  induction n generalizing t with
  | zero =>
    set s := start (fun x => ∑ j, (F 0 j) x)
      (fun x => ∑ j, (F 1 j) x) t with hs
    calc (F 0 i) (chainStart F 1 t) = (F 0 i) s := rfl
      _ = (F 1 i) s :=
        (Curve.apply_start_sum_eq (fun j => hc 0 le_rfl j) t i).symm
      _ ≤ (F 1 i) t := (F 1 i).mono (start_le _ _ t)
  | succ n ih =>
    set s := start (fun x => ∑ j, (F (n + 1) j) x)
      (fun x => ∑ j, (F (n + 2) j) x) t with hs
    calc (F 0 i) (chainStart F (n + 2) t)
        = (F 0 i) (chainStart F (n + 1) s) := rfl
      _ ≤ (F (n + 1) i) s :=
        ih (fun h hh => hc h (hh.trans (Nat.le_succ n))) s
      _ = (F (n + 2) i) s :=
        (Curve.apply_start_sum_eq (fun j => hc (n + 1) le_rfl j) t i).symm
      _ ≤ (F (n + 2) i) t := (F (n + 2) i).mono (start_le _ _ t)

/-- The chain PMOO residual `(β₀ ∗ ⋯ ∗ βₙ − α)⁺`: the chain
convolution less the cross-traffic, clamped. -/
noncomputable def pmooResidualChain (β : ℕ → ℝ≥0 → ℝ≥0) (n : ℕ)
    (α : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun v => chainConv β n v - α v

/-- `pmooResidualChain β n α v` is the clamped difference at `v`. -/
@[simp] theorem pmooResidualChain_apply (β : ℕ → ℝ≥0 → ℝ≥0) (n : ℕ)
    (α : ℝ≥0 → ℝ≥0) (v : ℝ≥0) :
    pmooResidualChain β n α v = chainConv β n v - α v := rfl

/-- `pmooResidualChain β n α 0 = 0` for hop curves null at the
origin. -/
theorem pmooResidualChain_zero_eq {β : ℕ → ℝ≥0 → ℝ≥0} {n : ℕ}
    (α : ℝ≥0 → ℝ≥0) (hβ0 : ∀ h, h ≤ n → β h 0 = 0) :
    pmooResidualChain β n α 0 = 0 := by
  rw [pmooResidualChain_apply, chainConv_zero_eq,
    Finset.sum_eq_zero fun h hh =>
      hβ0 h (Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)),
    zero_tsub]

/-- **Pay multiplexing only once along the chain, anchored form**:
across a tandem of `n + 1` strict servers crossed by every flow, the
tagged flow gains the chain PMOO residual from the fully cascaded
start — the telescope carries the aggregate, each cross flow pays
its arrival curve once over the whole window, and past the clamp the
bound rides the per-flow floor. -/
theorem add_pmooResidualChain_le_of_strict_chain {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {F : ℕ → ι → Curve} {β : ℕ → ℝ≥0 → ℝ≥0} {n : ℕ}
    {α : ι → ℝ≥0 → ℝ≥0}
    (hc : ∀ h, h ≤ n → ∀ j, F (h + 1) j ≤ F h j)
    (hstrict : ∀ h, h ≤ n → ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (F h j) x)
        (fun x => ∑ j, (F (h + 1) j) x) (Set.Ioc s t) →
      (∑ j, (F (h + 1) j) s) + β h (t - s) ≤ ∑ j, (F (h + 1) j) t)
    {i : ι} (harr : ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(F 0 j) (α j))
    (t : ℝ≥0) :
    (F 0 i) (chainStart F (n + 1) t)
      + pmooResidualChain β n
          (fun v => ∑ j ∈ Finset.univ.erase i, α j v)
          (t - chainStart F (n + 1) t)
      ≤ (F (n + 1) i) t := by
  set c := chainStart F (n + 1) t with hcdef
  have hct : c ≤ t := chainStart_le F (n + 1) t
  have htel := sum_add_chainConv_le_of_strict_chain hc hstrict t
  have hfloor := apply_chainStart_le_chain hc i t
  -- the cross-traffic pays once over `(c, t]`
  have hcross : (∑ j ∈ Finset.univ.erase i, (F (n + 1) j) t)
      ≤ (∑ j ∈ Finset.univ.erase i, (F 0 j) c)
        + ∑ j ∈ Finset.univ.erase i, α j (t - c) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j hj => ?_
    have harr' : (F 0 j) t ≤ (F 0 j) c + α j (t - c) := by
      have h := (isMaximalArrivalBound_iff_increment _ _).mp
        (harr j (Finset.ne_of_mem_erase hj)) c (t - c)
      rwa [add_tsub_cancel_of_le hct] at h
    exact le_trans (chain_apply_le hc j t) harr'
  -- the totals split over the tagged flow and the rest
  have hSt : (∑ j, (F (n + 1) j) t)
      = (F (n + 1) i) t + ∑ j ∈ Finset.univ.erase i, (F (n + 1) j) t :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  have hSc : (∑ j, (F 0 j) c)
      = (F 0 i) c + ∑ j ∈ Finset.univ.erase i, (F 0 j) c :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  rw [pmooResidualChain_apply]
  rcases le_or_gt (∑ j ∈ Finset.univ.erase i, α j (t - c))
      (chainConv β n (t - c)) with hcase | hcase
  · rw [← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub hcase]
    have htelR := NNReal.coe_le_coe.mpr htel
    have hcrossR := NNReal.coe_le_coe.mpr hcross
    have hStR := congrArg NNReal.toReal hSt
    have hScR := congrArg NNReal.toReal hSc
    push_cast at htelR hcrossR hStR hScR
    linarith
  · rw [tsub_eq_zero_of_le hcase.le, add_zero]
    exact hfloor

/-- **Pay multiplexing only once along the chain**: the tagged flow
is min-plus served at `(β₀ ∗ ⋯ ∗ βₙ − ∑_{j≠i} αⱼ)⁺` across the whole
tandem. -/
theorem minConv_pmooResidualChain_le_of_strict_chain {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {F : ℕ → ι → Curve} {β : ℕ → ℝ≥0 → ℝ≥0} {n : ℕ}
    {α : ι → ℝ≥0 → ℝ≥0}
    (hc : ∀ h, h ≤ n → ∀ j, F (h + 1) j ≤ F h j)
    (hstrict : ∀ h, h ≤ n → ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (F h j) x)
        (fun x => ∑ j, (F (h + 1) j) x) (Set.Ioc s t) →
      (∑ j, (F (h + 1) j) s) + β h (t - s) ≤ ∑ j, (F (h + 1) j) t)
    {i : ι} (harr : ∀ j, j ≠ i → IsMaximalArrivalBound ⇑(F 0 j) (α j))
    (t : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(F 0 i))
        (Deviation.liftENN (pmooResidualChain β n
          (fun v => ∑ j ∈ Finset.univ.erase i, α j v))) t
      ≤ ((F (n + 1) i) t : ℝ≥0∞) := by
  have hkey := add_pmooResidualChain_le_of_strict_chain hc hstrict
    harr t
  refine le_trans (minConv_le_add _ _
    (add_tsub_cancel_of_le (chainStart_le F (n + 1) t))) ?_
  exact_mod_cast hkey

/-! ## Book restatement (the PMOO multi-dimensional operator)
The tandem PMOO theorem, in the case where every flow crosses every
server: a tandem of `n + 1` servers, each offering a strict service
curve, with all cross flows arrival-constrained, min-plus serves the
tagged flow at `(β₀ ∗ ⋯ ∗ βₙ − ∑_{j≠i} αⱼ)⁺` — each cross flow's
burst is paid once across the whole tandem. The book's general
operator additionally distributes each `αᵢ` over the sub-path its
flow crosses (`∑_{j∈pᵢ} uⱼ` inside the infimum); flows entering and
leaving mid-tandem need the per-flow path infrastructure and are
deferred. The two-server instance is the chapter
`ServersResidualPmoo`. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ℕ → ι → Curve} {β : ℕ → ℝ≥0 → ℝ≥0} {n : ℕ}
    {α : ι → ℝ≥0 → ℝ≥0}
    (hc : ∀ h, h ≤ n → ∀ j, F (h + 1) j ≤ F h j)
    (hstrict : ∀ h, h ≤ n → ∀ s t, s ≤ t →
      IsBacklogged (fun x => ∑ j, (F h j) x)
        (fun x => ∑ j, (F (h + 1) j) x) (Set.Ioc s t) →
      (∑ j, (F (h + 1) j) s) + β h (t - s) ≤ ∑ j, (F (h + 1) j) t)
    {i : ι} (harr : ∀ j, j ≠ i → IsMaximalArrivalCurve ⇑(F 0 j) (α j))
    (t : ℝ≥0) :
    minConv (Deviation.liftENN ⇑(F 0 i))
        (Deviation.liftENN (pmooResidualChain β n
          (fun v => ∑ j ∈ Finset.univ.erase i, α j v))) t
      ≤ ((F (n + 1) i) t : ℝ≥0∞) :=
  minConv_pmooResidualChain_le_of_strict_chain hc hstrict
    (fun j hj => (harr j hj).2) t

end DeepWiki
