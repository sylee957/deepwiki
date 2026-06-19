import DeepWiki.NetworkCalculus.ServiceCurveStrict
import DeepWiki.NetworkCalculus.ServiceCurveMinimal

/-! # Weakly strict service curves
Between the strict and min-plus service curves sits the weakly strict
type: the strict increment is required only from the start of the
backlogged period of each `t`,
`D(t) ≥ D(Start(t)) + β(t − Start(t))`. The hierarchy
`strict ⊆ weakly strict ⊆ min-plus` holds at the relation level — the
min-plus transport of the strict theory factors through this middle
layer, since it only ever uses strictness at the start. The book's
standing assumption that `β` is non-decreasing and left-continuous is
dropped — the inclusions do not use it; it returns with the equality
characterizations of the hierarchy. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- A weakly strict (minimal) service curve: every served pair gains
`beta` from the start of the backlogged period of each `t`,
`D(Start(t)) + β(t − Start(t)) ≤ D(t)`. -/
def IsWeaklyStrictMinimalServiceCurve (beta : ℝ≥0 → ℝ≥0)
    (S : Curve → Curve → Prop) : Prop :=
  ∀ A D : Curve, S A D → ∀ t,
    D (start ⇑A ⇑D t) + beta (t - start ⇑A ⇑D t) ≤ D t

/-- The largest relation offering the weakly strict curve `beta`:
causality plus the start-anchored increment. -/
def weaklyStrictServiceRel (beta : ℝ≥0 → ℝ≥0) :
    Curve → Curve → Prop :=
  fun A D => D ≤ A ∧ ∀ t,
    D (start ⇑A ⇑D t) + beta (t - start ⇑A ⇑D t) ≤ D t

/-- `weaklyStrictServiceRel beta A D` unfolds to causality plus the
start-anchored bound. -/
theorem mem_weaklyStrictServiceRel_iff {beta : ℝ≥0 → ℝ≥0}
    {A D : Curve} :
    weaklyStrictServiceRel beta A D ↔
      D ≤ A ∧ ∀ t,
        D (start ⇑A ⇑D t) + beta (t - start ⇑A ⇑D t) ≤ D t :=
  Iff.rfl

/-- Each curve serves itself with any weakly strict curve null at the
origin: against itself the start is `t` itself (`start_self`). -/
theorem weaklyStrictServiceRel_self {beta : ℝ≥0 → ℝ≥0}
    (h0 : beta 0 = 0) (A : Curve) :
    weaklyStrictServiceRel beta A A := by
  refine ⟨fun _ => le_refl _, fun t => ?_⟩
  rw [start_self, tsub_self, h0, add_zero]

/-- When `beta 0 = 0`, `weaklyStrictServiceRel beta` is a server. -/
theorem isServer_weaklyStrictServiceRel {beta : ℝ≥0 → ℝ≥0}
    (h0 : beta 0 = 0) :
    IsServer (weaklyStrictServiceRel beta) :=
  ⟨fun _ _ hp => hp.1, fun A => ⟨A, weaklyStrictServiceRel_self h0 A⟩⟩

/-- The relation `weaklyStrictServiceRel beta` offers its own weakly
strict service curve. -/
theorem isWeaklyStrictMinimalServiceCurve_weaklyStrictServiceRel
    (beta : ℝ≥0 → ℝ≥0) :
    IsWeaklyStrictMinimalServiceCurve beta (weaklyStrictServiceRel beta) :=
  fun _ _ hp => hp.2

/-- A weakly strict service curve of a relation with a served pair is
null at the origin: the bound at `t = 0` gives `D 0 + beta 0 ≤ D 0`. -/
theorem IsWeaklyStrictMinimalServiceCurve.zero {beta : ℝ≥0 → ℝ≥0}
    {S : Curve → Curve → Prop}
    (hβ : IsWeaklyStrictMinimalServiceCurve beta S) {A D : Curve}
    (hp : S A D) : beta 0 = 0 := by
  have h := hβ A D hp 0
  rw [show start ⇑A ⇑D 0 = 0 from
      le_antisymm (start_le ⇑A ⇑D 0) zero_le, tsub_self] at h
  have h0 : beta 0 ≤ 0 :=
    le_of_add_le_add_left (a := D 0) (by rwa [add_zero])
  exact le_antisymm h0 zero_le

/-- The zero curve is a weakly strict service curve for every server:
the bound is monotonicity of `D` from the start. -/
theorem isWeaklyStrictMinimalServiceCurve_betaZero
    (S : Curve → Curve → Prop) :
    IsWeaklyStrictMinimalServiceCurve (fun _ => 0) S := by
  intro A D _ t
  show D (start ⇑A ⇑D t) + (0 : ℝ≥0) ≤ D t
  rw [add_zero]
  exact D.mono (start_le ⇑A ⇑D t)

/-- At the zero curve the weakly strict relation collapses to the
causal relation: the start-anchored bound is monotonicity, so only
causality binds. -/
theorem weaklyStrictServiceRel_betaZero :
    weaklyStrictServiceRel (fun _ => 0) = causalRel := by
  funext A D
  exact propext ⟨fun hp => hp.1,
    fun hc => ⟨hc,
      isWeaklyStrictMinimalServiceCurve_betaZero causalRel A D hc⟩⟩

/-- The join `beta ⊔ beta'` of two weakly strict service curves is
offered. -/
theorem IsWeaklyStrictMinimalServiceCurve.sup
    {S : Curve → Curve → Prop} {beta beta' : ℝ≥0 → ℝ≥0}
    (h : IsWeaklyStrictMinimalServiceCurve beta S)
    (h' : IsWeaklyStrictMinimalServiceCurve beta' S) :
    IsWeaklyStrictMinimalServiceCurve (beta ⊔ beta') S := by
  intro A D hp t
  show D (start ⇑A ⇑D t)
      + max (beta (t - start ⇑A ⇑D t)) (beta' (t - start ⇑A ⇑D t))
    ≤ D t
  rcases le_total (beta (t - start ⇑A ⇑D t))
      (beta' (t - start ⇑A ⇑D t)) with hle | hle
  · rw [max_eq_right hle]
    exact h' A D hp t
  · rw [max_eq_left hle]
    exact h A D hp t

/-- Weakly strict service curves are antitone: a smaller `beta` is
still offered. -/
theorem IsWeaklyStrictMinimalServiceCurve.mono
    {S : Curve → Curve → Prop} {beta beta' : ℝ≥0 → ℝ≥0}
    (h : beta ≤ beta') (hβ : IsWeaklyStrictMinimalServiceCurve beta' S) :
    IsWeaklyStrictMinimalServiceCurve beta S :=
  fun A D hp t =>
    le_trans (add_le_add le_rfl (h _)) (hβ A D hp t)

/-- A causal `S` offers the weakly strict `beta` iff its pairs all lie
in `weaklyStrictServiceRel beta`. -/
theorem isWeaklyStrictMinimalServiceCurve_iff_subset
    {S : Curve → Curve → Prop} (hc : IsCausal S) {beta : ℝ≥0 → ℝ≥0} :
    IsWeaklyStrictMinimalServiceCurve beta S ↔
      ∀ A D : Curve, S A D → weaklyStrictServiceRel beta A D := by
  constructor
  · intro h A D hp
    exact ⟨hc A D hp, h A D hp⟩
  · intro h A D hp
    exact (h A D hp).2

/-- The weakly-strict relation is antitone in `beta`. -/
theorem weaklyStrictServiceRel_mono
    {beta beta' : ℝ≥0 → ℝ≥0} (h : beta' ≤ beta) :
    weaklyStrictServiceRel beta ≤ weaklyStrictServiceRel beta' := by
  intro A D hp
  exact ⟨hp.1,
    ((isWeaklyStrictMinimalServiceCurve_weaklyStrictServiceRel beta).mono h)
      A D hp⟩

/-- Weakly strict service is preserved by the non-decreasing closure
`ndClosure`: the start is constant across its own backlogged window,
so each sub-increment anchors at the same start. -/
theorem isWeaklyStrictMinimalServiceCurve_ndClosure
    (beta : ℝ≥0 → ℝ≥0) {S : Curve → Curve → Prop}
    (hβ : IsWeaklyStrictMinimalServiceCurve beta S) :
    IsWeaklyStrictMinimalServiceCurve (ndClosure beta) S := by
  intro A D hp t
  show D (start ⇑A ⇑D t) + ndClosure beta (t - start ⇑A ⇑D t) ≤ D t
  unfold ndClosure
  refine add_ciSup_le _ _ _ (fun q => ?_)
  obtain ⟨u, (hu : u ≤ t - start ⇑A ⇑D t)⟩ := q
  have hsu : start ⇑A ⇑D t + u ≤ t := by
    have h1 : start ⇑A ⇑D t + u
        ≤ start ⇑A ⇑D t + (t - start ⇑A ⇑D t) := by gcongr
    rwa [add_tsub_cancel_of_le (start_le ⇑A ⇑D t)] at h1
  have hb := hβ A D hp (start ⇑A ⇑D t + u)
  rw [start_eq_start_of_le (A.zero_eq D) le_self_add hsu] at hb
  rw [show (start ⇑A ⇑D t + u) - start ⇑A ⇑D t = u by
    rw [add_comm]; exact add_tsub_cancel_right u _] at hb
  exact le_trans hb (D.mono hsu)

/-- Offering `ndClosure beta` weakly strictly is equivalent to
offering `beta`, for `beta` bounded on each `[0, t]`. -/
theorem isWeaklyStrictMinimalServiceCurve_ndClosure_iff
    (beta : ℝ≥0 → ℝ≥0) {S : Curve → Curve → Prop}
    (hbdd : ∀ t, BddAbove
      (Set.range (fun u : {u // u ≤ t} => beta u.1))) :
    IsWeaklyStrictMinimalServiceCurve (ndClosure beta) S ↔
      IsWeaklyStrictMinimalServiceCurve beta S := by
  constructor
  · intro h A D hp t
    exact le_trans
      (by gcongr; exact le_ndClosure beta hbdd (t - start ⇑A ⇑D t))
      (h A D hp t)
  · exact isWeaklyStrictMinimalServiceCurve_ndClosure beta

/-- The weakly strict relation is closure-invariant:
`weaklyStrictServiceRel (ndClosure beta) = weaklyStrictServiceRel
beta` for `beta` bounded on each `[0, t]`. -/
theorem weaklyStrictServiceRel_closure (beta : ℝ≥0 → ℝ≥0)
    (hbdd : ∀ t, BddAbove
      (Set.range (fun u : {u // u ≤ t} => beta u.1))) :
    weaklyStrictServiceRel (ndClosure beta)
      = weaklyStrictServiceRel beta := by
  funext A D
  refine propext ⟨fun hp => ⟨hp.1, ?_⟩, fun hp => ⟨hp.1, ?_⟩⟩
  · exact ((isWeaklyStrictMinimalServiceCurve_weaklyStrictServiceRel
      (ndClosure beta)).mono (fun u => le_ndClosure beta hbdd u))
      A D hp
  · exact (isWeaklyStrictMinimalServiceCurve_ndClosure beta
      (isWeaklyStrictMinimalServiceCurve_weaklyStrictServiceRel beta))
      A D hp

/-- **A strict service curve is weakly strict**: the interval from the
start of the backlogged period of `t` is backlogged, so the strict
increment applies there. -/
theorem IsStrictMinimalServiceCurve.isWeaklyStrictMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0}
    (hβ : IsStrictMinimalServiceCurve beta S) (hc : IsCausal S) :
    IsWeaklyStrictMinimalServiceCurve beta S :=
  fun A D hp t =>
    hβ A D hp (start ⇑A ⇑D t) t (start_le ⇑A ⇑D t)
      (isBacklogged_Ioc_start (fun x => hc A D hp x) t)

/-- Hierarchy, lower inclusion: the strict relation refines the weakly
strict one. -/
theorem strictServiceRel_le_weaklyStrictServiceRel
    (beta : ℝ≥0 → ℝ≥0) :
    strictServiceRel beta ≤ weaklyStrictServiceRel beta := by
  intro A D hp
  exact ⟨hp.1,
    (isStrictMinimalServiceCurve_strictServiceRel
      beta).isWeaklyStrictMinimalServiceCurve (fun _ _ hq => hq.1) A D hp⟩

/-- Output bound: a weakly-strict pair clears the arrivals present at
the start, `A(Start(t)) + β(t − Start(t)) ≤ D(t)`. -/
theorem weaklyStrictServiceRel_output_bound (beta : ℝ≥0 → ℝ≥0)
    (A D : Curve) (hp : weaklyStrictServiceRel beta A D) (t : ℝ≥0) :
    A (start ⇑A ⇑D t) + beta (t - start ⇑A ⇑D t) ≤ D t := by
  rw [A.apply_start_eq D (fun x => hp.1 x) t]
  exact hp.2 t

/-- **A weakly strict service curve is a min-plus service curve**: at
`s = start ⇑A ⇑D t` the output bound gives
`A s + beta (t - s) ≤ D t`, and the split `s + (t - s) = t` bounds the
convolution. -/
theorem IsWeaklyStrictMinimalServiceCurve.isMinimalServiceCurve
    {S : Curve → Curve → Prop} {beta : ℝ≥0 → ℝ≥0}
    (hβ : IsWeaklyStrictMinimalServiceCurve beta S) (hc : IsCausal S) :
    IsMinimalServiceCurve (liftEReal beta) S := by
  intro A D hp t
  have hst : start ⇑A ⇑D t ≤ t := start_le ⇑A ⇑D t
  have hbound : A (start ⇑A ⇑D t) + beta (t - start ⇑A ⇑D t) ≤ D t :=
    weaklyStrictServiceRel_output_bound beta A D
      ⟨hc A D hp, hβ A D hp⟩ t
  calc minConv (curveEReal A) (liftEReal beta) t
      ≤ curveEReal A (start ⇑A ⇑D t)
          + liftEReal beta (t - start ⇑A ⇑D t) :=
        minConv_le_add _ _ (add_tsub_cancel_of_le hst)
    _ ≤ curveEReal D t := by
        simp only [curveEReal_apply]
        exact_mod_cast hbound

/-- Hierarchy, upper inclusion: the weakly strict relation refines the
min-plus one. -/
theorem weaklyStrictServiceRel_le_minimalServiceRel
    (beta : ℝ≥0 → ℝ≥0) :
    weaklyStrictServiceRel beta ≤ minimalServiceRel (liftEReal beta) := by
  intro A D hp
  exact ⟨curveEReal_mono hp.1,
    (isWeaklyStrictMinimalServiceCurve_weaklyStrictServiceRel
      beta).isMinimalServiceCurve (fun _ _ hq => hq.1) A D hp⟩

/-! ## Book restatement (the middle of the service-curve hierarchy)
For every `β`, `S_strict(β) ⊆ S_wstrict(β) ⊆ S_mp(β)` — the two upper
inclusions of the hierarchy theorem (the bottom layer, variable
capacity nodes, is a separate chapter). The min-plus transport of the
strict theory factors through the weakly strict layer verbatim: the
strict hypothesis is only ever used at the start of backlogged
periods. -/
example (beta : ℝ≥0 → ℝ≥0) :
    strictServiceRel beta ≤ weaklyStrictServiceRel beta
      ∧ weaklyStrictServiceRel beta
        ≤ minimalServiceRel (liftEReal beta) :=
  ⟨strictServiceRel_le_weaklyStrictServiceRel beta,
    weaklyStrictServiceRel_le_minimalServiceRel beta⟩

/-! ## Book restatement (conditions of equality — the representable case)
The hierarchy theorem's equality criteria: `S_strict(β) = S_wstrict(β)`
iff `β↑ = δ_T` (`T ∈ ℝ₊ ∪ {+∞}`), and `S_wstrict(β) = S_mp(β)` iff
`β↑ = δ₀` or `0`. The delays `δ_T` (`T < +∞`) and the burst `δ₀` take
the value `+∞`, so the single `ℝ≥0`-valued instance of either
criterion is `β↑ = 0`, i.e. `β = 0` (`ndClosure_eq_zero_iff`): there
the whole hierarchy collapses onto the causal relation, as the book
notes — `S_mp(0) = S_wstrict(0) = {(A, D) ∈ F↑² | A ≥ D}`. The
strictness of the inclusions for nonzero curves is witnessed per
curve (the burst–stall ladder at `β = λ₁`); the book's general
strict-vs-weakly-strict witness rides a `δ₀`-shaped arrival, likewise
not `ℝ≥0`-valued, while its weakly-strict-vs-min-plus witnesses are
finite rate arrivals, representable and deferred. -/
example :
    strictServiceRel (fun _ => 0)
      = weaklyStrictServiceRel (fun _ => 0) := by
  rw [strictServiceRel_betaZero, weaklyStrictServiceRel_betaZero]
example :
    weaklyStrictServiceRel (fun _ => 0)
      = minimalServiceRel (liftEReal (fun _ => 0)) := by
  rw [weaklyStrictServiceRel_betaZero, liftEReal_betaZero,
    minimalServiceRel_betaZero]

end DeepWiki
