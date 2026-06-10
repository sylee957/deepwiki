import Book.ArrivalCurves
import Book.Servers
import Book.ConvolutionReal
import Book.ServersBacklog

/-! # Strict service curves
A strict service curve `β` bounds the output growth on each backlogged period:
`D s + β (t − s) ≤ D t`. This chapter develops the largest strict-service
relation `strictServiceRel β`, its server status, monotonicity, the join, the
output bound, the closure equivalences `Sₛₜᵣᵢ𝒸ₜ(β) = Sₛₜᵣᵢ𝒸ₜ(β↑) =
Sₛₜᵣᵢ𝒸ₜ(β*̄)`, and the maximal length of a backlogged period (bounded by the
first crossing of the arrival curve below `β`). -/

namespace DeepWiki

open Algebra Set Topology Filter
open scoped Classical NNReal ENNReal Algebra.Bridge

/-- `S` offers strict service `beta`: `D s + beta(t-s) ≤ D t` on backlog. -/
def IsStrictMinimalServiceCurve (beta : ℝ≥0 → ℝ≥0)
    (S : Curve → Curve → Prop) : Prop :=
  ∀ A D : Curve, S A D →
    ∀ s t, s ≤ t →
      IsBacklogged A D (Set.Ioc s t) →
        D s + beta (t - s) ≤ D t

/-- Largest causal relation offering strict service `beta`. -/
def strictServiceRel (beta : ℝ≥0 → ℝ≥0) :
    Curve → Curve → Prop :=
  fun A D => D ≤ A ∧
      ∀ s t, s ≤ t →
        IsBacklogged A D (Set.Ioc s t) →
          D s + beta (t - s) ≤ D t

/-- When `beta 0 = 0`, `strictServiceRel beta` is a server: causality is the first
conjunct, and left-totality holds since each input serves itself (its backlogged
period is empty, so the bound is vacuous except at `s = t`, where `beta 0 = 0`). -/
theorem isServer_strictServiceRel {beta : ℝ≥0 → ℝ≥0} (h0 : beta 0 = 0) :
    IsServer (strictServiceRel beta) := by
  refine ⟨fun _ _ hp => hp.1, fun A => ⟨A, (fun _ => le_refl _), ?_⟩⟩
  intro s t hst hbl
  by_cases h : (Set.Ioc s t).Nonempty
  · obtain ⟨u, hu⟩ := h
    exact absurd (hbl u hu) (lt_irrefl _)
  · rw [Set.not_nonempty_iff_eq_empty, Set.Ioc_eq_empty_iff] at h
    have : s = t := le_antisymm hst (not_lt.mp h)
    subst this
    rw [tsub_self, h0, add_zero]

/-- `strictServiceRel beta A D` unfolds to causality plus the strict bound
on backlogged periods. -/
theorem mem_strictServiceRel_iff {beta : ℝ≥0 → ℝ≥0} {A D : Curve} :
    strictServiceRel beta A D ↔
      D ≤ A ∧ ∀ s t, s ≤ t → IsBacklogged A D (Set.Ioc s t) →
        D s + beta (t - s) ≤ D t :=
  Iff.rfl

/-- The relation `strictServiceRel beta` offers its own strict service
curve. -/
theorem isStrictMinimalServiceCurve_strictServiceRel (beta : ℝ≥0 → ℝ≥0) :
    IsStrictMinimalServiceCurve beta (strictServiceRel beta) :=
  fun _ _ hp => hp.2

/-- Strict service curves are antitone: a smaller `beta` is still offered. -/
theorem IsStrictMinimalServiceCurve.mono
    {S : Curve → Curve → Prop} {beta beta' : ℝ≥0 → ℝ≥0}
    (h : beta ≤ beta') (hβ : IsStrictMinimalServiceCurve beta' S) :
    IsStrictMinimalServiceCurve beta S :=
  fun A D hp s t hst hbl =>
    le_trans (add_le_add le_rfl (h _)) (hβ A D hp s t hst hbl)

/-- A causal `S` offers strict service `beta` iff its pairs all lie in
`strictServiceRel beta`. -/
theorem isStrictMinimalServiceCurve_iff_subset
    {S : Curve → Curve → Prop} (hc : IsCausal S) {beta : ℝ≥0 → ℝ≥0} :
    IsStrictMinimalServiceCurve beta S ↔
      ∀ A D : Curve, S A D → strictServiceRel beta A D := by
  constructor
  · intro h A D hp
    exact ⟨hc _ _ hp, h A D hp⟩
  · intro h A D hp
    exact (h A D hp).2

/-- Strict-service relation is antitone in `beta`. -/
theorem strictServiceRel_mono
    {beta beta' : ℝ≥0 → ℝ≥0} (h : beta' ≤ beta) :
    strictServiceRel beta ≤ strictServiceRel beta' := by
  intro A D hp
  exact ⟨hp.1,
    ((isStrictMinimalServiceCurve_strictServiceRel beta).mono h) A D hp⟩

/-- The zero curve `beta₀ ≡ 0` is a strict service curve for every server: the
bound `D s + 0 ≤ D t` is just monotonicity of `D`. -/
theorem isStrictMinimalServiceCurve_betaZero (S : Curve → Curve → Prop) :
    IsStrictMinimalServiceCurve (fun _ => 0) S := by
  intro A D _ s t hst _
  show D s + (0 : ℝ≥0) ≤ D t
  rw [add_zero]
  exact D.mono hst

/-- A strict service curve is null at the origin: `beta 0 = 0`. The strict bound
at `s = t = 0` (the empty period `(0, 0]` is vacuously backlogged) gives
`D 0 + beta 0 ≤ D 0`, hence `beta 0 ≤ 0`. -/
theorem IsStrictMinimalServiceCurve.zero {beta : ℝ≥0 → ℝ≥0} {S : Curve → Curve → Prop}
    (hβ : IsStrictMinimalServiceCurve beta S) {A D : Curve} (hp : S A D) :
    beta 0 = 0 := by
  have hbl : IsBacklogged A D (Set.Ioc 0 0) := by intro u hu; simp at hu
  have h := hβ A D hp 0 0 (le_refl 0) hbl
  rw [tsub_self] at h
  have h0 : beta 0 ≤ 0 :=
    le_of_add_le_add_left (a := D 0) (by rwa [add_zero])
  exact le_antisymm h0 zero_le'

/-- The join `beta ⊔ beta'` of two strict service curves is offered. -/
theorem IsStrictMinimalServiceCurve.sup
    {S : Curve → Curve → Prop} {beta beta' : ℝ≥0 → ℝ≥0}
    (h : IsStrictMinimalServiceCurve beta S)
    (h' : IsStrictMinimalServiceCurve beta' S) :
    IsStrictMinimalServiceCurve (beta ⊔ beta') S := by
  intro A D hp s t hst hbl
  show D s + max (beta (t-s)) (beta' (t-s)) ≤ D t
  rcases le_total (beta (t-s)) (beta' (t-s)) with hle | hle
  · rw [max_eq_right hle]; exact h' A D hp s t hst hbl
  · rw [max_eq_left hle]; exact h A D hp s t hst hbl

/-- Output bound: `A(start) + beta(t - start) ≤ D t` for strict service. -/
theorem strictServiceRel_output_bound (beta : ℝ≥0 → ℝ≥0)
    (A D : Curve)
    (hp : strictServiceRel beta A D)
    (t : ℝ≥0) :
    A (start A D t) + beta (t - start A D t) ≤ D t := by
  have hc : ∀ x, D x ≤ A x := fun x => hp.1 x
  have hbl := isBacklogged_Ioc_start A D hc t
  have hbound := hp.2 (start A D t) t (start_le A D t) hbl
  rw [A_start_eq_D_start A D hc t]
  exact hbound

/-- Concatenating strict-service bounds across `s ≤ r ≤ t`. -/
theorem IsStrictMinimalServiceCurve.concat (beta : ℝ≥0 → ℝ≥0) {S : Curve → Curve → Prop}
    (hβ : IsStrictMinimalServiceCurve beta S)
    (A D : Curve)
    (hp : S A D)
    {s r t : ℝ≥0} (hsr : s ≤ r) (hrt : r ≤ t)
    (hbl : IsBacklogged A D (Set.Ioc s t)) :
    D s + (beta (r - s) + beta (t - r)) ≤ D t := by
  have b1 : D s + beta (r - s) ≤ D r :=
    hβ A D hp s r hsr
      (hbl.subset (Set.Ioc_subset_Ioc_right hrt))
  have b2 : D r + beta (t - r) ≤ D t :=
    hβ A D hp r t hrt
      (hbl.subset (Set.Ioc_subset_Ioc_left hsr))
  calc D s + (beta (r - s) + beta (t - r))
      = (D s + beta (r - s)) + beta (t - r) := by
        ring
    _ ≤ D r + beta (t - r) := by gcongr
    _ ≤ D t := b2

/-- Strict service is preserved by the non-decreasing closure `ndClosure`. -/
theorem isStrictMinimalServiceCurve_ndClosure
    (beta : ℝ≥0 → ℝ≥0) {S : Curve → Curve → Prop}
    (hβ : IsStrictMinimalServiceCurve beta S) :
    IsStrictMinimalServiceCurve (ndClosure beta) S := by
  intro A D hp s t hst hbl
  show D s + ndClosure beta (t - s) ≤ D t
  unfold ndClosure
  refine add_ciSup_le _ _ _ (fun q => ?_)
  obtain ⟨u, (hu : u ≤ t - s)⟩ := q
  have hsu : s + u ≤ t := by
    have : s + u ≤ s + (t - s) := by gcongr
    rwa [add_tsub_cancel_of_le hst] at this
  have hb := hβ A D hp s (s + u) le_self_add
    (hbl.subset (Set.Ioc_subset_Ioc_right hsu))
  rw [show (s + u) - s = u by
      rw [add_comm]; exact add_tsub_cancel_right u s] at hb
  exact le_trans hb (D.mono hsu)

/-- Offering `ndClosure beta` is equivalent to offering `beta` (when bdd). -/
theorem isStrictMinimalServiceCurve_ndClosure_iff
    (beta : ℝ≥0 → ℝ≥0) {S : Curve → Curve → Prop}
    (hbdd : ∀ t, BddAbove
      (Set.range (fun u : {u // u ≤ t} => beta u.1))) :
    IsStrictMinimalServiceCurve (ndClosure beta) S ↔
      IsStrictMinimalServiceCurve beta S := by
  constructor
  · intro h A D hp s t hst hbl
    exact le_trans
      (by gcongr; exact le_ndClosure beta hbdd (t - s))
      (h A D hp s t hst hbl)
  · exact isStrictMinimalServiceCurve_ndClosure beta

/-- Strict service is preserved by the max-plus self-convolution. -/
theorem isStrictMinimalServiceCurve_maxConvProj
    (beta : ℝ≥0 → ℝ≥0) {S : Curve → Curve → Prop}
    (hβ : IsStrictMinimalServiceCurve beta S) :
    IsStrictMinimalServiceCurve (maxConvProj beta beta) S := by
  intro A D hp s t hst hbl
  show D s + maxConvProj beta beta (t - s) ≤ D t
  refine add_maxConvProj_le _ _ _ _ (fun q => ?_)
  obtain ⟨⟨a, b⟩, (hab : a + b = t - s)⟩ := q
  have hsum : s + (a + b) = t := by
    rw [hab, add_tsub_cancel_of_le hst]
  have hsa : s + a ≤ t :=
    le_trans (by gcongr; exact le_self_add) hsum.le
  have hrs : (s + a) - s = a := by
    rw [add_comm]; exact add_tsub_cancel_right a s
  have htr : t - (s + a) = b := by
    rw [← hsum,
      show s + (a + b) = (s + a) + b by ring,
      add_tsub_cancel_left]
  have hcc :=
    IsStrictMinimalServiceCurve.concat beta hβ A D hp le_self_add hsa hbl
  rw [hrs, htr] at hcc
  exact hcc

/-- Strict service is preserved by every max-plus convolution power. -/
theorem isStrictMinimalServiceCurve_maxConvProjPow (beta : ℝ≥0 → ℝ≥0)
    {S : Curve → Curve → Prop} (hβ : IsStrictMinimalServiceCurve beta S)
    (n : ℕ) :
    IsStrictMinimalServiceCurve (maxConvProjPow beta n) S := by
  induction n with
  | zero => exact hβ
  | succ n ih => exact isStrictMinimalServiceCurve_maxConvProj _ ih

/-- Strict service is preserved by the super-additive closure
`superadditiveClosureMax`. -/
theorem isStrictMinimalServiceCurve_superadditiveClosureMax
    (beta : ℝ≥0 → ℝ≥0) {S : Curve → Curve → Prop}
    (hβ : IsStrictMinimalServiceCurve beta S) :
    IsStrictMinimalServiceCurve (superadditiveClosureMax beta) S := by
  intro A D hp s t hst hbl
  show D s + superadditiveClosureMax beta (t - s) ≤ D t
  unfold superadditiveClosureMax
  refine add_ciSup_le _ _ _ (fun n => ?_)
  exact isStrictMinimalServiceCurve_maxConvProjPow beta hβ n A D hp s t hst hbl

/-- Offering `superadditiveClosureMax beta` is equivalent to offering `beta` (when bdd). -/
theorem isStrictMinimalServiceCurve_superadditiveClosureMax_iff
    (beta : ℝ≥0 → ℝ≥0) {S : Curve → Curve → Prop}
    (hbdd : ∀ t, BddAbove
      (Set.range (fun n => maxConvProjPow beta n t))) :
    IsStrictMinimalServiceCurve (superadditiveClosureMax beta) S ↔
      IsStrictMinimalServiceCurve beta S := by
  constructor
  · intro h A D hp s t hst hbl
    exact le_trans
      (by gcongr; exact le_superadditiveClosureMax beta hbdd (t - s))
      (h A D hp s t hst hbl)
  · exact isStrictMinimalServiceCurve_superadditiveClosureMax beta

/-- Offering `beta`, its non-decreasing closure `ndClosure beta`, and its
super-additive closure `superadditiveClosureMax beta` are all equivalent:
`Sₛₜᵣᵢ𝒸ₜ(β) = Sₛₜᵣᵢ𝒸ₜ(β↑) = Sₛₜᵣᵢ𝒸ₜ(β*̄)`. -/
theorem isStrictMinimalServiceCurve_closures_iff
    (beta : ℝ≥0 → ℝ≥0) {S : Curve → Curve → Prop}
    (hbddNd : ∀ t, BddAbove
      (Set.range (fun u : {u // u ≤ t} => beta u.1)))
    (hbddSup : ∀ t, BddAbove
      (Set.range (fun n => maxConvProjPow beta n t))) :
    (IsStrictMinimalServiceCurve beta S ↔
        IsStrictMinimalServiceCurve (ndClosure beta) S) ∧
      (IsStrictMinimalServiceCurve beta S ↔
        IsStrictMinimalServiceCurve (superadditiveClosureMax beta) S) :=
  ⟨(isStrictMinimalServiceCurve_ndClosure_iff beta hbddNd).symm,
    (isStrictMinimalServiceCurve_superadditiveClosureMax_iff beta hbddSup).symm⟩

/-- Closure equivalence under the interpretable hypothesis that `beta` has some
affine rate bound `∃ r, ∀ s, beta s ≤ r * s`: this discharges both boundedness
conditions (`beta` is then bounded by `r * t` on `[0, t]`, and its
self-convolution iterates stay below `r * ·`), giving
`Sₛₜᵣᵢ𝒸ₜ(β) = Sₛₜᵣᵢ𝒸ₜ(β↑) = Sₛₜᵣᵢ𝒸ₜ(β*̄)`. Unlike super-additivity, this allows a
nontrivial closure. -/
theorem isStrictMinimalServiceCurve_closures_iff_of_affine_bound
    (beta : ℝ≥0 → ℝ≥0) {S : Curve → Curve → Prop}
    (hr : ∃ r : ℝ≥0, ∀ s, beta s ≤ r * s) :
    (IsStrictMinimalServiceCurve beta S ↔
        IsStrictMinimalServiceCurve (ndClosure beta) S) ∧
      (IsStrictMinimalServiceCurve beta S ↔
        IsStrictMinimalServiceCurve (superadditiveClosureMax beta) S) := by
  obtain ⟨r, hr⟩ := hr
  refine isStrictMinimalServiceCurve_closures_iff beta (fun t => ?_) (fun t => ?_)
  · exact ⟨r * t, by rintro x ⟨⟨u, hu⟩, rfl⟩; exact le_trans (hr u) (by gcongr)⟩
  · exact bddAbove_range_maxConvProjPow_of_affine_bound hr t

/-! ## Maximal length of a backlogged period -/

/-- On a backlogged period `(t, t + d]` of a causal pair with strict service
`beta` whose arrival admits maximal arrival curve `alpha`, the service curve
sits strictly below the arrival curve at every positive length `d' ≤ d`:
`beta d' < alpha d'`. -/
theorem beta_lt_alpha_of_isBacklogged
    {S : Curve → Curve → Prop} {beta alpha : ℝ≥0 → ℝ≥0}
    (hc : IsCausal S) (hβ : IsStrictMinimalServiceCurve beta S)
    {A D : Curve} (hp : S A D)
    (harr : IsMaximalArrivalCurve (⇑A) alpha)
    {t d : ℝ≥0} (hbl : IsBacklogged A D (Set.Ioc t (t + d)))
    {d' : ℝ≥0} (hd' : 0 < d') (hle : d' ≤ d) :
    beta d' < alpha d' := by
  have hcAD : ∀ x, D x ≤ A x := hc A D hp
  set s := start A D (t + d)
  have heq : A s = D s := A_start_eq_D_start A D hcAD (t + d)
  -- the start lies at or before `t`: no equality point inside the backlog
  have hst : s ≤ t := start_le_of_isBacklogged A D hbl
  -- `s + d'` stays inside the backlogged period from the start
  have hmem : s + d' ∈ Set.Ioc s (t + d) :=
    ⟨lt_add_of_pos_right s hd', add_le_add hst hle⟩
  have hbacklog : D (s + d') < A (s + d') :=
    isBacklogged_Ioc_start A D hcAD (t + d) (s + d') hmem
  -- strict service on `(s, s + d']`
  have hserv : D s + beta d' ≤ D (s + d') := by
    have := hβ A D hp s (s + d') le_self_add
      ((isBacklogged_Ioc_start A D hcAD (t + d)).subset
        (Set.Ioc_subset_Ioc_right hmem.2))
    rwa [add_tsub_cancel_left] at this
  -- arrival increment and `A = D` at the start close the chain
  have hchain : A s + beta d' < A s + alpha d' :=
    calc A s + beta d' = D s + beta d' := by rw [heq]
      _ ≤ D (s + d') := hserv
      _ < A (s + d') := hbacklog
      _ ≤ A s + alpha d' :=
          (isMaximalArrivalCurve_iff_increment (⇑A) alpha).mp harr s d'
  exact lt_of_add_lt_add_left hchain

/-- A positive crossing point `alpha d₀ ≤ beta d₀` bounds every backlogged
period of a causal pair with strict service `beta`: backlog on `(t, t + d]`
forces the length `d < d₀`. -/
theorem length_lt_crossing_of_isBacklogged
    {S : Curve → Curve → Prop} {beta alpha : ℝ≥0 → ℝ≥0}
    (hc : IsCausal S) (hβ : IsStrictMinimalServiceCurve beta S)
    {A D : Curve} (hp : S A D)
    (harr : IsMaximalArrivalCurve (⇑A) alpha)
    {t d : ℝ≥0} (hbl : IsBacklogged A D (Set.Ioc t (t + d)))
    {d₀ : ℝ≥0} (hd₀ : 0 < d₀) (hcross : alpha d₀ ≤ beta d₀) :
    d < d₀ := by
  by_contra h
  rw [not_lt] at h
  exact absurd hcross (not_le.mpr
    (beta_lt_alpha_of_isBacklogged hc hβ hp harr hbl hd₀ h))

/-- **Maximal length of a backlogged period.** Every backlogged period
`(t, t + d]` of a causal pair with strict service `beta` whose arrival
admits maximal arrival curve `alpha` has length at most the first crossing
`firstCrossing alpha beta` (`⊤` in `ℝ≥0∞` when the curves never cross). -/
theorem length_le_firstCrossing_of_isBacklogged
    {S : Curve → Curve → Prop} {beta alpha : ℝ≥0 → ℝ≥0}
    (hc : IsCausal S) (hβ : IsStrictMinimalServiceCurve beta S)
    {A D : Curve} (hp : S A D)
    (harr : IsMaximalArrivalCurve (⇑A) alpha)
    {t d : ℝ≥0} (hbl : IsBacklogged A D (Set.Ioc t (t + d))) :
    (d : ℝ≥0∞) ≤ firstCrossing alpha beta :=
  le_firstCrossing fun _ hx => ENNReal.coe_le_coe.mpr
    (length_lt_crossing_of_isBacklogged hc hβ hp harr hbl hx.1 hx.2).le

/-! ## Book restatement (maximal length of a backlogged period)
A server `S ⊆ Sₛₜᵣᵢ𝒸ₜ(beta)` whose arrival `A` admits maximal arrival
curve `alpha` has every backlogged period of length at most
`ℓmax = inf {x > 0 | alpha x ≤ beta x} = firstCrossing alpha beta`. -/
example {S : Curve → Curve → Prop} {beta alpha : ℝ≥0 → ℝ≥0}
    (hSrv : IsServer S) (hβ : IsStrictMinimalServiceCurve beta S)
    {A D : Curve} (hp : S A D)
    (harr : IsMaximalArrivalCurve (⇑A) alpha)
    {t d : ℝ≥0} (hbl : IsBacklogged A D (Set.Ioc t (t + d))) :
    (d : ℝ≥0∞) ≤ firstCrossing alpha beta :=
  length_le_firstCrossing_of_isBacklogged hSrv.1 hβ hp harr hbl

end DeepWiki
