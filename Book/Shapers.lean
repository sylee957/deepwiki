import Book.Servers
import Book.Closures
import Book.RealConvolution
import Book.ServiceCurveBacklog

/-! # Shapers
Greedy shapers and shaping curves in network calculus,
built on the convolution/closure dioid theory. -/

namespace DeepWiki

open Algebra Set Topology Filter
open scoped Classical NNReal ENNReal Algebra.Bridge

/-- `conv` is monotone in its right argument. -/
theorem conv_mono_right (D : Fmin) {sigma sigma' : Fmin}
    (h : sigma ≤ sigma') :
    conv D sigma ≤ conv D sigma' := by
  intro t
  rw [conv_apply]
  refine CompleteDioid.sSup_le _ _ ?_
  rintro x ⟨u, s, hus, rfl⟩
  rw [conv_apply]
  refine le_trans ?_
    (CompleteDioid.le_sSup _ _
      ⟨u, s, hus, rfl⟩)
  exact mul_le_mul_left (h s) (D u)

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

/-- Every curve pair of `S` lies in `strictServiceRel beta` iff `S` offers strict
service `beta`. -/
theorem subset_strictServiceRel_iff
    {S : Curve → Curve → Prop} (hSrv : IsServer S) {beta : ℝ≥0 → ℝ≥0} :
    (∀ A D : Curve, S A D →
        strictServiceRel beta A D) ↔
      IsStrictMinimalServiceCurve beta S := by
  constructor
  · intro h A D hp
    exact (h A D hp).2
  · intro h A D hp
    exact ⟨hSrv.1 _ _ hp, h A D hp⟩

/-- Strict-service relation is antitone in `beta`. -/
theorem strictServiceRel_mono
    {beta beta' : ℝ≥0 → ℝ≥0} (h : beta' ≤ beta) :
    strictServiceRel beta ≤ strictServiceRel beta' := by
  intro A D hp
  refine ⟨hp.1, fun s t hst hbl => ?_⟩
  refine le_trans ?_ (hp.2 s t hst hbl)
  gcongr
  exact h _

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
theorem strictServiceCurve_zero {beta : ℝ≥0 → ℝ≥0} {S : Curve → Curve → Prop}
    (hβ : IsStrictMinimalServiceCurve beta S) {A D : Curve} (hp : S A D) :
    beta 0 = 0 := by
  have hbl : IsBacklogged A D (Set.Ioc 0 0) := by intro u hu; simp at hu
  have h := hβ A D hp 0 0 (le_refl 0) hbl
  rw [tsub_self] at h
  have h0 : beta 0 ≤ 0 :=
    le_of_add_le_add_left (a := D 0) (by rwa [add_zero])
  exact le_antisymm h0 zero_le'

/-- The join `beta ⊔ beta'` of two strict service curves is offered. -/
theorem isStrictMinimalServiceCurve_sup
    {S : Curve → Curve → Prop} {beta beta' : ℝ≥0 → ℝ≥0}
    (h : IsStrictMinimalServiceCurve beta S)
    (h' : IsStrictMinimalServiceCurve beta' S) :
    IsStrictMinimalServiceCurve (beta ⊔ beta') S := by
  intro A D hp s t hst hbl
  show D s + max (beta (t-s)) (beta' (t-s)) ≤ D t
  rcases le_total (beta (t-s)) (beta' (t-s)) with hle | hle
  · rw [max_eq_right hle]; exact h' A D hp s t hst hbl
  · rw [max_eq_left hle]; exact h A D hp s t hst hbl

/-- Output bound: `A(Start) + beta(t - Start) ≤ D t` for strict service. -/
theorem strictService_output_bound (beta : ℝ≥0 → ℝ≥0)
    (A D : Curve)
    (hp : strictServiceRel beta A D)
    (t : ℝ≥0) :
    A (Start A D t) + beta (t - Start A D t) ≤ D t := by
  have hc : ∀ x, D x ≤ A x := fun x => hp.1 x
  have hbl := isBacklogged_Ioc_start A D hc t
  have hbound := hp.2 (Start A D t) t (start_le A D t) hbl
  rw [A_start_eq_D_start A D hc t]
  exact hbound

/-- Concatenating strict-service bounds across `s ≤ r ≤ t`. -/
theorem strict_concat (beta : ℝ≥0 → ℝ≥0) {S : Curve → Curve → Prop}
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
    strict_concat beta hβ A D hp le_self_add hsa hbl
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
`superAdditiveClosureMax`. -/
theorem isStrictMinimalServiceCurve_superAdditiveClosureMax
    (beta : ℝ≥0 → ℝ≥0) {S : Curve → Curve → Prop}
    (hβ : IsStrictMinimalServiceCurve beta S) :
    IsStrictMinimalServiceCurve (superAdditiveClosureMax beta) S := by
  intro A D hp s t hst hbl
  show D s + superAdditiveClosureMax beta (t - s) ≤ D t
  unfold superAdditiveClosureMax
  refine add_ciSup_le _ _ _ (fun n => ?_)
  exact isStrictMinimalServiceCurve_maxConvProjPow beta hβ n A D hp s t hst hbl

/-- Offering `superAdditiveClosureMax beta` is equivalent to offering `beta` (when bdd). -/
theorem isStrictMinimalServiceCurve_superAdditiveClosureMax_iff
    (beta : ℝ≥0 → ℝ≥0) {S : Curve → Curve → Prop}
    (hbdd : ∀ t, BddAbove
      (Set.range (fun n => maxConvProjPow beta n t))) :
    IsStrictMinimalServiceCurve (superAdditiveClosureMax beta) S ↔
      IsStrictMinimalServiceCurve beta S := by
  constructor
  · intro h A D hp s t hst hbl
    exact le_trans
      (by gcongr; exact le_superAdditiveClosureMax beta hbdd (t - s))
      (h A D hp s t hst hbl)
  · exact isStrictMinimalServiceCurve_superAdditiveClosureMax beta

/-- Offering `beta`, its non-decreasing closure `ndClosure beta`, and its
super-additive closure `superAdditiveClosureMax beta` are all equivalent:
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
        IsStrictMinimalServiceCurve (superAdditiveClosureMax beta) S) :=
  ⟨(isStrictMinimalServiceCurve_ndClosure_iff beta hbddNd).symm,
    (isStrictMinimalServiceCurve_superAdditiveClosureMax_iff beta hbddSup).symm⟩

/-- Under an affine bound `beta s ≤ r * s`, each self-convolution iterate stays
below `r * ·`: `maxConvProjPow beta n t ≤ r * t`, since `r * a + r * b = r * t`
on any split `a + b = t`. -/
theorem maxConvProjPow_le_of_affine_bound {beta : ℝ≥0 → ℝ≥0} {r : ℝ≥0}
    (hr : ∀ s, beta s ≤ r * s) (n : ℕ) (t : ℝ≥0) :
    maxConvProjPow beta n t ≤ r * t := by
  induction n generalizing t with
  | zero => exact hr t
  | succ n ih =>
    show maxConvProj (maxConvProjPow beta n) (maxConvProjPow beta n) t ≤ r * t
    refine maxConvProj_le _ _ t (r * t) (fun p => ?_)
    obtain ⟨⟨a, b⟩, (hab : a + b = t)⟩ := p
    calc maxConvProjPow beta n a + maxConvProjPow beta n b
        ≤ r * a + r * b := add_le_add (ih a) (ih b)
      _ = r * (a + b) := (mul_add r a b).symm
      _ = r * t := by rw [hab]

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
        IsStrictMinimalServiceCurve (superAdditiveClosureMax beta) S) := by
  obtain ⟨r, hr⟩ := hr
  refine isStrictMinimalServiceCurve_closures_iff beta (fun t => ?_) (fun t => ?_)
  · exact ⟨r * t, by rintro x ⟨⟨u, hu⟩, rfl⟩; exact le_trans (hr u) (by gcongr)⟩
  · exact ⟨r * t, by
      rintro x ⟨n, rfl⟩; exact maxConvProjPow_le_of_affine_bound hr n t⟩

/-- `sigma` is an arrival curve for `D`: `D ∗ sigma ≤ D`. -/
def AllowsArrivalCurve (D sigma : Fmin) : Prop :=
  conv D sigma ≤ D

/-- Arrival-curve constraint, kernelized: `D u ⊗ sigma s ≼ D t` for `u+s=t`. -/
theorem allowsArrivalCurve_iff_kernel
    (D sigma : Fmin) :
    AllowsArrivalCurve D sigma ↔
      ∀ u s t, u + s = t →
        D u ⊗ₒ sigma s ≼ₒ D t := by
  constructor
  · intro h u s t hus
    have hc : conv D sigma t ≼ₒ D t := h t
    have hterm :
        D u ⊗ₒ sigma s ≼ₒ conv D sigma t := by
      rw [conv_apply]
      exact CompleteDioid.le_sSup _ _
        ⟨u, s, hus, rfl⟩
    exact le_trans hterm hc
  · intro h t
    rw [conv_apply]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, s, hus, rfl⟩
    exact h u s t hus

/-- `S` is a shaper for `sigma`: every output allows arrival curve `sigma`. -/
def IsShaper (S : Curve → Curve → Prop) (sigma : Fmin) : Prop :=
  ∀ A D : Curve, S A D → AllowsArrivalCurve (toFmin D) sigma

/-- Largest causal relation that shapes outputs to arrival curve `sigma`. -/
def shaperRel (sigma : Fmin) : Curve → Curve → Prop :=
  fun A D => D ≤ A ∧
      AllowsArrivalCurve (toFmin D) sigma

/-- `shaperRel sigma A D` unfolds to causality and the arrival-curve bound. -/
theorem mem_shaperRel_iff
    {sigma : Fmin} {A D : Curve} :
    shaperRel sigma A D ↔
      D ≤ A ∧
        AllowsArrivalCurve (toFmin D) sigma :=
  Iff.rfl

/-- `shaperRel sigma` is a server: causality is the first conjunct, and
left-totality is the supplied witness `htot`. -/
theorem isServer_shaperRel (sigma : Fmin)
    (htot : ∀ A : Curve, ∃ D : Curve,
      shaperRel sigma A D) :
    IsServer (shaperRel sigma) :=
  ⟨fun _ _ hp => hp.1, htot⟩

/-- `S ≤ shaperRel sigma` iff `S` is a shaper for `sigma` on curve pairs. -/
theorem subset_shaperRel_iff
    {S : Curve → Curve → Prop} (hSrv : IsServer S) {sigma : Fmin} :
    (∀ A D : Curve, S A D →
        shaperRel sigma A D) ↔
      (∀ A D : Curve, S A D →
        AllowsArrivalCurve (toFmin D) sigma) := by
  constructor
  · intro h A D hp
    exact (h A D hp).2
  · intro h A D hp
    exact ⟨hSrv.1 _ _ hp, h A D hp⟩

/-- `sigma ≤ sigma⋆`: a curve is below its sub-additive closure. -/
theorem self_le_subadditiveClosure
    (sigma : Fmin) : sigma ≤ sigma⋆ := by
  intro t
  dsimp [subadditiveClosure]
  have h1 :
      convPow sigma 1 t ≼ₒ
        CompleteDioid.iSup
          (fun n : ℕ => convPow sigma n t) :=
    CompleteDioid.le_iSup
      (fun n : ℕ => convPow sigma n t) 1
  simpa [convPow_one] using h1

/-- Kernel inequality holds for the convolution unit `convUnit`. -/
theorem kernel_convUnit (D : Fmin) :
    ∀ u s t, u + s = t →
      D u ⊗ₒ convUnit s ≼ₒ D t := by
  intro u s t hus
  by_cases hs : s = 0
  · have hu : u = t := by
      rw [← hus, hs, add_zero]
    rw [convUnit, if_pos hs, hu]
    exact le_of_eq
      (Algebra.MulMonoid.otimes_one (D t))
  · rw [convUnit, if_neg hs]
    rw [Algebra.Semiring.otimes_eps]
    exact bot_le

/-- If `D` allows `sigma`, the kernel bound holds for every power `sigmaⁿ`. -/
theorem kernel_convPow_of_allows
    {D sigma : Fmin}
    (hD : AllowsArrivalCurve D sigma) :
    ∀ n u s t, u + s = t →
      D u ⊗ₒ convPow sigma n s ≼ₒ D t := by
  have hsigma :=
    (allowsArrivalCurve_iff_kernel D sigma).mp hD
  intro n
  induction n with
  | zero =>
      exact kernel_convUnit D
  | succ n ih =>
      intro u s t hus
      rw [convPow, conv_apply,
        CompleteDioid.mul_sSup]
      refine CompleteDioid.sSup_le _ _ ?_
      rintro x ⟨y, ⟨a, b, hab, rfl⟩, rfl⟩
      change D u ⊗ₒ
          (convPow sigma n a ⊗ₒ sigma b) ≼ₒ D t
      rw [← Algebra.MulMonoid.otimes_assoc]
      have hleft :
          (D u ⊗ₒ convPow sigma n a) ⊗ₒ
              sigma b ≼ₒ
            D (u + a) ⊗ₒ sigma b :=
        mul_le_mul_right (ih u a (u + a) rfl)
          (sigma b)
      have hsum : (u + a) + b = t := by
        rw [add_assoc, hab, hus]
      exact le_trans hleft
        (hsigma (u + a) b t hsum)

/-- `D` allows `sigma⋆` iff it allows `sigma`. -/
theorem allowsArrivalCurve_closure_iff
    (D sigma : Fmin) :
    AllowsArrivalCurve D sigma⋆ ↔
      AllowsArrivalCurve D sigma := by
  constructor
  · intro h
    exact le_trans
      (conv_mono_right D
        (self_le_subadditiveClosure sigma)) h
  · intro h
    rw [allowsArrivalCurve_iff_kernel]
    intro u s t hus
    rw [subadditiveClosure,
      CompleteDioid.mul_iSup]
    refine CompleteDioid.iSup_le _ _ ?_
    intro n
    exact kernel_convPow_of_allows h n u s t hus

/-- A shaper for `sigma` equals one for its closure: `shaperRel sigma = shaperRel sigma⋆`. -/
theorem shaperRel_closure
    (sigma : Fmin) :
    shaperRel sigma = shaperRel sigma⋆ := by
  funext A D
  apply propext
  constructor
  · intro hp
    exact ⟨hp.1,
      (allowsArrivalCurve_closure_iff
        (toFmin D) sigma).2 hp.2⟩
  · intro hp
    exact ⟨hp.1,
      (allowsArrivalCurve_closure_iff
        (toFmin D) sigma).1 hp.2⟩

/-- A shaper for `sigma` is also a shaper for `sigma⋆`. -/
theorem IsShaper.closure
    {S : Curve → Curve → Prop} {sigma : Fmin}
    (hS : IsShaper S sigma) :
    IsShaper S sigma⋆ := by
  intro A D hp
  exact (allowsArrivalCurve_closure_iff
    (toFmin D) sigma).2 (hS A D hp)

example
    (sigma : Fmin) :
    shaperRel sigma = shaperRel sigma⋆ :=
  shaperRel_closure sigma

example
    {S : Curve → Curve → Prop} {sigma : Fmin}
    (hS : IsShaper S sigma) :
    IsShaper S sigma⋆ :=
  IsShaper.closure hS

/-- A shaper for `sigma` is a shaper for any smaller `sigma' ≤ sigma`. -/
theorem IsShaper.of_le
    {S : Curve → Curve → Prop}
    {sigma sigma' : Fmin}
    (hS : IsShaper S sigma)
    (h : sigma' ≤ sigma) :
    IsShaper S sigma' := by
  intro A D hp
  exact le_trans
    (conv_mono_right (toFmin D) h) (hS A D hp)

/-- `shaperRel` is antitone in `sigma`. -/
theorem shaperRel_mono
    {sigma sigma' : Fmin}
    (h : sigma' ≤ sigma) :
    shaperRel sigma ≤ shaperRel sigma' := by
  intro A D hp
  exact ⟨hp.1,
    le_trans
      (conv_mono_right (toFmin D) h) hp.2⟩

example
    {sigma sigma' : Fmin}
    (h : sigma' ≤ sigma) :
    shaperRel sigma ≤ shaperRel sigma' :=
  shaperRel_mono h

example
    {S : Curve → Curve → Prop} {sigma sigma' : Fmin}
    (hS : IsShaper S sigma)
    (h : sigma' ≤ sigma) :
    IsShaper S sigma' :=
  IsShaper.of_le hS h

/-- `S` is a greedy shaper for `sigma`: every output is `A ∗ sigma`. -/
def IsGreedyShaper
    (S : Curve → Curve → Prop) (sigma : Fmin) : Prop :=
  ∀ A D : Curve, S A D → toFmin D = conv (toFmin A) sigma

/-- If `sigma 0 = eₒ` then `A ≼ A ∗ sigma` in the dioid order. -/
theorem self_le_conv_of_zeroAtOrigin
    (A sigma : Fmin) (h0 : sigma 0 = eₒ) :
    A ≤ conv A sigma := by
  intro t
  show A t ≼ₒ conv A sigma t
  rw [conv_apply]
  refine le_trans ?_
    (CompleteDioid.le_sSup _ _
      ⟨t, 0, add_zero t, rfl⟩)
  show A t ≼ₒ A t ⊗ₒ sigma 0
  rw [h0]
  exact le_of_eq (MulMonoid.otimes_one (A t)).symm

/-- Greedy-shaper relation: outputs are exactly `A ∗ sigma`. -/
def greedyRel (sigma : Fmin) : Curve → Curve → Prop :=
  fun A D => toFmin D = conv (toFmin A) sigma

/-- `greedyRel sigma A D` unfolds to `toFmin D = A ∗ sigma`. -/
theorem mem_greedyRel_iff
    {sigma : Fmin} {A D : Curve} :
    greedyRel sigma A D ↔
      toFmin D = conv (toFmin A) sigma :=
  Iff.rfl

/-- When `sigma 0 = eₒ`, `greedyRel sigma` is a server: causality follows from
`A ≼ A ∗ sigma`, and left-totality is the supplied witness `htot`. -/
theorem isServer_greedyRel
    (sigma : Fmin) (h0 : sigma 0 = eₒ)
    (htot : ∀ A : Curve, ∃ D : Curve,
      greedyRel sigma A D) :
    IsServer (greedyRel sigma) :=
  ⟨fun A D hp => by
      rw [le_iff_toFmin]
      rw [(hp : toFmin D = conv (toFmin A) sigma)]
      exact self_le_conv_of_zeroAtOrigin (toFmin A) sigma h0,
    htot⟩

/-- `IsGreedyShaper S sigma` iff `S ≤ greedyRel sigma`. -/
theorem isGreedyShaper_iff_subset
    {S : Curve → Curve → Prop} {sigma : Fmin} :
    IsGreedyShaper S sigma ↔
      ∀ A D : Curve, S A D → greedyRel sigma A D :=
  Iff.rfl

/-- `sigma` is sub-additive: `sigma u ⊗ sigma s ≼ sigma (u + s)`. -/
def IsSubadditiveF (sigma : Fmin) : Prop :=
  ∀ u s : ℝ≥0, sigma u ⊗ₒ sigma s ≼ₒ sigma (u + s)

/-- A sub-additive `sigma` allows itself as an arrival curve. -/
theorem allowsArrivalCurve_self_of_subadd
    {sigma : Fmin} (hsub : IsSubadditiveF sigma) :
    AllowsArrivalCurve sigma sigma := by
  rw [allowsArrivalCurve_iff_kernel]
  intro u s t hus
  rw [← hus]
  exact hsub u s

/-- For sub-additive `sigma`, `A ∗ sigma` allows arrival curve `sigma`. -/
theorem allowsArrivalCurve_conv_of_subadd
    (A : Fmin) {sigma : Fmin}
    (hsub : IsSubadditiveF sigma) :
    AllowsArrivalCurve (conv A sigma) sigma := by
  have h : conv A (conv sigma sigma) ≤ conv A sigma :=
    conv_mono_right A
      (allowsArrivalCurve_self_of_subadd hsub)
  show conv (conv A sigma) sigma ≤ conv A sigma
  rw [conv_assoc]
  exact h

/-- A greedy shaper for sub-additive `sigma` is a shaper for `sigma`. -/
theorem IsGreedyShaper.isShaper
    {S : Curve → Curve → Prop} {sigma : Fmin}
    (hsub : IsSubadditiveF sigma)
    (hS : IsGreedyShaper S sigma) :
    IsShaper S sigma := by
  intro A D hp
  rw [hS A D hp]
  exact allowsArrivalCurve_conv_of_subadd (toFmin A) hsub

end DeepWiki
