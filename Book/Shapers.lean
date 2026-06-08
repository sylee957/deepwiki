import Book.Servers
import Book.Closures
import Book.RealConvolution

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

/-- `S` offers min-plus service curve `beta`: `beta ∗ A ≤ D`. -/
def OffersMinPlusService (beta : ℝ≥0 → ℝ≥0) (S : Server) :
    Prop :=
  ∀ A D : Curve, (A, D) ∈ S → minConvProj A beta ≤ D

/-- `S` is a min-plus server for `beta` (offers it as service). -/
def IsMinPlusServer (beta : ℝ≥0 → ℝ≥0) (S : Server) :
    Prop :=
  OffersMinPlusService beta S

/-- Largest causal relation offering min-plus service `beta`. -/
def minPlusServiceRel (beta : ℝ≥0 → ℝ≥0) :
    Set (Curve × Curve) :=
  { p | p.2 ≤ p.1 ∧ minConvProj p.1 beta ≤ p.2 }

/-- Membership unfolding for `minPlusServiceRel`. -/
theorem mem_minPlusServiceRel_iff
    {beta : ℝ≥0 → ℝ≥0} {p : Curve × Curve} :
    p ∈ minPlusServiceRel beta ↔
      p.2 ≤ p.1 ∧ minConvProj p.1 beta ≤ p.2 :=
  Iff.rfl

/-- The server built from `minPlusServiceRel beta`. -/
def minPlusServer (beta : ℝ≥0 → ℝ≥0)
    (htot : ∀ A : Curve, ∃ D : Curve,
      (A, D) ∈ minPlusServiceRel beta) :
    Server where
  rel := minPlusServiceRel beta
  causal _A _D hp := hp.1
  leftTotal A := htot A

/-- `S ⊆ minPlusServiceRel beta` iff `S` offers service `beta`. -/
theorem subset_minPlusServiceRel_iff
    {S : Server} {beta : ℝ≥0 → ℝ≥0} :
    (∀ p ∈ S, p ∈ minPlusServiceRel beta) ↔
      OffersMinPlusService beta S := by
  constructor
  · intro h A D hp
    exact (h (A, D) hp).2
  · intro h p hp
    exact ⟨S.causal p.1 p.2 hp, h p.1 p.2 hp⟩

/-- Service curves are antitone: smaller `beta` is still offered. -/
theorem OffersMinPlusService.mono
    {S : Server} {beta beta' : ℝ≥0 → ℝ≥0}
    (h : beta ≤ beta') (hS : OffersMinPlusService beta' S) :
    OffersMinPlusService beta S :=
  fun A D hp =>
    le_trans (minConvProj_mono_right A h) (hS A D hp)

/-- The trivial zero service curve `beta ≡ 0`. -/
def betaZero : ℝ≥0 → ℝ≥0 := fun _ => 0

/-- Every server offers the zero service curve `betaZero`. -/
theorem offersMinPlusService_betaZero (S : Server) :
    OffersMinPlusService betaZero S := by
  intro A D _ t
  rw [minConvProj_eq]
  refine le_trans
    (ciInf_le (OrderBot.bddBelow _) ⟨(0, t), by simp⟩) ?_
  show A.1 0 + betaZero t ≤ D.1 t
  rw [A.zero]
  show (0 : ℝ≥0) + (0 : ℝ≥0) ≤ D.1 t
  simp

/-- `A`/`D` is backlogged on `I`: `D t < A t` for all `t ∈ I`. -/
def IsBacklogged (A D : Curve) (I : Set ℝ≥0) : Prop :=
  ∀ t ∈ I, D.1 t < A.1 t

/-- Start of the backlogged period of `t`: last `u ≤ t` with `A u = D u`. -/
noncomputable def Start (A D : Curve) (t : ℝ≥0) : ℝ≥0 :=
  sSup { u | u ≤ t ∧ A.1 u = D.1 u }

/-- The set defining `Start` is nonempty (`0` belongs). -/
theorem start_set_nonempty (A D : Curve) (t : ℝ≥0) :
    { u | u ≤ t ∧ A.1 u = D.1 u }.Nonempty :=
  ⟨0, by simp, by rw [A.zero, D.zero]⟩

/-- `Start A D t ≤ t`. -/
theorem start_le (A D : Curve) (t : ℝ≥0) :
    Start A D t ≤ t :=
  csSup_le (start_set_nonempty A D t) (fun _ hx => hx.1)

/-- `Start A D` is monotone in `t`. -/
theorem start_mono (A D : Curve) {t t' : ℝ≥0}
    (h : t ≤ t') : Start A D t ≤ Start A D t' :=
  csSup_le (start_set_nonempty A D t)
    (fun _ hx =>
      le_csSup ⟨t', fun _ hy => hy.1⟩
        ⟨le_trans hx.1 h, hx.2⟩)

/-- Backlog restricts to subsets of the interval. -/
theorem IsBacklogged.subset {A D : Curve}
    {I I' : Set ℝ≥0} (h : IsBacklogged A D I)
    (hsub : I' ⊆ I) : IsBacklogged A D I' :=
  fun t ht => h t (hsub ht)

/-- `(Start A D t, t]` is a backlogged period when `D ≤ A`. -/
theorem isBacklogged_Ioc_start (A D : Curve)
    (hc : ∀ x, D.1 x ≤ A.1 x) (t : ℝ≥0) :
    IsBacklogged A D (Set.Ioc (Start A D t) t) := by
  intro u hu
  have hbdd : BddAbove { u | u ≤ t ∧ A.1 u = D.1 u } :=
    ⟨t, fun x hx => hx.1⟩
  rcases (hc u).lt_or_eq with h | h
  · exact h
  · exact absurd (le_csSup hbdd ⟨hu.2, h.symm⟩)
      (not_le.mpr hu.1)

/-- At the start of a backlogged period, `A = D` (uses left continuity). -/
theorem A_start_eq_D_start (A D : Curve)
    (hc : ∀ x, D.1 x ≤ A.1 x) (t : ℝ≥0) :
    A.1 (Start A D t) = D.1 (Start A D t) := by
  set s := Start A D t with hs
  rcases (hc s).lt_or_eq with hlt | heq
  · exfalso
    have hbdd : BddAbove { u | u ≤ t ∧ A.1 u = D.1 u } :=
      ⟨t, fun x hx => hx.1⟩
    have hs0 : 0 < s := by
      rcases eq_zero_or_pos s with h | h
      · rw [h, A.zero, D.zero] at hlt
        exact absurd hlt (lt_irrefl 0)
      · exact h
    have hev : ∀ᶠ u in 𝓝[<] s, D.1 u < A.1 u :=
      (D.leftCont s).eventually_lt (A.leftCont s) hlt
    have hbasis :
        (𝓝[<] s).HasBasis (· < s) (Ioo · s) :=
      nhdsLT_basis_of_exists_lt ⟨0, hs0⟩
    rw [hbasis.eventually_iff] at hev
    obtain ⟨l, hls, hl⟩ := hev
    have hub : ∀ x ∈ { u | u ≤ t ∧ A.1 u = D.1 u },
        x ≤ l := by
      intro x hx
      by_contra hxl
      rw [not_le] at hxl
      rcases (le_csSup hbdd hx).lt_or_eq with hxlt | hxeq
      · have := hl ⟨hxl, hxlt⟩
        rw [hx.2] at this; exact absurd this (lt_irrefl _)
      · -- x = sSup = s with A x = D x, vs D s < A s
        subst hxeq
        exact absurd hx.2 (ne_of_gt hlt)
    exact absurd
      (csSup_le (start_set_nonempty A D t) hub)
      (not_le.mpr hls)
  · exact heq.symm

/-- `Start` is constant across an order-connected backlogged set. -/
theorem start_const_of_backlogged (A D : Curve)
    (hc : ∀ x, D.1 x ≤ A.1 x)
    {I : Set ℝ≥0} (hI : IsBacklogged A D I)
    (hoc : I.OrdConnected)
    {t t' : ℝ≥0} (ht : t ∈ I) (ht' : t' ∈ I) :
    Start A D t = Start A D t' := by
  wlog hle : t ≤ t' generalizing t t'
  · exact (this ht' ht (not_le.mp hle).le).symm
  refine le_antisymm (start_mono A D hle) ?_
  have hst : Start A D t' ≤ t := by
    by_contra h
    rw [not_le] at h
    have hmem : Start A D t' ∈ I :=
      hoc.out ht ht' ⟨h.le, start_le A D t'⟩
    have := hI _ hmem
    rw [A_start_eq_D_start A D hc t'] at this
    exact absurd this (lt_irrefl _)
  exact le_csSup ⟨t, fun y hy => hy.1⟩
    ⟨hst, A_start_eq_D_start A D hc t'⟩

/-- `S` offers strict service `beta`: `D s + beta(t-s) ≤ D t` on backlog. -/
def OffersStrictService (beta : ℝ≥0 → ℝ≥0)
    (S : Server) : Prop :=
  ∀ A D : Curve, (A, D) ∈ S →
    ∀ s t, s ≤ t →
      IsBacklogged A D (Set.Ioc s t) →
        D.1 s + beta (t - s) ≤ D.1 t

/-- Largest causal relation offering strict service `beta`. -/
def strictServiceRel (beta : ℝ≥0 → ℝ≥0) :
    Set (Curve × Curve) :=
  { p | p.2 ≤ p.1 ∧
      ∀ s t, s ≤ t →
        IsBacklogged p.1 p.2 (Set.Ioc s t) →
          p.2.1 s + beta (t - s) ≤ p.2.1 t }

/-- `S ⊆ strictServiceRel beta` iff `S` offers strict service `beta`. -/
theorem subset_strictServiceRel_iff
    {S : Server} {beta : ℝ≥0 → ℝ≥0} :
    (∀ p ∈ S, p ∈ strictServiceRel beta) ↔
      OffersStrictService beta S := by
  constructor
  · intro h A D hp
    exact (h (A, D) hp).2
  · intro h p hp
    exact ⟨S.causal p.1 p.2 hp, h p.1 p.2 hp⟩

/-- Every server offers the zero strict service curve. -/
theorem offersStrictService_betaZero (S : Server) :
    OffersStrictService betaZero S := by
  intro A D _ s t hst _
  show D.1 s + betaZero (t - s) ≤ D.1 t
  show D.1 s + (0 : ℝ≥0) ≤ D.1 t
  rw [add_zero]
  exact D.mono hst

/-- Strict-service relation is antitone in `beta`. -/
theorem strictServiceRel_mono
    {beta beta' : ℝ≥0 → ℝ≥0} (h : beta' ≤ beta) :
    strictServiceRel beta ⊆ strictServiceRel beta' := by
  intro p hp
  refine ⟨hp.1, fun s t hst hbl => ?_⟩
  refine le_trans ?_ (hp.2 s t hst hbl)
  gcongr
  exact h _

/-- Pointwise max of two strict service curves is offered. -/
theorem offersStrictService_sup
    {S : Server} {beta beta' : ℝ≥0 → ℝ≥0}
    (h : OffersStrictService beta S)
    (h' : OffersStrictService beta' S) :
    OffersStrictService
      (fun u => max (beta u) (beta' u)) S := by
  intro A D hp s t hst hbl
  show D.1 s + max (beta (t-s)) (beta' (t-s)) ≤ D.1 t
  rcases le_total (beta (t-s)) (beta' (t-s)) with hle | hle
  · rw [max_eq_right hle]; exact h' A D hp s t hst hbl
  · rw [max_eq_left hle]; exact h A D hp s t hst hbl

/-- Output bound: `A(Start) + beta(t - Start) ≤ D t` for strict service. -/
theorem strictService_output_bound (beta : ℝ≥0 → ℝ≥0)
    (A D : Curve) (hp : (A, D) ∈ strictServiceRel beta)
    (t : ℝ≥0) :
    A.1 (Start A D t) + beta (t - Start A D t) ≤ D.1 t := by
  have hc : ∀ x, D.1 x ≤ A.1 x := fun x => hp.1 x
  have hbl := isBacklogged_Ioc_start A D hc t
  have hbound := hp.2 (Start A D t) t (start_le A D t) hbl
  rw [A_start_eq_D_start A D hc t]
  exact hbound

/-- Concatenating strict-service bounds across `s ≤ r ≤ t`. -/
theorem strict_concat (beta : ℝ≥0 → ℝ≥0) {S : Server}
    (hβ : OffersStrictService beta S)
    (A D : Curve) (hp : (A, D) ∈ S)
    {s r t : ℝ≥0} (hsr : s ≤ r) (hrt : r ≤ t)
    (hbl : IsBacklogged A D (Set.Ioc s t)) :
    D.1 s + (beta (r - s) + beta (t - r)) ≤ D.1 t := by
  have b1 : D.1 s + beta (r - s) ≤ D.1 r :=
    hβ A D hp s r hsr
      (hbl.subset (Set.Ioc_subset_Ioc_right hrt))
  have b2 : D.1 r + beta (t - r) ≤ D.1 t :=
    hβ A D hp r t hrt
      (hbl.subset (Set.Ioc_subset_Ioc_left hsr))
  calc D.1 s + (beta (r - s) + beta (t - r))
      = (D.1 s + beta (r - s)) + beta (t - r) := by
        ring
    _ ≤ D.1 r + beta (t - r) := by gcongr
    _ ≤ D.1 t := b2

/-- Strict service is preserved by the non-decreasing closure `ndClosure`. -/
theorem offersStrictService_ndClosure
    (beta : ℝ≥0 → ℝ≥0) {S : Server}
    (hβ : OffersStrictService beta S) :
    OffersStrictService (ndClosure beta) S := by
  intro A D hp s t hst hbl
  show D.1 s + ndClosure beta (t - s) ≤ D.1 t
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
theorem offersStrictService_ndClosure_iff
    (beta : ℝ≥0 → ℝ≥0) {S : Server}
    (hbdd : ∀ t, BddAbove
      (Set.range (fun u : {u // u ≤ t} => beta u.1))) :
    OffersStrictService (ndClosure beta) S ↔
      OffersStrictService beta S := by
  constructor
  · intro h A D hp s t hst hbl
    exact le_trans
      (by gcongr; exact le_ndClosure beta hbdd (t - s))
      (h A D hp s t hst hbl)
  · exact offersStrictService_ndClosure beta

/-- Strict service is preserved by the max-plus self-convolution. -/
theorem offersStrictService_maxConvProj
    (beta : ℝ≥0 → ℝ≥0) {S : Server}
    (hβ : OffersStrictService beta S) :
    OffersStrictService (maxConvProj beta beta) S := by
  intro A D hp s t hst hbl
  show D.1 s + maxConvProj beta beta (t - s) ≤ D.1 t
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
theorem offers_maxConvProjPow (beta : ℝ≥0 → ℝ≥0)
    {S : Server} (hβ : OffersStrictService beta S)
    (n : ℕ) :
    OffersStrictService (maxConvProjPow beta n) S := by
  induction n with
  | zero => exact hβ
  | succ n ih => exact offersStrictService_maxConvProj _ ih

/-- Strict service is preserved by the super-additive closure
`superAdditiveClosureMax`. -/
theorem offersStrictService_superAdditiveClosureMax
    (beta : ℝ≥0 → ℝ≥0) {S : Server}
    (hβ : OffersStrictService beta S) :
    OffersStrictService (superAdditiveClosureMax beta) S := by
  intro A D hp s t hst hbl
  show D.1 s + superAdditiveClosureMax beta (t - s) ≤ D.1 t
  unfold superAdditiveClosureMax
  refine add_ciSup_le _ _ _ (fun n => ?_)
  exact offers_maxConvProjPow beta hβ n A D hp s t hst hbl

/-- Offering `superAdditiveClosureMax beta` is equivalent to offering `beta` (when bdd). -/
theorem offersStrictService_superAdditiveClosureMax_iff
    (beta : ℝ≥0 → ℝ≥0) {S : Server}
    (hbdd : ∀ t, BddAbove
      (Set.range (fun n => maxConvProjPow beta n t))) :
    OffersStrictService (superAdditiveClosureMax beta) S ↔
      OffersStrictService beta S := by
  constructor
  · intro h A D hp s t hst hbl
    exact le_trans
      (by gcongr; exact le_superAdditiveClosureMax beta hbdd (t - s))
      (h A D hp s t hst hbl)
  · exact offersStrictService_superAdditiveClosureMax beta

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
def IsShaper (S : Server) (sigma : Fmin) : Prop :=
  ∀ p ∈ S, AllowsArrivalCurve (↑p.2 : Fmin) sigma

/-- Largest causal relation that shapes outputs to arrival curve `sigma`. -/
def shaperRel (sigma : Fmin) : Set (Curve × Curve) :=
  { p | p.2 ≤ p.1 ∧
      AllowsArrivalCurve (↑p.2 : Fmin) sigma }

/-- Membership unfolding for `shaperRel`. -/
theorem mem_shaperRel_iff
    {sigma : Fmin} {p : Curve × Curve} :
    p ∈ shaperRel sigma ↔
      p.2 ≤ p.1 ∧
        AllowsArrivalCurve (↑p.2 : Fmin) sigma :=
  Iff.rfl

/-- The server built from `shaperRel sigma`. -/
def shaperServer (sigma : Fmin)
    (htot : ∀ A : Curve, ∃ D : Curve,
      (A, D) ∈ shaperRel sigma) :
    Server where
  rel := shaperRel sigma
  causal := fun _A _D hp => hp.1
  leftTotal A := htot A

/-- `S ⊆ shaperRel sigma` iff `S` is a shaper for `sigma`. -/
theorem subset_shaperRel_iff
    {S : Server} {sigma : Fmin} :
    (∀ p ∈ S, p ∈ shaperRel sigma) ↔
      IsShaper S sigma := by
  constructor
  · intro h p hp
    exact (h p hp).2
  · intro h p hp
    exact ⟨S.causal p.1 p.2 hp, h p hp⟩

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
  ext p
  constructor
  · intro hp
    exact ⟨hp.1,
      (allowsArrivalCurve_closure_iff
        (↑p.2 : Fmin) sigma).2 hp.2⟩
  · intro hp
    exact ⟨hp.1,
      (allowsArrivalCurve_closure_iff
        (↑p.2 : Fmin) sigma).1 hp.2⟩

/-- A shaper for `sigma` is also a shaper for `sigma⋆`. -/
theorem IsShaper.closure
    {S : Server} {sigma : Fmin}
    (hS : IsShaper S sigma) :
    IsShaper S sigma⋆ := by
  intro p hp
  exact (allowsArrivalCurve_closure_iff
    (↑p.2 : Fmin) sigma).2 (hS p hp)

example
    (sigma : Fmin) :
    shaperRel sigma = shaperRel sigma⋆ :=
  shaperRel_closure sigma

example
    {S : Server} {sigma : Fmin}
    (hS : IsShaper S sigma) :
    IsShaper S sigma⋆ :=
  IsShaper.closure hS

/-- A shaper for `sigma` is a shaper for any smaller `sigma' ≤ sigma`. -/
theorem IsShaper.of_le
    {S : Server}
    {sigma sigma' : Fmin}
    (hS : IsShaper S sigma)
    (h : sigma' ≤ sigma) :
    IsShaper S sigma' := by
  intro p hp
  exact le_trans
    (conv_mono_right (↑p.2 : Fmin) h) (hS p hp)

/-- `shaperRel` is antitone in `sigma`. -/
theorem shaperRel_mono
    {sigma sigma' : Fmin}
    (h : sigma' ≤ sigma) :
    shaperRel sigma ⊆ shaperRel sigma' := by
  intro p hp
  exact ⟨hp.1,
    le_trans
      (conv_mono_right (↑p.2 : Fmin) h) hp.2⟩

example
    {sigma sigma' : Fmin}
    (h : sigma' ≤ sigma) :
    shaperRel sigma ⊆ shaperRel sigma' :=
  shaperRel_mono h

example
    {S : Server} {sigma sigma' : Fmin}
    (hS : IsShaper S sigma)
    (h : sigma' ≤ sigma) :
    IsShaper S sigma' :=
  IsShaper.of_le hS h

/-- `S` is a greedy shaper for `sigma`: every output is `A ∗ sigma`. -/
def IsGreedyShaper
    (S : Server) (sigma : Fmin) : Prop :=
  ∀ p ∈ S, (↑p.2 : Fmin) = conv (↑p.1 : Fmin) sigma

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
def greedyRel (sigma : Fmin) : Set (Curve × Curve) :=
  { p | (↑p.2 : Fmin) = conv (↑p.1 : Fmin) sigma }

/-- Membership unfolding for `greedyRel`. -/
theorem mem_greedyRel_iff
    {sigma : Fmin} {p : Curve × Curve} :
    p ∈ greedyRel sigma ↔
      (↑p.2 : Fmin) = conv (↑p.1 : Fmin) sigma :=
  Iff.rfl

/-- The greedy-shaper server built from `greedyRel sigma`. -/
def greedyShaper
    (sigma : Fmin) (h0 : sigma 0 = eₒ)
    (htot : ∀ A : Curve, ∃ D : Curve,
      (A, D) ∈ greedyRel sigma) :
    Server where
  rel := greedyRel sigma
  causal A D hp := by
    rw [Curve.le_iff_conv]
    rw [(hp : (↑D : Fmin) = conv (↑A : Fmin) sigma)]
    exact self_le_conv_of_zeroAtOrigin (↑A) sigma h0
  leftTotal A := htot A

/-- `IsGreedyShaper S sigma` iff `S ⊆ greedyRel sigma`. -/
theorem isGreedyShaper_iff_subset
    {S : Server} {sigma : Fmin} :
    IsGreedyShaper S sigma ↔
      ∀ p ∈ S, p ∈ greedyRel sigma :=
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
    {S : Server} {sigma : Fmin}
    (hsub : IsSubadditiveF sigma)
    (hS : IsGreedyShaper S sigma) :
    IsShaper S sigma := by
  intro p hp
  rw [hS p hp]
  exact allowsArrivalCurve_conv_of_subadd (↑p.1) hsub

end DeepWiki
