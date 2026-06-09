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
