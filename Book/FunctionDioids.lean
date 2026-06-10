import Book.DioidFunctions
import Book.SubDioid
import Mathlib.Topology.Instances.NNReal.Lemmas

/-! # Function dioids
Generic `minConv`/`maxConv` with intro and elim lemmas (`minConv_le_add`,
`le_minConv`, `add_le_maxConv`, `maxConv_le`); the function spaces
`FminBar`/`FmaxBar` over the extended carriers, whose dioid product `conv`
agrees with `minConv`/`maxConv`; the predicates `IsNonneg`/`IsNullAtOrigin`
with closure lemmas; and the sub-complete-dioids `FPlus`/`FNondecr`. -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge

/-- (min,+) convolution: `t ↦ ⨅_{u+s=t} f u + g s`. -/
noncomputable def minConv
    {D T : Type*} [Add D] [Add T] [InfSet T]
    (f g : D → T) : D → T :=
  fun t =>
    ⨅ p : {p : D × D // p.1 + p.2 = t},
      f p.1.1 + g p.1.2

/-- (max,+) convolution: `t ↦ ⨆_{u+s=t} f u + g s`. -/
noncomputable def maxConv
    {D T : Type*} [Add D] [Add T] [SupSet T]
    (f g : D → T) : D → T :=
  fun t =>
    ⨆ p : {p : D × D // p.1 + p.2 = t},
      f p.1.1 + g p.1.2

/-- (min,+) deconvolution `g ⊘ h`: `t ↦ ⨆_s g (t + s) - h s`. -/
noncomputable def minDeconv
    {D T : Type*} [Add D] [Sub T] [SupSet T]
    (g h : D → T) : D → T :=
  fun t => ⨆ s : D, g (t + s) - h s

/-- (max,+) deconvolution `g ⊘̄ h`: `t ↦ ⨅_s g (t + s) - h s`, the order dual
of `minDeconv` (infimum in place of supremum). -/
noncomputable def maxDeconv
    {D T : Type*} [Add D] [Sub T] [InfSet T]
    (g h : D → T) : D → T :=
  fun t => ⨅ s : D, g (t + s) - h s

/-- Splittings `{p // p.1 + p.2 = t}` are nonempty. -/
instance splitNonempty {D : Type*} [AddZeroClass D]
    (t : D) :
    Nonempty {p : D × D // p.1 + p.2 = t} :=
  ⟨⟨(t, 0), by simp⟩⟩

/-- Elim: every split bounds the (min,+) convolution from above,
`minConv f g t ≤ f u + g s` whenever `u + s = t`. -/
theorem minConv_le_add {D T : Type*} [Add D] [Add T]
    [ConditionallyCompleteLattice T] [OrderBot T]
    (f g : D → T) {u s t : D} (h : u + s = t) :
    minConv f g t ≤ f u + g s :=
  ciInf_le_of_le (OrderBot.bddBelow _) ⟨(u, s), h⟩ le_rfl

/-- Intro: a uniform bound over all splits bounds the (min,+) convolution
from below, `x ≤ minConv f g t`. -/
theorem le_minConv {D T : Type*} [AddZeroClass D] [Add T]
    [ConditionallyCompleteLattice T] {f g : D → T} {x : T} {t : D}
    (h : ∀ u s, u + s = t → x ≤ f u + g s) :
    x ≤ minConv f g t :=
  le_ciInf fun p => h p.1.1 p.1.2 p.2

/-- Elim: every split bounds the (max,+) convolution from below,
`f u + g s ≤ maxConv f g t` whenever `u + s = t`. -/
theorem add_le_maxConv {D T : Type*} [Add D] [Add T]
    [ConditionallyCompleteLattice T] [OrderTop T]
    (f g : D → T) {u s t : D} (h : u + s = t) :
    f u + g s ≤ maxConv f g t :=
  le_ciSup_of_le (OrderTop.bddAbove _) ⟨(u, s), h⟩ le_rfl

/-- Intro: a uniform bound over all splits bounds the (max,+) convolution
from above, `maxConv f g t ≤ x`. -/
theorem maxConv_le {D T : Type*} [AddZeroClass D] [Add T]
    [ConditionallyCompleteLattice T] {f g : D → T} {x : T} {t : D}
    (h : ∀ u s, u + s = t → f u + g s ≤ x) :
    maxConv f g t ≤ x :=
  ciSup_le fun p => h p.1.1 p.1.2 p.2


/-- (min,+) functions valued in `R∪{±∞}`. -/
abbrev FminBar := ℝ≥0 → MinPlusExt

/-- Wrap a raw `ℝ≥0 → R∪{±∞}` function into `FminBar`. -/
instance : Coe (ℝ≥0 → WithTop (WithBot ℝ)) FminBar :=
  ⟨fun f t => ⟨f t⟩⟩

/-- `(f ∗ g)` on `FminBar` agrees with `minConv` numerically. -/
theorem conv_coe_min_apply
    (f g : ℝ≥0 → WithTop (WithBot ℝ)) (t : ℝ≥0) :
    ((conv (↑f) (↑g) t : MinPlusExt)
        : WithTop (WithBot ℝ))
      = minConv f g t := by
  apply le_antisymm
  · refine le_iInf ?_
    rintro ⟨⟨u, s⟩, hus⟩
    have hle := CompleteDioid.le_sSup _ _
      (show ((↑f : FminBar) u ⊗ₒ (↑g : FminBar) s)
          ∈ {x | ∃ u s, u + s = t
              ∧ x = (↑f : FminBar) u ⊗ₒ (↑g : FminBar) s}
        from ⟨u, s, hus, rfl⟩)
    rw [← conv_apply] at hle
    exact (MinPlusExt.le_iff _ _).mp hle
  · rw [conv_apply, ← MinPlusExt.le_iff]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, s, hus, rfl⟩
    rw [MinPlusExt.le_iff]
    exact iInf_le_of_le ⟨(u, s), hus⟩ (le_refl _)

/-- `(f ∗ g)` on `FminBar` is the coerced `minConv f g`. -/
theorem conv_coe_min
    (f g : ℝ≥0 → WithTop (WithBot ℝ)) :
    conv (↑f : FminBar) (↑g : FminBar)
      = (↑(minConv f g) : FminBar) := by
  funext t
  apply MinPlusExt.ext
  exact conv_coe_min_apply f g t

/-- (max,+) functions valued in `R∪{±∞}`. -/
abbrev FmaxBar := ℝ≥0 → MaxPlusExt

/-- Wrap a raw `ℝ≥0 → R∪{±∞}` function into `FmaxBar`. -/
instance : Coe (ℝ≥0 → WithBot (WithTop ℝ)) FmaxBar :=
  ⟨fun f t => ⟨f t⟩⟩

/-- `(f ∗ g)` on `FmaxBar` agrees with `maxConv` numerically. -/
theorem conv_coe_max_apply
    (f g : ℝ≥0 → WithBot (WithTop ℝ)) (t : ℝ≥0) :
    ((conv (↑f) (↑g) t : MaxPlusExt)
        : WithBot (WithTop ℝ))
      = maxConv f g t := by
  apply le_antisymm
  · rw [conv_apply, ← MaxPlusExt.le_iff]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, s, hus, rfl⟩
    rw [MaxPlusExt.le_iff]
    exact le_iSup_of_le ⟨(u, s), hus⟩ (le_refl _)
  · refine iSup_le ?_
    rintro ⟨⟨u, s⟩, hus⟩
    have hle := CompleteDioid.le_sSup _ _
      (show ((↑f : FmaxBar) u ⊗ₒ (↑g : FmaxBar) s)
          ∈ {x | ∃ u s, u + s = t
              ∧ x = (↑f : FmaxBar) u ⊗ₒ (↑g : FmaxBar) s}
        from ⟨u, s, hus, rfl⟩)
    rw [← conv_apply] at hle
    exact (MaxPlusExt.le_iff _ _).mp hle

/-- `(f ∗ g)` on `FmaxBar` is the coerced `maxConv f g`. -/
theorem conv_coe_max
    (f g : ℝ≥0 → WithBot (WithTop ℝ)) :
    conv (↑f : FmaxBar) (↑g : FmaxBar)
      = (↑(maxConv f g) : FmaxBar) := by
  funext t
  apply MaxPlusExt.ext
  exact conv_coe_max_apply f g t

/-- `f` is non-negative: `∀ t, 0 ≤ f t`. -/
def IsNonneg {D T : Type*} [Zero T] [LE T]
    (f : D → T) : Prop :=
  ∀ t, 0 ≤ f t

/-- `f` vanishes at the origin: `f 0 = 0`. -/
def IsNullAtOrigin {D T : Type*} [Zero D] [Zero T]
    (f : D → T) : Prop :=
  f 0 = 0

/-- A monotone function vanishing at the origin is nonnegative:
`0 = f 0 ≤ f t`. -/
theorem isNonneg_of_monotone_of_nullAtOrigin {D T : Type*}
    [_root_.AddCommMonoid D] [PartialOrder D] [CanonicallyOrderedAdd D]
    [Zero T] [Preorder T] {f : D → T}
    (hmono : Monotone f) (h0 : IsNullAtOrigin f) : IsNonneg f :=
  fun _ => h0 ▸ hmono zero_le'

example {α β : Type*} [Preorder α] [Preorder β]
    (f : α → β) :
    Monotone f ↔ ∀ x y, x ≤ y → f x ≤ f y :=
  Iff.rfl

/-- `IsNonneg` is closed under pointwise `min`. -/
theorem IsNonneg.min {D T : Type*} [LinearOrder T]
    [Zero T] {f g : D → T}
    (hf : IsNonneg f) (hg : IsNonneg g) :
    IsNonneg (fun t => min (f t) (g t)) :=
  fun t => le_min (hf t) (hg t)

/-- `IsNullAtOrigin` is closed under pointwise `min`. -/
theorem IsNullAtOrigin.min {D T : Type*} [Zero D]
    [LinearOrder T] [Zero T] {f g : D → T}
    (hf : IsNullAtOrigin f) (hg : IsNullAtOrigin g) :
    IsNullAtOrigin (fun t => min (f t) (g t)) := by
  show Min.min (f 0) (g 0) = 0
  rw [hf, hg, min_self]

example {α β : Type*} [Preorder α] [LinearOrder β]
    {f g : α → β} (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun t => min (f t) (g t)) :=
  hf.min hg

/-- `IsNonneg` is closed under pointwise `+`. -/
theorem IsNonneg.add {D T : Type*}
    [_root_.AddCommMonoid T] [PartialOrder T]
    [IsOrderedAddMonoid T] {f g : D → T}
    (hf : IsNonneg f) (hg : IsNonneg g) :
    IsNonneg (fun t => f t + g t) := by
  intro t
  calc (0 : T) = 0 + 0 := by simp
    _ ≤ f t + g t := by gcongr; exacts [hf t, hg t]

example {α β : Type*} [Preorder α]
    [_root_.AddCommMonoid β] [PartialOrder β]
    [IsOrderedAddMonoid β]
    {f g : α → β} (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun t => f t + g t) :=
  hf.add hg

/-- `IsNonneg` is closed under `minConv`. -/
theorem IsNonneg.conv {D T : Type*} [Add D]
    [_root_.AddCommMonoid T] [CompleteLattice T]
    [IsOrderedAddMonoid T] {f g : D → T}
    (hf : IsNonneg f) (hg : IsNonneg g) :
    IsNonneg (minConv f g) := by
  intro t
  simp only [minConv]
  refine le_iInf ?_
  rintro ⟨⟨u, s⟩, _⟩
  calc (0 : T) = 0 + 0 := by simp
    _ ≤ f u + g s := by gcongr; exacts [hf u, hg s]

/-- `IsNullAtOrigin` is closed under `minConv`. -/
theorem IsNullAtOrigin.conv {D T : Type*}
    [_root_.AddCommMonoid D] [PartialOrder D]
    [CanonicallyOrderedAdd D]
    [_root_.AddZeroClass T] [CompleteLattice T]
    {f g : D → T}
    (hf : IsNullAtOrigin f) (hg : IsNullAtOrigin g) :
    IsNullAtOrigin (minConv f g) := by
  show minConv f g 0 = 0
  simp only [minConv]
  apply le_antisymm
  · exact iInf_le_of_le ⟨(0, 0), by simp⟩ (by
      simp [IsNullAtOrigin] at hf hg; simp [hf, hg])
  · refine le_iInf ?_
    rintro ⟨⟨u, s⟩, (hus : u + s = 0)⟩
    obtain ⟨rfl, rfl⟩ := add_eq_zero.mp hus
    simp [IsNullAtOrigin] at hf hg; simp [hf, hg]

/-- `minConv` of two monotone functions is monotone. -/
theorem monotone_minConv {D T : Type*}
    [_root_.AddCommMonoid D] [LinearOrder D]
    [CanonicallyOrderedAdd D] [Sub D] [OrderedSub D]
    [_root_.AddCommMonoid T] [CompleteLattice T]
    [IsOrderedAddMonoid T] {f g : D → T}
    (hf : Monotone f) (hg : Monotone g) :
    Monotone (minConv f g) := by
  intro x y hxy
  simp only [minConv]
  refine le_iInf ?_
  rintro ⟨⟨u, s⟩, (hus : u + s = y)⟩
  refine iInf_le_of_le
    ⟨(Min.min u x, x - Min.min u x), by
      rw [add_tsub_cancel_of_le (min_le_right u x)]⟩ ?_
  have hs : x - Min.min u x ≤ s := by
    rw [tsub_le_iff_right]
    rcases le_total u x with h | h
    · rw [min_eq_left h, add_comm, hus]; exact hxy
    · rw [min_eq_right h]; exact le_add_self
  gcongr
  · exact hf (min_le_left u x)
  · exact hg hs

/-- Non-negative (min,+) functions: `F⁺`. -/
abbrev FPlus :=
  {f : FminBar // IsNonneg (fun t => (f t).toVal)}

/-- Non-negative non-decreasing (min,+) functions. -/
abbrev FNondecr :=
  {f : FminBar //
    IsNonneg (fun t => (f t).toVal)
      ∧ Monotone (fun t => (f t).toVal)}

/-- Coercing back the numeric values of `a` recovers `a`. -/
theorem coe_toVal (a : FminBar) :
    (↑(fun t => (a t).toVal) : FminBar) = a := by
  funext t; apply MinPlusExt.ext; rfl

/-- Numeric value of `(a ∗ b)` is `minConv` of their values. -/
theorem mul_toVal (a b : FminBar) (t : ℝ≥0) :
    ((a ⊗ₒ b) t).toVal
      = minConv (fun t => (a t).toVal)
          (fun t => (b t).toVal) t := by
  show ((conv a b t : MinPlusExt) : WithTop (WithBot ℝ)) = _
  rw [← coe_toVal a, ← coe_toVal b]
  exact conv_coe_min_apply _ _ t

/-- `IsNonneg` cuts out a sub-complete-dioid of `FminBar`. -/
theorem isSubCompleteDioid_FPlus :
    IsSubCompleteDioid
      (fun f : FminBar => IsNonneg (fun t => (f t).toVal))
      where
  add ha hb := fun t => le_min (ha t) (hb t)
  mul {a b} ha hb := fun t => by
    show (0 : WithTop (WithBot ℝ)) ≤ ((a ⊗ₒ b) t).toVal
    rw [mul_toVal]; exact (IsNonneg.conv ha hb) t
  eps := fun _ => le_top
  one := fun t => by
    show (0 : WithTop (WithBot ℝ))
        ≤ ((convUnit t : MinPlusExt)).toVal
    rcases eq_or_ne t 0 with h | h
    · rw [convUnit, if_pos h]; exact le_rfl
    · rw [convUnit, if_neg h]; exact le_top
  iSup F hF := fun t => le_iInf (fun i => hF i t)

/-- Non-neg + monotone cut out a sub-complete-dioid. -/
theorem isSubCompleteDioid_FNondecr :
    IsSubCompleteDioid
      (fun f : FminBar =>
        IsNonneg (fun t => (f t).toVal)
          ∧ Monotone (fun t => (f t).toVal))
      where
  add ha hb :=
    ⟨fun t => le_min (ha.1 t) (hb.1 t),
      fun _ _ hxy =>
        min_le_min (ha.2 hxy) (hb.2 hxy)⟩
  mul {a b} ha hb := by
    have hn := IsNonneg.conv ha.1 hb.1
    have hm := monotone_minConv ha.2 hb.2
    refine ⟨fun t => ?_, fun _ _ hxy => ?_⟩
    · show (0 : WithTop (WithBot ℝ)) ≤ ((a ⊗ₒ b) t).toVal
      rw [mul_toVal]; exact hn t
    · show ((a ⊗ₒ b) _).toVal ≤ ((a ⊗ₒ b) _).toVal
      rw [mul_toVal, mul_toVal]; exact hm hxy
  eps := ⟨fun _ => le_top, fun _ _ _ => le_top⟩
  one := by
    refine ⟨fun t => ?_, fun x y hxy => ?_⟩
    · show (0 : WithTop (WithBot ℝ))
          ≤ ((convUnit t : MinPlusExt)).toVal
      rcases eq_or_ne t 0 with h | h
      · rw [convUnit, if_pos h]; exact le_rfl
      · rw [convUnit, if_neg h]; exact le_top
    · show ((convUnit x : MinPlusExt)).toVal
          ≤ ((convUnit y : MinPlusExt)).toVal
      rcases eq_or_ne x 0 with hx | hx
      · rw [convUnit, if_pos hx]
        show (0 : WithTop (WithBot ℝ)) ≤ _
        rcases eq_or_ne y 0 with hy | hy
        · rw [convUnit, if_pos hy]; exact le_rfl
        · rw [convUnit, if_neg hy]; exact le_top
      · have hy : y ≠ 0 := by
          rintro rfl; exact hx (le_zero_iff.mp hxy)
        rw [convUnit, if_neg hx, convUnit, if_neg hy]
  iSup F hF :=
    ⟨fun t => le_iInf (fun i => (hF i).1 t),
      fun _ _ hxy =>
        le_iInf (fun i =>
          (iInf_le _ i).trans ((hF i).2 hxy))⟩

/-- `CompleteDioid` structure on `FPlus`. -/
noncomputable instance : CompleteDioid FPlus :=
  isSubCompleteDioid_FPlus.toCompleteDioid

/-- `CompleteDioid` structure on `FNondecr`. -/
noncomputable instance : CompleteDioid FNondecr :=
  isSubCompleteDioid_FNondecr.toCompleteDioid

/-- (min,+) functions valued in `R≥0∪{+∞}`. -/
abbrev Fmin := ℝ≥0 → MinPlusNN

/-- (max,+) functions valued in `R≥0∪{+∞}`. -/
abbrev Fmax := ℝ≥0 → MaxPlusNN

example (f g : Fmin) (t : ℝ≥0) :
    conv f g t
      = CompleteDioid.sSup
          { x | ∃ u s, u + s = t ∧ x = f u ⊗ₒ g s } :=
  conv_apply f g t

example (f g : Fmin) (t : ℝ≥0) :
    conv f g t
      = CompleteDioid.sSup
          { x | ∃ s : ℝ≥0,
              s ≤ t ∧ x = f (t - s) ⊗ₒ g s } :=
  conv_eq_sub f g t

example (f : Fmin) : conv convUnit f = f :=
  convUnit_left f

/-- `c + ⨆ f ≤ y` when `c + f i ≤ y` for all `i`. -/
theorem add_ciSup_le {ι : Type} [Nonempty ι]
    (c y : ℝ≥0) (f : ι → ℝ≥0)
    (h : ∀ i, c + f i ≤ y) : c + ⨆ i, f i ≤ y := by
  have hcy : c ≤ y :=
    le_trans le_self_add (h (Classical.arbitrary ι))
  have hsup : ⨆ i, f i ≤ y - c :=
    ciSup_le (fun i => le_tsub_of_add_le_left (h i))
  calc c + ⨆ i, f i ≤ c + (y - c) := by gcongr
    _ = y := add_tsub_cancel_of_le hcy

/-- Embed `g : ℝ≥0 → ℝ≥0` into `Fmin`. -/
def embMin (g : ℝ≥0 → ℝ≥0) : Fmin :=
  fun t => ⟨(g t : ℝ≥0∞)⟩

/-- Embed `g : ℝ≥0 → ℝ≥0` into `Fmax`. -/
def embMax (g : ℝ≥0 → ℝ≥0) : Fmax :=
  fun t => ⟨((g t : ℝ≥0∞) : WithBot ℝ≥0∞)⟩

/-- `minConv` of embedded functions, valued back in `ℝ≥0`. -/
noncomputable def minConvProj (g h : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t =>
    (conv (embMin g) (embMin h) t
      : MinPlusNN).toVal.toNNReal

/-- The (min,+) product of embedded values is `g u + h s`. -/
theorem embMin_mul (g h : ℝ≥0 → ℝ≥0) (u s : ℝ≥0) :
    ((embMin g u ⊗ₒ embMin h s : MinPlusNN) : ℝ≥0∞)
      = (g u : ℝ≥0∞) + (h s : ℝ≥0∞) := rfl

/-- `(embMin g ∗ embMin h)` as an `ℝ≥0∞`-valued infimum. -/
theorem conv_embMin_toE (g h : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    ((conv (embMin g) (embMin h) t : MinPlusNN) : ℝ≥0∞)
      = ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞) := by
  rw [conv_apply]
  show (⨅ x : {x : MinPlusNN //
        ∃ u s, u + s = t ∧ x = embMin g u ⊗ₒ embMin h s},
        (x.val : ℝ≥0∞)) = _
  apply le_antisymm
  · refine le_iInf (fun p => ?_)
    refine iInf_le_of_le
      ⟨embMin g p.1.1 ⊗ₒ embMin h p.1.2,
        p.1.1, p.1.2, p.2, rfl⟩ ?_
    show ((embMin g p.1.1 ⊗ₒ embMin h p.1.2 : MinPlusNN)
        : ℝ≥0∞) ≤ _
    rw [embMin_mul]; push_cast; rfl
  · refine le_iInf (fun x => ?_)
    obtain ⟨u, s, hus, hx⟩ := x.2
    refine iInf_le_of_le ⟨(u, s), hus⟩ ?_
    rw [show (x.val : ℝ≥0∞)
          = ((embMin g u ⊗ₒ embMin h s : MinPlusNN)
              : ℝ≥0∞) from congrArg _ hx, embMin_mul]
    push_cast; rfl

/-- `minConvProj` as the `ℝ≥0` infimum `⨅_{u+s=t} g u + h s`. -/
theorem minConvProj_eq (g h : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    minConvProj g h t
      = ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          (g p.1.1 + h p.1.2) := by
  rw [minConvProj, conv_embMin_toE,
    ← ENNReal.coe_iInf
      (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
        g p.1.1 + h p.1.2),
    ENNReal.toNNReal_coe]

/-- `minConvProj A` is monotone in its right argument. -/
theorem minConvProj_mono_right (A : ℝ≥0 → ℝ≥0)
    {g g' : ℝ≥0 → ℝ≥0} (h : g ≤ g') :
    minConvProj A g ≤ minConvProj A g' := by
  intro t
  rw [minConvProj_eq, minConvProj_eq]
  refine ciInf_mono (OrderBot.bddBelow _) (fun p => ?_)
  gcongr
  exact h p.1.2

/-- `maxConv` of embedded functions, valued back in `ℝ≥0`. -/
noncomputable def maxConvProj (g h : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t =>
    (conv (embMax g) (embMax h) t
      : MaxPlusNN).toVal.unbotD 0 |>.toNNReal

/-- The (max,+) product of embedded values is `g a + h b`. -/
theorem embMax_mul (g h : ℝ≥0 → ℝ≥0) (a b : ℝ≥0) :
    ((embMax g a ⊗ₒ embMax h b : MaxPlusNN)
        : WithBot ℝ≥0∞)
      = (((g a : ℝ≥0∞) : WithBot ℝ≥0∞))
        + (((h b : ℝ≥0∞) : WithBot ℝ≥0∞)) := rfl

/-- `(embMax g ∗ embMax h)` as a `WithBot ℝ≥0∞`-valued sup. -/
theorem conv_embMax_toW (g h : ℝ≥0 → ℝ≥0)
    (t : ℝ≥0) :
    ((conv (embMax g) (embMax h) t : MaxPlusNN)
        : WithBot ℝ≥0∞)
      = ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          (((g p.1.1 + h p.1.2 : ℝ≥0)
            : ℝ≥0∞) : WithBot ℝ≥0∞) := by
  rw [conv_apply]
  show (⨆ x : {x : MaxPlusNN //
        ∃ u s, u + s = t ∧
          x = embMax g u ⊗ₒ embMax h s},
        (x.val : WithBot ℝ≥0∞)) = _
  apply le_antisymm
  · refine iSup_le (fun x => ?_)
    obtain ⟨u, s, hus, hx⟩ := x.2
    refine le_iSup_of_le ⟨(u, s), hus⟩ ?_
    rw [show (x.val : WithBot ℝ≥0∞)
          = ((embMax g u ⊗ₒ embMax h s
                : MaxPlusNN) : WithBot ℝ≥0∞)
            from congrArg _ hx, embMax_mul]
    push_cast; rfl
  · refine iSup_le (fun p => ?_)
    refine le_iSup_of_le
      ⟨embMax g p.1.1 ⊗ₒ embMax h p.1.2,
        p.1.1, p.1.2, p.2, rfl⟩ ?_
    show _ ≤ ((embMax g p.1.1 ⊗ₒ embMax h p.1.2
        : MaxPlusNN) : WithBot ℝ≥0∞)
    rw [embMax_mul]; push_cast; rfl

/-- `maxConvProj` equals the `ℝ≥0∞` sup when that sup is finite. -/
theorem maxConvProj_coe (g h : ℝ≥0 → ℝ≥0) (t : ℝ≥0)
    (hfin : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞)) ≠ ⊤) :
    ((maxConvProj g h t : ℝ≥0) : ℝ≥0∞)
      = ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞) := by
  have hcoe : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        (((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞)
          : WithBot ℝ≥0∞))
      = (((⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞))
          : ℝ≥0∞) : WithBot ℝ≥0∞) :=
    (WithBot.coe_iSup (OrderTop.bddAbove _)).symm
  rw [maxConvProj, conv_embMax_toW, hcoe]
  rw [WithBot.unbotD_coe, ENNReal.coe_toNNReal hfin]

/-- `maxConvProj g h t ≤ c` if every splitting is `≤ c`. -/
theorem maxConvProj_le (g h : ℝ≥0 → ℝ≥0) (t c : ℝ≥0)
    (hsplit : ∀ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      g p.1.1 + h p.1.2 ≤ c) :
    maxConvProj g h t ≤ c := by
  rw [maxConvProj, conv_embMax_toW]
  have hcoe :
      (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        (((g p.1.1 + h p.1.2 : ℝ≥0)
          : ℝ≥0∞) : WithBot ℝ≥0∞))
      = (((⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞))
          : ℝ≥0∞) : WithBot ℝ≥0∞) :=
    (WithBot.coe_iSup (OrderTop.bddAbove _)).symm
  rw [hcoe, WithBot.unbotD_coe]
  have hb : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞))
        ≤ (c : ℝ≥0∞) :=
    iSup_le (fun p => by exact_mod_cast hsplit p)
  have := ENNReal.toNNReal_mono (by simp) hb
  simpa using this

/-- `c + maxConvProj g g t ≤ y` from a per-splitting bound. -/
theorem add_maxConvProj_le
    (g : ℝ≥0 → ℝ≥0) (t c y : ℝ≥0)
    (h : ∀ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
      c + (g p.1.1 + g p.1.2) ≤ y) :
    c + maxConvProj g g t ≤ y := by
  have hcy : c ≤ y :=
    le_trans le_self_add (h ⟨(t, 0), by simp⟩)
  have hsup : maxConvProj g g t ≤ y - c :=
    maxConvProj_le g g t (y - c)
      (fun p => le_tsub_of_add_le_left (h p))
  calc c + maxConvProj g g t ≤ c + (y - c) := by gcongr
    _ = y := add_tsub_cancel_of_le hcy

/-- `⨆ i, g i = - ⨅ i, - g i` for a bounded-above family. -/
theorem neg_ciInf_neg {ι : Type} [Nonempty ι]
    {T : Type*} [_root_.LinearOrder T]
    [_root_.AddCommGroup T]
    [ConditionallyCompleteLattice T]
    [CovariantClass T T (·+·) (·≤·)]
    (g : ι → T) (hbdd : BddAbove (Set.range g)) :
    (⨆ i, g i) = - ⨅ i, - g i := by
  have hbb : BddBelow (Set.range (fun i => - g i)) := by
    obtain ⟨c, hc⟩ := hbdd
    exact ⟨-c, by
      rintro _ ⟨i, rfl⟩; simpa using hc ⟨i, rfl⟩⟩
  apply le_antisymm
  · refine ciSup_le (fun i => ?_)
    rw [le_neg]; exact ciInf_le_of_le hbb i (le_refl _)
  · rw [neg_le]; refine le_ciInf (fun i => ?_)
    rw [le_neg, neg_neg]; exact le_ciSup hbdd i

/-- `maxConvProj g g` as `-` a (min,+) infimum over `ℝ`. -/
theorem maxConvProj_eq_neg_iInf
    (g : ℝ≥0 → ℝ≥0) (t : ℝ≥0)
    (hfin : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        ((g p.1.1 + g p.1.2 : ℝ≥0) : ℝ≥0∞))
        ≠ ⊤) :
    ((maxConvProj g g t : ℝ≥0) : ℝ)
      = - ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
            (- ((g p.1.1 : ℝ) + (g p.1.2 : ℝ))) := by
  have hsc : ((maxConvProj g g t : ℝ≥0) : ℝ≥0∞)
      = ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((g p.1.1 + g p.1.2 : ℝ≥0) : ℝ≥0∞) :=
    maxConvProj_coe g g t hfin
  have hbN : BddAbove (Set.range
      (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
        (g p.1.1 + g p.1.2 : ℝ≥0))) := by
    refine ⟨maxConvProj g g t, ?_⟩
    rintro _ ⟨p, rfl⟩
    have hle :
        ((g p.1.1 + g p.1.2 : ℝ≥0) : ℝ≥0∞)
        ≤ ((maxConvProj g g t : ℝ≥0) : ℝ≥0∞) := by
      rw [hsc]
      exact le_iSup
        (fun q : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
          ((g q.1.1 + g q.1.2 : ℝ≥0)
            : ℝ≥0∞)) p
    exact_mod_cast hle
  have hr : maxConvProj g g t
      = ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          (g p.1.1 + g p.1.2) := by
    rw [← ENNReal.coe_iSup hbN] at hsc
    exact_mod_cast hsc
  have hbR : BddAbove (Set.range
      (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
        ((g p.1.1 + g p.1.2 : ℝ≥0) : ℝ))) := by
    obtain ⟨c, hc⟩ := hbN
    refine ⟨(c : ℝ), ?_⟩
    rintro _ ⟨p, rfl⟩
    exact_mod_cast hc ⟨p, rfl⟩
  simp only [← NNReal.coe_add]
  rw [← neg_ciInf_neg _ hbR,
    show (((maxConvProj g g t : ℝ≥0)) : ℝ)
        = ((⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
            (g p.1.1 + g p.1.2) : ℝ≥0) : ℝ)
        from congrArg _ hr,
    NNReal.coe_iSup]

/-- `minConv` agrees with `minConvProj` on `ℝ≥0`. -/
theorem minConv_eq_minConvProj (g h : ℝ≥0 → ℝ≥0) :
    minConv g h = minConvProj g h := by
  funext t
  rw [minConv, minConvProj_eq]

/-- `maxConv` agrees with `maxConvProj` when the sup is finite. -/
theorem maxConv_eq_maxConvProj
    (g h : ℝ≥0 → ℝ≥0) (t : ℝ≥0)
    (hfin : (⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
        ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞))
        ≠ ⊤) :
    maxConv g h t = maxConvProj g h t := by
  have hbdd : BddAbove (Set.range
      (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
        g p.1.1 + h p.1.2)) := by
    by_contra hub
    exact hfin (ENNReal.iSup_coe_eq_top.mpr hub)
  have h : ((maxConv g h t : ℝ≥0) : ℝ≥0∞)
      = ((maxConvProj g h t : ℝ≥0) : ℝ≥0∞) := by
    rw [maxConv, ENNReal.coe_iSup hbdd,
      maxConvProj_coe _ _ _ hfin]
  exact_mod_cast h

end DeepWiki
