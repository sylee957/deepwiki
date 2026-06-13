import Book.DioidFunctions
import Book.SubDioid
import Mathlib.Topology.Instances.NNReal.Lemmas

/-! # Function dioids
Generic `minConv`/`maxConv` with intro and elim lemmas (`minConv_le_add`,
`le_minConv`, `add_le_maxConv`, `maxConv_le`) and the deconvolution term
bounds (`sub_le_minDeconv`, `maxDeconv_le_sub`); the function spaces
`FminBar`/`FmaxBar` over the extended carriers, whose dioid product `conv`
agrees with `minConv`/`maxConv`; the predicates `IsNonneg`/`IsNullAtOrigin`
with closure lemmas; and the sub-complete-dioids `FPlus`/`FNondecr`.
The abstract dioid structure on `D → T` underneath these readings is
`Book.DioidFunctions`. -/

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

/-- Intro with a leading constant, on the `ℝ≥0∞` carrier:
`c + maxConv f g t ≤ x` from the per-split bounds `c + (f u + g s) ≤ x`
(the constant pushes through the supremum). -/
theorem add_maxConv_le {D : Type*} [AddZeroClass D]
    {f g : D → ℝ≥0∞} {c x : ℝ≥0∞} {t : D}
    (h : ∀ u s, u + s = t → c + (f u + g s) ≤ x) :
    c + maxConv f g t ≤ x := by
  rw [show maxConv f g t
      = ⨆ p : {p : D × D // p.1 + p.2 = t}, f p.1.1 + g p.1.2 from rfl,
    ENNReal.add_iSup]
  exact iSup_le fun p => h p.1.1 p.1.2 p.2

/-- `minConv` is monotone in both arguments (pointwise), over any ordered
codomain with monotone `+` and infima, e.g. `EReal` or `ℝ≥0∞`. -/
theorem minConv_le_minConv {D T : Type*} [AddZeroClass D] [Add T]
    [ConditionallyCompleteLattice T] [OrderBot T]
    [AddLeftMono T] [AddRightMono T] {g g' h h' : D → T}
    (hg : ∀ t, g t ≤ g' t) (hh : ∀ t, h t ≤ h' t) (t : D) :
    minConv g h t ≤ minConv g' h' t :=
  le_minConv fun u s hus =>
    le_trans (minConv_le_add g h hus) (add_le_add (hg u) (hh s))

/-- The `(t, 0)` split: `minConv f g t ≤ f t` when `g 0 = 0`. -/
theorem minConv_le_left {D T : Type*} [AddZeroClass D] [AddZeroClass T]
    [ConditionallyCompleteLattice T] [OrderBot T]
    (f : D → T) {g : D → T} (h0 : g 0 = 0) (t : D) :
    minConv f g t ≤ f t :=
  le_of_le_of_eq (minConv_le_add f g (add_zero t)) (by rw [h0, add_zero])

/-- The `(0, t)` split: `minConv f g t ≤ g t` when `f 0 = 0`. -/
theorem minConv_le_right {D T : Type*} [AddZeroClass D] [AddZeroClass T]
    [ConditionallyCompleteLattice T] [OrderBot T]
    {f : D → T} (h0 : f 0 = 0) (g : D → T) (t : D) :
    minConv f g t ≤ g t :=
  le_of_le_of_eq (minConv_le_add f g (zero_add t)) (by rw [h0, zero_add])

/-- `minConv` at the origin: the only splitting of `0` is `(0, 0)`, so
`minConv f g 0 = f 0 + g 0`. -/
theorem minConv_apply_zero {D T : Type*} [_root_.AddCommMonoid D]
    [PartialOrder D] [CanonicallyOrderedAdd D] [Add T]
    [ConditionallyCompleteLattice T] [OrderBot T] (f g : D → T) :
    minConv f g 0 = f 0 + g 0 :=
  le_antisymm (minConv_le_add f g (add_zero 0))
    (le_minConv fun u s hus => by
      obtain ⟨rfl, rfl⟩ := add_eq_zero.mp hus
      exact le_rfl)

/-- `minConv f g = minConv g f`: the (min,+) convolution is commutative. -/
theorem minConv_comm {D T : Type*} [_root_.AddCommMonoid D]
    [_root_.AddCommMonoid T] [InfSet T] (f g : D → T) :
    minConv f g = minConv g f := by
  funext t
  simp only [minConv]
  rw [← sInf_range, ← sInf_range]
  refine congrArg sInf (Set.ext fun x => ⟨?_, ?_⟩) <;>
    · rintro ⟨⟨⟨u, s⟩, hus⟩, rfl⟩
      exact ⟨⟨(s, u), by rw [add_comm]; exact hus⟩, add_comm _ _⟩

/-- Elim: every term bounds the (min,+) deconvolution from below,
`g (t + s) - h s ≤ minDeconv g h t`. -/
theorem sub_le_minDeconv {D T : Type*} [Add D] [Sub T]
    [ConditionallyCompleteLattice T] [OrderTop T]
    (g h : D → T) (t s : D) :
    g (t + s) - h s ≤ minDeconv g h t :=
  le_ciSup_of_le (OrderTop.bddAbove _) s le_rfl

/-- Elim: the (max,+) deconvolution lies below every term,
`maxDeconv g h t ≤ g (t + s) - h s`. -/
theorem maxDeconv_le_sub {D T : Type*} [Add D] [Sub T]
    [ConditionallyCompleteLattice T] [OrderBot T]
    (g h : D → T) (t s : D) :
    maxDeconv g h t ≤ g (t + s) - h s :=
  ciInf_le_of_le (OrderBot.bddBelow _) s le_rfl

/-- Intro: a uniform bound over all terms bounds the (min,+) deconvolution
from above. -/
theorem minDeconv_le {D T : Type*} [Add D] [Nonempty D] [Sub T]
    [ConditionallyCompleteLattice T] {g h : D → T} {x : T} {t : D}
    (hb : ∀ s, g (t + s) - h s ≤ x) :
    minDeconv g h t ≤ x :=
  ciSup_le hb

/-- Intro: a uniform bound below all terms bounds the (max,+) deconvolution
from below. -/
theorem le_maxDeconv {D T : Type*} [Add D] [Nonempty D] [Sub T]
    [ConditionallyCompleteLattice T] {g h : D → T} {x : T} {t : D}
    (hb : ∀ s, x ≤ g (t + s) - h s) :
    x ≤ maxDeconv g h t :=
  le_ciInf hb

/-- `minDeconv g h` is monotone in its first slot when `g` is monotone. -/
theorem monotone_minDeconv {D T : Type*}
    [_root_.AddCommMonoid D] [PartialOrder D]
    [CovariantClass D D (·+·) (·≤·)]
    [CompleteLattice T] [_root_.AddCommMonoid T] [Sub T]
    [OrderedSub T] [CovariantClass T T (·+·) (·≤·)]
    (g h : D → T)
    (hg : Monotone g) : Monotone (minDeconv g h) := by
  intro x y hxy
  unfold minDeconv
  refine iSup_le (fun s => ?_)
  refine le_iSup_of_le s ?_
  have hxs : x + s ≤ y + s := by gcongr
  exact tsub_le_tsub_right (hg hxs) (h s)

/-- `maxDeconv g h` is monotone in its first slot when `g` is monotone. -/
theorem monotone_maxDeconv {D T : Type*}
    [_root_.AddCommMonoid D] [PartialOrder D]
    [CovariantClass D D (·+·) (·≤·)]
    [CompleteLattice T] [_root_.AddCommMonoid T] [Sub T]
    [OrderedSub T] [CovariantClass T T (·+·) (·≤·)]
    (g h : D → T)
    (hg : Monotone g) : Monotone (maxDeconv g h) := by
  intro x y hxy
  unfold maxDeconv
  refine le_iInf (fun s => ?_)
  refine iInf_le_of_le s ?_
  have hxs : x + s ≤ y + s := by gcongr
  exact tsub_le_tsub_right (hg hxs) (h s)


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
  rw [conv_apply, MinPlusExt.toVal_sSup]
  apply le_antisymm
  · refine le_iInf (fun p => ?_)
    exact iInf_le_of_le ⟨_, p.1.1, p.1.2, p.2, rfl⟩ le_rfl
  · refine le_iInf (fun x => ?_)
    obtain ⟨u, s, hus, hx⟩ := x.2
    rw [hx]
    exact iInf_le_of_le ⟨(u, s), hus⟩ le_rfl

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
  rw [conv_apply, MaxPlusExt.toVal_sSup]
  apply le_antisymm
  · refine iSup_le (fun x => ?_)
    obtain ⟨u, s, hus, hx⟩ := x.2
    rw [hx]
    exact le_iSup_of_le ⟨(u, s), hus⟩ le_rfl
  · refine iSup_le (fun p => ?_)
    exact le_iSup_of_le ⟨_, p.1.1, p.1.2, p.2, rfl⟩ le_rfl

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
  rw [minConv_apply_zero, show f 0 = 0 from hf, show g 0 = 0 from hg,
    add_zero]

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

/-- `maxConv` is monotone when its second argument is: a splitting of `x`
widens to a splitting of `y ≥ x` with the slack in the second slot. -/
theorem monotone_maxConv {D T : Type*}
    [_root_.AddCommMonoid D] [LinearOrder D]
    [CanonicallyOrderedAdd D] [Sub D] [OrderedSub D]
    [_root_.AddCommMonoid T] [CompleteLattice T]
    [IsOrderedAddMonoid T] {f g : D → T}
    (hg : Monotone g) :
    Monotone (maxConv f g) := by
  intro x y hxy
  refine maxConv_le fun u s hus => ?_
  calc f u + g s ≤ f u + g (s + (y - x)) :=
        add_le_add le_rfl (hg le_self_add)
    _ ≤ maxConv f g y :=
        add_le_maxConv f g
          (by rw [← add_assoc, hus, add_tsub_cancel_of_le hxy])

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
    rw [MinPlusExt.convUnit_toVal]
    split <;> simp
  iSup F hF := fun t => le_iInf (fun i => hF i t)

/-- Monotonicity of the numeric values cuts out a sub-complete-dioid of
`FminBar`. -/
theorem isSubCompleteDioid_monotone :
    IsSubCompleteDioid
      (fun f : FminBar => Monotone (fun t => (f t).toVal)) where
  add ha hb := fun _ _ hxy => min_le_min (ha hxy) (hb hxy)
  mul {a b} ha hb := fun _ _ hxy => by
    show ((a ⊗ₒ b) _).toVal ≤ ((a ⊗ₒ b) _).toVal
    rw [mul_toVal, mul_toVal]
    exact monotone_minConv ha hb hxy
  eps := fun _ _ _ => le_top
  one := fun x y hxy => by
    show ((convUnit x : MinPlusExt)).toVal
        ≤ ((convUnit y : MinPlusExt)).toVal
    rw [MinPlusExt.convUnit_toVal,
      MinPlusExt.convUnit_toVal]
    split_ifs with hx hy hy
    · exact le_rfl
    · exact le_top
    · exact absurd (le_zero_iff.mp (hy ▸ hxy)) hx
    · exact le_rfl
  iSup F hF := fun _ _ hxy =>
    le_iInf (fun i => (iInf_le _ i).trans ((hF i) hxy))

/-- Non-neg + monotone cut out a sub-complete-dioid. -/
theorem isSubCompleteDioid_FNondecr :
    IsSubCompleteDioid
      (fun f : FminBar =>
        IsNonneg (fun t => (f t).toVal)
          ∧ Monotone (fun t => (f t).toVal)) :=
  isSubCompleteDioid_FPlus.and isSubCompleteDioid_monotone

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
theorem add_ciSup_le {ι : Type*} [Nonempty ι]
    (c y : ℝ≥0) (f : ι → ℝ≥0)
    (h : ∀ i, c + f i ≤ y) : c + ⨆ i, f i ≤ y := by
  have hcy : c ≤ y :=
    le_trans le_self_add (h (Classical.arbitrary ι))
  have hsup : ⨆ i, f i ≤ y - c :=
    ciSup_le (fun i => le_tsub_of_add_le_left (h i))
  exact add_le_of_le_tsub_left_of_le hcy hsup

/-- Lift `g : ℝ≥0 → ℝ≥0` into `Fmin`. -/
def liftFmin (g : ℝ≥0 → ℝ≥0) : Fmin :=
  fun t => ⟨(g t : ℝ≥0∞)⟩

/-- Lift `g : ℝ≥0 → ℝ≥0` into `Fmax`. -/
def liftFmax (g : ℝ≥0 → ℝ≥0) : Fmax :=
  fun t => ⟨((g t : ℝ≥0∞) : WithBot ℝ≥0∞)⟩

/-- `minConv` of lifted functions, valued back in `ℝ≥0`. -/
noncomputable def minConvProj (g h : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t =>
    (conv (liftFmin g) (liftFmin h) t
      : MinPlusNN).toVal.toNNReal

/-- The (min,+) product of lifted values is `g u + h s`. -/
theorem liftFmin_mul (g h : ℝ≥0 → ℝ≥0) (u s : ℝ≥0) :
    ((liftFmin g u ⊗ₒ liftFmin h s : MinPlusNN) : ℝ≥0∞)
      = (g u : ℝ≥0∞) + (h s : ℝ≥0∞) := rfl

/-- `(liftFmin g ∗ liftFmin h)` as an `ℝ≥0∞`-valued infimum. -/
theorem conv_liftFmin_toVal (g h : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    ((conv (liftFmin g) (liftFmin h) t : MinPlusNN) : ℝ≥0∞)
      = ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          ((g p.1.1 + h p.1.2 : ℝ≥0) : ℝ≥0∞) := by
  rw [conv_apply, MinPlusNN.toVal_sSup]
  apply le_antisymm
  · refine le_iInf (fun p => ?_)
    refine iInf_le_of_le
      ⟨liftFmin g p.1.1 ⊗ₒ liftFmin h p.1.2,
        p.1.1, p.1.2, p.2, rfl⟩ ?_
    show ((liftFmin g p.1.1 ⊗ₒ liftFmin h p.1.2 : MinPlusNN)
        : ℝ≥0∞) ≤ _
    rw [liftFmin_mul]; push_cast; rfl
  · refine le_iInf (fun x => ?_)
    obtain ⟨u, s, hus, hx⟩ := x.2
    refine iInf_le_of_le ⟨(u, s), hus⟩ ?_
    rw [show (x.val : ℝ≥0∞)
          = ((liftFmin g u ⊗ₒ liftFmin h s : MinPlusNN)
              : ℝ≥0∞) from congrArg _ hx, liftFmin_mul]
    push_cast; rfl

/-- `minConvProj` as the `ℝ≥0` infimum `⨅_{u+s=t} g u + h s`. -/
theorem minConvProj_eq (g h : ℝ≥0 → ℝ≥0) (t : ℝ≥0) :
    minConvProj g h t
      = ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          (g p.1.1 + h p.1.2) := by
  rw [minConvProj, conv_liftFmin_toVal,
    ← ENNReal.coe_iInf
      (fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
        g p.1.1 + h p.1.2),
    ENNReal.toNNReal_coe]

/-- The projected convolution at the origin is the sum of the origin
values: the only split of `0` is `(0, 0)`. -/
theorem minConvProj_zero_eq (g h : ℝ≥0 → ℝ≥0) :
    minConvProj g h 0 = g 0 + h 0 := by
  rw [minConvProj_eq]
  refine le_antisymm
    (ciInf_le_of_le (OrderBot.bddBelow _) ⟨(0, 0), add_zero 0⟩ le_rfl) ?_
  refine le_ciInf fun p => ?_
  obtain ⟨hu, hs⟩ := add_eq_zero.mp p.2
  rw [hu, hs]

/-- Elim: every split bounds the projected convolution from above,
`minConvProj g h t ≤ g u + h s` whenever `u + s = t`. -/
theorem minConvProj_le_add {g h : ℝ≥0 → ℝ≥0} {u s t : ℝ≥0}
    (hus : u + s = t) :
    minConvProj g h t ≤ g u + h s := by
  rw [minConvProj_eq]
  exact ciInf_le_of_le (OrderBot.bddBelow _) ⟨(u, s), hus⟩ le_rfl

/-- Intro: a bound on every split bounds the projected convolution
from below. -/
theorem le_minConvProj {g h : ℝ≥0 → ℝ≥0} {x t : ℝ≥0}
    (hb : ∀ u s, u + s = t → x ≤ g u + h s) :
    x ≤ minConvProj g h t := by
  rw [minConvProj_eq]
  exact le_ciInf fun p => hb p.1.1 p.1.2 p.2

/-- `minConvProj A` is monotone in its right argument. -/
theorem minConvProj_mono_right (A : ℝ≥0 → ℝ≥0)
    {g g' : ℝ≥0 → ℝ≥0} (h : g ≤ g') :
    minConvProj A g ≤ minConvProj A g' := by
  intro t
  rw [minConvProj_eq, minConvProj_eq]
  refine ciInf_mono (OrderBot.bddBelow _) (fun p => ?_)
  gcongr
  exact h p.1.2

/-- `maxConv` of lifted functions, valued back in `ℝ≥0`. -/
noncomputable def maxConvProj (g h : ℝ≥0 → ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun t =>
    (conv (liftFmax g) (liftFmax h) t
      : MaxPlusNN).toVal.unbotD 0 |>.toNNReal

/-- The (max,+) product of lifted values is `g a + h b`. -/
theorem liftFmax_mul (g h : ℝ≥0 → ℝ≥0) (a b : ℝ≥0) :
    ((liftFmax g a ⊗ₒ liftFmax h b : MaxPlusNN)
        : WithBot ℝ≥0∞)
      = (((g a : ℝ≥0∞) : WithBot ℝ≥0∞))
        + (((h b : ℝ≥0∞) : WithBot ℝ≥0∞)) := rfl

/-- `(liftFmax g ∗ liftFmax h)` as a `WithBot ℝ≥0∞`-valued sup. -/
theorem conv_liftFmax_toVal (g h : ℝ≥0 → ℝ≥0)
    (t : ℝ≥0) :
    ((conv (liftFmax g) (liftFmax h) t : MaxPlusNN)
        : WithBot ℝ≥0∞)
      = ⨆ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t},
          (((g p.1.1 + h p.1.2 : ℝ≥0)
            : ℝ≥0∞) : WithBot ℝ≥0∞) := by
  rw [conv_apply, MaxPlusNN.toVal_sSup]
  apply le_antisymm
  · refine iSup_le (fun x => ?_)
    obtain ⟨u, s, hus, hx⟩ := x.2
    refine le_iSup_of_le ⟨(u, s), hus⟩ ?_
    rw [show (x.val : WithBot ℝ≥0∞)
          = ((liftFmax g u ⊗ₒ liftFmax h s
                : MaxPlusNN) : WithBot ℝ≥0∞)
            from congrArg _ hx, liftFmax_mul]
    push_cast; rfl
  · refine iSup_le (fun p => ?_)
    refine le_iSup_of_le
      ⟨liftFmax g p.1.1 ⊗ₒ liftFmax h p.1.2,
        p.1.1, p.1.2, p.2, rfl⟩ ?_
    show _ ≤ ((liftFmax g p.1.1 ⊗ₒ liftFmax h p.1.2
        : MaxPlusNN) : WithBot ℝ≥0∞)
    rw [liftFmax_mul]; push_cast; rfl

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
  rw [maxConvProj, conv_liftFmax_toVal, hcoe]
  rw [WithBot.unbotD_coe, ENNReal.coe_toNNReal hfin]

/-- Intro: a uniform bound over all splits bounds the projected (max,+)
convolution from above, `maxConvProj g h t ≤ c`. -/
theorem maxConvProj_le {g h : ℝ≥0 → ℝ≥0} {t c : ℝ≥0}
    (hsplit : ∀ u s, u + s = t → g u + h s ≤ c) :
    maxConvProj g h t ≤ c := by
  rw [maxConvProj, conv_liftFmax_toVal]
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
    iSup_le (fun p => by exact_mod_cast hsplit p.1.1 p.1.2 p.2)
  have := ENNReal.toNNReal_mono (by simp) hb
  simpa using this

/-- Elim: a splitting bounds `maxConvProj` from below, given a uniform
bound on all splittings (which keeps the projected supremum finite). -/
theorem add_le_maxConvProj_of_bound {g h : ℝ≥0 → ℝ≥0} {t c : ℝ≥0}
    (hbound : ∀ u s, u + s = t → g u + h s ≤ c)
    {u s : ℝ≥0} (hus : u + s = t) :
    g u + h s ≤ maxConvProj g h t := by
  have hfin : (⨆ q : {q : ℝ≥0 × ℝ≥0 // q.1 + q.2 = t},
      ((g q.1.1 + h q.1.2 : ℝ≥0) : ℝ≥0∞)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top
      (iSup_le fun q => by exact_mod_cast hbound q.1.1 q.1.2 q.2)
  rw [← ENNReal.coe_le_coe, maxConvProj_coe g h t hfin]
  exact le_iSup (fun q : {q : ℝ≥0 × ℝ≥0 // q.1 + q.2 = t} =>
    ((g q.1.1 + h q.1.2 : ℝ≥0) : ℝ≥0∞)) ⟨(u, s), hus⟩

/-- Intro with a leading constant: `c + maxConvProj g h t ≤ y` from the
per-split bounds `c + (g u + h s) ≤ y`. -/
theorem add_maxConvProj_le {g h : ℝ≥0 → ℝ≥0} {t c y : ℝ≥0}
    (hsplit : ∀ u s, u + s = t → c + (g u + h s) ≤ y) :
    c + maxConvProj g h t ≤ y := by
  have hcy : c ≤ y := le_trans le_self_add (hsplit t 0 (add_zero t))
  have hsup : maxConvProj g h t ≤ y - c :=
    maxConvProj_le fun u s hus => le_tsub_of_add_le_left (hsplit u s hus)
  exact add_le_of_le_tsub_left_of_le hcy hsup

/-- `⨆ i, g i = - ⨅ i, - g i` for a bounded-above family: indexed form of
`csInf_neg`. -/
theorem ciSup_eq_neg_ciInf_neg {ι : Type} [Nonempty ι]
    {T : Type*} [ConditionallyCompleteLattice T] [_root_.AddGroup T]
    [AddLeftMono T] [AddRightMono T]
    (g : ι → T) (hbdd : BddAbove (Set.range g)) :
    (⨆ i, g i) = - ⨅ i, - g i := by
  rw [← sInf_range, Set.range_comp' Neg.neg g, Set.image_neg_eq_neg,
    csInf_neg (Set.range_nonempty g) hbdd, neg_neg, sSup_range]

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
  rw [← ciSup_eq_neg_ciInf_neg _ hbR,
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
