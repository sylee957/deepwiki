import Book.ScalarDioids

/-! # Dioid-valued functions
Dioid-valued functions `D → T`: pointwise sum, convolution `∗`, and the
resulting complete-dioid structure on the function space. The numeric
(min,plus)/(max,plus) readings of this structure — `minConv`/`maxConv`
with their intro and elim API — live in `Book.FunctionDioids`. -/

namespace DeepWiki

open Algebra
open scoped Classical NNReal ENNReal Algebra.Bridge

/-- Pointwise dioid sum of functions: `(f ⊕ g) t = f t ⊕ₒ g t`. -/
def psum {D T : Type*} [CompleteDioid T]
    (f g : D → T) : D → T :=
  fun t => f t ⊕ₒ g t

/-- Convolution `(f ∗ g) t = ⨆ {f u ⊗ₒ g s | u + s = t}`. -/
noncomputable def conv {D T : Type*} [Add D]
    [CompleteDioid T]
    (f g : D → T) : D → T := fun t =>
  CompleteDioid.sSup
    { x | ∃ u s : D, u + s = t ∧ x = f u ⊗ₒ g s }

/-- Unfolds `conv f g t` to its defining supremum. -/
theorem conv_apply {D T : Type*} [Add D] [CompleteDioid T]
    (f g : D → T) (t : D) :
    conv f g t
      = CompleteDioid.sSup
          { x | ∃ u s, u + s = t ∧ x = f u ⊗ₒ g s } :=
  rfl

/-- Convolution zero `𝟘`: the constant `εₒ` function. -/
def convZero {D T : Type*} [CompleteDioid T] :
    D → T := fun _ => εₒ

/-- Convolution unit `𝟙`: `eₒ` at `0`, `εₒ` elsewhere. -/
noncomputable def convUnit {D T : Type*} [Zero D]
    [CompleteDioid T] : D → T :=
  fun t => if t = 0 then eₒ else εₒ

/-- Numeric reading of `convUnit` on `MinPlusNN`: `0` at the origin, `⊤` elsewhere. -/
theorem MinPlusNN.convUnit_toVal {D : Type*} [Zero D] (t : D) :
    (convUnit t : MinPlusNN).toVal = if t = 0 then (0 : ℝ≥0∞) else ⊤ := by
  unfold convUnit; split <;> rfl

/-- Numeric reading of `convUnit` on `MinPlusExt`: `0` at the origin, `⊤` elsewhere. -/
theorem MinPlusExt.convUnit_toVal {D : Type*} [Zero D] (t : D) :
    (convUnit t : MinPlusExt).toVal
      = if t = 0 then (0 : WithTop (WithBot ℝ)) else ⊤ := by
  unfold convUnit; split <;> rfl

/-- Numeric reading of `convUnit` on `MaxPlusNN`: `0` at the origin, `⊥` elsewhere. -/
theorem MaxPlusNN.convUnit_toVal {D : Type*} [Zero D] (t : D) :
    (convUnit t : MaxPlusNN).toVal = if t = 0 then (0 : WithBot ℝ≥0∞) else ⊥ := by
  unfold convUnit; split <;> rfl

/-- `convUnit t ≼ₒ f t` once `eₒ ≼ₒ f 0`: off the origin `convUnit` is the
dioid bottom `εₒ`. -/
theorem convUnit_le {D T : Type*} [Zero D] [CompleteDioid T]
    {f : D → T} (h0 : eₒ ≼ₒ f 0) (t : D) :
    convUnit t ≼ₒ f t := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [convUnit, if_pos rfl]; exact h0
  · rw [convUnit, if_neg ht]; exact OrderBot.bot_le _

/-- Pointwise supremum of a family of functions. -/
noncomputable def funSup {D : Type u} {T : Type u}
    [CompleteDioid T] {ι : Type u}
    (F : ι → D → T) : D → T :=
  fun t => CompleteDioid.iSup (fun i => F i t)

section Join
variable {T : Type*} [Algebra.CompleteDioid T]
open Algebra

/-- `a ≼ₒ a ⊕ₒ b`: a join dominates its left summand. -/
theorem le_oplus_left (a b : T) : a ≼ₒ a ⊕ₒ b := by
  show a ⊕ₒ (a ⊕ₒ b) = a ⊕ₒ b
  rw [← add_assoc, Dioid.oplus_idem]

/-- `b ≼ₒ a ⊕ₒ b`: a join dominates its right summand. -/
theorem le_oplus_right (a b : T) : b ≼ₒ a ⊕ₒ b := by
  show b ⊕ₒ (a ⊕ₒ b) = a ⊕ₒ b
  rw [add_comm a b,
    ← add_assoc, Dioid.oplus_idem]

/-- Join is the least upper bound: `a,b ≼ₒ c → a ⊕ₒ b ≼ₒ c`. -/
theorem oplus_le (a b c : T)
    (ha : a ≼ₒ c) (hb : b ≼ₒ c) : a ⊕ₒ b ≼ₒ c := by
  show (a ⊕ₒ b) ⊕ₒ c = c
  rw [add_assoc]
  show a ⊕ₒ (b ⊕ₒ c) = c
  rw [(by exact hb : b ⊕ₒ c = c)]; exact ha

/-- Join is monotone in both arguments. -/
theorem oplus_le_oplus {a b c d : T}
    (h1 : a ≼ₒ c) (h2 : b ≼ₒ d) : a ⊕ₒ b ≼ₒ c ⊕ₒ d :=
  oplus_le _ _ _ (le_trans h1 (le_oplus_left c d))
    (le_trans h2 (le_oplus_right c d))

end Join

open Algebra

/-- Three-fold convolution `⨆ {(f u ⊗ₒ g v) ⊗ₒ h z | u+v+z = t}`. -/
noncomputable def triple {D T : Type*} [Add D]
    [CompleteDioid T]
    (f g h : D → T) (t : D) : T :=
  CompleteDioid.sSup
    { x | ∃ u v z : D,
        u + v + z = t ∧ x = (f u ⊗ₒ g v) ⊗ₒ h z }

/-- `(f ∗ g) ∗ h = triple f g h`. -/
theorem conv_conv_eq_triple_left {D T : Type*}
    [_root_.AddCommMonoid D] [CompleteDioid T]
    (f g h : D → T) (t : D) :
    conv (conv f g) h t = triple f g h t := by
  apply le_antisymm
  · rw [conv_apply]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨w, z, hwz, rfl⟩
    rw [conv_apply, Algebra.sSup_mul]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro y ⟨q, ⟨u, v, huv, rfl⟩, rfl⟩
    refine CompleteDioid.le_sSup _ _ ⟨u, v, z, ?_, rfl⟩
    rw [huv]; exact hwz
  · rw [triple]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, v, z, hsum, rfl⟩
    rw [conv_apply]
    refine le_trans ?_ (CompleteDioid.le_sSup _
      ((conv f g (u+v)) ⊗ₒ h z) ⟨u+v, z, hsum, rfl⟩)
    refine mul_le_mul_right ?_ _
    rw [conv_apply]
    exact CompleteDioid.le_sSup _ _ ⟨u, v, rfl, rfl⟩

/-- `f ∗ (g ∗ h) = triple f g h`. -/
theorem conv_conv_eq_triple_right {D T : Type*}
    [_root_.AddCommMonoid D] [CompleteDioid T]
    (f g h : D → T) (t : D) :
    conv f (conv g h) t = triple f g h t := by
  apply le_antisymm
  · rw [conv_apply]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, p, hup, rfl⟩
    rw [conv_apply, CompleteDioid.mul_sSup]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro y ⟨q, ⟨v, z, hvz, rfl⟩, rfl⟩
    refine CompleteDioid.le_sSup _ _ ⟨u, v, z, ?_, ?_⟩
    · rw [add_assoc, hvz]; exact hup
    · exact (mul_assoc (f u) (g v) (h z)).symm
  · rw [triple]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, v, z, hsum, rfl⟩
    rw [conv_apply]
    refine le_trans ?_ (CompleteDioid.le_sSup _
      (f u ⊗ₒ (conv g h (v+z)))
      ⟨u, v+z, by rw [← add_assoc]; exact hsum, rfl⟩)
    rw [mul_assoc]
    refine mul_le_mul_left ?_ _
    rw [conv_apply]
    exact CompleteDioid.le_sSup _ _ ⟨v, z, rfl, rfl⟩

/-- Convolution is associative: `(f ∗ g) ∗ h = f ∗ (g ∗ h)`. -/
theorem conv_assoc {D T : Type*}
    [_root_.AddCommMonoid D] [CompleteDioid T]
    (f g h : D → T) :
    conv (conv f g) h = conv f (conv g h) := by
  funext t
  rw [conv_conv_eq_triple_left, conv_conv_eq_triple_right]

/-- Convolution is commutative: `f ∗ g = g ∗ f`. -/
theorem conv_comm {D T : Type*}
    [_root_.AddCommMonoid D] [CompleteDioid T]
    (f g : D → T) : conv f g = conv g f := by
  funext t
  show CompleteDioid.sSup _ = CompleteDioid.sSup _
  congr 1
  ext x
  constructor
  · rintro ⟨u, s, hus, rfl⟩
    exact ⟨s, u, by rw [add_comm]; exact hus, mul_comm _ _⟩
  · rintro ⟨u, s, hus, rfl⟩
    exact ⟨s, u, by rw [add_comm]; exact hus,
      mul_comm _ _⟩

/-- `convUnit` is a left identity: `convUnit ∗ f = f`. -/
theorem convUnit_left {D T : Type*} [AddZeroClass D]
    [CompleteDioid T]
    (f : D → T) : conv convUnit f = f := by
  funext t
  apply le_antisymm
  · rw [conv_apply]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, s, hus, rfl⟩
    by_cases hu : u = 0
    · have hs : s = t := by
        rw [← hus, hu, zero_add]
      rw [convUnit, if_pos hu, hs]
      exact le_of_eq (MulMonoid.one_otimes (f t))
    · rw [convUnit, if_neg hu, Semiring.eps_otimes]
      exact bot_le
  · rw [conv_apply]
    refine CompleteDioid.le_sSup _ _
      ⟨0, t, by rw [zero_add], ?_⟩
    rw [convUnit, if_pos rfl]
    exact (MulMonoid.one_otimes (f t)).symm

/-- `convUnit` is a right identity: `f ∗ convUnit = f`. -/
theorem convUnit_right {D T : Type*}
    [_root_.AddCommMonoid D] [CompleteDioid T]
    (f : D → T) : conv f convUnit = f := by
  rw [conv_comm, convUnit_left]

/-- Left distributivity: `f ∗ (g ⊕ h) = (f ∗ g) ⊕ (f ∗ h)`. -/
theorem conv_distrib {D T : Type*} [Add D]
    [CompleteDioid T]
    (f g h : D → T) :
    conv f (psum g h) = psum (conv f g) (conv f h) := by
  funext t
  apply le_antisymm
  · rw [conv_apply]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, s, hus, rfl⟩
    have hd : f u ⊗ₒ (psum g h s)
        = (f u ⊗ₒ g s) ⊕ₒ (f u ⊗ₒ h s) :=
      left_distrib (f u) (g s) (h s)
    show f u ⊗ₒ (psum g h s) ≼ₒ _
    rw [hd]
    refine oplus_le_oplus ?_ ?_
    · exact conv_apply f g t ▸
        CompleteDioid.le_sSup _ _ ⟨u, s, hus, rfl⟩
    · exact conv_apply f h t ▸
        CompleteDioid.le_sSup _ _ ⟨u, s, hus, rfl⟩
  · refine oplus_le _ _ _ ?_ ?_
    · rw [conv_apply]
      refine CompleteDioid.sSup_le _ _ ?_
      rintro x ⟨u, s, hus, rfl⟩
      rw [conv_apply]
      refine le_trans ?_ (CompleteDioid.le_sSup _
        (f u ⊗ₒ (psum g h s)) ⟨u, s, hus, rfl⟩)
      exact mul_le_mul_left (le_oplus_left _ _) _
    · rw [conv_apply]
      refine CompleteDioid.sSup_le _ _ ?_
      rintro x ⟨u, s, hus, rfl⟩
      rw [conv_apply]
      refine le_trans ?_ (CompleteDioid.le_sSup _
        (f u ⊗ₒ (psum g h s)) ⟨u, s, hus, rfl⟩)
      exact mul_le_mul_left (le_oplus_right _ _) _

/-- Right distributivity: `(g ⊕ h) ∗ f = (g ∗ f) ⊕ (h ∗ f)`. -/
theorem conv_distrib_right {D T : Type*}
    [_root_.AddCommMonoid D] [CompleteDioid T]
    (f g h : D → T) :
    conv (psum g h) f = psum (conv g f) (conv h f) := by
  rw [conv_comm, conv_distrib, conv_comm g f,
    conv_comm h f]

/-- `convZero` left-absorbs: `convZero ∗ f = convZero`. -/
theorem convZero_left {D T : Type*} [Add D]
    [CompleteDioid T]
    (f : D → T) :
    conv convZero f = convZero := by
  funext t
  apply le_antisymm
  · rw [conv_apply]
    refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨u, s, hus, rfl⟩
    rw [show convZero u = εₒ from rfl,
      Semiring.eps_otimes]
    exact bot_le
  · exact bot_le

/-- `convZero` right-absorbs: `f ∗ convZero = convZero`. -/
theorem convZero_right {D T : Type*}
    [_root_.AddCommMonoid D] [CompleteDioid T]
    (f : D → T) :
    conv f convZero = convZero := by
  rw [conv_comm, convZero_left]

/-- Complete-dioid structure on `D → T` via `psum`/`conv`. -/
noncomputable instance funCompleteDioid
    {D : Type u} [_root_.AddCommMonoid D]
    {T : Type u} [CompleteDioid T] :
    CompleteDioid (D → T) where
  add := psum
  zero := convZero
  mul := conv
  one := convUnit
  oplus_assoc f g h := funext fun t => add_assoc _ _ _
  eps_oplus f := funext fun t => zero_add _
  oplus_eps f := funext fun t => add_zero _
  oplus_comm f g := funext fun t => add_comm _ _
  otimes_assoc := conv_assoc
  one_otimes := convUnit_left
  otimes_one := convUnit_right
  left_distrib := conv_distrib
  right_distrib f g h := conv_distrib_right h f g
  eps_otimes := convZero_left
  otimes_eps := convZero_right
  otimes_comm := conv_comm
  oplus_idem f := funext fun t => Dioid.oplus_idem _
  iSup := funSup
  le_iSup F i :=
    funext fun t => CompleteDioid.le_iSup (fun j => F j t) i
  iSup_le F b hb :=
    funext fun t =>
      CompleteDioid.iSup_le (fun i => F i t) (b t)
        (fun i => congrFun (hb i) t)
  mul_iSup a F := by
    funext t
    show conv a (funSup F) t
        = funSup (fun i => conv a (F i)) t
    rw [conv_apply]
    apply le_antisymm
    · refine CompleteDioid.sSup_le _ _ ?_
      rintro x ⟨u, s, hus, rfl⟩
      show a u ⊗ₒ funSup F s ≼ₒ _
      rw [show funSup F s
          = CompleteDioid.iSup (fun i => F i s) from rfl,
        CompleteDioid.mul_iSup]
      refine CompleteDioid.iSup_le _ _ ?_
      intro i
      refine le_trans ?_
        (CompleteDioid.le_iSup
          (fun i => conv a (F i) t) i)
      rw [conv_apply]
      exact CompleteDioid.le_sSup _ _ ⟨u, s, hus, rfl⟩
    · refine CompleteDioid.iSup_le _ _ ?_
      intro i
      show conv a (F i) t ≼ₒ _
      rw [conv_apply]
      refine CompleteDioid.sSup_le _ _ ?_
      rintro x ⟨u, s, hus, rfl⟩
      refine le_trans ?_
        (CompleteDioid.le_sSup _ _ ⟨u, s, hus, rfl⟩)
      show a u ⊗ₒ F i s ≼ₒ a u ⊗ₒ funSup F s
      rw [show funSup F s
          = CompleteDioid.iSup (fun i => F i s) from rfl]
      exact mul_le_mul_left
        (CompleteDioid.le_iSup (fun i => F i s) i) _

/-- Convolution as `⨆ {f (t - s) ⊗ₒ g s | s ≤ t}` when `D` has subtraction. -/
theorem conv_eq_sub {D T : Type*}
    [_root_.AddCommMonoid D] [PartialOrder D]
    [CanonicallyOrderedAdd D] [Sub D] [OrderedSub D]
    [AddLeftReflectLE D] [CompleteDioid T]
    (f g : D → T) (t : D) :
    conv f g t
      = CompleteDioid.sSup
          { x | ∃ s : D,
              s ≤ t ∧ x = f (t - s) ⊗ₒ g s } := by
  show CompleteDioid.sSup _ = CompleteDioid.sSup _
  congr 1
  ext x
  constructor
  · rintro ⟨u, s, hus, rfl⟩
    refine ⟨s, ?_, ?_⟩
    · rw [← hus]; exact le_add_self
    · rw [show t - s = u by
        rw [← hus, add_tsub_cancel_right]]
  · rintro ⟨s, hst, rfl⟩
    refine ⟨t - s, s, ?_, rfl⟩
    rw [tsub_add_cancel_of_le hst]

/-- Add a constant on the right: `(addConst f K) t = f t ⊗ₒ K`. -/
def addConst {D T : Type*} [CompleteDioid T]
    (f : D → T) (K : T) : D → T :=
  fun t => f t ⊗ₒ K

/-- A right constant commutes through convolution. -/
theorem conv_add_const {D T : Type*} [Add D]
    [CompleteDioid T]
    (f g : D → T) (K : T) :
    addConst (conv f g) K = conv f (addConst g K) := by
  funext t
  show (conv f g t) ⊗ₒ K = _
  rw [conv_apply, conv_apply, Algebra.sSup_mul]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨u, s, hus, rfl⟩, rfl⟩
    exact ⟨u, s, hus, by
      show (f u ⊗ₒ g s) ⊗ₒ K = f u ⊗ₒ (addConst g K s)
      rw [show addConst g K s = g s ⊗ₒ K from rfl,
        mul_assoc]⟩
  · rintro ⟨u, s, hus, rfl⟩
    refine ⟨f u ⊗ₒ g s, ⟨u, s, hus, rfl⟩, ?_⟩
    show (f u ⊗ₒ g s) ⊗ₒ K = f u ⊗ₒ (addConst g K s)
    rw [show addConst g K s = g s ⊗ₒ K from rfl,
      mul_assoc]

/-- Convolution is monotone in its right argument. -/
theorem conv_le_conv_right {D : Type u}
    [_root_.AddCommMonoid D] {T : Type u}
    [CompleteDioid T] (f : D → T)
    {g g' : D → T} (h : g ≼ₒ g') :
    conv f g ≼ₒ conv f g' :=
  mul_le_mul_left h f

/-- Convolution is monotone in its left argument. -/
theorem conv_le_conv_left {D : Type u}
    [_root_.AddCommMonoid D] {T : Type u}
    [CompleteDioid T] {f f' : D → T}
    (h : f ≼ₒ f') (g : D → T) :
    conv f g ≼ₒ conv f' g :=
  mul_le_mul_right h g

end DeepWiki
