import Book.Order
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Insert
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! # Complete dioids
Dioids with arbitrary `iSup`/`sSup` and lower semi-continuity
`a ⊗ sSup s = sSup (a ⊗ ·) '' s`, plus the sub-complete-dioid builder. -/

namespace DeepWiki

namespace Algebra

open scoped Bridge

/-- `Dioid` with arbitrary `iSup` that is a LUB and lower semi-continuous. -/
class CompleteDioid (T : Type u) extends Dioid T where
  iSup : {ι : Type u} → (ι → T) → T
  le_iSup : ∀ {ι : Type u} (f : ι → T) (i : ι),
    f i ≼ₒ iSup f
  iSup_le : ∀ {ι : Type u} (f : ι → T) (b : T),
    (∀ i, f i ≼ₒ b) → iSup f ≼ₒ b
  mul_iSup : ∀ {ι : Type u} (a : T) (f : ι → T),
    a ⊗ₒ iSup f = iSup (fun i => a ⊗ₒ f i)

namespace CompleteDioid

/-- Supremum of a set `s`, via `iSup` over its subtype. -/
def sSup {T : Type*} [CompleteDioid T] (s : Set T) : T :=
  CompleteDioid.iSup (fun x : s => x.val)

/-- Members of `s` are `≼ₒ`-below `sSup s`. -/
theorem le_sSup {T : Type*} [CompleteDioid T]
    (s : Set T) (a : T) (h : a ∈ s) : a ≼ₒ sSup s :=
  CompleteDioid.le_iSup (fun x : s => x.val) ⟨a, h⟩

/-- `sSup s` is the least upper bound of `s`. -/
theorem sSup_le {T : Type*} [CompleteDioid T]
    (s : Set T) (b : T) (h : ∀ a ∈ s, a ≼ₒ b) :
    sSup s ≼ₒ b :=
  CompleteDioid.iSup_le _ b (fun x => h x.val x.2)

/-- `≼ₒ` half of `mul_sSup`: `a ⊗ sSup s ≼ₒ sSup (a ⊗ ·) '' s`. -/
theorem mul_sSup_le {T : Type*} [CompleteDioid T]
    (a : T) (s : Set T) :
    a ⊗ₒ sSup s ≼ₒ sSup ((fun b => a ⊗ₒ b) '' s) := by
  rw [show a ⊗ₒ sSup s
      = CompleteDioid.iSup (fun x : s => a ⊗ₒ x.val) from
    CompleteDioid.mul_iSup a _]
  apply CompleteDioid.iSup_le
  intro x
  exact CompleteDioid.le_sSup _ _ ⟨x.val, x.2, rfl⟩

end CompleteDioid

namespace Bridge

/-- Mathlib `SupSet` from `CompleteDioid.sSup`. -/
scoped instance instSupSet
    {T : Type*} [CompleteDioid T] : SupSet T where
  sSup := CompleteDioid.sSup

/-- Mathlib `CompleteSemilatticeSup` bridging `sSup` to `IsLUB`. -/
scoped instance instCompleteSemilatticeSup
    {T : Type*} [CompleteDioid T] :
    CompleteSemilatticeSup T where
  toPartialOrder := instPartialOrder
  toSupSet := instSupSet
  isLUB_sSup s :=
    ⟨fun a ha => CompleteDioid.le_sSup s a ha,
     fun b hb => CompleteDioid.sSup_le s b hb⟩

end Bridge

example {T : Type*} [CompleteDioid T] (s : Set T) :
    IsLUB s (CompleteDioid.sSup s) := isLUB_sSup s

/-- Lower semi-continuity: `a ⊗ sSup s = sSup (a ⊗ ·) '' s`. -/
theorem CompleteDioid.mul_sSup {T : Type*}
    [CompleteDioid T] (a : T) (s : Set T) :
    a ⊗ₒ CompleteDioid.sSup s
      = CompleteDioid.sSup ((fun b => a ⊗ₒ b) '' s) := by
  apply le_antisymm
  · exact CompleteDioid.mul_sSup_le a s
  · refine CompleteDioid.sSup_le _ _ ?_
    rintro x ⟨b, hb, rfl⟩
    exact mul_le_mul_left (CompleteDioid.le_sSup s b hb) a

/-- Right lower semi-continuity: `sSup s ⊗ a = sSup (· ⊗ a) '' s`. -/
theorem sSup_mul {T : Type*} [CompleteDioid T]
    (a : T) (s : Set T) :
    (CompleteDioid.sSup s) ⊗ₒ a
      = CompleteDioid.sSup ((fun b => b ⊗ₒ a) '' s) := by
  rw [mul_comm, CompleteDioid.mul_sSup]
  congr 1
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, mul_comm y a⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, mul_comm a y⟩

/-- Binary join `a ⊔ b` as `sSup {a, b}`. -/
def sup {T : Type*} [CompleteDioid T] (a b : T) : T :=
  CompleteDioid.sSup {a, b}

/-- `⊗` distributes over binary `sup`. -/
theorem mul_sup {T : Type*} [CompleteDioid T]
    (a b c : T) :
    a ⊗ₒ sup b c = sup (a ⊗ₒ b) (a ⊗ₒ c) := by
  unfold sup
  rw [CompleteDioid.mul_sSup]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨b, Or.inl rfl, rfl⟩
    · exact ⟨c, Or.inr rfl, rfl⟩

/-- Greatest element `⊤ₒ`, as `sSup Set.univ`. -/
def top (T : Type*) [CompleteDioid T] : T :=
  CompleteDioid.sSup Set.univ

/-- Notation `⊤ₒ[T]` for `top T`. -/
scoped notation:max "⊤ₒ[" T "]" => top T

/-- Everything is `≼ₒ`-below `⊤ₒ`. -/
theorem le_top {T : Type*} [CompleteDioid T] (a : T) :
    a ≼ₒ ⊤ₒ[T] :=
  CompleteDioid.le_sSup Set.univ a (Set.mem_univ a)

/-- `⊤ₒ` absorbs under `⊕`: `⊤ₒ ⊕ a = ⊤ₒ`. -/
theorem top_oplus {T : Type*} [CompleteDioid T] (a : T) :
    ⊤ₒ[T] ⊕ₒ a = ⊤ₒ[T] := by
  have h : a ⊕ₒ ⊤ₒ[T] = ⊤ₒ[T] := le_top a
  rw [add_comm, h]

/-- `εₒ ⊗ ⊤ₒ = εₒ` (`εₒ` is absorbing). -/
theorem eps_otimes_top {T : Type*} [CompleteDioid T] :
    εₒ ⊗ₒ ⊤ₒ[T] = εₒ :=
  zero_mul (top T)

/-- `⊤ₒ ⊗ εₒ = εₒ` (`εₒ` is absorbing). -/
theorem top_otimes_eps {T : Type*} [CompleteDioid T] :
    ⊤ₒ[T] ⊗ₒ εₒ = εₒ :=
  mul_zero (top T)

/-- `sSup {a, b} = a ⊕ b`. -/
theorem sSup_pair {T : Type*} [CompleteDioid T]
    (a b : T) : CompleteDioid.sSup {a, b} = a ⊕ₒ b := by
  apply le_antisymm
  · refine CompleteDioid.sSup_le _ _ ?_
    intro x hx
    rcases hx with hx | hx
    · show x ⊕ₒ (a ⊕ₒ b) = a ⊕ₒ b
      rw [hx, ← add_assoc, Dioid.oplus_idem]
    · rw [Set.mem_singleton_iff] at hx
      show x ⊕ₒ (a ⊕ₒ b) = a ⊕ₒ b
      rw [hx, add_comm a b,
        ← add_assoc, Dioid.oplus_idem]
  · have ha := CompleteDioid.le_sSup ({a, b} : Set T) a
      (by simp)
    have hb := CompleteDioid.le_sSup ({a, b} : Set T) b
      (by simp)
    show (a ⊕ₒ b) ⊕ₒ CompleteDioid.sSup {a, b}
      = CompleteDioid.sSup {a, b}
    rw [add_assoc, hb, ha]

/-- `a ≼ₒ b ↔ sSup {a, b} = b`. -/
theorem le_iff_sSup_pair {T : Type*} [CompleteDioid T]
    {a b : T} :
    a ≼ₒ b ↔ CompleteDioid.sSup {a, b} = b := by
  rw [sSup_pair]; rfl

/-- Right residual `b ⊘ a`: greatest `x` with `x ⊗ a ≼ₒ b`. -/
def resid {T : Type*} [CompleteDioid T] (b a : T) : T :=
  CompleteDioid.sSup { x | x ⊗ₒ a ≼ₒ b }

/-- Notation `b ⊘ₒ a` for the residual `resid b a`. -/
scoped notation:70 b:70 " ⊘ₒ " a:71 => resid b a

/-- Counit of the residuation: `(b ⊘ a) ⊗ a ≼ₒ b`. -/
theorem resid_mul_le {T : Type*} [CompleteDioid T]
    (b a : T) : (b ⊘ₒ a) ⊗ₒ a ≼ₒ b := by
  rw [resid, sSup_mul]
  refine CompleteDioid.sSup_le _ _ ?_
  rintro y ⟨x, hx, rfl⟩
  exact hx

/-- Adjunction: `x ⊗ a ≼ₒ b ↔ x ≼ₒ b ⊘ a`. -/
theorem mul_le_iff_le_resid {T : Type*}
    [CompleteDioid T] (x a b : T) :
    x ⊗ₒ a ≼ₒ b ↔ x ≼ₒ b ⊘ₒ a := by
  constructor
  · intro h
    exact CompleteDioid.le_sSup _ x h
  · intro h
    exact le_trans (mul_le_mul_right h a)
      (resid_mul_le b a)

/-- Unit of the residuation: `x ≼ₒ (x ⊗ a) ⊘ a`. -/
theorem le_resid_mul {T : Type*} [CompleteDioid T]
    (x a : T) : x ≼ₒ (x ⊗ₒ a) ⊘ₒ a :=
  (mul_le_iff_le_resid x a (x ⊗ₒ a)).mp (le_refl _)

/-- `b ⊘ a` is monotone in the numerator `b`. -/
theorem resid_mono {T : Type*} [CompleteDioid T]
    {b b' : T} (a : T) (h : b ≼ₒ b') :
    b ⊘ₒ a ≼ₒ b' ⊘ₒ a := by
  rw [← mul_le_iff_le_resid]
  exact le_trans (resid_mul_le b a) h

/-- `b ⊘ a` is antitone in the denominator `a`. -/
theorem resid_antitone {T : Type*} [CompleteDioid T]
    (b : T) {a a' : T} (h : a ≼ₒ a') :
    b ⊘ₒ a' ≼ₒ b ⊘ₒ a := by
  rw [← mul_le_iff_le_resid]
  exact le_trans (mul_le_mul_left h (b ⊘ₒ a'))
    (resid_mul_le b a')

/-- `P` is closed under `⊕`, `⊗`, `εₒ`, `eₒ`, and `iSup`. -/
structure IsSubCompleteDioid {T : Type u}
    [CompleteDioid T] (P : T → Prop) : Prop where
  add : ∀ {a b}, P a → P b → P (a ⊕ₒ b)
  mul : ∀ {a b}, P a → P b → P (a ⊗ₒ b)
  eps : P εₒ
  one : P eₒ
  iSup : ∀ {ι : Type u} (f : ι → T),
    (∀ i, P (f i)) → P (CompleteDioid.iSup f)

/-- `CompleteDioid` on the subtype `{x // P x}` of a closed predicate `P`. -/
@[reducible] noncomputable def
    IsSubCompleteDioid.toCompleteDioid
    {T : Type u} [CompleteDioid T] {P : T → Prop}
    (h : IsSubCompleteDioid P) :
    CompleteDioid {x : T // P x} where
  add a b := ⟨a.1 ⊕ₒ b.1, h.add a.2 b.2⟩
  zero := ⟨εₒ, h.eps⟩
  mul a b := ⟨a.1 ⊗ₒ b.1, h.mul a.2 b.2⟩
  one := ⟨eₒ, h.one⟩
  oplus_assoc _ _ _ := Subtype.ext (add_assoc _ _ _)
  eps_oplus _ := Subtype.ext (zero_add _)
  oplus_eps _ := Subtype.ext (add_zero _)
  oplus_comm _ _ := Subtype.ext (add_comm _ _)
  otimes_assoc _ _ _ := Subtype.ext (mul_assoc _ _ _)
  one_otimes _ := Subtype.ext (one_mul _)
  otimes_one _ := Subtype.ext (mul_one _)
  left_distrib _ _ _ := Subtype.ext (mul_add _ _ _)
  right_distrib _ _ _ := Subtype.ext (add_mul _ _ _)
  eps_otimes _ := Subtype.ext (zero_mul _)
  otimes_eps _ := Subtype.ext (mul_zero _)
  otimes_comm _ _ := Subtype.ext (mul_comm _ _)
  oplus_idem _ := Subtype.ext (Dioid.oplus_idem _)
  iSup f := ⟨CompleteDioid.iSup (fun i => (f i).1),
    h.iSup _ (fun i => (f i).2)⟩
  le_iSup f i := Subtype.ext (by
    show (f i).1 ⊕ₒ CompleteDioid.iSup _
        = CompleteDioid.iSup _
    exact CompleteDioid.le_iSup (fun i => (f i).1) i)
  iSup_le f b hb := Subtype.ext (by
    show CompleteDioid.iSup _ ⊕ₒ b.1 = b.1
    exact CompleteDioid.iSup_le (fun i => (f i).1) b.1
      (fun i => congrArg Subtype.val (hb i)))
  mul_iSup a f := Subtype.ext (by
    show a.1 ⊗ₒ CompleteDioid.iSup _
        = CompleteDioid.iSup _
    exact CompleteDioid.mul_iSup a.1 (fun i => (f i).1))

namespace IsSubCompleteDioid
variable {T : Type u} [CompleteDioid T] {P : T → Prop}
    (h : IsSubCompleteDioid P)

/-- Coercion commutes with subtype `⊕`. -/
theorem coe_add (a b : {x // P x}) :
    letI := h.toCompleteDioid
    ((a ⊕ₒ b : {x // P x}) : T) = (a : T) ⊕ₒ (b : T) :=
  rfl

/-- Coercion commutes with subtype `⊗`. -/
theorem coe_mul (a b : {x // P x}) :
    letI := h.toCompleteDioid
    ((a ⊗ₒ b : {x // P x}) : T) = (a : T) ⊗ₒ (b : T) :=
  rfl

/-- Coercion sends subtype `εₒ` to `εₒ`. -/
theorem coe_eps :
    letI := h.toCompleteDioid
    ((εₒ : {x // P x}) : T) = εₒ :=
  rfl

/-- Coercion sends subtype `eₒ` to `eₒ`. -/
theorem coe_one :
    letI := h.toCompleteDioid
    ((eₒ : {x // P x}) : T) = eₒ :=
  rfl

/-- Coercion commutes with subtype `iSup`. -/
theorem coe_iSup {ι : Type u} (f : ι → {x // P x}) :
    letI := h.toCompleteDioid
    ((CompleteDioid.iSup f : {x // P x}) : T)
      = CompleteDioid.iSup (fun i => (f i : T)) :=
  rfl

end IsSubCompleteDioid

end Algebra

end DeepWiki
