import Book.CompleteDioids

/-! # Sub-dioid builders
Predicate-builders cutting a sub-`Dioid` / sub-`CompleteDioid` out of an ambient
one: `IsSubDioid` (closed under `⊕`, `⊗`, `εₒ`, `eₒ`) and `IsSubCompleteDioid`
(additionally closed under `iSup`), each with a `toDioid`/`toCompleteDioid`
giving the structure on the subtype `{x // P x}`. -/

namespace DeepWiki

namespace Algebra

open scoped Bridge

/-- `P` is closed under `⊕ₒ`, `⊗ₒ`, `εₒ`, `eₒ` — a sub-`Dioid` predicate
(the `Dioid`-level analogue of `IsSubCompleteDioid`, with no `iSup`). -/
structure IsSubDioid {T : Type*} [Dioid T] (P : T → Prop) : Prop where
  add : ∀ {a b}, P a → P b → P (a ⊕ₒ b)
  mul : ∀ {a b}, P a → P b → P (a ⊗ₒ b)
  eps : P εₒ
  one : P eₒ

/-- `Dioid` on the subtype `{x // P x}` of a sub-`Dioid` predicate `P`. -/
@[reducible] noncomputable def IsSubDioid.toDioid
    {T : Type*} [Dioid T] {P : T → Prop} (h : IsSubDioid P) :
    Dioid {x : T // P x} where
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

/-- `P` is closed under `⊕`, `⊗`, `εₒ`, `eₒ`, and `iSup`. -/
structure IsSubCompleteDioid {T : Type u}
    [CompleteDioid T] (P : T → Prop) : Prop where
  add : ∀ {a b}, P a → P b → P (a ⊕ₒ b)
  mul : ∀ {a b}, P a → P b → P (a ⊗ₒ b)
  eps : P εₒ
  one : P eₒ
  iSup : ∀ {ι : Type u} (f : ι → T),
    (∀ i, P (f i)) → P (CompleteDioid.iSup f)

/-- A sub-`CompleteDioid` is in particular a sub-`Dioid` (forget `iSup`). -/
theorem IsSubCompleteDioid.toIsSubDioid {T : Type u} [CompleteDioid T]
    {P : T → Prop} (h : IsSubCompleteDioid P) : IsSubDioid P where
  add := h.add
  mul := h.mul
  eps := h.eps
  one := h.one

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
