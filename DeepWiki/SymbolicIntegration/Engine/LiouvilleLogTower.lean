import DeepWiki.SymbolicIntegration.LiouvilleLog
import DeepWiki.SymbolicIntegration.Engine.LiouvilleExpBridge
import Mathlib.Tactic

/-! # The multi-level transcendental-log Liouville tower-induction

Assembles the single-level log keystone `isLiouville_logExtension_uncond` via `IsLiouville.trans`
into the multi-level tower `F ⊆ F(log u₁) ⊆ F(log u₁, log u₂) ⊆ …`, Liouville over `F` at every
height modulo `NondegenerateLog uᵢ`.  Supplies the composite plumbing (`differentialAlgebra_trans`,
`containConstants_trans`), the inductive step `isLiouville_ratFunc_step`, and the bundled
`LiouvilleStage` tower. -/

open Polynomial
open scoped Differential
open DeepWiki.SymbolicIntegration.LiouvilleLog

namespace DeepWiki.SymbolicIntegration.LiouvilleTower

/-! ## The composite plumbing: `DifferentialAlgebra` and `ContainConstants` compose through a tower -/

/-- `DifferentialAlgebra` composes through a scalar tower: `DifferentialAlgebra A B` and
`DifferentialAlgebra B C` give `DifferentialAlgebra A C`. -/
theorem differentialAlgebra_trans {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Differential A] [Differential B] [Differential C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [DifferentialAlgebra A B] [DifferentialAlgebra B C] :
    DifferentialAlgebra A C where
  deriv_algebraMap a := by
    rw [IsScalarTower.algebraMap_apply A B C, deriv_algebraMap, deriv_algebraMap,
      ← IsScalarTower.algebraMap_apply A B C]

/-- `ContainConstants` composes through a scalar tower: `ContainConstants A B` and
`ContainConstants B C` give `ContainConstants A C`. -/
theorem containConstants_trans {A B C : Type*} [Field A] [Field B] [Field C]
    [Differential A] [Differential B] [Differential C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [DifferentialAlgebra B C]
    [Differential.ContainConstants A B] [Differential.ContainConstants B C] :
    Differential.ContainConstants A C where
  mem_range_of_deriv_eq_zero {x} hx := by
    obtain ⟨b, hb⟩ := mem_range_of_deriv_eq_zero B hx
    have hb0 : b′ = 0 := by
      have hbc : algebraMap B C b′ = 0 := by rw [← deriv_algebraMap, hb, hx]
      apply FaithfulSMul.algebraMap_injective B C; rw [hbc, map_zero]
    obtain ⟨a, ha⟩ := mem_range_of_deriv_eq_zero A hb0
    exact ⟨a, by rw [IsScalarTower.algebraMap_apply A B C, ha, hb]⟩

/-! ## The abstract inductive step and the bundled tower -/

section Step

variable {F K : Type*}
    [Field F] [Differential F] [CharZero F]
    [Field K] [Differential K] [CharZero K]
    [Algebra F K] [DifferentialAlgebra F K] [Differential.ContainConstants F K]

omit [CharZero F] in
/-- The tower-induction step: `IsLiouville F K` plus a nondegenerate log `u : K` gives
`IsLiouville F (RatFunc K)`. -/
theorem isLiouville_ratFunc_step (hFK : IsLiouville F K) (u : K) (hnd : NondegenerateLog u) :
    letI := logDifferential u
    IsLiouville F (RatFunc K) := by
  letI _dK1 : Differential (RatFunc K) := logDifferential u
  letI _dAK1 : DifferentialAlgebra K (RatFunc K) := logDifferentialAlgebra u
  letI _dCCK1 : Differential.ContainConstants K (RatFunc K) :=
    containConstants_of_nondegenerateLog u hnd
  have hKR : IsLiouville K (RatFunc K) := isLiouville_logExtension_uncond u hnd
  exact IsLiouville.trans (F := F) (K := K) (A := RatFunc K) hFK hKR

omit [CharZero F] in
/-- The tower-induction step, exponential layer: `IsLiouville F K` plus a nondegenerate exp `u : K`
gives `IsLiouville F (RatFunc K)`. The exp sibling of `isLiouville_ratFunc_step`, composing the exp
keystone with `IsLiouville.trans`. -/
theorem isLiouville_ratFunc_expStep (hFK : IsLiouville F K) (u : K)
    (hnd : DeepWiki.SymbolicIntegration.LiouvilleExp.NondegenerateExp u) :
    letI := DeepWiki.SymbolicIntegration.LiouvilleExp.expDifferential u
    IsLiouville F (RatFunc K) := by
  letI _dK1 : Differential (RatFunc K) :=
    DeepWiki.SymbolicIntegration.LiouvilleExp.expDifferential u
  letI _dAK1 : DifferentialAlgebra K (RatFunc K) :=
    DeepWiki.SymbolicIntegration.LiouvilleExp.expDifferentialAlgebra u
  letI _dCCK1 : Differential.ContainConstants K (RatFunc K) :=
    DeepWiki.SymbolicIntegration.LiouvilleExpBridge.containConstants_of_nondegenerateExp u hnd
  have hKR : IsLiouville K (RatFunc K) :=
    DeepWiki.SymbolicIntegration.LiouvilleExpBridge.isLiouville_expExtension_uncond u hnd
  exact IsLiouville.trans (F := F) (K := K) (A := RatFunc K) hFK hKR

end Step

section Tower

variable (F : Type) [Field F] [Differential F] [CharZero F]

/-- A Liouville stage over `F`: a differential field `carrier` that is a Liouville extension of `F`,
bundled with the composite plumbing instances the tower step needs. -/
structure LiouvilleStage where
  /-- The carrier field of this stage. -/
  carrier : Type
  /-- `carrier` is a field. -/
  [field : Field carrier]
  /-- `carrier` carries the (tower-extended) derivation. -/
  [diff : Differential carrier]
  /-- `carrier` has characteristic `0` (so further log extensions stay in the keystone's scope). -/
  [charZero : CharZero carrier]
  /-- `carrier` is an `F`-algebra. -/
  [algF : Algebra F carrier]
  /-- The derivation commutes with `algebraMap F carrier` (composite differential algebra). -/
  [diffAlgF : @DifferentialAlgebra F carrier _ _ algF _ diff]
  /-- Every constant of `carrier` lies in `F` (composite `ContainConstants`). -/
  [ccF : @Differential.ContainConstants F carrier _ _ algF diff]
  /-- `carrier` is a Liouville extension of `F`. -/
  isLiouvilleF : @IsLiouville F carrier _ field _ diff algF

namespace LiouvilleStage

variable {F}

attribute [instance] field diff charZero algF diffAlgF ccF

/-- The base stage: `F` itself, a Liouville extension of `F`. -/
def base : LiouvilleStage F := { carrier := F, isLiouvilleF := IsLiouville.rfl F }

/-- Extend a stage by one nondegenerate log `u`: the next stage has carrier `RatFunc S.carrier`. -/
noncomputable def extend (S : LiouvilleStage F) (u : S.carrier)
    (hnd : NondegenerateLog u) : LiouvilleStage F :=
  letI _dC1 : Differential (RatFunc S.carrier) := logDifferential u
  letI _dAC1 : DifferentialAlgebra S.carrier (RatFunc S.carrier) := logDifferentialAlgebra u
  letI _dCC1 : Differential.ContainConstants S.carrier (RatFunc S.carrier) :=
    containConstants_of_nondegenerateLog u hnd
  letI _dAF2 : DifferentialAlgebra F (RatFunc S.carrier) :=
    differentialAlgebra_trans (A := F) (B := S.carrier) (C := RatFunc S.carrier)
  letI _dCC2 : Differential.ContainConstants F (RatFunc S.carrier) :=
    containConstants_trans (A := F) (B := S.carrier) (C := RatFunc S.carrier)
  { carrier := RatFunc S.carrier
    isLiouvilleF := isLiouville_ratFunc_step S.isLiouvilleF u hnd }

/-- Extend a stage by one nondegenerate exp `u`: the next stage has carrier `RatFunc S.carrier`, with
the exp derivation. The exp sibling of `extend`; both produce Liouville stages, so a tower may mix log
and exp layers. -/
noncomputable def extendExp (S : LiouvilleStage F) (u : S.carrier)
    (hnd : DeepWiki.SymbolicIntegration.LiouvilleExp.NondegenerateExp u) : LiouvilleStage F :=
  letI _dC1 : Differential (RatFunc S.carrier) :=
    DeepWiki.SymbolicIntegration.LiouvilleExp.expDifferential u
  letI _dAC1 : DifferentialAlgebra S.carrier (RatFunc S.carrier) :=
    DeepWiki.SymbolicIntegration.LiouvilleExp.expDifferentialAlgebra u
  letI _dCC1 : Differential.ContainConstants S.carrier (RatFunc S.carrier) :=
    DeepWiki.SymbolicIntegration.LiouvilleExpBridge.containConstants_of_nondegenerateExp u hnd
  letI _dAF2 : DifferentialAlgebra F (RatFunc S.carrier) :=
    differentialAlgebra_trans (A := F) (B := S.carrier) (C := RatFunc S.carrier)
  letI _dCC2 : Differential.ContainConstants F (RatFunc S.carrier) :=
    containConstants_trans (A := F) (B := S.carrier) (C := RatFunc S.carrier)
  { carrier := RatFunc S.carrier
    isLiouvilleF := isLiouville_ratFunc_expStep S.isLiouvilleF u hnd }

/-- The `n`-level log tower: iterate `extend` `n` times along a dependent log supply `nextLog`,
carrier at height `n` the `n`-fold log extension `F(log u₁)⋯(log uₙ)`. -/
noncomputable def tower
    (nextLog : (S : LiouvilleStage F) → {u : S.carrier // NondegenerateLog u}) :
    ℕ → LiouvilleStage F
  | 0 => base
  | n + 1 =>
      let S := tower nextLog n
      S.extend (nextLog S).1 (nextLog S).2

/-- The multi-level tower is Liouville: `IsLiouville F (tower nextLog n).carrier` for every
height `n`. -/
theorem tower_isLiouville
    (nextLog : (S : LiouvilleStage F) → {u : S.carrier // NondegenerateLog u}) (n : ℕ) :
    IsLiouville F (tower nextLog n).carrier :=
  (tower nextLog n).isLiouvilleF

end LiouvilleStage

end Tower

/-! ## Concrete unrollings: the 2- and 3-fold `RatFunc` towers from `NondegenerateLog` alone -/

section Concrete

variable {F : Type*} [Field F] [Differential F] [CharZero F]

/-- The 2-level log tower: for nondegenerate logs `u₁` over `F` and `u₂` over `RatFunc F`,
`RatFunc (RatFunc F)` is a Liouville extension of `F`. -/
theorem isLiouville_logTower_two (u₁ : F) (u₂ : RatFunc F)
    (hnd₁ : NondegenerateLog u₁)
    (hnd₂ : letI := logDifferential u₁; NondegenerateLog u₂) :
    letI := logDifferential u₁
    letI := logDifferential u₂
    IsLiouville F (RatFunc (RatFunc F)) := by
  letI _dF1 : Differential (RatFunc F) := logDifferential u₁
  letI _dAF1 : DifferentialAlgebra F (RatFunc F) := logDifferentialAlgebra u₁
  letI _dCC1 : Differential.ContainConstants F (RatFunc F) :=
    containConstants_of_nondegenerateLog u₁ hnd₁
  letI _dF2 : Differential (RatFunc (RatFunc F)) := logDifferential u₂
  exact isLiouville_ratFunc_step (isLiouville_logExtension_uncond u₁ hnd₁) u₂ hnd₂

/-- The 3-level log tower: for nondegenerate logs `u₁, u₂, u₃`, `RatFunc (RatFunc (RatFunc F))` is a
Liouville extension of `F`. -/
theorem isLiouville_logTower_three (u₁ : F) (u₂ : RatFunc F) (u₃ : RatFunc (RatFunc F))
    (hnd₁ : NondegenerateLog u₁)
    (hnd₂ : letI := logDifferential u₁; NondegenerateLog u₂)
    (hnd₃ : letI := logDifferential u₁; letI := logDifferential u₂; NondegenerateLog u₃) :
    letI := logDifferential u₁
    letI := logDifferential u₂
    letI := logDifferential u₃
    IsLiouville F (RatFunc (RatFunc (RatFunc F))) := by
  letI _dF1 : Differential (RatFunc F) := logDifferential u₁
  letI _dAF1 : DifferentialAlgebra F (RatFunc F) := logDifferentialAlgebra u₁
  letI _dCC1 : Differential.ContainConstants F (RatFunc F) :=
    containConstants_of_nondegenerateLog u₁ hnd₁
  letI _dF2 : Differential (RatFunc (RatFunc F)) := logDifferential u₂
  letI _dAF2 : DifferentialAlgebra (RatFunc F) (RatFunc (RatFunc F)) := logDifferentialAlgebra u₂
  letI _dCC2 : Differential.ContainConstants (RatFunc F) (RatFunc (RatFunc F)) :=
    containConstants_of_nondegenerateLog u₂ hnd₂
  letI _dF3 : Differential (RatFunc (RatFunc (RatFunc F))) := logDifferential u₃
  letI _dAF12 : DifferentialAlgebra F (RatFunc (RatFunc F)) :=
    differentialAlgebra_trans (A := F) (B := RatFunc F) (C := RatFunc (RatFunc F))
  letI _dCC12 : Differential.ContainConstants F (RatFunc (RatFunc F)) :=
    containConstants_trans (A := F) (B := RatFunc F) (C := RatFunc (RatFunc F))
  have hL12 : IsLiouville F (RatFunc (RatFunc F)) :=
    isLiouville_ratFunc_step (isLiouville_logExtension_uncond u₁ hnd₁) u₂ hnd₂
  exact isLiouville_ratFunc_step hL12 u₃ hnd₃

end Concrete

/-! ### Restatements -/

section Examples

variable {F : Type*} [Field F] [Differential F] [CharZero F]

-- The composite plumbing: `DifferentialAlgebra` / `ContainConstants` compose through a scalar tower.
example {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Differential A] [Differential B] [Differential C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [DifferentialAlgebra A B] [DifferentialAlgebra B C] : DifferentialAlgebra A C :=
  differentialAlgebra_trans (A := A) (B := B) (C := C)

-- The per-level glue: a genuine new log introduces no new constants.
example (u : F) (hnd : NondegenerateLog u) :
    letI := logDifferential u
    Differential.ContainConstants F (RatFunc F) :=
  containConstants_of_nondegenerateLog u hnd

-- ★ The abstract inductive step: `IsLiouville F K` + a nondegenerate log over `K` ⟹
-- `IsLiouville F (RatFunc K)`.
example {K : Type*} [Field K] [Differential K] [CharZero K] [Algebra F K]
    [DifferentialAlgebra F K] [Differential.ContainConstants F K]
    (hFK : IsLiouville F K) (u : K) (hnd : NondegenerateLog u) :
    letI := logDifferential u
    IsLiouville F (RatFunc K) :=
  isLiouville_ratFunc_step hFK u hnd

-- The 2-level concrete tower from `NondegenerateLog` alone.
example (u₁ : F) (u₂ : RatFunc F) (hnd₁ : NondegenerateLog u₁)
    (hnd₂ : letI := logDifferential u₁; NondegenerateLog u₂) :
    letI := logDifferential u₁
    letI := logDifferential u₂
    IsLiouville F (RatFunc (RatFunc F)) :=
  isLiouville_logTower_two u₁ u₂ hnd₁ hnd₂

end Examples

section TowerExample

variable (F : Type) [Field F] [Differential F] [CharZero F]

-- ★★ The multi-level tower: the `n`-fold log extension is a Liouville extension of `F`.
example (nextLog : (S : LiouvilleStage F) → {u : S.carrier // NondegenerateLog u}) (n : ℕ) :
    IsLiouville F (LiouvilleStage.tower nextLog n).carrier :=
  LiouvilleStage.tower_isLiouville nextLog n

end TowerExample

end DeepWiki.SymbolicIntegration.LiouvilleTower
