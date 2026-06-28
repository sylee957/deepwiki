import DeepWiki.SymbolicIntegration.LiouvilleLogExtension
import Mathlib.Tactic

/-! # ★★ The MULTI-LEVEL transcendental-log Liouville tower-induction (structure-theorem completeness)

The single-level transcendental-log Liouville keystone is `isLiouville_logExtension_uncond`
(`LiouvilleLogExtension`): for a genuine new log monomial (`NondegenerateLog u`, i.e. `log u ∉ F`),
`F(log u) = RatFunc F` is a Liouville extension of `F`.  Mathlib's `IsLiouville.trans` stacks two
Liouville steps `F ⊆ K ⊆ A` into `F ⊆ A`.  This file assembles the two into the **multi-level tower**
`F ⊆ F(log u₁) ⊆ F(log u₁, log u₂) ⊆ …` — Liouville over `F` at every height, modulo only
`NondegenerateLog uᵢ` at each level.  This is the abstract structure-theorem completeness direction of
the transcendental Risch algorithm, mirroring the RDE tower-induction `crischFieldComplete_step`.

## What `IsLiouville.trans` actually requires (verified against Mathlib source)

`IsLiouville.trans : IsLiouville F K → IsLiouville K A → IsLiouville F A` for a tower `F → K → A`
needs (beyond the `Field`/`Differential`/`Algebra` instances, all automatic for the `RatFunc` tower):
`[DifferentialAlgebra F K]`, `[IsScalarTower F K A]`, and `[Differential.ContainConstants F K]`.  It
does **not** need `DifferentialAlgebra K A` or `DifferentialAlgebra F A` (the `IsLiouville` class itself
does not carry `DifferentialAlgebra`, only `Algebra` — the `DifferentialAlgebra F K` in the Mathlib
`variable` block is dropped by the class and reappears only as a hypothesis of `trans`).  The Mathlib
`Algebra`/`IsScalarTower`/`CharZero` tower instances for nested `RatFunc` synthesize automatically.

## The three per-level / composite pieces this file proves

* **`containConstants_of_nondegenerateLog`** — the genuine per-level glue: a new nondegenerate log
  introduces **no new constants** (`ContainConstants K (RatFunc K)`).  Proven via the keystone's
  corrected `v`-reduction `deriv_mem_range_imp_linear` (`x′ = 0 ⟹ x = v₀ + b·log u`, `b′ = 0`) plus the
  transcendence obstruction `not_isAntideriv_of_nondegenerateLog` forcing `b = 0`.  This is exactly the
  `ContainConstants F K` that `trans` needs at each step.
* **`differentialAlgebra_trans`** / **`containConstants_trans`** — the *composite* plumbing: both
  `DifferentialAlgebra` and `ContainConstants` compose through a scalar tower, so the level-`0`-to-top
  instances `DifferentialAlgebra F Kₙ` / `ContainConstants F Kₙ` (which `trans` needs at level `n+1`,
  and which do **not** synthesize automatically — Mathlib has no transitivity instance) are rebuilt at
  each level.  Mathlib-contributable on their own.

## The assembled induction

* **`isLiouville_ratFunc_step`** — the abstract inductive step: `IsLiouville F K` (composite so far) +
  a nondegenerate log `u : K` ⟹ `IsLiouville F (RatFunc K)`.  The engine each tower height invokes.
* **`LiouvilleStage`** bundles a differential field that is a Liouville extension of `F` together with
  the composite plumbing instances; **`base`** is `F`, **`extend`** adds one log level (using the step
  + the two `_trans` lemmas), **`tower`** iterates `extend` `n` times along a dependent log supply, and
  **`tower_isLiouville`** reads off `IsLiouville F (tower …).carrier`.  The genuine **n-level**
  tower-induction.  Concrete unrollings `isLiouville_logTower_two` / `isLiouville_logTower_three` exhibit
  the 2- and 3-fold `RatFunc` towers from `NondegenerateLog` alone.

Axiom-clean `[propext, Classical.choice, Quot.sound]`; NO `sorry`, NO `native_decide`. -/

open Polynomial
open scoped Differential
open DeepWiki.SymbolicIntegration.LiouvilleLog

namespace DeepWiki.SymbolicIntegration.LiouvilleTower

/-! ## The composite plumbing: `DifferentialAlgebra` and `ContainConstants` compose through a tower

Mathlib provides neither a `DifferentialAlgebra` nor a `ContainConstants` transitivity instance, yet
`IsLiouville.trans` at the `n+1`-st tower level needs the level-`0`-to-top instances.  These two lemmas
supply them. -/

/-- **`DifferentialAlgebra` composes through a scalar tower** (`differentialAlgebra_trans`): if `B/A`
and `C/B` each commute the derivation with `algebraMap`, so does `C/A`.  Proof: factor `algebraMap A C`
through `B` (`IsScalarTower.algebraMap_apply`) and apply `deriv_algebraMap` twice.  The composite
`DifferentialAlgebra F Kₙ` the tower induction needs (no Mathlib transitivity instance exists). -/
theorem differentialAlgebra_trans {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Differential A] [Differential B] [Differential C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [DifferentialAlgebra A B] [DifferentialAlgebra B C] :
    DifferentialAlgebra A C where
  deriv_algebraMap a := by
    rw [IsScalarTower.algebraMap_apply A B C, deriv_algebraMap, deriv_algebraMap,
      ← IsScalarTower.algebraMap_apply A B C]

/-- **`ContainConstants` composes through a scalar tower** (`containConstants_trans`): if every constant
of `B` is in `A` and every constant of `C` is in `B`, then every constant of `C` is in `A`.  Proof: a
constant `x` of `C` lies in `B` (`ContainConstants B C`); its `B`-preimage `b` is a constant
(`deriv_algebraMap` + `algebraMap`-injectivity), hence lies in `A`.  Needs `DifferentialAlgebra B C` (to
descend the constancy through the upper step).  The composite `ContainConstants F Kₙ` the tower induction
needs. -/
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

/-! ## The per-level glue: a nondegenerate log introduces no new constants

`IsLiouville.trans` needs `ContainConstants F K` at each step.  For a log extension `K ⊆ RatFunc K`, this
is exactly "the new log monomial is not a new constant" — a theorem from `NondegenerateLog`. -/

section PerLevel

variable {K : Type*} [Field K] [Differential K] [CharZero K]

/-- **A genuine new log monomial introduces no new constants** (`containConstants_of_nondegenerateLog`):
for `NondegenerateLog u` (`log u ∉ K`), `RatFunc K` with the log-monomial derivation `t' = u'/u`
satisfies `ContainConstants K (RatFunc K)` — every constant of `K(log u)` lies in `K`.  Proof: a constant
`x` (`x′ = 0`) has `x′ ∈ K`, so by the keystone's corrected `v`-reduction `deriv_mem_range_imp_linear`,
`x = v₀ + b·(log u)` with `v₀, b ∈ K` and `b′ = 0`; writing `x` as the image of the degree-`≤ 1`
polynomial `C v₀ + C b·X` and applying `derivExtends`, `x′ = 0` forces `v₀′ + b·(u'/u) = 0` in `K`, so if
`b ≠ 0` then `-v₀/b` would be a `K`-antiderivative of `u'/u` (`not_isAntideriv_of_nondegenerateLog`).
Hence `b = 0` and `x = v₀ ∈ K`.  This is the `ContainConstants` hypothesis `IsLiouville.trans` consumes at
each tower level. -/
theorem containConstants_of_nondegenerateLog (u : K) (hnd : NondegenerateLog u) :
    letI := logDifferential u
    Differential.ContainConstants K (RatFunc K) := by
  letI := logDifferential u
  letI := logDifferentialAlgebra u
  refine ⟨fun {x} hx => ?_⟩
  -- `x′ = 0 ∈ range`, so by the corrected `v`-reduction `x = v₀ + b·(log u)`, `b′ = 0`.
  have hxrange : x′ ∈ (algebraMap K (RatFunc K)).range := by rw [hx]; exact ⟨0, by rw [map_zero]⟩
  obtain ⟨v₀, b, hb0, hxeq⟩ := deriv_mem_range_imp_linear u hnd hxrange
  have hfa : ∀ a : K, algebraMap K (RatFunc K) a = algebraMap K[X] (RatFunc K) (C a) := by
    intro a; rw [algebraMap_eq_algebraMap_C]
  -- Rewrite `x` as the image of the degree-`≤ 1` polynomial `C v₀ + C b·X`.
  have hxP : x = algebraMap K[X] (RatFunc K) (C v₀ + C b * X) := by
    rw [hxeq, hfa v₀, hfa b, map_add, map_mul]
  -- `D (C v₀ + C b·X) = C v₀′ + C b · C (u'/u)` on `K[X]` (no fraction-field `ℤ`-algebra diamond).
  have hDp : logDerivPoly u (C v₀ + C b * X) = C v₀′ + C b * C (logCoeff u) := by
    rw [map_add, Derivation.leibniz, logDerivPoly_C, logDerivPoly_C, logDerivPoly_X, hb0]
    simp only [map_zero, smul_eq_mul, mul_zero, add_zero]
  have hxder : x′ = algebraMap K[X] (RatFunc K) (C v₀′ + C b * C (logCoeff u)) := by
    rw [hxP, derivExtends u (C v₀ + C b * X), hDp]
  -- `x′ = 0`, so by injectivity the polynomial is `0`, i.e. `v₀′ + b·(u'/u) = 0`.
  rw [hx] at hxder
  have hpoly0 : C v₀′ + C b * C (logCoeff u) = 0 :=
    FaithfulSMul.algebraMap_injective K[X] (RatFunc K) (by rw [← hxder, map_zero])
  have hF0 : v₀′ + b * logCoeff u = 0 := by
    have h := hpoly0; rw [← C_mul, ← map_add] at h; exact C_eq_zero.mp h
  -- If `b ≠ 0`, `-v₀/b` is a `K`-antiderivative of `u'/u` — forbidden.  So `b = 0` and `x = v₀ ∈ K`.
  have hbeq0 : b = 0 := by
    by_contra hbne
    refine not_isAntideriv_of_nondegenerateLog u hnd (s := -v₀ / b) ?_
    rw [Differential.deriv.leibniz_div_const (-v₀) b hb0, smul_eq_mul, map_neg]
    field_simp; linear_combination -hF0
  exact ⟨v₀, by rw [hxP, hbeq0, map_zero, zero_mul, add_zero, ← hfa v₀]⟩

end PerLevel

/-! ## The abstract inductive step and the bundled tower

`isLiouville_ratFunc_step` is the engine: extend a Liouville extension `F ⊆ K` by one nondegenerate log
over `K` to a Liouville extension `F ⊆ RatFunc K`.  `LiouvilleStage` then bundles the composite plumbing
so the step can be iterated. -/

section Step

variable {F K : Type*}
    [Field F] [Differential F] [CharZero F]
    [Field K] [Differential K] [CharZero K]
    [Algebra F K] [DifferentialAlgebra F K] [Differential.ContainConstants F K]

omit [CharZero F] in
/-- **The abstract tower-induction step** (`isLiouville_ratFunc_step`): given a Liouville extension
`F ⊆ K` (the composite so far, with its `DifferentialAlgebra F K` and `ContainConstants F K`) and a
genuine new log monomial `u : K` (`NondegenerateLog u`), the one-step-higher extension `F ⊆ RatFunc K`
is Liouville — `IsLiouville F (RatFunc K)`.  Combines the keystone `isLiouville_logExtension_uncond`
(`IsLiouville K (RatFunc K)`), the per-level `containConstants_of_nondegenerateLog`, and
`IsLiouville.trans`.  The engine each height of the `n`-level tower invokes. -/
theorem isLiouville_ratFunc_step (hFK : IsLiouville F K) (u : K) (hnd : NondegenerateLog u) :
    letI := logDifferential u
    IsLiouville F (RatFunc K) := by
  letI _dK1 : Differential (RatFunc K) := logDifferential u
  letI _dAK1 : DifferentialAlgebra K (RatFunc K) := logDifferentialAlgebra u
  letI _dCCK1 : Differential.ContainConstants K (RatFunc K) :=
    containConstants_of_nondegenerateLog u hnd
  have hKR : IsLiouville K (RatFunc K) := isLiouville_logExtension_uncond u hnd
  exact IsLiouville.trans (F := F) (K := K) (A := RatFunc K) hFK hKR

end Step

section Tower

variable (F : Type) [Field F] [Differential F] [CharZero F]

/-- **A Liouville stage over `F`**: a differential field `carrier` that is a Liouville extension of `F`,
bundled with the *composite* plumbing instances (`DifferentialAlgebra F carrier`,
`ContainConstants F carrier`) the tower step needs.  `IsLiouville F carrier` is recorded; iterating the
`extend` operation builds the `n`-level log tower. -/
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

/-- **The base stage** (`base`): `F` itself, a Liouville extension of `F` via `IsLiouville.rfl`.  Height
`0` of the tower. -/
def base : LiouvilleStage F := { carrier := F, isLiouvilleF := IsLiouville.rfl F }

/-- **Extend a stage by one nondegenerate log** (`extend`): given a stage `S` (Liouville over `F`) and a
genuine new log monomial `u : S.carrier` (`NondegenerateLog u`), the next stage has carrier
`RatFunc S.carrier`.  Its `IsLiouville F (RatFunc S.carrier)` comes from `isLiouville_ratFunc_step`
(`S.isLiouvilleF` + the keystone via `trans`); the composite `DifferentialAlgebra F (RatFunc S.carrier)`
and `ContainConstants F (RatFunc S.carrier)` are rebuilt by `differentialAlgebra_trans` /
`containConstants_trans` so the next `extend` can fire.  One height of the tower induction. -/
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

/-- **The `n`-level log tower** (`tower`): iterate `extend` `n` times along a dependent log supply
`nextLog`, which provides — for *any* reachable stage — a nondegenerate log over it.  Height `0` is
`base = F`; height `n+1` extends height `n` by `nextLog`'s log.  The carrier at height `n` is the
`n`-fold log extension `F(log u₁)(log u₂)⋯(log uₙ)`. -/
noncomputable def tower
    (nextLog : (S : LiouvilleStage F) → {u : S.carrier // NondegenerateLog u}) :
    ℕ → LiouvilleStage F
  | 0 => base
  | n + 1 =>
      let S := tower nextLog n
      S.extend (nextLog S).1 (nextLog S).2

/-- **★★ THE MULTI-LEVEL TOWER IS LIOUVILLE** (`tower_isLiouville`): for every height `n`, the `n`-fold
log extension built by `tower` is a Liouville extension of `F` — `IsLiouville F (tower nextLog n).carrier`.
The structure-theorem completeness of the transcendental-log tower: `F ⊆ F(log u₁) ⊆ F(log u₁, log u₂) ⊆
…` is Liouville over `F` at every level, modulo only `NondegenerateLog uᵢ` (supplied by `nextLog`) at each
level.  This is the multi-level analogue of the single-level keystone `isLiouville_logExtension_uncond`,
assembled by the tower induction. -/
theorem tower_isLiouville
    (nextLog : (S : LiouvilleStage F) → {u : S.carrier // NondegenerateLog u}) (n : ℕ) :
    IsLiouville F (tower nextLog n).carrier :=
  (tower nextLog n).isLiouvilleF

end LiouvilleStage

end Tower

/-! ## Concrete unrollings: the 2- and 3-fold `RatFunc` towers from `NondegenerateLog` alone

Exhibiting the tower induction on the literal nested-`RatFunc` carriers, with the per-level and composite
plumbing discharged inline — the load-bearing 2-level case and its one-step extension. -/

section Concrete

variable {F : Type*} [Field F] [Differential F] [CharZero F]

/-- **The 2-level log tower** (`isLiouville_logTower_two`): for genuine new logs `u₁` over `F` and `u₂`
over `F(log u₁) = RatFunc F`, the double log extension `RatFunc (RatFunc F)` is a Liouville extension of
`F` — modulo `NondegenerateLog` at each level **alone** (no `ContainConstants` hypothesis; it is the
proven `containConstants_of_nondegenerateLog`).  The load-bearing composition: the keystone at each
level + the per-level glue + `IsLiouville.trans`. -/
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

/-- **The 3-level log tower** (`isLiouville_logTower_three`): for genuine new logs `u₁, u₂, u₃` up the
tower `F ⊆ RatFunc F ⊆ RatFunc (RatFunc F)`, the triple log extension `RatFunc (RatFunc (RatFunc F))` is
a Liouville extension of `F` — modulo `NondegenerateLog` at each level alone.  Exhibits the second
application of the step: `differentialAlgebra_trans` / `containConstants_trans` rebuild the composite
`F`-to-level-`2` instances that `IsLiouville.trans` needs to chain the third level. -/
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

/-! ### Restatements (anonymous `example`s) pinning the landed results -/

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

/-! ### Axiom audit (all landed results axiom-clean; NO `native_decide`, NO `sorry`) -/

#print axioms differentialAlgebra_trans
#print axioms containConstants_trans
#print axioms containConstants_of_nondegenerateLog
#print axioms isLiouville_ratFunc_step
#print axioms LiouvilleTower.LiouvilleStage.tower_isLiouville
#print axioms isLiouville_logTower_two
#print axioms isLiouville_logTower_three

end DeepWiki.SymbolicIntegration.LiouvilleTower
