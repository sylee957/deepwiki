import DeepWiki.SymbolicIntegration.ComputableIntegrateTowerCorrectG

/-! # The base RDE-oracle abstract soundness `CRischFieldSpec` (Bronstein Ch. 6, the keystone)

`ComputableTowerRischDE` introduced the field-level Risch-DE oracle as a bare typeclass method
`CRischField.crischDESolve : α → α → Option α` (solving `Dy + f·y = g` over the field `α`), with a
constant base instance `CRischField ℚ` and a recursive tower instance `CRischField (QFunNZG β)` (run the
generic §6 pipeline `cRischDEG` over `CPolyG β = β[s]`). The oracle is only `native_decide`-validated:
there is no abstract spec connecting `crischDESolve b g = some y` to the field-level identity
`D(y) + b·y = g`. This file supplies that spec — `CRischFieldSpec` — and proves the **constant base
instance** `CRischFieldSpec ℚ` axiom-cleanly.

* **`class CRischFieldSpec α`** — the abstract spec: `crischDESolve b g = some y` implies the field-level
  RDE identity `(toK y)′ + (toK b)·(toK y) = toK g` over `K = CFieldSpec.K α`, with `′` the
  `CDiffFieldSpec` derivation (so the spec reads results exactly as the engine's correctness layer does,
  through `CFieldSpec.toK`). This is the abstract face of the leading-coefficient recursion target every
  §6 cancellation case calls (Bronstein eq. 6.23).
* **`instance CRischFieldSpec ℚ`** — the constant base (`D = 0`, `toK = id`): `crischDESolve b g = g/b`
  (`b ≠ 0`) / `0` (`g = 0`), so the identity collapses to the direct division soundness `b·(g/b) = g`.
  Axiom-clean (`[propext, Classical.choice, Quot.sound]`, no `native_decide`).
* **The discharged hyperexp residual** `crischDESolve_zero_intDeriv` — for the pure-integration RDE
  `Dy = R` (`b = 0`), `crischDESolve 0 R = some intR` gives `D(∫R) = R` lifted to the tower fraction
  field: `towerFractionFieldDerivG Dt (amG (C (toK intR))) = amG (C (toK R))`. This is exactly the
  base-oracle residual `hintR` that `ComputableHyperexpFullSoundness` carries as a documented hypothesis
  — discharged here from `CRischFieldSpec` (no `native_decide`), one step toward fully-abstract
  hyperexp soundness.

The **recursive instance `CRischFieldSpec (QFunNZG β)`** is the documented layer-bridge obstruction (the
section docstring below records it precisely): the §6 correctness `cRischDEG_rdeCleared_gen` is conditional
on the entire pipeline's intermediate `some`-results plus a transparent-input chain, none of which is
derivable from the bare `crischDESolve b g = some y`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ### The `CRischFieldSpec` class — the abstract soundness of the field-level RDE oracle

`crischDESolve_spec b g y` asserts that a *successful* solve `crischDESolve b g = some y` returns a
genuine solution of the field-level Risch differential equation `Dy + b·y = g`, read through the
correctness bridge `CFieldSpec.toK` into the genuine field `K = CFieldSpec.K α`: `(toK y)′ + (toK b)·(toK
y) = toK g`, with `′` the `CDiffFieldSpec` derivation. (Phrasing through `toK`/`Differential.deriv`
matches how the §6 pipeline's `cRischDEG_rdeCleared_gen` and the integral-soundness layer read engine
results — see `CDiffFieldSpec.toK_cderiv`.) -/

/-- **Abstract soundness of the field-level RDE oracle** `CRischField.crischDESolve`: whenever
`crischDESolve b g = some y`, the returned `y` solves the Risch differential equation `Dy + b·y = g`
over the genuine field `K = CFieldSpec.K α`, read through the bridge `toK`: `(toK y)′ + (toK b)·(toK y) =
toK g`, with `′ = Differential.deriv` the `CDiffFieldSpec` derivation. The abstract face of the §6.6
leading-coefficient recursion target (Bronstein eq. 6.23); carried as a typeclass so the tower recursion
threads it (base `ℚ`, recursive `QFunNZG β`). -/
class CRischFieldSpec (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CRischField α] where
  /-- A successful solve returns a genuine field-level RDE solution `(toK y)′ + (toK b)·(toK y) = toK g`. -/
  crischDESolve_spec : ∀ b g y : α, CRischField.crischDESolve b g = some y →
    @Differential.deriv _ _ CDiffFieldSpec.diffK (CFieldSpec.toK y)
        + CFieldSpec.toK b * CFieldSpec.toK y
      = CFieldSpec.toK g

/-! ### The constant base instance `CRischFieldSpec ℚ`

At the constants `ℚ` (`D = 0`, `toK = id`, `CFieldSpec.K ℚ = ℚ`) the oracle is the direct division
`crischDESolve b g = g/b` (`b ≠ 0`), `0` (`b = 0 ∧ g = 0`), and the spec `0 + b·y = g` is the soundness
of that division: `b·(g/b) = g` for `b ≠ 0`, and `b·0 = 0 = g` for `b = 0`. The base of the whole tower
recursion, axiom-clean. -/

/-- **`CRischFieldSpec ℚ`** — the constant-field base soundness: `crischDESolve b g = some y` over `ℚ`
(`D = 0`) means `y = g/b` (`b ≠ 0`) or `y = 0` (`b = 0 ∧ g = 0`), and the field identity `0 + b·y = g`
is the direct division soundness `b·(g/b) = g`. The bottoming-out spec of the tower recursion;
axiom-clean (`[propext, Classical.choice, Quot.sound]`, no `native_decide`). -/
instance instCRischFieldSpecQ : CRischFieldSpec ℚ where
  crischDESolve_spec b g y hsolve := by
    -- `crischDESolve b g = if b = 0 then (if g = 0 then some 0 else none) else some (g / b)`.
    show @Differential.deriv _ _ CDiffFieldSpec.diffK (id y) + id b * id y = id g
    -- the `ℚ` derivation is `0`, `toK = id`.
    have hderiv : @Differential.deriv _ _ (CDiffFieldSpec.diffK (α := ℚ)) (id y) = 0 := by
      show @Differential.deriv _ _ instDifferentialQ y = 0
      show (0 : Derivation ℤ ℚ ℚ) y = 0
      rw [Derivation.coe_zero]; rfl
    rw [hderiv, zero_add]
    show id b * id y = id g
    simp only [id_eq]
    -- `crischDESolve b g = if b = 0 then (if g = 0 then some 0 else none) else some (g / b)`.
    simp only [CRischField.crischDESolve] at hsolve
    by_cases hb : b = 0
    · -- `b = 0`: the solve is `if g = 0 then some 0 else none`, so `g = 0`, `y = 0`.
      rw [if_pos hb] at hsolve
      by_cases hg : g = 0
      · rw [if_pos hg, Option.some.injEq] at hsolve
        rw [hb, ← hsolve, hg]; ring
      · rw [if_neg hg] at hsolve; exact absurd hsolve (by simp)
    · -- `b ≠ 0`: the solve is `some (g / b)`, so `y = g / b` and `b·(g/b) = g`.
      rw [if_neg hb, Option.some.injEq] at hsolve
      rw [← hsolve, mul_div_cancel₀ g hb]

/-! ### Axiom audit (the constant base is axiom-clean) -/

#print axioms instCRischFieldSpecQ

end DeepWiki.SymbolicIntegration
