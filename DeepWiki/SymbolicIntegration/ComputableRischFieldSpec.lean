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

/-! ### ★ Discharging the base-oracle residual `D(∫R) = R` (the hyperexp `hintR`)

`ComputableHyperexpFullSoundness.cIntegrateHyperexpNormalG_sound` carries the base-oracle residual as a
documented hypothesis

  `hintR : towerFractionFieldDerivG Dt (amG α (C (toK intR))) = amG α (C (toK R))`

where `R = cHyperexpResidualG (cExpEtaG Dt) red.logs ∈ α` and `crischDESolve 0 R = some intR` — the
field-level antiderivative identity `D(∫R) = R` for the pure-integration RDE `Dy = R` (`b = 0`), with the
constant `∫R = intR ∈ α` embedded into the tower fraction field `RatFunc (CFieldSpec.K α)` as `amG (C (toK
intR))`. With `CRischFieldSpec α` in hand this is no longer a hypothesis: the spec turns the solve into the
field identity `(toK intR)′ = toK R` (the `b = 0` case), and `extendDeriv` on a *constant* `algebraMap (C
k)` reads off as `algebraMap (C k′)` (`extendDeriv_algebraMap` + `implicitDeriv_C`), with `k′` the
`CDiffFieldSpec` derivation — exactly `toK R`. Proved for an **arbitrary residual `R : α`** (so it
instantiates verbatim to the hyperexp `cHyperexpResidualG` residual), with NO `native_decide`. -/

section ResidualDischarge

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CRischField α] [CRischFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]

omit [CRischField α] [CRischFieldSpec α] in
/-- **`extendDeriv` of a constant is the constant of its derivative** (over the tower fraction field): for
`k : CFieldSpec.K α`, `towerFractionFieldDerivG Dt (amG α (C k)) = amG α (C k′)`, with `′` the
`CDiffFieldSpec` derivation. Since `amG = algebraMap K[X] (RatFunc K)` and `towerFractionFieldDerivG Dt =
extendDeriv (implicitDeriv (toPolyG Dt))`, this is `extendDeriv_algebraMap` followed by `implicitDeriv_C`
(`implicitDeriv v (C k) = C k′`). The constant-coefficient reading of the keystone derivation. -/
theorem towerFractionFieldDerivG_amG_C (Dt : CPolyG α) (k : CFieldSpec.K α) :
    towerFractionFieldDerivG Dt (amG α (Polynomial.C k))
      = amG α (Polynomial.C (@Differential.deriv _ _ CDiffFieldSpec.diffK k)) := by
  rw [towerFractionFieldDerivG, amG, extendDeriv_algebraMap, Differential.implicitDeriv_C]

/-- **★ The base-oracle residual `D(∫R) = R` discharged from `CRischFieldSpec`** (the hyperexp `hintR`):
for any residual `R : α`, if the base oracle solves the pure-integration RDE `Dy = R`
(`crischDESolve 0 R = some intR`), then the constant `∫R = intR`, embedded into the tower fraction field as
`amG (C (toK intR))`, differentiates back to `amG (C (toK R))`:

  `towerFractionFieldDerivG Dt (amG α (C (toK intR))) = amG α (C (toK R))`.

The `b = 0` case of `CRischFieldSpec.crischDESolve_spec` gives `(toK intR)′ + 0·(toK intR) = toK R`, i.e.
`(toK intR)′ = toK R`; `towerFractionFieldDerivG_amG_C` reads off the constant's derivative. This is
exactly the `hintR` hypothesis `ComputableHyperexpFullSoundness.cIntegrateHyperexpNormalG_sound` carries —
discharged with NO `native_decide`. -/
theorem crischDESolve_zero_intDeriv (Dt : CPolyG α) (R intR : α)
    (hsolve : CRischField.crischDESolve (CField.zero : α) R = some intR) :
    towerFractionFieldDerivG Dt (amG α (Polynomial.C (CFieldSpec.toK intR)))
      = amG α (Polynomial.C (CFieldSpec.toK R)) := by
  rw [towerFractionFieldDerivG_amG_C]
  -- the `b = 0` spec: `(toK intR)′ + (toK 0)·(toK intR) = toK R`, and `toK 0 = 0`.
  have hspec := CRischFieldSpec.crischDESolve_spec (CField.zero : α) R intR hsolve
  rw [CFieldSpec.toK_zero, zero_mul, add_zero] at hspec
  rw [hspec]

end ResidualDischarge

#print axioms crischDESolve_zero_intDeriv

/-! ### The cleared → field layer-bridge for the §6 RDE oracle (the genuinely-new half of Task 3)

The §6 correctness `cRischDEG_rdeCleared_gen` (`ComputableRischDETowerCorrectG`) outputs the **cleared**
polynomial identity over `(CFieldSpec.K α)[X]`

  `GD·FD·(D ynum·yden − ynum·D yden) + GD·FN·ynum·yden = GN·FD·yden²`

(`D = implicitDeriv (toPolyG Dt)`, all terms `toPolyG`-images). The field-level RDE spec wants instead

  `extendDeriv D (Y) + F·Y = G`     (`Y = amG ynum/amG yden`, `F = amG fnum/amG fden`, `G = amG gnum/amG gden`)

over `RatFunc (CFieldSpec.K α)`. The bridge between the two layers is the `amG`/quotient-rule manipulation:
lift the cleared identity through the injective `amG`, read `extendDeriv D Y = (amG(D ynum)·amG yden −
amG ynum·amG(D yden))/amG yden²` (`towerFractionFieldDerivG_div`), and divide through the nonzero
`amG gden·amG fden·amG yden²`. This mirrors `field_identity_of_checkIdentityG`'s cleared → field dance
(`div_add_div`/`div_eq_div_iff`/`linear_combination`). We prove this half of the layer-bridge generically;
the obstruction note below records why it does *not* yet compose into the full recursive instance. -/

section ClearedToField

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

open CPolyG

/-- **★ The cleared → field layer-bridge for the §6 RDE oracle**: given the **cleared** polynomial
identity that `cRischDEG_rdeCleared_gen` produces (its conclusion verbatim, with `D = implicitDeriv (toPolyG
Dt)`), together with the denominators `fden`, `gden`, `yden` nonzero, the **field-level Risch-DE identity**

  `towerFractionFieldDerivG Dt (amG ynum/amG yden) + (amG fnum/amG fden)·(amG ynum/amG yden) = amG gnum/amG gden`

holds over `RatFunc (CFieldSpec.K α)`. The genuinely-new half of the field↔poly layer-bridge: it reads the
quotient rule off `towerFractionFieldDerivG_div` and divides the cleared identity through the nonzero
`amG gden·amG fden·amG yden²` (the `field_identity_of_checkIdentityG` cleared → field technique applied to
the RDE shape). -/
theorem rischDE_field_of_cleared (Dt fnum fden gnum gden ynum yden : CPolyG α)
    (hfden : toPolyG fden ≠ 0) (hgden : toPolyG gden ≠ 0) (hyden : toPolyG yden ≠ 0)
    (hcleared : amG α (toPolyG gden) * amG α (toPolyG fden)
          * (amG α (Differential.implicitDeriv (toPolyG Dt) (toPolyG ynum)) * amG α (toPolyG yden)
              - amG α (toPolyG ynum) * amG α (Differential.implicitDeriv (toPolyG Dt) (toPolyG yden)))
        + amG α (toPolyG gden) * amG α (toPolyG fnum) * amG α (toPolyG ynum) * amG α (toPolyG yden)
      = amG α (toPolyG gnum) * amG α (toPolyG fden) * amG α (toPolyG yden) ^ 2) :
    towerFractionFieldDerivG Dt (amG α (toPolyG ynum) / amG α (toPolyG yden))
        + amG α (toPolyG fnum) / amG α (toPolyG fden)
          * (amG α (toPolyG ynum) / amG α (toPolyG yden))
      = amG α (toPolyG gnum) / amG α (toPolyG gden) := by
  -- nonzero readings
  have hFDne : amG α (toPolyG fden) ≠ 0 := amG_toPolyG_ne_zero hfden
  have hGDne : amG α (toPolyG gden) ≠ 0 := amG_toPolyG_ne_zero hgden
  have hYDne : amG α (toPolyG yden) ≠ 0 := amG_toPolyG_ne_zero hyden
  -- the quotient rule reads `D(YN/YD) = (amG(D ynum)·YD − YN·amG(D yden))/YD²`
  rw [towerFractionFieldDerivG_div, div_mul_div_comm,
    div_add_div _ _ (pow_ne_zero 2 hYDne) (mul_ne_zero hFDne hYDne),
    div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hYDne) (mul_ne_zero hFDne hYDne)) hGDne]
  ring_nf
  ring_nf at hcleared
  linear_combination amG α (toPolyG yden) * hcleared

end ClearedToField

#print axioms towerFractionFieldDerivG_amG_C
#print axioms rischDE_field_of_cleared

/-! ### ★ The recursive `CRischFieldSpec (QFunNZG β)` — the precise layer-bridge obstruction

The recursive instance — `crischDESolve b g = some y → (toK y)′ + (toK b)·(toK y) = toK g` over
`QFunNZG β`, where `crischDESolve` here runs the generic §6 pipeline `cRischDEG ([1] : CPolyG β) fuel
b.1.1 b.1.2 g.1.1 g.1.2` over `CPolyG β` — is **not** closeable from the available §6 correctness, for two
distinct reasons. The first is fundamental; the second is supplied above.

1. **★ The conditional-hypotheses gap (the fundamental obstruction).** The §6 correctness
   `cRischDEG_rdeCleared_gen` / `cRischDEG_rdeCleared_qfunNZG` (`ComputableRischDETowerCorrectG`) is **not**
   the clean implication "`cRischDEG … = some (ynum, yden)` ⟹ cleared identity". It is *conditional on the
   entire pipeline being threaded*: it takes as **hypotheses** the primitive-regime witness `hprim`, the §6.2
   normal-denominator success `hnorm : cRdeNormalDenominatorG … = some (a0, b0, c0, h0)`, the §6.4 SPDE success
   `hspde : cSPDEG … = some (bbar, cbar, m, α', β)`, the §6.5 non-cancellation success `hpoly :
   cPolyRischDENoCancelG … = some v`, the transparent-input chain `hin : CSPDEGClearedInputsGen …` (which
   itself bundles, *per recursion level*, `Associated`-gcd correctness, fuel bounds, and nonzero-denominator
   facts), plus the §6.2 divisibility side-conditions (`hdn`, `hfden0`, `hgden0`, `hdvdB`, `hdvdC`).
   **None of these is derivable from the bare `cRischDEG … = some (ynum, yden)`.** To build the
   instance one must run the pipeline's stages *forward* and prove, from the bare `some`-result, that (a) each
   intermediate stage also returned `some` with the matching reassembly, and (b) the whole
   `CSPDEGClearedInputsGen` transparent-input predicate holds on a real run — i.e. re-derive the §6 pipeline's
   *structural decomposition theorem* (every successful `cRischDEG` run factors through successful, regular
   stages). That theorem does not exist; it is the documented continuation. It is the §6 analogue of the
   missing "`cIntegrateGFull … = some res` ⟹ `checkIdentityG … = true`" forward-threading — which is exactly why
   the `checkIdentityG` ⟹ field-identity bridge (`field_identity_of_checkIdentityG`,
   `ComputableIntegrateTowerCorrectG`) instead gates on the engine's **own** boolean `checkIdentityG` re-check
   rather than on a structural decomposition. An
   analogous *checked* RDE oracle — re-validating `cRischDEG`'s output by an engine boolean RDE check and
   bridging *that* — is the tractable route to a `CRischFieldSpec`-style guarantee; it is a separate engine
   addition, out of scope here (it touches `ComputableTowerRischDE`, owned elsewhere).

2. **The cleared → field bridge (supplied: `rischDE_field_of_cleared`).** Even *given* the cleared polynomial
   identity that stage (1) would yield (the conclusion of `cRischDEG_rdeCleared_gen`, over
   `(CFieldSpec.K β)[X]`), translating it to the field-level spec `(toK y)′ + (toK b)·(toK y) = toK g` over
   `RatFunc (CFieldSpec.K β)` is the `amG`/quotient-rule layer-bridge. **This half is done above**
   (`rischDE_field_of_cleared`), generically over the coefficient carrier: it reads the quotient rule off
   `towerFractionFieldDerivG_div` and divides the cleared identity through the nonzero
   `amG gden·amG fden·amG yden²`. (Composing it into the field spec additionally needs a **generic**
   `CDiffFieldSpec (QFunNZG β)` instance — only the `QFunNZG ℚ`-pinned `instCDiffFieldSpecQFunNZG` exists,
   though `toQFunNZG_towerDerivQFunNZG` is already generic, so the generic instance is a mechanical lift — and
   the identification of the spec's `(toK y)′` with `towerFractionFieldDerivG [1] (toQFunNZG y)`, which is
   exactly `CDiffFieldSpec.toK_cderiv` at the recursive instance.)

So the committed deliverable is: the `CRischFieldSpec` **class**, the **base `ℚ` instance** (axiom-clean), the
**discharged hyperexp residual** `crischDESolve_zero_intDeriv` (`D(∫R) = R` from the spec, removing the
`hintR` native-residual from the hyperexp soundness chain — the headline ask), and the **cleared → field half
of the recursive layer-bridge** `rischDE_field_of_cleared`. The recursive *instance* is blocked on the §6
pipeline's structural-decomposition theorem (reason 1), recorded here so the gap and its tractable route (a
checked RDE oracle) are explicit. -/

end DeepWiki.SymbolicIntegration
