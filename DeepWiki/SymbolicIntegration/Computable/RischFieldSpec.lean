import DeepWiki.SymbolicIntegration.Computable.IntegrateTowerCorrectG

/-! # Abstract soundness spec `CRischFieldSpec` for the field-level RDE oracle

`CRischFieldSpec α` asserts that a successful `CRischField.crischDESolve b g = some y` yields the
field-level Risch-DE identity `(toK y)′ + (toK b)·(toK y) = toK g` over `K = CFieldSpec.K α`. Provides
the constant base instance over `ℚ`, the discharged pure-integration residual `D(∫R) = R`
(`crischDESolve_zero_intDeriv`), and the cleared-to-field layer bridge `rischDE_field_of_cleared`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ### The `CRischFieldSpec` class

The abstract soundness of the field-level RDE oracle, read through `CFieldSpec.toK` into the genuine
field `K = CFieldSpec.K α` with `′` the `CDiffFieldSpec` derivation. -/

/-- Abstract soundness of the field-level RDE oracle `CRischField.crischDESolve`: whenever
`crischDESolve b g = some y`, the returned `y` solves `Dy + b·y = g` over `K = CFieldSpec.K α`,
read through `toK`: `(toK y)′ + (toK b)·(toK y) = toK g`, with `′` the `CDiffFieldSpec`
derivation. Carried as a typeclass so the tower recursion threads it. -/
class CRischFieldSpec (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CRischField α] where
  /-- A successful solve returns a genuine field-level RDE solution `(toK y)′ + (toK b)·(toK y) = toK g`. -/
  crischDESolve_spec : ∀ b g y : α, CRischField.crischDESolve b g = some y →
    @Differential.deriv _ _ CDiffFieldSpec.diffK (CFieldSpec.toK y)
        + CFieldSpec.toK b * CFieldSpec.toK y
      = CFieldSpec.toK g

/-! ### The constant base instance `CRischFieldSpec ℚ` -/

/-- `CRischFieldSpec ℚ`, the constant-field base soundness: over `ℚ` (`D = 0`, `toK = id`) the
oracle is `crischDESolve b g = g/b` (`b ≠ 0`) or `0` (`b = 0 ∧ g = 0`), and the spec `0 + b·y = g`
is the division soundness `b·(g/b) = g`. -/
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

/-! ### The pure-integration residual `D(∫R) = R`

For the pure-integration RDE `Dy = R` (`b = 0`), a successful base-oracle solve gives the
antiderivative identity `D(∫R) = R` lifted to the tower fraction field, for an arbitrary
residual `R : α`. -/

section ResidualDischarge

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CRischField α] [CRischFieldSpec α] [Algebra ℚ (CFieldSpec.K α)]

omit [CRischField α] [CRischFieldSpec α] in
/-- `towerFractionFieldDerivG Dt (amG α (C k)) = amG α (C k′)`: the tower fraction-field derivation
of a constant is the constant of its `CDiffFieldSpec` derivative. -/
theorem towerFractionFieldDerivG_amG_C (Dt : CPolyG α) (k : CFieldSpec.K α) :
    towerFractionFieldDerivG Dt (amG α (Polynomial.C k))
      = amG α (Polynomial.C (@Differential.deriv _ _ CDiffFieldSpec.diffK k)) := by
  rw [towerFractionFieldDerivG, amG, extendDeriv_algebraMap, Differential.implicitDeriv_C]

/-- The pure-integration residual `D(∫R) = R`: if `crischDESolve 0 R = some intR`, the constant
`intR` embedded into the tower fraction field as `amG (C (toK intR))` differentiates back to
`amG (C (toK R))`. Discharges the base-oracle hypothesis `hintR` of
`ComputableHyperexpFullSoundness.cIntegrateHyperexpNormalGWf_sound`. -/
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

/-! ### The cleared-to-field layer bridge for the RDE oracle

Translates the cleared polynomial identity over `(CFieldSpec.K α)[X]` (the shape
`cRischDEG_rdeCleared_gen` outputs) into the field-level RDE identity over
`RatFunc (CFieldSpec.K α)`, via the quotient rule `towerFractionFieldDerivG_div`. -/

section ClearedToField

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

open CPolyG

/-- Cleared-to-field layer bridge for the RDE oracle: given the cleared polynomial identity of
`cRischDEG_rdeCleared_gen` (with `D = implicitDeriv (toPolyG Dt)`) and the denominators `fden`,
`gden`, `yden` nonzero, the field-level Risch-DE identity
`towerFractionFieldDerivG Dt (amG ynum/amG yden) + (amG fnum/amG fden)·(amG ynum/amG yden)
= amG gnum/amG gden` holds over `RatFunc (CFieldSpec.K α)`. -/
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
