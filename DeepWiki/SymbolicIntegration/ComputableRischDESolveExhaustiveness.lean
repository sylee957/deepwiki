import DeepWiki.SymbolicIntegration.ComputableRischDENormCompleteness
import DeepWiki.SymbolicIntegration.ComputableRischDEDegreeBound
import DeepWiki.SymbolicIntegration.ComputableRischDEStructural
import DeepWiki.SymbolicIntegration.ComputableRatFuncValuation

/-! # §6.4–6.6 RDE completeness — the Wf SPDE + poly-RDE solve is exhaustive (`hsolveWf`)

`RischDEInnerCompletenessWf` (`ComputableRischDECompleteness`) decomposes the deep §6 inner-solve
completeness into three converse clauses, `hnorm` / `hbound` / `hsolve`, stated against the fuel-free `Wf`
engine. `hnorm` is produced (modulo a Bronstein-Thm-6.1.2 divisibility) by `ComputableRischDENormCompleteness`;
`hbound` modulo a §6.3 cancellation residual by `ComputableRischDEDegreeBound`. This file pursues `hsolve` —
the **last and deepest** clause.

**What `hsolve` says.** `hsolve` is the SEARCH-EXHAUSTIVENESS of the §6.4 Wf SPDE peel (`cSPDEGWf`) +
§6.5/§6.6 Wf poly-RDE dispatcher (`cPolyRischDEGWf`): *if the input RDE has a polynomial solution then the
assembled Wf solve `cRischDEGWf` does not return `none`* —
`(∃ ynum yden, IsCRischDEGPolySol …) → (cRischDEGWf …).isSome = true`.

**The engine layer (`EngineLayerWf`).** `cRischDEGWf`'s body is a nested `match` over three Wf stages —
§6.2 `cRdeNormalDenominatorGWf`, §6.4 `cSPDEGWf` at the §6.3 bound degree on the special-cleared
coefficients, §6.5/§6.6 `cPolyRischDEGWf` — and a final reassembly. So `cRischDEGWf … = some _` **iff** each
of those three stages returns `some`:

* `cRischDEGWf_isSome_of_stages` — the three Wf stage successes force `cRischDEGWf.isSome = true` (pure
  control flow, no §6 mathematics);
* `cRischDEGWf_isSome_iff_stages` — the exact `isSome ↔ all-three-`some`` reading.

**The Wf exhaustiveness residual (`ExhaustiveResidualWf`, NEVER `sorry`).** `RischDESolveExhaustiveResidualWf`
bundles the three Wf stage-`some` implications directly (`hnorm`/`hspde`/`hpoly`), and
`hsolveWf_of_exhaustiveResidualWf` produces the exact `hsolveWf` clause from it. `rischDEInnerCompletenessWf_of_residuals`
(`AssembleWf`) then assembles `RischDEInnerCompletenessWf` from its three component Wf residuals.

The legacy fuel'd counterpart (`RischDEInnerCompleteness`, the non-`Wf` engine/preservation/degree-descent/
cancellation machinery) has been retired now that the fuel-free `Wf` twin above is the sole path consumed by
the production decision procedure (`ComputableRischDEDecisionProcedure.lean`). -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## Wf engine layer: `cRischDEGWf.isSome` from Wf stage `some`s

The fuel-free solver has the same nested control flow as `cRischDEG`, but its stages are the Wf normal
denominator, Wf SPDE, and Wf poly-RDE dispatcher. -/

section EngineLayerWf

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α] [CRischField α]

/-- The Wf stage `some`s force `cRischDEGWf.isSome`. -/
theorem cRischDEGWf_isSome_of_stages (Dt : CPolyG α) (fnum fden gnum gden : CPolyG α)
    (a0 b0 c0 h0 bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α)
    (hnorm : cRdeNormalDenominatorGWf Dt fnum fden gnum gden = some (a0, b0, c0, h0))
    (hspde : cSPDEGWf Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
        (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
        (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β))
    (hpoly : cPolyRischDEGWf Dt bbar cbar m = some v) :
    (cRischDEGWf Dt fnum fden gnum gden).isSome = true := by
  rw [cRischDEGWf, hnorm]
  simp only [hspde, hpoly, Option.isSome_some]

/-- The fuel-free assembled solve succeeds iff its three Wf stages succeed. -/
theorem cRischDEGWf_isSome_iff_stages (Dt : CPolyG α) (fnum fden gnum gden : CPolyG α) :
    (cRischDEGWf Dt fnum fden gnum gden).isSome = true ↔
      ∃ (a0 b0 c0 h0 bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α),
        cRdeNormalDenominatorGWf Dt fnum fden gnum gden = some (a0, b0, c0, h0)
        ∧ cSPDEGWf Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1
            (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
              (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
              (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1 : ℤ)
          = some (bbar, cbar, m, α', β)
        ∧ cPolyRischDEGWf Dt bbar cbar m = some v := by
  constructor
  · intro h
    obtain ⟨⟨ynum, yden⟩, hy⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, hpoly, _, _⟩ :=
      cRischDEGWf_some_imp_stages_structural Dt fnum fden gnum gden ynum yden hy
    exact ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, hpoly⟩
  · rintro ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, hpoly⟩
    exact cRischDEGWf_isSome_of_stages Dt fnum fden gnum gden a0 b0 c0 h0 bbar cbar m α' β v
      hnorm hspde hpoly

end EngineLayerWf

/-! ## The abstract non-cancellation solution predicate

`IsNoCancelSolK` is the shared `K[X]`-valued hypothesis vocabulary for the §6.5 non-cancellation base-oracle
agreement residuals consumed by the tower-induction step (`ComputableTowerRischDECompleteness`). -/

section NoCancelPredicate

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-- **An abstract (`K[X]`-valued) non-cancellation solution** `IsNoCancelSolK Dt b c q`:
`implicitDeriv (toPolyG Dt) q + toPolyG b · q = toPolyG c` for `q ∈ (CFieldSpec.K α)[X]` — the §6.5 equation
`Dq + b·q = c` (the post-SPDE shape, with leading coefficient `a = 1`). The non-cancellation analogue of
`IsReducedRdeSolK`. -/
def IsNoCancelSolK (Dt b c : CPolyG α) (q : (CFieldSpec.K α)[X]) : Prop :=
  Differential.implicitDeriv (toPolyG Dt) q + toPolyG b * q = toPolyG c

end NoCancelPredicate

/-! ## The §6.6 cancellation base-oracle hypotheses

`CancelPrimBaseOracle`/`CancelExpBaseOracle` and their uniform closures `CancelPrimOracleComplete`/
`CancelExpOracleComplete`, plus the no-top-cancellation engine-regime boundary `CancelPrimNoCancel`, are the
shared hypothesis vocabulary the tower-induction step (`ComputableTowerRischDECompleteness`) discharges from
the completeness IH one level down. -/

section CancelPredicate

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
  [CRischField α]

/-- **The per-step base-oracle hypothesis (primitive, the tower-induction IH)** `CancelPrimBaseOracle Dt b
c q`: the §6.6 eq. 6.23 base oracle `crischDESolve (cleadG b) (cleadG c)` returns `some s` whose `toK` is the
abstract solution's leading coefficient — `∃ s, crischDESolve (cleadG b) (cleadG c) = some s ∧ toK s =
(toPolyG q).leadingCoeff`. This bundles **completeness** (the oracle returns `some`) with **agreement** (it
returns the actual solution's leading coefficient `lc q`) — exactly what the degree-descent peel consumes. It
is the honest tower-induction hypothesis: at the coefficient level it is `crischDESolve`'s own completeness on
the base RDE the leading coefficient `lc q` solves (`FieldRDESolvable`-at-α). -/
def CancelPrimBaseOracle (b c : CPolyG α) (q : (CFieldSpec.K α)[X]) : Prop :=
  ∃ s : α, CRischField.crischDESolve (cleadG b) (cleadG c) = some s
    ∧ CFieldSpec.toK s = q.leadingCoeff

omit [CFracGcdCore α] in
/-- **The uniform base-oracle completeness hypothesis (primitive, the tower-induction IH)**
`CancelPrimOracleComplete Dt b`: for every `c'` and every degree-matched abstract solution `q'`
(`IsNoCancelSolK Dt b c' q'`, `deg q' = deg c'`), the eq. 6.23 base oracle finds its leading coefficient
(`CancelPrimBaseOracle b c' q'`). This is the honest tower-induction hypothesis in uniform form: the base
RDE solver `crischDESolve` is *complete and agreeing* on the leading-coefficient RDE at every level the
descent reaches. The single deep frontier the cancellation-regime exhaustiveness reduces to. -/
def CancelPrimOracleComplete (Dt b : CPolyG α) : Prop :=
  ∀ (c' : CPolyG α) (q' : (CFieldSpec.K α)[X]),
    IsNoCancelSolK Dt b c' q' → (q'.natDegree : ℤ) = cdegG c' → CancelPrimBaseOracle b c' q'

omit [CFracGcdCore α] [CRischField α] in
/-- **The no-top-cancellation hypothesis along the descent (the engine-regime boundary)**
`CancelPrimNoCancel Dt b`: every *nonzero* abstract solution `q'` of `D q' + b·q' = c'` is **degree-matched**
(`deg q' = deg c'`). This is exactly the regime where the engine's `m = deg c` search is exhaustive: genuine
top-cancellation (`deg q' > deg c'`, the §6.3-bound regime) is the documented boundary the cancellation
recursion's `m = deg c` start does not reach. An honest, precisely-named hypothesis (NOT a `sorry`). -/
def CancelPrimNoCancel (Dt b : CPolyG α) : Prop :=
  ∀ (c' : CPolyG α) (q' : (CFieldSpec.K α)[X]),
    IsNoCancelSolK Dt b c' q' → q' ≠ 0 → (q'.natDegree : ℤ) = cdegG c'

omit [CFracGcdCore α] in
/-- **The §6.6 eq. 6.24 base-RDE coefficient** `expCoeff Dt c b = b₀ + (deg c)·η` (`b₀ = cleadG b`,
`η = cExpEtaG Dt`), the first argument the hyperexponential engine `cPolyRischDECancelExpG` passes to
`crischDESolve` at working degree `deg c`. The `m·η` shift is the `tᵐ` factor's
hyperexponential contribution (`D(s·tᵐ) = (Ds + m·η·s)·tᵐ`). -/
def expCoeff (Dt : CPolyG α) (c b : CPolyG α) : α :=
  CField.add (cleadG b) (CField.mul (cnatCastG (cdegG c)) (cExpEtaG Dt))

/-- **The per-step base-oracle hypothesis (hyperexp, the tower-induction IH)** `CancelExpBaseOracle Dt
b c q`: the §6.6 eq. 6.24 base oracle `crischDESolve (expCoeff Dt c b) (cleadG c)` returns `some s`
whose `toK` is the abstract solution's leading coefficient. Bundles **completeness** with **agreement**
(`toK s = lc q`), threading the shift coefficient `expCoeff Dt c b`. The hyperexp analogue of
`CancelPrimBaseOracle`. -/
def CancelExpBaseOracle (Dt : CPolyG α) (b c : CPolyG α) (q : (CFieldSpec.K α)[X]) : Prop :=
  ∃ s : α, CRischField.crischDESolve (expCoeff Dt c b) (cleadG c) = some s
    ∧ CFieldSpec.toK s = q.leadingCoeff

omit [CFracGcdCore α] in
/-- **The uniform base-oracle completeness hypothesis (hyperexp, the tower-induction IH)**
`CancelExpOracleComplete Dt b`: for every `c'` and every degree-matched solution `q'`, the eq. 6.24
base oracle `crischDESolve (expCoeff Dt c' b) (cleadG c')` finds its leading coefficient. The hyperexp
analogue of `CancelPrimOracleComplete`. The honest tower-induction hypothesis for the hyperexponential
cancellation case. -/
def CancelExpOracleComplete (Dt b : CPolyG α) : Prop :=
  ∀ (c' : CPolyG α) (q' : (CFieldSpec.K α)[X]),
    IsNoCancelSolK Dt b c' q' → (q'.natDegree : ℤ) = cdegG c' → CancelExpBaseOracle Dt b c' q'

end CancelPredicate


/-! ## Wf §6.4–6.6 exhaustiveness residual

This is the fuel-free counterpart of `RischDESolveExhaustiveResidual`: a solution forces the Wf
normal-denominator stage, the Wf SPDE stage, and the Wf poly-RDE dispatcher to succeed. The resulting bridge
is the exact `RischDEInnerCompletenessWf.hsolve` field. -/

section ExhaustiveResidualWf

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
  [CRischField α]

/-- The Wf §6.4–6.6 exhaustiveness residual. -/
structure RischDESolveExhaustiveResidualWf (Dt fnum fden gnum gden : CPolyG α) : Prop where
  /-- §6.2/Wf: a polynomial solution makes the Wf normal-denominator step return `some`. -/
  hnorm : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    (cRdeNormalDenominatorGWf Dt fnum fden gnum gden).isSome = true
  /-- §6.4/Wf: a solution makes the Wf SPDE peel return `some`. -/
  hspde : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    ∀ a0 b0 c0 h0 : CPolyG α,
      cRdeNormalDenominatorGWf Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
      (cSPDEGWf Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1
          (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1 : ℤ)).isSome = true
  /-- §6.5/§6.6/Wf: for the Wf SPDE output, a solution makes the Wf poly-RDE dispatcher return `some`. -/
  hpoly : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    ∀ a0 b0 c0 h0 bbar cbar : CPolyG α, ∀ m : ℤ, ∀ α' β : CPolyG α,
      cRdeNormalDenominatorGWf Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
      cSPDEGWf Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1
          (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α', β) →
      (cPolyRischDEGWf Dt bbar cbar m).isSome = true

/-- The Wf exhaustiveness residual produces the exact Wf `hsolve` clause. -/
theorem hsolveWf_of_exhaustiveResidualWf (Dt fnum fden gnum gden : CPolyG α)
    (hres : RischDESolveExhaustiveResidualWf Dt fnum fden gnum gden) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRischDEGWf Dt fnum fden gnum gden).isSome = true := by
  intro hsol
  obtain ⟨⟨a0, b0, c0, h0⟩, hnorm⟩ := Option.isSome_iff_exists.mp (hres.hnorm hsol)
  obtain ⟨⟨bbar, cbar, m, α', β⟩, hspde⟩ :=
    Option.isSome_iff_exists.mp (hres.hspde hsol a0 b0 c0 h0 hnorm)
  obtain ⟨v, hpoly⟩ :=
    Option.isSome_iff_exists.mp (hres.hpoly hsol a0 b0 c0 h0 bbar cbar m α' β hnorm hspde)
  exact cRischDEGWf_isSome_of_stages Dt fnum fden gnum gden
    a0 b0 c0 h0 bbar cbar m α' β v hnorm hspde hpoly

end ExhaustiveResidualWf

/-! ## ★ `RischDEInnerCompletenessWf` fully assembled from its three Wf component residuals

The Wf path now has the same residual-level assembly as the legacy fueled path, but every component is stated
against the fuel-free APIs: `RdeNormalDivisibilityResidualWf`, `RdeBoundCancellationResidualWf`, and
`RischDESolveExhaustiveResidualWf`. This is the reusable proof object consumed by the Wf decision frontier. -/

section AssembleWf

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
  [CRischField α]

/-- **★ `RischDEInnerCompletenessWf` from its three Wf component residuals**. -/
theorem rischDEInnerCompletenessWf_of_residuals (Dt fnum fden gnum gden : CPolyG α)
    (hnormRes : RdeNormalDivisibilityResidualWf Dt fnum fden gnum gden)
    (hboundRes : RdeBoundCancellationResidualWf Dt fnum fden gnum gden)
    (hsolveRes : RischDESolveExhaustiveResidualWf Dt fnum fden gnum gden) :
    RischDEInnerCompletenessWf Dt fnum fden gnum gden where
  hnorm := hnormWf_of_divisibilityResidualWf Dt fnum fden gnum gden hnormRes
  hbound := hboundWf_of_cancellationResidualWf Dt fnum fden gnum gden hboundRes
  hsolve := hsolveWf_of_exhaustiveResidualWf Dt fnum fden gnum gden hsolveRes

end AssembleWf

/-! ### Restatement against `RischDEInnerCompletenessWf.hsolve`'s field type (anonymous `example`) -/

-- The Wf solve residual fits directly into the Wf inner-completeness assembly.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
    [CRischField α] (Dt fnum fden gnum gden : CPolyG α)
    (hnorm : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRdeNormalDenominatorGWf Dt fnum fden gnum gden).isSome = true)
    (hbound : ∀ a0 b0 c0 h0 : CPolyG α,
      cRdeNormalDenominatorGWf Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
      ∀ q : CPolyG α,
        IsReducedRdeSol Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1 q →
        cdegG q ≤ cRdeBoundDegreeG Dt
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1)
    (hres : RischDESolveExhaustiveResidualWf Dt fnum fden gnum gden) :
    RischDEInnerCompletenessWf Dt fnum fden gnum gden :=
  { hnorm := hnorm
    hbound := hbound
    hsolve := hsolveWf_of_exhaustiveResidualWf Dt fnum fden gnum gden hres }

/-! ## Operational witnesses: the reachable exhaustiveness layers fire concretely (`native_decide`)

The proven reachable layers are non-vacuous: on concrete *solvable* level-2 inputs the SPDE peel and the
poly-RDE dispatcher genuinely return `some`, and the assembled `cRischDEG` succeeds — certified by
`native_decide` over `ℚ(x)(t₁)`. These witness that `hsolve` is reached on real solvable RDEs, not
vacuously. -/

section OperationalWitnesses

/-- **The assembled `cRischDEG` succeeds on the solvable `Dy = 1`** (`cRischDEG_isSome_Dy_eq_one`,
`native_decide`): the integration RDE `Dy = 1` over `ℚ(x)(t₁)` is solvable (`y = t₁`), and the §6 solve
`cRischDEG` returns `some` — the §6.4–6.6 exhaustiveness witnessed operationally on the pure-integration
(`b = 0`) path that `cPolyRischDEG_isSome_of_bZero` covers. -/
theorem cRischDEG_isSome_Dy_eq_one :
    (cRischDEG ([CField.one] : CPolyG (QFunNZG ℚ)) towerRischDEFuel
      (CField.zero : Lvl2).1.1 (CField.zero : Lvl2).1.2
      (CField.one : Lvl2).1.1 (CField.one : Lvl2).1.2).isSome = true := by native_decide

/-- **The assembled `cRischDEG` succeeds on the solvable `Dy + y = t₁ + 1`** (`cRischDEG_isSome_Dy_plus_y`,
`native_decide`): the cancellation-path RDE `Dy + y = t₁ + 1` over `ℚ(x)(t₁)` is solvable (`y = t₁`), and the
§6 solve `cRischDEG` returns `some` — exhaustiveness on the §6.6 primitive-cancellation path (`f = 1 ≠ 0`, so
the SPDE peel + cancellation recursion run, not just integration). -/
theorem cRischDEG_isSome_Dy_plus_y :
    (cRischDEG ([CField.one] : CPolyG (QFunNZG ℚ)) towerRischDEFuel
      (CField.one : Lvl2).1.1 (CField.one : Lvl2).1.2
      towerRdeLvl2GPlusOne.1.1 towerRdeLvl2GPlusOne.1.2).isSome = true := by native_decide

end OperationalWitnesses

end DeepWiki.SymbolicIntegration
