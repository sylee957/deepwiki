import DeepWiki.SymbolicIntegration.ComputableRischFieldSpec
import DeepWiki.SymbolicIntegration.ComputableOneShotSoundness

/-! # §6 RDE structural decomposition — `cRischDEG = some _` ⟹ the stage `some`-results

`ComputableRischFieldSpec` records the **recursive** `CRischFieldSpec (QFunNZG β)` instance as the
documented layer-bridge obstruction: the §6 correctness `cRischDEG_rdeCleared_gen`
(`ComputableRischDETowerCorrectG`) is **conditional** on ≈13 hypotheses, none of which were yet derived
from the bare success `cRischDEG … = some (ynum, yden)`. This file **attempts** that derivation — the §6
*structural-decomposition theorem* — and partitions the ≈13 hypotheses into the **derivable** class
(forced by `cRischDEG`'s own `match` structure) and the **irreducible residual** (global regularity the
algorithm does not self-certify), stating each precisely.

The §6 RDE oracle `cRischDEG Dt fuel fnum fden gnum gden` is a chain of `match … with | none => none | …`
forms:

  `match cRdeNormalDenominatorG … with | some (a0,b0,c0,h0) =>`
  `  let (a,b,c,h1) := cRdeSpecialDenominatorG Dt fuel a0 b0 c0`
  `  match cSPDEG Dt fuel a b c (cRdeBoundDegreeG Dt fuel a b c) with | some (bbar,cbar,m,α',β) =>`
  `    match cPolyRischDEG Dt fuel bbar cbar m with | some v => some (cmulG (caddG (cmulG α' v) β) h1, h0)`

so a successful run **structurally forces** each intermediate stage to have returned `some` with the very
reassembly the capstone consumes. This is exactly the **derivable** bulk of the capstone's hypotheses.

* **`cRischDEG_some_imp_stages`** — ★ the structural-decomposition core: `cRischDEG … = some (ynum, yden)`
  yields the §6.2 `hnorm` (`cRdeNormalDenominatorG = some (a0,b0,c0,h0)`), the §6.4 `hspde` (`cSPDEG … =
  some (bbar,cbar,m,α',β)` at the bound degree on the special-cleared coefficients), the §6.5/§6.6
  dispatcher result `cPolyRischDEG … = some v`, and the output identification `ynum = (α'·v+β)·h1`,
  `yden = h0`. The three stage-`some`-results derived from bare success.
* **`cPolyRischDEG_some_imp_noCancel_of_primitive`** — the dispatcher → non-cancellation bridge in the
  primitive regime: when `Dt` is primitive (`cdegG Dt = 0`) and `bbar ≠ 0` (`db > max 0 (δ−1) = 0`),
  `cPolyRischDEG Dt fuel bbar cbar m = cPolyRischDENoCancelG Dt fuel bbar cbar m`, so the capstone's
  `hpoly` (which is the §6.5 non-cancellation solve, NOT the dispatcher) is the dispatcher result.

The genuinely **irreducible residual** — `hprim` (primitive-regime restriction; `cRischDEG` runs all
regimes), the §6.2 divisibility/fuel side-conditions (`hdn`, `hfbB`, `hdvdB`, `hfbC`, `hdvdC`), and the
transparent-input chain `hin : CSPDEGClearedInputsGen` (whose per-level `Associated`-gcd clauses are the
`CPrimPRSGenAssocReg` regularity that `associated_toPolyG_cgcdFFCore` itself takes as a hypothesis, and
which the engine never self-certifies) — is isolated and named in `RischDEStructuralResidual` below, with
the precise reason each is not forced by bare success. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α]

/-! ### ★ The structural-decomposition core: bare success ⟹ the stage `some`-results

`cRischDEG`'s body is a nested `match`; a `some` output cannot arise unless every guarded `match`
selected its `some`-branch with the matching reassembly. We peel the matches one by one (`rcases` on each
stage's `Option`, discharging the `none` arms by `simp`), reading off the §6.2/§6.4/§6.5 successes and the
output identification. This is the **bulk** of the capstone's hypotheses — the part genuinely forced by
the algorithm's own control flow. -/

/-- **★ `cRischDEG = some _` structurally forces the stage `some`-results.** If
`cRischDEG Dt fuel fnum fden gnum gden = some (ynum, yden)`, then there exist the §6.2 normal-denominator
output `(a0, b0, c0, h0)`, the §6.4 SPDE output `(bbar, cbar, m, α', β)` (on the special-cleared
coefficients at the §6.3 bound degree), and the §6.5/§6.6 dispatcher solution `v`, with

  `cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0)`,
  `cSPDEG Dt fuel ā b̄ c̄ (cRdeBoundDegreeG Dt fuel ā b̄ c̄) = some (bbar, cbar, m, α', β)`,
  `cPolyRischDEG Dt fuel bbar cbar m = some v`,

where `(ā, b̄, c̄, h1) = cRdeSpecialDenominatorG Dt fuel a0 b0 c0`, and the output reads
`ynum = (α'·v + β)·h1`, `yden = h0`. The three stage-`some`-results (`hnorm`, `hspde`, the dispatcher
result) derived from bare success — the derivable bulk of `cRischDEG_rdeCleared_gen`'s hypotheses. -/
theorem cRischDEG_some_imp_stages [CRischField α] (Dt : CPolyG α) (fuel : ℕ)
    (fnum fden gnum gden ynum yden : CPolyG α)
    (hsucc : cRischDEG Dt fuel fnum fden gnum gden = some (ynum, yden)) :
    ∃ (a0 b0 c0 h0 bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α),
      cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0)
      ∧ cSPDEG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
          (cRdeBoundDegreeG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α', β)
      ∧ cPolyRischDEG Dt fuel bbar cbar m = some v
      ∧ ynum = cmulG (caddG (cmulG α' v) β) (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.2
      ∧ yden = h0 := by
  rw [cRischDEG] at hsucc
  -- peel each `match` on `hsucc` only; keep every stage equation, then assemble the existential.
  -- (Destructure via `Option.rec` matching: `obtain`/`match` on `hsucc` would re-derive, so we case
  --  on each stage's value with a kept equation, discharging the `none` arms.)
  rcases hnorm : cRdeNormalDenominatorG Dt fuel fnum fden gnum gden with _ | ⟨a0, b0, c0, h0⟩ <;>
    rw [hnorm] at hsucc
  · exact absurd hsucc (by simp)
  · simp only at hsucc
    rcases hspde : cSPDEG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
        (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1 : ℤ)
      with _ | ⟨bbar, cbar, m, α', β⟩ <;> rw [hspde] at hsucc
    · exact absurd hsucc (by simp)
    · simp only at hsucc
      rcases hpoly : cPolyRischDEG Dt fuel bbar cbar m with _ | v <;> rw [hpoly] at hsucc
      · exact absurd hsucc (by simp)
      · rw [Option.some.injEq, Prod.mk.injEq] at hsucc
        obtain ⟨hynum, hyden⟩ := hsucc
        -- supply witnesses: the `cRdeNormalDenominatorG` conjunct was rewritten to `some _ = some _`
        -- by its `rcases … :` (reflexivity); `hspde`/`hpoly` carry their kept equations; the last two
        -- are the reassembly equations.
        exact ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v,
          rfl, hspde, hpoly, hynum.symm, hyden.symm⟩

/-! ### The dispatcher → non-cancellation bridge (primitive regime, positive `deg(bbar)`)

The capstone `cRischDEG_rdeCleared_gen` takes `hpoly : cPolyRischDENoCancelG Dt fuel bbar cbar m = some v`
— the §6.5 **non-cancellation** solve — whereas `cRischDEG`'s body (and hence `cRischDEG_some_imp_stages`)
yields the §6.5/§6.6 **dispatcher** `cPolyRischDEG Dt fuel bbar cbar m = some v`. The dispatcher routes by
`δ = cdegG Dt` and `db = cdegG bbar` (Lemma 6.5.1): in the **primitive** regime (`δ = 0`) with
`db > max 0 (δ−1) = 0` (i.e. `bbar` of positive degree) it routes to `cPolyRischDENoCancelG` verbatim. So
under `cdegG Dt = 0` and `0 < cdegG bbar`, the dispatcher result IS the capstone's non-cancellation result.
(`bbar = 0` would route to pure integration `cIntegratePolyG`; `db = 0` to the primitive cancellation
recursion `cPolyRischDECancelPrimG` — neither is `cPolyRischDENoCancelG`, so the bridge needs
`0 < cdegG bbar`, which the capstone's downstream consumption implicitly assumes.) -/

omit [CFracGcdCore α] in
/-- **The §6.5/§6.6 dispatcher reduces to the non-cancellation solve** in the primitive regime with
positive `deg(bbar)`: if `cdegG Dt = 0` (primitive monomial) and `0 < cdegG bbar`, then
`cPolyRischDEG Dt fuel bbar cbar m = cPolyRischDENoCancelG Dt fuel bbar cbar m`. So a dispatcher success
`cPolyRischDEG … = some v` (from `cRischDEG_some_imp_stages`) IS the capstone's `hpoly`. The
`bbar`-nonzero / positive-degree routing condition of Lemma 6.5.1's non-cancellation branch. -/
theorem cPolyRischDEG_eq_noCancel_of_primitive [CRischField α] (Dt : CPolyG α) (fuel : ℕ)
    (bbar cbar : CPolyG α) (m : ℤ) (hδ : cdegG Dt = 0) (hdb : 0 < cdegG bbar) :
    cPolyRischDEG Dt fuel bbar cbar m = cPolyRischDENoCancelG Dt fuel bbar cbar m := by
  rw [cPolyRischDEG]
  -- `bbar ≠ 0` (positive degree): `cdegG = (cnormG).length - 1` and `cisZeroG = (cnormG).isEmpty`,
  -- so `0 < cdegG bbar` forces the underlying list nonempty (length ≥ 2), hence `cisZeroG = false`.
  have hlen : 0 < (cnormG bbar : List α).length := by
    have := hdb; rw [cdegG] at this; omega
  have hbne : cisZeroG bbar = false := by
    rw [cisZeroG, List.isEmpty_eq_false_iff_exists_mem]
    exact List.exists_mem_of_length_pos hlen
  -- `δ = 0`, so `max 0 (δ − 1) = 0`, and `db = cdegG bbar > 0` makes the non-cancellation guard fire
  simp only [hbne, Bool.false_eq_true, if_false, hδ, Nat.cast_zero, zero_sub]
  rw [if_pos]
  -- the guard `(cdegG bbar : ℤ) > max 0 (-1) = 0`
  rw [show (max (0 : ℤ) (-1)) = 0 by norm_num]
  exact_mod_cast hdb

/-! ### ★ The combined derivable decomposition (primitive regime, positive `deg(bbar)`)

Composing `cRischDEG_some_imp_stages` (the three stage-`some` results) with
`cPolyRischDEG_eq_noCancel_of_primitive` (the dispatcher → non-cancellation bridge): in the primitive
regime (`cdegG Dt = 0`) with positive `deg(bbar)`, a bare success `cRischDEG … = some (ynum, yden)` yields
`hnorm`, `hspde`, **and** the capstone's `hpoly` (`cPolyRischDENoCancelG … = some v`) — three of the
≈13 hypotheses of `cRischDEG_rdeCleared_gen`, all derived from bare success. The remaining hypotheses are
the irreducible residual `RischDEStructuralResidual` below. -/

/-- **★ The derivable hypotheses of `cRischDEG_rdeCleared_gen` from bare success** (primitive regime,
positive `deg(bbar)`): if `cRischDEG Dt fuel fnum fden gnum gden = some (ynum, yden)`, `cdegG Dt = 0`, and
the §6.4 SPDE output `bbar` has positive degree, then the §6.2 `hnorm`, the §6.4 `hspde` (at the bound
degree on the special-cleared coefficients), and the capstone's §6.5 non-cancellation `hpoly`
(`cPolyRischDENoCancelG … = some v`) all hold, with the output reading `ynum = (α'·v + β)·h1`, `yden = h0`.
The structural-decomposition theorem's derivable conclusion — the three stage results threaded through the
dispatcher bridge. (`hprim`, the §6.2 divisibility/fuel side-conditions, and the per-level `Associated`-gcd
transparent-input chain `hin` remain the irreducible residual; see `RischDEStructuralResidual`.) -/
theorem cRischDEG_some_imp_noCancel_of_primitive [CRischField α] (Dt : CPolyG α) (fuel : ℕ)
    (fnum fden gnum gden ynum yden : CPolyG α) (hδ : cdegG Dt = 0)
    (hsucc : cRischDEG Dt fuel fnum fden gnum gden = some (ynum, yden)) :
    ∃ (a0 b0 c0 h0 bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α),
      cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0)
      ∧ cSPDEG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
          (cRdeBoundDegreeG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α', β)
      ∧ (0 < cdegG bbar → cPolyRischDENoCancelG Dt fuel bbar cbar m = some v)
      ∧ ynum = cmulG (caddG (cmulG α' v) β) (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.2
      ∧ yden = h0 := by
  obtain ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, hdisp, hynum, hyden⟩ :=
    cRischDEG_some_imp_stages Dt fuel fnum fden gnum gden ynum yden hsucc
  refine ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, ?_, hynum, hyden⟩
  intro hdb
  rw [← cPolyRischDEG_eq_noCancel_of_primitive Dt fuel bbar cbar m hδ hdb]
  exact hdisp

/-! ### ★ The precise irreducible residual (what bare success does NOT self-certify)

The structural decomposition above derives `hnorm`, `hspde`, `hpoly` (3 of ≈13). The remaining hypotheses
of `cRischDEG_rdeCleared_gen` are **not** forced by `cRischDEG … = some _`; each asserts a fact the engine
does not validate on a successful run. We package them as the explicit residual, with the precise reason
each is irreducible. (This is a `Prop`-bundle of stated assumptions, NOT proved from success — it makes the
boundary citable, with NO `sorry`.) -/

section Residual

variable [CFieldSpec α] [CDiffFieldSpec α] [CRischField α]

/-- **The precise irreducible residual of the §6 RDE structural decomposition**
`RischDEStructuralResidual Dt fuel fnum fden gnum gden a0 b0 c0 h0`: the hypotheses of
`cRischDEG_rdeCleared_gen` that a bare success `cRischDEG … = some _` does NOT self-certify, bundled with
the derivable stage results (`cRischDEG_some_imp_stages`) factored out. Three irreducible classes:

* **`hprim`** — `cdegG (cSpecialPolyG Dt fuel) = 0` (primitive regime). `cRischDEG` runs **all** monomial
  regimes (primitive / hyperexponential / hypertangent); `cRischDEG_rdeCleared_gen` is proved **only** for
  the primitive special regime (it `rw`s `cRdeSpecialDenominatorG_primitive_eq_gen`). A non-primitive
  success satisfies a *different* cleared identity, so `hprim` is a genuine regime restriction, not forced.
* **§6.2 divisibility/fuel side-conditions** (`hdn`, `hfbB`, `hdvdB`, `hfbC`, `hdvdC`). `cRdeNormalDenominatorG`
  checks **only** `cdvdG fuel en dnh2` before returning `some`; it does NOT check that the normal part `dₙ`
  is nonzero (`hdn`), that the `B`/`C` numerators are divisible by `fden`/`gden` (`hdvdB`/`hdvdC` — it
  computes `cdivG` unconditionally, truncating on non-divisibility), or the fuel bounds (`hfbB`/`hfbC`).
  These hold on regular inputs but are not validated by the `some`-return.
* **`hin`** — `CSPDEGClearedInputsGen` on the special-cleared coefficients at the bound degree. This bundles,
  **per recursion level**, the gcd-correctness `Associated (toPolyG (cgcdFFCore …)) (gcd …)` — which
  `associated_toPolyG_cgcdFFCore` *itself* discharges only from a `CPrimPRSGenAssocReg` per-step
  content-exactness hypothesis (`ComputableTowerGcdFFCorrect`), a per-run regularity the engine carries as
  an explicit assumption and **never** decides/self-certifies — plus per-level fuel bounds and
  nonzero-denominator facts. This is the deep kernel: the §6 pipeline does not re-validate its gcds, so the
  `Associated` clauses are not recoverable from `cRischDEG … = some _`.

Bundling these (with `hδ : cdegG Dt = 0` and `0 < cdegG bbar` for the dispatcher bridge) and the derivable
stage results yields the full `cRischDEG_rdeCleared_gen` hypothesis set — see
`rdeCleared_of_success_and_residual`. -/
structure RischDEStructuralResidual (Dt : CPolyG α) (fuel : ℕ)
    (fnum fden gnum gden a0 b0 c0 h0 : CPolyG α) : Prop where
  /-- Primitive special regime: `cdegG (cSpecialPolyG Dt fuel) = 0` (the capstone is primitive-only). -/
  hprim : cdegG (cSpecialPolyG Dt fuel) = 0
  /-- §6.2: the normal part `dₙ = (cSplitFactorFastG Dt fuel fden).1` is nonzero. -/
  hdn : toPolyG (cSplitFactorFastG Dt fuel fden).1 ≠ 0
  /-- §6.2: the input denominator `fden` is nonzero. -/
  hfden0 : cnormG fden ≠ []
  /-- §6.2: the input denominator `gden` is nonzero. -/
  hgden0 : cnormG gden ≠ []
  /-- §6.2 fuel bound on the `B`-numerator. -/
  hfbB : (cnormG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) fnum)
      (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h0)) fden)) :
      List α).length ≤ fuel
  /-- §6.2: `fden` divides the `B`-numerator (the `cdivG` clearing is exact). -/
  hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) fnum)
      (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h0)) fden))
  /-- §6.2 fuel bound on the `C`-numerator. -/
  hfbC : (cnormG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) h0) gnum) :
      List α).length ≤ fuel
  /-- §6.2: `gden` divides the `C`-numerator (the `cdivG` clearing is exact). -/
  hdvdC : toPolyG gden ∣ toPolyG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) h0) gnum)
  /-- §6.4: the per-level transparent-input chain `CSPDEGClearedInputsGen` on the special-cleared
  coefficients at the §6.3 bound degree — bundling the per-level `Associated`-gcd correctness (the
  `CPrimPRSGenAssocReg` regularity kernel), fuel bounds, and nonzero-denominator facts. -/
  hin : CSPDEGClearedInputsGen Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
      (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1 (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
      (cRdeBoundDegreeG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
        (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1 : ℤ)

/-! ### ★ The boundary theorem: bare success + the residual ⟹ the cleared identity

Composing the derivable decomposition (`cRischDEG_some_imp_noCancel_of_primitive`) with the precise
residual (`RischDEStructuralResidual`) recovers **exactly** the hypotheses of `cRischDEG_rdeCleared_gen`,
hence the cleared Risch-DE identity for the returned `y = ynum/yden`. This makes the boundary citable: the
ONLY assumptions beyond the bare success and the structural side-conditions (`hδ`, positive `deg(bbar)`)
are those bundled in `RischDEStructuralResidual` — the primitive-regime restriction, the §6.2
divisibility/fuel side-conditions, and the per-level `Associated`-gcd transparent-input chain (whose
`CPrimPRSGenAssocReg` kernel the engine never self-certifies). -/

/-- **★ The §6 cleared Risch-DE identity from bare success and the isolated residual** (primitive regime,
positive `deg(bbar)`): given `cRischDEG Dt fuel fnum fden gnum gden = some (ynum, yden)`, `cdegG Dt = 0`,
the SPDE output `bbar` of positive degree, and the irreducible residual `RischDEStructuralResidual` on the
matching §6.2 normal-denominator output, the returned `y = ynum/yden` satisfies the cleared identity
`gden·fden·(D(ynum)·yden − ynum·D(yden)) + gden·fnum·ynum·yden = gnum·fden·yden²` over `(CFieldSpec.K α)[X]`.
This is `cRischDEG_rdeCleared_gen` with its ≈13 hypotheses partitioned: the three stage-`some` results
derived from bare success (`cRischDEG_some_imp_noCancel_of_primitive`), the rest supplied by the residual —
the precise structural-decomposition boundary. -/
theorem rdeCleared_of_success_and_residual (Dt : CPolyG α) (fuel : ℕ)
    (fnum fden gnum gden ynum yden : CPolyG α) (hδ : cdegG Dt = 0)
    (hsucc : cRischDEG Dt fuel fnum fden gnum gden = some (ynum, yden))
    (hres : ∀ a0 b0 c0 h0 : CPolyG α,
      cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0) →
      RischDEStructuralResidual Dt fuel fnum fden gnum gden a0 b0 c0 h0)
    (hdb : ∀ a0 b0 c0 bbar cbar : CPolyG α, ∀ m : ℤ, ∀ α' β : CPolyG α,
      cSPDEG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
          (cRdeBoundDegreeG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α', β) → 0 < cdegG bbar) :
    toPolyG gden * toPolyG fden
        * (Differential.implicitDeriv (toPolyG Dt) (toPolyG ynum) * toPolyG yden
            - toPolyG ynum * Differential.implicitDeriv (toPolyG Dt) (toPolyG yden))
        + toPolyG gden * toPolyG fnum * toPolyG ynum * toPolyG yden
      = toPolyG gnum * toPolyG fden * toPolyG yden ^ 2 := by
  -- the three stage `some`-results from bare success (control-flow decomposition)
  obtain ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, hdisp, hynum, hyden⟩ :=
    cRischDEG_some_imp_stages Dt fuel fnum fden gnum gden ynum yden hsucc
  have hres' := hres a0 b0 c0 h0 hnorm
  have hdb' := hdb a0 b0 c0 bbar cbar m α' β hspde
  -- the dispatcher result is the capstone's `hpoly` (non-cancellation) via the primitive bridge
  have hpoly : cPolyRischDENoCancelG Dt fuel bbar cbar m = some v := by
    rw [← cPolyRischDEG_eq_noCancel_of_primitive Dt fuel bbar cbar m hδ hdb']; exact hdisp
  -- the capstone's cleared identity for the reassembled `y = (Q·[1])/h0`
  have hcap := cRischDEG_rdeCleared_gen Dt fuel fnum fden gnum gden a0 b0 c0 h0 bbar cbar m α' β v
    hres'.hprim hnorm hres'.hdn hres'.hfden0 hres'.hgden0 hres'.hfbB hres'.hdvdB hres'.hfbC hres'.hdvdC
    hspde hres'.hin hpoly
  simp only at hcap
  -- in the primitive regime the special-denominator 4th component `h1` is `[CField.one]`, so our
  -- `ynum = (Q)·h1` is the capstone's `ynum = (Q)·[1]`; `yden = h0`.
  have hh1 : (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.2 = ([CField.one] : CPolyG α) := by
    rw [cRdeSpecialDenominatorG_primitive_eq_gen Dt fuel a0 b0 c0 hres'.hprim]
  rw [hh1] at hynum
  rw [hynum, hyden]
  exact hcap

/-! ### ★ The cancellation regime — same cleared identity, same shared residual (primitive case)

The non-cancellation path above feeds the capstone `cRischDEG_rdeCleared_gen` an `hpoly` of the
**non-cancellation success** form `cPolyRischDENoCancelG … = some v`, which the capstone immediately
converts (via `cPolyRischDENoCancelG_cleared_identity_gen`) to the poly-RDE field identity
`D(v) + bbar·v = cbar`. Every downstream stage of the capstone — `cSPDEG_cleared_lifting_of_inputs_gen`
(takes the identity directly) and `cRdeNormalDenominatorG_cleared_lift_gen` — is **regime-agnostic**:
it consumes only that poly-RDE identity, never the solver form. So we re-factor the capstone at the
poly-RDE identity (`rdeClearedIdentity_of_polyRDEIdentity`), then feed it the cancellation poly-RDE
soundness `cPolyRischDEG_cancelPrim_sound` (base-oracle-free, `ComputableOneShotSoundness`) for the
**primitive cancellation** regime (`cdegG Dt = 0`, `cdegG bbar = 0`, `bbar ≠ 0`).

The residual is **identical** to the non-cancellation path's `RischDEStructuralResidual`: the cancellation
poly-RDE soundness carries NO base-oracle hypothesis (`[CRischFieldSpec α]`), so it adds nothing — the
only change is the §6.5/§6.6 dispatch condition (`cdegG bbar = 0` instead of `0 < cdegG bbar`).

**The hyperexponential cancellation regime (`cdegG Dt = 1`, `cPolyRischDEG_cancelExp_sound`) is NOT
reachable here**: the capstone is gated on the **primitive special regime** `hprim : cdegG (cSpecialPolyG
Dt fuel) = 0` (it `rw`s `cRdeSpecialDenominatorG_primitive_eq_gen`), but `cdegG Dt = 1` makes the special
polynomial `cSpecialPolyG Dt fuel` (the special part of `Dt`, `= t` for hyperexp) have degree `1`, so
`hprim` cannot hold and the §6.2 special-denominator reduction is non-trivial there. Covering CancelExp
would need a hyperexponential-special-regime cleared lifting, which does not exist — exactly the
non-primitive special case the residual docstring flags ("a non-primitive success satisfies a *different*
cleared identity"). This is the precise, cancellation-specific obstruction. -/

omit [CRischField α] in
/-- **★ The §6 cleared identity from the residual and the bare poly-RDE identity** (primitive regime): the
capstone `cRischDEG_rdeCleared_gen` re-factored to take the §6.5/§6.6 poly-RDE field identity
`D(v) + bbar·v = cbar` (in `cmonomialDeriv`/`toPolyG` form) **directly**, rather than the non-cancellation
solver-success form `cPolyRischDENoCancelG … = some v`. Given the primitive special regime, the §6.2 normal
denominator output, its divisibility/fuel certificates, the §6.4 SPDE output under `CSPDEGClearedInputsGen`,
and `hidentity`, the reconstruction `ynum = (α'·v + β)·[1]`, `yden = h0` satisfies the cleared Risch-DE
identity over `(CFieldSpec.K α)[X]`. The poly-RDE-identity-keyed spine shared by BOTH regimes — its single
regime-dependent input is `hidentity`, supplied by the non-cancellation or the cancellation solver. -/
theorem rdeClearedIdentity_of_polyRDEIdentity (Dt : CPolyG α) (fuel : ℕ)
    (fnum fden gnum gden a0 b0 c0 h0 : CPolyG α)
    (bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α)
    (hprim : cdegG (cSpecialPolyG Dt fuel) = 0)
    (hnorm : cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0))
    (hdn : toPolyG (cSplitFactorFastG Dt fuel fden).1 ≠ 0)
    (hfden0 : cnormG fden ≠ []) (hgden0 : cnormG gden ≠ [])
    (hfbB : (cnormG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h0)) fden)) :
        List α).length ≤ fuel)
    (hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h0)) fden)))
    (hfbC : (cnormG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) h0) gnum) :
        List α).length ≤ fuel)
    (hdvdC : toPolyG gden ∣ toPolyG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) h0) gnum))
    (hspde : cSPDEG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1 (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β))
    (hin : CSPDEGClearedInputsGen Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1 (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1 : ℤ))
    (hidentity : Differential.implicitDeriv (toPolyG Dt) (toPolyG v) + toPolyG bbar * toPolyG v
      = toPolyG cbar) :
    toPolyG gden * toPolyG fden
        * (Differential.implicitDeriv (toPolyG Dt) (toPolyG (cmulG (caddG (cmulG α' v) β) [CField.one]))
              * toPolyG h0
            - toPolyG (cmulG (caddG (cmulG α' v) β) [CField.one])
              * Differential.implicitDeriv (toPolyG Dt) (toPolyG h0))
        + toPolyG gden * toPolyG fnum * toPolyG (cmulG (caddG (cmulG α' v) β) [CField.one]) * toPolyG h0
      = toPolyG gnum * toPolyG fden * toPolyG h0 ^ 2 := by
  set Q := caddG (cmulG α' v) β with hQ
  -- the primitive special-denominator stage is the identity, so the SPDE was run on `(a0, b0, c0)`
  have hspecial := cRdeSpecialDenominatorG_primitive_eq_gen Dt fuel a0 b0 c0 hprim
  rw [hspecial] at hspde hin
  simp only at hspde hin
  -- §6.4-§6.5 spine: from the poly-RDE identity for `v`, `Q = α'·v + β` solves the reduced equation
  have hred : toPolyG a0 * Differential.implicitDeriv (toPolyG Dt) (toPolyG Q) + toPolyG b0 * toPolyG Q
      = toPolyG c0 :=
    cSPDEG_cleared_lifting_of_inputs_gen Dt fuel a0 b0 c0
      (cRdeBoundDegreeG Dt fuel a0 b0 c0 : ℤ) bbar cbar m α' β hspde hin v hidentity
  -- `ynum = Q·[1]` has `toPolyG ynum = toPolyG Q`
  have hone : toPolyG ([CField.one] : CPolyG α) = 1 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]
  have hynum : toPolyG (cmulG Q [CField.one]) = toPolyG Q := by
    rw [toPolyG_cmulG, hone, mul_one]
  -- §6.2 normal-denominator cleared lifting from the reduced solve
  have hlift := cRdeNormalDenominatorG_cleared_lift_gen Dt fuel fnum fden gnum gden a0 b0 c0 h0 Q
    hnorm hdn hfden0 hgden0 hfbB hdvdB hfbC hdvdC hred
  rw [hynum]
  exact hlift

/-- **★ The §6 cleared Risch-DE identity from bare success and the isolated residual — primitive
cancellation regime** (`rdeCleared_of_success_and_residual_cancelPrim`): the cancellation analogue of
`rdeCleared_of_success_and_residual`. Given `cRischDEG Dt fuel fnum fden gnum gden = some (ynum, yden)`,
`cdegG Dt = 0`, the same residual `RischDEStructuralResidual`, and the §6.5/§6.6 **cancellation** dispatch
condition (the SPDE output `bbar` has degree `0` and is nonzero — routing to `cPolyRischDECancelPrimG`), the
returned `y = ynum/yden` satisfies the cleared identity `gden·fden·(D(ynum)·yden − ynum·D(yden)) +
gden·fnum·ynum·yden = gnum·fden·yden²` over `(CFieldSpec.K α)[X]`. The §6.5/§6.6 poly step is discharged by
`cPolyRischDEG_cancelPrim_sound` (base-oracle-free) and fed to `rdeClearedIdentity_of_polyRDEIdentity` —
**the SAME residual as the non-cancellation path, no cancellation-specific addition**. With
`rdeCleared_of_success_and_residual`, the `cRischDEG`-level cleared identity now covers both the
non-cancellation and the primitive-cancellation dispatch arms (modulo the shared gcd-`Associated`
residual). -/
theorem rdeCleared_of_success_and_residual_cancelPrim (Dt : CPolyG α) (fuel : ℕ)
    (fnum fden gnum gden ynum yden : CPolyG α) (hδ : cdegG Dt = 0)
    (hsucc : cRischDEG Dt fuel fnum fden gnum gden = some (ynum, yden))
    (hres : ∀ a0 b0 c0 h0 : CPolyG α,
      cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0) →
      RischDEStructuralResidual Dt fuel fnum fden gnum gden a0 b0 c0 h0)
    (hdb0 : ∀ a0 b0 c0 bbar cbar : CPolyG α, ∀ m : ℤ, ∀ α' β : CPolyG α,
      cSPDEG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
          (cRdeBoundDegreeG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α', β) → cdegG bbar = 0 ∧ cisZeroG bbar = false) :
    toPolyG gden * toPolyG fden
        * (Differential.implicitDeriv (toPolyG Dt) (toPolyG ynum) * toPolyG yden
            - toPolyG ynum * Differential.implicitDeriv (toPolyG Dt) (toPolyG yden))
        + toPolyG gden * toPolyG fnum * toPolyG ynum * toPolyG yden
      = toPolyG gnum * toPolyG fden * toPolyG yden ^ 2 := by
  -- the three stage `some`-results from bare success (control-flow decomposition, regime-agnostic)
  obtain ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, hdisp, hynum, hyden⟩ :=
    cRischDEG_some_imp_stages Dt fuel fnum fden gnum gden ynum yden hsucc
  have hres' := hres a0 b0 c0 h0 hnorm
  obtain ⟨hdbarz, hbarne⟩ := hdb0 a0 b0 c0 bbar cbar m α' β hspde
  -- the dispatcher took the primitive-cancellation arm; its poly-RDE soundness gives `D(v)+bbar·v = cbar`
  have hpoly : toPolyG (cmonomialDeriv Dt v) + toPolyG bbar * toPolyG v = toPolyG cbar :=
    cPolyRischDEG_cancelPrim_sound Dt bbar cbar v fuel m hδ hdbarz hbarne hdisp
  have hidentity : Differential.implicitDeriv (toPolyG Dt) (toPolyG v) + toPolyG bbar * toPolyG v
      = toPolyG cbar := by rw [← toPolyG_cmonomialDeriv]; exact hpoly
  -- feed the identity to the regime-agnostic cleared spine; `h1 = [1]` in the primitive regime
  have hcap := rdeClearedIdentity_of_polyRDEIdentity Dt fuel fnum fden gnum gden a0 b0 c0 h0
    bbar cbar m α' β v hres'.hprim hnorm hres'.hdn hres'.hfden0 hres'.hgden0 hres'.hfbB hres'.hdvdB
    hres'.hfbC hres'.hdvdC hspde hres'.hin hidentity
  have hh1 : (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.2 = ([CField.one] : CPolyG α) := by
    rw [cRdeSpecialDenominatorG_primitive_eq_gen Dt fuel a0 b0 c0 hres'.hprim]
  rw [hh1] at hynum
  rw [hynum, hyden]
  exact hcap

/-! ### ★ The hyperexponential special regime — the cleared identity from the isolated §6.2 obligation

The primitive paths above (`rdeClearedIdentity_of_polyRDEIdentity`, `rdeCleared_of_success_and_residual*`)
all `rw` `cRdeSpecialDenominatorG_primitive_eq_gen`, which needs `hprim : cdegG (cSpecialPolyG Dt fuel) = 0`
— the §6.2 special-denominator stage is the **identity** there (`h₁ = [1]`, SPDE runs on `(a₀,b₀,c₀)`,
reconstruction `ynum = Q·[1]`). In the **hyperexponential** regime (`cdegG Dt = 1`, special polynomial
`p = cSpecialPolyG Dt fuel = t`, `cdegG p = 1`), `hprim` is FALSE: the §6.2 special-denominator reduction
is **non-trivial** (`h₁ = p^{−n} = pᵏ` with `k = −n ≥ 0`), SPDE runs on the special-cleared
`(ā,b̄,c̄) = (a₀·pᴺ, (b₀ + n·a₀·Dp/p)·pᴺ, c₀·p^{N−n})`, and the reconstruction is `ynum = Q·pᵏ`.

The genuine §6.2 content (Bronstein Lemma 6.2.1/6.2.2) is the **substitution correctness**: that `R = Q·pᵏ`
solves the *original* `a₀·D(R) + b₀·R = c₀`. By `specialDenominatorSubst_expand` the Leibniz expansion is
`a₀·D(Q·pᵏ) + b₀·(Q·pᵏ) = (a₀·D(Q) + b₀·Q + k·a₀·E·Q)·pᵏ` (`E = Dp/p = η ∈ k` for hyperexp), so the
substitution lands on `a₀·D(R) + b₀·R = c₀` **iff** the reduced obligation
`a₀·D(Q) + b₀·Q + k·a₀·E·Q = c₀/pᵏ` holds — and **that** is exactly the `ν_p`-exponent bookkeeping
(`n_b = ν_p(b₀)`, `n_c = ν_p(c₀)`, the `N`-shift) whose carrier-level correctness (`cValuationG`
correctness, the special-part self-derivative divisibility `p ∣ Dp`) is **not yet proven** — the sole
remaining §6.2 obstruction. We therefore isolate that obligation as the single explicit hypothesis
`hspecialReduced : a₀·D(R) + b₀·R = c₀` (`R = ynum = Q·h₁`, in the exact form
`cRdeNormalDenominatorG_cleared_lift_gen` consumes) and discharge **everything else** through the shared
normal-denominator spine. The cancellation poly-RDE soundness `cPolyRischDEG_cancelExp_field` (already
proven, base-oracle-free) is what supplies the bar-equation in the CancelExp arm; it is *not* what is
missing — the missing piece is purely the §6.2 special-denominator substitution correctness above. -/

omit [CRischField α] in
/-- **★ The §6 special-regime cleared Risch-DE identity from the isolated §6.2 substitution obligation**:
the non-primitive (hyperexponential `cdegG Dt = 1`, hypertangent `cdegG Dt = 2`) analogue of the primitive
`rdeClearedIdentity_of_polyRDEIdentity`, stated with the general special-denominator reconstruction
`ynum = (α'·v+β)·h₁` (`h₁ = pᵏ`, NOT collapsed to `[1]` as in the primitive case). It takes the §6.2
special-denominator substitution correctness `a₀·D(ynum) + b₀·ynum = c₀` — the exact fact the unproven
`cValuationG`-correctness would discharge (by `specialDenominatorSubst_expand`, equivalent to the
`ν_p`-exponent reduced obligation `a₀·D(Q) + b₀·Q + k·a₀·E·Q = c₀/pᵏ`) — as the single explicit hypothesis
`hspecialReduced`, and lifts it through the shared normal-denominator spine
`cRdeNormalDenominatorG_cleared_lift_gen` to the full cleared identity
`gden·fden·(D(ynum)·yden − ynum·D(yden)) + gden·fnum·ynum·yden = gnum·fden·yden²`, `yden = h₀`, over
`(CFieldSpec.K α)[X]`. Reuses the primitive path's normal-denominator certificates verbatim; the ONLY
non-primitive-specific input is `hspecialReduced`. -/
theorem cRischDEG_rdeCleared_gen_hyperexp (Dt : CPolyG α) (fuel : ℕ)
    (fnum fden gnum gden a0 b0 c0 h0 : CPolyG α) (α' β v : CPolyG α)
    (hnorm : cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0))
    (hdn : toPolyG (cSplitFactorFastG Dt fuel fden).1 ≠ 0)
    (hfden0 : cnormG fden ≠ []) (hgden0 : cnormG gden ≠ [])
    (hfbB : (cnormG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h0)) fden)) :
        List α).length ≤ fuel)
    (hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h0)) fden)))
    (hfbC : (cnormG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) h0) gnum) :
        List α).length ≤ fuel)
    (hdvdC : toPolyG gden ∣ toPolyG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) h0) gnum))
    (hspecialReduced :
      toPolyG a0
          * Differential.implicitDeriv (toPolyG Dt)
              (toPolyG (cmulG (caddG (cmulG α' v) β) (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.2))
        + toPolyG b0
          * toPolyG (cmulG (caddG (cmulG α' v) β) (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.2)
      = toPolyG c0) :
    let ynum := cmulG (caddG (cmulG α' v) β) (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.2
    let yden := h0
    toPolyG gden * toPolyG fden
        * (Differential.implicitDeriv (toPolyG Dt) (toPolyG ynum) * toPolyG yden
            - toPolyG ynum * Differential.implicitDeriv (toPolyG Dt) (toPolyG yden))
        + toPolyG gden * toPolyG fnum * toPolyG ynum * toPolyG yden
      = toPolyG gnum * toPolyG fden * toPolyG yden ^ 2 := by
  intro ynum yden
  -- the reconstruction `R = ynum = Q·h₁` solves the reduced normal-denominator equation (the isolated
  -- §6.2 obligation), so the shared normal-denominator spine lifts it to the cleared identity
  exact cRdeNormalDenominatorG_cleared_lift_gen Dt fuel fnum fden gnum gden a0 b0 c0 h0 ynum
    hnorm hdn hfden0 hgden0 hfbB hdvdB hfbC hdvdC hspecialReduced

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- ★ The structural-decomposition core: a bare `cRischDEG` success factors through the §6.2/§6.4/§6.5
-- stage successes with the matching output reassembly.
example (Dt : CPolyG α) (fuel : ℕ) (fnum fden gnum gden ynum yden : CPolyG α)
    (hsucc : cRischDEG Dt fuel fnum fden gnum gden = some (ynum, yden)) :
    ∃ (a0 b0 c0 h0 bbar cbar : CPolyG α) (m : ℤ) (v : CPolyG α),
      cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0)
      ∧ cPolyRischDEG Dt fuel bbar cbar m = some v
      ∧ yden = h0 := by
  obtain ⟨a0, b0, c0, h0, bbar, cbar, m, _, _, v, hnorm, _, hdisp, _, hyden⟩ :=
    cRischDEG_some_imp_stages Dt fuel fnum fden gnum gden ynum yden hsucc
  exact ⟨a0, b0, c0, h0, bbar, cbar, m, v, hnorm, hdisp, hyden⟩

-- ★ The cancellation regime reaches the SAME `cRischDEG`-level cleared identity as the non-cancellation
-- path, modulo the SAME `RischDEStructuralResidual` — the §6.5/§6.6 dispatch condition is the only change
-- (`cdegG bbar = 0` ∧ `bbar ≠ 0`, routing to the primitive cancellation solve).
example (Dt : CPolyG α) (fuel : ℕ) (fnum fden gnum gden ynum yden : CPolyG α) (hδ : cdegG Dt = 0)
    (hsucc : cRischDEG Dt fuel fnum fden gnum gden = some (ynum, yden))
    (hres : ∀ a0 b0 c0 h0 : CPolyG α,
      cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0) →
      RischDEStructuralResidual Dt fuel fnum fden gnum gden a0 b0 c0 h0)
    (hdb0 : ∀ a0 b0 c0 bbar cbar : CPolyG α, ∀ m : ℤ, ∀ α' β : CPolyG α,
      cSPDEG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
          (cRdeBoundDegreeG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α', β) → cdegG bbar = 0 ∧ cisZeroG bbar = false) :
    toPolyG gden * toPolyG fden
        * (Differential.implicitDeriv (toPolyG Dt) (toPolyG ynum) * toPolyG yden
            - toPolyG ynum * Differential.implicitDeriv (toPolyG Dt) (toPolyG yden))
        + toPolyG gden * toPolyG fnum * toPolyG ynum * toPolyG yden
      = toPolyG gnum * toPolyG fden * toPolyG yden ^ 2 :=
  rdeCleared_of_success_and_residual_cancelPrim Dt fuel fnum fden gnum gden ynum yden hδ hsucc hres hdb0

-- ★ The non-primitive (hyperexp/hypertangent) special-regime cleared identity: the general
-- reconstruction `ynum = (α'·v+β)·h₁` (`h₁ = pᵏ`) reaches the SAME `cRischDEG`-level cleared identity as
-- the primitive path, reducing the ENTIRE non-primitive case to the single isolated §6.2 substitution
-- obligation `a₀·D(ynum) + b₀·ynum = c₀` — exactly the `ν_p`-bookkeeping the unproven `cValuationG`
-- correctness supplies. Everything else is the shared normal-denominator spine.
example (Dt : CPolyG α) (fuel : ℕ) (fnum fden gnum gden a0 b0 c0 h0 : CPolyG α) (α' β v : CPolyG α)
    (hnorm : cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0))
    (hdn : toPolyG (cSplitFactorFastG Dt fuel fden).1 ≠ 0)
    (hfden0 : cnormG fden ≠ []) (hgden0 : cnormG gden ≠ [])
    (hfbB : (cnormG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h0)) fden)) :
        List α).length ≤ fuel)
    (hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h0)) fden)))
    (hfbC : (cnormG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) h0) gnum) :
        List α).length ≤ fuel)
    (hdvdC : toPolyG gden ∣ toPolyG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h0) h0) gnum))
    (hspecialReduced :
      toPolyG a0
          * Differential.implicitDeriv (toPolyG Dt)
              (toPolyG (cmulG (caddG (cmulG α' v) β) (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.2))
        + toPolyG b0
          * toPolyG (cmulG (caddG (cmulG α' v) β) (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.2)
      = toPolyG c0) :
    let ynum := cmulG (caddG (cmulG α' v) β) (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.2
    let yden := h0
    toPolyG gden * toPolyG fden
        * (Differential.implicitDeriv (toPolyG Dt) (toPolyG ynum) * toPolyG yden
            - toPolyG ynum * Differential.implicitDeriv (toPolyG Dt) (toPolyG yden))
        + toPolyG gden * toPolyG fnum * toPolyG ynum * toPolyG yden
      = toPolyG gnum * toPolyG fden * toPolyG yden ^ 2 :=
  cRischDEG_rdeCleared_gen_hyperexp Dt fuel fnum fden gnum gden a0 b0 c0 h0 α' β v
    hnorm hdn hfden0 hgden0 hfbB hdvdB hfbC hdvdC hspecialReduced

end Residual

/-! ### Axiom audit (the structural decomposition rests only on the standard kernel axioms) -/

#print axioms cRischDEG_some_imp_stages
#print axioms cPolyRischDEG_eq_noCancel_of_primitive
#print axioms rdeCleared_of_success_and_residual
#print axioms rdeClearedIdentity_of_polyRDEIdentity
#print axioms rdeCleared_of_success_and_residual_cancelPrim
#print axioms cRischDEG_rdeCleared_gen_hyperexp

end DeepWiki.SymbolicIntegration
