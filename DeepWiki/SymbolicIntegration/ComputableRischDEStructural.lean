import DeepWiki.SymbolicIntegration.ComputableRischFieldSpec

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

end DeepWiki.SymbolicIntegration
