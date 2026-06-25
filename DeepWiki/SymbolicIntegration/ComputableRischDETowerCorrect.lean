import DeepWiki.SymbolicIntegration.ComputableIntegrateTowerCorrect
import DeepWiki.SymbolicIntegration.ComputableRischDEPipelineCorrect
import DeepWiki.SymbolicIntegration.ComputableTowerRischDE

/-! # Abstract correctness of the GENERIC tower Risch-DE oracle `cRischDEG` at the level-1 carrier ℚ(x)
The generic tower §6 oracle `cRischDEG` (`ComputableTowerRischDE`) assembles the Risch differential
equation pipeline `Dy + f·y = g` on the `[CField α] [CDiffField α] [CFracGcdCore α] [CRischField α]`-generic
ops — §6.2 normal/special denominators (`cRdeNormalDenominatorG`/`cRdeSpecialDenominatorG`), the §6.3
degree bound (`cRdeBoundDegreeG`), the §6.4 SPDE (`cSPDEG`), and the §6.5/§6.6 PolyRischDE dispatch
(`cPolyRischDEG`) — recursing into the base solve `CRischField.crischDESolve`. It is `native_decide`-validated
only (the level-2 `towerRdeLvl2_solves_*` headlines).

This file gives the generic RDE oracle the abstract cleared-identity `Dy + f·y = g` it lacked — at the
level-1 carrier `α = QFunNZ` the engine collapse instantiates, where `cgcdFFCore` reads through `toPolyG`
to the SAME gcd as `cgcdFF` up to associates (the nucleus `ComputableSplitFactorTowerCorrect` filled the
§3.5 piece; the §5 transport `ComputableIntegrateTowerCorrect` is the template).

**The route (mirroring the §5 transport).** The generic stages at `α = QFunNZ` differ from the QFunNZ
`cRischDE` stages only in the gcd (`cgcdFFCore` vs `cgcdFF`, inside the §6.2 denominator/§6.4 SPDE steps)
and `cdivG` vs `cdivFF` (definitionally equal, `cdivFF := cdivG`). The §6 cleared-identity machinery is
mostly **gcd-free**:

* The **§6.5 non-cancellation** loop (`cPolyRischDENoCancelG`) has the **identical body** to
  `cPolyRischDENoCancel` (no gcd: only `cdegG`/`cleadG`/`cmonomialDeriv`/`cshiftG`/`csub/mul/addG`), so its
  cleared identity transports **verbatim** (`cPolyRischDENoCancelG_cleared_identity`).
* The **§6.4 SPDE** (`cSPDEG`) differs from `cSPDE` only at `let g := cgcdFFCore …`; its lifting
  (`cSPDEG_cleared_lifting`) is the same `gcd`-peel induction gated on a per-level certificate
  `cSPDEGCleared`, and the certificate discharge `cSPDEGCleared_of_inputs` is where the gcd actually
  enters — bridged through the §5 nucleus `associated_toPolyG_cgcdFFCore_node` (the certificate's
  `Associated (toPolyG g) (gcd …)` clause), exactly as the §5 split-factor transport.
* The **§6.2 normal denominator** glue (`rdeNormalDenominator_glue`) is a commutative-ring `Derivation`
  identity — already engine-agnostic and **reused directly** from `ComputableRischDEPipelineCorrect`.

The deliverable:

* **`cPolyRischDENoCancelG_cleared_identity`** — the §6.5 non-cancellation cleared identity for the generic
  loop (verbatim transport).
* **`cSPDEGCleared` / `cSPDEG_cleared_lifting` / `CSPDEGClearedInputs` / `cSPDEGCleared_of_inputs`** — the
  §6.4 SPDE generic certificate, lifting, transparent inputs, and discharge (the `cgcdFF ⤳ cgcdFFCore`
  bridge enters only in the discharge).
* **`cSPDEG_polyRischDENoCancel_cleared_of_inputs`** — the §6.4+§6.5 polynomial-stage spine.
* **`cRdeNormalDenominatorG_cleared_lift`** — the §6.2 normal-denominator cleared lifting (generic).
* **`cRdeSpecialDenominatorG_primitive_eq`** — the §6.2 special denominator is the identity in the
  primitive regime.
* **★ `cRischDEG_rdeCleared`** — the generic RDE oracle's cleared identity `Dy + f·y = g`: in the primitive
  regime, `cRischDEG` returns a `(ynum, yden)` whose `y = ynum/yden` solves the cleared Risch-DE
  `gden·fden·(D(ynum)·yden − ynum·D(yden)) + gden·fnum·ynum·yden = gnum·fden·yden²` over `(RatFunc ℚ)[X]`. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### §6.5 — the generic non-cancellation cleared identity `D(q) + b·q = c` (verbatim transport)

`cPolyRischDENoCancelG Dt fuel b c n` (`ComputableTowerRischDE`) has the **identical body** to
`cPolyRischDENoCancel` (`ComputableRischDE`): both peel `p = (lc(c)/lc(b))·tᵐ`, recurse on
`c' = c − D(p) − b·p`, glue `q ← p + (recursive q)` — no gcd anywhere (only
`cdegG`/`cleadG`/`cmonomialDeriv`/`cshiftG`/`csub/mul/addG`). So the QFunNZ proof
`cPolyRischDENoCancel_cleared_identity` transports **verbatim** (the only change is the function name). -/

/-- **`cPolyRischDENoCancelG` satisfies the cleared RDE identity `D(q) + b·q = c`** (abstract, ALL inputs)
over the field ℚ(x), whenever the generic non-cancellation solve **succeeds**. If
`cPolyRischDENoCancelG Dt fuel b c n = some q` then, with `D = cmonomialDeriv Dt` (`= implicitDeriv
(toPolyG Dt)` through `toPolyG`), `implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG b * toPolyG q =
toPolyG c` in `(RatFunc ℚ)[X]`. The generic mirror of `cPolyRischDENoCancel_cleared_identity`, transported
verbatim (the loop body is identical — `cPolyRischDENoCancelG` has no gcd). Proved by induction on `fuel`:
each pass peels `p = (lc(c)/lc(b))·tᵐ`, recurses on `c' = c − D(p) − b·p`, and the additivity of
`implicitDeriv` glues `D(p+q) + b·(p+q) = D(p) + b·p + (D(q) + b·q) = D(p) + b·p + c' = c`. -/
theorem cPolyRischDENoCancelG_cleared_identity (Dt b : CPolyG QFunNZ) :
    ∀ (fuel : ℕ) (c : CPolyG QFunNZ) (n : ℤ) (q : CPolyG QFunNZ),
      cPolyRischDENoCancelG Dt fuel b c n = some q →
        Differential.implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG b * toPolyG q = toPolyG c := by
  intro fuel
  induction fuel with
  | zero =>
    intro c n q hq
    -- `cPolyRischDENoCancelG Dt 0 _ _ _ = none`, contradiction
    rw [cPolyRischDENoCancelG] at hq
    exact absurd hq (by simp)
  | succ fuel ih =>
    intro c n q hq
    rw [cPolyRischDENoCancelG] at hq
    by_cases hc : cisZeroG c = true
    · -- base case: `c = 0`, returns `[]`, so `D(0) + b·0 = 0 = c`
      rw [if_pos hc, Option.some.injEq] at hq
      subst hq
      have hc0 : toPolyG c = 0 := (cisZeroG_iff c).mp hc
      rw [toPolyG_nil, map_zero, mul_zero, add_zero, hc0]
    · -- recursion branch
      rw [if_neg hc] at hq
      set m : ℤ := (cdegG c : ℤ) - (cdegG b : ℤ) with hm
      by_cases hguard : n < 0 ∨ m < 0 ∨ m > n
      · rw [if_pos hguard] at hq
        exact absurd hq (by simp)
      · rw [if_neg hguard] at hq
        simp only at hq
        set coeff := CField.div (cleadG c) (cleadG b) with hcoeff
        set p := cshiftG m.toNat [coeff] with hp
        set c' := csubG (csubG c (cmonomialDeriv Dt p)) (cmulG b p) with hc'
        -- destructure the recursive call
        rcases hrec : cPolyRischDENoCancelG Dt fuel b c' (m - 1) with _ | qrec
        · rw [hrec] at hq; exact absurd hq (by simp)
        · rw [hrec, Option.some.injEq] at hq
          -- the recursive identity on `c'`
          have ihrec := ih c' (m - 1) qrec hrec
          -- `q = p + qrec`
          subst hq
          rw [toPolyG_caddG, map_add, mul_add]
          -- expand `c' = c − D(p) − b·p` through `toPolyG`
          have hc'eq : toPolyG c' = toPolyG c
              - Differential.implicitDeriv (toPolyG Dt) (toPolyG p) - toPolyG b * toPolyG p := by
            rw [hc', toPolyG_csubG, toPolyG_csubG, toPolyG_cmonomialDeriv, toPolyG_cmulG]
          rw [hc'eq] at ihrec
          -- glue: `D(p) + D(qrec) + (b·p + b·qrec) = D(p) + b·p + (D(qrec) + b·qrec) = c`
          linear_combination ihrec

-- The §6.5 generic non-cancellation cleared identity, restated. When `cPolyRischDENoCancelG Dt fuel b c n
-- = some q`, the output `q` solves `D(q) + b·q = c` over ℚ(x)[t].
example (Dt b c : CPolyG QFunNZ) (fuel : ℕ) (n : ℤ) (q : CPolyG QFunNZ)
    (hq : cPolyRischDENoCancelG Dt fuel b c n = some q) :
    Differential.implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG b * toPolyG q = toPolyG c :=
  cPolyRischDENoCancelG_cleared_identity Dt b fuel c n q hq

#print axioms cPolyRischDENoCancelG_cleared_identity

end DeepWiki.SymbolicIntegration
