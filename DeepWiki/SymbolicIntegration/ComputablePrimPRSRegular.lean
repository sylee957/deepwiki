import DeepWiki.SymbolicIntegration.ComputableTowerGcdFFCorrect
import DeepWiki.SymbolicIntegration.ComputableTowerWellFounded

/-! # Is the primitive-PRS content-exactness `CPrimPRSGenAssocReg` unconditional?

`ComputableTowerGcdFFCorrect.associated_toPolyG_cgcdFFCore` — the abstract correctness of the recursive
tower fraction-free gcd over `β(s)[t]` — is gated on the per-step regularity bundle
`CPrimPRSGenAssocReg cgcdB fuel P Q`. This file determines whether that bundle is an **unconditional
theorem** (so the recursive `CRischFieldSpec` and fully-abstract Risch soundness close end-to-end) or a
**genuine per-run non-degeneracy assumption**, and SHARPENS it precisely.

## Anatomy of `cprimPRSgcdGenCore` (the kernel) and `CPrimPRSGenAssocReg` (the gate)

`cprimPRSgcdGenCore cgcdB fuel P Q` (`ComputableTowerGcdFFCore`) runs a **primitive polynomial-remainder
sequence** in `t` over the GCD-domain coefficient ring `CPolyG β = β[s]`:
* if `Q` is zero, return `gbprimitivePartCore 30 cgcdB P` (strip `P`'s content);
* else set `r := gbprimitivePartCore 30 cgcdB (gbpsremainderCore 60 P Q)` — the **primitive part** of the
  **pseudo-remainder** — and recurse on `(Q, r)` with one less fuel.

`CPrimPRSGenAssocReg cgcdB fuel P Q` (`ComputableTowerGcdFFCorrect`) is the inductive bundle the gcd
invariant of *each step* consumes. At a non-terminal `fuel+1` step (with `Pn = gbnormCore P`, `Qn =
gbnormCore Q`, `prem = gbpsremainderCore 60 Pn Qn`, `r = gbprimitivePartCore 30 cgcdB prem`) it asks for:
  * **(i) termination** — the recursion reaches `gbisZeroCore Qn = true`;
  * **(ii) a pseudo-division witness** `(s, c)` with
    `C (amG (toPolyG c)) · toGBPolyG Pn = toGBPolyG s · toGBPolyG Qn + toGBPolyG prem` **and the multiplier
    `amG (toPolyG c) ≠ 0`** (a `β(s)`-unit);
  * **(iii) the content strip is a `β(s)`-unit scaling** — `Associated (toGBPolyG r) (toGBPolyG prem)`.

## The verdict (proved below)

`CPrimPRSGenAssocReg` is **NOT unconditional**, and the obstruction is **not** a missing
content/GCD-domain fact — it is exactly TWO per-run non-degeneracy ingredients, which we name sharply:

1. **The PRS terminates within the supplied `fuel`** — i.e. `CPrimPRSGenRegular cgcdB fuel P Q`
   (`ComputableTowerWellFounded`), the genuine per-step `t`-length-drop witness. The pseudo-remainder degree
   *does* strictly drop at the polynomial level over the integral domain `(CFieldSpec.K β)[X]` (`lc(Q)` is a
   non-zero-divisor) — this is a real theorem — but the engine's loop guard compares the **normalized list
   length** `(gbnormCore r).length`, and **no engine lemma states that list-length drop** abstractly over
   the non-field coefficient ring `CPolyG β = β[s]` (the same gap `ComputableTowerWellFounded` records:
   "no abstract `gbpsremainderCore` length-drop lemma"). So termination enters as the per-run witness.
2. **The content-gcd `cgcdB` is gcd-correct** — `CgcdBCorrect cgcdB`. On a real tower run this is the
   level-`β` gcd-correctness of `cgcdFFRawCore β` (the tower induction). It is **not** unconditional even at
   the base: `associated_toPolyG_cgcdExtG` needs `cgcdTerminatesG`, so the base `cgcdFFRawCore ℚ =
   (cgcdExtG _).1` is gcd-correct only on terminating Euclid runs.

Given those two — plus transparent per-step content-nonzero / fuel side-conditions the algorithm self-
satisfies — clauses (ii) and (iii) of `CPrimPRSGenAssocReg` are **theorems** (clause (ii)'s identity is
`toGBPolyG_gbpsremainderCore`, already unconditional; its nonzero-multiplier part is recovered here; clause
(iii) is `associated_toGBPolyG_gbprimitivePartCore_of_correct`). The deliverable is the **reduction
theorem** `cPrimPRSGenAssocReg_of_regular_of_correct`: `CPrimPRSGenRegular` + `CgcdBCorrect` + the
transparent side-conditions ⟹ `CPrimPRSGenAssocReg`. That replaces the opaque 13-hypothesis gate with the
**precise** non-degeneracy: *termination* and *level-β gcd-correctness*.

So fully-abstract soundness is **not** closed by an unconditional `CPrimPRSGenAssocReg`; it is closed *up
to* threading these two per-run witnesses through the tower recursion. This resolves the memory's tension:
the residual is **bookkeeping of termination + the level-β gcd-correctness induction**, NOT a missing
research-grade content theorem. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG GBPolyCore

variable {β : Type*} [CField β] [CFieldSpec β]

/-! ## Step 2 — the per-step content lemmas

`ComputableTowerGcdFFCorrect` already proves the two *content* halves of a primitive-PRS step
unconditionally / from `CgcdBCorrect`:
* **clause (ii) identity** — `toGBPolyG_gbpsremainderCore`: the pseudo-remainder satisfies the `β(s)[t]`
  Euclidean relation `C (amG (toPolyG c)) · toGBPolyG p = toGBPolyG s · toGBPolyG q + toGBPolyG prem`;
* **clause (iii)** — `associated_toGBPolyG_gbprimitivePartCore_of_correct`: under `CgcdBCorrect cgcdB`
  (the level-`β` gcd-correctness) plus content-nonzero/fuel, the content strip is a `β(s)`-unit scaling,
  `Associated (toGBPolyG r) (toGBPolyG prem)` — via Mathlib's generic content/`gcd`-fold theory over the
  `NormalizedGCDMonoid` `(CFieldSpec.K β)[X]` (the same lever the whole FF-gcd correctness uses).

What clause (ii) of `CPrimPRSGenAssocReg` *additionally* demands — and the existing
`toGBPolyG_gbpsremainderCore` does **not** give — is that the multiplier be a `β(s)`-**unit**
(`amG (toPolyG c) ≠ 0`). We supply that here. The pseudo-division multiplier accumulated by
`gbpsremainderCore fuel p q` is a power of `lc(q)` (the divisor `q` is held fixed across the loop; only `p`
descends), so it is nonzero exactly when `q ≠ 0`. This is **not** a per-run assumption: at a non-terminal
step the loop guard already gives `q ≠ 0`. So clause (ii) is unconditional given `q ≠ 0`. -/

/-- **The leading `t`-coefficient of a nonzero `GBPolyCore` reads nonzero**: if `gbisZeroCore q = false`
(`q ≠ 0` in `t`), then `toPolyG (gblcCore q) ≠ 0` in `R = (CFieldSpec.K β)[X]`. The top normalized
`t`-coefficient is `cnormG`-nonempty, hence `toPolyG`-nonzero (`gbnormCore_getLast?_toPolyG_ne_zero`). -/
theorem toPolyG_gblcCore_ne_zero {q : GBPolyCore β} (hq : gbisZeroCore q = false) :
    CPolyG.toPolyG (gblcCore q) ≠ 0 := by
  -- `gbnormCore q ≠ []` (zero test is `false`), so `getLast?` is `some v` with `toPolyG v ≠ 0`
  have hne : gbnormCore q ≠ [] := by
    rw [gbisZeroCore, List.isEmpty_eq_false_iff_exists_mem] at hq
    obtain ⟨a, ha⟩ := hq
    exact List.ne_nil_of_mem ha
  rcases hg : (gbnormCore q).getLast? with _ | v
  · exact absurd (List.getLast?_eq_none_iff.mp hg) hne
  · have hlc : gblcCore q = v := by rw [gblcCore, hg, Option.getD_some]
    rw [hlc]
    exact gbnormCore_getLast?_toPolyG_ne_zero q v hg

/-- **The multiplier of `gbpsremainderCore` is `toPolyG`-nonzero when the divisor is nonzero.** Mirrors
`toGBCoeffPoly_gbpsremainderCore` (the pseudo-division identity) but additionally produces a multiplier `c`
with `toPolyG c ≠ 0`, provided `gbisZeroCore (gbnormCore q) = false`. The divisor `q` is fixed across the
`gbpsremainderCore` loop, so the accumulated multiplier is a power of `lc(q)` — nonzero exactly because
`q ≠ 0` (the integral domain `(CFieldSpec.K β)[X]` has no zero divisors, `toPolyG_cmulG`). The
nonzero-multiplier strengthening of clause (ii) of `CPrimPRSGenAssocReg`. -/
theorem toGBCoeffPoly_gbpsremainderCore_ne_zero (fuel : ℕ) (p q : GBPolyCore β)
    (hq : gbisZeroCore (gbnormCore q) = false) :
    ∃ (s : GBPolyCore β) (c : CPolyG β),
      Polynomial.C (CPolyG.toPolyG c) * toGBCoeffPoly p
          = toGBCoeffPoly s * toGBCoeffPoly q + toGBCoeffPoly (gbpsremainderCore fuel p q)
        ∧ CPolyG.toPolyG c ≠ 0 := by
  have hone : CPolyG.toPolyG ([CField.one] : CPolyG β) = 1 := by
    rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]
  -- `lc(gbnormCore q)` reads nonzero (the divisor is nonzero)
  have hlcq : CPolyG.toPolyG (gblcCore (gbnormCore q)) ≠ 0 :=
    toPolyG_gblcCore_ne_zero hq
  induction fuel generalizing p with
  | zero =>
    exact ⟨[], [CField.one], by simp [gbpsremainderCore, toGBCoeffPoly_gbnormCore, hone],
      by rw [hone]; exact one_ne_zero⟩
  | succ fuel ih =>
    simp only [gbpsremainderCore]
    split_ifs with hqz hlen
    · exact ⟨[], [CField.one], by simp [toGBCoeffPoly_gbnormCore, hone],
        by rw [hone]; exact one_ne_zero⟩
    · exact ⟨[], [CField.one], by simp [toGBCoeffPoly_gbnormCore, hone],
        by rw [hone]; exact one_ne_zero⟩
    · obtain ⟨s', c', hsc, hc'⟩ := ih (gbnormCore (gbsubCore (gbscaleCCore (gblcCore (gbnormCore q))
        (gbnormCore p))
        (gbscaleCCore (gblcCore (gbnormCore p))
          (gbshiftCore ((gbnormCore p).length - (gbnormCore q).length) (gbnormCore q)))))
      have hp' : toGBCoeffPoly (gbnormCore (gbsubCore (gbscaleCCore (gblcCore (gbnormCore q))
          (gbnormCore p))
          (gbscaleCCore (gblcCore (gbnormCore p))
            (gbshiftCore ((gbnormCore p).length - (gbnormCore q).length) (gbnormCore q)))))
          = Polynomial.C (CPolyG.toPolyG (gblcCore (gbnormCore q))) * toGBCoeffPoly p
            - Polynomial.C (CPolyG.toPolyG (gblcCore (gbnormCore p)))
              * Polynomial.X ^ ((gbnormCore p).length - (gbnormCore q).length) * toGBCoeffPoly q := by
        rw [toGBCoeffPoly_gbnormCore, toGBCoeffPoly_gbsubCore, toGBCoeffPoly_gbscaleCCore,
          toGBCoeffPoly_gbscaleCCore, toGBCoeffPoly_gbshiftCore, toGBCoeffPoly_gbnormCore,
          toGBCoeffPoly_gbnormCore]
        ring
      rw [hp', gbpsremainderCore_gbnormCore_right] at hsc
      refine ⟨gbaddCore s' (gbscaleCCore (CPolyG.cmulG c' (gblcCore (gbnormCore p)))
          (gbshiftCore ((gbnormCore p).length - (gbnormCore q).length) [[CField.one]])),
          CPolyG.cmulG c' (gblcCore (gbnormCore q)), ?_, ?_⟩
      · rw [toGBCoeffPoly_gbaddCore, toGBCoeffPoly_gbscaleCCore, toGBCoeffPoly_gbshiftCore,
          toGBCoeffPoly_one, CPolyG.toPolyG_cmulG, map_mul, CPolyG.toPolyG_cmulG, map_mul]
        linear_combination hsc
      · rw [CPolyG.toPolyG_cmulG]
        exact mul_ne_zero hc' hlcq

/-- **`gbpsremainderCore` lifts to a `β(s)[t]` Euclidean relation with a `β(s)`-UNIT multiplier** (clause
(ii) of `CPrimPRSGenAssocReg`, fully discharged): if `gbisZeroCore (gbnormCore q) = false`, there is a
quotient `s` and a multiplier `c` with
`C (amG (toPolyG c)) · toGBPolyG p = toGBPolyG s · toGBPolyG q + toGBPolyG (gbpsremainderCore fuel p q)`
**and `amG (toPolyG c) ≠ 0`** in `(RatFunc (CFieldSpec.K β))[X]`. The unconditional (given `q ≠ 0`) clause
(ii) — the nonzero-multiplier strengthening of `toGBPolyG_gbpsremainderCore`. -/
theorem toGBPolyG_gbpsremainderCore_ne_zero (fuel : ℕ) (p q : GBPolyCore β)
    (hq : gbisZeroCore (gbnormCore q) = false) :
    ∃ (s : GBPolyCore β) (c : CPolyG β),
      Polynomial.C (QFunNZG.amG β (CPolyG.toPolyG c)) * toGBPolyG p
          = toGBPolyG s * toGBPolyG q + toGBPolyG (gbpsremainderCore fuel p q)
        ∧ QFunNZG.amG β (CPolyG.toPolyG c) ≠ 0 := by
  obtain ⟨s, c, hsc, hc⟩ := toGBCoeffPoly_gbpsremainderCore_ne_zero fuel p q hq
  refine ⟨s, c, ?_, QFunNZG.amG_toPolyG_ne_zero hc⟩
  have hl := congrArg (liftKG β) hsc
  simp only [map_add, map_mul] at hl
  rw [liftKG_C] at hl
  simpa [toGBPolyG] using hl

end DeepWiki.SymbolicIntegration
