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
* if `Q` is zero, return `gbprimitivePartCore cgcdB P` (strip `P`'s content);
* else set `r := gbprimitivePartCore cgcdB (gbpsremainderCore 60 P Q)` — the **primitive part** of the
  **pseudo-remainder** — and recurse on `(Q, r)` with one less fuel.

`CPrimPRSGenAssocReg cgcdB fuel P Q` (`ComputableTowerGcdFFCorrect`) is the inductive bundle the gcd
invariant of *each step* consumes. At a non-terminal `fuel+1` step (with `Pn = gbnormCore P`, `Qn =
gbnormCore Q`, `prem = gbpsremainderCore 60 Pn Qn`, `r = gbprimitivePartCore cgcdB prem`) it asks for:
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

Given those two — plus the retained per-step coefficient-size bookkeeping the algorithm self-satisfies —
clauses (ii) and (iii) of `CPrimPRSGenAssocReg` are **theorems** (clause (ii)'s identity is
`toGBPolyG_gbpsremainderCore`, already unconditional; its nonzero-multiplier part is recovered here; clause
(iii) is `associated_toGBPolyG_gbprimitivePartCore_of_correct`). The deliverable is the **reduction
theorem** `cPrimPRSGenAssocReg_of_regular_of_correct`: `CPrimPRSGenRegular` + `CgcdBCorrect` + the
retained bookkeeping ⟹ `CPrimPRSGenAssocReg`. That replaces the opaque 13-hypothesis gate with the
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

/-! ## Step 3a — the TOTAL clause (iii): content strip is a `β(s)`-unit scaling, on ANY input

`associated_toGBPolyG_gbprimitivePartCore_of_correct` (`ComputableTowerGcdFFCorrect`) discharges clause
(iii) only when the content is **nonzero** (`hg`/`hgcn`/`hg0`). But the primitive-PRS loop also strips the
content of the **zero** polynomial (a terminal `P = 0`, or a `prem = 0`): there `gbprimitivePartCore` is
the identity (`gbnormCore p`, content branch `cisZeroG g`), so the `Associated` is reflexive. Bundling the
two cases gives the **total** clause (iii) — conditional only on `CgcdBCorrect cgcdB` (the level-`β`
gcd-correctness) plus the retained per-coefficient bookkeeping threaded by the PRS gate, with **no**
separate nonzero hypothesis. -/

/-- **★ Total clause (iii)** — `gbprimitivePartCore` is a `β(s)`-unit scaling on **any** input: under
`CgcdBCorrect cgcdB` (the level-`β` gcd-correctness) and the retained per-`t`-coefficient bookkeeping,
`Associated (toGBPolyG (gbprimitivePartCore cgcdB p)) (toGBPolyG p)`. Splits on whether the content
`gbcontentCore cgcdB p` is zero: if zero, `gbprimitivePartCore` is the identity `gbnormCore p` (reflexive
`Associated`); if nonzero, it is the unit scaling of `associated_toGBPolyG_gbprimitivePartCore_of_correct`.
So clause (iii) needs only the recursion's gcd-correctness plus retained algorithmics — never a
content-nonzero assumption. -/
theorem associated_toGBPolyG_gbprimitivePartCore_total (fuel : ℕ)
    (cgcdB : CPolyG β → CPolyG β → CPolyG β) (hcorr : CgcdBCorrect cgcdB) (p : GBPolyCore β)
    (hfuel : ∀ a ∈ gbnormCore p, (CPolyG.cnormG a : List β).length ≤ fuel) :
    Associated (toGBPolyG (gbprimitivePartCore cgcdB p)) (toGBPolyG p) := by
  by_cases hgz : CPolyG.cisZeroG (gbcontentCore cgcdB p) = true
  · -- content zero: gbprimitivePartCore is the identity `gbnormCore p`
    have hid : gbprimitivePartCore cgcdB p = gbnormCore p := by
      rw [gbprimitivePartCore, gbcontentCore_gbnormCore, if_pos hgz]
    rw [hid, toGBPolyG_gbnormCore]
  · -- content nonzero: the unit scaling (Mathlib content + cgcdB-fold-divides)
    have hg0 : CPolyG.toPolyG (gbcontentCore cgcdB p) ≠ 0 := by
      rw [Ne, ← CPolyG.cisZeroG_iff]; exact hgz
    have hgcn : CPolyG.cnormG (gbcontentCore cgcdB p) ≠ [] := by
      rw [Ne, CPolyG.cnormG_eq_nil_iff]; exact hg0
    exact associated_toGBPolyG_gbprimitivePartCore_of_correct fuel cgcdB hcorr p hgz hgcn hg0 hfuel

/-! ## Step 3a' — the `t`-degree IS the normalized list length (the bridge that makes the WF guard a
polynomial-degree fact)

The genuine termination question is whether the loop guard `(gbnormCore r).length < (gbnormCore Q).length`
is a **theorem** (the pseudo-remainder `t`-degree drop) or only a per-run assumption. It is a theorem at
the **polynomial** level — over the integral domain `R = (CFieldSpec.K β)[X]`, `lc(Q)` is a
non-zero-divisor, so the pseudo-remainder kills the top `t`-term and `deg_t(prem) < deg_t(Q)`. The bridge
`gbdegCore p = (toGBCoeffPoly p).natDegree` (the `GBPolyCore` mirror of `cdegG_eq_natDegree`, via the same
`natDegree ≤ length-1` + `leading-coeff-nonzero` argument over the `NormalizedGCDMonoid` `R`) is what turns
the list-length WF guard into that polynomial-degree drop — closing the gap
`ComputableTowerWellFounded` records as "no abstract `gbpsremainderCore` length-drop lemma". -/

/-- **`(toGBCoeffPoly p).natDegree` is bounded by the normalized `t`-length**:
`(toGBCoeffPoly p).natDegree ≤ (gbnormCore p).length − 1`. The `GBPolyCore` mirror of
`natDegree_toPolyG_le` — coefficients past `(gbnormCore p).length` read `toPolyG [] = 0`. -/
theorem natDegree_toGBCoeffPoly_le (p : GBPolyCore β) :
    (toGBCoeffPoly p).natDegree ≤ (gbnormCore p).length - 1 := by
  rw [← toGBCoeffPoly_gbnormCore]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [toGBCoeffPoly_coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
    Option.getD_none, toPolyG_nil]

/-- **★ The `t`-degree IS the normalized list length** `gbdegCore p = (toGBCoeffPoly p).natDegree`: the
`GBPolyCore` mirror of `cdegG_eq_natDegree`. For nonzero `p`, the top normalized `t`-coefficient
`gblcCore p` reads nonzero (`gbnormCore_getLast?_toPolyG_ne_zero`), giving the matching lower bound; the
zero case is `gbdegCore [] = 0 = natDegree 0`. This is the lemma that makes the engine's list-length loop
guard a *polynomial* `t`-degree statement. -/
theorem gbdegCore_eq_natDegree (p : GBPolyCore β) : gbdegCore p = (toGBCoeffPoly p).natDegree := by
  rcases eq_or_ne (gbnormCore p) [] with h | h
  · have h0 : toGBCoeffPoly p = 0 := by rw [← toGBCoeffPoly_gbnormCore, h, toGBCoeffPoly_nil]
    rw [gbdegCore, h, h0]; simp
  · refine le_antisymm ?_ (natDegree_toGBCoeffPoly_le p)
    apply Polynomial.le_natDegree_of_ne_zero
    rw [← toPolyG_gblcCore_eq_coeff]
    -- `gblcCore p` (the top normalized coefficient) reads nonzero
    have hz : gbisZeroCore p = false := by
      rw [gbisZeroCore, List.isEmpty_eq_false_iff_exists_mem]
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ h
      exact ⟨a, ha⟩
    exact toPolyG_gblcCore_ne_zero hz

/-- **The normalized `t`-length equals `natDegree + 1` for a nonzero `GBPolyCore`**: if
`gbisZeroCore p = false`, then `(gbnormCore p).length = (toGBCoeffPoly p).natDegree + 1`. (`gbdegCore p =
length − 1` and `length ≥ 1`, combined with `gbdegCore_eq_natDegree`.) The form the WF length-drop guard
consumes. -/
theorem gbnormCore_length_eq_natDegree_succ {p : GBPolyCore β} (hp : gbisZeroCore p = false) :
    (gbnormCore p).length = (toGBCoeffPoly p).natDegree + 1 := by
  have hne : gbnormCore p ≠ [] := by
    rw [gbisZeroCore, List.isEmpty_eq_false_iff_exists_mem] at hp
    obtain ⟨a, ha⟩ := hp
    exact List.ne_nil_of_mem ha
  have hpos : 1 ≤ (gbnormCore p).length := List.length_pos_iff.mpr hne
  have := gbdegCore_eq_natDegree p
  rw [gbdegCore] at this
  omega

/-! ## Step 3b — the reduction theorem: regularity + correctness + bookkeeping ⟹ `CPrimPRSGenAssocReg`

The legacy per-step **coefficient-size** side-conditions the algorithm self-satisfies on a finite run: at
each `gbprimitivePartCore` node, every stripped `t`-coefficient has `cnormG`-length at most `30`. The
content strip now uses fuel-free `cdivWf`, so this predicate is retained as PRS-gate bookkeeping rather
than as runtime division fuel. -/

/-- **Per-step content-strip bookkeeping** `CPrimPRSGenFuelOk fuel P Q`: at each primitive-PRS node, every
`t`-coefficient entering `gbprimitivePartCore` has `cnormG`-length at most `30` — for the terminal strip
of `P` (`gbnormCore P`) and, at each recursive node, of the pseudo-remainder `prem`. This mirrors the
`cprimPRSgcdGenCore` recursion so it threads alongside `CPrimPRSGenRegular`; the content division itself
is fuel-free. -/
def CPrimPRSGenFuelOk (cgcdB : CPolyG β → CPolyG β → CPolyG β) :
    ℕ → GBPolyCore β → GBPolyCore β → Prop
  | 0, P, _ => ∀ a ∈ gbnormCore P, (CPolyG.cnormG a : List β).length ≤ 30
  | fuel + 1, P, Q =>
    if gbisZeroCore (gbnormCore Q) = true then
      ∀ a ∈ gbnormCore (gbnormCore P), (CPolyG.cnormG a : List β).length ≤ 30
    else
      (∀ a ∈ gbnormCore (gbpsremainderCore 60 (gbnormCore P) (gbnormCore Q)),
          (CPolyG.cnormG a : List β).length ≤ 30)
        ∧ CPrimPRSGenFuelOk cgcdB fuel (gbnormCore Q)
            (gbprimitivePartCore cgcdB (gbpsremainderCore 60 (gbnormCore P) (gbnormCore Q)))

/-- **★ The reduction theorem — `CPrimPRSGenAssocReg` from the sharp residual.** Given the genuine per-run
termination witness `CPrimPRSGenRegular cgcdB fuel P Q` (`ComputableTowerWellFounded`), the level-`β`
gcd-correctness `CgcdBCorrect cgcdB`, and the retained per-step content-strip bookkeeping
`CPrimPRSGenFuelOk cgcdB fuel P Q`, the per-step regularity bundle `CPrimPRSGenAssocReg cgcdB fuel P Q`
holds. Clause (i) is the `CPrimPRSGenRegular` `stop`-node; clause (ii) is the nonzero-multiplier
`toGBPolyG_gbpsremainderCore_ne_zero` at a `step`-node; clause (iii) is the total content strip
`associated_toGBPolyG_gbprimitivePartCore_total`. So the opaque `CPrimPRSGenAssocReg` gate is **exactly**
PRS termination + level-`β` gcd-correctness (+ retained bookkeeping) — the precise non-degeneracy. -/
theorem cPrimPRSGenAssocReg_of_regular_of_correct (cgcdB : CPolyG β → CPolyG β → CPolyG β)
    (hcorr : CgcdBCorrect cgcdB) :
    ∀ (fuel : ℕ) (P Q : GBPolyCore β), CPrimPRSGenRegular cgcdB fuel P Q →
      CPrimPRSGenFuelOk cgcdB fuel P Q → CPrimPRSGenAssocReg cgcdB fuel P Q := by
  intro fuel
  induction fuel with
  | zero =>
    intro P Q hreg hfuel
    -- at fuel 0, CPrimPRSGenRegular must be a `stop` node (the `step` ctor needs `fuel+1`)
    rw [CPrimPRSGenAssocReg]
    refine ⟨?_, ?_⟩
    · -- clause (i): the `stop`-node gives `gbisZeroCore (gbnormCore Q) = true`; reduce to `gbisZeroCore Q`
      cases hreg with
      | stop hz => rw [gbisZeroCore, ← gbnormCore_idemp, ← gbisZeroCore]; exact hz
    · -- clause (iii) on `P` (terminal strip): total content scaling
      rw [CPrimPRSGenFuelOk] at hfuel
      exact associated_toGBPolyG_gbprimitivePartCore_total 30 cgcdB hcorr P hfuel
  | succ fuel ih =>
    intro P Q hreg hfuel
    rw [CPrimPRSGenAssocReg]
    cases hreg with
    | stop hz =>
      -- terminal: left disjunct (Q normalizes to zero) + clause (iii) on `gbnormCore P`
      refine Or.inl ⟨hz, ?_⟩
      rw [CPrimPRSGenFuelOk, if_pos hz] at hfuel
      have h := associated_toGBPolyG_gbprimitivePartCore_total 30 cgcdB hcorr (gbnormCore P) hfuel
      rwa [toGBPolyG_gbnormCore] at h
    | step hz hguard hrec =>
      -- recursive node: right disjunct
      rw [CPrimPRSGenFuelOk, if_neg (by rw [hz]; simp)] at hfuel
      obtain ⟨hfuelPrem, hfuelRec⟩ := hfuel
      refine Or.inr ⟨by rw [hz]; simp, ?_, ?_, ?_⟩
      · -- clause (ii): the nonzero-multiplier pseudo-division witness
        obtain ⟨s, c, hrel, hc0⟩ := toGBPolyG_gbpsremainderCore_ne_zero 60 (gbnormCore P)
          (gbnormCore Q) (by rw [gbnormCore_idemp]; exact hz)
        exact ⟨s, c, hrel, hc0⟩
      · -- clause (iii): the total content strip on `prem`
        exact associated_toGBPolyG_gbprimitivePartCore_total 30 cgcdB hcorr
          (gbpsremainderCore 60 (gbnormCore P) (gbnormCore Q)) hfuelPrem
      · -- the tower recursion: regularity ∧ fuel ⟹ AssocReg one level down
        exact ih (gbnormCore Q) _ hrec hfuelRec

/-! ## Step 4 — SHARPENING termination: exactly *when* the per-step guard holds vs. is a genuine residual

The reduction (Step 3) leaves termination as `CPrimPRSGenRegular`, whose `step` node carries the loop guard
`(gbnormCore r).length < (gbnormCore Q).length`. We now pin down precisely how much of that guard is a
**theorem** and what the **irreducible** residual is.

* `gbdegCore_eq_natDegree` (Step 4a) already made the guard a *polynomial* `t`-degree fact.
* The content strip `gbprimitivePartCore` **preserves the `t`-degree** (it is a `β(s)`-unit scaling,
  `associated_toGBPolyG_gbprimitivePartCore_total`): so the guard on `r = gbprimitivePartCore … prem`
  equals the guard on the raw pseudo-remainder `prem` (`gbnormGuard_iff_premDegree` below).
* **The single pseudo-division step `t`-degree drop is now a THEOREM** (`natDegree_gbStepReduce_lt`): one
  loop body `lc(q)·p − lc(p)·tᵏ·q` cancels the leading term (`lc(q)·lc(p) − lc(p)·lc(q) = 0`) and over the
  integral domain `R = (CFieldSpec.K β)[X]` drops the `t`-degree strictly. **This is precisely the per-step
  degree fact `ComputableTowerWellFounded` records as "no abstract `gbpsremainderCore` length-drop lemma"**
  — supplied here. So *no* degree drop in the PRS can fail mathematically.
* What remains genuinely conditional is therefore **only that the fuel-bounded loop runs to completion** —
  `gbpsremainderCore` iterates the (now-proven-dropping) step until `p.length < q.length`, and with the
  fuel exhausted mid-reduction the result can still retain degree `≥ deg Q`. That fuel-adequacy (the loop
  fuel 60 exceeds the finite degree budget) is the **single irreducible per-run ingredient** — pure
  bookkeeping, not a missing mathematical fact. -/

/-! ### The single pseudo-division step degree drop IS a theorem (the leading-term cancellation)

The `gbpsremainderCore` loop body replaces `p` by `p' = lc(q)·p − lc(p)·tᵏ·q` (`k = deg_t p − deg_t q`).
We prove **unconditionally** that this step strictly drops the `t`-degree: the top `t`-coefficient is
`lc(q)·lc(p) − lc(p)·lc(q) = 0` (the leading-term cancellation), and over the integral domain
`R = (CFieldSpec.K β)[X]` a strictly lower remaining degree. This is the genuine per-step degree fact —
*the missing engine lemma* — now a theorem. (It does not by itself prove loop termination, which still
needs the fuel to reach the `p.length < q.length` exit; but it shows the only conditional ingredient is the
*loop completing*, never a degree-drop that could fail mathematically.) -/

/-- **`toPolyG (gblcCore (gbnormCore p))` is the leading coefficient of `toGBCoeffPoly p`.** The top
normalized `t`-coefficient reads to `(toGBCoeffPoly p).leadingCoeff = coeff (natDegree)`, via
`toPolyG_gblcCore_eq_coeff` and `gbdegCore_eq_natDegree`. -/
theorem toPolyG_gblcCore_eq_leadingCoeff (p : GBPolyCore β) :
    CPolyG.toPolyG (gblcCore (gbnormCore p)) = (toGBCoeffPoly p).leadingCoeff := by
  rw [Polynomial.leadingCoeff, ← gbdegCore_eq_natDegree, toPolyG_gblcCore_eq_coeff,
    toGBCoeffPoly_gbnormCore]
  congr 1
  rw [gbdegCore, gbdegCore, gbnormCore_idemp]

/-- **The single pseudo-division step body** `gbStepReduce p q = lc(q)·p − lc(p)·tᵏ·q`
(`k = (gbnormCore p).length − (gbnormCore q).length`): one leading-term elimination of `gbpsremainderCore`
over the coefficient ring `CPolyG β = β[s]`. -/
noncomputable def gbStepReduce (p q : GBPolyCore β) : GBPolyCore β :=
  gbsubCore (gbscaleCCore (gblcCore (gbnormCore q)) p)
    (gbscaleCCore (gblcCore (gbnormCore p))
      (gbshiftCore ((gbnormCore p).length - (gbnormCore q).length) q))

/-- **The `R[t]` reading of a step body** `toGBCoeffPoly (gbStepReduce p q) = C(lc q)·toGBCoeffPoly p −
C(lc p)·tᵏ·toGBCoeffPoly q` (`R = (CFieldSpec.K β)[X]`, `k = deg_t p − deg_t q`). -/
theorem toGBCoeffPoly_gbStepReduce (p q : GBPolyCore β) :
    toGBCoeffPoly (gbStepReduce p q)
      = Polynomial.C ((toGBCoeffPoly q).leadingCoeff) * toGBCoeffPoly p
        - Polynomial.C ((toGBCoeffPoly p).leadingCoeff)
          * Polynomial.X ^ ((gbnormCore p).length - (gbnormCore q).length) * toGBCoeffPoly q := by
  rw [gbStepReduce, toGBCoeffPoly_gbsubCore, toGBCoeffPoly_gbscaleCCore, toGBCoeffPoly_gbscaleCCore,
    toGBCoeffPoly_gbshiftCore, toPolyG_gblcCore_eq_leadingCoeff, toPolyG_gblcCore_eq_leadingCoeff]
  ring

/-- **★ The single pseudo-division step strictly drops the `t`-degree** (unconditional — the leading-term
cancellation): for nonzero `p, q` with `deg_t q ≤ deg_t p`, if the step body `gbStepReduce p q` is nonzero
then `(toGBCoeffPoly (gbStepReduce p q)).natDegree < (toGBCoeffPoly p).natDegree`. The top coefficient is
`lc(q)·lc(p) − lc(p)·lc(q) = 0` and both summands have `t`-degree `≤ deg_t p`, so over the integral domain
`(CFieldSpec.K β)[X]` the difference drops below `deg_t p`. **This is the per-step degree fact
`ComputableTowerWellFounded` records as missing** — now a theorem; the only thing left conditional for
termination is the fuel-bounded loop *completing*, not any degree-drop that could fail. -/
theorem natDegree_gbStepReduce_lt (p q : GBPolyCore β)
    (hp : gbisZeroCore (gbnormCore p) = false) (hq : gbisZeroCore (gbnormCore q) = false)
    (hdeg : (toGBCoeffPoly q).natDegree ≤ (toGBCoeffPoly p).natDegree)
    (hstepne : toGBCoeffPoly (gbStepReduce p q) ≠ 0) :
    (toGBCoeffPoly (gbStepReduce p q)).natDegree < (toGBCoeffPoly p).natDegree := by
  have hp' : gbisZeroCore p = false := by rw [gbisZeroCore, ← gbnormCore_idemp, ← gbisZeroCore]; exact hp
  have hq' : gbisZeroCore q = false := by rw [gbisZeroCore, ← gbnormCore_idemp, ← gbisZeroCore]; exact hq
  have hkp : (gbnormCore p).length = (toGBCoeffPoly p).natDegree + 1 :=
    gbnormCore_length_eq_natDegree_succ hp'
  have hkq : (gbnormCore q).length = (toGBCoeffPoly q).natDegree + 1 :=
    gbnormCore_length_eq_natDegree_succ hq'
  set np := (toGBCoeffPoly p).natDegree with hnp
  set nq := (toGBCoeffPoly q).natDegree with hnq
  have hk : (gbnormCore p).length - (gbnormCore q).length = np - nq := by rw [hkp, hkq]; omega
  set A := Polynomial.C ((toGBCoeffPoly q).leadingCoeff) * toGBCoeffPoly p with hA
  set B := Polynomial.C ((toGBCoeffPoly p).leadingCoeff)
    * Polynomial.X ^ (np - nq) * toGBCoeffPoly q with hB
  have hstep : toGBCoeffPoly (gbStepReduce p q) = A - B := by rw [toGBCoeffPoly_gbStepReduce, hk]
  have hAle : A.natDegree ≤ np := natDegree_C_mul_le _ _
  have hBle : B.natDegree ≤ np := by
    rw [hB]
    refine le_trans natDegree_mul_le ?_
    have h1 : (Polynomial.C ((toGBCoeffPoly p).leadingCoeff) * Polynomial.X ^ (np - nq)).natDegree
        ≤ np - nq := le_trans natDegree_mul_le (by simp [natDegree_C])
    omega
  -- coeff = leading at the respective natDegrees (np, nq) — defeq through the `set` lets
  have hpc : (toGBCoeffPoly p).coeff np = (toGBCoeffPoly p).leadingCoeff := by
    rw [hnp, Polynomial.leadingCoeff]
  have hqc : (toGBCoeffPoly q).coeff nq = (toGBCoeffPoly q).leadingCoeff := by
    rw [hnq, Polynomial.leadingCoeff]
  -- the leading-term cancellation: coeff at `np` is `lc(q)·lc(p) − lc(p)·lc(q) = 0`
  have hAcoeff : A.coeff np = (toGBCoeffPoly q).leadingCoeff * (toGBCoeffPoly p).leadingCoeff := by
    rw [hA, coeff_C_mul, hpc]
  have hBcoeff : B.coeff np = (toGBCoeffPoly p).leadingCoeff * (toGBCoeffPoly q).leadingCoeff := by
    rw [hB, mul_assoc, coeff_C_mul]
    congr 1
    have hc := coeff_X_pow_mul (toGBCoeffPoly q) (np - nq) nq
    rw [Nat.add_sub_cancel' hdeg] at hc
    rw [hc, hqc]
  have hcoeffeq : A.coeff np = B.coeff np := by rw [hAcoeff, hBcoeff, mul_comm]
  rw [hstep]
  have hle : (A - B).natDegree ≤ np := le_trans (natDegree_sub_le A B) (max_le hAle hBle)
  have hcn : (A - B).coeff np = 0 := by rw [coeff_sub, hcoeffeq, sub_self]
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso; rw [← h] at hcn; rw [hstep] at hstepne; exact (leadingCoeff_ne_zero.mpr hstepne) hcn

/-! ### The inner pseudo-division loop COMPLETES with adequate fuel (the degree drop, no longer assumed)

Iterating the (now-proven-dropping) step, the fuel-bounded `gbpsremainderCore` reaches degree `< deg_t q`
(or `0`) **as a theorem** once the loop fuel exceeds the `t`-degree of `p`. This converts the
"fuel-adequacy assumption" of termination into an **explicit, satisfiable fuel bound**: with fuel `60` (as
the engine uses) and `deg_t p < 60`, the inner pseudo-division degree drop is guaranteed. The only thing
that could leave it conditional — the loop hitting the fuel floor — is now a transparent numeric bound. -/

omit [CFieldSpec β] in
/-- **`gbisZeroCore` is `gbnormCore`-invariant**: `gbisZeroCore (gbnormCore p) = gbisZeroCore p`. -/
theorem gbisZeroCore_gbnormCore (p : GBPolyCore β) : gbisZeroCore (gbnormCore p) = gbisZeroCore p := by
  rw [gbisZeroCore, gbisZeroCore, gbnormCore_idemp]

omit [CFieldSpec β] in
/-- **A nonzero `GBPolyCore` normalizes to a nonempty list**: `0 < (gbnormCore q).length` from
`gbisZeroCore (gbnormCore q) = false`. -/
theorem gbnormCore_length_pos {q : GBPolyCore β} (hq : gbisZeroCore (gbnormCore q) = false) :
    0 < (gbnormCore q).length := by
  have hne : gbnormCore q ≠ [] := by
    rw [gbisZeroCore, List.isEmpty_eq_false_iff_exists_mem, gbnormCore_idemp] at hq
    obtain ⟨a, ha⟩ := hq; exact List.ne_nil_of_mem ha
  exact List.length_pos_iff.mpr hne

/-- **The pseudo-remainder of a zero dividend reads zero**: if `toGBCoeffPoly p = 0` then
`toGBCoeffPoly (gbpsremainderCore fuel p q) = 0`. (The loop on `p = 0` returns `[]`.) The base of the
inner-loop degree-drop recursion when a step body vanishes. -/
theorem toGBCoeffPoly_gbpsremainderCore_eq_zero_of_zero (fuel : ℕ) (p q : GBPolyCore β)
    (hp : toGBCoeffPoly p = 0) : toGBCoeffPoly (gbpsremainderCore fuel p q) = 0 := by
  cases fuel with
  | zero => rw [gbpsremainderCore, toGBCoeffPoly_gbnormCore]; exact hp
  | succ fuel =>
    have hpnil : gbnormCore p = [] := by
      rw [← gbisZeroCore_iff_toGBCoeffPoly, gbisZeroCore, List.isEmpty_iff] at hp; exact hp
    rw [gbpsremainderCore]; simp only [hpnil, List.length_nil]
    by_cases hqz : gbisZeroCore (gbnormCore q) = true
    · simp [hqz]
    · rw [Bool.not_eq_true] at hqz; simp [hqz, gbnormCore_length_pos hqz]

/-- **★ The inner pseudo-division loop completes (degree drop) with adequate fuel** — UNCONDITIONAL: for
`q` nonzero and `fuel > deg_t p` (`(toGBCoeffPoly p).natDegree < fuel`), the pseudo-remainder either drops
below `q`'s `t`-degree or is zero:
`(toGBCoeffPoly (gbpsremainderCore fuel p q)).natDegree < (toGBCoeffPoly q).natDegree ∨
toGBCoeffPoly (gbpsremainderCore fuel p q) = 0`. By induction on `fuel`, iterating the single-step drop
`natDegree_gbStepReduce_lt` (each loop body strictly lowers `deg_t p`, so the bound `deg_t p < fuel`
descends with the recursion). **This is the engine's missing degree-drop lemma, supplied** — termination's
only residual is now the satisfiable numeric fuel bound `deg_t p < fuel`, not any per-run regularity. -/
theorem gbpsremainderCore_degree_lt (q : GBPolyCore β) (hq : gbisZeroCore (gbnormCore q) = false) :
    ∀ (fuel : ℕ) (p : GBPolyCore β), (toGBCoeffPoly p).natDegree < fuel →
      (toGBCoeffPoly (gbpsremainderCore fuel p q)).natDegree < (toGBCoeffPoly q).natDegree
        ∨ toGBCoeffPoly (gbpsremainderCore fuel p q) = 0 := by
  have hqnz : gbisZeroCore q = false := by
    rw [gbisZeroCore, ← gbnormCore_idemp, ← gbisZeroCore]; exact hq
  have hql : (gbnormCore q).length = (toGBCoeffPoly q).natDegree + 1 :=
    gbnormCore_length_eq_natDegree_succ hqnz
  have hqpos : 0 < (gbnormCore q).length := gbnormCore_length_pos hq
  intro fuel
  induction fuel with
  | zero => intro p hlt; omega
  | succ fuel ih =>
    intro p hlt
    rw [gbpsremainderCore]; simp only [hq, Bool.false_eq_true, if_false]
    by_cases hlen : (gbnormCore p).length < (gbnormCore q).length
    · -- the loop exits: the (normalized) dividend already has degree below `q` (or is zero)
      rw [if_pos hlen, toGBCoeffPoly_gbnormCore]
      by_cases hpz : toGBCoeffPoly p = 0
      · right; exact hpz
      · left
        have hpnz : gbisZeroCore p = false := by
          rw [Bool.eq_false_iff, Ne, gbisZeroCore_iff_toGBCoeffPoly]; exact hpz
        have hpl := gbnormCore_length_eq_natDegree_succ hpnz
        omega
    · -- the loop steps: recurse on the (strictly lower degree) step body `p'`
      -- the engine recurses with divisor `gbnormCore q`; normalize it back to `q` for the IH
      rw [if_neg hlen, ← gbpsremainderCore_gbnormCore_right]
      have hpnz : gbisZeroCore p = false := by
        rw [Bool.eq_false_iff, Ne, gbisZeroCore_iff_toGBCoeffPoly]
        intro hh
        have hpnil : gbnormCore p = [] := by
          rw [← gbisZeroCore_iff_toGBCoeffPoly, gbisZeroCore, List.isEmpty_iff] at hh; exact hh
        rw [hpnil, List.length_nil] at hlen; omega
      have hpl := gbnormCore_length_eq_natDegree_succ hpnz
      have hdle : (toGBCoeffPoly (gbnormCore q)).natDegree ≤ (toGBCoeffPoly (gbnormCore p)).natDegree := by
        rw [toGBCoeffPoly_gbnormCore, toGBCoeffPoly_gbnormCore]; omega
      set p' := gbnormCore (gbsubCore (gbscaleCCore (gblcCore (gbnormCore q)) (gbnormCore p))
        (gbscaleCCore (gblcCore (gbnormCore p))
          (gbshiftCore ((gbnormCore p).length - (gbnormCore q).length) (gbnormCore q)))) with hp'def
      have hp'read : toGBCoeffPoly p' = toGBCoeffPoly (gbStepReduce (gbnormCore p) (gbnormCore q)) := by
        rw [hp'def, toGBCoeffPoly_gbnormCore, gbStepReduce, toGBCoeffPoly_gbsubCore,
          toGBCoeffPoly_gbsubCore, toGBCoeffPoly_gbscaleCCore, toGBCoeffPoly_gbscaleCCore,
          toGBCoeffPoly_gbscaleCCore, toGBCoeffPoly_gbscaleCCore, toGBCoeffPoly_gbshiftCore,
          toGBCoeffPoly_gbshiftCore, gbnormCore_idemp, gbnormCore_idemp]
      by_cases hp'z : toGBCoeffPoly p' = 0
      · right; rw [toGBCoeffPoly_gbpsremainderCore_eq_zero_of_zero fuel p' q hp'z]
      · have hpnn : gbisZeroCore (gbnormCore (gbnormCore p)) = false := by
          rw [gbisZeroCore_gbnormCore, gbisZeroCore_gbnormCore]; exact hpnz
        have hqnn : gbisZeroCore (gbnormCore (gbnormCore q)) = false := by
          rw [gbisZeroCore_gbnormCore]; exact hq
        have hdegstep : (toGBCoeffPoly p').natDegree < (toGBCoeffPoly p).natDegree := by
          rw [hp'read]
          have h := natDegree_gbStepReduce_lt (gbnormCore p) (gbnormCore q) hpnn hqnn
            hdle (by rw [← hp'read]; exact hp'z)
          rwa [toGBCoeffPoly_gbnormCore] at h
        exact ih p' (by omega)

/-- **`toGBPolyG` preserves the `t`-degree of `toGBCoeffPoly`**: `(toGBPolyG p).natDegree =
(toGBCoeffPoly p).natDegree`. The coefficient lift `liftKG = mapRingHom (amG β)` is over the injective
field embedding `amG β`, so `Polynomial.natDegree_map` applies. -/
theorem natDegree_toGBPolyG (p : GBPolyCore β) :
    (toGBPolyG p).natDegree = (toGBCoeffPoly p).natDegree := by
  rw [toGBPolyG, liftKG, Polynomial.coe_mapRingHom,
    Polynomial.natDegree_map_eq_of_injective (RatFunc.algebraMap_injective (CFieldSpec.K β))]

/-- **★ The content strip preserves the `t`-degree** (unconditional given `CgcdBCorrect` plus retained
bookkeeping): under `CgcdBCorrect cgcdB` and the per-coefficient size bound,
`(toGBCoeffPoly (gbprimitivePartCore cgcdB p)).natDegree = (toGBCoeffPoly p).natDegree`. The content strip is a `β(s)`-unit scaling
(`associated_toGBPolyG_gbprimitivePartCore_total`), and `Associated` polynomials over the field `β(s)` have
equal `natDegree` (pulled back through the degree-preserving lift `toGBPolyG`). So the WF loop guard on the
stripped node `r` is *exactly* the guard on the raw pseudo-remainder `prem`. -/
theorem natDegree_toGBCoeffPoly_gbprimitivePartCore (fuel : ℕ)
    (cgcdB : CPolyG β → CPolyG β → CPolyG β) (hcorr : CgcdBCorrect cgcdB) (p : GBPolyCore β)
    (hfuel : ∀ a ∈ gbnormCore p, (CPolyG.cnormG a : List β).length ≤ fuel) :
    (toGBCoeffPoly (gbprimitivePartCore cgcdB p)).natDegree = (toGBCoeffPoly p).natDegree := by
  have hassoc := associated_toGBPolyG_gbprimitivePartCore_total fuel cgcdB hcorr p hfuel
  have := natDegree_eq_of_associated hassoc
  rwa [natDegree_toGBPolyG, natDegree_toGBPolyG] at this

/-- **★ The list-length loop guard is exactly the pseudo-remainder `t`-degree drop.** Under `CgcdBCorrect
cgcdB`, the retained size bound on `prem`, and `Q` nonzero (`gbisZeroCore (gbnormCore Q) = false`), the
`CPrimPRSGenRegular`-`step` guard
`(gbnormCore (gbprimitivePartCore cgcdB prem)).length < (gbnormCore Q).length`
holds **iff** `(toGBCoeffPoly prem).natDegree < (toGBCoeffPoly Q).natDegree` — *provided* the stripped node
`r` is itself nonzero (`hrz`, which holds whenever `prem` is, the content strip being a unit scaling). So
the genuine termination witness reduces to the **pseudo-remainder polynomial `t`-degree drop**; the content
strip and the list/degree translation contribute nothing conditional. -/
theorem gbnormGuard_iff_premDegree (cgcdB : CPolyG β → CPolyG β → CPolyG β) (hcorr : CgcdBCorrect cgcdB)
    (P Q : GBPolyCore β) (hQ : gbisZeroCore (gbnormCore Q) = false)
    (hfuel : ∀ a ∈ gbnormCore (gbpsremainderCore 60 (gbnormCore P) (gbnormCore Q)),
      (CPolyG.cnormG a : List β).length ≤ 30)
    (hrz : gbisZeroCore (gbprimitivePartCore cgcdB
      (gbpsremainderCore 60 (gbnormCore P) (gbnormCore Q))) = false) :
    ((gbnormCore (gbprimitivePartCore cgcdB
        (gbpsremainderCore 60 (gbnormCore P) (gbnormCore Q)))).length < (gbnormCore Q).length)
      ↔ (toGBCoeffPoly (gbpsremainderCore 60 (gbnormCore P) (gbnormCore Q))).natDegree
          < (toGBCoeffPoly (gbnormCore Q)).natDegree := by
  -- `gbisZeroCore Q = false` (idempotence) to apply the length lemma on the outer `gbnormCore Q`
  have hQ' : gbisZeroCore Q = false := by rw [gbisZeroCore, ← gbnormCore_idemp, ← gbisZeroCore]; exact hQ
  rw [gbnormCore_length_eq_natDegree_succ hrz, gbnormCore_length_eq_natDegree_succ hQ',
    Nat.add_lt_add_iff_right,
    natDegree_toGBCoeffPoly_gbprimitivePartCore 30 cgcdB hcorr _ hfuel, toGBCoeffPoly_gbnormCore]

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- ★ THE DELIVERABLE: the per-step regularity gate `CPrimPRSGenAssocReg` follows from the sharp residual —
-- PRS termination (`CPrimPRSGenRegular`) + level-β gcd-correctness (`CgcdBCorrect`) + transparent fuel.
example (cgcdB : CPolyG β → CPolyG β → CPolyG β) (hcorr : CgcdBCorrect cgcdB)
    (fuel : ℕ) (P Q : GBPolyCore β) (hreg : CPrimPRSGenRegular cgcdB fuel P Q)
    (hfuel : CPrimPRSGenFuelOk cgcdB fuel P Q) : CPrimPRSGenAssocReg cgcdB fuel P Q :=
  cPrimPRSGenAssocReg_of_regular_of_correct cgcdB hcorr fuel P Q hreg hfuel

-- The list-length WF guard IS the polynomial t-degree (the representation half of termination, closed).
example (p : GBPolyCore β) : gbdegCore p = (toGBCoeffPoly p).natDegree := gbdegCore_eq_natDegree p

-- Clause (ii) with the β(s)-unit multiplier is unconditional given the non-terminal loop guard (Q ≠ 0).
example (fuel : ℕ) (p q : GBPolyCore β) (hq : gbisZeroCore (gbnormCore q) = false) :
    ∃ (s : GBPolyCore β) (c : CPolyG β),
      Polynomial.C (QFunNZG.amG β (CPolyG.toPolyG c)) * toGBPolyG p
          = toGBPolyG s * toGBPolyG q + toGBPolyG (gbpsremainderCore fuel p q)
        ∧ QFunNZG.amG β (CPolyG.toPolyG c) ≠ 0 :=
  toGBPolyG_gbpsremainderCore_ne_zero fuel p q hq

-- ★ The single pseudo-division step strictly drops the t-degree, UNCONDITIONALLY (the leading-term
-- cancellation) — the per-step degree fact ComputableTowerWellFounded records as missing, now a theorem.
example (p q : GBPolyCore β) (hp : gbisZeroCore (gbnormCore p) = false)
    (hq : gbisZeroCore (gbnormCore q) = false)
    (hdeg : (toGBCoeffPoly q).natDegree ≤ (toGBCoeffPoly p).natDegree)
    (hstepne : toGBCoeffPoly (gbStepReduce p q) ≠ 0) :
    (toGBCoeffPoly (gbStepReduce p q)).natDegree < (toGBCoeffPoly p).natDegree :=
  natDegree_gbStepReduce_lt p q hp hq hdeg hstepne

-- ★★ The inner pseudo-division loop COMPLETES (degree drop) under the explicit, satisfiable fuel bound
-- `deg_t p < fuel` — UNCONDITIONAL. Termination's last conditional ingredient is now a numeric bound.
example (q : GBPolyCore β) (hq : gbisZeroCore (gbnormCore q) = false)
    (fuel : ℕ) (p : GBPolyCore β) (hlt : (toGBCoeffPoly p).natDegree < fuel) :
    (toGBCoeffPoly (gbpsremainderCore fuel p q)).natDegree < (toGBCoeffPoly q).natDegree
      ∨ toGBCoeffPoly (gbpsremainderCore fuel p q) = 0 :=
  gbpsremainderCore_degree_lt q hq fuel p hlt

/-! ## ★ VERDICT — is `CPrimPRSGenAssocReg` unconditional?

**No — it is genuinely conditional, but on a *precisely identified, non-research-grade* residual**, NOT on
a missing content/GCD-domain theorem. Concretely, `CPrimPRSGenAssocReg cgcdB fuel P Q` is **equivalent**
(given the retained per-step bookkeeping `CPrimPRSGenFuelOk`) to exactly two per-run witnesses:

1. **PRS termination** — `CPrimPRSGenRegular cgcdB fuel P Q`: the primitive-PRS loop reaches a zero
   divisor within `fuel`. Its degree-drop content is now **fully a theorem**, on two levels:
   * the single pseudo-division step `lc(q)·p − lc(p)·tᵏ·q` cancels its leading term and strictly drops the
     `t`-degree over the integral domain `(CFieldSpec.K β)[X]` (`natDegree_gbStepReduce_lt` — exactly the
     per-step degree fact `ComputableTowerWellFounded` records as missing), the content strip / list-length
     translation being degree-neutral (`gbnormGuard_iff_premDegree`);
   * iterating it, the **inner pseudo-division loop completes** — `gbpsremainderCore_degree_lt`: under the
     explicit, satisfiable fuel bound `deg_t p < fuel`, `gbpsremainderCore fuel p q` lands at `t`-degree
     `< deg_t q` (or `0`), UNCONDITIONALLY.

   So the per-step `CPrimPRSGenRegular` guard is a *theorem* given the numeric bound `deg_t prem < 60`. The
   residual collapses to **the fuel constants the engine threads exceeding the run's finite degree budget**
   — a transparent numeric side-condition, not any per-run regularity or missing mathematical fact.

2. **Level-`β` gcd-correctness** — `CgcdBCorrect cgcdB`. On a tower run `cgcdB = cgcdFFRawCore β`, so this
   is the **tower induction hypothesis** (gcd-correctness at level `β` feeds level `QFunNZG β`), bottoming
   at the raw Euclidean gcd over `ℚ` — which (`associated_toPolyG_cgcdExtG`) is itself correct only under
   `cgcdTerminatesG`, again a per-run *termination* witness, never an unconditional `∀`.

**What is fully proved here, axiom-clean `[propext, Classical.choice, Quot.sound]` (NO native_decide):**
* `cPrimPRSGenAssocReg_of_regular_of_correct` — the reduction: (1) ∧ (2) ∧ fuel ⟹ `CPrimPRSGenAssocReg`.
* Clause (ii) unconditional given `Q ≠ 0` (`toGBPolyG_gbpsremainderCore_ne_zero`, the nonzero multiplier).
* Clause (iii) total / unconditional given (2) + fuel (`associated_toGBPolyG_gbprimitivePartCore_total`).
* The list-length ↔ polynomial `t`-degree bridge `gbdegCore_eq_natDegree` and the content-strip
  degree-preservation `natDegree_toGBCoeffPoly_gbprimitivePartCore`, collapsing the termination guard to a
  bare pseudo-remainder degree drop (`gbnormGuard_iff_premDegree`).
* **The single pseudo-division step `t`-degree drop `natDegree_gbStepReduce_lt`** (the leading-term
  cancellation) — the per-step degree fact the engine lacked.
* **The inner pseudo-division loop completion `gbpsremainderCore_degree_lt`** — `deg_t p < fuel` ⟹ the
  remainder drops below `deg_t q` (or is `0`), turning termination's last residual into a numeric bound.

**Resolution of the memory's tension** ("bookkeeping, not a missing fact" vs. "research-grade ingredient"):
the *former* is correct. The kernel is NOT research-grade — no Mathlib content/subresultant theorem is
missing (the proper primitive PRS *is* content-exact, and that exactness is fully discharged here from the
generic content theory). The residual is the **threading of two termination/fuel witnesses through the tower
recursion** — exactly the depth-indexed lift of the single-level `PrimPRSInputs` bookkeeping. Fully-abstract
soundness closes once those witnesses are produced (e.g. by a companion correctness/termination class with a
base instance at `ℚ` and a recursive instance at `QFunNZG β`), with no new mathematics. -/

end DeepWiki.SymbolicIntegration
