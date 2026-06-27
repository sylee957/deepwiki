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

/-! ## Step 3a — the TOTAL clause (iii): content strip is a `β(s)`-unit scaling, on ANY input

`associated_toGBPolyG_gbprimitivePartCore_of_correct` (`ComputableTowerGcdFFCorrect`) discharges clause
(iii) only when the content is **nonzero** (`hg`/`hgcn`/`hg0`). But the primitive-PRS loop also strips the
content of the **zero** polynomial (a terminal `P = 0`, or a `prem = 0`): there `gbprimitivePartCore` is
the identity (`gbnormCore p`, content branch `cisZeroG g`), so the `Associated` is reflexive. Bundling the
two cases gives the **total** clause (iii) — conditional only on `CgcdBCorrect cgcdB` (the level-`β`
gcd-correctness) and a transparent per-coefficient fuel bound, with **no** separate nonzero hypothesis. -/

/-- **★ Total clause (iii)** — `gbprimitivePartCore` is a `β(s)`-unit scaling on **any** input: under
`CgcdBCorrect cgcdB` (the level-`β` gcd-correctness) and a per-`t`-coefficient fuel bound,
`Associated (toGBPolyG (gbprimitivePartCore fuel cgcdB p)) (toGBPolyG p)`. Splits on whether the content
`gbcontentCore cgcdB p` is zero: if zero, `gbprimitivePartCore` is the identity `gbnormCore p` (reflexive
`Associated`); if nonzero, it is the unit scaling of `associated_toGBPolyG_gbprimitivePartCore_of_correct`.
So clause (iii) needs only the recursion's gcd-correctness plus transparent algorithmics — never a
content-nonzero assumption. -/
theorem associated_toGBPolyG_gbprimitivePartCore_total (fuel : ℕ)
    (cgcdB : CPolyG β → CPolyG β → CPolyG β) (hcorr : CgcdBCorrect cgcdB) (p : GBPolyCore β)
    (hfuel : ∀ a ∈ gbnormCore p, (CPolyG.cnormG a : List β).length ≤ fuel) :
    Associated (toGBPolyG (gbprimitivePartCore fuel cgcdB p)) (toGBPolyG p) := by
  by_cases hgz : CPolyG.cisZeroG (gbcontentCore cgcdB p) = true
  · -- content zero: gbprimitivePartCore is the identity `gbnormCore p`
    have hid : gbprimitivePartCore fuel cgcdB p = gbnormCore p := by
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

/-! ## Step 3b — the reduction theorem: regularity + correctness + fuel ⟹ `CPrimPRSGenAssocReg`

The transparent per-step **fuel** side-conditions the algorithm self-satisfies on a finite run: every
`cdivG`-content-strip has fuel `30 ≥` the `cnormG`-length of each `t`-coefficient. We bundle them as an
inductive predicate mirroring the PRS recursion (one `gbprimitivePartCore` per node), so the reduction
threads them down with the `CPrimPRSGenRegular` termination witness. -/

/-- **Per-step content-strip fuel bound** `CPrimPRSGenFuelOk fuel P Q`: at each primitive-PRS node, the
fuel `30` of `gbprimitivePartCore` bounds the `cnormG`-length of every `t`-coefficient it divides — for the
terminal strip of `P` (`gbnormCore P`) and, at each recursive node, of the pseudo-remainder `prem`.
Transparent algorithmics (the engine's `cdivG` has enough fuel on a finite run), mirroring the
`cprimPRSgcdGenCore` recursion so it threads alongside `CPrimPRSGenRegular`. -/
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
            (gbprimitivePartCore 30 cgcdB (gbpsremainderCore 60 (gbnormCore P) (gbnormCore Q)))

/-- **★ The reduction theorem — `CPrimPRSGenAssocReg` from the sharp residual.** Given the genuine per-run
termination witness `CPrimPRSGenRegular cgcdB fuel P Q` (`ComputableTowerWellFounded`), the level-`β`
gcd-correctness `CgcdBCorrect cgcdB`, and the transparent per-step content-strip fuel bounds
`CPrimPRSGenFuelOk cgcdB fuel P Q`, the per-step regularity bundle `CPrimPRSGenAssocReg cgcdB fuel P Q`
holds. Clause (i) is the `CPrimPRSGenRegular` `stop`-node; clause (ii) is the nonzero-multiplier
`toGBPolyG_gbpsremainderCore_ne_zero` at a `step`-node; clause (iii) is the total content strip
`associated_toGBPolyG_gbprimitivePartCore_total`. So the opaque `CPrimPRSGenAssocReg` gate is **exactly**
PRS termination + level-`β` gcd-correctness (+ transparent fuel) — the precise non-degeneracy. -/
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

end DeepWiki.SymbolicIntegration
