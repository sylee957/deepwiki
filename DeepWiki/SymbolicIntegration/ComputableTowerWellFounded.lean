import DeepWiki.SymbolicIntegration.ComputableTowerGcdFFCore
import DeepWiki.SymbolicIntegration.ComputableTowerIntegrate
import DeepWiki.SymbolicIntegration.ComputableWellFounded
import DeepWiki.SymbolicIntegration.ComputableWellFounded2
import DeepWiki.SymbolicIntegration.ComputableWellFounded3

/-! # Fuel-free (well-founded) GENERIC tower integration engine

The generic tower engine (`ComputableTowerIntegrate`) — `cIntegrateG`, `cRischDEG`, and their pipeline —
is `[CField α] [CDiffField α] [CFracGcdCore α]`-generic and gate-clean, but every op carries an explicit
`fuel : ℕ`. This file builds the **fuel-free** companions `…GWf`, by the same runtime-guard well-founded
recursion as the `QFunNZ`-specific arc (`ComputableWellFounded*`), now lifted to the generic carrier.

Every recursion in the generic pipeline bottoms out at one of THREE fuel-recursive ops; the rest is a flat
composition over fuel'd leaves:

* **`cprimPRSgcdGenCoreWf`** — the fraction-free primitive-PRS kernel (inside `CFracGcdCore.cgcdFFCore`),
  recursing on `(gbnormCore Q).length`. Its `…Wf` companion `cgcdFFCoreWf` re-runs the whole flat
  fraction-free gcd over the tower with no fuel.
* **`cSplitFactorFastGWf`** — Bronstein §3.5 split, recursing on `(cnormG p).length` (the `cSplitFactorFastWf`
  pattern, now generic).
* **`cSqfreeYunFFGgoWf`** — Yun squarefree factorization, recursing on the **multiplicity counter** `fo`
  (the `cSqfreeYunFFgoWf` Yun-exception, structural — sound at skipped multiplicities).

The flat-composition ops (`canonicalRepresentationFastGWf`, `cHermiteReduceTowerGWf`,
`cResidueResultantTowerGWf`/`cLogPartGWf`, `cIntegrateReducedGWf`, and the headline `cIntegrateGWf`)
substitute the fuel-free leaves and are bridged to their fuel'd `…G` originals. The generic leaves
`cdivmodWf`/`cgcdWf`/`cresultantWf` (`ComputableWellFounded`/`ComputableWellFounded2`) are reused verbatim
where the pipeline bottoms out at them.

Every `…GWf` def is **`[CField α]`-only on the fuel-free fragment** (plus `[CDiffField α]`/`[CFracGcdCore α]`
where the pipeline needs the derivation / the fraction-free gcd) — never `[CFieldSpec α]`, which would break
`native_decide` over the noncomputable tower (the keystone lesson). The fuel bounds live only inside the
bridge proofs; the runtime ops carry no fuel. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

/-! ## Part 1 — the fuel-free fraction-free gcd `cgcdFFCoreWf`

`cgcdFFCore fuel p q = cmonicG (cgcdFFRawCore fuel p q)` is the public monic fraction-free gcd; the work is
the level-recursive `cgcdFFRawCore` (a `CFracGcdCore` method), which for the recursive tower instance
clears denominators and runs `cprimPRSgcdGenCore` (the primitive PRS over the GCD-domain). We give a
fuel-free companion `cprimPRSgcdGenCoreWf` of that kernel (the only fuel-recursive piece), then a
`CFracGcdCoreWf` class whose method `cgcdFFRawCoreWf` is fuel-free, with the base/recursive instances
mirroring `CFracGcdCore`, and the public wrapper `cgcdFFCoreWf := cmonicG ∘ cgcdFFRawCoreWf`. -/

/-! ### The fuel-free primitive-PRS kernel `cprimPRSgcdGenCoreWf`

`cprimPRSgcdGenCore cgcdB fuel P Q` recurses `(P, Q) → (Q, r)` with `r = gbprimitivePartCore (gbpsremainder
P Q)`; the normalized `t`-length `(gbnormCore Q).length` strictly drops each step. The fuel-free companion
recurses with no fuel under the structural runtime guard `(gbnormCore r).length < (gbnormCore Q).length`, so
`decreasing_by` is `assumption`. -/

namespace GBPolyCore

variable {B : Type*} [CField B]

/-- **`gbnormCore` is idempotent** `gbnormCore (gbnormCore p) = gbnormCore p`: normalizing twice is the same
as once (the `cnormG`-of-coefficients is idempotent and the trailing-zero strip leaves a normalized poly
fixed). The bivariate analogue of `cnormG_idem`; discharges the `decreasing_by` of `cprimPRSgcdGenCoreWf`. -/
@[simp] theorem gbnormCore_idem (p : GBPolyCore B) : gbnormCore (gbnormCore p) = gbnormCore p := by
  induction p with
  | nil => rfl
  | cons a as ih =>
    rw [gbnormCore]
    cases hr : gbnormCore as with
    | nil =>
      by_cases ha : CPolyG.cisZeroG (CPolyG.cnormG a)
      · simp only [ha, if_true]; rfl
      · simp only [ha, Bool.false_eq_true, if_false]
        show gbnormCore [CPolyG.cnormG a] = [CPolyG.cnormG a]
        rw [gbnormCore, show gbnormCore ([] : GBPolyCore B) = [] from rfl]
        simp only [CPolyG.cnormG_idem, ha, Bool.false_eq_true, if_false]
    | cons r rs =>
      have hih : gbnormCore (r :: rs) = r :: rs := by rw [← hr]; exact ih
      rw [gbnormCore, hih, CPolyG.cnormG_idem]

/-- **Fuel-free generic primitive polynomial-remainder-sequence gcd** `cprimPRSgcdGenCoreWf cgcdB P Q ∈
GBPolyCore B`: the fuel-free companion of `cprimPRSgcdGenCore`. The gcd of `P, Q` in `t` (over the
coefficient ring `CPolyG B = B[s]`), up to a `B[s]`-content factor, with **no fuel at runtime**. Mirrors
`cprimPRSgcdGenCore`'s body — normalize `P, Q`; if `Q = 0` return the primitive part of `P`, else take the
next PRS node `r = gbprimitivePartCore 30 cgcdB (gbpsremainderCore 60 P Q)` and recurse on `(Q, r)`. The
recursion is taken only under the structural guard `(gbnormCore r).length < (gbnormCore Q).length`, so
`decreasing_by` is `assumption`. `[CField B]`-only (no `[CFieldSpec B]`), so it `native_decide`s over the
noncomputable-`CFieldSpec` tower. The content-gcd `cgcdB` is passed in (the level-`β` fuel-free
`cgcdFFRawCoreWf`). -/
def cprimPRSgcdGenCoreWf (cgcdB : CPolyG B → CPolyG B → CPolyG B) (P Q : GBPolyCore B) :
    GBPolyCore B :=
  let P := gbnormCore P
  let Q := gbnormCore Q
  if gbisZeroCore Q then gbprimitivePartCore 30 cgcdB P
  else
    let r := gbprimitivePartCore 30 cgcdB (gbpsremainderCore 60 P Q)
    if (gbnormCore r).length < (gbnormCore Q).length then
      cprimPRSgcdGenCoreWf cgcdB Q r
    else gbprimitivePartCore 30 cgcdB P   -- unreachable on a real run (PRS `t`-degree drop)
termination_by (gbnormCore Q).length
decreasing_by exact Nat.lt_of_lt_of_le ‹_ < _› (le_of_eq (by rw [gbnormCore_idem]))

end GBPolyCore

/-! ### Bridge of `cprimPRSgcdGenCoreWf` to the fuel'd `cprimPRSgcdGenCore`

There is no abstract `gbpsremainderCore` length-drop lemma over the generic GCD-domain `CPolyG B = B[s]`
(the pseudo-remainder degree drop over a non-field coefficient ring is exactly the per-step fact a real PRS
run satisfies but no engine lemma states), so — as with the Yun loop (`CSqfreeYunGoRegular`) — the bridge
takes a **fuel-regularity predicate** `CPrimPRSGenRegular` that mirrors the `cprimPRSgcdGenCore` fuel
recursion **with the per-step length-drop guard built in**. The WF guard then never fails along a regular
run, and the WF def coincides with the fuel'd version. The fuel lives only in the predicate / bridge proof;
the runtime `cprimPRSgcdGenCoreWf` carries none. -/

/-- **Per-run primitive-PRS-kernel fuel-regularity** `CPrimPRSGenRegular cgcdB fuel P Q`: mirrors the
`cprimPRSgcdGenCore` fuel recursion as an inductive predicate over the structural fuel counter — `stop`
(any fuel) when the next divisor is zero (`gbisZeroCore (gbnormCore Q)`, the loop ends), or `step`
(fuel `n+1`) when `Q` is nonzero, the next PRS node `r = gbprimitivePartCore 30 cgcdB (gbpsremainderCore 60
(gbnormCore P) (gbnormCore Q))` strictly drops the normalized `t`-length
(`(gbnormCore r).length < (gbnormCore Q).length` — the WF guard a real run meets), and the same holds
recursively on `(gbnormCore Q, r)` at one less fuel. The transparent per-node preconditions a real PRS
descent satisfies (the genuine termination witness: the `t`-degree strictly drops each step). -/
inductive CPrimPRSGenRegular {B : Type*} [CField B] (cgcdB : CPolyG B → CPolyG B → CPolyG B) :
    ℕ → GBPolyCore B → GBPolyCore B → Prop
  /-- terminal node: the next divisor is zero, the loop stops (any fuel). -/
  | stop {fuel : ℕ} {P Q : GBPolyCore B} (hz : GBPolyCore.gbisZeroCore (GBPolyCore.gbnormCore Q) = true) :
      CPrimPRSGenRegular cgcdB fuel P Q
  /-- recursive node: `Q` nonzero, the next PRS node drops the `t`-length, recurse on `(gbnormCore Q, r)`. -/
  | step {fuel : ℕ} {P Q : GBPolyCore B} (hz : GBPolyCore.gbisZeroCore (GBPolyCore.gbnormCore Q) = false)
      (hguard : (GBPolyCore.gbnormCore (GBPolyCore.gbprimitivePartCore 30 cgcdB
          (GBPolyCore.gbpsremainderCore 60 (GBPolyCore.gbnormCore P) (GBPolyCore.gbnormCore Q)))).length
        < (GBPolyCore.gbnormCore Q).length)
      (hrec : CPrimPRSGenRegular cgcdB fuel (GBPolyCore.gbnormCore Q)
        (GBPolyCore.gbprimitivePartCore 30 cgcdB
          (GBPolyCore.gbpsremainderCore 60 (GBPolyCore.gbnormCore P) (GBPolyCore.gbnormCore Q)))) :
      CPrimPRSGenRegular cgcdB (fuel + 1) P Q

namespace GBPolyCore

variable {B : Type*} [CField B]

/-- **`gbprimitivePartCore` is `gbnormCore`-invariant in its polynomial argument**
`gbprimitivePartCore fuel cgcdB (gbnormCore p) = gbprimitivePartCore fuel cgcdB p` (it normalizes its
argument internally, `gbnormCore_idem`). Reconciles the WF kernel's normalized base with the fuel'd one. -/
theorem gbprimitivePartCore_gbnorm (fuel : ℕ) (cgcdB : CPolyG B → CPolyG B → CPolyG B)
    (p : GBPolyCore B) :
    gbprimitivePartCore fuel cgcdB (gbnormCore p) = gbprimitivePartCore fuel cgcdB p := by
  rw [gbprimitivePartCore, gbprimitivePartCore, gbnormCore_idem]

/-- **Bridge — `cprimPRSgcdGenCoreWf` equals `cprimPRSgcdGenCore` on a regular run.** Under
`CPrimPRSGenRegular cgcdB fuel P Q` (the per-step `t`-length-drop a real PRS run meets, with sufficient
fuel), `cprimPRSgcdGenCoreWf cgcdB P Q = cprimPRSgcdGenCore cgcdB fuel P Q`. The fuel regularity lives only
here; the WF kernel carries none. By induction on the `CPrimPRSGenRegular` derivation: at a `stop` node both
return `gbprimitivePartCore 30 cgcdB (gbnormCore P)`; at a `step` node both take the same next PRS node `r`
and recurse — the WF guard fires (`hguard`) and the fuel'd version (at `fuel+1`) descends. -/
theorem cprimPRSgcdGenCoreWf_eq (cgcdB : CPolyG B → CPolyG B → CPolyG B) :
    ∀ (fuel : ℕ) (P Q : GBPolyCore B), CPrimPRSGenRegular cgcdB fuel P Q →
      cprimPRSgcdGenCoreWf cgcdB P Q = cprimPRSgcdGenCore cgcdB fuel P Q := by
  intro fuel P Q hreg
  induction hreg with
  | @stop fuel P Q hz =>
    -- next divisor zero: both return `gbprimitivePartCore 30 cgcdB (gbnormCore P)`
    rw [cprimPRSgcdGenCoreWf.eq_def, if_pos hz]
    cases fuel with
    | zero => rw [cprimPRSgcdGenCore, gbprimitivePartCore_gbnorm]
    | succ fuel => rw [cprimPRSgcdGenCore, if_pos hz]
  | @step fuel P Q hz hguard hrec ih =>
    -- recursive step: both take the same next PRS node `r`, recurse; the WF guard fires
    rw [cprimPRSgcdGenCoreWf.eq_def, cprimPRSgcdGenCore]
    -- the WF guard compares against `(gbnormCore (gbnormCore Q)).length`; reconcile via idempotence
    have hguard' : (gbnormCore (gbprimitivePartCore 30 cgcdB
          (gbpsremainderCore 60 (gbnormCore P) (gbnormCore Q)))).length
        < (gbnormCore (gbnormCore Q)).length := by rwa [gbnormCore_idem]
    simp only [hz, Bool.false_eq_true, if_false, if_pos hguard']
    exact ih

end GBPolyCore

/-! ### `class CFracGcdCoreWf α` — the recursive FUEL-FREE fraction-free gcd over `α[t]`

The fuel-free mirror of `CFracGcdCore`, tying the tower with no fuel:
* **`class CFracGcdCoreWf α`** (one method `cgcdFFRawCoreWf`, the *raw* content-normalized fuel-free gcd).
* **Base `instance CFracGcdCoreWf ℚ`** — `ℚ[t]`'s raw fraction-free gcd is the **fuel-free** generic
  Euclidean gcd `(cgcdWf p q).1` (the fuel-free companion of `(cgcdExtG _).1`).
* **Recursive `instance CFracGcdCoreWf (QFunNZG β) [CFracGcdCoreWf β]`** — clear denominators into
  `GBPolyCore β`, run the **fuel-free** kernel `cprimPRSgcdGenCoreWf` with the level-`β` `cgcdFFRawCoreWf` as
  content-gcd, lift back. Bottoms at `CFracGcdCoreWf ℚ`.
* **`instance CFracGcdCoreWf QFunNZ`** — the concrete level-1 carrier; its raw fuel-free gcd is the existing
  QFunNZ-specific `cgcdFFWf` (`ComputableWellFounded3`).

The public **monic** gcd is `cgcdFFCoreWf := cmonicG ∘ cgcdFFRawCoreWf` (monic-normalize only at the top).
Every method is `[CField α]`-only (plus the recursion's `[CFieldDomain β]`/`[CFracGcdCoreWf β]`) — no
`[CFieldSpec α]`, so the whole gcd `native_decide`s over the noncomputable tower. -/

/-- **Recursive FUEL-FREE fraction-free gcd over a tower level** (fuel-free mirror of `CFracGcdCore`): the
*raw* (content-normalized, NOT monic) gcd `cgcdFFRawCoreWf p q` of `p, q ∈ CPolyG α = α[t]`, with **no fuel
at runtime**. The method is the RAW gcd (what the recursion consumes as a content-gcd; monic normalization
is applied only at the top, by `cgcdFFCoreWf`). Bottoms at `CFracGcdCoreWf ℚ`. -/
class CFracGcdCoreWf (α : Type*) [CField α] where
  /-- The *raw* (content-normalized, non-monic) FUEL-FREE fraction-free gcd over `α[t]`. -/
  cgcdFFRawCoreWf : CPolyG α → CPolyG α → CPolyG α

namespace CFracGcdCoreWf

variable {α : Type*} [CField α] [CFracGcdCoreWf α]

/-- **The public monic FUEL-FREE fraction-free gcd** `cgcdFFCoreWf p q := cmonicG (cgcdFFRawCoreWf p q)`
over `α[t]`: monic-normalize the raw recursive fuel-free gcd. The fuel-free companion of
`CFracGcdCore.cgcdFFCore` — monic normalization happens once at the top, never inside the recursion. -/
def cgcdFFCoreWf (p q : CPolyG α) : CPolyG α := CPolyG.cmonicG (cgcdFFRawCoreWf p q)

end CFracGcdCoreWf

/-- **Base `CFracGcdCoreWf ℚ`** — the bottom of the tower. `ℚ[t]`'s raw fraction-free gcd is the
**fuel-free** generic Euclidean gcd `(CPolyG.cgcdWf p q).1` (the fuel-free companion of
`instCFracGcdCoreQ`'s `(cgcdExtG _).1`). -/
instance instCFracGcdCoreWfQ : CFracGcdCoreWf ℚ where
  cgcdFFRawCoreWf p q := (CPolyG.cgcdWf p q).1

section
variable {β : Type*} [CField β] [CFieldDomain β] [CFracGcdCoreWf β]

/-- **★ `CFracGcdCoreWf (QFunNZG β)`** — the *raw* FUEL-FREE fraction-free gcd over `β(s)[t]`, built by
running the fuel-free kernel `cprimPRSgcdGenCoreWf` over the GCD-domain `CPolyG β = β[s]` with the level-`β`
`cgcdFFRawCoreWf` as content-gcd. Clear denominators of both inputs into `GBPolyCore β = (β[s])[t]`, order
them by `t`-degree (the PRS needs the larger first), run the fuel-free primitive PRS with
`cgcdB := CFracGcdCoreWf.cgcdFFRawCoreWf` recursing one level down, and lift back to `β(s)[t]` — no
`cmonicG` (this is the raw method). Computable (`Prop`-erased subtype proofs), **no fuel at runtime**;
recurses strictly one level down, bottoming at `CFracGcdCoreWf ℚ`. -/
instance instCFracGcdCoreWfQFunNZG : CFracGcdCoreWf (QFunNZG β) where
  cgcdFFRawCoreWf p q :=
    let P := CPolyG.cclearDenomsCoreG p
    let Q := CPolyG.cclearDenomsCoreG q
    let (P, Q) := if GBPolyCore.gbdegCore P < GBPolyCore.gbdegCore Q then (Q, P) else (P, Q)
    CPolyG.liftGBPolyCoreG (GBPolyCore.cprimPRSgcdGenCoreWf CFracGcdCoreWf.cgcdFFRawCoreWf P Q)

end

/-- **`CFracGcdCoreWf QFunNZ`** — the *concrete* level-1 carrier (`ComputableField`'s `QFunNZ`). Its raw
fuel-free fraction-free gcd is the QFunNZ-specific `cgcdFFWf` (`ComputableWellFounded3`). Lets the generic
fuel-free integration pipeline instantiate at `α = QFunNZ` — the level-1 validation carrier — and run
**flat and fuel-free** there, matching the specialized `cIntegrateWf`. -/
instance instCFracGcdCoreWfQFunNZ : CFracGcdCoreWf QFunNZ where
  cgcdFFRawCoreWf p q := CPolyG.cgcdFFWf p q

/-! ### `native_decide` smoke tests for the fuel-free fraction-free gcd `cgcdFFCoreWf`

The whole fuel-free fraction-free gcd executes in native code over the generic tower carriers — every
`…Wf` op is `[CField α]`-only, so nothing noncomputable reaches the native compiler. -/

open QFunNZ

/-- `cgcdFFCoreWf` over the concrete level-1 carrier `QFunNZ` (ℚ(x)[t]): `gcd_t(t² − 1, t − 1)` is
degree-1 (an associate of `t − 1`, normalized length 2) — the whole fuel-free fraction-free gcd runs
end-to-end over ℚ(x). -/
example :
    (CFracGcdCoreWf.cgcdFFCoreWf [(ofConstNZ (-1)), ofConstNZ 0, ofConstNZ 1]
      [(ofConstNZ (-1)), ofConstNZ 1] : List QFunNZ).length = 2 := by native_decide

/-- `cgcdFFCoreWf` over the concrete level-1 carrier agrees with the fuel'd `cgcdFFCore` on
`gcd_t(t² − 1, t − 1)` (both monic) — the fuel-free flat fraction-free gcd matches the fuel'd one, tested
by `cisZeroG` of the difference over ℚ(x)[t] (`QFunNZ` has no `DecidableEq`). -/
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (CFracGcdCoreWf.cgcdFFCoreWf [(ofConstNZ (-1)), ofConstNZ 0, ofConstNZ 1]
        [(ofConstNZ (-1)), ofConstNZ 1])
      (CFracGcdCore.cgcdFFCore 4 [(ofConstNZ (-1)), ofConstNZ 0, ofConstNZ 1]
        [(ofConstNZ (-1)), ofConstNZ 1])) = true := by native_decide

end DeepWiki.SymbolicIntegration
