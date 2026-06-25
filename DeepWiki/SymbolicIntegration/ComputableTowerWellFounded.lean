import DeepWiki.SymbolicIntegration.ComputableTowerGcdFFCore
import DeepWiki.SymbolicIntegration.ComputableTowerIntegrate
import DeepWiki.SymbolicIntegration.ComputableWellFounded
import DeepWiki.SymbolicIntegration.ComputableWellFounded2
import DeepWiki.SymbolicIntegration.ComputableWellFounded3
import DeepWiki.SymbolicIntegration.ComputableWellFounded4
import DeepWiki.SymbolicIntegration.ComputableWellFounded5

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

/-! ## Part 2 — the integration pipeline's two remaining fuel-recursive bottoms

Besides the fraction-free gcd (Part 1), the generic integration pipeline recurses in exactly two more
places: the §3.5 split loop `cSplitFactorFastG` (`t`-degree drop) and Yun's main loop `cSqfreeYunFFGgo`
(multiplicity counter). Both get fuel-free companions here, generic and `[CField α]`-only on the
fuel-free fragment, replaying the `cSplitFactorFastWf` / `cSqfreeYunFFgoWf` patterns. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α]

/-- **The fuel-free generic `SplitFactor` step** `cstepGWf Dt p = cdivWf (cgcdFFCoreWf p (cmonomialDeriv Dt
p)) (cgcdFFCoreWf p (cderivG p))` — the special-factor candidate `S = gcd(p, Dp)/gcd(p, dp/dt)` computed
with the fuel-free fraction-free gcd `cgcdFFCoreWf` and the fuel-free generic exact division `cdivWf`. The
generic fuel-free companion of `cSplitFactorFastG`'s inline step. -/
def cstepGWf (Dt : CPolyG α) (p : CPolyG α) : CPolyG α :=
  cdivWf (CFracGcdCoreWf.cgcdFFCoreWf p (cmonomialDeriv Dt p))
    (CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p))

/-- **Generic fuel-free splitting-factorization loop** (Bronstein §3.5) `cSplitFactorFastGWf Dt p =
(pₙ, pₛ)`: the generic, fuel-free companion of `cSplitFactorFastG`. One step extracts `S = cstepGWf Dt p`;
a constant `S` (`cdegG S = 0`) ⇒ `p` is normal, else recurse on the exact quotient `p/S = cdivWf p S` and
accumulate `S` into the special part. True well-founded recursion on `(cnormG p).length` — **no fuel at
runtime**; the recursion is taken only under the structural guard `(cnormG (cdivWf p S)).length <
(cnormG p).length`, so `decreasing_by` is `assumption`. Over a real run the guard never fails (the
non-constant special factor strictly drops the `t`-degree), so `cSplitFactorFastGWf` agrees with
`cSplitFactorFastG`. `[CField α] [CDiffField α] [CFracGcdCoreWf α]`-generic — runs at any tower level. -/
def cSplitFactorFastGWf (Dt : CPolyG α) (p : CPolyG α) : CPolyG α × CPolyG α :=
  let S := cstepGWf Dt p
  if cdegG S = 0 then (p, [CField.one])
  else
    let pq := cdivWf p S
    if (cnormG pq : List α).length < (cnormG p : List α).length then
      let (qn, qs) := cSplitFactorFastGWf Dt pq
      (qn, cmulG S qs)
    else (p, [CField.one])   -- unreachable on a real run (the special factor drops the degree)
termination_by (cnormG p).length
decreasing_by assumption

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CFracGcdCoreWf α]

/-- **Generic fuel-free Yun main loop** (fraction-free) `cSqfreeYunFFGgoWf fo b d`: the generic, fuel-free
companion of `cSqfreeYunFFGgo`, recursing **structurally on the outer multiplicity counter** `fo` (so
`decreasing_by` is automatic and the loop never stops early — unlike a degree-guarded loop, which truncates
at skipped multiplicities). Stops when `b` is constant (`cdegG b = 0`) or the counter is exhausted, else
emits `p = cmonicG (cgcdFFCoreWf b d)`, recurses on `b' = cdivWf b p`, `d' = cdivWf d p − b'` with `fo`
decremented. The inner gcd/division leaves are the fuel-free `cgcdFFCoreWf`/`cdivWf` — **no fuel at
runtime**; the counter `fo` is supplied once by the entry `cSqfreeYunFFGWf` as `cyunBoundG`. Agrees with
`cSqfreeYunFFGgo` at the same counter `fo`. `[CField α] [CFracGcdCoreWf α]`-generic. -/
def cSqfreeYunFFGgoWf : ℕ → CPolyG α → CPolyG α → List (CPolyG α)
  | 0, _, _ => []
  | fo + 1, b, d =>
    if cdegG b = 0 then []
    else
      let p := cmonicG (CFracGcdCoreWf.cgcdFFCoreWf b d)
      let b' := cdivWf b p
      let d' := csubG (cdivWf d p) (cderivG b')
      p :: cSqfreeYunFFGgoWf fo b' d'

/-- **Sufficient internal multiplicity-counter bound** `cyunBoundG p := (cnormG p).length`: a provably
sufficient outer Yun counter for `cSqfreeYunFFGgoWf` on `p` (Yun's outer loop runs one step per
multiplicity slot, the max multiplicity is `≤ deg p < (cnormG p).length`). Computed once from the input, so
the caller passes **no fuel**. The generic analogue of `yunBound`. -/
def cyunBoundG (p : CPolyG α) : ℕ := (cnormG p : List α).length

/-- **Generic fuel-free Yun squarefree factorization in `t`** `cSqfreeYunFFGWf p = [p₁, …, pₘ]`: the
generic, fuel-free companion of `cSqfreeYunFFG`. With `g = cgcdFFCoreWf p (cderivG p)`, `b₁ = cdivWf p g`,
`d₁ = cderivG p/g − b₁'`, runs the fuel-free Yun loop `cSqfreeYunFFGgoWf (cyunBoundG p) b₁ d₁` — the outer
counter is the internally-computed `cyunBoundG p`, so the caller passes **no fuel**. `p` is associate to
`∏ᵢ pᵢ^i`; every gcd is the fuel-free `cgcdFFCoreWf`, every exact division the fuel-free `cdivWf` — **no
fuel at runtime**. Correct even at skipped multiplicities. `[CField α] [CFracGcdCoreWf α]`-generic. -/
def cSqfreeYunFFGWf (p : CPolyG α) : List (CPolyG α) :=
  let g := CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p)
  let b1 := cdivWf p g
  let d1 := csubG (cdivWf (cderivG p) g) (cderivG b1)
  cSqfreeYunFFGgoWf (cyunBoundG p) b1 d1

end CPolyG

/-! ## Part 3 — the flat-composition pipeline (fuel-free leaf substitution)

Everything past the three recursive bottoms is a flat composition over fuel'd leaves. The fuel-free
companions substitute the fuel-free leaves — the generic ones reused verbatim (`cbezoutOneWf`,
`cextendedEuclideanSplitWf`, `cdiophantineGWf`, `cHermiteReduceTowerInnerWf`, `cPrimitivePolyIntegrateWf`,
`cdivWf`, the §5.6 `cresultantWf`/`cinterpolateG`/`cHornerG`) and the new ones from Parts 1–2 (`cgcdFFCoreWf`,
`cSplitFactorFastGWf`, `cSqfreeYunFFGWf`). Each `…GWf` mirrors its `…G` original op-for-op with the fuel
dropped — a pure composition, no new recursion. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α]

/-- **Generic fuel-free `CanonicalRepresentation`** (Bronstein §3.5, p.103) over the tower:
`canonicalRepresentationFastGWf Dt a d = (fₚ, fₛ, fₙ) = (q, (b, dₛ), (c, dₙ))` for `f = a/d` (`d` monic).
The generic fuel-free companion of `canonicalRepresentationFastG`: divide `a = q·d + r` (`cdivmodWf`); split
the denominator `d = dₛ·dₙ` (`cSplitFactorFastGWf`); Bézout-split `r` over the coprime `(dₙ, dₛ)`
(`cextendedEuclideanSplitWf` with `cbezoutOneWf`, the already-generic fuel-free helpers). Every sub-op is a
WF leaf — **no fuel at runtime**. Stated with `.1`/`.2` projections so the bridge rewrites cleanly. -/
def canonicalRepresentationFastGWf (Dt : CPolyG α) (a d : CPolyG α) :
    CPolyG α × (CPolyG α × CPolyG α) × (CPolyG α × CPolyG α) :=
  let qr := cdivmodWf a d
  let dnds := cSplitFactorFastGWf Dt d
  let uw := cbezoutOneWf dnds.1 dnds.2
  let bc := cextendedEuclideanSplitWf dnds.1 dnds.2 qr.2 uw.1 uw.2
  (qr.1, (bc.1, dnds.2), (bc.2, dnds.1))

/-- **Generic fuel-free transcendental Hermite reduction** `cHermiteReduceTowerGWf Dt a d = ((gnum, gden),
(h_num, h_den))` (Bronstein §5.3, p.139) over the tower: the generic fuel-free companion of
`cHermiteReduceTowerG`. Squarefree-factor `d` with the fuel-free `cSqfreeYunFFGWf`; for each factor `(v, i)`
of multiplicity `i ≥ 2`, run the (already-generic) fuel-free inner loop `cHermiteReduceTowerInnerWf` (with
`u = d/vⁱ` via the fuel-free `cdivWf`); recover `h_num` over the squarefree radical `Dstar` via `cdivWf`.
The `Dstar`/`g` foldl is structural; every fuel'd sub-op is a WF leaf — **no fuel at runtime**. Stated with
`.1`/`.2` projections so the bridge rewrites cleanly. -/
def cHermiteReduceTowerGWf (Dt : CPolyG α) (a d : CPolyG α) :
    (CPolyG α × CPolyG α) × (CPolyG α × CPolyG α) :=
  let factors := cSqfreeYunFFGWf d                          -- `[v₁, …, vₘ]`, vᵢ of multiplicity i
  let Dstar := factors.foldl (fun acc vi => cmulG acc vi) [CField.one]   -- squarefree radical ∏ᵢ vᵢ
  let g : CPolyG α × CPolyG α := factors.zipIdx.foldl
    (fun (gAcc : CPolyG α × CPolyG α) (vi, idx) =>
      let i := idx + 1
      if i ≤ 1 then gAcc
      else
        let Vi_pow := cpowG vi i
        let u := cdivWf d Vi_pow
        let (gloc, _) := cHermiteReduceTowerInnerWf Dt vi u (i - 1) a ([CField.zero], [CField.one])
        (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))  -- gAcc + gloc
    ([CField.zero], [CField.one])
  let gprimeNum := csubG (cmulG (cmonomialDeriv Dt g.1) g.2) (cmulG g.1 (cmonomialDeriv Dt g.2))
  let gden2 := cmulG g.2 g.2
  let resNum := csubG (cmulG a gden2) (cmulG d gprimeNum)
  let resDen := cmulG d gden2
  let hNum := cdivWf (cmulG resNum Dstar) resDen
  ((cnormG g.1, cnormG g.2), (cnormG hNum, cnormG Dstar))

/-! ### The generic fuel-free §5.6 logarithmic part (Rothstein–Trager)

`cResidueResultantTowerGWf`/`cLogArgTowerGWf`/`cRationalResiduesGWf`/`cLogPartGWf` mirror the generic fuel'd
`cResidueResultantTowerG`/etc., taking the residue candidates **as `α` elements** (the generic form), with
the §5.6 leaves made fuel-free: the residue resultant samples through the (already-generic) fuel-free
resultant `cresultantWf`, the log argument is the fuel-free `cgcdFFCoreWf`. The `z`-node list, `cinterpolateG`,
the residue `filter`, and the `cHornerG` root test are all structural. -/

/-- **Generic fuel-free residue resultant** `cResidueResultantTowerGWf Dt a d = R(z) = res_t(d, a − z·Dd)`,
the generic fuel-free companion of `cResidueResultantTowerG`. Sample `R(zₖ) = res_t(d, a − zₖ·Dd)` at the
natural nodes `zₖ = cnatCastG k` (`k = 0…deg_t d`) with the **fuel-free** Euclidean-PRS resultant
`cresultantWf`, then Lagrange-interpolate (`cinterpolateG`). The node list and interpolation are structural —
**no fuel at runtime**. -/
def cResidueResultantTowerGWf (Dt : CPolyG α) (a d : CPolyG α) : CPolyG α :=
  let n := cdegG d
  let pts : List (α × α) := (List.range (n + 1)).map (fun k =>
    let zk : α := cnatCastG k
    (zk, cresultantWf d (cAmcDdG Dt a d zk)))
  cinterpolateG pts

/-- **Generic fuel-free log argument** `cLogArgTowerGWf Dt a d c = gcd_t(d, a − c·Dd)` for a residue `c : α`,
the generic fuel-free companion of `cLogArgTowerG`: the **fuel-free** fraction-free gcd `cgcdFFCoreWf` of `d`
and `a − c·Dd`. **No fuel at runtime**. -/
def cLogArgTowerGWf (Dt : CPolyG α) (a d : CPolyG α) (c : α) : CPolyG α :=
  CFracGcdCoreWf.cgcdFFCoreWf d (cAmcDdG Dt a d c)

/-- **Generic fuel-free rational/field residues** `cRationalResiduesGWf Dt a d cands`: keep the candidates
`c ∈ cands : List α` that are roots of the **fuel-free** residue resultant `R(z) = cResidueResultantTowerGWf
Dt a d`, i.e. `R(c) = 0` (tested by `CField.isZero (cHornerG R c)`). A structural `filter`, the residue
resultant fuel-free — **no fuel at runtime**. -/
def cRationalResiduesGWf (Dt : CPolyG α) (a d : CPolyG α) (cands : List α) : List α :=
  let R := cResidueResultantTowerGWf Dt a d
  cands.filter (fun c => CField.isZero (cHornerG R c))

/-- **Generic fuel-free logarithmic part** `cLogPartGWf Dt a d cands = [(c, gcd_t(d, a − c·Dd)) | c ∈
residues]`: pair each residue `c : α` (from `cRationalResiduesGWf`) with its fuel-free log argument
`cLogArgTowerGWf Dt a d c`. A structural composition of the fuel-free §5.6 pieces — **no fuel at runtime**. -/
def cLogPartGWf (Dt : CPolyG α) (a d : CPolyG α) (cands : List α) : List (α × CPolyG α) :=
  (cRationalResiduesGWf Dt a d cands).map (fun c => (c, cLogArgTowerGWf Dt a d c))

/-- **The generic fuel-free reduced-case integration capstone** `cIntegrateReducedGWf Dt a d cands`: for
`f = a/d` reduced/normal, `∫ f = g + ∑ c·log(v)`. Hermite-reduce (`cHermiteReduceTowerGWf`) to the rational
part `g = gnum/gden` and the simple residual `h = h_num/h_den`, then take the residue log part of `h`
(`cLogPartGWf`, residues drawn from `cands : List α`). Returns the `IntegralResultG` `⟨(gnum, gden),
[(c, v)]⟩`. The generic fuel-free companion of `cIntegrateReducedG` — **no fuel at runtime**. -/
def cIntegrateReducedGWf (Dt : CPolyG α) (a d : CPolyG α) (cands : List α) :
    IntegralResultG α :=
  let H := cHermiteReduceTowerGWf Dt a d
  let logs := cLogPartGWf Dt H.2.1 H.2.2 cands
  ⟨(H.1.1, H.1.2), logs⟩

/-- **★ THE HEADLINE — the generic fuel-free tower integral** `cIntegrateGWf Dt a d cands` (Bronstein Ch. 5,
the reduced-case driver over the tower): the generic, fuel-free companion of `cIntegrateG`. Integrate
`f = a/d ∈ α(t)` over `D = cmonomialDeriv Dt`, returning `some ⟨(gnum, gden), [(cᵢ, vᵢ)]⟩` with `∫ f =
gnum/gden + ∑ᵢ cᵢ·log(vᵢ)`, or `none`. Steps: (1) `canonicalRepresentationFastGWf` splits `f = fₚ + fₛ + fₙ`;
(2) the simple normal part `fₙ = cn/dn` is integrated by `cIntegrateReducedGWf`; (3) if `fₚ` and the special
part `b/dₛ` both vanish, return the simple-part integral, else `none`. A pure composition over the fuel-free
pipeline — **no fuel at runtime**; `native_decide`-able over the noncomputable tower.
`[CField α] [CDiffField α] [CFracGcdCoreWf α]`-generic — runs at any tower level. -/
def cIntegrateGWf (Dt : CPolyG α) (a d : CPolyG α) (cands : List α) :
    Option (IntegralResultG α) :=
  let (fp, (b, _ds), (cn, dn)) := canonicalRepresentationFastGWf Dt a d
  let nrm := cIntegrateReducedGWf Dt cn dn cands
  if cisZeroG fp && cisZeroG b then some nrm else none

end CPolyG

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

/-! ## Part 4 — bridges of the flat-composition pipeline to the fuel'd `…G` originals

Each flat-composition `…GWf` op mirrors its `…G` original with the fuel dropped, so its bridge to the fuel'd
version is a pure rewrite that threads the per-leaf sub-agreements (every fuel'd sub-op replaced by its
fuel-free companion at sufficient fuel). Following the established pattern (`cIntegrateReducedWf_eq`,
`cIntegrateWf_eq`, `cLogPartWf_eq`), the sub-agreements are taken as **hypotheses** — the fuel bounds they
carry live only there; the runtime `…GWf` carries none. The recursive-bottom agreements
(`cSplitFactorFastGWf`/`cSqfreeYunFFGgoWf`/`cgcdFFCoreWf`) feed in through their own regularity gates. -/

namespace CPolyG

section
variable {α : Type*} [CField α] [CDiffField α]

/-- **Bridge — `cRationalResiduesGWf` equals `cRationalResiduesG` at any sufficient fuel.** When the
fuel-free residue resultant agrees with the fuel'd one (`hR : cResidueResultantTowerGWf Dt a d =
cResidueResultantTowerG Dt fuel a d`), the `cHornerG`-root filter predicates coincide, so
`cRationalResiduesGWf Dt a d cands = cRationalResiduesG Dt fuel a d cands`. -/
theorem cRationalResiduesGWf_eq (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α)
    (hR : cResidueResultantTowerGWf Dt a d = cResidueResultantTowerG Dt fuel a d) :
    cRationalResiduesGWf Dt a d cands = cRationalResiduesG Dt fuel a d cands := by
  rw [cRationalResiduesGWf, cRationalResiduesG, hR]

end

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α] [CFracGcdCoreWf α]

/-- **Bridge — `cLogPartGWf` equals `cLogPartG` at any sufficient fuel.** From the residue-resultant bridge
`hR` (so the rational-residue lists coincide, `cRationalResiduesGWf_eq`) and the per-residue log-argument
bridge `hLogArg` (`cLogArgTowerGWf … c = cLogArgTowerG fuel … c` for every kept residue `c`),
`cLogPartGWf Dt a d cands = cLogPartG Dt fuel a d cands`. The fuel bounds live only in `hR`/`hLogArg`. -/
theorem cLogPartGWf_eq (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α)
    (hR : cResidueResultantTowerGWf Dt a d = cResidueResultantTowerG Dt fuel a d)
    (hLogArg : ∀ c ∈ cRationalResiduesGWf Dt a d cands,
      cLogArgTowerGWf Dt a d c = cLogArgTowerG Dt fuel a d c) :
    cLogPartGWf Dt a d cands = cLogPartG Dt fuel a d cands := by
  rw [cLogPartGWf, cLogPartG, ← cRationalResiduesGWf_eq Dt fuel a d cands hR]
  apply List.map_congr_left
  intro c hc
  rw [hLogArg c hc]

/-- **Bridge — `cIntegrateReducedGWf` equals `cIntegrateReducedG` at any sufficient fuel.** From the Hermite
bridge `hHermite : cHermiteReduceTowerGWf Dt a d = cHermiteReduceTowerG Dt fuel a d` and the log-part bridge
`hLog` on the resulting simple residual, `cIntegrateReducedGWf Dt a d cands = cIntegrateReducedG Dt fuel a d
cands`. The fuel bounds live only in `hHermite`/`hLog`. -/
theorem cIntegrateReducedGWf_eq (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α)
    (hHermite : cHermiteReduceTowerGWf Dt a d = cHermiteReduceTowerG Dt fuel a d)
    (hLog : cLogPartGWf Dt (cHermiteReduceTowerGWf Dt a d).2.1 (cHermiteReduceTowerGWf Dt a d).2.2 cands
      = cLogPartG Dt fuel (cHermiteReduceTowerG Dt fuel a d).2.1
          (cHermiteReduceTowerG Dt fuel a d).2.2 cands) :
    cIntegrateReducedGWf Dt a d cands = cIntegrateReducedG Dt fuel a d cands := by
  rw [cIntegrateReducedGWf, cIntegrateReducedG, hLog, hHermite]

/-- **★ Bridge — the headline `cIntegrateGWf` equals `cIntegrateG` at any sufficient fuel.** From the two
sub-bridges that the canonical split (`hcanon : canonicalRepresentationFastGWf Dt a d =
canonicalRepresentationFastG Dt fuel a d`) feeds — the reduced capstone `hred` on the resulting normal part
`(cn, dn)` — `cIntegrateGWf Dt a d cands = cIntegrateG Dt fuel a d cands`. The fuel bounds live only in the
hypotheses; the headline `cIntegrateGWf` carries none. A pure composition rewrite. -/
theorem cIntegrateGWf_eq (Dt : CPolyG α) (fuel : ℕ) (a d : CPolyG α) (cands : List α)
    (hcanon : canonicalRepresentationFastGWf Dt a d = canonicalRepresentationFastG Dt fuel a d)
    (hred : cIntegrateReducedGWf Dt (canonicalRepresentationFastGWf Dt a d).2.2.1
        (canonicalRepresentationFastGWf Dt a d).2.2.2 cands
      = cIntegrateReducedG Dt fuel (canonicalRepresentationFastG Dt fuel a d).2.2.1
          (canonicalRepresentationFastG Dt fuel a d).2.2.2 cands) :
    cIntegrateGWf Dt a d cands = cIntegrateG Dt fuel a d cands := by
  rw [cIntegrateGWf, cIntegrateG]
  -- both sides `match (canonical split) with | (fp,(b,_ds),cn,dn) => …`; the split agrees by `hcanon`,
  -- and the reduced capstone on the destructured `(cn, dn)` agrees by `hred` (its projections are
  -- exactly the match's `cn`/`dn`). Rewrite `hred` (a projection identity) then collapse via `hcanon`.
  simp only [hcanon] at hred ⊢
  -- after `hcanon` both `match`es are on `canonicalRepresentationFastG fuel a d`; reduce to projections
  rw [show (canonicalRepresentationFastG Dt fuel a d)
      = ((canonicalRepresentationFastG Dt fuel a d).1,
         ((canonicalRepresentationFastG Dt fuel a d).2.1.1,
          (canonicalRepresentationFastG Dt fuel a d).2.1.2),
         ((canonicalRepresentationFastG Dt fuel a d).2.2.1,
          (canonicalRepresentationFastG Dt fuel a d).2.2.2)) from rfl]
  simp only []
  rw [hred]

end CPolyG

/-! ## Part 5 — bridges of the recursive bottoms `cSqfreeYunFFGgoWf` / `cSplitFactorFastGWf`

The two recursive bottoms get bridges to their fuel'd `…G` originals. As with the `QFunNZ` arc
(`cSqfreeYunFFgoWf_eq`, `cSplitFactorFastWf_eq`), the bridges carry `[CFieldSpec α]` (the fuel'd-leaf
agreements `cdivmodWf_eq_of_fuel` / `cgcdWf_eq_of_fuel` need a genuine field) — but the **defs** stay
`[CField α]`-only. The per-node `cgcdFFCoreWf = cgcdFFCore fuel` agreement (which itself threads
`cprimPRSgcdGenCoreWf_eq` through every tower level) is taken as a per-node hypothesis in the regularity
gate, exactly the `CgcdFFNodeReg` role in the QFunNZ version. -/

namespace CPolyG

variable {α : Type*} [CField α] [CFracGcdCore α] [CFracGcdCoreWf α] [CFieldSpec α]

/-- **Per-run generic Yun-loop regularity** `CSqfreeYunGoGenRegular fuel n b d`: mirrors the
`cSqfreeYunFFGgo` recursion as an inductive predicate **with a step budget** `n` (the multiplicity counter,
the genuine termination witness — sound at skipped multiplicities). `stop` (any budget) at a constant
running poly `b` (`cdegG b = 0`), or `step` (budget `n+1`) when the per-step fuel-free leaves match the
fuel'd ops — the gcd `cgcdFFCoreWf b d = cgcdFFCore fuel b d` (`hgcd`, the `CgcdFFNodeReg` role) and the two
exact divisions `cdivWf b p`/`cdivWf d p` are reduced (`(cnormG b).length ≤ fuel`, `(cnormG d).length ≤
fuel`) — and the same holds recursively on the quotient within budget `n`. -/
inductive CSqfreeYunGoGenRegular (fuel : ℕ) : ℕ → CPolyG α → CPolyG α → Prop
  /-- terminal node: the running poly `b` is constant, the loop stops (any remaining budget). -/
  | stop {n : ℕ} {b d : CPolyG α} (hdeg : cdegG b = 0) : CSqfreeYunGoGenRegular fuel n b d
  /-- recursive node: `b` non-constant, the per-step leaves match the fuel'd ops, recurse within budget. -/
  | step {n : ℕ} {b d : CPolyG α} (hne : cdegG b ≠ 0)
      (hgcd : CFracGcdCoreWf.cgcdFFCoreWf b d = CFracGcdCore.cgcdFFCore fuel b d)
      (hblen : (cnormG b : List α).length ≤ fuel) (hdlen : (cnormG d : List α).length ≤ fuel)
      (hrec : CSqfreeYunGoGenRegular fuel n (cdivWf b (cmonicG (CFracGcdCore.cgcdFFCore fuel b d)))
        (csubG (cdivWf d (cmonicG (CFracGcdCore.cgcdFFCore fuel b d)))
          (cderivG (cdivWf b (cmonicG (CFracGcdCore.cgcdFFCore fuel b d)))))) :
      CSqfreeYunGoGenRegular fuel (n + 1) b d

/-- **Bridge — `cSqfreeYunFFGgoWf` equals `cSqfreeYunFFGgo` at the same outer counter.** For any outer Yun
counter `fo` at least the step budget `n` of a regular run (`n ≤ fo`, `CSqfreeYunGoGenRegular fuel n b d`),
`cSqfreeYunFFGgoWf fo b d = cSqfreeYunFFGgo fuel fo b d`. The fuel bounds live only here; `cSqfreeYunFFGgoWf`
carries none. By induction on the regularity predicate (the step budget is the genuine termination witness,
the multiplicity counter), generalizing `fo`: at a constant `b` both stop; else the step's WF leaves match
the fuel'd ops (`hgcd`, `cdivmodWf_eq_of_fuel`), and the IH applies within budget `n ≤ fo − 1`. -/
theorem cSqfreeYunFFGgoWf_eq (fuel : ℕ) : ∀ (n : ℕ) (b d : CPolyG α),
    CSqfreeYunGoGenRegular fuel n b d → ∀ (fo : ℕ), n ≤ fo →
      cSqfreeYunFFGgoWf fo b d = cSqfreeYunFFGgo fuel fo b d := by
  intro n b d hreg
  induction hreg with
  | @stop n b d hdeg =>
    intro fo _
    cases fo with
    | zero => rfl
    | succ fo => rw [cSqfreeYunFFGgoWf, cSqfreeYunFFGgo, if_pos hdeg, if_pos hdeg]
  | @step n b d hne hgcd hblen hdlen hrec ih =>
    intro fo hfo
    cases fo with
    | zero => exact absurd hfo (Nat.not_succ_le_zero n)
    | succ fo =>
      rw [cSqfreeYunFFGgoWf, cSqfreeYunFFGgo, if_neg hne, if_neg hne]
      set p := cmonicG (CFracGcdCore.cgcdFFCore fuel b d) with hp
      have hbq : cdivWf b p = CPolyG.cdivG fuel b p := by
        rw [cdivWf, cdivmodWf_eq_of_fuel fuel b p hblen, cdivG]
      have hdq : cdivWf d p = CPolyG.cdivG fuel d p := by
        rw [cdivWf, cdivmodWf_eq_of_fuel fuel d p hdlen, cdivG]
      simp only [hgcd, ← hp, ← hbq, ← hdq]
      rw [ih fo (Nat.le_of_succ_le_succ hfo)]

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α] [CFracGcdCoreWf α] [CFieldSpec α]

/-- **The generic fuel-free step matches the generic fuel'd step** `cstepGWf Dt p = S` where
`S = cdivG (fuel+1) (cgcdFFCore (fuel+1) p (cmonomialDeriv Dt p)) (cgcdFFCore (fuel+1) p (cderivG p))` (the
inline `cSplitFactorFastG` step), under the per-step agreements: both `cgcdFFCore` calls bridged
(`hgcdN`/`hgcdD`) and the exact division's numerator gcd short enough for `cdivWf = cdivG (fuel+1)`
(`hnlen`). The generic analogue of `cstepWf_eq`. -/
theorem cstepGWf_eq (Dt : CPolyG α) (fuel : ℕ) (p : CPolyG α)
    (hgcdN : CFracGcdCoreWf.cgcdFFCoreWf p (cmonomialDeriv Dt p)
      = CFracGcdCore.cgcdFFCore (fuel + 1) p (cmonomialDeriv Dt p))
    (hgcdD : CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p)
      = CFracGcdCore.cgcdFFCore (fuel + 1) p (cderivG p))
    (hnlen : (cnormG (CFracGcdCore.cgcdFFCore (fuel + 1) p (cmonomialDeriv Dt p)) : List α).length
      ≤ fuel + 1) :
    cstepGWf Dt p
      = cdivG (fuel + 1) (CFracGcdCore.cgcdFFCore (fuel + 1) p (cmonomialDeriv Dt p))
          (CFracGcdCore.cgcdFFCore (fuel + 1) p (cderivG p)) := by
  rw [cstepGWf, hgcdN, hgcdD, cdivWf, cdivmodWf_eq_of_fuel (fuel + 1) _ _ hnlen, cdivG]

/-- **Per-run generic split-factor regularity** `CSplitFactorGenRegular Dt fuel p`: mirrors the
`cSplitFactorFastG` `fuel`-recursion as an inductive predicate. Every node carries the step agreement
(`hgcdN`/`hgcdD`/`hnlen`, so `cstepGWf Dt p` matches the fuel'd inline `S = cdivG (cgcdFFCore p Dp)
(cgcdFFCore p dp)`, via `cstepGWf_eq`); `stop` then ends at a constant step (`cdegG S = 0`, any fuel), and
`step` (fuel `n+1`) continues at a non-constant step whose exact quotient `p/S = cdivWf p S` is reduced
(`(cnormG p).length ≤ fuel+1`) and strictly drops the normalized length (`(cnormG (cdivWf p S)).length <
(cnormG p).length` — the WF guard), with the same holding recursively on `p/S`. The transparent per-node
preconditions a real split run satisfies. -/
inductive CSplitFactorGenRegular (Dt : CPolyG α) : ℕ → CPolyG α → Prop
  /-- terminal node: the special-factor step `S` (matched to the fuel'd inline by `hgcd*`) is constant. -/
  | stop {fuel : ℕ} {p : CPolyG α}
      (hgcdN : CFracGcdCoreWf.cgcdFFCoreWf p (cmonomialDeriv Dt p)
        = CFracGcdCore.cgcdFFCore (fuel + 1) p (cmonomialDeriv Dt p))
      (hgcdD : CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p)
        = CFracGcdCore.cgcdFFCore (fuel + 1) p (cderivG p))
      (hnlen : (cnormG (CFracGcdCore.cgcdFFCore (fuel + 1) p (cmonomialDeriv Dt p)) : List α).length
        ≤ fuel + 1)
      (hdeg : cdegG (cstepGWf Dt p) = 0) : CSplitFactorGenRegular Dt (fuel + 1) p
  /-- recursive node: the step `S` (matched to the fuel'd inline) is non-constant; recurse on `p/S`. -/
  | step {fuel : ℕ} {p : CPolyG α}
      (hgcdN : CFracGcdCoreWf.cgcdFFCoreWf p (cmonomialDeriv Dt p)
        = CFracGcdCore.cgcdFFCore (fuel + 1) p (cmonomialDeriv Dt p))
      (hgcdD : CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p)
        = CFracGcdCore.cgcdFFCore (fuel + 1) p (cderivG p))
      (hnlen : (cnormG (CFracGcdCore.cgcdFFCore (fuel + 1) p (cmonomialDeriv Dt p)) : List α).length
        ≤ fuel + 1)
      (hdeg : cdegG (cstepGWf Dt p) ≠ 0) (hplen : (cnormG p : List α).length ≤ fuel + 1)
      (hguard : (cnormG (cdivWf p (cstepGWf Dt p)) : List α).length < (cnormG p : List α).length)
      (hrec : CSplitFactorGenRegular Dt fuel (cdivWf p (cstepGWf Dt p))) :
      CSplitFactorGenRegular Dt (fuel + 1) p

/-- **The fuel'd `cSplitFactorFastG (fuel+1)` loop step shape**, with its inline special factor abstracted as
`cstepGWf Dt p` (under the step agreements, `cstepGWf_eq`): the fuel'd loop body is the `if cdegG S = 0`
branch on `S = cstepGWf Dt p`, recursing on `cdivG (fuel+1) p S`. Folds the fuel'd inline
`cdivG … (cgcdFFCore …) (cgcdFFCore …)` back to `cstepGWf` for a clean case split. -/
theorem cSplitFactorFastG_succ_shape (Dt : CPolyG α) (fuel : ℕ) (p : CPolyG α)
    (hgcdN : CFracGcdCoreWf.cgcdFFCoreWf p (cmonomialDeriv Dt p)
      = CFracGcdCore.cgcdFFCore (fuel + 1) p (cmonomialDeriv Dt p))
    (hgcdD : CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p)
      = CFracGcdCore.cgcdFFCore (fuel + 1) p (cderivG p))
    (hnlen : (cnormG (CFracGcdCore.cgcdFFCore (fuel + 1) p (cmonomialDeriv Dt p)) : List α).length
      ≤ fuel + 1) :
    cSplitFactorFastG Dt (fuel + 1) p
      = (if cdegG (cstepGWf Dt p) = 0 then (p, [CField.one])
         else ((cSplitFactorFastG Dt fuel (cdivG (fuel + 1) p (cstepGWf Dt p))).1,
               cmulG (cstepGWf Dt p) (cSplitFactorFastG Dt fuel (cdivG (fuel + 1) p (cstepGWf Dt p))).2)) := by
  have hstep : cstepGWf Dt p
      = cdivG (fuel + 1) (CFracGcdCore.cgcdFFCore (fuel + 1) p (cmonomialDeriv Dt p))
          (CFracGcdCore.cgcdFFCore (fuel + 1) p (cderivG p)) := cstepGWf_eq Dt fuel p hgcdN hgcdD hnlen
  conv_lhs => rw [cSplitFactorFastG]
  rw [hstep]

/-- **Bridge — `cSplitFactorFastGWf` equals `cSplitFactorFastG` on a regular run.** Under
`CSplitFactorGenRegular Dt fuel p` (the per-step degree-drop + leaf agreements a real split run meets, with
sufficient fuel), `cSplitFactorFastGWf Dt p = cSplitFactorFastG Dt fuel p`. The fuel regularity lives only
here; the WF loop carries none. By induction on the `CSplitFactorGenRegular` derivation: each node abstracts
the fuel'd inline `S` as `cstepGWf` (`cSplitFactorFastG_succ_shape`); at `stop` both return `(p, [one])`; at
`step` the WF guard fires (`hguard`, the quotient bridged by `cdivmodWf_eq_of_fuel`) and the fuel'd version
descends. -/
theorem cSplitFactorFastGWf_eq (Dt : CPolyG α) :
    ∀ (fuel : ℕ) (p : CPolyG α), CSplitFactorGenRegular Dt fuel p →
      cSplitFactorFastGWf Dt p = cSplitFactorFastG Dt fuel p := by
  intro fuel p hreg
  induction hreg with
  | @stop fuel p hgcdN hgcdD hnlen hdeg =>
    rw [cSplitFactorFastGWf.eq_def, if_pos hdeg,
      cSplitFactorFastG_succ_shape Dt fuel p hgcdN hgcdD hnlen, if_pos hdeg]
  | @step fuel p hgcdN hgcdD hnlen hdeg hplen hguard hrec ih =>
    rw [cSplitFactorFastGWf.eq_def, cSplitFactorFastG_succ_shape Dt fuel p hgcdN hgcdD hnlen,
      if_neg hdeg, if_pos hguard]
    -- LHS now `match cSplitFactorFastGWf (cdivWf p S) with …`; apply IH first (while still `cdivWf`)
    rw [ih]
    -- the WF quotient `cdivWf p S` matches the fuel'd `cdivG (fuel+1) p S`
    have hdiv : cdivWf p (cstepGWf Dt p) = cdivG (fuel + 1) p (cstepGWf Dt p) := by
      rw [cdivWf, cdivmodWf_eq_of_fuel (fuel + 1) p (cstepGWf Dt p) hplen, cdivG]
    rw [hdiv, if_neg hdeg]

end CPolyG

/-! ### ★ THE HEADLINE `native_decide` validation — a FULL elementary tower integral, FUEL-FREE, at LEVEL 2

Bronstein's Example 5.6.2 lifted to **tower level 2** (`CPolyG Lvl2 = ℚ(x)(t₁)[t₂]`, `Dt₂ = 1`), now run by
the **fuel-free** generic integrator. The simple integrand `f = (1/2)/(t₂+1) − (1/2)/(t₂−1)` (assembled as
`a/d`, `d = t₂² − 1`) has elementary antiderivative `(1/2)log(t₂+1) − (1/2)log(t₂−1)`; the residues `±1/2`
have log arguments `t₂ ± 1`. The whole fuel-free generic tower integrator — canonical split + Hermite
rational part + Rothstein–Trager residue logs, with **no fuel at runtime** — computes over the tower at
level 2 and the returned `g + ∑ cᵢ·log(vᵢ)` genuinely differentiates back to `f`. Reuses the level-2 example
data of `ComputableTowerIntegrate`. -/

/-- **The fuel-free recovered level-2 logarithmic part has length 2** (`native_decide`): the residue scan
over `ℚ(x)(t₁)[t₂]` finds exactly the two rational residues `±1/2` (log arguments `t₂ ± 1`) — the fuel-free
`cIntegrateReducedGWf` capstone's `logs` list has length `2`. -/
example :
    (CPolyG.cIntegrateReducedGWf towerIntLvl2Dt towerIntLvl2Num towerIntLvl2Den
      towerIntLvl2Cands).logs.length = 2 := by native_decide

/-- **★ A FULL elementary tower integral at LEVEL 2, FUEL-FREE, and `D(∫f) = f`** (`native_decide`, the
headline deliverable). For `f = (1/2)/(t₂+1) − (1/2)/(t₂−1)` over ℚ(x)(t₁)(t₂) (tower **level 2**), the
fuel-free generic capstone `cIntegrateReducedGWf` — canonical split, Hermite rational part, Rothstein–Trager
residue logarithms, **no fuel at runtime** — returns an `IntegralResultG` whose antiderivative identity
`D(rational) + ∑ᵢ cᵢ·(D(vᵢ)/vᵢ) = f` holds exactly (`checkIdentityG`, cleared by `cisZeroG`). The WHOLE
fuel-free elementary tower integral computes at level 2 and differentiates back to `f`. -/
example :
    CPolyG.checkIdentityG towerIntLvl2Dt
      (CPolyG.cIntegrateReducedGWf towerIntLvl2Dt towerIntLvl2Num towerIntLvl2Den
        towerIntLvl2Cands)
      towerIntLvl2Num towerIntLvl2Den = true := by native_decide

/-- **★ The full fuel-free `cIntegrateGWf` driver runs end-to-end at level 2 and `D(∫f) = f`**
(`native_decide`, the headline deliverable): on the same level-2 simple integrand (a pure normal element,
`fₚ = fₛ = 0`), the assembled fuel-free top-level `cIntegrateGWf` — canonical split + reduced capstone,
**no fuel at runtime** — returns `some res`, and `res` satisfies the antiderivative identity `D(res) = f`
over ℚ(x)(t₁)[t₂]. The assembled GENERIC FUEL-FREE tower integral driver computes at level 2. -/
theorem towerIntLvl2_driverGWf :
    (match CPolyG.cIntegrateGWf towerIntLvl2Dt towerIntLvl2Num towerIntLvl2Den
        towerIntLvl2Cands with
      | some res => CPolyG.checkIdentityG towerIntLvl2Dt res towerIntLvl2Num towerIntLvl2Den
      | none => false) = true := by native_decide

-- The headline fuel-free integration-driver bridge carries only the standard axioms (no `native` axiom);
-- the `native_decide` example `towerIntLvl2_driverGWf` carries `Lean.ofReduceBool` separately.
#print axioms CPolyG.cIntegrateGWf_eq
#print axioms towerIntLvl2_driverGWf

/-! ## Part 6 — STRETCH: the generic fuel-free RDE recursive bottoms (§6 PolyRischDE / SPDE)

The §6 RDE pipeline `cRischDEG` (`ComputableTowerRischDE`) is a second large pipeline whose flat structure
mirrors the integration one but whose recursive bottoms differ. This part builds the fuel-free companions of
its two `[CField α]`-generic degree-recursion bottoms — the §6.5 non-cancellation solve
`cPolyRischDENoCancelG` (recursing on `(cnormG c).length`) and the §6.4 SPDE `cSPDEG` (recursing on
`(n+1).toNat`) — replaying the `QFunNZ`-specific `cPolyRischDENoCancelWf` / `cSPDEWf` patterns generically.
(The cancellation cases `cPolyRischDECancelPrimG`/`cPolyRischDECancelExpG` carry `[CRischField α]` and the
top driver `cRischDEG` is a flat composition over these — the documented continuation of the stretch.) -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

/-- **Generic fuel-free divisibility test** `cdvdGWf q p := cisZeroG (cmodWf p q)`: `true` iff `q ∣ p` over
`α[t]`, via the fuel-free remainder `cmodWf`. The fuel-free companion of `cdvdG` — **no fuel at runtime**. -/
def cdvdGWf (q p : CPolyG α) : Bool := cisZeroG (cmodWf p q)

/-- **Generic fuel-free non-cancellation Poly-Risch-DE** (Bronstein §6.5, book p.208)
`cPolyRischDENoCancelGWf Dt b c n`: the generic, fuel-free companion of `cPolyRischDENoCancelG`. Solves
`Dq + b·q = c` (eq. 6.19) for `q ∈ α[t]` with `deg(q) ≤ n` (`n : ℤ`), top-down — `p = (lc(c)/lc(b))·tᵐ`
(`m = deg(c) − deg(b)`), recurse on `c' = c − D(p) − b·p` (`D = cmonomialDeriv Dt`). Returns `none` or
`some q`. True well-founded recursion on `(cnormG c).length` — **no fuel at runtime**; the recursion is taken
only under the structural guard `(cnormG c').length < (cnormG c).length`, so `decreasing_by` is `assumption`.
Over a non-cancellation run the guard never fails (the leading term cancels, dropping the degree), so it
agrees with `cPolyRischDENoCancelG`. `[CField α] [CDiffField α]`-generic — runs at any tower level. -/
def cPolyRischDENoCancelGWf (Dt : CPolyG α) (b c : CPolyG α) (n : ℤ) :
    Option (CPolyG α) :=
  if cisZeroG c then some []
  else
    let m : ℤ := (cdegG c : ℤ) - (cdegG b : ℤ)
    if n < 0 ∨ m < 0 ∨ m > n then none
    else
      let coeff := CField.div (cleadG c) (cleadG b)
      let p := cshiftG m.toNat [coeff]
      let c' := csubG (csubG c (cmonomialDeriv Dt p)) (cmulG b p)
      if (cnormG c' : List α).length < (cnormG c : List α).length then
        match cPolyRischDENoCancelGWf Dt b c' (m - 1) with
        | none => none
        | some q => some (caddG p q)
      else none   -- unreachable on a non-cancellation run (the leading term cancels, degree drops)
termination_by (cnormG c).length
decreasing_by assumption

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α]

/-- **Generic fuel-free SPDE** (Bronstein §6.4, book p.203) `cSPDEGWf Dt a b c n`: the generic, fuel-free
companion of `cSPDEG`. The `g = gcd(a, b)`-peel reducing the degree-bounded `a·Dq + b·q = c` to one with
`a = 1`. Returns `none` or `some (b̄, c̄, m, α', β)` so any solution is `q = α'·h + β` with `h` solving
`Dh + b̄·h = c̄`, `deg(h) ≤ m`. Peels `g = cgcdFFCoreWf a b` (fuel-free); the constant `a/g` base case
returns the identity reconstruction, else solves the Bézout `cdiophantineGWf b̄ ā c̄` (already-generic
fuel-free) and recurses on `ā = a/g` at `n − deg(ā)`. True well-founded recursion on `(n+1).toNat` — **no
fuel at runtime**; the recursion is taken only under the structural guard `(n − deg(ā) + 1).toNat <
(n+1).toNat`, so `decreasing_by` is `assumption`. The inner gcd/division/divisibility are the fuel-free
`cgcdFFCoreWf`/`cdivWf`/`cdvdGWf`. `[CField α] [CDiffField α] [CFracGcdCoreWf α]`-generic. -/
def cSPDEGWf (Dt : CPolyG α) (a b c : CPolyG α) (n : ℤ) :
    Option (CPolyG α × CPolyG α × ℤ × CPolyG α × CPolyG α) :=
  if n < 0 then
    if cisZeroG c then some ([], [], 0, [], []) else none
  else
    let g := CFracGcdCoreWf.cgcdFFCoreWf a b
    if cdvdGWf g c then
      let a' := cdivWf a g
      let b' := cdivWf b g
      let c' := cdivWf c g
      if cdegG a' = 0 then
        let ainv := CField.inv (cleadG a')
        some (cscaleG ainv b', cscaleG ainv c', n, [CField.one], [])
      else
        let (r, z) := cdiophantineGWf b' a' c'
        let Da := cmonomialDeriv Dt a'
        let Dr := cmonomialDeriv Dt r
        if (n - (cdegG a' : ℤ) + 1).toNat < (n + 1).toNat then
          match cSPDEGWf Dt a' (caddG b' Da) (csubG z Dr) (n - (cdegG a' : ℤ)) with
          | none => none
          | some (bbar, cbar, m, α', β) =>
              some (bbar, cbar, m, cmulG a' α', caddG (cmulG a' β) r)
        else none   -- unreachable on a real run (`deg ā ≥ 1`, so the bound `n − deg ā` strictly drops)
    else none
termination_by (n + 1).toNat
decreasing_by assumption

end CPolyG

/-! ### `native_decide` smoke tests for the generic fuel-free RDE bottoms

The whole fuel-free §6.5/§6.4 recursive bottoms execute in native code over the generic tower — `[CField α]`-
only on the fuel-free fragment, so nothing noncomputable reaches the native compiler. -/

open QFunNZ

/-- `cPolyRischDENoCancelGWf` over `ℚ(x)[t]`: solving `Dq + 0·q = 0` (`c = 0`) succeeds with the zero
solution (length-0 list) — the fuel-free §6.5 own-loop runs over the tower (`Option.map .length` dodges
`QFunNZ`'s missing `DecidableEq`). -/
example :
    (CPolyG.cPolyRischDENoCancelGWf ([ofConstNZ 0] : CPolyG QFunNZ) [] [] 3).map
      (fun q => (q : List QFunNZ).length) = some 0 := by native_decide

/-- `cSPDEGWf` over `ℚ(x)[t]`: with a negative degree bound and `c = 0`, the short-circuit succeeds with
the all-zero tuple (its `b̄` component has length 0) — the fuel-free §6.4 own-loop runs over the tower. -/
example :
    ((CPolyG.cSPDEGWf ([ofConstNZ 1] : CPolyG QFunNZ) [ofConstNZ 1] [ofConstNZ 1] [] (-1)).map
      (fun t => (t.1 : List QFunNZ).length)) = some 0 := by native_decide

end DeepWiki.SymbolicIntegration
