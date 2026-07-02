import DeepWiki.SymbolicIntegration.ComputableTowerGcdFFCore
import DeepWiki.SymbolicIntegration.ComputableTowerIntegrate
import DeepWiki.SymbolicIntegration.ComputableFuelFreeGcd
import DeepWiki.SymbolicIntegration.ComputableFuelFreeDiophantine
import DeepWiki.SymbolicIntegration.ComputableFuelFreeResultant

/-! # Fuel-free (well-founded) GENERIC tower integration engine

The generic tower engine (`ComputableTowerIntegrate`/`ComputableTowerRischDE`) — `cIntegrateGFull`,
`cRischDEG`, and their pipeline —
is `[CField α] [CDiffField α] [CFracGcdCore α]`-generic and gate-clean, but every op carries an explicit
`fuel : ℕ`. This file builds the **fuel-free** companions `…GWf`, by the same runtime-guard well-founded
recursion as the fuel-free gcd (`ComputableFuelFreeGcd*`), over the generic carrier.

Every recursion in the generic pipeline bottoms out at one of THREE fuel-recursive ops; the rest is a flat
composition over fuel-free leaves:

* **`cprimPRSgcdGenCoreWf`** — the fraction-free primitive-PRS kernel (inside `CFracGcdCore.cgcdFFCore`),
  recursing on `(gbnormCore Q).length`. Its `…Wf` companion `cgcdFFCoreWf` re-runs the whole flat
  fraction-free gcd over the tower with no fuel.
* **`cSplitFactorFastGWf`** — Bronstein §3.5 split, recursing on `(cnormG p).length` (the `cSplitFactorFastWf`
  pattern, now generic).
* **`cSqfreeYunFFGgoWf`** — Yun squarefree factorization, recursing on the **multiplicity counter** `fo`
  (the `cSqfreeYunFFgoWf` Yun-exception, structural — sound at skipped multiplicities).

The flat-composition ops (`canonicalRepresentationFastGWf`, `cHermiteReduceTowerGWf`,
`cResidueResultantTowerGWf`/`cLogPartGWf`, and the reduced-case capstone `cIntegrateReducedGWf`)
substitute the fuel-free leaves directly. The generic leaves
`cdivmodWf`/`cgcdWf`/`cresultantWf` (`ComputableFuelFreeGcd`/`ComputableFuelFreeResultant`) are reused verbatim
where the pipeline bottoms out at them.

Every `…GWf` def is **`[CField α]`-only on the fuel-free fragment** (plus `[CDiffField α]`/`[CFracGcdCore α]`
where the pipeline needs the derivation / the fraction-free gcd) — never `[CFieldSpec α]`, which would break
`native_decide` over the noncomputable tower (the keystone lesson). The runtime ops carry no fuel. -/

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
next PRS node `r = gbprimitivePartCore cgcdB (gbpsremainderCore 60 P Q)` and recurse on `(Q, r)`. The
recursion is taken only under the structural guard `(gbnormCore r).length < (gbnormCore Q).length`, so
`decreasing_by` is `assumption`. `[CField B]`-only (no `[CFieldSpec B]`), so it `native_decide`s over the
noncomputable-`CFieldSpec` tower. The content-gcd `cgcdB` is passed in (the level-`β` fuel-free
`cgcdFFRawCoreWf`). -/
def cprimPRSgcdGenCoreWf (cgcdB : CPolyG B → CPolyG B → CPolyG B) (P Q : GBPolyCore B) :
    GBPolyCore B :=
  let P := gbnormCore P
  let Q := gbnormCore Q
  if gbisZeroCore Q then gbprimitivePartCore cgcdB P
  else
    let r := gbprimitivePartCore cgcdB (gbpsremainderCore 60 P Q)
    if (gbnormCore r).length < (gbnormCore Q).length then
      cprimPRSgcdGenCoreWf cgcdB Q r
    else gbprimitivePartCore cgcdB P   -- unreachable on a real run (PRS `t`-degree drop)
termination_by (gbnormCore Q).length
decreasing_by exact Nat.lt_of_lt_of_le ‹_ < _› (le_of_eq (by rw [gbnormCore_idem]))

end GBPolyCore

/-! ### Primitive-PRS termination predicate

There is no abstract `gbpsremainderCore` length-drop lemma over the generic GCD-domain `CPolyG B = B[s]`
(the pseudo-remainder degree drop over a non-field coefficient ring is exactly the per-step fact a real PRS run
satisfies but no engine lemma states), so the correctness layer uses a **fuel-regularity predicate**
`CPrimPRSGenRegular` that mirrors the `cprimPRSgcdGenCore` fuel recursion with the per-step length-drop guard
built in. The runtime `cprimPRSgcdGenCoreWf` carries no fuel. -/

/-- **Per-run primitive-PRS-kernel fuel-regularity** `CPrimPRSGenRegular cgcdB fuel P Q`: mirrors the
`cprimPRSgcdGenCore` fuel recursion as an inductive predicate over the structural fuel counter — `stop`
(any fuel) when the next divisor is zero (`gbisZeroCore (gbnormCore Q)`, the loop ends), or `step`
(fuel `n+1`) when `Q` is nonzero, the next PRS node `r = gbprimitivePartCore cgcdB (gbpsremainderCore 60
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
      (hguard : (GBPolyCore.gbnormCore (GBPolyCore.gbprimitivePartCore cgcdB
          (GBPolyCore.gbpsremainderCore 60 (GBPolyCore.gbnormCore P) (GBPolyCore.gbnormCore Q)))).length
        < (GBPolyCore.gbnormCore Q).length)
      (hrec : CPrimPRSGenRegular cgcdB fuel (GBPolyCore.gbnormCore Q)
        (GBPolyCore.gbprimitivePartCore cgcdB
          (GBPolyCore.gbpsremainderCore 60 (GBPolyCore.gbnormCore P) (GBPolyCore.gbnormCore Q)))) :
      CPrimPRSGenRegular cgcdB (fuel + 1) P Q

/-! ### `class CFracGcdCoreWf α` — the recursive FUEL-FREE fraction-free gcd over `α[t]`

The fuel-free mirror of `CFracGcdCore`, tying the tower with no fuel:
* **`class CFracGcdCoreWf α`** (one method `cgcdFFRawCoreWf`, the *raw* content-normalized fuel-free gcd).
* **Base `instance CFracGcdCoreWf ℚ`** — `ℚ[t]`'s raw fraction-free gcd is the **fuel-free** generic
  Euclidean gcd `(cgcdWf p q).1` (the fuel-free companion of `(cgcdExtG _).1`).
* **Recursive `instance CFracGcdCoreWf (QFunNZG β) [CFracGcdCoreWf β]`** — clear denominators into
  `GBPolyCore β`, run the **fuel-free** kernel `cprimPRSgcdGenCoreWf` with the level-`β` `cgcdFFRawCoreWf` as
  content-gcd, lift back. Bottoms at `CFracGcdCoreWf ℚ`. So `CFracGcdCoreWf (QFunNZG ℚ)` is the level-1
  ℚ(x) carrier's raw fuel-free gcd.

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
non-constant special factor strictly drops the `t`-degree). `[CField α] [CDiffField α] [CFracGcdCoreWf α]`-
generic — runs at any tower level. -/
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
runtime**; the counter `fo` is supplied once by the entry `cSqfreeYunFFGWf` as `cyunBoundG`.
`[CField α] [CFracGcdCoreWf α]`-generic. -/
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

Everything past the three recursive bottoms is a flat composition over fuel-free leaves. The fuel-free
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
The `Dstar`/`g` foldl is structural; every formerly fueled sub-op is a WF leaf — **no fuel at runtime**. Stated with
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

`cResidueResultantTowerGWf`/`cLogArgTowerGWf`/`cRationalResiduesGWf`/`cLogPartGWf` mirror the generic fueled
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

end CPolyG

/-! ### ★ THE HEADLINE `native_decide` validation — a FULL elementary tower integral, FUEL-FREE, at LEVEL 2

Bronstein's Example 5.6.2 lifted to **tower level 2** (`CPolyG Lvl2 = ℚ(x)(t₁)[t₂]`, `Dt₂ = 1`), now run by
the **fuel-free** generic integrator. The simple integrand `f = (1/2)/(t₂+1) − (1/2)/(t₂−1)` (assembled as
`a/d`, `d = t₂² − 1`) has elementary antiderivative `(1/2)log(t₂+1) − (1/2)log(t₂−1)`; the residues `±1/2`
have log arguments `t₂ ± 1`. The whole fuel-free generic tower integrator — canonical split + Hermite
rational part + Rothstein–Trager residue logs, with **no fuel at runtime** — computes over the tower at
level 2 and the returned `g + ∑ cᵢ·log(vᵢ)` genuinely differentiates back to `f`. Reuses the level-2 example
data of `ComputableTowerIntegrate`. -/

/-- **The fuel-free Hermite reducer computes the rational part at level 2** (`native_decide`): for
`f = 1/t₂²` over `ℚ(x)(t₁)[t₂]` with `Dt₂ = t₂² + 1`, the returned rational part and residual satisfy
the cleared Hermite identity. -/
theorem towerHermiteLvl2_rationalPartWf :
    (let res := CPolyG.cHermiteReduceTowerGWf towerHermiteLvl2Dt
        towerHermiteLvl2A towerHermiteLvl2D
      let gnum := res.1.1
      let gden := res.1.2
      let hNum := res.2.1
      let hDen := res.2.2
      let Dgnum := CPolyG.cmonomialDeriv towerHermiteLvl2Dt gnum
      let Dgden := CPolyG.cmonomialDeriv towerHermiteLvl2Dt gden
      let gprimeNum := CPolyG.csubG (CPolyG.cmulG Dgnum gden) (CPolyG.cmulG gnum Dgden)
      let gden2 := CPolyG.cmulG gden gden
      let lhs := CPolyG.cmulG
        (CPolyG.caddG (CPolyG.cmulG gprimeNum hDen) (CPolyG.cmulG hNum gden2)) towerHermiteLvl2D
      let rhs := CPolyG.cmulG towerHermiteLvl2A (CPolyG.cmulG gden2 hDen)
      CPolyG.cisZeroG (CPolyG.csubG lhs rhs)) = true := by native_decide

/-- **The fuel-free level-2 residual denominator has degree 1** (`native_decide`). -/
theorem towerHermiteLvl2_residual_degreeWf :
    CPolyG.cdegG (CPolyG.cHermiteReduceTowerGWf towerHermiteLvl2Dt
      towerHermiteLvl2A towerHermiteLvl2D).2.2 = 1 := by native_decide

/-- **The fuel-free canonical representation recombines to `f` at level 2** (`native_decide`). -/
theorem towerCanRepLvl2_recombinesWf :
    (let res := CPolyG.canonicalRepresentationFastGWf towerCanRepLvl2Dt
        towerCanRepLvl2A towerCanRepLvl2D
      let q := res.1
      let b := res.2.1.1
      let ds := res.2.1.2
      let c := res.2.2.1
      let dn := res.2.2.2
      let dsdn := CPolyG.cmulG ds dn
      let num := CPolyG.caddG (CPolyG.caddG (CPolyG.cmulG q dsdn) (CPolyG.cmulG b dn))
        (CPolyG.cmulG c ds)
      CPolyG.cisZeroG (CPolyG.csubG (CPolyG.cmulG num towerCanRepLvl2D)
        (CPolyG.cmulG towerCanRepLvl2A dsdn))) = true := by native_decide

/-- **The fuel-free recovered level-2 logarithmic part has length 2** (`native_decide`): the residue scan
over `ℚ(x)(t₁)[t₂]` finds exactly the two rational residues `±1/2` (log arguments `t₂ ± 1`) — the fuel-free
`cIntegrateReducedGWf` capstone's `logs` list has length `2`. -/
theorem towerIntLvl2_logs_lengthWf :
    (CPolyG.cIntegrateReducedGWf towerIntLvl2Dt towerIntLvl2Num towerIntLvl2Den
      towerIntLvl2Cands).logs.length = 2 := by native_decide

/-- **★ A FULL elementary tower integral at LEVEL 2, FUEL-FREE, and `D(∫f) = f`** (`native_decide`, the
headline deliverable). For `f = (1/2)/(t₂+1) − (1/2)/(t₂−1)` over ℚ(x)(t₁)(t₂) (tower **level 2**), the
fuel-free generic capstone `cIntegrateReducedGWf` — canonical split, Hermite rational part, Rothstein–Trager
residue logarithms, **no fuel at runtime** — returns an `IntegralResultG` whose antiderivative identity
`D(rational) + ∑ᵢ cᵢ·(D(vᵢ)/vᵢ) = f` holds exactly (`checkIdentityG`, cleared by `cisZeroG`). The WHOLE
fuel-free elementary tower integral computes at level 2 and differentiates back to `f`. -/
theorem towerIntLvl2_fullIntegralWf :
    CPolyG.checkIdentityG towerIntLvl2Dt
      (CPolyG.cIntegrateReducedGWf towerIntLvl2Dt towerIntLvl2Num towerIntLvl2Den
        towerIntLvl2Cands)
      towerIntLvl2Num towerIntLvl2Den = true := by native_decide

#print axioms towerHermiteLvl2_rationalPartWf
#print axioms towerCanRepLvl2_recombinesWf
#print axioms towerIntLvl2_fullIntegralWf

/-! ## Part 4 — STRETCH: the generic fuel-free RDE recursive bottoms (§6 PolyRischDE / SPDE)

The §6 RDE pipeline `cRischDEG` (`ComputableTowerRischDE`) is a second large pipeline whose flat structure
mirrors the integration one but whose recursive bottoms differ. This part builds the fuel-free companions of
its two `[CField α]`-generic degree-recursion bottoms — the §6.5 non-cancellation solve
`cPolyRischDENoCancelG` (recursing on `(cnormG c).length`) and the §6.4 SPDE `cSPDEG` (recursing on
`(n+1).toNat`) — the generic fuel-free non-cancellation and SPDE own-loops.
(The cancellation cases `cPolyRischDECancelPrimG`/`cPolyRischDECancelExpG` carry `[CRischField α]` and the
top driver `cRischDEG` is a flat composition over these — the documented continuation of the stretch.) -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

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

end DeepWiki.SymbolicIntegration
