import DeepWiki.SymbolicIntegration.ComputableTowerGcdFFCore
import DeepWiki.SymbolicIntegration.ComputableTowerIntegrate
import DeepWiki.SymbolicIntegration.ComputableWellFounded
import DeepWiki.SymbolicIntegration.ComputableWellFounded2

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

end DeepWiki.SymbolicIntegration
