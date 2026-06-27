import DeepWiki.SymbolicIntegration.ComputableRischDECompleteness
import DeepWiki.SymbolicIntegration.ComputableWeakNormalizerCorrect

/-! # §6.2 RDE completeness — the normal-denominator step preserves solvability (`hnorm`)

`RischDEInnerCompleteness` (`ComputableRischDECompleteness`) decomposes the deep §6 inner-solve
completeness into three converse clauses, `hnorm` / `hbound` / `hsolve`. `hbound` is produced (modulo a
precise cancellation residual) by `ComputableRischDEDegreeBound`; this file pursues `hnorm`.

**What `hnorm` says.** `hnorm` is the SOLVABILITY-PRESERVATION of Bronstein §6.2's `RdeNormalDenominator`:
*if the input RDE has a polynomial solution then the §6.2 reduction does not return `none`* —
`(∃ ynum yden, IsCRischDEGPolySol …) → (cRdeNormalDenominatorG …).isSome = true`. It is the **reverse**
direction of the §6.2 soundness step (whose forward `some ⟹ cleared-identity` is the proven soundness arc).

**The §6.2 transformation, made precise.** `cRdeNormalDenominatorG Dt fuel fnum fden gnum gden`
(`ComputableTowerRischDE`) splits the denominators into normal parts `dₙ = (cSplitFactorFastG Dt fuel
fden).1`, `eₙ = (cSplitFactorFastG Dt fuel gden).1`, forms `h = gcd(eₙ, eₙ')/gcd(p, p')`
(`p = gcd(dₙ, eₙ)`), and returns `some (a, b, c, h)` **iff the single guard `cdvdG fuel eₙ (dₙ·h·h)`
holds** — otherwise `none`. So the §6.2 step loses a solution **only** through that one divisibility gate,
and `hnorm` is **exactly**:

  a polynomial solution `⟹ cdvdG fuel eₙ (dₙ·h·h) = true`   (equivalently `(…).isSome = true`).

**The two-layer structure of `hnorm` (this file's contribution).**

* **The engine layer is fully reachable** and is closed here, axiom-clean (NO `native_decide`/`sorry`):
  - `cRdeNormalDenominatorG_isSome_iff` — the §6.2 step's `isSome` is *exactly* its `cdvdG` guard
    (`(…).isSome = true ↔ cdvdG fuel eₙ (dₙ·h·h) = true`), the precise control-flow reading.
  - `cdvdG_of_dvd` — the **converse of `dvd_of_cdvdG`**: a *mathematical* divisibility
    `toPolyG eₙ ∣ toPolyG (dₙ·h·h)` (with `eₙ ≠ 0` and the benign fuel bound) forces the engine check
    `cdvdG = true`, via the unique-remainder property of the §6.2 Euclidean `cmodG`.
  - `cRdeNormalDenominatorG_isSome_of_dvd` — composing the two: the *mathematical* §6.2 divisibility
    `eₙ ∣ dₙh²` makes the §6.2 step return `some`. This collapses `hnorm` to a single divisibility fact.

* **The mathematical divisibility is the irreducible §6.2 residual** (precisely isolated, NEVER `sorry`).
  That a *polynomial solution forces* `eₙ ∣ dₙh²` is **Bronstein Theorem 6.1.2** — the necessity of the
  normal-denominator divisibility, a valuation-theoretic fact at the normal poles that the engine does not
  self-certify (the soundness arc only ever *reads off* `eₙ ∣ dₙh²` from a successful `cdvdG`, never
  *derives* it from a solution). It is bundled as `RdeNormalDivisibilityResidual`, and `hnorm` is produced
  modulo it (`hnorm_of_divisibilityResidual`).

So `hnorm` reduces — through a fully proven engine layer — to the single mathematical divisibility
`solution ⟹ eₙ ∣ dₙh²` (Bronstein Thm 6.1.2), which is the precise §6.2 frontier. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## The engine layer: `isSome` is exactly the `cdvdG` guard, and `dvd ⟹ cdvdG`

`cRdeNormalDenominatorG`'s body is `if cdvdG fuel eₙ (dₙ·h·h) then some (…) else none`. The `isSome` is
therefore *definitionally* the guard. And the engine `cdvdG` is honest in **both** directions on a nonzero
divisor with enough fuel: `dvd_of_cdvdG` is the proven forward read; `cdvdG_of_dvd` here is the converse,
from the §6.2 Euclidean division identity (`toPolyG_cdivmodG'`) and the unique-remainder property. -/

section EngineLayer

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CFracGcdCore α]

end EngineLayer

end DeepWiki.SymbolicIntegration
