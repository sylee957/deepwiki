import DeepWiki.SymbolicIntegration.ComputableTowerField
import DeepWiki.SymbolicIntegration.ComputableTowerDeriv
import DeepWiki.SymbolicIntegration.ComputableHermiteTower
import DeepWiki.SymbolicIntegration.ComputableSplitSquarefree

/-! # The generic integration pipeline over arbitrary-depth differential towers
`ComputableTowerField`/`ComputableTowerDeriv` built the generic fraction-field carrier `QFunNZG α`
(the next tower level ℚ(x)(t₁)(t₂)…) with a *computable* `CField` instance AND a *computable*
derivation tower (`CDiffField (QFunNZG α)`, `towerDerivQFunNZG`). What was still
**`QFunNZ`-hardwired** is the §3.5/§5.3 integration pipeline: `cSplitFactorFast`,
`canonicalRepresentationFast`, `cHermiteReduceTower` (`ComputableSplitFactorFast`/
`ComputableCanonicalRep`/`ComputableHermiteTower`). Those are already on the **generic** engine ops
(`caddG`/`cmulG`/`cmonomialDeriv`/`cdivG`/…) — the *only* `QFunNZ`-specific call is the fraction-free
gcd `cgcdFF` (with its `BPoly = ℚ[x][t]` `clearDenoms` bridge).

This file produces **generic copies** (suffix `G`) over `[CField α] [CFieldDomain α] [CDiffField α]`,
replacing every `cgcdFF fuel p q` with `cgcdMonicG fuel p q := cmonicG (cgcdExtG fuel p q).1` — the
already-generic Euclidean gcd (validated at tower level 2 in `ComputableTowerField`). We accept the
ℚ(x)-coefficient swell of the Euclidean kernel: it is a separate optimization, and the small
level-2 validations stay in budget.

* **`cgcdMonicG`** — the monic gcd via the generic extended Euclidean `cgcdExtG`, the generic
  drop-in for `cgcdFF`.
* **`cSplitFactorFastG`** (§3.5 special/normal split `p = pₙ·pₛ` via the derivation `D` + gcd).
* **`cSqfreeYunFFG`** (Yun squarefree factorization in `t`, the formal `dp/dt`) — what the Hermite
  reduction factors the denominator with.
* **`canonicalRepresentationFastG`** (the `a/d → (fₚ, (b, dₛ), (c, dₙ))` canonical representation),
  reusing the already-generic Bézout helpers `cbezoutOne`/`cextendedEuclideanSplit`.
* **`cHermiteReduceTowerG`** (the transcendental Hermite reduction of the simple normal part →
  rational `g` + reduced remainder — the RATIONAL PART of the integral), reusing the already-generic
  inner loop `cHermiteReduceTowerInner`/`cdiophantineG`.

**★ The headline `native_decide`** runs `canonicalRepresentationFastG` + `cHermiteReduceTowerG` on a
concrete proper fraction over `CPolyG (QFunNZG (QFunNZG ℚ)) = ℚ(x)(t₁)[t₂]` whose denominator has a
**repeated `t₂`-factor**, and certifies `D(g) + h = f`: tower integration, rational part, executing
at **level 2**. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### The generic monic gcd — the drop-in for `cgcdFF`

`cgcdFF` (the `QFunNZ`-specific fraction-free primitive PRS) and the generic Euclidean
`cgcdExtG` compute the *same* gcd up to a unit; `cgcdFF` already monic-normalizes. The generic
replacement is `cmonicG (cgcdExtG fuel p q).1`: the gcd component of the extended Euclidean triple,
monic-normalized over the field. It carries the ℚ(x)-coefficient swell of the field-division kernel
(that is the documented optimization gap), but is fully `[CField α]`-generic — it runs at any tower
level (validated at level 2 in `ComputableTowerField`). -/

/-- **Generic monic gcd** `cgcdMonicG fuel p q = monic gcd(p, q)`: the gcd component of the generic
extended Euclidean `cgcdExtG`, monic-normalized (`cmonicG`). The `[CField α]`-generic drop-in for the
`QFunNZ`-specific fraction-free `cgcdFF` (same gcd up to a unit, both monic). Runs at any tower
level. -/
def cgcdMonicG (fuel : ℕ) (p q : CPolyG α) : CPolyG α :=
  cmonicG (cgcdExtG fuel p q).1

end CPolyG

end DeepWiki.SymbolicIntegration
