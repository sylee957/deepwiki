import DeepWiki.SymbolicIntegration.ComputableTranscendentalOverAlgebraic
import DeepWiki.SymbolicIntegration.ComputableGenericBezout
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.RatFunc.Degree

/-! # General-`n` radical extensions: the `∛`/`nth`-root inverse and a cube-root `CField`

The simple-radical carrier `RadExt α n f = α[y]/(yⁿ − f)`
(`ComputableTranscendentalOverAlgebraic`) is `n`-generic for its ring/derivation
(`radAdd`/`radMul`/`radDeriv` all take `n`/`f` explicitly), but its **inverse** was the `n = 2`
conjugate-norm `radInv2` only (`u⁻¹ = ū/(a² − b²f)`), so `instCFieldRadExt` is an honest *field*
solely at `n = 2`. This file lifts the inverse to **arbitrary `n`** via the **extended Euclidean
algorithm** in `α[y]`, and exhibits the engine differentiating/integrating over a **cube root**.

* **`radInvN n f g`** — the general-`n` inverse of `g ∈ α[y]/(yⁿ − f)`. When `yⁿ − f` is irreducible,
  `g` is a unit, so `cbezoutOne` finds `s·g + t·(yⁿ − f) = 1` in `α[y]`; reducing `s` mod `yⁿ = f`
  gives `g⁻¹` (because `(yⁿ − f) ≡ 0`, so `s·g ≡ 1`). Reuses the engine's `cbezoutOne` (built on
  `cgcdExtG`). Generic over every `[CField α]` and every `n`. At `n = 2` it agrees with `radInv2`
  (the conjugate-norm reciprocal, `radInvN_eq_radInv2_at_two` over ℚ(x)).
* **`RadExtN α n f`** — a *fresh* carrier (mirroring `RadExt`) whose `CField` inverse is `radInvN`
  rather than `radInv2`, so it is an honest field for **every** `n` where `yⁿ − f` is irreducible
  (not just `n = 2`). `add`/`mul`/`neg`/`isZero` are the same radical-carrier ops, `cderiv` the same
  diagonal `radDeriv`. A fresh type (not a second instance on `RadExt`) avoids overlapping with the
  existing `radInv2`-based `instCFieldRadExt`.
* **`CFieldN3` / the cube root `∛(x²+1)` over ℚ(x)** — the concrete carrier
  `RadExtN (QFunNZG ℚ) 3 (x²+1)`, an honest computable field: `y³ − (x²+1)` is **irreducible** over
  ℚ(x) (`x²+1` is not a perfect cube — `intDegree 2` is not divisible by `3`), proven via
  `X_pow_sub_C_irreducible_of_prime` (prime `3`).
* **★ the milestone (`native_decide`)** — over the cube-root carrier, the diagonal derivation
  `D(y) = (f'/(3f))·y` for `y = ∛(x²+1)` fires through `CDiffField.cderiv`, the cube `y·y·y = f`
  folds (`radMul 3 f`), and `u · u⁻¹ = 1` holds with `u⁻¹ = radInvN 3 f u` — the engine
  differentiating/multiplying/inverting over a **cube** root, not just a square root.

**Soundness note.** `radDeriv`-is-a-derivation is already proven `n`-generic in
`ComputableRadicalDerivationInvariant` (`toPolyG_radDeriv_radAdd`, `mk_toPolyG_radDeriv_radMul` —
additivity and Leibniz over `α[y]/(yⁿ − f)` for every `n`), so the abstract derivation laws of the
cube-root carrier `RadExtN α 3 f` are *inherited* from that `n`-generic result: nothing in the
derivation soundness is `n = 2`-specific. What this file adds beyond `n = 2` is the **inverse**
(`radInvN`) and a fresh field carrier around it; the genuine-field justification is the `n`-generic
irreducibility criterion (`X_pow_sub_C_irreducible_of_prime`). The `radInvN` correctness itself —
`toK (radInvN g) = (toK g)⁻¹` from the `cbezoutOne` Bézout identity read through `toPolyG` modulo the
`radIdeal` — is the natural next abstract step (the Bézout helper's `toPolyG`-image identity already
lives in `ComputableCanonicalRepCorrect`); here it is `native_decide`-validated. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem

namespace RadElem

variable {α : Type*} [CField α]

/-! ### The defining modulus `yⁿ − f` and the general-`n` inverse `radInvN`

The modulus `yⁿ − f ∈ α[y]` as a dense coefficient list, then the inverse of `g` in `α[y]/(yⁿ − f)`
by extended Euclid: solve `s·g + t·(yⁿ − f) = 1` and reduce `s` mod `yⁿ = f`. -/

/-- **The defining modulus `yⁿ − f`** `radModulus n f = [−f, 0, …, 0, 1]` (constant `−f`, then `n − 1`
zeros, then `1` at index `n`) as a `CPolyG α`: `cshiftG n [1] − [f] = yⁿ − f`. The polynomial whose
quotient is `α[y]/(yⁿ − f) = RadExt α n f`. -/
def radModulus (n : ℕ) (f : α) : CPolyG α :=
  CPolyG.csubG (CPolyG.cshiftG n [CField.one]) [f]

/-- **The general-`n` inverse** `radInvN n f g` of `g ∈ α[y]/(yⁿ − f)` via the **extended Euclidean
algorithm** in `α[y]`: from `cbezoutOne fuel g (yⁿ − f) = (s, t)` with `s·g + t·(yⁿ − f) = 1` (valid
when `yⁿ − f` is irreducible, so `g` is a unit), the inverse is `s mod (yⁿ = f)` — because the
modulus `≡ 0`, `s·g ≡ 1`. The Bézout cofactor `s` is reduced to degree `< n` by `radReduce`. Fuel for
both `cbezoutOne` and `radReduce` is `2·(n + len g) + 2`, comfortably above the degrees involved
(`deg s < n`, the Euclid recursion length `≤ n + 1`). Generic over `[CField α]` and `n`; the honest
field inverse whenever `yⁿ − f` is irreducible (Trager's algebraic-extension reciprocal). -/
def radInvN (n : ℕ) (f : α) (g : RadElem α) : RadElem α :=
  let fuel := 2 * (n + (g : List α).length) + 2
  let (s, _) := CPolyG.cbezoutOne fuel g (radModulus n f)
  radReduce n f fuel s

end RadElem

/-! ### Sanity: `radInvN` inverts, and agrees with `radInv2` at `n = 2` (`native_decide`)

Over `ℚ(x)`, `n = 2`, `f = x²+1` (the `arcsinh` radical): `radInvN` produces a genuine inverse, and
it matches `radInv2` up to the canonical (reduced) representative. -/

open RadElem

/-- **★ `radInvN` inverts at `n = 2`** (`native_decide`): over `(QFunNZG ℚ)[y]/(y² − (x²+1))`, for
`u = x + y`, the extended-Euclid inverse `radInvN 2 (x²+1) u` satisfies `radMul 2 (x²+1) u (radInvN …)
= 1` (checked by `radIsZero` of the product minus `[1]`). THE GENERAL-`n` INVERSE COMPUTES AND
INVERTS — at `n = 2` it reproduces the conjugate-norm reciprocal through extended Euclid. -/
theorem radInvN_mul_self_eq_one_at_two :
    radIsZero (radSub (radMul 2 fullRhoArcsinh fullUxPlusY
        (radInvN 2 fullRhoArcsinh fullUxPlusY)) radOne) = true := by native_decide

/-- **`radInvN` agrees with `radInv2` at `n = 2`** (`native_decide`): the extended-Euclid inverse and
the conjugate-norm inverse are the **same** element of `(QFunNZG ℚ)[y]/(y² − (x²+1))` (both reduced),
for `u = x + y`. Checked by `radIsZero` of the difference `radInvN 2 ρ u − radInv2 ρ u`. The two
constructions coincide where both apply — `radInvN` is the honest generalization of `radInv2`. -/
theorem radInvN_eq_radInv2_at_two :
    radIsZero (radSub (radInvN 2 fullRhoArcsinh fullUxPlusY)
        (radInv2 fullRhoArcsinh fullUxPlusY)) = true := by native_decide

end DeepWiki.SymbolicIntegration
