# The recursive Risch tower (`RischSolver`) — clean rebuild

## What was missing

The `LawfulRischLevel`/`LawfulRischLevelLrt` solvers are **one-level**: `MonomialCase.integrateSpecial`
(the polynomial/special-part hook) fires only when `D(fp) = 0` — the polynomial part has **constant
coefficients**. So the tower could do the reduced part (Hermite + LRT) but never the **coefficient
recursion** that integrates a non-constant polynomial part by recursing into the coefficient field. That
recursion is the heart of the transcendental algorithm (Bronstein §5.3–5.9); without it the "tower" can't
integrate `∫x·log x`, `∫x·eˣ`, or anything that needs it, and there can be no tower step.

## The design

`RischSolver α` (`RischSolverTower.lean`) — a recursive solver: `integrate Dt a d` integrates `a/d ∈ α(t)`
to a genuine root-free `LrtResultG α`; `sound` certifies `IsGenuineIntegralResultLrtG`.

- **Base** (`instRischSolverOfLawfulLrt`, priority 100) — the genuine one-level LRT solver *is* a
  `RischSolver` (reuses `integrateLrt`/`soundLrt`). Correct at the tower base `ℚ(x)` where the
  polynomial-part coefficients are constants. **Built.**
- **`integrateRational`** — limited integration = `integrate` restricted to **log-free** results:
  `some (num, den)` with `D(num/den) = a/d`, else `none`. The primitive the coefficient recursion calls
  (a coefficient must integrate to an element of the coefficient field, not a log). `integrateRational_sound`
  gives the log-free `LrtResultG ⟨(num,den),[]⟩` LRT identity. **Built.**
- **`cLimitedIntegratePolyRatG η intR p`** — the coefficient recursion. Primitive case `Dθ = η ∈ α`,
  polynomial part `p = Σ aᵢ tⁱ`: the antiderivative `q = Σ bᵢ tⁱ` has `D_tower(q) = Σᵢ (D(bᵢ) + (i+1)·η·bᵢ₊₁) tⁱ`,
  so matching coefficients gives the **top-down** system `D(bᵢ) = aᵢ − (i+1)·η·bᵢ₊₁`, each solved by the
  limited integration `intR` of an `α`-coefficient. Parameterized by `intR : α → Option α` so the tower step
  plugs in `RischSolver β.integrateRational`. **Built** (gate-green algorithm).

## Soundness — DONE (`cLimitedIntegratePolyRatG_poly_sound`)

With `intR` sound (`∀ c b, intR c = some b → cderiv b = c`) and `cLimitedIntegratePolyRatG η intR p = some q`,
`implicitDeriv (C ⟦η⟧) (toPolyG q) = toPolyG p` (the tower derivative of `q` is `p`) — **proven, no sorry**.
The four bridges:
1. **Fold induction** — `limIntTopFirst_drop` (`q.drop |L| = acc`) + `limIntTopFirst_eq` (coefficient
   equations at each processing position) + `cLimitedIntegratePolyRatG_eq` (indexed form
   `cderiv (q[i]) = aᵢ − (i+1)·η·q[i+1]`, `i < deg p`). **Done.**
2. **`toK` transport** — `CFieldSpec.toK_sub`/`toK_mul` + inline `toK (cnatCastG k) = (k : K)`. **Done.**
3. **Coefficient ↔ polynomial** — `coeff m (implicitDeriv (C η) Q) = D(coeff m Q) + η·(m+1)·coeff (m+1) Q`
   (`coeff_mapCoeffs` + `coeff_C_mul` + `coeff_derivative`) + `CDiffFieldSpec.toK_cderiv`. **Done.**
4. **`Polynomial.ext`** — coefficient-wise, off-degree both sides vanish (`getElem?_eq_none`). **Done.**

So the primitive special-part soundness is no longer restricted to `D(fp)=0` — it holds for any polynomial
part whose coefficients integrate (rationally) in the coefficient field. The recursion the rebuild was for is
a proven-correct algorithm.

## Remaining — the tower step

`instance [RischSolver β] → RischSolver (QFunNZG β)` : integrate `a/d ∈ (QFunNZG β)(t)` by
- canonical rep (poly + reduced + special) — existing;
- reduced part via genuine LRT (`cIntegrateReducedLrtG`) — **done, generic**;
- polynomial part via `cLimitedIntegratePolyRatG η intR` with `intR c := RischSolver β.integrateRational Ds
  (num c) (den c)` — the coefficient `c ∈ QFunNZG β = β(s)` is split into `num/den ∈ CPolyG β`, and `Ds` is
  `β`'s monomial derivative. The plumbing: the `QFunNZG` fraction num/den extraction + threading `Ds` from
  the differential-carrier structure.

Soundness threads the LRT reduced soundness (`hreducedLrt`, closed to `LrtReducedGenuineData` genuine data)
+ `cLimitedIntegratePolyRatG_sound` + the reconstruction (`combineSNLrt`). Blocked previously only because
the base couldn't recurse; with the recursion built, the step closes modulo these soundness lemmas.

## Status

Built & gate-green (commits `4aab225d`, `2de63ea4`, `01545f24`, `cd144146`): the recursive `RischSolver`
class + base instance, the limited-integration interface + soundness, the coefficient-recursion algorithm,
**and its full soundness `D_tower(q) = p`** (`cLimitedIntegratePolyRatG_poly_sound`, no sorry). The reduced
part (genuine LRT) and Hermite are already generic and reused verbatim.

**Only the tower-step wiring remains** — the QFunNZG plumbing that supplies `intR := RischSolver β.integrateRational
Ds (num c) (den c)` (split each coefficient `c ∈ QFunNZG β = β(s)` into `num/den ∈ CPolyG β`, thread `Ds` =
`β`'s monomial derivative), combines the polynomial-part result with the LRT reduced part (`combineSNLrt`), and
threads the two soundness lemmas into the step instance `[RischSolver β] → RischSolver (QFunNZG β)`. The hard
mathematics — the coefficient recursion and its soundness — is done.
