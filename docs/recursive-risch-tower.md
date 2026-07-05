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

## Remaining — soundness (four bridges)

`cLimitedIntegratePolyRatG_sound` : with `intR` sound (`∀ c b, intR c = some b → D(b) = c`) and
`cLimitedIntegratePolyRatG η intR p = some q`, then `implicitDeriv (C η) (toPolyG q) = toPolyG p` (the
tower derivative of `q` is `p`). Path:
1. **Fold induction** — the fold produces `q` with the coefficient equations `cderiv (q.getD i) = aᵢ −
   (i+1)·η·(q.getD (i+1))` for `i < p.length` (each accepted step is an `intR` success; `hintR` gives the
   equation). Cleanest via a structural-recursion redefinition (`limIntTopFirst` on `p.zipIdx.reverse`).
2. **`toK` transport** — push the raw `CField`-op equations through `toK` to `K = CFieldSpec.K α`.
3. **Coefficient ↔ polynomial** — `coeff i (implicitDeriv (C η) Q) = D(coeff i Q) + η·(i+1)·coeff (i+1) Q`
   (`mapCoeffs` + `C η · derivative`, `coeff_derivative`), matched to `toK (p.getD i) = coeff i (toPolyG p)`.
4. **`Polynomial.ext`** — assemble 2–3 into the polynomial identity.

Then the primitive special-part soundness is no longer restricted to `D(fp)=0` — it holds for any polynomial
part whose coefficients integrate (rationally) in the coefficient field.

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

Phases A + B built & gate-green (commits `4aab225d`, `2de63ea4`): the recursive `RischSolver` class, the
base instance, the limited-integration interface + soundness, and the coefficient-recursion algorithm. The
four-bridge soundness of the recursion and the tower-step wiring are the multi-session continuation. The
reduced part (genuine LRT) and Hermite are already generic and reused verbatim.
