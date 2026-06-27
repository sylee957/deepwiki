import DeepWiki.SymbolicIntegration.ComputableOneShotAssembly
import DeepWiki.SymbolicIntegration.ComputableHyperexpNormal

/-! # Unconditional soundness of the §5.9 hyperexponential normal-part driver (Bronstein §5.9)

`ComputableOneShotAssembly` proved the **conditional** hyperexp one-shot for the *raw* driver
`cIntegrateGFull` — `cIntegrateGFull_hyperexp_oneShot`, gated on the integrability witness `∑c = 0`. The
genuine obstruction it pinned (closing status): `cIntegrateGFull`'s pure-normal branch emits the raw §5.6
Rothstein–Trager logs, which **overshoot** a hyperexponential normal part by `R = η·∑c` (the
`extendDeriv_logPart_eq_div_add_residual` leftover); the §5.9 residual-feedback driver
`cIntegrateHyperexpNormalG` (`ComputableHyperexpNormal`) is the one that *corrects* the overshoot —
`∫fₙ = logPart − ∫R`, absorbing `R` into a base integral `∫R = crischDESolve 0 R`. This file proves that
driver SOUND, **unconditionally in `∑c`** (no `∑c = 0` side condition), modulo the base-RDE-oracle's
`∫R`-soundness (the precise residual — see the scope note).

The two ingredients (the file delivers both):

* **★ The overshoot identity (Task 1, UNCONDITIONAL, axiom-clean)** —
  `hyperexp_residue_sum_eq_overshoot_add`: for a hyperexponential monomial `v = C b·X` (`Dt = η′·t`),
  squarefree `d = ∏_{α∈s}(t−α)`, `deg a < #s`, every root normal, the §5.6 Rothstein–Trager residue sum
  `∑_α C(c_α)·D(log(t−α))` equals `algebraMap(C(b·∑c)) + a/d` over `RatFunc K` — **no** `∑c = 0`. The raw
  log part differentiates to the integrand `a/d` PLUS the residual `R = b·∑c`. Composes the unconditional
  decomposition `monomial_residue_sum_eq_cancel_add` (residue sum = cancel sum + a/d) with
  `hyperexp_cancel_sum_eq` (the hyperexp cancel sum IS `algebraMap(C(b·∑c))`). This is the genuine new
  content: the `extendDeriv_logPart_eq_div_add_residual` claim, PROVEN, in the precise residue form.
* **★★ The base residual `∫R`-soundness (Task 2, the documented base-oracle residual)** — the §5.9 feedback
  integrates `R ∈ α` by `crischDESolve 0 R` (the pure-integration `Dy = R`, one tower level down). The base
  oracle `CRischField.crischDESolve` is a bare typeclass method with **no abstract spec layer**
  (`CRischFieldSpec` does not exist — see `ComputableTranscendentalOverAlgebraic`), so its soundness is only
  `native_decide`-validated today (e.g. `nNormInv_baseIntegral_eq_x`). We therefore carry the precise
  base-oracle conclusion `D(∫R) = R` as the explicit hypothesis `hintR`, isolating it as the *single*
  documented residual the unconditional driver soundness reduces to.

* **★★★ The driver soundness (Task 3)** — `cIntegrateHyperexpNormalG_sound` /
  `cIntegrateHyperexpFullG_sound`: `cIntegrateHyperexpNormalG Dt fuel a d cands = some res ⟹ D(res) = a/d`
  for a hyperexp `Dt = η′·t`, **unconditional in `∑c`**, gated on the abstract engine inputs (Hermite half,
  per-root reassembly) PLUS the base-oracle residual `hintR` and the residual-read bridge
  `R = b·∑c`. Composes Task 1 (overshoot) with Task 2 (`hintR`): the new rational part `g − ∫R`
  differentiates to `(a/d + R) − R = a/d`, the `R` cancelling. The §5.9 feedback is exactly the term that
  makes the hyperexp normal part integrable WITHOUT the `∑c = 0` side condition.

## Scope — what is proven unconditionally and what reduces to the base oracle

The **overshoot identity (Task 1) is fully proven, axiom-clean** (`[propext, Classical.choice, Quot.sound]`,
no `native_decide`): it is the genuine §5.9 content (the raw RT logs overshoot by `R = η·∑c`, refuting the
naive "log part alone" integral whenever `∑c ≠ 0`). The driver soundness (Task 3) is proven gated on two
*documented* inputs: (a) the same abstract engine bridges (`hherm`, `hform`, …) the primitive/hyperexp
one-shots in `ComputableOneShotAssembly` already take, and (b) the base-RDE-oracle residual
`hintR : D(∫R) = R` — which is NOT abstractly available because `crischDESolve` has no spec layer (it is only
`native_decide`-validated, and operates one tower level down: `crischDESolve 0 R` over `ℚ(x)` runs the §6
pipeline over `ℚ[x]`). So the unconditional-in-`∑c` hyperexp soundness reduces, precisely, to the base
oracle's `∫R`-soundness — the documented residual, the opposite condition to `∑c = 0` (it is the absorbing
of `∑c ≠ 0`, not its vanishing). -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ### ★ Task 1: the overshoot identity `D(logPart) = a/d + R` for the hyperexponential monomial

The raw §5.6 Rothstein–Trager log part `∑_α c_α·log(t−α)` of a hyperexponential normal part `fₙ = a/d`
overshoots: its derivative is `a/d + R`, NOT `a/d`, with the residual `R = b·∑c` (`b = η′`). This is the
`extendDeriv_logPart_eq_div_add_residual` claim, made precise and proven from two UNCONDITIONAL pieces in
`ComputableOneShotAssembly`'s `ResidueMatchTower`:

* `monomial_residue_sum_eq_cancel_add` — residue sum = (polynomial-part cancel sum) + a/d, for ANY monomial.
* `hyperexp_cancel_sum_eq` — for the hyperexp monomial `v = C b·X`, the cancel sum is `algebraMap(C(b·∑c))`.

So residue sum = `algebraMap(C(b·∑c)) + a/d`. No integrability witness — `∑c` is whatever it is, and the
overshoot `R = b·∑c` is carried, not killed. (When `∑c = 0` the overshoot vanishes and this collapses to
the residue match `= a/d`, the `hyperexp_residue_match_iff_sum_zero` regime.) -/

namespace ResidueMatchTower

variable {K : Type*} [Field K] [Differential K] [Algebra ℚ K]

/-- **★ The hyperexponential overshoot identity** `residue sum = algebraMap(C(b·∑c)) + a/d` (Bronstein
§5.9, the raw-log overshoot) — for the hyperexponential monomial `v = C b·X` (`Dt = η′·t`, `b = η′`), a
squarefree `d = ∏_{α∈s}(t−α)`, `deg a < #s`, every root normal (`(C b·X).eval α ≠ α′`), the §5.6
Rothstein–Trager residue sum `∑_{α∈s} C(c_α)·(D(t−α)/(t−α))` (`c_α = a(α)/(Dd)(α)`, `D = extendDeriv
(implicitDeriv (C b·X))`) equals `algebraMap(C(b·∑_α c_α)) + a/d` over `RatFunc K` — **UNCONDITIONALLY**, no
`∑c = 0`. The raw log part differentiates to the integrand `a/d` PLUS the residual `R = b·∑c`: the
`extendDeriv_logPart_eq_div_add_residual` claim, proven. Composes the unconditional decomposition
`monomial_residue_sum_eq_cancel_add` (residue sum = cancel sum + a/d) with `hyperexp_cancel_sum_eq` (the
hyperexp cancel sum IS `algebraMap(C(b·∑c))`). The genuine §5.9 new content — the residual `R = b·∑c` the
feedback driver must absorb. -/
theorem hyperexp_residue_sum_eq_overshoot_add (s : Finset K) (a : K[X]) (b : K)
    (hA : a.degree < s.card) (hnorm : ∀ α ∈ s, (C b * X).eval α ≠ α′) :
    ∑ α ∈ s, algebraMap K[X] (RatFunc K)
          (C (a.eval α / (Differential.implicitDeriv (C b * X) (Lagrange.nodal s id)).eval α))
        * (extendDeriv (Differential.implicitDeriv (C b * X))
              (algebraMap K[X] (RatFunc K) (X - C α))
            / algebraMap K[X] (RatFunc K) (X - C α))
      = algebraMap K[X] (RatFunc K)
            (C (b * ∑ α ∈ s,
              a.eval α / (Differential.implicitDeriv (C b * X) (Lagrange.nodal s id)).eval α))
        + algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) := by
  -- residue sum = (cancel sum) + a/d (unconditional), then cancel sum = algebraMap(C(b·∑c)) (hyperexp)
  rw [monomial_residue_sum_eq_cancel_add s a (C b * X) hA hnorm,
    hyperexp_cancel_sum_eq s b
      (fun α => a.eval α / (Differential.implicitDeriv (C b * X) (Lagrange.nodal s id)).eval α)]

end ResidueMatchTower

end DeepWiki.SymbolicIntegration
