# `minplus` — an executable, proved-correct (min,plus) calculator

`minplus` computes with **ultimately pseudo-periodic (UPP)** integer sequences — the finite
function class of deterministic network calculus (DNC Chapter 4). A UPP sequence is given by
`<vals> <period> <incr>`: a stored prefix `v0,v1,…` followed by a positive period `d` and increment
`c`, denoting `f(n) = f(n − d) + c` past the prefix. The operations are run by the **same Lean
functions proved correct** in `DeepWiki.NetworkCalculus.UppSequence` — `evalNat`, `UppSeq.add`
(`evalNat_add`), `UppSeq.min` (`evalNat_min`, balanced case). Like the `wiki`/`tlts` tools it is out
of `defaultTargets`, so it never touches the math gate.

```
lake build minplus
lake exe minplus            # usage
```

## Commands

| command | result |
|---|---|
| `minplus eval <vals> <period> <incr> <n>` | `f(n)` |
| `minplus seq  <vals> <period> <incr> <k>` | `f(0), …, f(k−1)` |
| `minplus add  <v1> <p1> <c1> <v2> <p2> <c2> <k>` | `(f+g)(0..k−1)` — **proved correct** (`evalNat_add`) |
| `minplus min  <v1> <p1> <c1> <v2> <p2> <c2> <k>` | `(f⊓g)(0..k−1)` — pointwise min; the result is UPP (`min_evalNat_add_lcm`) |
| `minplus max  <v1> <p1> <c1> <v2> <p2> <c2> <k>` | `(f⊔g)(0..k−1)` — pointwise max; the result is UPP (`max_evalNat_add_lcm`) |
| `minplus conv <v1> <p1> <c1> <v2> <p2> <c2> <k>` | `(f⊗g)(0..k−1)` — the (min,plus) convolution `⨅_{k≤n} f(k)+g(n−k)` (`convNat_le`/`convNat_eq`) |
| `minplus convupp <v1> <p1> <c1> <v2> <p2> <c2>` | `f⊗g` **as a UPP sequence** `vals period=d incr=c` — the composable closed form, Lemma 4.4 (`convUpp` via `convFrom`/`evalNat_convFrom`) |
| `minplus addupp <v1> <p1> <c1> <v2> <p2> <c2>` | `f+g` **as a UPP sequence** (`UppSeq.add` / `evalNat_add`) |
| `minplus minupp <v1> <p1> <c1> <v2> <p2> <c2>` | `f⊓g` **as a UPP sequence** (`minUpp`; `min_evalNat_add_lcm_window`) |
| `minplus maxupp <v1> <p1> <c1> <v2> <p2> <c2>` | `f⊔g` **as a UPP sequence** (`maxUpp`; `max_evalNat_add_lcm_window`) |
| `minplus deconv <v1> <p1> <c1> <v2> <p2> <c2> <k>` | `(f⊘g)(0..k−1)` — the deconvolution `⨆_{k≥0} f(n+k)−g(k)`; finite (and computed) only when `slope_f ≤ slope_g`, else refused (`deconvNat`/`deconvNat_isGreatest`) |
| `minplus deconvupp <v1> <p1> <c1> <v2> <p2> <c2>` | `f⊘g` **as a UPP sequence** — period `d_f`, increment `c_f` (`deconvUpp`; `deconvNat_add_period`, Lemma 4.5); needs `slope_f ≤ slope_g` |
| `minplus backlog <vα> <pα> <cα> <vβ> <pβ> <cβ>` | the **backlog bound** `supₜ(α(t)−β(t)) = (α⊘β)(0)` — worst-case buffer; needs `slope_α ≤ slope_β` (`backlogBound`/`deconvNat_isGreatest`) |
| `minplus delay <vα> <pα> <cα> <vβ> <pβ> <cβ>` | the **delay bound** `min{d : ∀t α(t)≤β(t+d)}` — worst-case delay, proved to be the *least* dominating shift (`delayBound`/`delayBound_least`); needs `slope_α ≤ slope_β` |
| `minplus closure <vals> <period> <incr> <k>` | the **sub-additive closure** `f*(0..k−1) = δ₀ ⊓ f ⊓ f² ⊓ ⋯` via `closureApproxNat f n n`; exact for `f(0)=0`; refuses `f(0)<0` (where `f* = −∞`) |
| `minplus residual <vβ> <pβ> <cβ> <vα> <pα> <cα> <k>` | the **residual service curve** `[β−α]⁺↑(0..k−1)` — leftover service for a flow after a cross-flow (arrival `α`) is served by `β`; `residualAt` with intro/elim/mono proved |
| `minplus tandem <α:v p c> <β1:v p c> <β2:v p c>` | **two servers in series**: the end-to-end service curve `β1∗β2` (concatenation thm `IsMinimalServiceCurve.comp`) + end-to-end backlog/delay — "pay bursts only once" |

`<vals>` is comma-separated with no spaces, e.g. `0,1,2`.

## Soundness

Each command computes its result via the Lean functions proved in `UppSequence.lean`. `add` denotes
the pointwise sum (`evalNat_add`); `min`/`max`/`conv` sample the pointwise minimum / maximum /
`(min,plus)` convolution directly (correct by definition). Beyond merely sampling, the *results are
themselves ultimately pseudo-periodic*: `min`/`max` by `min_evalNat_add_lcm`/`max_evalNat_add_lcm`
(Lemma 4.3, all slope cases, via the Archimedean crossover `evalNat_eventually_le`); `add` by
`IsUPPWith.add`; convolution by the general closed form `convNat_add_lcm` (Lemma 4.4, all slope cases).

**The `*upp` commands return the result as an actual UPP sequence** — the *composable* form, so
operators chain. Each assembles a `UppSeq` whose `evalNat` provably reproduces the pointwise
operation once the prefix reaches a stabilization rank: `convupp` via `convFrom`/`evalNat_convFrom`
(rank `rank_r+rank_s+d` balanced, else a minimizer-region crossover, `convNat_add_lcm_window`);
`addupp` via `UppSeq.add` (always periodic past `max(rank_r,rank_s)`); `minupp`/`maxupp` via
`fromSamples`/`evalNat_fromSamples` with `min`/`max_evalNat_add_lcm_window` (past the crossover the
slower operand *is* the min, the faster *is* the max). The crossover rank for `min`/`max` is found by
a finite plain-`≤` window search (`findCrossoverLe`), valid by `evalNat_le_of_window_le`; the
convolution uses the *offset* search (`findCrossover`). So each printed quadruplet is the genuine UPP
closed form, ready to feed into another operator.

**`deconv` is the genuine deconvolution**, not just a window max: `deconvNat` is proved to be the
*greatest* of all terms `f(n+k)−g(k)` over every `k ≥ 0` (`deconvNat_isGreatest`), because past the
search window the terms are non-increasing per period (`deconvNat_ge`). It is finite only when
`slope_f ≤ slope_g`; the CLI refuses otherwise (the deconvolution is `+∞`). `deconvupp` returns it as
a UPP sequence (period `d_f`, increment `c_f` — its UPP-ness is `deconvNat_add_period`, Lemma 4.5), so
deconvolution composes too. The **sub-additive closure** `f* = δ₀ ⊓ f ⊓ f² ⊓ ⋯` (Lemma 4.7–4.9)
is sampled by `closureApproxNat f n n = ⨅_{m≤n} f^⊗ᵐ(n)` — the proved truncated closure
(`UppSeq.closureApproxNat`, with `closureApproxNat_idem`/`_eq_of_stable`). This is **exact** when
`f(0)=0` (the standard service/arrival-curve case): any `m`-fold convolution with `m > n` must spend
`m−n` zero-steps, which at `f(0)=0` cost nothing, so ranks beyond `n` never lower `f*(n)`. The CLI
refuses `f(0)<0`, where the closure diverges to `−∞`. Returning the closure *as a single UPP sequence*
(rather than a finite sample) remains future work — it needs the stabilization rank from
`closureApproxNat_eq_of_stable` lifted to a period/increment.

## Example

```sh
minplus seq 0,1,2 2 3 8           # 0, 1, 2, 4, 5, 7, 8, 10   (period 2, +3)
minplus eval 0,1,2 2 3 5          # 7
minplus add 0,1,2 2 3 0,1,2 2 3 8 # 0, 2, 4, 8, 10, 14, 16, 20   (doubled)
minplus min 0,1,2 2 3 0,1,2 2 3 8 # 0, 1, 2, 4, 5, 7, 8, 10   (balanced: f ⊓ f = f)
minplus min 0,2 1 2 3,4 1 1 8     # 0, 2, 4, 6, 7, 8, 9, 10   (2n ⊓ (n+3), different slopes)
minplus conv 0 1 1 2 1 1 6        # 2, 3, 4, 5, 6, 7   (rate-1 latencies add)
minplus convupp 0 1 1 0 1 2       # 0, 1  period=1  incr=1   (n ⊗ 2n = n, as a UPP sequence)
minplus convupp 0,1,2 2 3 0,1,2 2 3  # 0, 1, 2, 3, 4, 6  period=2  incr=3   (demoSeq ⊗ demoSeq)
minplus minupp 0,2 1 2 3,4 1 1    # 0, 2, 4, 6  period=1  incr=1   (2n ⊓ (n+3) → n+3 past crossover)
minplus maxupp 0,2 1 2 3,4 1 1    # 3, 4, 5, 6  period=1  incr=2   (2n ⊔ (n+3) → 2n past crossover)
minplus addupp 0 1 1 0 1 2        # 0, 3  period=1  incr=3   (n + 2n = 3n)
minplus deconv 0 1 1 0 1 2 6      # 0, 1, 2, 3, 4, 5   (n ⊘ 2n = n; slope 1 ≤ 2, finite)
minplus deconvupp 5,6 1 1 0 1 2   # 5, 6  period=1  incr=1   ((n+5) ⊘ 2n = n+5, as a UPP sequence)
```

## Network-calculus applications

The calculator computes real deterministic-network-calculus results on rate-latency service curves
`β_{R,T}(t) = R(t−T)₊` and token-bucket arrival curves `α_{r,b}(t) = b+rt` (both gate-verified in
`Calc.lean`):

- **Server concatenation** `β₁ ⊗ β₂` — the end-to-end service curve is rate-latency with the minimum
  rate and the summed latency: `β_{1,2} ⊗ β_{2,1} = β_{1,3}`.
  `minplus convupp 0,0,0 1 1 0,0 1 2` → `0, 0, 0, 0, 1  period=1  incr=1` (`= max(n−3,0)`).
- **Output arrival curve** `α ⊘ β` — a flow's bound after a server; the burst inflates by `r·T`:
  `α_{1,2} ⊘ β_{2,1}` is a token bucket of rate `1`, burst `2+1·1 = 3`.
  `minplus deconvupp 0,3 1 1 0,0 1 2` → `3, 4  period=1  incr=1` (`= n+3`).
- **Backlog bound** `supₜ(α(t)−β(t))` — the worst-case buffer occupancy, equal to `(α⊘β)(0)`; for a
  token bucket through a rate-latency server it is the classic `b + r·T`.
  `minplus backlog 0,3 1 1 0,0 1 2` → `backlog bound = 3`.
- **Delay bound** `min{d : ∀t α(t)≤β(t+d)}` — the worst-case delay (max horizontal deviation); for the
  same token bucket and server it is the classic `T + b/R`.
  `minplus delay 0,3 1 1 0,0 1 2` → `delay bound = 2`.
- **Residual service curve** `[β−α]⁺↑` — the *multi-flow* leftover: with several flows sharing a server
  of curve `β`, the service still guaranteed to one flow once a cross-flow constrained by arrival curve
  `α` is served. A rate-2 server carrying a rate-1 cross-flow leaves a rate-1 residual:
  `minplus residual 0,2 1 2 0,1 1 1 6` → `0, 1, 2, 3, 4, 5`.
- **Tandem (servers in series)** — the *multi-hop* end-to-end analysis: two servers `β1`, `β2` traversed
  in sequence offer the convolved service curve `β1∗β2` (the concatenation theorem), and the end-to-end
  delay/backlog are computed against it. For a token bucket `α_{1,2}` through two `β_{2,1}` servers:
  `minplus tandem 0,3 1 1 0,0 1 2 0,0 1 2` → end-to-end `β1∗β2 = β_{2,2}`, backlog `4`, delay `3`. The
  delay `3` beats the sum of per-hop delays `2 + 3 = 5` — **pay bursts only once** — a fact gate-verified
  by `native_decide` in `Calc.lean`.

(`backlog` is fully proved via `deconvNat_isGreatest`. `delay` is a finite search whose decisive-window
property is now the proved lemma `evalNat_le_shift_of_window`: if `α(t) ≤ β(t+d)` on one period-window
past the transient it holds for all `t`, since the gap `α(t)−β(t+d)` is non-increasing per period. The
search over `[0, deconvBound)` thus covers the transient directly and the periodic tail by descent.
That `List.find?` returns the *least* such `d` — so the reported bound is the genuine `min` — is now
the proved `delayBound_least` (via `find?_range_least`), with a concrete witness that `d=2` is least
for the canonical pair. So the delay bound is verified-minimal whenever the search succeeds.

`residual` computes the integer-argument (discrete, `ℕ`-indexed) values of the library's residual curve
`residualCurve = [β−α]⁺↑`, with the intro/elim/monotone/nonneg satellites (`clampedDiff_le_residualAt`,
`residualAt_le`, `residualAt_mono`, `residualAt_nonneg`) proved at the UPP level — so the output is a
genuine non-decreasing service curve dominating the clamped difference. Equality with the *continuous-time*
`residualCurve` over `ℝ≥0` would need the piecewise-linear interpolation bridge, which is out of scope.)

## Scope and frontier

The single-flow core (`eval … delay`/`closure`) and both multi-flow analyses (`residual` for
multiplexing, `tandem` for concatenation) are **verified for the discrete-time, integer-valued UPP
model** — every operator runs the same Lean function proved correct in `UppSequence`, and the two
deviation bounds are proved extremal (`deconvNat_isGreatest`, `delayBound_least`).

Two orthogonal generalizations remain:

- **Rational values** (fractional rates/bursts) are *not* a research gap: `UppSeq V` and its operators
  are generic over any `[AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [Archimedean V]`, and
  `ℚ` satisfies all four with decidable order. The proved-correct `convNat`/`deconvNat`/`min`/`max`
  already compute over `ℚ` unchanged (gate-verified in `Calc.lean`); exposing them at the CLI needs only
  a rational reader/printer at the boundary — a mechanical, not foundational, step.
- **Continuous time** (rational breakpoint *positions* with linear interpolation between them) is a
  genuinely different model: the operators become infima/suprema over a continuous `t`, and tying the
  discrete `ℕ`-indexed values to the `ℝ≥0`-valued library curves (`residualCurve`, `concatConv`) needs
  the piecewise-linear interpolation bridge. This is the real remaining frontier.
