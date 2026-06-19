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

`<vals>` is comma-separated with no spaces, e.g. `0,1,2`.

## Soundness

Each command computes its result via the Lean functions proved in `UppSequence.lean`. `add` denotes
the pointwise sum (`evalNat_add`); `min`/`max`/`conv` sample the pointwise minimum / maximum /
`(min,plus)` convolution directly (correct by definition). Beyond merely sampling, the *results are
themselves ultimately pseudo-periodic*: `min`/`max` by `min_evalNat_add_lcm`/`max_evalNat_add_lcm`
(Lemma 4.3, all slope cases, via the Archimedean crossover `evalNat_eventually_le`); `add` by
`IsUPPWith.add`; convolution by the general closed form `convNat_add_lcm` (Lemma 4.4, all slope cases).

**`convupp` returns the convolution as an actual UPP sequence** — the *composable* form. It assembles
`convFrom r s T`, whose `evalNat` provably reproduces `convNat` (`evalNat_convFrom`) once `T` is a
genuine stabilization rank. For the balanced case `T = rank_r+rank_s+d` (the book's rank); for the
strict-slope case `T` is read off a crossover `N₀` found by a finite window search (`findCrossover`)
whose validity is exactly `evalNat_add_le_of_window_le` + `convNat_add_lcm_window`. So the printed
quadruplet is the genuine UPP closed form of `f⊗g`, ready to feed into another operator.
(Deconvolution and sub-additive closure are future work.)

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
```
