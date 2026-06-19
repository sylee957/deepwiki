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
| `minplus min  <v1> <p1> <c1> <v2> <p2> <c2> <k>` | `(f⊓g)(0..k−1)` — proved correct in the **balanced** case |
| `minplus conv <v1> <p1> <c1> <v2> <p2> <c2> <k>` | `(f⊗g)(0..k−1)` — the (min,plus) convolution `⨅_{k≤n} f(k)+g(n−k)` (`convNat_le`/`convNat_eq`) |

`<vals>` is comma-separated with no spaces, e.g. `0,1,2`.

## Soundness

`add` is proved correct for all inputs. `min` is proved correct only in the **balanced** case (equal
asymptotic slopes `c₁/d₁ = c₂/d₂`, the book's `d_g c_f = d_f c_g`); for unequal slopes the calculator
**refuses** rather than print an unproved result — the dominant-slope case needs an Archimedean
crossover bound (not yet formalized). Convolution and deconvolution are future work.

## Example

```sh
minplus seq 0,1,2 2 3 8           # 0, 1, 2, 4, 5, 7, 8, 10   (period 2, +3)
minplus eval 0,1,2 2 3 5          # 7
minplus add 0,1,2 2 3 0,1,2 2 3 8 # 0, 2, 4, 8, 10, 14, 16, 20   (doubled)
minplus min 0,1,2 2 3 0,1,2 2 3 8 # 0, 1, 2, 4, 5, 7, 8, 10   (balanced: f ⊓ f = f)
minplus min 0,2 1 2 3,4 1 1 8     # refused: slopes 2/1 and 1/1 differ
```
