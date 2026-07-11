import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalIntegralBasis
import Sources.Hdl_1721_1_15391.Source

/-! # Trager catalog — Chapter 2 §5: Integral Bases of Simple Radical Extensions
Trager's explicit **integral basis** for a simple radical extension `K(x)[y]/(yⁿ − ρ)` (`ρ ∈ ℚ[x]`):
no general Ch. 2 idealizer / Round-2 algorithm is needed, because the natural basis `1, y, …, y^{n−1}`
is already *normal* (Trager Ch. 2 §5, thesis p. 30, from the `Tᵢ`-decoupling of `AppendixA`), and the
maximal denominator clearing the `i`-th radical is `dᵢ = ∏ⱼ Pⱼ^{⌊i·eⱼ/n⌋}` (p. 30), giving the basis
`[1, y/d₁, …, y^{n−1}/d_{n−1}]` (p. 31). The `DeepWiki.SymbolicIntegration` library renders this for
`n = 2` (the hyperelliptic / unnested-square-root case) in `ComputableRadicalIntegralBasis`, validated by
`native_decide`: the square-part split `ρ = d²·s` (`s` squarefree), the basis `[1, y/d]`, the
integral-closure certificates, and the discriminant `4s` + hyperelliptic genus.

**Computable-vs-abstract.** Every entry below is a computable function or a `native_decide` witness on a
worked radicand. The abstract correctness (that `[1, y/d]` IS the integral closure of `ℚ[x]` for every
`ρ`) is validated by the examples, not proved in general. The integral basis is the prerequisite for the
**divisor construction** (Ch. 5 §3, catalog `Sources.Hdl_1721_1_15391.Chapter5`) and the
**principal-divisor / torsion test** (Ch. 6) that produce the actual log arguments `vᵢ`.

## NOT YET FORMALIZED (audit 2026-06-26)
Ch. 2 §2 The general integral basis (the idealizer / Round-2 / Trager–Zassenhaus algorithm building the
  integral closure for an ARBITRARY algebraic curve, not just a simple radical) `[infra]`.
Ch. 2 §3 Normalization at infinity (extending the integral basis to the places at `∞`, the local
  integral closure at the infinite valuations) `[infra]`.
Ch. 2 §5: the simple-radical integral basis for radical degree `n ≥ 3` (only `n = 2`, the
  `[1, y/d]` hyperelliptic case, is realized and validated; the general `dᵢ = ∏ⱼ Pⱼ^{⌊i·eⱼ/n⌋}` for the
  higher radicals `y², …, y^{n−1}` is unbuilt) `[deferred]`. -/

open DeepWiki.SymbolicIntegration DeepWiki.SymbolicIntegration.CPoly

namespace DeepWiki.Tiaf

/-! ## The square-part / squarefree-part split for `n = 2` (Ch. 2 §5, p. 30) -/

/-- **Square part** `radSquarePart ρ = d = ∏ᵢ Pᵢ^{⌊i/2⌋}` (Trager, Chapter 2 §5, p. 30): the root of
the largest square divisor of `ρ`, read off the multiplicity-indexed squarefree factorization
`ρ = ∏ᵢ Pᵢ^i`. Trager's general `dᵢ = ∏ⱼ Pⱼ^{⌊i·eⱼ/n⌋}` specialized to `n = 2, i = 1`, so `d² ∣ ρ` and
`ρ/d²` is squarefree. -/
abbrev ch2_squarePart := @radSquarePart

/-- **Squarefree part** `radSquarefreePart ρ = s = ∏_{i odd} Pᵢ = ρ/d²` (Trager, Chapter 2 §5,
p. 30): the radical-style squarefree part collecting one copy of each odd-multiplicity factor, so
`ρ = d²·s` with `s` squarefree and `(y/d)² = s`. -/
abbrev ch2_squarefreePart := @radSquarefreePart

/-! ## The integral basis `[1, y/d]` (Ch. 2 §5, p. 31) -/

/-- **The simple-radical integral basis** `radIntegralBasis ρ = (d, s)` (Trager, Chapter 2 §5, p. 31):
the integral closure of `ℚ[x]` in `ℚ(x)[y]/(y² − ρ)` has the explicit `ℚ[x]`-basis `[1, y/d]`, with
`d = radSquarePart ρ` and `s = radSquarefreePart ρ = ρ/d²` squarefree, `(y/d)² = s`. Returned as the pair
`(d, s)` (the basis is `1` and `y/d`; `s` is the minimal-polynomial constant `(y/d)² = s`). -/
abbrev ch2_integralBasis := @radIntegralBasis

/-! ## Integral-closure validation predicates (Ch. 2 §5) -/

/-- **The square-part split is exact** `radSplitExact ρ` (Trager, Chapter 2 §5, p. 30–31): `d²·s = ρ`,
so `s = ρ/d²` is a genuine `ℚ[x]` polynomial — the precondition that `y/d` satisfies the monic `T² − s = 0`
over `ℚ[x]`. -/
abbrev ch2_splitExact := @radSplitExact

/-- **`y/d` is integral: `s` is squarefree** `radSquarefreePartIsSquarefree ρ` (Trager, Chapter 2 §5,
p. 31): `gcd(s, s') = 1`, so `(y/d)² = s` is squarefree and `y/d` is a root of the monic `T² − s ∈ ℚ[x][T]`
— the integral closure contains it. -/
abbrev ch2_squarefreePartIsSquarefree := @radSquarefreePartIsSquarefree

/-- **`y/(d·P)` is NOT integral** `radNotIntegralFactor ρ P` (Trager, Chapter 2 §5, p. 31, maximality):
for nonconstant `P`, `P² ∤ s` (since `s` is squarefree), so `y/(d·P)` would need the non-polynomial minimal
polynomial `T² − s/P²` — hence `y/d` is the MAXIMAL integral element of the form `y/q`. -/
abbrev ch2_notIntegralFactor := @radNotIntegralFactor

/-! ## ★ The integral-basis validation capstone (Ch. 2 §5) -/

/-- **★ THE SIMPLE-RADICAL INTEGRAL BASIS COMPUTES AND VALIDATES** (Trager, Chapter 2 §5, p. 29–31,
`native_decide`): for the radicands `x³+1` (basis `[1, y]`), `x²(x+1)` (basis `[1, y/x]`), and `x⁴(x−1)`
(basis `[1, y/x²]`), the split `ρ = d²·s` is EXACT (`s ∈ ℚ[x]`), `s` is SQUAREFREE (so `y/d` is INTEGRAL),
and `y/(d·P)` is NOT integral (so `y/d` is MAXIMAL) — i.e. `[1, y/d]` realized as the integral closure of
`ℚ[x]` in `ℚ(x)[y]/(y²−ρ)`, end to end. -/
abbrev ch2_integralBasis_validates := @radIntegralBasis_validates

/-! ## Discriminant and genus of the simple-radical basis (Ch. 2 §4–§5) -/

/-- **Basis discriminant** `radBasisDiscriminant ρ = 4·s` (Trager, Chapter 2 §5, p. 30): the
discriminant `disc(T² − s) = 4s` of the minimal polynomial of the basis element `y/d`
(`s = radSquarefreePart ρ`). -/
abbrev ch2_basisDiscriminant := @radBasisDiscriminant

/-- **Genus** `radGenus ρ = ⌈deg s / 2⌉ − 1` (Trager, Chapter 2 §4, p. 29): the genus of the
hyperelliptic curve `y² = s` (`s` squarefree of degree `m`), Trager's `g = d/2 − [K(x,y):K(x)] + 1`
specialized to the simple radical `y² = s`. -/
abbrev ch2_genus := @radGenus

/-- **★ THE GENUS OF THE SIMPLE-RADICAL CURVE COMPUTES** (Trager, Chapter 2 §4–§5, p. 29–31, hyperelliptic
`g = ⌈deg s/2⌉ − 1`, `native_decide`): `y² = x` is rational (`g = 0`), `y² = x³+1` is elliptic (`g = 1`),
`y² = x⁵+1` is genus `2` — read off the squarefree part `s` of the integral-basis computation. -/
abbrev ch2_genus_validates := @radGenus_validates

end DeepWiki.Tiaf
