import DeepWiki.SymbolicIntegration.ComputableSplitFactorFast

/-! # Computable `SplitSquarefreeFactor` over the tower ℚ(x)[t] — Bronstein Example 3.5.2
On top of the fraction-free `splitFactor` engine of `ComputableSplitFactorFast` (the `cgcdFF`
primitive-PRS gcd that defeats coefficient swell) we add the two pieces Bronstein's §3.5
`SplitSquarefreeFactor` needs over ℚ(x)[t]:

* **`cSqfreeYunFF fuel p`** — Yun's squarefree factorization in `t` (the *formal* derivative `dp/dt`,
  NOT the differential `D`): `g = cgcdFF p (cderivG p)`, `b₁ = p/g`, `d₁ = p'/g − b₁'`, and the
  recurrence `pᵢ = cgcdFF bᵢ dᵢ`, `bᵢ₊₁ = bᵢ/pᵢ`, `dᵢ₊₁ = dᵢ/pᵢ − bᵢ₊₁'`. Returns the
  position-indexed list `[p₁, p₂, …, pₘ]` (`pᵢ` the squarefree part of multiplicity `i`, monic; an
  absent multiplicity is the unit `[1]`), so `p` is associate to `∏ᵢ pᵢ^i`. Every gcd is `cgcdFF`,
  every exact division `cdivG`.

* **`cSplitSquarefreeFactorFast Dt fuel p`** (Bronstein Fig. §3.5, p.102) — for each Yun factor `pᵢ`,
  `Sᵢ = cgcdFF pᵢ (cmonomialDeriv Dt pᵢ)` (the *special* part, via the DIFFERENTIAL `cmonomialDeriv`)
  and `Nᵢ = pᵢ/Sᵢ` (the *normal* part); returns `((N₁,…,Nₘ), (S₁,…,Sₘ))`.

* **The payoff (`splitSquarefreeFast_ex352`)**: on Example 3.5.1's degree-5 `p` over ℚ(x)[t]
  (`Dt = −t²−(3/2x)t+1/(2x)`), `cSplitSquarefreeFactorFast` reproduces Bronstein's worked answer
  (book p.102): squarefree splitting `p = p₁ p₂²`, normal part `pₙ = N₁N₂² = 4x²(t−1)(xt−1)²`, special
  part `pₛ = S₁ = t²+(1/x)t−(2x−1)/(4x²)` — pinned by `native_decide` (monic-normalized recombination,
  via `cisZeroG` of the difference). -/

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

/-! ### Yun squarefree factorization in `t` over ℚ(x)[t] (fraction-free gcd) -/

/-- Yun's main loop (fraction-free): from `(b, d, i)` emit `pᵢ = cgcdFF b d` (monic), recurse on
`bᵢ₊₁ = b/pᵢ`, `dᵢ₊₁ = d/pᵢ − bᵢ₊₁'`. Stops when `b` is constant. Each emitted `pᵢ` is monic (so an
absent multiplicity is the unit `[1]`), keeping the list **position-indexed by multiplicity**. -/
def cSqfreeYunFFgo (fuel : ℕ) : ℕ → CPolyG QFunNZ → CPolyG QFunNZ → List (CPolyG QFunNZ)
  | 0, _, _ => []
  | fo + 1, b, d =>
    if cdegG b = 0 then []
    else
      let p := cmonicG (cgcdFF fuel b d)
      let b' := cdivG fuel b p
      let d' := csubG (cdivG fuel d p) (cderivG b')
      p :: cSqfreeYunFFgo fuel fo b' d'

/-- **Yun squarefree factorization over ℚ(x)[t]** `cSqfreeYunFF fuel p = [p₁, p₂, …, pₘ]`: the
*purely-algebraic* squarefree factorization in `t` (the formal derivative `dp/dt = cderivG`, not the
differential `D`). With `g = cgcdFF p (cderivG p)`, `b₁ = p/g`, `d₁ = p'/g − b₁'`, the recurrence
`pᵢ = cgcdFF bᵢ dᵢ` peels the monic squarefree part of multiplicity `i`. `p` is associate to
`∏ᵢ pᵢ^i`. All gcds are fraction-free (`cgcdFF`), so it reduces over the tower (`native_decide`). -/
def cSqfreeYunFF (fuel : ℕ) (p : CPolyG QFunNZ) : List (CPolyG QFunNZ) :=
  let g := cgcdFF fuel p (cderivG p)
  let b1 := cdivG fuel p g
  let d1 := csubG (cdivG fuel (cderivG p) g) (cderivG b1)
  cSqfreeYunFFgo fuel fuel b1 d1

/-! ### Bronstein's `SplitSquarefreeFactor` (Fig. §3.5, p.102) -/

/-- **Computable `SplitSquarefreeFactor`** (Bronstein §3.5, p.102): `cSplitSquarefreeFactorFast Dt
fuel p = ((N₁,…,Nₘ), (S₁,…,Sₘ))`. First `(p₁,…,pₘ) ← cSqfreeYunFF p` (squarefree factorization in
`t`); then for each `i`, `Sᵢ = cgcdFF pᵢ (cmonomialDeriv Dt pᵢ)` is the **special** part (using the
DIFFERENTIAL `cmonomialDeriv`) and `Nᵢ = pᵢ/Sᵢ` the **normal** part. Reduces over ℚ(x)[t]. -/
def cSplitSquarefreeFactorFast (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ) :
    List (CPolyG QFunNZ) × List (CPolyG QFunNZ) :=
  let ps := cSqfreeYunFF fuel p
  let parts := ps.map (fun pi =>
    let Si := cgcdFF fuel pi (cmonomialDeriv Dt pi)
    let Ni := cdivG fuel pi Si
    (Ni, Si))
  (parts.map Prod.fst, parts.map Prod.snd)

end CPolyG

end DeepWiki.SymbolicIntegration
