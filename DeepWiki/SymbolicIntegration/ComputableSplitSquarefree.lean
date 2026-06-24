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

/-! ### Sanity: a known squarefree-factored `p = (t−1)²(t−2)` over ℚ(x)[t]

With ℚ-constant coefficients (so the differential `cmonomialDeriv` for the *split* uses `Dt`), the
squarefree factorization in `t` of `p = (t−1)²(t−2) = t³ − 4t² + 5t − 2` is `p₁ = t−2` (multiplicity
`1`) and `p₂ = t−1` (multiplicity `2`), i.e. `p = p₁ · p₂²`. `native_decide` over the tower. -/

open CPolyG QFunNZ

/-- `p = (t−1)²(t−2) = t³ − 4t² + 5t − 2` over ℚ(x)[t] (ℚ-constant coefficients). -/
def sqfreeSanityP : CPolyG QFunNZ := [ofConstNZ (-2), ofConstNZ 5, ofConstNZ (-4), ofConstNZ 1]

/-- **Sanity (Yun factorization)**: the squarefree factorization in `t` of `(t−1)²(t−2)` is two
factors `[p₁, p₂]` of `t`-degrees `[1, 1]` (multiplicities `1, 2`). -/
example : (CPolyG.cSqfreeYunFF 8 sqfreeSanityP).map CPolyG.cdegG = [1, 1] := by native_decide

/-- **Sanity (multiplicity-1 factor)**: the first Yun factor of `(t−1)²(t−2)` is monic `t − 2`. -/
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonicG ((CPolyG.cSqfreeYunFF 8 sqfreeSanityP).headD []))
      [ofConstNZ (-2), ofConstNZ 1]) = true := by native_decide

/-- **Sanity (multiplicity-2 factor)**: the second Yun factor of `(t−1)²(t−2)` is monic `t − 1`. -/
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonicG ((CPolyG.cSqfreeYunFF 8 sqfreeSanityP).getD 1 []))
      [ofConstNZ (-1), ofConstNZ 1]) = true := by native_decide

/-! ### The payoff — Bronstein's Example 3.5.2 computes (`native_decide`)

Same `k = ℚ(x)`, monomial `t` with `Dt = −t² − (3/(2x))t + 1/(2x)`, and the SAME degree-5 `p` as
Example 3.5.1. Bronstein's worked answer (book p.102):

* squarefree factorization `p = p₁ p₂²` with `p₁` of `t`-degree `3`, `p₂` of `t`-degree `1`
  (`(p₁,…,pₘ) ← Squarefree(p)`);
* for `p₁`: `S₁ = gcd(p₁, Dp₁) = t² + (1/x)t − (2x−1)/(4x²)`, `N₁ = p₁/S₁ = 4x²(t−1)`;
* for `p₂`: `Dp₂ = −xt² − t/2 + 1/2`, `S₂ = gcd(p₂, Dp₂) = 1`, `N₂ = p₂/S₂ = xt − 1`;
* hence the normal part `pₙ = N₁N₂² = 4x²(t−1)(xt−1)²` and the special part `pₛ = S₁`.

`cSplitSquarefreeFactorFast` reproduces these: the `N`-factors recombine (by multiplicity `Nᵢ^i`,
monic) to `pₙ` and the `S`-factors to `pₛ`, checked by `cisZeroG` of the difference over ℚ(x)[t]. -/

/-- Example 3.5.2's expected special part `pₛ = S₁ = t² + (1/x)t − (2x−1)/(4x²)` (book p.102). -/
def splitSquarefreeFastEx352Ps : CPolyG QFunNZ :=
  [mkCoeff [1, -2] [0, 0, 4], mkCoeff [1] [0, 1], mkCoeff [1] [1]]

/-- The linear factor `t − 1` over ℚ(x)[t]. -/
def splitSquarefreeFastEx352Tm1 : CPolyG QFunNZ := [mkCoeff [-1] [1], mkCoeff [1] [1]]

/-- The linear factor `xt − 1` over ℚ(x)[t]. -/
def splitSquarefreeFastEx352Xtm1 : CPolyG QFunNZ := [mkCoeff [-1] [1], mkCoeff [0, 1] [1]]

/-- Example 3.5.2's expected normal part `pₙ = N₁N₂² = 4x²(t−1)(xt−1)²` (book p.102), built from its
factors `4x² · (t−1) · (xt−1)²`. -/
def splitSquarefreeFastEx352Pn : CPolyG QFunNZ :=
  CPolyG.cmulG [mkCoeff [0, 0, 4] [1]]
    (CPolyG.cmulG splitSquarefreeFastEx352Tm1
      (CPolyG.cmulG splitSquarefreeFastEx352Xtm1 splitSquarefreeFastEx352Xtm1))

/-- Recombine a positional-by-multiplicity factor list `[q₁, q₂, …]` into `∏ᵢ qᵢ^i`. -/
def splitSquarefreeFastRecombine (qs : List (CPolyG QFunNZ)) : CPolyG QFunNZ :=
  qs.zipIdx.foldl (fun acc (qi, i) => CPolyG.cmulG acc (CPolyG.cpowG qi (i + 1))) [CField.one]

/-- **Example 3.5.2 factor degrees** — `cSplitSquarefreeFactorFast` on the degree-5 `p` returns
`N`-factor `t`-degrees `[1, 1]` and `S`-factor `t`-degrees `[2, 0]`, matching Bronstein's
`N₁ = 4x²(t−1)`, `N₂ = xt−1`, `S₁ = t²+(1/x)t−(2x−1)/(4x²)`, `S₂ = 1`. -/
example :
    (((CPolyG.cSplitSquarefreeFactorFast splitFastExample351Dt 8 splitFastExample351P).1).map
        CPolyG.cdegG,
     ((CPolyG.cSplitSquarefreeFactorFast splitFastExample351Dt 8 splitFastExample351P).2).map
        CPolyG.cdegG) = ([1, 1], [2, 0]) := by native_decide

/-- **Example 3.5.2 normal part is the book's `pₙ`** — the `N`-factors recombine (by multiplicity) to
`4x²(t−1)(xt−1)²` (monic), via `cisZeroG` of the difference over ℚ(x)[t]. -/
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonicG (splitSquarefreeFastRecombine
        (CPolyG.cSplitSquarefreeFactorFast splitFastExample351Dt 8 splitFastExample351P).1))
      (CPolyG.cmonicG splitSquarefreeFastEx352Pn)) = true := by native_decide

/-- **Example 3.5.2 special part is the book's `pₛ`** — the `S`-factors recombine (by multiplicity)
to `t²+(1/x)t−(2x−1)/(4x²)` (monic), via `cisZeroG` of the difference over ℚ(x)[t]. -/
example :
    CPolyG.cisZeroG (CPolyG.csubG
      (CPolyG.cmonicG (splitSquarefreeFastRecombine
        (CPolyG.cSplitSquarefreeFactorFast splitFastExample351Dt 8 splitFastExample351P).2))
      (CPolyG.cmonicG splitSquarefreeFastEx352Ps)) = true := by native_decide

/-- **Example 3.5.2** (Bronstein §3.5, p.102) COMPUTES: the fraction-free `cSplitSquarefreeFactorFast`
on the degree-5 `p` over ℚ(x)[t] (monomial `t` with `Dt = −t²−(3/2x)t+1/(2x)`) returns `N`-factor
`t`-degrees `[1, 1]` and `S`-factor `t`-degrees `[2, 0]`, with the `N`-factors recombining (by
multiplicity) to Bronstein's normal part `pₙ = N₁N₂² = 4x²(t−1)(xt−1)²` and the `S`-factors to the
special part `pₛ = S₁ = t²+(1/x)t−(2x−1)/(4x²)` — all monic-normalized, by `native_decide`. -/
theorem splitSquarefreeFast_ex352 :
    (((CPolyG.cSplitSquarefreeFactorFast splitFastExample351Dt 8 splitFastExample351P).1).map
        CPolyG.cdegG,
       ((CPolyG.cSplitSquarefreeFactorFast splitFastExample351Dt 8 splitFastExample351P).2).map
        CPolyG.cdegG) = ([1, 1], [2, 0])
    ∧ CPolyG.cisZeroG (CPolyG.csubG
        (CPolyG.cmonicG (splitSquarefreeFastRecombine
          (CPolyG.cSplitSquarefreeFactorFast splitFastExample351Dt 8 splitFastExample351P).1))
        (CPolyG.cmonicG splitSquarefreeFastEx352Pn)) = true
    ∧ CPolyG.cisZeroG (CPolyG.csubG
        (CPolyG.cmonicG (splitSquarefreeFastRecombine
          (CPolyG.cSplitSquarefreeFactorFast splitFastExample351Dt 8 splitFastExample351P).2))
        (CPolyG.cmonicG splitSquarefreeFastEx352Ps)) = true := by native_decide

end DeepWiki.SymbolicIntegration
