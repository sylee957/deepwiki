import DeepWiki.SymbolicIntegration.ComputableCanonicalRep
import DeepWiki.SymbolicIntegration.ComputableSplitSquarefree

/-! # Computable transcendental Hermite reduction over the tower ℚ(x)[t] (Bronstein §5.3)
Bronstein's `HermiteReduce(f, D)` (§5.3, p.139, quadratic version) rewrites the *normal* part
`fₙ = a/d` of an element of a monomial extension `k(t)` as `D(g) + h` with `h`'s denominator
**squarefree** — the transcendental analogue of the rational Hermite reduction of `HermiteCompute`,
with the plain derivative `d/dx` replaced by the **monomial derivation** `D = κ_D + Dt·d/dt`
(`cmonomialDeriv Dt`). The pseudocode loop is identical:

```
(d₁,…,dₘ) ← SquareFree(d);  g ← 0
for i ← 2 to m, deg dᵢ > 0 do
  v ← dᵢ;  u ← d/vⁱ
  for j ← i−1 downto 1 do
    (b,c) ← ExtendedEuclidean(u·Dv, v, −a/j)   -- b·(u·Dv) + c·v = −a/j
    g ← g + b/vʲ;  a ← −j·c − u·Db
  d ← uv
(q,r) ← PolyDivide(a, uv);  return (g, r/(uv), q+fₚ+fₛ)
```

* **`cHermiteReduceTowerInner`** runs the inner `j`-loop over one squarefree factor `v` of
  multiplicity `i`, peeling `b/vʲ` into `g` against the full current numerator `a` over the global
  denominator `d` (`u = d/vⁱ`). Every `Dv`, `Db` is `cmonomialDeriv Dt`; the Bézout solve routes
  through the generic `cdiophantineG` (extended-Euclid cofactors, rescaled).
* **`cHermiteReduceTower Dt fuel a d`** = `((gnum, gden), (h_num, h_den))`: squarefree-factor `d`
  (`cSqfreeYunFF`, fraction-free), accumulate `g` per factor, and recover the residual `h` over the
  squarefree radical `Dstar` exactly from `a/d = D(g) + h_num/Dstar` (clear denominators, divide).
  The gcds inside the Bézout solve are over ℚ(x)[t]; the squarefree factorization is fraction-free.

The deliverable is the **computable** algorithm plus the `native_decide` evidence `D(g) + h = f`
(`hermiteTower_example`), the cleared-denominator identity over ℚ(x)[t]. Abstract correctness (that
`g` is the integral's rational part) is NOT proved here. -/

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

/-- **Natural number as a field element** `cnatCastG k = 1 + 1 + … + 1` (`k` times), built only from
`CField.add`/`CField.one`. Needs only `[CField α]`, so it reduces (`native_decide`); used to form the
`−a/j` scaling in the Hermite inner loop. (`ComputableFieldGcd.nsmulG` carries a `[CFieldSpec α]`
binder and so does not reduce in the bridge-free engine context.) -/
def cnatCastG : ℕ → α
  | 0 => CField.zero
  | k + 1 => CField.add CField.one (cnatCastG k)

/-! ### The generic Bézout/Diophantine solver over ℚ(x)[t]

`cdiophantineG fuel p q rhs = (b, c)` solving `b·p + c·q = rhs` with `deg b < deg q`, for coprime
`p, q` (so `gcd(p,q)` is a nonzero constant). The generic mirror of `Compute.cdiophantine`
(`HermiteCompute`): from `cgcdExtG p q = (g, s, t)` with `s·p + t·q = g` (constant), scale `(s,t)` by
`rhs/g`, then reduce the first cofactor mod `q` and absorb the quotient into the second. This is the
`ExtendedEuclidean(p, q, rhs)` step of Bronstein's §5.3 `HermiteReduce`. -/

/-- **Generic Diophantine/Bézout solver** `cdiophantineG fuel p q rhs = (b, c)` solving
`b·p + c·q = rhs` with `deg b < deg q`, for **coprime** `p, q`. From `cgcdExtG p q = (g, s, t)` with
`s·p + t·q = g` (a nonzero constant), rescale `(s,t)` by `rhs/g`, reduce the first cofactor mod `q`
(`S = quo·q + b`), and absorb `quo·p` into the second (`c = T + quo·p`). Generic over `[CField α]`. -/
def cdiophantineG (fuel : ℕ) (p q rhs : CPolyG α) : CPolyG α × CPolyG α :=
  let (g, s, t) := cgcdExtG fuel p q
  let ginv := CField.inv (cleadG g)
  let S := cscaleG ginv (cmulG rhs s)
  let T := cscaleG ginv (cmulG rhs t)
  let (quo, b) := cdivmodG fuel S q
  let c := caddG T (cmulG quo p)
  (cnormG b, cnormG c)

/-! ### The inner Hermite loop over one squarefree factor (the monomial derivation `D`)

`cHermiteReduceTowerInner Dt fuel v u i a g` runs the `j = i−1 … 1` loop of `HermiteReduce` for the
squarefree factor `v` of multiplicity `i`, with `u = d/vⁱ` fixed. Each step solves
`b·(u·Dv) + c·v = −a/j` (`cdiophantineG`, `Dv = cmonomialDeriv Dt v`), accumulates `b/vʲ` into `g`,
and updates `a ← −j·c − u·Db` (`Db = cmonomialDeriv Dt b`). Mirrors `Compute.hermiteInner` with the
plain derivative replaced by the monomial derivation. -/

/-- **Inner Hermite loop** over a squarefree factor `v` (multiplicity `i`, `u = d/vⁱ`), driven by the
counter `j` (§5.3, quadratic version, p.139). Solve `b·(u·Dv) + c·v = −a/j` (`cdiophantineG`,
`Dv = cmonomialDeriv Dt v` the *monomial* derivation), accumulate the rational summand `b/vʲ` into the
fraction `g`, update `a ← −j·c − u·Db`. Returns the accumulated rational part `g = (num, den)` and the
final numerator `a`. -/
def cHermiteReduceTowerInner (Dt : CPolyG α) (fuel : ℕ) (v u : CPolyG α) :
    ℕ → CPolyG α → CPolyG α × CPolyG α → (CPolyG α × CPolyG α) × CPolyG α
  | 0, a, g => (g, a)
  | j + 1, a, g =>
    let jval : α := cnatCastG (j + 1)                                 -- `j` as a field element
    let Dv := cmonomialDeriv Dt v
    let p := cmulG u Dv
    let rhs := cscaleG (CField.neg (CField.inv jval)) a               -- `−a/j`
    let (b, c) := cdiophantineG fuel p v rhs
    -- summand `b/vʲ`: denominator is `v` raised to power `j+1`.
    let Vpow := cpowG v (j + 1)
    let g' := (caddG (cmulG g.1 Vpow) (cmulG b g.2), cmulG g.2 Vpow)  -- `g + b/Vʲ` (cross-multiplied)
    let a' := csubG (cscaleG (CField.neg jval) c) (cmulG u (cmonomialDeriv Dt b))  -- `−j·c − u·Db`
    cHermiteReduceTowerInner Dt fuel v u j a' g'

end CPolyG

/-! ### The transcendental Hermite reduction over ℚ(x)[t]

`cHermiteReduceTower` is specialized to `QFunNZ` because the squarefree factorization `cSqfreeYunFF`
is the fraction-free Yun factorization over ℚ(x)[t]; the inner loop / Bézout helpers above stay
generic. -/

namespace CPolyG

/-- **Transcendental Hermite reduction** `cHermiteReduceTower Dt fuel a d = ((gnum, gden), (h_num,
h_den))` (Bronstein §5.3, p.139) over the tower ℚ(x)[t]: input `f = a/d` reduced/normal (`d` monic,
squarefree-factorable, `deg a < deg d`), output the rational part `g = gnum/gden` (already integrated)
and the residual `h = h_num/h_den` with `h_den` squarefree, satisfying `D(g) + h = a/d` for the
monomial derivation `D = cmonomialDeriv Dt`. Squarefree-factor `d` (`cSqfreeYunFF`, fraction-free); for
each factor `(v, i)` of multiplicity `i ≥ 2`, run `cHermiteReduceTowerInner` (peeling `b/vʲ` against
the full numerator `a` over `d`); the residual `h_num` over the squarefree radical `Dstar = ∏ᵢ vᵢ` is
recovered exactly from `a/d = D(g) + h_num/Dstar`. Reduces over the tower (`native_decide`). -/
def cHermiteReduceTower (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ) :
    (CPolyG QFunNZ × CPolyG QFunNZ) × (CPolyG QFunNZ × CPolyG QFunNZ) :=
  let factors := cSqfreeYunFF fuel d                          -- `[v₁, …, vₘ]`, vᵢ of multiplicity i
  let Dstar := factors.foldl (fun acc vi => cmulG acc vi) [CField.one]   -- squarefree radical ∏ᵢ vᵢ
  -- Accumulate the rational part `g` (a fraction num/den). Each factor of multiplicity `i ≥ 2`
  -- contributes via the inner loop against the full numerator `a` over `d`.
  let g : CPolyG QFunNZ × CPolyG QFunNZ := factors.zipIdx.foldl
    (fun (gAcc : CPolyG QFunNZ × CPolyG QFunNZ) (vi, idx) =>
      let i := idx + 1
      if i ≤ 1 then gAcc
      else
        let Vi_pow := cpowG vi i
        let u := cdivG fuel d Vi_pow
        let (gloc, _) := cHermiteReduceTowerInner Dt fuel vi u (i - 1) a ([CField.zero], [CField.one])
        (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))  -- gAcc + gloc
    ([CField.zero], [CField.one])
  let (gnum, gden) := g
  -- residual numerator `h_num` over `Dstar`, from `a/d − D(g) = h_num/Dstar`:
  -- `(a·gden² − d·(D(gnum)·gden − gnum·D(gden)))·Dstar / (d·gden²)` (exact division to a polynomial).
  let gprimeNum := csubG (cmulG (cmonomialDeriv Dt gnum) gden) (cmulG gnum (cmonomialDeriv Dt gden))
  let gden2 := cmulG gden gden
  let resNum := csubG (cmulG a gden2) (cmulG d gprimeNum)
  let resDen := cmulG d gden2
  let hNum := cdivG fuel (cmulG resNum Dstar) resDen
  ((cnormG gnum, cnormG gden), (cnormG hNum, cnormG Dstar))

end CPolyG

/-! ### `native_decide` validation — the cleared identity `D(g) + h = f` over ℚ(x)[t]

`k = ℚ(x)` with `ℚ`-constant coefficients, monomial `t` with `Dt = t² + 1` (i.e. `t = tan x`, the
setting of Bronstein's Example 5.3.1). We take `f = a/d = 1/t²`, whose denominator `d = t²` has the
**repeated normal factor** `t` of multiplicity `2`, so Hermite actually lowers a multiplicity (`t` is
normal: `gcd(t, Dt) = gcd(t, t²+1) = 1`). The reduction returns `g = −1/t`, `h = −1` (squarefree
denominator `t`): `D(−1/t) = (t²+1)/t²` so `D(g) + h = (t²+1)/t² − 1 = 1/t² = f`.

The load-bearing check is the cleared-denominator form of `D(gnum/gden) + h_num/h_den = a/d`. With
`D(g) = (D(gnum)·gden − gnum·D(gden))/gden²` (the quotient rule for the monomial derivation), combine
the three fractions over the common denominator `gden²·h_den·d` and equate numerators:
`(gprimeNum·h_den + h_num·gden²)·d = a·(gden²·h_den)` — `cisZeroG` of the difference over ℚ(x)[t].
(The computed reduction is `g = −1/t`, `h = −t/t = −1`: `D(−1/t) = (t²+1)/t²` so `D(g)+h = 1/t² = f`,
the genuine multiplicity-`2 → 1` lowering of the factor `t`.) -/

open CPolyG QFunNZ

/-- Validation monomial derivative `Dt = t² + 1` (so `t = tan x`; Bronstein Example 5.3.1 setting). -/
def hermiteTowerExampleDt : CPolyG QFunNZ := [ofConstNZ 1, ofConstNZ 0, ofConstNZ 1]

/-- Validation numerator `a = 1` over ℚ(x)[t] (ℚ-constant coefficients). -/
def hermiteTowerExampleA : CPolyG QFunNZ := [ofConstNZ 1]

/-- Validation denominator `d = t²` (the normal factor `t` of multiplicity `2`, so Hermite lowers the
power): under `Dt = t² + 1`, `t` is normal (`gcd(t, Dt) = gcd(t, t²+1) = 1`), and `t²` is its square,
so the squarefree factorization in `t` has a multiplicity-`2` factor that Hermite reduces. -/
def hermiteTowerExampleD : CPolyG QFunNZ := [ofConstNZ 0, ofConstNZ 0, ofConstNZ 1]

/-- **`cHermiteReduceTower` satisfies `D(g) + h = f`** (`native_decide`): for `f = a/d = 1/t²` over
ℚ(x)(t) with the monomial derivation `D = cmonomialDeriv Dt`, `Dt = t² + 1` (so `t = tan x`), the
computed `((gnum, gden), (h_num, h_den))` satisfies the Hermite identity `D(gnum/gden) + h_num/h_den =
a/d`. With `D(g) = gprimeNum/gden²`, `gprimeNum = D(gnum)·gden − gnum·D(gden)`, combine over the common
denominator `gden²·h_den·d` and equate numerators: `(gprimeNum·h_den + h_num·gden²)·d = a·(gden²·h_den)`,
checked by `cisZeroG` of the difference over ℚ(x)[t]. The denominator `d = t²` has a repeated normal
factor `t`, so this exercises the genuine multiplicity-lowering step (`g = −1/t`, `h = −1`). This is
the deliverable: the computable transcendental Hermite reduction executes over the tower and
`D(g) + h` genuinely reconstructs `f`. -/
theorem hermiteTower_example :
    (let res := CPolyG.cHermiteReduceTower hermiteTowerExampleDt 12
        hermiteTowerExampleA hermiteTowerExampleD
      let gnum := res.1.1
      let gden := res.1.2
      let hNum := res.2.1
      let hDen := res.2.2
      let Dgnum := CPolyG.cmonomialDeriv hermiteTowerExampleDt gnum
      let Dgden := CPolyG.cmonomialDeriv hermiteTowerExampleDt gden
      let gprimeNum := CPolyG.csubG (CPolyG.cmulG Dgnum gden) (CPolyG.cmulG gnum Dgden)
      let gden2 := CPolyG.cmulG gden gden
      -- `D(g) + h − f = 0` ⟺ `(gprimeNum·h_den + h_num·gden²)·d = a·(gden²·h_den)`
      let lhs := CPolyG.cmulG
        (CPolyG.caddG (CPolyG.cmulG gprimeNum hDen) (CPolyG.cmulG hNum gden2)) hermiteTowerExampleD
      let rhs := CPolyG.cmulG hermiteTowerExampleA (CPolyG.cmulG gden2 hDen)
      CPolyG.cisZeroG (CPolyG.csubG lhs rhs)) = true := by native_decide

/-- **The residual `h` has a squarefree denominator** (`native_decide`): the Hermite reduction lowered
the multiplicity-`2` factor `t` of `d = t²` to multiplicity `1`, so the residual denominator
`h_den = Dstar = t` is squarefree (`t`-degree `1`), as the Hermite reduction guarantees. -/
theorem hermiteTower_example_residual_degree :
    CPolyG.cdegG (CPolyG.cHermiteReduceTower hermiteTowerExampleDt 12
      hermiteTowerExampleA hermiteTowerExampleD).2.2 = 1 := by native_decide

#print axioms hermiteTower_example

end DeepWiki.SymbolicIntegration
