import DeepWiki.SymbolicIntegration.ComputableGenericBezout
import DeepWiki.SymbolicIntegration.ComputableMonomialDeriv

/-! # The generic inner Hermite loop over the monomial derivation (`[CField α] [CDiffField α]`)
`cHermiteReduceTowerInner` runs the `j`-loop of Bronstein's §5.3 `HermiteReduce` over one squarefree
factor `v`, driven by the **monomial derivation** `cmonomialDeriv Dt`. It is generic over a
computable differential field `[CField α] [CDiffField α]` — the `QFunNZ`-specific squarefree
factorization (`cSqfreeYunFF`) that calls it lives in `ComputableHermiteTower`. -/

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

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

end DeepWiki.SymbolicIntegration
