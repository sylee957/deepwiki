import DeepWiki.SymbolicIntegration.ComputableGenericBezout
import DeepWiki.SymbolicIntegration.ComputableMonomialDeriv

/-! # The generic inner Hermite loop over the monomial derivation (`[CField α] [CDiffField α]`)
`cHermiteReduceTowerInner` runs the `j`-loop of Bronstein's §5.3 `HermiteReduce` over one squarefree
factor `v`, driven by the **monomial derivation** `cmonomialDeriv Dt`. It is generic over a
computable differential field `[CField α] [CDiffField α]` — the squarefree
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

/-! ### ★ The per-step cofactor degree bound — the keystone of Hermite properness

Each `cHermiteReduceTowerInner` step solves `b·(u·Dv) + c·v = −a/j` with `cdiophantineG`, accumulating the
summand `b/vʲ` into `g`. For the assembled rational part `g` to stay **proper** (the deep input to
`hproper`), each emitted `b` must satisfy `deg b < deg v` — exactly the reduced first cofactor of the
Bézout solve. `cdiophantineG`'s first component is `cnormG (cmodG fuel S v)` (the Euclidean remainder of
the rescaled `S` mod `v`), so its degree is `< deg v` by `cmodG_length_lt`. This is the transcendental
analogue of `diophantineSolveReduced_fst_degree_lt` — the per-step degree foundation a fold-induction
threads into `g`'s properness. The `hfuel` premise (enough fuel for the rescaled dividend) is what the
fuel-free `cdiophantineGWf` form discharges intrinsically. -/

variable [CFieldSpec α]

omit [CDiffField α] in
/-- **★ `cdiophantineG`'s first cofactor is proper** — the per-step Hermite keystone: the Bézout solve
`cdiophantineG fuel p q rhs = (b, c)` returns a first cofactor `b` with `deg b < deg q` (under nonzero
divisor `q` and enough fuel for the rescaled dividend). `b = cnormG (cmodG fuel S q)` is a Euclidean
remainder mod `q` (`S = (rhs·s)/lc(g)` from the extended gcd), so `cmodG_length_lt` bounds its normalized
length below `q`'s, and `toPolyG_degree_lt_of_length_lt` turns that into the `degree` bound. The
transcendental analogue of `diophantineSolveReduced_fst_degree_lt` — the per-step degree invariant the
Hermite `g`-fold needs to keep its rational part proper. -/
theorem cdiophantineG_fst_degree_lt (fuel : ℕ) (p q rhs : CPolyG α) (hq : cnormG q ≠ [])
    (hfuel : (cnormG (cscaleG (CField.inv (cleadG (cgcdExtG fuel p q).1))
        (cmulG rhs (cgcdExtG fuel p q).2.1)) : List α).length ≤ fuel) :
    (toPolyG (cdiophantineG fuel p q rhs).1).degree < (toPolyG q).degree := by
  -- `(cdiophantineG …).1 = cnormG (cmodG fuel S q)` (definitional).
  have hfst : (cdiophantineG fuel p q rhs).1
      = cnormG (cmodG fuel (cscaleG (CField.inv (cleadG (cgcdExtG fuel p q).1))
          (cmulG rhs (cgcdExtG fuel p q).2.1)) q) := rfl
  rw [hfst]
  refine toPolyG_degree_lt_of_length_lt _ _ hq ?_
  rw [cnormG_idem]
  exact cmodG_length_lt fuel _ q hq hfuel

end CPolyG

end DeepWiki.SymbolicIntegration
