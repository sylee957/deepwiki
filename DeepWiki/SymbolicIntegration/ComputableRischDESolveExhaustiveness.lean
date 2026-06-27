import DeepWiki.SymbolicIntegration.ComputableRischDENormCompleteness
import DeepWiki.SymbolicIntegration.ComputableRischDEStructural

/-! # §6.4–6.6 RDE completeness — the SPDE + poly-RDE solve is exhaustive (`hsolve`)

`RischDEInnerCompleteness` (`ComputableRischDECompleteness`) decomposes the deep §6 inner-solve
completeness into three converse clauses, `hnorm` / `hbound` / `hsolve`. `hnorm` is produced (modulo a
Bronstein-Thm-6.1.2 divisibility) by `ComputableRischDENormCompleteness`; `hbound` modulo a §6.3
cancellation residual by `ComputableRischDEDegreeBound`. This file pursues `hsolve` — the **last and
deepest** clause.

**What `hsolve` says.** `hsolve` is the SEARCH-EXHAUSTIVENESS of the §6.4 SPDE peel (`cSPDEG`) +
§6.5/§6.6 poly-RDE dispatcher (`cPolyRischDEG`): *if the input RDE has a polynomial solution then the
assembled solve `cRischDEG` does not return `none`* —
`(∃ ynum yden, IsCRischDEGPolySol …) → (cRischDEG …).isSome = true`. It is the **reverse** of the
soundness recursion `cSPDEG_cleared_lifting_gen` / `cPolyRischDENoCancelG_cleared_identity_gen` (whose
forward `some ⟹ cleared-identity` is the proven soundness arc). Keep it **independent of whether the bound
is correct** (that is `hbound`'s job): exhaustiveness is *within the bound the engine searches to*.

**The control-flow skeleton (fully reachable, closed here axiom-clean).** `cRischDEG`'s body is a nested
`match` over three stages — §6.2 `cRdeNormalDenominatorG`, §6.4 `cSPDEG` at the §6.3 bound degree on the
special-cleared coefficients, §6.5/§6.6 `cPolyRischDEG` — and a final reassembly. So `cRischDEG … = some _`
**iff** each of those three stages returns `some` (the converse of `cRischDEG_some_imp_stages`):

* `cRischDEG_isSome_of_stages` — the §6.2/§6.4/§6.5 successes force `cRischDEG.isSome = true` (pure control
  flow, no §6 mathematics);
* `cRischDEG_isSome_iff_stages` — the exact `isSome ↔ all-three-`some`` reading.

**The reachable base layer (closed here).** `cPolyRischDEG`'s `b = 0` branch is **pure integration**
(`cIntegratePolyG`, the term-by-term antiderivative, which is *total*), and `cPolyRischDENoCancelG`'s
`c = 0` short-circuit is total. So the genuinely *base* sub-cases of the dispatcher are exhaustive
unconditionally:

* `cPolyRischDENoCancelG_isSome_of_cZero` — `c = 0` ⟹ the non-cancellation solve returns `some []`;
* `cPolyRischDEG_isSome_of_bZero` — `b = 0` (with the engine's `deg c + 1 ≤ n` integration guard) ⟹ the
  dispatcher returns `some` (`cIntegratePolyG c`).

**The deep residual (precisely isolated, NEVER `sorry`).** The genuine exhaustiveness content — that a
polynomial solution survives the §6.4 SPDE peel **and** the §6.5/§6.6 poly-RDE dispatcher — is the reverse
of the entire §6.4–6.6 soundness recursion: (a) the SPDE per-step **solution-preservation inverse** (a
solution of the original `a·Dq + b·q = c` descends to a solution of the reduced equation, and the base
constant peel finds it), and (b) the poly-RDE dispatcher **exhaustiveness across the cancellation cases**
(non-cancellation top-down solve, primitive/hyperexponential cancellation recursions). Neither is
formalized in the engine (only the cleared-identity soundness is). We bundle them as the explicit, named
residuals `SPDEExhaustiveResidual` / `PolyRischDEExhaustiveResidual` and a §6.2-special-stage bridge
`RdeReducedSolExists`, and produce `hsolve` modulo them. This is the honest §6.4–6.6 exhaustiveness
frontier; each clause is the converse of a fact the soundness layer used forward. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ## The engine layer: `cRischDEG.isSome` is exactly the conjunction of the three stage `some`s

`cRischDEG`'s body is

  `match cRdeNormalDenominatorG … with | some (a0,b0,c0,h0) =>`
  `  let (a,b,c,h1) := cRdeSpecialDenominatorG Dt fuel a0 b0 c0`
  `  match cSPDEG Dt fuel a b c (cRdeBoundDegreeG Dt fuel a b c) with | some (bbar,cbar,m,α',β) =>`
  `    match cPolyRischDEG Dt fuel bbar cbar m with | some v => some ((α'·v+β)·h1, h0)`

so a `some` output requires (and is forced by) every guarded `match` selecting its `some`-branch.
`cRischDEG_some_imp_stages` (`ComputableRischDEStructural`) is the forward read; here we prove the
**converse** — the three stage `some`s force `cRischDEG.isSome` — which is the entry point of `hsolve`. -/

section EngineLayer

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α] [CRischField α]

/-- **★ The three stage `some`s force `cRischDEG.isSome`** (`cRischDEG_isSome_of_stages`, the converse of
`cRischDEG_some_imp_stages`): if the §6.2 normal-denominator step returns `some (a0, b0, c0, h0)`, the §6.4
SPDE step (at the §6.3 bound degree on the special-cleared coefficients) returns `some (bbar, cbar, m, α',
β)`, and the §6.5/§6.6 poly-RDE dispatcher returns `some v`, then the assembled solve succeeds —
`(cRischDEG Dt fuel fnum fden gnum gden).isSome = true`. Pure control flow: each `some` selects its
`match`-branch, so the reassembly `some ((α'·v + β)·h1, h0)` fires. The engine-layer entry point of the
§6.4–6.6 exhaustiveness `hsolve`. -/
theorem cRischDEG_isSome_of_stages (Dt : CPolyG α) (fuel : ℕ) (fnum fden gnum gden : CPolyG α)
    (a0 b0 c0 h0 bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α)
    (hnorm : cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0))
    (hspde : cSPDEG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
        (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β))
    (hpoly : cPolyRischDEG Dt fuel bbar cbar m = some v) :
    (cRischDEG Dt fuel fnum fden gnum gden).isSome = true := by
  rw [cRischDEG, hnorm]
  simp only [hspde, hpoly, Option.isSome_some]

/-- **The assembled solve succeeds iff the three stages succeed** (`cRischDEG_isSome_iff_stages`): the
exact `isSome`-reading of `cRischDEG`'s control flow —
`(cRischDEG …).isSome = true ↔ ∃ a0 b0 c0 h0 bbar cbar m α' β v, (the three stage `some`s)`. The `→` is the
structural decomposition `cRischDEG_some_imp_stages` (wrapped through `isSome`), the `←` is
`cRischDEG_isSome_of_stages`. The precise control-flow boundary on which `hsolve` rests: a solution forcing
`cRischDEG.isSome` is *exactly* a solution forcing all three stages to return `some`. -/
theorem cRischDEG_isSome_iff_stages (Dt : CPolyG α) (fuel : ℕ) (fnum fden gnum gden : CPolyG α) :
    (cRischDEG Dt fuel fnum fden gnum gden).isSome = true ↔
      ∃ (a0 b0 c0 h0 bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α),
        cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0)
        ∧ cSPDEG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1
            (cRdeBoundDegreeG Dt fuel (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).1
              (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.1
              (cRdeSpecialDenominatorG Dt fuel a0 b0 c0).2.2.1 : ℤ)
          = some (bbar, cbar, m, α', β)
        ∧ cPolyRischDEG Dt fuel bbar cbar m = some v := by
  constructor
  · intro h
    obtain ⟨⟨ynum, yden⟩, hy⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, hpoly, _, _⟩ :=
      cRischDEG_some_imp_stages Dt fuel fnum fden gnum gden ynum yden hy
    exact ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, hpoly⟩
  · rintro ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, hnorm, hspde, hpoly⟩
    exact cRischDEG_isSome_of_stages Dt fuel fnum fden gnum gden a0 b0 c0 h0 bbar cbar m α' β v
      hnorm hspde hpoly

end EngineLayer

/-! ## The reachable base layer: the dispatcher's total sub-cases are exhaustive unconditionally

`cPolyRischDEG`'s `b = 0` branch is **pure integration** — `cIntegratePolyG c`, the term-by-term
antiderivative, which is *total* and always succeeds once the engine's `deg c + 1 ≤ n` guard holds — and
`cPolyRischDENoCancelG`'s `c = 0` short-circuit returns `some []` unconditionally. These are the genuine
*base* sub-cases of the §6.5/§6.6 dispatcher: where the recursion bottoms, exhaustiveness holds with **no**
solution hypothesis (the engine simply returns the antiderivative / zero). Closed here axiom-clean — the
base case of the §6.4–6.6 exhaustiveness. -/

section BaseLayerNoCancel

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α]

omit [CFracGcdCore α] in
/-- **The non-cancellation solve succeeds on `c = 0`** (`cPolyRischDENoCancelG_isSome_of_cZero`): with one
unit of fuel and `cisZeroG c = true`, the §6.5 non-cancellation loop returns `some []` — the trivial
solution `q = 0` of `Dq + b·q = 0`. The `c = 0` short-circuit is *total*: no degree guard, no recursion. The
base case of `cPolyRischDENoCancelG`'s exhaustiveness. -/
theorem cPolyRischDENoCancelG_isSome_of_cZero (Dt : CPolyG α) (fuel : ℕ) (b c : CPolyG α) (n : ℤ)
    (hc : cisZeroG c = true) :
    (cPolyRischDENoCancelG Dt (fuel + 1) b c n).isSome = true := by
  rw [cPolyRischDENoCancelG, if_pos hc, Option.isSome_some]

end BaseLayerNoCancel

section BaseLayer

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α] [CRischField α]

omit [CFracGcdCore α] in
/-- **The dispatcher succeeds on `b = 0`, `c = 0`** (`cPolyRischDEG_isSome_of_bZero_cZero`): when both
`b = 0` and `c = 0` the equation `Dq + b·q = c` is `Dq = 0`, and the dispatcher returns `some []` (the zero
solution). The `b = 0`-integration branch's total `c = 0` short-circuit. -/
theorem cPolyRischDEG_isSome_of_bZero_cZero (Dt : CPolyG α) (fuel : ℕ) (b c : CPolyG α) (n : ℤ)
    (hb : cisZeroG b = true) (hc : cisZeroG c = true) :
    (cPolyRischDEG Dt fuel b c n).isSome = true := by
  rw [cPolyRischDEG]
  simp only [hb, if_true, hc, Option.isSome_some]

omit [CFracGcdCore α] in
/-- **The dispatcher succeeds on `b = 0` within the integration guard** (`cPolyRischDEG_isSome_of_bZero`):
when `b = 0` the equation `Dq + b·q = c` is the pure integration `Dq = c`, solved by the *total*
term-by-term antiderivative `cIntegratePolyG c` — so the dispatcher returns `some` whenever the engine's
integration guard `cdegG c + 1 ≤ n` holds (`¬ ((cdegG c : ℤ) + 1 > n)`). The `b = 0`-integration branch's
exhaustiveness: integration never fails inside its degree budget. -/
theorem cPolyRischDEG_isSome_of_bZero (Dt : CPolyG α) (fuel : ℕ) (b c : CPolyG α) (n : ℤ)
    (hb : cisZeroG b = true) (hn : ¬ ((cdegG c : ℤ) + 1 > n)) :
    (cPolyRischDEG Dt fuel b c n).isSome = true := by
  rw [cPolyRischDEG]
  simp only [hb, if_true]
  by_cases hc : cisZeroG c = true
  · simp only [hc, if_true, Option.isSome_some]
  · rw [Bool.not_eq_true] at hc
    simp only [hc, Bool.false_eq_true, if_false, if_neg hn, Option.isSome_some]

end BaseLayer

/-! ## The SPDE control-flow layer: when `cSPDEG.isSome` is forced (reachable, axiom-clean)

`cSPDEG`'s body, at `fuel + 1`, branches: `n < 0` returns `some` iff `cisZeroG c`; otherwise with
`g = cgcdFFCore fuel a b`, the divisibility gate `cdvdG fuel g c` decides — if it fails, `none` (no solution
of degree `≤ n`); if it holds, the constant-base sub-case `cdegG (a/g) = 0` returns `some` *directly*, and
the recursion sub-case `cdegG (a/g) ≠ 0` returns `some` iff the recursive peel succeeds. We read off each
forcing condition (the **converse** of the soundness peel `cSPDEG_cleared_lifting_gen`'s match-descent).
Pure control flow; the constant-base case is the genuine SPDE base of exhaustiveness. -/

section SPDELayer

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α]

/-- **`cSPDEG` succeeds on the `n < 0` base with `c = 0`** (`cSPDEG_isSome_of_neg_cZero`): with one unit of
fuel, `n < 0`, and `cisZeroG c = true`, the SPDE peel returns the all-zero tuple `some ([], [], 0, [], [])`
— the degenerate "no constraint, zero solution" base. The `n < 0` short-circuit, exhaustive when `c = 0`
(the only solvable sub-case there). -/
theorem cSPDEG_isSome_of_neg_cZero (Dt : CPolyG α) (fuel : ℕ) (a b c : CPolyG α) (n : ℤ)
    (hn : n < 0) (hc : cisZeroG c = true) :
    (cSPDEG Dt (fuel + 1) a b c n).isSome = true := by
  rw [cSPDEG, if_pos hn, if_pos hc, Option.isSome_some]

/-- **`cSPDEG` succeeds in the constant-base case** (`cSPDEG_isSome_of_const_base`): with one unit of fuel,
`¬ (n < 0)`, the gcd divisibility gate `cdvdG fuel g c = true` (`g = cgcdFFCore fuel a b`), and the divided
leading coefficient degenerate `cdegG (a/g) = 0`, the SPDE peel returns `some (…)` *directly* (with `α' = 1`,
`β = 0`, the reduced equation `Dh + (b/g/lc)·h = c/g/lc`). The genuine SPDE **base case** of exhaustiveness:
once `g ∣ c`, a constant `a/g` needs no recursion. -/
theorem cSPDEG_isSome_of_const_base (Dt : CPolyG α) (fuel : ℕ) (a b c : CPolyG α) (n : ℤ)
    (hn : ¬ (n < 0)) (hdvd : cdvdG fuel (CFracGcdCore.cgcdFFCore fuel a b) c = true)
    (hdeg : cdegG (cdivG fuel a (CFracGcdCore.cgcdFFCore fuel a b)) = 0) :
    (cSPDEG Dt (fuel + 1) a b c n).isSome = true := by
  rw [cSPDEG, if_neg hn]
  simp only [hdvd, hdeg, if_pos, Option.isSome_some]

/-- **`cSPDEG`'s `isSome` in the recursion case is exactly the sub-call's** (`cSPDEG_isSome_of_recurse`):
with one unit of fuel, `¬ (n < 0)`, the gcd gate `cdvdG fuel g c = true`, the divided leading coefficient
**non**-degenerate `cdegG (a/g) ≠ 0`, and the recursive SPDE peel on the reduced equation succeeding, the
SPDE peel returns `some` — the reassembly `some (bbar, cbar, m, a/g·α', a/g·β + r)` fires. The converse
control flow of the soundness peel's recursive descent: SPDE exhaustiveness reduces, level by level, to the
sub-problem's exhaustiveness. -/
theorem cSPDEG_isSome_of_recurse (Dt : CPolyG α) (fuel : ℕ) (a b c : CPolyG α) (n : ℤ)
    (hn : ¬ (n < 0)) (hdvd : cdvdG fuel (CFracGcdCore.cgcdFFCore fuel a b) c = true)
    (hdeg : cdegG (cdivG fuel a (CFracGcdCore.cgcdFFCore fuel a b)) ≠ 0)
    (hrec : (cSPDEG Dt fuel (cdivG fuel a (CFracGcdCore.cgcdFFCore fuel a b))
        (caddG (cdivG fuel b (CFracGcdCore.cgcdFFCore fuel a b))
          (cmonomialDeriv Dt (cdivG fuel a (CFracGcdCore.cgcdFFCore fuel a b))))
        (csubG (cdiophantineG fuel (cdivG fuel b (CFracGcdCore.cgcdFFCore fuel a b))
            (cdivG fuel a (CFracGcdCore.cgcdFFCore fuel a b))
            (cdivG fuel c (CFracGcdCore.cgcdFFCore fuel a b))).2
          (cmonomialDeriv Dt (cdiophantineG fuel (cdivG fuel b (CFracGcdCore.cgcdFFCore fuel a b))
            (cdivG fuel a (CFracGcdCore.cgcdFFCore fuel a b))
            (cdivG fuel c (CFracGcdCore.cgcdFFCore fuel a b))).1))
        (n - (cdegG (cdivG fuel a (CFracGcdCore.cgcdFFCore fuel a b)) : ℤ))).isSome = true) :
    (cSPDEG Dt (fuel + 1) a b c n).isSome = true := by
  rw [cSPDEG, if_neg hn]
  -- destructure the recursive `Option` via its `isSome` to a concrete `some`
  obtain ⟨⟨bbar, cbar, m, α', β⟩, hsome⟩ := Option.isSome_iff_exists.mp hrec
  -- the gcd gate fires, the constant-base guard fails, the recursive call is `some`, the reassembly fires
  simp only [hdvd, if_true, hdeg, hsome, if_false, Option.isSome_some]

end SPDELayer

end DeepWiki.SymbolicIntegration
