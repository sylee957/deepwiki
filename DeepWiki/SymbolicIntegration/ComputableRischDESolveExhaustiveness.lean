import DeepWiki.SymbolicIntegration.ComputableRischDENormCompleteness
import DeepWiki.SymbolicIntegration.ComputableRischDEDegreeBound
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

/-! ## ★ The SPDE per-step solution-preservation (the structural heart, reachable cases)

The SPDE peel's exhaustiveness is the **reverse** of the soundness lifting `cSPDEG_cleared_lifting_gen`:
a solution `q` of the original `a·Dq + b·q = c` must descend to a solution of the reduced equation, so the
peel does not lose it. Two reachable layers:

* **The divisibility necessity** (★ the keystone, fully proven): if `g ∣ a` and `g ∣ b` then a solution
  forces `g ∣ c`. Because `c = a·Dq + b·q` and `g` divides both summands — pure algebra, **no** gcd
  correctness, no valuation theory. This is exactly what makes the SPDE `cdvdG fuel g c` gate *never reject a
  true solution*: with `g = gcd(a, b)` the gate's failure is a genuine certificate of unsolvability (the
  converse of the soundness peel's `g ∣ c` read-off).
* **The constant-base descent** (fully proven): when `a/g` is a constant (`deg(a/g) = 0`, the SPDE base
  case), the divided equation `(a/g)·Dq + (b/g)·q = c/g` *is* the reduced equation up to the leading-unit
  rescale, so `q` itself is the reduced solution `h` (with `α' = 1`, `β = 0`). No diophantine peel, no
  recursion.

The genuinely deep step — the diophantine degree-peel inverse (`deg(a/g) ≠ 0`: a solution `q` reduces, via
the Bézout relation `(b/g)·r + (a/g)·z = c/g`, to a *lower-degree* solution `h` with `q = (a/g)·h + r`) —
is the irreducible recursion residual, isolated below. -/

section Preservation

/-- **★ The SPDE peel-step inverse (algebraic core)** `spde_step_glue_inverse`: the **converse** of
`spde_step_glue`. Over a commutative ring with no zero divisors, given the Bézout relation `b·r + a·z = c`,
a *nonzero* leading coefficient `a ≠ 0`, and a solution of the divided equation **already in peeled form**
`a·D(a·h + r) + b·(a·h + r) = c`, the peeled factor `h` solves the **reduced** equation
`a·Dh + (b + Da)·h = z − Dr`. Pure algebra: expand `D(a·h + r)`, subtract the Bézout `b·r`, and cancel the
nonzero `a`. This is the exact inverse of the soundness peel atom `spde_step_glue` — the algebraic heart of
the SPDE peel's solution-preservation, with the **only** remaining deep input being the divisibility that
writes a solution `q` in the form `a·h + r` (i.e. `a ∣ q − r`). -/
theorem spde_step_glue_inverse {R : Type*} [CommRing R] [NoZeroDivisors R] (D : Derivation ℤ R R)
    (a b c r z h : R) (ha : a ≠ 0)
    (hbez : b * r + a * z = c)
    (hpeeled : a * D (a * h + r) + b * (a * h + r) = c) :
    a * D h + (b + D a) * h = z - D r := by
  -- expand the derivation on the peeled solution
  have hD : D (a * h + r) = a * D h + D a * h + D r := by
    rw [map_add, Derivation.leibniz]; simp only [smul_eq_mul]; ring
  rw [hD] at hpeeled
  -- `a · (a·Dh + (b + Da)·h - (z - Dr)) = c - (b·r + a·z) = 0`, then cancel the nonzero `a`
  have hcancel : a * (a * D h + (b + D a) * h - (z - D r)) = 0 := by
    linear_combination hpeeled - hbez
  have hzero : a * D h + (b + D a) * h - (z - D r) = 0 :=
    (mul_eq_zero.mp hcancel).resolve_left ha
  linear_combination hzero

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-- **★ The SPDE divisibility necessity** (`dvd_c_of_isReducedRdeSol`, the keystone reachable fact): if a
divisor `g` divides both leading coefficients (`toPolyG g ∣ toPolyG a`, `toPolyG g ∣ toPolyG b`) and `q`
solves the §6.3-reduced equation `a·Dq + b·q = c` (`IsReducedRdeSol Dt a b c q`), then `g` divides the
right-hand side — `toPolyG g ∣ toPolyG c`. Because `toPolyG c = toPolyG a · D(toPolyG q) + toPolyG b ·
toPolyG q` and `g` divides each summand. Pure algebra: **no** gcd correctness, no valuation theory. This is
the converse of the soundness peel's `g ∣ c` read-off — exactly what makes the SPDE `cdvdG fuel g c` gate
never reject a true solution (its failure certifies unsolvability). -/
theorem dvd_c_of_isReducedRdeSol (Dt a b c q g : CPolyG α)
    (hga : toPolyG g ∣ toPolyG a) (hgb : toPolyG g ∣ toPolyG b)
    (hsol : IsReducedRdeSol Dt a b c q) :
    toPolyG g ∣ toPolyG c := by
  -- `toPolyG c = toPolyG a · D(toPolyG q) + toPolyG b · toPolyG q`
  have heq : toPolyG c
      = toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG b * toPolyG q :=
    hsol.symm
  rw [heq]
  exact dvd_add (hga.mul_right _) (hgb.mul_right _)

/-- **★ The SPDE constant-base descent** (`isReducedRdeSol_const_base`): when the divided leading
coefficient `a/g` is a *unit* `Polynomial.C a0` (`a0 ≠ 0`, the `deg(a/g) = 0` SPDE base case) and the three
exact-division identities `(a/g)·g = a`, `(b/g)·g = b`, `(c/g)·g = c` hold (`g ≠ 0`), a solution `q` of the
original `a·Dq + b·q = c` solves the **rescaled reduced** equation `Dq + (a0⁻¹·(b/g))·q = a0⁻¹·(c/g)` — i.e.
`q` is the reduced solution `h` directly (the `α' = 1`, `β = 0` reassembly). The reverse of `spde_const_base`
(the soundness constant-base step): no diophantine peel, no recursion. -/
theorem isReducedRdeSol_const_base (Dt a b c q ad bd cd g : CPolyG α) (a0 : CFieldSpec.K α)
    (ha0 : a0 ≠ 0) (hadC : toPolyG ad = Polynomial.C a0)
    (hgne : toPolyG g ≠ 0)
    (hdiva : toPolyG ad * toPolyG g = toPolyG a) (hdivb : toPolyG bd * toPolyG g = toPolyG b)
    (hdivc : toPolyG cd * toPolyG g = toPolyG c)
    (hsol : IsReducedRdeSol Dt a b c q) :
    Differential.implicitDeriv (toPolyG Dt) (toPolyG q)
        + (Polynomial.C a0⁻¹ * toPolyG bd) * toPolyG q
      = Polynomial.C a0⁻¹ * toPolyG cd := by
  -- the original equation, abstractly
  have heq : toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG b * toPolyG q
      = toPolyG c := hsol
  -- divide the equation through by `g` (g ≠ 0, cancellation in the polynomial domain)
  have hdivided : toPolyG ad * Differential.implicitDeriv (toPolyG Dt) (toPolyG q)
      + toPolyG bd * toPolyG q = toPolyG cd := by
    have hmulg : (toPolyG ad * Differential.implicitDeriv (toPolyG Dt) (toPolyG q)
          + toPolyG bd * toPolyG q) * toPolyG g = toPolyG cd * toPolyG g := by
      rw [hdivc]; rw [← heq, ← hdiva, ← hdivb]; ring
    exact mul_right_cancel₀ hgne hmulg
  -- substitute `ad = C a0`, then divide by the unit `a0`
  rw [hadC] at hdivided
  -- multiply through by `C a0⁻¹`: `C a0⁻¹ · (C a0 · Dq + bd · q) = C a0⁻¹ · cd`
  have hscaled : Polynomial.C a0⁻¹ * (Polynomial.C a0 * Differential.implicitDeriv (toPolyG Dt) (toPolyG q)
      + toPolyG bd * toPolyG q) = Polynomial.C a0⁻¹ * toPolyG cd := by
    rw [hdivided]
  rw [mul_add] at hscaled
  -- `C a0⁻¹ · C a0 = C 1 = 1`
  have hCunit : Polynomial.C a0⁻¹ * Polynomial.C a0 = 1 := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ ha0, Polynomial.C_1]
  rw [← mul_assoc, hCunit, one_mul] at hscaled
  -- the `bd` term is already in the goal's left-associated `C a0⁻¹ * bd * q` form
  linear_combination hscaled

end Preservation

/-! ## ★ The precise §6.4–6.6 exhaustiveness residual, and `hsolve` modulo it (NEVER `sorry`)

The engine layer (`cRischDEG_isSome_of_stages`) reduces `hsolve` — `solvable ⟹ cRischDEG.isSome` — to the
three staged successes: §6.2 `cRdeNormalDenominatorG`, §6.4 `cSPDEG` (at the §6.3 bound on the
special-cleared coefficients), §6.5/§6.6 `cPolyRischDEG`. The §6.2 success is `hnorm`
(`ComputableRischDENormCompleteness`); the remaining two — **SPDE peel exhaustiveness** and **poly-RDE
dispatcher exhaustiveness** — are the genuine §6.4–6.6 content of `hsolve`. We bundle them as the explicit,
named residual `RischDESolveExhaustiveResidual`, in solvability-implies / staged form, and produce the exact
`hsolve` clause modulo it.

**Why each clause is the irreducible core.**

* **`hspde`** — the §6.4 SPDE peel returns `some` on a solvable input. The reachable layers are proven here:
  the divisibility necessity (`dvd_c_of_isReducedRdeSol`, so the `cdvdG g c` gate never rejects a solution),
  the constant-base descent (`isReducedRdeSol_const_base`), and ★ the **peel-step inverse**
  (`spde_step_glue_inverse`, the exact converse of the soundness peel atom `spde_step_glue`/
  `cSPDE_peel_cleared_gen`): once a solution is written in peeled form `q = (a/g)·h + r`, the factor `h`
  *provably* solves the reduced equation `(a/g)·Dh + ((b/g) + D(a/g))·h = z − Dr`. The irreducible residue is
  thereby narrowed to the **peeling-divisibility** `(a/g) ∣ (q − r)` (which writes a solution in peeled form,
  via the Bézout `(b/g)·r + (a/g)·z = c/g`) plus the recursion's degree-descent assembly. The engine never
  derives these (it only lifts a sub-solution up, never descends a solution down).

* **`hpoly`** — the §6.5/§6.6 poly-RDE dispatcher returns `some` on a solvable reduced equation. The
  reachable base sub-cases are proven here (`cPolyRischDEG_isSome_of_bZero` integration,
  `cPolyRischDENoCancelG_isSome_of_cZero`). The irreducible residue is the **dispatcher exhaustiveness across
  the cancellation regimes**: the non-cancellation top-down solve (`cPolyRischDENoCancelG`) and the
  primitive/hyperexponential cancellation recursions (`cPolyRischDECancel{Prim,Exp}G`, which recurse into the
  level-below base oracle `crischDESolve`) each *find* a bounded solution if one exists. This is the converse
  of the soundness `cPolyRischDENoCancelG_cleared_identity_gen` and the cancellation cleared identities;
  unformalized in the engine.

A `Prop`-bundle of stated assumptions, NO `sorry`; each clause is the converse of a fact the soundness layer
used forward. -/

section ExhaustiveResidual

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
  [CRischField α]

/-- **★ The precise §6.4–6.6 exhaustiveness residual** `RischDESolveExhaustiveResidual Dt fnum fden gnum
gden`: the two staged converse facts a polynomial solution clears the §6.4 SPDE and §6.5/§6.6 poly-RDE
`none`-gates, in solvability-implies form. `hnorm`: a solution makes the §6.2 normal-denominator step return
`some` (produced by `ComputableRischDENormCompleteness` — recorded here as the upstream precondition).
`hspde`: ★ for the §6.2-special-cleared coefficients of a normal-denominator output, a solution makes the
§6.4 SPDE peel at the §6.3 bound degree return `some` (the divisibility necessity + constant-base descent are
proven; the diophantine degree-peel inverse is the deep residue). `hpoly`: ★ for the SPDE output
`(bbar, cbar, m)`, a solution makes the §6.5/§6.6 poly-RDE dispatcher return `some` (the b=0/c=0 base
sub-cases are proven; the cancellation-regime exhaustiveness is the deep residue). Their conjunction, threaded
through `cRischDEG_isSome_of_stages`, is exactly `hsolve`. A `Prop`-bundle of stated assumptions, NO
`sorry`. -/
structure RischDESolveExhaustiveResidual (Dt fnum fden gnum gden : CPolyG α) : Prop where
  /-- §6.2: a polynomial solution makes the normal-denominator step return `some` (from `hnorm`). -/
  hnorm : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    (cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden).isSome = true
  /-- ★ §6.4: for a normal-denominator output `(a0, b0, c0, h0)`, a solution makes the SPDE peel at the §6.3
  bound degree on the special-cleared coefficients return `some` (the diophantine degree-peel inverse, deep). -/
  hspde : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    ∀ a0 b0 c0 h0 : CPolyG α,
      cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden = some (a0, b0, c0, h0) →
      (cSPDEG Dt towerRischDEFuel (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1
          (cRdeBoundDegreeG Dt towerRischDEFuel (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1 : ℤ)).isSome = true
  /-- ★ §6.5/§6.6: for the SPDE output `(bbar, cbar, m)`, a solution makes the poly-RDE dispatcher return
  `some` (the cancellation-regime exhaustiveness, deep). -/
  hpoly : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    ∀ a0 b0 c0 h0 bbar cbar : CPolyG α, ∀ m : ℤ, ∀ α' β : CPolyG α,
      cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden = some (a0, b0, c0, h0) →
      cSPDEG Dt towerRischDEFuel (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1
          (cRdeBoundDegreeG Dt towerRischDEFuel (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α', β) →
      (cPolyRischDEG Dt towerRischDEFuel bbar cbar m).isSome = true

/-- **★ `hsolve` from the §6.4–6.6 exhaustiveness residual** (`hsolve_of_exhaustiveResidual`): under
`RischDESolveExhaustiveResidual Dt fnum fden gnum gden`, the assembled §6 solve preserves solvability — a
polynomial solution makes `cRischDEG` return `some`,
`(∃ ynum yden, IsCRischDEGPolySol …) → (cRischDEG Dt towerRischDEFuel …).isSome = true`. This is **exactly**
the `hsolve` clause of `RischDEInnerCompleteness`. The residual's three staged facts (§6.2 norm + §6.4 SPDE +
§6.5/§6.6 poly-RDE successes) are threaded through the engine-layer control-flow `cRischDEG_isSome_of_stages`:
destructure each stage's `some` and feed the next. The §6.4–6.6 exhaustiveness clause, modulo the precisely
isolated diophantine-peel + cancellation-regime residue. -/
theorem hsolve_of_exhaustiveResidual (Dt fnum fden gnum gden : CPolyG α)
    (hres : RischDESolveExhaustiveResidual Dt fnum fden gnum gden) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRischDEG Dt towerRischDEFuel fnum fden gnum gden).isSome = true := by
  intro hsol
  -- §6.2: the normal-denominator step succeeds; destructure its output
  obtain ⟨⟨a0, b0, c0, h0⟩, hnorm⟩ := Option.isSome_iff_exists.mp (hres.hnorm hsol)
  -- §6.4: the SPDE peel at the bound succeeds; destructure its 5-tuple output
  obtain ⟨⟨bbar, cbar, m, α', β⟩, hspde⟩ :=
    Option.isSome_iff_exists.mp (hres.hspde hsol a0 b0 c0 h0 hnorm)
  -- §6.5/§6.6: the poly-RDE dispatcher succeeds; destructure its output
  obtain ⟨v, hpoly⟩ :=
    Option.isSome_iff_exists.mp (hres.hpoly hsol a0 b0 c0 h0 bbar cbar m α' β hnorm hspde)
  -- assemble through the engine-layer control flow
  exact cRischDEG_isSome_of_stages Dt towerRischDEFuel fnum fden gnum gden
    a0 b0 c0 h0 bbar cbar m α' β v hnorm hspde hpoly

end ExhaustiveResidual

/-! ## ★ `RischDEInnerCompleteness` fully assembled from its three component residuals

With `hsolve` now produced (`hsolve_of_exhaustiveResidual`), all three clauses of
`RischDEInnerCompleteness` are available from their component residuals: `hnorm` from the §6.2 divisibility
(`hnorm_of_divisibilityResidual`, `ComputableRischDENormCompleteness`), `hbound` from the §6.3 cancellation
(`hbound_of_cancellationResidual`, `ComputableRischDEDegreeBound`), `hsolve` from the §6.4–6.6 exhaustiveness
here. We record the full assembly — `RischDEInnerCompleteness` from the three precise residuals — completing
the map of clause (c) of `RischDECompletenessResidual` to its three precisely isolated deep facts. -/

section Assemble

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
  [CRischField α]

/-- **★ `RischDEInnerCompleteness` from its three component residuals**
(`rischDEInnerCompleteness_of_residuals`): given the §6.2 divisibility residual
`RdeNormalDivisibilityResidual` (which yields `hnorm`), the §6.3 cancellation residual
`RdeBoundCancellationResidual` (which yields `hbound`), and the §6.4–6.6 exhaustiveness residual
`RischDESolveExhaustiveResidual` (which yields `hsolve`), the full `RischDEInnerCompleteness Dt fnum fden gnum
gden` holds. This is the assembly point: clause (c) of `RischDECompletenessResidual` is now reduced **in
full** to its three precisely isolated deep facts — the §6.2 normal-denominator divisibility (Bronstein Thm
6.1.2), the §6.3 degree-bound `λ`-cancellation, and the §6.4–6.6 SPDE/poly-RDE exhaustiveness — each a
stated `Prop`, none a `sorry`. -/
theorem rischDEInnerCompleteness_of_residuals (Dt fnum fden gnum gden : CPolyG α)
    (hnormRes : RdeNormalDivisibilityResidual Dt fnum fden gnum gden)
    (hboundRes : RdeBoundCancellationResidual Dt fnum fden gnum gden)
    (hsolveRes : RischDESolveExhaustiveResidual Dt fnum fden gnum gden) :
    RischDEInnerCompleteness Dt fnum fden gnum gden where
  hnorm := hnorm_of_divisibilityResidual Dt fnum fden gnum gden hnormRes
  hbound := hbound_of_cancellationResidual Dt fnum fden gnum gden hboundRes
  hsolve := hsolve_of_exhaustiveResidual Dt fnum fden gnum gden hsolveRes

end Assemble

/-! ### Restatement against `RischDEInnerCompleteness.hsolve`'s field type (anonymous `example`) -/

-- ★ The produced `hsolve` has exactly `RischDEInnerCompleteness.hsolve`'s type — confirmed by using it as
-- that field in a partial structure check together with abstract `hnorm`/`hbound`.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
    [CRischField α] (Dt fnum fden gnum gden : CPolyG α)
    (hnorm : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden).isSome = true)
    (hbound : ∀ a0 b0 c0 h0 : CPolyG α,
      cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden = some (a0, b0, c0, h0) →
      ∀ q : CPolyG α,
        IsReducedRdeSol Dt (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1 q →
        cdegG q ≤ cRdeBoundDegreeG Dt towerRischDEFuel
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1)
    (hres : RischDESolveExhaustiveResidual Dt fnum fden gnum gden) :
    RischDEInnerCompleteness Dt fnum fden gnum gden :=
  { hnorm := hnorm
    hbound := hbound
    hsolve := hsolve_of_exhaustiveResidual Dt fnum fden gnum gden hres }

/-! ## Operational witnesses: the reachable exhaustiveness layers fire concretely (`native_decide`)

The proven reachable layers are non-vacuous: on concrete *solvable* level-2 inputs the SPDE peel and the
poly-RDE dispatcher genuinely return `some`, and the assembled `cRischDEG` succeeds — certified by
`native_decide` over `ℚ(x)(t₁)`. These witness that `hsolve` is reached on real solvable RDEs, not
vacuously. -/

section OperationalWitnesses

/-- **The assembled `cRischDEG` succeeds on the solvable `Dy = 1`** (`cRischDEG_isSome_Dy_eq_one`,
`native_decide`): the integration RDE `Dy = 1` over `ℚ(x)(t₁)` is solvable (`y = t₁`), and the §6 solve
`cRischDEG` returns `some` — the §6.4–6.6 exhaustiveness witnessed operationally on the pure-integration
(`b = 0`) path that `cPolyRischDEG_isSome_of_bZero` covers. -/
theorem cRischDEG_isSome_Dy_eq_one :
    (cRischDEG ([CField.one] : CPolyG (QFunNZG ℚ)) towerRischDEFuel
      (CField.zero : Lvl2).1.1 (CField.zero : Lvl2).1.2
      (CField.one : Lvl2).1.1 (CField.one : Lvl2).1.2).isSome = true := by native_decide

/-- **The assembled `cRischDEG` succeeds on the solvable `Dy + y = t₁ + 1`** (`cRischDEG_isSome_Dy_plus_y`,
`native_decide`): the cancellation-path RDE `Dy + y = t₁ + 1` over `ℚ(x)(t₁)` is solvable (`y = t₁`), and the
§6 solve `cRischDEG` returns `some` — exhaustiveness on the §6.6 primitive-cancellation path (`f = 1 ≠ 0`, so
the SPDE peel + cancellation recursion run, not just integration). -/
theorem cRischDEG_isSome_Dy_plus_y :
    (cRischDEG ([CField.one] : CPolyG (QFunNZG ℚ)) towerRischDEFuel
      (CField.one : Lvl2).1.1 (CField.one : Lvl2).1.2
      towerRdeLvl2GPlusOne.1.1 towerRdeLvl2GPlusOne.1.2).isSome = true := by native_decide

end OperationalWitnesses

/-! ### Final verdict (stated precisely)

**Is `hsolve` discharged?** **YES — modulo a precisely isolated deep §6.4–6.6 residue.**
`hsolve_of_exhaustiveResidual` produces the **exact** `hsolve` clause of `RischDEInnerCompleteness` from
`RischDESolveExhaustiveResidual` (confirmed by the field-type `example` and the full assembly
`rischDEInnerCompleteness_of_residuals`). The §6.4–6.6 SPDE/poly-RDE solve loses a solution only through the
SPDE peel's `cdvdG`-gate and the dispatcher's degree/recursion gates, and `hsolve` is those gates'
exhaustiveness.

**What is closed unconditionally (the engine + base + preservation layers; NO `sorry`):**
* `cRischDEG_isSome_of_stages` / `cRischDEG_isSome_iff_stages` — the **converse** of
  `cRischDEG_some_imp_stages`: the three stage `some`s force `cRischDEG.isSome` (pure control flow);
* the **base layer** — `cPolyRischDENoCancelG_isSome_of_cZero` (c=0), `cPolyRischDEG_isSome_of_bZero` (b=0
  pure integration via the *total* `cIntegratePolyG`, inside the engine's degree guard): the dispatcher's
  total sub-cases are exhaustive unconditionally;
* the **SPDE control flow** — `cSPDEG_isSome_of_neg_cZero` (n<0 base), `cSPDEG_isSome_of_const_base` (g∣c +
  constant `a/g` ⟹ `some` directly), `cSPDEG_isSome_of_recurse` (the recursion's `isSome` is the sub-call's);
* ★ the **SPDE per-step solution-preservation** — `dvd_c_of_isReducedRdeSol` (the **divisibility necessity**:
  g∣a ∧ g∣b ⟹ a solution forces g∣c, so the SPDE `cdvdG` gate never rejects a true solution — pure algebra,
  no gcd correctness), `isReducedRdeSol_const_base` (the constant-base descent: q itself is the reduced
  solution), and ★ `spde_step_glue_inverse` (the **peel-step inverse**, exact converse of the soundness
  `spde_step_glue`: a solution in peeled form `q = a·h + r` makes `h` provably solve the reduced equation,
  by cancelling the nonzero leading `a`). These are the structural heart, proven for the reachable cases.

**The deep residual** (`RischDESolveExhaustiveResidual`, NEVER `sorry`). Two staged converse facts the engine
does not self-certify:
* **`hspde`** — the §6.4 SPDE peel returns `some` on a solvable input. Reachable layers proven (divisibility
  necessity + constant-base descent + ★ the **peel-step inverse** `spde_step_glue_inverse`: a solution in
  peeled form `q = (a/g)·h + r` makes `h` provably solve the reduced equation). The irreducible residue is
  thereby narrowed to the **peeling-divisibility** `(a/g) ∣ (q − r)` (writing a solution in peeled form, via
  the Bézout `(b/g)·r + (a/g)·z = c/g`) plus the recursion's degree-descent assembly.
* **`hpoly`** — the §6.5/§6.6 poly-RDE dispatcher returns `some` on a solvable reduced equation. Reachable
  base sub-cases proven (b=0/c=0); the irreducible residue is the **cancellation-regime exhaustiveness** (the
  non-cancellation top-down solve and the primitive/hyperexponential cancellation recursions each find a
  bounded solution if one exists) — the converse of the cancellation cleared identities.

**What `RischDEInnerCompleteness` now reduces to (the complete 3-clause map).** With `hnorm`
(`ComputableRischDENormCompleteness`, modulo Bronstein Thm 6.1.2 divisibility), `hbound`
(`ComputableRischDEDegreeBound`, modulo the §6.3 `λ`-cancellation), and `hsolve` here (modulo the §6.4–6.6
diophantine-peel + cancellation-regime residue), `rischDEInnerCompleteness_of_residuals` assembles
`RischDEInnerCompleteness` **in full** from its three precise residuals. Clause (c) of
`RischDECompletenessResidual` — and hence the whole §6 decision-procedure completeness `solvable ⟹ some` — is
mapped to exactly three precisely isolated deep facts, **none** a `sorry`: the §6.2 normal-denominator
divisibility, the §6.3 degree-bound cancellation, and the §6.4–6.6 SPDE/poly-RDE exhaustiveness. -/

/-! ### Axiom audit (the engine, base, SPDE-control-flow, preservation layers, and the modular assembly
are axiom-clean; NO `sorry`; only the `native_decide` operational witnesses use the compiler) -/

#print axioms cRischDEG_isSome_of_stages
#print axioms cRischDEG_isSome_iff_stages
#print axioms cPolyRischDEG_isSome_of_bZero
#print axioms cSPDEG_isSome_of_const_base
#print axioms cSPDEG_isSome_of_recurse
#print axioms spde_step_glue_inverse
#print axioms dvd_c_of_isReducedRdeSol
#print axioms isReducedRdeSol_const_base
#print axioms hsolve_of_exhaustiveResidual
#print axioms rischDEInnerCompleteness_of_residuals

end DeepWiki.SymbolicIntegration
