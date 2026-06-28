import DeepWiki.SymbolicIntegration.ComputableRischDENormCompleteness
import DeepWiki.SymbolicIntegration.ComputableRischDEDegreeBound
import DeepWiki.SymbolicIntegration.ComputableRischDEStructural
import DeepWiki.SymbolicIntegration.ComputableRatFuncValuation

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

The diophantine degree-peel step (`deg(a/g) ≠ 0`: a solution `q` reduces, via the Bézout relation
`(b/g)·r + (a/g)·z = c/g`, to a *lower-degree* solution `h` with `q = (a/g)·h + r`) is **now proven** as the
per-step inverse `spde_peel_inverse_of_isCoprime` / `spde_peel_inverse_toPolyG` — assembling the keystone
**peeling-divisibility** `peeling_dvd_of_isCoprime` (`(a/g) ∣ q − r`, from `gcd(a/g, b/g) = 1`) with the
algebraic peel `spde_step_glue_inverse`. The irreducible recursion residual narrows to **only** the
degree-descent assembly (iterating this per-step inverse down the shrinking `deg(a/g)` ladder), isolated
below. -/

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

/-- **★ The SPDE peeling divisibility (algebraic core)** `peeling_dvd_of_isCoprime`: over a commutative
ring, if `a` and `b` are **coprime** (`IsCoprime a b`, the SPDE invariant after dividing by `gcd(a, b)`), a
solution of the divided equation `a·Dq + b·q = c`, and the Bézout relation `b·r + a·z = c`, then `a` divides
`q − r` — `a ∣ q − r`. Pure algebra: subtracting the two relations gives `b·(q − r) = a·(z − Dq)`, so
`a ∣ b·(q − r)`, and coprimality cancels `b`. This is the **keystone** that writes a solution `q` in the
peeled form `q = a·h + r` consumed by `spde_step_glue_inverse` — the divisibility the engine never derives
(it only lifts a sub-solution up). -/
theorem peeling_dvd_of_isCoprime {R : Type*} [CommRing R] (D : Derivation ℤ R R)
    (a b c r z q : R) (hco : IsCoprime a b)
    (hsol : a * D q + b * q = c)
    (hbez : b * r + a * z = c) :
    a ∣ q - r := by
  -- subtract the two relations: `b·(q − r) = a·(z − Dq)`, so `a ∣ b·(q − r)`
  have hmul : b * (q - r) = a * (z - D q) := by linear_combination hsol - hbez
  have hdvd : a ∣ b * (q - r) := ⟨z - D q, hmul⟩
  exact hco.dvd_of_dvd_mul_left hdvd

/-- **★ The SPDE per-step solution-preservation inverse** `spde_peel_inverse_of_isCoprime`: over a
commutative ring with no zero divisors, the **full** inverse of one §6.4 SPDE peel step. Given coprime,
nonzero leading coefficients (`IsCoprime a b`, `a ≠ 0`), a solution of the divided equation
`a·Dq + b·q = c`, and the Bézout relation `b·r + a·z = c`, there is a peel factor `h` with `q = a·h + r`
that *provably* solves the **reduced** equation `a·Dh + (b + Da)·h = z − Dr`. Assembles
`peeling_dvd_of_isCoprime` (writes `q = a·h + r`) with `spde_step_glue_inverse` (descends the solution).
This is the exact converse of the soundness peel `spde_step_glue`; the irreducible residue of the §6.4 SPDE
exhaustiveness is thereby narrowed to the recursion's degree-descent assembly plus the gcd-coprimality
discharge — the peeling divisibility itself is now proven. -/
theorem spde_peel_inverse_of_isCoprime {R : Type*} [CommRing R] [NoZeroDivisors R]
    (D : Derivation ℤ R R) (a b c r z q : R) (hco : IsCoprime a b) (ha : a ≠ 0)
    (hsol : a * D q + b * q = c)
    (hbez : b * r + a * z = c) :
    ∃ h : R, q = a * h + r ∧ a * D h + (b + D a) * h = z - D r := by
  -- the keystone divisibility writes `q = a·h + r`
  obtain ⟨h, hh⟩ := peeling_dvd_of_isCoprime D a b c r z q hco hsol hbez
  refine ⟨h, by linear_combination hh, ?_⟩
  -- substitute `q = a·h + r` into the divided equation, then run the peel-step inverse
  have hpeeled : a * D (a * h + r) + b * (a * h + r) = c := by
    rw [show a * h + r = q from by linear_combination -hh]; exact hsol
  exact spde_step_glue_inverse D a b c r z h ha hbez hpeeled

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

/-- **★ The SPDE peeling divisibility through `toPolyG`** (`dvd_sub_of_isReducedRdeSol`): the engine-carrier
form of `peeling_dvd_of_isCoprime`. If the divided leading coefficients are coprime
(`IsCoprime (toPolyG ad) (toPolyG bd)`, the SPDE invariant after dividing by `gcd`), `q` solves the divided
equation `ad·Dq + bd·q = cd` (`IsReducedRdeSol Dt ad bd cd q`), and the Bézout cofactors `r, z` satisfy
`bd·r + ad·z = cd`, then `ad ∣ q − r` — `toPolyG ad ∣ toPolyG q − toPolyG r`. The keystone that writes a
divided-equation solution in the peeled form `q = ad·h + r` (`q − r = ad·h`), which the recursion needs and
the engine never derives. -/
theorem dvd_sub_of_isReducedRdeSol (Dt ad bd cd r z q : CPolyG α)
    (hco : IsCoprime (toPolyG ad) (toPolyG bd))
    (hsol : IsReducedRdeSol Dt ad bd cd q)
    (hbez : toPolyG bd * toPolyG r + toPolyG ad * toPolyG z = toPolyG cd) :
    toPolyG ad ∣ toPolyG q - toPolyG r :=
  peeling_dvd_of_isCoprime (Differential.implicitDeriv (toPolyG Dt))
    (toPolyG ad) (toPolyG bd) (toPolyG cd) (toPolyG r) (toPolyG z) (toPolyG q) hco hsol hbez

/-- **★ The SPDE per-step solution-preservation inverse through `toPolyG`** (`spde_peel_inverse_toPolyG`):
the engine-carrier **full** inverse of one §6.4 SPDE peel step. Given coprime, nonzero leading coefficients
(`IsCoprime (toPolyG ad) (toPolyG bd)`, `toPolyG ad ≠ 0`), a divided-equation solution
`IsReducedRdeSol Dt ad bd cd q`, and the Bézout `bd·r + ad·z = cd`, there is a peel factor `h` with
`q = ad·h + r` that **provably** solves the reduced equation `ad·Dh + (bd + D(ad))·h = z − Dr` over
`(CFieldSpec.K α)[X]`. The exact converse of `cSPDE_peel_cleared_gen`: the §6.4 SPDE peel descends a
solution one level, so it cannot lose it. The degree-descent recursion built on it is now also proven
(`cSPDEG_isSome_of_structG_bounded`, `SPDEDegreeDescent` section); the remaining §6.4 residue narrows to
fuel sufficiency plus the upstream fractional→reduced bridge. -/
theorem spde_peel_inverse_toPolyG (Dt ad bd cd r z q : CPolyG α)
    (hco : IsCoprime (toPolyG ad) (toPolyG bd)) (had : toPolyG ad ≠ 0)
    (hsol : IsReducedRdeSol Dt ad bd cd q)
    (hbez : toPolyG bd * toPolyG r + toPolyG ad * toPolyG z = toPolyG cd) :
    ∃ h : (CFieldSpec.K α)[X],
      toPolyG q = toPolyG ad * h + toPolyG r ∧
      toPolyG ad * Differential.implicitDeriv (toPolyG Dt) h
          + (toPolyG bd + Differential.implicitDeriv (toPolyG Dt) (toPolyG ad)) * h
        = toPolyG z - Differential.implicitDeriv (toPolyG Dt) (toPolyG r) :=
  spde_peel_inverse_of_isCoprime (Differential.implicitDeriv (toPolyG Dt))
    (toPolyG ad) (toPolyG bd) (toPolyG cd) (toPolyG r) (toPolyG z) (toPolyG q) hco had hsol hbez

-- ★ Restatement: the peeling divisibility says *exactly* `a ∣ q − r` from coprimality + the two relations.
example {R : Type*} [CommRing R] (D : Derivation ℤ R R) (a b c r z q : R)
    (hco : IsCoprime a b) (hsol : a * D q + b * q = c) (hbez : b * r + a * z = c) :
    a ∣ q - r :=
  peeling_dvd_of_isCoprime D a b c r z q hco hsol hbez

-- ★ Restatement: the per-step inverse produces `h` with `q = a·h + r` solving the reduced equation.
example {R : Type*} [CommRing R] [NoZeroDivisors R] (D : Derivation ℤ R R) (a b c r z q : R)
    (hco : IsCoprime a b) (ha : a ≠ 0) (hsol : a * D q + b * q = c) (hbez : b * r + a * z = c) :
    ∃ h : R, q = a * h + r ∧ a * D h + (b + D a) * h = z - D r :=
  spde_peel_inverse_of_isCoprime D a b c r z q hco ha hsol hbez

/-- **★ The §6.2 normal-denominator cleared lifting INVERSE (algebraic core)** `rdeNormalDenominator_glue_inverse`:
the **converse** of `rdeNormalDenominator_glue`. Over a commutative ring with no zero divisors, with the normal
part `DN ≠ 0`, `FDEN ≠ 0`, `GDEN ≠ 0`, the factorization `A = DN·H` and the two exact-division certificates
`B·FDEN = A·FNUM − DN·DH·FDEN`, `C·GDEN = DN·H²·GNUM`, a *cleared* solution **already in normalized form**
`yden = H`, `ynum = Q` (the §6.2 reconstruction `q = y·h`'s denominator equals the clearing factor `H`) —
`GDEN·FDEN·(D(Q)·H − Q·D(H)) + GDEN·FNUM·Q·H = GNUM·FDEN·H²` — makes `Q` solve the **reduced** equation
`A·D(Q) + B·Q = C`. Pure algebra: multiply the goal by `FDEN·GDEN`, the whole identity is `DN` times the
cleared identity, cancel the nonzero `DN·FDEN·GDEN`. The exact inverse of the soundness §6.2 glue
`rdeNormalDenominator_glue`; the **only** remaining deep input is the denominator-clearing that brings a general
fractional solution `ynum/yden` to the normalized `yden = H` form (Bronstein Thm 6.1.2(i): `q = yh ∈ k⟨t⟩`). -/
theorem rdeNormalDenominator_glue_inverse {R : Type*} [CommRing R] [NoZeroDivisors R]
    (D : Derivation ℤ R R) (DN H FNUM FDEN GNUM GDEN A B C Q : R)
    (hFDEN : FDEN ≠ 0) (hGDEN : GDEN ≠ 0)
    (hA : A = DN * H)
    (hB : B * FDEN = A * FNUM - DN * D H * FDEN)
    (hC : C * GDEN = DN * H ^ 2 * GNUM)
    (hcleared : GDEN * FDEN * (D Q * H - Q * D H) + GDEN * FNUM * Q * H = GNUM * FDEN * H ^ 2) :
    A * D Q + B * Q = C := by
  apply mul_left_cancel₀ (mul_ne_zero hFDEN hGDEN)
  linear_combination GDEN * Q * hB - FDEN * hC + DN * hcleared
    + (FDEN * GDEN * D Q + GDEN * FNUM * Q) * hA

/-- **★ The §6.2 special-denominator substitution INVERSE (algebraic core)**
`specialDenominatorSubst_cleared_inverse`: the **converse** of `specialDenominatorSubst_cleared`. Over a
commutative ring with no zero divisors, for a special irreducible `p ≠ 0` with `D p = E·p` (the
hyperexponential case `p = t`, `E = η ∈ k`), a *special-cleared* solution **already in reconstructed form**
`r = q·pᵏ` solving `a·D(r) + b·r = c·pᵏ` makes the factor `q` solve the **reduced** equation
`a·D(q) + b·q + k·a·E·q = c`. Pure algebra: expand by Leibniz (`specialDenominatorSubst_expand`), then cancel
the nonzero `pᵏ`. The exact inverse of the soundness §6.2 special glue `specialDenominatorSubst_cleared`; the
remaining deep input is the `νₚ`-bookkeeping divisibility `pᵏ ∣ Q` that writes a reduced solution in the
reconstructed form `Q = q·pᵏ` (Bronstein Lemma 6.2.x). -/
theorem specialDenominatorSubst_cleared_inverse {R : Type*} [CommRing R] [NoZeroDivisors R]
    (D : Derivation ℤ R R) (a b c p E q : R) (k : ℕ) (hp : p ≠ 0) (hDp : D p = E * p)
    (hcleared : a * D (q * p ^ k) + b * (q * p ^ k) = c * p ^ k) :
    a * D q + b * q + (k : R) * (a * E) * q = c := by
  -- Leibniz-expand the cleared LHS as `(reduced)·pᵏ` (mirror of `specialDenominatorSubst_expand`)
  have hexp : a * D (q * p ^ k) + b * (q * p ^ k)
      = (a * D q + b * q + (k : R) * (a * E) * q) * p ^ k := by
    rw [Derivation.leibniz, Derivation.leibniz_pow, hDp]
    cases k with
    | zero => simp
    | succ k => simp only [Nat.add_sub_cancel, smul_eq_mul, Nat.cast_succ, pow_succ]; ring
  rw [hexp] at hcleared
  exact mul_right_cancel₀ (pow_ne_zero k hp) hcleared

/-- **★ The reverse special glue in the `negn = 0` (no-clear) sub-regime — `νₚ`-divisibility VACUOUS**
(`specialDenominatorSubst_cleared_inverse_noClear`): the `k = 0` specialization of
`specialDenominatorSubst_cleared_inverse`, where the §6.2 special-cleared equation is at power `p⁰ = 1`. Since
`negn = 0` for ALL inputs (`cSpecialDenomNoClearG_always`), the §6.2 reconstruction power is `pⁿᵉᵍⁿ = p⁰ = 1`
(`cRdeSpecialDenominatorG_h1_eq_one_always`), so the `νₚ`-bookkeeping divisibility `pⁿᵉᵍⁿ ∣ Q` is the trivial
`1 ∣ Q` (`one_dvd`): a *special-cleared* solution `Q` is **already** in reconstructed form `Q = Q·p⁰ = Q`,
and from `a·D(Q·p⁰) + b·(Q·p⁰) = c·p⁰` the reduced equation `a·D(Q) + b·Q = c` carries NO `k·a·E·Q` (here
`0·a·E·Q`) correction term. The documented `negn > 0` non-primitive continuation is thereby vacuous — the
hyperexp/hypertangent special-clearing reduces to the same `(a, b, c)`-shape as the primitive regime. -/
theorem specialDenominatorSubst_cleared_inverse_noClear {R : Type*} [CommRing R] [NoZeroDivisors R]
    (D : Derivation ℤ R R) (a b c p E Q : R) (hp : p ≠ 0) (hDp : D p = E * p)
    (hcleared : a * D (Q * p ^ 0) + b * (Q * p ^ 0) = c * p ^ 0) :
    a * D Q + b * Q = c := by
  -- the reconstructed form `Q = Q·p⁰` needs only the trivial `1 ∣ Q`; the `0·a·E·Q` correction vanishes
  have h := specialDenominatorSubst_cleared_inverse D a b c p E Q 0 hp hDp hcleared
  simpa using h

end Preservation

/-! ## ★ The §6.4 SPDE degree-descent recursion assembly (the `hspde` structural heart)

The per-step inverse `spde_peel_inverse_toPolyG` descends a solution ONE level; the §6.4 exhaustiveness
needs the whole degree-descent: iterating it down the strictly-shrinking `deg(a/g)` ladder until `cSPDEG`
short-circuits, forcing `cSPDEG.isSome`. This section assembles that recursion, mirroring the soundness
lifting `cSPDEG_cleared_lifting_gen` (`ComputableRischDETowerCorrectG`) IN REVERSE: the same fuel / `cdvdG`
/ `cdegG` case split, run for the existence (`isSome`) direction.

The reverse direction needs TWO facts the forward (soundness) direction never did, exactly as the
honest-landing analysis predicted: (a) the **degree-descent bookkeeping** — `deg(h) ≤ n − deg(a/g)` for the
peeled factor — proven here (`degree_peeled_le`, `cisZeroG_of_isReducedRdeSolK_neg`); the abstract solution
`spde_peel_inverse_of_isCoprime` produces lives in `K[X]`, so we thread an ABSTRACT `IsReducedRdeSolK`
witness (no `CPolyG`-lift obligation); and (b) **fuel sufficiency** — the degree ladder must bottom out
before the fuel runs out (the soundness side is happy with `none` at fuel 0; the existence side is not).
The whole assembly is therefore PROVEN modulo only fuel sufficiency, isolated as the `fuel = 0 ↦ False`
base of `CSPDEGStructG`. -/

section SPDEDegreeDescent

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Coprimality of the divided coefficients** (`isCoprime_bd_ad_of_divided`): when `g ~ gcd(a, b)`
divides both exactly, `gcd(b/g, a/g)` is a unit (`cgcdExtG_isUnit_of_divided_gen`), so dividing the Bézout
identity by that unit gives `IsCoprime (toPolyG bd) (toPolyG ad)` — the SPDE coprimality invariant. -/
theorem isCoprime_bd_ad_of_divided [CFracGcdCore α] (fuel : ℕ) (a b ad bd g : CPolyG α)
    (hgne : toPolyG g ≠ 0)
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b)))
    (hdiva : toPolyG ad * toPolyG g = toPolyG a)
    (hdivb : toPolyG bd * toPolyG g = toPolyG b)
    (hterm : cgcdTerminatesG fuel bd ad) :
    IsCoprime (toPolyG bd) (toPolyG ad) := by
  have hunit := cgcdExtG_isUnit_of_divided_gen fuel a b ad bd g hgne hgassoc hdiva hdivb hterm
  have hbez := toPolyG_cgcdExtG fuel bd ad
  obtain ⟨u, hu⟩ := hunit
  refine ⟨↑u⁻¹ * toPolyG (cgcdExtG fuel bd ad).2.1, ↑u⁻¹ * toPolyG (cgcdExtG fuel bd ad).2.2, ?_⟩
  have hinv : (↑u⁻¹ : (CFieldSpec.K α)[X]) * toPolyG (cgcdExtG fuel bd ad).1 = 1 := by
    rw [← hu]; exact Units.inv_mul u
  calc ↑u⁻¹ * toPolyG (cgcdExtG fuel bd ad).2.1 * toPolyG bd
        + ↑u⁻¹ * toPolyG (cgcdExtG fuel bd ad).2.2 * toPolyG ad
      = ↑u⁻¹ * (toPolyG (cgcdExtG fuel bd ad).2.1 * toPolyG bd
          + toPolyG (cgcdExtG fuel bd ad).2.2 * toPolyG ad) := by ring
    _ = ↑u⁻¹ * toPolyG (cgcdExtG fuel bd ad).1 := by rw [hbez]
    _ = 1 := hinv

/-- **An ABSTRACT (`K[X]`-valued) reduced-equation solution** `IsReducedRdeSolK Dt a b c q`:
`toPolyG a · D(q) + toPolyG b · q = toPolyG c` for `q ∈ (CFieldSpec.K α)[X]` — the shape the per-step
inverse `spde_peel_inverse_of_isCoprime` produces (so the degree-descent threads it without a `CPolyG`
lift). The `K[X]` analogue of `IsReducedRdeSol`. -/
def IsReducedRdeSolK (Dt a b c : CPolyG α) (q : (CFieldSpec.K α)[X]) : Prop :=
  toPolyG a * Differential.implicitDeriv (toPolyG Dt) q + toPolyG b * q = toPolyG c

/-- **A `CPolyG` reduced solution lifts to a `K[X]` one** (`isReducedRdeSolK_of_isReducedRdeSol`): a
polynomial-carrier solution `IsReducedRdeSol Dt a b c q` is *definitionally* the `K[X]`-witness
`IsReducedRdeSolK Dt a b c (toPolyG q)` (the same equation, `q` read through `toPolyG`). The trivial bridge
from the `hbound`-shaped `IsReducedRdeSol` to the degree-descent-shaped `IsReducedRdeSolK`. -/
theorem isReducedRdeSolK_of_isReducedRdeSol (Dt a b c q : CPolyG α)
    (hsol : IsReducedRdeSol Dt a b c q) :
    IsReducedRdeSolK Dt a b c (toPolyG q) :=
  hsol

/-- **★ The §6.2 normal-denominator cleared lifting INVERSE through `toPolyG`**
(`isReducedRdeSol_of_cleared_normalized`): the engine-carrier converse of
`cRdeNormalDenominatorG_cleared_lift_gen`. From `cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a,
b, c, h)`, the §6.2 normal-clear certificates (the same `B/C` exactness `toPolyG_cdivG_exact_mul_gen` the
soundness lift consumes), `fden, gden ≠ 0`, and a *normalized* cleared solution `IsCRischDEGPolySol Dt fnum
fden gnum gden Q h` (a fractional solution whose **denominator equals the §6.2 clearing factor** `h = h0`,
`ynum = Q`), the reconstruction `Q` solves the **reduced** equation — `IsReducedRdeSol Dt a b c Q`. Extracts
the `A = dₙ·h` / `B·fden = …` / `C·gden = …` certificates exactly as the soundness lift, then runs the
algebraic inverse `rdeNormalDenominator_glue_inverse`. The exact converse of the §6.2 soundness lift; the
**only** remaining deep input is the denominator-clearing that brings a general fractional `ynum/yden` to the
normalized `yden = h` form (Bronstein Thm 6.1.2(i): the solution `q = yh` is a *polynomial*). -/
theorem isReducedRdeSol_of_cleared_normalized [CFracGcdCore α] (Dt : CPolyG α) (fuel : ℕ)
    (fnum fden gnum gden a b c h Q : CPolyG α)
    (hres : cRdeNormalDenominatorG Dt fuel fnum fden gnum gden = some (a, b, c, h))
    (hfden0 : cnormG fden ≠ []) (hgden0 : cnormG gden ≠ [])
    (hfbB : (cnormG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h)) fden)) :
        List α).length ≤ fuel)
    (hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h) fnum)
        (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 (cmonomialDeriv Dt h)) fden)))
    (hfbC : (cnormG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h) h) gnum) :
        List α).length ≤ fuel)
    (hdvdC : toPolyG gden ∣ toPolyG (cmulG (cmulG (cmulG (cSplitFactorFastG Dt fuel fden).1 h) h) gnum))
    (hcleared : IsCRischDEGPolySol Dt fnum fden gnum gden Q h) :
    IsReducedRdeSol Dt a b c Q := by
  set dn := (cSplitFactorFastG Dt fuel fden).1 with hdndef
  set bNum := csubG (cmulG (cmulG dn h) fnum) (cmulG (cmulG dn (cmonomialDeriv Dt h)) fden) with hbNum
  set cNum := cmulG (cmulG (cmulG dn h) h) gnum with hcNum
  rw [cRdeNormalDenominatorG] at hres
  split at hres
  · rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hres
    obtain ⟨ha, hb, hc, hh⟩ := hres
    rw [hh] at ha hb hc
    have hA : toPolyG a = toPolyG dn * toPolyG h := by rw [← ha, toPolyG_cmulG]
    have hBexact : toPolyG b * toPolyG fden = toPolyG bNum := by
      rw [← hb]; exact toPolyG_cdivG_exact_mul_gen fuel bNum fden hfden0 hfbB hdvdB
    have hBeq : toPolyG bNum = toPolyG a * toPolyG fnum
        - toPolyG dn * Differential.implicitDeriv (toPolyG Dt) (toPolyG h) * toPolyG fden := by
      rw [hbNum, toPolyG_csubG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG,
        toPolyG_cmonomialDeriv, ← ha, toPolyG_cmulG]
    have hCexact : toPolyG c * toPolyG gden = toPolyG cNum := by
      rw [← hc]; exact toPolyG_cdivG_exact_mul_gen fuel cNum gden hgden0 hfbC hdvdC
    have hCeq : toPolyG cNum = toPolyG dn * toPolyG h ^ 2 * toPolyG gnum := by
      rw [hcNum, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG]; ring
    have hBcert : toPolyG b * toPolyG fden = toPolyG a * toPolyG fnum
        - toPolyG dn * Differential.implicitDeriv (toPolyG Dt) (toPolyG h) * toPolyG fden := by
      rw [hBexact]; exact hBeq
    have hCcert : toPolyG c * toPolyG gden = toPolyG dn * toPolyG h ^ 2 * toPolyG gnum := by
      rw [hCexact]; exact hCeq
    have hfden_ne : toPolyG fden ≠ 0 := fun hz => hfden0 ((cnormG_eq_nil_iff fden).mpr hz)
    have hgden_ne : toPolyG gden ≠ 0 := fun hz => hgden0 ((cnormG_eq_nil_iff gden).mpr hz)
    unfold IsCRischDEGPolySol at hcleared
    unfold IsReducedRdeSol
    exact rdeNormalDenominator_glue_inverse (Differential.implicitDeriv (toPolyG Dt))
      (toPolyG dn) (toPolyG h) (toPolyG fnum) (toPolyG fden) (toPolyG gnum) (toPolyG gden)
      (toPolyG a) (toPolyG b) (toPolyG c) (toPolyG Q)
      hfden_ne hgden_ne hA hBcert hCcert hcleared
  · exact absurd hres (by simp)

/-- **The `K[X]`-witness divisibility necessity** (`dvd_c_of_isReducedRdeSolK`): if `g` divides both
leading coefficients and `q : K[X]` solves `a·Dq + b·q = c`, then `g ∣ c` — the `K[X]` analogue of
`dvd_c_of_isReducedRdeSol` (same `dvd_add` algebra). -/
theorem dvd_c_of_isReducedRdeSolK (Dt a b c g : CPolyG α) (q : (CFieldSpec.K α)[X])
    (hga : toPolyG g ∣ toPolyG a) (hgb : toPolyG g ∣ toPolyG b)
    (hsol : IsReducedRdeSolK Dt a b c q) :
    toPolyG g ∣ toPolyG c := by
  have heq : toPolyG c
      = toPolyG a * Differential.implicitDeriv (toPolyG Dt) q + toPolyG b * q := hsol.symm
  rw [heq]; exact dvd_add (hga.mul_right _) (hgb.mul_right _)

/-- **The SPDE `cdvdG` gate never rejects a `K[X]` solution** (`cdvdG_g_c_of_isReducedRdeSolK`): with `g ~
gcd(a, b)` nonzero and the fuel covering `c`, an abstract reduced solution forces `cdvdG fuel g c = true`
(via `dvd_c_of_isReducedRdeSolK` + `cdvdG_of_dvd`). The reverse of the soundness peel's `g ∣ c` read-off. -/
theorem cdvdG_g_c_of_isReducedRdeSolK [CFracGcdCore α] (Dt a b c g : CPolyG α)
    (q : (CFieldSpec.K α)[X]) (fuel : ℕ)
    (hg0 : cnormG g ≠ []) (hfc : (cnormG c : List α).length ≤ fuel)
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b)))
    (hsol : IsReducedRdeSolK Dt a b c q) :
    cdvdG fuel g c = true :=
  cdvdG_of_dvd fuel g c hg0 hfc (dvd_c_of_isReducedRdeSolK Dt a b c g q
    (hgassoc.dvd.trans (gcd_dvd_left _ _)) (hgassoc.dvd.trans (gcd_dvd_right _ _)) hsol)

/-- **The recursive solvable-inputs predicate** `CSPDEGSolvableInputsGen Dt fuel a b c n` (the
existence-direction analogue of `CSPDEGClearedInputsGen`): mirrors `cSPDEG`'s recursion carrying at EACH
level an abstract `K[X]` reduced solution (the witness `spde_peel_inverse_of_isCoprime` produces) plus, in
the non-base branch, the gcd `Associated` clause, the fuel bounds, `a ≠ 0`, the Euclidean termination, and
itself on the peeled reduced equation. The base `fuel = 0` is `False` (a solvable problem needs ≥ 1 unit of
fuel). The hypothesis the degree-descent induction consumes. -/
def CSPDEGSolvableInputsGen [CFracGcdCore α] (Dt : CPolyG α) :
    ℕ → (a b c : CPolyG α) → (n : ℤ) → Prop
  | 0, _, _, _, _ => False
  | fuel + 1, a, b, c, n =>
    (∃ q : (CFieldSpec.K α)[X], IsReducedRdeSolK Dt a b c q) ∧
    if n < 0 then cisZeroG c = true
    else
      let g := CFracGcdCore.cgcdFFCore fuel a b
      let ad := cdivG fuel a g
      let bd := cdivG fuel b g
      (cnormG g ≠ []) ∧ Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b))
        ∧ ((cnormG a : List α).length ≤ fuel)
        ∧ ((cnormG b : List α).length ≤ fuel)
        ∧ ((cnormG c : List α).length ≤ fuel)
        ∧ (cnormG a ≠ [])
        ∧ (if cdegG ad = 0 then True
           else
             let rz := cdiophantineG fuel bd ad (cdivG fuel c g)
             cgcdTerminatesG fuel bd ad
               ∧ CSPDEGSolvableInputsGen Dt fuel ad (caddG bd (cmonomialDeriv Dt ad))
                   (csubG rz.2 (cmonomialDeriv Dt rz.1)) (n - (cdegG ad : ℤ)))

/-- **★ The §6.4 SPDE degree-descent induction** (`cSPDEG_isSome_of_solvableInputs`): from the recursive
solvable-inputs predicate, the SPDE peel succeeds — `(cSPDEG Dt fuel a b c n).isSome = true`. By fuel
induction, the exact REVERSE of the soundness lifting `cSPDEG_cleared_lifting_gen`: the `n < 0`/const-base/
recursion cases dispatched through `cSPDEG_isSome_of_neg_cZero` / `cSPDEG_isSome_of_const_base` /
`cSPDEG_isSome_of_recurse`, with the `cdvdG` gate discharged by the divisibility necessity
`cdvdG_g_c_of_isReducedRdeSolK`. The control-flow heart of `hspde`. -/
theorem cSPDEG_isSome_of_solvableInputs [CFracGcdCore α] (Dt : CPolyG α) :
    ∀ (fuel : ℕ) (a b c : CPolyG α) (n : ℤ),
      CSPDEGSolvableInputsGen Dt fuel a b c n →
      (cSPDEG Dt fuel a b c n).isSome = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b c n hin
    exact absurd hin (by rw [CSPDEGSolvableInputsGen]; exact not_false)
  | succ fuel ih =>
    intro a b c n hin
    rw [CSPDEGSolvableInputsGen] at hin
    obtain ⟨⟨q, hsol⟩, hrest⟩ := hin
    by_cases hn : n < 0
    · rw [if_pos hn] at hrest
      exact cSPDEG_isSome_of_neg_cZero Dt fuel a b c n hn hrest
    · rw [if_neg hn] at hrest
      set g := CFracGcdCore.cgcdFFCore fuel a b with hg
      set ad := cdivG fuel a g with had
      set bd := cdivG fuel b g with hbd
      obtain ⟨hg0, hgassoc, hfa, hfb, hfc, ha0, hrec⟩ := hrest
      have hdvd : cdvdG fuel g c = true :=
        cdvdG_g_c_of_isReducedRdeSolK Dt a b c g q fuel hg0 hfc hgassoc hsol
      by_cases hdeg : cdegG ad = 0
      · exact cSPDEG_isSome_of_const_base Dt fuel a b c n hn hdvd hdeg
      · rw [if_neg hdeg] at hrec
        obtain ⟨hterm, hrecin⟩ := hrec
        have hrecsome := ih ad (caddG bd (cmonomialDeriv Dt ad))
          (csubG (cdiophantineG fuel bd ad (cdivG fuel c g)).2
            (cmonomialDeriv Dt (cdiophantineG fuel bd ad (cdivG fuel c g)).1))
          (n - (cdegG ad : ℤ)) hrecin
        exact cSPDEG_isSome_of_recurse Dt fuel a b c n hn hdvd hdeg hrecsome

/-- **★ The per-level peeled reduced witness** (`exists_peeled_reducedSolK`): threading the proven per-step
inverse `spde_peel_inverse_of_isCoprime` over `K[X]`. From the structural gcd data and an abstract reduced
solution `q : K[X]` of the current level, there is a peeled factor `h : K[X]` with `q = (a/g)·h + r` that is
an `IsReducedRdeSolK` solution of the NEXT level's reduced equation. Assembles the divided-coefficient
exactness, `isCoprime_bd_ad_of_divided`, the divided solution, and the Bézout `toPolyG_cdiophantineG`.
Produces exactly the `K[X]` witness `CSPDEGSolvableInputsGen` carries — no `CPolyG` lift needed. -/
theorem exists_peeled_reducedSolK [CFracGcdCore α] (Dt a b c g ad bd : CPolyG α)
    (q : (CFieldSpec.K α)[X]) (fuel : ℕ)
    (had : ad = cdivG fuel a g) (hbd : bd = cdivG fuel b g)
    (hg0 : cnormG g ≠ []) (hfa : (cnormG a : List α).length ≤ fuel)
    (hfb : (cnormG b : List α).length ≤ fuel) (hfc : (cnormG c : List α).length ≤ fuel)
    (ha0 : cnormG a ≠ [])
    (hgassoc : Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b)))
    (hterm : cgcdTerminatesG fuel bd ad)
    (hsol : IsReducedRdeSolK Dt a b c q) :
    ∃ h : (CFieldSpec.K α)[X],
      q = toPolyG ad * h + toPolyG (cdiophantineG fuel bd ad (cdivG fuel c g)).1 ∧
      IsReducedRdeSolK Dt ad (caddG bd (cmonomialDeriv Dt ad))
        (csubG (cdiophantineG fuel bd ad (cdivG fuel c g)).2
          (cmonomialDeriv Dt (cdiophantineG fuel bd ad (cdivG fuel c g)).1)) h := by
  have hgne : toPolyG g ≠ 0 := fun h => hg0 ((cnormG_eq_nil_iff g).mpr h)
  have hane : toPolyG a ≠ 0 := fun h => ha0 ((cnormG_eq_nil_iff a).mpr h)
  have hdiva : toPolyG ad * toPolyG g = toPolyG a := had ▸ cdivG_a_exact_of_gcd fuel a b g hg0 hfa hgassoc
  have hdivb : toPolyG bd * toPolyG g = toPolyG b := hbd ▸ cdivG_b_exact_of_gcd fuel a b g hg0 hfb hgassoc
  have hadne : toPolyG ad ≠ 0 := fun h => hane (by rw [← hdiva, h, zero_mul])
  have hadnil : cnormG ad ≠ [] := fun h => hadne ((cnormG_eq_nil_iff ad).mp h)
  have hco : IsCoprime (toPolyG ad) (toPolyG bd) :=
    (isCoprime_bd_ad_of_divided fuel a b ad bd g hgne hgassoc hdiva hdivb hterm).symm
  have hgc : toPolyG g ∣ toPolyG c :=
    dvd_c_of_isReducedRdeSolK Dt a b c g q (hgassoc.dvd.trans (gcd_dvd_left _ _))
      (hgassoc.dvd.trans (gcd_dvd_right _ _)) hsol
  have hdivc : toPolyG (cdivG fuel c g) * toPolyG g = toPolyG c :=
    toPolyG_cdivG_exact fuel c g hg0 hfc hgc
  have hsoldiv : IsReducedRdeSolK Dt ad bd (cdivG fuel c g) q := by
    unfold IsReducedRdeSolK at hsol ⊢
    have hmulg : (toPolyG ad * Differential.implicitDeriv (toPolyG Dt) q + toPolyG bd * q) * toPolyG g
        = toPolyG (cdivG fuel c g) * toPolyG g := by rw [hdivc, ← hsol, ← hdiva, ← hdivb]; ring
    exact mul_right_cancel₀ hgne hmulg
  have hgC := toPolyG_cgcdExtG_eq_C_of_divided_gen fuel a b ad bd g hgne hgassoc hdiva hdivb hterm
  have hgCne := toK_cleadG_cgcdExtG_ne_zero_of_divided_gen fuel a b ad bd g hgne hgassoc hdiva hdivb hterm
  have hbez0 := toPolyG_cdiophantineG fuel bd ad (cdivG fuel c g) hadnil hgC hgCne
  have hbez : toPolyG bd * toPolyG (cdiophantineG fuel bd ad (cdivG fuel c g)).1
      + toPolyG ad * toPolyG (cdiophantineG fuel bd ad (cdivG fuel c g)).2
      = toPolyG (cdivG fuel c g) := by rw [mul_comm (toPolyG bd), mul_comm (toPolyG ad)]; exact hbez0
  obtain ⟨h, hqeq, hred⟩ := spde_peel_inverse_of_isCoprime
    (Differential.implicitDeriv (toPolyG Dt)) (toPolyG ad) (toPolyG bd) (toPolyG (cdivG fuel c g))
    (toPolyG (cdiophantineG fuel bd ad (cdivG fuel c g)).1)
    (toPolyG (cdiophantineG fuel bd ad (cdivG fuel c g)).2) q hco hadne hsoldiv hbez
  refine ⟨h, hqeq, ?_⟩
  unfold IsReducedRdeSolK
  rw [toPolyG_caddG, toPolyG_cmonomialDeriv, toPolyG_csubG, toPolyG_cmonomialDeriv]
  linear_combination hred

/-- **The `n < 0` base obligation** (`cisZeroG_of_isReducedRdeSolK_neg`): a bounded (`deg ≤ n < 0`) abstract
reduced solution forces the RHS to vanish — `cisZeroG c = true`. Since `natDegree ≥ 0`, the bound is
impossible, so `q = 0`, whence `toPolyG c = a·D(0) + b·0 = 0`. The degree-descent's terminating-branch
discharge. -/
theorem cisZeroG_of_isReducedRdeSolK_neg [CFracGcdCore α] (Dt a b c : CPolyG α)
    (q : (CFieldSpec.K α)[X]) (n : ℤ) (hn : n < 0)
    (hsol : IsReducedRdeSolK Dt a b c q) (hq : q = 0 ∨ (q.natDegree : ℤ) ≤ n) :
    cisZeroG c = true := by
  have hq0 : q = 0 := by
    rcases hq with h | h
    · exact h
    · have : (0 : ℤ) ≤ q.natDegree := Int.natCast_nonneg q.natDegree
      omega
  rw [cisZeroG_iff]
  have := hsol
  rw [IsReducedRdeSolK, hq0] at this
  simpa using this.symm

/-- **★ The degree-descent bookkeeping** (`degree_peeled_le`): from `q = a·h + r` with `deg r < deg a`,
`a ≠ 0`, and the bound on `q`, the peeled factor `h` satisfies the NEXT level's bound `n − deg a`. The
degree fact the soundness lifting never needed (it lifts ANY `h`; the existence side must keep `h` bounded
to feed the recursion's short-circuit). The zero quirk is carried by the `(· = 0 ∨ natDegree ≤ ·)` shape. -/
theorem degree_peeled_le {K : Type*} [Field K] (ad h r q : K[X]) (n : ℤ)
    (hadne : ad ≠ 0) (hrlt : r.degree < ad.degree)
    (hq : q = ad * h + r) (hbound : q = 0 ∨ (q.natDegree : ℤ) ≤ n) :
    h = 0 ∨ (h.natDegree : ℤ) ≤ n - (ad.natDegree : ℤ) := by
  by_cases hh : h = 0
  · exact Or.inl hh
  · right
    have hadhne : ad * h ≠ 0 := mul_ne_zero hadne hh
    have hadle : ad.degree ≤ (ad * h).degree := by
      rw [Polynomial.degree_mul]
      exact le_add_of_nonneg_right (Polynomial.zero_le_degree_iff.mpr hh)
    have hrlt' : r.degree < (ad * h).degree := lt_of_lt_of_le hrlt hadle
    have hqnat : q.natDegree = ad.natDegree + h.natDegree := by
      rw [hq, Polynomial.natDegree_add_eq_left_of_degree_lt hrlt', Polynomial.natDegree_mul hadne hh]
    have hqdeg : q.degree = (ad * h).degree := by
      rw [hq]; exact Polynomial.degree_add_eq_left_of_degree_lt hrlt'
    have hqne : q ≠ 0 := by
      intro h0; exact hadhne (Polynomial.degree_eq_bot.mp (hqdeg ▸ Polynomial.degree_eq_bot.mpr h0))
    rcases hbound with h0 | hb
    · exact absurd h0 hqne
    · rw [hqnat] at hb; push_cast at hb ⊢; omega

/-- **The unconditional structural-gcd predicate** `CSPDEGStructG Dt fuel a b c n`: the data the EXISTENCE
direction needs to PROVE the `cdvdG` gate (so NOT gated behind `cdvdG`, unlike the soundness
`CSPDEGClearedInputsGen`). At each non-base level: nonzero gcd `Associated` to `gcd(a, b)`, the fuel bounds,
`a ≠ 0`, the diophantine cofactor fuel bound (for `deg r < deg(a/g)` via `cdiophantineG_fst_degree_lt`),
Euclidean termination, and itself on the peeled level for every RHS. Base `fuel = 0` is `False` — FUEL
SUFFICIENCY, the genuine extra termination fact. -/
def CSPDEGStructG [CFracGcdCore α] (Dt : CPolyG α) :
    ℕ → (a b c : CPolyG α) → (n : ℤ) → Prop
  | 0, _, _, _, _ => False
  | fuel + 1, a, b, c, n =>
    if n < 0 then True
    else
      let g := CFracGcdCore.cgcdFFCore fuel a b
      let ad := cdivG fuel a g
      let bd := cdivG fuel b g
      (cnormG g ≠ []) ∧ Associated (toPolyG g) (gcd (toPolyG a) (toPolyG b))
        ∧ ((cnormG a : List α).length ≤ fuel)
        ∧ ((cnormG b : List α).length ≤ fuel)
        ∧ ((cnormG c : List α).length ≤ fuel)
        ∧ (cnormG a ≠ [])
        ∧ (if cdegG ad = 0 then True
           else
             ((cnormG (cscaleG (CField.inv (cleadG (cgcdExtG fuel bd ad).1))
                 (cmulG (cdivG fuel c g) (cgcdExtG fuel bd ad).2.1)) : List α).length ≤ fuel)
               ∧ cgcdTerminatesG fuel bd ad
               ∧ ∀ c' : CPolyG α, CSPDEGStructG Dt fuel ad (caddG bd (cmonomialDeriv Dt ad)) c'
                   (n - (cdegG ad : ℤ)))

omit [CDiffFieldSpec α] in
/-- **★ The degree-descent ladder bottoms out at `n < 0` — fuel sufficiency at the bottom**
(`cSPDEGStructG_of_neg`): once the bound `n` has descended below `0`, `CSPDEGStructG Dt (fuel + 1) a b c n`
holds **unconditionally** (the `n < 0 ↦ True` short-circuit), needing NO further fuel. Each non-base peel
strictly drops `n` by `cdegG (a/g) ≥ 1`, so the descent reaches this base in `≤ n + 1` steps; the residual
`fuel = 0 ↦ False` base is therefore the ONLY genuine fuel obligation, and it is unreachable once `n < 0`.
The cheap, honest fuel-sufficiency fact (the full per-input descent needs the engine's per-level gcd data,
which `CSPDEGStructG` itself bundles — or the fuel-free `cSPDEGWf` engine, which discharges it by
construction). -/
theorem cSPDEGStructG_of_neg [CFracGcdCore α] (Dt : CPolyG α) (fuel : ℕ) (a b c : CPolyG α) (n : ℤ)
    (hn : n < 0) :
    CSPDEGStructG Dt (fuel + 1) a b c n := by
  rw [CSPDEGStructG, if_pos hn]; trivial

/-- **★ The complete §6.4 degree-descent discharge MODULO FUEL SUFFICIENCY**
(`cSPDEGSolvableInputs_of_structG`): from the unconditional structural data `CSPDEGStructG` and a bounded
abstract reduced solution, `CSPDEGSolvableInputsGen` holds. Wires ALL the proven pieces — the `K[X]`
divisibility gate (`cdvdG_g_c_of_isReducedRdeSolK`), the `n < 0` base (`cisZeroG_of_isReducedRdeSolK_neg`),
the peeled witness (`exists_peeled_reducedSolK`), and the degree bookkeeping (`degree_peeled_le` via
`cdiophantineG_fst_degree_lt`). NO degree obligation remains; the SOLE residual is the `fuel = 0` base —
i.e. fuel sufficiency, the genuine extra termination fact the soundness direction never needed. -/
theorem cSPDEGSolvableInputs_of_structG [CFracGcdCore α] (Dt : CPolyG α) :
    ∀ (fuel : ℕ) (a b c : CPolyG α) (n : ℤ) (q : (CFieldSpec.K α)[X]),
      CSPDEGStructG Dt fuel a b c n →
      IsReducedRdeSolK Dt a b c q →
      (q = 0 ∨ (q.natDegree : ℤ) ≤ n) →
      CSPDEGSolvableInputsGen Dt fuel a b c n := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b c n q hin _ _
    exact absurd hin (by rw [CSPDEGStructG]; exact not_false)
  | succ fuel ih =>
    intro a b c n q hin hsol hq
    rw [CSPDEGSolvableInputsGen]
    refine ⟨⟨q, hsol⟩, ?_⟩
    by_cases hn : n < 0
    · rw [if_pos hn]
      exact cisZeroG_of_isReducedRdeSolK_neg Dt a b c q n hn hsol hq
    · rw [if_neg hn]
      rw [CSPDEGStructG, if_neg hn] at hin
      set g := CFracGcdCore.cgcdFFCore fuel a b with hg
      set ad := cdivG fuel a g with had
      set bd := cdivG fuel b g with hbd
      obtain ⟨hg0, hgassoc, hfa, hfb, hfc, ha0, hrest⟩ := hin
      refine ⟨hg0, hgassoc, hfa, hfb, hfc, ha0, ?_⟩
      by_cases hdeg : cdegG ad = 0
      · rw [if_pos hdeg]; trivial
      · rw [if_neg hdeg] at hrest ⊢
        obtain ⟨hdiofuel, hterm, hstructrec⟩ := hrest
        refine ⟨hterm, ?_⟩
        obtain ⟨h, hqeq, hredsol⟩ := exists_peeled_reducedSolK Dt a b c g ad bd q fuel
          had hbd hg0 hfa hfb hfc ha0 hgassoc hterm hsol
        have hadne : toPolyG ad ≠ 0 := by
          have hgne : toPolyG g ≠ 0 := fun h => hg0 ((cnormG_eq_nil_iff g).mpr h)
          have hane : toPolyG a ≠ 0 := fun h => ha0 ((cnormG_eq_nil_iff a).mpr h)
          have hdiva : toPolyG ad * toPolyG g = toPolyG a :=
            had ▸ cdivG_a_exact_of_gcd fuel a b g hg0 hfa hgassoc
          exact fun h => hane (by rw [← hdiva, h, zero_mul])
        have hadnil : cnormG ad ≠ [] := fun h => hadne ((cnormG_eq_nil_iff ad).mp h)
        have hrlt : (toPolyG (cdiophantineG fuel bd ad (cdivG fuel c g)).1).degree
            < (toPolyG ad).degree :=
          cdiophantineG_fst_degree_lt fuel bd ad (cdivG fuel c g) hadnil hdiofuel
        have hcdeg : (toPolyG ad).natDegree = cdegG ad := (cdegG_eq_natDegree ad).symm
        have hbound : h = 0 ∨ (h.natDegree : ℤ) ≤ n - (cdegG ad : ℤ) := by
          have := degree_peeled_le (toPolyG ad) h
            (toPolyG (cdiophantineG fuel bd ad (cdivG fuel c g)).1) q n hadne hrlt hqeq hq
          rwa [hcdeg] at this
        exact ih ad (caddG bd (cmonomialDeriv Dt ad))
          (csubG (cdiophantineG fuel bd ad (cdivG fuel c g)).2
            (cmonomialDeriv Dt (cdiophantineG fuel bd ad (cdivG fuel c g)).1))
          (n - (cdegG ad : ℤ)) h (hstructrec _) hredsol hbound

/-- **★ END-TO-END: the §6.4 SPDE peel succeeds on a bounded reduced solution, MODULO FUEL SUFFICIENCY**
(`cSPDEG_isSome_of_structG_bounded`): composes the complete discharge `cSPDEGSolvableInputs_of_structG`
with the degree-descent induction `cSPDEG_isSome_of_solvableInputs`. The §6.4 `hspde` content modulo only
fuel sufficiency (the `CSPDEGStructG` `fuel = 0 ↦ False` base) and the upstream `IsCRischDEGPolySol →
∃ q, IsReducedRdeSolK (special-cleared) q` bridge (the §6.2/§6.3 normal+special-denominator chain). -/
theorem cSPDEG_isSome_of_structG_bounded [CFracGcdCore α] (Dt : CPolyG α) (fuel : ℕ)
    (a b c : CPolyG α) (n : ℤ) (q : (CFieldSpec.K α)[X])
    (hstruct : CSPDEGStructG Dt fuel a b c n) (hsol : IsReducedRdeSolK Dt a b c q)
    (hq : q = 0 ∨ (q.natDegree : ℤ) ≤ n) :
    (cSPDEG Dt fuel a b c n).isSome = true :=
  cSPDEG_isSome_of_solvableInputs Dt fuel a b c n
    (cSPDEGSolvableInputs_of_structG Dt fuel a b c n q hstruct hsol hq)

end SPDEDegreeDescent

/-! ## ★ The §6.2/6.3 fractional→reduced bridge — `hspde`'s upstream input (the primitive regime, PROVEN)

The §6.4 degree-descent assembly `cSPDEG_isSome_of_structG_bounded` consumes an **abstract reduced solution**
`IsReducedRdeSolK (special-cleared) q` plus the degree bound and fuel sufficiency. But the `hspde` clause is
typed against a **fractional** `IsCRischDEGPolySol` solution. The missing link — flagged as the upstream
residue of the §6.4 frontier — is the **fractional→reduced bridge** `IsCRischDEGPolySol → ∃ q,
IsReducedRdeSolK (special-cleared) q ∧ bound`: the §6.2 (normal-denominator) + §6.3 (special-denominator)
COMPLETENESS reduction.

This section PROVES that bridge in the **primitive regime** (the validated regime, where the special monic
irreducible is constant, `cdegG (cSpecialPolyG …) = 0`, witnessed operationally by `cRischDEG_isSome_Dy_eq_one`),
by COMPOSING the proven algebraic reverse-glues with residual #2's degree bound:

* the **reverse normal glue** `isReducedRdeSol_of_cleared_normalized` (the exact converse of the §6.2 soundness
  lift `cRdeNormalDenominatorG_cleared_lift_gen`, running `rdeNormalDenominator_glue_inverse`): a *normalized*
  cleared solution (denominator = the §6.2 clearing factor `h0`) gives a reduced `IsReducedRdeSol (a0,b0,c0) Q`;
* the **primitive special-stage identity** `cRdeSpecialDenominatorG_primitive_eq_gen`
  (`(a0,b0,c0,1)`), so the special-cleared coefficients *are* `(a0,b0,c0)` and the reverse special glue is the
  identity;
* the **trivial `K[X]` lift** `isReducedRdeSolK_of_isReducedRdeSol`, and the degree bound through
  `cdegG_eq_natDegree` + residual #2's `hbound`.

The bridge is therefore PROVEN modulo a precisely isolated residual `RdeFractionalToReducedResidual` whose
only deep clause is the **denominator-normalization** `hnormalize` (Bronstein Thm 6.1.2(i): a fractional
solution `y` has `q = y·h0` a *polynomial*, i.e. some normalized solution exists) — plus the engine-provable
§6.2 normal-clear certificates `hcerts`. Composing through the §6.4 assembly,
`cSPDEG_isSome_of_fractional_primitive` discharges the `hspde` content modulo this bridge residual + residual
#2's bound + fuel sufficiency. The non-primitive (hyperexp/hypertangent) special-clearing — needing the
reverse special glue `specialDenominatorSubst_cleared_inverse` with the `νₚ`-bookkeeping divisibility
`pⁿᵉᵍⁿ ∣ Q` — is the documented continuation. -/

section FractionalToReducedBridge

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]

/-- **The §6.2 normal-clear `B`-numerator certificate polynomial** `rdeNormalBNum Dt fnum fden h0`:
`dₙ·h0·fnum − dₙ·D(h0)·fden` (`dₙ = (cSplitFactorFastG Dt towerRischDEFuel fden).1`), whose exact
divisibility by `fden` is the §6.2 `b`-coefficient certificate. The `B` term of
`isReducedRdeSol_of_cleared_normalized`'s cert hypotheses, named for the residual bundle. -/
abbrev rdeNormalBNum (Dt fnum fden h0 : CPolyG α) : CPolyG α :=
  csubG (cmulG (cmulG (cSplitFactorFastG Dt towerRischDEFuel fden).1 h0) fnum)
    (cmulG (cmulG (cSplitFactorFastG Dt towerRischDEFuel fden).1 (cmonomialDeriv Dt h0)) fden)

/-- **The §6.2 normal-clear `C`-numerator certificate polynomial** `rdeNormalCNum Dt fden gnum h0`:
`dₙ·h0²·gnum`, whose exact divisibility by `gden` is the §6.2 `c`-coefficient certificate. The `C` term of
`isReducedRdeSol_of_cleared_normalized`'s cert hypotheses, named for the residual bundle. -/
abbrev rdeNormalCNum (Dt fden gnum h0 : CPolyG α) : CPolyG α :=
  cmulG (cmulG (cmulG (cSplitFactorFastG Dt towerRischDEFuel fden).1 h0) h0) gnum

/-! ### ★ The `hnormalize` composition verdict and its precise irreducible remainder

**`hnormalize` does NOT compose from the `cValuationG`-correctness keystone.** That keystone
(`toPolyG_pow_cValuationG_dvd` / `cValuationG_sharp`) is **polynomial** multiplicity — `νₚ` of an element of
`K[X]` by trial division. `hnormalize` (Bronstein Thm 6.1.2(i)) is a **fraction-field valuation** fact about
the solution `y = ynum/yden ∈ K(t)` (where `K = CFieldSpec.K α`): the denominator of `y` divides the §6.1
clearing factor `h0` (so `q = y·h0` is normal-pole-free). Sub-fact map:

* `cValuationG`-correctness `pⁿ ∣ x` + sharpness — EXISTS, but it is the `K[X]`-multiplicity tool used by
  residual #1's `eₙ ∣ dₙh²` *divisibility* (`ComputableRischDENormDivisibility`), a different clause one level
  below `hnormalize`'s `K(t)`-valuation claim.
* the per-prime RDE order bound `νₚ(y) ≥ −νₚ(h0)` for `y ∈ K(t)` — NEW; its math heart is
  **Bronstein Lemma 6.1.1 / Theorem 4.4.2**, "a derivation drops the order at a normal pole by exactly one"
  (`νₚ(Dy) = νₚ(y) − 1`). The reusable **polynomial-ring kernel** of that fact is now PROVEN, derivation-
  generic, in `ComputableRischDETowerCorrectG`: `pow_sub_one_dvd_deriv_of_pow_dvd` (lower bound, universal),
  `not_pow_dvd_deriv_of_normal` (exact half at a normal prime, char zero), and the assembled
  `emultiplicity_deriv_eq_sub_one_of_normal`.
* residual #1's `derivative_rootMultiplicity`/`cValuationG` machinery — partial, the `K[X]` side only.

**Status of the four pieces** (★ items 1, 4 and the per-prime heart are now PROVEN):
1. ✅ the **`K(t)`-valuation lift** — `ComputableRatFuncValuation` defines the integer valuation
   `ratFuncOrd p y = νₚ(num y) − νₚ(denom y)` on `RatFunc K` and PROVES `νₚ(D y) = νₚ(y) − 1` at a normal
   pole (`ratFuncOrd_extendDeriv_eq_sub_one_of_normal`), lifting the `K[X]` Wronskian kernel
   (`emultiplicity_wronskian_numerator_eq_of_normal`) through the engine's fraction-field derivation
   `extendDeriv = towerFractionFieldDerivG` — NOT via `Polynomial.idealX`, but a direct `multiplicity`
   valuation. The valuation algebra (`ratFuncOrd_mul`, `ratFuncOrd_add_of_lt`) and the **per-prime RDE
   no-pole bound** `ratFuncOrd_nonneg_of_rde_at_normal` (a pole forces `νₚ(Dy)<νₚ(fy)`, so the sum's order
   `= νₚ(y)−1 < 0 ≤ νₚ(g)`, contradiction) are PROVEN — the §6.1 pole-cancellation heart.
4. ✅ the **non-degeneracy** premise — carried explicitly: `rdeFractional_of_isCRischDEGPolySol` takes
   `fden, gden, yden ≠ 0` and lifts the cleared `IsCRischDEGPolySol` identity to the genuine fraction-field
   RDE `D Y + F·Y = G` over `RatFunc K`, wiring the valuation calculus to the engine hypothesis.

What **is now assembled** (the global `∃ Q` conclusion is CLOSED, see the §6.1 global-assembly section
below — `exists_isCRischDEGPolySol_h0_of_poleBounded` / `hnormalize_of_poleBounded`):
1. ✅ **Step 1 — weak normalization, demonstrated**: `ratFuncOrd_solution_nonneg_off_h0` discharges
   `νₚ(Y) ≥ 0` for every normal `p ∤ h0` with `νₚ(F),νₚ(G) ≥ 0`, the proven per-prime RDE bound applied
   through the fractional lift. The residual content (the sharp pole count at `p ∣ h0`, and the
   weak-normalization confinement of `F`/`G` poles to `h0`) is bundled as the honest per-prime hypothesis
   `IsRdeNormalPoleBounded` (Bronstein Thm 6.1.2(i) per-prime form).
2. ✅ **Step 2 — UFM recombination, PROVEN**: `solution_denom_dvd_h0_of_poleBounded` turns the per-prime
   bound `∀ p, −νₚ(h0) ≤ νₚ(Y)` into `denom(Y) ∣ h0` via `UniqueFactorizationMonoid.dvd_iff_emultiplicity_le`
   (`ComputableRatFuncValuation.ratFunc_denom_dvd_of_ratFuncOrd_bound`).
3. ✅ **`CPolyG`-realization, PROVEN modulo `toK`-surjectivity**: `RatFunc.denom_dvd` then gives
   `Y = amG(Q')/amG(h0)` for a polynomial `Q' : K[X]`; `toPolyG_surjective_of_toK_surjective` (true at every
   tower carrier) pulls `Q'` back to a `CPolyG`, and the reverse cleared-identity bridge
   `isCRischDEGPolySol_of_field_rde` recovers the engine's polynomial-solution predicate.

So `hnormalize` is **closed** as a derived theorem (`hnormalize_of_poleBounded`, NO `sorry`) modulo exactly
three precisely-isolated honest hypotheses: `IsRdeNormalPoleBounded` (the genuine deep §6.1 Thm 6.1.2(i)
per-prime content), `toK`-surjectivity (engine realization), and the `cRdeNormalDenominatorG`-output
nonzeros (engine-provable, as in `hcerts`). The `k⟨t⟩` special-pole subtlety is folded into
`IsRdeNormalPoleBounded`: in the primitive regime `cdegG (cSpecialPolyG) = 0` there are no special primes,
so the per-prime bound ranges over all (normal) primes and `Q = Y·h0 ∈ k[t]` is the full Thm 6.1.2(i). -/

/-- **★ The §6.2/6.3 fractional→reduced bridge residual** `RdeFractionalToReducedResidual Dt fnum fden gnum
gden`: the precise upstream input the §6.4 `hspde` needs but the engine does not self-certify, in
solvability-implies form. `hnormalize`: ★ the **single deep clause** (Bronstein Thm 6.1.2(i)) — a fractional
solution yields one whose **denominator equals the §6.2 clearing factor** `h0` (`∃ Q, IsCRischDEGPolySol … Q
h0`), i.e. `q = y·h0` is a *polynomial*. Does NOT compose from `cValuationG`-correctness (that is `K[X]`
multiplicity; this is a `K(t)` valuation fact); its math kernel `νₚ(Dy) = νₚ(y) − 1` is proven derivation-
generic (`emultiplicity_deriv_eq_sub_one_of_normal`), the irreducible remainder being the `K(t)`-valuation
lift + weak normalization + `k⟨t⟩` (see the section note above). `hcerts`: the §6.2 normal-clear certificates
(the `B/C` exact divisibilities + fuel/nonzero bounds the soundness lift also consumes — engine-provable,
bundled honestly). A `Prop`-bundle of stated assumptions, NO `sorry`; the irreducible §6.2 denominator-
clearing content of the fractional→reduced bridge. -/
structure RdeFractionalToReducedResidual (Dt fnum fden gnum gden : CPolyG α) : Prop where
  /-- ★ Bronstein Thm 6.1.2(i): a fractional solution yields one with denominator = the clearing factor `h0`
  (`q = y·h0 ∈ k[t]`). The deep §6.1/6.2 denominator-clearing content — now DERIVABLE (no `sorry`) via
  `hnormalize_of_poleBounded` from the proven `K(t)`-valuation assembly plus the honest per-prime pole bound
  `IsRdeNormalPoleBounded` + `toK`-surjectivity + the output nonzeros. -/
  hnormalize : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    ∀ a0 b0 c0 h0 : CPolyG α,
      cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden = some (a0, b0, c0, h0) →
      ∃ Q : CPolyG α, IsCRischDEGPolySol Dt fnum fden gnum gden Q h0
  /-- The §6.2 normal-clear certificates (`fden, gden ≠ 0`, the `B/C` exact divisibilities + fuel bounds) —
  engine-provable from the §6.2 setup, the same facts `cRdeNormalDenominatorG_cleared_lift_gen` consumes. -/
  hcerts : ∀ a0 b0 c0 h0 : CPolyG α,
    cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden = some (a0, b0, c0, h0) →
      (cnormG fden ≠ []) ∧ (cnormG gden ≠ [])
      ∧ ((cnormG (rdeNormalBNum Dt fnum fden h0) : List α).length ≤ towerRischDEFuel)
      ∧ (toPolyG fden ∣ toPolyG (rdeNormalBNum Dt fnum fden h0))
      ∧ ((cnormG (rdeNormalCNum Dt fden gnum h0) : List α).length ≤ towerRischDEFuel)
      ∧ (toPolyG gden ∣ toPolyG (rdeNormalCNum Dt fden gnum h0))

omit [CFracGcdCore α] in
/-- **★ The cleared-identity → fraction-field RDE bridge** (`rdeFractional_of_isCRischDEGPolySol`): a
fractional `IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden` (the cleared *polynomial* identity over
`(CFieldSpec.K α)[X]`) yields the genuine **fraction-field** Risch DE `D Y + F·Y = G` over
`RatFunc (CFieldSpec.K α)` — with `D = towerFractionFieldDerivG Dt = extendDeriv (implicitDeriv (toPolyG
Dt))`, `Y = amG ynum / amG yden`, `F = amG fnum / amG fden`, `G = amG gnum / amG gden` — under the honest
non-degeneracy hypotheses `fden, gden, yden ≠ 0` (the cleared identity is satisfied vacuously by a zero
denominator; recovering an actual `y ∈ K(t)` needs them nonzero). Expands the derivative via the quotient
rule (`towerFractionFieldDerivG_div`), clears denominators (all nonzero), and collapses the resulting field
identity onto `amG` of the `IsCRischDEGPolySol` polynomial identity (`amG` a ring hom). This is the wiring
that makes the `K(t)`-valuation calculus (`ratFuncOrd_nonneg_of_rde_at_normal`) applicable to the engine's
`IsCRischDEGPolySol` — the bridge the §6.1 `hnormalize` valuation argument runs over. -/
theorem rdeFractional_of_isCRischDEGPolySol [Algebra ℚ (CFieldSpec.K α)]
    (Dt fnum fden gnum gden ynum yden : CPolyG α)
    (hfden : toPolyG fden ≠ 0) (hgden : toPolyG gden ≠ 0) (hyden : toPolyG yden ≠ 0)
    (hsol : IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) :
    towerFractionFieldDerivG Dt (amG α (toPolyG ynum) / amG α (toPolyG yden))
        + amG α (toPolyG fnum) / amG α (toPolyG fden)
          * (amG α (toPolyG ynum) / amG α (toPolyG yden))
      = amG α (toPolyG gnum) / amG α (toPolyG gden) := by
  -- the `amG`-images of the nonzero denominators are nonzero.
  have hFDne : amG α (toPolyG fden) ≠ 0 := amG_toPolyG_ne_zero hfden
  have hGDne : amG α (toPolyG gden) ≠ 0 := amG_toPolyG_ne_zero hgden
  have hYDne : amG α (toPolyG yden) ≠ 0 := amG_toPolyG_ne_zero hyden
  -- expand the derivative via the quotient rule.
  rw [towerFractionFieldDerivG_div]
  -- the `amG`-image of the cleared polynomial identity (a ring-hom translation of `hsol`).
  have hsolF : amG α (toPolyG gden) * amG α (toPolyG fden)
        * (amG α (Differential.implicitDeriv (toPolyG Dt) (toPolyG ynum)) * amG α (toPolyG yden)
            - amG α (toPolyG ynum) * amG α (Differential.implicitDeriv (toPolyG Dt) (toPolyG yden)))
      + amG α (toPolyG gden) * amG α (toPolyG fnum) * amG α (toPolyG ynum) * amG α (toPolyG yden)
      = amG α (toPolyG gnum) * amG α (toPolyG fden) * amG α (toPolyG yden) ^ 2 := by
    have h := congrArg (amG α) hsol
    simpa only [map_add, map_mul, map_sub, map_pow] using h
  -- combine the LHS into a single fraction, then cross-multiply against `Gn/g`.
  rw [div_mul_div_comm, div_add_div _ _ (pow_ne_zero 2 hYDne) (mul_ne_zero hFDne hYDne),
    div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hYDne) (mul_ne_zero hFDne hYDne)) hGDne]
  ring_nf
  ring_nf at hsolF
  linear_combination (amG α (toPolyG yden)) * hsolF

/-- **★ The fractional→reduced bridge in the primitive regime** (`exists_isReducedRdeSol_special_of_fractional`):
under `RdeFractionalToReducedResidual` and the primitive special regime (`cdegG (cSpecialPolyG …) = 0`), a
fractional `IsCRischDEGPolySol` solution yields a `Q : CPolyG` solving the **special-cleared** reduced equation
— `IsReducedRdeSol (cRdeSpecialDenominatorG … a0 b0 c0) Q`. Composes the residual's normalization
(`hnormalize`) and certs (`hcerts`) through the reverse normal glue `isReducedRdeSol_of_cleared_normalized`,
then the primitive special-stage identity `cRdeSpecialDenominatorG_primitive_eq_gen` (special-cleared =
`(a0,b0,c0)`). The §6.2/6.3 completeness reduction, primitive regime, PROVEN modulo only the bridge residual. -/
theorem exists_isReducedRdeSol_special_of_fractional
    (Dt fnum fden gnum gden a0 b0 c0 h0 : CPolyG α)
    (hprim : cdegG (cSpecialPolyG Dt towerRischDEFuel) = 0)
    (hnorm : cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden = some (a0, b0, c0, h0))
    (hres : RdeFractionalToReducedResidual Dt fnum fden gnum gden)
    (hsol : ∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) :
    ∃ Q : CPolyG α, IsReducedRdeSol Dt
      (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
      (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
      (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1 Q := by
  obtain ⟨Q, hQcleared⟩ := hres.hnormalize hsol a0 b0 c0 h0 hnorm
  obtain ⟨hfden0, hgden0, hfbB, hdvdB, hfbC, hdvdC⟩ := hres.hcerts a0 b0 c0 h0 hnorm
  have hred : IsReducedRdeSol Dt a0 b0 c0 Q :=
    isReducedRdeSol_of_cleared_normalized Dt towerRischDEFuel fnum fden gnum gden a0 b0 c0 h0 Q
      hnorm hfden0 hgden0 hfbB hdvdB hfbC hdvdC hQcleared
  refine ⟨Q, ?_⟩
  rw [cRdeSpecialDenominatorG_primitive_eq_gen Dt towerRischDEFuel a0 b0 c0 hprim]
  exact hred

/-- **★ The §6.4 `hspde` content from the fractional→reduced bridge (primitive regime)**
(`cSPDEG_isSome_of_fractional_primitive`): END-TO-END discharge of the `hspde` clause's body in the primitive
regime. From a fractional solution, the bridge residual, residual #2's degree bound `hbound`, and fuel
sufficiency `CSPDEGStructG` (on the special-cleared coefficients at the §6.3 bound), the §6.4 SPDE peel
succeeds — `(cSPDEG … (special-cleared) … (bound)).isSome = true`. Composes
`exists_isReducedRdeSol_special_of_fractional` (the bridge) with the proven §6.4 degree-descent assembly
`cSPDEG_isSome_of_structG_bounded`: the bridged reduced solution `Q` is bounded (via `hbound` +
`cdegG_eq_natDegree`) and lifts to `IsReducedRdeSolK`. The exact `hspde` clause MODULO the bridge residual +
residual #2's bound + fuel sufficiency — discharging residual #3's clause (ii) in the primitive regime. -/
theorem cSPDEG_isSome_of_fractional_primitive
    (Dt fnum fden gnum gden a0 b0 c0 h0 : CPolyG α)
    (hprim : cdegG (cSpecialPolyG Dt towerRischDEFuel) = 0)
    (hnorm : cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden = some (a0, b0, c0, h0))
    (hres : RdeFractionalToReducedResidual Dt fnum fden gnum gden)
    (hbound : ∀ q : CPolyG α,
      IsReducedRdeSol Dt (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1 q →
      cdegG q ≤ cRdeBoundDegreeG Dt towerRischDEFuel
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1)
    (hstruct : CSPDEGStructG Dt towerRischDEFuel
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt towerRischDEFuel
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1 : ℤ))
    (hsol : ∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) :
    (cSPDEG Dt towerRischDEFuel
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt towerRischDEFuel
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1 : ℤ)).isSome = true := by
  obtain ⟨Q, hQred⟩ :=
    exists_isReducedRdeSol_special_of_fractional Dt fnum fden gnum gden a0 b0 c0 h0 hprim hnorm hres hsol
  have hdeg : (toPolyG Q).natDegree ≤ cRdeBoundDegreeG Dt towerRischDEFuel
      (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
      (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
      (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1 := by
    have := hbound Q hQred; rwa [cdegG_eq_natDegree] at this
  exact cSPDEG_isSome_of_structG_bounded Dt towerRischDEFuel _ _ _ _ (toPolyG Q) hstruct
    (isReducedRdeSolK_of_isReducedRdeSol Dt _ _ _ Q hQred) (Or.inr (by exact_mod_cast hdeg))

/-- **★ The exact `hspde` clause from the fractional→reduced bridge (primitive regime)**
(`hspde_of_fractionalBridge`): produces the **verbatim** `RischDESolveExhaustiveResidual.hspde` field type from
the §6.2/6.3 bridge residual, the primitive special regime, residual #2's per-output degree bound `hbound`,
and per-output fuel sufficiency `hstruct`. For each normal-denominator output `(a0, b0, c0, h0)`, dispatches to
the end-to-end `cSPDEG_isSome_of_fractional_primitive`. This is the discharge of residual #3's clause (ii):
`hspde` is no longer an *assumed* converse fact — it is *produced* from the precisely isolated upstream bridge
residual (deep clause: the §6.1/6.2 denominator-normalization) + residual #2's bound + fuel sufficiency,
reducing `RischDESolveExhaustiveResidual` to **only** `hpoly` (§6.5/6.6) plus `hnorm` (§6.2, residual #1). -/
theorem hspde_of_fractionalBridge (Dt fnum fden gnum gden : CPolyG α)
    (hprim : cdegG (cSpecialPolyG Dt towerRischDEFuel) = 0)
    (hres : RdeFractionalToReducedResidual Dt fnum fden gnum gden)
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
    (hstruct : ∀ a0 b0 c0 h0 : CPolyG α,
      cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden = some (a0, b0, c0, h0) →
      CSPDEGStructG Dt towerRischDEFuel
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt towerRischDEFuel
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1 : ℤ)) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    ∀ a0 b0 c0 h0 : CPolyG α,
      cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden = some (a0, b0, c0, h0) →
      (cSPDEG Dt towerRischDEFuel (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1
          (cRdeBoundDegreeG Dt towerRischDEFuel (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1 : ℤ)).isSome = true := by
  intro hsol a0 b0 c0 h0 hnorm
  exact cSPDEG_isSome_of_fractional_primitive Dt fnum fden gnum gden a0 b0 c0 h0 hprim hnorm hres
    (hbound a0 b0 c0 h0 hnorm) (hstruct a0 b0 c0 h0 hnorm) hsol

end FractionalToReducedBridge

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
  the constant-base descent (`isReducedRdeSol_const_base`), ★ the **peel-step inverse**
  (`spde_step_glue_inverse`, the exact converse of the soundness peel atom `spde_step_glue`/
  `cSPDE_peel_cleared_gen`), and ★ now the **peeling-divisibility** itself
  (`dvd_sub_of_isReducedRdeSol` / `peeling_dvd_of_isCoprime`: from the SPDE coprimality `gcd(a/g, b/g) = 1`,
  a divided-equation solution forces `(a/g) ∣ (q − r)`, via the Bézout `(b/g)·r + (a/g)·z = c/g` —
  `IsCoprime.dvd_of_dvd_mul_left` after `(b/g)·(q − r) = (a/g)·(z − Dq)`). Their composite
  `spde_peel_inverse_toPolyG` is the **complete one-step inverse**: a divided-equation solution `q`
  *provably* yields a peel factor `h` with `q = (a/g)·h + r` solving the reduced
  `(a/g)·Dh + ((b/g) + D(a/g))·h = z − Dr`. ★ The **degree-descent recursion assembly is now PROVEN** (the
  `SPDEDegreeDescent` section): `cSPDEG_isSome_of_solvableInputs` runs the soundness lifting
  `cSPDEG_cleared_lifting_gen` IN REVERSE down the `cdegG(a/g)`-shrinking ladder, threading the per-step
  inverse over `K[X]` (`exists_peeled_reducedSolK`, so no `CPolyG`-lift obligation), the gcd-coprimality
  (`isCoprime_bd_ad_of_divided`), the `n < 0` base (`cisZeroG_of_isReducedRdeSolK_neg`), and ★ the
  **degree-descent bookkeeping** `deg(h) ≤ n − deg(a/g)` (`degree_peeled_le`) — the fact the forward
  direction never needed. `cSPDEG_isSome_of_structG_bounded` assembles the whole descent
  (`cSPDEGSolvableInputs_of_structG`) modulo **only fuel sufficiency** (the `CSPDEGStructG` `fuel = 0 ↦
  False` base — the degree ladder bottoms out before fuel runs out). The residue narrows to fuel
  sufficiency **plus** the upstream `IsCRischDEGPolySol → ∃ q, IsReducedRdeSolK (special-cleared) q ∧ bound`
  bridge (the §6.2/§6.3 normal+special-denominator chain), which `hspde` as currently typed still needs.

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
§6.4 SPDE peel at the §6.3 bound degree return `some` (the divisibility necessity + constant-base descent +
the complete per-step inverse + ★ now the **degree-descent recursion assembly**
`cSPDEG_isSome_of_structG_bounded` are proven; only fuel sufficiency and the upstream fractional→reduced
bridge remain). `hpoly`: ★ for the SPDE output
`(bbar, cbar, m)`, a solution makes the §6.5/§6.6 poly-RDE dispatcher return `some` (the b=0/c=0 base
sub-cases are proven; the cancellation-regime exhaustiveness is the deep residue). Their conjunction, threaded
through `cRischDEG_isSome_of_stages`, is exactly `hsolve`. A `Prop`-bundle of stated assumptions, NO
`sorry`. -/
structure RischDESolveExhaustiveResidual (Dt fnum fden gnum gden : CPolyG α) : Prop where
  /-- §6.2: a polynomial solution makes the normal-denominator step return `some` (from `hnorm`). -/
  hnorm : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    (cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden).isSome = true
  /-- ★ §6.4: for a normal-denominator output `(a0, b0, c0, h0)`, a solution makes the SPDE peel at the §6.3
  bound degree on the special-cleared coefficients return `some` (per-step inverse AND degree-descent
  assembly proven; only fuel sufficiency + the upstream fractional→reduced bridge remain). -/
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

/-- **★ `RischDESolveExhaustiveResidual` from the fractional→reduced bridge (primitive regime)**
(`exhaustiveResidual_of_fractionalBridge`): builds the §6.4–6.6 exhaustiveness residual from the §6.2/6.3
bridge residual `RdeFractionalToReducedResidual` (which discharges `hspde` via `hspde_of_fractionalBridge`),
the §6.2 `hnorm` (residual #1), residual #2's per-output degree bound, the per-output fuel sufficiency, and the
§6.5/6.6 `hpoly`. The `hspde` clause is no longer assumed — it is *produced* from the precisely isolated
upstream bridge. So residual #3 (`RischDESolveExhaustiveResidual`) is reduced, in the primitive regime, to
**only** `hnorm` (§6.2 normal-denominator, = residual #1) + `hpoly` (§6.5/6.6 cancellation-regime
exhaustiveness) + the upstream bridge residual (deep clause: §6.1/6.2 denominator-normalization) + residual
#2's bound + fuel sufficiency — clause (ii) `hspde` is closed. -/
theorem exhaustiveResidual_of_fractionalBridge (Dt fnum fden gnum gden : CPolyG α)
    (hprim : cdegG (cSpecialPolyG Dt towerRischDEFuel) = 0)
    (hnormSome : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden).isSome = true)
    (hbridge : RdeFractionalToReducedResidual Dt fnum fden gnum gden)
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
    (hstruct : ∀ a0 b0 c0 h0 : CPolyG α,
      cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden = some (a0, b0, c0, h0) →
      CSPDEGStructG Dt towerRischDEFuel
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt towerRischDEFuel
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1 : ℤ))
    (hpolyDispatch : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      ∀ a0 b0 c0 h0 bbar cbar : CPolyG α, ∀ m : ℤ, ∀ α' β : CPolyG α,
        cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden = some (a0, b0, c0, h0) →
        cSPDEG Dt towerRischDEFuel (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1
            (cRdeBoundDegreeG Dt towerRischDEFuel (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
              (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
              (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1 : ℤ)
          = some (bbar, cbar, m, α', β) →
        (cPolyRischDEG Dt towerRischDEFuel bbar cbar m).isSome = true) :
    RischDESolveExhaustiveResidual Dt fnum fden gnum gden where
  hnorm := hnormSome
  hspde := hspde_of_fractionalBridge Dt fnum fden gnum gden hprim hbridge hbound hstruct
  hpoly := hpolyDispatch

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
* ★ the **SPDE per-step solution-preservation** (the structural heart, now *complete* for one peel step) —
  `dvd_c_of_isReducedRdeSol` (the **divisibility necessity**: g∣a ∧ g∣b ⟹ a solution forces g∣c, so the SPDE
  `cdvdG` gate never rejects a true solution — pure algebra, no gcd correctness), `isReducedRdeSol_const_base`
  (the constant-base descent: q itself is the reduced solution), `spde_step_glue_inverse` (the **peel-step
  inverse**, exact converse of the soundness `spde_step_glue`: a solution in peeled form `q = a·h + r` makes
  `h` provably solve the reduced equation, by cancelling the nonzero leading `a`), ★ the **peeling-divisibility**
  `peeling_dvd_of_isCoprime` / `dvd_sub_of_isReducedRdeSol` (from `gcd(a/g, b/g) = 1`, a divided-equation
  solution forces `(a/g) ∣ q − r` — `IsCoprime.dvd_of_dvd_mul_left` after `(b/g)·(q − r) = (a/g)·(z − Dq)`),
  and their composite ★ `spde_peel_inverse_of_isCoprime` / `spde_peel_inverse_toPolyG` (the **complete one-step
  inverse**: a divided-equation solution `q` yields a peel factor `h` with `q = (a/g)·h + r` solving the
  reduced equation — the diophantine degree-peel step is no longer a residue);
* ★ the **§6.4 degree-descent recursion assembly** (the `SPDEDegreeDescent` section, the structural heart of
  `hspde`, now *complete* modulo fuel sufficiency) — `cSPDEG_isSome_of_solvableInputs` (the soundness lifting
  `cSPDEG_cleared_lifting_gen` run IN REVERSE down the `cdegG(a/g)` ladder), `exists_peeled_reducedSolK` (the
  per-step inverse threaded over `K[X]`, so no `CPolyG`-lift), `isCoprime_bd_ad_of_divided` (the SPDE
  coprimality from the unit divided-gcd), `cisZeroG_of_isReducedRdeSolK_neg` (the `n < 0 ⟹ q = 0 ⟹ c = 0`
  base), ★ `degree_peeled_le` (the **degree-descent bookkeeping** `deg h ≤ n − deg(a/g)` — the fact the
  forward direction never needed), and the assembly `cSPDEGSolvableInputs_of_structG` /
  `cSPDEG_isSome_of_structG_bounded` (the whole descent, modulo only the `CSPDEGStructG` `fuel = 0 ↦ False`
  base = fuel sufficiency).

**The deep residual** (`RischDESolveExhaustiveResidual`, NEVER `sorry`). Two staged converse facts the engine
does not self-certify:
* **`hspde`** — the §6.4 SPDE peel returns `some` on a solvable input. Reachable layers proven: divisibility
  necessity + constant-base descent + the complete one-step inverse + ★ the **degree-descent recursion
  assembly** `cSPDEG_isSome_of_structG_bounded` (the per-step inverse iterated down the shrinking `deg(a/g)`
  ladder, with the degree bookkeeping `degree_peeled_le` proven), and ★ now the **fractional→reduced bridge**
  itself in the primitive regime — `cSPDEG_isSome_of_fractional_primitive` / `hspde_of_fractionalBridge` /
  `exhaustiveResidual_of_fractionalBridge` (the §6.2 reverse normal glue `rdeNormalDenominator_glue_inverse` /
  `isReducedRdeSol_of_cleared_normalized`, the primitive special-stage identity, residual #2's bound, and the
  trivial `K[X]` lift), so the upstream bridge `IsCRischDEGPolySol → ∃ q, IsReducedRdeSolK (special-cleared) q
  ∧ bound` is PROVEN modulo only its own deep clause. The residue narrows to: (i) **fuel sufficiency** — the
  degree ladder bottoms out before fuel runs out (the `CSPDEGStructG` `fuel = 0 ↦ False` base; soundness is
  happy with `none` at fuel 0); (ii) the bridge residual `RdeFractionalToReducedResidual`, whose **single deep
  clause** is the §6.1/6.2 **denominator-normalization** `hnormalize` (Bronstein Thm 6.1.2(i): `q = y·h0` is a
  *polynomial*) — the cert clause `hcerts` is engine-provable; and (iii) the **non-primitive** special-clearing
  (hyperexp/hypertangent), needing the reverse special glue `specialDenominatorSubst_cleared_inverse` (proven)
  with the `νₚ`-bookkeeping divisibility `pⁿᵉᵍⁿ ∣ Q` — the documented continuation. The algebraic spine of
  clause (ii) is thereby **discharged**: residual #3's `hspde` is reduced to the denominator-normalization
  fact + fuel sufficiency.
* **`hpoly`** — the §6.5/§6.6 poly-RDE dispatcher returns `some` on a solvable reduced equation. Reachable
  base sub-cases proven (b=0/c=0); the irreducible residue is the **cancellation-regime exhaustiveness** (the
  non-cancellation top-down solve and the primitive/hyperexponential cancellation recursions each find a
  bounded solution if one exists) — the converse of the cancellation cleared identities.

**What `RischDEInnerCompleteness` now reduces to (the complete 3-clause map).** With `hnorm`
(`ComputableRischDENormCompleteness`, modulo Bronstein Thm 6.1.2 divisibility), `hbound`
(`ComputableRischDEDegreeBound`, modulo the §6.3 `λ`-cancellation), and `hsolve` here (modulo the §6.4–6.6
SPDE degree-descent-assembly + cancellation-regime residue — the per-step SPDE inverse incl. its
peeling-divisibility now proven), `rischDEInnerCompleteness_of_residuals` assembles
`RischDEInnerCompleteness` **in full** from its three precise residuals. Clause (c) of
`RischDECompletenessResidual` — and hence the whole §6 decision-procedure completeness `solvable ⟹ some` — is
mapped to exactly three precisely isolated deep facts, **none** a `sorry`: the §6.2 normal-denominator
divisibility, the §6.3 degree-bound cancellation, and the §6.4–6.6 SPDE/poly-RDE exhaustiveness. -/

/-! ### Restatements of the §6.4 degree-descent assembly (anonymous `example`s) -/

-- ★ The degree-descent induction: the recursive solvable-inputs predicate forces `cSPDEG.isSome`.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
    (Dt : CPolyG α) (fuel : ℕ) (a b c : CPolyG α) (n : ℤ)
    (h : CSPDEGSolvableInputsGen Dt fuel a b c n) :
    (cSPDEG Dt fuel a b c n).isSome = true :=
  cSPDEG_isSome_of_solvableInputs Dt fuel a b c n h

-- ★ The end-to-end §6.4 success on a bounded reduced solution, modulo fuel sufficiency (`CSPDEGStructG`).
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
    (Dt : CPolyG α) (fuel : ℕ) (a b c : CPolyG α) (n : ℤ) (q : (CFieldSpec.K α)[X])
    (hstruct : CSPDEGStructG Dt fuel a b c n) (hsol : IsReducedRdeSolK Dt a b c q)
    (hq : q = 0 ∨ (q.natDegree : ℤ) ≤ n) :
    (cSPDEG Dt fuel a b c n).isSome = true :=
  cSPDEG_isSome_of_structG_bounded Dt fuel a b c n q hstruct hsol hq

/-! ### Restatements of the §6.2/6.3 fractional→reduced bridge (anonymous `example`s) -/

-- ★ The reverse normal glue: the converse of `rdeNormalDenominator_glue` (normalized `yden = H`).
example {R : Type*} [CommRing R] [NoZeroDivisors R] (D : Derivation ℤ R R)
    (DN H FNUM FDEN GNUM GDEN A B C Q : R) (hFDEN : FDEN ≠ 0) (hGDEN : GDEN ≠ 0)
    (hA : A = DN * H) (hB : B * FDEN = A * FNUM - DN * D H * FDEN)
    (hC : C * GDEN = DN * H ^ 2 * GNUM)
    (hcleared : GDEN * FDEN * (D Q * H - Q * D H) + GDEN * FNUM * Q * H = GNUM * FDEN * H ^ 2) :
    A * D Q + B * Q = C :=
  rdeNormalDenominator_glue_inverse D DN H FNUM FDEN GNUM GDEN A B C Q hFDEN hGDEN hA hB hC hcleared

-- ★ The reverse special glue: the converse of `specialDenominatorSubst_cleared` (`Dp = E·p`, cancel `pᵏ`).
example {R : Type*} [CommRing R] [NoZeroDivisors R] (D : Derivation ℤ R R) (a b c p E q : R) (k : ℕ)
    (hp : p ≠ 0) (hDp : D p = E * p)
    (hcleared : a * D (q * p ^ k) + b * (q * p ^ k) = c * p ^ k) :
    a * D q + b * q + (k : R) * (a * E) * q = c :=
  specialDenominatorSubst_cleared_inverse D a b c p E q k hp hDp hcleared

-- ★ The `negn = 0` (no-clear) reverse special glue: `pⁿᵉᵍⁿ ∣ Q` is the trivial `1 ∣ Q`, no correction term.
example {R : Type*} [CommRing R] [NoZeroDivisors R] (D : Derivation ℤ R R) (a b c p E Q : R)
    (hp : p ≠ 0) (hDp : D p = E * p)
    (hcleared : a * D (Q * p ^ 0) + b * (Q * p ^ 0) = c * p ^ 0) :
    a * D Q + b * Q = c :=
  specialDenominatorSubst_cleared_inverse_noClear D a b c p E Q hp hDp hcleared

-- ★ The degree-descent ladder bottoms out at `n < 0`: `CSPDEGStructG` holds with no further fuel.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
    (Dt : CPolyG α) (fuel : ℕ) (a b c : CPolyG α) (n : ℤ) (hn : n < 0) :
    CSPDEGStructG Dt (fuel + 1) a b c n :=
  cSPDEGStructG_of_neg Dt fuel a b c n hn

-- ★ The bridge produces the EXACT `hspde` field type of `RischDESolveExhaustiveResidual`, used as that field.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
    [CRischField α] (Dt fnum fden gnum gden : CPolyG α)
    (hprim : cdegG (cSpecialPolyG Dt towerRischDEFuel) = 0)
    (hnormSome : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      (cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden).isSome = true)
    (hbridge : RdeFractionalToReducedResidual Dt fnum fden gnum gden)
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
    (hstruct : ∀ a0 b0 c0 h0 : CPolyG α,
      cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden = some (a0, b0, c0, h0) →
      CSPDEGStructG Dt towerRischDEFuel
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
        (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1
        (cRdeBoundDegreeG Dt towerRischDEFuel
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1 : ℤ))
    (hpolyDispatch : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      ∀ a0 b0 c0 h0 bbar cbar : CPolyG α, ∀ m : ℤ, ∀ α' β : CPolyG α,
        cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden = some (a0, b0, c0, h0) →
        cSPDEG Dt towerRischDEFuel (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
            (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
            (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1
            (cRdeBoundDegreeG Dt towerRischDEFuel (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).1
              (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.1
              (cRdeSpecialDenominatorG Dt towerRischDEFuel a0 b0 c0).2.2.1 : ℤ)
          = some (bbar, cbar, m, α', β) →
        (cPolyRischDEG Dt towerRischDEFuel bbar cbar m).isSome = true) :
    RischDESolveExhaustiveResidual Dt fnum fden gnum gden :=
  exhaustiveResidual_of_fractionalBridge Dt fnum fden gnum gden hprim hnormSome hbridge hbound
    hstruct hpolyDispatch

/-! ### Axiom audit (the engine, base, SPDE-control-flow, preservation, ★ degree-descent layers, and the
modular assembly are axiom-clean; NO `sorry`; only the `native_decide` operational witnesses use the
compiler) -/

#print axioms cRischDEG_isSome_of_stages
#print axioms cRischDEG_isSome_iff_stages
#print axioms cPolyRischDEG_isSome_of_bZero
#print axioms cSPDEG_isSome_of_const_base
#print axioms cSPDEG_isSome_of_recurse
#print axioms spde_step_glue_inverse
#print axioms peeling_dvd_of_isCoprime
#print axioms spde_peel_inverse_of_isCoprime
#print axioms dvd_c_of_isReducedRdeSol
#print axioms dvd_sub_of_isReducedRdeSol
#print axioms spde_peel_inverse_toPolyG
#print axioms isReducedRdeSol_const_base
#print axioms cSPDEG_isSome_of_solvableInputs
#print axioms exists_peeled_reducedSolK
#print axioms degree_peeled_le
#print axioms cisZeroG_of_isReducedRdeSolK_neg
#print axioms cSPDEGSolvableInputs_of_structG
#print axioms cSPDEG_isSome_of_structG_bounded
#print axioms cSPDEGStructG_of_neg
#print axioms hsolve_of_exhaustiveResidual
#print axioms rischDEInnerCompleteness_of_residuals
#print axioms rdeNormalDenominator_glue_inverse
#print axioms specialDenominatorSubst_cleared_inverse
#print axioms specialDenominatorSubst_cleared_inverse_noClear
#print axioms isReducedRdeSolK_of_isReducedRdeSol
#print axioms isReducedRdeSol_of_cleared_normalized
#print axioms exists_isReducedRdeSol_special_of_fractional
#print axioms cSPDEG_isSome_of_fractional_primitive
#print axioms hspde_of_fractionalBridge
#print axioms exhaustiveResidual_of_fractionalBridge

/-! ### ★ The §6.1 `K(t)`-valuation wiring (the new `hnormalize` substrate) -/

-- ★ The cleared `IsCRischDEGPolySol` identity lifts to the genuine fraction-field RDE `D Y + F·Y = G`.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
    [Algebra ℚ (CFieldSpec.K α)] (Dt fnum fden gnum gden ynum yden : CPolyG α)
    (hfden : toPolyG fden ≠ 0) (hgden : toPolyG gden ≠ 0) (hyden : toPolyG yden ≠ 0)
    (hsol : IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) :
    towerFractionFieldDerivG Dt (amG α (toPolyG ynum) / amG α (toPolyG yden))
        + amG α (toPolyG fnum) / amG α (toPolyG fden)
          * (amG α (toPolyG ynum) / amG α (toPolyG yden))
      = amG α (toPolyG gnum) / amG α (toPolyG gden) :=
  rdeFractional_of_isCRischDEGPolySol Dt fnum fden gnum gden ynum yden hfden hgden hyden hsol

#print axioms rdeFractional_of_isCRischDEGPolySol

/-! ### ★ The §6.1 `hnormalize` global assembly (Steps 1+2): weak normalization ⟹ `denom(Y) ∣ h0`

The two global steps of Bronstein Thm 6.1.2(i), wiring the proven `K(t)`-valuation substrate
(`ComputableRatFuncValuation`) to the engine. The field solution is `Y = amG(ynum)/amG(yden)` (the
`rdeFractional_of_isCRischDEGPolySol` lift). `h0` is the §6.2 clearing factor `cRdeNormalDenominatorG`
returns; `H0 := toPolyG h0` its polynomial image.

* **Step 1 (weak normalization, demonstrated)** — `ratFuncOrd_solution_nonneg_off_h0`: the proven per-prime
  RDE no-pole bound `ratFuncOrd_nonneg_of_rde_at_normal` discharges `νₚ(Y) ≥ 0` for every **normal** prime
  `p` that is not a pole of `F` nor `G`. This is exactly the regime weak normalization (Bronstein Defn 6.1.1)
  confines the relevant primes to; the residual content (the sharp count at `p ∣ h0`, and the confinement of
  `F`/`G` poles to `h0`) is bundled as the explicit honest hypothesis `IsRdeNormalPoleBounded` below.
* **Step 2 (UFM recombination, PROVEN)** — `solution_denom_dvd_h0_of_poleBounded`: from the per-prime bound
  `∀ p, −νₚ(H0) ≤ νₚ(Y)` (no pole of `Y` exceeds the order of `H0`) the divisibility `denom(Y) ∣ H0` follows
  by the `UniqueFactorizationMonoid` recombination `ratFunc_denom_dvd_of_ratFuncOrd_bound`. -/

section Hnormalize

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CharZero (CFieldSpec.K α)] [Algebra ℚ (CFieldSpec.K α)]

/-- **The fraction-field RDE solution attached to a fractional `IsCRischDEGPolySol`**
`rdeSolutionG ynum yden = amG(ynum)/amG(yden) ∈ K(t)`. The element `Y` the §6.1 valuation calculus runs on,
solving `D Y + F·Y = G` (`rdeFractional_of_isCRischDEGPolySol`) for `F = amG(fnum)/amG(fden)`,
`G = amG(gnum)/amG(gden)`, `D = towerFractionFieldDerivG Dt`. -/
noncomputable def rdeSolutionG (ynum yden : CPolyG α) : RatFunc (CFieldSpec.K α) :=
  amG α (toPolyG ynum) / amG α (toPolyG yden)

/-- **★ Step 1 (weak normalization, demonstrated): `νₚ(Y) ≥ 0` at every normal off-pole prime.** For a
fractional solution `Y = rdeSolutionG ynum yden`, a prime `p` **normal** for the monomial derivation
(`¬ p ∣ implicitDeriv (toPolyG Dt) p`) that is **not a pole** of `F = amG(fnum)/amG(fden)` (`νₚ(F) ≥ 0`) nor
of `G = amG(gnum)/amG(gden)` (`νₚ(G) ≥ 0`) has `νₚ(Y) ≥ 0` — no pole. The proven per-prime RDE bound
`ratFuncOrd_nonneg_of_rde_at_normal` applied through the `rdeFractional_of_isCRischDEGPolySol` lift; the
genuine §6.1 pole-cancellation content the global normalizer rests on. -/
theorem ratFuncOrd_solution_nonneg_off_h0
    (Dt fnum fden gnum gden ynum yden : CPolyG α)
    (hfden : toPolyG fden ≠ 0) (hgden : toPolyG gden ≠ 0) (hyden : toPolyG yden ≠ 0)
    (hsol : IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden)
    {p : (CFieldSpec.K α)[X]} (hp : Prime p)
    (hnormal : ¬ p ∣ Differential.implicitDeriv (toPolyG Dt) p)
    (hf : 0 ≤ ratFuncOrd p (amG α (toPolyG fnum) / amG α (toPolyG fden)))
    (hg : 0 ≤ ratFuncOrd p (amG α (toPolyG gnum) / amG α (toPolyG gden))) :
    0 ≤ ratFuncOrd p (rdeSolutionG ynum yden) :=
  ratFuncOrd_nonneg_of_rde_at_normal (Differential.implicitDeriv (toPolyG Dt)) hp hnormal
    (rdeFractional_of_isCRischDEGPolySol Dt fnum fden gnum gden ynum yden hfden hgden hyden hsol)
    hf hg

/-- **The per-prime normal-pole bound** `IsRdeNormalPoleBounded Dt H0 ynum yden` (Bronstein Thm 6.1.2(i),
per-prime form): the fraction-field solution `Y = rdeSolutionG ynum yden` has **no pole exceeding the order
of `H0`** — `−νₚ(H0) ≤ νₚ(Y)` for every prime `p`. The honest hypothesis carrying the residual §6.1 content
beyond the demonstrated normal-off-pole regime (`ratFuncOrd_solution_nonneg_off_h0`): the sharp pole count at
`p ∣ H0` and the weak-normalization confinement of `F`/`G` poles to `H0`. With it, the global denominator
divisibility `denom(Y) ∣ H0` is PROVEN (`solution_denom_dvd_h0_of_poleBounded`). -/
def IsRdeNormalPoleBounded (H0 ynum yden : CPolyG α) : Prop :=
  ∀ p : (CFieldSpec.K α)[X], Prime p →
    -(multiplicity p (toPolyG H0) : ℤ) ≤ ratFuncOrd p (rdeSolutionG ynum yden)

omit [CDiffField α] [CDiffFieldSpec α] [CharZero (CFieldSpec.K α)] [Algebra ℚ (CFieldSpec.K α)] in
/-- **★ Step 2 (UFM recombination, PROVEN): `denom(Y) ∣ H0`.** From the per-prime normal-pole bound
`IsRdeNormalPoleBounded` (no pole of `Y` exceeds the order of `H0 = toPolyG h0`), the denominator of the
fraction-field solution `Y` divides `H0`. The `UniqueFactorizationMonoid` prime-factor recombination
(`ratFunc_denom_dvd_of_ratFuncOrd_bound`), the global Bronstein Thm 6.1.2(i) divisibility step. -/
theorem solution_denom_dvd_h0_of_poleBounded
    (H0 ynum yden : CPolyG α) (hH0 : toPolyG H0 ≠ 0)
    (hbound : IsRdeNormalPoleBounded H0 ynum yden) :
    (rdeSolutionG ynum yden).denom ∣ toPolyG H0 :=
  ratFunc_denom_dvd_of_ratFuncOrd_bound hH0 hbound

omit [CDiffField α] [CDiffFieldSpec α] [CharZero (CFieldSpec.K α)] [Algebra ℚ (CFieldSpec.K α)] in
/-- `toPolyG (CField.zero :: c) = X · toPolyG c`: prepending the engine zero shifts by `X` (Horner step
with leading coefficient `toK 0 = 0`). The brick of `toPolyG`'s monomial preimage. -/
theorem toPolyG_zero_cons (c : CPolyG α) :
    toPolyG (CField.zero :: c) = X * toPolyG c := by
  rw [toPolyG_cons, CFieldSpec.toK_zero, map_zero, zero_add]

omit [CDiffField α] [CDiffFieldSpec α] [CharZero (CFieldSpec.K α)] [Algebra ℚ (CFieldSpec.K α)] in
/-- **`toPolyG` is surjective when `toK` is** (`toPolyG_surjective_of_toK_surjective`): if the coefficient
bridge `toK : α → CFieldSpec.K α` is surjective then every `q : (CFieldSpec.K α)[X]` is `toPolyG` of some
`CPolyG α`. True at every tower carrier (`toK` is surjective onto `RatFunc` at each level, fractions kept
unreduced); the honest engine-realization hypothesis that pulls the abstract `K[X]` normalized solution back
to a `CPolyG`. Proof by `Polynomial.induction_on'`: additive closure (`toPolyG_caddG`) plus the monomial
case `monomial n a = X^n · C a` built as `replicate n 0 ++ [a₀]` with `a = toK a₀`. -/
theorem toPolyG_surjective_of_toK_surjective
    (hsurj : Function.Surjective (CFieldSpec.toK : α → CFieldSpec.K α)) :
    Function.Surjective (toPolyG : CPolyG α → (CFieldSpec.K α)[X]) := by
  intro q
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
    obtain ⟨cp, hcp⟩ := hp
    obtain ⟨cr, hcr⟩ := hr
    exact ⟨caddG cp cr, by rw [toPolyG_caddG, hcp, hcr]⟩
  | monomial n a =>
    obtain ⟨a₀, ha₀⟩ := hsurj a
    refine ⟨List.replicate n CField.zero ++ [a₀], ?_⟩
    induction n with
    | zero => simp [toPolyG_cons, ha₀, ← C_mul_X_pow_eq_monomial]
    | succ k ih =>
      rw [List.replicate_succ, List.cons_append, toPolyG_zero_cons, ih, X_mul_monomial]

omit [CharZero (CFieldSpec.K α)] in
/-- **★ The reverse cleared-identity bridge** (`isCRischDEGPolySol_of_field_rde`): the converse of
`rdeFractional_of_isCRischDEGPolySol`. If `Y = amG(Q)/amG(h0)` solves the fraction-field RDE
`D Y + F·Y = G` (with `D = towerFractionFieldDerivG Dt`, `F = amG(fnum)/amG(fden)`,
`G = amG(gnum)/amG(gden)`) and the denominators `fden, gden, h0` are nonzero, then the cleared **polynomial**
identity `IsCRischDEGPolySol Dt fnum fden gnum gden Q h0` holds. Expands `D` by the quotient rule
(`towerFractionFieldDerivG_div`), clears all denominators (nonzero), and folds the field identity back onto
`amG` of the `IsCRischDEGPolySol` polynomial identity (`amG` injective). The wiring that turns the §6.1
field-level normalized solution into the engine's polynomial-solution predicate. -/
theorem isCRischDEGPolySol_of_field_rde
    (Dt fnum fden gnum gden Q h0 : CPolyG α)
    (hfden : toPolyG fden ≠ 0) (hgden : toPolyG gden ≠ 0) (hh0 : toPolyG h0 ≠ 0)
    (hrde : towerFractionFieldDerivG Dt (amG α (toPolyG Q) / amG α (toPolyG h0))
        + amG α (toPolyG fnum) / amG α (toPolyG fden)
          * (amG α (toPolyG Q) / amG α (toPolyG h0))
      = amG α (toPolyG gnum) / amG α (toPolyG gden)) :
    IsCRischDEGPolySol Dt fnum fden gnum gden Q h0 := by
  have hFDne : amG α (toPolyG fden) ≠ 0 := amG_toPolyG_ne_zero hfden
  have hGDne : amG α (toPolyG gden) ≠ 0 := amG_toPolyG_ne_zero hgden
  have hH0ne : amG α (toPolyG h0) ≠ 0 := amG_toPolyG_ne_zero hh0
  -- expand the derivative via the quotient rule, then clear all denominators into one field identity.
  rw [towerFractionFieldDerivG_div, div_mul_div_comm] at hrde
  field_simp at hrde
  -- the cleared identity is `amG` of the `IsCRischDEGPolySol` polynomial identity; `amG` is injective.
  unfold IsCRischDEGPolySol
  apply (RatFunc.algebraMap_injective (CFieldSpec.K α))
  simp only [map_add, map_mul, map_sub, map_pow]
  ring_nf
  ring_nf at hrde
  linear_combination hrde

omit [CharZero (CFieldSpec.K α)] in
/-- **★ The §6.1 field-level `hnormalize`** (`exists_isCRischDEGPolySol_h0_of_poleBounded`): the FULL
Bronstein Thm 6.1.2(i) conclusion, modulo the honest per-prime pole bound `IsRdeNormalPoleBounded` and the
honest engine-realization `toK`-surjectivity. From a fractional solution `IsCRischDEGPolySol … ynum yden`
whose fraction-field reading `Y = amG(ynum)/amG(yden)` has no pole exceeding the order of `h0`, there is a
`CPolyG` `Q` with `IsCRischDEGPolySol Dt fnum fden gnum gden Q h0` — i.e. one whose denominator is exactly
the §6.2 clearing factor `h0` (`Q = Y·h0 ∈ K[X]` is a polynomial). Assembles Step 2 (`denom(Y) ∣ h0`,
`solution_denom_dvd_h0_of_poleBounded`) → `RatFunc.denom_dvd` (`Y = amG(Q')/amG(h0)`, `Q' : K[X]`) →
`toPolyG`-surjectivity (pull `Q'` back to a `CPolyG`) → the reverse cleared-identity bridge
(`isCRischDEGPolySol_of_field_rde`). This is the deep `hnormalize` clause, derived (no `sorry`) from the
proven `K(t)`-valuation substrate plus two precisely-isolated honest hypotheses. -/
theorem exists_isCRischDEGPolySol_h0_of_poleBounded
    (Dt fnum fden gnum gden ynum yden h0 : CPolyG α)
    (hfden : toPolyG fden ≠ 0) (hgden : toPolyG gden ≠ 0) (hyden : toPolyG yden ≠ 0)
    (hh0 : toPolyG h0 ≠ 0)
    (hsurj : Function.Surjective (CFieldSpec.toK : α → CFieldSpec.K α))
    (hsol : IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden)
    (hbound : IsRdeNormalPoleBounded h0 ynum yden) :
    ∃ Q : CPolyG α, IsCRischDEGPolySol Dt fnum fden gnum gden Q h0 := by
  -- Step 2: the denominator of the fraction-field solution divides `h0`.
  have hdvd : (rdeSolutionG ynum yden).denom ∣ toPolyG h0 :=
    solution_denom_dvd_h0_of_poleBounded h0 ynum yden hh0 hbound
  -- so `Y = amG(Q')/amG(h0)` for some polynomial `Q' : K[X]` (`RatFunc.denom_dvd`).
  obtain ⟨Q', hQ'⟩ := (RatFunc.denom_dvd hh0).mp hdvd
  -- pull `Q'` back to a `CPolyG` via `toK`-surjectivity.
  obtain ⟨Q, hQ⟩ := toPolyG_surjective_of_toK_surjective hsurj Q'
  refine ⟨Q, ?_⟩
  -- the fraction-field RDE solved by `Y`, re-expressed as `amG(Q)/amG(h0)`.
  have hYrde := rdeFractional_of_isCRischDEGPolySol Dt fnum fden gnum gden ynum yden
    hfden hgden hyden hsol
  rw [show amG α (toPolyG ynum) / amG α (toPolyG yden) = rdeSolutionG ynum yden from rfl, hQ',
    ← hQ] at hYrde
  exact isCRischDEGPolySol_of_field_rde Dt fnum fden gnum gden Q h0 hfden hgden hh0 hYrde

end Hnormalize

/-! ### ★ Closing the `hnormalize` field of `RdeFractionalToReducedResidual`

The `hnormalize` field is no longer a bald assumption: `hnormalize_of_poleBounded` DERIVES it (Bronstein
Thm 6.1.2(i), `∃ Q, IsCRischDEGPolySol … Q h0`) from the proven §6.1 `K(t)`-valuation assembly
(`exists_isCRischDEGPolySol_h0_of_poleBounded`) and three precisely-isolated honest hypotheses, each
engine-provable / a faithful side condition:
* `hsurj` — `toK`-surjectivity (the engine realization; true at every tower carrier, fractions unreduced);
* `hden` — `fden, gden ≠ 0` and `h0 ≠ 0` at the `cRdeNormalDenominatorG` output (the §6.2 setup nonzeros,
  the same facts `hcerts` bundles);
* `hpole` — the per-prime normal-pole bound `IsRdeNormalPoleBounded` (Bronstein Thm 6.1.2(i) per-prime form:
  the solution's poles are confined to `h0` with the sharp order count) — the genuine deep §6.1 content,
  whose normal-off-pole regime is *already discharged* by the proven `ratFuncOrd_solution_nonneg_off_h0`. -/

section HnormalizeField

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCore α]
  [CharZero (CFieldSpec.K α)] [Algebra ℚ (CFieldSpec.K α)]

omit [CharZero (CFieldSpec.K α)] in
/-- **★ The derived `hnormalize` field** (`hnormalize_of_poleBounded`): the exact `hnormalize` clause of
`RdeFractionalToReducedResidual` — `(∃ ynum yden, IsCRischDEGPolySol …) → ∀ a0 b0 c0 h0,
cRdeNormalDenominatorG … = some (a0,b0,c0,h0) → ∃ Q, IsCRischDEGPolySol … Q h0` — produced from the proven
§6.1 valuation assembly plus the honest engine-realization (`hsurj`), nonzero (`hden`), and per-prime
normal-pole-bound (`hpole`) hypotheses. Closes the single deep clause of the fractional→reduced bridge,
reducing `RdeFractionalToReducedResidual` to `hcerts` (engine-provable) + these three honest inputs. -/
theorem hnormalize_of_poleBounded
    (Dt fnum fden gnum gden : CPolyG α)
    (hsurj : Function.Surjective (CFieldSpec.toK : α → CFieldSpec.K α))
    (hden : ∀ a0 b0 c0 h0 : CPolyG α,
      cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden = some (a0, b0, c0, h0) →
        toPolyG fden ≠ 0 ∧ toPolyG gden ≠ 0 ∧ toPolyG h0 ≠ 0)
    (hpole : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      ∀ a0 b0 c0 h0 : CPolyG α,
        cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden = some (a0, b0, c0, h0) →
          ∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden
            ∧ toPolyG yden ≠ 0 ∧ IsRdeNormalPoleBounded h0 ynum yden) :
    (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
      ∀ a0 b0 c0 h0 : CPolyG α,
        cRdeNormalDenominatorG Dt towerRischDEFuel fnum fden gnum gden = some (a0, b0, c0, h0) →
        ∃ Q : CPolyG α, IsCRischDEGPolySol Dt fnum fden gnum gden Q h0 := by
  intro hex a0 b0 c0 h0 hnorm
  obtain ⟨hfden, hgden, hh0⟩ := hden a0 b0 c0 h0 hnorm
  obtain ⟨ynum, yden, hsol, hyden, hbound⟩ := hpole hex a0 b0 c0 h0 hnorm
  exact exists_isCRischDEGPolySol_h0_of_poleBounded Dt fnum fden gnum gden ynum yden h0
    hfden hgden hyden hh0 hsurj hsol hbound

end HnormalizeField

/-! ### Restatements of the §6.1 `hnormalize` global assembly (anonymous `example`s) -/

-- ★ Step 1 (demonstrated): the proven per-prime bound gives `νₚ(Y) ≥ 0` at a normal off-pole prime.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CharZero (CFieldSpec.K α)] [Algebra ℚ (CFieldSpec.K α)]
    (Dt fnum fden gnum gden ynum yden : CPolyG α)
    (hfden : toPolyG fden ≠ 0) (hgden : toPolyG gden ≠ 0) (hyden : toPolyG yden ≠ 0)
    (hsol : IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden)
    {p : (CFieldSpec.K α)[X]} (hp : Prime p)
    (hnormal : ¬ p ∣ Differential.implicitDeriv (toPolyG Dt) p)
    (hf : 0 ≤ ratFuncOrd p (amG α (toPolyG fnum) / amG α (toPolyG fden)))
    (hg : 0 ≤ ratFuncOrd p (amG α (toPolyG gnum) / amG α (toPolyG gden))) :
    0 ≤ ratFuncOrd p (rdeSolutionG ynum yden) :=
  ratFuncOrd_solution_nonneg_off_h0 Dt fnum fden gnum gden ynum yden hfden hgden hyden hsol hp
    hnormal hf hg

-- ★ Step 2 (PROVEN): the per-prime pole bound forces the denominator to divide `h0`.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CharZero (CFieldSpec.K α)] [Algebra ℚ (CFieldSpec.K α)]
    (H0 ynum yden : CPolyG α) (hH0 : toPolyG H0 ≠ 0)
    (hbound : IsRdeNormalPoleBounded H0 ynum yden) :
    (rdeSolutionG ynum yden).denom ∣ toPolyG H0 :=
  solution_denom_dvd_h0_of_poleBounded H0 ynum yden hH0 hbound

-- ★ The field-level `hnormalize`: a pole-bounded fractional solution yields `∃ Q, IsCRischDEGPolySol … Q h0`.
example {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CharZero (CFieldSpec.K α)] [Algebra ℚ (CFieldSpec.K α)]
    (Dt fnum fden gnum gden ynum yden h0 : CPolyG α)
    (hfden : toPolyG fden ≠ 0) (hgden : toPolyG gden ≠ 0) (hyden : toPolyG yden ≠ 0)
    (hh0 : toPolyG h0 ≠ 0)
    (hsurj : Function.Surjective (CFieldSpec.toK : α → CFieldSpec.K α))
    (hsol : IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden)
    (hbound : IsRdeNormalPoleBounded h0 ynum yden) :
    ∃ Q : CPolyG α, IsCRischDEGPolySol Dt fnum fden gnum gden Q h0 :=
  exists_isCRischDEGPolySol_h0_of_poleBounded Dt fnum fden gnum gden ynum yden h0
    hfden hgden hyden hh0 hsurj hsol hbound

#print axioms ratFunc_denom_dvd_of_ratFuncOrd_bound
#print axioms toPolyG_surjective_of_toK_surjective
#print axioms isCRischDEGPolySol_of_field_rde
#print axioms exists_isCRischDEGPolySol_h0_of_poleBounded
#print axioms hnormalize_of_poleBounded

end DeepWiki.SymbolicIntegration
