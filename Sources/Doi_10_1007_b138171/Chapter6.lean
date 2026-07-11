import DeepWiki.SymbolicIntegration.Engine.Tower.RischDE
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEInstance
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDEWellFounded
import DeepWiki.SymbolicIntegration.Engine.Tower.Integrate
import DeepWiki.SymbolicIntegration.Engine.CanonicalRepresentationDense
import Sources.Doi_10_1007_b138171.Source

/-! # Symbolic Integration catalog — Chapter 6: The Risch Differential Equation
Solving `Dy + f·y = g` for `y` in a monomial extension — the engine of the exponential case of the
integration algorithm. The **whole RDE pipeline** is now rendered as a **computable** solver over the
monomial tower ℚ(x)[t]: weak normalizer + normal denominator (§6.1/§6.2), special denominator (§6.2),
degree bound (§6.3), SPDE (§6.4), the non-cancellation case (§6.5) and the primitive + hyperexponential
cancellation cases (§6.6), assembled into the full fuel-free `cRischDE` and validated end-to-end on
Examples 6.5.1 / 6.4.1.

**Computable-vs-abstract.** Each stage below is a computable function validated by `native_decide` on the
book's worked example (matching the book's intermediate values, or checking that the returned `y`
*actually solves* the equation via the cleared polynomial identity); the *abstract* correctness theorems
(the `Dy + fy = g ↔ a·Dq + b·q = c` equivalence, Thm 6.4.1, etc.) are **NOT** proved. The §6.6
hypertangent cancellation case (`PolyRischDECancelTan`, needs the Ch. 8 coupled system) and the full
§5.12/§7.3 parametric-logarithmic-derivative recognizer remain deferred.

**Carrier: the generic ℚ(x).** The whole pipeline is aliased to the canonical **generic** engine at
`α = DenseFrac ℚ` (the recursive `Frac(ℚ[x])`, every instance bottoming at ℚ with no hand-built piece). The
leading-coefficient base solve of the §6.6 cancellation cases is the **generic**
`CRischField.crischDESolve` over `DenseFrac ℚ` (the recursive tower oracle, every instance bottoming at ℚ).

## NOT YET FORMALIZED (audit 2026-06-24)
§6.1 The Normal Part of the Denominator: Def 6.1.1; Thm 6.1.2; Cor 6.1.1; Lemma 6.1.1; Ex 6.1.1
  (abstract correctness; the algorithms `WeakNormalizer` + `RdeNormalDenominator` are now computable +
  native_decide-validated on Ex 6.1.2, see `alg_6_1_weakNormalizer`/`alg_6_2_normalDenominator`/
  `ex_6_1_2`).
§6.2 The Special Part of the Denominator: Lemma 6.2.1, Lemma 6.2.2, Lemma 6.2.4; Ex 6.2.1 (abstract
  correctness; `RdeSpecialDenominator` is now computable + native_decide-validated on Ex 6.2.2, see
  `alg_6_2_specialDenominator`/`ex_6_2_2`).
§6.3 Degree Bounds: Cor 6.3.1; Lemma 6.3.1, Lemma 6.3.2, Lemma 6.3.3, Lemma 6.3.4, Lemma 6.3.5;
  Ex 6.3.1, Ex 6.3.2, Ex 6.3.3 (abstract correctness; `RdeBoundDegree` is now computable +
  native_decide-validated on Ex 6.3.4, see `alg_6_3_boundDegree`/`ex_6_3_4`).
§6.4 The SPDE Algorithm: Thm 6.4.1 (abstract correctness; the algorithm `SPDE` is now computable, see
  `alg_6_4_spde`, and exercised through the full-solver no-solution run `ex_6_4_1`).
§6.5 The Non-Cancellation Cases: Lemma 6.5.1; Ex 6.5.2, Ex 6.5.3 (abstract correctness; the algorithm
  `PolyDESolve`/`PolyRischDENoCancel` is now computable + native_decide-validated end-to-end on Ex
  6.5.1, see `alg_6_5_polyRischDENoCancel`/`ex_6_5_1`).
§6.6 The Cancellation Cases: Ex 6.6.1; the **hypertangent** cancellation solver `PolyRischDECancelTan`
  (`δ = 2`, recurses to a base RDE over `k(√−1)` / a Ch. 8 `CoupledDESystem`) — the **primitive**
  (`PolyRischDECancelPrim`) and **hyperexponential** (`PolyRischDECancelExp`) cancellation solvers are
  now computable + native_decide-validated (see `alg_6_6_cancelPrim`/`alg_6_6_cancelExp`/
  `ex_6_6_cancelPrim`/`ex_6_6_cancelExp`).
Exercise 6.1.

The remaining gaps are the **abstract correctness theorems** (the pipeline is computationally rendered
and example-validated but not proved correct), the §6.6 hypertangent cancellation case (the Ch. 8
coupled-system layer), the full §5.12/§7.3 logarithmic-derivative-of-a-radical recognizer (the
`CFrac.parametricLogDeriv` constant stub decides only the reachable obstruction), and the cancellation
refinements of `RdeSpecialDenominator`/`RdeBoundDegree` (which only *raise* the bound in that case). -/

open DeepWiki.SymbolicIntegration DeepWiki.SymbolicIntegration.DensePoly

namespace DeepWiki.Si

/-! ### Generic-carrier input builders (catalog-local)

The §6 smoke examples over the generic ℚ(x) = `DenseFrac ℚ` carrier read their ℚ(x) coefficients as
num/den lists over `DensePoly ℚ = List ℚ`. `CFrac.ofScalar` embeds constants, while
`CFrac.ofFraction` packages an arbitrary numerator and denominator. This is catalog infrastructure,
not a book item. -/

/-- The variable `x ∈ ℚ(x)` as `DenseFrac ℚ` (numerator `[0,1]`, denominator `[1]`). -/
def qX6 : DenseFrac ℚ := CFrac.ofFraction [0, 1] [1] (by cfrac_nonzero)

/-- **Cleared Risch-DE identity check over the generic ℚ(x)[t]** (the `DenseFrac ℚ` mirror of the engine's
`rdeClearedCheck`): `true` iff `y = ynum/yden` solves `Dy + (fnum/fden)·y = gnum/gden`, verified as the
polynomial identity obtained by clearing all denominators (`Dy = (D(ynum)·yden − ynum·D(yden))/yden²`):
`gden·fden·(D(ynum)·yden − ynum·D(yden)) + gden·fnum·ynum·yden = gnum·fden·yden²`, decided by `cisZero`
of the cleared difference (`D = CPolyEngine.monomialDeriv Dt`). -/
def rdeClearedCheckG6 (Dt fnum fden gnum gden ynum yden : DensePoly (DenseFrac ℚ)) : Bool :=
  let Dyn := CPolyEngine.monomialDeriv Dt ynum
  let Dyd := CPolyEngine.monomialDeriv Dt yden
  let lhs := DensePoly.cadd
    (DensePoly.cmul (DensePoly.cmul gden fden) (DensePoly.csub (DensePoly.cmul Dyn yden) (DensePoly.cmul ynum Dyd)))
    (DensePoly.cmul (DensePoly.cmul (DensePoly.cmul gden fnum) ynum) yden)
  let rhs := DensePoly.cmul (DensePoly.cmul gnum fden) (DensePoly.cmul yden yden)
  DensePoly.cisZero (DensePoly.csub lhs rhs)

/-! ## §6.1 The Normal Part of the Denominator — computable + validated -/

/-- **Algorithm `WeakNormalizer`** (§6.1, p.183): the fuel-free computable
`cWeakNormalizer Dt fnum fden = q ∈ k[t]` (the generic engine at the generic ℚ(x) = `DenseFrac ℚ`)
over the tower, returning `q` such that `f − Dq/q` is weakly normalized (via the residue resultant and
its positive integer roots). Computable + `native_decide`-validated; abstract correctness deferred. -/
noncomputable abbrev alg_6_1_weakNormalizer := cWeakNormalizer (α := DenseFrac ℚ)

/-- **Algorithm `RdeNormalDenominator`** (§6.2 eq. 6.2 / Cor 6.1.1, p.185): the fuel-free computable
`cRdeNormalDenominator Dt fnum fden gnum gden` (the generic engine at `DenseFrac ℚ`) over the tower,
returning `none` (no solution) or the reduction quadruplet `(a, b, c, h)` reducing `Dy + f·y = g` to the
simple-part equation `a·Dq + b·q = c` with `q = y·h`. Computable + `native_decide`-validated; abstract
correctness deferred. -/
noncomputable abbrev alg_6_2_normalDenominator := cRdeNormalDenominator (α := DenseFrac ℚ)

/-- **Example 6.1.2** (§6.1/§6.2, p.183/185/186): for `Dy + (t²+1)y = 1/t²` (`t = tan x`, `Dt = 1+t²`),
`cWeakNormalizer` returns `q = 1` (already weakly normalized) and `cRdeNormalDenominator` returns the
book's quadruplet `(a, b, c, h) = (t, (t−1)(t²+1), 1, t)`, pinned componentwise over the generic ℚ(x)[t]
(`native_decide`). -/
theorem ex_6_1_2 :
    (let Dt : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1, CFrac.ofScalar 0, CFrac.ofScalar 1]              -- `Dt = t²+1`
     let fnum : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1, CFrac.ofScalar 0, CFrac.ofScalar 1]            -- `f = t²+1`
     let fden : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1]
     let gnum : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1]                                -- `g = 1/t²`
     let gden : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 0, CFrac.ofScalar 0, CFrac.ofScalar 1]
     let exA : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 0, CFrac.ofScalar 1]                       -- `a = t`
     let exB : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar (-1), CFrac.ofScalar 1, CFrac.ofScalar (-1), CFrac.ofScalar 1]  -- `(t−1)(t²+1)`
     let exC : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1]                                 -- `c = 1`
     let exH : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 0, CFrac.ofScalar 1]                       -- `h = t`
     DensePoly.cisZero (DensePoly.csub (DensePoly.cWeakNormalizer Dt fnum fden) [CCommRing.one])
     ∧ (match DensePoly.cRdeNormalDenominator Dt fnum fden gnum gden with
        | some (a, b, c, h) =>
            DensePoly.cisZero (DensePoly.csub a exA)
              && DensePoly.cisZero (DensePoly.csub b exB)
              && DensePoly.cisZero (DensePoly.csub c exC)
              && DensePoly.cisZero (DensePoly.csub h exH)
        | none => false) = true) := by native_decide

/-! ## §6.2 The Special Part of the Denominator — computable + validated -/

/-- **Algorithm `RdeSpecialDenominator`** (§6.2, the `RdeSpecialDenom{Exp,Tan}` boxes, p.190/192): the
fuel-free computable `cRdeSpecialDenominator Dt a b c` (the generic engine at `DenseFrac ℚ`) over the tower,
reducing the simple-part equation `a·Dq + b·q = c` to a polynomial equation over `k[t]` by clearing the
special factor `p` (the substitution `q = h·pⁿ`). Computable + `native_decide`-validated; abstract
correctness deferred. -/
noncomputable abbrev alg_6_2_specialDenominator := cRdeSpecialDenominator (α := DenseFrac ℚ)

/-- **Example 6.2.2** (§6.2, the `RdeSpecialDenomTan` box, p.192): continuing Ex 6.1.2,
`cRdeSpecialDenominator` on `(a, b, c) = (t, (t−1)(t²+1), 1)` (special irreducible `p = t²+1`,
`n_b = 1`, `n_c = 0`, `n = N = 0`) returns the *unchanged* `(t, (t−1)(t²+1), 1, 1)` over the generic
ℚ(x)[t] (`native_decide`). -/
theorem ex_6_2_2 :
    (let Dt : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1, CFrac.ofScalar 0, CFrac.ofScalar 1]
     let exA : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 0, CFrac.ofScalar 1]                       -- `a = t`
     let exB : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar (-1), CFrac.ofScalar 1, CFrac.ofScalar (-1), CFrac.ofScalar 1]  -- `(t−1)(t²+1)`
     let exC : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1]                                 -- `c = 1`
     match DensePoly.cRdeSpecialDenominator Dt exA exB exC with
     | (abar, bbar, cbar, h) =>
         DensePoly.cisZero (DensePoly.csub abar exA)
           && DensePoly.cisZero (DensePoly.csub bbar exB)
           && DensePoly.cisZero (DensePoly.csub cbar exC)
           && DensePoly.cisZero (DensePoly.csub h [CCommRing.one])) = true := by native_decide

/-! ## §6.3 Degree Bounds — computable + validated -/

/-- **Algorithm `RdeBoundDegree`** (§6.3, the `RdeBoundDegree{Base,Prim,Exp,NonLinear}` boxes,
p.198–201): the computable `cRdeBoundDegree Dt a b c = n ∈ ℕ` (the generic engine at `DenseFrac ℚ`)
over the tower, an explicit upper bound on `deg_t(q)` for any polynomial solution `q` of
`a·Dq + b·q = c`, case-split by `δ = deg(Dt)`. Computable + `native_decide`-validated; abstract
correctness deferred. -/
noncomputable abbrev alg_6_3_boundDegree
    (Dt a b c : DensePoly (DenseFrac ℚ)) : ℕ :=
  cRdeBoundDegree (P := List) (α := DenseFrac ℚ) Dt a b c

/-- **Example 6.3.4** (§6.3, the `RdeBoundDegreeNonLinear` box, p.202): continuing Ex 6.1.2/6.2.2,
`cRdeBoundDegree` on `(a, b, c) = (t, (t−1)(t²+1), 1)` with `δ = 2` returns the degree bound `0`
(any polynomial solution lies in ℚ(x)) over the generic ℚ(x)[t], `native_decide`. -/
theorem ex_6_3_4 :
    (let Dt : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1, CFrac.ofScalar 0, CFrac.ofScalar 1]
     let exA : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 0, CFrac.ofScalar 1]
     let exB : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar (-1), CFrac.ofScalar 1, CFrac.ofScalar (-1), CFrac.ofScalar 1]
     let exC : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1]
     DensePoly.cRdeBoundDegree Dt exA exB exC) = 0 := by native_decide

/-! ## §6.4 The SPDE Algorithm — computable -/

/-- **Algorithm `SPDE`** (§6.4, Rothstein's `SPDE(a, b, c, D, n)` box, p.203): the fuel-free computable
`cSPDE Dt a b c n` (the generic engine at `DenseFrac ℚ`) over the tower — the recursive
`gcd(a, b)`-peeling reduction of the degree-bounded `a·Dq + b·q = c` to one with `a = 1`. Returns
`none` ("no solution of degree ≤ n") or `(b̄, c̄, m, α, β)`. Computable (exercised through the
full-solver no-solution run `ex_6_4_1`); abstract correctness (Thm 6.4.1) deferred. -/
noncomputable abbrev alg_6_4_spde := cSPDE (α := DenseFrac ℚ)

/-! ## §6.5 The Non-Cancellation Cases — computable + validated -/

/-- **Algorithm `PolyRischDENoCancel`** (§6.5, the `PolyRischDENoCancel1(b, c, D, n)` box, p.208): the
fuel-free computable `cPolyRischDENoCancel Dt b c n` (the generic engine at `DenseFrac ℚ`) over the tower — the
non-cancellation case solving `Dq + b·q = c` degree-by-degree from the top down
(`lc(c) = lc(b)·lc(q)`). Returns `Option (DensePoly (DenseFrac ℚ))`. Computable +
`native_decide`-validated end-to-end; abstract correctness deferred. -/
noncomputable abbrev alg_6_5_polyRischDENoCancel := cPolyRischDENoCancel (α := DenseFrac ℚ)

/-- **Algorithm `PolyRischDE`** (§6.5/§6.6 dispatcher): the fuel-free computable `cPolyRischDE Dt b c n`
(the generic engine at `DenseFrac ℚ`) routing `Dq + b·q = c` to the non-cancellation solver or the
primitive/hyperexponential cancellation solvers by monomial type and `deg(b)` (Lemma 6.5.1). -/
noncomputable abbrev alg_6_5_polyRischDE := cPolyRischDE (α := DenseFrac ℚ)

/-- **The full Risch DE solver**: the fuel-free computable `cRischDE Dt fnum fden gnum gden` (the
canonical generic engine, here at the generic ℚ(x) = `DenseFrac ℚ`) over the tower, chaining normal
denominator (§6.2) → special denominator (§6.2) → degree bound (§6.3) → SPDE (§6.4) → PolyRischDE
(§6.5/§6.6), reconstructing `y` solving `Dy + f·y = g`, or `none`. The generic mirror has its own
cleared-identity correctness layer; validated end-to-end on Ex 6.5.1 / 6.4.1. -/
noncomputable abbrev alg_6_rischDE := cRischDE (α := DenseFrac ℚ)

/-- **Example 6.5.1** (§6.5, p.208): the full `cRischDE` solves
`Dy + (t²+1)y = t³+(x+1)t²+t+(x+2)` (`t = tan x`) end-to-end, returning `y = t + x`, verified to
*actually solve* the equation by the cleared polynomial identity over the generic ℚ(x)[t]
(`native_decide`). -/
theorem ex_6_5_1 :
    (let Dt : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1, CFrac.ofScalar 0, CFrac.ofScalar 1]              -- `Dt = t²+1`
     let fnum : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1, CFrac.ofScalar 0, CFrac.ofScalar 1]            -- `f = t²+1`
     let fden : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1]
     -- `g = t³ + (x+1)t² + t + (x+2)` (low→high in `t`)
     let gnum : DensePoly (DenseFrac ℚ) :=
       [CCommRing.add qX6 (CFrac.ofScalar 2), CFrac.ofScalar 1, CCommRing.add qX6 (CFrac.ofScalar 1), CFrac.ofScalar 1]
     match DensePoly.cRischDE Dt fnum fden gnum fden with
     | some (ynum, yden) => rdeClearedCheckG6 Dt fnum fden gnum fden ynum yden
     | none => false) = true := by native_decide

/-- **Example 6.4.1** (§6.4, p.204): the full `cRischDE` on `Dy + (t²+1)y = 1/t²` (`t = tan x`) returns
`none` — `SPDE` reaches `n = −1 < 0` with `c ≠ 0`, so `∫ e^{tan x}/tan²x dx` is not elementary over the
generic ℚ(x)[t] (`native_decide`). -/
theorem ex_6_4_1 :
    (let Dt : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1, CFrac.ofScalar 0, CFrac.ofScalar 1]
     let fnum : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1, CFrac.ofScalar 0, CFrac.ofScalar 1]
     let fden : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1]
     let gnum : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1]
     let gden : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 0, CFrac.ofScalar 0, CFrac.ofScalar 1]            -- `1/t²`
     DensePoly.cRischDE Dt fnum fden gnum gden).isNone = true := by native_decide

/-! ## §6.6 The Cancellation Cases — primitive + hyperexponential computable + validated -/

/-- **Algorithm `PolyRischDECancelPrim`** (§6.6, p.212): the fuel-free computable
`cPolyRischDECancelPrim Dt b c n` (the generic engine at `DenseFrac ℚ`) over the tower — the
primitive cancellation case (`Dt ∈ k`, `b ∈ k*`, where `cPolyRischDENoCancel` cannot proceed),
recursing degree-by-degree into the eq. 6.23 base Risch DE over `k = ℚ(x)` after the §5.12 `b = Dz/z`
test. Returns `Option (DensePoly (DenseFrac ℚ))`. Computable + `native_decide`-validated; abstract
correctness deferred. -/
noncomputable abbrev alg_6_6_cancelPrim := cPolyRischDECancelPrim (α := DenseFrac ℚ)

/-- **Algorithm `PolyRischDECancelExp`** (§6.6, p.213): the fuel-free computable
`cPolyRischDECancelExp Dt b c n` (the generic engine at `DenseFrac ℚ`) over the tower — the
hyperexponential cancellation case (`Dt/t = η ∈ k`, `δ = 1`, `b ∈ k*`), recursing degree-by-degree into
the eq. 6.24 base RDE `RischDE(b + m·η, lc(c))` over ℚ(x). Returns `Option (DensePoly (DenseFrac ℚ))`.
Computable + `native_decide`-validated; abstract correctness deferred. -/
noncomputable abbrev alg_6_6_cancelExp := cPolyRischDECancelExp (α := DenseFrac ℚ)

/-- **The base Risch DE over ℚ(x)** (§6.6 eq. 6.23): the generic tower base solve
`CRischField.crischDESolve (α := DenseFrac ℚ) f g = Option (DenseFrac ℚ)` solving `Ds + f·s = g` over
`k = ℚ(x)` (`D = d/dx`) — the leading-coefficient recursion target of the cancellation cases. The
recursive `CRischField (DenseFrac ℚ)` instance runs the generic §6 pipeline over `ℚ[x]` and bottoms at the
`CRischField ℚ` constant solve. -/
noncomputable abbrev alg_6_6_rischDEBase := @CRischField.crischDESolve (DenseFrac ℚ) _ _

/-- **The rational Risch DE over ℚ(x)** (§6.6 eq. 6.23 base solve): the generic tower base solve
`CRischField.crischDESolve (α := DenseFrac ℚ)` — the whole Ch. 6 pipeline re-run at the base level over
`DensePoly ℚ = ℚ[x]` (the recursive `instCRischFieldCFrac`, bottoming at `CRischField ℚ`). The generic
`DenseFrac ℚ` carrier needs no special-cased `cRationalRDE`: the rational base solve *is* `crischDESolve`
at this level. Computable + `native_decide`-validated (`ex_6_6_rationalRDE`). -/
noncomputable abbrev alg_6_6_rationalRDE := @CRischField.crischDESolve (DenseFrac ℚ) _ _

/-- **Example (§6.6, p.212)**, primitive cancellation: `cPolyRischDECancelPrim` on
`Dq + 1·q = log(x) + 1/x` (`t = log x`, `b = 1 ∈ ℚ*`) solves to `q = log(x) = t`, verified to *actually
solve* `Dq + b·q = c` by the cleared difference over the generic ℚ(x)[t] (`native_decide`); the
dispatcher `cPolyRischDE` routes the same input to the cancellation solver. -/
theorem ex_6_6_cancelPrim :
    (let Dt : DensePoly (DenseFrac ℚ) := [CFrac.ofFraction [1] [0, 1] (by cfrac_nonzero)]                          -- `Dt = 1/x`
     let b : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1]                                   -- `b = 1`
     let c : DensePoly (DenseFrac ℚ) := [CFrac.ofFraction [1] [0, 1] (by cfrac_nonzero), CFrac.ofScalar 1]                 -- `c = t + 1/x`
     (match DensePoly.cPolyRischDECancelPrim Dt b c 5 with
       | some q =>
           DensePoly.cisZero (DensePoly.csub
             (DensePoly.cadd (CPolyEngine.monomialDeriv Dt q) (DensePoly.cmul b q)) c)
       | none => false)
     && (match DensePoly.cPolyRischDE Dt b c 5, DensePoly.cPolyRischDECancelPrim Dt b c 5 with
         | some q1, some q2 => DensePoly.cisZero (DensePoly.csub q1 q2)
         | _, _ => false)) = true := by native_decide

/-- **Example (§6.6, p.213)**, hyperexponential cancellation: `cPolyRischDECancelExp` on
`Dq + (1/x)·q = (2+x)·exp(x)` (`t = exp x`, `η = 1`, `b = 1/x`) solves to `q = x·exp(x) = x·t`, verified
to *actually solve* `Dq + b·q = c` by the cleared difference over the generic ℚ(x)[t] (`native_decide`);
the dispatcher `cPolyRischDE` routes the same input to the hyperexponential cancellation solver. -/
theorem ex_6_6_cancelExp :
    (let Dt : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 0, CFrac.ofScalar 1]                        -- `Dt = t`
     let b : DensePoly (DenseFrac ℚ) := [CFrac.ofFraction [1] [0, 1] (by cfrac_nonzero)]                           -- `b = 1/x`
     let c : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 0, CFrac.ofFraction [2, 1] [1] (by cfrac_nonzero)]                 -- `c = (2+x)t`
     (match DensePoly.cPolyRischDECancelExp Dt b c 5 with
       | some q =>
           DensePoly.cisZero (DensePoly.csub
             (DensePoly.cadd (CPolyEngine.monomialDeriv Dt q) (DensePoly.cmul b q)) c)
       | none => false)
     && (match DensePoly.cPolyRischDE Dt b c 5, DensePoly.cPolyRischDECancelExp Dt b c 5 with
         | some q1, some q2 => DensePoly.cisZero (DensePoly.csub q1 q2)
         | _, _ => false)) = true := by native_decide

/-- **Example (§6.6 eq. 6.23)**, general non-constant base recursion: `cRischDE` on
`Dy + (1/x)y = 2·log(x) + 1` (`t = log x`) drives the primitive cancellation case through the
non-constant base RDE `RischDE(1/x, 2) = x` over ℚ(x) to `y = x·log(x)`, verified by the cleared
identity over the generic ℚ(x)[t] (`native_decide`). The eq. 6.23 base solve target — `crischDESolve`
at `DenseFrac ℚ` on `(1/x, 2)` — is checked to return `s = x`. -/
theorem ex_6_6_baseRecursion :
    (let Dt : DensePoly (DenseFrac ℚ) := [CFrac.ofFraction [1] [0, 1] (by cfrac_nonzero)]                          -- `Dt = 1/x`
     let fnum : DensePoly (DenseFrac ℚ) := [CFrac.ofFraction [1] [0, 1] (by cfrac_nonzero)]                        -- `f = 1/x`
     let fden : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1]
     let gnum : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1, CFrac.ofScalar 2]                      -- `g = 2t + 1`
     let gden : DensePoly (DenseFrac ℚ) := [CFrac.ofScalar 1]
     (match DensePoly.cRischDE Dt fnum fden gnum gden with
       | some (ynum, yden) => rdeClearedCheckG6 Dt fnum fden gnum gden ynum yden
       | none => false)
     && (match CRischField.crischDESolve (CFrac.ofFraction [1] [0, 1] (by cfrac_nonzero)) (CFrac.ofScalar 2) with
         | some s => CCommRing.isZero (CField.sub s qX6)                            -- `s = x`
         | none => false)) = true := by native_decide

/-- **Example (§6.6 eq. 6.23)**, standalone rational base solve: the generic tower base solve
`CRischField.crischDESolve (α := DenseFrac ℚ)` on `Ds + (1/x)s = 2` returns `s = x` — the whole Ch. 6
pipeline at the base level over ℚ[x] (`instCRischFieldCFrac`, bottoming at `CRischField ℚ`), verified
`s = x` directly over `DenseFrac ℚ` (`native_decide`). -/
theorem ex_6_6_rationalRDE :
    (match CRischField.crischDESolve (CFrac.ofFraction [1] [0, 1] (by cfrac_nonzero)) (CFrac.ofScalar 2) with
      | some s => CCommRing.isZero (CField.sub s qX6)
      | none => false) = true := by native_decide

end DeepWiki.Si
