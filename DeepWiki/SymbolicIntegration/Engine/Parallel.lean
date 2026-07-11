import DeepWiki.SymbolicIntegration.Engine.Parametric
import DeepWiki.ComputableAlgebra.PolyEuclideanDense
import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded
import DeepWiki.ComputableAlgebra.PolyEngine
import DeepWiki.ComputableAlgebra.PolyEuclidean
import DeepWiki.ComputableAlgebra.PolyReprGcd
import DeepWiki.SymbolicIntegration.Engine.Tower.Lvl2

/-! # Computable parallel (Risch–Norman) integration over ℚ(t) (Bronstein Chapter 10)

Bronstein, *Symbolic Integration I*, Chapter 10 ("Parallel Integration", book p.297–318) presents the
**Risch–Norman heuristic** (the "new Risch algorithm" / "parallel Risch algorithm"), an alternative to
the recursive Risch algorithm of Chapters 5–7. Instead of peeling off one transcendental generator at a
time, it views the integrand `f` in the multivariate rational field `K = C(t₁,…,tₙ)` and integrates *all
generators at once*. By the strong Liouville Theorem (5.5.3), if `∫f` is elementary then
```
  f = Dv + Σᵢ cᵢ·(Duᵢ/uᵢ)                                                                      (10.1)
```
with `v ∈ K`, constants `cᵢ`, and `uᵢ` polynomials in `t₁,…,tₙ` (logarithmic-derivative identity). The
method makes **educated guesses** for the `uᵢ` (the **log arguments**) and the denominator + degree of
`v` (the **rational part**), turning the unknowns — the `cᵢ` and the numerator coefficients of `v` —
into a **linear system over the constants** `Const(K)`, solved through `CLinearSolve`. It is
**heuristic, not algorithmic**: a guess
may be too small (so a genuine elementary integral is missed) — turning it into a decision procedure for
a class of integrands "remains an open problem" (book p.298). Its appeal is implementation ease and speed.

## §10.2 — the shape of the guess (book p.301–308)

Theorem 10.2.1 (book p.302) fixes the structure of an elementary integral: with `denD(K)` the
denominator of `K` w.r.t. the derivation and `d = dₛ·dₙ` its splitting factorization,
```
  f = D(b / (s·∏_{j≥2} dⱼ^{j-1})) + Σᵢ αᵢ·(Dsᵢ/sᵢ) + Σᵢ βᵢ·(Dpᵢ/pᵢ) + Σᵢ γᵢ·(Dwᵢ/wᵢ)               (10.2)
```
where the `dⱼ` are the squarefree factors of `dₙ`, the `sᵢ` are the irreducible **special** polynomials
(`S^irr_{K:F}`, Theorem 10.2.2 lists them for towers of monomials: the irreducible factors of `denD(K)`
plus `1+tⱼ²` for hypertangents), and the `pᵢ` are the irreducible factors of `dₙ`. The rational-part
denominator `s` is guessed as `s = dₛ·∏_{p ∈ S, p∤dₛ} p` (eq. 10.3, the "common guess `s = dₛ`" of book
p.305, which may need to be larger to absorb cancellations — the heuristic's failure mode).

## §10.3 — the integration method `ParallelIntegrate(f, D)` (book p.309)

1. `h ← lcm(denominators of Dtᵢ)`; the special part `S` of the candidate logs (the irreducible specials
   `S^irr_{K:F}` for monomial towers, an exhaustive low-degree search otherwise);
2. `(dₙ, dₛ) ← SplitFactor(d)`, `(d₁,…,dₑ) ← SquareFree(dₙ)`, `{p₁,…,p_l} ← IrreducibleFactors(d₁⋯dₑ)`
   — the candidate **log arguments**;
3. rational-part denominator `vₛ ← dₛ·∏dⱼ^{j-1}`, numerator-degree bound `bᵢ` (eq. 10.4/10.5), and the
   undetermined-coefficient numerator `b = Σ u_{i₁…iₙ} t₁^{i₁}⋯tₙ^{iₙ}`;
4. substitute the ansatz `v = b/vₛ`, `Σ αᵢ log(sᵢ) + Σ βᵢ log(pᵢ)` into (10.2), equate to `f`, clear
   denominators (eq. 10.6) — an **inhomogeneous linear system** for the constants `u…, αᵢ, βᵢ`;
5. solve it (linear algebra). No solution ⟹ `"failed"` (the guess was too small, *or* `f` has no
   elementary integral — the method cannot tell which). A solution ⟹ `∫f = v + Σ αᵢ log sᵢ + Σ βᵢ log pᵢ`.

## What this file delivers (computable over the base monomial field `k = ℚ`, `ccompute`-validated)

We realize `ParallelIntegrate` over the **base monomial case** `k = ℚ`, `t` a single monomial with
derivative `Dt ∈ ℚ[t]` and the derivation `D = Dt·d/dt` (`Const(k) = ℚ`, `κ_D = 0`) — the worked
Examples 10.3.1/10.3.3 setting and the field `ℚ(t)` the engine computes over (`DensePoly ℚ`,
exactly as §7.1 in `ComputableParametric`). The transcendental monomials reachable this way include
`t = exp(x)` (`Dt = t`), `t = tan(x)` (`Dt = 1 + t²`) and `t = x` (`Dt = 1`, ordinary rational
integration). The candidate **log arguments** are taken to be the **squarefree factors** of `d` (the
default educated guess; an integrand whose denominator factors into squarefree-but-reducible pieces over
ℚ would need the irreducible refinement of step 2 — the documented continuation). Concretely:

* **`cSqfreeYunFactors`** — Yun's squarefree factorization over `ℚ[t]` (the `(d₁,…,dₑ)` of step 2).
* **`cParallelSystemQ`** — builds the eq. 10.6 inhomogeneous linear system: from the squarefree
  factorization it forms the rational-part denominator `s = ∏ dⱼ^{j-1}`, the bounded-degree numerator
  ansatz `b` (coefficients `u₀…u_β`), the log atoms `{dⱼ}` (coefficients `c₁…c_m`), clears
  `f = D(b/s) + Σ cⱼ·Dpⱼ/pⱼ` by the common denominator `s²·∏pⱼ` (which `d` divides) to the polynomial
  identity `a·s = (Db·s − b·Ds)·∏pⱼ + Σ cⱼ·Dpⱼ·s²·∏_{k≠j}pₖ`, and reads off the matrix.
* **`CLinearSolve.solveAny`** — a *particular* solution of the (typically underdetermined: the arbitrary
  constant of integration leaves free variables) inhomogeneous system, complementing the unique-solution
  `CLinearSolve.solveUnique`.
* **`cParallelIntegrate`** — the `ParallelIntegrate(f, D)` box: returns `some (rational part (b,s),
  [(cⱼ, log arg pⱼ)])` or `none` ("failed" — ansatz infeasible / no elementary integral in the guess).

## What is documented / deferred

The genuine **multivariate tower** `ℚ(x)[t]` (`a d : DensePoly (DenseFrac ℚ)`, the `cParallelIntegrateTower`
signature stub) needs the special-polynomial list `S^irr_{K:F}` and irreducible factorization over `F̄`
(Theorems 10.2.1/10.2.2, Examples 10.3.2/10.3.4) — the documented continuation; the §10.1 multivariate
`SplitFactor`/`SplitSquarefreeFactor` and the §10.4 simple-differential-field exponent bounds
(Def 10.4.1/Thm 10.4.1) are likewise out of scope here. Abstract correctness (that a returned ansatz
solution satisfies (10.1)) is *not* proved; instead every landed integral is `ccompute`-validated on
its **cleared antiderivative identity** `D(∫f) = f` over `ℚ(t)`. No `sorry`. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

namespace DensePoly

/-! ### The base monomial derivation and small helpers -/

end DensePoly

/-- **Base monomial derivation** `cDerivMonomialQ Dt p = (dp/dt)·Dt` in any polynomial-engine
representation, where the coefficient field `ℚ` is constant under the derivation. -/
def cDerivMonomialQ {P : Type → Type} [CPoly P] [CPolyEngine P] (Dt p : P ℚ) : P ℚ :=
  CPolyEngine.mul (CPolyEngine.deriv p) Dt

example :
    CPoly.cdeg (cDerivMonomialQ
      (CPoly.SparsePoly.ofList [(1, 1)] : CPoly.SparsePoly ℚ)
      (CPoly.SparsePoly.ofList [(0, 1), (1, 2), (2, 3)])) = 2 := by
  ccompute

namespace DensePoly

/-! ### The eq. 10.6 linear system of the Risch–Norman ansatz -/

/-- **The Risch–Norman ansatz data** `cParallelAnsatzQ fuel Dt a d` (Bronstein §10.3 steps 2–4):
from `f = a/d` (over `ℚ(t)`, `D = Dt·d/dt`) build the candidate `∫f = b/s + Σⱼ cⱼ·log(pⱼ)`. Returns
`(ps, s, nU)` where:

* `ps = [d₁,…,d_m]` — the monic **squarefree factors** of `d` (the candidate log arguments `pⱼ`);
* `s = ∏ⱼ dⱼ^{j-1}` — the rational-part denominator `vₛ` (eq. 10.3, `dₛ = 1` over ℚ as all of `ℚ[t]` is
  normal for `D = d/dt`; for general `Dt`, `s` still divides `d` and `s·∏pⱼ = monic(d)`);
* `nU` — the number of numerator coefficients `u₀,…,u_{nU-1}` of `b` (degree bound from eq. 10.4/10.5,
  widened to absorb a polynomial part of `f`: `nU = max(deg s, deg a − deg d + deg s) + 2`).

`d` need not be monic; the caller's `a` is rescaled by `1/lc(d)` in `cParallelSystemQ`. -/
def cParallelAnsatzQ (d : DensePoly ℚ) (degA : ℤ) :
    List (DensePoly ℚ) × DensePoly ℚ × ℕ :=
  let sf := cSqfreeYunFactors d
  let ps := sf.map Prod.fst
  let s := cprod (sf.map (fun (p, e) => cpow p (e - 1)))
  let degS : ℤ := (cdeg s : ℤ)
  let degD : ℤ := (cdeg d : ℤ)
  let bound : ℤ := max degS (degA - degD + degS) + 1
  (ps, s, bound.toNat + 1)

/-- **The eq. 10.6 inhomogeneous linear system** `cParallelSystemQ Dt a d = (rows, rhs, nU, m)`
(Bronstein §10.3 step 4). Substituting the ansatz `∫(a/d) = b/s + Σⱼ cⱼ·log(pⱼ)` (with `b = Σ uᵢ tⁱ`,
`{pⱼ}` the squarefree factors of `d`, `s = ∏ dⱼ^{j-1}`) into `f = D(b/s) + Σⱼ cⱼ·Dpⱼ/pⱼ` and clearing
the common denominator `M = s²·∏pⱼ` (which `monic(d)` divides, `M/d = s`) yields the polynomial identity
```
  a·s = (Db·s − b·Ds)·∏ⱼpⱼ + Σⱼ cⱼ·Dpⱼ·s²·∏_{k≠j}pₖ                                            (10.6)
```
(with `a` first rescaled to make `d` monic, `D = Dt·d/dt`). Equating `tⁱ`-coefficients gives the dense
matrix `rows` and right-hand side `rhs = coeffs(a·s)` over the unknowns `(u₀,…,u_{nU-1}, c₁,…,c_m)`
(`nU` numerator coefficients then `m = #squarefree factors` log coefficients). Fed to the abstract
`CLinearSolve.solveAny` operation. -/
def cParallelSystemQ (Dt a d : DensePoly ℚ) :
    List (List ℚ) × List ℚ × ℕ × ℕ :=
  let lcd := clead d
  let a := cscale (1 / lcd) a                                   -- make `d` monic: `f = a/d` unchanged
  let (ps, s, nU) := cParallelAnsatzQ d (cdeg a : ℤ)
  let m := ps.length
  let prodPs := cprod ps
  let s2 := cmul s s
  let Ds := cDerivMonomialQ Dt s
  let target := cmul a s                                        -- rhs `a·s`
  -- `uᵢ`-column: `b = tⁱ` contributes `(D(tⁱ)·s − tⁱ·Ds)·∏pⱼ` to the lhs of (10.6).
  let uPolys : List (DensePoly ℚ) := (List.range nU).map (fun i =>
    let bi : DensePoly ℚ := cshift i [(1 : ℚ)]
    cmul (csub (cmul (cDerivMonomialQ Dt bi) s) (cmul bi Ds)) prodPs)
  -- `cⱼ`-column: `Dpⱼ·s²·∏_{k≠j}pₖ`.
  let cPolys : List (DensePoly ℚ) := (List.range m).map (fun j =>
    let pj := ps.getD j [(1 : ℚ)]
    let others := cprod (ps.zipIdx.filterMap (fun (p, k) => if k = j then none else some p))
    cmul (cmul (cDerivMonomialQ Dt pj) s2) others)
  let allPolys := uPolys ++ cPolys
  let nrows := (target :: allPolys).foldl (fun acc p => max acc (cnorm p).length) 0
  let rows : List (List ℚ) :=
    (List.range nrows).map (fun i => allPolys.map (fun p => CPoly.coeff p i))
  let rhs : List ℚ := CPoly.coeffs target nrows
  (rows, rhs, nU, m)

/-- Every equation row of `cParallelSystemQ` has one entry for each ansatz unknown. -/
theorem cParallelSystemQ_row_length (Dt a d : DensePoly ℚ) :
    ∀ row ∈ (cParallelSystemQ Dt a d).1,
      row.length = (cParallelSystemQ Dt a d).2.2.1 + (cParallelSystemQ Dt a d).2.2.2 := by
  simp [cParallelSystemQ]

/-- `cParallelSystemQ` has one right-hand-side entry for every equation row. -/
theorem cParallelSystemQ_rows_length_eq_rhs (Dt a d : DensePoly ℚ) :
    (cParallelSystemQ Dt a d).1.length = (cParallelSystemQ Dt a d).2.1.length := by
  simp [cParallelSystemQ]

/-- A returned particular solution of `cParallelSystemQ` satisfies every ansatz equation. -/
theorem cParallelSystemQ_solveAny_sound [LawfulCLinearSolve ℚ]
    (Dt a d : DensePoly ℚ) (sol : List ℚ)
    (hsol : CLinearSolve.solveAny (cParallelSystemQ Dt a d).1 (cParallelSystemQ Dt a d).2.1
      ((cParallelSystemQ Dt a d).2.2.1 + (cParallelSystemQ Dt a d).2.2.2) = some sol) :
    ∀ i, i < (cParallelSystemQ Dt a d).1.length →
      linearSolveRow (cParallelSystemQ Dt a d).1 (cParallelSystemQ Dt a d).2.1 sol i := by
  apply LawfulCLinearSolve.solveAny_sound (cParallelSystemQ Dt a d).1
    (cParallelSystemQ Dt a d).2.1
    ((cParallelSystemQ Dt a d).2.2.1 + (cParallelSystemQ Dt a d).2.2.2) sol ?_ ?_ hsol
  · exact cParallelSystemQ_row_length Dt a d
  · exact cParallelSystemQ_rows_length_eq_rhs Dt a d

/-- **Parallel (Risch–Norman) integration over `ℚ(t)`** `cParallelIntegrate fuel Dt a d` (Bronstein
§10.3, the `ParallelIntegrate(f, D)` box, book p.309), `k = ℚ`, the monomial `t` with derivative
`Dt ∈ ℚ[t]`, `D = Dt·d/dt`. For the integrand `f = a/d ∈ ℚ(t)` it builds the ansatz
`∫f = b/s + Σⱼ cⱼ·log(pⱼ)` (`{pⱼ}` = squarefree factors of `d`, `s = ∏ dⱼ^{j-1}`, `b` the bounded-degree
undetermined numerator), forms the eq. 10.6 linear system (`cParallelSystemQ`), and solves it
(`CLinearSolve.solveAny`). Returns:

* `some ((b, s), [(c₁, p₁), …, (c_m, p_m)])` — the rational part `b/s` and the log terms `Σ cⱼ log(pⱼ)`
  of the elementary antiderivative; or
* `none` — `"failed"`: the linear system is inconsistent, i.e. the educated guess (squarefree-factor
  logs + the degree bound) does **not** capture an elementary integral. Being heuristic, this does *not*
  prove `f` has no elementary integral — only that none exists *in this ansatz* (book p.298).

Validated on transcendental integrands (`t = exp x`, `t = tan x`) and rational ones via the cleared
identity `D(∫f) = f`. -/
def cParallelIntegrate [CLinearSolve ℚ] (Dt a d : DensePoly ℚ) :
    Option ((DensePoly ℚ × DensePoly ℚ) × List (ℚ × DensePoly ℚ)) :=
  let (rows, rhs, nU, m) := cParallelSystemQ Dt a d
  let (ps, s, _) := cParallelAnsatzQ d (cdeg (cscale (1 / clead d) a) : ℤ)
  match CLinearSolve.solveAny rows rhs (nU + m) with
  | none => none
  | some sol =>
    let b : DensePoly ℚ := (List.range nU).map (fun i => sol.getD i 0)   -- numerator coefficients
    let cs : List ℚ := (List.range m).map (fun j => sol.getD (nU + j) 0)
    let logs : List (ℚ × DensePoly ℚ) := (List.zip cs ps).filter (fun (c, _) => c ≠ 0)
    some ((cnorm b, s), logs)

end DensePoly

/-! ### The cleared antiderivative identity `D(∫f) = f` — the validation predicate

The returned `((b, s), [(cⱼ, pⱼ)])` reconstructs `∫f = b/s + Σⱼ cⱼ·log(pⱼ)`, whose derivative is the
rational function `D(b/s) + Σⱼ cⱼ·Dpⱼ/pⱼ`. We assemble that as a single `(num, den)` over `ℚ(t)` and
check `D(∫f) = a/d` by the *cleared* identity `num·d − a·den = 0` (`cisZero`), the faithful
`D(∫f) = f`. -/

/-- **Derivative of a parallel-integration result, as a single fraction** `cParallelResultDerivQ Dt
((b,s), logs) = (num, den)` with `num/den = D(b/s + Σ cⱼ log pⱼ) = (Db·s − b·Ds)/s² + Σ cⱼ·Dpⱼ/pⱼ`. The
common denominator is `s²·∏pⱼ`; the numerator is assembled in any polynomial-engine representation. -/
def cParallelResultDerivQ {P : Type → Type} [CPoly P] [CPolyEngine P] (Dt : P ℚ)
    (res : (P ℚ × P ℚ) × List (ℚ × P ℚ)) : P ℚ × P ℚ :=
  let ((b, s), logs) := res
  let ps := logs.map Prod.snd
  let prodPs := CPolyEngine.prod ps
  let s2 := CPolyEngine.mul s s
  let den := CPolyEngine.mul s2 prodPs                              -- `s²·∏pⱼ`
  -- rational part `D(b/s) = (Db·s − b·Ds)/s²`, over `den`: numerator `(Db·s − b·Ds)·∏pⱼ`.
  let Ds := cDerivMonomialQ Dt s
  let ratNum := CPolyEngine.mul
    (CPolyEngine.sub (CPolyEngine.mul (cDerivMonomialQ Dt b) s) (CPolyEngine.mul b Ds)) prodPs
  -- log part `Σ cⱼ·Dpⱼ/pⱼ`, over `den`: `Σ cⱼ·Dpⱼ·s²·∏_{k≠j}pₖ`.
  let logNum : P ℚ := (logs.zipIdx).foldl (fun acc ((c, pj), j) =>
    let others := CPolyEngine.prod
      (ps.zipIdx.filterMap (fun (p, k) => if k = j then none else some p))
    CPolyEngine.add acc (CPolyEngine.scale c
      (CPolyEngine.mul (CPolyEngine.mul (cDerivMonomialQ Dt pj) s2) others)))
    CPoly.czero
  (CPolyEngine.add ratNum logNum, den)

/-- **The cleared antiderivative check** `cParallelCheckQ Dt a d res`: `true` iff the
parallel-integration result `res = ((b,s), logs)` satisfies `D(b/s + Σ cⱼ log pⱼ) = a/d` as rational
functions over `ℚ(t)`, decided by `cisZero (num·d − a·den)` where `(num, den) =
cParallelResultDerivQ … res`. This is the faithful `D(∫f) = f` certificate (no equality decision on
`DenseFrac ℚ` needed — the polynomial cross-difference is zero-tested in the engine representation). -/
def cParallelCheckQ {P : Type → Type} [CPoly P] [CPolyEngine P] (Dt a d : P ℚ)
    (res : (P ℚ × P ℚ) × List (ℚ × P ℚ)) : Bool :=
  let (num, den) := cParallelResultDerivQ Dt res
  CPolyEngine.cisZero (CPolyEngine.sub (CPolyEngine.mul num d) (CPolyEngine.mul a den))

example :
    cParallelCheckQ
      (CPoly.SparsePoly.ofList [(0, 1)] : CPoly.SparsePoly ℚ)
      (CPoly.SparsePoly.ofList [(0, 1)])
      (CPoly.SparsePoly.ofList [(0, 1)])
      ((CPoly.SparsePoly.ofList [(1, 1)], CPoly.SparsePoly.ofList [(0, 1)]), []) = true := by
  ccompute

/-! ### Represented rational-function towers — documented signature stub

The genuine differential tower `k(t) = ℚ(x)(t)` needs the special-polynomial list `S^irr_{K:F}`
(Theorem 10.2.2) and the irreducible
factorization of `dₙ` over `F̄ = ℚ̄(x)` (Theorem 10.2.1, Examples 10.3.2/10.3.4) before the eq. 10.6 solve
— the matrix entries then lie in `F = ℚ(x)`, not `Const(k) = ℚ`, so Lemma 7.1.2's row-differentiation
reduction to a `ℚ`-system precedes `crref` (cf. `ComputableParametric` §7.1). We expose the signature
(over any `CFrac F Q` representation of `ℚ(x)`) and route the base-field case `Dt, a, d ∈ ℚ[t]` (every
coefficient a represented `ℚ`-constant) through the landed `DensePoly.cParallelIntegrate`; a coefficient with
a genuine `x`-dependence returns `none` ("deferred to the tower construction"). -/

namespace DensePoly

/-- Convert a represented-fraction polynomial to dense rational coefficients when every coefficient is constant. -/
def cToRatCoeffsQ {P Q : Type → Type} [CPoly P] [CPolyEngine P]
    [CPoly Q] [CPolyEngine Q] [CPolyGcd Q ℚ] [CPolyEuclidean Q]
    {F : (α : Type) → [CField α] → Type} [CFrac F Q] [LawfulCFrac F Q] [CFieldDomain ℚ Q]
    (p : P (F ℚ)) : Option (DensePoly ℚ) :=
  (CPolyEngine.coeffList p).foldr (fun (z : F ℚ) acc =>
    match acc with
    | none => none
    | some qs =>
      let num := CFrac.num z
      let den := CFrac.den z
      let g := CPolyGcd.compute num den
      let num' := CPolyEuclidean.div num g
      let den' := CPolyEuclidean.div den g
      if CPoly.cdeg num' = 0 ∧ CPoly.cdeg den' = 0 then
        some ((CPoly.coeff num' 0 / CPoly.coeff den' 0) :: qs)
      else none) (some [])

/-- Run the base-field parallel integrator through any represented-fraction coefficient carrier. -/
def cParallelIntegrateTower {P Q : Type → Type} [CPoly P] [CPolyEngine P]
    [CPoly Q] [CPolyEngine Q] [CPolyGcd Q ℚ] [CPolyEuclidean Q]
    {F : (α : Type) → [CField α] → Type} [CFrac F Q] [LawfulCFrac F Q] [CFieldDomain ℚ Q] [CLinearSolve ℚ]
    (Dt a d : P (F ℚ)) : Option ((P (F ℚ) × P (F ℚ)) × List (ℚ × P (F ℚ))) :=
  match cToRatCoeffsQ Dt, cToRatCoeffsQ a, cToRatCoeffsQ d with
  | some DtQ, some aQ, some dQ =>
    match cParallelIntegrate DtQ aQ dQ with
    | none => none
    | some ((b, s), logs) =>
      let lift : DensePoly ℚ → P (F ℚ) := fun p =>
        CPolyEngine.ofCoeffList ((p : List ℚ).map CFrac.ofScalar)
      some ((lift b, lift s), logs.map (fun (c, p) => (c, lift p)))
  | _, _, _ => none

/-- The parallel tower wrapper executes with a sparse outer polynomial representation. -/
example :
    (cParallelIntegrateTower
      (CPoly.SparsePoly.ofList [(0, CFrac.ofScalar 1)] : CPoly.SparsePoly (DenseFrac ℚ))
      (CPoly.SparsePoly.ofList [(1, CFrac.ofScalar 2)])
      (CPoly.SparsePoly.ofList [(0, CFrac.ofScalar 1), (2, CFrac.ofScalar 1)])).isSome = true := by
  ccompute

/-- The parallel tower wrapper also executes with sparse inner fractions and sparse outer polynomials. -/
example :
    (cParallelIntegrateTower
      (CPoly.SparsePoly.ofList [(0, CFrac.ofScalar 1)] : CPoly.SparsePoly (SparseFrac ℚ))
      (CPoly.SparsePoly.ofList [(1, CFrac.ofScalar 2)])
      (CPoly.SparsePoly.ofList [(0, CFrac.ofScalar 1), (2, CFrac.ofScalar 1)])).isSome = true := by
  ccompute

end DensePoly

/-! ### Examples — executable cleared antiderivative identities

Each example feeds an integrand `f = a/d` over `ℚ(t)` with a known elementary integral to
`cParallelIntegrate`, then verifies the returned `∫f = b/s + Σ cⱼ log pⱼ` actually satisfies
`D(∫f) = f` via `cParallelCheckQ` (the cleared polynomial identity `num·d − a·den = 0`). -/

open DensePoly

/-! #### (1) Pure log, `t = x` (`Dt = 1`): `∫ 2t/(t²+1) dt = log(t²+1)`.
The squarefree factor `t²+1` is irreducible over ℚ, `s = 1`, the candidate log argument is `t²+1`, and
the solve gives `c₁ = 1` (and zero numerator). -/

/-- Example: `f = 2t/(t²+1)`, `t = x` (`Dt = [1]`), antiderivative `log(t²+1)`. -/
def parallelExampleLogA : DensePoly ℚ := [0, 2]
/-- The denominator `t²+1`. -/
def parallelExampleLogD : DensePoly ℚ := [1, 0, 1]

/-- **Pure-log parallel integration computes** (`ccompute`, Bronstein §10.3, book p.309). For
`∫ 2t/(t²+1) dt` over `ℚ(t)` (`D = d/dt`), `cParallelIntegrate` returns `some res` whose reconstructed
antiderivative `b/s + Σ cⱼ log pⱼ` is verified to **actually satisfy** `D(res) = 2t/(t²+1)` by the
cleared identity `cParallelCheckQ` (`num·d − a·den = 0`). The Risch–Norman ansatz (squarefree-factor log
candidates + linear solve) recovers `log(t²+1)`. -/
theorem parallelIntegrate_log_example :
    (match cParallelIntegrate [1] parallelExampleLogA parallelExampleLogD with
      | some res => cParallelCheckQ [1] parallelExampleLogA parallelExampleLogD res
      | none => false) = true := by ccompute

/-! #### (2) Transcendental, `t = exp x` (`Dt = t = [0,1]`): `∫ t/(t+1)² dx = −1/(t+1)`.
A genuine element of `ℚ(exp x)`: `D(−1/(t+1)) = Dt·1/(t+1)² = t/(t+1)²`. The squarefree factor `t+1` has
multiplicity 2, so `s = t+1` (rational part) and the candidate log `t+1` gets coefficient `0`. -/

/-- Example: `f = t/(t+1)²`, `t = exp x` (`Dt = [0,1]`), antiderivative `−1/(t+1)`. -/
def parallelExampleExpA : DensePoly ℚ := [0, 1]
/-- The denominator `(t+1)² = t² + 2t + 1`. -/
def parallelExampleExpD : DensePoly ℚ := [1, 2, 1]
/-- The exponential monomial derivative `Dt = t` (`t = exp x`, `Dexp = exp`). -/
def parallelExampleExpDt : DensePoly ℚ := [0, 1]

/-- **Transcendental parallel integration computes** (`ccompute`, Bronstein §10.3, book p.309). For
`∫ exp(x)/(exp(x)+1)² dx` — `f = t/(t+1)²` over the genuine transcendental field `ℚ(exp x)` with the
monomial derivation `Dt = t` — `cParallelIntegrate` returns `some res` (the rational part `−1/(t+1)`),
verified to **actually satisfy** `D(res) = t/(t+1)²` by `cParallelCheckQ`. This is the §10.3 deliverable:
the Risch–Norman ansatz + linear solve recovers an elementary antiderivative over a nontrivial monomial
extension (`Dt ≠ 1`), exactly the "parallel" virtue of handling the generator `t = exp x` directly. -/
theorem parallelIntegrate_exp_example :
    (match cParallelIntegrate parallelExampleExpDt parallelExampleExpA parallelExampleExpD with
      | some res => cParallelCheckQ parallelExampleExpDt parallelExampleExpA parallelExampleExpD res
      | none => false) = true := by ccompute

/-! #### (3) Transcendental mixed rational + log, `t = exp x` (`Dt = t`):
`∫ (t²+2t)/(t+1)² dx = −1/(t+1) + log(t+1)`. The antiderivative carries **both** a rational part and a
log simultaneously — the full Risch–Norman shape. `D(−1/(t+1) + log(t+1)) = t/(t+1)² + t/(t+1) =
(t²+2t)/(t+1)²`. -/

/-- Example: `f = (t²+2t)/(t+1)²`, `t = exp x` (`Dt = [0,1]`), antiderivative `−1/(t+1) + log(t+1)`. -/
def parallelExampleMixA : DensePoly ℚ := [0, 2, 1]

/-- **Mixed rational + log parallel integration computes** (`ccompute`, Bronstein §10.3, book
p.309). For `∫ (exp(x)²+2exp(x))/(exp(x)+1)² dx` — `f = (t²+2t)/(t+1)²` over `ℚ(exp x)`, `Dt = t` — the
single linear solve of `cParallelIntegrate` produces **both** the rational part `−1/(t+1)` and the log
`log(t+1)` at once, verified to **actually satisfy** `D(res) = (t²+2t)/(t+1)²` by `cParallelCheckQ`. This
exhibits the full Liouville shape (10.1) `f = Dv + Σ cⱼ Duⱼ/uⱼ` recovered in one parallel linear-algebra
step — the chapter's headline. -/
theorem parallelIntegrate_mixed_example :
    (match cParallelIntegrate parallelExampleExpDt parallelExampleMixA parallelExampleExpD with
      | some res => cParallelCheckQ parallelExampleExpDt parallelExampleMixA parallelExampleExpD res
      | none => false) = true := by ccompute

/-! #### (4) The heuristic *fails* — `∫ 1/(exp(x)+1) dx` is not elementary in the ansatz.
With `t = exp x`, `Dt = t`, `f = 1/(t+1)`: the only candidate log is `t+1` with `Dp/p = t/(t+1)`, which
cannot produce the `1/(t+1)` shape (the integral `∫dx/(eˣ+1) = x − log(eˣ+1)` needs the generator
`x = ∫1`, *outside* `ℚ(exp x)`). So the linear system is inconsistent and `cParallelIntegrate` returns
`none` — the documented **heuristic failure** (book p.298: a `none` does not prove non-elementarity, only
that the guess was too small). -/

/-- Example: `f = 1/(exp x + 1)`, whose antiderivative `x − log(exp x + 1)` lies outside `ℚ(exp x)`. -/
def parallelExampleFailA : DensePoly ℚ := [1]
/-- The denominator `exp x + 1 = t + 1`. -/
def parallelExampleFailD : DensePoly ℚ := [1, 1]

/-- **The parallel heuristic fails on a non-(ansatz-)elementary integrand** (`ccompute`, Bronstein
§10.3, book p.298). `∫ 1/(exp(x)+1) dx` has antiderivative `x − log(exp x+1)`, which is **not** in the
candidate space `b/(t+1) + c·log(t+1)` over `ℚ(exp x)` (it needs the generator `x = ∫1` outside the
field). `cParallelIntegrate` returns `none` — the linear system is inconsistent. This is the chapter's
key caveat: the method is *heuristic*, and `none` means "no elementary integral **in this guess**", not a
proof of non-elementarity. -/
theorem parallelIntegrate_failure_example :
    cParallelIntegrate parallelExampleExpDt parallelExampleFailA parallelExampleFailD = none := by
  ccompute

end DeepWiki.SymbolicIntegration
