import DeepWiki.SymbolicIntegration.Engine.Parametric
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd
import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv
import DeepWiki.ComputableAlgebra.GenericPolyEngine
import DeepWiki.SymbolicIntegration.Engine.Tower.Field

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
into a **linear system over the constants** `Const(K)`, solved by ordinary linear algebra
(`crref`/`cConstSolveUniqueQ` of `ComputableParametric`). It is **heuristic, not algorithmic**: a guess
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

## What this file delivers (computable over the base monomial field `k = ℚ`, `native_decide`-validated)

We realize `ParallelIntegrate` over the **base monomial case** `k = ℚ`, `t` a single monomial with
derivative `Dt ∈ ℚ[t]` and the derivation `D = Dt·d/dt` (`Const(k) = ℚ`, `κ_D = 0`) — the worked
Examples 10.3.1/10.3.3 setting and the field `ℚ(t)` the engine `native_decide`s over (`CPoly ℚ`,
exactly as §7.1 in `ComputableParametric`). The transcendental monomials reachable this way include
`t = exp(x)` (`Dt = t`), `t = tan(x)` (`Dt = 1 + t²`) and `t = x` (`Dt = 1`, ordinary rational
integration). The candidate **log arguments** are taken to be the **squarefree factors** of `d` (the
default educated guess; an integrand whose denominator factors into squarefree-but-reducible pieces over
ℚ would need the irreducible refinement of step 2 — the documented continuation). Concretely:

* **`cSquarefreeFactorsQ`** — Yun's squarefree factorization over `ℚ[t]` (the `(d₁,…,dₑ)` of step 2).
* **`cParallelSystemQ`** — builds the eq. 10.6 inhomogeneous linear system: from the squarefree
  factorization it forms the rational-part denominator `s = ∏ dⱼ^{j-1}`, the bounded-degree numerator
  ansatz `b` (coefficients `u₀…u_β`), the log atoms `{dⱼ}` (coefficients `c₁…c_m`), clears
  `f = D(b/s) + Σ cⱼ·Dpⱼ/pⱼ` by the common denominator `s²·∏pⱼ` (which `d` divides) to the polynomial
  identity `a·s = (Db·s − b·Ds)·∏pⱼ + Σ cⱼ·Dpⱼ·s²·∏_{k≠j}pₖ`, and reads off the matrix.
* **`cConstSolveAnyQ`** — a *particular* solution of the (typically underdetermined: the arbitrary
  constant of integration leaves free variables) inhomogeneous system, complementing the unique-solution
  `cConstSolveUniqueQ`.
* **`cParallelIntegrate`** — the `ParallelIntegrate(f, D)` box: returns `some (rational part (b,s),
  [(cⱼ, log arg pⱼ)])` or `none` ("failed" — ansatz infeasible / no elementary integral in the guess).

## What is documented / deferred

The genuine **multivariate tower** `ℚ(x)[t]` (`a d : CPoly (QFunNZG ℚ)`, the `cParallelIntegrateTower`
signature stub) needs the special-polynomial list `S^irr_{K:F}` and irreducible factorization over `F̄`
(Theorems 10.2.1/10.2.2, Examples 10.3.2/10.3.4) — the documented continuation; the §10.1 multivariate
`SplitFactor`/`SplitSquarefreeFactor` and the §10.4 simple-differential-field exponent bounds
(Def 10.4.1/Thm 10.4.1) are likewise out of scope here. Abstract correctness (that a returned ansatz
solution satisfies (10.1)) is *not* proved; instead every landed integral is `native_decide`-validated on
its **cleared antiderivative identity** `D(∫f) = f` over `ℚ(t)`. No `sorry`. -/

namespace DeepWiki.SymbolicIntegration

open CPoly

namespace CPoly

/-! ### Squarefree factorization over `ℚ[t]` (Yun's algorithm) — the `(d₁,…,dₑ)` of §10.3 step 2 -/

/-- **Yun squarefree factorization over `ℚ[t]`** `cSquarefreeFactorsQ fuel p = [(d₁,1),…,(dₑ,e)]`: the
list of monic squarefree factors `dⱼ` of `p` paired with their multiplicities `j`, so
`p ~ ∏ⱼ dⱼ^j` and the `dⱼ` are pairwise coprime and squarefree (Bronstein §1.7 `Squarefree`). Computed
by Yun: `c ← gcd(p, p′)`, `w ← p/c` (product of the distinct factors), then peel `dⱼ = w/gcd(w,c)`,
`w ← gcd(w,c)`, `c ← c/gcd(w,c)`. Euclidean leaves are fuel-free; constant factors are dropped. -/
def cSquarefreeFactorsQ (p : CPoly ℚ) : List (CPoly ℚ × ℕ) :=
  let p := cmonic p
  let c0 := cmonic (cgcdWf p (cderiv p)).1
  let w0 := cdivWf p c0
  let rec go : ℕ → CPoly ℚ → CPoly ℚ → ℕ → List (CPoly ℚ × ℕ)
    | 0, _, _, _ => []
    | f + 1, w, c, i =>
      if cdeg c = 0 then
        (if cdeg w = 0 then [] else [(cmonic w, i)])
      else
        let y := cmonic (cgcdWf w c).1
        let z := cdivWf w y
        let cnext := cdivWf c y
        let rest := go f y cnext (i + 1)
        if cdeg z = 0 then rest else (cmonic z, i) :: rest
  go (cdeg p + 1) w0 c0 1

/-! ### The base monomial derivation and small helpers -/

/-- **Base monomial derivation** `cDerivMonomialQ Dt p = (dp/dt)·Dt` on `CPoly ℚ` (the derivation
`D = Dt·d/dt`, `κ_D = 0` since the coefficient field `ℚ` is constants under `D`). For `Dt = [1]` this is
`d/dt` (ordinary rational integration, `t = x`); `Dt = [0,1]` gives the exponential monomial
`t = exp(x)` (`Dt = t`); `Dt = [1,0,1]` the hypertangent `t = tan(x)` (`Dt = 1 + t²`). -/
def cDerivMonomialQ (Dt p : CPoly ℚ) : CPoly ℚ := cmul (cderiv p) Dt

/-- **Product of a list of `CPoly ℚ`** `cProductQ [p₁,…,pₙ] = p₁⋯pₙ` (`[1]` for the empty list). -/
def cProductQ (ps : List (CPoly ℚ)) : CPoly ℚ := ps.foldl cmul [(1 : ℚ)]

/-- **`tⁱ`-coefficient of a `CPoly ℚ`** `cParCoeffQ p i = coefficient(p, tⁱ)` (`0` out of range). -/
def cParCoeffQ (p : CPoly ℚ) (i : ℕ) : ℚ := (p : List ℚ).getD i 0

/-! ### A *particular*-solution linear solver over ℚ (the §10.3 step-5 solve)

The eq. 10.6 system is generally **underdetermined** — the arbitrary constant of integration (and any
ansatz over-provisioning) leaves free columns. `cConstSolveAnyQ` returns *a* solution (free variables
set to `0`), complementing `cConstSolveUniqueQ` (`ComputableParametric`) which insists on uniqueness. -/

/-- **A particular solution over ℚ** `cConstSolveAnyQ Arows urhs ncols`: solve `A·x⃗ = u⃗` for *some*
`x⃗ ∈ ℚ^ncols`, returning `some x⃗` (free variables set to `0`) when the system is consistent, else
`none` (a pivot in the augmented column ⟹ inconsistent). Used for §10.3 step 5, where the ansatz system
typically has a solution *space* (the `+ constant` freedom). Row-reduces `[A | u]` and reads each pivot
variable off its row's augmented entry; non-pivot (free) variables are `0`. -/
def cConstSolveAnyQ (Arows : List (List ℚ)) (urhs : List ℚ) (ncols : ℕ) : Option (List ℚ) :=
  let aug := List.zipWith (fun r u => r ++ [u]) Arows urhs
  let (R, pivCols) := crref aug (ncols + 1)
  if pivCols.contains ncols then none           -- pivot in the rhs column: inconsistent
  else
    some ((List.range ncols).map (fun j =>
      match pivCols.idxOf? j with
      | some pr => (R.getD pr []).getD ncols 0
      | none => 0))                             -- free variable ⇒ 0 (particular solution)

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
def cParallelAnsatzQ (d : CPoly ℚ) (degA : ℤ) :
    List (CPoly ℚ) × CPoly ℚ × ℕ :=
  let sf := cSquarefreeFactorsQ d
  let ps := sf.map Prod.fst
  let s := cProductQ (sf.map (fun (p, e) => cpow p (e - 1)))
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
(`nU` numerator coefficients then `m = #squarefree factors` log coefficients). Fed to `cConstSolveAnyQ`. -/
def cParallelSystemQ (Dt a d : CPoly ℚ) :
    List (List ℚ) × List ℚ × ℕ × ℕ :=
  let lcd := clead d
  let a := cscale (1 / lcd) a                                   -- make `d` monic: `f = a/d` unchanged
  let (ps, s, nU) := cParallelAnsatzQ d (cdeg a : ℤ)
  let m := ps.length
  let prodPs := cProductQ ps
  let s2 := cmul s s
  let Ds := cDerivMonomialQ Dt s
  let target := cmul a s                                        -- rhs `a·s`
  -- `uᵢ`-column: `b = tⁱ` contributes `(D(tⁱ)·s − tⁱ·Ds)·∏pⱼ` to the lhs of (10.6).
  let uPolys : List (CPoly ℚ) := (List.range nU).map (fun i =>
    let bi : CPoly ℚ := cshift i [(1 : ℚ)]
    cmul (csub (cmul (cDerivMonomialQ Dt bi) s) (cmul bi Ds)) prodPs)
  -- `cⱼ`-column: `Dpⱼ·s²·∏_{k≠j}pₖ`.
  let cPolys : List (CPoly ℚ) := (List.range m).map (fun j =>
    let pj := ps.getD j [(1 : ℚ)]
    let others := cProductQ (ps.zipIdx.filterMap (fun (p, k) => if k = j then none else some p))
    cmul (cmul (cDerivMonomialQ Dt pj) s2) others)
  let allPolys := uPolys ++ cPolys
  let nrows := (target :: allPolys).foldl (fun acc p => max acc (cnorm p).length) 0
  let rows : List (List ℚ) :=
    (List.range nrows).map (fun i => allPolys.map (fun p => cParCoeffQ p i))
  let rhs : List ℚ := (List.range nrows).map (fun i => cParCoeffQ target i)
  (rows, rhs, nU, m)

/-- **Parallel (Risch–Norman) integration over `ℚ(t)`** `cParallelIntegrate fuel Dt a d` (Bronstein
§10.3, the `ParallelIntegrate(f, D)` box, book p.309), `k = ℚ`, the monomial `t` with derivative
`Dt ∈ ℚ[t]`, `D = Dt·d/dt`. For the integrand `f = a/d ∈ ℚ(t)` it builds the ansatz
`∫f = b/s + Σⱼ cⱼ·log(pⱼ)` (`{pⱼ}` = squarefree factors of `d`, `s = ∏ dⱼ^{j-1}`, `b` the bounded-degree
undetermined numerator), forms the eq. 10.6 linear system (`cParallelSystemQ`), and solves it
(`cConstSolveAnyQ`). Returns:

* `some ((b, s), [(c₁, p₁), …, (c_m, p_m)])` — the rational part `b/s` and the log terms `Σ cⱼ log(pⱼ)`
  of the elementary antiderivative; or
* `none` — `"failed"`: the linear system is inconsistent, i.e. the educated guess (squarefree-factor
  logs + the degree bound) does **not** capture an elementary integral. Being heuristic, this does *not*
  prove `f` has no elementary integral — only that none exists *in this ansatz* (book p.298).

Validated on transcendental integrands (`t = exp x`, `t = tan x`) and rational ones via the cleared
identity `D(∫f) = f`. -/
def cParallelIntegrate (Dt a d : CPoly ℚ) :
    Option ((CPoly ℚ × CPoly ℚ) × List (ℚ × CPoly ℚ)) :=
  let (rows, rhs, nU, m) := cParallelSystemQ Dt a d
  let (ps, s, _) := cParallelAnsatzQ d (cdeg (cscale (1 / clead d) a) : ℤ)
  match cConstSolveAnyQ rows rhs (nU + m) with
  | none => none
  | some sol =>
    let b : CPoly ℚ := (List.range nU).map (fun i => sol.getD i 0)   -- numerator coefficients
    let cs : List ℚ := (List.range m).map (fun j => sol.getD (nU + j) 0)
    let logs : List (ℚ × CPoly ℚ) := (List.zip cs ps).filter (fun (c, _) => c ≠ 0)
    some ((cnorm b, s), logs)

/-! ### The cleared antiderivative identity `D(∫f) = f` — the validation predicate

The returned `((b, s), [(cⱼ, pⱼ)])` reconstructs `∫f = b/s + Σⱼ cⱼ·log(pⱼ)`, whose derivative is the
rational function `D(b/s) + Σⱼ cⱼ·Dpⱼ/pⱼ`. We assemble that as a single `(num, den)` over `ℚ(t)` and
check `D(∫f) = a/d` by the *cleared* identity `num·d − a·den = 0` (`cisZero`), the faithful
`D(∫f) = f`. -/

/-- **Derivative of a parallel-integration result, as a single fraction** `cParallelResultDerivQ Dt
((b,s), logs) = (num, den)` with `num/den = D(b/s + Σ cⱼ log pⱼ) = (Db·s − b·Ds)/s² + Σ cⱼ·Dpⱼ/pⱼ`. The
common denominator is `s²·∏pⱼ`; the numerator is assembled over it. Used by the cleared `D(∫f) = f`
check. -/
def cParallelResultDerivQ (Dt : CPoly ℚ)
    (res : (CPoly ℚ × CPoly ℚ) × List (ℚ × CPoly ℚ)) : CPoly ℚ × CPoly ℚ :=
  let ((b, s), logs) := res
  let ps := logs.map Prod.snd
  let prodPs := cProductQ ps
  let s2 := cmul s s
  let den := cmul s2 prodPs                                        -- `s²·∏pⱼ`
  -- rational part `D(b/s) = (Db·s − b·Ds)/s²`, over `den`: numerator `(Db·s − b·Ds)·∏pⱼ`.
  let Ds := cDerivMonomialQ Dt s
  let ratNum := cmul (csub (cmul (cDerivMonomialQ Dt b) s) (cmul b Ds)) prodPs
  -- log part `Σ cⱼ·Dpⱼ/pⱼ`, over `den`: `Σ cⱼ·Dpⱼ·s²·∏_{k≠j}pₖ`.
  let logNum : CPoly ℚ := (logs.zipIdx).foldl (fun acc ((c, pj), j) =>
    let others := cProductQ (ps.zipIdx.filterMap (fun (p, k) => if k = j then none else some p))
    cadd acc (cscale c (cmul (cmul (cDerivMonomialQ Dt pj) s2) others))) []
  (cadd ratNum logNum, den)

/-- **The cleared antiderivative check** `cParallelCheckQ fuel Dt a d res`: `true` iff the
parallel-integration result `res = ((b,s), logs)` satisfies `D(b/s + Σ cⱼ log pⱼ) = a/d` as rational
functions over `ℚ(t)`, decided by `cisZero (num·d − a·den)` where `(num, den) =
cParallelResultDerivQ … res`. This is the faithful `D(∫f) = f` certificate (no equality decision on
`QFunNZG ℚ` needed — the polynomial cross-difference is `cisZero`-tested over `ℚ`). -/
def cParallelCheckQ (Dt a d : CPoly ℚ)
    (res : (CPoly ℚ × CPoly ℚ) × List (ℚ × CPoly ℚ)) : Bool :=
  let (num, den) := cParallelResultDerivQ Dt res
  cisZero (csub (cmul num d) (cmul a den))

end CPoly

/-! ### The genuine tower `ℚ(x)[t]` — documented signature stub

The prompt's `cParallelIntegrate Dt fuel (a d : CPoly (QFunNZG ℚ))` over the genuine differential tower
`k(t) = ℚ(x)(t)` needs the special-polynomial list `S^irr_{K:F}` (Theorem 10.2.2) and the irreducible
factorization of `dₙ` over `F̄ = ℚ̄(x)` (Theorem 10.2.1, Examples 10.3.2/10.3.4) before the eq. 10.6 solve
— the matrix entries then lie in `F = ℚ(x)`, not `Const(k) = ℚ`, so Lemma 7.1.2's row-differentiation
reduction to a `ℚ`-system precedes `crref` (cf. `ComputableParametric` §7.1). We expose the signature
(over the **generic** ℚ(x) = `QFunNZG ℚ` carrier) and route the base-field case `Dt, a, d ∈ ℚ[t]` (every
coefficient a `ℚ`-constant `QFunNZG ℚ`) through the landed `CPoly.cParallelIntegrate`; a coefficient with
a genuine `x`-dependence returns `none` ("deferred to the tower construction"). -/

namespace CPoly

/-- A ℚ constant `n ∈ ℚ ⊂ ℚ(x)` as a `QFunNZG ℚ` element (the tower-coefficient builder, the `ℚ → QFunNZG ℚ`
constant embedding; denominator `[1]` nonzero by `cisZeroG_one_singleton`). -/
def qConstTowerG (n : ℚ) : QFunNZG ℚ := ⟨([n], [(1 : ℚ)]), QFunNZG.cisZeroG_one_singleton⟩

/-- **`QFunNZG ℚ`-coefficient `CPoly` to a `ℚ`-coefficient one, when every coefficient is a
`ℚ`-constant.** `cToRatCoeffsQ p = some q` with `q : CPoly ℚ` iff each coefficient of
`p : CPoly (QFunNZG ℚ)` reduces to a `ℚ`-constant (the numerator/denominator gcd-cancelled to degree-0
numerator and denominator), else `none`. The base-field guard for the tower wrapper: the lowest-terms
reduction divides `(num, den)` by their gcd (`cgcdWf`/`cdivWf`), and a `ℚ`-constant is exactly a
degree-0 quotient over a degree-0 (nonzero) remainder denominator. -/
def cToRatCoeffsQ (p : CPoly (QFunNZG ℚ)) : Option (CPoly ℚ) :=
  (p : List (QFunNZG ℚ)).foldr (fun (z : QFunNZG ℚ) acc =>
    match acc with
    | none => none
    | some qs =>
      let num := z.1.1
      let den := z.1.2
      let g := (cgcdWf num den).1
      let num' := cdivWf num g
      let den' := cdivWf den g
      if cdeg num' = 0 ∧ cdeg den' = 0 then
        some ((((num' : List ℚ).headD 0) / ((den' : List ℚ).headD 1)) :: qs)
      else none) (some [])

/-- **Parallel integration over the tower `ℚ(x)[t]`** `cParallelIntegrateTower fuel Dt a d` (Bronstein
§10.3, `a d : CPoly (QFunNZG ℚ)`): the genuine-tower signature over the generic ℚ(x) = `QFunNZG ℚ`
carrier. The base-field case — `Dt, a, d` all with `ℚ`-constant coefficients (so `k = ℚ`, the field
`ℚ(t)`) — is routed through `cParallelIntegrate` and the result lifted back to `QFunNZG ℚ` coefficients
(rational part `(b, s)` and log arguments `pⱼ`, with the `ℚ`-constants `cⱼ`). A genuine `x`-dependent
coefficient (the full tower, needing the §10.2 special-poly list + `F̄`-factorization) returns `none` —
the documented continuation. -/
def cParallelIntegrateTower (Dt a d : CPoly (QFunNZG ℚ)) :
    Option ((CPoly (QFunNZG ℚ) × CPoly (QFunNZG ℚ)) × List (ℚ × CPoly (QFunNZG ℚ))) :=
  match cToRatCoeffsQ Dt, cToRatCoeffsQ a, cToRatCoeffsQ d with
  | some DtQ, some aQ, some dQ =>
    match cParallelIntegrate DtQ aQ dQ with
    | none => none
    | some ((b, s), logs) =>
      let lift : CPoly ℚ → CPoly (QFunNZG ℚ) := fun p => (p : List ℚ).map qConstTowerG
      some ((lift b, lift s), logs.map (fun (c, p) => (c, lift p)))
  | _, _, _ => none

end CPoly

/-! ### Examples — `native_decide`, the cleared antiderivative identity `D(∫f) = f`

Each example feeds an integrand `f = a/d` over `ℚ(t)` with a known elementary integral to
`cParallelIntegrate`, then verifies the returned `∫f = b/s + Σ cⱼ log pⱼ` actually satisfies
`D(∫f) = f` via `cParallelCheckQ` (the cleared polynomial identity `num·d − a·den = 0`). -/

open CPoly

/-! #### (1) Pure log, `t = x` (`Dt = 1`): `∫ 2t/(t²+1) dt = log(t²+1)`.
The squarefree factor `t²+1` is irreducible over ℚ, `s = 1`, the candidate log argument is `t²+1`, and
the solve gives `c₁ = 1` (and zero numerator). -/

/-- Example: `f = 2t/(t²+1)`, `t = x` (`Dt = [1]`), antiderivative `log(t²+1)`. -/
def parallelExampleLogA : CPoly ℚ := [0, 2]
/-- The denominator `t²+1`. -/
def parallelExampleLogD : CPoly ℚ := [1, 0, 1]

/-- **Pure-log parallel integration computes** (`native_decide`, Bronstein §10.3, book p.309). For
`∫ 2t/(t²+1) dt` over `ℚ(t)` (`D = d/dt`), `cParallelIntegrate` returns `some res` whose reconstructed
antiderivative `b/s + Σ cⱼ log pⱼ` is verified to **actually satisfy** `D(res) = 2t/(t²+1)` by the
cleared identity `cParallelCheckQ` (`num·d − a·den = 0`). The Risch–Norman ansatz (squarefree-factor log
candidates + linear solve) recovers `log(t²+1)`. -/
theorem parallelIntegrate_log_example :
    (match cParallelIntegrate [1] parallelExampleLogA parallelExampleLogD with
      | some res => cParallelCheckQ [1] parallelExampleLogA parallelExampleLogD res
      | none => false) = true := by native_decide

/-! #### (2) Transcendental, `t = exp x` (`Dt = t = [0,1]`): `∫ t/(t+1)² dx = −1/(t+1)`.
A genuine element of `ℚ(exp x)`: `D(−1/(t+1)) = Dt·1/(t+1)² = t/(t+1)²`. The squarefree factor `t+1` has
multiplicity 2, so `s = t+1` (rational part) and the candidate log `t+1` gets coefficient `0`. -/

/-- Example: `f = t/(t+1)²`, `t = exp x` (`Dt = [0,1]`), antiderivative `−1/(t+1)`. -/
def parallelExampleExpA : CPoly ℚ := [0, 1]
/-- The denominator `(t+1)² = t² + 2t + 1`. -/
def parallelExampleExpD : CPoly ℚ := [1, 2, 1]
/-- The exponential monomial derivative `Dt = t` (`t = exp x`, `Dexp = exp`). -/
def parallelExampleExpDt : CPoly ℚ := [0, 1]

/-- **Transcendental parallel integration computes** (`native_decide`, Bronstein §10.3, book p.309). For
`∫ exp(x)/(exp(x)+1)² dx` — `f = t/(t+1)²` over the genuine transcendental field `ℚ(exp x)` with the
monomial derivation `Dt = t` — `cParallelIntegrate` returns `some res` (the rational part `−1/(t+1)`),
verified to **actually satisfy** `D(res) = t/(t+1)²` by `cParallelCheckQ`. This is the §10.3 deliverable:
the Risch–Norman ansatz + linear solve recovers an elementary antiderivative over a nontrivial monomial
extension (`Dt ≠ 1`), exactly the "parallel" virtue of handling the generator `t = exp x` directly. -/
theorem parallelIntegrate_exp_example :
    (match cParallelIntegrate parallelExampleExpDt parallelExampleExpA parallelExampleExpD with
      | some res => cParallelCheckQ parallelExampleExpDt parallelExampleExpA parallelExampleExpD res
      | none => false) = true := by native_decide

/-! #### (3) Transcendental mixed rational + log, `t = exp x` (`Dt = t`):
`∫ (t²+2t)/(t+1)² dx = −1/(t+1) + log(t+1)`. The antiderivative carries **both** a rational part and a
log simultaneously — the full Risch–Norman shape. `D(−1/(t+1) + log(t+1)) = t/(t+1)² + t/(t+1) =
(t²+2t)/(t+1)²`. -/

/-- Example: `f = (t²+2t)/(t+1)²`, `t = exp x` (`Dt = [0,1]`), antiderivative `−1/(t+1) + log(t+1)`. -/
def parallelExampleMixA : CPoly ℚ := [0, 2, 1]

/-- **Mixed rational + log parallel integration computes** (`native_decide`, Bronstein §10.3, book
p.309). For `∫ (exp(x)²+2exp(x))/(exp(x)+1)² dx` — `f = (t²+2t)/(t+1)²` over `ℚ(exp x)`, `Dt = t` — the
single linear solve of `cParallelIntegrate` produces **both** the rational part `−1/(t+1)` and the log
`log(t+1)` at once, verified to **actually satisfy** `D(res) = (t²+2t)/(t+1)²` by `cParallelCheckQ`. This
exhibits the full Liouville shape (10.1) `f = Dv + Σ cⱼ Duⱼ/uⱼ` recovered in one parallel linear-algebra
step — the chapter's headline. -/
theorem parallelIntegrate_mixed_example :
    (match cParallelIntegrate parallelExampleExpDt parallelExampleMixA parallelExampleExpD with
      | some res => cParallelCheckQ parallelExampleExpDt parallelExampleMixA parallelExampleExpD res
      | none => false) = true := by native_decide

/-! #### (4) The heuristic *fails* — `∫ 1/(exp(x)+1) dx` is not elementary in the ansatz.
With `t = exp x`, `Dt = t`, `f = 1/(t+1)`: the only candidate log is `t+1` with `Dp/p = t/(t+1)`, which
cannot produce the `1/(t+1)` shape (the integral `∫dx/(eˣ+1) = x − log(eˣ+1)` needs the generator
`x = ∫1`, *outside* `ℚ(exp x)`). So the linear system is inconsistent and `cParallelIntegrate` returns
`none` — the documented **heuristic failure** (book p.298: a `none` does not prove non-elementarity, only
that the guess was too small). -/

/-- Example: `f = 1/(exp x + 1)`, whose antiderivative `x − log(exp x + 1)` lies outside `ℚ(exp x)`. -/
def parallelExampleFailA : CPoly ℚ := [1]
/-- The denominator `exp x + 1 = t + 1`. -/
def parallelExampleFailD : CPoly ℚ := [1, 1]

/-- **The parallel heuristic fails on a non-(ansatz-)elementary integrand** (`native_decide`, Bronstein
§10.3, book p.298). `∫ 1/(exp(x)+1) dx` has antiderivative `x − log(exp x+1)`, which is **not** in the
candidate space `b/(t+1) + c·log(t+1)` over `ℚ(exp x)` (it needs the generator `x = ∫1` outside the
field). `cParallelIntegrate` returns `none` — the linear system is inconsistent. This is the chapter's
key caveat: the method is *heuristic*, and `none` means "no elementary integral **in this guess**", not a
proof of non-elementarity. -/
theorem parallelIntegrate_failure_example :
    cParallelIntegrate parallelExampleExpDt parallelExampleFailA parallelExampleFailD = none := by
  native_decide

end DeepWiki.SymbolicIntegration
