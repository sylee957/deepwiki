import DeepWiki.SymbolicIntegration.ComputableGeneralDerivation
import DeepWiki.SymbolicIntegration.ComputableGeneralRationalSolve
import DeepWiki.SymbolicIntegration.ComputableFuelFreeDiophantine

/-! # DERIVING the LOG ARGUMENT `u` (with `∫(integrand) dx = log u`) for an ARBITRARY plane curve, PRINCIPAL
case, by undetermined coefficients over the integral basis through the general derivation `afDeriv` (Trager,
*Integration of Algebraic Functions*, Ch. 5, the logarithmic-part algorithm)

`ComputableGeneralRationalSolve` derived the **rational part** `v` (with `afDeriv f v = integrand`) for an
arbitrary curve `K(x)[y]/(f)` by a `K`-linear solve over the integral basis — the general-curve analogue of
the hyperelliptic `radLogArgSolve`/`radIntegrateRational`. This file does the same for the **log part**: it
**derives** the log argument `u` (with `∫(integrand) dx = log u`) by a `K`-linear solve, the general-curve
analogue of the hyperelliptic `radLogArgSolveG` (which solves `radDeriv(N)·D − N·D' − radMul(N,integrand)·D =
0` over the radical carrier), now lifted from `radDeriv` to the GENERAL derivation `afDeriv`.

**KEY: the log part's PRINCIPAL case is ALSO a linear solve — which SIDESTEPS the general torsion.** Just as
the rational part is `afDeriv f u = integrand` (linear in `u`), the log part is the **log-derivative
condition**

  **`afDeriv f u = afMul f u integrand`**   (in `K(x)[y]/(f)`),

i.e. `D(log u) = afDeriv(u)/u = integrand`. This is **LINEAR in `u`**: `afDeriv f` is `K`-linear and `afMul f
· integrand` is `K`-linear, so `afDeriv f u − afMul f u integrand` is a `K`-linear function of `u`. With the
ansatz

  **`u = Σ_{i,j} c_{ij}·xʲ·wᵢ`**   over the integral basis `[w₁,…,wₙ]` (`integralBasis f`), degree `j ≤ degBound`,

the condition is a finite **homogeneous** `K`-linear system whose columns are the per-monomial residuals
`afDeriv f (xʲ wᵢ) − afMul f (xʲ wᵢ) integrand`. A nonzero **kernel vector** of that system **is** `u` (up to
the `log(c·u) = log c + log u` scalar freedom). Solving it by `kernelBasisG` derives `u` for a NON-radical
(non-hyperelliptic) curve, the **PRINCIPAL case** — a bounded-degree `u` exists. The general
divisor-class-group **torsion** (the residue divisor is `m`-torsion with `m > 1`, needing `(1/m)log`) is the
NON-principal case ⟹ no bounded `u` ⟹ deferred (the genuine sub-arc, documented at the end). The linear solve
**sidesteps** it: when `u` exists at this `degBound`, the kernel is nonzero and we read it off.

* **`afLogResidual fuel f integrand u`** — the log-derivative residual `afDeriv f u − afMul f u integrand` in
  `K(x)[y]/(f)` (vanishes iff `∫(integrand) = log u`). The lifted `radDeriv(N)·D − N·D' − radMul(N,integrand)·D`
  at `D = 1` (`u = N`), from `radDeriv` to `afDeriv`.
* **`afLogColumns …`** — the residual columns `[afDeriv f (xʲ wᵢ) − afMul f (xʲ wᵢ) integrand …]` (no forced
  `−integrand` column — the system is homogeneous in `u` directly, unlike `afRationalSolve`'s).
* **`afLogMatrix …`** — the `K`-matrix (clear each power-basis coordinate to numerators over `K`, read off
  `x`-power coefficients), one row per coordinate per `x`-power (`afRatMatrix`'s extraction).
* **`afLogArgSolve fuel f basis degBound integrand`** — solve the system (`kernelBasisG`), take the first
  nonzero kernel vector, reassemble `u = Σ_{ij} c_{ij} xʲ wᵢ`; `none` if the kernel is trivial.

**Validations** (`native_decide`):
* **★ DERIVE the log argument on the NON-HYPERELLIPTIC curve `y³ − x² − 1`** (`afLogArgSolve_nonhyper_*`):
  round-trip — pick `u = y` on `f = y³ − x² − 1`, set `integrand = afDeriv f u / u` (verified via
  `afDeriv f u = afMul f u integrand`), then `afLogArgSolve` recovers `u` (up to scale) and the log-derivative
  certificate `afLogResidual = 0` confirms `∫ integrand = log u`. `u` is the solver's OUTPUT.
* **Hyperelliptic conservativity**: on `y² = x²+1`, `afLogArgSolve` recovers the arcsinh `u = x + y` for
  `∫ dx/√(x²+1)` — the same answer `radLogArgSolveG` gives, the general solve specializing back to the radical
  case.
* **The `v + Σ log u` stretch**: `afIntegrateAlgebraic` wires `afRationalSolve` + `afLogArgSolve` into a
  general-curve `∫ = v + log u` (principal case), the general analogue of `cIntegrateAlgebraic`.

**The engine now DERIVES the LOG argument for general (non-hyperelliptic) curves (PRINCIPAL case)** — the
log-derivative condition `afDeriv f u = afMul f u integrand` is `K`-linear in `u`, solved by `kernelBasisG`
over the integral basis through the general derivation `afDeriv`, sidestepping the general divisor-class-group
torsion (the NON-principal case). The non-principal/torsion continuation (general divisors + good reduction)
is documented at the end as the deferred BIG piece. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CPolyG

/-! ### The log-derivative residual `afDeriv f u − afMul f u integrand` (`afLogResidual`)

`∫(integrand) dx = log u` holds iff `D(log u) = afDeriv(u)/u = integrand`, i.e. — multiplying by `u`, which is
division-free — `afDeriv f u = afMul f u integrand` in `K(x)[y]/(f)`. The **residual** `afDeriv f u − afMul f u
integrand` is the element of the carrier whose vanishing (all `n = deg f` power-basis coordinates zero as
`K(x)` elements) certifies the log integral. This is the hyperelliptic `radLogResidualG`'s
`radDeriv(N)·D − N·D' − radMul(N,integrand)·D` lifted from the diagonal `radDeriv` to the general `afDeriv` at
`D = 1` (so `u = N`, `D' = 0`): `radDeriv(N) − radMul(N,integrand) ↦ afDeriv(u) − afMul(u,integrand)`. The
residual is `K`-LINEAR in `u` (both `afDeriv f` and `afMul f · integrand` are `K`-linear), the property the
log-argument solve turns on. -/

/-- **The log-derivative residual** `afLogResidual fuel f integrand u = afDeriv f u − afMul f u integrand` in
`K(x)[y]/(f)`, whose vanishing (`cisZeroG`) certifies `∫(integrand) dx = log u` (since `D(log u)·u =
afDeriv(u)`, the division-free equality `afDeriv(u) = afMul(u, integrand)`). The general-curve analogue of the
hyperelliptic log-derivative certificate `radDeriv(N) − radMul(N, integrand)` (at `D = 1`), lifted from the
diagonal `radDeriv` to the GENERAL derivation `afDeriv`. `K`-linear in `u`; fuel `≥ deg f` feeds `afDeriv`'s
`f_y`-inversion. -/
def afLogResidual (fuel : ℕ) (f integrand u : CPolyG (QFunNZG ℚ)) : CPolyG (QFunNZG ℚ) :=
  csubG (afDeriv fuel f u) (afMul f u integrand)

/-- **The log-derivative certificate as a `Bool`** `afIsLogIntegral fuel f integrand u` — `true` iff the
residual `afLogResidual fuel f integrand u` vanishes, i.e. `∫(integrand) dx = log u` in `K(x)[y]/(f)`. The
general-curve analogue of `radIsLogIntegral`; the check the round-trip derivations use to confirm the derived
`u`. -/
def afIsLogIntegral (fuel : ℕ) (f integrand u : CPolyG (QFunNZG ℚ)) : Bool :=
  cisZeroG (afLogResidual fuel f integrand u)

/-! ### The residual columns `[afDeriv f (xʲ wᵢ) − afMul f (xʲ wᵢ) integrand …]` (`afLogColumns`)

By `K`-linearity of `u ↦ afLogResidual fuel f integrand u`, for `u = Σ c_{ij} xʲ wᵢ` the residual is
`Σ_{ij} c_{ij}·(afDeriv f (xʲ wᵢ) − afMul f (xʲ wᵢ) integrand)`. So the **homogeneous** system `Σ_k c_k·colₖ =
0` has columns `colₖ = afLogResidual` evaluated on the ansatz monomials `afRatMonomials basis degBound`
(`xʲ wᵢ`). Unlike the rational-part solve (which carries a forced `−integrand` column for the inhomogeneous
RHS), the log system is homogeneous in `u` **directly** — the kernel vector IS `u` (no RHS normalization,
hence the `log(c·u)` scalar freedom). Each column is a `CPolyG (QFunNZG ℚ)` (an element of `K(x)[y]/(f)`, ≤ `n`
power-basis coordinates over `K(x)`). -/

/-- **The residual columns of the log-argument system** `afLogColumns fuel f basis degBound integrand`: the
per-monomial log-derivative residuals `afLogResidual fuel f integrand (xʲ wᵢ) = afDeriv f (xʲ wᵢ) − afMul f
(xʲ wᵢ) integrand`, one per `afRatMonomials basis degBound` entry. A nonzero **kernel vector** `c` of the
resulting system gives `u = Σ_k c_k·(xʲ wᵢ)` solving the log-derivative condition `afDeriv f u = afMul f u
integrand`. NO forced `−integrand` column (the system is homogeneous in `u`); each column is a `CPolyG
(QFunNZG ℚ)`; fuel feeds `afDeriv`'s `f_y`-inversion. -/
def afLogColumns (fuel : ℕ) (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ)))
    (degBound : ℕ) (integrand : CPolyG (QFunNZG ℚ)) : List (CPolyG (QFunNZG ℚ)) :=
  (afRatMonomials basis degBound).map (afLogResidual fuel f integrand)

/-! ### The `K`-matrix of the log-argument system (`afLogMatrix`)

Each residual column is a `CPolyG (QFunNZG ℚ)` whose coordinates `r_{ik} ∈ K(x)` are fractions `num/den`. The
equality `Σ_k c_k r_{ik} = 0` (per power-basis coordinate `i ∈ [0, n)`) becomes `K = ℚ`-linear by clearing
each coordinate to numerators over a common denominator across the columns and reading off `x`-power
coefficients — exactly `afRatMatrix`'s extraction, now on the homogeneous log columns (no forced RHS column).
One **row per coordinate `i` per `x`-power**, one **column per residual column**. -/

/-- **The `ℚ`-matrix of the log-argument linear system** `afLogMatrix fuel f basis degBound integrand =
(rows, nCols)`. For each power-basis coordinate `i ∈ [0, n)` (`n = deg f`) and each residual column `k`
(`afLogColumns`), read the `K(x)` entry `r_{ik}` and clear it to the numerator `P_{ik} = num(r_{ik})·∏_{l≠k}
den(r_{il}) ∈ ℚ[x]` (common denominator across the columns of that coordinate). One row per `x`-power of the
`P_{i·}`; entry `(row, k)` is the `ℚ`-coefficient of that `x`-power in `P_{ik}`. A kernel vector `c` solves
`Σ_k c_k r_{ik} = 0` for all `i` ⟹ `afDeriv f (Σ c_{ij} xʲ wᵢ) = afMul f (Σ c_{ij} xʲ wᵢ) integrand`. The
log analogue of `afRatMatrix` (homogeneous in `u`: the columns are the log residuals, no forced
`−integrand`). -/
def afLogMatrix (fuel : ℕ) (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ)))
    (degBound : ℕ) (integrand : CPolyG (QFunNZG ℚ)) : List (List ℚ) × ℕ :=
  let cols := afLogColumns fuel f basis degBound integrand
  let nCols := cols.length
  let n := cdegG f
  let rowsForCoord : ℕ → List (List ℚ) := fun i =>
    let entryOf : ℕ → QFunNZG ℚ := fun k => (cols[k]!).getD i CField.zero
    let nums : List (CPolyG ℚ) := (List.range nCols).map (fun k => cnormG (entryOf k).1.1)
    let dens : List (CPolyG ℚ) := (List.range nCols).map (fun k => cnormG (entryOf k).1.2)
    let cleared : List (CPolyG ℚ) := (List.range nCols).map (fun k =>
      let prod := (List.range nCols).foldl (fun acc l =>
        if l = k then acc else cmulG acc (dens[l]!)) [(1 : ℚ)]
      cnormG (cmulG (nums[k]!) prod))
    let width := (cleared.foldl (fun acc p => max acc p.length) 0)
    (List.range width).map (fun r =>
      (List.range nCols).map (fun k => (cleared[k]!).getD r 0))
  let allRows := (List.range n).flatMap rowsForCoord
  let nonzero := allRows.filter (fun row => row.any (fun a => a ≠ 0))
  (nonzero, nCols)

/-! ### ★ Solve for the log argument `u` (`afLogArgSolve`)

Solve the homogeneous `ℚ`-system `afLogMatrix` for a nonzero kernel vector (`kernelBasisG`) and reassemble
`u = Σ_{ij} c_{ij}·xʲ·wᵢ` from its coordinates. Unlike the rational-part solve, there is **no RHS coordinate
to normalize** — the kernel vector *is* `u` (the system is homogeneous in `u`), so any nonzero kernel vector
is a solution, up to the `log(c·u) = log c + log u` scalar freedom. The **PRINCIPAL case** is exactly when a
nonzero kernel vector exists at this `degBound` (a bounded-degree `u`); `none` signals the trivial kernel
(no log argument of this shape at this `degBound` — the non-principal/torsion case needs the deferred divisor
machinery). -/

/-- **★ DERIVE the log argument `u`** `afLogArgSolve fuel f basis degBound integrand = some u` — the element
`u = Σ_{i,j} c_{ij}·xʲ·wᵢ` over the integral basis `basis = [w₀,…,w_{m−1}]` (degree `j ≤ degBound`, `c_{ij} ∈
ℚ`) with **`∫(integrand) dx = log u`**, i.e. **`afDeriv f u = afMul f u integrand`**, **computed** by the
`K`-linear solve. Builds the `ℚ`-matrix `afLogMatrix` (undetermined coefficients on the ansatz monomials `xʲ
wᵢ`, columns the log-derivative residuals `afDeriv f (xʲ wᵢ) − afMul f (xʲ wᵢ) integrand`), finds the **first
nonzero kernel-basis vector** (`kernelBasisG`, then `List.find?`), and reassembles `u`. Returns `none` when
the kernel is trivial (no log argument of this shape at this `degBound` — the PRINCIPAL case fails, signalling
the deferred non-principal/torsion case). The general-curve analogue of `radLogArgSolveG` — the whole linear
solve runs over `K`, using `afDeriv` (the general derivation) and the integral basis, so it DERIVES the LOG
argument for an ARBITRARY plane curve, not just the hyperelliptic radical case. `u` is the solver's OUTPUT,
up to the `log(c·u)` scalar freedom. -/
def afLogArgSolve (fuel : ℕ) (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ)))
    (degBound : ℕ) (integrand : CPolyG (QFunNZG ℚ)) : Option (CPolyG (QFunNZG ℚ)) :=
  let (rows, nCols) := afLogMatrix fuel f basis degBound integrand
  let kers := kernelBasisG nCols rows
  -- the kernel vector IS u (the system is homogeneous in u); take the first nonzero one
  match kers.find? (fun c => c.any (fun a => a ≠ 0)) with
  | none => none
  | some c =>
    let monos := afRatMonomials basis degBound
    let u : CPolyG (QFunNZG ℚ) :=
      (List.range monos.length).foldl (fun acc idx =>
        let coeff : ℚ := c.getD idx 0
        caddG acc (cscaleG (qxOfNum [coeff]) (monos.getD idx []))) ([] : CPolyG (QFunNZG ℚ))
    some u

/-! ### ★ DERIVE the log argument on the NON-HYPERELLIPTIC curve `y³ − x² − 1` (`native_decide`)

The curve `f = y³ − x² − 1` (`gcLogF`), degree 3 in `y`, **non-hyperelliptic** (degree `> 2`), a genuine
trigonal curve (not the pure radical `y³ = x²`). To produce a clean log integral we **round-trip**: pick a
carrier element `u` (here `u = y`, the generator), form `integrand = afDeriv f u / u` — concretely we use the
log-derivative form, certifying it by `afDeriv f u = afMul f u integrand` — then `afLogArgSolve` recovers `u`
(up to scale) from `integrand` and the certificate `afLogResidual = 0` confirms `∫ integrand = log u`. `u` is
the solver's OUTPUT, derived by the `K`-linear log-derivative solve over the integral basis. -/

/-- The non-hyperelliptic curve `f = y³ − x² − 1 ∈ ℚ(x)[y]` (`a₀ = −(x²+1)`, `a₁ = a₂ = 0`, monic, degree 3),
the `CPolyG (QFunNZG ℚ)` `[−(x²+1), 0, 0, 1]`. A genuine trigonal curve (not the pure radical `y³ = x²`); the
log-argument solve derives `u` for a log integral on it. -/
def gcLogF : CPolyG (QFunNZG ℚ) :=
  [qxOfNum [-1, 0, -1], CField.zero, CField.zero, CField.one]

/-- The integral basis of `y³ − x² − 1` (the ansatz basis for the log-argument solve). For this curve the
discriminant `−4·0³ − 27·(x²+1)² = −27(x²+1)²` has no bad prime making the order non-maximal at a finite
linear prime, so the integral basis is the power basis `[1, y, y²]`. -/
def gcLogBasis : List (CPolyG (QFunNZG ℚ)) := integralBasis gcLogF

/-- The chosen log argument `u = y` (the generator `afBasisElem 1 = [0, 1]`) of `ℚ(x)[y]/(y³ − x² − 1)` — the
round-trip target whose `integrand = afDeriv f y / y` the solver must recover `y` from. -/
def gcLogU : CPolyG (QFunNZG ℚ) := afBasisElem 1

/-- The log-derivative integrand `afDeriv f u / u` for `u = y` on `y³ − x² − 1`, computed as `afMul f
(afDeriv f y) (y⁻¹ mod f)` where `y⁻¹ ≡ y²/(x²+1) mod f` (since `y·y²/(x²+1) = y³/(x²+1) = (x²+1)/(x²+1) = 1`).
So `integrand = afDeriv(y)·y²/(x²+1)`. By construction `∫ integrand dx = log y`, and `afDeriv f y = afMul f y
integrand` (the log-derivative condition). The solver's INPUT; `y` is what it recovers. -/
def gcLogIntegrand : CPolyG (QFunNZG ℚ) :=
  afMul gcLogF (afDeriv 8 gcLogF gcLogU)
    [CField.zero, CField.zero, qxOfFrac [1] [1, 0, 1] (by decide)]

-- Sanity print: the log-derivative integrand for `∫ afDeriv(y)/y dx = log y` on `y³ − x² − 1`.
#eval (gcLogIntegrand.map (fun z => ((z.1.1 : List ℚ), (z.1.2 : List ℚ))))

/-- **The integrand really is the log-derivative of `u = y`** (`native_decide`): `afDeriv f y = afMul f y
integrand` on `y³ − x² − 1`, i.e. `afLogResidual` of `u = y` vanishes — confirming `gcLogIntegrand` is a clean
log integrand `∫ = log y` (the round-trip target is well-posed before the solve recovers it). -/
theorem gcLog_integrand_is_logderiv :
    afIsLogIntegral 8 gcLogF gcLogIntegrand gcLogU = true := by native_decide

/-- The DERIVED log argument of `∫ (afDeriv(y)/y) dx` on `y³ − x² − 1` — `afLogArgSolve` over the integral
basis, ansatz degree `1`. Expected `u = y` (up to a nonzero scalar; the `log(c·y)` freedom). -/
def gcLogSolvedU : Option (CPolyG (QFunNZG ℚ)) :=
  afLogArgSolve 8 gcLogF gcLogBasis 1 gcLogIntegrand

-- Sanity print: the DERIVED log argument `u` for `∫ afDeriv(y)/y dx` (expected a scalar multiple of `y`).
#eval (gcLogSolvedU.map (fun u => u.map (fun z => ((z.1.1 : List ℚ), (z.1.2 : List ℚ)))))

/-- **★★ DERIVE the log argument `u` (a multiple of `y`) for `∫ (afDeriv(y)/y) dx = log y` on the
NON-HYPERELLIPTIC `y³ − x² − 1`** (`native_decide`): the log argument is the solver's **OUTPUT** — `afLogArgSolve`
over the integral basis `[1, y, y²]` (ansatz degree `1`) returns `some u`, the derived `u` passes the
log-derivative certificate **`afDeriv f u = afMul f u integrand`** (`afIsLogIntegral`), AND `u` is a nonzero
scalar multiple of `y` (matching the round-trip target up to the `log(c·u)` scalar freedom). DERIVED, not
verified-forward: the `K`-linear log-derivative solve `Σ c_{ij} (afDeriv (xʲ wᵢ) − afMul (xʲ wᵢ) integrand) =
0`, through the GENERAL derivation `afDeriv`, recovers the LOG argument for a NON-hyperelliptic curve,
sidestepping the divisor-class-group torsion (PRINCIPAL case). Checked by `afIsLogIntegral` on the derived `u`
AND that `u = [0, c]` with `c ≠ 0`. -/
theorem afLogArgSolve_nonhyper_intLogY :
    (gcLogSolvedU.map (fun u =>
      afIsLogIntegral 8 gcLogF gcLogIntegrand u
      && cisZeroG [u.getD 0 CField.zero]
      && !cisZeroG [u.getD 1 CField.zero]
      && cisZeroG [u.getD 2 CField.zero])) = some true := by native_decide

/-! ### ★ A second non-hyperelliptic log argument: `u = y² + x` on `y³ − x² − 1` (`native_decide`)

A `y²`-mixing target on the same trigonal curve. Take `u = y² + x` (`[x, 0, 1]`), form its log-derivative
integrand `afDeriv f u / u`, and recover `u` (up to scale). Here `u⁻¹` is a genuine field inverse in
`K(x)[y]/(f)` (via the Bezout cofactor `cdiophantineGWf u f [1]`), so the integrand mixes all three power-basis
coordinates — a stronger test of the `K`-linear log solve than the pure-`y` generator. -/

/-- The second log-argument target `u = y² + x` (`[x, 0, 1]`) on `y³ − x² − 1` — a `y²`-mixing element whose
log-derivative integrand the solver must recover `u` from. -/
def gcLogU2 : CPolyG (QFunNZG ℚ) := [qxOfNum [0, 1], CField.zero, CField.one]

/-- The field inverse `u⁻¹ mod f` of `u = y² + x` on `y³ − x² − 1` — the first Bezout cofactor of `s·u + t·f =
1` (`cdiophantineGWf u f [1]`), valid since `u` is a unit of `K(x)[y]/(f)` (coprime to the irreducible `f`).
Used to build the log-derivative integrand `afDeriv(u)·u⁻¹`. -/
def gcLogU2Inv : CPolyG (QFunNZG ℚ) := (cdiophantineGWf gcLogU2 gcLogF [CField.one]).1

/-- The log-derivative integrand `afDeriv f u / u = afMul f (afDeriv f u) u⁻¹` for `u = y² + x` on `y³ − x² −
1`. By construction `∫ integrand dx = log(y² + x)` and `afDeriv f u = afMul f u integrand`. The solver's
INPUT; `y² + x` (up to scale) is what it recovers. -/
def gcLogIntegrand2 : CPolyG (QFunNZG ℚ) :=
  afMul gcLogF (afDeriv 8 gcLogF gcLogU2) gcLogU2Inv

/-- **The second integrand is the log-derivative of `u = y² + x`** (`native_decide`): `afDeriv f u = afMul f u
integrand` on `y³ − x² − 1`, i.e. `afLogResidual` of `u = y² + x` vanishes — the round-trip target `∫ = log(y²
+ x)` is well-posed. -/
theorem gcLog2_integrand_is_logderiv :
    afIsLogIntegral 8 gcLogF gcLogIntegrand2 gcLogU2 = true := by native_decide

/-- The DERIVED log argument of `∫ (afDeriv(y²+x)/(y²+x)) dx` on `y³ − x² − 1` — `afLogArgSolve` over the
integral basis, ansatz degree `1`. Expected `u = y² + x` (up to a nonzero scalar). -/
def gcLogSolvedU2 : Option (CPolyG (QFunNZG ℚ)) :=
  afLogArgSolve 8 gcLogF gcLogBasis 1 gcLogIntegrand2

-- Sanity print: the DERIVED log argument `u` for the second target (a scalar multiple of `y² + x`).
#eval (gcLogSolvedU2.map (fun u => u.map (fun z => ((z.1.1 : List ℚ), (z.1.2 : List ℚ)))))

/-- **★★ DERIVE the log argument `u` (a multiple of `y² + x`) for `∫ (afDeriv(y²+x)/(y²+x)) dx = log(y²+x)` on
`y³ − x² − 1`** (`native_decide`): the second non-hyperelliptic log argument, a `y²`-mixing target — the
solver's **OUTPUT**, `afLogArgSolve` over the integral basis `[1, y, y²]` (ansatz degree `1`) returns `some u`
that passes the log-derivative certificate **`afDeriv f u = afMul f u integrand`** (`afIsLogIntegral`) AND is a
nonzero scalar multiple of `y² + x` (i.e. `u = c·(y² + x)` for `c ≠ 0`: `u₂ ≠ 0`, `u₁ = 0`, `u₀ = c·x` so
`u₀·1 = u₂·x`). DERIVED through the GENERAL `afDeriv`, a full three-coordinate target. Checked by
`afIsLogIntegral` on `u` AND `u = c·(y²+x)`. -/
theorem afLogArgSolve_nonhyper_intLogU2 :
    (gcLogSolvedU2.map (fun u =>
      afIsLogIntegral 8 gcLogF gcLogIntegrand2 u
      && !cisZeroG [u.getD 2 CField.zero]
      && cisZeroG [u.getD 1 CField.zero]
      && cisZeroG (csubG [u.getD 0 CField.zero]
            [CField.mul (u.getD 2 CField.zero) (qxOfNum [0, 1])]))) = some true := by native_decide

/-! ### Hyperelliptic conservativity: `afLogArgSolve` recovers arcsinh `u = x + y` on `y² = x²+1`
(`native_decide`)

The general solve must reproduce the hyperelliptic log argument on a radical curve `y² = ρ`. Take `f = y² −
(x²+1)` (`y = √(x²+1)`, genus 0), `∫ dx/√(x²+1) = log(x + y)` (arcsinh). The integrand `1/y` lifts into the
carrier as `y/(x²+1)` (since `1/y = y/y² = y/(x²+1)`), i.e. `[0, 1/(x²+1)]`. `afLogArgSolve` over the power
basis `[1, y]` (ansatz degree `1`) derives `u = x + y` (up to scale) — the SAME argument `radLogArgSolveG`
gives in `ComputableRadicalLogArgGeneric`. The general-curve log solve specializes back to the hyperelliptic
case. -/

/-- The hyperelliptic curve `f = y² − (x²+1) ∈ ℚ(x)[y]` (`y = √(x²+1)`, genus 0), the `CPolyG (QFunNZG ℚ)`
`[−(x²+1), 0, 1]` — the arcsinh case for the conservativity check (the same radicand as
`ComputableRadicalLogArgGeneric`'s `genArgRhoArcsinh`). -/
def gcHypLogF : CPolyG (QFunNZG ℚ) :=
  [qxOfNum [-1, 0, -1], CField.zero, CField.one]

/-- The integral basis of `y² = x²+1` (the power basis `[1, y]`, no finite poles). -/
def gcHypLogBasis : List (CPolyG (QFunNZG ℚ)) := integralBasis gcHypLogF

/-- The integrand `1/√(x²+1) = 1/y` lifted into `ℚ(x)[y]/(y² − (x²+1))` as `[0, 1/(x²+1)] = y/(x²+1)` (since
`1/y = y/y² = y/(x²+1)`), the `afDeriv`-carrier form of `∫ dx/√(x²+1)`. The arcsinh integrand; `afLogArgSolve`
derives `u = x + y`. -/
def gcHypLogIntegrand : CPolyG (QFunNZG ℚ) :=
  [CField.zero, qxOfFrac [1] [1, 0, 1] (by decide)]

/-- The DERIVED log argument of `∫ dx/√(x²+1)` on `y² = x²+1` — `afLogArgSolve` over the power basis `[1, y]`,
ansatz degree `1`. Expected `u = x + y` (up to a nonzero scalar). -/
def gcHypLogSolvedU : Option (CPolyG (QFunNZG ℚ)) :=
  afLogArgSolve 8 gcHypLogF gcHypLogBasis 1 gcHypLogIntegrand

-- Sanity print: the DERIVED arcsinh log argument `u` (a scalar multiple of `x + y`).
#eval (gcHypLogSolvedU.map (fun u => u.map (fun z => ((z.1.1 : List ℚ), (z.1.2 : List ℚ)))))

/-- **★ Hyperelliptic conservativity: `afLogArgSolve` recovers arcsinh `u = x + y` for `∫ dx/√(x²+1)` on `y² =
x²+1`** (`native_decide`): the general-curve log solve, on a radical (hyperelliptic) curve, reproduces the
hyperelliptic log argument — `afLogArgSolve` over the power basis `[1, y]` returns `some u` that passes the
log-derivative certificate **`afDeriv f u = afMul f u integrand`** (`afIsLogIntegral`, `∫ dx/√(x²+1) = log u`)
AND is a nonzero scalar multiple of `x + y` (`u = c·(x + y)`: `u₁ ≠ 0`, `u₀ = c·x` so `u₀ = u₁·x`). DERIVED
through the GENERAL `afDeriv`, agreeing with the arcsinh `u = x + y` that `radLogArgSolveG` gives: the
general-curve log solve specializes back to the radical case. Checked by `afIsLogIntegral` on `u` AND `u =
c·(x+y)`. -/
theorem afLogArgSolve_hyper_arcsinh :
    (gcHypLogSolvedU.map (fun u =>
      afIsLogIntegral 8 gcHypLogF gcHypLogIntegrand u
      && !cisZeroG [u.getD 1 CField.zero]
      && cisZeroG (csubG [u.getD 0 CField.zero]
            [CField.mul (u.getD 1 CField.zero) (qxOfNum [0, 1])]))) = some true := by native_decide

/-! ### ★ STRETCH: a general-curve `∫ = v + log u` (principal case) — `afIntegrateAlgebraic`

Wiring `afRationalSolve` (the rational part `v` with `afDeriv f v = ratIntegrand`) and `afLogArgSolve` (the log
argument `u` with `afDeriv f u = afMul f u logIntegrand`) into a single general-curve integration, the general
analogue of `cIntegrateAlgebraic`. Given an integrand presented as a rational part `ratIntegrand` plus a
log-derivative part `logIntegrand`, return `(v, u)` with `∫ (ratIntegrand + logIntegrand) dx = v + log u`
(PRINCIPAL case: both solves succeed at the given `degBound`). This is the skeleton — the full algorithm would
*split* a single integrand into its rational and log-derivative parts (the Hermite/residue reduction); here we
take the split as input, exhibiting that once split, BOTH parts are linear solves through the same general
derivation `afDeriv`. -/

/-- **★ A general-curve `∫ = v + log u` (principal case)** `afIntegrateAlgebraic fuel f basis degBound
ratIntegrand logIntegrand = some (v, u)`: the rational part `v` (`afRationalSolve`, `afDeriv f v =
ratIntegrand`) and the log argument `u` (`afLogArgSolve`, `afDeriv f u = afMul f u logIntegrand`), so
`∫ (ratIntegrand + logIntegrand) dx = v + log u`. `none` if either solve fails at this `degBound`. The general
analogue of `cIntegrateAlgebraic` — both parts a `K`-linear solve over the integral basis through the GENERAL
derivation `afDeriv` (the rational part inhomogeneous with a forced `−ratIntegrand` column, the log part
homogeneous in `u`), sidestepping the divisor-class-group torsion (PRINCIPAL case). The integrand-splitting
(Hermite/residue reduction) into rational + log-derivative parts is the deferred front-end; once split, this
exhibits both parts as linear solves. -/
def afIntegrateAlgebraic (fuel : ℕ) (f : CPolyG (QFunNZG ℚ)) (basis : List (CPolyG (QFunNZG ℚ)))
    (degBound : ℕ) (ratIntegrand logIntegrand : CPolyG (QFunNZG ℚ)) :
    Option (CPolyG (QFunNZG ℚ) × CPolyG (QFunNZG ℚ)) :=
  match afRationalSolve fuel f basis degBound ratIntegrand,
        afLogArgSolve fuel f basis degBound logIntegrand with
  | some v, some u => some (v, u)
  | _, _ => none

/-- The rational-part integrand `∫ y dx = (3/5)xy` on the cuspidal cubic `y³ = x²` (the `gcuspCubicY = y`
integrand from `ComputableGeneralRationalSolve`), the rational summand of the combined `∫ = v + log u`
target. -/
def gcCombineRatIntegrand : CPolyG (QFunNZG ℚ) := gcuspCubicY

/-- The log-derivative integrand `afDeriv f y / y = afMul f (afDeriv f y) (y²/x²)` for `u = y` on the cuspidal
cubic `y³ = x²` (`y⁻¹ ≡ y²/x² mod f` since `y·y²/x² = y³/x² = x²/x² = 1`), the log summand of the combined `∫ =
v + log u` target. By construction `∫ (afDeriv f y / y) dx = log y`. -/
def gcCombineLogIntegrand : CPolyG (QFunNZG ℚ) :=
  afMul gcuspCubicF (afDeriv 8 gcuspCubicF gcuspCubicY)
    [CField.zero, CField.zero, qxOfFrac [1] [0, 0, 1] (by decide)]

/-- The combined `∫ = v + log u` on the cuspidal cubic `y³ = x²` — `afIntegrateAlgebraic` with rational part
`∫ y dx` (→ `v = (3/5)xy`) and log part `∫ afDeriv(y)/y dx` (→ `u` a multiple of `y`), ansatz degree `2`. -/
def gcCombineSolved : Option (CPolyG (QFunNZG ℚ) × CPolyG (QFunNZG ℚ)) :=
  afIntegrateAlgebraic 8 gcuspCubicF gcuspCubicBasis 2 gcCombineRatIntegrand gcCombineLogIntegrand

-- Sanity print: the combined (v, u) for `∫ (y + afDeriv(y)/y) dx = v + log u` on `y³ = x²`.
#eval (gcCombineSolved.map (fun p =>
  (p.1.map (fun z => ((z.1.1 : List ℚ), (z.1.2 : List ℚ))),
   p.2.map (fun z => ((z.1.1 : List ℚ), (z.1.2 : List ℚ))))))

/-- **★ STRETCH: a general-curve `∫ (y + afDeriv(y)/y) dx = v + log u` on the cuspidal cubic `y³ = x²`**
(`native_decide`): `afIntegrateAlgebraic` wires `afRationalSolve` + `afLogArgSolve` into a single integration
— it returns `some (v, u)` with the rational part `v = (3/5)xy` (`afDeriv f v = y`) AND the log argument `u` a
nonzero multiple of `y` (`afDeriv f u = afMul f u logIntegrand`, `∫ afDeriv(y)/y = log y`). So `∫ (y +
afDeriv(y)/y) dx = (3/5)xy + log y`, both parts DERIVED by `K`-linear solves through the GENERAL derivation
`afDeriv` (PRINCIPAL case), the general analogue of `cIntegrateAlgebraic`. Checked by `afDeriv f v − y`
vanishing, `afIsLogIntegral` on `u`, and `u` a nonzero multiple of `y`. -/
theorem afIntegrateAlgebraic_cuspCubic_combine :
    (gcCombineSolved.map (fun p =>
      let v := p.1
      let u := p.2
      cisZeroG (csubG (afDeriv 8 gcuspCubicF v) gcCombineRatIntegrand)
      && cisZeroG (csubG v [CField.zero, qxOfNum [0, 3/5]])
      && afIsLogIntegral 8 gcuspCubicF gcCombineLogIntegrand u
      && cisZeroG [u.getD 0 CField.zero]
      && !cisZeroG [u.getD 1 CField.zero])) = some true := by native_decide

/-! ### The deferred BIG piece: the NON-principal / torsion case (general divisors + good reduction)

`afLogArgSolve` now **DERIVES** the log argument `u` (with `∫(integrand) dx = log u`) for an arbitrary plane
curve `K(x)[y]/(f)` — by undetermined coefficients `u = Σ c_{ij} xʲ wᵢ` over the integral basis, the
log-derivative condition `afDeriv f u = afMul f u integrand` made a finite homogeneous `K`-linear system
(columns `afDeriv f (xʲ wᵢ) − afMul f (xʲ wᵢ) integrand`) solved by `kernelBasisG`. This is the general-curve
analogue of the hyperelliptic `radLogArgSolveG` — the SAME linear solve, lifted from the diagonal `radDeriv` to
the general derivation `afDeriv` and the integral basis. The validated derivations (the log argument `u ∝ y`
and `u ∝ y² + x` on the non-hyperelliptic `y³ − x² − 1`; the arcsinh `u ∝ x + y` on the hyperelliptic `y² =
x²+1`; the combined `∫ = v + log u` on the cuspidal cubic) show the log argument as the solver's **OUTPUT**.

**Why the PRINCIPAL case is a linear solve, and what the NON-principal case needs.** The log-derivative
condition `afDeriv f u = afMul f u integrand` is linear in `u` because `afDeriv f` and `afMul f · integrand`
are `K`-linear; so when a **bounded-degree** `u` exists (the PRINCIPAL case — the residue divisor of the
integrand is *principal*, the divisor of an actual function `u` on the curve), the kernel of the cleared system
is nonzero and `afLogArgSolve` reads `u` off. This **SIDESTEPS** the general divisor-class-group torsion: we
never form the divisor or test its order; we directly solve for `u`.

The deferred BIG piece is the **NON-principal / torsion case**. When the residue divisor `δ = Σ rₚ·(P)` (the
integrand's simple-pole residues, `genResidueResultant`/`ComputableGeneralResidues`) is **not** principal but
some `K`-multiple `m·δ` (`m > 1`) is — i.e. `δ` is `m`-**torsion** in the Jacobian `Pic⁰(C)` — the elementary
integral has a `(1/m)·log u` term where `u` is the function with `div(u) = m·δ`, and **no** bounded-degree `u`
with `div(u) = δ` exists, so `afLogArgSolve` returns `none`. Deciding this needs:

1. **The residue divisor** `δ` of the integrand over the general carrier (the simple-pole residues, finite +
   at infinity), as a formal sum of places — the general analogue of `ComputableHyperellipticDivisor`.

2. **Divisor-class arithmetic in `Pic⁰(C)`** for an arbitrary curve — reduced divisors, addition (the general
   Cantor composition / a Hess-style Riemann–Roch reduction over `K[x]`), and the **order test** (is `m·δ`
   principal for some `m`?), the general analogue of `ComputableCantorComposition` / `ComputableDivisorOrder` /
   `ComputablePrincipalGenerator` / `ComputableTorsionLogTerm`, which carry exactly this for the **hyperelliptic**
   Jacobian. The torsion order `m` and the principal generator `u` of `m·δ` give the `(1/m)log u` term.

3. **Good reduction** (Trager Ch. 6 / Davenport): to decide torsion over `ℚ`, reduce the curve mod a good
   prime `p`, compute the (finite) group order of `Pic⁰(C)(𝔽_p)`, and lift — the effective torsion bound.

The **log-argument linear solve `afLogArgSolve`** (this file) is the PRINCIPAL-case engine; the residue-divisor
→ general-Jacobian-torsion → `(1/m)log` path is the NON-principal continuation, the genuine sub-arc that the
hyperelliptic divisor machinery (`ComputableTorsionLogTerm`) already realizes on the diagonal and that the
general carrier (with `afDeriv` as the derivation) would lift. -/

/-! ### `#print axioms` — does the engine DERIVE the general-curve LOG argument (principal case)?

Each derive-then-verify theorem carries the standard `[propext, Classical.choice, Quot.sound]` plus the
`native_decide` compiler axiom — **no `sorry`, no `sorryAx`, no extra axiom** (`afLogArgSolve` is a
non-recursive composition over the fuel-bounded engine: `afLogColumns`/`afLogMatrix` are `List`-folds over
`afDeriv`/`afMul` and `cmulG`/`cnormG`; `kernelBasisG`/`gaussElimG` fold over finite `List.range`s; the
`ℕ`-fuel `8` feeds `afDeriv`'s `f_y`-inversion). **The engine now DERIVES the LOG argument for an ARBITRARY
plane curve (PRINCIPAL case)** — undetermined coefficients `u = Σ c_{ij} xʲ wᵢ` over the integral basis, the
log-derivative condition `afDeriv f u = afMul f u integrand` a homogeneous `K`-linear system solved by
`kernelBasisG`, the general-curve analogue of the hyperelliptic `radLogArgSolveG`, **sidestepping the general
divisor-class-group torsion** (the NON-principal case). The log argument is the solver's **OUTPUT**: `u ∝ y`
and `u ∝ y² + x` for log integrals on the non-hyperelliptic `y³ − x² − 1` (`afLogArgSolve_nonhyper_intLogY`,
`afLogArgSolve_nonhyper_intLogU2`), the arcsinh `u ∝ x + y` for `∫ dx/√(x²+1)` on the hyperelliptic `y² = x²+1`
(conservativity, `afLogArgSolve_hyper_arcsinh`), and the combined `∫ = v + log u` on the cuspidal cubic
(`afIntegrateAlgebraic_cuspCubic_combine`). DERIVED, not verified-forward. -/

-- ★★ DERIVE the LOG argument on the NON-HYPERELLIPTIC curve `y³ − x² − 1` (two targets):
#print axioms afLogArgSolve_nonhyper_intLogY
#print axioms afLogArgSolve_nonhyper_intLogU2

-- ★ Hyperelliptic conservativity: the general solve recovers arcsinh `u = x + y` on `y² = x²+1`:
#print axioms afLogArgSolve_hyper_arcsinh

-- ★ STRETCH: the general-curve `∫ = v + log u` (principal case) on the cuspidal cubic `y³ = x²`:
#print axioms afIntegrateAlgebraic_cuspCubic_combine

end DeepWiki.SymbolicIntegration
