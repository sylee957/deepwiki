import DeepWiki.SymbolicIntegration.ComputableRadicalCase2
import DeepWiki.SymbolicIntegration.ComputableIntegrate

/-! # Algebraic-function integration: the log-part residues (Trager Ch. 5 §2, eq. 7)

After the simple-radical **rational** part is reduced (Trager Appendix A, `ComputableRadicalExtension` /
`ComputableRadicalIntegrate` / `ComputableRadicalCase2`), the heart of the **logarithmic** part is the
computation of the *residues* — the constants `cᵢ` of the log terms `Σ cᵢ log vᵢ`. This file opens that
axis with Trager's Chapter 5 §2 residue resultant (thesis p.56–59, eq. 7).

For a differential `f dx` on the curve `F(x,y) = 0`, with `f(x,y) = g(x,y)/D(x)` and at most simple
finite poles, Trager's Theorem 2 says the residue at a place over a root `x₀` of `D(x)` (branch index
`r`) is the value of `r·g/D'` there. Computing *all* residues at once: introduce a new indeterminate `Z`
and form the polynomial whose roots are the residues divided by their (positive integer) branch orders,

  **`R(Z) = resultant_X( resultant_Y( Z·D'(X) − g(X,Y), F(X,Y) ), D(X) )`**   (eq. 7).

`R` is computed by **rational operations over the constant field `K`** (no extension to *find* it). Its
splitting field is the minimal extension `K'` containing all the residues — the smallest field in which
the integral can be expressed. Two failure tests for elementary integrability of a `df/f`-type
differential: (1) order `≥ −1` at every place (poles at most simple — the precondition for this whole
computation), and (2) all residues are integers.

**★ Simple-radical specialization (`F = yⁿ − ρ`, focus `n = 2`).** An element of the radical extension
is `g = g₀(x) + g₁(x)·y`, so `Z·D'(x) − g = (Z·D'(x) − g₀(x)) − g₁(x)·y` is **linear in `y`**. The inner
`resultant_Y` of a linear-in-`y` polynomial against `F = y² − ρ` is just the **norm**
`(Z·D'(x) − g₀(x))² − g₁(x)²·ρ(x)` (a polynomial in `x, Z`). The outer `resultant_X(that, D(X))`
eliminates `x`, leaving `R(Z) ∈ K[Z]`. So for `n = 2` the entire eq. 7 is **one norm + one univariate
resultant** — both already in the engine.

This is the algebraic-case generalization of the **transcendental** Rothstein–Trager residue resultant
`cResidueResultantTower` (`ComputableLogPartTower`), which computes the *single* univariate resultant
`R(z) = res_t(d, a − z·Dd)` by the evaluation+interpolation template. Here we keep that template but
replace the second resultant operand `a − z·Dd` with the **norm** `(Z·D'−g₀)² − g₁²·ρ`: for each rational
node `c`, evaluate the norm at `Z = c`, take `resultant_X(norm_c, D)` (one `cresultantG` over `K`), and
Lagrange-interpolate the points `(c, R(c))` back to `R(Z) ∈ K[Z]`.

* **`cAlgResidueNorm`** — the inner-norm-at-a-node `(c·D' − g₀)² − g₁²·ρ ∈ K[X]` (the `n = 2`
  `resultant_Y` against `y² − ρ`, evaluated at `Z = c`).
* **`cAlgResidueResultant`** (`n = 2`) — `R(Z) ∈ K[Z]` by evaluation+interpolation, mirroring
  `cResidueResultantTower`. `deg_Z R ≤ 2·deg_X D` (the square doubles the `Z`-degree), so `2·deg D + 1`
  nodes are exact.
* **`cIsResidue`** — the membership test `(Z − c) ∣ R(Z)` (is `c` a residue?), exact and computable.
* **`cResiduesMatch`** — `R(Z)` equals (monic) a given product `∏ (Z − cᵢ)^{mᵢ}` of claimed residues, the
  failure-test certificate (e.g. all residues integer ⇒ `R` is a product of integer linear factors and a
  power of `Z`).

**Validation** (`native_decide`): `∫ dx / ((x − 1)·y)` on the curve `y² = x` (so `y = √x`). Rationalizing,
`1/((x−1)y) = y/((x²−x))`, i.e. `g(x,y) = y` (`g₀ = 0, g₁ = 1`) and `D(x) = x² − x = x(x−1)`. Then
`D' = 2x − 1`, and the norm at `Z = c` is `(c(2x−1))² − x`. The engine computes
`R(Z) = Z⁴ − Z² = Z²(Z − 1)(Z + 1)`: the residues are `Z = ±1` (the simple pole at `x = 1`, on the two
sheets `y = ±1`, residue `g/D' = (±1)/(2·1−1) = ±1`) plus `Z = 0` of multiplicity `2` (the **branch
place** `x = 0` of `√x`, where the actual residue `r·g/D' = 2·y/(2x−1)` vanishes since `y(0) = 0`). All
residues `±1` are **integers**, so this `df/f`-type differential passes both Trager failure tests
(`∫ dx/((x−1)√x)` is elementary).

**OUT OF SCOPE — the genuinely hard next step (documented, not attempted).** This delivers the residues
`cᵢ` and the minimal-extension polynomial `R(Z)`, which Trager calls the heart and the tractable part. It
does **not** build the actual log arguments `vᵢ`: those require the **divisor construction** (Trager Ch. 5
§3), the **principal-divisor test** (the minimal multiple of a candidate divisor that is principal scales
the candidate coefficient), and — the real obstruction — the **torsion / points-of-finite-order bound**
(Trager Ch. 6, good reduction), which decides whether a divisor's multiple is *ever* principal. Splitting
`R` over `K'` (algebraic factoring, [48]) to extract the residues symbolically is likewise out of scope;
the example uses the known rational residues `±1` so the membership test checks directly. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### The `n = 2` residue resultant `R(Z) = res_X((Z·D' − g₀)² − g₁²·ρ, D)` -/

/-- **The inner residue norm at a node** `cAlgResidueNorm Dprime rho g0 g1 c = (c·D' − g₀)² − g₁²·ρ ∈
K[X]` — Trager eq. 7's inner `resultant_Y(Z·D'(X) − g(X,Y), y² − ρ)` for the simple radical `F = y² − ρ`,
`g = g₀ + g₁·y`, evaluated at `Z = c`. Because `Z·D' − g = (Z·D' − g₀) − g₁·y` is linear in `y`, that
inner resultant is the **norm** of the linear form, `(c·D' − g₀)² − g₁²·ρ`, a polynomial in `X` over `K`.
`Dprime = D'` (the `X`-derivative of `D`, supplied by the caller). Generic over `[CField α]`. -/
def cAlgResidueNorm (Dprime rho g0 g1 : CPolyG α) (c : α) : CPolyG α :=
  let zg0 := csubG (cscaleG c Dprime) g0                  -- `c·D' − g₀`
  csubG (cmulG zg0 zg0) (cmulG (cmulG g1 g1) rho)         -- `(c·D' − g₀)² − g₁²·ρ`

/-- **The `n = 2` algebraic-residue resultant** `cAlgResidueResultant fuel D rho g0 g1 = R(Z) ∈ K[Z]`
(Trager Ch. 5 §2 eq. 7, `F = y² − ρ`, `g = g₀ + g₁·y`):
`R(Z) = res_X((Z·D' − g₀)² − g₁²·ρ, D)`, returned as a `CPolyG α` whose variable is the residue
indeterminate `Z`. Computed by the **evaluation + interpolation** template of the transcendental
`cResidueResultantTower`: for nodes `c = 0, 1, …, 2·deg D`, evaluate the inner norm `cAlgResidueNorm`
at `Z = c` and take the univariate resultant `res_X(norm_c, D)` (`cresultantG`, eliminating `X`), then
Lagrange-interpolate the points `(c, R(c))` over `K` (`cinterpolateG`). `deg_Z R ≤ 2·deg_X D` (the norm's
square doubles the `Z`-degree), so `2·deg D + 1` nodes are exact. `D' = cderivG D` (the `X`-derivative).
Restricted to `n = 2` — the `linear-in-y` reduction is what collapses eq. 7's inner `resultant_Y` to the
single norm. Generic over `[CField α]`. -/
def cAlgResidueResultant (fuel : ℕ) (D rho g0 g1 : CPolyG α) : CPolyG α :=
  let Dprime := cderivG D
  let nNodes := 2 * cdegG D + 1                          -- `deg_Z R ≤ 2·deg_X D`
  let pts : List (α × α) := (List.range (nNodes + 1)).map (fun k =>
    let c : α := cnatCastG k
    (c, cresultantG fuel (cAlgResidueNorm Dprime rho g0 g1 c) D))
  cinterpolateG pts

/-! ### Residue membership and the integer-residue failure-test certificate -/

/-- **Residue membership test** `cIsResidue fuel R c = ((Z − c) ∣ R)` — is the value `c ∈ K` a residue,
i.e. a root of `R(Z)`? Tested by the exact division remainder `cmodG R (Z − c) = 0` (`(Z − c) ∣ R(Z)`).
Computable and exact; used to confirm a claimed rational residue (Trager: the roots of `R` are the
residues divided by their branch orders). Generic over `[CField α]`. -/
def cIsResidue (fuel : ℕ) (R : CPolyG α) (c : α) : Bool :=
  cisZeroG (cmodG fuel R [CField.neg c, CField.one])      -- `R mod (Z − c) = 0`

/-- **Integer-residue / factorization certificate** `cResiduesMatch R factors` — does the residue
resultant `R(Z)` equal, up to a `K`-scalar, the product `∏ (Z − cᵢ)` of the claimed residue linear
factors `factors = [c₁, …, c_m]` (with repetition encoding multiplicity)? Checked by `cisZeroG` of the
monic difference `cmonicG R − cmonicG (∏ (Z − cᵢ))` (all the ops are fuel-free). The **failure-test
certificate**: when all roots of `R` are exhibited as integers (plus the trivial `Z = 0` branch-place
roots), `R` is a product of integer linear factors and `cResiduesMatch` certifies it — so the
`df/f`-type differential passes Trager's "all residues are integers" test. Generic over `[CField α]`. -/
def cResiduesMatch (R : CPolyG α) (factors : List α) : Bool :=
  let prod := factors.foldl (fun acc c => cmulG acc [CField.neg c, CField.one]) [CField.one]
  cisZeroG (csubG (cmonicG R) (cmonicG prod))

end CPolyG

/-! ### ★ Validation: `∫ dx / ((x − 1)·y)` on `y² = x` (`native_decide`)

`K = ℚ` (constants), curve `F = y² − x` (`y = √x`, so `ρ = x`). The integrand `f = 1/((x − 1)·y)`
rationalizes to `f = y/((x − 1)·x) = y/(x² − x)`, i.e. numerator `g(x,y) = y` (`g₀ = 0, g₁ = 1`) and
denominator `D(x) = x² − x = x(x − 1)`. Then `D'(x) = 2x − 1`, and the inner norm at `Z = c` is
`(c·(2x − 1))² − x`. -/

open CPolyG

/-- Validation radicand `ρ = x` (curve `y² = x`), as a `ℚ[x]` polynomial `[0, 1]`. -/
def algResExX_rho : CPolyG ℚ := [0, 1]

/-- Validation denominator `D = x² − x = x(x − 1)` (its roots `x = 0, 1` carry the poles/branch place),
`ℚ[x]` `[0, -1, 1]`. -/
def algResExX_D : CPolyG ℚ := [0, -1, 1]

/-- Validation numerator low part `g₀ = 0` (`g(x,y) = y` has no `y⁰` part). -/
def algResExX_g0 : CPolyG ℚ := []

/-- Validation numerator `y`-coefficient `g₁ = 1` (`g(x,y) = y`), `ℚ[x]` `[1]`. -/
def algResExX_g1 : CPolyG ℚ := [1]

/-- The computed residue resultant `R(Z)` for `∫ dx/((x−1)√x)`. -/
def algResExX_R : CPolyG ℚ := cAlgResidueResultant 20 algResExX_D algResExX_rho algResExX_g0 algResExX_g1

/-- The expected monic residue resultant `R(Z) = Z⁴ − Z² = Z²(Z − 1)(Z + 1)` (low→high in `Z`,
`[0, 0, -1, 0, 1]`): residues `Z = ±1` (the simple pole at `x = 1`, sheets `y = ±1`) and `Z = 0` of
multiplicity `2` (the branch place `x = 0`, residue `0`). -/
def algResExX_expected : CPolyG ℚ := [0, 0, -1, 0, 1]

-- Sanity print: `R(Z) = Z⁴ − Z²` (low→high in `Z`).
#eval (cnormG algResExX_R : List ℚ)

/-- **★ The `n = 2` algebraic-residue resultant computes** (`native_decide`, Trager Ch. 5 §2 eq. 7). For
`∫ dx/((x − 1)·y)` on `y² = x` — `D = x² − x`, `ρ = x`, `g₀ = 0`, `g₁ = 1` — the engine's
`cAlgResidueResultant` (inner norm `(Z·D' − g₀)² − g₁²·ρ`, outer `res_X(·, D)` by
evaluation+interpolation) produces `R(Z) = Z⁴ − Z² = Z²(Z − 1)(Z + 1)`: checked by `cisZeroG` of
`R − (Z⁴ − Z²)` over ℚ[Z]. THE ALGEBRAIC-INTEGRAL LOG-PART RESIDUE RESULTANT COMPUTES for simple
radicals — eq. 7's double resultant collapses, at `n = 2`, to the engine's norm + one univariate
resultant, and returns the curve's residues. -/
theorem algResExX_resultant_eq :
    cisZeroG (csubG algResExX_R algResExX_expected) = true := by native_decide

/-- **★ The residues `±1` are roots of `R`** (`native_decide`): `cIsResidue R (±1) = true` — both `Z = 1`
and `Z = −1` divide `R(Z) = Z²(Z − 1)(Z + 1)`, confirming the residues of `∫ dx/((x − 1)√x)` at the
simple pole `x = 1` (sheets `y = ±1`) are `±1`, exactly Trager's Theorem-2 value `g/D' = (±1)/(2·1−1)`.
And `Z = 0` is a residue too (the branch place `x = 0`). -/
theorem algResExX_residues_pm_one :
    cIsResidue 20 algResExX_R (1 : ℚ) = true
    ∧ cIsResidue 20 algResExX_R (-1 : ℚ) = true
    ∧ cIsResidue 20 algResExX_R (0 : ℚ) = true := by native_decide

/-- **`Z = 2` is not a residue** (`native_decide`): `cIsResidue R 2 = false` — `R(2) = 16 − 4 = 12 ≠ 0`,
so the membership test correctly rejects a non-residue. (A negative control on `cIsResidue`.) -/
theorem algResExX_two_not_residue :
    cIsResidue 20 algResExX_R (2 : ℚ) = false := by native_decide

/-- **★ All residues are integers** (`native_decide`, Trager's failure test 2). The residue resultant
factors as `R(Z) = Z·Z·(Z − 1)·(Z + 1)` — a product of **integer** linear factors (`0, 0, 1, −1`) — so
`cResiduesMatch R [0, 0, 1, -1] = true`. The residues `±1` (and the branch-place `0`) are all integers,
hence `∫ dx/((x − 1)√x)`, a `df/f`-type differential, passes Trager's "all residues are integers" test:
its logarithmic part `Σ cᵢ log vᵢ` has integer coefficients and is elementary. THE INTEGER-RESIDUE
FAILURE TEST COMPUTES on `R(Z)`. -/
theorem algResExX_all_residues_integer :
    cResiduesMatch algResExX_R [0, 0, 1, -1] = true := by native_decide

/-- Restatement (the deliverable): the `n = 2` algebraic-residue resultant `cAlgResidueResultant` of
`∫ dx/((x − 1)·y)` on `y² = x` is `Z⁴ − Z²`, whose nonzero roots `±1` are the residues — computed by
Trager eq. 7 over the constant field ℚ alone. -/
example : cisZeroG (csubG
    (cAlgResidueResultant 20 algResExX_D algResExX_rho algResExX_g0 algResExX_g1)
    [0, 0, -1, 0, 1]) = true := by native_decide

#print axioms algResExX_resultant_eq
#print axioms algResExX_all_residues_integer

end DeepWiki.SymbolicIntegration
