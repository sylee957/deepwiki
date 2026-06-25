import DeepWiki.SymbolicIntegration.ComputableHyperexpBoundary

/-! # The complete hyperexponential simple integral (Bronstein §5.9)

`ComputableHyperexpBoundary` made the hyperexponential residual **explicit**:
`extendDeriv δ (∑ aᵢ·log gᵢ) = a/d + R` with `R = C(η·∑ res α) ∈ k = ℚ(x)` an honest constant of `t`
(the `X`-coefficient `η = δX`-leading times the residue sum). The §5.6 log part therefore overshoots
the simple integrand `a/d` by `R`. Because `R` is a rational function of `x`, it is itself elementary
integrable; subtracting an antiderivative `Y` of `R` corrects the overshoot and yields the **complete**
hyperexponential simple integral.

This file turns that observation into a **theorem** (no engine modification): given the proven residual
identity and any `Y` with `D Y = R`, the corrected log part `(∑ aᵢ·log gᵢ) − Y` differentiates exactly
to `a/d`. The composition is `map_sub` plus the two identities:
`D(logPart − Y) = D(logPart) − D Y = (a/d + R) − R = a/d`.

## Exhibiting `Y`

`R = algMap(C r₀)` is the image of the **constant-in-`t`** element `r₀ = η·∑ res α ∈ k`. An
antiderivative `Y` with `D Y = R` is the image of a **base** antiderivative `y₀ ∈ k` of `r₀` under the
base derivation `δ|_k` (`= d/dx` on `ℚ(x)`): since `δ (C y₀) = C (y₀′)` (`implicitDeriv_C`, the base
derivation acts coefficientwise), if `y₀′ = r₀` then `extendDeriv δ (algMap (C y₀)) = algMap (C r₀) = R`
(`extendDeriv_algebraMap`). So `Y = algMap (C y₀)` discharges the hypothesis. The existence of a base
antiderivative `y₀` is the §2 rational-integration fact (`RationalIntegrationLogForm`; Liouville): a
rational function of `x` is elementary integrable — though `y₀` itself may carry a log part when `r₀` is
a general proper fraction, so the integral is stated with `Y` as the *given* base antiderivative rather
than forcing the full §2 base integration here.

## The §5.9 reading

The corrected log part `(∑ aᵢ·log gᵢ) − Y` is exactly the §5.9 hyperexponential reduction's output: the
§5.6 log part, minus the antiderivative of its leftover residual `R`. That `R ∈ k` always has an
elementary antiderivative is why the hyperexponential simple case is *elementary*; the engine's failure
to subtract `Y` is an engine limit (it never wires `R` back through §5.9/§6), not a non-elementarity. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### The core identity: `D(logPart − Y) = a/d` (the headline)

Generic over a base field `K` and a base derivation `δ : Derivation ℤ K[X] K[X]`, with the fraction-field
derivation `extendDeriv δ` on `RatFunc K`. The proven residual lemma gives `D(logPart) = a/d + R`; given
any `Y` with `D Y = R`, the corrected log part differentiates to `a/d` by a three-line composition. -/

section Core
variable {K : Type*} [Field K] [Algebra ℚ K] (δ : Derivation ℤ K[X] K[X])

/-- **The corrected hyperexponential simple integral** (`D(logPart − Y) = a/d`, the headline): over a
split squarefree `d = nodal s id`, with a base derivation `δ` of **hyperexponential** type
`δ(X − Cα) = C η·X + C(γ α)` (degree-≤1, `η = δX` uniform), `b α = η·α + γ α ≠ 0` and δ-constant residues
`C(res α)`, the §5.6 logarithmic part `∑_{α∈s} algMap(C(res α))·L α` overshoots `A/d` by the explicit
residual `R = algMap(C(η·∑ res α))`; so for **any** `Y` with `extendDeriv δ Y = R` (an antiderivative of
the residual — which exists since `R ∈ k = ℚ(x)` is rational in `x`, hence elementary integrable), the
**corrected** log part `(∑ aᵢ·log gᵢ) − Y` differentiates **exactly** to `A/d`:
`extendDeriv δ ((∑_{α∈s} algMap(C(res α))·L α) − Y) = A/d`. The §5.9 completion of
`extendDeriv_logPart_eq_div_add_residual`: subtracting the antiderivative of the leftover residual
cancels the overshoot. Trivial composition — `map_sub`, the proven residual identity, and `DY = R`:
`D(logPart − Y) = D(logPart) − D Y = (A/d + R) − R = A/d`. -/
theorem extendDeriv_logPart_sub_antideriv_eq_div (A : K[X]) (s : Finset K) (hA : A.degree < s.card)
    (η : K) (γ : K → K) (hδ : ∀ α ∈ s, δ (X - C α) = C η * X + C (γ α))
    (hb0 : ∀ α ∈ s, η * α + γ α ≠ 0)
    (hc : ∀ α ∈ s, δ (C (A.eval α / (δ (Lagrange.nodal s id)).eval α)) = 0)
    (L : K → RatFunc K)
    (hL : ∀ α ∈ s, extendDeriv δ (L α)
      = algebraMap K[X] (RatFunc K) (δ (X - C α)) / algebraMap K[X] (RatFunc K) (X - C α))
    (Y : RatFunc K)
    (hY : extendDeriv δ Y
      = algebraMap K[X] (RatFunc K)
          (C (η * ∑ α ∈ s, A.eval α / (δ (Lagrange.nodal s id)).eval α))) :
    extendDeriv δ ((∑ α ∈ s,
          algebraMap K[X] (RatFunc K) (C (A.eval α / (δ (Lagrange.nodal s id)).eval α)) * L α) - Y)
      = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) := by
  rw [map_sub, extendDeriv_logPart_eq_div_add_residual δ A s hA η γ hδ hb0 hc L hL, hY,
    add_sub_cancel_right]

/-- **Lifting a base antiderivative to a residual antiderivative** (the §2→§5.9 bridge): if `y₀ ∈ K`
satisfies `δ (C y₀) = C r₀` under the base derivation `δ` (the constant case `δ (C b) = C b′` of
`implicitDeriv_C`, i.e. `y₀′ = r₀` in `k = ℚ(x)`), then `Y := algMap (C y₀)` is a residual antiderivative:
`extendDeriv δ (algMap (C y₀)) = algMap (C r₀)` (= `R`). The lift through `extendDeriv_algebraMap` — the
extended derivation agrees with `δ` on polynomial images. So a base antiderivative `y₀` of the
constant-in-`t` residual `r₀` discharges the `hY` hypothesis of `extendDeriv_logPart_sub_antideriv_eq_div`. -/
theorem extendDeriv_algebraMap_C_of_baseDeriv {y₀ r₀ : K} (hbase : δ (C y₀) = C r₀) :
    extendDeriv δ (algebraMap K[X] (RatFunc K) (C y₀))
      = algebraMap K[X] (RatFunc K) (C r₀) := by
  rw [extendDeriv_algebraMap, hbase]

/-- **The complete hyperexponential simple integral from a base antiderivative** (the §5.9 headline with
`Y` exhibited): when the constant-in-`t` residual `r₀ = η·∑ res α ∈ k` has a base antiderivative `y₀ ∈ k`
(`δ (C y₀) = C r₀`, i.e. `y₀′ = r₀` in `ℚ(x)` — guaranteed elementary by the §2 rational integrator
`RationalIntegrationLogForm`/Liouville), the corrected log part with the **concrete** correction
`Y = algMap (C y₀)` differentiates exactly to `A/d`:
`extendDeriv δ ((∑ aᵢ·log gᵢ) − algMap (C y₀)) = A/d`. Composes
`extendDeriv_logPart_sub_antideriv_eq_div` with the lift `extendDeriv_algebraMap_C_of_baseDeriv` (which
turns `δ (C y₀) = C r₀` into the residual-antiderivative hypothesis). The concrete §5.9 simple integral:
log part minus a base antiderivative of the leftover residual. -/
theorem extendDeriv_logPart_sub_baseAntideriv_eq_div (A : K[X]) (s : Finset K) (hA : A.degree < s.card)
    (η : K) (γ : K → K) (hδ : ∀ α ∈ s, δ (X - C α) = C η * X + C (γ α))
    (hb0 : ∀ α ∈ s, η * α + γ α ≠ 0)
    (hc : ∀ α ∈ s, δ (C (A.eval α / (δ (Lagrange.nodal s id)).eval α)) = 0)
    (L : K → RatFunc K)
    (hL : ∀ α ∈ s, extendDeriv δ (L α)
      = algebraMap K[X] (RatFunc K) (δ (X - C α)) / algebraMap K[X] (RatFunc K) (X - C α))
    (y₀ : K)
    (hbase : δ (C y₀) = C (η * ∑ α ∈ s, A.eval α / (δ (Lagrange.nodal s id)).eval α)) :
    extendDeriv δ ((∑ α ∈ s,
          algebraMap K[X] (RatFunc K) (C (A.eval α / (δ (Lagrange.nodal s id)).eval α)) * L α)
            - algebraMap K[X] (RatFunc K) (C y₀))
      = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) :=
  extendDeriv_logPart_sub_antideriv_eq_div δ A s hA η γ hδ hb0 hc L hL _
    (extendDeriv_algebraMap_C_of_baseDeriv δ hbase)

/-- Headline restatement: the corrected hyperexponential simple integral `D((∑ aᵢ·log gᵢ) − Y) = A/d`
given any residual antiderivative `Y` (`DY = R`). -/
example (A : K[X]) (s : Finset K) (hA : A.degree < s.card) (η : K) (γ : K → K)
    (hδ : ∀ α ∈ s, δ (X - C α) = C η * X + C (γ α)) (hb0 : ∀ α ∈ s, η * α + γ α ≠ 0)
    (hc : ∀ α ∈ s, δ (C (A.eval α / (δ (Lagrange.nodal s id)).eval α)) = 0)
    (L : K → RatFunc K)
    (hL : ∀ α ∈ s, extendDeriv δ (L α)
      = algebraMap K[X] (RatFunc K) (δ (X - C α)) / algebraMap K[X] (RatFunc K) (X - C α))
    (Y : RatFunc K)
    (hY : extendDeriv δ Y
      = algebraMap K[X] (RatFunc K)
          (C (η * ∑ α ∈ s, A.eval α / (δ (Lagrange.nodal s id)).eval α))) :
    extendDeriv δ ((∑ α ∈ s,
          algebraMap K[X] (RatFunc K) (C (A.eval α / (δ (Lagrange.nodal s id)).eval α)) * L α) - Y)
      = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) :=
  extendDeriv_logPart_sub_antideriv_eq_div δ A s hA η γ hδ hb0 hc L hL Y hY

/-- Headline restatement: the concrete §5.9 simple integral from a base antiderivative `y₀′ = r₀`. -/
example (A : K[X]) (s : Finset K) (hA : A.degree < s.card) (η : K) (γ : K → K)
    (hδ : ∀ α ∈ s, δ (X - C α) = C η * X + C (γ α)) (hb0 : ∀ α ∈ s, η * α + γ α ≠ 0)
    (hc : ∀ α ∈ s, δ (C (A.eval α / (δ (Lagrange.nodal s id)).eval α)) = 0)
    (L : K → RatFunc K)
    (hL : ∀ α ∈ s, extendDeriv δ (L α)
      = algebraMap K[X] (RatFunc K) (δ (X - C α)) / algebraMap K[X] (RatFunc K) (X - C α))
    (y₀ : K)
    (hbase : δ (C y₀) = C (η * ∑ α ∈ s, A.eval α / (δ (Lagrange.nodal s id)).eval α)) :
    extendDeriv δ ((∑ α ∈ s,
          algebraMap K[X] (RatFunc K) (C (A.eval α / (δ (Lagrange.nodal s id)).eval α)) * L α)
            - algebraMap K[X] (RatFunc K) (C y₀))
      = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id) :=
  extendDeriv_logPart_sub_baseAntideriv_eq_div δ A s hA η γ hδ hb0 hc L hL y₀ hbase

end Core

/-! ### Tie to the engine data over the tower `RatFunc (RatFunc ℚ)`

The same correction stated on the engine's actual carrier and residual object: the engine's log-residue
sum `logResidueSum Dt logs` overshoots the simple residual `towerAlg(hNum)/towerAlg(hDen)` by the
explicit `towerHyperexpResidual Dt hNum η s` (`towerLogResidueSum_eq_div_add_residual_of_residueData`).
Subtracting any tower antiderivative `Y` of that residual recovers the simple residual exactly. The
residual is the image of the **constant-in-`t`** element `r₀ = η·∑ res α ∈ ℚ(x)` (`towerHyperexpResidual
= towerAlg (C r₀)`), so a base `d/dx`-antiderivative `y₀ ∈ ℚ(x)` of `r₀` gives the concrete correction
`Y = towerAlg (C y₀)`. -/

namespace CPolyG

open scoped Differential
open QFunNZ

/-- The tower fraction field's `Algebra ℚ` (matching the keystone instances), so `algebraMap ℚ
(CFieldSpec.K QFunNZ)` resolves uniformly with the proven RT spine. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K QFunNZ) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

open DeepWiki.SymbolicIntegration in
open scoped Classical Differential in
/-- **The engine's hyperexponential residue sum, corrected** (`logSum − R = hₛ`, the engine-data
headline): for a hyperexponential monomial `toPolyG Dt = C η·X + C w₀` with the concrete denominator
split `toPolyG hDen = nodal s id`, `deg hNum < #s`, seed normality, and the concrete log list, the engine's
`logResidueSum Dt logs` (the symbolic derivative of its §5.6 log-part output `∑ aᵢ·log gᵢ`) equals the
simple residual `towerAlg(hNum)/towerAlg(hDen)` **plus** the explicit residual `towerHyperexpResidual Dt
hNum η s` (`towerLogResidueSum_eq_div_add_residual_of_residueData`). Subtracting the residual therefore
recovers the simple residual exactly:
`logResidueSum Dt logs − towerHyperexpResidual Dt hNum η s = towerAlg(hNum)/towerAlg(hDen)`.
The §5.9 correction on the engine's own carrier and residual object: since `logResidueSum = D(∑ aᵢ·log gᵢ)`
and `towerHyperexpResidual = D Y` for an antiderivative `Y` of `R` (`towerFractionFieldDeriv_algebraMap_C_of_baseDeriv`),
this is exactly `D((∑ aᵢ·log gᵢ) − Y) = hₛ` — the engine output corrected by `−Y` integrates `hₛ`. Pure
`sub_eq` of the proven residual identity. -/
theorem towerLogResidueSum_sub_residual_eq_div_of_residueData (Dt : CPolyG QFunNZ)
    {η w₀ : CFieldSpec.K QFunNZ} (htop : toPolyG Dt = C η * X + C w₀)
    (hNum hDen : CPolyG QFunNZ) (logs : List (ℚ × CPolyG QFunNZ))
    (s : Finset (CFieldSpec.K QFunNZ))
    (hden : toPolyG hDen = Lagrange.nodal s id)
    (hA : (toPolyG hNum).degree < s.card)
    (hb0 : ∀ α ∈ s, η * α + (w₀ - α′) ≠ 0)
    (hkeysNodup : (logs.map (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).Nodup)
    (hkeysImage : (logs.map (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).toFinset
      = s.image (fun α => (toPolyG hNum).eval α
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α))
    (harg : ∀ cv ∈ logs, toPolyG cv.2
      = ∏ α ∈ s.filter (fun α => (toPolyG hNum).eval α
            / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α
              = CFieldSpec.toK (ofConstNZ cv.1)), (X - C α)) :
    logResidueSum Dt logs - towerHyperexpResidual Dt hNum η s
      = towerAlg (toPolyG hNum) / towerAlg (toPolyG hDen) := by
  rw [towerLogResidueSum_eq_div_add_residual_of_residueData Dt htop hNum hDen logs s hden hA hb0
    hkeysNodup hkeysImage harg, add_sub_cancel_right]

open DeepWiki.SymbolicIntegration in
open scoped Classical Differential in
/-- **The tower residual is the image of a constant-in-`t` element**: `towerHyperexpResidual Dt hNum η s
= towerAlg (C r₀)` with `r₀ = η·∑ res α ∈ k = ℚ(x)` (definitionally — the residual is built as
`towerAlg (C …)`). The hook to exhibit `Y` via a base antiderivative: a base `d/dx`-antiderivative
`y₀ ∈ ℚ(x)` of `r₀` lifts to the tower correction `Y = towerAlg (C y₀)`. -/
theorem towerHyperexpResidual_eq_algebraMap_C (Dt hNum : CPolyG QFunNZ) (η : CFieldSpec.K QFunNZ)
    (s : Finset (CFieldSpec.K QFunNZ)) :
    towerHyperexpResidual Dt hNum η s
      = towerAlg (C (η * ∑ α ∈ s, (toPolyG hNum).eval α
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α)) :=
  rfl

open DeepWiki.SymbolicIntegration in
open scoped Classical Differential in
/-- **A base antiderivative lifts to a tower residual antiderivative** (the §2→§5.9 bridge on the tower):
if `y₀ ∈ ℚ(x)` is a base `d/dx`-antiderivative of `r₀ = η·∑ res α` — i.e. `y₀′ = r₀` in `k`, equivalently
`implicitDeriv (toPolyG Dt) (C y₀) = C r₀` (the constant case of `implicitDeriv_C`) — then
`Y := towerAlg (C y₀)` is a tower antiderivative of the residual:
`towerFractionFieldDeriv Dt (towerAlg (C y₀)) = towerHyperexpResidual Dt hNum η s`. The lift through
`towerFractionFieldDeriv_algebraMap`. So `Y = towerAlg (C y₀)` is the concrete `Y` whose derivative is the
residual `R` subtracted in `towerLogResidueSum_sub_residual_eq_div_of_residueData`. -/
theorem towerFractionFieldDeriv_algebraMap_C_of_baseDeriv (Dt hNum : CPolyG QFunNZ)
    (η : CFieldSpec.K QFunNZ) (s : Finset (CFieldSpec.K QFunNZ)) (y₀ : CFieldSpec.K QFunNZ)
    (hbase : Differential.implicitDeriv (toPolyG Dt) (C y₀)
      = C (η * ∑ α ∈ s, (toPolyG hNum).eval α
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α)) :
    towerFractionFieldDeriv Dt (towerAlg (C y₀)) = towerHyperexpResidual Dt hNum η s := by
  rw [towerHyperexpResidual_eq_algebraMap_C, towerFractionFieldDeriv_algebraMap, hbase]

open DeepWiki.SymbolicIntegration in
open scoped Classical Differential in
/-- **The engine's hyperexponential residue sum, corrected by an exhibited derivative** (the §5.9
engine-data headline with `Y` concrete): with the residueData hypotheses, when the constant-in-`t` residual
`r₀ = η·∑ res α ∈ ℚ(x)` has a base `d/dx`-antiderivative `y₀ ∈ ℚ(x)` (`implicitDeriv (toPolyG Dt) (C y₀) =
C r₀`, i.e. `y₀′ = r₀`; guaranteed elementary by the §2 rational integrator), the engine's residue sum minus
the **derivative of the concrete correction** `Y = towerAlg (C y₀)` equals the simple residual:
`logResidueSum Dt logs − towerFractionFieldDeriv Dt (towerAlg (C y₀)) = towerAlg(hNum)/towerAlg(hDen)`.
Since `logResidueSum = D(∑ aᵢ·log gᵢ)` this reads `D(∑ aᵢ·log gᵢ) − D Y = D((∑ aᵢ·log gᵢ) − Y) = hₛ` — "the
engine's §5.6 hyperexponential log-part output, corrected by `−Y` for the explicit residual, integrates
`hₛ`", the complete §5.9 simple integral on the engine's carrier and data. Composes the correction
`towerLogResidueSum_sub_residual_eq_div_of_residueData` with the lift
`towerFractionFieldDeriv_algebraMap_C_of_baseDeriv`. -/
theorem towerLogResidueSum_sub_baseDeriv_eq_div_of_residueData (Dt : CPolyG QFunNZ)
    {η w₀ : CFieldSpec.K QFunNZ} (htop : toPolyG Dt = C η * X + C w₀)
    (hNum hDen : CPolyG QFunNZ) (logs : List (ℚ × CPolyG QFunNZ))
    (s : Finset (CFieldSpec.K QFunNZ))
    (hden : toPolyG hDen = Lagrange.nodal s id)
    (hA : (toPolyG hNum).degree < s.card)
    (hb0 : ∀ α ∈ s, η * α + (w₀ - α′) ≠ 0)
    (hkeysNodup : (logs.map (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).Nodup)
    (hkeysImage : (logs.map (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).toFinset
      = s.image (fun α => (toPolyG hNum).eval α
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α))
    (harg : ∀ cv ∈ logs, toPolyG cv.2
      = ∏ α ∈ s.filter (fun α => (toPolyG hNum).eval α
            / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α
              = CFieldSpec.toK (ofConstNZ cv.1)), (X - C α))
    (y₀ : CFieldSpec.K QFunNZ)
    (hbase : Differential.implicitDeriv (toPolyG Dt) (C y₀)
      = C (η * ∑ α ∈ s, (toPolyG hNum).eval α
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α)) :
    logResidueSum Dt logs - towerFractionFieldDeriv Dt (towerAlg (C y₀))
      = towerAlg (toPolyG hNum) / towerAlg (toPolyG hDen) := by
  rw [towerFractionFieldDeriv_algebraMap_C_of_baseDeriv Dt hNum η s y₀ hbase]
  exact towerLogResidueSum_sub_residual_eq_div_of_residueData Dt htop hNum hDen logs s hden hA hb0
    hkeysNodup hkeysImage harg

open DeepWiki.SymbolicIntegration in
open scoped Classical Differential in
/-- Restatement: the engine's corrected hyperexponential residue sum `logSum − R = hₛ` — the citable §5.9
engine-data deliverable (`R = towerHyperexpResidual`, an antiderivative of `R` corrects the §5.6 log part
into the complete simple integral). -/
example (Dt : CPolyG QFunNZ) {η w₀ : CFieldSpec.K QFunNZ} (htop : toPolyG Dt = C η * X + C w₀)
    (hNum hDen : CPolyG QFunNZ) (logs : List (ℚ × CPolyG QFunNZ))
    (s : Finset (CFieldSpec.K QFunNZ)) (hden : toPolyG hDen = Lagrange.nodal s id)
    (hA : (toPolyG hNum).degree < s.card) (hb0 : ∀ α ∈ s, η * α + (w₀ - α′) ≠ 0)
    (hkeysNodup : (logs.map (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).Nodup)
    (hkeysImage : (logs.map (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).toFinset
      = s.image (fun α => (toPolyG hNum).eval α
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α))
    (harg : ∀ cv ∈ logs, toPolyG cv.2
      = ∏ α ∈ s.filter (fun α => (toPolyG hNum).eval α
            / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α
              = CFieldSpec.toK (ofConstNZ cv.1)), (X - C α)) :
    logResidueSum Dt logs - towerHyperexpResidual Dt hNum η s
      = towerAlg (toPolyG hNum) / towerAlg (toPolyG hDen) :=
  towerLogResidueSum_sub_residual_eq_div_of_residueData Dt htop hNum hDen logs s hden hA hb0
    hkeysNodup hkeysImage harg

end CPolyG

/-! ### The §5.9 status, precisely

`extendDeriv_logPart_sub_antideriv_eq_div` (and the engine-data
`CPolyG.towerLogResidueSum_sub_residual_eq_div_of_residueData`) closes the **mathematical** §5.9 gap as a
theorem: the §5.6 hyperexponential log part overshoots `a/d` by the explicit residual `R = C(η·∑ res α) ∈
k`, and subtracting **any** antiderivative `Y` of `R` (which exists, since `R ∈ k = ℚ(x)` is rational in
`x`) recovers `a/d` exactly. The `Y`-exhibition (`extendDeriv_logPart_sub_baseAntideriv_eq_div`,
`CPolyG.towerLogResidueSum_sub_baseDeriv_eq_div_of_residueData`) makes `Y` **concrete** as `algMap (C
y₀)` for a **base** `d/dx`-antiderivative `y₀ ∈ ℚ(x)` of the constant-in-`t` residual `r₀ = η·∑ res α`.

The remaining gap is the *base integration itself*: producing `y₀` with `y₀′ = r₀` for the specific
`r₀ ∈ ℚ(x)`. This is exactly the §2 rational-function integration the library already formalizes
(`RationalIntegrationLogForm` — `∫ R/V = ∑ a·log Gₐ`; Liouville), so `y₀` always exists and is elementary
(rational part plus logs), but is left as the `hbase` hypothesis rather than wired through the §2
integrator here. This file's deliverable is the §5.9 *correction identity* and its reduction to base
integration — turning the explicit residual of `ComputableHyperexpBoundary` into the complete simple
integral `(∑ aᵢ·log gᵢ) − Y`. Closing the base-integration hypothesis (and wiring the whole correction
into `cIntegrate`) is the remaining engine work, out of scope under the no-engine-edit constraint. -/

-- Axiom audits for the headline deliverables (`[propext, Classical.choice, Quot.sound]` — no
-- `native_decide`, no `sorryAx`).
#print axioms extendDeriv_logPart_sub_antideriv_eq_div
#print axioms extendDeriv_algebraMap_C_of_baseDeriv
#print axioms extendDeriv_logPart_sub_baseAntideriv_eq_div
#print axioms CPolyG.towerLogResidueSum_sub_residual_eq_div_of_residueData
#print axioms CPolyG.towerHyperexpResidual_eq_algebraMap_C
#print axioms CPolyG.towerFractionFieldDeriv_algebraMap_C_of_baseDeriv
#print axioms CPolyG.towerLogResidueSum_sub_baseDeriv_eq_div_of_residueData
