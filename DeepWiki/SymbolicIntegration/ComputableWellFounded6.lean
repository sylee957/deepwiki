import DeepWiki.SymbolicIntegration.ComputableWellFounded5
import DeepWiki.SymbolicIntegration.ComputableIntegrate
import DeepWiki.SymbolicIntegration.ComputableIntegrateCorrect
import DeepWiki.SymbolicIntegration.ComputableIntegrateChecked
import DeepWiki.SymbolicIntegration.ComputableResidueBridge
import DeepWiki.SymbolicIntegration.ComputableResultantGeneric

/-! # Fuel-free (well-founded) Rothstein–Trager + the top-level integrator — `cIntegrateWf`

This completes the fuel-free conversion of the transcendental Risch integrator begun in
`ComputableWellFounded`/`…2`/`…3`/`…4`/`…5` (all leaves + the §3.5 splitting-factorization layer + the §5
own-loops `cPolyReduceTowerWf`/`cPrimitivePolyIntegrateWf`/`cHermiteReduceTowerWf`) into the §5.6
Rothstein–Trager logarithmic part and the top compositions, reaching the user's target `cIntegrateWf` — a
fuel-free end-to-end transcendental Risch integrator over the tower ℚ(x)[t].

* **`cResidueResultantTowerWf`** — the fuel-free §5.6 residue resultant `R(z) = res_t(d, a − z·Dd)`. The
  fuel touches *only* the per-sample Euclidean-PRS resultant `cresultantG`; the rest (the bounded `z`-node
  list, the Lagrange interpolation `cinterpolateG`) is **structural**. So the fuel-free companion
  substitutes the WF-leaf resultant `cresultantWf` (`ComputableWellFounded2`) into the structural
  evaluation + interpolation template — **no fuel at runtime**. The bridge replaces each sample's
  `cresultantWf = cresultantG fuel` (`cresultantWf_eq_of_fuel`) and the Sylvester-resultant transport
  `toPolyG_cResidueResultantTower` follows.

* **`cLogArgTowerWf`** — the fuel-free §5.6 log argument `gcd_t(d, a − c·Dd)`. The fuel touches only the
  fraction-free monic gcd `cgcdFF`; the companion substitutes `cgcdFFWf` (`ComputableWellFounded3`). Bridge
  `cgcdFFWf = cgcdFF fuel` then transports `cLogArgTower_toPolyG_eq_prod`.

* **`cLogPartWf`** — the fuel-free assembled logarithmic part `[(c, gcd_t(d, a − c·Dd)) | c ∈ rational
  residues]`. A **composition**: the rational residues `cRationalResiduesWf` (the `cResidueResultantTowerWf`
  root scan, structural `filter`) then a structural map of `cLogArgTowerWf`. Bridge + transport
  `cLogPart_logResidueSum_eq_div`.

* **`cIntegrateReducedWf`** — the fuel-free reduced-case capstone: composes `cHermiteReduceTowerWf`
  (`ComputableWellFounded5`) with `cLogPartWf`.

* **`cIntegrateWf`** (the **goal**) — the fuel-free top-level `cIntegrate`: composes
  `canonicalRepresentationFastWf` (`ComputableWellFounded4`), `cPrimitivePolyIntegrateWf`
  (`ComputableWellFounded5`), and `cIntegrateReducedWf` — all now fuel-free. A pure **composition** (no new
  recursion). The bridge `cIntegrateWf = cIntegrate fuel` (threading the sub-bridges) transports
  `cIntegrate_checkIdentity_uncond` → the fuel-free `D(cIntegrateWf f) = f` in the primitive regime.

* **`cIntegrateCheckedWf`** — the fuel-free **self-validating** integrator: guard `cIntegrateWf` by the
  engine's own cleared antiderivative check `IntegralResult.checkIdentity`. Its correctness
  `cIntegrateCheckedWf_correct` is **UNCONDITIONAL** (all inputs, all regimes) and **engine-independent**:
  `cIntegrateCheckedWf = some res` forces `checkIdentity = true`, and the converse bridge
  `field_identity_of_checkIdentity` (engine-agnostic) turns that into `D(res) = f` — *no* bridge to the
  fuel'd `cIntegrate` is needed.

As throughout, where a fuel'd bridge is given the fuel bounds live only in the bridge proof; the runtime
WF ops carry no fuel. The `native_decide` smoke tests re-run Bronstein's Example 5.6.2 (`t = log x`) over
the noncomputable-`CFieldSpec` tower `QFunNZ` (ℚ(x)), now end-to-end fuel-free. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZ

/-! ### Target RT.1 — the fuel-free residue resultant `cResidueResultantTowerWf` (§5.6)

`cResidueResultantTower Dt fuel a d` (Bronstein §5.6) computes `R(z) = res_t(d, a − z·Dd) ∈ ℚ(x)[z]` by the
§2.4 evaluation + interpolation template: sample `R(zₖ) = res_t(d, a − zₖ·Dd)` at `zₖ = 0, 1, …, deg_t d`
via the generic Euclidean-PRS resultant `cresultantG`, then Lagrange-interpolate (`cinterpolateG`). The
fuel feeds **only** the per-sample `cresultantG`; the `z`-node list (`List.range (n+1)`) and the
interpolation are structural. The fuel-free companion substitutes the WF-leaf `cresultantWf`. -/

namespace CPolyG

/-- **Fuel-free residue resultant** (Bronstein §5.6) `cResidueResultantTowerWf Dt a d = R(z) =
res_t(d, a − z·Dd) ∈ ℚ(x)[z]`, the fuel-free companion of `cResidueResultantTower`. Identical structure —
sample at `zₖ = 0, …, deg_t d` and Lagrange-interpolate — but each sample's resultant is the **fuel-free**
Euclidean-PRS resultant `cresultantWf` (`ComputableWellFounded2`) instead of `cresultantG fuel`. The
`z`-node list and `cinterpolateG` are structural, so **no fuel at runtime**; `native_decide`-able over the
noncomputable-`CFieldSpec` tower `QFunNZ`. -/
def cResidueResultantTowerWf (Dt : CPolyG QFunNZ) (a d : CPolyG QFunNZ) : CPolyG QFunNZ :=
  let n := cdegG d                                    -- `deg_z R ≤ deg_t d = n`
  let pts : List (QFunNZ × QFunNZ) := (List.range (n + 1)).map (fun k =>
    let zk : QFunNZ := ofConstNZ (k : ℚ)
    (zk, cresultantWf d (cAmcDd Dt a d zk)))
  cinterpolateG pts

end CPolyG

/-! ### Bridge of `cResidueResultantTowerWf` to the fuel'd `cResidueResultantTower`, and transport

The two differ only in the per-sample resultant. Under the per-node fuel bound
`(cnormG d).length + (cnormG (a − zₖ·Dd)).length + 2 ≤ fuel` (the `cresultantWf_eq_of_fuel` margin),
each sample agrees, so the node-point lists coincide and the structural `cinterpolateG` produces the same
`R(z)`. The Sylvester-resultant transport `toPolyG_cResidueResultantTower` then carries over. -/

namespace CPolyG

/-- **Bridge — `cResidueResultantTowerWf` equals `cResidueResultantTower` at any sufficient fuel.** Under
the per-node fuel bound `(cnormG d).length + (cnormG (cAmcDd Dt a d (ofConstNZ k))).length + 2 ≤ fuel` for
every node `k ∈ range (deg_t d + 1)` (the `cresultantWf_eq_of_fuel` margin), the sampled node-point lists
coincide and the structural Lagrange interpolation `cinterpolateG` produces the same `R(z)`:
`cResidueResultantTowerWf Dt a d = cResidueResultantTower Dt fuel a d`. The fuel bound lives only here;
`cResidueResultantTowerWf` carries none. -/
theorem cResidueResultantTowerWf_eq (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ)
    (hfuel : ∀ k ∈ Finset.range (cdegG d + 1),
      (cnormG d : List QFunNZ).length
        + (cnormG (cAmcDd Dt a d (ofConstNZ (k : ℚ))) : List QFunNZ).length + 2 ≤ fuel) :
    cResidueResultantTowerWf Dt a d = CPolyG.cResidueResultantTower Dt fuel a d := by
  rw [cResidueResultantTowerWf, CPolyG.cResidueResultantTower]
  -- the two `pts` lists agree element-by-element: the inner `z`-node list (`List.range (n+1)` mapped to
  -- abscissas `↑k`) is identical on both sides; only the resultant call differs.  We feed `cinterpolateG`
  -- the same list by proving the two `.map`s equal.
  congr 1
  apply List.map_congr_left
  intro k hk
  -- `k ∈ (do let j ← List.range (n+1); pure ↑j)` ⟹ `k = ↑j` for some `j ∈ range (n+1)`
  simp only [List.bind_eq_flatMap, List.mem_flatMap, List.mem_range, List.mem_singleton,
    List.pure_def] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  -- each sample: `cresultantWf d (a − zⱼ·Dd) = cresultantG fuel d (a − zⱼ·Dd)` (unfold the `have zk`)
  dsimp only
  rw [cresultantWf_eq_of_fuel fuel d (cAmcDd Dt a d (ofConstNZ (j : ℚ)))
    (hfuel j (Finset.mem_range.mpr hj))]

open scoped Classical in
/-- **`cResidueResultantTowerWf` realizes the abstract RT-resultant** (transported, fuel-free): for monic
`toPolyG d` with `deg(a − k·Δd) ≤ deg d` at each node and the per-node `cresultantWf` fuel margin, the
fuel-free residue resultant reads under `toPolyG` as the abstract `rtResultantSeed`,
`Δd = implicitDeriv (toPolyG Dt) (toPolyG d)`. The fuel-free companion of
`toPolyG_cResidueResultantTower`, transported through the bridge `cResidueResultantTowerWf_eq`. -/
theorem toPolyG_cResidueResultantTowerWf (Dt a d : CPolyG QFunNZ) (fuel : ℕ)
    (hdmonic : (toPolyG d).Monic)
    (hamc : ∀ k ∈ Finset.range (cdegG d + 1),
      (toPolyG (cAmcDd Dt a d (ofConstNZ (k : ℚ)))).natDegree ≤ (toPolyG d).natDegree)
    (hfuel : ∀ k ∈ Finset.range (cdegG d + 1),
      (cnormG d : List QFunNZ).length
        + (cnormG (cAmcDd Dt a d (ofConstNZ (k : ℚ))) : List QFunNZ).length + 2 ≤ fuel) :
    toPolyG (cResidueResultantTowerWf Dt a d)
      = rtResultantSeed (toPolyG a) (toPolyG d)
          (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)) := by
  rw [cResidueResultantTowerWf_eq Dt fuel a d hfuel]
  exact toPolyG_cResidueResultantTower Dt a d fuel hdmonic hamc hfuel

end CPolyG

-- The fuel-free §5.6 residue-resultant headline carries only the standard axioms (no `native` axiom).
#print axioms CPolyG.toPolyG_cResidueResultantTowerWf

/-! ### Target RT.2 — the fuel-free log argument `cLogArgTowerWf` (§5.6)

`cLogArgTower Dt fuel a d c = gcd_t(d, a − c·Dd)` is the fraction-free monic gcd `cgcdFF fuel d (a − c·Dd)`;
the fuel touches only `cgcdFF`. The fuel-free companion substitutes the WF-leaf `cgcdFFWf`
(`ComputableWellFounded3`). -/

namespace CPolyG

/-- **Fuel-free log argument** (Bronstein §5.6) `cLogArgTowerWf Dt a d c = gcd_t(d, a − c·Dd) ∈ ℚ(x)[t]`
for a residue `c ∈ ℚ`, the fuel-free companion of `cLogArgTower`: the fraction-free monic-in-`t` gcd of `d`
and `a − c·Dd` via the **fuel-free** `cgcdFFWf` (`ComputableWellFounded3`) instead of `cgcdFF fuel`. **No
fuel at runtime**; `native_decide`-able over the tower `QFunNZ`. -/
def cLogArgTowerWf (Dt : CPolyG QFunNZ) (a d : CPolyG QFunNZ) (c : ℚ) : CPolyG QFunNZ :=
  cgcdFFWf d (cAmcDd Dt a d (ofConstNZ c))

/-- **Bridge — `cLogArgTowerWf` equals `cLogArgTower` at any sufficient fuel.** With the WF-leaf
`cgcdFFWf_eq_of_fuel` bounds on the `bdeg`-ordered cleared pair of `d`, `a − c·Dd` (the divisor cleared
poly's `t`-length `≤ fuel`, the degree ordering, the larger cleared poly's `t`-length `≤ 60`),
`cLogArgTowerWf Dt a d c = cLogArgTower Dt fuel a d c`. The fuel bounds live only here; `cLogArgTowerWf`
carries none. Directly the gcd bridge `cgcdFFWf_eq_of_fuel d (a − c·Dd)`. -/
theorem cLogArgTowerWf_eq (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ) (c : ℚ)
    (hflen : (Compute.bnorm (if Compute.bdeg (clearDenoms d)
          < Compute.bdeg (clearDenoms (cAmcDd Dt a d (ofConstNZ c)))
        then clearDenoms d else clearDenoms (cAmcDd Dt a d (ofConstNZ c)))).length ≤ fuel)
    (hfdeg : (Compute.bnorm (if Compute.bdeg (clearDenoms d)
          < Compute.bdeg (clearDenoms (cAmcDd Dt a d (ofConstNZ c)))
        then clearDenoms d else clearDenoms (cAmcDd Dt a d (ofConstNZ c)))).length
      ≤ (Compute.bnorm (if Compute.bdeg (clearDenoms d)
          < Compute.bdeg (clearDenoms (cAmcDd Dt a d (ofConstNZ c)))
        then clearDenoms (cAmcDd Dt a d (ofConstNZ c)) else clearDenoms d)).length)
    (hf60 : (Compute.bnorm (if Compute.bdeg (clearDenoms d)
          < Compute.bdeg (clearDenoms (cAmcDd Dt a d (ofConstNZ c)))
        then clearDenoms (cAmcDd Dt a d (ofConstNZ c)) else clearDenoms d)).length ≤ 60) :
    cLogArgTowerWf Dt a d c = CPolyG.cLogArgTower Dt fuel a d c := by
  rw [cLogArgTowerWf, CPolyG.cLogArgTower]
  exact cgcdFFWf_eq_of_fuel fuel d (cAmcDd Dt a d (ofConstNZ c)) hflen hfdeg hf60

open scoped Classical Differential in
/-- **`cLogArgTowerWf` realizes the abstract RT product** (transported, fuel-free): for the split
squarefree denominator `toPolyG hDen = nodal s id` and a residue `c`, the fuel-free log argument reads
under `toPolyG` as the Rothstein–Trager product `∏_{res α = c}(X − α)`. The fuel-free companion of
`cLogArgTower_toPolyG_eq_prod`, transported through the bridge `cLogArgTowerWf_eq` (its `cgcdFFWf` bounds)
and the same per-residue `cgcdFF` regularity `hreg`. -/
theorem toPolyG_cLogArgTowerWf_eq_prod (Dt : CPolyG QFunNZ) (fuel : ℕ) (hNum hDen : CPolyG QFunNZ)
    (s : Finset (CFieldSpec.K QFunNZ)) (hden : toPolyG hDen = Lagrange.nodal s id)
    (hDd : ∀ α ∈ s, (Differential.implicitDeriv (toPolyG Dt) (toPolyG hDen)).eval α ≠ 0) (c : ℚ)
    (hflen : (Compute.bnorm (if Compute.bdeg (clearDenoms hDen)
          < Compute.bdeg (clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))
        then clearDenoms hDen else clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))).length ≤ fuel)
    (hfdeg : (Compute.bnorm (if Compute.bdeg (clearDenoms hDen)
          < Compute.bdeg (clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))
        then clearDenoms hDen else clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))).length
      ≤ (Compute.bnorm (if Compute.bdeg (clearDenoms hDen)
          < Compute.bdeg (clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))
        then clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)) else clearDenoms hDen)).length)
    (hf60 : (Compute.bnorm (if Compute.bdeg (clearDenoms hDen)
          < Compute.bdeg (clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))
        then clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)) else clearDenoms hDen)).length ≤ 60)
    (hreg : PrimPRSInputs fuel
      (if Compute.bdeg (clearDenoms hDen)
            < Compute.bdeg (clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))
        then clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)) else clearDenoms hDen)
      (if Compute.bdeg (clearDenoms hDen)
            < Compute.bdeg (clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))
        then clearDenoms hDen else clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))) :
    toPolyG (cLogArgTowerWf Dt hNum hDen c)
      = ∏ α ∈ s.filter (fun α => (toPolyG hNum).eval α
            / (Differential.implicitDeriv (toPolyG Dt) (toPolyG hDen)).eval α
              = CFieldSpec.toK (ofConstNZ c)), (X - C α) := by
  rw [cLogArgTowerWf_eq Dt fuel hNum hDen c hflen hfdeg hf60]
  exact cLogArgTower_toPolyG_eq_prod Dt fuel hNum hDen s hden hDd c hreg

end CPolyG

-- The fuel-free §5.6 log-argument headline carries only the standard axioms.
#print axioms CPolyG.toPolyG_cLogArgTowerWf_eq_prod

end DeepWiki.SymbolicIntegration
