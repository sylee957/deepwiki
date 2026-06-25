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

/-! ### Target RT.3 — the fuel-free logarithmic part `cLogPartWf` (§5.6)

`cLogPart Dt fuel a d cands = [(c, gcd_t(d, a − c·Dd)) | c ∈ rational residues]` is a **composition**: the
rational residues `cRationalResidues` (a structural `filter` of `cands` by `R(c) = 0`,
`R = cResidueResultantTower`) then a structural map of `cLogArgTower`. The fuel-free companion substitutes
the fuel-free residue resultant `cResidueResultantTowerWf` (into the filter) and the fuel-free log argument
`cLogArgTowerWf` (into the map). -/

namespace CPolyG

/-- **Fuel-free rational residues** `cRationalResiduesWf Dt a d cands`: the fuel-free companion of
`cRationalResidues` — keep the candidates `c ∈ cands` that are roots of the **fuel-free** residue resultant
`R(z) = cResidueResultantTowerWf Dt a d`, i.e. `R(c) = 0` in ℚ(x) (tested by `cisZeroG [cevalG R
(ofConstNZ c)]`). A structural `filter`, the residue resultant fuel-free — **no fuel at runtime**. -/
def cRationalResiduesWf (Dt : CPolyG QFunNZ) (a d : CPolyG QFunNZ) (cands : List ℚ) : List ℚ :=
  let R := cResidueResultantTowerWf Dt a d
  cands.filter (fun c => cisZeroG [cevalG R (ofConstNZ c)])

/-- **Fuel-free logarithmic part** `cLogPartWf Dt a d cands = [(c, gcd_t(d, a − c·Dd)) | c ∈ rational
residues]`: the fuel-free companion of `cLogPart` — pair each rational residue `c` (from the fuel-free
`cRationalResiduesWf`) with its fuel-free log argument `cLogArgTowerWf Dt a d c`. A structural composition
of the fuel-free §5.6 pieces — **no fuel at runtime**; `native_decide`-able over the tower `QFunNZ`. -/
def cLogPartWf (Dt : CPolyG QFunNZ) (a d : CPolyG QFunNZ) (cands : List ℚ) :
    List (ℚ × CPolyG QFunNZ) :=
  (cRationalResiduesWf Dt a d cands).map (fun c => (c, cLogArgTowerWf Dt a d c))

end CPolyG

/-! ### Bridge of `cLogPartWf` to the fuel'd `cLogPart`, and transport

The fuel'd `cLogPart = (cRationalResidues …).map (fun c => (c, cLogArgTower … c))`. Under the residue-resultant
bridge (`cResidueResultantTowerWf = cResidueResultantTower fuel`, so the filter predicates coincide and
`cRationalResiduesWf = cRationalResidues fuel`) and the per-residue log-argument bridge
(`cLogArgTowerWf … c = cLogArgTower fuel … c` for each kept residue), the two lists coincide. The
`logResidueSum` transport `cLogPart_logResidueSum_eq_div` then carries over. -/

namespace CPolyG

/-- **Bridge — `cRationalResiduesWf` equals `cRationalResidues` at any sufficient fuel.** When the
fuel-free residue resultant agrees with the fuel'd one (`hR : cResidueResultantTowerWf Dt a d =
cResidueResultantTower Dt fuel a d`, from the per-node `cResidueResultantTowerWf_eq` bound), the filter
predicates coincide, so `cRationalResiduesWf Dt a d cands = cRationalResidues Dt fuel a d cands`. -/
theorem cRationalResiduesWf_eq (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ) (cands : List ℚ)
    (hR : cResidueResultantTowerWf Dt a d = CPolyG.cResidueResultantTower Dt fuel a d) :
    cRationalResiduesWf Dt a d cands = CPolyG.cRationalResidues Dt fuel a d cands := by
  rw [cRationalResiduesWf, CPolyG.cRationalResidues, hR]

/-- **Bridge — `cLogPartWf` equals `cLogPart` at any sufficient fuel.** From the residue-resultant bridge
`hR` (so the rational-residue lists coincide, `cRationalResiduesWf_eq`) and the per-residue log-argument
bridge `hLogArg` (`cLogArgTowerWf … c = cLogArgTower fuel … c` for every kept residue `c`),
`cLogPartWf Dt a d cands = cLogPart Dt fuel a d cands`. The fuel bounds live only in `hR`/`hLogArg`;
`cLogPartWf` carries none. -/
theorem cLogPartWf_eq (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ) (cands : List ℚ)
    (hR : cResidueResultantTowerWf Dt a d = CPolyG.cResidueResultantTower Dt fuel a d)
    (hLogArg : ∀ c ∈ cRationalResiduesWf Dt a d cands,
      cLogArgTowerWf Dt a d c = CPolyG.cLogArgTower Dt fuel a d c) :
    cLogPartWf Dt a d cands = CPolyG.cLogPart Dt fuel a d cands := by
  rw [cLogPartWf, CPolyG.cLogPart, ← cRationalResiduesWf_eq Dt fuel a d cands hR]
  -- map over the same residue list; the per-entry pair agrees by `hLogArg`
  apply List.map_congr_left
  intro c hc
  rw [hLogArg c hc]

end CPolyG

open DeepWiki.SymbolicIntegration.CPolyG QFunNZ in
open scoped Classical Differential in
/-- **`cLogPartWf` realizes the integrand `hNum/hDen` as its residue sum** (transported, fuel-free): in the
primitive split-squarefree regime, the fuel-free logarithmic part's residue sum equals the integrand over
the tower fraction field, `logResidueSum Dt (cLogPartWf Dt hNum hDen cands) = hNum/hDen`. The fuel-free
companion of `cLogPart_logResidueSum_eq_div`, transported through the bridge `cLogPartWf_eq` (the
residue-resultant + per-residue log-argument fuel agreements `hR`/`hLogArg`). -/
theorem cLogPartWf_logResidueSum_eq_div (Dt : CPolyG QFunNZ) {w₀ : CFieldSpec.K QFunNZ}
    (htop : toPolyG Dt = C w₀) (fuel : ℕ) (hNum hDen : CPolyG QFunNZ) (cands : List ℚ)
    (hR : cResidueResultantTowerWf Dt hNum hDen = CPolyG.cResidueResultantTower Dt fuel hNum hDen)
    (hLogArg : ∀ c ∈ cRationalResiduesWf Dt hNum hDen cands,
      cLogArgTowerWf Dt hNum hDen c = CPolyG.cLogArgTower Dt fuel hNum hDen c)
    (s : Finset (CFieldSpec.K QFunNZ)) (hden : toPolyG hDen = Lagrange.nodal s id)
    (hA : (toPolyG hNum).degree < s.card)
    (hb0 : ∀ α ∈ s, w₀ - α′ ≠ 0)
    (hDd : ∀ α ∈ s, (Differential.implicitDeriv (toPolyG Dt) (toPolyG hDen)).eval α ≠ 0)
    (hkeysNodup : ((CPolyG.cLogPart Dt fuel hNum hDen cands).map
        (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).Nodup)
    (hkeysImage : ((CPolyG.cLogPart Dt fuel hNum hDen cands).map
        (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).toFinset
      = s.image (fun α => (toPolyG hNum).eval α
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α))
    (hreg : ∀ c ∈ CPolyG.cRationalResidues Dt fuel hNum hDen cands, PrimPRSInputs fuel
      (if Compute.bdeg (clearDenoms hDen)
            < Compute.bdeg (clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))
        then clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)) else clearDenoms hDen)
      (if Compute.bdeg (clearDenoms hDen)
            < Compute.bdeg (clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))
        then clearDenoms hDen else clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))) :
    logResidueSum Dt (cLogPartWf Dt hNum hDen cands)
      = towerAlg (toPolyG hNum) / towerAlg (toPolyG hDen) := by
  rw [cLogPartWf_eq Dt fuel hNum hDen cands hR hLogArg]
  exact cLogPart_logResidueSum_eq_div Dt htop fuel hNum hDen cands s hden hA hb0 hDd hkeysNodup
    hkeysImage hreg

-- The fuel-free §5.6 log-part residue-sum headline carries only the standard axioms.
#print axioms cLogPartWf_logResidueSum_eq_div

/-! ### `native_decide` smoke test for the fuel-free RT trio (Bronstein Example 5.6.2, `t = log x`)

Re-runs `logPartTower_example` over the noncomputable-`CFieldSpec` tower `QFunNZ` (ℚ(x)), now **fuel-free**:
the residue resultant `R(z)` (its monic part the book's `z³ − xz² − z/4 + x/4`) and the two log-argument
gcds `t ± x` at the rational residues `c = ±1/2`, all without fuel at runtime (the RT trio carries no fuel
and no noncomputable bridge into the compiled body). Reuses the §5.6 example data of
`ComputableLogPartTower`. -/

open CPolyG QFunNZ in
/-- **The fuel-free §5.6 RT log part executes over the tower** (`native_decide`, Bronstein Example 5.6.2):
for `f = (2t²−t−x²)/(t³−x²t)`, `t = log x`, `Dt = 1/x`, the fuel-free residue resultant
`cResidueResultantTowerWf`'s monic part equals the book's `z³ − xz² − z/4 + x/4`, and the fuel-free log
arguments `cLogArgTowerWf … (±1/2) = t ± x` — the whole §5.6 residue-criterion log part now *computes*
fuel-free over the monomial tower ℚ(x)[t]. The fuel-free companion of `logPartTower_example`. -/
theorem logPartTowerWf_example :
    cisZeroG (csubG
        (cmonicG (cResidueResultantTowerWf logPartExampleDt logPartExampleA logPartExampleD))
        logPartExampleResMonic) = true
    ∧ cisZeroG (csubG (cLogArgTowerWf logPartExampleDt logPartExampleA logPartExampleD (1/2))
        logPartExampleArgPlus) = true
    ∧ cisZeroG (csubG (cLogArgTowerWf logPartExampleDt logPartExampleA logPartExampleD (-1/2))
        logPartExampleArgMinus) = true := by native_decide

#print axioms logPartTowerWf_example

/-! ### Target TOP.1 — the fuel-free reduced-case capstone `cIntegrateReducedWf`

`cIntegrateReduced Dt fuel a d cands` Hermite-reduces `f = a/d` to the rational part `g` and the simple
residual `h`, then takes the rational-residue log part of `h`. A **composition** — the fuel-free companion
substitutes `cHermiteReduceTowerWf` (`ComputableWellFounded5`) and `cLogPartWf`. -/

namespace CPolyG

/-- **Fuel-free reduced-case capstone** `cIntegrateReducedWf Dt a d cands = IntegralResult`: the fuel-free
companion of `cIntegrateReduced`. Hermite-reduce `f = a/d` with the **fuel-free** `cHermiteReduceTowerWf` to
the rational part `g = gnum/gden` and the simple residual `h = hNum/hDen` (squarefree denominator), then
take the rational-residue log part of `h` with the **fuel-free** `cLogPartWf`. Returns the `IntegralResult`
`⟨(gnum, gden), [(c, v)]⟩` — **no fuel at runtime**; stated with `.1`/`.2` projections so the bridge
`cIntegrateReducedWf_eq` rewrites cleanly. -/
def cIntegrateReducedWf (Dt : CPolyG QFunNZ) (a d : CPolyG QFunNZ) (cands : List ℚ) :
    IntegralResult :=
  let H := cHermiteReduceTowerWf Dt a d
  let logs := cLogPartWf Dt H.2.1 H.2.2 cands
  ⟨(H.1.1, H.1.2), logs⟩

end CPolyG

/-! ### Bridge of `cIntegrateReducedWf` to the fuel'd `cIntegrateReduced`

Under the Hermite bridge (`cHermiteReduceTowerWf = cHermiteReduceTower fuel`, the WF5
`cHermiteReduceTowerWf_eq_of_steps`) and the `cLogPartWf` bridge on the resulting simple residual
(`hNum/hDen`), the two `IntegralResult`s coincide. -/

namespace CPolyG

/-- **Bridge — `cIntegrateReducedWf` equals `cIntegrateReduced` at any sufficient fuel.** From the Hermite
bridge `hHermite : cHermiteReduceTowerWf Dt a d = cHermiteReduceTower Dt fuel a d` (the WF5
`cHermiteReduceTowerWf_eq_of_steps`) and the log-part bridge `hLog` on the resulting simple residual,
`cIntegrateReducedWf Dt a d cands = cIntegrateReduced Dt fuel a d cands`. The fuel bounds live only in
`hHermite`/`hLog`; `cIntegrateReducedWf` carries none. -/
theorem cIntegrateReducedWf_eq (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ) (cands : List ℚ)
    (hHermite : cHermiteReduceTowerWf Dt a d = CPolyG.cHermiteReduceTower Dt fuel a d)
    (hLog : cLogPartWf Dt (cHermiteReduceTowerWf Dt a d).2.1 (cHermiteReduceTowerWf Dt a d).2.2 cands
      = CPolyG.cLogPart Dt fuel (CPolyG.cHermiteReduceTower Dt fuel a d).2.1
          (CPolyG.cHermiteReduceTower Dt fuel a d).2.2 cands) :
    cIntegrateReducedWf Dt a d cands = CPolyG.cIntegrateReduced Dt fuel a d cands := by
  rw [cIntegrateReducedWf, CPolyG.cIntegrateReduced]
  -- the fuel'd `cIntegrateReduced` destructures `cHermiteReduceTower` via `let ((gnum,gden),(hNum,hDen))`;
  -- rewrite the Hermite result and the log part, then both sides are the same `IntegralResult`
  rw [hLog, hHermite]

end CPolyG

/-! ### The fuel-free primitive-poly bridge `cPrimitivePolyIntegrateWf = cPrimitivePolyIntegrate fuel`

`cIntegrate` integrates the polynomial part `fp` via the fuel'd `cPrimitivePolyIntegrate` (§5.8 primitive
sub-case). Its own-loop fuel-free companion `cPrimitivePolyIntegrateWf` (`ComputableWellFounded5`, proved
correct *directly* by WF induction, with no fuel'd bridge) must be related to the fuel'd op for the
`cIntegrateWf = cIntegrate fuel` composition. The two share the **identical** peeling recurrence (peel
`q₀ = c·t^(m+1)`, recurse on `p − D(q₀)`); over a genuine run the leading term cancels and the normalized
length strictly drops, so the WF guard never fails and the fuel'd version descends one step at a time. We
package the per-step length-drop as a `j`-bounded fuel-regularity predicate and bridge by WF induction. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

/-- **Per-run primitive-poly fuel-regularity** `CPrimIntRegular Dt fuel p`: mirrors the fuel'd
`cPrimitivePolyIntegrate` descent as an inductive predicate over the structural fuel counter — `stop` when
the loop is done (`(cnormG p).length ≤ 1`, only the `t⁰` term left; any fuel), or `step` when the loop
continues (`¬ (cnormG p).length ≤ 1`), the peeled leading term genuinely drops the normalized length
(`(cnormG (p − D(q₀))).length < (cnormG p).length` — the WF guard a real run meets), and the same holds
recursively on `p' = cnormG p − D(q₀)` at one less fuel (so `fuel` is sufficient). The transparent per-node
preconditions a real primitive-integration run satisfies. -/
inductive CPrimIntRegular (Dt : CPolyG α) : ℕ → CPolyG α → Prop
  /-- terminal node: the loop is done (only the `t⁰` term left), at any fuel. -/
  | stop {fuel : ℕ} {p : CPolyG α} (hdone : (cnormG p : List α).length ≤ 1) :
      CPrimIntRegular Dt fuel p
  /-- recursive node: the loop continues, the leading term drops the length, recurse on `p'`. -/
  | step {fuel : ℕ} {p : CPolyG α} (hne : ¬ (cnormG p : List α).length ≤ 1)
      (hguard : (cnormG (csubG (cnormG p) (cmonomialDeriv Dt
          (cshiftG (cdegG p + 1) [CField.div (cleadG p)
            (CField.mul (cnatCastG (cdegG p + 1)) (cleadG Dt))]))) : List α).length
        < (cnormG p : List α).length)
      (hrec : CPrimIntRegular Dt fuel (csubG (cnormG p) (cmonomialDeriv Dt
          (cshiftG (cdegG p + 1) [CField.div (cleadG p)
            (CField.mul (cnatCastG (cdegG p + 1)) (cleadG Dt))])))) :
      CPrimIntRegular Dt (fuel + 1) p

/-- **Bridge — `cPrimitivePolyIntegrateWf` equals the fuel'd `cPrimitivePolyIntegrate` on a regular run.**
Under `CPrimIntRegular Dt fuel p` (the per-step length-drop a real run meets, with sufficient fuel),
`cPrimitivePolyIntegrateWf Dt p = cPrimitivePolyIntegrate Dt fuel p`. The fuel regularity lives only here;
the WF own-loop carries none. By induction on the `CPrimIntRegular` derivation: at a `stop` node both return
`([], cnormG p)`; at a `step` node both peel the same `q₀` and recurse — the WF guard fires (`hguard`) and
the fuel'd version (at `fuel + 1`) descends. -/
theorem cPrimitivePolyIntegrateWf_eq (Dt : CPolyG α) :
    ∀ (fuel : ℕ) (p : CPolyG α), CPrimIntRegular Dt fuel p →
      cPrimitivePolyIntegrateWf Dt p = CPolyG.cPrimitivePolyIntegrate Dt fuel p := by
  intro fuel p hreg
  induction hreg with
  | @stop fuel p hdone =>
    -- both return `([], cnormG p)`: WF via `if_pos hdone`; fuel'd via `if_pos` (fuel ≥ 1) or directly
    rw [cPrimitivePolyIntegrateWf.eq_def, if_pos hdone]
    cases fuel with
    | zero => rw [CPolyG.cPrimitivePolyIntegrate]
    | succ fuel =>
      rw [CPolyG.cPrimitivePolyIntegrate]
      -- fuel'd `fuel+1` body `let p := cnormG p`, so its `if` condition is `(cnormG p).length ≤ 1 = hdone`
      rw [if_pos hdone]
  | @step fuel p hne hguard hrec ih =>
    -- both peel `q₀ = c·t^(m+1)`, recurse on `p' = cnormG p − D(q₀)`; WF guard fires, fuel'd descends
    rw [cPrimitivePolyIntegrateWf.eq_def, if_neg hne, if_pos hguard,
      CPolyG.cPrimitivePolyIntegrate, if_neg hne]
    -- the fuel'd body's `have m := cdegG (cnormG p)`/`cleadG (cnormG p)` reduce to `cdegG p`/`cleadG p`
    simp only [cdegG_cnormG, cleadG_cnormG]
    -- the recursive results agree by the IH
    rw [ih]

end CPolyG

/-! ### Target TOP.2 — the fuel-free top-level integrator `cIntegrateWf` (the goal)

`cIntegrate Dt fuel a d cands` (Bronstein Ch. 5, assembled) splits `f = fₚ + fₛ + fₙ`
(`canonicalRepresentationFast`), integrates the simple normal part via `cIntegrateReduced`, integrates the
polynomial part via `cPrimitivePolyIntegrate`, and returns `some` (combining the rational parts) when the
polynomial remainder vanishes, else `none`. A pure **composition** — no new recursion. The fuel-free
companion `cIntegrateWf` substitutes the three now-fuel-free sub-ops: `canonicalRepresentationFastWf`
(`ComputableWellFounded4`), `cPrimitivePolyIntegrateWf` (`ComputableWellFounded5`), and `cIntegrateReducedWf`. -/

namespace CPolyG

/-- **The fuel-free top-level transcendental Risch integrator** `cIntegrateWf Dt a d cands` (Bronstein Ch.
5, the goal): the fuel-free companion of `cIntegrate`, integrating `f = a/d ∈ ℚ(x)(t)` over the monomial
derivation `D = cmonomialDeriv Dt`, returning `some ⟨(gnum, gden), [(cᵢ, vᵢ)]⟩` with `∫ f = gnum/gden + ∑ᵢ
cᵢ·log(vᵢ)`, or `none` if `∫ f` is **not elementary**. Identical assembly to `cIntegrate` — canonical split
+ reduced capstone + primitive polynomial part — but with every fuel'd sub-op replaced by its fuel-free
companion: `canonicalRepresentationFastWf`, `cIntegrateReducedWf`, `cPrimitivePolyIntegrateWf`. A pure
composition, **no fuel at runtime**; `native_decide`-able over the noncomputable-`CFieldSpec` tower `QFunNZ`.
Stated with `.1`/`.2` projections so the bridge `cIntegrateWf_eq` rewrites cleanly. -/
def cIntegrateWf (Dt : CPolyG QFunNZ) (a d : CPolyG QFunNZ) (cands : List ℚ) :
    Option IntegralResult :=
  let split := canonicalRepresentationFastWf Dt a d
  let cn := split.2.2.1
  let dn := split.2.2.2
  let fp := split.1
  -- (2) simple normal part `fₙ = cn/dn`.
  let nrm := cIntegrateReducedWf Dt cn dn cands
  -- (3) polynomial part `fₚ = fp`: primitive constant-coefficient integration.
  let pr := cPrimitivePolyIntegrateWf Dt fp
  if cisZeroG pr.2 then
    let gnum := caddG (cmulG nrm.rational.1 [CField.one]) (cmulG pr.1 nrm.rational.2)
    let gden := nrm.rational.2
    some ⟨(gnum, gden), nrm.logs⟩
  else
    none

end CPolyG

/-! ### Bridge of `cIntegrateWf` to the fuel'd `cIntegrate`, threading the sub-bridges

`cIntegrateWf = cIntegrate fuel` under the three sub-bridges: the canonical split
(`canonicalRepresentationFastWf_eq`, the `CCanonicalRepFastWfRegular` gate), the reduced capstone
(`cIntegrateReducedWf_eq`), and the primitive polynomial part (`cPrimitivePolyIntegrateWf_eq`, the
`CPrimIntRegular` gate). Since the assembly is a pure composition, rewriting each sub-result collapses the
two drivers. The fuel bounds live only in the bridge hypotheses; `cIntegrateWf` carries none. -/

namespace CPolyG

/-- **Bridge — `cIntegrateWf` equals `cIntegrate` at any sufficient fuel.** From the two sub-bridges that
the canonical split (`canonicalRepresentationFastWf_eq`) feeds — the reduced capstone `hred` on the
resulting normal part `(cn, dn)` and the primitive polynomial part `hpoly : cPrimitivePolyIntegrateWf Dt fp
= cPrimitivePolyIntegrate Dt fuel fp` on the resulting polynomial part `fp`, both already carrying the
fuel'd `canonicalRepresentationFast Dt fuel a d` on the right — `cIntegrateWf Dt a d cands = cIntegrate Dt
fuel a d cands`. The fuel bounds live only in the hypotheses; `cIntegrateWf` carries none. A pure
composition rewrite: `hred`/`hpoly` carry the entire LHS into fuel'd form, and the RHS's
`match (fp,(_b,_ds),cn,dn) := …` collapses to the `.1`/`.2.2.1`/`.2.2.2` projections by `Prod.eta`. -/
theorem cIntegrateWf_eq (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ) (cands : List ℚ)
    (hred : cIntegrateReducedWf Dt (canonicalRepresentationFastWf Dt a d).2.2.1
        (canonicalRepresentationFastWf Dt a d).2.2.2 cands
      = CPolyG.cIntegrateReduced Dt fuel (CPolyG.canonicalRepresentationFast Dt fuel a d).2.2.1
          (CPolyG.canonicalRepresentationFast Dt fuel a d).2.2.2 cands)
    (hpoly : cPrimitivePolyIntegrateWf Dt (canonicalRepresentationFastWf Dt a d).1
      = CPolyG.cPrimitivePolyIntegrate Dt fuel (CPolyG.canonicalRepresentationFast Dt fuel a d).1) :
    cIntegrateWf Dt a d cands = CPolyG.cIntegrate Dt fuel a d cands := by
  rw [cIntegrateWf, CPolyG.cIntegrate]
  -- rewrite the reduced and polynomial sub-results; after these the LHS is entirely in fuel'd form and
  -- the RHS's `match (fp,(_b,_ds),cn,dn) := canonicalRepresentationFast fuel a d` collapses to the `.1`/
  -- `.2.2.1`/`.2.2.2` projections (`Prod.eta` defeq), closing the goal by the trailing `rfl`.
  rw [hred, hpoly]

end CPolyG

/-! ### Target TOP.3 — the fuel-free self-validating integrator `cIntegrateCheckedWf` (the headline)

The raw `cIntegrateWf` (like the fuel'd `cIntegrate`) returns its `IntegralResult` **without** re-validating
it against the antiderivative identity, so out of its documented scope it can emit a wrong `some res`. The
**checked wrapper** `cIntegrateCheckedWf` guards `cIntegrateWf` by the engine's own cleared antiderivative
check `IntegralResult.checkIdentity` — returning `some res` only when `checkIdentity Dt res a d = true`.

Its correctness `cIntegrateCheckedWf_correct` is **UNCONDITIONAL** (all inputs, all regimes) and crucially
**engine-independent**: `cIntegrateCheckedWf = some res` forces `checkIdentity Dt res a d = true` (pure
`Option.bind` reasoning), and the converse bridge `field_identity_of_checkIdentity` (which works on *any*
`res`, no reference to `cIntegrate`/`cIntegrateWf`) turns that into the field identity `D(res) = f`. So **no
bridge to the fuel'd `cIntegrate` is needed** — the `checkIdentity` guard alone supplies correctness. This
is the cleanest fuel-free headline: the self-validating integrator that never returns a wrong answer. -/

namespace CPolyG

/-- **The fuel-free self-validating integrator** `cIntegrateCheckedWf Dt a d cands`: run the fuel-free
engine `cIntegrateWf`, then **guard** its output by the engine's own cleared antiderivative check
`IntegralResult.checkIdentity`. Returns `some res` only when `checkIdentity Dt res a d = true` (i.e. `res`
is a genuine antiderivative of `f = a/d`), and `none` otherwise — so it never returns a wrong answer. The
fuel-free companion of `cIntegrateChecked`: a thin wrapper that does **not** modify `cIntegrateWf`. **No
fuel at runtime**; `native_decide`-able over the tower `QFunNZ`. -/
def cIntegrateCheckedWf (Dt : CPolyG QFunNZ) (a d : CPolyG QFunNZ) (cands : List ℚ) :
    Option IntegralResult :=
  (cIntegrateWf Dt a d cands).bind
    (fun res => if IntegralResult.checkIdentity Dt res a d then some res else none)

end CPolyG

open IntegralResult in
/-- **`cIntegrateCheckedWf f = some res ⟹ D(res) = f`**, the ultimate fuel-free integrator-correctness
statement — **UNCONDITIONAL**, for ALL inputs and ALL regimes (primitive, hyperexponential, anything),
**fuel-free**. If `cIntegrateCheckedWf Dt a d cands = some res`, then the field-level antiderivative
identity `towerFractionFieldDeriv Dt (g) + logResidueSum Dt res.logs = a/d` holds over the tower fraction
field `RatFunc (RatFunc ℚ)`, where `g = towerAlg(res.rational.1)/towerAlg(res.rational.2)`. The only side
conditions are the structural nonzero-denominator hypotheses (`gden`, `d`, every log argument `vᵢ` nonzero)
the field statement needs; **no** regime / `fₛ = 0` / residue-set / degree / fuel hypothesis is required —
the `checkIdentity` guard inside `cIntegrateCheckedWf` supplies all of that. Immediate from the wrapper
definition (`some` forces `checkIdentity = true`) and the **engine-agnostic** converse bridge
`field_identity_of_checkIdentity` — *no bridge to the fuel'd `cIntegrate` is used*. The fuel-free companion
of `cIntegrateChecked_correct`. -/
theorem cIntegrateCheckedWf_correct (Dt : CPolyG QFunNZ) (a d : CPolyG QFunNZ)
    (cands : List ℚ) (res : IntegralResult)
    (hsome : CPolyG.cIntegrateCheckedWf Dt a d cands = some res)
    (hgden : toPolyG res.rational.2 ≠ 0) (hdne : toPolyG d ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPolyG cv.2 ≠ 0) :
    towerFractionFieldDeriv Dt (towerAlg (toPolyG res.rational.1) / towerAlg (toPolyG res.rational.2))
        + logResidueSum Dt res.logs
      = towerAlg (toPolyG a) / towerAlg (toPolyG d) := by
  -- the wrapper returned `some res`, so the guard `checkIdentity` fired `true` (pure `Option.bind`)
  have hcheck : IntegralResult.checkIdentity Dt res a d = true := by
    rw [CPolyG.cIntegrateCheckedWf] at hsome
    rcases hci : CPolyG.cIntegrateWf Dt a d cands with _ | res'
    · rw [hci] at hsome; simp only [Option.bind_none] at hsome; exact absurd hsome (by simp)
    · rw [hci] at hsome
      simp only [Option.bind_some] at hsome
      by_cases hc : IntegralResult.checkIdentity Dt res' a d
      · simp only [hc, if_true, Option.some.injEq] at hsome
        rw [← hsome]; exact hc
      · simp only [hc] at hsome; exact absurd hsome (by simp)
  -- the engine-agnostic converse bridge turns the guard into the field identity (no fuel'd reference)
  exact field_identity_of_checkIdentity Dt res a d hgden hdne hlogs hcheck

-- The HEADLINE (fuel-free): the self-validating integrator never returns a wrong answer.
-- `cIntegrateCheckedWf f = some res` ⟹ `D(res) = f` over the tower fraction field — UNCONDITIONAL, for
-- EVERY input and EVERY regime, with NO fuel and NO bridge to the fuel'd engine. The `checkIdentity` guard
-- alone supplies correctness; the only side conditions are the structural nonzero-denominator facts.
example (Dt : CPolyG QFunNZ) (a d : CPolyG QFunNZ) (cands : List ℚ) (res : IntegralResult)
    (hsome : CPolyG.cIntegrateCheckedWf Dt a d cands = some res)
    (hgden : toPolyG res.rational.2 ≠ 0) (hdne : toPolyG d ≠ 0)
    (hlogs : ∀ cv ∈ res.logs, toPolyG cv.2 ≠ 0) :
    towerFractionFieldDeriv Dt (towerAlg (toPolyG res.rational.1) / towerAlg (toPolyG res.rational.2))
        + logResidueSum Dt res.logs
      = towerAlg (toPolyG a) / towerAlg (toPolyG d) :=
  cIntegrateCheckedWf_correct Dt a d cands res hsome hgden hdne hlogs

-- The fuel-free self-validating integrator's headline carries only the standard axioms.
#print axioms cIntegrateCheckedWf_correct

/-! ### `native_decide` — the fuel-free integrator on Bronstein's Example 5.6.2 (`t = log x`)

Re-runs `integrate_example`/`integrate_example_driver`/`cIntegrateChecked` over the noncomputable-`CFieldSpec`
tower `QFunNZ` (ℚ(x)), now **fuel-free** end-to-end. The validated transcendental integrand is
`f = (1/2)·D(t+x)/(t+x) − (1/2)·D(t−x)/(t−x)` over ℚ(x)(log x) (`Dt = 1/x`), whose elementary antiderivative
is `(1/2)log(t+x) − (1/2)log(t−x)`. The fuel-free `cIntegrateReducedWf`/`cIntegrateWf` recover it (Hermite
`g = 0`, rational residues `±1/2`), and the antiderivative identity `D(∫f) = f` holds — checked, cleared of
denominators, by `IntegralResult.checkIdentity`. Reuses the §5.6 example data of `ComputableIntegrate`. -/

open CPolyG QFunNZ in
/-- **The fuel-free reduced capstone integrates the transcendental integrand, `D(∫f) = f`** (`native_decide`,
Bronstein Example 5.6.2, `t = log x`): `cIntegrateReducedWf` returns an `IntegralResult` whose antiderivative
identity holds exactly — the fuel-free analog of `integrate_example`, the whole RT log part end-to-end with
**no fuel at runtime**. -/
theorem integrateReducedWf_example :
    IntegralResult.checkIdentity integrateExampleDt
      (cIntegrateReducedWf integrateExampleDt integrateExampleNum integrateExampleDen
        integrateExampleCands)
      integrateExampleNum integrateExampleDen = true := by native_decide

open CPolyG QFunNZ in
/-- **The fuel-free top-level `cIntegrateWf` runs end-to-end and `D(∫f) = f`** (`native_decide`, the goal on
Example 5.6.2): on the transcendental integrand (a pure simple/normal element, `fₚ = fₛ = 0`), the
fuel-free `cIntegrateWf` — canonical split + reduced capstone + (empty) polynomial part — returns `some res`
satisfying the antiderivative identity `D(res) = f`. The fuel-free analog of `integrate_example_driver`;
pins the assembled fuel-free driver, **no fuel at runtime**. -/
theorem integrateWf_example_driver :
    (match cIntegrateWf integrateExampleDt integrateExampleNum integrateExampleDen
        integrateExampleCands with
      | some res => IntegralResult.checkIdentity integrateExampleDt res
          integrateExampleNum integrateExampleDen
      | none => false) = true := by native_decide

open CPolyG QFunNZ in
/-- **The fuel-free self-validating `cIntegrateCheckedWf` returns `some` on the genuine integral**
(`native_decide`, Example 5.6.2): on the transcendental integrand with a true elementary antiderivative, the
checked wrapper's guard `checkIdentity` fires `true`, so `cIntegrateCheckedWf … = some res` — it accepts the
correct answer (cf. `cIntegrateCheckedWf_correct`, which then certifies `D(res) = f`). **No fuel at
runtime**. -/
theorem integrateCheckedWf_example_isSome :
    (cIntegrateCheckedWf integrateExampleDt integrateExampleNum integrateExampleDen
      integrateExampleCands).isSome = true := by native_decide

open CPolyG QFunNZ in
/-- **`cIntegrateWf` agrees with the fuel'd `cIntegrate`** on Example 5.6.2 (`native_decide`): both return
`some res` passing `checkIdentity`, so the fuel-free driver matches the fuel'd one on the book example. -/
theorem integrateWf_eq_fueled_example :
    (match cIntegrateWf integrateExampleDt integrateExampleNum integrateExampleDen
        integrateExampleCands,
        cIntegrate integrateExampleDt 30 integrateExampleNum integrateExampleDen integrateExampleCands with
      | some r1, some r2 =>
          IntegralResult.checkIdentity integrateExampleDt r1 integrateExampleNum integrateExampleDen
          && IntegralResult.checkIdentity integrateExampleDt r2 integrateExampleNum integrateExampleDen
      | _, _ => false) = true := by native_decide

#print axioms integrateWf_example_driver

/-! ### Transport of the all-inputs `D(cIntegrateWf f) = f` to the raw fuel-free integrator (primitive regime)

For the **raw** (unchecked) fuel-free `cIntegrateWf`, the all-inputs antiderivative correctness in the
primitive split-squarefree regime — `cIntegrate_checkIdentity_uncond` — transports through the bridge
`cIntegrateWf_eq`: under the same transparent regularity/exact-division/fuel + residue-set data the fuel'd
headline carries, *plus* the bridge equation `hbridge : cIntegrateWf Dt a d cands = cIntegrate Dt fuel a d
cands` (assembled from the three sub-bridges), `cIntegrateWf Dt a d cands = some res` with
`IntegralResult.checkIdentity Dt res a d = true`. Rewriting `hbridge` reduces it to the fuel'd headline. -/

open DeepWiki.SymbolicIntegration.CPolyG QFunNZ in
open scoped Classical Differential in
/-- **`cIntegrateWf` returns `some res` with `D(res) = f`** for ALL inputs in the primitive regime,
**fuel-free** (transported): the fuel-free companion of `cIntegrate_checkIdentity_uncond`. Under the bridge
`hbridge : cIntegrateWf Dt a d cands = cIntegrate Dt fuel a d cands` and the same hypotheses the fuel'd
headline carries (canonical-rep regularity, Hermite exact-division/nonzero-divisor/fuel preconditions,
absent special part `hfs0 : fₛ = 0`, all denominators nonzero, the §5.6 split-squarefree residue-set
data + per-residue `cgcdFF` regularity), `cIntegrateWf Dt a d cands = some res` and the engine's cleared
antiderivative identity `IntegralResult.checkIdentity Dt res a d = true` holds — i.e. `D(g) + ∑ᵢ
cᵢ·(D(vᵢ)/vᵢ) = f` cleared of denominators. Rewrites `hbridge` to the fuel'd `cIntegrate` and applies
`cIntegrate_checkIdentity_uncond`. -/
theorem cIntegrateWf_checkIdentity_uncond (Dt : CPolyG QFunNZ) {w₀ : CFieldSpec.K QFunNZ}
    (htop : toPolyG Dt = C w₀) (fuel : ℕ) (a d : CPolyG QFunNZ) (cands : List ℚ)
    (hbridge : CPolyG.cIntegrateWf Dt a d cands = CPolyG.cIntegrate Dt fuel a d cands)
    (fp b ds cn dn : CPolyG QFunNZ)
    (hcanon : canonicalRepresentationFast Dt fuel a d = (fp, (b, ds), (cn, dn)))
    (gnumH gdenH hNum hDen : CPolyG QFunNZ)
    (hHermite : cHermiteReduceTower Dt fuel cn dn = ((gnumH, gdenH), (hNum, hDen)))
    (pq prem : CPolyG QFunNZ)
    (hpoly : cPrimitivePolyIntegrate Dt fuel fp = (pq, prem))
    (hpremZero : cisZeroG prem = true)
    (hcanreg : CCanonicalRepFastRegular Dt fuel a d)
    (hfs0 : towerAlg (toPolyG b) / towerAlg (toPolyG ds) = 0)
    (gprimeNum resNum resDen : CPolyG QFunNZ)
    (hgprimeE : gprimeNum
      = csubG (cmulG (cmonomialDeriv Dt gnumH) gdenH) (cmulG gnumH (cmonomialDeriv Dt gdenH)))
    (hresNum : resNum = csubG (cmulG cn (cmulG gdenH gdenH)) (cmulG dn gprimeNum))
    (hresDen : resDen = cmulG dn (cmulG gdenH gdenH))
    (hhNumE : hNum = cdivG fuel (cmulG resNum hDen) resDen)
    (hq0 : cnormG resDen ≠ [])
    (hfuelH : (cnormG (cmulG resNum hDen) : List QFunNZ).length ≤ fuel)
    (hdvd : toPolyG resDen ∣ toPolyG (cmulG resNum hDen))
    (hgdenHne : toPolyG gdenH ≠ 0) (hHDenne : toPolyG hDen ≠ 0) (hdnne : toPolyG dn ≠ 0)
    (hlognz : ∀ cv ∈ cLogPart Dt fuel hNum hDen cands, toPolyG cv.2 ≠ 0)
    (s : Finset (CFieldSpec.K QFunNZ)) (hden : toPolyG hDen = Lagrange.nodal s id)
    (hAh : (toPolyG hNum).degree < s.card)
    (hb0 : ∀ α ∈ s, w₀ - α′ ≠ 0)
    (hDd : ∀ α ∈ s, (Differential.implicitDeriv (toPolyG Dt) (toPolyG hDen)).eval α ≠ 0)
    (hadeg : (toPolyG hNum).natDegree ≤ (toPolyG hDen).natDegree)
    (hδdeg : (Differential.implicitDeriv (toPolyG Dt) (toPolyG hDen)).natDegree
      ≤ (toPolyG hDen).natDegree)
    (hamc : ∀ k ∈ Finset.range (cdegG hDen + 1),
      (toPolyG (cAmcDd Dt hNum hDen (ofConstNZ (k : ℚ)))).natDegree ≤ (toPolyG hDen).natDegree)
    (hfuelR : ∀ k ∈ Finset.range (cdegG hDen + 1),
      (cnormG hDen : List QFunNZ).length
        + (cnormG (cAmcDd Dt hNum hDen (ofConstNZ (k : ℚ))) : List QFunNZ).length + 2 ≤ fuel)
    (hcompl : ∀ α ∈ s, ∃ c ∈ cands, (toPolyG hNum).eval α
        / (Differential.implicitDeriv (toPolyG Dt) (toPolyG hDen)).eval α
          = CFieldSpec.toK (ofConstNZ c))
    (hdistinct : (cands.filter (fun c =>
        cisZeroG [cevalG (cResidueResultantTower Dt fuel hNum hDen) (ofConstNZ c)])).map
        (fun c => CFieldSpec.toK (ofConstNZ c)) |>.Nodup)
    (hreg : ∀ c ∈ cRationalResidues Dt fuel hNum hDen cands, PrimPRSInputs fuel
      (if Compute.bdeg (clearDenoms hDen)
            < Compute.bdeg (clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))
        then clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)) else clearDenoms hDen)
      (if Compute.bdeg (clearDenoms hDen)
            < Compute.bdeg (clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))
        then clearDenoms hDen else clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))) :
    ∃ res : IntegralResult, CPolyG.cIntegrateWf Dt a d cands = some res
      ∧ IntegralResult.checkIdentity Dt res a d = true := by
  rw [hbridge]
  exact cIntegrate_checkIdentity_uncond Dt htop fuel a d cands fp b ds cn dn hcanon gnumH gdenH hNum
    hDen hHermite pq prem hpoly hpremZero hcanreg hfs0 gprimeNum resNum resDen hgprimeE hresNum
    hresDen hhNumE hq0 hfuelH hdvd hgdenHne hHDenne hdnne hlognz s hden hAh hb0 hDd hadeg hδdeg hamc
    hfuelR hcompl hdistinct hreg

-- The fuel-free raw-integrator antiderivative-correctness headline carries only the standard axioms.
#print axioms cIntegrateWf_checkIdentity_uncond

end DeepWiki.SymbolicIntegration
