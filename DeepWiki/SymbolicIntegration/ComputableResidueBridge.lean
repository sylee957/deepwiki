import DeepWiki.SymbolicIntegration.ComputableIntegrateCorrect

/-! # The concrete-list → abstract-residue bridge for the §5.6 log part (discharging `hLog`)
`cIntegrate_checkIdentity` (`ComputableIntegrateCorrect`) proves `D(cIntegrate f) = f` in the primitive
regime gated on **one** named hypothesis `hLog : logResidueSum Dt (cLogPart Dt fuel hNum hDen cands) =
hNum/hDen` — the §5.6 Rothstein–Trager log-part identity for the **concrete** `cLogPart` output. This
file bridges the concrete residue computation (`cResidueResultantTower`/`cLogArgTower`/`cLogPart`,
`ComputableLogPartTower`) to the **abstract** split-field residue identity already proven
(`towerLogPart_eq_div_of_const_seed`, `ComputableLogPartTowerCorrect`, over `Finset K` /
`Lagrange.nodal` / `gcd(d, a − c·Δd)` residues).

The structure mirrors §2's `RationalIntegrationGcdLogForm` (the d/dx Czichowski gcd-log form), which
proved `gcd(D, A − a·D') = ∏_{res(α)=a}(X−α)` for `D' = derivative D`. The §5.6 case needs the **seed**
`Dd = Δd = implicitDeriv (toPolyG Dt) d` in place of `derivative d`. This file proves:

* **The seed-generic Czichowski gcd-product identity** (`gcd_nodal_eq_prod_residue_seed`): over a split
  squarefree `d = nodal s id = ∏_{α∈s}(X−α)`, for an arbitrary residue-denominator seed `Dd` nonzero at
  each root, `gcd(d, A − C c·Dd) = ∏_{α: A(α)/Dd(α)=c}(X−α)` — the polynomial that `cLogArgTower`'s
  `gcd_t(d, a − c·Dd)` realizes (up to a unit, via `cgcdFF`). The seed generalization of §2's
  `gcd_nodal_eq_prod_residue`.
* **The abstract `hLog` reduction** (`logResidueSum_eq_div_of_residueData`): packaging the precise
  concrete→abstract correspondence (the split squarefree `toPolyG hDen = nodal s id`, the list-of-residues
  ↔ `s.image res` match, the per-log-argument `toPolyG vᵢ = gcd(...)` match, and the constant-seed
  primitive regime) as transparent hypotheses, the concrete `logResidueSum` equals the integrand `hNum/hDen`
  by feeding the abstract `towerLogPart_eq_div_of_const_seed`. The remaining gap to a fully self-contained
  discharge is the **residue-set correspondence** itself (that `cRationalResidues`/`cgcdFF` produce exactly
  `s.image res`/`gcd(...)`) — which needs the generic `cresultantG`/`cinterpolateG` abstract correctness
  (the §2 `cresultant_eq`/`toPoly_cinterpolate_eval` template, generalized off the concrete ℚ carrier to
  `CFieldSpec`), not yet built. The reduction here isolates exactly that gap as the `hresidueData` bundle. -/

open Polynomial

open scoped Classical Differential

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

open scoped Classical in
/-- **Seed-generic Czichowski gcd-product identity** (the §5.6 monomial-seed analogue of §2's
`gcd_nodal_eq_prod_residue`): for split squarefree `d = Lagrange.nodal s id = ∏_{α∈s}(X−α)` and an
arbitrary residue-denominator seed `Dd` that is **nonzero at every root** of `d`, the gcd
`gcd(d, A − C c·Dd)` factors as the product of `(X−α)` over the roots `α` of `d` whose §5.6 residue
`A(α)/Dd(α)` equals `c`. This is exactly the Rothstein–Trager log argument `gᶜ = ∏_{res α = c}(X−α)`
realized by `cLogArgTower … c = gcd_t(d, a − c·Dd)` (with `Dd = Δd`). Proved by `isRoot_gcd_iff_residue_seed`
(the seed-generic root criterion) + the gcd splits as a monic product of those linear factors (it divides
the separable `d`, so its roots are nodup). The §2 case is `Dd = derivative d` (then `Dd(α) = d'(α) ≠ 0`
at simple roots by separability). -/
theorem gcd_nodal_eq_prod_residue_seed (s : Finset K) (A Dd : K[X])
    (hDd : ∀ α ∈ s, Dd.eval α ≠ 0) (c : K) :
    gcd (Lagrange.nodal s id) (A - C c * Dd)
      = ∏ α ∈ s.filter (fun α => A.eval α / Dd.eval α = c), (X - C α) := by
  set d := Lagrange.nodal s id with hd
  set res : K → K := fun α => A.eval α / Dd.eval α with hres
  set E := A - C c * Dd with hE
  -- `d = ∏_{α∈s}(X − α)` (the split form); `d` separable, monic, nonzero, roots `s`
  have hdprod : d = ∏ α ∈ s, (X - C α) := by simp [hd, Lagrange.nodal_eq, id]
  have hdsep : d.Separable := by
    rw [hdprod]; exact separable_prod_X_sub_C_iff'.mpr fun _ _ _ _ h => h
  have hdmonic : d.Monic := hd ▸ Lagrange.nodal_monic
  have hd0 : d ≠ 0 := hd ▸ Lagrange.nodal_ne_zero
  have hdroots : d.roots = s.val := by rw [hdprod, roots_prod_X_sub_C]
  -- `gcd d E` is separable (divides `d`), splits, is monic and nonzero
  have hgsep : (gcd d E).Separable := hdsep.of_dvd (gcd_dvd_left _ _)
  have hg0 : gcd d E ≠ 0 := fun h => hd0 (zero_dvd_iff.mp (h ▸ gcd_dvd_left d E))
  have hgmonic : (gcd d E).Monic := normalize_gcd d E ▸ monic_normalize hg0
  have hdsplits : d.Splits := by
    rw [hdprod]; exact Splits.prod fun α _ => Splits.X_sub_C _
  have hgsplits : (gcd d E).Splits := hdsplits.of_dvd hd0 (gcd_dvd_left d E)
  -- the roots of the gcd are exactly the residue-`c` roots of `d`, i.e. `(filter).val`
  have hroots : (gcd d E).roots = (s.filter (fun α => res α = c)).val := by
    refine Multiset.Nodup.ext (nodup_roots hgsep) (s.filter (fun α => res α = c)).nodup |>.mpr
      fun α => ?_
    rw [mem_roots hg0, Finset.mem_val, Finset.mem_filter]
    constructor
    · intro hα
      have hdα : d.IsRoot α := dvd_iff_isRoot.mp ((dvd_iff_isRoot.mpr hα).trans (gcd_dvd_left d E))
      have hαs : α ∈ s := by
        have : α ∈ s.val := hdroots ▸ (mem_roots hd0).mpr hdα
        exact this
      obtain ⟨_, hres'⟩ := (isRoot_gcd_iff_residue_seed A d Dd c α (hDd α hαs)).mp hα
      exact ⟨hαs, hres'⟩
    · rintro ⟨hαs, hres'⟩
      have hdα : d.IsRoot α := (mem_roots hd0).mp (hdroots ▸ hαs)
      exact (isRoot_gcd_iff_residue_seed A d Dd c α (hDd α hαs)).mpr ⟨hdα, hres'⟩
  rw [hgsplits.eq_prod_roots_of_monic hgmonic, hroots, Finset.prod_eq_multiset_prod]

open scoped Classical in
/-- Restatement: the seed-generic Czichowski gcd-product identity `gcd(d, A − c·Dd) = ∏_{res α = c}(X−α)`
for split squarefree `d = nodal s id`, with the residue seed `Dd` nonzero at each root. -/
example (s : Finset K) (A Dd : K[X]) (hDd : ∀ α ∈ s, Dd.eval α ≠ 0) (c : K) :
    gcd (Lagrange.nodal s id) (A - C c * Dd)
      = ∏ α ∈ s.filter (fun α => A.eval α / Dd.eval α = c), (X - C α) :=
  gcd_nodal_eq_prod_residue_seed s A Dd hDd c

#print axioms gcd_nodal_eq_prod_residue_seed

/-! ### The abstract `hLog` reduction — the concrete residue sum equals the integrand `A/d`

`logResidueSum Dt logs` (`ComputableIntegrateCorrect`) is the `List.sum`
`∑_{(c,v)∈logs} towerAlg(C(toK(ofConstNZ c)))·(Δv)/v` over the concrete log list. The §5.6 abstract
residue match `sum_residue_grouped_logDeriv_eq_div` (`ComputableLogPartTowerCorrect`) gives the
`Finset.sum` over distinct residues `∑_{c∈s.image res} algMap(C c)·(δgᶜ)/gᶜ = algMap A/algMap d`. The
reduction below converts the concrete `List.sum` to the abstract `Finset.sum` and discharges it,
**given the structural correspondence** between the two indexings as transparent hypotheses (the
documented residue-set match): the concrete denominator splits as `toPolyG hDen = nodal s id` over
`RatFunc ℚ` (the primitive split squarefree), the residue list's values `toK(ofConstNZ c)` enumerate
the distinct residues `s.image res` without repetition, and each concrete log argument
`toPolyG v = gᶜ`. -/

open DeepWiki.SymbolicIntegration.CPolyG QFunNZ

open scoped Classical in
/-- **The concrete `logResidueSum` equals the abstract residue-grouped sum** (the list→Finset
reindexing): writing `K := CFieldSpec.K QFunNZ = RatFunc ℚ`, `δ := implicitDeriv (toPolyG Dt)`,
`A := toPolyG hNum`, `d := Lagrange.nodal s id`, and `res α := A(α)/(δ d)(α)`, suppose the concrete log
list `logs` corresponds to the distinct-residue Finset data via an injective-on-`logs.map Prod.fst` tag
map `e c := CFieldSpec.toK (ofConstNZ c)` whose image is exactly `s.image res` and which is nodup on the
list keys, and each concrete log argument reads as the abstract Rothstein–Trager factor
`toPolyG v = ∏_{res α = e c}(X−α)`. Then `logResidueSum Dt logs` equals the abstract grouped sum
`∑_{c∈s.image res} towerAlg(C c)·(towerAlg(δ gᶜ)/towerAlg(gᶜ))`. The `List.sum`↔`Finset.sum` bridge of
the residue match. -/
theorem logResidueSum_eq_grouped (Dt : CPolyG QFunNZ) (hNum : CPolyG QFunNZ)
    (logs : List (ℚ × CPolyG QFunNZ)) (s : Finset (CFieldSpec.K QFunNZ))
    (hkeysNodup : (logs.map (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).Nodup)
    (hkeysImage : (logs.map (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).toFinset
      = s.image (fun α => (toPolyG hNum).eval α
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α))
    (harg : ∀ cv ∈ logs, toPolyG cv.2
      = ∏ α ∈ s.filter (fun α => (toPolyG hNum).eval α
            / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α
              = CFieldSpec.toK (ofConstNZ cv.1)), (X - C α)) :
    logResidueSum Dt logs
      = ∑ c ∈ s.image (fun α => (toPolyG hNum).eval α
            / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α),
          towerAlg (Polynomial.C c)
            * (towerAlg (Differential.implicitDeriv (toPolyG Dt)
                  (∏ α ∈ s.filter (fun α => (toPolyG hNum).eval α
                      / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α = c),
                    (X - C α)))
                / towerAlg (∏ α ∈ s.filter (fun α => (toPolyG hNum).eval α
                      / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α = c),
                    (X - C α))) := by
  classical
  set A := toPolyG hNum with hA
  set δ := Differential.implicitDeriv (toPolyG Dt) with hδ
  set d := Lagrange.nodal s id with hd
  set res : CFieldSpec.K QFunNZ → CFieldSpec.K QFunNZ := fun α => A.eval α / (δ d).eval α with hres
  set e : ℚ × CPolyG QFunNZ → CFieldSpec.K QFunNZ := fun cv => CFieldSpec.toK (ofConstNZ cv.1) with he
  -- the abstract grouped term at a residue value `c`
  set F : CFieldSpec.K QFunNZ → RatFunc (CFieldSpec.K QFunNZ) := fun c =>
    towerAlg (Polynomial.C c)
      * (towerAlg (δ (∏ α ∈ s.filter (fun α => res α = c), (X - C α)))
          / towerAlg (∏ α ∈ s.filter (fun α => res α = c), (X - C α))) with hF
  -- rewrite `logResidueSum` (a `List.sum`) as a sum of `F (e cv)` over the list, via `harg`
  have hterm : ∀ cv ∈ logs,
      towerAlg (Polynomial.C (CFieldSpec.toK (ofConstNZ cv.1)))
          * (towerAlg (toPolyG (cmonomialDeriv Dt cv.2)) / towerAlg (toPolyG cv.2))
        = F (e cv) := by
    intro cv hcv
    rw [hF, he, toPolyG_cmonomialDeriv, harg cv hcv]
  -- the list sum of `F ∘ e` over `logs` equals the list sum of `F` over the residue-value keys
  have hlistsum : logResidueSum Dt logs = ((logs.map e).map F).sum := by
    rw [logResidueSum, List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro cv hcv; simpa using hterm cv hcv
  -- the Finset sum over `s.image res = (logs.map e).toFinset`, folded back into the residue-value list
  rw [hlistsum, ← hkeysImage]
  exact (List.sum_toFinset F hkeysNodup).symm

open scoped Classical Differential in
/-- **The abstract `hLog` discharge** (`logResidueSum Dt logs = hNum/hDen`, primitive regime): in the
primitive regime `toPolyG Dt = C w₀` (`Dt ∈ k = ℚ(x)`), if the concrete denominator splits as
`toPolyG hDen = Lagrange.nodal s id` over `RatFunc ℚ` (the split squarefree primitive simple element),
the numerator degree is `< #s`, the normality `w₀ − α′ ≠ 0` holds at each root, and the concrete log
list `logs` corresponds to the distinct-residue data (`hkeysNodup`/`hkeysImage`/`harg`, the residue-set
match), then the concrete residue sum `logResidueSum Dt logs` equals the integrand
`towerAlg(toPolyG hNum)/towerAlg(toPolyG hDen)`. Composes the list→Finset reindexing
`logResidueSum_eq_grouped` with the proven abstract residue match `sum_residue_grouped_logDeriv_eq_div`
(specialized to `δ = implicitDeriv (toPolyG Dt)`, primitive constancy `δ(X − Cα) = C(w₀ − α′)` via
`implicitDeriv_X_sub_C`). This is exactly the `hLog` hypothesis of `cIntegrate_field_identity` /
`cIntegrate_checkIdentity`, discharged given the residue-set correspondence. -/
theorem logResidueSum_eq_div_of_residueData (Dt : CPolyG QFunNZ) {w₀ : CFieldSpec.K QFunNZ}
    (htop : toPolyG Dt = C w₀) (hNum hDen : CPolyG QFunNZ)
    (logs : List (ℚ × CPolyG QFunNZ)) (s : Finset (CFieldSpec.K QFunNZ))
    (hden : toPolyG hDen = Lagrange.nodal s id)
    (hA : (toPolyG hNum).degree < s.card)
    (hb0 : ∀ α ∈ s, w₀ - α′ ≠ 0)
    (hkeysNodup : (logs.map (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).Nodup)
    (hkeysImage : (logs.map (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).toFinset
      = s.image (fun α => (toPolyG hNum).eval α
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α))
    (harg : ∀ cv ∈ logs, toPolyG cv.2
      = ∏ α ∈ s.filter (fun α => (toPolyG hNum).eval α
            / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α
              = CFieldSpec.toK (ofConstNZ cv.1)), (X - C α)) :
    logResidueSum Dt logs = towerAlg (toPolyG hNum) / towerAlg (toPolyG hDen) := by
  classical
  rw [logResidueSum_eq_grouped Dt hNum logs s hkeysNodup hkeysImage harg, hden]
  -- the abstract residue match with the primitive constant seed `b α = w₀ − α′`
  exact sum_residue_grouped_logDeriv_eq_div (Differential.implicitDeriv (toPolyG Dt))
    (toPolyG hNum) s hA (fun α => w₀ - α′)
    (fun α _ => by rw [implicitDeriv_X_sub_C, htop, ← C_sub]) hb0

open scoped Classical Differential in
/-- Restatement: the abstract `hLog` discharge — the concrete §5.6 residue sum equals the integrand in
the primitive regime, given the residue-set correspondence. -/
example (Dt : CPolyG QFunNZ) {w₀ : CFieldSpec.K QFunNZ} (htop : toPolyG Dt = C w₀)
    (hNum hDen : CPolyG QFunNZ) (logs : List (ℚ × CPolyG QFunNZ)) (s : Finset (CFieldSpec.K QFunNZ))
    (hden : toPolyG hDen = Lagrange.nodal s id) (hA : (toPolyG hNum).degree < s.card)
    (hb0 : ∀ α ∈ s, w₀ - α′ ≠ 0)
    (hkeysNodup : (logs.map (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).Nodup)
    (hkeysImage : (logs.map (fun cv => CFieldSpec.toK (ofConstNZ cv.1))).toFinset
      = s.image (fun α => (toPolyG hNum).eval α
          / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α))
    (harg : ∀ cv ∈ logs, toPolyG cv.2
      = ∏ α ∈ s.filter (fun α => (toPolyG hNum).eval α
            / (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)).eval α
              = CFieldSpec.toK (ofConstNZ cv.1)), (X - C α)) :
    logResidueSum Dt logs = towerAlg (toPolyG hNum) / towerAlg (toPolyG hDen) :=
  logResidueSum_eq_div_of_residueData Dt htop hNum hDen logs s hden hA hb0 hkeysNodup hkeysImage harg

/-! ### Closing the per-log-argument match `harg` — `toPolyG (cLogArgTower …) = ∏(X−α)`

The `harg` hypothesis of `logResidueSum_eq_div_of_residueData` asks each concrete log argument
`v = cLogArgTower Dt fuel hNum hDen c = cgcdFF fuel hDen (hNum − c·Δd)` to read as the abstract
Rothstein–Trager factor `∏_{res α = c}(X−α)`. The concrete `cgcdFF` is `Associated` to the abstract
`gcd(toPolyG hDen, …)` (`associated_toPolyG_cgcdFF_of_inputs`), the abstract gcd factors as the product
(`gcd_nodal_eq_prod_residue_seed`), and both sides are **monic** (`cgcdFF` ends in `cmonicG`; a product of
`X − Cα` is monic), so `Associated` upgrades to **equality** (`eq_of_monic_of_associated`). This discharges
`harg` from the concrete `cgcdFF` regularity, leaving only the residue-set enumeration (`hkeysImage`/
`hkeysNodup`) — the generic `cResidueResultantTower` root-finding correspondence — as the remaining gap. -/

open DeepWiki.SymbolicIntegration.Compute in
/-- **`cmonicG` produces a monic image** (over `RatFunc ℚ`): for `p` with `toPolyG p ≠ 0`, the monic
normalization `cmonicG p` reads as the monic polynomial `C((toPolyG p).leadingCoeff⁻¹)·toPolyG p`. The
`cgcdFF` output is `cmonicG`-normalized, so its `toPolyG` is monic — half of the `Associated ⟹ equal`
upgrade. -/
theorem monic_toPolyG_cmonicG (p : CPolyG QFunNZ) (hp : toPolyG p ≠ 0) :
    (toPolyG (CPolyG.cmonicG p)).Monic := by
  have hcz : CPolyG.cisZeroG (CPolyG.cnormG p) = false := by
    rw [Bool.eq_false_iff]; intro h
    exact hp ((toPolyG_cnormG p) ▸ (cisZeroG_iff (CPolyG.cnormG p)).mp h)
  have hmon : CPolyG.cmonicG p = cscaleG (CField.inv (cleadG (CPolyG.cnormG p))) (CPolyG.cnormG p) := by
    rw [CPolyG.cmonicG]; simp only [hcz, Bool.false_eq_true, if_false]
  rw [hmon, toPolyG_cscaleG, toPolyG_cnormG, CFieldSpec.toK_inv, toK_cleadG_eq_leadingCoeff,
    toPolyG_cnormG, Polynomial.Monic.def, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hp)]

/-- **`cmonicG` output is monic whenever nonzero**: if the monic normalization reads as a *nonzero*
polynomial `toPolyG (cmonicG p) ≠ 0`, it is monic. (`cmonicG` of a `toPolyG`-zero input is `[]` with
`toPolyG = 0`, so nonzero forces the nonzero branch.) The convenient form when nonzero-ness comes from an
`Associated` to a nonzero target. -/
theorem monic_toPolyG_cmonicG_of_ne (p : CPolyG QFunNZ) (hp : toPolyG (CPolyG.cmonicG p) ≠ 0) :
    (toPolyG (CPolyG.cmonicG p)).Monic := by
  refine monic_toPolyG_cmonicG p (fun h => hp ?_)
  rw [CPolyG.cmonicG]
  have hcz : CPolyG.cisZeroG (CPolyG.cnormG p) = true :=
    (cisZeroG_iff (CPolyG.cnormG p)).mpr ((toPolyG_cnormG p).trans h)
  simp only [hcz, if_true, toPolyG_nil]

open scoped Classical in
open DeepWiki.SymbolicIntegration.CPolyG QFunNZ in
/-- **The concrete log argument reads as the Rothstein–Trager product** (`harg` closed): in the
primitive split regime `toPolyG hDen = Lagrange.nodal s id` with the monomial seed `Δd` nonzero at every
root, the concrete `cLogArgTower Dt fuel hNum hDen c = cgcdFF fuel hDen (hNum − c·Δd)` reads as the
abstract factor `∏_{α: A(α)/Δd(α) = toK(ofConstNZ c)}(X−α)` (`A = toPolyG hNum`). Composes the `cgcdFF`
correctness `associated_toPolyG_cgcdFF_of_inputs` (Associated to `gcd(toPolyG hDen, toPolyG(hNum − c·Δd))`),
the seed-generic gcd-product `gcd_nodal_eq_prod_residue_seed`, and the monic upgrade
`eq_of_monic_of_associated` (`cgcdFF` monic via `monic_toPolyG_cmonicG`, the product monic via
`monic_prod_of_monic`/`monic_X_sub_C`). This discharges each `harg` term from the concrete `cgcdFF`
regularity hypothesis. -/
theorem cLogArgTower_toPolyG_eq_prod (Dt : CPolyG QFunNZ) (fuel : ℕ) (hNum hDen : CPolyG QFunNZ)
    (s : Finset (CFieldSpec.K QFunNZ)) (hden : toPolyG hDen = Lagrange.nodal s id)
    (hDd : ∀ α ∈ s, (Differential.implicitDeriv (toPolyG Dt) (toPolyG hDen)).eval α ≠ 0) (c : ℚ)
    (hreg : PrimPRSInputs fuel
      (if Compute.bdeg (clearDenoms hDen)
            < Compute.bdeg (clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))
        then clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)) else clearDenoms hDen)
      (if Compute.bdeg (clearDenoms hDen)
            < Compute.bdeg (clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))
        then clearDenoms hDen else clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))) :
    toPolyG (cLogArgTower Dt fuel hNum hDen c)
      = ∏ α ∈ s.filter (fun α => (toPolyG hNum).eval α
            / (Differential.implicitDeriv (toPolyG Dt) (toPolyG hDen)).eval α
              = CFieldSpec.toK (ofConstNZ c)), (X - C α) := by
  classical
  -- the `cAmcDd` reads as `A − C c · Δd` over the field
  have hamc : toPolyG (cAmcDd Dt hNum hDen (ofConstNZ c))
      = toPolyG hNum - Polynomial.C (CFieldSpec.toK (ofConstNZ c))
          * Differential.implicitDeriv (toPolyG Dt) (toPolyG hDen) := by
    rw [cAmcDd, cDd, toPolyG_csubG, toPolyG_cscaleG, toPolyG_cmonomialDeriv]
  -- the abstract gcd factors as the product (seed-generic Czichowski identity)
  have hgcd : gcd (toPolyG hDen) (toPolyG (cAmcDd Dt hNum hDen (ofConstNZ c)))
      = ∏ α ∈ s.filter (fun α => (toPolyG hNum).eval α
            / (Differential.implicitDeriv (toPolyG Dt) (toPolyG hDen)).eval α
              = CFieldSpec.toK (ofConstNZ c)), (X - C α) := by
    rw [hamc, hden] at *
    exact gcd_nodal_eq_prod_residue_seed s (toPolyG hNum)
      (Differential.implicitDeriv (toPolyG Dt) (Lagrange.nodal s id)) hDd
      (CFieldSpec.toK (ofConstNZ c))
  -- the product `∏(X−α)` is monic
  have hprodmonic : (∏ α ∈ s.filter (fun α => (toPolyG hNum).eval α
        / (Differential.implicitDeriv (toPolyG Dt) (toPolyG hDen)).eval α
          = CFieldSpec.toK (ofConstNZ c)), (X - C α)).Monic :=
    monic_prod_of_monic _ _ fun α _ => monic_X_sub_C α
  -- `cLogArgTower` is `cgcdFF`, `Associated` to the abstract gcd, hence to the product
  have hassoc : Associated (toPolyG (cLogArgTower Dt fuel hNum hDen c))
      (∏ α ∈ s.filter (fun α => (toPolyG hNum).eval α
            / (Differential.implicitDeriv (toPolyG Dt) (toPolyG hDen)).eval α
              = CFieldSpec.toK (ofConstNZ c)), (X - C α)) := by
    rw [cLogArgTower, ← hgcd]
    exact associated_toPolyG_cgcdFF_of_inputs fuel hDen (cAmcDd Dt hNum hDen (ofConstNZ c)) hreg
  -- `cLogArgTower` is nonzero (Associated to the nonzero product `∏(X−α)`)
  have hne : toPolyG (cLogArgTower Dt fuel hNum hDen c) ≠ 0 :=
    (hassoc.symm.ne_zero_iff).mp hprodmonic.ne_zero
  -- `cgcdFF` ends in `cmonicG`, so its nonzero `toPolyG` is monic; upgrade `Associated` to equality
  have hgcdmonic : (toPolyG (cLogArgTower Dt fuel hNum hDen c)).Monic := by
    have hne' := hne
    rw [cLogArgTower, cgcdFF] at hne' ⊢
    generalize (if Compute.bdeg (clearDenoms hDen)
        < Compute.bdeg (clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))
      then (clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)), clearDenoms hDen)
      else (clearDenoms hDen, clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))) = PQ at hne' ⊢
    obtain ⟨P, Q⟩ := PQ
    exact monic_toPolyG_cmonicG_of_ne _ hne'
  exact eq_of_monic_of_associated hgcdmonic hprodmonic hassoc

open scoped Classical Differential in
/-- Restatement: the concrete §5.6 log argument `cLogArgTower Dt fuel hNum hDen c` reads as the abstract
Rothstein–Trager product `∏_{res α = c}(X−α)` over the split squarefree denominator. -/
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (hNum hDen : CPolyG QFunNZ)
    (s : Finset (CFieldSpec.K QFunNZ)) (hden : toPolyG hDen = Lagrange.nodal s id)
    (hDd : ∀ α ∈ s, (Differential.implicitDeriv (toPolyG Dt) (toPolyG hDen)).eval α ≠ 0) (c : ℚ)
    (hreg : PrimPRSInputs fuel
      (if Compute.bdeg (clearDenoms hDen)
            < Compute.bdeg (clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))
        then clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)) else clearDenoms hDen)
      (if Compute.bdeg (clearDenoms hDen)
            < Compute.bdeg (clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))
        then clearDenoms hDen else clearDenoms (cAmcDd Dt hNum hDen (ofConstNZ c)))) :
    toPolyG (cLogArgTower Dt fuel hNum hDen c)
      = ∏ α ∈ s.filter (fun α => (toPolyG hNum).eval α
            / (Differential.implicitDeriv (toPolyG Dt) (toPolyG hDen)).eval α
              = CFieldSpec.toK (ofConstNZ c)), (X - C α) :=
  cLogArgTower_toPolyG_eq_prod Dt fuel hNum hDen s hden hDd c hreg

#print axioms logResidueSum_eq_grouped
#print axioms logResidueSum_eq_div_of_residueData
#print axioms monic_toPolyG_cmonicG
#print axioms monic_toPolyG_cmonicG_of_ne
#print axioms cLogArgTower_toPolyG_eq_prod

end DeepWiki.SymbolicIntegration
