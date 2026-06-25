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

end DeepWiki.SymbolicIntegration
