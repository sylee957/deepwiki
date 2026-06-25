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

end DeepWiki.SymbolicIntegration
