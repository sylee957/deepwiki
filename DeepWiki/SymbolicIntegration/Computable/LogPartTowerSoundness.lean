import DeepWiki.SymbolicIntegration.Computable.NormalPartSoundness
import DeepWiki.SymbolicIntegration.PartialFraction
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.ResidueMultiplicity

/-! # The Rothstein–Trager residue identity over the transcendental tower

Transports the algebraic Rothstein–Trager residue identity to the transcendental tower with the
monomial derivation `D = cmonomialDeriv Dt`.  Delivers: the residue resultant's roots are the residues
(`roots_residueResultantTowerG_eq_residues`); the log-argument gcd is the residue's linear factor
(`residue_gcd_eq_linear_factor`); the `logResidueSumG` reading as a monomial log-derivative sum; and,
given the residue match, `logResidueSumG = a/d`, assembled with the Hermite half into the fuel-free
reduced-case field identity `D(g) + logResidueSumG = a/d` with no engine certificate. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

/-! ### The tower residue resultant's roots are the residues -/

namespace LogResidueTower

variable {K : Type*} [Field K]

/-- Linear factor of the tower residue resultant: for `ddval ≠ 0`,
`C aval − X·C ddval = −C ddval·(X − C (aval/ddval))`. -/
theorem residueLinearFactor_eq (aval ddval : K) (hd : ddval ≠ 0) :
    Polynomial.C aval - Polynomial.X * Polynomial.C ddval
      = -Polynomial.C ddval * (Polynomial.X - Polynomial.C (aval / ddval)) := by
  have hC : Polynomial.C ddval * Polynomial.C (aval / ddval) = Polynomial.C aval := by
    rw [← C_mul, mul_div_cancel₀ _ hd]
  linear_combination -hC

/-- The tower residue resultant's roots are the residues: given the product form
`R = C lc^N · ∏_{α∈droots}(C (aval α) − z·C (ddval α))` with `ddval α ≠ 0`,
`R.roots = droots.map (fun α => aval α / ddval α)`. -/
theorem roots_residueResultantTowerG_eq_residues (lc : K) (N : ℕ) (droots : Multiset K)
    (aval ddval : K → K)
    (hlc : lc ≠ 0)
    (hDd : ∀ α ∈ droots, ddval α ≠ 0)
    (R : K[X])
    (hR : R = Polynomial.C lc ^ N
      * (droots.map (fun α =>
          Polynomial.C (aval α) - Polynomial.X * Polynomial.C (ddval α))).prod) :
    R.roots = droots.map (fun α => aval α / ddval α) := by
  subst hR
  -- drop the nonzero leading scalar `C lc^N`
  rw [show (Polynomial.C lc : K[X]) ^ N = Polynomial.C (lc ^ N) from (map_pow _ _ _).symm,
    Polynomial.roots_C_mul _ (pow_ne_zero N hlc)]
  -- rewrite each factor `C(aval α) − z·C(ddval α) = −C(ddval α)·(z − C(residue α))`
  rw [Multiset.map_congr rfl (fun α hα => residueLinearFactor_eq (aval α) (ddval α) (hDd α hα))]
  -- `∏_α (−C(ddval α))·(z − residue α) = (∏_α −C(ddval α))·(∏_α (z − residue α))`
  rw [Multiset.prod_map_mul]
  -- the nonzero scalar `∏_α −C(ddval α)`, pulled out via `roots_C_mul`
  have hscal : (droots.map (fun α => -Polynomial.C (ddval α))).prod
      = Polynomial.C ((droots.map (fun α => -ddval α)).prod) := by
    rw [map_multiset_prod (Polynomial.C : K →+* K[X]), Multiset.map_map]
    simp only [Function.comp_apply, map_neg]
  have hscal0 : (droots.map (fun α => -ddval α)).prod ≠ 0 :=
    Multiset.prod_ne_zero (by simpa using fun α hα => hDd α hα)
  rw [hscal, Polynomial.roots_C_mul _ hscal0]
  -- the product of monic linear factors `∏_α (z − residue α)` has roots `{residue α}`
  rw [show (droots.map (fun α => Polynomial.X - Polynomial.C (aval α / ddval α)))
      = (droots.map (fun α => aval α / ddval α)).map (fun a => Polynomial.X - Polynomial.C a) by
      rw [Multiset.map_map]; rfl,
    Polynomial.roots_multiset_prod_X_sub_C]

/-! ### The residue↔linear-factor bijection: `gcd_t(d, a − c·Dd) = X − β` -/

/-- The Rothstein–Trager log argument is the residue's linear factor: for `d = ∏_{α∈s}(X − α)`
squarefree, `Dd(α) ≠ 0` on `s`, distinct residues, and `β ∈ s` with `c = a(β)/Dd(β)`,
`gcd(d, a − C c·Dd)` is associate to `X − C β`. -/
theorem residue_gcd_associated_linear_factor [DecidableEq K] (s : Finset K) (a Dd : K[X])
    (hDd : ∀ α ∈ s, Dd.eval α ≠ 0)
    (hdist : ∀ α ∈ s, ∀ β ∈ s, α ≠ β → a.eval α / Dd.eval α ≠ a.eval β / Dd.eval β)
    (β : K) (hβ : β ∈ s) :
    Associated (gcd (Lagrange.nodal s id) (a - Polynomial.C (a.eval β / Dd.eval β) * Dd))
      (Polynomial.X - Polynomial.C β) := by
  set d : K[X] := Lagrange.nodal s id with hd
  set c : K := a.eval β / Dd.eval β with hc
  set g : K[X] := a - Polynomial.C c * Dd with hg
  -- work with `EuclideanDomain.gcd` (where `isRoot_gcd_iff_isRoot_left_right` lives), then bridge:
  -- the ambient `GCDMonoid.gcd` and `EuclideanDomain.gcd` are associates (both are gcds)
  set gE : K[X] := EuclideanDomain.gcd d g with hgE
  have hbridge : Associated (gcd d g) gE :=
    associated_of_dvd_dvd
      (EuclideanDomain.dvd_gcd (gcd_dvd_left d g) (gcd_dvd_right d g))
      (dvd_gcd (EuclideanDomain.gcd_dvd_left d g) (EuclideanDomain.gcd_dvd_right d g))
  refine hbridge.trans ?_
  -- `d` is split (a product of linear factors) and nonzero
  have hd_ne : d ≠ 0 := Lagrange.nodal_ne_zero
  have hsplit_d : Polynomial.Splits d := by
    rw [hd, Lagrange.nodal_eq]
    exact Polynomial.Splits.prod (fun i _ => Polynomial.Splits.X_sub_C _)
  -- `d.roots = s.val` (simple, split)
  have hroots_d : d.roots = s.val := by
    rw [hd, Lagrange.nodal_eq]
    simpa using Polynomial.roots_prod_X_sub_C s
  -- `d` is squarefree (separable, since `id` is injective on `s`)
  have hsep_d : Squarefree d := by
    rw [hd, Lagrange.nodal_eq]
    exact (Polynomial.separable_prod_X_sub_C_iff'.mpr
      (fun x _ y _ h => h)).squarefree
  -- `g` vanishes at `β`: `a(β) − c·Dd(β) = 0` since `c = a(β)/Dd(β)` and `Dd(β) ≠ 0`
  have hgβ : g.IsRoot β := by
    have hDdβ : Dd.eval β ≠ 0 := hDd β hβ
    simp only [hg, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, hc]
    rw [div_mul_cancel₀ _ hDdβ, sub_self]
  -- `β` is a root of `d`
  have hdβ : d.IsRoot β := by
    rw [← Polynomial.mem_roots hd_ne, hroots_d]; exact hβ
  -- `gE = EuclideanDomain.gcd d g ∣ d` (nonzero) ⟹ `gE` is nonzero
  have hgcd_dvd_d : gE ∣ d := EuclideanDomain.gcd_dvd_left d g
  have hgcd_ne : gE ≠ 0 := fun h => hd_ne (zero_dvd_iff.mp (h ▸ hgcd_dvd_d))
  -- the roots of `gE` are exactly `{β}`
  have hgcd_roots : gE.roots = {β} := by
    -- roots ≤ d.roots = s.val, hence nodup (a sub-multiset of the nodup Finset support)
    have hle : gE.roots ≤ d.roots := Polynomial.roots.le_of_dvd hd_ne hgcd_dvd_d
    rw [hroots_d] at hle
    have hnodup : gE.roots.Nodup := Multiset.nodup_of_le hle s.nodup
    -- β ∈ roots (common root of `d` and `g`)
    have hβ_mem : β ∈ gE.roots := by
      rw [Polynomial.mem_roots hgcd_ne]
      exact Polynomial.isRoot_gcd_iff_isRoot_left_right.mpr ⟨hdβ, hgβ⟩
    -- any root α of the gcd equals β (common root of `d`, `g` ⟹ residue α = c ⟹ α = β)
    have hsub : ∀ α ∈ gE.roots, α = β := by
      intro α hα_root
      by_contra hα_ne
      have hα_in_s : α ∈ s := by
        have : α ∈ (s.val : Multiset K) := Multiset.mem_of_le hle hα_root
        simpa using this
      have hcommon := Polynomial.isRoot_gcd_iff_isRoot_left_right.mp
        ((Polynomial.mem_roots hgcd_ne).mp hα_root)
      have hα_g : g.IsRoot α := hcommon.2
      have hDdα : Dd.eval α ≠ 0 := hDd α hα_in_s
      have hres_eq : a.eval α / Dd.eval α = c := by
        simp only [hg, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_C] at hα_g
        rw [div_eq_iff hDdα]; linear_combination hα_g
      exact hdist α hα_in_s β hβ hα_ne (by rw [hres_eq, hc])
    -- nodup + all elements `β` + contains `β` ⟹ `= {β}` (antisymmetry of `≤`)
    refine le_antisymm (Multiset.le_iff_count.mpr (fun x => ?_))
      (Multiset.le_iff_count.mpr (fun x => ?_))
    · -- count x roots ≤ count x {β}
      rw [Multiset.count_singleton]
      by_cases hx : x ∈ gE.roots
      · rw [hsub x hx, Multiset.count_eq_one_of_mem hnodup hβ_mem, if_pos rfl]
      · rw [Multiset.count_eq_zero_of_notMem hx]; positivity
    · -- count x {β} ≤ count x roots
      rw [Multiset.count_singleton]
      by_cases hx : x = β
      · rw [if_pos hx, hx, Multiset.count_eq_one_of_mem hnodup hβ_mem]
      · rw [if_neg hx]; positivity
  -- gE splits, single root β ⟹ gE = C(leadingCoeff)·(X − C β), hence associate to X − C β
  have hgcd_split : Polynomial.Splits gE := hsplit_d.of_dvd hd_ne hgcd_dvd_d
  have heq : gE = Polynomial.C gE.leadingCoeff * (Polynomial.X - Polynomial.C β) :=
    hgcd_split.eq_X_sub_C_of_single_root hgcd_roots
  have hlcunit : IsUnit (Polynomial.C gE.leadingCoeff) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hgcd_ne))
  rw [heq]
  exact associated_unit_mul_left (Polynomial.X - Polynomial.C β)
    (Polynomial.C gE.leadingCoeff) hlcunit

/-- Literal form of `residue_gcd_associated_linear_factor`: over `K[X]` the normalized gcd gives
`gcd(d, a − C c·Dd) = X − C β`, under the same hypotheses. -/
theorem residue_gcd_eq_linear_factor [DecidableEq K] (s : Finset K) (a Dd : K[X])
    (hDd : ∀ α ∈ s, Dd.eval α ≠ 0)
    (hdist : ∀ α ∈ s, ∀ β ∈ s, α ≠ β → a.eval α / Dd.eval α ≠ a.eval β / Dd.eval β)
    (β : K) (hβ : β ∈ s) :
    gcd (Lagrange.nodal s id) (a - Polynomial.C (a.eval β / Dd.eval β) * Dd)
      = Polynomial.X - Polynomial.C β := by
  have hassoc := residue_gcd_associated_linear_factor s a Dd hDd hdist β hβ
  -- the gcd is nonzero (its associate `X − C β` is nonzero)
  have hne : gcd (Lagrange.nodal s id) (a - Polynomial.C (a.eval β / Dd.eval β) * Dd) ≠ 0 := by
    intro h; rw [h] at hassoc
    exact (Polynomial.X_sub_C_ne_zero β) ((associated_zero_iff_eq_zero _).mp hassoc.symm)
  -- the ambient `gcd` on `K[X]` is monic-normalized (`normalize (gcd) = gcd` ⟹ `Monic` for `≠ 0`)
  have hmonic : (gcd (Lagrange.nodal s id) (a - Polynomial.C (a.eval β / Dd.eval β) * Dd)).Monic := by
    have := normalize_gcd (Lagrange.nodal s id) (a - Polynomial.C (a.eval β / Dd.eval β) * Dd)
    rwa [Polynomial.normalize_eq_self_iff_monic hne] at this
  exact eq_of_monic_of_associated hmonic (Polynomial.monic_X_sub_C β) hassoc

end LogResidueTower

/-! ### The `logResidueSumG` reading as a monomial log-derivative sum -/

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- `toPolyG (cAmcDdG Dt a d c) = toPolyG a − C(toK c)·implicitDeriv (toPolyG Dt) (toPolyG d)`. -/
theorem toPolyG_cAmcDdG (Dt a d : CPolyG α) (c : α) :
    toPolyG (cAmcDdG Dt a d c)
      = toPolyG a - Polynomial.C (CFieldSpec.toK c)
          * Differential.implicitDeriv (toPolyG Dt) (toPolyG d) := by
  rw [cAmcDdG]
  simp only [denote]
/-- Per-term log-derivative reading:
`towerFractionFieldDerivG Dt (amG v)/amG v = amG (toPolyG (cmonomialDeriv Dt v))/amG (toPolyG v)`. -/
theorem towerFractionFieldDerivG_logDeriv (Dt v : CPolyG α) :
    towerFractionFieldDerivG Dt (amG α (toPolyG v)) / amG α (toPolyG v)
      = amG α (toPolyG (cmonomialDeriv Dt v)) / amG α (toPolyG v) := by
  rw [towerFractionFieldDerivG, extendDeriv_algebraMap]
  simp only [denote]

/-- `logResidueSumG` reads as the monomial log-derivative sum
`∑_{(c,v)} amG(C(toK c))·(towerFractionFieldDerivG Dt (amG v)/amG v)`. -/
theorem logResidueSumG_eq_logDeriv_sum (Dt : CPolyG α) (logs : List (α × CPolyG α)) :
    logResidueSumG Dt logs
      = (logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum := by
  rw [logResidueSumG]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro cv _
  rw [towerFractionFieldDerivG_logDeriv]

/-! ### The RT residue identity: `logResidueSumG = a/d` from the residue match -/

/-- `logResidueSumG = a/d` from the residue match: given the log-derivative sum equals `amG a/amG d`,
so does `logResidueSumG Dt logs`. -/
theorem logResidueSumG_eq_of_residue_match (Dt : CPolyG α) (a d : CPolyG α)
    (logs : List (α × CPolyG α))
    (hmatch : (logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
        = amG α (toPolyG a) / amG α (toPolyG d)) :
    logResidueSumG Dt logs = amG α (toPolyG a) / amG α (toPolyG d) := by
  rw [logResidueSumG_eq_logDeriv_sum Dt logs]
  exact hmatch

/-! ### Assembly: the reduced-case field identity from the Hermite half + the RT residue match -/

/-- The reduced-case field identity: given the Hermite half `D(g) + h = a/d` and the RT residue match
(the residue logs' log-derivative sum equals `h`), `D(g) + logResidueSumG = a/d`. -/
theorem field_identity_of_reducedG_of_residueMatch (Dt : CPolyG α)
    (gnum gden hNum hDen anum aden : CPolyG α) (logs : List (α × CPolyG α))
    (hherm : towerFractionFieldDerivG Dt (amG α (toPolyG gnum) / amG α (toPolyG gden))
          + amG α (toPolyG hNum) / amG α (toPolyG hDen)
        = amG α (toPolyG anum) / amG α (toPolyG aden))
    (hmatch : (logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
        = amG α (toPolyG hNum) / amG α (toPolyG hDen)) :
    towerFractionFieldDerivG Dt (amG α (toPolyG gnum) / amG α (toPolyG gden))
        + logResidueSumG Dt logs
      = amG α (toPolyG anum) / amG α (toPolyG aden) := by
  rw [logResidueSumG_eq_of_residue_match Dt hNum hDen logs hmatch, hherm]

/-! ### The fuel-free reduced-case one-shot for `cIntegrateReducedGWf`

Reads `cIntegrateReducedGWf`'s fields into `field_identity_of_reducedG_of_residueMatch`. -/

variable [CFracGcdCoreWf α]

/-- The fuel-free reduced-case one-shot: for `res = cIntegrateReducedGWf Dt a d cands`, given the
Hermite half and the RT residue match, `D(g) + logResidueSumG Dt res.logs = a/d`. -/
theorem field_identity_of_cIntegrateReducedGWf_of_residueMatch (Dt : CPolyG α)
    (a d : CPolyG α) (cands : List α)
    (hherm : towerFractionFieldDerivG Dt
            (amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
              / amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2))
          + amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1)
            / amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2)
        = amG α (toPolyG a) / amG α (toPolyG d))
    (hmatch : ((CPolyG.cIntegrateReducedGWf Dt a d cands).logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
        = amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1)
          / amG α (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2)) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
          / amG α (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2))
        + logResidueSumG Dt (CPolyG.cIntegrateReducedGWf Dt a d cands).logs
      = amG α (toPolyG a) / amG α (toPolyG d) :=
  field_identity_of_reducedG_of_residueMatch Dt
    (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1
    (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2
    (cHermiteReduceTowerGWf Dt a d).2.1 (cHermiteReduceTowerGWf Dt a d).2.2
    a d (CPolyG.cIntegrateReducedGWf Dt a d cands).logs hherm hmatch

/-! ### The deliverables at the level-1 carrier `α = QFunNZG ℚ` -/

/-- `Algebra ℚ (CFieldSpec.K (QFunNZG ℚ))` via `CFieldSpec.K (QFunNZG ℚ) = RatFunc ℚ`. -/
noncomputable local instance : Algebra ℚ (CFieldSpec.K (QFunNZG ℚ)) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- The tower residue resultant's roots are the residues over `ℚ(x)`
(`roots_residueResultantTowerG_eq_residues` at `K = RatFunc ℚ`). -/
theorem roots_residueResultantTowerG_eq_residues_qfunNZG (lc : CFieldSpec.K (QFunNZG ℚ)) (N : ℕ)
    (droots : Multiset (CFieldSpec.K (QFunNZG ℚ))) (aval ddval : CFieldSpec.K (QFunNZG ℚ) → CFieldSpec.K (QFunNZG ℚ))
    (hlc : lc ≠ 0) (hDd : ∀ α ∈ droots, ddval α ≠ 0) (R : (CFieldSpec.K (QFunNZG ℚ))[X])
    (hR : R = Polynomial.C lc ^ N
      * (droots.map (fun α =>
          Polynomial.C (aval α) - Polynomial.X * Polynomial.C (ddval α))).prod) :
    R.roots = droots.map (fun α => aval α / ddval α) :=
  LogResidueTower.roots_residueResultantTowerG_eq_residues lc N droots aval ddval hlc hDd R hR

/-- The fuel-free reduced-case RT one-shot over `ℚ(x)(t)`: for `res = cIntegrateReducedGWf Dt a d
cands`, given the Hermite half and the RT residue match, `D(g) + logResidueSumG Dt res.logs = amG a/amG d`. -/
theorem field_identity_of_cIntegrateReducedGWf_of_residueMatch_qfunNZG (Dt : CPolyG (QFunNZG ℚ))
    (a d : CPolyG (QFunNZG ℚ)) (cands : List (QFunNZG ℚ))
    (hherm : towerFractionFieldDerivG Dt
            (amG (QFunNZG ℚ) (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
              / amG (QFunNZG ℚ) (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2))
          + amG (QFunNZG ℚ) (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1)
            / amG (QFunNZG ℚ) (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2)
        = amG (QFunNZG ℚ) (toPolyG a) / amG (QFunNZG ℚ) (toPolyG d))
    (hmatch : ((CPolyG.cIntegrateReducedGWf Dt a d cands).logs.map (fun cv =>
          amG (QFunNZG ℚ) (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG (QFunNZG ℚ) (toPolyG cv.2))
                / amG (QFunNZG ℚ) (toPolyG cv.2)))).sum
        = amG (QFunNZG ℚ) (toPolyG (cHermiteReduceTowerGWf Dt a d).2.1)
          / amG (QFunNZG ℚ) (toPolyG (cHermiteReduceTowerGWf Dt a d).2.2)) :
    towerFractionFieldDerivG Dt
        (amG (QFunNZG ℚ) (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.1)
          / amG (QFunNZG ℚ) (toPolyG (CPolyG.cIntegrateReducedGWf Dt a d cands).rational.2))
        + logResidueSumG Dt (CPolyG.cIntegrateReducedGWf Dt a d cands).logs
      = amG (QFunNZG ℚ) (toPolyG a) / amG (QFunNZG ℚ) (toPolyG d) :=
  field_identity_of_cIntegrateReducedGWf_of_residueMatch Dt a d cands hherm hmatch

/-! ### Restatements -/

-- ★ THE MILESTONE (abstract, axiom-clean, no native_decide): the tower residue resultant's roots ARE the
-- residues `a(α)/Dd(α)` — the transcendental `roots_rtResultant`, monomial-derivative general.
example {K : Type*} [Field K] (lc : K) (N : ℕ) (droots : Multiset K) (aval ddval : K → K)
    (hlc : lc ≠ 0) (hDd : ∀ α ∈ droots, ddval α ≠ 0) (R : K[X])
    (hR : R = Polynomial.C lc ^ N
      * (droots.map (fun α =>
          Polynomial.C (aval α) - Polynomial.X * Polynomial.C (ddval α))).prod) :
    R.roots = droots.map (fun α => aval α / ddval α) :=
  LogResidueTower.roots_residueResultantTowerG_eq_residues lc N droots aval ddval hlc hDd R hR

-- ★ THE KEYSTONE (Task 1, abstract, no native_decide): the Rothstein–Trager log argument `gcd(d, a − c·Dd)`
-- IS the residue's linear factor `X − β`, for `d = ∏_{α∈s}(X − α)` squarefree with distinct residues.
example {K : Type*} [Field K] [DecidableEq K] (s : Finset K) (a Dd : K[X])
    (hDd : ∀ α ∈ s, Dd.eval α ≠ 0)
    (hdist : ∀ α ∈ s, ∀ β ∈ s, α ≠ β → a.eval α / Dd.eval α ≠ a.eval β / Dd.eval β)
    (β : K) (hβ : β ∈ s) :
    gcd (Lagrange.nodal s id) (a - Polynomial.C (a.eval β / Dd.eval β) * Dd)
      = Polynomial.X - Polynomial.C β :=
  LogResidueTower.residue_gcd_eq_linear_factor s a Dd hDd hdist β hβ

-- ★★ THE RT HALF (abstract, checker-free, no native_decide): the residue sum differentiates to the Hermite
-- leftover, so `D(g) + logResidueSumG = a/d` — given the abstract Hermite telescoping + the residue match.
example (Dt : CPolyG α) (gnum gden hNum hDen anum aden : CPolyG α) (logs : List (α × CPolyG α))
    (hherm : towerFractionFieldDerivG Dt (amG α (toPolyG gnum) / amG α (toPolyG gden))
          + amG α (toPolyG hNum) / amG α (toPolyG hDen)
        = amG α (toPolyG anum) / amG α (toPolyG aden))
    (hmatch : (logs.map (fun cv =>
          amG α (Polynomial.C (CFieldSpec.toK cv.1))
            * (towerFractionFieldDerivG Dt (amG α (toPolyG cv.2)) / amG α (toPolyG cv.2)))).sum
        = amG α (toPolyG hNum) / amG α (toPolyG hDen)) :
    towerFractionFieldDerivG Dt (amG α (toPolyG gnum) / amG α (toPolyG gden))
        + logResidueSumG Dt logs
      = amG α (toPolyG anum) / amG α (toPolyG aden) :=
  field_identity_of_reducedG_of_residueMatch Dt gnum gden hNum hDen anum aden logs hherm hmatch

/-! ### Axiom audit -/

#print axioms LogResidueTower.residueLinearFactor_eq
#print axioms LogResidueTower.roots_residueResultantTowerG_eq_residues
#print axioms LogResidueTower.residue_gcd_associated_linear_factor
#print axioms LogResidueTower.residue_gcd_eq_linear_factor
#print axioms monic_toPolyG_cmonicG
#print axioms toPolyG_cAmcDdG
#print axioms towerFractionFieldDerivG_logDeriv
#print axioms logResidueSumG_eq_logDeriv_sum
#print axioms logResidueSumG_eq_of_residue_match
#print axioms field_identity_of_reducedG_of_residueMatch
#print axioms field_identity_of_cIntegrateReducedGWf_of_residueMatch
#print axioms roots_residueResultantTowerG_eq_residues_qfunNZG
#print axioms field_identity_of_cIntegrateReducedGWf_of_residueMatch_qfunNZG

end DeepWiki.SymbolicIntegration
