import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.LrtGeneralDerivation
import DeepWiki.SymbolicIntegration.Engine.LogPartTowerSoundness

/-! # Connecting the computable tower residue resultant to the general-derivation abstract theory (G4b)

`cResidueResultantTowerGWf Dt a d` interpolates the resultant samples `res_t(d, a − zₖ·Dd)` (`Dd =
cmonomialDeriv Dt d`). This file certifies it against the general-derivation abstract residue resultant
`rtResultantGen (toPolyG a) (toPolyG d) B` with `B = implicitDeriv (toPolyG Dt) (toPolyG d)` (G1–G3), for
the **primitive** reduced case (`Dt` constant, `Dstar` monic). Sample agreement is the core; the full
interpolation certification (`toPolyG … = rtResultantGen …`) follows by interpolation uniqueness. See
`docs/generalize-lrt-derivation.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-- **Sample agreement.** `toK (cresultantWf d (cAmcDdG Dt a d c))` equals the general-derivation abstract
residue resultant `rtResultantGen (toPolyG a) (toPolyG d) B` (`B = implicitDeriv (toPolyG Dt) (toPolyG d)`)
evaluated at `toK c`, for **monic** `d`, **constant** `Dt`, and proper `a` (`deg a < deg d`). The engine
computes the resultant at the *actual* degree `deg(a − c·Dd)`; the abstract `rtResultantGen` uses the formal
degree `deg d − 1`; `Polynomial.resultant_add_right_deg` reconciles them (`lc d = 1` from monic). -/
theorem toK_cresultantWf_cAmcDdG_eq_eval (Dt a d : CPolyG α) (c : α)
    (hDmonic : (toPolyG d).Monic) (hDt0 : (toPolyG Dt).natDegree = 0)
    (hAD : (toPolyG a).natDegree < (toPolyG d).natDegree) :
    CFieldSpec.toK (cresultantWf d (cAmcDdG Dt a d c))
      = (rtResultantGen (toPolyG a) (toPolyG d)
          (Differential.implicitDeriv (toPolyG Dt) (toPolyG d))).eval (CFieldSpec.toK c) := by
  set B := Differential.implicitDeriv (toPolyG Dt) (toPolyG d) with hBdef
  have hBdeg : B.natDegree ≤ (toPolyG d).natDegree - 1 :=
    natDegree_implicitDeriv_le_of_monic (toPolyG Dt) (toPolyG d) hDmonic hDt0
  have htE : toPolyG (cAmcDdG Dt a d c) = toPolyG a - C (CFieldSpec.toK c) * B :=
    toPolyG_cAmcDdG Dt a d c
  have hEdeg : (toPolyG a - C (CFieldSpec.toK c) * B).natDegree ≤ (toPolyG d).natDegree - 1 := by
    refine (natDegree_sub_le _ _).trans (max_le (by omega) ?_)
    exact (natDegree_C_mul_le _ _).trans hBdeg
  simp only [denote]
  rw [rtResultantGen_eval, cdegG_eq_natDegree d,
    cdegG_eq_natDegree (cAmcDdG Dt a d c), htE]
  obtain ⟨k, hk⟩ :
      ∃ k, (toPolyG d).natDegree - 1 = (toPolyG a - C (CFieldSpec.toK c) * B).natDegree + k :=
    ⟨(toPolyG d).natDegree - 1 - (toPolyG a - C (CFieldSpec.toK c) * B).natDegree, by omega⟩
  rw [hk, Polynomial.resultant_add_right_deg (toPolyG d) (toPolyG a - C (CFieldSpec.toK c) * B)
      (toPolyG d).natDegree (toPolyG a - C (CFieldSpec.toK c) * B).natDegree k le_rfl,
    show (toPolyG d).coeff (toPolyG d).natDegree = (toPolyG d).leadingCoeff from rfl,
    hDmonic.leadingCoeff, one_pow, one_mul]

open scoped Classical in
/-- **The tower residue-resultant certification (G4b).** `toPolyG (cResidueResultantTowerGWf Dt a d) =
rtResultantGen (toPolyG a) (toPolyG d) B` (`B = implicitDeriv (toPolyG Dt) (toPolyG d)`), for **monic** `d`,
**constant** `Dt`, and proper `a`. The computable engine's residue resultant (an interpolant of the
resultant samples) provably computes the general-derivation abstract residue resultant — via interpolation
uniqueness (both have `z`-degree `≤ deg d` and agree at the `deg d + 1` integer nodes). This is the object
`lazardRiobooTrager_output_isSimilar_gcd_gen` (G3) reasons about. -/
theorem toPolyG_cResidueResultantTowerGWf [CharZero (CFieldSpec.K α)] (Dt a d : CPolyG α)
    (hDmonic : (toPolyG d).Monic) (hDt0 : (toPolyG Dt).natDegree = 0)
    (hAD : (toPolyG a).natDegree < (toPolyG d).natDegree) :
    toPolyG (cResidueResultantTowerGWf Dt a d)
      = rtResultantGen (toPolyG a) (toPolyG d)
          (Differential.implicitDeriv (toPolyG Dt) (toPolyG d)) := by
  set B := Differential.implicitDeriv (toPolyG Dt) (toPolyG d) with hBdef
  set pts : List (α × α) := (List.range (cdegG d + 1)).map
    (fun k => (cnatCastG k, cresultantWf d (cAmcDdG Dt a d (cnatCastG k)))) with hpts
  have hcompute : cResidueResultantTowerGWf Dt a d = cinterpolateG pts := rfl
  have hfst : pts.map (fun p => CFieldSpec.toK p.1)
      = (List.range (cdegG d + 1)).map (Nat.cast : ℕ → CFieldSpec.K α) := by
    rw [hpts, List.map_map]
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply, CPolyG.toK_cnatCastG]
  have hnodup : (pts.map (fun p => CFieldSpec.toK p.1)).Nodup := by
    rw [hfst]; exact (List.nodup_range).map Nat.cast_injective
  have hlen : pts.length = cdegG d + 1 := by rw [hpts, List.length_map, List.length_range]
  have hne : pts ≠ [] := by rw [hpts]; simp
  rw [hcompute]
  symm
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (R := CFieldSpec.K α) (ι := ℕ)
    (s := Finset.range (cdegG d + 1)) (v := (Nat.cast : ℕ → CFieldSpec.K α))
    (f := rtResultantGen (toPolyG a) (toPolyG d) B) (g := toPolyG (cinterpolateG pts)) ?_ ?_ ?_ ?_
  · intro x _ y _ h; exact Nat.cast_injective h
  · rw [Finset.card_range, Nat.cast_withBot]
    refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    rw [Nat.cast_withBot, WithBot.coe_lt_coe]
    have h1 := natDegree_rtResultantGen_le (toPolyG a) (toPolyG d) B
    have h2 := cdegG_eq_natDegree d
    omega
  · rw [Finset.card_range, Nat.cast_withBot]
    have := degree_toPolyG_cinterpolateG_lt pts hne
    rw [hlen] at this
    simpa [Nat.cast_withBot] using this
  · intro k hk
    rw [Finset.mem_range] at hk
    have hmem : (cnatCastG k, cresultantWf d (cAmcDdG Dt a d (cnatCastG k))) ∈ pts := by
      rw [hpts, List.mem_map]; exact ⟨k, List.mem_range.mpr hk, rfl⟩
    rw [show (k : CFieldSpec.K α) = CFieldSpec.toK (cnatCastG k : α) from
        (CPolyG.toK_cnatCastG k).symm,
      eval_toPolyG_cinterpolateG pts hnodup hmem,
      toK_cresultantWf_cAmcDdG_eq_eval Dt a d (cnatCastG k) hDmonic hDt0 hAD]

omit [CDiffFieldSpec α] in
/-- **The residue resultant of a constant is a constant** (`cdegG d = 0 ⟹ cdegG (cResidueResultantTowerGWf
Dt a d) = 0`): the interpolation runs over `n + 1 = 1` node, and a single-point Lagrange interpolant is a
constant (`degree_toPolyG_cinterpolateG_lt`). The no-poles residue-resultant fact behind `cLrtLogArgG = []`. -/
theorem cdegG_cResidueResultantTowerGWf_eq_zero_of_cdegG_zero (Dt a d : CPolyG α) (hd : cdegG d = 0) :
    cdegG (cResidueResultantTowerGWf Dt a d) = 0 := by
  rw [cResidueResultantTowerGWf]
  simp only [hd, Nat.zero_add]
  set pts : List (α × α) := (List.range 1).map (fun k =>
    (cnatCastG k, cresultantWf d (cAmcDdG Dt a d (cnatCastG k)))) with hpts
  have hlen : pts.length = 1 := by rw [hpts, List.length_map, List.length_range]
  have hne : pts ≠ [] := by rw [← List.length_pos_iff_ne_nil, hlen]; norm_num
  by_cases hz : toPolyG (cinterpolateG pts) = 0
  · rw [cdegG_eq_natDegree, hz, Polynomial.natDegree_zero]
  · have hlt := degree_toPolyG_cinterpolateG_lt pts hne
    rw [hlen] at hlt
    rw [cdegG_eq_natDegree]
    have := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hlt
    omega

end DeepWiki.SymbolicIntegration
