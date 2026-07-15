import DeepWiki.SymbolicIntegration.SubresultantCorrectness
import DeepWiki.SymbolicIntegration.LrtMonicLogs
import DeepWiki.SymbolicIntegration.Engine.ResidueResultantTowerSpec
import Mathlib.LinearAlgebra.Lagrange

/-! # Rothstein–Trager resultant correctness

Specialization of the generic tower residue resultant to the ordinary derivative over `ℚ`, plus the
base-change and residue-regularity lemmas used by the LRT development. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-- The generic tower residue resultant specialized to `Dt = 1` realizes `rtResultant` over `ℚ`. -/
theorem toPolyG_cResidueResultantTower_one_eq_rtResultant (A D : DensePoly ℚ)
    (hDmonic : (DensePoly.toPoly D).Monic)
    (hAD : (DensePoly.toPoly A).natDegree < (DensePoly.toPoly D).natDegree) :
    DensePoly.toPoly (DensePoly.cResidueResultantTower ([1] : DensePoly ℚ) A D) =
      rtResultant (DensePoly.toPoly A) (DensePoly.toPoly D) := by
  letI : CharZero (CFieldSpec.K ℚ) := inferInstanceAs (CharZero ℚ)
  have hOne : DensePoly.toPoly ([1] : DensePoly ℚ) = 1 := by
    simp [DensePoly.toPolyG_cons]
  have hDt0 : (DensePoly.toPoly ([1] : DensePoly ℚ)).natDegree = 0 := by
    rw [hOne, Polynomial.natDegree_one]
  have himp : Differential.implicitDeriv (DensePoly.toPoly ([1] : DensePoly ℚ))
      (DensePoly.toPoly D) = Polynomial.derivative (DensePoly.toPoly D) := by
    rw [hOne, Differential.implicitDeriv]
    have hmc : Differential.mapCoeffs (DensePoly.toPoly D) = 0 := by
      ext i
      rw [Differential.coeff_mapCoeffs, Polynomial.coeff_zero]
      show @Differential.deriv ℚ _ _ ((DensePoly.toPoly D).coeff i) = 0
      rfl
    simp only [Derivation.add_apply, hmc, Derivation.restrictScalars_apply, one_smul, zero_add]
    rfl
  have h := toPolyG_cResidueResultantTowerG ([1] : DensePoly ℚ) A D hDmonic hDt0 hAD
  rw [himp, rtResultantGen_derivative] at h
  exact h

end DeepWiki.SymbolicIntegration

namespace DeepWiki.SymbolicIntegration

open Polynomial

/-! ### `rtResultant` under an injective base change -/

/-- `rtResultant` commutes with an injective base change `σ : K →+* L`:
`rtResultant (A.map σ) (D.map σ) = (rtResultant A D).map σ`. -/
theorem rtResultant_map_of_injective {K L : Type*} [Field K] [Field L] (σ : K →+* L)
    (hσ : Function.Injective σ) (A D : K[X]) :
    rtResultant (A.map σ) (D.map σ) = (rtResultant A D).map σ := by
  rw [rtResultant, rtResultant]
  have hdeg : (D.map σ).natDegree = D.natDegree := Polynomial.natDegree_map_eq_of_injective hσ D
  -- rewrite each operand of the LHS resultant as `(operand over K[X]).map (mapRingHom σ)`
  -- the key commuting square `C ∘ σ = mapRingHom σ ∘ C`
  have hcomm : (C : L →+* L[X]).comp σ = (Polynomial.mapRingHom σ).comp (C : K →+* K[X]) := by
    ext k; simp
  have hop1 : (D.map σ).map (C : L →+* L[X])
      = (D.map (C : K →+* K[X])).map (Polynomial.mapRingHom σ) := by
    rw [Polynomial.map_map, Polynomial.map_map, hcomm]
  have hop2 : (A.map σ).map (C : L →+* L[X])
        - C Polynomial.X * (derivative (D.map σ)).map (C : L →+* L[X])
      = ((A.map (C : K →+* K[X])
          - C Polynomial.X * (derivative D).map (C : K →+* K[X]))).map
            (Polynomial.mapRingHom σ) := by
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_C,
      Polynomial.coe_mapRingHom, Polynomial.map_map, derivative_map, Polynomial.map_map,
      Polynomial.map_map, hcomm]
    simp
  rw [hdeg, hop1, hop2]
  rw [Polynomial.resultant_map_map (f := D.map (C : K →+* K[X]))
    (g := A.map (C : K →+* K[X]) - C Polynomial.X * (derivative D).map (C : K →+* K[X]))
    (Polynomial.mapRingHom σ) (m := D.natDegree) (n := D.natDegree - 1)]
  rw [Polynomial.coe_mapRingHom]

/-! ### Root multiplicity of `C c · p³` at a simple root of `p` -/

/-- `rootMultiplicity β (p^n) = n · rootMultiplicity β p` for `p ≠ 0`. -/
theorem rootMultiplicity_pow {F : Type*} [Field F] {p : F[X]} (hp0 : p ≠ 0) (β : F) (n : ℕ) :
    Polynomial.rootMultiplicity β (p ^ n) = n * Polynomial.rootMultiplicity β p := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero m hp0) hp0), ih]
    ring

/-- A nonzero scalar times `p^n` has multiplicity `n` at each root of separable `p`. -/
theorem rootMultiplicity_C_mul_pow_of_separable {F : Type*} [Field F] {c : F} (hc : c ≠ 0)
    {p : F[X]} (hsep : p.Separable) {β : F} (hβ : p.IsRoot β) (n : ℕ) :
    Polynomial.rootMultiplicity β (Polynomial.C c * p ^ n) = n := by
  have hp0 : p ≠ 0 := hsep.ne_zero
  have hpn0 : p ^ n ≠ 0 := pow_ne_zero n hp0
  have hCc0 : (Polynomial.C c : F[X]) ≠ 0 := by simpa [Polynomial.C_eq_zero] using hc
  -- `rootMult β (C c · pⁿ) = rootMult β (C c) + rootMult β (pⁿ)`
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hCc0 hpn0)]
  -- `rootMult β (C c) = 0`
  have hCmult : Polynomial.rootMultiplicity β (Polynomial.C c) = 0 := by
    rw [Polynomial.rootMultiplicity_eq_zero]
    simp [Polynomial.IsRoot, hc]
  -- `rootMult β p = 1` (simple root of a separable polynomial)
  have hp1 : Polynomial.rootMultiplicity β p = 1 := by
    have hle := Polynomial.rootMultiplicity_le_one_of_separable hsep β
    have hge : 1 ≤ Polynomial.rootMultiplicity β p :=
      (Polynomial.rootMultiplicity_pos hp0).mpr hβ
    omega
  rw [hCmult, zero_add, rootMultiplicity_pow hp0, hp1, mul_one]


/-! ### `lrtSubresultant` under an injective base change, and the eval-commute -/

/-- `lrtSubresultant` commutes with an injective base change `ι : F →+* G`:
`(lrtSubresultant A D j).map (mapRingHom ι) = lrtSubresultant (A.map ι) (D.map ι) j`. -/
theorem lrtSubresultant_map_of_injective {F G : Type*} [Field F] [Field G] (ι : F →+* G)
    (hι : Function.Injective ι) (A D : F[X]) (j : ℕ) :
    (lrtSubresultant A D j).map (Polynomial.mapRingHom ι) = lrtSubresultant (A.map ι) (D.map ι) j := by
  rw [lrtSubresultant, lrtSubresultant]
  have hdeg : (D.map ι).natDegree = D.natDegree := Polynomial.natDegree_map_eq_of_injective hι D
  have hcomm : (C : G →+* G[X]).comp ι = (Polynomial.mapRingHom ι).comp (C : F →+* F[X]) := by
    ext k; simp
  -- rewrite the RHS operands as `(operand over F[X]).map (mapRingHom ι)`
  have hop1 : (D.map ι).map (C : G →+* G[X])
      = (D.map (C : F →+* F[X])).map (Polynomial.mapRingHom ι) := by
    rw [Polynomial.map_map, Polynomial.map_map, hcomm]
  have hop2 : (A.map ι).map (C : G →+* G[X])
          - C Polynomial.X * (derivative (D.map ι)).map (C : G →+* G[X])
      = (A.map (C : F →+* F[X])
          - C Polynomial.X * (derivative D).map (C : F →+* F[X])).map (Polynomial.mapRingHom ι) := by
    have hAmap : (A.map ι).map (C : G →+* G[X])
        = (A.map (C : F →+* F[X])).map (Polynomial.mapRingHom ι) := by
      rw [Polynomial.map_map, hcomm, ← Polynomial.map_map]
    have hDmap : (derivative (D.map ι)).map (C : G →+* G[X])
        = ((derivative D).map (C : F →+* F[X])).map (Polynomial.mapRingHom ι) := by
      rw [derivative_map, Polynomial.map_map, Polynomial.map_map, hcomm]
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.coe_mapRingHom,
      Polynomial.map_X]
    exact congrArg₂ (fun x y : Polynomial (Polynomial G) => x - y) hAmap
      (congrArg₂ (fun x y : Polynomial (Polynomial G) => x * y) rfl hDmap)
  rw [hdeg, hop1, hop2, subresultant_map]

/-- Eval-after-map commutes with an injective base change `ι`:
`((lrtSubresultant A D j).map (evalRingHom a)).map ι = (lrtSubresultant (A.map ι) (D.map ι) j).map (evalRingHom (ι a))`. -/
theorem map_eval_lrtSubresultant_map {F G : Type*} [Field F] [Field G] (ι : F →+* G)
    (hι : Function.Injective ι) (A D : F[X]) (j : ℕ) (a : F) :
    ((lrtSubresultant A D j).map (Polynomial.evalRingHom a)).map ι
      = (lrtSubresultant (A.map ι) (D.map ι) j).map (Polynomial.evalRingHom (ι a)) := by
  rw [← lrtSubresultant_map_of_injective ι hι, Polynomial.map_map, Polynomial.map_map]
  congr 1
  ext q
  · simp
  · simp [Polynomial.coe_mapRingHom]


end DeepWiki.SymbolicIntegration
