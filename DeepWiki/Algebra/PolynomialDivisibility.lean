import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

/-! # Polynomial divisibility identities

Small divisibility identities for clearing polynomial denominators.
-/

namespace DeepWiki

/-- If `D ∣ R` and `gd2 ∣ (R / D) * S`, then `D * gd2 ∣ R * S`. -/
theorem polynomial_dvd_cleared_identity_of_split {K : Type*} [Field K]
    {R D gd2 S : Polynomial K}
    (hD : D ≠ 0) (hDR : D ∣ R) (hgd : gd2 ∣ (R / D) * S) :
    D * gd2 ∣ R * S := by
  obtain ⟨M, hM⟩ := hDR
  have hMeq : R / D = M := by rw [hM, mul_div_cancel_left₀ _ hD]
  rw [hMeq] at hgd
  obtain ⟨N, hN⟩ := hgd
  exact ⟨N, by rw [hM]; linear_combination D * hN⟩

/-- If `D = S * W` and `W * gd2 ∣ R`, then `D * gd2 ∣ R * S`. -/
theorem polynomial_dvd_cleared_identity_of_radical {K : Type*} [Field K]
    {R D gd2 S W : Polynomial K} (hSD : D = S * W) (hWgd : W * gd2 ∣ R) :
    D * gd2 ∣ R * S := by
  obtain ⟨N, hN⟩ := hWgd
  exact ⟨N, by rw [hSD]; linear_combination S * hN⟩

end DeepWiki
