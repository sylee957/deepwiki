import DeepWiki.SymbolicIntegration.RiobooLogToRealSplit

/-! # Coprimality of the real and imaginary parts of the LRT gcd
From the gcd-cofactor factorizations `C − (a+i·b)·D' = (E₁+i·E₂)·(A+i·B)` and `D = (F₁+i·F₂)·(A+i·B)`
with `D` squarefree and `b` a unit, the real and imaginary parts `A, B` are coprime (`rioboo_coprime`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

section Coprimality
variable {S : Type*} [CommRing S] [IsDomain S] [CharZero S]

/-- With `i² = −1`, a conjugation `σ` (`σ i = −i`) fixing `i`-free `a₁, a₂, b₁, b₂`, in a char-`0`
domain, `a₁ + i·a₂ = b₁ + i·b₂ ⟹ a₁ = b₁ ∧ a₂ = b₂`. -/
theorem eq_and_eq_of_add_imag_eq {i a₁ a₂ b₁ b₂ : S} (hi : i ^ 2 = -1)
    (σ : S →+* S) (hσi : σ i = -i)
    (hσa₁ : σ a₁ = a₁) (hσa₂ : σ a₂ = a₂) (hσb₁ : σ b₁ = b₁) (hσb₂ : σ b₂ = b₂)
    (h : a₁ + i * a₂ = b₁ + i * b₂) : a₁ = b₁ ∧ a₂ = b₂ := by
  -- Reduce to `(a₁ − b₁) + i·(a₂ − b₂) = 0` and its conjugate.
  have hi0 : (i : S) ≠ 0 := by rintro rfl; simp at hi
  have h1 : (a₁ - b₁) + i * (a₂ - b₂) = 0 := by linear_combination h
  have hc : (a₁ - b₁) - i * (a₂ - b₂) = 0 := by
    have := congrArg σ h1
    rw [map_add, map_mul, hσi, map_sub, hσa₁, hσb₁, map_sub, hσa₂, hσb₂, map_zero,
      neg_mul] at this
    linear_combination this
  have hP : (2 : S) * (a₁ - b₁) = 0 := by linear_combination h1 + hc
  have hiQ : (2 : S) * (i * (a₂ - b₂)) = 0 := by linear_combination h1 - hc
  refine ⟨sub_eq_zero.mp ((mul_eq_zero.mp hP).resolve_left two_ne_zero), sub_eq_zero.mp ?_⟩
  have := (mul_eq_zero.mp hiQ).resolve_left two_ne_zero
  exact (mul_eq_zero.mp this).resolve_left hi0

/-- Imaginary part of `C − (a+i·b)·D' = (E₁ + i·E₂)·(A + i·B)` (all operands `i`-free): `−b·D' = E₁·B + E₂·A`. -/
theorem imagPart_eq_of_mul_split {i a b C D' E₁ E₂ A B : S} (hi : i ^ 2 = -1)
    (σ : S →+* S) (hσi : σ i = -i)
    (hσa : σ a = a) (hσb : σ b = b) (hσC : σ C = C) (hσD' : σ D' = D')
    (hσE₁ : σ E₁ = E₁) (hσE₂ : σ E₂ = E₂) (hσA : σ A = A) (hσB : σ B = B)
    (h : C - (a + i * b) * D' = (E₁ + i * E₂) * (A + i * B)) :
    -(b * D') = E₁ * B + E₂ * A := by
  -- Write both sides as `(i-free) + i·(imag)` and match the `i`-component.
  have hform : (C - a * D') + i * (-(b * D'))
      = (E₁ * A - E₂ * B) + i * (E₁ * B + E₂ * A) := by
    linear_combination h + (B * E₂) * hi
  have hσreL : σ (C - a * D') = C - a * D' := by
    rw [map_sub, hσC, map_mul, hσa, hσD']
  have hσimL : σ (-(b * D')) = -(b * D') := by
    rw [map_neg, map_mul, hσb, hσD']
  have hσreR : σ (E₁ * A - E₂ * B) = E₁ * A - E₂ * B := by
    rw [map_sub, map_mul, hσE₁, hσA, map_mul, hσE₂, hσB]
  have hσimR : σ (E₁ * B + E₂ * A) = E₁ * B + E₂ * A := by
    rw [map_add, map_mul, hσE₁, hσB, map_mul, hσE₂, hσA]
  exact (eq_and_eq_of_add_imag_eq hi σ hσi hσreL hσimL hσreR hσimR hform).2

/-- Real part of `D = (F₁ + i·F₂)·(A + i·B)` (all operands `i`-free): `D = F₁·A − F₂·B`. -/
theorem realPart_eq_of_mul_split {i D F₁ F₂ A B : S} (hi : i ^ 2 = -1)
    (σ : S →+* S) (hσi : σ i = -i)
    (hσD : σ D = D) (hσF₁ : σ F₁ = F₁) (hσF₂ : σ F₂ = F₂) (hσA : σ A = A) (hσB : σ B = B)
    (h : D = (F₁ + i * F₂) * (A + i * B)) :
    D = F₁ * A - F₂ * B := by
  have hform : D + i * (0 : S)
      = (F₁ * A - F₂ * B) + i * (F₁ * B + F₂ * A) := by
    linear_combination h + (B * F₂) * hi
  have hσreL : σ D = D := hσD
  have hσimL : σ (0 : S) = 0 := map_zero σ
  have hσreR : σ (F₁ * A - F₂ * B) = F₁ * A - F₂ * B := by
    rw [map_sub, map_mul, hσF₁, hσA, map_mul, hσF₂, hσB]
  have hσimR : σ (F₁ * B + F₂ * A) = F₁ * B + F₂ * A := by
    rw [map_add, map_mul, hσF₁, hσB, map_mul, hσF₂, hσA]
  exact (eq_and_eq_of_add_imag_eq hi σ hσi hσreL hσimL hσreR hσimR hform).1

/-- Given `C − (a+i·b)·D' = (E₁ + i·E₂)·(A + i·B)`, `D = (F₁ + i·F₂)·(A + i·B)` (all operands `i`-free,
`i² = −1`), `IsCoprime D D'`, and `b` a unit, the real and imaginary parts satisfy `IsCoprime A B`. -/
theorem rioboo_coprime {i a b C D D' E₁ E₂ F₁ F₂ A B : S} (hi : i ^ 2 = -1)
    (σ : S →+* S) (hσi : σ i = -i)
    (hσa : σ a = a) (hσb : σ b = b) (hσC : σ C = C) (hσD : σ D = D) (hσD' : σ D' = D')
    (hσE₁ : σ E₁ = E₁) (hσE₂ : σ E₂ = E₂) (hσF₁ : σ F₁ = F₁) (hσF₂ : σ F₂ = F₂)
    (hσA : σ A = A) (hσB : σ B = B)
    (hbunit : IsUnit b)
    (hsqfree : IsCoprime D D')
    (hresidueSplit : C - (a + i * b) * D' = (E₁ + i * E₂) * (A + i * B))
    (hdenSplit : D = (F₁ + i * F₂) * (A + i * B)) :
    IsCoprime A B := by
  -- Extract the imaginary residue equation and the real denominator equation.
  have himag : -(b * D') = E₁ * B + E₂ * A :=
    imagPart_eq_of_mul_split hi σ hσi hσa hσb hσC hσD' hσE₁ hσE₂ hσA hσB hresidueSplit
  have hreal : D = F₁ * A - F₂ * B :=
    realPart_eq_of_mul_split hi σ hσi hσD hσF₁ hσF₂ hσA hσB hdenSplit
  -- Bézout for squarefreeness: `G₁·D + G₂·D' = 1`.
  obtain ⟨G₁, G₂, hG⟩ := hsqfree
  -- `b = (b·G₁·F₁ − G₂·E₂)·A − (b·G₁·F₂ + G₂·E₁)·B`.
  have hkey : b = (b * G₁ * F₁ - G₂ * E₂) * A - (b * G₁ * F₂ + G₂ * E₁) * B := by
    have e1 : b * D = b * (F₁ * A - F₂ * B) := by rw [hreal]
    have e2 : b * D' = -(E₁ * B + E₂ * A) := by linear_combination -himag
    calc b = b * (G₁ * D + G₂ * D') := by rw [hG]; ring
      _ = G₁ * (b * D) + G₂ * (b * D') := by ring
      _ = G₁ * (b * (F₁ * A - F₂ * B)) + G₂ * -(E₁ * B + E₂ * A) := by rw [e1, e2]
      _ = (b * G₁ * F₁ - G₂ * E₂) * A - (b * G₁ * F₂ + G₂ * E₁) * B := by ring
  -- The unit `b` is a combination of `A, B`, hence `IsCoprime A B`.
  obtain ⟨c, hc⟩ := hbunit.exists_left_inv
  exact ⟨c * (b * G₁ * F₁ - G₂ * E₂), -(c * (b * G₁ * F₂ + G₂ * E₁)), by
    linear_combination c * hkey.symm + hc⟩

end Coprimality

end DeepWiki.SymbolicIntegration
