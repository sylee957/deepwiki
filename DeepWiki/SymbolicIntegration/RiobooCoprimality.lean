import DeepWiki.SymbolicIntegration.RiobooLogToRealSplit

/-! # Rioboo's `LogToReal` specializes well — coprimality of the real/imaginary parts (Bronstein §2.8, Thm 2.8.4)
Theorem 2.8.4 (Rioboo, p.67–68) guarantees that Rioboo's arctangent reduction `φ(u,v,x)` specializes
without division by `0`: when `R = P + i·Q` is a squarefree factor of the Rothstein–Trager resultant
of `C/D` and `S = A + i·B` is the LRT gcd, then for every `a, b ∈ K̄` solving `P(a,b) = Q(a,b) = 0`
with `b ≠ 0`, the real/imaginary parts `A(a,b,x), B(a,b,x)` are **coprime** in `K(a,b)[x]` — so the
arctan numerator `(A·D + B·C)/(B·D − A·C)` has a nonzero denominator.

The proof is **purely algebraic** (Bézout); the real closure is only the setting for `a, b`. We take
the LRT gcd-cofactor factorizations as hypotheses (the faithful "`A+iB` is a common divisor of
`C − (a+i·b)·D'` and `D`" content):
* (2.27) `C − (a+i·b)·D' = (E₁ + i·E₂)·(A + i·B)`
* (2.28) `D = (F₁ + i·F₂)·(A + i·B)`
and derive, by **equating `i`-free and `i`-components through a conjugation `σ` (`σ i = −i`)**:
* (2.29) `−b·D' = E₁·B + E₂·A`   (imaginary part of (2.27); `C, D'` are `i`-free, `Im(−(a+ib)D') = −b·D'`)
* (2.30) `D = F₁·A − F₂·B`        (real part of (2.28)).
Then `D` squarefree (`IsCoprime D D'`) gives `G₁·D + G₂·D' = 1`, and
`b = b·(G₁D + G₂D') = (bG₁F₁ − G₂E₂)·A − (bG₁F₂ + G₂E₁)·B`, so `b ∈ span {A, B}`; with `b` a unit
this is `IsCoprime A B`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

section Coprimality
variable {S : Type*} [CommRing S] [IsDomain S] [CharZero S]

/-- **`i`-free component extraction** (§2.8, the real/imag matching behind (2.27)⟹(2.29),
(2.28)⟹(2.30)): in a char-`0` integral domain with `i² = −1` and a conjugation `σ` (`σ i = −i`)
certifying `a₁, a₂, b₁, b₂` are `i`-free (`σ` fixes each), `a₁ + i·a₂ = b₁ + i·b₂ ⟹ a₁ = b₁ ∧ a₂ = b₂`.
Subtract to reduce to `(a₁−b₁) + i·(a₂−b₂) = 0` and its conjugate, then cancel `2` (char `0`) and
`i` (nonzero since `i² = −1`). The domain `(K(a,b))(i)[x]` of the §2.8 application qualifies. -/
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

/-- **Imaginary part of (2.27) ⟹ (2.29)** (§2.8, p.68): from
`C − (a+i·b)·D' = (E₁ + i·E₂)·(A + i·B)` (`i² = −1`, all of `C, D', E₁, E₂, A, B, a, b` `i`-free,
certified by a conjugation `σ` and `2`-cancellation), taking the imaginary part gives
`−b·D' = E₁·B + E₂·A`. (The `i`-free part is `(2.30)`-style `C − a·D' = E₁·A − E₂·B`; we only need the
imaginary half here.) -/
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

/-- **Real part of (2.28) ⟹ (2.30)** (§2.8, p.68): from `D = (F₁ + i·F₂)·(A + i·B)` (`i² = −1`, all of
`D, F₁, F₂, A, B` `i`-free, certified by a conjugation `σ` and `2`-cancellation), taking the real part
gives `D = F₁·A − F₂·B`. -/
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

/-- **Theorem 2.8.4, the Bézout coprimality core** (§2.8, p.67–68, Rioboo): given the LRT gcd-cofactor
factorizations
* (2.27) `C − (a+i·b)·D' = (E₁ + i·E₂)·(A + i·B)`,
* (2.28) `D = (F₁ + i·F₂)·(A + i·B)`,
with `i² = −1`, `D` squarefree (`IsCoprime D D'`, `D' = D'`), `b` a unit (`b ≠ 0` in a field), and a
conjugation `σ` (`σ i = −i`) certifying all of `a, b, C, D, D', E₁, E₂, F₁, F₂, A, B` are `i`-free,
then **`IsCoprime A B`** — i.e. `gcd(A, B) = 1`. Proof: imaginary part of (2.27) gives
`(2.29) −b·D' = E₁B + E₂A`, real part of (2.28) gives `(2.30) D = F₁A − F₂B`; with `G₁D + G₂D' = 1`
from squarefreeness, `b = b(G₁D + G₂D') = (bG₁F₁ − G₂E₂)·A − (bG₁F₂ + G₂E₁)·B`, so the unit `b` lies
in `span {A, B}`, giving `IsCoprime A B`. -/
theorem rioboo_coprime {i a b C D D' E₁ E₂ F₁ F₂ A B : S} (hi : i ^ 2 = -1)
    (σ : S →+* S) (hσi : σ i = -i)
    (hσa : σ a = a) (hσb : σ b = b) (hσC : σ C = C) (hσD : σ D = D) (hσD' : σ D' = D')
    (hσE₁ : σ E₁ = E₁) (hσE₂ : σ E₂ = E₂) (hσF₁ : σ F₁ = F₁) (hσF₂ : σ F₂ = F₂)
    (hσA : σ A = A) (hσB : σ B = B)
    (hbunit : IsUnit b)
    (hsqfree : IsCoprime D D')
    (h27 : C - (a + i * b) * D' = (E₁ + i * E₂) * (A + i * B))
    (h28 : D = (F₁ + i * F₂) * (A + i * B)) :
    IsCoprime A B := by
  -- (2.29) and (2.30).
  have h29 : -(b * D') = E₁ * B + E₂ * A :=
    imagPart_eq_of_mul_split hi σ hσi hσa hσb hσC hσD' hσE₁ hσE₂ hσA hσB h27
  have h30 : D = F₁ * A - F₂ * B :=
    realPart_eq_of_mul_split hi σ hσi hσD hσF₁ hσF₂ hσA hσB h28
  -- Bézout for squarefreeness: `G₁·D + G₂·D' = 1`.
  obtain ⟨G₁, G₂, hG⟩ := hsqfree
  -- `b = (b·G₁·F₁ − G₂·E₂)·A − (b·G₁·F₂ + G₂·E₁)·B`.
  have hkey : b = (b * G₁ * F₁ - G₂ * E₂) * A - (b * G₁ * F₂ + G₂ * E₁) * B := by
    have e1 : b * D = b * (F₁ * A - F₂ * B) := by rw [h30]
    have e2 : b * D' = -(E₁ * B + E₂ * A) := by linear_combination -h29
    calc b = b * (G₁ * D + G₂ * D') := by rw [hG]; ring
      _ = G₁ * (b * D) + G₂ * (b * D') := by ring
      _ = G₁ * (b * (F₁ * A - F₂ * B)) + G₂ * -(E₁ * B + E₂ * A) := by rw [e1, e2]
      _ = (b * G₁ * F₁ - G₂ * E₂) * A - (b * G₁ * F₂ + G₂ * E₁) * B := by ring
  -- The unit `b` is a combination of `A, B`, hence `IsCoprime A B`.
  obtain ⟨c, hc⟩ := hbunit.exists_left_inv
  exact ⟨c * (b * G₁ * F₁ - G₂ * E₂), -(c * (b * G₁ * F₂ + G₂ * E₁)), by
    linear_combination c * hkey.symm + hc⟩

end Coprimality

section Restatement
variable {S : Type*} [CommRing S] [IsDomain S] [CharZero S]

/-- Restatement of **Theorem 2.8.4** against the book wording (§2.8, p.67–68): with `R = P + i·Q` a
squarefree RT-resultant factor and `S = A + i·B` the LRT gcd, given the gcd-cofactor relations
`C − (a+i·b)·D' = (E₁+i·E₂)(A+i·B)` (2.27), `D = (F₁+i·F₂)(A+i·B)` (2.28), `D` squarefree, and `b ≠ 0`
(a unit), then `gcd(A(a,b,x), B(a,b,x)) = 1` in `K(a,b)[x]` — here as `IsCoprime A B`. -/
example {i a b C D D' E₁ E₂ F₁ F₂ A B : S} (hi : i ^ 2 = -1)
    (σ : S →+* S) (hσi : σ i = -i)
    (hσa : σ a = a) (hσb : σ b = b) (hσC : σ C = C) (hσD : σ D = D) (hσD' : σ D' = D')
    (hσE₁ : σ E₁ = E₁) (hσE₂ : σ E₂ = E₂) (hσF₁ : σ F₁ = F₁) (hσF₂ : σ F₂ = F₂)
    (hσA : σ A = A) (hσB : σ B = B)
    (hbunit : IsUnit b) (hsqfree : IsCoprime D D')
    (h27 : C - (a + i * b) * D' = (E₁ + i * E₂) * (A + i * B))
    (h28 : D = (F₁ + i * F₂) * (A + i * B)) :
    IsCoprime A B :=
  rioboo_coprime hi σ hσi hσa hσb hσC hσD hσD' hσE₁ hσE₂ hσF₁ hσF₂ hσA hσB hbunit hsqfree h27 h28

end Restatement

end DeepWiki.SymbolicIntegration
