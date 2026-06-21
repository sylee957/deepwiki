import DeepWiki.SymbolicIntegration.Subresultants
import DeepWiki.SymbolicIntegration.PseudoDivision

/-! # The subresultant Fundamental PRS Theorem (Bronstein §1.5, Brown–Traub §5)
The subresultants of consecutive elements of a polynomial remainder sequence are *similar*
(`IsSimilar`, from `PseudoDivision`), so `Sⱼ(F₁,F₂)` is similar to `Sⱼ(Fₘ,F_{m+1})` for every step.
This is the subresultant counterpart of the gcd-based Theorem 1.5.1 (`IsPRS.isSimilar_gcd`), built by
telescoping the single-step relation `subresultant_prs_step` (Brown–Traub Lemma 2, eq 21). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {R : Type*} [CommRing R]

/-- **Fundamental PRS Theorem, per-step similarity** (Brown–Traub §5): across one PRS division step
`α·A = β·C + B·Q` (with `lc B ≠ 0`, `α, β ≠ 0`), the subresultants `Sⱼ(A,B)` and `Sⱼ(B,C)` are
similar (`0 ≤ j < deg C`). The similarity constants are read off `subresultant_prs_step` (eq 21). -/
theorem subresultant_prs_similar [IsDomain R] (A B C_poly Q : R[X]) (α β : R) (a b c j : ℕ)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hlcB : B.coeff b ≠ 0) (hjc : j < c) (hcb : c < b)
    (hcpoly : C_poly.natDegree = c) (hB : B.natDegree ≤ b) (hQ : Q.natDegree + b ≤ a)
    (hrel : C α * A = C β * C_poly + B * Q) :
    IsSimilar (subresultant A B a b j) (subresultant B C_poly b c j) := by
  refine ⟨α ^ (b - j), (-1 : R) ^ ((a - j) * (b - j)) * (B.coeff b) ^ (a - c) * β ^ (b - j),
    pow_ne_zero _ hα,
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hlcB)) (pow_ne_zero _ hβ),
    ?_⟩
  rw [subresultant_prs_step A B C_poly Q α β a b c j hβ hjc hcb hcpoly hB hQ hrel,
    map_mul, map_mul, map_pow, map_pow, map_pow, map_neg, map_one]
  ring

/-- **Fundamental PRS Theorem** (Brown–Traub §5, eqs 30–31; Bronstein Thm 1.5.2 core): for a PRS `F`
with division steps `α l·F l = β l·F (l+2) + F (l+1)·Q l` (`0 ≤ j < deg F(l+2)`, degrees strictly
decreasing, leading/scaling coefficients nonzero), the first subresultant `Sⱼ(F₀,F₁)` is similar to
`Sⱼ(Fₘ,F_{m+1})` for every `m`. Telescopes the per-step similarity `subresultant_prs_similar` by
induction on `m` via `IsSimilar.trans`. -/
theorem subresultant_prs_telescope [IsDomain R] (F : ℕ → R[X]) (α β : ℕ → R) (Q : ℕ → R[X])
    (j : ℕ) (m : ℕ)
    (hα : ∀ l < m, α l ≠ 0) (hβ : ∀ l < m, β l ≠ 0)
    (hlc : ∀ l < m, (F (l + 1)).coeff (F (l + 1)).natDegree ≠ 0)
    (hcb : ∀ l < m, (F (l + 2)).natDegree < (F (l + 1)).natDegree)
    (hj : ∀ l < m, j < (F (l + 2)).natDegree)
    (hQ : ∀ l < m, (Q l).natDegree + (F (l + 1)).natDegree ≤ (F l).natDegree)
    (hrel : ∀ l < m, C (α l) * F l = C (β l) * F (l + 2) + F (l + 1) * Q l) :
    IsSimilar (subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree j)
      (subresultant (F m) (F (m + 1)) (F m).natDegree (F (m + 1)).natDegree j) := by
  induction m with
  | zero => exact IsSimilar.refl _
  | succ n ih =>
    refine (ih (fun l hl => hα l (by omega)) (fun l hl => hβ l (by omega))
      (fun l hl => hlc l (by omega)) (fun l hl => hcb l (by omega)) (fun l hl => hj l (by omega))
      (fun l hl => hQ l (by omega)) (fun l hl => hrel l (by omega))).trans ?_
    exact subresultant_prs_similar (F n) (F (n + 1)) (F (n + 2)) (Q n) (α n) (β n)
      (F n).natDegree (F (n + 1)).natDegree (F (n + 2)).natDegree j
      (hα n (by omega)) (hβ n (by omega)) (hlc n (by omega)) (hj n (by omega)) (hcb n (by omega))
      rfl le_rfl (hQ n (by omega)) (hrel n (by omega))

end DeepWiki.SymbolicIntegration
