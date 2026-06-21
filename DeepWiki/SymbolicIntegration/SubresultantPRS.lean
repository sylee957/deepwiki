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

/-- **Fundamental PRS Theorem, explicit product form** (Brown–Traub §5, eq 30): the exact-constant
telescoping of `subresultant_prs_step` (eq 21) down a PRS. `Sⱼ(F₀,F₁)·∏_{l<m} αₗ^(n_{l+1}-j)` equals
`Sⱼ(Fₘ,F_{m+1})·∏_{l<m}[(-1)^((nₗ-j)(n_{l+1}-j))·(lc F_{l+1})^(nₗ-n_{l+2})·βₗ^(n_{l+1}-j)]`. The
explicit `ηᵢ/τᵢ` similarity coefficients (eq 1.9) are read off these products at the regular indices. -/
theorem subresultant_prs_telescope_explicit [IsDomain R] (F : ℕ → R[X]) (α β : ℕ → R) (Q : ℕ → R[X])
    (j : ℕ) (m : ℕ)
    (hβ : ∀ l < m, β l ≠ 0)
    (hcb : ∀ l < m, (F (l + 2)).natDegree < (F (l + 1)).natDegree)
    (hj : ∀ l < m, j < (F (l + 2)).natDegree)
    (hQ : ∀ l < m, (Q l).natDegree + (F (l + 1)).natDegree ≤ (F l).natDegree)
    (hrel : ∀ l < m, C (α l) * F l = C (β l) * F (l + 2) + F (l + 1) * Q l) :
    subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree j
        * ∏ l ∈ Finset.range m, C (α l ^ ((F (l + 1)).natDegree - j))
      = subresultant (F m) (F (m + 1)) (F m).natDegree (F (m + 1)).natDegree j
        * ∏ l ∈ Finset.range m, ((-1 : R[X]) ^ (((F l).natDegree - j) * ((F (l + 1)).natDegree - j))
            * C ((F (l + 1)).coeff (F (l + 1)).natDegree) ^ ((F l).natDegree - (F (l + 2)).natDegree)
            * C (β l ^ ((F (l + 1)).natDegree - j))) := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ← mul_assoc,
      ih (fun l hl => hβ l (by omega)) (fun l hl => hcb l (by omega)) (fun l hl => hj l (by omega))
        (fun l hl => hQ l (by omega)) (fun l hl => hrel l (by omega))]
    have h21 := subresultant_prs_step (F n) (F (n + 1)) (F (n + 2)) (Q n) (α n) (β n)
      (F n).natDegree (F (n + 1)).natDegree (F (n + 2)).natDegree j (hβ n (by omega))
      (hj n (by omega)) (hcb n (by omega)) rfl le_rfl (hQ n (by omega)) (hrel n (by omega))
    linear_combination (∏ l ∈ Finset.range n,
      ((-1 : R[X]) ^ (((F l).natDegree - j) * ((F (l + 1)).natDegree - j))
        * C ((F (l + 1)).coeff (F (l + 1)).natDegree) ^ ((F l).natDegree - (F (l + 2)).natDegree)
        * C (β l ^ ((F (l + 1)).natDegree - j)))) * h21

/-- **Fundamental PRS Theorem, vanishing branch** (Bronstein Thm 1.5.2, the `Sⱼ(A,B) = 0` case): if the
subresultant at the telescope endpoint vanishes (`Sⱼ(Fₘ,F_{m+1}) = 0` — e.g. a gap index, by
`subresultant_prs_step_gap`), then `Sⱼ(F₀,F₁) = 0`. The explicit telescope (eq 30) gives
`Sⱼ(F₀,F₁)·∏ C(αₗ^…) = 0`, and the `α`-product is nonzero in the domain, so `Sⱼ(F₀,F₁) = 0`. -/
theorem subresultant_prs_vanish [IsDomain R] (F : ℕ → R[X]) (α β : ℕ → R) (Q : ℕ → R[X])
    (j : ℕ) (m : ℕ)
    (hα : ∀ l < m, α l ≠ 0) (hβ : ∀ l < m, β l ≠ 0)
    (hcb : ∀ l < m, (F (l + 2)).natDegree < (F (l + 1)).natDegree)
    (hj : ∀ l < m, j < (F (l + 2)).natDegree)
    (hQ : ∀ l < m, (Q l).natDegree + (F (l + 1)).natDegree ≤ (F l).natDegree)
    (hrel : ∀ l < m, C (α l) * F l = C (β l) * F (l + 2) + F (l + 1) * Q l)
    (hend : subresultant (F m) (F (m + 1)) (F m).natDegree (F (m + 1)).natDegree j = 0) :
    subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree j = 0 := by
  have h30 := subresultant_prs_telescope_explicit F α β Q j m hβ hcb hj hQ hrel
  rw [hend, zero_mul] at h30
  have hprod : (∏ l ∈ Finset.range m, C (α l ^ ((F (l + 1)).natDegree - j))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro l hl
    rw [Ne, C_eq_zero]
    exact pow_ne_zero _ (hα l (Finset.mem_range.mp hl))
  exact (mul_eq_zero.mp h30).resolve_right hprod

/-- **Fundamental PRS Theorem, regular index `j = deg C`** (Brown–Traub eq 22): across a PRS step
`α·A = β·C + B·Q` (with `C ≠ 0`, `lc B ≠ 0`, `α,β ≠ 0`), `S_{deg C}(A,B)` is similar to the remainder
`C` itself. From `subresultant_prs_step_deg`. -/
theorem subresultant_prs_similar_remainder [IsDomain R] (A B C_poly Q : R[X]) (α β : R) (a b c : ℕ)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hlcB : B.coeff b ≠ 0) (hC : C_poly ≠ 0) (hcb : c < b)
    (hcpoly : C_poly.natDegree = c) (hB : B.natDegree ≤ b) (hQ : Q.natDegree + b ≤ a)
    (hrel : C α * A = C β * C_poly + B * Q) :
    IsSimilar (subresultant A B a b c) C_poly := by
  have hlcBC : (C β * C_poly).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr (mul_ne_zero (by rwa [Ne, C_eq_zero]) hC)
  refine ⟨α ^ (b - c),
    (-1 : R) ^ ((a - c) * (b - c)) * (B.coeff b) ^ (a - c)
      * (C β * C_poly).leadingCoeff ^ (b - c - 1) * β,
    pow_ne_zero _ hα,
    mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hlcB))
      (pow_ne_zero _ hlcBC)) hβ, ?_⟩
  rw [subresultant_prs_step_deg A B C_poly Q α β a b c hβ hcb hcpoly hB hQ hrel]
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

/-- **Fundamental PRS Theorem, regular index `j = deg B − 1`** (Brown–Traub eq 24): across a PRS step,
`S_{deg B-1}(A,B)` is similar to the remainder `C`. From `subresultant_prs_step_top`. -/
theorem subresultant_prs_similar_remainder_top [IsDomain R] (A B C_poly Q : R[X]) (α β : R)
    (a b c : ℕ) (hα : α ≠ 0) (hβ : β ≠ 0) (hlcB : B.coeff b ≠ 0) (hcb : c < b)
    (hcpoly : C_poly.natDegree = c) (hB : B.natDegree ≤ b) (hQ : Q.natDegree + b ≤ a)
    (hrel : C α * A = C β * C_poly + B * Q) :
    IsSimilar (subresultant A B a b (b - 1)) C_poly := by
  refine ⟨α, (-1 : R) ^ (a - b + 1) * (B.coeff b) ^ (a - b + 1) * β, hα,
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hlcB)) hβ, ?_⟩
  rw [subresultant_prs_step_top A B C_poly Q α β a b c hβ hcb hcpoly hB hQ hrel]
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

/-- **Fundamental PRS Theorem, nonzero case** (Bronstein Thm 1.5.2): at the regular index
`j = deg F_{m+2}`, the subresultant `Sⱼ(F₀,F₁)` is *similar to the PRS element* `F_{m+2}` — telescoping
the similarity down to `Sⱼ(Fₘ,F_{m+1})` and then to the remainder `F_{m+2}` (`subresultant_prs_similar_remainder`)
via `IsSimilar.trans`. This is the structural content of Thm 1.5.2: every nonzero subresultant of `A,B`
is similar to a PRS element. -/
theorem subresultant_prs_similar_elt [IsDomain R] (F : ℕ → R[X]) (α β : ℕ → R) (Q : ℕ → R[X]) (m : ℕ)
    (hα : ∀ l ≤ m, α l ≠ 0) (hβ : ∀ l ≤ m, β l ≠ 0)
    (hlc : ∀ l ≤ m, (F (l + 1)).coeff (F (l + 1)).natDegree ≠ 0)
    (hcb : ∀ l ≤ m, (F (l + 2)).natDegree < (F (l + 1)).natDegree)
    (hj : ∀ l < m, (F (m + 2)).natDegree < (F (l + 2)).natDegree)
    (hQ : ∀ l ≤ m, (Q l).natDegree + (F (l + 1)).natDegree ≤ (F l).natDegree)
    (hrel : ∀ l ≤ m, C (α l) * F l = C (β l) * F (l + 2) + F (l + 1) * Q l)
    (hC : F (m + 2) ≠ 0) :
    IsSimilar (subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree (F (m + 2)).natDegree)
      (F (m + 2)) :=
  (subresultant_prs_telescope F α β Q (F (m + 2)).natDegree m
      (fun l hl => hα l (by omega)) (fun l hl => hβ l (by omega)) (fun l hl => hlc l (by omega))
      (fun l hl => hcb l (by omega)) hj (fun l hl => hQ l (by omega))
      (fun l hl => hrel l (by omega))).trans
    (subresultant_prs_similar_remainder (F m) (F (m + 1)) (F (m + 2)) (Q m) (α m) (β m)
      (F m).natDegree (F (m + 1)).natDegree (F (m + 2)).natDegree (hα m le_rfl) (hβ m le_rfl)
      (hlc m le_rfl) hC (hcb m le_rfl) rfl le_rfl (hQ m le_rfl) (hrel m le_rfl))

/-- `IsSimilar p q` over a domain lifts to an exact rational scalar over the field of fractions:
`p = C η · q` in `Frac(D)[x]` for some nonzero `η ∈ Frac(D)` (namely `η = b/a` from the witnesses
`C a · p = C b · q`). -/
theorem IsSimilar.exists_fractionRing {D : Type*} [CommRing D] [IsDomain D] {p q : D[X]}
    (h : IsSimilar p q) :
    ∃ η : FractionRing D, η ≠ 0 ∧
      p.map (algebraMap D (FractionRing D)) = C η * q.map (algebraMap D (FractionRing D)) := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  have hinj := IsFractionRing.injective D (FractionRing D)
  have hφa : algebraMap D (FractionRing D) a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha
  have hφb : algebraMap D (FractionRing D) b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb
  refine ⟨algebraMap D (FractionRing D) b / algebraMap D (FractionRing D) a,
    div_ne_zero hφb hφa, ?_⟩
  have key : C (algebraMap D (FractionRing D) a) * p.map (algebraMap D (FractionRing D))
      = C (algebraMap D (FractionRing D) b) * q.map (algebraMap D (FractionRing D)) := by
    rw [← Polynomial.map_C, ← Polynomial.map_C, ← Polynomial.map_mul, ← Polynomial.map_mul, hab]
  calc p.map (algebraMap D (FractionRing D))
      = C ((algebraMap D (FractionRing D) a)⁻¹) * (C (algebraMap D (FractionRing D) a)
          * p.map (algebraMap D (FractionRing D))) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hφa, map_one, one_mul]
    _ = C ((algebraMap D (FractionRing D) a)⁻¹) * (C (algebraMap D (FractionRing D) b)
          * q.map (algebraMap D (FractionRing D))) := by rw [key]
    _ = C (algebraMap D (FractionRing D) b / algebraMap D (FractionRing D) a)
          * q.map (algebraMap D (FractionRing D)) := by rw [div_eq_mul_inv, map_mul]; ring
/-- **Theorem 1.5.2** (Bronstein §1.5, p.23) — exact rational coefficient form over `Frac(D)`: at a
regular index `j = deg F_{m+2}`, the subresultant equals an explicit nonzero rational multiple `ηᵢ` of
the PRS element, `Sⱼ(F₀,F₁) = ηᵢ · F_{m+2}` in `Frac(D)[x]`. (The structural `D[x]` similarity is
`subresultant_prs_similar_elt`; here it is lifted to the exact scalar `ηᵢ ∈ Frac(D)` via
`IsSimilar.exists_fractionRing`.) -/
theorem subresultant_prs_eq_fractionRing {D : Type*} [CommRing D] [IsDomain D]
    (F : ℕ → D[X]) (α β : ℕ → D) (Q : ℕ → D[X]) (m : ℕ)
    (hα : ∀ l ≤ m, α l ≠ 0) (hβ : ∀ l ≤ m, β l ≠ 0)
    (hlc : ∀ l ≤ m, (F (l + 1)).coeff (F (l + 1)).natDegree ≠ 0)
    (hcb : ∀ l ≤ m, (F (l + 2)).natDegree < (F (l + 1)).natDegree)
    (hj : ∀ l < m, (F (m + 2)).natDegree < (F (l + 2)).natDegree)
    (hQ : ∀ l ≤ m, (Q l).natDegree + (F (l + 1)).natDegree ≤ (F l).natDegree)
    (hrel : ∀ l ≤ m, C (α l) * F l = C (β l) * F (l + 2) + F (l + 1) * Q l)
    (hC : F (m + 2) ≠ 0) :
    ∃ η : FractionRing D, η ≠ 0 ∧
      (subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree (F (m + 2)).natDegree).map
          (algebraMap D (FractionRing D))
        = C η * (F (m + 2)).map (algebraMap D (FractionRing D)) :=
  (subresultant_prs_similar_elt F α β Q m hα hβ hlc hcb hj hQ hrel hC).exists_fractionRing

/-- **Fundamental PRS Theorem, nonzero case at the other regular index `j = deg F_{m+1} − 1`** (Bronstein
Thm 1.5.2): `Sⱼ(F₀,F₁)` is similar to the PRS element `F_{m+2}` — telescoping the similarity to the
endpoint and then to the remainder via `subresultant_prs_similar_remainder_top` (eq 24). Together with
`subresultant_prs_similar_elt` (the `j = deg F_{m+2}` index), this covers both regular indices. -/
theorem subresultant_prs_similar_elt_top [IsDomain R] (F : ℕ → R[X]) (α β : ℕ → R) (Q : ℕ → R[X])
    (m : ℕ) (hα : ∀ l ≤ m, α l ≠ 0) (hβ : ∀ l ≤ m, β l ≠ 0)
    (hlc : ∀ l ≤ m, (F (l + 1)).coeff (F (l + 1)).natDegree ≠ 0)
    (hcb : ∀ l ≤ m, (F (l + 2)).natDegree < (F (l + 1)).natDegree)
    (hj : ∀ l < m, (F (m + 1)).natDegree - 1 < (F (l + 2)).natDegree)
    (hQ : ∀ l ≤ m, (Q l).natDegree + (F (l + 1)).natDegree ≤ (F l).natDegree)
    (hrel : ∀ l ≤ m, C (α l) * F l = C (β l) * F (l + 2) + F (l + 1) * Q l) :
    IsSimilar (subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree ((F (m + 1)).natDegree - 1))
      (F (m + 2)) :=
  (subresultant_prs_telescope F α β Q ((F (m + 1)).natDegree - 1) m
      (fun l hl => hα l (by omega)) (fun l hl => hβ l (by omega)) (fun l hl => hlc l (by omega))
      (fun l hl => hcb l (by omega)) hj (fun l hl => hQ l (by omega))
      (fun l hl => hrel l (by omega))).trans
    (subresultant_prs_similar_remainder_top (F m) (F (m + 1)) (F (m + 2)) (Q m) (α m) (β m)
      (F m).natDegree (F (m + 1)).natDegree (F (m + 2)).natDegree (hα m le_rfl) (hβ m le_rfl)
      (hlc m le_rfl) (hcb m le_rfl) rfl le_rfl (hQ m le_rfl) (hrel m le_rfl))

end DeepWiki.SymbolicIntegration
