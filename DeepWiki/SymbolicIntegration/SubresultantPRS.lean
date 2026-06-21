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

/-- **Theorem 1.5.3, base step** (the subresultant-PRS `η=1` at the first division step): for a
pseudo-division `lc(B)^(δ+1)·A = B·Q + (-1)^(δ+1)·Rem` (the subresultant choice `β = (-1)^(δ+1)`,
`δ = deg A − deg B`), the subresultant equals the remainder exactly, `S_{deg B-1}(A,B) = Rem`. The two
`(-1)^(δ+1)` factors square to `1`, so the leading-coefficient powers cancel (`η = 1`). -/
theorem subresultant_eq_pseudoRem [IsDomain R] (A B Rem Q : R[X]) (a b c : ℕ)
    (hlcB : B.coeff b ≠ 0) (hcb : c < b) (hcpoly : Rem.natDegree = c) (hB : B.natDegree ≤ b)
    (hQ : Q.natDegree + b ≤ a)
    (hrel : C ((B.coeff b) ^ (a - b + 1)) * A
      = C ((-1 : R) ^ (a - b + 1)) * Rem + B * Q) :
    subresultant A B a b (b - 1) = Rem := by
  have hstep := subresultant_prs_step_top A B Rem Q ((B.coeff b) ^ (a - b + 1)) ((-1 : R) ^ (a - b + 1))
    a b c (pow_ne_zero _ (by norm_num)) hcb hcpoly hB hQ hrel
  rw [map_pow] at hstep
  have hsq : (-1 : R[X]) ^ (a - b + 1) * (-1) ^ (a - b + 1) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have key : (C (B.coeff b)) ^ (a - b + 1) * subresultant A B a b (b - 1)
      = (C (B.coeff b)) ^ (a - b + 1) * Rem := by
    rw [hstep]
    simp only [map_pow, map_neg, map_one]
    rw [show (-1 : R[X]) ^ (a - b + 1) * ((C (B.coeff b)) ^ (a - b + 1)
        * ((-1) ^ (a - b + 1) * Rem))
      = ((-1 : R[X]) ^ (a - b + 1) * (-1) ^ (a - b + 1)) * ((C (B.coeff b)) ^ (a - b + 1) * Rem)
      from by ring, hsq, one_mul]
  exact mul_left_cancel₀ (pow_ne_zero _ (by rw [Ne, C_eq_zero]; exact hlcB)) key

/-- **Explicit closed form at the η-index** (the equation Bronstein's Thm 1.5.3 / Collins's Theorem 1(b)
specializes): combining the telescope (eq 30) at `j = deg F_{m+1} − 1` with the endpoint step (eq 24),
`Sⱼ(F₀,F₁)·(αₘ-product) = (sign·lc^·βₘ·F_{m+2})·(telescope rhs-product)`. The `ηᵢ` of Thm 1.5.2 is the
ratio of the two products; `ηᵢ = 1` is the assertion that they are equal for the subresultant p.r.s. -/
theorem subresultant_prs_closed_top [IsDomain R] (F : ℕ → R[X]) (α β : ℕ → R) (Q : ℕ → R[X]) (m : ℕ)
    (hβ : ∀ l ≤ m, β l ≠ 0)
    (hcb : ∀ l ≤ m, (F (l + 2)).natDegree < (F (l + 1)).natDegree)
    (hj : ∀ l < m, (F (m + 1)).natDegree - 1 < (F (l + 2)).natDegree)
    (hQ : ∀ l ≤ m, (Q l).natDegree + (F (l + 1)).natDegree ≤ (F l).natDegree)
    (hrel : ∀ l ≤ m, C (α l) * F l = C (β l) * F (l + 2) + F (l + 1) * Q l) :
    subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree ((F (m + 1)).natDegree - 1)
        * (C (α m)
          * ∏ l ∈ Finset.range m, C (α l ^ ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1))))
      = ((-1 : R[X]) ^ ((F m).natDegree - (F (m + 1)).natDegree + 1)
          * (C ((F (m + 1)).coeff (F (m + 1)).natDegree ^ ((F m).natDegree - (F (m + 1)).natDegree + 1))
             * (C (β m) * F (m + 2))))
        * ∏ l ∈ Finset.range m,
            ((-1 : R[X]) ^ (((F l).natDegree - ((F (m + 1)).natDegree - 1))
                  * ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1)))
              * C ((F (l + 1)).coeff (F (l + 1)).natDegree) ^ ((F l).natDegree - (F (l + 2)).natDegree)
              * C (β l ^ ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1)))) := by
  have htel := subresultant_prs_telescope_explicit F α β Q ((F (m + 1)).natDegree - 1) m
    (fun l hl => hβ l (by omega)) (fun l hl => hcb l (by omega)) hj
    (fun l hl => hQ l (by omega)) (fun l hl => hrel l (by omega))
  have htop := subresultant_prs_step_top (F m) (F (m + 1)) (F (m + 2)) (Q m) (α m) (β m)
    (F m).natDegree (F (m + 1)).natDegree (F (m + 2)).natDegree (hβ m le_rfl) (hcb m le_rfl) rfl
    le_rfl (hQ m le_rfl) (hrel m le_rfl)
  set αprod := ∏ l ∈ Finset.range m, C (α l ^ ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1)))
    with hαdef
  set Prhs := ∏ l ∈ Finset.range m,
      ((-1 : R[X]) ^ (((F l).natDegree - ((F (m + 1)).natDegree - 1))
            * ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1)))
        * C ((F (l + 1)).coeff (F (l + 1)).natDegree) ^ ((F l).natDegree - (F (l + 2)).natDegree)
        * C (β l ^ ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1)))) with hPdef
  linear_combination C (α m) * htel + Prhs * htop

section NormalCollapse

variable {M : Type*} [CommRing M]

open Finset in
/-- **Leading-coefficient product collapse** — the keystone of Collins's Theorem 1 in the normal case
(`δ=1`), which forces `ηᵢ = 1`. In `subresultant_prs_closed_top`, the normal reduced/subresultant p.r.s.
coefficients are `αₗ = (lc F_{l+1})²` and `βₗ = (lc Fₗ)²` (`β₀ = 1`); after the signs cancel
(`(-1)^(k(k+1)) = 1`), the `αₘ`-product on the left equals the `(lc² · βₗ)`-product on the right —
peeling the last `α`-factor (`prod_range_succ`) against the first `β`-factor (`prod_range_succ'`, where
`β₀ = 1` drops out) reindexes the two product tails to the same value. -/
theorem lc_prod_collapse_normal (c : ℕ → M) (n : ℕ) :
    ∏ l ∈ range (n + 1), (c (l + 1)) ^ (2 * (n + 1 - l + 1))
      = (c (n + 1)) ^ 2 * (∏ l ∈ range (n + 1), (c (l + 1)) ^ 2)
        * ∏ l ∈ range (n + 1), (if l = 0 then (1 : M) else (c l) ^ 2) ^ (n + 1 - l + 1) := by
  rw [prod_range_succ (f := fun l => (c (l + 1)) ^ (2 * (n + 1 - l + 1))),
    prod_range_succ (f := fun l => (c (l + 1)) ^ 2), prod_range_succ']
  simp only [Nat.succ_ne_zero, if_false, if_true, one_pow, mul_one]
  rw [show 2 * (n + 1 - n + 1) = 4 from by omega]
  have hcomb : (∏ x ∈ range n, (c (x + 1)) ^ 2)
        * (∏ x ∈ range n, ((c (x + 1)) ^ 2) ^ (n + 1 - (x + 1) + 1))
      = ∏ x ∈ range n, (c (x + 1)) ^ (2 * (n + 1 - x + 1)) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl (fun x hx => ?_)
    rw [← pow_mul, ← pow_add]
    rw [mem_range] at hx
    congr 1
    omega
  rw [← hcomb]
  ring

end NormalCollapse

open Finset in
/-- **Theorem 1.5.3 / Collins Theorem 1, normal case** (`ηᵢ = 1`): for a *normal* subresultant/reduced
p.r.s. — strictly degree-decreasing by one (`hdeg : (F l).natDegree = d - l`), with the coefficient
choice `αₗ = (lc F_{l+1})²` and `βₗ = (lc Fₗ)²` (`β₀ = 1`) encoded in `hrel` — the subresultant equals
the PRS element exactly: `S_{deg F_{m+1} − 1}(F₀, F₁) = F_{m+2}`. Assembles
`subresultant_prs_closed_top` (the η-index closed form), the sign cancellation (`Nat.even_mul_succ_self`),
and the leading-coefficient product collapse `lc_prod_collapse_normal`, then cancels the (nonzero) leading
product. -/
theorem subresultant_prs_normal_eq [IsDomain R] (F : ℕ → R[X]) (Q : ℕ → R[X]) (m d : ℕ)
    (hm : 1 ≤ m) (hd : m + 2 ≤ d)
    (hdeg : ∀ l ≤ m + 2, (F l).natDegree = d - l)
    (hlc : ∀ l ≤ m + 1, (F l).coeff (F l).natDegree ≠ 0)
    (hQ : ∀ l ≤ m, (Q l).natDegree + (F (l + 1)).natDegree ≤ (F l).natDegree)
    (hrel : ∀ l ≤ m,
      C (((F (l + 1)).coeff (F (l + 1)).natDegree) ^ 2) * F l
        = C (if l = 0 then (1 : R) else ((F l).coeff (F l).natDegree) ^ 2) * F (l + 2)
          + F (l + 1) * Q l) :
    subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree ((F (m + 1)).natDegree - 1)
      = F (m + 2) := by
  set α : ℕ → R := fun l => ((F (l + 1)).coeff (F (l + 1)).natDegree) ^ 2 with hα
  set β : ℕ → R := fun l => if l = 0 then (1 : R) else ((F l).coeff (F l).natDegree) ^ 2 with hβ
  have hcb : ∀ l ≤ m, (F (l + 2)).natDegree < (F (l + 1)).natDegree := by
    intro l hl; rw [hdeg (l + 2) (by omega), hdeg (l + 1) (by omega)]; omega
  have hj' : ∀ l < m, (F (m + 1)).natDegree - 1 < (F (l + 2)).natDegree := by
    intro l hl; rw [hdeg (m + 1) (by omega), hdeg (l + 2) (by omega)]; omega
  have hβne : ∀ l ≤ m, β l ≠ 0 := by
    intro l hl; simp only [hβ]; split
    · exact one_ne_zero
    · exact pow_ne_zero _ (hlc l (by omega))
  have hclosed := subresultant_prs_closed_top F α β Q m hβne hcb hj' hQ hrel
  -- degree facts (range m membership ⇒ l < m)
  have hE : ∀ l ∈ range m, (F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1) = m - l + 1 := by
    intro l hl; rw [mem_range] at hl; rw [hdeg (l + 1) (by omega), hdeg (m + 1) (by omega)]; omega
  have hG : ∀ l ∈ range m, (F l).natDegree - (F (l + 2)).natDegree = 2 := by
    intro l hl; rw [mem_range] at hl; rw [hdeg l (by omega), hdeg (l + 2) (by omega)]; omega
  have hSgn : ∀ l ∈ range m,
      (-1 : R[X]) ^ (((F l).natDegree - ((F (m + 1)).natDegree - 1))
        * ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1))) = 1 := by
    intro l hl
    refine Even.neg_one_pow ?_
    rw [mem_range] at hl
    rw [hdeg l (by omega), hdeg (l + 1) (by omega), hdeg (m + 1) (by omega)]
    rw [show d - l - (d - (m + 1) - 1) = (m - l + 1) + 1 from by omega,
      show d - (l + 1) - (d - (m + 1) - 1) = m - l + 1 from by omega, mul_comm]
    exact Nat.even_mul_succ_self _
  have hend : (F m).natDegree - (F (m + 1)).natDegree + 1 = 2 := by
    rw [hdeg m (by omega), hdeg (m + 1) (by omega)]; omega
  have hL : C (α m) * ∏ l ∈ range m, C (α l ^ ((F (l + 1)).natDegree - ((F (m + 1)).natDegree - 1)))
      = C (((F (m + 1)).coeff (F (m + 1)).natDegree) ^ 2
          * ∏ l ∈ range m, ((F (l + 1)).coeff (F (l + 1)).natDegree) ^ (2 * (m - l + 1))) := by
    rw [map_mul, map_prod]
    simp only [hα]
    congr 1
    refine prod_congr rfl (fun l hl => ?_)
    rw [hE l hl, ← pow_mul]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  set SL : R := ((F (k + 1 + 1)).coeff (F (k + 1 + 1)).natDegree) ^ 2
      * ∏ l ∈ range (k + 1), ((F (l + 1)).coeff (F (l + 1)).natDegree) ^ (2 * (k + 1 - l + 1))
    with hSLdef
  have hScal : ((F (k + 1 + 1)).coeff (F (k + 1 + 1)).natDegree) ^ 2
        * (β (k + 1) * ∏ l ∈ range (k + 1),
            (((F (l + 1)).coeff (F (l + 1)).natDegree) ^ 2 * β l ^ (k + 1 - l + 1)))
      = SL := by
    rw [hSLdef]
    have hcol := lc_prod_collapse_normal (fun l => (F l).coeff (F l).natDegree) k
    rw [hcol, prod_mul_distrib]
    simp only [hβ]
    rw [if_neg (Nat.succ_ne_zero k)]
    ring
  rw [hL] at hclosed
  have hSLne : C SL ≠ 0 := by
    rw [Ne, C_eq_zero, hSLdef]
    refine mul_ne_zero (pow_ne_zero _ (hlc (k + 1 + 1) (by omega))) ?_
    rw [Finset.prod_ne_zero_iff]
    intro l hl
    exact pow_ne_zero _ (hlc (l + 1) (by rw [mem_range] at hl; omega))
  have hprodR : (∏ l ∈ range (k + 1),
        ((-1 : R[X]) ^ (((F l).natDegree - ((F (k + 1 + 1)).natDegree - 1))
              * ((F (l + 1)).natDegree - ((F (k + 1 + 1)).natDegree - 1)))
          * C ((F (l + 1)).coeff (F (l + 1)).natDegree) ^ ((F l).natDegree - (F (l + 2)).natDegree)
          * C (β l ^ ((F (l + 1)).natDegree - ((F (k + 1 + 1)).natDegree - 1)))))
      = ∏ l ∈ range (k + 1),
          ((C ((F (l + 1)).coeff (F (l + 1)).natDegree)) ^ 2 * C (β l ^ (k + 1 - l + 1))) := by
    refine prod_congr rfl (fun l hl => ?_)
    rw [hSgn l hl, hG l hl, hE l hl, one_mul]
  rw [hend, neg_one_sq, one_mul, hprodR] at hclosed
  have hBprod : (∏ l ∈ range (k + 1),
        ((C ((F (l + 1)).coeff (F (l + 1)).natDegree)) ^ 2 * C (β l ^ (k + 1 - l + 1))))
      = C (∏ l ∈ range (k + 1),
          (((F (l + 1)).coeff (F (l + 1)).natDegree) ^ 2 * β l ^ (k + 1 - l + 1))) := by
    rw [map_prod]
    refine prod_congr rfl (fun l hl => ?_)
    simp only [map_mul, map_pow]
  rw [hBprod] at hclosed
  rw [show (C (((F (k + 1 + 1)).coeff (F (k + 1 + 1)).natDegree) ^ 2)
        * (C (β (k + 1)) * F (k + 1 + 2)))
        * C (∏ l ∈ range (k + 1),
            (((F (l + 1)).coeff (F (l + 1)).natDegree) ^ 2 * β l ^ (k + 1 - l + 1)))
      = F (k + 1 + 2) * (C (((F (k + 1 + 1)).coeff (F (k + 1 + 1)).natDegree) ^ 2)
        * (C (β (k + 1)) * C (∏ l ∈ range (k + 1),
            (((F (l + 1)).coeff (F (l + 1)).natDegree) ^ 2 * β l ^ (k + 1 - l + 1)))))
      from by ring, ← map_mul, ← map_mul, hScal] at hclosed
  exact mul_right_cancel₀ hSLne hclosed

section DefectiveCollapse

open Finset

variable {M : Type*} [CommMonoid M]

/-- Index shift: a product over `range m` of `c (l+1) ^ (f l)` reindexes to `Ico 1 (m+1)` over
`c k ^ (f (k-1))`. -/
theorem shift_prod (c : ℕ → M) (f : ℕ → ℕ) (m : ℕ) :
    ∏ l ∈ range m, (c (l + 1)) ^ (f l) = ∏ k ∈ Ico 1 (m + 1), (c k) ^ (f (k - 1)) := by
  rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel]
  refine prod_congr rfl (fun l _ => ?_)
  rw [show (1 : ℕ) + l - 1 = l from by omega, Nat.add_comm 1 l]

/-- The `β`-endpoint fold (Collins defective case): with `E m = 1` at the η-index, the separate endpoint
`c m ^ (δ_{m-1}+1)` (`= βₘ`) absorbs into the `β`-product, giving `∏_{k ∈ Ico 1 (m+1)} c k ^ ((δ_{k-1}+1)·E k)`
(the `l=0` term `β₀=1` drops). -/
theorem beta_fold (c : ℕ → M) (δ E : ℕ → ℕ) (m : ℕ) (hm : 1 ≤ m) (hEm : E m = 1) :
    (c m) ^ (δ (m - 1) + 1)
        * ∏ l ∈ range m, (if l = 0 then (1 : M) else (c l) ^ (δ (l - 1) + 1)) ^ (E l)
      = ∏ k ∈ Ico 1 (m + 1), (c k) ^ ((δ (k - 1) + 1) * E k) := by
  rw [Finset.prod_Ico_succ_top hm, hEm, mul_one, mul_comm]
  congr 1
  rw [Finset.range_eq_Ico, ← Finset.prod_Ico_consecutive _ (Nat.zero_le 1) hm]
  rw [show ∏ l ∈ Ico 0 1, (if l = 0 then (1 : M) else (c l) ^ (δ (l - 1) + 1)) ^ (E l) = 1 from by
        rw [← Finset.range_eq_Ico, Finset.prod_range_one]; simp, one_mul]
  refine prod_congr rfl (fun l hl => ?_)
  rw [Finset.mem_Ico] at hl
  rw [if_neg (by omega), ← pow_mul]

/-- **General-δ leading-coefficient collapse** — the combinatorial heart of Collins's Theorem 1(b) in the
*defective* case. With `E` decreasing by the gaps (`E k = E (k+1) + δ (k+1)`), gaps positive (`1 ≤ δ k`), and
`E m = 1` (the η-index), the `αₘ`-product on the left equals the `(βₘ · lc · β)`-product on the right times
exactly Collins's coefficient `∏ c (l+1) ^ (δ l · (δ_{l+1} − 1))` — i.e. `∏ cᵢ^(δᵢ₋₁(δᵢ−1))`. Every product
reindexes (`shift_prod`, `beta_fold`) to a common `∏_{k ∈ Ico 1 (m+1)}`, and one `prod_congr` discharges it
via the per-`k` identity `(δ_{k-1}+1)·E_{k-1} = (δ_{k-1}+1)·E_k + (δ_{k-1}+δ_k) + δ_{k-1}(δ_k−1)`. -/
theorem lc_collapse_defective (c : ℕ → M) (δ E : ℕ → ℕ) (m : ℕ) (hm : 1 ≤ m)
    (hE : ∀ k, E k = E (k + 1) + δ (k + 1)) (hδ : ∀ k, 1 ≤ δ k) (hEm : E m = 1) :
    ∏ l ∈ range m, (c (l + 1)) ^ ((δ l + 1) * E l)
      = (c m) ^ (δ (m - 1) + 1)
        * (∏ l ∈ range m, ((c (l + 1)) ^ (δ l + δ (l + 1))
            * (if l = 0 then (1 : M) else (c l) ^ (δ (l - 1) + 1)) ^ (E l)))
        * ∏ l ∈ range m, (c (l + 1)) ^ (δ l * (δ (l + 1) - 1)) := by
  rw [Finset.prod_mul_distrib]
  have hR :
      (c m) ^ (δ (m - 1) + 1)
        * ((∏ l ∈ range m, (c (l + 1)) ^ (δ l + δ (l + 1)))
            * ∏ l ∈ range m, (if l = 0 then (1 : M) else (c l) ^ (δ (l - 1) + 1)) ^ (E l))
        * ∏ l ∈ range m, (c (l + 1)) ^ (δ l * (δ (l + 1) - 1))
      = ((c m) ^ (δ (m - 1) + 1)
            * ∏ l ∈ range m, (if l = 0 then (1 : M) else (c l) ^ (δ (l - 1) + 1)) ^ (E l))
          * (∏ l ∈ range m, (c (l + 1)) ^ (δ l + δ (l + 1)))
          * ∏ l ∈ range m, (c (l + 1)) ^ (δ l * (δ (l + 1) - 1)) := by ac_rfl
  rw [hR, beta_fold c δ E m hm hEm, shift_prod c (fun l => δ l + δ (l + 1)) m,
    shift_prod c (fun l => δ l * (δ (l + 1) - 1)) m, shift_prod c (fun l => (δ l + 1) * E l) m,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine prod_congr rfl (fun k hk => ?_)
  rw [Finset.mem_Ico] at hk
  rw [← pow_add, ← pow_add]
  congr 1
  simp only [show (k - 1) + 1 = k from by omega]
  have hEk : E (k - 1) = E k + δ k := by
    have h := hE (k - 1); rwa [show k - 1 + 1 = k from by omega] at h
  have hb := hδ k
  rw [hEk]
  rcases hd : δ k with _ | p
  · omega
  · simp; ring

end DefectiveCollapse

section SubresPRSCoeff

variable {K : Type*} [Field K]

/-- The subresultant-PRS coefficient `γᵢ` (Bronstein §1.5, p.23): `γ₁ = -1` and
`γᵢ₊₁ = (-rᵢ)^δᵢ · γᵢ^(1-δᵢ)`, where `rᵢ = lc Rᵢ` and `δᵢ = deg Rᵢ₋₁ - deg Rᵢ`. The exponent `1-δᵢ`
is a (possibly negative) integer, so `γ` lives in the field of fractions. -/
noncomputable def subresPRS_gamma (r : ℕ → K) (δ : ℕ → ℕ) : ℕ → K
  | 0 => 1
  | 1 => -1
  | (i + 2) => (-(r (i + 1))) ^ (δ (i + 1))
      * (subresPRS_gamma r δ (i + 1)) ^ ((1 : ℤ) - (δ (i + 1) : ℤ))

/-- The subresultant-PRS coefficient `βᵢ` (Bronstein §1.5, p.23): `β₁ = (-1)^(δ₁+1)` and
`βᵢ₊₁ = -rᵢ · γᵢ₊₁^(δᵢ+1)`. -/
noncomputable def subresPRS_beta (r : ℕ → K) (δ : ℕ → ℕ) : ℕ → K
  | 0 => 1
  | 1 => (-1) ^ (δ 1 + 1)
  | (i + 2) => -(r (i + 1)) * (subresPRS_gamma r δ (i + 2)) ^ (δ (i + 1) + 1)

/-- The subresultant-PRS coefficients `γᵢ` are nonzero (so the `γᵢ^(1-δᵢ)` division is well-defined),
provided every `rᵢ = lc Rᵢ` is nonzero. -/
theorem subresPRS_gamma_ne_zero (r : ℕ → K) (δ : ℕ → ℕ) (hr : ∀ i, r i ≠ 0) :
    ∀ i, 1 ≤ i → subresPRS_gamma r δ i ≠ 0 := by
  intro i
  induction i with
  | zero => omega
  | succ n ih =>
    intro _
    match n, ih with
    | 0, _ => simp [subresPRS_gamma]
    | (k + 1), ih =>
      rw [subresPRS_gamma]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr (hr (k + 1))))
        (zpow_ne_zero _ (ih (by omega)))

end SubresPRSCoeff

/-- **Theorem 1.5.3 / Collins Theorem 1(c), defective (gap) vanishing**: for a PRS, the subresultant
`Sⱼ(F₀,F₁)` vanishes at every *defective* index strictly inside the last degree gap,
`deg F_{m+2} < j < deg F_{m+1} − 1`. Telescopes to step `m` (`subresultant_prs_vanish`) where the
single-step gap subresultant vanishes (`subresultant_prs_step_gap`, Brown–Traub eq 23). -/
theorem subresultant_prs_gap_zero [IsDomain R] (F : ℕ → R[X]) (α β : ℕ → R) (Q : ℕ → R[X]) (m j : ℕ)
    (hα : ∀ l ≤ m, α l ≠ 0) (hβ : ∀ l ≤ m, β l ≠ 0)
    (hcb : ∀ l ≤ m, (F (l + 2)).natDegree < (F (l + 1)).natDegree)
    (hj : ∀ l < m, j < (F (l + 2)).natDegree)
    (hQ : ∀ l ≤ m, (Q l).natDegree + (F (l + 1)).natDegree ≤ (F l).natDegree)
    (hrel : ∀ l ≤ m, C (α l) * F l = C (β l) * F (l + 2) + F (l + 1) * Q l)
    (hlo : (F (m + 2)).natDegree < j) (hhi : j < (F (m + 1)).natDegree - 1) :
    subresultant (F 0) (F 1) (F 0).natDegree (F 1).natDegree j = 0 := by
  apply subresultant_prs_vanish F α β Q j m (fun l hl => hα l (by omega))
    (fun l hl => hβ l (by omega)) (fun l hl => hcb l (by omega)) hj
    (fun l hl => hQ l (by omega)) (fun l hl => hrel l (by omega))
  exact subresultant_prs_step_gap (F m) (F (m + 1)) (F (m + 2)) (Q m) (α m) (β m)
    (F m).natDegree (F (m + 1)).natDegree (F (m + 2)).natDegree j (hα m le_rfl) (hβ m le_rfl)
    hlo hhi rfl le_rfl (hQ m le_rfl) (hrel m le_rfl)

end DeepWiki.SymbolicIntegration
