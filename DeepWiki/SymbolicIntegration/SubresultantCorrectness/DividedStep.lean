import DeepWiki.SymbolicIntegration.SubresultantCorrectness.LrtOperands

/-! # β-divided subresultant PRS steps
Exact `ℚ[t]` scalar division for `BPoly`, the β-divided pseudo-remainder step,
and its one-step subresultant similarity bridge. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### `bdivC` realizes exact `ℚ[t]`-division -/

/-- If every `x`-coefficient of `p` divides exactly by `c`, then
`C(toPoly c) · toBPoly (p.map (cdiv fuel · c)) = toBPoly p`. -/
theorem toBPoly_map_cdiv_exact (fuel : ℕ) (p : BPoly) (c : CPoly ℚ) (hc : cnorm c ≠ [])
    (hrem : ∀ a ∈ p, toPoly (cmod fuel a c) = 0) :
    Polynomial.C (toPoly c) * toBPoly (p.map (fun a => cdiv fuel a c)) = toBPoly p := by
  induction p with
  | nil => simp
  | cons a as ih =>
    have has := ih (fun b hb => hrem b (by simp [hb]))
    have ha : toPoly a = toPoly (cdiv fuel a c) * toPoly c :=
      toPoly_cdiv_of_cmod_zero fuel a c hc (hrem a (by simp))
    rw [List.map_cons, toBPoly_cons, toBPoly_cons]
    rw [ha, map_mul]
    linear_combination Polynomial.X * has

/-- `C(toPoly c) · toBPoly (bdivC fuel p c) = toBPoly p` when every `x`-coefficient of `p` divides
exactly by `c`: `bdivC` is exact scalar `ℚ[t]`-division. -/
theorem toBPoly_bdivC_exact (fuel : ℕ) (p : BPoly) (c : CPoly ℚ) (hc : cnorm c ≠ [])
    (hrem : ∀ a ∈ p, toPoly (cmod fuel a c) = 0) :
    Polynomial.C (toPoly c) * toBPoly (bdivC fuel p c) = toBPoly p := by
  rw [bdivC, toBPoly_bnorm]
  exact toBPoly_map_cdiv_exact fuel p c hc hrem

/-- `bdivC` exact division from divisibility: if `toPoly c ∣ toPoly a` for every `x`-coefficient `a`,
then `C(toPoly c) · toBPoly (bdivC fuel p c) = toBPoly p`. -/
theorem toBPoly_bdivC_exact_of_dvd (fuel : ℕ) (p : BPoly) (c : CPoly ℚ) (hc : cnorm c ≠ [])
    (hfuel : ∀ a ∈ p, (cnorm a).length ≤ fuel) (hdvd : ∀ a ∈ p, toPoly c ∣ toPoly a) :
    Polynomial.C (toPoly c) * toBPoly (bdivC fuel p c) = toBPoly p :=
  toBPoly_bdivC_exact fuel p c hc
    (fun a ha => cmod_eq_zero_of_dvd fuel a c hc (hfuel a ha) (hdvd a ha))

/-- `C(toPoly g) · toBPoly (bprimitivePartX fuel p) = toBPoly p` with `g = bcontentX fuel p` nonzero
and dividing each `x`-coefficient exactly: `bprimitivePartX` strips a `ℚ[t]` content factor. -/
theorem toBPoly_bprimitivePartX_exact (fuel : ℕ) (p : BPoly)
    (hg : ¬ cisZero (bcontentX fuel p) = true) (hgcn : cnorm (bcontentX fuel p) ≠ [])
    (hrem : ∀ a ∈ bnorm p, toPoly (cmod fuel a (bcontentX fuel p)) = 0) :
    Polynomial.C (toPoly (bcontentX fuel p)) * toBPoly (bprimitivePartX fuel p) = toBPoly p := by
  have hbc : bcontentX fuel (bnorm p) = bcontentX fuel p := by
    rw [bcontentX, bcontentX, bnorm_idem]
  rw [bprimitivePartX]
  simp only [hbc, hg, Bool.false_eq_true, if_false]
  rw [toBPoly_bnorm, toBPoly_map_cdiv_exact fuel (bnorm p) (bcontentX fuel p) hgcn hrem,
    toBPoly_bnorm]

/-! ### One subresultant-PRS step on the β-divided remainder -/

/-- A pseudo-division step whose β-division of the remainder is exact. -/
structure IsBdivCExactStep (fuel : ℕ) (p q : BPoly) (β : CPoly ℚ) (s : BPoly) (c : CPoly ℚ) : Prop where
  /-- The pseudo-division relation before β-division. -/
  relation : Polynomial.C (toPoly c) * toBPoly p
    = toBPoly s * toBPoly q + toBPoly (bpsremainder fuel p q)
  /-- The β divisor is nonzero after normalization. -/
  beta_cnorm_ne : cnorm β ≠ []
  /-- β divides every coefficient of the pseudo-remainder exactly. -/
  exact_division : ∀ a ∈ bpsremainder fuel p q, toPoly (cmod fuel a β) = 0

/-- One subresultant-PRS step on the β-divided remainder `r = bdivC fuel (bpsremainder fuel p q) β`:
`C((toPoly c)^(m−j)) · Sⱼ(A,B; n,m) = (-1)^((m−j)(n−j)) · C((toPoly β)^(m−j)) · Sⱼ(B, toBPoly r; m,n)`. -/
theorem subresultant_C_mul_eq_bdivC_of_bpsremainder (fuel : ℕ) (p q : BPoly) (β : CPoly ℚ) (n m j : ℕ)
    (s : BPoly) (c : CPoly ℚ)
    (hstep : IsBdivCExactStep fuel p q β s c)
    (hjm : j ≤ m) (hjn : j < n)
    (hB : (toBPoly q).natDegree ≤ m)
    (hQ : (toBPoly s).natDegree + m ≤ n) :
    Polynomial.C ((toPoly c) ^ (m - j)) * subresultant (toBPoly p) (toBPoly q) n m j
      = (-1 : (ℚ[X])[X]) ^ ((m - j) * (n - j))
        * (Polynomial.C ((toPoly β) ^ (m - j))
          * subresultant (toBPoly q) (toBPoly (bdivC fuel (bpsremainder fuel p q) β)) m n j) := by
  have hremStep := subresultant_C_mul_eq_rem_of_bpsremainder fuel p q n m j s c
    hstep.relation hjm hjn hB hQ
  have hexact : toBPoly (bpsremainder fuel p q)
      = Polynomial.C (toPoly β) * toBPoly (bdivC fuel (bpsremainder fuel p q) β) :=
    (toBPoly_bdivC_exact fuel (bpsremainder fuel p q) β hstep.beta_cnorm_ne hstep.exact_division).symm
  rw [hremStep, hexact,
    subresultant_C_mul_right (toPoly β) (toBPoly q)
      (toBPoly (bdivC fuel (bpsremainder fuel p q) β)) m n j (le_of_lt hjn) hjm]

/-- LRT subresultant after one β-divided PRS step (next element `R₃ = bdivC fuel (bpsremainder fuel P Q) β`):
`C((toPoly c)^(m−j)) · lrtSubresultant A D j = (-1)^((m−j)(n−j)) · C((toPoly β)^(m−j)) · Sⱼ(Q, R₃; m,n)`. -/
theorem lrtSubresultant_C_mul_eq_bdivC_of_bpsremainder (fuel : ℕ) (A D : CPoly ℚ) (β : CPoly ℚ) (j : ℕ)
    (s : BPoly) (c : CPoly ℚ)
    (hstep : IsBdivCExactStep fuel (liftCtoBPoly D) (bArgAmtD' A D) β s c)
    (hjm : j ≤ (toPoly D).natDegree - 1) (hjn : j < (toPoly D).natDegree)
    (hB : (toBPoly (bArgAmtD' A D)).natDegree ≤ (toPoly D).natDegree - 1)
    (hQ : (toBPoly s).natDegree + ((toPoly D).natDegree - 1) ≤ (toPoly D).natDegree) :
    Polynomial.C ((toPoly c) ^ (((toPoly D).natDegree - 1) - j))
        * lrtSubresultant (toPoly A) (toPoly D) j
      = (-1 : (ℚ[X])[X]) ^ ((((toPoly D).natDegree - 1) - j) * ((toPoly D).natDegree - j))
        * (Polynomial.C ((toPoly β) ^ (((toPoly D).natDegree - 1) - j))
          * subresultant (toBPoly (bArgAmtD' A D))
              (toBPoly (bdivC fuel (bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D)) β))
              ((toPoly D).natDegree - 1) (toPoly D).natDegree j) := by
  rw [lrtSubresultant_eq_subresultant_toBPoly]
  exact subresultant_C_mul_eq_bdivC_of_bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D) β
    (toPoly D).natDegree ((toPoly D).natDegree - 1) j s c hstep hjm hjn hB hQ

/-! ### The one-step PRS reduction as a `ℚ[t]`-similarity -/

/-- One divided PRS step as a `ℚ[t]`-similarity: with content factors nonzero,
`IsSimilar (lrtSubresultant A D j) (Sⱼ(Q, bdivC … prem; m, n))`. -/
theorem isSimilar_lrtSubresultant_subresultant_bdivC (fuel : ℕ) (A D : CPoly ℚ) (β : CPoly ℚ) (j : ℕ)
    (s : BPoly) (c : CPoly ℚ)
    (hstep : IsBdivCExactStep fuel (liftCtoBPoly D) (bArgAmtD' A D) β s c)
    (hc0 : toPoly c ≠ 0) (hβ0 : toPoly β ≠ 0)
    (hjm : j ≤ (toPoly D).natDegree - 1) (hjn : j < (toPoly D).natDegree)
    (hB : (toBPoly (bArgAmtD' A D)).natDegree ≤ (toPoly D).natDegree - 1)
    (hQ : (toBPoly s).natDegree + ((toPoly D).natDegree - 1) ≤ (toPoly D).natDegree) :
    IsSimilar (lrtSubresultant (toPoly A) (toPoly D) j)
      (subresultant (toBPoly (bArgAmtD' A D))
        (toBPoly (bdivC fuel (bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D)) β))
        ((toPoly D).natDegree - 1) (toPoly D).natDegree j) := by
  refine ⟨(toPoly c) ^ (((toPoly D).natDegree - 1) - j),
    (-1 : ℚ[X]) ^ ((((toPoly D).natDegree - 1) - j) * ((toPoly D).natDegree - j))
      * (toPoly β) ^ (((toPoly D).natDegree - 1) - j),
    pow_ne_zero _ hc0,
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hβ0), ?_⟩
  rw [lrtSubresultant_C_mul_eq_bdivC_of_bpsremainder fuel A D β j s c hstep hjm hjn hB hQ]
  simp only [Polynomial.C_mul, map_pow, map_neg, map_one]
  ring

/-! ### Telescoping the divided one-step similarity along the whole `subresPRS` -/

/-- Generic divided one-step similarity over arbitrary `BPoly`s: with `r = bdivC fuel (bpsremainder fuel
p q) β`, `IsSimilar (Sⱼ(toBPoly p, toBPoly q; n, m)) (Sⱼ(toBPoly q, toBPoly r; m, n))`. -/
theorem isSimilar_subresultant_bdivC_step (fuel : ℕ) (p q : BPoly) (β : CPoly ℚ) (n m j : ℕ)
    (s : BPoly) (c : CPoly ℚ)
    (hstep : IsBdivCExactStep fuel p q β s c)
    (hc0 : toPoly c ≠ 0) (hβ0 : toPoly β ≠ 0)
    (hjm : j ≤ m) (hjn : j < n)
    (hB : (toBPoly q).natDegree ≤ m)
    (hQ : (toBPoly s).natDegree + m ≤ n) :
    IsSimilar (subresultant (toBPoly p) (toBPoly q) n m j)
      (subresultant (toBPoly q) (toBPoly (bdivC fuel (bpsremainder fuel p q) β)) m n j) := by
  refine ⟨(toPoly c) ^ (m - j),
    (-1 : ℚ[X]) ^ ((m - j) * (n - j)) * (toPoly β) ^ (m - j),
    pow_ne_zero _ hc0,
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hβ0), ?_⟩
  rw [subresultant_C_mul_eq_bdivC_of_bpsremainder fuel p q β n m j s c hstep hjm hjn hB hQ]
  simp only [Polynomial.C_mul, map_pow, map_neg, map_one]
  ring

/-- The combined per-step PRS relation through `toBPoly`:
`C(toPoly c)·toBPoly p = C(toPoly β)·toBPoly r + toBPoly q·toBPoly s` with `r = bdivC fuel (prem p q) β`. -/
theorem toBPoly_prs_rel (fuel : ℕ) (p q : BPoly) (β : CPoly ℚ) (s : BPoly) (c : CPoly ℚ)
    (hstep : IsBdivCExactStep fuel p q β s c) :
    Polynomial.C (toPoly c) * toBPoly p
      = Polynomial.C (toPoly β) * toBPoly (bdivC fuel (bpsremainder fuel p q) β)
        + toBPoly q * toBPoly s := by
  rw [hstep.relation,
    toBPoly_bdivC_exact fuel (bpsremainder fuel p q) β hstep.beta_cnorm_ne hstep.exact_division]
  ring

end DeepWiki.SymbolicIntegration.Compute
