import DeepWiki.SymbolicIntegration.SubresultantCorrectness.LrtOperands

/-! # β-divided subresultant PRS steps
Exact `ℚ[t]` scalar division for `GBPolyCore ℚ`, the β-divided pseudo-remainder step,
and its one-step subresultant similarity bridge. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### `bdivC` realizes exact `ℚ[t]`-division -/

/-- If every `x`-coefficient of `p` divides exactly by `c`, then
`C(toPoly c) · GBPolyCore.toGBCoeffPoly (p.map (DensePoly.cdivWf · c)) = GBPolyCore.toGBCoeffPoly p`. -/
theorem toBPoly_map_cdiv_exact (p : GBPolyCore ℚ) (c : DensePoly ℚ) (hc : cnorm c ≠ [])
    (hrem : ∀ a ∈ p, toPoly (DensePoly.cmodWf a c) = 0) :
    Polynomial.C (toPoly c) * GBPolyCore.toGBCoeffPoly (p.map (fun a => DensePoly.cdivWf a c)) = GBPolyCore.toGBCoeffPoly p := by
  induction p with
  | nil => simp
  | cons a as ih =>
    have has := ih (fun b hb => hrem b (by simp [hb]))
    have hrem' : DensePoly.toPoly (DensePoly.cmodWf a c) = 0 := by
      simpa only [toPoly_eq_dense] using hrem a (by simp)
    have ha' := DensePoly.toPolyG_cmodWf a c hc
    rw [hrem', add_zero] at ha'
    have ha : toPoly a = toPoly (DensePoly.cdivWf a c) * toPoly c := by
      simpa only [toPoly_eq_dense] using ha'
    rw [List.map_cons, GBPolyCore.toGBCoeffPoly_cons, GBPolyCore.toGBCoeffPoly_cons]
    change Polynomial.C (toPoly c) * (Polynomial.C (toPoly (DensePoly.cdivWf a c)) + _)
      = Polynomial.C (toPoly a) + _
    rw [ha, map_mul]
    linear_combination Polynomial.X * has

/-- `C(toPoly c) · GBPolyCore.toGBCoeffPoly (bdivC p c) = GBPolyCore.toGBCoeffPoly p` when every `x`-coefficient of `p` divides
exactly by `c`: `bdivC` is exact scalar `ℚ[t]`-division. -/
theorem toBPoly_bdivC_exact (p : GBPolyCore ℚ) (c : DensePoly ℚ) (hc : cnorm c ≠ [])
    (hrem : ∀ a ∈ p, toPoly (DensePoly.cmodWf a c) = 0) :
    Polynomial.C (toPoly c) * GBPolyCore.toGBCoeffPoly (bdivC p c) = GBPolyCore.toGBCoeffPoly p := by
  rw [bdivC, GBPolyCore.toGBCoeffPoly_gbnormCore]
  exact toBPoly_map_cdiv_exact p c hc hrem

/-- `bdivC` exact division from divisibility: if `toPoly c ∣ toPoly a` for every `x`-coefficient `a`,
then `C(toPoly c) · GBPolyCore.toGBCoeffPoly (bdivC p c) = GBPolyCore.toGBCoeffPoly p`. -/
theorem toBPoly_bdivC_exact_of_dvd (p : GBPolyCore ℚ) (c : DensePoly ℚ) (hc : cnorm c ≠ [])
    (hdvd : ∀ a ∈ p, toPoly c ∣ toPoly a) :
    Polynomial.C (toPoly c) * GBPolyCore.toGBCoeffPoly (bdivC p c) = GBPolyCore.toGBCoeffPoly p :=
  toBPoly_bdivC_exact p c hc
    (fun a ha => by
      have hdvd' : DensePoly.toPoly c ∣ DensePoly.toPoly a := by
        simpa only [toPoly_eq_dense] using hdvd a ha
      simpa only [toPoly_eq_dense] using
        DensePoly.toPolyG_cmodWf_eq_zero_of_dvd a c hc hdvd')

/-- `C(toPoly g) · GBPolyCore.toGBCoeffPoly (bprimitivePartX p) = GBPolyCore.toGBCoeffPoly p` with `g = bcontentX p` nonzero
and dividing each `x`-coefficient exactly: `bprimitivePartX` strips a `ℚ[t]` content factor. -/
theorem toBPoly_bprimitivePartX_exact (p : GBPolyCore ℚ)
    (hg : ¬ cisZero (bcontentX p) = true) (hgcn : cnorm (bcontentX p) ≠ [])
    (hrem : ∀ a ∈ GBPolyCore.gbnormCore p, toPoly (DensePoly.cmodWf a (bcontentX p)) = 0) :
    Polynomial.C (toPoly (bcontentX p)) * GBPolyCore.toGBCoeffPoly (bprimitivePartX p) = GBPolyCore.toGBCoeffPoly p := by
  have hbc : bcontentX (GBPolyCore.gbnormCore p) = bcontentX p := by
    rw [bcontentX, bcontentX, GBPolyCore.gbnormCore_idemp]
  rw [bprimitivePartX]
  simp only [hbc, hg, Bool.false_eq_true, if_false]
  rw [GBPolyCore.toGBCoeffPoly_gbnormCore, toBPoly_map_cdiv_exact (GBPolyCore.gbnormCore p) (bcontentX p) hgcn hrem,
    GBPolyCore.toGBCoeffPoly_gbnormCore]

/-! ### One subresultant-PRS step on the β-divided remainder -/

/-- A pseudo-division step whose β-division of the remainder is exact. -/
structure IsBdivCExactStep (fuel : ℕ) (p q : GBPolyCore ℚ) (β : DensePoly ℚ) (s : GBPolyCore ℚ) (c : DensePoly ℚ) : Prop where
  /-- The pseudo-division relation before β-division. -/
  relation : Polynomial.C (toPoly c) * GBPolyCore.toGBCoeffPoly p
    = GBPolyCore.toGBCoeffPoly s * GBPolyCore.toGBCoeffPoly q + GBPolyCore.toGBCoeffPoly (GBPolyCore.gbpsremainderCore fuel p q)
  /-- The β divisor is nonzero after normalization. -/
  beta_cnorm_ne : cnorm β ≠ []
  /-- β divides every coefficient of the pseudo-remainder exactly. -/
  exact_division : ∀ a ∈ GBPolyCore.gbpsremainderCore fuel p q, toPoly (DensePoly.cmodWf a β) = 0

/-- One subresultant-PRS step on the β-divided remainder `r = bdivC (GBPolyCore.gbpsremainderCore fuel p q) β`:
`C((toPoly c)^(m−j)) · Sⱼ(A,B; n,m) = (-1)^((m−j)(n−j)) · C((toPoly β)^(m−j)) · Sⱼ(B, GBPolyCore.toGBCoeffPoly r; m,n)`. -/
theorem subresultant_C_mul_eq_bdivC_of_bpsremainder (fuel : ℕ) (p q : GBPolyCore ℚ) (β : DensePoly ℚ) (n m j : ℕ)
    (s : GBPolyCore ℚ) (c : DensePoly ℚ)
    (hstep : IsBdivCExactStep fuel p q β s c)
    (hjm : j ≤ m) (hjn : j < n)
    (hB : (GBPolyCore.toGBCoeffPoly q).natDegree ≤ m)
    (hQ : (GBPolyCore.toGBCoeffPoly s).natDegree + m ≤ n) :
    Polynomial.C ((toPoly c) ^ (m - j)) * subresultant (GBPolyCore.toGBCoeffPoly p) (GBPolyCore.toGBCoeffPoly q) n m j
      = (-1 : (ℚ[X])[X]) ^ ((m - j) * (n - j))
        * (Polynomial.C ((toPoly β) ^ (m - j))
          * subresultant (GBPolyCore.toGBCoeffPoly q) (GBPolyCore.toGBCoeffPoly (bdivC (GBPolyCore.gbpsremainderCore fuel p q) β)) m n j) := by
  have hremStep := subresultant_C_mul_eq_rem_of_bpsremainder fuel p q n m j s c
    hstep.relation hjm hjn hB hQ
  have hexact : GBPolyCore.toGBCoeffPoly (GBPolyCore.gbpsremainderCore fuel p q)
      = Polynomial.C (toPoly β) * GBPolyCore.toGBCoeffPoly (bdivC (GBPolyCore.gbpsremainderCore fuel p q) β) :=
    (toBPoly_bdivC_exact (GBPolyCore.gbpsremainderCore fuel p q) β hstep.beta_cnorm_ne hstep.exact_division).symm
  rw [hremStep, hexact,
    subresultant_C_mul_right (toPoly β) (GBPolyCore.toGBCoeffPoly q)
      (GBPolyCore.toGBCoeffPoly (bdivC (GBPolyCore.gbpsremainderCore fuel p q) β)) m n j (le_of_lt hjn) hjm]

/-- LRT subresultant after one β-divided PRS step (next element `R₃ = bdivC (GBPolyCore.gbpsremainderCore fuel P Q) β`):
`C((toPoly c)^(m−j)) · lrtSubresultant A D j = (-1)^((m−j)(n−j)) · C((toPoly β)^(m−j)) · Sⱼ(Q, R₃; m,n)`. -/
theorem lrtSubresultant_C_mul_eq_bdivC_of_bpsremainder (fuel : ℕ) (A D : DensePoly ℚ) (β : DensePoly ℚ) (j : ℕ)
    (s : GBPolyCore ℚ) (c : DensePoly ℚ)
    (hstep : IsBdivCExactStep fuel (liftCtoBPoly D) (bArgAmtD' A D) β s c)
    (hjm : j ≤ (toPoly D).natDegree - 1) (hjn : j < (toPoly D).natDegree)
    (hB : (GBPolyCore.toGBCoeffPoly (bArgAmtD' A D)).natDegree ≤ (toPoly D).natDegree - 1)
    (hQ : (GBPolyCore.toGBCoeffPoly s).natDegree + ((toPoly D).natDegree - 1) ≤ (toPoly D).natDegree) :
    Polynomial.C ((toPoly c) ^ (((toPoly D).natDegree - 1) - j))
        * lrtSubresultant (toPoly A) (toPoly D) j
      = (-1 : (ℚ[X])[X]) ^ ((((toPoly D).natDegree - 1) - j) * ((toPoly D).natDegree - j))
        * (Polynomial.C ((toPoly β) ^ (((toPoly D).natDegree - 1) - j))
          * subresultant (GBPolyCore.toGBCoeffPoly (bArgAmtD' A D))
              (GBPolyCore.toGBCoeffPoly (bdivC (GBPolyCore.gbpsremainderCore fuel (liftCtoBPoly D) (bArgAmtD' A D)) β))
              ((toPoly D).natDegree - 1) (toPoly D).natDegree j) := by
  rw [lrtSubresultant_eq_subresultant_toBPoly]
  exact subresultant_C_mul_eq_bdivC_of_bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D) β
    (toPoly D).natDegree ((toPoly D).natDegree - 1) j s c hstep hjm hjn hB hQ

/-! ### The one-step PRS reduction as a `ℚ[t]`-similarity -/

/-- One divided PRS step as a `ℚ[t]`-similarity: with content factors nonzero,
`IsSimilar (lrtSubresultant A D j) (Sⱼ(Q, bdivC … prem; m, n))`. -/
theorem isSimilar_lrtSubresultant_subresultant_bdivC (fuel : ℕ) (A D : DensePoly ℚ) (β : DensePoly ℚ) (j : ℕ)
    (s : GBPolyCore ℚ) (c : DensePoly ℚ)
    (hstep : IsBdivCExactStep fuel (liftCtoBPoly D) (bArgAmtD' A D) β s c)
    (hc0 : toPoly c ≠ 0) (hβ0 : toPoly β ≠ 0)
    (hjm : j ≤ (toPoly D).natDegree - 1) (hjn : j < (toPoly D).natDegree)
    (hB : (GBPolyCore.toGBCoeffPoly (bArgAmtD' A D)).natDegree ≤ (toPoly D).natDegree - 1)
    (hQ : (GBPolyCore.toGBCoeffPoly s).natDegree + ((toPoly D).natDegree - 1) ≤ (toPoly D).natDegree) :
    IsSimilar (lrtSubresultant (toPoly A) (toPoly D) j)
      (subresultant (GBPolyCore.toGBCoeffPoly (bArgAmtD' A D))
        (GBPolyCore.toGBCoeffPoly (bdivC (GBPolyCore.gbpsremainderCore fuel (liftCtoBPoly D) (bArgAmtD' A D)) β))
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

/-- Generic divided one-step similarity over arbitrary `GBPolyCore ℚ`s: with `r = bdivC (GBPolyCore.gbpsremainderCore fuel
p q) β`, `IsSimilar (Sⱼ(GBPolyCore.toGBCoeffPoly p, GBPolyCore.toGBCoeffPoly q; n, m)) (Sⱼ(GBPolyCore.toGBCoeffPoly q, GBPolyCore.toGBCoeffPoly r; m, n))`. -/
theorem isSimilar_subresultant_bdivC_step (fuel : ℕ) (p q : GBPolyCore ℚ) (β : DensePoly ℚ) (n m j : ℕ)
    (s : GBPolyCore ℚ) (c : DensePoly ℚ)
    (hstep : IsBdivCExactStep fuel p q β s c)
    (hc0 : toPoly c ≠ 0) (hβ0 : toPoly β ≠ 0)
    (hjm : j ≤ m) (hjn : j < n)
    (hB : (GBPolyCore.toGBCoeffPoly q).natDegree ≤ m)
    (hQ : (GBPolyCore.toGBCoeffPoly s).natDegree + m ≤ n) :
    IsSimilar (subresultant (GBPolyCore.toGBCoeffPoly p) (GBPolyCore.toGBCoeffPoly q) n m j)
      (subresultant (GBPolyCore.toGBCoeffPoly q) (GBPolyCore.toGBCoeffPoly (bdivC (GBPolyCore.gbpsremainderCore fuel p q) β)) m n j) := by
  refine ⟨(toPoly c) ^ (m - j),
    (-1 : ℚ[X]) ^ ((m - j) * (n - j)) * (toPoly β) ^ (m - j),
    pow_ne_zero _ hc0,
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hβ0), ?_⟩
  rw [subresultant_C_mul_eq_bdivC_of_bpsremainder fuel p q β n m j s c hstep hjm hjn hB hQ]
  simp only [Polynomial.C_mul, map_pow, map_neg, map_one]
  ring

/-- The combined per-step PRS relation through `GBPolyCore.toGBCoeffPoly`:
`C(toPoly c)·GBPolyCore.toGBCoeffPoly p = C(toPoly β)·GBPolyCore.toGBCoeffPoly r + GBPolyCore.toGBCoeffPoly q·GBPolyCore.toGBCoeffPoly s` with `r = bdivC (prem p q) β`. -/
theorem toBPoly_prs_rel (fuel : ℕ) (p q : GBPolyCore ℚ) (β : DensePoly ℚ) (s : GBPolyCore ℚ) (c : DensePoly ℚ)
    (hstep : IsBdivCExactStep fuel p q β s c) :
    Polynomial.C (toPoly c) * GBPolyCore.toGBCoeffPoly p
      = Polynomial.C (toPoly β) * GBPolyCore.toGBCoeffPoly (bdivC (GBPolyCore.gbpsremainderCore fuel p q) β)
        + GBPolyCore.toGBCoeffPoly q * GBPolyCore.toGBCoeffPoly s := by
  rw [hstep.relation,
    toBPoly_bdivC_exact (GBPolyCore.gbpsremainderCore fuel p q) β hstep.beta_cnorm_ne hstep.exact_division]
  ring

end DeepWiki.SymbolicIntegration.Compute
