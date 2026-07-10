import DeepWiki.SymbolicIntegration.SubresultantCorrectness.LrtOperands

/-! # β-divided subresultant PRS steps
Exact `ℚ[t]` scalar division for `GBPolyCore ℚ`, the β-divided pseudo-remainder step,
and its one-step subresultant similarity bridge. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### `bdivC` realizes exact `ℚ[t]`-division -/

/-- If every `x`-coefficient of `p` divides exactly by `c`, then
`C(toPoly c) · DensePoly.toPoly (p.map (DensePoly.cdivWf · c)) = DensePoly.toPoly p`. -/
theorem toBPoly_map_cdiv_exact (p : GBPolyCore ℚ) (c : DensePoly ℚ) (hc : cnorm c ≠ [])
    (hrem : ∀ a ∈ p, toPoly (DensePoly.cmodWf a c) = 0) :
    Polynomial.C (toPoly c) * DensePoly.toPoly (p.map (fun a => DensePoly.cdivWf a c)) = DensePoly.toPoly p := by
  apply GBPolyCore.toPolyG_map_cdivWf_exact p c hc
  intro a ha
  have hdiv := DensePoly.toPolyG_cmodWf a c hc
  have hrem' : DensePoly.toPoly (DensePoly.cmodWf a c) = 0 := by
    exact hrem a ha
  rw [hrem', add_zero] at hdiv
  refine ⟨DensePoly.toPoly (DensePoly.cdivWf a c), ?_⟩
  simpa only [mul_comm] using hdiv

/-- `C(toPoly c) · DensePoly.toPoly (bdivC p c) = DensePoly.toPoly p` when every `x`-coefficient of `p` divides
exactly by `c`: `bdivC` is exact scalar `ℚ[t]`-division. -/
theorem toBPoly_bdivC_exact (p : GBPolyCore ℚ) (c : DensePoly ℚ) (hc : cnorm c ≠ [])
    (hrem : ∀ a ∈ p, toPoly (DensePoly.cmodWf a c) = 0) :
    Polynomial.C (toPoly c) * DensePoly.toPoly (bdivC p c) = DensePoly.toPoly p := by
  rw [bdivC, GBPolyCore.toPolyG_gbnormCore]
  exact toBPoly_map_cdiv_exact p c hc hrem

/-- `bdivC` exact division from divisibility: if `toPoly c ∣ toPoly a` for every `x`-coefficient `a`,
then `C(toPoly c) · DensePoly.toPoly (bdivC p c) = DensePoly.toPoly p`. -/
theorem toBPoly_bdivC_exact_of_dvd (p : GBPolyCore ℚ) (c : DensePoly ℚ) (hc : cnorm c ≠ [])
    (hdvd : ∀ a ∈ p, toPoly c ∣ toPoly a) :
    Polynomial.C (toPoly c) * DensePoly.toPoly (bdivC p c) = DensePoly.toPoly p :=
  toBPoly_bdivC_exact p c hc
    (fun a ha => by
      have hdvd' : DensePoly.toPoly c ∣ DensePoly.toPoly a := by
        exact hdvd a ha
      exact
        DensePoly.toPolyG_cmodWf_eq_zero_of_dvd a c hc hdvd')

/-- The `cgcdWfGcd` primitive part preserves denotation when content division is exact. -/
theorem toPolyG_gbprimitivePartCore_cgcdWfGcd_exact (p : GBPolyCore ℚ)
    (hg : ¬ cisZero (GBPolyCore.gbcontentCore DensePoly.cgcdWfGcd p) = true)
    (hgcn : cnorm (GBPolyCore.gbcontentCore DensePoly.cgcdWfGcd p) ≠ [])
    (hrem : ∀ a ∈ GBPolyCore.gbnormCore p,
      toPoly (DensePoly.cmodWf a (GBPolyCore.gbcontentCore DensePoly.cgcdWfGcd p)) = 0) :
    Polynomial.C (toPoly (GBPolyCore.gbcontentCore DensePoly.cgcdWfGcd p))
        * DensePoly.toPoly
          (GBPolyCore.gbprimitivePartCore DensePoly.cgcdWfGcd p)
      = DensePoly.toPoly p := by
  rw [GBPolyCore.gbprimitivePartCore]
  simp only [GBPolyCore.gbcontentCore_gbnormCore, hg, Bool.false_eq_true, if_false]
  rw [GBPolyCore.toPolyG_gbnormCore,
    toBPoly_map_cdiv_exact (GBPolyCore.gbnormCore p)
      (GBPolyCore.gbcontentCore DensePoly.cgcdWfGcd p) hgcn hrem,
    GBPolyCore.toPolyG_gbnormCore]

/-! ### One subresultant-PRS step on the β-divided remainder -/

/-- A pseudo-division step whose β-division of the remainder is exact. -/
structure IsBdivCExactStep (fuel : ℕ) (p q : GBPolyCore ℚ) (β : DensePoly ℚ) (s : GBPolyCore ℚ) (c : DensePoly ℚ) : Prop where
  /-- The pseudo-division relation before β-division. -/
  relation : Polynomial.C (toPoly c) * DensePoly.toPoly p
    = DensePoly.toPoly s * DensePoly.toPoly q + DensePoly.toPoly (GBPolyCore.gbpsremainderCore fuel p q)
  /-- The β divisor is nonzero after normalization. -/
  beta_cnorm_ne : cnorm β ≠ []
  /-- β divides every coefficient of the pseudo-remainder exactly. -/
  exact_division : ∀ a ∈ GBPolyCore.gbpsremainderCore fuel p q, toPoly (DensePoly.cmodWf a β) = 0

/-- One subresultant-PRS step on the β-divided remainder `r = bdivC (GBPolyCore.gbpsremainderCore fuel p q) β`:
`C((toPoly c)^(m−j)) · Sⱼ(A,B; n,m) = (-1)^((m−j)(n−j)) · C((toPoly β)^(m−j)) · Sⱼ(B, DensePoly.toPoly r; m,n)`. -/
theorem subresultant_C_mul_eq_bdivC_of_bpsremainder (fuel : ℕ) (p q : GBPolyCore ℚ) (β : DensePoly ℚ) (n m j : ℕ)
    (s : GBPolyCore ℚ) (c : DensePoly ℚ)
    (hstep : IsBdivCExactStep fuel p q β s c)
    (hjm : j ≤ m) (hjn : j < n)
    (hB : (DensePoly.toPoly q).natDegree ≤ m)
    (hQ : (DensePoly.toPoly s).natDegree + m ≤ n) :
    Polynomial.C ((toPoly c) ^ (m - j)) * subresultant (DensePoly.toPoly p) (DensePoly.toPoly q) n m j
      = (-1 : (ℚ[X])[X]) ^ ((m - j) * (n - j))
        * (Polynomial.C ((toPoly β) ^ (m - j))
          * subresultant (DensePoly.toPoly q) (DensePoly.toPoly (bdivC (GBPolyCore.gbpsremainderCore fuel p q) β)) m n j) := by
  have hremStep := subresultant_C_mul_eq_rem_of_bpsremainder fuel p q n m j s c
    hstep.relation hjm hjn hB hQ
  have hexact : DensePoly.toPoly (GBPolyCore.gbpsremainderCore fuel p q)
      = Polynomial.C (toPoly β) * DensePoly.toPoly (bdivC (GBPolyCore.gbpsremainderCore fuel p q) β) :=
    (toBPoly_bdivC_exact (GBPolyCore.gbpsremainderCore fuel p q) β hstep.beta_cnorm_ne hstep.exact_division).symm
  rw [hremStep, hexact,
    subresultant_C_mul_right (toPoly β) (DensePoly.toPoly q)
      (DensePoly.toPoly (bdivC (GBPolyCore.gbpsremainderCore fuel p q) β)) m n j (le_of_lt hjn) hjm]

/-- LRT subresultant after one β-divided PRS step (next element `R₃ = bdivC (GBPolyCore.gbpsremainderCore fuel P Q) β`):
`C((toPoly c)^(m−j)) · lrtSubresultant A D j = (-1)^((m−j)(n−j)) · C((toPoly β)^(m−j)) · Sⱼ(Q, R₃; m,n)`. -/
theorem lrtSubresultant_C_mul_eq_bdivC_of_bpsremainder (fuel : ℕ) (A D : DensePoly ℚ) (β : DensePoly ℚ) (j : ℕ)
    (s : GBPolyCore ℚ) (c : DensePoly ℚ)
    (hstep : IsBdivCExactStep fuel (liftCtoBPoly D) (bArgAmtD' A D) β s c)
    (hjm : j ≤ (toPoly D).natDegree - 1) (hjn : j < (toPoly D).natDegree)
    (hB : (DensePoly.toPoly (bArgAmtD' A D)).natDegree ≤ (toPoly D).natDegree - 1)
    (hQ : (DensePoly.toPoly s).natDegree + ((toPoly D).natDegree - 1) ≤ (toPoly D).natDegree) :
    Polynomial.C ((toPoly c) ^ (((toPoly D).natDegree - 1) - j))
        * lrtSubresultant (toPoly A) (toPoly D) j
      = (-1 : (ℚ[X])[X]) ^ ((((toPoly D).natDegree - 1) - j) * ((toPoly D).natDegree - j))
        * (Polynomial.C ((toPoly β) ^ (((toPoly D).natDegree - 1) - j))
          * subresultant (DensePoly.toPoly (bArgAmtD' A D))
              (DensePoly.toPoly (bdivC (GBPolyCore.gbpsremainderCore fuel (liftCtoBPoly D) (bArgAmtD' A D)) β))
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
    (hB : (DensePoly.toPoly (bArgAmtD' A D)).natDegree ≤ (toPoly D).natDegree - 1)
    (hQ : (DensePoly.toPoly s).natDegree + ((toPoly D).natDegree - 1) ≤ (toPoly D).natDegree) :
    IsSimilar (lrtSubresultant (toPoly A) (toPoly D) j)
      (subresultant (DensePoly.toPoly (bArgAmtD' A D))
        (DensePoly.toPoly (bdivC (GBPolyCore.gbpsremainderCore fuel (liftCtoBPoly D) (bArgAmtD' A D)) β))
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
p q) β`, `IsSimilar (Sⱼ(DensePoly.toPoly p, DensePoly.toPoly q; n, m)) (Sⱼ(DensePoly.toPoly q, DensePoly.toPoly r; m, n))`. -/
theorem isSimilar_subresultant_bdivC_step (fuel : ℕ) (p q : GBPolyCore ℚ) (β : DensePoly ℚ) (n m j : ℕ)
    (s : GBPolyCore ℚ) (c : DensePoly ℚ)
    (hstep : IsBdivCExactStep fuel p q β s c)
    (hc0 : toPoly c ≠ 0) (hβ0 : toPoly β ≠ 0)
    (hjm : j ≤ m) (hjn : j < n)
    (hB : (DensePoly.toPoly q).natDegree ≤ m)
    (hQ : (DensePoly.toPoly s).natDegree + m ≤ n) :
    IsSimilar (R := ℚ[X])
      (subresultant (DensePoly.toPoly p : (ℚ[X])[X]) (DensePoly.toPoly q) n m j)
      (subresultant (DensePoly.toPoly q)
        (DensePoly.toPoly (bdivC (GBPolyCore.gbpsremainderCore fuel p q) β)) m n j) := by
  refine ⟨(toPoly c) ^ (m - j),
    (-1 : ℚ[X]) ^ ((m - j) * (n - j)) * (toPoly β) ^ (m - j),
    pow_ne_zero _ hc0,
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hβ0), ?_⟩
  rw [subresultant_C_mul_eq_bdivC_of_bpsremainder fuel p q β n m j s c hstep hjm hjn hB hQ]
  simp only [Polynomial.C_mul, map_pow, map_neg, map_one]
  ring

/-- The combined per-step PRS relation through `DensePoly.toPoly`:
`C(toPoly c)·DensePoly.toPoly p = C(toPoly β)·DensePoly.toPoly r + DensePoly.toPoly q·DensePoly.toPoly s` with `r = bdivC (prem p q) β`. -/
theorem toBPoly_prs_rel (fuel : ℕ) (p q : GBPolyCore ℚ) (β : DensePoly ℚ) (s : GBPolyCore ℚ) (c : DensePoly ℚ)
    (hstep : IsBdivCExactStep fuel p q β s c) :
    Polynomial.C (toPoly c) * DensePoly.toPoly p
      = Polynomial.C (toPoly β) * DensePoly.toPoly (bdivC (GBPolyCore.gbpsremainderCore fuel p q) β)
        + DensePoly.toPoly q * DensePoly.toPoly s := by
  rw [hstep.relation,
    toBPoly_bdivC_exact (GBPolyCore.gbpsremainderCore fuel p q) β hstep.beta_cnorm_ne hstep.exact_division]
  ring

end DeepWiki.SymbolicIntegration.Compute
