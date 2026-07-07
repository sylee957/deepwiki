import DeepWiki.SymbolicIntegration.Compute.Correctness
import DeepWiki.SymbolicIntegration.SubresultantCorrectness.ToBPolyDegree
import DeepWiki.SymbolicIntegration.SubresultantPRS
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree

/-! # Bridging the computable subresultant PRS to the abstract subresultant
Connects the computable bivariate PRS engine (`BPoly = ℚ[t][x]`, `bpsremainder`, `subresPRS`) to the
abstract Sylvester-submatrix `subresultant` through the `toBPoly : BPoly → (ℚ[X])[X]` homomorphism, up to
the full `lrtGcdCompute ↔ lrtSubresultant` agreement over a residue ring. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### One subresultant-PRS step of the computable pseudo-remainder -/

/-- One subresultant-PRS step through `toBPoly`: from the pseudo-division identity for `(s, c)`,
`C((toPoly c)^(m−j)) · Sⱼ(A,B; n,m) = (-1)^((m−j)(n−j)) · Sⱼ(B, Rem; m,n)` under the degree bounds. -/
theorem subresultant_C_mul_eq_rem_of_bpsremainder (fuel : ℕ) (p q : BPoly) (n m j : ℕ)
    (s : BPoly) (c : CPoly)
    (hsc : Polynomial.C (toPoly c) * toBPoly p
        = toBPoly s * toBPoly q + toBPoly (bpsremainder fuel p q))
    (hjm : j ≤ m) (hjn : j < n)
    (hB : (toBPoly q).natDegree ≤ m)
    (hQ : (toBPoly s).natDegree + m ≤ n) :
    Polynomial.C ((toPoly c) ^ (m - j)) * subresultant (toBPoly p) (toBPoly q) n m j
      = (-1 : (ℚ[X])[X]) ^ ((m - j) * (n - j))
        * subresultant (toBPoly q) (toBPoly (bpsremainder fuel p q)) m n j := by
  rw [← subresultant_C_mul_left (toPoly c) (toBPoly p) (toBPoly q) n m j hjm (le_of_lt hjn)]
  exact subresultant_rem (Polynomial.C (toPoly c) * toBPoly p) (toBPoly q) (toBPoly s)
    (toBPoly (bpsremainder fuel p q)) n m j hjm hjn hB hQ (by rw [hsc]; ring)

/-- Existence form: some quotient/content `(s, c)` realize the pseudo-division identity and, given the
quotient-degree bound, the subresultant reduction. -/
theorem exists_subresultant_C_mul_eq_rem_of_bpsremainder (fuel : ℕ) (p q : BPoly) (n m j : ℕ)
    (hjm : j ≤ m) (hjn : j < n) (hB : (toBPoly q).natDegree ≤ m) :
    ∃ (s : BPoly) (c : CPoly),
      Polynomial.C (toPoly c) * toBPoly p
          = toBPoly s * toBPoly q + toBPoly (bpsremainder fuel p q)
        ∧ ((toBPoly s).natDegree + m ≤ n →
          Polynomial.C ((toPoly c) ^ (m - j)) * subresultant (toBPoly p) (toBPoly q) n m j
            = (-1 : (ℚ[X])[X]) ^ ((m - j) * (n - j))
              * subresultant (toBPoly q) (toBPoly (bpsremainder fuel p q)) m n j) := by
  obtain ⟨s, c, hsc⟩ := toBPoly_bpsremainder fuel p q
  exact ⟨s, c, hsc, fun hQs =>
    subresultant_C_mul_eq_rem_of_bpsremainder fuel p q n m j s c hsc hjm hjn hB hQs⟩

/-! ### Identifying the LRT operands: the computable lifts realize `D.map C`, `A − t·D'` -/

/-- `toPoly (cC c) = C c`: the constant-`CPoly` lift realizes the `ℚ[X]` constant. -/
@[simp] theorem toPoly_cC (c : ℚ) : toPoly (cC c) = Polynomial.C c := by
  rw [cC, toPoly_cnorm]
  simp [toPoly_cons]

/-- `toBPoly (liftCtoBPoly p) = (toPoly p).map C`: `liftCtoBPoly` realizes the coefficient embedding. -/
theorem toBPoly_liftCtoBPoly (p : CPoly) :
    toBPoly (liftCtoBPoly p) = (toPoly p).map (Polynomial.C : ℚ →+* ℚ[X]) := by
  induction p with
  | nil => simp [liftCtoBPoly]
  | cons a as ih =>
    show toBPoly (cC a :: liftCtoBPoly as) = _
    rw [toBPoly_cons, toPoly_cons, ih, toPoly_cC, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_X, Polynomial.map_C]

/-- `toPoly ctVar = X`: the computable `t`-variable lifts to the indeterminate `X ∈ ℚ[t]`. -/
@[simp] theorem toPoly_ctVar : toPoly ctVar = (Polynomial.X : ℚ[X]) := by
  rw [ctVar]; simp [toPoly_cons]

/-- `toBPoly (bArgAmtD' A D) = (toPoly A).map C − C X · (derivative (toPoly D)).map C`: the LRT second
operand `A − t·D'`. -/
theorem toBPoly_bArgAmtD' (A D : CPoly) :
    toBPoly (bArgAmtD' A D)
      = (toPoly A).map (Polynomial.C : ℚ →+* ℚ[X])
        - Polynomial.C Polynomial.X * (derivative (toPoly D)).map (Polynomial.C : ℚ →+* ℚ[X]) := by
  rw [bArgAmtD', toBPoly_bsub, toBPoly_liftCtoBPoly, toBPoly_bscaleC, toBPoly_liftCtoBPoly,
    toPoly_ctVar, toPoly_cderiv]

/-- `lrtSubresultant A D j` is the abstract subresultant of the `toBPoly` images of the computable
operands at formal degrees `deg D`, `deg D − 1`. -/
theorem lrtSubresultant_eq_subresultant_toBPoly (A D : CPoly) (j : ℕ) :
    lrtSubresultant (toPoly A) (toPoly D) j
      = subresultant (toBPoly (liftCtoBPoly D)) (toBPoly (bArgAmtD' A D))
          (toPoly D).natDegree ((toPoly D).natDegree - 1) j := by
  rw [lrtSubresultant, toBPoly_liftCtoBPoly, toBPoly_bArgAmtD']

/-! ### The LRT subresultant reduced to the first computable pseudo-remainder -/

/-- LRT subresultant after one computable pseudo-division step:
`C((toPoly c)^(m−j)) · lrtSubresultant A D j = (-1)^((m−j)(n−j)) · Sⱼ(Q, prem(P,Q); m, n)` with
`n = deg D`, `m = deg D − 1`, `P = liftCtoBPoly D`, `Q = bArgAmtD' A D`. -/
theorem lrtSubresultant_C_mul_eq_rem_of_bpsremainder (fuel : ℕ) (A D : CPoly) (j : ℕ)
    (s : BPoly) (c : CPoly)
    (hsc : Polynomial.C (toPoly c) * toBPoly (liftCtoBPoly D)
        = toBPoly s * toBPoly (bArgAmtD' A D)
          + toBPoly (bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D)))
    (hjm : j ≤ (toPoly D).natDegree - 1) (hjn : j < (toPoly D).natDegree)
    (hB : (toBPoly (bArgAmtD' A D)).natDegree ≤ (toPoly D).natDegree - 1)
    (hQ : (toBPoly s).natDegree + ((toPoly D).natDegree - 1) ≤ (toPoly D).natDegree) :
    Polynomial.C ((toPoly c) ^ (((toPoly D).natDegree - 1) - j))
        * lrtSubresultant (toPoly A) (toPoly D) j
      = (-1 : (ℚ[X])[X]) ^ ((((toPoly D).natDegree - 1) - j) * ((toPoly D).natDegree - j))
        * subresultant (toBPoly (bArgAmtD' A D))
            (toBPoly (bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D)))
            ((toPoly D).natDegree - 1) (toPoly D).natDegree j := by
  rw [lrtSubresultant_eq_subresultant_toBPoly]
  exact subresultant_C_mul_eq_rem_of_bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D)
    (toPoly D).natDegree ((toPoly D).natDegree - 1) j s c hsc hjm hjn hB hQ

/-! ### `bdivC` realizes exact `ℚ[t]`-division -/

/-- If every `x`-coefficient of `p` divides exactly by `c`, then
`C(toPoly c) · toBPoly (p.map (cdiv fuel · c)) = toBPoly p`. -/
theorem toBPoly_map_cdiv_exact (fuel : ℕ) (p : BPoly) (c : CPoly) (hc : cnorm c ≠ [])
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
theorem toBPoly_bdivC_exact (fuel : ℕ) (p : BPoly) (c : CPoly) (hc : cnorm c ≠ [])
    (hrem : ∀ a ∈ p, toPoly (cmod fuel a c) = 0) :
    Polynomial.C (toPoly c) * toBPoly (bdivC fuel p c) = toBPoly p := by
  rw [bdivC, toBPoly_bnorm]
  exact toBPoly_map_cdiv_exact fuel p c hc hrem

/-- `bdivC` exact division from divisibility: if `toPoly c ∣ toPoly a` for every `x`-coefficient `a`,
then `C(toPoly c) · toBPoly (bdivC fuel p c) = toBPoly p`. -/
theorem toBPoly_bdivC_exact_of_dvd (fuel : ℕ) (p : BPoly) (c : CPoly) (hc : cnorm c ≠ [])
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
structure IsBdivCExactStep (fuel : ℕ) (p q : BPoly) (β : CPoly) (s : BPoly) (c : CPoly) : Prop where
  /-- The pseudo-division relation before β-division. -/
  relation : Polynomial.C (toPoly c) * toBPoly p
    = toBPoly s * toBPoly q + toBPoly (bpsremainder fuel p q)
  /-- The β divisor is nonzero after normalization. -/
  beta_cnorm_ne : cnorm β ≠ []
  /-- β divides every coefficient of the pseudo-remainder exactly. -/
  exact_division : ∀ a ∈ bpsremainder fuel p q, toPoly (cmod fuel a β) = 0

/-- One subresultant-PRS step on the β-divided remainder `r = bdivC fuel (bpsremainder fuel p q) β`:
`C((toPoly c)^(m−j)) · Sⱼ(A,B; n,m) = (-1)^((m−j)(n−j)) · C((toPoly β)^(m−j)) · Sⱼ(B, toBPoly r; m,n)`. -/
theorem subresultant_C_mul_eq_bdivC_of_bpsremainder (fuel : ℕ) (p q : BPoly) (β : CPoly) (n m j : ℕ)
    (s : BPoly) (c : CPoly)
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
theorem lrtSubresultant_C_mul_eq_bdivC_of_bpsremainder (fuel : ℕ) (A D : CPoly) (β : CPoly) (j : ℕ)
    (s : BPoly) (c : CPoly)
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
theorem isSimilar_lrtSubresultant_subresultant_bdivC (fuel : ℕ) (A D : CPoly) (β : CPoly) (j : ℕ)
    (s : BPoly) (c : CPoly)
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
theorem isSimilar_subresultant_bdivC_step (fuel : ℕ) (p q : BPoly) (β : CPoly) (n m j : ℕ)
    (s : BPoly) (c : CPoly)
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
theorem toBPoly_prs_rel (fuel : ℕ) (p q : BPoly) (β : CPoly) (s : BPoly) (c : CPoly)
    (hstep : IsBdivCExactStep fuel p q β s c) :
    Polynomial.C (toPoly c) * toBPoly p
      = Polynomial.C (toPoly β) * toBPoly (bdivC fuel (bpsremainder fuel p q) β)
        + toBPoly q * toBPoly s := by
  rw [hstep.relation,
    toBPoly_bdivC_exact fuel (bpsremainder fuel p q) β hstep.beta_cnorm_ne hstep.exact_division]
  ring

/-! ### The abstract-PRS telescope over the computable chain -/

/-- Full chain telescope: for a computable PRS chain `G` satisfying the divided one-step hypotheses,
`IsSimilar (Sⱼ(toBPoly (G 0), toBPoly (G 1))) (Sⱼ(toBPoly (G m), toBPoly (G (m+1))))` at the elements'
own degrees. -/
theorem isSimilar_subresPRS_telescope (fuel : ℕ) (G : ℕ → BPoly)
    (bt : ℕ → CPoly) (s : ℕ → BPoly) (c : ℕ → CPoly) (j m : ℕ)
    (hsc : ∀ l < m, Polynomial.C (toPoly (c l)) * toBPoly (G l)
        = toBPoly (s l) * toBPoly (G (l + 1)) + toBPoly (bpsremainder fuel (G l) (G (l + 1))))
    (hβcn : ∀ l < m, cnorm (bt l) ≠ [])
    (hdiv : ∀ l < m, ∀ a ∈ bpsremainder fuel (G l) (G (l + 1)), toPoly (cmod fuel a (bt l)) = 0)
    (hG2 : ∀ l < m, G (l + 2) = bdivC fuel (bpsremainder fuel (G l) (G (l + 1))) (bt l))
    (hc0 : ∀ l < m, toPoly (c l) ≠ 0) (hβ0 : ∀ l < m, toPoly (bt l) ≠ 0)
    (hlc : ∀ l < m, (toBPoly (G (l + 1))).coeff (toBPoly (G (l + 1))).natDegree ≠ 0)
    (hcb : ∀ l < m, (toBPoly (G (l + 2))).natDegree < (toBPoly (G (l + 1))).natDegree)
    (hj : ∀ l < m, j < (toBPoly (G (l + 2))).natDegree)
    (hQ : ∀ l < m, (toBPoly (s l)).natDegree + (toBPoly (G (l + 1))).natDegree
      ≤ (toBPoly (G l)).natDegree) :
    IsSimilar
      (subresultant (toBPoly (G 0)) (toBPoly (G 1))
        (toBPoly (G 0)).natDegree (toBPoly (G 1)).natDegree j)
      (subresultant (toBPoly (G m)) (toBPoly (G (m + 1)))
        (toBPoly (G m)).natDegree (toBPoly (G (m + 1))).natDegree j) :=
  subresultant_prs_telescope (fun i => toBPoly (G i)) (fun l => toPoly (c l))
    (fun l => toPoly (bt l)) (fun l => toBPoly (s l)) j m
    hc0 hβ0 hlc hcb hj hQ
    (fun l hl => by
      have hrel := toBPoly_prs_rel fuel (G l) (G (l + 1)) (bt l) (s l) (c l)
        ⟨hsc l hl, hβcn l hl, hdiv l hl⟩
      rw [hG2 l hl]; exact hrel)

/-! ### The chain endpoint: `Sⱼ` is similar to the degree-`j` `subresPRS` element -/

/-- A divided subresultant PRS chain through index `m` with a regular endpoint. -/
structure IsSubresPRSChainInput (fuel : ℕ) (G : ℕ → BPoly) (bt : ℕ → CPoly)
    (s : ℕ → BPoly) (c : ℕ → CPoly) (m : ℕ) : Prop where
  /-- Each pseudo-remainder step is exact after β-division. -/
  exact_step : ∀ l ≤ m, IsBdivCExactStep fuel (G l) (G (l + 1)) (bt l) (s l) (c l)
  /-- Each next chain element is the β-divided pseudo-remainder. -/
  next_eq : ∀ l ≤ m, G (l + 2) = bdivC fuel (bpsremainder fuel (G l) (G (l + 1))) (bt l)
  /-- Each pseudo-division scalar reads to a nonzero polynomial. -/
  scale_toPoly_ne : ∀ l ≤ m, toPoly (c l) ≠ 0
  /-- Each β divisor reads to a nonzero polynomial. -/
  beta_toPoly_ne : ∀ l ≤ m, toPoly (bt l) ≠ 0
  /-- Each middle chain element has nonzero leading coefficient. -/
  leading_coeff_ne : ∀ l ≤ m, (toBPoly (G (l + 1))).coeff (toBPoly (G (l + 1))).natDegree ≠ 0
  /-- Degrees strictly drop along the divided PRS chain. -/
  degree_drop : ∀ l ≤ m, (toBPoly (G (l + 2))).natDegree < (toBPoly (G (l + 1))).natDegree
  /-- The endpoint degree lies below all earlier second-successor degrees. -/
  endpoint_degree_lt : ∀ l < m, (toBPoly (G (m + 2))).natDegree < (toBPoly (G (l + 2))).natDegree
  /-- Each pseudo-quotient satisfies the degree bound used by subresultant reduction. -/
  quotient_degree_le : ∀ l ≤ m, (toBPoly (s l)).natDegree + (toBPoly (G (l + 1))).natDegree
    ≤ (toBPoly (G l)).natDegree
  /-- The endpoint chain element is nonzero after `toBPoly`. -/
  endpoint_ne_zero : toBPoly (G (m + 2)) ≠ 0

/-- At the regular index `j = deg (toBPoly (G (m+2)))`,
`IsSimilar (Sⱼ(toBPoly (G 0), toBPoly (G 1))) (toBPoly (G (m+2)))`. -/
theorem isSimilar_subresPRS_elt (fuel : ℕ) (G : ℕ → BPoly)
    (bt : ℕ → CPoly) (s : ℕ → BPoly) (c : ℕ → CPoly) (m : ℕ)
    (hchain : IsSubresPRSChainInput fuel G bt s c m) :
    IsSimilar
      (subresultant (toBPoly (G 0)) (toBPoly (G 1))
        (toBPoly (G 0)).natDegree (toBPoly (G 1)).natDegree (toBPoly (G (m + 2))).natDegree)
      (toBPoly (G (m + 2))) :=
  subresultant_prs_similar_elt (fun i => toBPoly (G i)) (fun l => toPoly (c l))
    (fun l => toPoly (bt l)) (fun l => toBPoly (s l)) m
    hchain.scale_toPoly_ne hchain.beta_toPoly_ne hchain.leading_coeff_ne hchain.degree_drop
    hchain.endpoint_degree_lt hchain.quotient_degree_le
    (fun l hl => by
      have hrel := toBPoly_prs_rel fuel (G l) (G (l + 1)) (bt l) (s l) (c l)
        (hchain.exact_step l hl)
      rw [hchain.next_eq l hl]; exact hrel)
    hchain.endpoint_ne_zero

/-! ### LRT endpoint: `lrtSubresultant` similar to the degree-`j` `subresPRS` element -/

/-- For the LRT chain (`G 0 = liftCtoBPoly D`, `G 1 = bArgAmtD' A D`) with the regular formal degrees,
`IsSimilar (lrtSubresultant A D (deg (G (m+2)))) (toBPoly (G (m+2)))`. -/
theorem isSimilar_lrtSubresultant_subresPRS_elt (fuel : ℕ) (A D : CPoly) (G : ℕ → BPoly)
    (bt : ℕ → CPoly) (s : ℕ → BPoly) (c : ℕ → CPoly) (m : ℕ)
    (hG0 : G 0 = liftCtoBPoly D) (hG1 : G 1 = bArgAmtD' A D)
    (hd0 : (toBPoly (G 0)).natDegree = (toPoly D).natDegree)
    (hd1 : (toBPoly (G 1)).natDegree = (toPoly D).natDegree - 1)
    (hchain : IsSubresPRSChainInput fuel G bt s c m) :
    IsSimilar (lrtSubresultant (toPoly A) (toPoly D) (toBPoly (G (m + 2))).natDegree)
      (toBPoly (G (m + 2))) := by
  have hend := isSimilar_subresPRS_elt fuel G bt s c m hchain
  rw [hd0, hd1] at hend
  rw [lrtSubresultant_eq_subresultant_toBPoly, ← hG0, ← hG1]
  exact hend

/-! ### `bsubresultantGcd ∼ lrtSubresultant` (modulo the degree-`j` filter identity) -/

/-! #### The degree-`j` filter identity, structurally -/

/-- If `L.filter pred = [w]`, then `(L.filter pred).getLast?.getD d = w`. -/
theorem getLast?_getD_filter_eq_of_singleton {α : Type*} (L : List α) (pred : α → Bool) (w d : α)
    (hfil : L.filter pred = [w]) :
    (L.filter pred).getLast?.getD d = w := by
  rw [hfil, List.getLast?_singleton, Option.getD_some]

/-- If the degree-`j` nonzero filter of `subresPRS fuel P Q` is `[w]`, then `bsubresultantGcd fuel j P Q = w`. -/
theorem bsubresultantGcd_eq_of_filter_singleton (fuel j : ℕ) (P Q : BPoly) (w : BPoly)
    (hfil : (subresPRS fuel P Q).filter (fun R => decide (bdeg R = j ∧ ¬ bisZero R)) = [w]) :
    bsubresultantGcd fuel j P Q = w := by
  rw [bsubresultantGcd]
  exact getLast?_getD_filter_eq_of_singleton _ _ w [] hfil

/-- If the degree-`j` nonzero filter of `subresPRS fuel P Q` is `[G (m+2)]`, then
`toBPoly (bsubresultantGcd fuel j P Q) = toBPoly (G (m+2))`. -/
theorem toBPoly_bsubresultantGcd_eq_of_filter_singleton (fuel : ℕ) (P Q : BPoly) (G : ℕ → BPoly) (m : ℕ)
    (hfil : (subresPRS fuel P Q).filter
        (fun R => decide (bdeg R = (toBPoly (G (m + 2))).natDegree ∧ ¬ bisZero R)) = [G (m + 2)]) :
    toBPoly (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree P Q) = toBPoly (G (m + 2)) := by
  rw [bsubresultantGcd_eq_of_filter_singleton fuel (toBPoly (G (m + 2))).natDegree P Q (G (m + 2)) hfil]

/-- Given the filter identity `hfilt`, `IsSimilar (lrtSubresultant A D j) (toBPoly (bsubresultantGcd
fuel j (G 0) (G 1)))` at `j = deg (toBPoly (G (m+2)))`. -/
theorem isSimilar_lrtSubresultant_bsubresultantGcd (fuel : ℕ) (A D : CPoly) (G : ℕ → BPoly)
    (bt : ℕ → CPoly) (s : ℕ → BPoly) (c : ℕ → CPoly) (m : ℕ)
    (hG0 : G 0 = liftCtoBPoly D) (hG1 : G 1 = bArgAmtD' A D)
    (hd0 : (toBPoly (G 0)).natDegree = (toPoly D).natDegree)
    (hd1 : (toBPoly (G 1)).natDegree = (toPoly D).natDegree - 1)
    (hchain : IsSubresPRSChainInput fuel G bt s c m)
    (hfilt : toBPoly (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1))
      = toBPoly (G (m + 2))) :
    IsSimilar (lrtSubresultant (toPoly A) (toPoly D) (toBPoly (G (m + 2))).natDegree)
      (toBPoly (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1))) := by
  rw [hfilt]
  exact isSimilar_lrtSubresultant_subresPRS_elt fuel A D G bt s c m hG0 hG1 hd0 hd1
    hchain

/-- As `isSimilar_lrtSubresultant_bsubresultantGcd`, but with the filter identity derived from the
singleton-filter hypothesis `hfil` instead of taken directly. -/
theorem isSimilar_lrtSubresultant_bsubresultantGcd_real (fuel : ℕ) (A D : CPoly) (G : ℕ → BPoly)
    (bt : ℕ → CPoly) (s : ℕ → BPoly) (c : ℕ → CPoly) (m : ℕ)
    (hG0 : G 0 = liftCtoBPoly D) (hG1 : G 1 = bArgAmtD' A D)
    (hd0 : (toBPoly (G 0)).natDegree = (toPoly D).natDegree)
    (hd1 : (toBPoly (G 1)).natDegree = (toPoly D).natDegree - 1)
    (hchain : IsSubresPRSChainInput fuel G bt s c m)
    (hfil : (subresPRS fuel (G 0) (G 1)).filter
        (fun R => decide (bdeg R = (toBPoly (G (m + 2))).natDegree ∧ ¬ bisZero R)) = [G (m + 2)]) :
    IsSimilar (lrtSubresultant (toPoly A) (toPoly D) (toBPoly (G (m + 2))).natDegree)
      (toBPoly (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1))) :=
  isSimilar_lrtSubresultant_bsubresultantGcd fuel A D G bt s c m hG0 hG1 hd0 hd1
    hchain
    (toBPoly_bsubresultantGcd_eq_of_filter_singleton fuel (G 0) (G 1) G m hfil)

/-! ### `bprimitivePartX` preserves similarity, and `lrtSubresultant ∼ lrtSubresultantCompute` -/

/-- The content stripped by `bprimitivePartX fuel p` is nonzero and divides every coefficient exactly. -/
structure IsPrimitivePartXInput (fuel : ℕ) (p : BPoly) : Prop where
  /-- The computed content is not boolean-zero. -/
  content_not_zero : ¬ cisZero (bcontentX fuel p) = true
  /-- The normalized content list is nonempty. -/
  content_cnorm_ne : cnorm (bcontentX fuel p) ≠ []
  /-- The computed content reads to a nonzero polynomial. -/
  content_toPoly_ne : toPoly (bcontentX fuel p) ≠ 0
  /-- The content divides every normalized `x`-coefficient exactly. -/
  exact_division : ∀ a ∈ bnorm p, toPoly (cmod fuel a (bcontentX fuel p)) = 0

/-- `IsSimilar (toBPoly p) (toBPoly (bprimitivePartX fuel p))` under the content-exactness hypotheses. -/
theorem isSimilar_toBPoly_bprimitivePartX (fuel : ℕ) (p : BPoly)
    (hprim : IsPrimitivePartXInput fuel p) :
    IsSimilar (toBPoly p) (toBPoly (bprimitivePartX fuel p)) :=
  ⟨1, toPoly (bcontentX fuel p), one_ne_zero, hprim.content_toPoly_ne, by
    rw [map_one, one_mul, toBPoly_bprimitivePartX_exact fuel p hprim.content_not_zero
      hprim.content_cnorm_ne hprim.exact_division]⟩

/-- Given the endpoint hypotheses, the filter identity `hfilt`, and content-exactness of `bprimitivePartX`,
`IsSimilar (lrtSubresultant A D j) (toBPoly (lrtSubresultantCompute fuel j A D))`. -/
theorem isSimilar_lrtSubresultant_lrtSubresultantCompute (fuel : ℕ) (A D : CPoly) (G : ℕ → BPoly)
    (bt : ℕ → CPoly) (s : ℕ → BPoly) (c : ℕ → CPoly) (m : ℕ)
    (hG0 : G 0 = liftCtoBPoly D) (hG1 : G 1 = bArgAmtD' A D)
    (hd0 : (toBPoly (G 0)).natDegree = (toPoly D).natDegree)
    (hd1 : (toBPoly (G 1)).natDegree = (toPoly D).natDegree - 1)
    (hchain : IsSubresPRSChainInput fuel G bt s c m)
    (hfilt : toBPoly (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1))
      = toBPoly (G (m + 2)))
    (hprim : IsPrimitivePartXInput fuel
      (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1))) :
    IsSimilar (lrtSubresultant (toPoly A) (toPoly D) (toBPoly (G (m + 2))).natDegree)
      (toBPoly (lrtSubresultantCompute fuel (toBPoly (G (m + 2))).natDegree A D)) := by
  have hraw := isSimilar_lrtSubresultant_bsubresultantGcd fuel A D G bt s c m hG0 hG1 hd0 hd1
    hchain hfilt
  have hprimSim := isSimilar_toBPoly_bprimitivePartX fuel
    (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1)) hprim
  rw [lrtSubresultantCompute, ← hG0, ← hG1]
  exact hraw.trans hprimSim

/-! ### The `bmonicXmodR` mod-`R` unit bridge (`lrtSubresultantCompute → lrtGcdCompute`)
Modeling the residue ring `ℚ[t]/(R)` by an arbitrary ring hom `φ : ℚ[X] →+* S` killing `toPoly R`, the
monic-in-`x` normalization `bmonicXmodR` is multiplication by a residue-ring unit. -/

/-- For `φ` killing `toPoly R`, `φ (toPoly (credR fuel R c)) = φ (toPoly c)`. -/
theorem map_toPoly_credR {S : Type*} [CommRing S] (φ : ℚ[X] →+* S) (fuel : ℕ) (R c : CPoly)
    (hR : cnorm R ≠ []) (hφR : φ (toPoly R) = 0) :
    φ (toPoly (credR fuel R c)) = φ (toPoly c) := by
  have hdiv := toPoly_cdivmod' fuel c R hR
  rw [show (cdivmod fuel c R).1 = cdiv fuel c R from rfl,
      show (cdivmod fuel c R).2 = cmod fuel c R from rfl] at hdiv
  rw [credR, hdiv, map_add, map_mul, hφR, mul_zero, zero_add]

/-- With `Φ = mapRingHom φ` and `φ` killing `toPoly R`,
`Φ (toBPoly (p.map (credR fuel R))) = Φ (toBPoly p)`. -/
theorem mapRingHom_toBPoly_map_credR {S : Type*} [CommRing S] (φ : ℚ[X] →+* S) (fuel : ℕ) (R : CPoly)
    (p : BPoly) (hR : cnorm R ≠ []) (hφR : φ (toPoly R) = 0) :
    (Polynomial.mapRingHom φ) (toBPoly (p.map (credR fuel R)))
      = (Polynomial.mapRingHom φ) (toBPoly p) := by
  induction p with
  | nil => simp
  | cons a as ih =>
    rw [List.map_cons, toBPoly_cons, toBPoly_cons, map_add, map_add, map_mul, map_mul, ih]
    congr 1
    rw [Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.map_C, map_toPoly_credR φ fuel R a hR hφR]

/-- With `Φ = mapRingHom φ` and `φ` killing `toPoly R`, `Φ (toBPoly (bredR fuel R p)) = Φ (toBPoly p)`. -/
theorem mapRingHom_toBPoly_bredR {S : Type*} [CommRing S] (φ : ℚ[X] →+* S) (fuel : ℕ) (R : CPoly)
    (p : BPoly) (hR : cnorm R ≠ []) (hφR : φ (toPoly R) = 0) :
    (Polynomial.mapRingHom φ) (toBPoly (bredR fuel R p)) = (Polynomial.mapRingHom φ) (toBPoly p) := by
  rw [bredR, toBPoly_bnorm, mapRingHom_toBPoly_map_credR φ fuel R p hR hφR]

/-- `cinvMod` is the mod-`R` inverse: for `φ` killing `toPoly R`, when the extended-Euclidean gcd of `c, R`
reduces to a nonzero constant `C u`, `φ (toPoly (cinvMod fuel R c)) · φ (toPoly c) = 1`. -/
theorem map_toPoly_cinvMod_mul {S : Type*} [CommRing S] (φ : ℚ[X] →+* S) (fuel : ℕ) (R c : CPoly)
    (hR : cnorm R ≠ []) (hφR : φ (toPoly R) = 0) {u : ℚ} (hu : u ≠ 0)
    (hg : toPoly (cgcdExt fuel c R).1 = Polynomial.C u) :
    φ (toPoly (cinvMod fuel R c)) * φ (toPoly c) = 1 := by
  -- Bézout: toPoly s · toPoly c + toPoly t · toPoly R = toPoly g = C u
  have hbez := toPoly_cgcdExt fuel c R
  -- clead g = u (leading coeff of the constant C u)
  have hlead : clead (cgcdExt fuel c R).1 = u := by
    rw [clead_eq_leadingCoeff, hg, Polynomial.leadingCoeff_C]
  -- φ image of the inverse: drop the credR, expand the cscale
  rw [cinvMod]
  -- cinvMod fuel R c = credR fuel R (cscale (clead g)⁻¹ s), with s = (cgcdExt fuel c R).2.1
  rw [map_toPoly_credR φ fuel R _ hR hφR, toPoly_cscale, map_mul, hlead]
  -- now: φ (C u⁻¹) * φ (toPoly s) * φ (toPoly c) = 1
  -- from Bézout image: φ(toPoly s)·φ(toPoly c) = φ (C u)
  have himg : φ (toPoly (cgcdExt fuel c R).2.1) * φ (toPoly c) = φ (Polynomial.C u) := by
    have := congrArg φ hbez
    rw [map_add, map_mul, map_mul, hφR, mul_zero, add_zero, hg] at this
    exact this
  rw [mul_assoc, himg, ← map_mul, ← Polynomial.C_mul, inv_mul_cancel₀ hu, Polynomial.C_1, map_one]

/-- With `Φ = mapRingHom φ` and `φ` killing `toPoly R`,
`Φ (toBPoly (q.map (fun c => credR fuel R (cmul c inv)))) = C (φ (toPoly inv)) · Φ (toBPoly q)`. -/
theorem mapRingHom_toBPoly_map_credR_cmul {S : Type*} [CommRing S] (φ : ℚ[X] →+* S) (fuel : ℕ)
    (R inv : CPoly) (q : BPoly) (hR : cnorm R ≠ []) (hφR : φ (toPoly R) = 0) :
    (Polynomial.mapRingHom φ) (toBPoly (q.map (fun c => credR fuel R (cmul c inv))))
      = Polynomial.C (φ (toPoly inv)) * (Polynomial.mapRingHom φ) (toBPoly q) := by
  induction q with
  | nil => simp
  | cons a as ih =>
    rw [List.map_cons, toBPoly_cons, toBPoly_cons, map_add, map_add, map_mul, map_mul, ih, mul_add]
    congr 1
    · rw [Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.map_C,
        map_toPoly_credR φ fuel R _ hR hφR, toPoly_cmul, map_mul, Polynomial.C_mul, mul_comm]
    · rw [Polynomial.coe_mapRingHom (f := φ), Polynomial.map_X]; ring

/-- With `Φ = mapRingHom φ` and `φ` killing `toPoly R`, when the leading coefficient's mod-`R` gcd reduces
to a nonzero constant `C u`, `Φ (toBPoly (bmonicXmodR fuel R p)) = C (φ (toPoly inv)) · Φ (toBPoly p)` with
`φ (toPoly inv)` a unit in `S`. -/
theorem mapRingHom_toBPoly_bmonicXmodR {S : Type*} [CommRing S] (φ : ℚ[X] →+* S) (fuel : ℕ) (R : CPoly)
    (p : BPoly) (hR : cnorm R ≠ []) (hφR : φ (toPoly R) = 0) {u : ℚ} (hu : u ≠ 0)
    (hg : toPoly (cgcdExt fuel (blc (bredR fuel R p)) R).1 = Polynomial.C u)
    (hpz : ¬ bisZero (bredR fuel R p) = true) :
    (Polynomial.mapRingHom φ) (toBPoly (bmonicXmodR fuel R p))
        = Polynomial.C (φ (toPoly (cinvMod fuel R (blc (bredR fuel R p)))))
          * (Polynomial.mapRingHom φ) (toBPoly p)
      ∧ φ (toPoly (cinvMod fuel R (blc (bredR fuel R p))))
          * φ (toPoly (blc (bredR fuel R p))) = 1 := by
  refine ⟨?_, map_toPoly_cinvMod_mul φ fuel R (blc (bredR fuel R p)) hR hφR hu hg⟩
  rw [bmonicXmodR]
  simp only [hpz, Bool.false_eq_true, if_false]
  rw [toBPoly_bnorm,
    mapRingHom_toBPoly_map_credR_cmul φ fuel R (cinvMod fuel R (blc (bredR fuel R p)))
      (bredR fuel R p) hR hφR,
    mapRingHom_toBPoly_bredR φ fuel R p hR hφR]

/-! ### The full `lrtGcdCompute ↔ lrtSubresultant` agreement over the residue ring `ℚ[t]/(R)` -/

/-- A `ℚ[t]`-similarity `IsSimilar A B` whose witnesses stay `φ`-nonzero gives
`IsSimilar (Φ A) (Φ B)` (`Φ = mapRingHom φ`). -/
theorem isSimilar_mapRingHom {S : Type*} [CommRing S] (φ : ℚ[X] →+* S) {A B : (ℚ[X])[X]}
    (h : IsSimilar A B) (hne : ∀ a b : ℚ[X], a ≠ 0 → b ≠ 0 → Polynomial.C a * A = Polynomial.C b * B
      → φ a ≠ 0 ∧ φ b ≠ 0) :
    IsSimilar ((Polynomial.mapRingHom φ) A) ((Polynomial.mapRingHom φ) B) := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  obtain ⟨hφa, hφb⟩ := hne a b ha hb hab
  refine ⟨φ a, φ b, hφa, hφb, ?_⟩
  have hcong := congrArg (Polynomial.map φ) hab
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C] at hcong
  simpa only [Polynomial.coe_mapRingHom] using hcong

/-- The full `lrtGcdCompute ↔ lrtSubresultant` agreement over `S = ℚ[t]/(R)`: for a residue map
`φ : ℚ[X] →+* S` killing `toPoly R`, under the whole-chain and regularity hypotheses,
`IsSimilar (Φ (lrtSubresultant A D j)) (Φ (toBPoly (lrtGcdCompute fuel j R A D)))`. -/
theorem lrtGcdCompute_isSimilar_lrtSubresultant {S : Type*} [CommRing S] [IsDomain S] (φ : ℚ[X] →+* S)
    (fuel : ℕ) (R A D : CPoly) (G : ℕ → BPoly) (bt : ℕ → CPoly) (s : ℕ → BPoly) (c : ℕ → CPoly) (m : ℕ)
    (hRcn : cnorm R ≠ []) (hφR : φ (toPoly R) = 0)
    (hG0 : G 0 = liftCtoBPoly D) (hG1 : G 1 = bArgAmtD' A D)
    (hd0 : (toBPoly (G 0)).natDegree = (toPoly D).natDegree)
    (hd1 : (toBPoly (G 1)).natDegree = (toPoly D).natDegree - 1)
    (hchain : IsSubresPRSChainInput fuel G bt s c m)
    (hfilt : toBPoly (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1))
      = toBPoly (G (m + 2)))
    (hprim : IsPrimitivePartXInput fuel
      (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree (G 0) (G 1)))
    (hne : ∀ a b : ℚ[X], a ≠ 0 → b ≠ 0 →
        Polynomial.C a * lrtSubresultant (toPoly A) (toPoly D) (toBPoly (G (m + 2))).natDegree
          = Polynomial.C b * toBPoly (lrtSubresultantCompute fuel (toBPoly (G (m + 2))).natDegree A D)
        → φ a ≠ 0 ∧ φ b ≠ 0)
    {u : ℚ} (hu : u ≠ 0)
    (hgu : toPoly (cgcdExt fuel
        (blc (bredR fuel R (lrtSubresultantCompute fuel (toBPoly (G (m + 2))).natDegree A D))) R).1
      = Polynomial.C u)
    (hpz : ¬ bisZero (bredR fuel R
        (lrtSubresultantCompute fuel (toBPoly (G (m + 2))).natDegree A D)) = true) :
    IsSimilar ((Polynomial.mapRingHom φ)
        (lrtSubresultant (toPoly A) (toPoly D) (toBPoly (G (m + 2))).natDegree))
      ((Polynomial.mapRingHom φ) (toBPoly
        (lrtGcdCompute fuel (toBPoly (G (m + 2))).natDegree R A D))) := by
  -- abstract ℚ[t]-similarity, mapped through φ to the residue ring
  have habs := isSimilar_lrtSubresultant_lrtSubresultantCompute fuel A D G bt s c m hG0 hG1 hd0 hd1
    hchain hfilt hprim
  have hmap := isSimilar_mapRingHom φ habs hne
  -- the bmonicXmodR unit bridge: lrtGcdCompute = bmonicXmodR R lrtSubresultantCompute
  obtain ⟨hbridge, hunit⟩ := mapRingHom_toBPoly_bmonicXmodR φ fuel R
    (lrtSubresultantCompute fuel (toBPoly (G (m + 2))).natDegree A D) hRcn hφR hu hgu hpz
  have hsimUnit := isSimilar_of_unit_mul
    (A := (Polynomial.mapRingHom φ) (toBPoly
      (lrtSubresultantCompute fuel (toBPoly (G (m + 2))).natDegree A D)))
    (B := (Polynomial.mapRingHom φ) (toBPoly
      (lrtGcdCompute fuel (toBPoly (G (m + 2))).natDegree R A D)))
    hunit (by rw [lrtGcdCompute]; exact hbridge)
  exact hmap.trans hsimUnit

/-! ### From the chain agreement to `lrtGcdCompute`
The pieces above assemble the full multi-step subresultant-PRS chain agreement into the headline
`lrtGcdCompute_isSimilar_lrtSubresultant`, with the degree-`j` filter identity and the `bmonicXmodR` unit
bridge both discharged structurally, and the concrete `subresPRS` data supplied by the `goState` section
below. -/

-- Restatement: `bdivC` is exact ℚ[t]-division — `C(toPoly c)·toBPoly(bdivC fuel p c) = toBPoly p`
-- when every x-coefficient divides exactly.
example (fuel : ℕ) (p : BPoly) (c : CPoly) (hc : cnorm c ≠ [])
    (hrem : ∀ a ∈ p, toPoly (cmod fuel a c) = 0) :
    Polynomial.C (toPoly c) * toBPoly (bdivC fuel p c) = toBPoly p :=
  toBPoly_bdivC_exact fuel p c hc hrem

-- Restatement: the LRT subresultant is ℚ[t]-similar to the next divided PRS pair's subresultant.
example (fuel : ℕ) (A D β : CPoly) (j : ℕ) (s : BPoly) (c : CPoly)
    (hsc : Polynomial.C (toPoly c) * toBPoly (liftCtoBPoly D)
        = toBPoly s * toBPoly (bArgAmtD' A D)
          + toBPoly (bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D)))
    (hβ : cnorm β ≠ [])
    (hdiv : ∀ a ∈ bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D), toPoly (cmod fuel a β) = 0)
    (hc0 : toPoly c ≠ 0) (hβ0 : toPoly β ≠ 0)
    (hjm : j ≤ (toPoly D).natDegree - 1) (hjn : j < (toPoly D).natDegree)
    (hB : (toBPoly (bArgAmtD' A D)).natDegree ≤ (toPoly D).natDegree - 1)
    (hQ : (toBPoly s).natDegree + ((toPoly D).natDegree - 1) ≤ (toPoly D).natDegree) :
    IsSimilar (lrtSubresultant (toPoly A) (toPoly D) j)
      (subresultant (toBPoly (bArgAmtD' A D))
        (toBPoly (bdivC fuel (bpsremainder fuel (liftCtoBPoly D) (bArgAmtD' A D)) β))
        ((toPoly D).natDegree - 1) (toPoly D).natDegree j) :=
  isSimilar_lrtSubresultant_subresultant_bdivC fuel A D β j s c ⟨hsc, hβ, hdiv⟩
    hc0 hβ0 hjm hjn hB hQ

-- Restatement: the WHOLE computable PRS chain telescopes — `Sⱼ(G 0, G 1) ~ Sⱼ(G m, G (m+1))` for any `m`.
example (fuel : ℕ) (G : ℕ → BPoly) (bt : ℕ → CPoly) (s : ℕ → BPoly) (c : ℕ → CPoly) (j m : ℕ)
    (hsc : ∀ l < m, Polynomial.C (toPoly (c l)) * toBPoly (G l)
        = toBPoly (s l) * toBPoly (G (l + 1)) + toBPoly (bpsremainder fuel (G l) (G (l + 1))))
    (hβcn : ∀ l < m, cnorm (bt l) ≠ [])
    (hdiv : ∀ l < m, ∀ a ∈ bpsremainder fuel (G l) (G (l + 1)), toPoly (cmod fuel a (bt l)) = 0)
    (hG2 : ∀ l < m, G (l + 2) = bdivC fuel (bpsremainder fuel (G l) (G (l + 1))) (bt l))
    (hc0 : ∀ l < m, toPoly (c l) ≠ 0) (hβ0 : ∀ l < m, toPoly (bt l) ≠ 0)
    (hlc : ∀ l < m, (toBPoly (G (l + 1))).coeff (toBPoly (G (l + 1))).natDegree ≠ 0)
    (hcb : ∀ l < m, (toBPoly (G (l + 2))).natDegree < (toBPoly (G (l + 1))).natDegree)
    (hj : ∀ l < m, j < (toBPoly (G (l + 2))).natDegree)
    (hQ : ∀ l < m, (toBPoly (s l)).natDegree + (toBPoly (G (l + 1))).natDegree
      ≤ (toBPoly (G l)).natDegree) :
    IsSimilar
      (subresultant (toBPoly (G 0)) (toBPoly (G 1))
        (toBPoly (G 0)).natDegree (toBPoly (G 1)).natDegree j)
      (subresultant (toBPoly (G m)) (toBPoly (G (m + 1)))
        (toBPoly (G m)).natDegree (toBPoly (G (m + 1))).natDegree j) :=
  isSimilar_subresPRS_telescope fuel G bt s c j m hsc hβcn hdiv hG2 hc0 hβ0 hlc hcb hj hQ

-- Restatement: FACT 1 — the degree-`j` filter identity. A singleton degree-`j` filter of `subresPRS`
-- makes `bsubresultantGcd` read as that single chain element `G (m+2)` (under `toBPoly`).
example (fuel : ℕ) (P Q : BPoly) (G : ℕ → BPoly) (m : ℕ)
    (hfil : (subresPRS fuel P Q).filter
        (fun R => decide (bdeg R = (toBPoly (G (m + 2))).natDegree ∧ ¬ bisZero R)) = [G (m + 2)]) :
    toBPoly (bsubresultantGcd fuel (toBPoly (G (m + 2))).natDegree P Q) = toBPoly (G (m + 2)) :=
  toBPoly_bsubresultantGcd_eq_of_filter_singleton fuel P Q G m hfil

-- Restatement: FACT 2 — the `bmonicXmodR` mod-`R` unit bridge. Over any `φ : ℚ[X] →+* S` killing
-- `toPoly R`, `bmonicXmodR`'s `Φ`-image is a residue-ring UNIT (`η · η' = 1`) times `toBPoly p`'s.
example {S : Type*} [CommRing S] (φ : ℚ[X] →+* S) (fuel : ℕ) (R : CPoly) (p : BPoly)
    (hR : cnorm R ≠ []) (hφR : φ (toPoly R) = 0) {u : ℚ} (hu : u ≠ 0)
    (hg : toPoly (cgcdExt fuel (blc (bredR fuel R p)) R).1 = Polynomial.C u)
    (hpz : ¬ bisZero (bredR fuel R p) = true) :
    (Polynomial.mapRingHom φ) (toBPoly (bmonicXmodR fuel R p))
        = Polynomial.C (φ (toPoly (cinvMod fuel R (blc (bredR fuel R p)))))
          * (Polynomial.mapRingHom φ) (toBPoly p)
      ∧ φ (toPoly (cinvMod fuel R (blc (bredR fuel R p))))
          * φ (toPoly (blc (bredR fuel R p))) = 1 :=
  mapRingHom_toBPoly_bmonicXmodR φ fuel R p hR hφR hu hg hpz

/-! ### Instantiating the abstract chain from the concrete `subresPRS.go`
Mirrors the internal `subresPRS.go` recurrence as a top-level state machine `goState`, so the abstract
chain data `G`/`bt`/`s`/`c` and its side-conditions can be supplied from the real `subresPRS fuel P Q`. -/

/-- ψ-accumulator update of one `subresPRS.go` step: `ψ' = (−lc Ri₋₁)^δ / ψ^(δ−1)` (`ψ' = ψ` when `δ = 0`). -/
def goPsi' (fuel : ℕ) (Ri_1 : BPoly) (psi : CPoly) (dp : ℕ) : CPoly :=
  if dp = 0 then psi else cdiv fuel (cpowP (cneg (blc Ri_1)) dp) (cpowP psi (dp - 1))

/-- β-divisor of one `subresPRS.go` step: `β = −lc(Ri₋₁) · ψ'^δ` with `ψ'` from `goPsi'`. -/
def goBeta (fuel : ℕ) (Ri_1 : BPoly) (psi : CPoly) (dp : ℕ) : CPoly :=
  cmul (cneg (blc Ri_1)) (cpowP (goPsi' fuel Ri_1 psi dp) dp)

/-- One `subresPRS.go` step on the state `(Ri₋₁, Ri, ψ, δ) ↦ (Ri, Ri₊₁, ψ', δ')` with
`Ri₊₁ = bdivC fuel (prem Ri₋₁ Ri) β`, `ψ' = goPsi'`, `β = goBeta`, `δ' = bdeg Ri − bdeg Ri₊₁`. -/
def goStep (fuel : ℕ) : BPoly × BPoly × CPoly × ℕ → BPoly × BPoly × CPoly × ℕ
  | (Ri_1, Ri, psi, dp) =>
    let psi' := goPsi' fuel Ri_1 psi dp
    let beta := goBeta fuel Ri_1 psi dp
    let Ri1 := bdivC fuel (bpsremainder fuel Ri_1 Ri) beta
    (Ri, Ri1, psi', bdeg Ri - bdeg Ri1)

/-- The `subresPRS.go` state at index `i`: `goState fuel s₀ i = goStepⁱ s₀`. -/
def goState (fuel : ℕ) (s0 : BPoly × BPoly × CPoly × ℕ) : ℕ → BPoly × BPoly × CPoly × ℕ
  | 0 => s0
  | i + 1 => goStep fuel (goState fuel s0 i)

/-- `goState fuel (goStep fuel s₀) k = goState fuel s₀ (k+1)`. -/
theorem goState_goStep (fuel : ℕ) (s0 : BPoly × BPoly × CPoly × ℕ) (k : ℕ) :
    goState fuel (goStep fuel s0) k = goState fuel s0 (k + 1) := by
  induction k generalizing s0 with
  | zero => rfl
  | succ n ih => rw [goState, goState, ih]

/-- `(goState fuel s₀ (l+1)).1 = (goState fuel s₀ l).2.1`. -/
theorem goState_succ_fst (fuel : ℕ) (s0 : BPoly × BPoly × CPoly × ℕ) (l : ℕ) :
    (goState fuel s0 (l + 1)).1 = (goState fuel s0 l).2.1 := by
  show (goStep fuel (goState fuel s0 l)).1 = _
  rw [goStep]

/-- The divided-PRS recurrence for `goState`: `(goState fuel s₀ (l+2)).1 = bdivC fuel (prem …)
(goBeta …)`, holding definitionally. -/
theorem goState_fst_add_two (fuel : ℕ) (s0 : BPoly × BPoly × CPoly × ℕ) (l : ℕ) :
    (goState fuel s0 (l + 2)).1
      = bdivC fuel (bpsremainder fuel (goState fuel s0 l).1 (goState fuel s0 (l + 1)).1)
          (goBeta fuel (goState fuel s0 l).1 (goState fuel s0 l).2.2.1 (goState fuel s0 l).2.2.2) := by
  rw [goState_succ_fst fuel s0 (l + 1)]
  show (goStep fuel (goState fuel s0 l)).2.1 = _
  rw [goStep]
  rw [goState_succ_fst fuel s0 l]

/-! #### The `go`-list ↔ `goState` bridge -/

/-- While `s.2.1` is nonzero, `go fuel (fo+1) …` emits it and recurses on the `goStep`-advanced state. -/
theorem go_step_state (fuel fo : ℕ) (s : BPoly × BPoly × CPoly × ℕ) (hz : ¬ bisZero s.2.1 = true) :
    subresPRS.go fuel (fo + 1) s.1 s.2.1 s.2.2.1 s.2.2.2
      = s.2.1 :: subresPRS.go fuel fo (goStep fuel s).1 (goStep fuel s).2.1
          (goStep fuel s).2.2.1 (goStep fuel s).2.2.2 := by
  obtain ⟨Ri_1, Ri, psi, dp⟩ := s
  rw [subresPRS.go.eq_2]
  simp only at hz
  simp only [hz, Bool.false_eq_true, if_false]
  rfl

/-- While the chain stays nonzero through index `k` and `k < fo`, the `k`-th element of `go fuel fo …` is
`(goState fuel s k).2.1`. -/
theorem go_getD (fuel : ℕ) (s : BPoly × BPoly × CPoly × ℕ) (k fo : ℕ) (hfo : k < fo)
    (hnz : ∀ i ≤ k, ¬ bisZero (goState fuel s i).2.1 = true) :
    (subresPRS.go fuel fo s.1 s.2.1 s.2.2.1 s.2.2.2).getD k [] = (goState fuel s k).2.1 := by
  induction k generalizing s fo with
  | zero =>
    obtain ⟨f', rfl⟩ : ∃ f', fo = f' + 1 := ⟨fo - 1, by omega⟩
    rw [go_step_state fuel f' s (hnz 0 (by omega))]
    rfl
  | succ n ih =>
    obtain ⟨f', rfl⟩ : ∃ f', fo = f' + 1 := ⟨fo - 1, by omega⟩
    rw [go_step_state fuel f' s (hnz 0 (by omega)), List.getD_cons_succ,
      ih (goStep fuel s) f' (by omega)
        (fun i hi => by rw [goState_goStep]; exact hnz (i + 1) (by omega)),
      goState_goStep]

/-- The `i`-th element of `subresPRS fuel P Q` is `(goState fuel (P,Q,[-1],…) i).1`, while the chain stays
nonzero through `i−1` and `i ≤ fuel`. -/
theorem subresPRS_getD (fuel : ℕ) (P Q : BPoly) (i : ℕ) (hfo : i ≤ fuel)
    (hnz : ∀ k < i, ¬ bisZero (goState fuel (P, Q, [-1], bdeg P - bdeg Q) k).2.1 = true) :
    (subresPRS fuel P Q).getD i [] = (goState fuel (P, Q, [-1], bdeg P - bdeg Q) i).1 := by
  rw [subresPRS.eq_def]
  cases i with
  | zero => rfl
  | succ n =>
    rw [List.getD_cons_succ]
    have h := go_getD fuel (P, Q, [-1], bdeg P - bdeg Q) n fuel (by omega)
      (fun k hk => hnz k (by omega))
    simp only at h
    rw [h, goState_succ_fst]

/-- If `s.2.1` is zero, `go fuel fo … = []`. -/
theorem go_zero (fuel fo : ℕ) (s : BPoly × BPoly × CPoly × ℕ) (hz : bisZero s.2.1 = true) :
    subresPRS.go fuel fo s.1 s.2.1 s.2.2.1 s.2.2.2 = [] := by
  cases fo with
  | zero => rw [subresPRS.go.eq_1]
  | succ f' =>
    obtain ⟨Ri_1, Ri, psi, dp⟩ := s
    rw [subresPRS.go.eq_2]
    simp only at hz
    simp only [hz, if_true]

/-- When the chain is nonzero through `k`, zero at `k+1`, and fuel suffices,
`go fuel fo … = (List.range (k+1)).map (fun i => (goState fuel s i).2.1)`. -/
theorem go_eq_range (fuel : ℕ) (s : BPoly × BPoly × CPoly × ℕ) (k fo : ℕ) (hfo : k + 1 < fo)
    (hnz : ∀ i ≤ k, ¬ bisZero (goState fuel s i).2.1 = true)
    (hz : bisZero (goState fuel s (k + 1)).2.1 = true) :
    subresPRS.go fuel fo s.1 s.2.1 s.2.2.1 s.2.2.2
      = (List.range (k + 1)).map (fun i => (goState fuel s i).2.1) := by
  induction k generalizing s fo with
  | zero =>
    obtain ⟨f', rfl⟩ : ∃ f', fo = f' + 1 := ⟨fo - 1, by omega⟩
    rw [go_step_state fuel f' s (hnz 0 (by omega)),
      go_zero fuel f' (goStep fuel s) hz]
    rfl
  | succ n ih =>
    obtain ⟨f', rfl⟩ : ∃ f', fo = f' + 1 := ⟨fo - 1, by omega⟩
    rw [go_step_state fuel f' s (hnz 0 (by omega)),
      ih (goStep fuel s) f' (by omega)
        (fun i hi => by rw [goState_goStep]; exact hnz (i + 1) (by omega))
        (by rw [goState_goStep]; exact hz)]
    conv_rhs => rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    rw [goState_goStep]

/-- If `N` is the unique index below `n` with `q N = true`, then `(List.range n).filter q = [N]`. -/
theorem filter_range_unique {n N : ℕ} (q : ℕ → Bool) (hN : N < n) (hqN : q N = true)
    (huniq : ∀ i, i < n → q i = true → i = N) :
    (List.range n).filter q = [N] := by
  have hnodup : (List.range n).Nodup := List.nodup_range
  have hfnodup : ((List.range n).filter q).Nodup := hnodup.filter q
  have hmem : N ∈ (List.range n).filter q := by
    rw [List.mem_filter, List.mem_range]; exact ⟨hN, hqN⟩
  have hall : ∀ x ∈ (List.range n).filter q, x = N := by
    intro x hx
    rw [List.mem_filter, List.mem_range] at hx
    exact huniq x hx.1 hx.2
  cases hl : (List.range n).filter q with
  | nil => rw [hl] at hmem; simp at hmem
  | cons a as =>
    rw [hl] at hall hmem hfnodup
    have ha : a = N := hall a (by simp)
    have has : as = [] := by
      cases as with
      | nil => rfl
      | cons b bs =>
        exfalso
        have hb : b = N := hall b (by simp)
        rw [ha, hb] at hfnodup
        simp at hfnodup
    rw [ha, has]

/-- When the chain `G i := (goState fuel (P,Q,[-1],…) i).1` is nonzero through `N`, zero at `N+1`, and
`N+1 < fuel`, `subresPRS fuel P Q = (List.range (N+1)).map G`. -/
theorem subresPRS_eq_range (fuel : ℕ) (P Q : BPoly) (N : ℕ) (hfo : N + 1 < fuel)
    (hnz : ∀ i ≤ N, ¬ bisZero (goState fuel (P, Q, [-1], bdeg P - bdeg Q) i).1 = true)
    (hzN : bisZero (goState fuel (P, Q, [-1], bdeg P - bdeg Q) (N + 1)).1 = true) :
    subresPRS fuel P Q
      = (List.range (N + 1)).map (fun i => (goState fuel (P, Q, [-1], bdeg P - bdeg Q) i).1) := by
  set s0 : BPoly × BPoly × CPoly × ℕ := (P, Q, [-1], bdeg P - bdeg Q) with hs0
  rw [subresPRS.eq_def]
  cases N with
  | zero =>
    have hQz : bisZero s0.2.1 = true := by
      have := hzN; rw [goState_succ_fst] at this; exact this
    rw [go_zero fuel fuel s0 hQz]
    show [P] = [(goState fuel s0 0).1]
    rfl
  | succ n =>
    rw [go_eq_range fuel s0 n fuel (by omega)
      (fun i hi => by rw [← goState_succ_fst]; exact hnz (i + 1) (by omega))
      (by rw [← goState_succ_fst]; exact hzN)]
    conv_rhs => rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    refine congrArg (P :: ·) (List.map_congr_left ?_)
    intro i _
    simp only [Function.comp_apply, goState_succ_fst]

/-- If `f (i+1) < f i` for all `i < N`, then `N` is the only index `i ≤ N` with `f i = f N`. -/
theorem unique_of_strictAnti (f : ℕ → ℕ) (N : ℕ) (hstrict : ∀ i < N, f (i + 1) < f i) :
    ∀ i ≤ N, f i = f N → i = N := by
  have mono : ∀ j ≤ N, ∀ i < j, f j < f i := by
    intro j hj
    induction j with
    | zero => intro i hi; omega
    | succ n ih =>
      intro i hi
      have hstep : f (n + 1) < f n := hstrict n (by omega)
      rcases Nat.lt_or_ge i n with hlt | hge
      · have := ih (by omega) i hlt; omega
      · have : i = n := by omega
        subst this; omega
  intro i hi heq
  by_contra hne
  have hiN : i < N := lt_of_le_of_ne hi hne
  have := mono N (le_refl N) i hiN
  omega

/-- The degree-`bdeg (G N)` nonzero filter of `subresPRS fuel P Q` is `[G N]`, under nonzero-through-`N`,
zero-at-`N+1`, strict `bdeg` decrease, and `N+1 < fuel`. -/
theorem subresPRS_filter_singleton (fuel : ℕ) (P Q : BPoly) (N : ℕ) (hfo : N + 1 < fuel)
    (hnz : ∀ i ≤ N, ¬ bisZero (goState fuel (P, Q, [-1], bdeg P - bdeg Q) i).1 = true)
    (hzN : bisZero (goState fuel (P, Q, [-1], bdeg P - bdeg Q) (N + 1)).1 = true)
    (hstrict : ∀ i < N, bdeg (goState fuel (P, Q, [-1], bdeg P - bdeg Q) (i + 1)).1
        < bdeg (goState fuel (P, Q, [-1], bdeg P - bdeg Q) i).1) :
    (subresPRS fuel P Q).filter
        (fun R => decide (bdeg R = bdeg (goState fuel (P, Q, [-1], bdeg P - bdeg Q) N).1
          ∧ ¬ bisZero R))
      = [(goState fuel (P, Q, [-1], bdeg P - bdeg Q) N).1] := by
  set s0 : BPoly × BPoly × CPoly × ℕ := (P, Q, [-1], bdeg P - bdeg Q) with hs0
  set G := fun i => (goState fuel s0 i).1 with hG
  rw [subresPRS_eq_range fuel P Q N hfo hnz hzN, List.filter_map]
  have hfilt : (List.range (N + 1)).filter
      ((fun R => decide (bdeg R = bdeg (G N) ∧ ¬ bisZero R)) ∘ G) = [N] := by
    apply filter_range_unique
    · omega
    · simp only [Function.comp_apply, decide_eq_true_eq, true_and]
      exact hnz N (le_refl N)
    · intro i hi hqi
      simp only [Function.comp_apply, decide_eq_true_eq] at hqi
      exact unique_of_strictAnti (fun i => bdeg (G i)) N hstrict i (by omega) hqi.1
  rw [hfilt, List.map_singleton]

/-! #### Concrete chain data from `subresPRS` -/

/-- The concrete `subresPRS` chain element `chainG fuel P Q i := (goState fuel (P,Q,[-1],…) i).1`. -/
noncomputable def chainG (fuel : ℕ) (P Q : BPoly) (i : ℕ) : BPoly :=
  (goState fuel (P, Q, [-1], bdeg P - bdeg Q) i).1

/-- The concrete `subresPRS` β-divisor `chainBt fuel P Q l := goBeta …` at the `l`-th state. -/
noncomputable def chainBt (fuel : ℕ) (P Q : BPoly) (l : ℕ) : CPoly :=
  goBeta fuel (goState fuel (P, Q, [-1], bdeg P - bdeg Q) l).1
    (goState fuel (P, Q, [-1], bdeg P - bdeg Q) l).2.2.1
    (goState fuel (P, Q, [-1], bdeg P - bdeg Q) l).2.2.2

/-- The concrete pseudo-division quotient `chainS fuel P Q l` for the chain pair `(chainG l, chainG (l+1))`. -/
noncomputable def chainS (fuel : ℕ) (P Q : BPoly) (l : ℕ) : BPoly :=
  (toBPoly_bpsremainder fuel (chainG fuel P Q l) (chainG fuel P Q (l + 1))).choose

/-- The concrete pseudo-division content `chainC fuel P Q l` for the chain pair `(chainG l, chainG (l+1))`. -/
noncomputable def chainC (fuel : ℕ) (P Q : BPoly) (l : ℕ) : CPoly :=
  (toBPoly_bpsremainder fuel (chainG fuel P Q l) (chainG fuel P Q (l + 1))).choose_spec.choose

/-- `chainG fuel P Q 0 = P`. -/
@[simp] theorem chainG_zero (fuel : ℕ) (P Q : BPoly) : chainG fuel P Q 0 = P := rfl

/-- `chainG fuel P Q 1 = Q`. -/
@[simp] theorem chainG_one (fuel : ℕ) (P Q : BPoly) : chainG fuel P Q 1 = Q := by
  rw [chainG, goState_succ_fst]; rfl

/-- The pseudo-division identity holds for the concrete `chainS`/`chainC`. -/
theorem chain_hsc (fuel : ℕ) (P Q : BPoly) (l : ℕ) :
    Polynomial.C (toPoly (chainC fuel P Q l)) * toBPoly (chainG fuel P Q l)
      = toBPoly (chainS fuel P Q l) * toBPoly (chainG fuel P Q (l + 1))
        + toBPoly (bpsremainder fuel (chainG fuel P Q l) (chainG fuel P Q (l + 1))) :=
  (toBPoly_bpsremainder fuel (chainG fuel P Q l) (chainG fuel P Q (l + 1))).choose_spec.choose_spec

/-- The divided-PRS recurrence `chainG (l+2) = bdivC fuel (prem (chainG l) (chainG (l+1))) (chainBt l)`. -/
theorem chain_hG2 (fuel : ℕ) (P Q : BPoly) (l : ℕ) :
    chainG fuel P Q (l + 2)
      = bdivC fuel (bpsremainder fuel (chainG fuel P Q l) (chainG fuel P Q (l + 1)))
          (chainBt fuel P Q l) := by
  rw [chainG, goState_fst_add_two, chainBt]
  rfl

/-- The filter identity for the concrete chain:
`toBPoly (bsubresultantGcd fuel (deg (chainG (m+2))) P Q) = toBPoly (chainG (m+2))`. -/
theorem chain_hfilt (fuel : ℕ) (P Q : BPoly) (m : ℕ) (hfo : m + 2 + 1 < fuel)
    (hnz : ∀ i ≤ m + 2, ¬ bisZero (chainG fuel P Q i) = true)
    (hzN : bisZero (chainG fuel P Q (m + 2 + 1)) = true)
    (hstrict : ∀ i < m + 2, bdeg (chainG fuel P Q (i + 1)) < bdeg (chainG fuel P Q i)) :
    toBPoly (bsubresultantGcd fuel (toBPoly (chainG fuel P Q (m + 2))).natDegree P Q)
      = toBPoly (chainG fuel P Q (m + 2)) := by
  have hfil := subresPRS_filter_singleton fuel P Q (m + 2) hfo hnz hzN hstrict
  rw [bdeg_eq_natDegree] at hfil
  exact toBPoly_bsubresultantGcd_eq_of_filter_singleton fuel P Q (chainG fuel P Q) m hfil

/-! ### The clean concrete agreement: `lrtGcdCompute ↔ lrtSubresultant` for the real `subresPRS` -/

/-- The clean concrete `lrtGcdCompute ↔ lrtSubresultant` agreement for the real
`subresPRS fuel (liftCtoBPoly D) (bArgAmtD' A D)` chain: for a residue map `φ` killing `toPoly R`, under
the regularity inputs, `IsSimilar (Φ (lrtSubresultant A D j)) (Φ (toBPoly (lrtGcdCompute fuel j R A D)))`
over `S = ℚ[t]/(R)` at `j = (toBPoly (chainG (m+2))).natDegree`. -/
theorem lrtGcdCompute_isSimilar_lrtSubresultant_concrete {S : Type*} [CommRing S] [IsDomain S]
    (φ : ℚ[X] →+* S) (fuel : ℕ) (R A D : CPoly) (m : ℕ)
    (hRcn : cnorm R ≠ []) (hφR : φ (toPoly R) = 0)
    (hd0 : (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) 0)).natDegree
      = (toPoly D).natDegree)
    (hd1 : (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) 1)).natDegree
      = (toPoly D).natDegree - 1)
    -- singleton-filter inputs (chain nonzero through m+2, zero after, strict bdeg decrease, fuel)
    (hfoF : m + 2 + 1 < fuel)
    (hnzF : ∀ i ≤ m + 2, ¬ bisZero (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) i) = true)
    (hzNF : bisZero (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2 + 1)) = true)
    (hstrictF : ∀ i < m + 2,
      bdeg (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (i + 1))
        < bdeg (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) i))
    -- Collins β-divisibility + chain degree/nonzero regularity
    (hβcn : ∀ l ≤ m, cnorm (chainBt fuel (liftCtoBPoly D) (bArgAmtD' A D) l) ≠ [])
    (hdiv : ∀ l ≤ m, ∀ a ∈ bpsremainder fuel (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) l)
        (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (l + 1)),
      toPoly (cmod fuel a (chainBt fuel (liftCtoBPoly D) (bArgAmtD' A D) l)) = 0)
    (hc0 : ∀ l ≤ m, toPoly (chainC fuel (liftCtoBPoly D) (bArgAmtD' A D) l) ≠ 0)
    (hβ0 : ∀ l ≤ m, toPoly (chainBt fuel (liftCtoBPoly D) (bArgAmtD' A D) l) ≠ 0)
    (hlc : ∀ l ≤ m, (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (l + 1))).coeff
      (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (l + 1))).natDegree ≠ 0)
    (hcb : ∀ l ≤ m, (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (l + 2))).natDegree
      < (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (l + 1))).natDegree)
    (hjlt : ∀ l < m, (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree
      < (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (l + 2))).natDegree)
    (hQ : ∀ l ≤ m, (toBPoly (chainS fuel (liftCtoBPoly D) (bArgAmtD' A D) l)).natDegree
        + (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (l + 1))).natDegree
      ≤ (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) l)).natDegree)
    (hCne : toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2)) ≠ 0)
    -- bprimitivePartX content-exactness on the degree-j element
    (hprim : IsPrimitivePartXInput fuel
      (bsubresultantGcd fuel
        (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree
        (liftCtoBPoly D) (bArgAmtD' A D)))
    (hne : ∀ a b : ℚ[X], a ≠ 0 → b ≠ 0 →
        Polynomial.C a * lrtSubresultant (toPoly A) (toPoly D)
            (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree
          = Polynomial.C b * toBPoly (lrtSubresultantCompute fuel
            (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree A D)
        → φ a ≠ 0 ∧ φ b ≠ 0)
    {u : ℚ} (hu : u ≠ 0)
    (hgu : toPoly (cgcdExt fuel
        (blc (bredR fuel R (lrtSubresultantCompute fuel
          (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree A D))) R).1
      = Polynomial.C u)
    (hpz : ¬ bisZero (bredR fuel R
        (lrtSubresultantCompute fuel
          (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree A D)) = true) :
    IsSimilar ((Polynomial.mapRingHom φ)
        (lrtSubresultant (toPoly A) (toPoly D)
          (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree))
      ((Polynomial.mapRingHom φ) (toBPoly
        (lrtGcdCompute fuel
          (toBPoly (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree R A D))) := by
  have hfilt := chain_hfilt fuel (liftCtoBPoly D) (bArgAmtD' A D) m hfoF hnzF hzNF hstrictF
  have hchain : IsSubresPRSChainInput fuel
      (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D))
      (chainBt fuel (liftCtoBPoly D) (bArgAmtD' A D))
      (chainS fuel (liftCtoBPoly D) (bArgAmtD' A D))
      (chainC fuel (liftCtoBPoly D) (bArgAmtD' A D)) m := {
    exact_step := fun l hl => ⟨chain_hsc fuel (liftCtoBPoly D) (bArgAmtD' A D) l,
      hβcn l hl, hdiv l hl⟩
    next_eq := fun l _ => chain_hG2 fuel (liftCtoBPoly D) (bArgAmtD' A D) l
    scale_toPoly_ne := hc0
    beta_toPoly_ne := hβ0
    leading_coeff_ne := hlc
    degree_drop := hcb
    endpoint_degree_lt := hjlt
    quotient_degree_le := hQ
    endpoint_ne_zero := hCne }
  exact lrtGcdCompute_isSimilar_lrtSubresultant φ fuel R A D
    (chainG fuel (liftCtoBPoly D) (bArgAmtD' A D))
    (chainBt fuel (liftCtoBPoly D) (bArgAmtD' A D))
    (chainS fuel (liftCtoBPoly D) (bArgAmtD' A D))
    (chainC fuel (liftCtoBPoly D) (bArgAmtD' A D)) m
    hRcn hφR (chainG_zero fuel (liftCtoBPoly D) (bArgAmtD' A D))
    (chainG_one fuel (liftCtoBPoly D) (bArgAmtD' A D)) hd0 hd1
    hchain hfilt hprim hne hu hgu hpz

-- Restatement: the divided-PRS recurrence `hG2` holds DEFINITIONALLY for the concrete `subresPRS`
-- chain element `chainG` and β-divisor `chainBt` (no list/recurrence plumbing).
example (fuel : ℕ) (P Q : BPoly) (l : ℕ) :
    chainG fuel P Q (l + 2)
      = bdivC fuel (bpsremainder fuel (chainG fuel P Q l) (chainG fuel P Q (l + 1)))
          (chainBt fuel P Q l) :=
  chain_hG2 fuel P Q l

-- Restatement: the degree-`j` filter of the REAL `subresPRS` returns the chain's degree-`j` element —
-- the singleton-filter fact `hfilt` DISCHARGED from strict `bdeg` decrease (no hypothesis taken).
example (fuel : ℕ) (P Q : BPoly) (m : ℕ) (hfo : m + 2 + 1 < fuel)
    (hnz : ∀ i ≤ m + 2, ¬ bisZero (chainG fuel P Q i) = true)
    (hzN : bisZero (chainG fuel P Q (m + 2 + 1)) = true)
    (hstrict : ∀ i < m + 2, bdeg (chainG fuel P Q (i + 1)) < bdeg (chainG fuel P Q i)) :
    toBPoly (bsubresultantGcd fuel (toBPoly (chainG fuel P Q (m + 2))).natDegree P Q)
      = toBPoly (chainG fuel P Q (m + 2)) :=
  chain_hfilt fuel P Q m hfo hnz hzN hstrict


/-! ### The `AdjoinRoot.mk ↔ eval-at-root` bridge for `lrtSubresultant` -/

/-- For a field `K`, `f : K[X]`, `S = AdjoinRoot f`, `σ = of f`, `α = root f`, the lifted residue map
`Φ = mapRingHom (mk f)` sends `lrtSubresultant A D j` to
`(lrtSubresultant (A.map σ) (D.map σ) j).map (evalRingHom α)`. -/
theorem mapRingHom_mk_lrtSubresultant {K : Type*} [Field K] (f : K[X]) [Fact (Irreducible f)]
    (A D : K[X]) (j : ℕ) :
    (Polynomial.mapRingHom (AdjoinRoot.mk f)) (lrtSubresultant A D j)
      = (lrtSubresultant (A.map (AdjoinRoot.of f)) (D.map (AdjoinRoot.of f)) j).map
          (Polynomial.evalRingHom (AdjoinRoot.root f)) := by
  set σ : K →+* AdjoinRoot f := AdjoinRoot.of f with hσ
  set α : AdjoinRoot f := AdjoinRoot.root f with hα
  -- `mk f ∘ C = of f = σ` (the base-change embedding of constants).
  have hmkC : (AdjoinRoot.mk f).comp (C : K →+* K[X]) = σ := by
    rw [hσ, AdjoinRoot.of]
  -- the base change `σ = of f` is injective (field hom), so it preserves the `x`-degree parameters.
  have hσinj : Function.Injective σ := (AdjoinRoot.of f).injective
  have hdeg : (D.map σ).natDegree = D.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hσinj D
  -- LHS: push `mk f` through the subresultant determinant (`subresultant_map`), then through the operands.
  rw [Polynomial.coe_mapRingHom, lrtSubresultant, ← subresultant_map]
  -- RHS: specialize the base-changed `lrtSubresultant` at `α` (`lrtSubresultant_eval` shape).
  rw [lrtSubresultant_eval, hdeg]
  congr 1
  · -- `(D.map C).map (mk f) = (D.map σ).map (evalRingHom α … )`-side: both equal `D.map σ`.
    rw [Polynomial.map_map, hmkC]
  · -- the second LRT operand matches: `(A.map C − C X·D'.map C).map (mk f) = A.map σ − C α·(D.map σ)'`.
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_map, hmkC,
      Polynomial.map_C, AdjoinRoot.mk_X, derivative_map]

/-! ### A *correct* residue-map bridge for `IsSimilar` (replacing the over-strong universal `hne`)
The headline `lrtGcdCompute_isSimilar_lrtSubresultant` pushes a `ℚ[t]`-similarity through `φ` via
`isSimilar_mapRingHom`, whose hypothesis `hne` quantifies over **all** witness pairs `(a, b)` of the
similarity and demands `φ a ≠ 0 ∧ φ b ≠ 0`. That hypothesis is **unsatisfiable** whenever `φ` has a
nontrivial kernel: if `(a₀, b₀)` is one witness pair, so is `(q·a₀, q·b₀)` for any `q ≠ 0`, and taking
`q = f` (the modulus, which `φ` kills) gives a pair with `φ (q·a₀) = 0` — refuting `hne`. So `_concrete`
cannot be instantiated to its (true) conclusion through that path.

The fix: push through using only the **gcd-reduced** witness pair. For `φ = AdjoinRoot.mk f` with `f`
irreducible (`ℚ[X]` a Euclidean domain), if `IsSimilar A B` and the `φ`-images `Φ A`, `Φ B` are nonzero,
then `IsSimilar (Φ A) (Φ B)`: divide the witnesses `a, b` by `g = gcd a b` to get a coprime pair
`(a', b')` with the same relation; were `φ a' = 0` then (as `Φ B ≠ 0`, `S[x]` a domain) `φ b' = 0` too, so
`f ∣ a'` and `f ∣ b'`, forcing `IsUnit f` against irreducibility. Hence both `φ a', φ b' ≠ 0`, the genuine
residue-ring similarity witnesses. -/

/-- **The correct residue-map `IsSimilar` bridge**: for `φ : ℚ[X] →+* S` (`S` a domain) whose kernel is
exactly the multiples of an *irreducible* `f` (`hker : ∀ x, φ x = 0 ↔ f ∣ x`), a `ℚ[t]`-similarity
`IsSimilar A B` with **nonzero** `φ`-images `Φ A`, `Φ B` (`Φ = Polynomial.mapRingHom φ`) gives a residue-ring
similarity `IsSimilar (Φ A) (Φ B)`. Unlike `isSimilar_mapRingHom`'s universal `hne` (unsatisfiable when
`ker φ ≠ 0`), this uses the gcd-reduced (coprime) witness pair, whose `φ`-images cannot both vanish (else
`f` divides a coprime pair, hence is a unit). -/
theorem isSimilar_mapRingHom_of_irreducible {S : Type*} [CommRing S] [IsDomain S]
    (f : ℚ[X]) (hf : Irreducible f) (φ : ℚ[X] →+* S) (hker : ∀ x, φ x = 0 ↔ f ∣ x)
    {A B : (ℚ[X])[X]} (h : IsSimilar A B)
    (hA : (Polynomial.mapRingHom φ) A ≠ 0) (hB : (Polynomial.mapRingHom φ) B ≠ 0) :
    IsSimilar ((Polynomial.mapRingHom φ) A) ((Polynomial.mapRingHom φ) B) := by
  classical
  obtain ⟨a, b, ha, hb, hab⟩ := h
  set g := GCDMonoid.gcd a b with hg
  have hgne : g ≠ 0 := gcd_ne_zero_of_left ha
  set a' := a / g with ha'def
  set b' := b / g with hb'def
  have hcop : IsCoprime a' b' := isCoprime_div_gcd_div_gcd hb
  have hga : g * a' = a := EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_left a b)
  have hgb : g * b' = b := EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_right a b)
  have ha'ne : a' ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hga; exact ha hga.symm
  have hb'ne : b' ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hgb; exact hb hgb.symm
  -- the gcd-reduced relation `C a' * A = C b' * B`
  have hab' : Polynomial.C a' * A = Polynomial.C b' * B := by
    have hcancel : Polynomial.C g * (Polynomial.C a' * A) = Polynomial.C g * (Polynomial.C b' * B) := by
      rw [← mul_assoc, ← mul_assoc, ← Polynomial.C_mul, ← Polynomial.C_mul, hga, hgb, hab]
    have hCg : (Polynomial.C g : (ℚ[X])[X]) ≠ 0 := by
      simpa [Polynomial.C_eq_zero] using hgne
    exact mul_left_cancel₀ hCg hcancel
  -- φ-images of a', b' are nonzero (else f divides the coprime pair → f a unit)
  have hφa' : φ a' ≠ 0 := by
    intro h0
    have hfa' : f ∣ a' := (hker a').1 h0
    -- from C a' * A = C b' * B, φ: C(φ a')·ΦA = C(φ b')·ΦB ⟹ 0 = C(φ b')·ΦB ⟹ φ b' = 0
    have himg := congrArg (Polynomial.map φ) hab'
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C] at himg
    simp only [Polynomial.coe_mapRingHom] at hA hB
    rw [h0, map_zero, zero_mul] at himg
    have hφb' : φ b' = 0 := by
      by_contra hb0
      exact hB (by
        have : (Polynomial.C (φ b') : S[X]) ≠ 0 := by simpa [Polynomial.C_eq_zero] using hb0
        exact (mul_eq_zero.mp himg.symm).resolve_left this)
    have hfb' : f ∣ b' := (hker b').1 hφb'
    exact hf.not_isUnit (hcop.isUnit_of_dvd' hfa' hfb')
  have hφb' : φ b' ≠ 0 := by
    intro h0
    have hfb' : f ∣ b' := (hker b').1 h0
    have himg := congrArg (Polynomial.map φ) hab'
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C] at himg
    simp only [Polynomial.coe_mapRingHom] at hA hB
    rw [h0, map_zero, zero_mul] at himg
    have hφa' : φ a' = 0 := by
      by_contra ha0
      exact hA (by
        have : (Polynomial.C (φ a') : S[X]) ≠ 0 := by simpa [Polynomial.C_eq_zero] using ha0
        exact (mul_eq_zero.mp himg).resolve_left this)
    have hfa' : f ∣ a' := (hker a').1 hφa'
    exact hf.not_isUnit (hcop.isUnit_of_dvd' hfa' hfb')
  -- assemble the residue-ring similarity with witnesses (φ a', φ b')
  refine ⟨φ a', φ b', hφa', hφb', ?_⟩
  have hcong := congrArg (Polynomial.map φ) hab'
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C] at hcong
  simpa only [Polynomial.coe_mapRingHom] using hcong

end DeepWiki.SymbolicIntegration.Compute
