import DeepWiki.SymbolicIntegration.SubresultantCorrectness
import Sources.Doi_10_1007_b138171.Exercise22

/-! # Exercise 2.2 worked example: the LRT subresultant chain at squarefree index j = 1

The native_decide-validated concrete run of the LRT subresultant machinery on Bronstein
Exercise 2.2 (§2.9, p.72): discharging every chain-regularity hypothesis for A/D (data in
Compute.Exercise22) and reading off the IsSimilar closure over the residue ring
ℚ[t]/(R), R = cmonic cR22 irreducible. The general theory lives in
DeepWiki/SymbolicIntegration/SubresultantCorrectness. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### Exercise 2.2: the LRT subresultant chain at the squarefree index `j = 1` (§2.9, p.72)
The same closure for **Exercise 2.2** (`A = 8x⁹+…`, `D = x¹⁰−2x⁸−…`, both in `Exercise22Compute`). The
Rothstein–Trager resultant `R = res_x(D, A − t·D')` is the **degree-10** integer polynomial `cR22`, and
it is **squarefree** (`ex_2_2_resultant_squarefree`). So *every* residue has multiplicity `1`, the LRT
subresultant index is `j = 1`, and the per-residue gcd `S₁ = x + c₀(t)` is monic-linear in `x`
(`ex_2_2_S1_monic_linear`). The subresultant PRS has the **distinct** `x`-degrees `[10,9,…,1,0]` (indices
`0..10`), so the degree-`1` element is the chain index `m + 2 = 9` (`m = 7`); the regular LRT index is
`(DensePoly.toPoly (chain 60 hP hQ 9)).natDegree = 1`. We discharge every chain-regularity input over `ℚ[t]` by
`native_decide` (the `[10,…,0]` distinct-degree chain), mirroring Example 2.4.1 at the easier squarefree
multiplicity `1`. -/

/-- The Exercise 2.2 chain abbreviation: `hP = liftCtoBPoly cD22`, `hQ = bArgAmtD' cA22 cD22`. -/
private abbrev hP : GBPolyCore ℚ := liftCtoBPoly cD22
private abbrev hQ : GBPolyCore ℚ := bArgAmtD' cA22 cD22

/-- **The degree-1 element's `x`-degree is 1**: `(DensePoly.toPoly (chain 60 hP hQ 9)).natDegree = 1` (the regular
LRT index `j = m+2 = 9` ↦ degree `1`, the squarefree per-residue gcd `x + c₀(t)`). Via `DensePoly.cdegG_eq_natDegree`
and `native_decide` on `DensePoly.cdeg (chain … 9)`. -/
theorem natDegree_toBPoly_chainG9_ex22 :
    (DensePoly.toPoly (chain 60 hP hQ 9)).natDegree = 1 := by
  rw [← DensePoly.cdegG_eq_natDegree]
  show DensePoly.cdeg (goState 60 (hP, hQ, [-1], 1) 9).1 = 1
  native_decide

/-- `(toPoly cD22).natDegree = 10`: `D = x¹⁰−2x⁸−…` has degree 10 (via `DensePoly.cdegG_eq_natDegree`). -/
theorem natDegree_toPoly_cD22 : (toPoly cD22).natDegree = 10 := by
  rw [← DensePoly.cdegG_eq_natDegree]; decide

/-- **`hd0` for Ex 2.2**: `(DensePoly.toPoly (chain 60 hP hQ 0)).natDegree = (toPoly cD22).natDegree` (both 10). -/
theorem hd0_ex22 :
    (DensePoly.toPoly (chain 60 hP hQ 0)).natDegree = (toPoly cD22).natDegree := by
  rw [← DensePoly.cdegG_eq_natDegree, natDegree_toPoly_cD22]
  show DensePoly.cdeg (goState 60 (hP, hQ, [-1], 1) 0).1 = 10
  native_decide

/-- **`hd1` for Ex 2.2**: `(DensePoly.toPoly (chain 60 hP hQ 1)).natDegree = (toPoly cD22).natDegree − 1`
(both 9). -/
theorem hd1_ex22 :
    (DensePoly.toPoly (chain 60 hP hQ 1)).natDegree = (toPoly cD22).natDegree - 1 := by
  rw [← DensePoly.cdegG_eq_natDegree, natDegree_toPoly_cD22]
  show DensePoly.cdeg (goState 60 (hP, hQ, [-1], 1) 1).1 = 10 - 1
  native_decide

/-- **Chain nonzero through index 9**: `chain 0 … chain 9` are all nonzero (degrees `10,…,1`). -/
theorem chainG_ne_zero_ex22 :
    ∀ i ≤ 9, ¬ DensePoly.cisZero (chain 60 hP hQ i) = true := by
  simp only [chain]; native_decide

/-- **`hβcn` for Ex 2.2**: the β-divisors `chainBt 0 … chainBt 7` are nonzero `ℚ[t]` lists. -/
theorem hβcn_ex22 :
    ∀ l ≤ 7, cnorm (chainBt 60 hP hQ l) ≠ [] := by
  intro l hl; interval_cases l <;>
    · simp only [chainBt]; native_decide

/-- **`hβ0` for Ex 2.2**: the β-divisors `chainBt 0 … chainBt 7` read to nonzero `ℚ[t]` polynomials
(`toPoly ≠ 0`), via `DensePoly.cnormG_eq_nil_iff`. -/
theorem hβ0_ex22 :
    ∀ l ≤ 7, toPoly (chainBt 60 hP hQ l) ≠ 0 := by
  intro l hl h
  exact hβcn_ex22 l hl ((DensePoly.cnormG_eq_nil_iff _).mpr h)

/-- **`hdiv` for Ex 2.2** (Collins β-divisibility, concrete): `chainBt l` divides every `x`-coefficient
of the pseudo-remainder `prem (chain l) (chain (l+1))` exactly (`cmod` reads to 0), via
`DensePoly.cnormG_eq_nil_iff`. The decidable per-coefficient `cmod`-zero certificate, `native_decide`'d. -/
theorem hdiv_ex22 :
    ∀ l ≤ 7, ∀ a ∈ GBPolyCore.gbpsremainderCore 60 (chain 60 hP hQ l) (chain 60 hP hQ (l + 1)),
      toPoly (CPolyEuclidean.mod a (chainBt 60 hP hQ l)) = 0 := by
  intro l hl a ha
  rw [← DensePoly.cnormG_eq_nil_iff]
  revert a ha
  interval_cases l <;>
    · simp only [chainBt, chain]; native_decide

/-- **`hlc` for Ex 2.2**: the leading `x`-coefficient of `chain (l+1)` (`l ≤ 7`) is nonzero. -/
theorem hlc_ex22 :
    ∀ l ≤ 7, (DensePoly.toPoly (chain 60 hP hQ (l + 1))).coeff
      (DensePoly.toPoly (chain 60 hP hQ (l + 1))).natDegree ≠ 0 := by
  intro l hl
  rw [← DensePoly.cdegG_eq_natDegree, ← GBPolyCore.toPolyG_gblcCore_eq_coeff]
  exact toPolyG_gblcCore_ne_zero
    (Bool.eq_false_iff.mpr (chainG_ne_zero_ex22 (l + 1) (by omega)))

/-- **`hcb` for Ex 2.2**: the `x`-degrees strictly decrease (`chain (l+2)` below `chain (l+1)`,
`l ≤ 7`: `8<9, …, 1<2`), via `DensePoly.cdegG_eq_natDegree`. -/
theorem hcb_ex22 :
    ∀ l ≤ 7, (DensePoly.toPoly (chain 60 hP hQ (l + 2))).natDegree
      < (DensePoly.toPoly (chain 60 hP hQ (l + 1))).natDegree := by
  intro l hl
  rw [← DensePoly.cdegG_eq_natDegree, ← DensePoly.cdegG_eq_natDegree]
  interval_cases l <;>
    · simp only [chain]; native_decide

/-- **`hjlt` for Ex 2.2**: the degree-1 element `chain 9` is strictly below `chain (l+2)` for `l<7`
(`1 < 8,7,…,2`), via `DensePoly.cdegG_eq_natDegree`. -/
theorem hjlt_ex22 :
    ∀ l < 7, (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree
      < (DensePoly.toPoly (chain 60 hP hQ (l + 2))).natDegree := by
  intro l hl
  rw [← DensePoly.cdegG_eq_natDegree, ← DensePoly.cdegG_eq_natDegree]
  interval_cases l <;>
    · simp only [chain]; native_decide

/-- **`hCne` for Ex 2.2**: the degree-1 chain element `chain 9` is nonzero (`DensePoly.toPoly ≠ 0`), via
`DensePoly.cisZeroG_iff`. -/
theorem hCne_ex22 : DensePoly.toPoly (chain 60 hP hQ (7 + 2)) ≠ 0 := by
  rw [Ne, ← DensePoly.cisZeroG_iff]
  exact chainG_ne_zero_ex22 9 (by omega)

/-- **The degree-1 filter of `subresPRS` is `[chain 9]`** (the singleton-filter, by `native_decide`):
the `[10,9,…,1,0]` chain degrees are all distinct, so the degree-1 nonzero filter of `subresPRS 60 hP hQ`
is exactly the single element `chain 9`. Direct `native_decide` (both sides computable). -/
theorem subresPRS_filter_singleton_ex22 :
    (subresPRS 60 hP hQ).filter
        (fun R => decide (DensePoly.cdeg R = (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree ∧ ¬ DensePoly.cisZero R))
      = [chain 60 hP hQ (7 + 2)] := by
  rw [natDegree_toBPoly_chainG9_ex22]
  show (subresPRS 60 hP hQ).filter (fun R => decide (DensePoly.cdeg R = 1 ∧ ¬ DensePoly.cisZero R))
      = [(goState 60 (hP, hQ, [-1], 1) (7 + 2)).1]
  native_decide

/-- **`hfilt` for Ex 2.2**: the degree-1 filter of `bsubresultantGcd 60 1 hP hQ` returns `chain 9`
(under `DensePoly.toPoly`). From the singleton filter `subresPRS_filter_singleton_ex22` via
`toBPoly_bsubresultantGcd_eq_of_filter_singleton`. -/
theorem hfilt_ex22 :
    DensePoly.toPoly (bsubresultantGcd 60 (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree hP hQ)
      = DensePoly.toPoly (chain 60 hP hQ (7 + 2)) :=
  toBPoly_bsubresultantGcd_eq_of_filter_singleton 60 hP hQ (chain 60 hP hQ) 7
    subresPRS_filter_singleton_ex22

/-- **`hg` for Ex 2.2**: the `ℚ[t]`-content of the degree-1 raw subresultant is nonzero
(`¬ cisZero (GBPolyCore.gbcontentCore CPolyGcd.compute (bsubresultantGcd 60 1 hP hQ))`). -/
theorem hg_ex22 :
    ¬ cisZero (GBPolyCore.gbcontentCore CPolyGcd.compute (bsubresultantGcd 60
      (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree hP hQ)) = true := by
  rw [natDegree_toBPoly_chainG9_ex22]; native_decide

/-- **`hgcn` for Ex 2.2**: the `ℚ[t]`-content of the degree-1 raw subresultant has nonempty `cnorm`. -/
theorem hgcn_ex22 :
    cnorm (GBPolyCore.gbcontentCore CPolyGcd.compute (bsubresultantGcd 60
      (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree hP hQ)) ≠ [] := by
  rw [natDegree_toBPoly_chainG9_ex22]; native_decide

/-- **`hg0` for Ex 2.2**: the `ℚ[t]`-content reads to a nonzero `ℚ[t]` polynomial (`toPoly ≠ 0`), via
`DensePoly.cnormG_eq_nil_iff`. -/
theorem hg0_ex22 :
    toPoly (GBPolyCore.gbcontentCore CPolyGcd.compute (bsubresultantGcd 60
      (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree hP hQ)) ≠ 0 := by
  intro h; exact hgcn_ex22 ((DensePoly.cnormG_eq_nil_iff _).mpr h)

/-- **`hrem` for Ex 2.2**: the `ℚ[t]`-content divides every `x`-coefficient of the degree-1 raw
subresultant exactly (`cmod` reads to 0), via `DensePoly.cnormG_eq_nil_iff`. -/
theorem hrem_ex22 :
    ∀ a ∈ GBPolyCore.gbnormCore (bsubresultantGcd 60
        (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree hP hQ),
      toPoly (CPolyEuclidean.mod a (GBPolyCore.gbcontentCore CPolyGcd.compute (bsubresultantGcd 60
        (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree hP hQ))) = 0 := by
  intro a ha
  rw [← DensePoly.cnormG_eq_nil_iff]
  revert a ha
  rw [natDegree_toBPoly_chainG9_ex22]
  native_decide

/-! ### The `Classical.choose` content/quotient bounds for Ex 2.2 (`hc0`/`hQ`, degree argument)
`hc0` (content `chainC l` nonzero) and `hQ` (quotient-degree bound) mention the noncomputable
`Classical.choose` witnesses `chainC`/`chainS`, so are not directly `native_decide`'able. As for Example
2.4.1 they follow from the pseudo-division identity `chain_hsc` by a **degree argument** over the domain
`(ℚ[X])[X]`, using only computable chain facts (`chain l` nonzero with known `x`-degrees, β dividing the
pseudo-remainder). Here `l ≤ 7`, indices `l, l+1, l+2 ∈ {0,…,9}`. -/

/-- The chain elements `chain 0 … chain 9` are nonzero under `DensePoly.toPoly` (`i ≤ 9`), via
`DensePoly.cisZeroG_iff` and `chainG_ne_zero_ex22`. -/
theorem toBPoly_chainG_ne_zero_ex22 (i : ℕ) (hi : i ≤ 9) : DensePoly.toPoly (chain 60 hP hQ i) ≠ 0 := by
  rw [Ne, ← DensePoly.cisZeroG_iff]
  exact chainG_ne_zero_ex22 i hi

/-- **The pseudo-remainder is `C(toPoly βₗ)` times the next chain element** (Ex 2.2, `l ≤ 7`):
`DensePoly.toPoly (prem (chain l) (chain (l+1))) = C(toPoly (chainBt l)) · DensePoly.toPoly (chain (l+2))`. From
`chain_hG2` (the divided-step recurrence) and the β-divisor exact division `toBPoly_bdivC_exact`
(`hdiv_ex22`). -/
theorem toBPoly_prem_ex22 (l : ℕ) (hl : l ≤ 7) :
    DensePoly.toPoly (GBPolyCore.gbpsremainderCore 60 (chain 60 hP hQ l) (chain 60 hP hQ (l + 1)))
      = Polynomial.C (toPoly (chainBt 60 hP hQ l)) * DensePoly.toPoly (chain 60 hP hQ (l + 2)) := by
  have hexact := toBPoly_bdivC_exact
    (GBPolyCore.gbpsremainderCore 60 (chain 60 hP hQ l) (chain 60 hP hQ (l + 1))) (chainBt 60 hP hQ l)
    (hβcn_ex22 l hl) (fun a ha => hdiv_ex22 l hl a ha)
  rw [chain_hG2]
  exact hexact.symm

/-- The `x`-degree of the pseudo-remainder `prem (chain l) (chain (l+1))` equals
`deg (chain (l+2))` (`l ≤ 7`): the `C(toPoly βₗ)` constant factor does not change the `x`-degree
(`toPoly βₗ ≠ 0`), via `toBPoly_prem_ex22` and `natDegree_C_mul`. -/
theorem natDegree_toBPoly_prem_ex22 (l : ℕ) (hl : l ≤ 7) :
    (DensePoly.toPoly (GBPolyCore.gbpsremainderCore 60 (chain 60 hP hQ l) (chain 60 hP hQ (l + 1)))).natDegree
      = (DensePoly.toPoly (chain 60 hP hQ (l + 2))).natDegree := by
  rw [toBPoly_prem_ex22 l hl, Polynomial.natDegree_C_mul (hβ0_ex22 l hl)]

/-- **`hc0` for Ex 2.2**: the pseudo-division content `chainC l` (`l ≤ 7`) reads to a nonzero `ℚ[t]`
polynomial (`toPoly (chainC l) ≠ 0`). Degree argument over the domain `(ℚ[X])[X]` (identical to
`hc0_ex241`): if `toPoly (chainC l) = 0`, then `chain_hsc` gives `DensePoly.toPoly (chainS l)·DensePoly.toPoly (chain (l+1))
= − DensePoly.toPoly (prem)`; the RHS has `x`-degree `deg (chain (l+2)) < deg (chain (l+1))`, while the LHS has
`x`-degree `≥ deg (chain (l+1))` (if `chainS l ≠ 0`) or forces `chain (l+2) = 0` — both contradictions. -/
theorem hc0_ex22 : ∀ l ≤ 7, toPoly (chainC 60 hP hQ l) ≠ 0 := by
  intro l hl hc0
  have hsc := chain_hsc 60 hP hQ l
  rw [hc0, map_zero, zero_mul] at hsc
  have hprem := toBPoly_prem_ex22 l hl
  have hG1ne := toBPoly_chainG_ne_zero_ex22 (l + 1) (by omega)
  have hG2ne := toBPoly_chainG_ne_zero_ex22 (l + 2) (by omega)
  have hβne := hβ0_ex22 l hl
  have heq : DensePoly.toPoly (chainS 60 hP hQ l) * DensePoly.toPoly (chain 60 hP hQ (l + 1))
      = - DensePoly.toPoly (GBPolyCore.gbpsremainderCore 60 (chain 60 hP hQ l) (chain 60 hP hQ (l + 1))) := by
    linear_combination -hsc
  have hpremne : DensePoly.toPoly (GBPolyCore.gbpsremainderCore 60 (chain 60 hP hQ l) (chain 60 hP hQ (l + 1))) ≠ 0 := by
    rw [hprem]
    have hβdense : DensePoly.toPoly (chainBt 60 hP hQ l) ≠ 0 := by
      exact hβne
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hβdense) hG2ne
  by_cases hSne : DensePoly.toPoly (chainS 60 hP hQ l) = 0
  · rw [hSne, zero_mul, eq_comm, neg_eq_zero] at heq
    exact hpremne heq
  · have hdRHS : (- DensePoly.toPoly (GBPolyCore.gbpsremainderCore 60 (chain 60 hP hQ l) (chain 60 hP hQ (l + 1)))).natDegree
        = (DensePoly.toPoly (chain 60 hP hQ (l + 2))).natDegree := by
      rw [Polynomial.natDegree_neg, natDegree_toBPoly_prem_ex22 l hl]
    have hdLHS : (DensePoly.toPoly (chainS 60 hP hQ l) * DensePoly.toPoly (chain 60 hP hQ (l + 1))).natDegree
        = (DensePoly.toPoly (chainS 60 hP hQ l)).natDegree + (DensePoly.toPoly (chain 60 hP hQ (l + 1))).natDegree :=
      Polynomial.natDegree_mul hSne hG1ne
    have hdeg := congrArg Polynomial.natDegree heq
    rw [hdLHS, hdRHS] at hdeg
    have hcb := hcb_ex22 l hl
    omega

/-- **The `x`-degree of `chain (l+1)` is strictly below that of `chain l`** (Ex 2.2, `l ≤ 7`):
`deg (chain (l+1)) < deg (chain l)` (`9<10, …, 2<3`), via `DensePoly.cdegG_eq_natDegree`. -/
theorem natDegree_toBPoly_chainG_strictAnti_ex22 (l : ℕ) (hl : l ≤ 7) :
    (DensePoly.toPoly (chain 60 hP hQ (l + 1))).natDegree < (DensePoly.toPoly (chain 60 hP hQ l)).natDegree := by
  rw [← DensePoly.cdegG_eq_natDegree, ← DensePoly.cdegG_eq_natDegree]
  interval_cases l <;>
    · simp only [chain]; native_decide

/-- **`hQ` for Ex 2.2**: the pseudo-division quotient degree bound
`deg (chainS l) + deg (chain (l+1)) ≤ deg (chain l)` (`l ≤ 7`). Degree argument over `(ℚ[X])[X]` on
`chain_hsc` (with `hc0_ex22` giving the content nonzero) — identical to `hQ_ex241`. -/
theorem hQ_ex22 : ∀ l ≤ 7,
    (DensePoly.toPoly (chainS 60 hP hQ l)).natDegree + (DensePoly.toPoly (chain 60 hP hQ (l + 1))).natDegree
      ≤ (DensePoly.toPoly (chain 60 hP hQ l)).natDegree := by
  intro l hl
  have hsc := chain_hsc 60 hP hQ l
  have hGlne := toBPoly_chainG_ne_zero_ex22 l (by omega)
  have hG1ne := toBPoly_chainG_ne_zero_ex22 (l + 1) (by omega)
  have hcl := hc0_ex22 l hl
  have hpremdeg := natDegree_toBPoly_prem_ex22 l hl
  have hcb := hcb_ex22 l hl
  have hstrict := natDegree_toBPoly_chainG_strictAnti_ex22 l hl
  have hdLHS : (Polynomial.C (toPoly (chainC 60 hP hQ l)) * DensePoly.toPoly (chain 60 hP hQ l)).natDegree
      = (DensePoly.toPoly (chain 60 hP hQ l)).natDegree :=
    Polynomial.natDegree_C_mul hcl
  by_cases hSne : DensePoly.toPoly (chainS 60 hP hQ l) = 0
  · rw [hSne, Polynomial.natDegree_zero]
    omega
  · have hmuldeg : (DensePoly.toPoly (chainS 60 hP hQ l) * DensePoly.toPoly (chain 60 hP hQ (l + 1))).natDegree
        = (DensePoly.toPoly (chainS 60 hP hQ l)).natDegree + (DensePoly.toPoly (chain 60 hP hQ (l + 1))).natDegree :=
      Polynomial.natDegree_mul hSne hG1ne
    have hpremlt : (DensePoly.toPoly (GBPolyCore.gbpsremainderCore 60 (chain 60 hP hQ l) (chain 60 hP hQ (l + 1)))).natDegree
        < (DensePoly.toPoly (chainS 60 hP hQ l) * DensePoly.toPoly (chain 60 hP hQ (l + 1))).natDegree := by
      rw [hmuldeg, hpremdeg]; omega
    have hRHSdeg : (DensePoly.toPoly (chainS 60 hP hQ l) * DensePoly.toPoly (chain 60 hP hQ (l + 1))
          + DensePoly.toPoly (GBPolyCore.gbpsremainderCore 60 (chain 60 hP hQ l) (chain 60 hP hQ (l + 1)))).natDegree
        = (DensePoly.toPoly (chainS 60 hP hQ l) * DensePoly.toPoly (chain 60 hP hQ (l + 1))).natDegree :=
      Polynomial.natDegree_add_eq_left_of_natDegree_lt hpremlt
    have hdeg := congrArg Polynomial.natDegree hsc
    rw [hdLHS, hRHSdeg, hmuldeg] at hdeg
    omega

/-! ### The `ℚ[t]`-similarity `lrtSubresultant ∼ lrtSubresultantCompute` for Ex 2.2 (all chain hyps discharged) -/

/-- **`lrtSubresultant ∼ lrtSubresultantCompute` for Ex 2.2** (`ℚ[t]`-similarity, all chain hypotheses
discharged): the abstract LRT subresultant `lrtSubresultant (toPoly cA22) (toPoly cD22) 1` is `ℚ[t]`-similar
to the computable primitive LRT subresultant `DensePoly.toPoly (lrtSubresultantCompute 60 1 cA22 cD22)`. The full
chain agreement `isSimilar_lrtSubresultant_lrtSubresultantCompute` with every regularity hypothesis
discharged for the real `subresPRS` chain of Exercise 2.2 at the squarefree index `j = 1`. -/
theorem isSimilar_lrtSubresultant_lrtSubresultantCompute_ex22 :
    IsSimilar (lrtSubresultant (toPoly cA22) (toPoly cD22)
        (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree)
      (DensePoly.toPoly (lrtSubresultantCompute 60
        (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree cA22 cD22)) := by
  let hchain : IsSubresPRSChainInput 60 (chain 60 hP hQ) (chainBt 60 hP hQ)
      (chainS 60 hP hQ) (chainC 60 hP hQ) 7 := {
    exact_step := fun l hl => ⟨chain_hsc 60 hP hQ l, hβcn_ex22 l hl, hdiv_ex22 l hl⟩
    next_eq := fun l _ => chain_hG2 60 hP hQ l
    scale_toPoly_ne := hc0_ex22
    beta_toPoly_ne := hβ0_ex22
    leading_coeff_ne := hlc_ex22
    degree_drop := hcb_ex22
    endpoint_degree_lt := hjlt_ex22
    quotient_degree_le := hQ_ex22
    endpoint_ne_zero := hCne_ex22 }
  let hprim : IsPrimitivePartXInput
      (bsubresultantGcd 60 (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree hP hQ) := {
    content_not_zero := hg_ex22
    content_cnorm_ne := hgcn_ex22
    content_toPoly_ne := hg0_ex22
    exact_division := hrem_ex22 }
  exact isSimilar_lrtSubresultant_lrtSubresultantCompute 60 cA22 cD22 (chain 60 hP hQ)
    (chainBt 60 hP hQ) (chainS 60 hP hQ) (chainC 60 hP hQ) 7
    (chainG_zero 60 hP hQ) (chainG_one 60 hP hQ) hd0_ex22 hd1_ex22 hchain
    hfilt_ex22 hprim

/-! ### The residue ring `ℚ[t]/(R)` for Ex 2.2 and the `bmonicXmodR` unit regularity (`native_decide`)
The modulus is the monic primitive Rothstein–Trager resultant `R = cmonic cR22` (degree 10, squarefree).
The `bmonicXmodR` monic-in-`x` normalization needs the leading `x`-coefficient of the mod-`R`-reduced
primitive subresultant to be a **unit mod `R`**; concretely the extended-Euclidean gcd of that leading
coefficient with `R` reduces to a nonzero **constant** `u₂₂` (`native_decide`), so it is a unit. -/

/-- **`cnorm (cmonic cR22) ≠ []`** — the modulus `R = cmonic cR22` reads to a nonzero `ℚ[t]` polynomial. -/
theorem cnorm_cmonic_cR22_ne : cnorm (cmonic cR22) ≠ [] := by native_decide

/-- **The leading-`x`-coefficient mod-`R` gcd is a singleton constant** (Ex 2.2): the extended-Euclidean
gcd `.1` of the reduced primitive subresultant's leading `x`-coefficient with `R = cmonic cR22` is a
one-element list `[u₂₂]` (a nonzero constant in `ℚ[t]`), so the leading coefficient is a unit mod `R`.
The list and its head's nonvanishing are `native_decide` facts. -/
theorem cgcdWf_blc_bredR_singleton_ex22 :
    ∃ u : ℚ, u ≠ 0 ∧
      (CPolyEuclidean.gcdExt (GBPolyCore.gblcCore (bredR (cmonic cR22)
        (lrtSubresultantCompute 60 (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree cA22 cD22)))
        (cmonic cR22)).1
      = [u] := by
  rw [natDegree_toBPoly_chainG9_ex22]
  refine ⟨(CPolyEuclidean.gcdExt (GBPolyCore.gblcCore (bredR (cmonic cR22)
      (lrtSubresultantCompute 60 1 cA22 cD22))) (cmonic cR22)).1.headI, ?_, ?_⟩
  · native_decide
  · native_decide

/-- **`hgu` for Ex 2.2** (`bmonicXmodR` regularity): the leading-`x`-coefficient mod-`R` gcd reads to a
nonzero constant `C u₂₂` — so the leading coefficient is a unit mod `R = cmonic cR22`. From
`cgcdWf_blc_bredR_singleton_ex22` (`gcd = [u₂₂]`) and `toPoly [u₂₂] = C u₂₂`. -/
theorem hgu_ex22 :
    ∃ u : ℚ, u ≠ 0 ∧
      toPoly (CPolyEuclidean.gcdExt (GBPolyCore.gblcCore (bredR (cmonic cR22)
        (lrtSubresultantCompute 60 (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree cA22 cD22)))
        (cmonic cR22)).1
      = Polynomial.C u := by
  obtain ⟨u, hu, hgcd⟩ := cgcdWf_blc_bredR_singleton_ex22
  exact ⟨u, hu, by
    rw [hgcd]
    simp [DensePoly.toPolyG_cons, DensePoly.toPolyG_nil]⟩

/-- **`hpz` for Ex 2.2**: the mod-`R` reduction of the primitive degree-1 subresultant is nonzero
(`¬ DensePoly.cisZero (bredR (cmonic cR22) (lrtSubresultantCompute 60 1 cA22 cD22))`). -/
theorem hpz_ex22 :
    ¬ DensePoly.cisZero (bredR (cmonic cR22)
        (lrtSubresultantCompute 60 (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree cA22 cD22)) = true := by
  rw [natDegree_toBPoly_chainG9_ex22]; native_decide

/-- **`Φ (DensePoly.toPoly (lrtGcdCompute …)) ≠ 0`** (Ex 2.2): the `φ`-image of the computable LRT log argument is
nonzero — its degree-1 `x`-coefficient is `φ (toPoly [1]) = φ 1 = 1 ≠ 0` (the engine's output
`S₁ = x + c₀(t)` is monic in `x`, leading coefficient `[1]`, `ex_2_2_S1_monic_linear`). Works for any ring
hom `φ : ℚ[X] →+* S` into a nonzero ring. -/
theorem mapRingHom_φ_toBPoly_lrtGcdCompute_ne_zero_ex22 {S : Type*} [CommRing S] [Nontrivial S]
    (φ : ℚ[X] →+* S) :
    (Polynomial.mapRingHom φ) (DensePoly.toPoly
      (lrtGcdCompute 60 (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree (cmonic cR22) cA22 cD22)) ≠ 0 := by
  rw [natDegree_toBPoly_chainG9_ex22]
  intro h
  have hcoeff : ((Polynomial.mapRingHom φ) (DensePoly.toPoly
      (lrtGcdCompute 60 1 (cmonic cR22) cA22 cD22))).coeff 1 = 0 := by rw [h]; simp
  rw [Polynomial.coe_mapRingHom, Polynomial.coeff_map, DensePoly.toPolyG_coeff_dense] at hcoeff
  -- the degree-1 `x`-coefficient of `lrtGcdCompute … = [c₀, [1]]` is `toPoly [1] = 1`, `φ 1 = 1 ≠ 0`
  rw [show (lrtGcdCompute 60 1 (cmonic cR22) cA22 cD22).getD 1 [] = [1] by native_decide] at hcoeff
  rw [show toPoly ([1] : DensePoly ℚ) = 1 by
    simp [DensePoly.toPolyG_cons, DensePoly.toPolyG_nil], map_one] at hcoeff
  exact one_ne_zero hcoeff

/-! ### Closing Exercise 2.2: the residue ring `ℚ[t]/(R)`, `R = cmonic cR22` irreducible
`R = cmonic cR22` is a degree-10 **squarefree** polynomial; it is in fact **irreducible over `ℚ`** (it
is irreducible mod the prime `37` — a single degree-10 factor in `𝔽₃₇[t]` — and irreducibility mod a
prime not dividing the leading coefficient implies irreducibility over `ℚ`). So `S = AdjoinRoot (toPoly
(cmonic cR22)) = ℚ[t]/(R)` is a **degree-10 field**, hence a domain, over which the LRT log argument is
normalized. Because `R` is squarefree, *every* residue has multiplicity `1` — exactly the LRT index
`j = 1` — so no multiplicity argument beyond the regular-index nonvanishing is needed.

Proving the degree-10 irreducibility *inside Lean* requires a reduction-mod-`p` irreducibility certificate
(`Monic.irreducible_of_irreducible_map` plus `Irreducible` over `𝔽₃₇[t]` for a degree-10 polynomial), which
has no `native_decide`-able decision procedure in Mathlib; it is the one mathematics-grade input taken as a
hypothesis (`hirr`), together with the residue non-vanishing `hLne` (mirroring Example 2.4.1's `hLne`). -/

/-- **Exercise 2.2's LRT closure**, modulo the two mathematics-grade inputs: given that the monic primitive
Rothstein–Trager resultant `R = cmonic cR22` is **irreducible over `ℚ`** (`hirr` — true; `R` is irreducible
mod `37`), so `S = ℚ[t]/(R)` is a field, and given the residue non-vanishing `hLne` (`Φ (lrtSubresultant
A D 1) ≠ 0`, `Φ = mapRingHom (mk R)`), the `Φ`-image of the abstract LRT subresultant
`lrtSubresultant (toPoly cA22) (toPoly cD22) 1` is `IsSimilar` over `ℚ[t]/(R)` to the `Φ`-image of the
computable LRT log argument `DensePoly.toPoly (lrtGcdCompute 60 1 R cA22 cD22) = x + c₀(t)`. So the engine's
degree-1 squarefree output **is** the honest LRT subresultant of Exercise 2.2, up to a residue-ring unit.
The hypothesis-free `ℚ[t]`-similarity (`isSimilar_lrtSubresultant_lrtSubresultantCompute_ex22`) is pushed
through the residue map by the *correct* bridge `isSimilar_mapRingHom_of_irreducible`, then chained with the
`bmonicXmodR` unit bridge. -/
theorem lrtGcdCompute_ex22_isSimilar_lrtSubresultant
    (hirr : Irreducible (toPoly (cmonic cR22)))
    (hLne : (Polynomial.mapRingHom (AdjoinRoot.mk (toPoly (cmonic cR22))))
      (lrtSubresultant (toPoly cA22) (toPoly cD22)
        (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree) ≠ 0) :
    IsSimilar ((Polynomial.mapRingHom (AdjoinRoot.mk (toPoly (cmonic cR22))))
        (lrtSubresultant (toPoly cA22) (toPoly cD22)
          (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree))
      ((Polynomial.mapRingHom (AdjoinRoot.mk (toPoly (cmonic cR22)))) (DensePoly.toPoly
        (lrtGcdCompute 60 (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree (cmonic cR22) cA22 cD22))) := by
  haveI : Fact (Irreducible (toPoly (cmonic cR22))) := ⟨hirr⟩
  set φ : ℚ[X] →+* AdjoinRoot (toPoly (cmonic cR22)) := AdjoinRoot.mk (toPoly (cmonic cR22)) with hφ
  have hφR : φ (toPoly (cmonic cR22)) = 0 := AdjoinRoot.mk_self
  have hφker : ∀ x, φ x = 0 ↔ toPoly (cmonic cR22) ∣ x := fun x => AdjoinRoot.mk_eq_zero
  -- Φ L ∼ Φ M via the correct bridge (R irreducible)
  have hMne : (Polynomial.mapRingHom φ) (DensePoly.toPoly (lrtSubresultantCompute 60
      (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree cA22 cD22)) ≠ 0 := by
    obtain ⟨u, hu, hgu⟩ := hgu_ex22
    obtain ⟨hbridge, _⟩ := mapRingHom_toPolyG_bmonicXmodR φ (cmonic cR22)
      (lrtSubresultantCompute 60 (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree cA22 cD22)
      cnorm_cmonic_cR22_ne hφR hu hgu hpz_ex22
    intro h
    apply mapRingHom_φ_toBPoly_lrtGcdCompute_ne_zero_ex22 φ
    rw [lrtGcdCompute, hbridge, h, mul_zero]
  have hLM : IsSimilar
      ((Polynomial.mapRingHom φ) (lrtSubresultant (toPoly cA22) (toPoly cD22)
        (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree))
      ((Polynomial.mapRingHom φ) (DensePoly.toPoly (lrtSubresultantCompute 60
        (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree cA22 cD22))) :=
    isSimilar_mapRingHom_of_irreducible (toPoly (cmonic cR22)) hirr φ hφker
      isSimilar_lrtSubresultant_lrtSubresultantCompute_ex22 hLne hMne
  -- Φ M ∼ Φ M_gcd via the bmonicXmodR unit bridge
  obtain ⟨u, hu, hgu⟩ := hgu_ex22
  obtain ⟨hbridge, hunit⟩ := mapRingHom_toPolyG_bmonicXmodR φ (cmonic cR22)
    (lrtSubresultantCompute 60 (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree cA22 cD22)
    cnorm_cmonic_cR22_ne hφR hu hgu hpz_ex22
  have hMMgcd : IsSimilar
      ((Polynomial.mapRingHom φ) (DensePoly.toPoly (lrtSubresultantCompute 60
        (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree cA22 cD22)))
      ((Polynomial.mapRingHom φ) (DensePoly.toPoly
        (lrtGcdCompute 60 (DensePoly.toPoly (chain 60 hP hQ (7 + 2))).natDegree (cmonic cR22) cA22 cD22))) :=
    isSimilar_of_unit_mul hunit (by rw [lrtGcdCompute]; exact hbridge)
  exact hLM.trans hMMgcd

/-- **The engine's output is the honest LRT subresultant of Exercise 2.2** (§2.9, p.72), at the index `j`
spelled `1`: over the residue field `ℚ[t]/(R)` (`R = cmonic cR22` irreducible), the `Φ`-image of the
abstract `lrtSubresultant (toPoly cA22) (toPoly cD22) 1` is `IsSimilar` to the `Φ`-image of the engine's
computed log argument `cS1_22 = lrtGcdCompute 60 1 R cA22 cD22 = x + c₀(t)` (`ex_2_2_S1_monic_linear`).
Restates `lrtGcdCompute_ex22_isSimilar_lrtSubresultant` with the index rewritten `(DensePoly.toPoly (chain 60 hP hQ
9)).natDegree = 1` (`natDegree_toBPoly_chainG9_ex22`). The two hypotheses are the `ℚ`-irreducibility of the
degree-10 squarefree resultant `R` and the residue non-vanishing of the noncomputable subresultant. -/
example
    (hirr : Irreducible (toPoly (cmonic cR22)))
    (hLne : (Polynomial.mapRingHom (AdjoinRoot.mk (toPoly (cmonic cR22))))
      (lrtSubresultant (toPoly cA22) (toPoly cD22) 1) ≠ 0) :
    IsSimilar ((Polynomial.mapRingHom (AdjoinRoot.mk (toPoly (cmonic cR22))))
        (lrtSubresultant (toPoly cA22) (toPoly cD22) 1))
      ((Polynomial.mapRingHom (AdjoinRoot.mk (toPoly (cmonic cR22)))) (DensePoly.toPoly cS1_22)) := by
  have h := lrtGcdCompute_ex22_isSimilar_lrtSubresultant hirr
    (by rw [natDegree_toBPoly_chainG9_ex22]; exact hLne)
  rw [natDegree_toBPoly_chainG9_ex22] at h
  exact h


end DeepWiki.SymbolicIntegration.Compute
