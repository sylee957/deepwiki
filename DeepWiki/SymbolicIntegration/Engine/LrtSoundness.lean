import DeepWiki.SymbolicIntegration.Engine.LrtIntegrate
import DeepWiki.SymbolicIntegration.Engine.IntegrateTowerCorrectG
import DeepWiki.SymbolicIntegration.Engine.SubresultantTowerSpec
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.LrtGeneralDerivation
import DeepWiki.SymbolicIntegration.Engine.ResidueMatchSoundness
import DeepWiki.SymbolicIntegration.SpecialFirstKind
import DeepWiki.SymbolicIntegration.Engine.Hermite.ValuationTower
import DeepWiki.SymbolicIntegration.Engine.ResidueResultantTowerSpec

/-! # Symbolic-log soundness for the root-free LRT reduced integrator

`IsIntegralResultLrt` is the soundness contract for `cIntegrateReducedLrt`'s **symbolic** log part
`[(Rᵢ, Sᵢ)]`, denoting `Σᵢ Σ_{Rᵢ(c)=0} c·(Δ Sᵢ(c,t))/Sᵢ(c,t)`. To handle **algebraic** residues without
building a `Differential (AlgebraicClosure K)` instance, it is stated over an arbitrary differential
extension `E` of `K = CFieldSpec.K α` in which every `Rᵢ` splits (the descent vehicle): `extendDeriv` /
`Differential.implicitDeriv` are already generic over any such `E`. See `docs/g5-lrt-soundness.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

/-- The coefficient-list polynomial `Σ_{(a,k) ∈ l.zipIdx s} C a · Xᵏ = Σ_{i<len} C(l[i])·X^{s+i}`. -/
theorem zipIdx_C_mul_X_pow_sum_eq {R : Type*} [Semiring R] (l : List R) (s : ℕ) :
    ((l.zipIdx s).map (fun p : R × ℕ => Polynomial.C p.1 * Polynomial.X ^ p.2)).sum
      = ∑ i ∈ Finset.range l.length, Polynomial.C (l.getD i 0) * Polynomial.X ^ (s + i) := by
  induction l generalizing s with
  | nil => simp
  | cons a t ih =>
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, ih (s + 1), List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
    rw [add_comm (Polynomial.C a * Polynomial.X ^ s)]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show s + 1 + i = s + (i + 1) from by omega]

/-- The `n`-th coefficient of the coefficient-list polynomial is `l.getD n 0`. -/
theorem zipIdx_C_mul_X_pow_sum_coeff {R : Type*} [Semiring R] (l : List R) (n : ℕ) :
    (((l.zipIdx).map (fun p : R × ℕ => Polynomial.C p.1 * Polynomial.X ^ p.2)).sum).coeff n
      = l.getD n 0 := by
  rw [zipIdx_C_mul_X_pow_sum_eq l 0]
  simp only [Nat.zero_add, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
  by_cases hn : n < l.length
  · rw [if_pos hn]
  · rw [if_neg hn, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

section Ext

variable {E : Type*} [Field E] [Algebra (CFieldSpec.K α) E]

/-- Base-change of a `K`-polynomial to `RatFunc E` (`K = CFieldSpec.K α`). -/
noncomputable def amGExt (p : (CFieldSpec.K α)[X]) : RatFunc E :=
  algebraMap E[X] (RatFunc E) (p.map (algebraMap (CFieldSpec.K α) E))

/-- The symbolic log argument `Sᵢ` (a list of `z`-polynomials, one per `t`-power) evaluated at a residue
`c ∈ E` and **monic-normalized in `t`**: the raw `E[t]` polynomial `Σₖ (Sᵢ[k] at z=c)·tᵏ` divided by its
leading `t`-coefficient. The monic normalization is required for tower soundness: the raw subresultant
`Sᵢ(c) = sᵢ(c)·(monic gcd)` carries a
leading-coefficient unit `sᵢ(c)` whose *tower* log-derivative `D_base(sᵢ(c))/sᵢ(c)` does **not** vanish
(unlike the formal `d/dx` case), so the raw argument gives a spurious extra term. Dividing by the leading
coefficient turns `Sᵢ(c)` into the **monic gcd**, whose log-derivative is exactly the RT residue term. -/
noncomputable def evalLrtArg (Si : List (DensePoly α)) (c : E) : E[X] :=
  let raw : E[X] := (Si.zipIdx.map (fun p =>
    C ((toPoly p.1).eval₂ (algebraMap (CFieldSpec.K α) E) c) * X ^ p.2)).sum
  raw * C raw.leadingCoeff⁻¹

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **`evalLrtArg`'s raw sum is the base-changed abstract polynomial.** Given the coefficient identity
`toPoly (Sᵢ.getD n []) = P.coeff n` (P the abstract `lrtSubresultantGen`), the computable raw sum equals
`P.map (eval₂RingHom (algebraMap K E) c)` (`= S`, the base-changed subresultant at `z = c`). -/
theorem raw_eq_map (Si : List (DensePoly α)) (c : E) (P : ((CFieldSpec.K α)[X])[X])
    (hg4c : ∀ n, toPoly (Si.getD n []) = P.coeff n) :
    (Si.zipIdx.map (fun p => Polynomial.C ((toPoly p.1).eval₂ (algebraMap (CFieldSpec.K α) E) c)
        * Polynomial.X ^ p.2)).sum
      = P.map (Polynomial.eval₂RingHom (algebraMap (CFieldSpec.K α) E) c) := by
  have hcommute : (Si.zipIdx.map (fun p => Polynomial.C ((toPoly p.1).eval₂
        (algebraMap (CFieldSpec.K α) E) c) * Polynomial.X ^ p.2))
      = (Si.map (fun sk => (toPoly sk).eval₂ (algebraMap (CFieldSpec.K α) E) c)).zipIdx.map
        (fun p : E × ℕ => Polynomial.C p.1 * Polynomial.X ^ p.2) := by
    rw [List.zipIdx_map, List.map_map]; rfl
  rw [hcommute]
  ext n
  rw [zipIdx_C_mul_X_pow_sum_coeff, Polynomial.coeff_map, Polynomial.coe_eval₂RingHom, ← hg4c n,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases Si[n]? with
  | none => simp [toPolyG_nil]
  | some sk => simp

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **The monic log argument is the residue-pole product.** Given the coefficient identity and that
the base-changed subresultant `S` is similar to `∏_{β}(t−β)`, `evalLrtArg Sᵢ c = ∏_{β}(t−β)`. Composes
`raw_eq_map` (`raw = S`) with `monicNormalize_eq_of_isSimilar_prod` (`monic(S) = ∏`). -/
theorem evalLrtArg_eq_prod (Si : List (DensePoly α)) (c : E) (A D B : (CFieldSpec.K α)[X]) (j : ℕ)
    (poles : Multiset E) (hφ : Function.Injective (algebraMap (CFieldSpec.K α) E))
    (hg4c : ∀ n, toPoly (Si.getD n []) = (lrtSubresultantGen A D B j).coeff n)
    (hsim : IsSimilar (subresultant (D.map (algebraMap (CFieldSpec.K α) E))
        (A.map (algebraMap (CFieldSpec.K α) E)
          - Polynomial.C c * B.map (algebraMap (CFieldSpec.K α) E)) D.natDegree (D.natDegree - 1) j)
      (poles.map (fun β => Polynomial.X - Polynomial.C β)).prod) :
    evalLrtArg Si c = (poles.map (fun β => Polynomial.X - Polynomial.C β)).prod := by
  have hraw : (Si.zipIdx.map (fun p => Polynomial.C
        ((toPoly p.1).eval₂ (algebraMap (CFieldSpec.K α) E) c) * Polynomial.X ^ p.2)).sum
      = subresultant (D.map (algebraMap (CFieldSpec.K α) E))
        (A.map (algebraMap (CFieldSpec.K α) E)
          - Polynomial.C c * B.map (algebraMap (CFieldSpec.K α) E)) D.natDegree (D.natDegree - 1) j := by
    rw [raw_eq_map Si c (lrtSubresultantGen A D B j) hg4c,
      lrtSubresultantGen_map_eval₂ _ A D B c j hφ]
  simp only [evalLrtArg]
  rw [hraw]
  exact monicNormalize_eq_of_isSimilar_prod poles hsim

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **The pure-single-log branch (`i = deg Dstar`) evaluates to `Dstar` itself.** For the const-embedded `Dstar`
(`Dstar.map (·::[])` — a `t`-polynomial with *constant* `z`-coefficients, no residue dependence), `evalLrtArg`'s
raw sum is `Dstar_E`, and when `Dstar_E` is monic the monic normalization is trivial. This is the log argument
of a single pure log `c·D(Dstar)/Dstar` (all poles share one residue) — the `i = n` branch of `cLrtLogArg`. -/
theorem evalLrtArg_const_embed_eq (Dstar : DensePoly α) (c : E)
    (hmonic : ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E)).Monic) :
    evalLrtArg (Dstar.map (fun x => ([x] : DensePoly α))) c
      = (toPoly Dstar).map (algebraMap (CFieldSpec.K α) E) := by
  have hg4c : ∀ n, toPoly ((Dstar.map (fun x => ([x] : DensePoly α))).getD n [])
      = ((toPoly Dstar).map C).coeff n := by
    intro n
    rw [Polynomial.coeff_map, toPolyG_coeff, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getD_eq_getElem?_getD]
    cases h : Dstar[n]? with
    | none => simp [toPolyG_nil, CFieldSpec.toK_zero]
    | some a => simp [toPolyG_cons, toPolyG_nil]
  have hraw : ((Dstar.map (fun x => ([x] : DensePoly α))).zipIdx.map (fun p =>
        C ((toPoly p.1).eval₂ (algebraMap (CFieldSpec.K α) E) c) * X ^ p.2)).sum
      = (toPoly Dstar).map (algebraMap (CFieldSpec.K α) E) := by
    rw [raw_eq_map (Dstar.map (fun x => ([x] : DensePoly α))) c ((toPoly Dstar).map C) hg4c,
      Polynomial.map_map]
    have hcomp : (Polynomial.eval₂RingHom (algebraMap (CFieldSpec.K α) E) c).comp
        (C : (CFieldSpec.K α) →+* (CFieldSpec.K α)[X]) = algebraMap (CFieldSpec.K α) E := by
      ext k; simp
    rw [hcomp]
  simp only [evalLrtArg]
  rw [hraw, hmonic.leadingCoeff, inv_one, map_one, mul_one]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **The engine's parametric subresultant gives the residue-pole product.** With coefficients certified by
`CPolySubresultant.toPoly_parametric_getD`, `evalLrtArg (CPolySubresultant.parametric Dstar hNum Dd (cdeg Dstar)(cdeg Dd) j) c
= ∏_{β}(t−β)`, given `deg Dd = deg Dstar − 1` and `IsSimilar S (∏)`. -/
theorem evalLrtArg_cSubresultantParam_eq_prod [CharZero (CFieldSpec.K α)]
    (Dstar hNum Dd : DensePoly α) (c : E) (j : ℕ) (poles : Multiset E)
    (hm : cdeg Dd = cdeg Dstar - 1)
    (hφ : Function.Injective (algebraMap (CFieldSpec.K α) E))
    (hsim : IsSimilar (subresultant ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E))
        ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)
          - Polynomial.C c * (toPoly Dd).map (algebraMap (CFieldSpec.K α) E))
        (toPoly Dstar).natDegree ((toPoly Dstar).natDegree - 1) j)
      (poles.map (fun β => Polynomial.X - Polynomial.C β)).prod) :
    evalLrtArg (CPolySubresultant.parametric Dstar hNum Dd (cdeg Dstar) (cdeg Dd) j) c
      = (poles.map (fun β => Polynomial.X - Polynomial.C β)).prod :=
  evalLrtArg_eq_prod _ c (toPoly hNum) (toPoly Dstar) (toPoly Dd) j poles hφ
    (fun n => CPolySubresultant.toPoly_parametric_getD Dstar hNum Dd j n hm) hsim

open Classical in
omit [CDiffField α] [CDiffFieldSpec α] in
/-- **`hfac` core: the entry log argument is the residue-`c` pole product.** For `Dstar_E = nodal allpoles`
(split) and the entry index `i = rootMultiplicity c` in the residue resultant (the Yun index ↔ fiber-size
match), `evalLrtArg (CPolySubresultant.parametric … i) c = ∏_{β ∈ allpoles, res β = c}(t − β)`. Chains
`evalLrtArg_cSubresultantParam_eq_prod` with `isSimilar_subresultant_prod`. -/
theorem evalLrtArg_eq_fiber_prod [CharZero (CFieldSpec.K α)] [IsAlgClosed E]
    (Dstar hNum Dd : DensePoly α) (allpoles : Finset E) (c : E) (i : ℕ)
    (hm : cdeg Dd = cdeg Dstar - 1)
    (hsplit : (toPoly Dstar).map (algebraMap (CFieldSpec.K α) E) = Lagrange.nodal allpoles id)
    (hB : ∀ β ∈ allpoles, ((toPoly Dd).map (algebraMap (CFieldSpec.K α) E)).eval β ≠ 0)
    (hA : ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)).natDegree
        < (Lagrange.nodal allpoles id).natDegree)
    (hB_deg : ((toPoly Dd).map (algebraMap (CFieldSpec.K α) E)).natDegree
        ≤ (Lagrange.nodal allpoles id).natDegree - 1)
    (hindex : i = (rtResultantGen ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E))
        (Lagrange.nodal allpoles id) ((toPoly Dd).map (algebraMap (CFieldSpec.K α) E))).rootMultiplicity c)
    (hi : i < (Lagrange.nodal allpoles id).natDegree) :
    evalLrtArg (CPolySubresultant.parametric Dstar hNum Dd (cdeg Dstar) (cdeg Dd) i) c
      = ((allpoles.filter (fun β => ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)).eval β
            / ((toPoly Dd).map (algebraMap (CFieldSpec.K α) E)).eval β = c)).val.map
          (fun β => X - C β)).prod := by
  refine evalLrtArg_cSubresultantParam_eq_prod Dstar hNum Dd c i
    ((allpoles.filter (fun β => ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)).eval β
        / ((toPoly Dd).map (algebraMap (CFieldSpec.K α) E)).eval β = c)).val) hm
    (algebraMap (CFieldSpec.K α) E).injective ?_
  rw [hsplit, hindex]
  have hdeg : (toPoly Dstar).natDegree = (Lagrange.nodal allpoles id).natDegree := by
    rw [← natDegree_map_eq_of_injective (algebraMap (CFieldSpec.K α) E).injective (toPoly Dstar),
      hsplit]
  have hsim := isSimilar_subresultant_prod ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E))
    ((toPoly Dd).map (algebraMap (CFieldSpec.K α) E)) allpoles c hB hA hB_deg (hindex ▸ hi)
  rw [Finset.prod_eq_multiset_prod] at hsim
  convert hsim using 2
  all_goals omega

variable [Differential E] [Algebra ℚ E]

/-- The `E`-tower derivation on `RatFunc E`: `extendDeriv` of `implicitDeriv (Dt base-changed to E)`. The
generic (any differential extension `E`) analogue of `towerFractionFieldDeriv`. -/
noncomputable def towerDerivExt (Dt : DensePoly α) : Derivation ℤ (RatFunc E) (RatFunc E) :=
  extendDeriv (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E)))

omit [CDiffField α] [CDiffFieldSpec α] [Differential E] [Algebra ℚ E] in
/-- The base-change of a nonzero `K`-polynomial to `E` stays nonzero (`algebraMap K E` is an injective field
hom), so `Polynomial.mapRingHom` preserves nonzerodivisors — the hypothesis of `RatFunc.mapRingHom`. -/
theorem ratFuncBaseChange_nonZeroDivisors :
    nonZeroDivisors ((CFieldSpec.K α)[X]) ≤ Submonoid.comap
      (Polynomial.mapRingHom (algebraMap (CFieldSpec.K α) E)) (nonZeroDivisors (E[X])) := by
  intro p hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero] at *
  simpa [Polynomial.mapRingHom, Polynomial.map_ne_zero_iff
    (algebraMap (CFieldSpec.K α) E).injective] using hp

variable (E) in
/-- **The base-change ring hom** `RatFunc K →+* RatFunc E` induced by `algebraMap K E` (`K = CFieldSpec.K α`).
Sends `am p ↦ amGExt p`; used to transfer the `K`-level Hermite field identity to `E`. -/
noncomputable def ratFuncBaseChange : RatFunc (CFieldSpec.K α) →+* RatFunc E :=
  RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap (CFieldSpec.K α) E))
    ratFuncBaseChange_nonZeroDivisors

omit [CDiffField α] [CDiffFieldSpec α] [Differential E] [Algebra ℚ E] in
/-- The base-change hom sends `am p / am q ↦ amGExt p / amGExt q`. -/
theorem ratFuncBaseChange_amG_div (p q : (CFieldSpec.K α)[X]) :
    ratFuncBaseChange E (am α p / am α q) = amGExt (E := E) p / amGExt (E := E) q := by
  erw [RatFunc.map_apply_div]
  rfl
  exact ratFuncBaseChange_nonZeroDivisors

omit [CDiffField α] [CDiffFieldSpec α] [Differential E] [Algebra ℚ E] in
/-- The base-change hom sends `am p ↦ amGExt p`. -/
theorem ratFuncBaseChange_amG (p : (CFieldSpec.K α)[X]) :
    ratFuncBaseChange E (am α p) = amGExt (E := E) p := by
  have h1 : am α p = am α p / am α 1 := by simp [am]
  rw [h1, ratFuncBaseChange_amG_div]
  simp [amGExt]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Quotient rule for `towerDerivExt`** (the `E`-analogue of `towerFractionFieldDerivG_div`): for `E`-polys
`P, Q`, `Δ(P/Q) = (Δ'P·Q − P·Δ'Q)/Q²` in `RatFunc E`, where `Δ' = implicitDeriv (Dt base-changed to E)`. -/
theorem towerDerivExt_div (Dt : DensePoly α) (P Q : E[X]) :
    towerDerivExt Dt (algebraMap E[X] (RatFunc E) P / algebraMap E[X] (RatFunc E) Q)
      = (algebraMap E[X] (RatFunc E)
            (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E)) P)
          * algebraMap E[X] (RatFunc E) Q
          - algebraMap E[X] (RatFunc E) P
            * algebraMap E[X] (RatFunc E)
                (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E)) Q))
        / (algebraMap E[X] (RatFunc E) Q) ^ 2 := by
  rw [towerDerivExt, ← RatFunc.mk_eq_div, extendDeriv_mk, RatFunc.mk_eq_div, map_sub, map_mul,
    map_mul, map_pow]

/-- **The base-change intertwines the tower derivation** (the crux of the `K→E` transfer): applying
`ratFuncBaseChange` to a `K`-tower derivative of an `am`-fraction gives the `E`-tower derivative of the
corresponding `amGExt`-fraction. Via both quotient rules (`towerFractionFieldDerivG_div`, `towerDerivExt_div`)
and `implicitDeriv_map` (the monomial derivation commutes with base change). -/
theorem ratFuncBaseChange_towerFractionFieldDerivG [Algebra ℚ (CFieldSpec.K α)]
    [DifferentialAlgebra (CFieldSpec.K α) E] (Dt : DensePoly α)
    (gnum gden : (CFieldSpec.K α)[X]) :
    ratFuncBaseChange E (towerFractionFieldDeriv Dt (am α gnum / am α gden))
      = towerDerivExt Dt (amGExt (E := E) gnum / amGExt (E := E) gden) := by
  rw [towerFractionFieldDerivG_div, map_div₀, map_sub, map_mul, map_mul, map_pow]
  simp only [ratFuncBaseChange_amG, amGExt]
  rw [towerDerivExt_div, implicitDeriv_map, implicitDeriv_map]

open Classical in
/-- **The Hermite half over `E`** (`hherm`): base-changing the `K`-level `cHermiteReduceTowerG_field_identity`
to `E` via `ratFuncBaseChange`. `D_E(g) + hNum/Dstar = a/d` over `RatFunc E`, with `hNum = H.2.1` (the residual
identified via `toPolyG_hNum'_eq_2_1`), `Dstar = H.2.2`. `hcopgcd` is the genuine differential-normality side
condition. This is the `hherm` input to `isIntegralResultLrtG_of_hherm_of_logMatch`. -/
theorem hherm_lrt_E [CharZero (CFieldSpec.K α)] [Algebra ℚ (CFieldSpec.K α)]
    [DifferentialAlgebra (CFieldSpec.K α) E] [CFracGcdCoreWf α] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1 ≠ 0) :
    (towerDerivExt Dt (amGExt (toPoly (cHermiteReduceTower Dt a d).1.1)
          / amGExt (toPoly (cHermiteReduceTower Dt a d).1.2))
        + amGExt (toPoly (cHermiteReduceTower Dt a d).2.1)
          / amGExt (toPoly (cHermiteReduceTower Dt a d).2.2) : RatFunc E)
      = amGExt (toPoly a) / amGExt (toPoly d) := by
  have hK := congrArg (ratFuncBaseChange E)
    (cHermiteReduceTowerG_field_identity hgcd Dt a d hd0 hpp hcopgcd)
  rw [map_add, ratFuncBaseChange_towerFractionFieldDerivG, ratFuncBaseChange_amG_div,
    ratFuncBaseChange_amG_div] at hK
  rw [← toPolyG_hNum'_eq_2_1 hgcd Dt a d hd0 hpp hcopgcd]
  exact hK

/-- The **algebraic residue sum** over `E`: `Σᵢ Σ_{c ∈ roots(Rᵢ in E)} c·(Δ Sᵢ(c,t))/Sᵢ(c,t)` — the honest
denotation of the symbolic LRT log part, summing over the residues (roots of each `Rᵢ`) in `E`. -/
noncomputable def logResidueSumLrt (Dt : DensePoly α)
    (logs : List (DensePoly α × List (DensePoly α))) : RatFunc E :=
  (logs.map (fun p =>
    (((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots.map (fun c =>
      algebraMap E (RatFunc E) c
        * (towerDerivExt Dt (algebraMap E[X] (RatFunc E) (evalLrtArg p.2 c))
            / algebraMap E[X] (RatFunc E) (evalLrtArg p.2 c)))).sum)).sum

/-- The per-pole logarithmic term `(Δ (t−β))/(t−β)` for a pole `β ∈ E`. -/
noncomputable def poleTerm (Dt : DensePoly α) (β : E) : RatFunc E :=
  towerDerivExt Dt (algebraMap E[X] (RatFunc E) (X - C β))
    / algebraMap E[X] (RatFunc E) (X - C β)

/-- The single-`(Rᵢ, Sᵢ)` residue term: `Σ_{c ∈ roots(Rᵢ in E)} c·(Δ Sᵢ(c,t))/Sᵢ(c,t)`. -/
noncomputable def logResidueTermLrt (Dt : DensePoly α) (p : DensePoly α × List (DensePoly α)) : RatFunc E :=
  (((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots.map (fun c =>
    algebraMap E (RatFunc E) c
      * (towerDerivExt Dt (algebraMap E[X] (RatFunc E) (evalLrtArg p.2 c))
          / algebraMap E[X] (RatFunc E) (evalLrtArg p.2 c)))).sum

omit [CDiffField α] [CDiffFieldSpec α] in
/-- `logResidueSumLrt` is the sum of the per-`(Rᵢ, Sᵢ)` terms. -/
theorem logResidueSumLrtG_eq_sum (Dt : DensePoly α) (logs : List (DensePoly α × List (DensePoly α))) :
    logResidueSumLrt (E := E) Dt logs = (logs.map (logResidueTermLrt (E := E) Dt)).sum := rfl

omit [CDiffField α] [CDiffFieldSpec α] in
/-- Rewrite the residue sum termwise: if each `(Rᵢ, Sᵢ)` term equals `f p`, then `logResidueSumLrt = Σ f`. -/
theorem logResidueSumLrtG_eq_termwise (Dt : DensePoly α) (logs : List (DensePoly α × List (DensePoly α)))
    (f : DensePoly α × List (DensePoly α) → RatFunc E)
    (hterm : ∀ p ∈ logs, logResidueTermLrt Dt p = f p) :
    logResidueSumLrt (E := E) Dt logs = (logs.map f).sum := by
  rw [logResidueSumLrtG_eq_sum]
  exact congrArg List.sum (List.map_congr_left hterm)

omit [CDiffField α] [CDiffFieldSpec α] in
/-- `logResidueSumLrt` of the empty log list is `0`. -/
@[simp] theorem logResidueSumLrtG_nil (Dt : DensePoly α) :
    logResidueSumLrt (E := E) Dt ([] : List (DensePoly α × List (DensePoly α))) = 0 := rfl

omit [CDiffField α] [CDiffFieldSpec α] in
/-- `logResidueSumLrt` peels the head. -/
theorem logResidueSumLrtG_cons (Dt : DensePoly α) (p : DensePoly α × List (DensePoly α))
    (rest : List (DensePoly α × List (DensePoly α))) :
    logResidueSumLrt (E := E) Dt (p :: rest)
      = logResidueTermLrt (E := E) Dt p + logResidueSumLrt (E := E) Dt rest := by
  rw [logResidueSumLrtG_eq_sum, logResidueSumLrtG_eq_sum, List.map_cons, List.sum_cons]

/-! ### Log-derivative additivity (the residue↔pole reindexing core) -/

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Log-derivative additivity for the `E`-tower derivation.** `D(a·b)/(a·b) = D(a)/a + D(b)/b`. -/
theorem towerDerivExt_div_mul (Dt : DensePoly α) (a b : RatFunc E) (ha : a ≠ 0) (hb : b ≠ 0) :
    towerDerivExt Dt (a * b) / (a * b)
      = towerDerivExt Dt a / a + towerDerivExt Dt b / b := by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  field_simp
  ring

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Log-derivative of a product is the sum of log-derivatives**: `D(∏ xᵢ)/∏ xᵢ = Σ D(xᵢ)/xᵢ` (for nonzero
factors). This is the algebraic core of the residue↔pole reindexing — it splits the log-derivative of a
`gcd = ∏(t−β)` into the per-pole terms `monomial_residue_match_of_cancel` sums over. -/
theorem towerDerivExt_div_prod (Dt : DensePoly α) (l : Multiset (RatFunc E)) (hl : ∀ x ∈ l, x ≠ 0) :
    towerDerivExt Dt l.prod / l.prod = (l.map (fun x => towerDerivExt Dt x / x)).sum := by
  induction l using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have ha : a ≠ 0 := hl a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, x ≠ 0 := fun x hx => hl x (Multiset.mem_cons_of_mem hx)
    have hsp : s.prod ≠ 0 := Multiset.prod_ne_zero (fun h => (hs 0 h) rfl)
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      towerDerivExt_div_mul Dt a s.prod ha hsp, ih hs]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- Log-derivative of a product of **polynomial** factors through `algebraMap`:
`D(⟦∏ pᵢ⟧)/⟦∏ pᵢ⟧ = Σ D(⟦pᵢ⟧)/⟦pᵢ⟧` (`⟦·⟧ = algebraMap E[X] (RatFunc E)`, nonzero factors). This is the
form applied to a `gcd = ∏(t−β)` — it produces the per-pole terms directly. -/
theorem towerDerivExt_div_algebraMap_prod (Dt : DensePoly α) (l : Multiset E[X]) (hl : ∀ p ∈ l, p ≠ 0) :
    towerDerivExt Dt (algebraMap E[X] (RatFunc E) l.prod) / algebraMap E[X] (RatFunc E) l.prod
      = (l.map (fun p => towerDerivExt Dt (algebraMap E[X] (RatFunc E) p)
          / algebraMap E[X] (RatFunc E) p)).sum := by
  rw [map_multiset_prod, towerDerivExt_div_prod Dt (l.map (algebraMap E[X] (RatFunc E))) (by
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact fun h => hl p hp (IsFractionRing.injective E[X] (RatFunc E) (by rw [h, map_zero])) ),
    Multiset.map_map]
  rfl

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Term-level assembly: the residue term is the residue-weighted per-pole sum.** Given that each
monic log argument `evalLrtArg Sᵢ c` factors as `∏_{β ∈ fac c}(t−β)` (the gcd as linear factors), the
per-`Rᵢ` residue term becomes `Σ_{c ∈ roots Rᵢ} c·(Σ_{β ∈ fac c} poleTerm β)` — via the log-derivative
product split. Combined with `residue_pole_regroup` this collapses to the pole sum. -/
theorem logResidueTermLrtG_eq_pole_sum (Dt : DensePoly α) (p : DensePoly α × List (DensePoly α))
    (fac : E → Multiset E)
    (hfac : ∀ c ∈ ((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots,
      evalLrtArg p.2 c = ((fac c).map (fun β => X - C β)).prod) :
    logResidueTermLrt Dt p
      = (((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots.map (fun c =>
          algebraMap E (RatFunc E) c * ((fac c).map (poleTerm Dt)).sum)).sum := by
  rw [logResidueTermLrt]
  refine congrArg Multiset.sum (Multiset.map_congr rfl (fun c hc => ?_))
  rw [hfac c hc, towerDerivExt_div_algebraMap_prod Dt ((fac c).map (fun β => X - C β)) (by
    intro q hq
    rw [Multiset.mem_map] at hq
    obtain ⟨β, _, rfl⟩ := hq
    exact X_sub_C_ne_zero β), Multiset.map_map]
  rfl

open scoped Differential Classical in
omit [CDiffField α] [CDiffFieldSpec α] in
/-- **The residue-weighted pole sum is the normal part** (over `E`). Instantiating the
tower residue-match identity `monomial_residue_match_of_cancel` at `K := E` with derivation data
`v = (toPoly Dt).map φ` (so `poleTerm Dt β` is literally its `extendDeriv(implicitDeriv v)(t−β)/(t−β)`
summand): the residue-weighted pole sum `Σ_β res(β)·poleTerm β` equals `a/∏_{β∈s}(t−β)`, where the RT
residue `res β = a(β)/D(∏)(β)` and `hcancel` is the (automatically-true for a primitive `Dt`)
polynomial-part cancellation. -/
theorem pole_sum_eq_normalPart (Dt : DensePoly α) (a : E[X]) (s : Finset E)
    (hA : a.degree < s.card)
    (hnorm : ∀ β ∈ s, ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E)).eval β ≠ β′)
    (hcancel : ∑ β ∈ s, algebraMap E[X] (RatFunc E)
        (C (a.eval β / (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
              (Lagrange.nodal s id)).eval β)
          * ((((toPoly Dt).map (algebraMap (CFieldSpec.K α) E)) - C (β′)) /ₘ (X - C β))) = 0) :
    ∑ β ∈ s, algebraMap E (RatFunc E)
          (a.eval β / (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
              (Lagrange.nodal s id)).eval β)
        * poleTerm Dt β
      = algebraMap E[X] (RatFunc E) a / algebraMap E[X] (RatFunc E) (Lagrange.nodal s id) := by
  rw [← ResidueMatchTower.monomial_residue_match_of_cancel s a
        ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E)) hA hnorm hcancel]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  congr 1

end Ext

open scoped Classical in
/-- **Residue↔pole regrouping.** Grouping poles `β` by residue value `res β = c`, the *residue*-indexed sum
`Σ_c c·(Σ_{res β = c} term β)` equals the *pole*-indexed sum `Σ_β res(β)·term β`. This is the combinatorial
core connecting `logResidueSumLrt` (residue-indexed, via the `Rᵢ` roots) to the pole sum that
`monomial_residue_match_of_cancel` proves equals `hNum/Dstar`. -/
theorem residue_pole_regroup {E : Type*} [Field E] (poles : Finset E) (res : E → E)
    (term : E → RatFunc E) :
    (∑ c ∈ poles.image res, algebraMap E (RatFunc E) c
        * (∑ β ∈ poles.filter (fun β => res β = c), term β))
      = ∑ β ∈ poles, algebraMap E (RatFunc E) (res β) * term β := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := poles) (t := poles.image res)
    (g := res) (fun β hβ => Finset.mem_image_of_mem res hβ)
    (fun β => algebraMap E (RatFunc E) (res β) * term β)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun β hβ => ?_)
  rw [Finset.mem_filter] at hβ
  rw [hβ.2]

open scoped Classical in
/-- **Per-`Rᵢ` residue term = finset pole sum.** When `Rᵢ`'s roots (in `E`) are exactly the residue values
of a pole set `polesᵢ` and each monic log argument factors over the residue-`c` poles
(`fac c = polesᵢ.filter (res · = c)`), the residue term collapses to the pole sum
`Σ_{β ∈ polesᵢ} res(β)·poleTerm β`. Chains `logResidueTermLrtG_eq_pole_sum` (product split) with
`residue_pole_regroup` (residue↔pole). -/
theorem logResidueTermLrtG_eq_finset_pole_sum {α : Type*} [CField α] [CFieldSpec α] {E : Type*}
    [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E]
    (Dt : DensePoly α) (p : DensePoly α × List (DensePoly α)) (polesᵢ : Finset E) (res : E → E)
    (hroots : ((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots = (polesᵢ.image res).val)
    (hfac : ∀ c ∈ ((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots,
      evalLrtArg p.2 c = ((polesᵢ.filter (fun β => res β = c)).val.map (fun β => X - C β)).prod) :
    logResidueTermLrt Dt p = ∑ β ∈ polesᵢ, algebraMap E (RatFunc E) (res β) * poleTerm Dt β := by
  rw [logResidueTermLrtG_eq_pole_sum Dt p
    (fun c => (polesᵢ.filter (fun β => res β = c)).val) hfac, hroots]
  exact residue_pole_regroup polesᵢ res (poleTerm Dt)

open Classical in
/-- **A monic separable polynomial over an algebraically-closed field is `nodal` of its roots.** Splitting
(alg-closed) + monic gives `p = ∏ (X − β)` over the root multiset, and separable makes the roots `Nodup`, so
the multiset product collapses to the `Finset` product `Lagrange.nodal p.roots.toFinset id`. -/
theorem monic_separable_eq_nodal {E : Type*} [Field E] [IsAlgClosed E] (p : E[X])
    (hm : p.Monic) (hsep : p.Separable) :
    p = Lagrange.nodal p.roots.toFinset id := by
  classical
  have hnodup : p.roots.Nodup := Polynomial.nodup_roots hsep
  have hprod : p = (p.roots.map (fun β => X - C β)).prod :=
    (IsAlgClosed.splits p).eq_prod_roots_of_monic hm
  rw [Lagrange.nodal, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr hnodup]
  simpa using hprod

/-- **The concrete residue resultant base-changed to `E` is the abstract `rtResultantGen`.** Combines
(`toPolyG_cResidueResultantTowerG`, `R = rtResultantGen` over `K`), `rtResultantGen_map` (base change), and
`implicitDeriv_map` (the derivation image commutes). Over an alg-closed `E`, `roots_rtResultantGen` then reads
off the residues from this. -/
theorem toPolyG_cResidueResultantTowerG_map {α : Type*} [CField α] [CFieldSpec α] [CDiffField α]
    [CDiffFieldSpec α] [CharZero (CFieldSpec.K α)] {E : Type*} [Field E] [Algebra (CFieldSpec.K α) E]
    [Differential E] [DifferentialAlgebra (CFieldSpec.K α) E]
    (Dt a d : DensePoly α) (hDmonic : (toPoly d).Monic) (hDt0 : (toPoly Dt).natDegree = 0)
    (hAD : (toPoly a).natDegree < (toPoly d).natDegree) :
    (toPoly (cResidueResultantTower Dt a d)).map (algebraMap (CFieldSpec.K α) E)
      = rtResultantGen ((toPoly a).map (algebraMap (CFieldSpec.K α) E))
          ((toPoly d).map (algebraMap (CFieldSpec.K α) E))
          (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
            ((toPoly d).map (algebraMap (CFieldSpec.K α) E))) := by
  rw [toPolyG_cResidueResultantTowerG Dt a d hDmonic hDt0 hAD,
    rtResultantGen_map (algebraMap (CFieldSpec.K α) E) _ _ _
      (algebraMap (CFieldSpec.K α) E).injective, implicitDeriv_map]

open Classical in
/-- **The residue resultant's roots over `E` are the residues.** Composes
`toPolyG_cResidueResultantTowerG_map` (concrete `R_E = rtResultantGen`) with `roots_rtResultantGen` (roots =
residues) over an alg-closed `E`: `(R_E).roots = Dstar_E.roots.map (β ↦ hNum(β)/D(Dstar)(β))`. `hB` is the
Rothstein–Trager normality (`D(Dstar)(β) ≠ 0` at poles). This is the `hroots` residue structure for `hlog`. -/
theorem residueResultant_map_roots {α : Type*} [CField α] [CFieldSpec α] [CDiffField α]
    [CDiffFieldSpec α] [CharZero (CFieldSpec.K α)] {E : Type*} [Field E] [Algebra (CFieldSpec.K α) E]
    [Differential E] [DifferentialAlgebra (CFieldSpec.K α) E] [IsAlgClosed E]
    (Dt hNum Dstar : DensePoly α) (hDmonic : (toPoly Dstar).Monic) (hDt0 : (toPoly Dt).natDegree = 0)
    (hAD : (toPoly hNum).natDegree < (toPoly Dstar).natDegree)
    (hB : ∀ β ∈ ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E)).roots,
        (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
          ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E))).eval β ≠ 0)
    (hB_deg : (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
          ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E))).natDegree
        ≤ ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E)).natDegree - 1) :
    ((toPoly (cResidueResultantTower Dt hNum Dstar)).map (algebraMap (CFieldSpec.K α) E)).roots
      = ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E)).roots.map (fun β =>
          ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)).eval β
            / (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
                ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E))).eval β) := by
  rw [toPolyG_cResidueResultantTowerG_map Dt hNum Dstar hDmonic hDt0 hAD]
  refine roots_rtResultantGen _ _ _ ?_ hB ?_ hB_deg
  · exact (hDmonic.map (algebraMap (CFieldSpec.K α) E)).ne_zero
  · rw [natDegree_map_eq_of_injective (algebraMap (CFieldSpec.K α) E).injective,
      natDegree_map_eq_of_injective (algebraMap (CFieldSpec.K α) E).injective]
    exact hAD

/-- **A list-indexed disjoint partition splits a `Finset` sum.** For pairwise-disjoint per-index pole sets
`polesOf`, the list-sum of per-index `Finset` sums equals the `Finset` sum over their union — the pure
combinatorial fact behind `hpart`. -/
theorem sum_over_list_partition {ι : Type*} {γ : Type*} [DecidableEq γ] {M : Type*} [AddCommMonoid M]
    (l : List ι) (polesOf : ι → Finset γ) (g : γ → M)
    (hdisj : l.Pairwise (fun p q => Disjoint (polesOf p) (polesOf q))) :
    (l.map (fun p => ∑ β ∈ polesOf p, g β)).sum
      = ∑ β ∈ (l.map polesOf).foldr (· ∪ ·) ∅, g β := by
  have hmemfold : ∀ (L : List (Finset γ)) (β : γ), β ∈ L.foldr (· ∪ ·) ∅ → ∃ s ∈ L, β ∈ s := by
    intro L β hβ
    induction L with
    | nil => simp at hβ
    | cons hd u ih =>
      rw [List.foldr_cons, Finset.mem_union] at hβ
      rcases hβ with h | h
      · exact ⟨hd, List.mem_cons_self, h⟩
      · obtain ⟨s', hs', hβ'⟩ := ih h
        exact ⟨s', List.mem_cons_of_mem hd hs', hβ'⟩
  induction l with
  | nil => simp
  | cons p t ih =>
    rw [List.pairwise_cons] at hdisj
    have hpt : Disjoint (polesOf p) ((t.map polesOf).foldr (· ∪ ·) ∅) := by
      rw [Finset.disjoint_right]
      intro β hβ hβp
      obtain ⟨s, hs, hβs⟩ := hmemfold (t.map polesOf) β hβ
      rw [List.mem_map] at hs
      obtain ⟨q, hqt, rfl⟩ := hs
      exact (Finset.disjoint_left.mp (hdisj.1 q hqt) hβp) hβs
    rw [List.map_cons, List.sum_cons, List.map_cons, List.foldr_cons,
      Finset.sum_union hpt, ih hdisj.2]

/-- Membership in a `foldr (· ∪ ·) ∅` of `Finset`s: `β` is in the union iff it is in some list member. -/
theorem mem_foldr_union_iff {γ : Type*} [DecidableEq γ] (L : List (Finset γ)) (β : γ) :
    β ∈ L.foldr (· ∪ ·) ∅ ↔ ∃ s ∈ L, β ∈ s := by
  induction L with
  | nil => simp
  | cons hd u ih =>
    rw [List.foldr_cons, Finset.mem_union, ih]
    simp only [List.mem_cons, exists_eq_or_imp]

open Classical in
/-- **Filter-partition pole sum** (the concrete `hpart`). With `polesOf p := allpoles.filter (res · ∈ rootSet p)`
for pairwise-disjoint `rootSet`s (the `Rᵢ.roots`, disjoint via Yun coprimality) that cover every pole's residue,
the list-sum of per-entry pole sums equals the full sum over `allpoles`. Discharges the `hpart` hypothesis of
`logResidueSumLrtG_eq_poleSum`/`_eq_normalPart`. -/
theorem sum_filter_rootSet_partition {α : Type*} [CField α] [CFieldSpec α] {E : Type*}
    [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E]
    (Dt : DensePoly α) (allpoles : Finset E) (res : E → E)
    (logs : List (DensePoly α × List (DensePoly α))) (rootSet : DensePoly α × List (DensePoly α) → Finset E)
    (hdisj : logs.Pairwise (fun p q => Disjoint (rootSet p) (rootSet q)))
    (hcover : ∀ β ∈ allpoles, ∃ p ∈ logs, res β ∈ rootSet p) :
    (logs.map (fun p => ∑ β ∈ allpoles.filter (fun β => res β ∈ rootSet p),
        algebraMap E (RatFunc E) (res β) * poleTerm Dt β)).sum
      = ∑ β ∈ allpoles, algebraMap E (RatFunc E) (res β) * poleTerm Dt β := by
  have hfilterdisj : logs.Pairwise (fun p q =>
      Disjoint (allpoles.filter (fun β => res β ∈ rootSet p))
        (allpoles.filter (fun β => res β ∈ rootSet q))) := by
    refine hdisj.imp fun {p q} hpq => ?_
    rw [Finset.disjoint_left]
    intro β hβp hβq
    rw [Finset.mem_filter] at hβp hβq
    exact (Finset.disjoint_left.mp hpq hβp.2) hβq.2
  rw [sum_over_list_partition logs (fun p => allpoles.filter (fun β => res β ∈ rootSet p))
    (fun β => algebraMap E (RatFunc E) (res β) * poleTerm Dt β) hfilterdisj]
  congr 1
  refine Finset.ext (fun β => ?_)
  rw [mem_foldr_union_iff]
  constructor
  · rintro ⟨s, hs, hβs⟩
    rw [List.mem_map] at hs
    obtain ⟨p, _, rfl⟩ := hs
    exact (Finset.mem_filter.mp hβs).1
  · intro hβ
    obtain ⟨p, hp, hres⟩ := hcover β hβ
    exact ⟨allpoles.filter (fun β => res β ∈ rootSet p),
      List.mem_map_of_mem hp, Finset.mem_filter.mpr ⟨hβ, hres⟩⟩

open Classical in
/-- **`hroots` for the filter partition.** When `Rᵢ`'s roots are `Nodup` (squarefree) and every root is a
residue `res β` of some pole `β ∈ allpoles`, the image of `polesOf p := allpoles.filter (res · ∈ Rᵢ.roots)`
under `res` recovers `Rᵢ.roots` exactly: `Rᵢ.roots = ((polesOf p).image res).val`. -/
theorem roots_eq_image_res_filter {E : Type*} [Field E] (allpoles : Finset E) (res : E → E) (Ri : E[X])
    (hnodup : Ri.roots.Nodup) (hsub : ∀ c ∈ Ri.roots, ∃ β ∈ allpoles, res β = c) :
    Ri.roots = ((allpoles.filter (fun β => res β ∈ Ri.roots.toFinset)).image res).val := by
  have hFinset : Ri.roots.toFinset
      = (allpoles.filter (fun β => res β ∈ Ri.roots.toFinset)).image res := by
    refine Finset.ext (fun c => ?_)
    rw [Finset.mem_image]
    constructor
    · intro hc
      obtain ⟨β, hβ, hres⟩ := hsub c (Multiset.mem_toFinset.mp hc)
      exact ⟨β, Finset.mem_filter.mpr ⟨hβ, hres ▸ hc⟩, hres⟩
    · rintro ⟨β, hβ, rfl⟩
      exact (Finset.mem_filter.mp hβ).2
  rw [← hFinset, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]

open scoped Classical in
/-- **Log-part sum in pole form (partition assembly).** Summing the per-`Rᵢ` pole sums over a per-entry
pole set `polesOf` that tiles the full pole set: `logResidueSumLrt = Σ_{β ∈ allpoles} res(β)·poleTerm β`.
Chains `logResidueSumLrtG_eq_termwise` (sum over entries) with `logResidueTermLrtG_eq_finset_pole_sum`
(each entry ↦ its pole sum). `hpart` is the structural fact that the entries' pole sets partition
`allpoles` (the LRT/Yun fiber-size decomposition). -/
theorem logResidueSumLrtG_eq_poleSum {α : Type*} [CField α] [CFieldSpec α] {E : Type*}
    [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E]
    (Dt : DensePoly α) (logs : List (DensePoly α × List (DensePoly α))) (allpoles : Finset E) (res : E → E)
    (polesOf : DensePoly α × List (DensePoly α) → Finset E)
    (hroots : ∀ p ∈ logs, ((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots
      = ((polesOf p).image res).val)
    (hfac : ∀ p ∈ logs, ∀ c ∈ ((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots,
      evalLrtArg p.2 c = (((polesOf p).filter (fun β => res β = c)).val.map (fun β => X - C β)).prod)
    (hpart : (logs.map (fun p => ∑ β ∈ polesOf p,
        algebraMap E (RatFunc E) (res β) * poleTerm Dt β)).sum
      = ∑ β ∈ allpoles, algebraMap E (RatFunc E) (res β) * poleTerm Dt β) :
    logResidueSumLrt Dt logs = ∑ β ∈ allpoles, algebraMap E (RatFunc E) (res β) * poleTerm Dt β := by
  rw [logResidueSumLrtG_eq_termwise Dt logs
      (fun p => ∑ β ∈ polesOf p, algebraMap E (RatFunc E) (res β) * poleTerm Dt β)
      (fun p hp => logResidueTermLrtG_eq_finset_pole_sum Dt p (polesOf p) res (hroots p hp) (hfac p hp))]
  exact hpart

open scoped Differential Classical in
/-- **LRT log-part soundness (the named theorem).** The tower derivative of the LRT symbolic log part
denotes the normal integrand: `logResidueSumLrt Dt logs = hNum/Dstar` over `E`, where `Dstar` splits as
`∏_{β ∈ allpoles}(t−β)`. Composes `logResidueSumLrtG_eq_poleSum` (log sum ↦ residue-weighted pole sum,
over a pole partition `polesOf`) with `pole_sum_eq_normalPart` (the Rothstein–Trager residue match
`Σ_β res(β)·poleTerm β = hNum/Dstar`). The residue is fixed to the RT form
`res β = hNum(β)/D(∏)(β)`. -/
theorem logResidueSumLrtG_eq_normalPart {α : Type*} [CField α] [CFieldSpec α] {E : Type*}
    [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E]
    (Dt hNum : DensePoly α) (logs : List (DensePoly α × List (DensePoly α))) (allpoles : Finset E)
    (polesOf : DensePoly α × List (DensePoly α) → Finset E)
    (hroots : ∀ p ∈ logs, ((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots
      = ((polesOf p).image (fun β => ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)).eval β
          / (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
              (Lagrange.nodal allpoles id)).eval β)).val)
    (hfac : ∀ p ∈ logs, ∀ c ∈ ((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots,
      evalLrtArg p.2 c = (((polesOf p).filter (fun β =>
          ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)).eval β
            / (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
                (Lagrange.nodal allpoles id)).eval β = c)).val.map (fun β => X - C β)).prod)
    (hpart : (logs.map (fun p => ∑ β ∈ polesOf p,
        algebraMap E (RatFunc E) (((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)).eval β
            / (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
                (Lagrange.nodal allpoles id)).eval β) * poleTerm Dt β)).sum
      = ∑ β ∈ allpoles, algebraMap E (RatFunc E)
          (((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)).eval β
            / (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
                (Lagrange.nodal allpoles id)).eval β) * poleTerm Dt β)
    (hA : ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)).degree < allpoles.card)
    (hnorm : ∀ β ∈ allpoles, ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E)).eval β ≠ β′)
    (hcancel : ∑ β ∈ allpoles, algebraMap E[X] (RatFunc E)
        (C (((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)).eval β
              / (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
                  (Lagrange.nodal allpoles id)).eval β)
          * ((((toPoly Dt).map (algebraMap (CFieldSpec.K α) E)) - C (β′)) /ₘ (X - C β))) = 0) :
    logResidueSumLrt Dt logs
      = algebraMap E[X] (RatFunc E) ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E))
        / algebraMap E[X] (RatFunc E) (Lagrange.nodal allpoles id) := by
  rw [logResidueSumLrtG_eq_poleSum Dt logs allpoles _ polesOf hroots hfac hpart]
  exact pole_sum_eq_normalPart Dt ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)) allpoles
    hA hnorm hcancel

open scoped Differential Classical in
/-- **`hlog` from the Yun structure** (the assembly of the three discharge cores). With `polesOf p :=
allpoles.filter (res · ∈ Rᵢ.roots)`, `logResidueSumLrtG_eq_normalPart`'s hypotheses discharge from: `hnodup`
(each `Rᵢ` squarefree) + `hressub` (each root is a residue) ⟹ `hroots` (`roots_eq_image_res_filter`); `hdisj`
(Yun coprimality) + `hcover` (reconstruction) ⟹ `hpart` (`sum_filter_rootSet_partition`); `hentry` (each entry
log arg = its fiber product, from `evalLrtArg_eq_fiber_prod`) ⟹ `hfac`. Conclusion: `logResidueSumLrt =
hNum/∏(t−β)`. -/
theorem logResidueSumLrtG_eq_normalPart_of_yun {α : Type*} [CField α] [CFieldSpec α] {E : Type*}
    [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E]
    (Dt hNum : DensePoly α) (logs : List (DensePoly α × List (DensePoly α))) (allpoles : Finset E) (res : E → E)
    (hres : res = fun β => ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)).eval β
        / (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
            (Lagrange.nodal allpoles id)).eval β)
    (hnodup : ∀ p ∈ logs, ((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots.Nodup)
    (hressub : ∀ p ∈ logs, ∀ c ∈ ((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots,
        ∃ β ∈ allpoles, res β = c)
    (hdisj : logs.Pairwise (fun p q =>
        Disjoint ((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots.toFinset
          ((toPoly q.1).map (algebraMap (CFieldSpec.K α) E)).roots.toFinset))
    (hcover : ∀ β ∈ allpoles, ∃ p ∈ logs,
        res β ∈ ((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots.toFinset)
    (hentry : ∀ p ∈ logs, ∀ c ∈ ((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots,
        evalLrtArg p.2 c
          = ((allpoles.filter (fun β => res β = c)).val.map (fun β => X - C β)).prod)
    (hA : ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)).degree < allpoles.card)
    (hnorm : ∀ β ∈ allpoles, ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E)).eval β ≠ β′)
    (hcancel : ∑ β ∈ allpoles, algebraMap E[X] (RatFunc E)
        (C (res β) * ((((toPoly Dt).map (algebraMap (CFieldSpec.K α) E)) - C (β′)) /ₘ (X - C β))) = 0) :
    logResidueSumLrt Dt logs
      = algebraMap E[X] (RatFunc E) ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E))
        / algebraMap E[X] (RatFunc E) (Lagrange.nodal allpoles id) := by
  subst hres
  refine logResidueSumLrtG_eq_normalPart Dt hNum logs allpoles
    (fun p => allpoles.filter (fun β =>
      ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)).eval β
        / (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
            (Lagrange.nodal allpoles id)).eval β
      ∈ ((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots.toFinset)) ?_ ?_ ?_ hA hnorm hcancel
  · intro p hp
    exact roots_eq_image_res_filter allpoles _ ((toPoly p.1).map (algebraMap (CFieldSpec.K α) E))
      (hnodup p hp) (hressub p hp)
  · intro p hp c hc
    rw [hentry p hp c hc]
    congr 2
    congr 1
    ext β
    simp only [Finset.mem_filter, Multiset.mem_toFinset]
    exact ⟨fun h => ⟨⟨h.1, by rw [h.2]; exact hc⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  · exact sum_filter_rootSet_partition Dt allpoles _ logs
      (fun p => ((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots.toFinset) hdisj hcover

/-- **LRT field-identity assembler** (the analogue of `field_identity_of_reducedG_of_residueMatch`, over
`E`). Given the log-part match `hlog` (`logResidueSumLrt = hNum/Dstar`, from
`logResidueSumLrtG_eq_normalPart`) and the Hermite half `hherm` (`D(g) + hNum/Dstar = a/d`), the full
reduced field identity `D(g) + logResidueSumLrt = a/d` holds. -/
theorem field_identity_lrt_of_hherm_of_logMatch {α : Type*} [CField α] [CFieldSpec α] {E : Type*}
    [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E]
    (Dt gnum gden hNum hDen anum aden : DensePoly α) (logs : List (DensePoly α × List (DensePoly α)))
    (hlog : (logResidueSumLrt Dt logs : RatFunc E) = amGExt (toPoly hNum) / amGExt (toPoly hDen))
    (hherm : (towerDerivExt Dt (amGExt (toPoly gnum) / amGExt (toPoly gden))
          + amGExt (toPoly hNum) / amGExt (toPoly hDen) : RatFunc E)
        = amGExt (toPoly anum) / amGExt (toPoly aden)) :
    (towerDerivExt Dt (amGExt (toPoly gnum) / amGExt (toPoly gden)) + logResidueSumLrt Dt logs
        : RatFunc E)
      = amGExt (toPoly anum) / amGExt (toPoly aden) := by
  rw [hlog]; exact hherm

/-- **Symbolic-log soundness for the LRT reduced result.** Over **any** algebraically-closed differential
extension `E` of `K = CFieldSpec.K α` (so both `Dstar`'s poles and every residue polynomial `Rᵢ`'s roots lie
in `E`), the `E`-tower derivative of the rational part plus the algebraic residue sum equals `anum/aden`
(base-changed to `E`). The `E`-quantification is the descent vehicle (instantiate `E` at the algebraic closure
to prove; injectivity of the base change gives the `K`-level statement). This is the root-free analogue of
`IsIntegralResult` handling algebraic residues. -/
def IsIntegralResultLrt (Dt anum aden : DensePoly α) (res : LrtResult α) : Prop :=
  ∀ (E : Type*) [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E]
    [DifferentialAlgebra (CFieldSpec.K α) E] [IsAlgClosed E],
    (towerDerivExt Dt (amGExt (toPoly res.rational.1) / amGExt (toPoly res.rational.2))
          + logResidueSumLrt Dt res.logs : RatFunc E)
      = amGExt (toPoly anum) / amGExt (toPoly aden)

/-- **`IsIntegralResultLrt` from the log match + Hermite half.** Packages `field_identity_lrt_of_hherm_of_
logMatch` under the `E`-quantifier: given, over every splitting extension `E`, the log-part match `hlog`
(`logResidueSumLrt res.logs = hNum/Dstar`) and the Hermite half `hherm` (`D(g) + hNum/Dstar = a/d`), the
soundness predicate `IsIntegralResultLrt` holds. This is the final-assembly skeleton: what remains is
discharging `hlog` (via `logResidueSumLrtG_eq_normalPart` + the Yun partition) and `hherm` (base-change of
the Hermite tower soundness) for `res = cIntegrateReducedLrt`. -/
theorem isIntegralResultLrtG_of_hherm_of_logMatch.{u} (Dt anum aden : DensePoly α) (res : LrtResult α)
    (hNum hDen : DensePoly α)
    (hlog : ∀ (E : Type u) [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E]
        [DifferentialAlgebra (CFieldSpec.K α) E] [IsAlgClosed E],
        (logResidueSumLrt Dt res.logs : RatFunc E) = amGExt (toPoly hNum) / amGExt (toPoly hDen))
    (hherm : ∀ (E : Type u) [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E]
        [DifferentialAlgebra (CFieldSpec.K α) E] [IsAlgClosed E],
        (towerDerivExt Dt (amGExt (toPoly res.rational.1) / amGExt (toPoly res.rational.2))
            + amGExt (toPoly hNum) / amGExt (toPoly hDen) : RatFunc E)
          = amGExt (toPoly anum) / amGExt (toPoly aden)) :
    IsIntegralResultLrt.{_, u} Dt anum aden res := by
  intro E _ _ _ _ _ _
  exact field_identity_lrt_of_hherm_of_logMatch Dt res.rational.1 res.rational.2 hNum hDen anum aden
    res.logs (hlog E) (hherm E)

omit [CDiffFieldSpec α] in
variable [CFracGcdCoreWf α] in
/-- **The symbolic log part is empty when the squarefree denominator is a constant** (`cdeg Dstar = 0`):
there are no poles and hence no residues. The residue resultant of a constant is constant
(`cdegG_cResidueResultantTowerG_eq_zero_of_cdegG_zero`), whose Yun factorization is empty
(`cSqfreeYunFFG_eq_nil_of_cdegG_zero`), so the `filterMap` runs over the empty list. The trivial-normal-part
(no-poles) base of the reduced soundness. -/
theorem cLrtLogArgG_eq_nil_of_cdegG_zero (Dt hNum Dstar : DensePoly α) (hDstar : cdeg Dstar = 0) :
    cLrtLogArg Dt hNum Dstar = [] := by
  have hR := cSqfreeYunFFG_eq_nil_of_cdegG_zero (cResidueResultantTower Dt hNum Dstar)
    (cdegG_cResidueResultantTowerG_eq_zero_of_cdegG_zero Dt hNum Dstar hDstar)
  have hR' : cSqfreeYunFF (CPoly.residueResultantTower Dt hNum Dstar) = [] := by
    simpa [cResidueResultantTower] using hR
  simp only [cLrtLogArg, CPoly.lrtLogArg, squarefreeYun_dense_wf_eq, hR', List.zipIdx_nil,
    List.filterMap_nil]

omit [CFieldSpec α] [CDiffFieldSpec α] in
variable [CFracGcdCoreWf α] in
/-- **Membership in `cLrtLogArg`.** Each entry `p` comes from a `(Rᵢ, idx)` in the Yun factorization
`cSqfreeYunFF R` (`R = cResidueResultantTower …`) with `Rᵢ` non-constant, and `p = (Rᵢ, CPolySubresultant.parametric
… (idx+1))`. Unfolds the `filterMap ∘ zipIdx`; the foundation for the per-entry Yun facts. -/
theorem mem_cLrtLogArgG (Dt hNum Dstar : DensePoly α) (p : DensePoly α × List (DensePoly α))
    (hp : p ∈ cLrtLogArg Dt hNum Dstar) :
    ∃ idx, (p.1, idx) ∈ (cSqfreeYunFF (cResidueResultantTower Dt hNum Dstar)).zipIdx
      ∧ ¬ ((cnorm p.1 : List α).length ≤ 1)
      ∧ (idx + 1 ≠ cdeg Dstar → p.2 = CPolySubresultant.parametric Dstar hNum (CPolyEngine.monomialDeriv Dt Dstar) (cdeg Dstar)
          (cdeg (CPolyEngine.monomialDeriv Dt Dstar)) (idx + 1))
      ∧ (idx + 1 = cdeg Dstar → p.2 = Dstar.map (fun x => ([x] : DensePoly α))) := by
  rw [cLrtLogArg, CPoly.lrtLogArg, squarefreeYun_dense_wf_eq] at hp
  simp_rw [degBound_cnorm_dense_eq, coefficientConstants_dense_eq] at hp
  rw [List.mem_filterMap] at hp
  obtain ⟨⟨Ri, idx⟩, hmem, hfn⟩ := hp
  simp only at hfn
  split at hfn
  · simp at hfn
  · rename_i hlen
    split at hfn
    · -- `i = n` (pure single log): `p.2 = Dstar`; the subresultant claim is vacuous.
      rename_i hin
      rw [Option.some_inj] at hfn; subst hfn
      exact ⟨idx, hmem, hlen, fun hne => absurd hin hne, fun _ => rfl⟩
    · -- else: `p.2 = subresultant`.
      rename_i hin
      rw [Option.some_inj] at hfn; subst hfn
      exact ⟨idx, hmem, hlen, fun _ => rfl, fun heq => absurd heq hin⟩

omit [CDiffField α] [CDiffFieldSpec α] in
variable [CFracGcdCoreWf α] in
/-- `R` is a nonzero input for the squarefree Yun factorization. -/
structure IsYunFactorizationInput (R : DensePoly α) [NormalizedGCDMonoid (CFieldSpec.K α)] : Prop where
  /-- `R` denotes a nonzero polynomial. -/
  nonzero : toPoly R ≠ 0
  /-- The primitive part of `R` denotes a nonzero polynomial. -/
  primPart_nonzero : (toPoly R).primPart ≠ 0

open Classical in
omit [CDiffFieldSpec α] in
variable [CFracGcdCoreWf α] in
/-- **`hnodup` per entry.** Each entry's `Rᵢ` is a Yun factor of `R`, hence squarefree
(`cSqfreeYunFFG_squarefree`), so over char-zero `K` it is separable, and its base change to `E` stays
separable ⟹ `Nodup` roots. -/
theorem nodup_roots_cLrtLogArgG_entry [CharZero (CFieldSpec.K α)] {E : Type*} [Field E]
    [Algebra (CFieldSpec.K α) E] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt hNum Dstar : DensePoly α)
    (hR : IsYunFactorizationInput (cResidueResultantTower Dt hNum Dstar))
    (p : DensePoly α × List (DensePoly α)) (hp : p ∈ cLrtLogArg Dt hNum Dstar) :
    ((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots.Nodup := by
  obtain ⟨idx, hmem, _, _⟩ := mem_cLrtLogArgG Dt hNum Dstar p hp
  have hget : (cSqfreeYunFF (cResidueResultantTower Dt hNum Dstar))[idx]? = some p.1 :=
    List.mk_mem_zipIdx_iff_getElem?.mp hmem
  obtain ⟨hj, hp1'⟩ := List.getElem?_eq_some_iff.mp hget
  have hp1 : (cSqfreeYunFF (cResidueResultantTower Dt hNum Dstar)).get ⟨idx, hj⟩ = p.1 := by
    rw [List.get_eq_getElem]; exact hp1'
  have hsqf : Squarefree (toPoly p.1) :=
    hp1 ▸ cSqfreeYunFFG_squarefree hgcd _ hR.nonzero hR.primPart_nonzero idx hj
  exact Polynomial.nodup_roots
    ((PerfectField.separable_iff_squarefree.mpr hsqf).map)

/-- The roots of the nodal polynomial `∏_{β ∈ s}(X − β)` are exactly `s` (as a multiset). -/
theorem nodal_roots {E : Type*} [Field E] (s : Finset E) :
    (Lagrange.nodal s id).roots = s.val := by
  rw [Lagrange.nodal]; simp only [id_eq]; exact Polynomial.roots_prod_X_sub_C s

/-- `rootMultiplicity c (p^n) = n · rootMultiplicity c p` (nonzero `p`). -/
theorem rootMultiplicity_pow_eq {E : Type*} [Field E] (p : E[X]) (n : ℕ) (c : E) (hp : p ≠ 0) :
    rootMultiplicity c (p ^ n) = n * rootMultiplicity c p := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero k hp) hp), ih,
      Nat.succ_mul]

/-- `rootMultiplicity` is invariant under `Associated` (the unit factor has no roots). -/
theorem associated_rootMultiplicity_eq {E : Type*} [Field E] {p q : E[X]} (h : Associated p q) (c : E) :
    rootMultiplicity c p = rootMultiplicity c q := by
  obtain ⟨u, rfl⟩ := h
  by_cases hp : p = 0
  · simp [hp]
  · have hu0 : rootMultiplicity c (↑u : E[X]) = 0 := by
      apply Polynomial.rootMultiplicity_eq_zero
      obtain ⟨c0, hc0, hc0eq⟩ := Polynomial.isUnit_iff.mp u.isUnit
      rw [← hc0eq, Polynomial.IsRoot, Polynomial.eval_C]
      exact fun h => hc0.ne_zero h
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hp u.ne_zero), hu0, Nat.add_zero]

/-- A root of a squarefree polynomial has multiplicity exactly `1` (`≥ 1` from being a root, `≤ 1` since a
double factor `(X−c)²` would contradict squarefreeness). -/
theorem squarefree_rootMultiplicity_eq_one {E : Type*} [Field E] {p : E[X]} (hsf : Squarefree p)
    (c : E) (hc : p.IsRoot c) : rootMultiplicity c p = 1 := by
  have hp0 : p ≠ 0 := hsf.ne_zero
  have h1 : 0 < rootMultiplicity c p := (Polynomial.rootMultiplicity_pos hp0).mpr hc
  have h2 : rootMultiplicity c p ≤ 1 := by
    by_contra h
    rw [not_le] at h
    have hdvd : (X - C c) ^ 2 ∣ p :=
      (pow_dvd_pow _ h).trans (Polynomial.pow_rootMultiplicity_dvd p c)
    exact Polynomial.not_isUnit_X_sub_C c (hsf (X - C c) (pow_two (X - C c) ▸ hdvd))
  omega

/-- A root of the powered product `prodPow i L = ∏ⱼ L[j]^(i+j)` (`i ≠ 0`, nonzero) is a root of some factor
`v ∈ L`. The root-of-product step for `hcover` (a residue is a root of the Yun reconstruction `R ~ ∏Rᵢ^i`). -/
theorem mem_roots_prodPow {E : Type*} [Field E] (i : ℕ) (hi : i ≠ 0) (L : List E[X]) (a : E)
    (hne : prodPow i L ≠ 0) (ha : a ∈ (prodPow i L).roots) : ∃ v ∈ L, a ∈ v.roots := by
  induction L generalizing i with
  | nil => rw [prodPow, Polynomial.roots_one] at ha; simp at ha
  | cons e es ih =>
    rw [prodPow] at hne ha
    rw [Polynomial.roots_mul hne, Multiset.mem_add] at ha
    rcases ha with ha | ha
    · rw [Polynomial.roots_pow, Multiset.mem_nsmul] at ha
      exact ⟨e, List.mem_cons_self, ha.2⟩
    · have hrest : prodPow (i + 1) es ≠ 0 := fun h => hne (by rw [h, mul_zero])
      obtain ⟨v, hv, hav⟩ := ih (i + 1) (Nat.succ_ne_zero i) hrest ha
      exact ⟨v, List.mem_cons_of_mem e hv, hav⟩

/-- `prodPow` commutes with a polynomial base change `φ`: `(prodPow i L).map φ = prodPow i (L.map (·.map φ))`. -/
theorem prodPow_map {K E : Type*} [Field K] [Field E] (φ : K →+* E) (i : ℕ) (L : List K[X]) :
    (prodPow i L).map φ = prodPow i (L.map (Polynomial.map φ)) := by
  induction L generalizing i with
  | nil => simp [prodPow]
  | cons e es ih =>
    simp only [prodPow, List.map_cons, Polynomial.map_mul, Polynomial.map_pow]
    rw [ih]

/-- If `c` is a root of no factor of `L`, then `rootMultiplicity c (prodPow i L) = 0` (a root of the product
would be a root of some factor, by `mem_roots_prodPow`). -/
theorem rootMult_prodPow_eq_zero {E : Type*} [Field E] (i : ℕ) (hi : i ≠ 0) (L : List E[X]) (c : E)
    (hne : prodPow i L ≠ 0) (hnot : ∀ v ∈ L, rootMultiplicity c v = 0) :
    rootMultiplicity c (prodPow i L) = 0 := by
  by_contra h
  have hroot : c ∈ (prodPow i L).roots :=
    Polynomial.mem_roots'.mpr ⟨hne, (Polynomial.rootMultiplicity_pos hne).mp (Nat.pos_of_ne_zero h)⟩
  obtain ⟨v, hv, hcv⟩ := mem_roots_prodPow i hi L c hne hroot
  obtain ⟨hv0, hvroot⟩ := Polynomial.mem_roots'.mp hcv
  have hpos := (Polynomial.rootMultiplicity_pos hv0).mpr hvroot
  rw [hnot v hv] at hpos
  exact Nat.lt_irrefl 0 hpos

/-- **The multiplicity in `prodPow` from a unique simple root.** If `c` is a simple root of exactly one factor
`L[idx]` (`rootMultiplicity = 1`) and of no other factor, then `rootMultiplicity c (prodPow i L) = i + idx`
(the exponent of `L[idx]` in `prodPow i L = ∏ⱼ L[j]^(i+j)`). The multiplicity heart of `hentry`. -/
theorem rootMult_prodPow_of_unique {E : Type*} [Field E] (c : E) :
    ∀ (L : List E[X]) (i idx : ℕ) (_ : i ≠ 0) (hidx : idx < L.length), prodPow i L ≠ 0 →
      rootMultiplicity c (L[idx]'hidx) = 1 →
      (∀ (j : ℕ) (hj : j < L.length), j ≠ idx → rootMultiplicity c (L[j]'hj) = 0) →
      rootMultiplicity c (prodPow i L) = i + idx := by
  intro L
  induction L with
  | nil => intro i idx _ hidx; simp at hidx
  | cons e es ih =>
    intro i idx hi hidx hne hc hother
    rw [prodPow] at hne ⊢
    have he0 : e ≠ 0 := fun h => (left_ne_zero_of_mul hne) (by rw [h, zero_pow hi])
    have hrest0 : prodPow (i + 1) es ≠ 0 := right_ne_zero_of_mul hne
    rw [Polynomial.rootMultiplicity_mul hne, rootMultiplicity_pow_eq e i c he0]
    cases idx with
    | zero =>
      simp only [List.getElem_cons_zero] at hc
      rw [hc, mul_one, rootMult_prodPow_eq_zero (i + 1) (Nat.succ_ne_zero i) es c hrest0 ?_,
        Nat.add_zero]
      intro v hv
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
      exact hother (k + 1) (by simpa using hk) (Nat.succ_ne_zero k)
    | succ idx' =>
      have hidx' : idx' < es.length := by simpa using hidx
      simp only [List.getElem_cons_succ] at hc
      have he_z : rootMultiplicity c e = 0 := by
        have h0 := hother 0 (Nat.zero_lt_succ _) (Nat.succ_ne_zero idx').symm
        simpa using h0
      rw [he_z, mul_zero, zero_add,
        ih (i + 1) idx' (Nat.succ_ne_zero i) hidx' hrest0 hc ?_]
      · omega
      · intro j hj hjne
        have := hother (j + 1) (by simpa using hj) (by omega)
        simpa using this

/-- **Coprime polynomials have disjoint roots.** A common root `a` would give `1 = (u·p+v·q)(a) = 0`. -/
theorem disjoint_roots_of_isCoprime {E : Type*} [Field E] [DecidableEq E] (p q : E[X])
    (h : IsCoprime p q) : Disjoint p.roots.toFinset q.roots.toFinset := by
  rw [Finset.disjoint_left]
  intro a hap haq
  rw [Multiset.mem_toFinset, Polynomial.mem_roots'] at hap haq
  obtain ⟨u, v, huv⟩ := h
  have h1 : (u * p + v * q).eval a = 1 := by rw [huv]; simp
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, hap.2, haq.2] at h1
  simp at h1

open Classical in
omit [CDiffField α] [CDiffFieldSpec α] in
variable [CFracGcdCoreWf α] in
/-- **Distinct Yun factors have disjoint roots over `E`.** `cSqfreeYunFFG_isRelPrime` (`IsRelPrime`) ⟹
`IsCoprime` (PID) ⟹ `IsCoprime` over `E` (base change) ⟹ disjoint roots. -/
theorem disjoint_yun_factors [CharZero (CFieldSpec.K α)] {E : Type*} [Field E]
    [Algebra (CFieldSpec.K α) E] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (R : DensePoly α)
    (hR : IsYunFactorizationInput R) {j k : ℕ} (hj : j < (cSqfreeYunFF R).length)
    (hk : k < (cSqfreeYunFF R).length) (hjk : j ≠ k) :
    Disjoint ((toPoly ((cSqfreeYunFF R).get ⟨j, hj⟩)).map (algebraMap (CFieldSpec.K α) E)).roots.toFinset
      ((toPoly ((cSqfreeYunFF R).get ⟨k, hk⟩)).map (algebraMap (CFieldSpec.K α) E)).roots.toFinset := by
  have hcopE := ((cSqfreeYunFFG_isRelPrime hgcd R hR.nonzero hR.primPart_nonzero hj hk hjk).isCoprime).map
    (Polynomial.mapRingHom (algebraMap (CFieldSpec.K α) E))
  simp only [Polynomial.coe_mapRingHom] at hcopE
  exact disjoint_roots_of_isCoprime _ _ hcopE

open Classical in
omit [CDiffField α] [CDiffFieldSpec α] in
variable [CFracGcdCoreWf α] in
/-- **A Yun factor stays squarefree over `E`.** Squarefree over char-zero `K` ⟹ separable ⟹ separable over
`E` (base change) ⟹ squarefree over `E`. -/
theorem yun_factor_map_squarefree [CharZero (CFieldSpec.K α)] {E : Type*} [Field E]
    [Algebra (CFieldSpec.K α) E] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (R : DensePoly α)
    (hR : IsYunFactorizationInput R) {j : ℕ} (hj : j < (cSqfreeYunFF R).length) :
    Squarefree ((toPoly ((cSqfreeYunFF R).get ⟨j, hj⟩)).map (algebraMap (CFieldSpec.K α) E)) :=
  ((PerfectField.separable_iff_squarefree.mpr
    (cSqfreeYunFFG_squarefree hgcd R hR.nonzero hR.primPart_nonzero j hj)).map).squarefree

open Classical in
omit [CDiffField α] [CDiffFieldSpec α] in
variable [CFracGcdCoreWf α] in
/-- **The residue multiplicity is the Yun-factor index + 1** (the `hindex` crux). For `c` a root of the
`idx`-th Yun factor of `R` (base-changed to `E`), `rootMultiplicity c (R_E) = idx + 1`: `R ~ ∏Rⱼ^(j+1)`
(reconstruction), and `c` is a simple root of only `R_idx` (squarefree ⟹ mult 1; coprimality ⟹ mult 0
elsewhere), so `rootMult_prodPow_of_unique` gives `1 + idx`. -/
theorem rootMult_R_map_eq_idx_succ [CharZero (CFieldSpec.K α)] {E : Type*} [Field E]
    [Algebra (CFieldSpec.K α) E] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (R : DensePoly α)
    (hR : IsYunFactorizationInput R) (idx : ℕ) (hidx : idx < (cSqfreeYunFF R).length) (c : E)
    (hc : c ∈ ((toPoly ((cSqfreeYunFF R).get ⟨idx, hidx⟩)).map (algebraMap (CFieldSpec.K α) E)).roots) :
    rootMultiplicity c ((toPoly R).map (algebraMap (CFieldSpec.K α) E)) = idx + 1 := by
  have hrec := (cSqfreeYunFFG_reconstruction hgcd R hR.nonzero hR.primPart_nonzero).map
    (Polynomial.mapRingHom (algebraMap (CFieldSpec.K α) E))
  simp only [Polynomial.coe_mapRingHom, prodPow_map] at hrec
  rw [associated_rootMultiplicity_eq hrec c]
  have hprodne : prodPow 1 (((cSqfreeYunFF R).map toPoly).map
      (Polynomial.map (algebraMap (CFieldSpec.K α) E))) ≠ 0 :=
    fun h => ((Polynomial.map_ne_zero_iff (algebraMap (CFieldSpec.K α) E).injective).mpr hR.nonzero)
      (hrec.eq_zero_iff.mpr h)
  have hlen : idx < (((cSqfreeYunFF R).map toPoly).map
      (Polynomial.map (algebraMap (CFieldSpec.K α) E))).length := by
    rw [List.length_map, List.length_map]; exact hidx
  have hget : ∀ (j : ℕ) (hj : j < (cSqfreeYunFF R).length),
      (((cSqfreeYunFF R).map toPoly).map (Polynomial.map (algebraMap (CFieldSpec.K α) E)))[j]'
          (by rw [List.length_map, List.length_map]; exact hj)
        = (toPoly ((cSqfreeYunFF R).get ⟨j, hj⟩)).map (algebraMap (CFieldSpec.K α) E) := by
    intro j hj; rw [List.getElem_map, List.getElem_map]; rfl
  rw [rootMult_prodPow_of_unique c _ 1 idx one_ne_zero hlen hprodne ?_ ?_]
  · omega
  · rw [hget idx hidx]
    exact squarefree_rootMultiplicity_eq_one (yun_factor_map_squarefree hgcd R hR hidx) c
      (Polynomial.isRoot_of_mem_roots hc)
  · intro j hj hjne
    have hj' : j < (cSqfreeYunFF R).length := by rw [List.length_map, List.length_map] at hj; exact hj
    rw [hget j hj']
    apply Polynomial.rootMultiplicity_eq_zero
    intro hroot
    have hcj : c ∈ ((toPoly ((cSqfreeYunFF R).get ⟨j, hj'⟩)).map
        (algebraMap (CFieldSpec.K α) E)).roots :=
      Polynomial.mem_roots'.mpr ⟨(yun_factor_map_squarefree hgcd R hR hj').ne_zero, hroot⟩
    exact (Finset.disjoint_left.mp (disjoint_yun_factors hgcd R hR hidx hj' (Ne.symm hjne))
      (Multiset.mem_toFinset.mpr hc)) (Multiset.mem_toFinset.mpr hcj)

open Classical in
variable [CFracGcdCoreWf α] in
/-- **`hentry` per entry.** Each entry's log argument evaluates to its residue-`c` pole product. Obtains the
entry structure (`mem_cLrtLogArgG`: `p.2 = CPolySubresultant.parametric … (idx+1)`), establishes the index match
`idx+1 = rootMultiplicity c R` (`rootMult_R_map_eq_idx_succ` + `R_E = rtResultantGen`), then applies
`evalLrtArg_eq_fiber_prod`; the fiber `Dd_E = implicitDeriv Dt_E Dstar_E` alignment closes it. -/
theorem entry_log_eq_fiber_prod [CharZero (CFieldSpec.K α)] {E : Type*} [Field E]
    [Algebra (CFieldSpec.K α) E] [Differential E] [DifferentialAlgebra (CFieldSpec.K α) E] [IsAlgClosed E]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt hNum Dstar : DensePoly α) (allpoles : Finset E)
    (hDmonic : (toPoly Dstar).Monic) (hDt0 : (toPoly Dt).natDegree = 0)
    (hAD : (toPoly hNum).natDegree < (toPoly Dstar).natDegree)
    (hsplit : (toPoly Dstar).map (algebraMap (CFieldSpec.K α) E) = Lagrange.nodal allpoles id)
    (hR : IsYunFactorizationInput (cResidueResultantTower Dt hNum Dstar))
    (hm : cdeg (CPolyEngine.monomialDeriv Dt Dstar) = cdeg Dstar - 1)
    (hB : ∀ β ∈ allpoles, ((toPoly (CPolyEngine.monomialDeriv Dt Dstar)).map
        (algebraMap (CFieldSpec.K α) E)).eval β ≠ 0)
    (hA : ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)).natDegree
        < (Lagrange.nodal allpoles id).natDegree)
    (hB_deg : ((toPoly (CPolyEngine.monomialDeriv Dt Dstar)).map (algebraMap (CFieldSpec.K α) E)).natDegree
        ≤ (Lagrange.nodal allpoles id).natDegree - 1)
    (p : DensePoly α × List (DensePoly α)) (hp : p ∈ cLrtLogArg Dt hNum Dstar)
    (c : E) (hc : c ∈ ((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots) :
    evalLrtArg p.2 c = ((allpoles.filter (fun β =>
        ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)).eval β
          / (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
              (Lagrange.nodal allpoles id)).eval β = c)).val.map (fun β => X - C β)).prod := by
  obtain ⟨idx, hmem, _, hp2imp, hp2n⟩ := mem_cLrtLogArgG Dt hNum Dstar p hp
  obtain ⟨hj, hp1'⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hmem)
  have hp1 : (cSqfreeYunFF (cResidueResultantTower Dt hNum Dstar)).get ⟨idx, hj⟩ = p.1 := by
    rw [List.get_eq_getElem]; exact hp1'
  -- `Dd_E = implicitDeriv Dt_E (nodal)` (fiber alignment)
  have hDd : (toPoly (CPolyEngine.monomialDeriv Dt Dstar)).map (algebraMap (CFieldSpec.K α) E)
      = Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
          (Lagrange.nodal allpoles id) := by
    simp only [denote]
    rw [implicitDeriv_map, hsplit]
  -- `rtResultantGen hNum_E (nodal) Dd_E = R_E`, hence `rootMult = idx+1`
  have hRR : rtResultantGen ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E))
        (Lagrange.nodal allpoles id) ((toPoly (CPolyEngine.monomialDeriv Dt Dstar)).map (algebraMap (CFieldSpec.K α) E))
      = (toPoly (cResidueResultantTower Dt hNum Dstar)).map (algebraMap (CFieldSpec.K α) E) := by
    rw [hDd, ← hsplit, ← toPolyG_cResidueResultantTowerG_map Dt hNum Dstar hDmonic hDt0 hAD]
  have hindex : idx + 1 = (rtResultantGen ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E))
      (Lagrange.nodal allpoles id) ((toPoly (CPolyEngine.monomialDeriv Dt Dstar)).map
        (algebraMap (CFieldSpec.K α) E))).rootMultiplicity c := by
    rw [hRR, rootMult_R_map_eq_idx_succ hgcd _ hR idx hj c (hp1 ▸ hc)]
  have hdeg : (Lagrange.nodal allpoles id).natDegree = cdeg Dstar := by
    rw [← hsplit, natDegree_map_eq_of_injective (algebraMap (CFieldSpec.K α) E).injective,
      ← cdegG_eq_natDegree]
  set φ := algebraMap (CFieldSpec.K α) E with hφ
  by_cases heqn : idx + 1 = cdeg Dstar
  · -- **`i = n`: single pure log** — `p.2 = Dstar`, `evalLrtArg = Dstar_E`, and the fiber is *all* poles.
    have hDsep : (Lagrange.nodal allpoles id).Separable := by
      rw [Lagrange.nodal, ← Finset.prod_attach]
      exact separable_prod_X_sub_C_iff'.mpr fun a _ b _ h => Subtype.ext (by simpa using h)
    have hBroots : ∀ β ∈ (Lagrange.nodal allpoles id).roots,
        ((toPoly (CPolyEngine.monomialDeriv Dt Dstar)).map φ).eval β ≠ 0 := fun β hβ =>
      hB β (Finset.mem_val.mp (nodal_roots allpoles ▸ hβ))
    -- `#fiber = deg gcd = rootMult c R_E = idx+1 = cdeg Dstar = #allpoles`, so `fiber = allpoles`.
    have hfiber : (allpoles.filter (fun β => ((toPoly hNum).map φ).eval β
        / (Differential.implicitDeriv ((toPoly Dt).map φ) (Lagrange.nodal allpoles id)).eval β = c))
        = allpoles := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      have hcnt := natDegree_gcd_eq_count_residue_gen ((toPoly hNum).map φ) (Lagrange.nodal allpoles id)
        ((toPoly (CPolyEngine.monomialDeriv Dt Dstar)).map φ) hDsep hBroots c
      have hrm := rootMultiplicity_rtResultantGen_eq_natDegree_gcd ((toPoly hNum).map φ)
        (Lagrange.nodal allpoles id) ((toPoly (CPolyEngine.monomialDeriv Dt Dstar)).map φ) hDsep hBroots hA hB_deg c
      have hcard : (allpoles.filter (fun β => ((toPoly hNum).map φ).eval β
          / (Differential.implicitDeriv ((toPoly Dt).map φ) (Lagrange.nodal allpoles id)).eval β = c)).card
          = idx + 1 := by
        rw [← hDd, hindex, hrm, hcnt, nodal_roots, Multiset.count_map, Finset.card_def,
          Finset.filter_val]
        exact congrArg Multiset.card (Multiset.filter_congr fun a _ => eq_comm)
      have hcardall : allpoles.card = idx + 1 := by
        rw [heqn, ← hdeg, Lagrange.natDegree_nodal]
      omega
    rw [hp2n heqn, evalLrtArg_const_embed_eq Dstar c (hDmonic.map φ), hfiber, hsplit, Lagrange.nodal,
      Finset.prod_eq_multiset_prod]
    simp only [id_eq]
  · -- **`i < n`: subresultant** — the original path, `hi` now derived from `idx+1 ≤ cdeg` (`hindex` + degree).
    have hR_E0 : (rtResultantGen ((toPoly hNum).map φ) (Lagrange.nodal allpoles id)
        ((toPoly (CPolyEngine.monomialDeriv Dt Dstar)).map φ)) ≠ 0 := by
      rw [hRR, Polynomial.map_ne_zero_iff φ.injective]; exact hR.nonzero
    have hle : idx + 1 ≤ cdeg Dstar := by
      have h1 : idx + 1 ≤ (rtResultantGen ((toPoly hNum).map φ) (Lagrange.nodal allpoles id)
          ((toPoly (CPolyEngine.monomialDeriv Dt Dstar)).map φ)).natDegree := by
        rw [hindex]
        refine le_trans (le_of_eq ?_) (Polynomial.natDegree_le_of_dvd
          (Polynomial.pow_rootMultiplicity_dvd _ c) hR_E0)
        rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
      exact le_trans h1 (by rw [← hdeg]; exact natDegree_rtResultantGen_le _ _ _)
    have hi' : (rtResultantGen ((toPoly hNum).map φ) (Lagrange.nodal allpoles id)
        ((toPoly (CPolyEngine.monomialDeriv Dt Dstar)).map φ)).rootMultiplicity c
        < (Lagrange.nodal allpoles id).natDegree := by rw [← hindex, hdeg]; omega
    rw [hp2imp heqn, evalLrtArg_eq_fiber_prod Dstar hNum (CPolyEngine.monomialDeriv Dt Dstar) allpoles c (idx + 1) hm
      hsplit hB hA hB_deg hindex (hindex ▸ hi'), hDd]


open Classical in
omit [CDiffFieldSpec α] in
variable [CFracGcdCoreWf α] in
/-- **`hdisj`.** The entries of `cLrtLogArg` have pairwise-disjoint `Rᵢ`-root sets: each entry comes from a
distinct Yun-factor position, and distinct Yun factors are coprime hence disjoint (`disjoint_yun_factors`).
Via `List.pairwise_filterMap` over the `zipIdx`. -/
theorem disjoint_cLrtLogArgG [CharZero (CFieldSpec.K α)] {E : Type*} [Field E]
    [Algebra (CFieldSpec.K α) E] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt hNum Dstar : DensePoly α)
    (hR : IsYunFactorizationInput (cResidueResultantTower Dt hNum Dstar)) :
    (cLrtLogArg Dt hNum Dstar).Pairwise (fun p q =>
      Disjoint ((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots.toFinset
        ((toPoly q.1).map (algebraMap (CFieldSpec.K α) E)).roots.toFinset) := by
  rw [cLrtLogArg, CPoly.lrtLogArg, squarefreeYun_dense_wf_eq]
  simp_rw [degBound_cnorm_dense_eq, coefficientConstants_dense_eq]
  rw [List.pairwise_filterMap, List.pairwise_iff_getElem]
  intro i j hi hj hij b hb b' hb'
  have hi' : i < (cSqfreeYunFF (cResidueResultantTower Dt hNum Dstar)).length := by
    rwa [List.length_zipIdx] at hi
  have hj' : j < (cSqfreeYunFF (cResidueResultantTower Dt hNum Dstar)).length := by
    rwa [List.length_zipIdx] at hj
  rw [List.getElem_zipIdx] at hb hb'
  simp only [Nat.zero_add] at hb hb'
  -- `b.1`/`b'.1` are the Yun factors at `i`/`j` in BOTH some-branches (`i = n` emits `Dstar`, else the
  -- subresultant), so the disjointness closes identically regardless of the `i = n` branch.
  split_ifs at hb hb' <;>
    first
      | simp only [reduceCtorEq] at hb
      | simp only [reduceCtorEq] at hb'
      | (obtain rfl := Option.some.inj hb; obtain rfl := Option.some.inj hb';
         exact disjoint_yun_factors hgcd _ hR hi' hj' (Nat.ne_of_lt hij))

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **A Yun factor with a root is non-constant** (`¬ (cnorm Rᵢ).length ≤ 1`): a root forces
`natDegree(Rᵢ) ≥ 1`, but `(cnorm Rᵢ).length ≤ 1` forces `natDegree ≤ 0`. This certifies the `filterMap`
guard for the residue-hosting entry in `hcover`. -/
theorem not_len_le_one_of_root {E : Type*} [Field E] [Algebra (CFieldSpec.K α) E] (Ri : DensePoly α)
    (hR0 : toPoly Ri ≠ 0) (c : E)
    (hc : c ∈ ((toPoly Ri).map (algebraMap (CFieldSpec.K α) E)).roots) :
    ¬ ((cnorm Ri : List α).length ≤ 1) := by
  intro hlen
  have hnd := natDegree_toPolyG_le Ri
  have hdvd : (X - C c) ∣ (toPoly Ri).map (algebraMap (CFieldSpec.K α) E) :=
    dvd_iff_isRoot.mpr (isRoot_of_mem_roots hc)
  have hle := Polynomial.natDegree_le_of_dvd hdvd
    ((Polynomial.map_ne_zero_iff (algebraMap (CFieldSpec.K α) E).injective).mpr hR0)
  rw [Polynomial.natDegree_X_sub_C,
    Polynomial.natDegree_map_eq_of_injective (algebraMap (CFieldSpec.K α) E).injective] at hle
  omega


variable [CFracGcdCoreWf α] in
/-- **`hressub` per entry.** Every root `c` of an entry's `Rᵢ` (over `E`) is a residue `res β` of some pole `β`:
`Rᵢ ∣ R` (Yun factor divides the resultant), so `Rᵢ_E.roots ≤ R_E.roots = residues` (`residueResultant_map_roots`).
-/
theorem residue_of_root_cLrtLogArgG_entry [CharZero (CFieldSpec.K α)] {E : Type*} [Field E]
    [Algebra (CFieldSpec.K α) E] [Differential E] [DifferentialAlgebra (CFieldSpec.K α) E] [IsAlgClosed E]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt hNum Dstar : DensePoly α) (allpoles : Finset E)
    (hDmonic : (toPoly Dstar).Monic) (hDt0 : (toPoly Dt).natDegree = 0)
    (hAD : (toPoly hNum).natDegree < (toPoly Dstar).natDegree)
    (hB : ∀ β ∈ ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E)).roots,
        (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
          ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E))).eval β ≠ 0)
    (hB_deg : (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
          ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E))).natDegree
        ≤ ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E)).natDegree - 1)
    (hsplit : (toPoly Dstar).map (algebraMap (CFieldSpec.K α) E) = Lagrange.nodal allpoles id)
    (hR0 : toPoly (cResidueResultantTower Dt hNum Dstar) ≠ 0)
    (p : DensePoly α × List (DensePoly α)) (hp : p ∈ cLrtLogArg Dt hNum Dstar)
    (c : E) (hc : c ∈ ((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots) :
    ∃ β ∈ allpoles, ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)).eval β
        / (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
            (Lagrange.nodal allpoles id)).eval β = c := by
  obtain ⟨idx, hmem, _, _⟩ := mem_cLrtLogArgG Dt hNum Dstar p hp
  have hp1mem : p.1 ∈ cSqfreeYunFF (cResidueResultantTower Dt hNum Dstar) := by
    obtain ⟨hj, hp1'⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hmem)
    exact hp1' ▸ List.getElem_mem hj
  have hdvd : toPoly p.1 ∣ toPoly (cResidueResultantTower Dt hNum Dstar) :=
    (List.dvd_prod (List.mem_map_of_mem (f := toPoly) hp1mem)).trans
      (prod_map_cSqfreeYunFFG_dvd hgcd _ hR0)
  have hR0E : (toPoly (cResidueResultantTower Dt hNum Dstar)).map
      (algebraMap (CFieldSpec.K α) E) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap (CFieldSpec.K α) E).injective).mpr hR0
  have hcR := Multiset.mem_of_le
    (Polynomial.roots.le_of_dvd hR0E (Polynomial.map_dvd (algebraMap (CFieldSpec.K α) E) hdvd)) hc
  rw [residueResultant_map_roots Dt hNum Dstar hDmonic hDt0 hAD hB hB_deg, hsplit] at hcR
  obtain ⟨β, hβ, hres⟩ := Multiset.mem_map.mp hcR
  exact ⟨β, Finset.mem_val.mp (nodal_roots allpoles ▸ hβ), hres⟩

omit [CFieldSpec α] [CDiffFieldSpec α] in
variable [CFracGcdCoreWf α] in
/-- **Reverse membership in `cLrtLogArg`.** A non-constant Yun factor `Rᵢ = (cSqfreeYunFF R)[idx]` hosts an
entry `(Rᵢ, Sᵢ) ∈ cLrtLogArg` — `Sᵢ` is `Dstar` (`idx+1 = deg Dstar`, the single-pure-log branch) or the
subresultant otherwise. The constructive direction of `mem_cLrtLogArgG`, used by `hcover` (which only needs the
hosting entry's `Rᵢ`, not its `Sᵢ`). -/
theorem mem_cLrtLogArgG_of_yun_factor (Dt hNum Dstar : DensePoly α) (idx : ℕ) (Ri : DensePoly α)
    (hget : (cSqfreeYunFF (cResidueResultantTower Dt hNum Dstar))[idx]? = some Ri)
    (hlen : ¬ ((cnorm Ri : List α).length ≤ 1)) :
    ∃ Si, (Ri, Si) ∈ cLrtLogArg Dt hNum Dstar := by
  refine ⟨if idx + 1 = cdeg Dstar then Dstar.map (fun c => ([c] : DensePoly α))
      else CPolySubresultant.parametric Dstar hNum (CPolyEngine.monomialDeriv Dt Dstar) (cdeg Dstar)
        (cdeg (CPolyEngine.monomialDeriv Dt Dstar)) (idx + 1), ?_⟩
  rw [cLrtLogArg, CPoly.lrtLogArg, squarefreeYun_dense_wf_eq]
  simp_rw [degBound_cnorm_dense_eq, coefficientConstants_dense_eq]
  refine List.mem_filterMap.mpr ⟨(Ri, idx), List.mk_mem_zipIdx_iff_getElem?.mpr hget, ?_⟩
  simp only [if_neg hlen]
  simp only [CPolyEngine.cdeg_dense_eq]
  split <;> rfl

open Classical in
variable [CFracGcdCoreWf α] in
/-- **`hcover` per pole.** Every pole `β`'s residue is a root of some entry's `Rᵢ`: the residue is a root of
`R_E` (`residueResultant_map_roots`), which factors as `∏Rᵢ^i` (reconstruction, base-changed), so the residue
is a root of some Yun factor `Rᵢ_E`; that `Rᵢ` is non-constant (`not_len_le_one_of_root`), hence hosts an
entry (`mem_cLrtLogArgG_of_yun_factor`). -/
theorem cover_cLrtLogArgG [CharZero (CFieldSpec.K α)] {E : Type*} [Field E]
    [Algebra (CFieldSpec.K α) E] [Differential E] [DifferentialAlgebra (CFieldSpec.K α) E] [IsAlgClosed E]
    (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt hNum Dstar : DensePoly α) (allpoles : Finset E)
    (hDmonic : (toPoly Dstar).Monic) (hDt0 : (toPoly Dt).natDegree = 0)
    (hAD : (toPoly hNum).natDegree < (toPoly Dstar).natDegree)
    (hB : ∀ β ∈ ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E)).roots,
        (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
          ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E))).eval β ≠ 0)
    (hB_deg : (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
          ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E))).natDegree
        ≤ ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E)).natDegree - 1)
    (hsplit : (toPoly Dstar).map (algebraMap (CFieldSpec.K α) E) = Lagrange.nodal allpoles id)
    (hR : IsYunFactorizationInput (cResidueResultantTower Dt hNum Dstar))
    (β : E) (hβ : β ∈ allpoles) :
    ∃ p ∈ cLrtLogArg Dt hNum Dstar,
      ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)).eval β
          / (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
              (Lagrange.nodal allpoles id)).eval β
        ∈ ((toPoly p.1).map (algebraMap (CFieldSpec.K α) E)).roots.toFinset := by
  set φ := algebraMap (CFieldSpec.K α) E
  set res := ((toPoly hNum).map φ).eval β
      / (Differential.implicitDeriv ((toPoly Dt).map φ) (Lagrange.nodal allpoles id)).eval β
  have hresR : res ∈ ((toPoly (cResidueResultantTower Dt hNum Dstar)).map φ).roots := by
    rw [residueResultant_map_roots Dt hNum Dstar hDmonic hDt0 hAD hB hB_deg, hsplit]
    exact Multiset.mem_map.mpr ⟨β, nodal_roots allpoles ▸ Finset.mem_val.mpr hβ, rfl⟩
  have hrec := (cSqfreeYunFFG_reconstruction hgcd _ hR.nonzero hR.primPart_nonzero).map
    (Polynomial.mapRingHom φ)
  simp only [Polynomial.coe_mapRingHom, prodPow_map] at hrec
  have hprodne : prodPow 1 ((cSqfreeYunFF (cResidueResultantTower Dt hNum Dstar)).map toPoly
      |>.map (Polynomial.map φ)) ≠ 0 :=
    fun h => ((Polynomial.map_ne_zero_iff φ.injective).mpr hR.nonzero) (hrec.eq_zero_iff.mpr h)
  have hresP := Multiset.mem_of_le (Polynomial.roots.le_of_dvd hprodne hrec.dvd) hresR
  obtain ⟨v, hv, hresv⟩ := mem_roots_prodPow 1 one_ne_zero _ res hprodne hresP
  rw [List.map_map, List.mem_map] at hv
  obtain ⟨Ri, hRimem, hRiv⟩ := hv
  obtain ⟨idx, hidx⟩ := List.getElem?_of_mem hRimem
  have hRi0 : toPoly Ri ≠ 0 := (cSqfreeYunFFG_monic hgcd _ hR.nonzero Ri hRimem).ne_zero
  have hresRi : res ∈ ((toPoly Ri).map φ).roots := by
    rw [Function.comp_apply] at hRiv; rwa [← hRiv] at hresv
  obtain ⟨Si, hSi⟩ := mem_cLrtLogArgG_of_yun_factor Dt hNum Dstar idx Ri hidx
    (not_len_le_one_of_root Ri hRi0 res hresRi)
  exact ⟨(Ri, Si), hSi, Multiset.mem_toFinset.mpr hresRi⟩

open Classical in
/-- **★ The complete LRT reduced-case soundness** (modulo the log-part match). Assembles the whole
`IsIntegralResultLrt` for `cIntegrateReducedLrt Dt a d`: the Hermite half is discharged outright by
`hherm_lrt_E` (base-change of `cHermiteReduceTowerG_field_identity`), leaving only the log-part match `hlog`
(`logResidueSumLrt (cLrtLogArg …) = hNum/Dstar` over every alg-closed `E`, provable via
`logResidueSumLrtG_eq_normalPart_of_yun` + the Yun facts). `hd0`/`hpp`/`hcopgcd` are the genuine Hermite-side
conditions. -/
theorem isIntegralResultLrtG_cIntegrateReducedLrtG.{u} [CharZero (CFieldSpec.K α)]
    [Algebra ℚ (CFieldSpec.K α)] [CFracGcdCoreWf α] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α)))
    (Dt a d : DensePoly α) (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1 ≠ 0)
    (hlog : ∀ (E : Type u) [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E]
        [DifferentialAlgebra (CFieldSpec.K α) E] [IsAlgClosed E],
        (logResidueSumLrt Dt (cLrtLogArg Dt (cHermiteReduceTower Dt a d).2.1
              (cHermiteReduceTower Dt a d).2.2) : RatFunc E)
          = amGExt (toPoly (cHermiteReduceTower Dt a d).2.1)
            / amGExt (toPoly (cHermiteReduceTower Dt a d).2.2)) :
    IsIntegralResultLrt.{_, u} Dt a d (cIntegrateReducedLrt Dt a d) := by
  refine isIntegralResultLrtG_of_hherm_of_logMatch Dt a d (cIntegrateReducedLrt Dt a d)
    (cHermiteReduceTower Dt a d).2.1 (cHermiteReduceTower Dt a d).2.2 hlog ?_
  intro E _ _ _ _ _ _
  exact hherm_lrt_E hgcd Dt a d hd0 hpp hcopgcd

open scoped Differential in
open Classical in
variable [CFracGcdCoreWf α] in
/-- **The final `hlog` wiring.** Plugs the five Yun facts into `logResidueSumLrtG_eq_normalPart_of_yun`,
discharging `hsplit` via `monic_separable_eq_nodal` (`Dstar` monic + separable). The residue side
conditions are normality, properness, degree control, and polynomial-part cancellation. Conclusion:
`logResidueSumLrt (cLrtLogArg …) = hNum/Dstar`, the capstone's `hlog`. -/
theorem logMatch_of_setup [CharZero (CFieldSpec.K α)] {E : Type*} [Field E]
    [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E] [DifferentialAlgebra (CFieldSpec.K α) E]
    [IsAlgClosed E] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt hNum Dstar : DensePoly α)
    (hDmonic : (toPoly Dstar).Monic) (hDsep : (toPoly Dstar).Separable)
    (hDt0 : (toPoly Dt).natDegree = 0) (hAD : (toPoly hNum).natDegree < (toPoly Dstar).natDegree)
    (hR : IsYunFactorizationInput (cResidueResultantTower Dt hNum Dstar))
    (hm : cdeg (CPolyEngine.monomialDeriv Dt Dstar) = cdeg Dstar - 1)
    (hB : ∀ β ∈ ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E)).roots,
        (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
          ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E))).eval β ≠ 0)
    (hB_deg : (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
          ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E))).natDegree
        ≤ ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E)).natDegree - 1)
    (hAnd : ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)).natDegree
        < ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E)).natDegree)
    (hAdeg : ((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)).degree
        < ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E)).roots.toFinset.card)
    (hnorm : ∀ β ∈ ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E)).roots.toFinset,
        ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E)).eval β ≠ β′)
    (hcancel : ∑ β ∈ ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E)).roots.toFinset,
        algebraMap E[X] (RatFunc E)
        (C (((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)).eval β
              / (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
                  (Lagrange.nodal ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E)).roots.toFinset
                    id)).eval β)
          * ((((toPoly Dt).map (algebraMap (CFieldSpec.K α) E)) - C (β′)) /ₘ (X - C β))) = 0) :
    (logResidueSumLrt Dt (cLrtLogArg Dt hNum Dstar) : RatFunc E)
      = amGExt (toPoly hNum) / amGExt (toPoly Dstar) := by
  set φ := algebraMap (CFieldSpec.K α) E with hφdef
  set allpoles := ((toPoly Dstar).map φ).roots.toFinset with hallpoles
  have hmonicE : ((toPoly Dstar).map φ).Monic := hDmonic.map φ
  have hsepE : ((toPoly Dstar).map φ).Separable := (Polynomial.separable_map φ).mpr hDsep
  have hsplit : (toPoly Dstar).map φ = Lagrange.nodal allpoles id :=
    monic_separable_eq_nodal _ hmonicE hsepE
  have hnd : (Lagrange.nodal allpoles id).natDegree = ((toPoly Dstar).map φ).natDegree := by rw [hsplit]
  have hDd2 : (toPoly (CPolyEngine.monomialDeriv Dt Dstar)).map φ
      = Differential.implicitDeriv ((toPoly Dt).map φ) ((toPoly Dstar).map φ) := by
    simp only [denote]
    rw [implicitDeriv_map]
  rw [logResidueSumLrtG_eq_normalPart_of_yun Dt hNum (cLrtLogArg Dt hNum Dstar) allpoles _ rfl
    (fun p hp => nodup_roots_cLrtLogArgG_entry hgcd Dt hNum Dstar hR p hp)
    (fun p hp c hc => residue_of_root_cLrtLogArgG_entry hgcd Dt hNum Dstar allpoles hDmonic hDt0 hAD
      hB hB_deg hsplit hR.nonzero p hp c hc)
    (disjoint_cLrtLogArgG hgcd Dt hNum Dstar hR)
    (fun β hβ => cover_cLrtLogArgG hgcd Dt hNum Dstar allpoles hDmonic hDt0 hAD hB hB_deg hsplit hR
      β hβ)
    (fun p hp c hc => entry_log_eq_fiber_prod hgcd Dt hNum Dstar allpoles hDmonic hDt0 hAD hsplit hR
      hm (fun β hβ => by rw [hDd2]; exact hB β (Multiset.mem_toFinset.mp hβ))
      (by rw [hnd]; exact hAnd) (by rw [hnd, hDd2]; exact hB_deg) p hp c hc)
    hAdeg hnorm hcancel]
  rw [← hsplit]
  simp only [amGExt, hφdef]

open scoped Differential in
open Classical in
/-- **`hcancel` is automatic in the primitive case.** When `Dt` is a constant (`(toPoly Dt).natDegree = 0` —
the primitive monomial `Dθ ∈ k`), the factor `((toPoly Dt).map φ − C β′) /ₘ (X − β)` is a constant divided by
a linear, hence `0`, so the whole RT-cancellation sum vanishes with **no** side hypothesis. -/
theorem hcancel_of_primitive {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    {E : Type*} [Field E] [Algebra (CFieldSpec.K α) E] [Differential E]
    (Dt hNum Dstar : DensePoly α) (hDt0 : (toPoly Dt).natDegree = 0) :
    (∑ β ∈ ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E)).roots.toFinset,
        algebraMap E[X] (RatFunc E)
        (C (((toPoly hNum).map (algebraMap (CFieldSpec.K α) E)).eval β
              / (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
                  (Lagrange.nodal ((toPoly Dstar).map (algebraMap (CFieldSpec.K α) E)).roots.toFinset
                    id)).eval β)
          * ((((toPoly Dt).map (algebraMap (CFieldSpec.K α) E)) - C (β′)) /ₘ (X - C β))) = 0) := by
  apply Finset.sum_eq_zero
  intro β _
  have hdiv : (((toPoly Dt).map (algebraMap (CFieldSpec.K α) E)) - C (β′)) /ₘ (X - C β) = 0 := by
    rw [Polynomial.divByMonic_eq_zero_iff (Polynomial.monic_X_sub_C β), Polynomial.degree_X_sub_C]
    calc (((toPoly Dt).map (algebraMap (CFieldSpec.K α) E)) - C (β′)).degree
        ≤ max (((toPoly Dt).map (algebraMap (CFieldSpec.K α) E)).degree) ((C (β′) : E[X]).degree) :=
          Polynomial.degree_sub_le _ _
      _ ≤ 0 := max_le (le_trans Polynomial.degree_map_le
          (le_trans (Polynomial.degree_le_natDegree) (by rw [hDt0]; rfl))) Polynomial.degree_C_le
      _ < 1 := by decide
  rw [hdiv, mul_zero, map_zero]

open scoped Differential in
open Classical in
variable [CFracGcdCoreWf α] in
/-- **The assembled LRT reduced-case soundness**: the root-free analogue of `hreduced`, fully composed.
Threads `logMatch_of_setup` (the log-part match, from the five Yun facts) into the capstone
`isIntegralResultLrtG_cIntegrateReducedLrtG`, yielding `IsIntegralResultLrt Dt a d (cIntegrateReducedLrt Dt a d)`
outright. `hd0`/`hpp`/`hcopgcd` are the Hermite-side conditions; `Dstar = (cHermiteReduceTower Dt a d).2.2`
monic + separable is *discharged internally* (`toPolyG_cHermiteReduceTowerG_Dstar_monic`/`_squarefree`);
`hDt0`/`hAD`/`hm` and `hR` are the `K`-level residue-data facts; `hR` bundles the residue
resultant nonzero and primitive-part nonzero hypotheses. `hE`
bundles the **two genuine** per-splitting-extension conditions: `implicitDeriv` nonvanishing at the poles
(`hB`) and normality `hnorm` (`η ≠ Dβ`). The pure-log branch is handled directly by `cLrtLogArg` at
`i = deg Dstar`, so `entry_log_eq_fiber_prod` covers it as well. Everything else is discharged
internally: the RT cancellation `hcancel` is
automatic in the primitive case (`hDt0`: `Dt` constant, via `hcancel_of_primitive`), and the three
degree/properness conditions `hAnd`/`hAdeg`/`hB_deg` follow from the `K`-level `hAD`/`hm` by base change
(`φ = algebraMap` preserves `natDegree` over a field; `Dstar` monic + separable ⟹ its root count is its degree).
Unlike the rational `hreduced`, this is general: residues may be algebraic. -/
theorem isIntegralResultLrtG_cIntegrateReducedLrtG_of_setup.{u} [CharZero (CFieldSpec.K α)]
    [Algebra ℚ (CFieldSpec.K α)] (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α)
    (hd0 : toPoly d ≠ 0) (hpp : (toPoly d).primPart ≠ 0)
    (hcopgcd : ∀ x ∈ (cSqfreeYunFF d).zipIdx.filter (fun x => ¬ (x.2 + 1 ≤ 1)),
      (toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1).natDegree = 0
      ∧ toPoly (CPolyEuclidean.gcdExt (cmul (CPolyEuclidean.div d (cpow x.1 (x.2 + 1)))
          (CPolyEngine.monomialDeriv Dt x.1)) x.1).1 ≠ 0)
    (hDt0 : (toPoly Dt).natDegree = 0)
    (hAD : (toPoly (cHermiteReduceTower Dt a d).2.1).natDegree
        < (toPoly (cHermiteReduceTower Dt a d).2.2).natDegree)
    (hR : IsYunFactorizationInput
        (cResidueResultantTower Dt (cHermiteReduceTower Dt a d).2.1
          (cHermiteReduceTower Dt a d).2.2))
    (hm : cdeg (CPolyEngine.monomialDeriv Dt (cHermiteReduceTower Dt a d).2.2)
        = cdeg (cHermiteReduceTower Dt a d).2.2 - 1)
    (hE : ∀ (E : Type u) [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E]
        [DifferentialAlgebra (CFieldSpec.K α) E] [IsAlgClosed E],
        ∀ β ∈ ((toPoly (cHermiteReduceTower Dt a d).2.2).map
                (algebraMap (CFieldSpec.K α) E)).roots.toFinset,
            ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E)).eval β ≠ β′) :
    IsIntegralResultLrt.{_, u} Dt a d (cIntegrateReducedLrt Dt a d) := by
  have hDmonic := toPolyG_cHermiteReduceTowerG_Dstar_monic hgcd Dt a d hd0
  have hDsep : (toPoly (cHermiteReduceTower Dt a d).2.2).Separable :=
    PerfectField.separable_iff_squarefree.mpr
      (toPolyG_cHermiteReduceTowerG_Dstar_squarefree hgcd Dt a d hd0 hpp)
  refine isIntegralResultLrtG_cIntegrateReducedLrtG hgcd Dt a d hd0 hpp hcopgcd (fun E _ _ _ _ _ _ => ?_)
  have hnorm := hE E
  -- The degree-side conditions are *discharged internally* from the `K`-level facts by base change
  -- (`φ = algebraMap (CFieldSpec.K α) E` preserves `natDegree` over a field), leaving only the genuine
  -- normality `hnorm`. (`hB` — `implicitDeriv` nonvanishing at the poles — is now *derived* from `hnorm`:
  -- `hnorm` ⟺ `IsCoprime Dstar_E (implicitDeriv Dt_E Dstar_E)`, and coprimality means no shared root.)
  have hAnd : ((toPoly (cHermiteReduceTower Dt a d).2.1).map (algebraMap (CFieldSpec.K α) E)).natDegree
      < ((toPoly (cHermiteReduceTower Dt a d).2.2).map (algebraMap (CFieldSpec.K α) E)).natDegree := by
    rw [Polynomial.natDegree_map, Polynomial.natDegree_map]; exact hAD
  have hDmonicE : ((toPoly (cHermiteReduceTower Dt a d).2.2).map
      (algebraMap (CFieldSpec.K α) E)).Monic := hDmonic.map _
  have hDsepE : ((toPoly (cHermiteReduceTower Dt a d).2.2).map
      (algebraMap (CFieldSpec.K α) E)).Separable := hDsep.map
  have hB : ∀ β ∈ ((toPoly (cHermiteReduceTower Dt a d).2.2).map
          (algebraMap (CFieldSpec.K α) E)).roots,
      (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
        ((toPoly (cHermiteReduceTower Dt a d).2.2).map
          (algebraMap (CFieldSpec.K α) E))).eval β ≠ 0 := by
    intro β hβ
    have hcop : IsCoprime ((toPoly (cHermiteReduceTower Dt a d).2.2).map (algebraMap (CFieldSpec.K α) E))
        (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
          ((toPoly (cHermiteReduceTower Dt a d).2.2).map (algebraMap (CFieldSpec.K α) E))) := by
      rw [monic_separable_eq_nodal _ hDmonicE hDsepE, Lagrange.nodal]
      exact (isCoprime_prod_X_sub_C_implicitDeriv_iff _ _).mpr (by simpa using hnorm)
    exact isCoprime_X_sub_C_iff.mp (hcop.of_isCoprime_of_dvd_left
      (dvd_iff_isRoot.mpr (Polynomial.isRoot_of_mem_roots hβ)))
  have hcard : ((toPoly (cHermiteReduceTower Dt a d).2.2).map
        (algebraMap (CFieldSpec.K α) E)).roots.toFinset.card
      = ((toPoly (cHermiteReduceTower Dt a d).2.2).map (algebraMap (CFieldSpec.K α) E)).natDegree := by
    conv_rhs => rw [monic_separable_eq_nodal _ hDmonicE hDsepE]
    rw [Lagrange.natDegree_nodal]
  have hAdeg : ((toPoly (cHermiteReduceTower Dt a d).2.1).map (algebraMap (CFieldSpec.K α) E)).degree
      < ((toPoly (cHermiteReduceTower Dt a d).2.2).map
          (algebraMap (CFieldSpec.K α) E)).roots.toFinset.card := by
    rw [hcard]; exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hAnd)
  have hB_deg : (Differential.implicitDeriv ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E))
        ((toPoly (cHermiteReduceTower Dt a d).2.2).map (algebraMap (CFieldSpec.K α) E))).natDegree
      = ((toPoly (cHermiteReduceTower Dt a d).2.2).map (algebraMap (CFieldSpec.K α) E)).natDegree - 1 := by
    rw [← implicitDeriv_map, ← toPolyG_cmonomialDeriv, Polynomial.natDegree_map, Polynomial.natDegree_map,
      ← cdegG_eq_natDegree, ← cdegG_eq_natDegree, hm]
  exact logMatch_of_setup hgcd Dt (cHermiteReduceTower Dt a d).2.1
    (cHermiteReduceTower Dt a d).2.2 hDmonic hDsep hDt0 hAD hR hm hB hB_deg.le hAnd hAdeg hnorm
    (hcancel_of_primitive Dt (cHermiteReduceTower Dt a d).2.1 (cHermiteReduceTower Dt a d).2.2 hDt0)

universe u

open scoped Differential in
open Classical in
variable [CFracGcdCoreWf α] in
/-- **The `∀E` residue pole-normality condition, as a universe-polymorphic `def`** (mirroring
`IsIntegralResultLrt`): at every algebraically-closed differential extension `E` of `K = CFieldSpec.K α`, the
monomial derivation `Dt` avoids the pole derivatives (`η ≠ β′`). Being a `def` — not an inline `∀ (E : Type u)`
field — its `E`-universe auto-generalizes, so it can be instantiated at `E = AlgebraicClosure K` (whose universe
is the *existential* one of `CFieldSpec.K`), which a rigid structure-field universe cannot. This is what lets
`hR0` be *derived* rather than assumed (see `hR0_of_normalityData`). -/
def LrtPoleNormalityData (Dt a d : DensePoly α) : Prop :=
  ∀ (E : Type*) [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E]
    [DifferentialAlgebra (CFieldSpec.K α) E] [IsAlgClosed E],
    ∀ β ∈ ((toPoly (cHermiteReduceTower Dt a d).2.2).map
            (algebraMap (CFieldSpec.K α) E)).roots.toFinset,
        ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E)).eval β ≠ β′

open scoped Differential in
/-- **The genuine primitive-monomial property (input-INDEPENDENT).** At every alg-closed differential extension
`E`, `(Dt)(β) ≠ β′` for **every** `β ∈ E` (not just the poles of some integrand). In the primitive case
(`deg Dt = 0`, `(Dt)(β) = η` constant) this is exactly `η ∉ range(D_E)`: `η = Dt` is not a derivative, so
`t` is a genuine monomial. A property of the tower
LEVEL's monomial `Dt` alone — so it discharges the per-input `hE` for **every** `a/d` at once. -/
def GenuinePrimitiveMonomialLrt (Dt : DensePoly α) : Prop :=
  ∀ (E : Type*) [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E]
    [DifferentialAlgebra (CFieldSpec.K α) E] [IsAlgClosed E],
    ∀ (β : E), ((toPoly Dt).map (algebraMap (CFieldSpec.K α) E)).eval β ≠ β′

open scoped Differential in
variable [CFracGcdCoreWf α] in
/-- **Per-input pole-normality from the input-independent monomial property.** `LrtPoleNormalityData Dt a d`
(quantified over a specific integrand's Hermite poles) is an immediate consequence of
`GenuinePrimitiveMonomialLrt Dt` (which covers *all* `β`); the input `a/d` drops out. This is the faithfulness
reframing: genuine normality is a property of the monomial, not of each integrand. -/
theorem lrtPoleNormalityData_of_genuineMonomial {Dt a d : DensePoly α}
    (hgen : GenuinePrimitiveMonomialLrt Dt) : LrtPoleNormalityData Dt a d :=
  fun E _ _ _ _ _ _ β _ => hgen E β

open scoped Differential in
open Classical in
variable [CFracGcdCoreWf α] in
/-- **The genuine per-input side conditions of the assembled LRT reduced soundness**, bundled. Beyond the
automatic facts (`hpp`/`hRpp`, both `primPart_ne_zero`), `isIntegralResultLrtG_cIntegrateReducedLrtG_of_setup`
needs the residue-data plus tower-nondegeneracy hypotheses. All of the *normality* ones —
the Yun-factor coprimality `hcopgcd`, the residue resultant nonzero `hR0`, the monomial-derivative degree
`hm`, and the per-input pole-normality `hnorm` — are derived from the single **input-independent**
monomial property `hE` (`hcopgcd_of_genuineMonomial`, `hR0_of_normalityData`, `hm_of_genuineMonomial`,
`lrtPoleNormalityData_of_genuineMonomial`). The **primitive-case scope tag** `hDt0` (`deg Dt = 0`) is a
decidable runtime guard: `cIntegrateCaseLrt`'s `if cdeg Dt = 0` branch
discharges it, so a successful run supplies it (`isIntegralResultLrtG_cIntegrateReducedLrtG_of_genuine` takes it
as an explicit hypothesis, threaded from the branch). The **Hermite properness `hAD`** is supplied from input
properness: `isIntegralResultLrtG_cIntegrateReducedLrtG_of_genuine` takes `deg a < deg d`
(supplied by `crNormNum_degree_lt_crNormDen` at the canonical normal part) and case-splits on `deg Dstar` —
deriving `.natDegree hAD` from the `.degree` discharge (`hAD_degree_of_genuineMonomial`) when there are poles,
and handling `deg Dstar = 0` as the trivially-sound no-poles branch (`…_of_noPoles`). So this structure now
carries the **single** genuine monomial condition `hE`; `cLrtLogArg`'s `i = deg Dstar` branch handles the
pure-single-log case. -/
structure LrtReducedGenuineData (Dt a d : DensePoly α) : Prop where
  /-- The **single** genuine condition: the **input-independent** monomial normality `η = Dt` is not a
  derivative (`GenuinePrimitiveMonomialLrt Dt`). *Every* per-input condition — the Yun-factor coprimality
  `hcopgcd`, the residue resultant nonzero `hR0`, the monomial-derivative degree drop `hm`, the pole-normality
  `LrtPoleNormalityData`, and now the Hermite properness `hAD` (via the `.degree` discharge + the no-poles
  case-split, `isIntegralResultLrtG_cIntegrateReducedLrtG_of_genuine`) — is *derived* from it, so this depends
  only on the tower level's monomial, not on `a/d`. (The `a d` parameters are now vestigial.) -/
  hE : GenuinePrimitiveMonomialLrt Dt

-- `isIntegralResultLrtG_cIntegrateReducedLrtG_of_genuine` lives in `LrtResidueResultantDischarge` (it derives
-- `hR0` from `hE` via the algebraic closure, which is downstream of this file).

end DeepWiki.SymbolicIntegration
