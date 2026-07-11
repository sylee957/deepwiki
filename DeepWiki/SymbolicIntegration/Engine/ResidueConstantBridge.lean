import DeepWiki.SymbolicIntegration.Engine.YunSquarefreeDecomposition
import DeepWiki.SymbolicIntegration.Engine.LrtGuarded

/-! # The residue bridge — a passing guard forces the result residues constant

The `←` sufficiency of `primitiveLrtDecides` needs: if the residue resultant `R` (monic) has `D`-constant
coefficients (the guard `cResidueConstantGuard`), then each of its squarefree Yun factors does too
(`allResiduesConstantLrt`). Abstractly, over `K[X]` with `D = Differential.mapCoeffs` (the coefficient-wise
derivation, `D X = 0`): if `mapCoeffs P = 0` and `P = Qⁱ · M` with `Q` monic and coprime to `M` (a Yun
factor at multiplicity `i ≥ 1`, char 0), then `mapCoeffs Q = 0`.

This file proves that abstract core (`mapCoeffs_eq_zero_of_coprime_pow_factor`). -/

namespace DeepWiki.SymbolicIntegration.ResidueBridge

open Polynomial Differential

variable {K : Type*} [Field K] [Differential K] [CharZero K]

omit [CharZero K] in
/-- **A monic polynomial's `mapCoeffs` drops degree.** The top coefficient of `Q` is `1`, whose derivative is
`0`, and higher coefficients vanish — so `mapCoeffs Q` has degree `< deg Q`. -/
theorem natDegree_mapCoeffs_lt {Q : K[X]} (hQ : Q.Monic) (hd : 0 < Q.natDegree) :
    (mapCoeffs Q).natDegree < Q.natDegree := by
  have hle : (mapCoeffs Q).natDegree ≤ Q.natDegree - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_mapCoeffs]
    rcases eq_or_lt_of_le (show Q.natDegree ≤ N by omega) with h | h
    · rw [← h, hQ.coeff_natDegree]; exact Derivation.map_one_eq_zero _
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h]; exact map_zero _
  omega

/-- **The abstract residue-bridge core.** If `mapCoeffs P = 0` (all coefficients `D`-constant) and
`P = Qⁱ · M` with `Q` monic and coprime to `M` (`i ≥ 1`, char 0), then `mapCoeffs Q = 0`. Proof: dividing the
Leibniz expansion `mapCoeffs P = Qⁱ⁻¹ · (Q·mapCoeffs M + i·M·mapCoeffs Q)` by `Qⁱ⁻¹` gives
`Q·mapCoeffs M + i·M·mapCoeffs Q = 0`, so `Q ∣ mapCoeffs Q` (coprime `M`, char-0 unit `i`); and `Q` monic
forces `mapCoeffs Q` to drop degree, hence vanish. -/
theorem mapCoeffs_eq_zero_of_coprime_pow_factor {P Q M : K[X]} {i : ℕ} (hi : 1 ≤ i) (hQ : Q.Monic)
    (hfact : P = Q ^ i * M) (hcop : IsCoprime Q M) (hP : mapCoeffs P = 0) :
    mapCoeffs Q = 0 := by
  -- Leibniz expansion of `mapCoeffs P`, with `Qⁱ = Qⁱ⁻¹ · Q` factored out.
  have hpow : Q ^ i = Q ^ (i - 1) * Q := by rw [← pow_succ]; congr 1; omega
  have hexp : mapCoeffs P = Q ^ (i - 1) * (Q * mapCoeffs M + (i : K[X]) * (M * mapCoeffs Q)) := by
    rw [hfact, Derivation.leibniz, Derivation.leibniz_pow, hpow]
    simp only [smul_eq_mul, nsmul_eq_mul]
    ring
  -- Cancel the nonzero factor `Qⁱ⁻¹` in the domain `K[X]`.
  have hQ0 : Q ^ (i - 1) ≠ 0 := pow_ne_zero _ hQ.ne_zero
  rw [hP] at hexp
  have hzero : Q * mapCoeffs M + (i : K[X]) * (M * mapCoeffs Q) = 0 := by
    rcases mul_eq_zero.mp hexp.symm with h | h
    · exact absurd h hQ0
    · exact h
  -- `Q ∣ i·(M·mapCoeffs Q)`; `i` is a unit and `Q` coprime to `M`, so `Q ∣ mapCoeffs Q`.
  have hdvd : Q ∣ mapCoeffs Q := by
    have h1 : Q ∣ (i : K[X]) * (M * mapCoeffs Q) := ⟨-mapCoeffs M, by linear_combination hzero⟩
    have hiU : IsUnit ((i : K[X])) := by
      rw [show ((i : K[X])) = C (i : K) by simp]
      exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))
    have h2 : Q ∣ M * mapCoeffs Q := (IsUnit.dvd_mul_left hiU).mp h1
    exact hcop.dvd_of_dvd_mul_left h2
  -- `Q` monic ⟹ `mapCoeffs Q` drops degree ⟹ `mapCoeffs Q = 0`.
  by_contra hne
  rcases Nat.eq_zero_or_pos Q.natDegree with h0 | hpos
  · have hc0 : Q.coeff 0 = 1 := by have h := hQ.coeff_natDegree; rwa [h0] at h
    have hQ1 : Q = 1 := by rw [Polynomial.eq_C_of_natDegree_eq_zero h0, hc0, map_one]
    exact hne (by rw [hQ1]; exact Derivation.map_one_eq_zero _)
  · have hlt := natDegree_mapCoeffs_lt hQ hpos
    have := Polynomial.natDegree_le_of_dvd hdvd hne
    omega

omit [Differential K] [CharZero K] in
/-- List product of coprime terms: `q` coprime to each entry ⟹ coprime to the product. -/
private theorem isCoprime_list_prod_right {q : K[X]} {L : List K[X]}
    (h : ∀ x ∈ L, IsCoprime q x) : IsCoprime q L.prod := by
  induction L with
  | nil => simpa using isCoprime_one_right
  | cons a t ih =>
    rw [List.prod_cons]
    exact (h a (by simp)).mul_right (ih fun x hx => h x (by simp [hx]))

/-- **The core, extended to a full pairwise-coprime monic factorization.** If `P = ∏ Qₖ^eₖ` with the `Qₖ`
pairwise coprime, each monic with `eₖ ≥ 1`, and `mapCoeffs P = 0`, then `mapCoeffs Qₖ = 0` for every
factor `Qₖ`. This is the core `mapCoeffs_eq_zero_of_coprime_pow_factor` applied uniformly across the
squarefree Yun decomposition. -/
theorem mapCoeffs_eq_zero_of_mem_coprime_prod {P : K[X]} {L : List (K[X] × ℕ)}
    (hmonic : ∀ q ∈ L, (Prod.fst q).Monic) (hpos : ∀ q ∈ L, 1 ≤ q.2)
    (hcop : L.Pairwise (fun a b => IsCoprime a.1 b.1))
    (hfact : P = (L.map fun q => q.1 ^ q.2).prod) (hP : mapCoeffs P = 0)
    {q : K[X] × ℕ} (hq : q ∈ L) : mapCoeffs q.1 = 0 := by
  -- Move `q` to the front: `L = s ++ q :: t ~ q :: (s ++ t)`.
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hq
  have hperm : (s ++ q :: t).Perm (q :: (s ++ t)) := List.perm_middle
  -- `P = q.1 ^ q.2 · (product of the rest)`.
  have hPeq : P = q.1 ^ q.2 * ((s ++ t).map fun r => r.1 ^ r.2).prod := by
    rw [hfact, (hperm.map fun r => r.1 ^ r.2).prod_eq, List.map_cons, List.prod_cons]
  -- `q.1` coprime to every remaining factor (pairwise coprimality across the permuted list).
  have hcopP : (q :: (s ++ t)).Pairwise (fun a b => IsCoprime a.1 b.1) :=
    (hperm.pairwise_iff (fun h => h.symm)).mp hcop
  have hqcop : ∀ r ∈ s ++ t, IsCoprime q.1 r.1 := (List.pairwise_cons.mp hcopP).1
  have hcop' : IsCoprime q.1 ((s ++ t).map fun r => r.1 ^ r.2).prod := by
    apply isCoprime_list_prod_right
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact (hqcop r hr).pow_right
  exact mapCoeffs_eq_zero_of_coprime_pow_factor (hpos q hq) (hmonic q hq) hPeq hcop' hP

end DeepWiki.SymbolicIntegration.ResidueBridge

/-! ## Stage 1 — pairwise coprimality of the Yun factors -/

namespace DeepWiki.SymbolicIntegration

open DensePoly Polynomial Classical

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CFracGcdCoreWf α] [CharZero (CFieldSpec.K α)]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- Each Yun factor is `Associated` to a distinct `sqfreeFactPart` of the residue resultant (index `1 + k`),
by `cSqfreeYunFFG_forall₂`. -/
theorem associated_toPolyG_cSqfreeYunFFG_get (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (R : DensePoly α)
    (hR0 : toPoly R ≠ 0) (hpp : (toPoly R).primPart ≠ 0)
    (k : ℕ) (hk : k < (cSqfreeYunFF R).length) :
    Associated (toPoly (cSqfreeYunFF R)[k]) (sqfreeFactPart (toPoly R) (1 + k)) := by
  have hf₂ := cSqfreeYunFFG_forall₂ hgcd R hR0 hpp
  obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.mp hf₂
  have hk₁ : k < ((cSqfreeYunFF R).map toPoly).length := by simpa using hk
  have hk₂ : k < ((List.range (cSqfreeYunFF R).length).map
      fun j => sqfreeFactPart (toPoly R) (1 + j)).length := by simpa using hk
  have h := hget k hk₁ hk₂
  simpa using h

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Stage 1.** The Yun factors of `R` (as polynomial images) are pairwise coprime: each is `Associated` to a
distinct `sqfreeFactPart` of `toPoly R`, and those are pairwise relatively prime
(`sqfreeFactPart_isRelPrime`). -/
theorem pairwise_isCoprime_toPolyG_cSqfreeYunFFG (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (R : DensePoly α)
    (hR0 : toPoly R ≠ 0) (hpp : (toPoly R).primPart ≠ 0) :
    (cSqfreeYunFF R).Pairwise (fun a b => IsCoprime (toPoly a) (toPoly b)) := by
  rw [List.pairwise_iff_get]
  intro i j hij
  have ai := associated_toPolyG_cSqfreeYunFFG_get hgcd R hR0 hpp i i.isLt
  have aj := associated_toPolyG_cSqfreeYunFFG_get hgcd R hR0 hpp j j.isLt
  have hne : (1 + (i : ℕ)) ≠ (1 + (j : ℕ)) := by omega
  have hc : IsCoprime (sqfreeFactPart (toPoly R) (1 + (i : ℕ)))
      (sqfreeFactPart (toPoly R) (1 + (j : ℕ))) := (sqfreeFactPart_isRelPrime _ hne).isCoprime
  exact ((hc.of_isCoprime_of_dvd_left ai.dvd).symm.of_isCoprime_of_dvd_left aj.dvd).symm

/-! ## Stage 2 — the monic product decomposition -/

/-- `prodPow 1 M = ∏ Mₖ^(1+k)` as a `zipIdx` product. -/
theorem prodPow_one_eq_zipIdx {K : Type*} [Field K] (M : List K[X]) :
    prodPow 1 M = (M.zipIdx.map fun x => x.1 ^ (1 + x.2)).prod := by
  rw [prodPow_eq_prod_mul_zipIdxPow]
  have h2 : (M.zipIdx.map fun x => x.1 ^ (1 + x.2)).prod
      = (M.zipIdx.map fun x => x.1).prod * (M.zipIdx.map fun x => x.1 ^ x.2).prod := by
    rw [← List.prod_map_mul]; congr 1
    exact List.map_congr_left fun x _ => by rw [pow_add, pow_one]
  rw [h2]; congr 1; simp

/-- `prodPow i` of a list of monic polynomials is monic. -/
theorem monic_prodPow {K : Type*} [Field K] (i : ℕ) {M : List K[X]}
    (hM : ∀ p ∈ M, p.Monic) : (prodPow i M).Monic := by
  induction M generalizing i with
  | nil => exact monic_one
  | cons a es ih =>
    exact ((hM a (by simp)).pow i).mul (ih (i + 1) (fun p hp => hM p (by simp [hp])))

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Stage 2.** The monic normalization of `R` equals the product of its (monic) Yun factors raised to their
multiplicities: `⟦cmonic R⟧ = ∏ ⟦Rₖ⟧^(1+k)`. Via `cSqfreeYunFFG_reconstruction` (`toPoly R` is `Associated`
to that product), lifted through `normalize`: both `⟦cmonic R⟧ = normalize ⟦R⟧` and the (monic) product equal
`normalize` of associated polynomials, hence are equal. The Yun factors are already monic
(`cSqfreeYunFFG_monic`), so no per-factor normalization is needed. -/
theorem toPolyG_cmonicG_eq_prod_yun (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (R : DensePoly α)
    (hR0 : toPoly R ≠ 0) (hpp : (toPoly R).primPart ≠ 0) :
    toPoly (cmonic R) = ((cSqfreeYunFF R).zipIdx.map fun x => toPoly x.1 ^ (1 + x.2)).prod := by
  have hrhs : prodPow 1 ((cSqfreeYunFF R).map toPoly)
      = ((cSqfreeYunFF R).zipIdx.map fun x => toPoly x.1 ^ (1 + x.2)).prod := by
    rw [prodPow_one_eq_zipIdx, List.zipIdx_map, List.map_map]; rfl
  have hM_monic : (prodPow 1 ((cSqfreeYunFF R).map toPoly)).Monic :=
    monic_prodPow 1 (fun p hp => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp; exact cSqfreeYunFFG_monic hgcd R hR0 r hr)
  rw [← hrhs, toPolyG_cmonicG_eq_normalize, ← hM_monic.normalize_eq_self]
  exact normalize_eq_normalize_iff_associated.mpr (cSqfreeYunFFG_reconstruction hgcd R hR0 hpp)

/-! ## Stage 3 — assembly -/

open Differential ResidueBridge in
/-- **Stage 3a.** Each Yun factor of `R` has `D`-constant coefficients, given the monic normalization of `R`
does (the guard). Apply the list-level core `mapCoeffs_eq_zero_of_mem_coprime_prod` to the pairwise-coprime
monic decomposition of `⟦cmonic R⟧` (Stages 1 + 2). -/
theorem mapCoeffs_toPolyG_yunFactor_eq_zero (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (R : DensePoly α)
    (hR0 : toPoly R ≠ 0) (hpp : (toPoly R).primPart ≠ 0)
    (hguard : mapCoeffs (toPoly (cmonic R)) = 0)
    {Ri : DensePoly α} (hRi : Ri ∈ cSqfreeYunFF R) :
    mapCoeffs (toPoly Ri) = 0 := by
  have hfst : (cSqfreeYunFF R).zipIdx.map Prod.fst = cSqfreeYunFF R :=
    List.zipIdx_map_fst 0 _
  set L := (cSqfreeYunFF R).zipIdx.map fun x => (toPoly x.1, 1 + x.2) with hL
  have hmem_fst : ∀ x ∈ (cSqfreeYunFF R).zipIdx, x.1 ∈ cSqfreeYunFF R := fun x hx =>
    hfst ▸ List.mem_map_of_mem hx
  have hmonic : ∀ q ∈ L, (Prod.fst q).Monic := by
    intro q hq; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
    exact cSqfreeYunFFG_monic hgcd R hR0 _ (hmem_fst x hx)
  have hpos : ∀ q ∈ L, 1 ≤ q.2 := by
    intro q hq; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hq; omega
  have hcop : L.Pairwise fun a b => IsCoprime a.1 b.1 := by
    rw [hL, List.pairwise_map]
    have hp := pairwise_isCoprime_toPolyG_cSqfreeYunFFG hgcd R hR0 hpp
    rw [← hfst, List.pairwise_map] at hp
    exact hp
  have hfact : toPoly (cmonic R) = (L.map fun q => q.1 ^ q.2).prod := by
    rw [hL, List.map_map]; exact toPolyG_cmonicG_eq_prod_yun hgcd R hR0 hpp
  -- `(toPoly Ri, 1 + k) ∈ L` for `Ri`'s index `k`.
  obtain ⟨z, hz, hz1⟩ := List.mem_map.mp (hfst ▸ hRi)
  have hqL : (toPoly z.1, 1 + z.2) ∈ L := List.mem_map_of_mem hz
  have := mapCoeffs_eq_zero_of_mem_coprime_prod hmonic hpos hcop hfact hguard hqL
  rwa [hz1] at this

open Differential in
/-- **Stage 3b (core).** Every log argument produced by `cLrtLogArg` has `D`-constant residues, given the
residue resultant `R` is `D`-constant (the guard) and nonzero. Each log's `Rᵢ` is a Yun factor of `R`, so has
`D`-constant coefficients (Stage 3a); since `Rᵢ` is monic, `⟦cmonic Rᵢ⟧ = ⟦Rᵢ⟧`, and `cisZero (CPolyEngine.mapDeriv ·)`
is the computable reading of `mapCoeffs ⟦·⟧ = 0`. -/
theorem all_cLrtLogArgG_residueConstant_of_guard (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt hNum Dstar : DensePoly α)
    (hR0 : toPoly (cResidueResultantTower Dt hNum Dstar) ≠ 0)
    (hguard : cisZero (CPolyEngine.mapDeriv (cmonic (cResidueResultantTower Dt hNum Dstar))) = true) :
    (cLrtLogArg Dt hNum Dstar).all (fun RS => cisZero (CPolyEngine.mapDeriv (cmonic RS.1))) = true := by
  set R := cResidueResultantTower Dt hNum Dstar with hRdef
  have hpp : (toPoly R).primPart ≠ 0 := Polynomial.primPart_ne_zero _
  have hguard' : mapCoeffs (toPoly (cmonic R)) = 0 := by
    have hzero := (cisZeroG_iff _).mp hguard
    simpa only [denote] using hzero
  rw [List.all_eq_true]
  intro RS hRS
  rw [cLrtLogArg, CPoly.lrtLogArg, squarefreeYun_dense_wf_eq] at hRS
  simp_rw [degBound_cnorm_dense_eq, coefficientConstants_dense_eq] at hRS
  rw [List.mem_filterMap] at hRS
  obtain ⟨⟨Ri, idx⟩, hmem, hg⟩ := hRS
  simp only at hg
  -- `RS.1 = Ri` in both some-branches (`i = n` emits `Dstar` as `RS.2`, else the subresultant), so the
  -- residue-poly `RS.1` — the only thing that matters here — is the Yun factor regardless.
  have hRS1 : RS.1 = Ri := by
    split_ifs at hg <;>
      first
        | simp only [reduceCtorEq] at hg
        | (rw [Option.some.injEq] at hg; exact (congrArg Prod.fst hg).symm)
  rw [hRS1]
  have hRi : Ri ∈ cSqfreeYunFF R := by
    have h := List.mem_map_of_mem (f := Prod.fst) hmem
    rwa [List.zipIdx_map_fst] at h
  have hRi0 : mapCoeffs (toPoly Ri) = 0 :=
    mapCoeffs_toPolyG_yunFactor_eq_zero hgcd R hR0 hpp hguard' hRi
  have hcm : toPoly (cmonic Ri) = toPoly Ri := by
    rw [toPolyG_cmonicG_eq_normalize]
    exact (cSqfreeYunFFG_monic hgcd R hR0 Ri hRi).normalize_eq_self
  rw [cisZeroG_iff]
  simpa only [denote, hcm] using hRi0

/-- **Stage 3b (the residue bridge).** A passing residue guard forces the reduced LRT result's residues to be
constant: `cResidueConstantGuard a d = true → allResiduesConstantLrt (cIntegrateReducedLrt a d) = true`.
Both sides run on the same Hermite reduce, so this is `all_cLrtLogArgG_residueConstant_of_guard` at
`(hNum, Dstar) = (H.2.1, H.2.2)`. The `hR0` precondition (nonzero residue resultant) is the same one the raw
reduced soundness (`isIntegralResultLrtG_cIntegrateReducedLrtG_of_setup`) requires, supplied by the setup. -/
theorem allResiduesConstantLrtG_of_guard (hgcd : CgcdBCorrect (CFracGcdCoreWf.cgcdFFCoreWf (α := α))) (Dt a d : DensePoly α)
    (hR0 : toPoly (cResidueResultantTower Dt (cHermiteReduceTower Dt a d).2.1
      (cHermiteReduceTower Dt a d).2.2) ≠ 0)
    (hguard : cResidueConstantGuard Dt a d = true) :
    allResiduesConstantLrt (cIntegrateReducedLrt Dt a d) = true :=
  all_cLrtLogArgG_residueConstant_of_guard hgcd Dt _ _ hR0 hguard

end DeepWiki.SymbolicIntegration
