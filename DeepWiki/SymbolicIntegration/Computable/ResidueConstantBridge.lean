import DeepWiki.SymbolicIntegration.Computable.YunTowerCorrect

/-! # The residue bridge — a passing guard forces the result residues constant

The `←` sufficiency of `primitiveLrtDecides` needs: if the residue resultant `R` (monic) has `D`-constant
coefficients (the guard `cResidueConstantGuardG`), then each of its squarefree Yun factors does too
(`allResiduesConstantLrtG`). Abstractly, over `K[X]` with `D = Differential.mapCoeffs` (the coefficient-wise
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
