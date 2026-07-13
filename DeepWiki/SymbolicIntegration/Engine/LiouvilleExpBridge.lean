import DeepWiki.SymbolicIntegration.LiouvilleExpExtension
import DeepWiki.SymbolicIntegration.LiouvilleLog

/-! # The exponential pole-matching, ported from the logarithmic case

Discharges `ExpPoleMatching u` from `NondegenerateExp u` (`expPoleMatching_of_nondegenerateExp`), giving
the unconditional exp keystone `isLiouville_expExtension_uncond`. The special factor `X = exp u` is a
unit and is split into the `F`-part; pole-matching runs over `π ≠ X`. -/

open scoped Differential
open Polynomial Differential

namespace DeepWiki.SymbolicIntegration.LiouvilleExpBridge

open DeepWiki.SymbolicIntegration.LiouvilleExp
open DeepWiki.SymbolicIntegration.LiouvilleLog (wConst poleMult factorsFinset
  monic_of_mem_normalizedFactors factorsFinset_monic_irreducible poleMult_eq_zero_of_notMem
  squarefree_prod_of_monic_irreducible)

section ExpPole

variable {F : Type*} [Field F] [Differential F] [CharZero F]

open RatFunc

/-! ## The exp `logDeriv` factorization fold (derivation-touching, re-derived for `expDerivPoly`) -/

omit [CharZero F] in
/-- For `w ≠ 0`, `logDeriv w = logDeriv(algebraMap (num w)) − logDeriv(algebraMap (denom w))`. -/
theorem logDeriv_eq_num_sub_denom (u : F) {w : RatFunc F} (hw : w ≠ 0) :
    letI := expDifferential u
    logDeriv w = logDeriv (algebraMap F[X] (RatFunc F) (RatFunc.num w))
        - logDeriv (algebraMap F[X] (RatFunc F) (RatFunc.denom w)) := by
  letI := expDifferential u
  have hnum : algebraMap F[X] (RatFunc F) (RatFunc.num w) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.num_ne_zero hw)
  have hden : algebraMap F[X] (RatFunc F) (RatFunc.denom w) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero w)
  conv_lhs => rw [← RatFunc.num_div_denom w]
  exact logDeriv_div _ _ hnum hden

omit [CharZero F] in
/-- `logDeriv` of a polynomial image folds along its UFD factorization: for `p ≠ 0`,
`logDeriv (algebraMap p) = logDeriv (algebraMap (C lc)) + ∑_{π ∈ factors} (count π) · logDeriv (algebraMap π)`. -/
theorem logDeriv_algebraMap_eq_unit_add_sum [DecidableEq F] (u : F) {p : F[X]} (hp : p ≠ 0) :
    letI := expDifferential u
    logDeriv (algebraMap F[X] (RatFunc F) p)
      = logDeriv (algebraMap F[X] (RatFunc F) (Polynomial.C p.leadingCoeff))
        + ∑ π ∈ (UniqueFactorizationMonoid.normalizedFactors p).toFinset,
            ((UniqueFactorizationMonoid.normalizedFactors p).count π : RatFunc F)
              * logDeriv (algebraMap F[X] (RatFunc F) π) := by
  letI := expDifferential u
  have hfac_ne : ∀ π ∈ UniqueFactorizationMonoid.normalizedFactors p, π ≠ 0 := fun π hπ =>
    UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hπ
  have hprod : Polynomial.C p.leadingCoeff * (UniqueFactorizationMonoid.normalizedFactors p).prod = p :=
    Polynomial.leadingCoeff_mul_prod_normalizedFactors p
  have hlcne : Polynomial.C p.leadingCoeff ≠ 0 := by
    simpa [Polynomial.C_eq_zero] using Polynomial.leadingCoeff_ne_zero.mpr hp
  have hprodne : (UniqueFactorizationMonoid.normalizedFactors p).prod ≠ 0 := by
    intro h0
    apply hp
    rw [← hprod, h0, mul_zero]
  have hAlc : algebraMap F[X] (RatFunc F) (Polynomial.C p.leadingCoeff) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hlcne
  have hAprod : algebraMap F[X] (RatFunc F) (UniqueFactorizationMonoid.normalizedFactors p).prod ≠ 0 :=
    RatFunc.algebraMap_ne_zero hprodne
  conv_lhs => rw [← hprod, map_mul, Differential.logDeriv_mul _ _ hAlc hAprod]
  congr 1
  rw [map_multiset_prod,
    Differential.logDeriv_multisetProd (UniqueFactorizationMonoid.normalizedFactors p)
      (f := fun π => algebraMap F[X] (RatFunc F) π)
      (fun π hπ => RatFunc.algebraMap_ne_zero (hfac_ne π hπ))]
  rw [Finset.sum_multiset_map_count]
  refine Finset.sum_congr rfl fun π hπ => ?_
  rw [nsmul_eq_mul]

omit [CharZero F] in
/-- Pole decomposition: for `w ≠ 0`, `logDeriv w = logDeriv (algebraMap (wConst w))
+ ∑_{π ∈ factorsFinset w} algebraMap (C (poleMult w π)) · logDeriv (algebraMap π)`. -/
theorem logDeriv_eq_wConst_add_sum [DecidableEq F] (u : F) {w : RatFunc F} (hw : w ≠ 0) :
    letI := expDifferential u
    logDeriv w = logDeriv (algebraMap F (RatFunc F) (wConst w))
      + ∑ π ∈ factorsFinset w,
          algebraMap F[X] (RatFunc F) (Polynomial.C (poleMult w π))
            * logDeriv (algebraMap F[X] (RatFunc F) π) := by
  letI := expDifferential u
  set n := RatFunc.num w with hn
  set d := RatFunc.denom w with hd
  have hnne : n ≠ 0 := RatFunc.num_ne_zero hw
  have hdne : d ≠ 0 := RatFunc.denom_ne_zero w
  rw [logDeriv_eq_num_sub_denom u hw, ← hn, ← hd,
    logDeriv_algebraMap_eq_unit_add_sum u hnne, logDeriv_algebraMap_eq_unit_add_sum u hdne]
  set Mn := UniqueFactorizationMonoid.normalizedFactors n with hMn
  set Md := UniqueFactorizationMonoid.normalizedFactors d with hMd
  have hlcn : n.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hnne
  have hlcd : d.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hdne
  have hAn : algebraMap F[X] (RatFunc F) (Polynomial.C n.leadingCoeff) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (by simpa [Polynomial.C_eq_zero] using hlcn)
  have hAd : algebraMap F[X] (RatFunc F) (Polynomial.C d.leadingCoeff) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (by simpa [Polynomial.C_eq_zero] using hlcd)
  have hwconst : logDeriv (algebraMap F[X] (RatFunc F) (Polynomial.C n.leadingCoeff))
      - logDeriv (algebraMap F[X] (RatFunc F) (Polynomial.C d.leadingCoeff))
      = logDeriv (algebraMap F (RatFunc F) (wConst w)) := by
    rw [wConst, ← hn, ← hd, map_div₀, ratFunc_algebraMap_eq_algebraMap_C, ratFunc_algebraMap_eq_algebraMap_C,
      logDeriv_div _ _ hAn hAd]
  have hcast : ∀ (m : Multiset F[X]) (π : F[X]),
      ((m.count π : ℕ) : RatFunc F)
        = algebraMap F[X] (RatFunc F) (Polynomial.C ((m.count π : ℕ) : F)) := by
    intro m π
    rw [← ratFunc_algebraMap_eq_algebraMap_C, map_natCast]
  have hsub_n : (Mn.toFinset : Finset F[X]) ⊆ factorsFinset w := by
    rw [factorsFinset, ← hn]; exact Finset.subset_union_left
  have hsub_d : (Md.toFinset : Finset F[X]) ⊆ factorsFinset w := by
    rw [factorsFinset, ← hd]; exact Finset.subset_union_right
  have hext_n : ∑ π ∈ Mn.toFinset,
        ((Mn.count π : ℕ) : RatFunc F) * logDeriv (algebraMap F[X] (RatFunc F) π)
      = ∑ π ∈ factorsFinset w,
          algebraMap F[X] (RatFunc F) (Polynomial.C ((Mn.count π : ℕ) : F))
            * logDeriv (algebraMap F[X] (RatFunc F) π) := by
    rw [Finset.sum_subset hsub_n (fun π _ hπ => by
      rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hπ
      rw [hπ]; simp)]
    exact Finset.sum_congr rfl fun π _ => by rw [hcast]
  have hext_d : ∑ π ∈ Md.toFinset,
        ((Md.count π : ℕ) : RatFunc F) * logDeriv (algebraMap F[X] (RatFunc F) π)
      = ∑ π ∈ factorsFinset w,
          algebraMap F[X] (RatFunc F) (Polynomial.C ((Md.count π : ℕ) : F))
            * logDeriv (algebraMap F[X] (RatFunc F) π) := by
    rw [Finset.sum_subset hsub_d (fun π _ hπ => by
      rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at hπ
      rw [hπ]; simp)]
    exact Finset.sum_congr rfl fun π _ => by rw [hcast]
  rw [hext_n, hext_d, ← hwconst]
  have hpole : ∑ π ∈ factorsFinset w,
        algebraMap F[X] (RatFunc F) (Polynomial.C (poleMult w π))
          * logDeriv (algebraMap F[X] (RatFunc F) π)
      = ∑ π ∈ factorsFinset w,
          algebraMap F[X] (RatFunc F) (Polynomial.C ((Mn.count π : ℕ) : F))
            * logDeriv (algebraMap F[X] (RatFunc F) π)
        - ∑ π ∈ factorsFinset w,
          algebraMap F[X] (RatFunc F) (Polynomial.C ((Md.count π : ℕ) : F))
            * logDeriv (algebraMap F[X] (RatFunc F) π) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [poleMult, ← hn, ← hd, ← hMn, ← hMd, map_sub, map_sub, sub_mul]
  rw [hpole]; ring

/-! ## Splitting off the special factor `X` (the exp-specific step) -/

omit [CharZero F] in
/-- The special-factor term is `F`-valued: `algebraMap (C r) · logDeriv (algebraMap X) =
algebraMap (r · u')` in `RatFunc F`, since `logDeriv (exp u) = u'`. -/
theorem X_term_eq_algebraMap (u : F) (r : F) :
    letI := expDifferential u
    algebraMap F[X] (RatFunc F) (Polynomial.C r) * logDeriv (algebraMap F[X] (RatFunc F) Polynomial.X)
      = algebraMap F (RatFunc F) (r * u′) := by
  letI := expDifferential u
  rw [logDeriv_X_eq, ← ratFunc_algebraMap_eq_algebraMap_C (b := r), ← map_mul]

omit [CharZero F] in
/-- Splits a `C`-residue pole sum `∑_{π ∈ S}` into the `F`-valued `X` term plus the genuine-pole part
over `S.erase X`. -/
theorem sum_pole_split_X [DecidableEq F] (u : F) (S : Finset F[X]) (r : F[X] → F) :
    letI := expDifferential u
    (∑ π ∈ S, algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
        * logDeriv (algebraMap F[X] (RatFunc F) π))
      = (if Polynomial.X ∈ S then algebraMap F (RatFunc F) (r Polynomial.X * u′) else 0)
        + ∑ π ∈ S.erase Polynomial.X, algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
            * logDeriv (algebraMap F[X] (RatFunc F) π) := by
  letI := expDifferential u
  by_cases hX : Polynomial.X ∈ S
  · rw [if_pos hX, ← Finset.add_sum_erase S _ hX, X_term_eq_algebraMap]
  · rw [if_neg hX, Finset.erase_eq_of_notMem hX, zero_add]

/-! ## The multi-term collection (exp port) -/

omit [CharZero F] in
/-- An `F`-coefficient combination of `logDeriv`s of `F`-elements is a polynomial (in
`(algebraMap F[X]).range`). -/
theorem sum_const_logDeriv_algebraMap_mem_range (u : F) {ι : Type*} [Fintype ι]
    (c : ι → F) (x : ι → F) :
    letI := expDifferential u
    (∑ i, algebraMap F (RatFunc F) (c i)
        * logDeriv (algebraMap F (RatFunc F) (x i)))
      ∈ (algebraMap F[X] (RatFunc F)).range := by
  letI := expDifferential u
  letI := expDifferentialAlgebra u
  refine ⟨Polynomial.C (∑ i, c i * logDeriv (x i)), ?_⟩
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [logDeriv_algebraMap, ← ratFunc_algebraMap_eq_algebraMap_C, ← map_mul]

omit [CharZero F] in
/-- Multi-term pole-collection: `∑ᵢ ↑(cᵢ)·logDeriv wᵢ = ∑ᵢ ↑(cᵢ)·logDeriv (↑(wConst wᵢ))
+ ∑_{π ∈ S} ↑(C (∑ᵢ cᵢ · poleMult wᵢ π)) · logDeriv (↑π)`, `S = ⋃ᵢ factorsFinset wᵢ`. -/
theorem sum_const_logDeriv_eq_wConst_add_pole [DecidableEq F] (u : F) {ι : Type*} [Fintype ι]
    (c : ι → F) (w : ι → RatFunc F) (hw : ∀ i, w i ≠ 0) :
    letI := expDifferential u
    ∑ i, algebraMap F (RatFunc F) (c i) * logDeriv (w i)
      = ∑ i, algebraMap F (RatFunc F) (c i)
            * logDeriv (algebraMap F (RatFunc F) (wConst (w i)))
        + ∑ π ∈ Finset.univ.biUnion (fun i => factorsFinset (w i)),
            algebraMap F[X] (RatFunc F)
                (Polynomial.C (∑ i, c i * poleMult (w i) π))
              * logDeriv (algebraMap F[X] (RatFunc F) π) := by
  letI := expDifferential u
  set S := Finset.univ.biUnion (fun i => factorsFinset (w i)) with hS
  have hsubS : ∀ i, factorsFinset (w i) ⊆ S := fun i =>
    Finset.subset_biUnion_of_mem (fun i => factorsFinset (w i)) (Finset.mem_univ i)
  have hper : ∀ i, algebraMap F (RatFunc F) (c i) * logDeriv (w i)
      = algebraMap F (RatFunc F) (c i) * logDeriv (algebraMap F (RatFunc F) (wConst (w i)))
        + ∑ π ∈ S, algebraMap F (RatFunc F) (c i)
            * (algebraMap F[X] (RatFunc F) (Polynomial.C (poleMult (w i) π))
                * logDeriv (algebraMap F[X] (RatFunc F) π)) := by
    intro i
    rw [logDeriv_eq_wConst_add_sum u (hw i), mul_add, Finset.mul_sum]
    congr 1
    rw [Finset.sum_subset (hsubS i) (fun π _ hπ => by
      rw [poleMult_eq_zero_of_notMem hπ]; simp)]
  rw [Finset.sum_congr rfl (fun i _ => hper i), Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ratFunc_algebraMap_eq_algebraMap_C, ← mul_assoc, ← map_mul, ← Polynomial.C_mul]

/-! ## Pole-independence over `π ≠ X` (exp port; the special factor is excluded) -/

open scoped algebraMap in
omit [CharZero F] in
/-- Pole-independence modulo `π ∤ Dπ`: for distinct monic irreducible `πⱼ` with `deg dⱼ < deg πⱼ`, if
`∑ⱼ dⱼ · logDeriv πⱼ` is a polynomial and each `πⱼ ∤ D πⱼ`, then every `dⱼ = 0`. -/
theorem poleIndependence_of_not_dvd (u : F) {ιπ : Type*} [Fintype ιπ]
    (π : ιπ → F[X]) (d : ιπ → F[X]) (hmon : ∀ j, (π j).Monic) (hirr : ∀ j, Irreducible (π j))
    (hinj : Function.Injective π) (hdeg : ∀ j, (d j).natDegree < (π j).natDegree)
    (hDne : ∀ j, ¬ π j ∣ expDerivPoly u (π j))
    (hpoly : letI := expDifferential u
      (∑ j, algebraMap F[X] (RatFunc F) (d j)
          * logDeriv (algebraMap F[X] (RatFunc F) (π j)))
        ∈ (algebraMap F[X] (RatFunc F)).range) :
    ∀ j, d j = 0 := by
  letI := expDifferential u
  set Dπ : ιπ → F[X] := fun j => expDerivPoly u (π j) with hDπ
  set rem : ιπ → F[X] := fun j => (d j * Dπ j) %ₘ (π j) with hrem
  set quo : ιπ → F[X] := fun j => (d j * Dπ j) /ₘ (π j) with hquo
  have hdegπ : ∀ j, 1 ≤ (π j).natDegree := fun j => (hirr j).natDegree_pos
  have hdegrem : ∀ j, (rem j).degree < (π j).degree := fun j =>
    degree_modByMonic_lt _ (hmon j)
  have hπne : ∀ j, (algebraMap F[X] (RatFunc F) (π j)) ≠ 0 := fun j =>
    RatFunc.algebraMap_ne_zero (hmon j).ne_zero
  have hterm : ∀ j, algebraMap F[X] (RatFunc F) (d j)
      * logDeriv (algebraMap F[X] (RatFunc F) (π j))
      = (quo j : RatFunc F) + (rem j : RatFunc F) / (π j : RatFunc F) := by
    intro j
    rw [logDeriv_algebraMap_eq u (π j)]
    show algebraMap F[X] (RatFunc F) (d j)
        * (algebraMap F[X] (RatFunc F) (Dπ j) / algebraMap F[X] (RatFunc F) (π j))
      = (quo j : RatFunc F) + (rem j : RatFunc F) / (π j : RatFunc F)
    have hsplit : d j * Dπ j = π j * quo j + rem j := by
      rw [hrem, hquo, add_comm]; exact (modByMonic_add_div (d j * Dπ j) (π j)).symm
    rw [mul_div_assoc', ← map_mul, hsplit, map_add, map_mul, add_div]
    congr 1
    rw [mul_comm, mul_div_assoc, div_self (hπne j), mul_one]
  obtain ⟨P, hP⟩ := hpoly
  simp_rw [hterm] at hP
  rw [Finset.sum_add_distrib, ← map_sum] at hP
  have hcop : Set.Pairwise (Finset.univ : Finset ιπ) fun i j => IsCoprime (π i) (π j) := by
    intro i _ j _ hij
    rw [(hirr i).coprime_iff_not_dvd]
    intro hdvd
    exact hij (hinj (eq_of_monic_of_associated (hmon i) (hmon j)
      ((hirr i).associated_of_dvd (hirr j) hdvd)))
  have hdeg0 : ∀ j, (0 : F[X]).degree < (π j).degree := by
    intro j
    rw [Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr (Polynomial.degree_eq_bot.not.mpr (hmon j).ne_zero)
  have huniq := Polynomial.quo_add_sum_rem_div_unique (R := F) (K := RatFunc F)
    (g := π) (s := Finset.univ) (fun j _ => hmon j) hcop
    (q₁ := ∑ j, quo j) (q₂ := P) (r₁ := rem) (r₂ := fun _ => 0)
    (fun j _ => hdegrem j) (fun j _ => hdeg0 j)
    (by push_cast; simpa [div_eq_mul_inv] using hP.symm)
  intro j
  have hrem0 : rem j = 0 := huniq.2 j (Finset.mem_univ j)
  have hdvd : π j ∣ d j * Dπ j :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (hmon j)).mp hrem0
  have hdvdd : π j ∣ d j := ((hirr j).prime.dvd_or_dvd hdvd).resolve_right (hDne j)
  by_contra hd0
  exact absurd (Polynomial.natDegree_le_of_dvd hdvdd hd0) (by have := hdeg j; omega)

open scoped algebraMap in
/-- Pole-independence over monic irreducibles `≠ X` with constant residues: given `NondegenerateExp`,
if `∑_{π ∈ S} ↑(C (r π)) · logDeriv (↑π)` is a polynomial then every `r π = 0`. -/
theorem poleIndependence_finset_const_ne_X (u : F) (hnd : NondegenerateExp u) (S : Finset F[X])
    (hmon : ∀ π ∈ S, π.Monic) (hirr : ∀ π ∈ S, Irreducible π) (hXS : Polynomial.X ∉ S)
    (r : F[X] → F)
    (hpoly : letI := expDifferential u
      (∑ π ∈ S, algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
          * logDeriv (algebraMap F[X] (RatFunc F) π))
        ∈ (algebraMap F[X] (RatFunc F)).range) :
    ∀ π ∈ S, r π = 0 := by
  letI := expDifferential u
  have hkey := poleIndependence_of_not_dvd u (ιπ := ↥S)
    (π := fun j => (j : F[X])) (d := fun j => Polynomial.C (r (j : F[X])))
    (fun j => hmon j j.2) (fun j => hirr j j.2) Subtype.val_injective
    (fun j => by
      calc (Polynomial.C (r (j : F[X]))).natDegree ≤ 0 := (Polynomial.natDegree_C _).le
        _ < (↑j : F[X]).natDegree := (hirr j j.2).natDegree_pos)
    (fun j => not_dvd_expDerivPoly_of_ne_X u hnd (hmon j j.2) (hirr j j.2)
      (fun hXeq => hXS (hXeq ▸ j.2)))
    (by
      rw [← Finset.sum_attach S (fun π => algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
        * logDeriv (algebraMap F[X] (RatFunc F) π))] at hpoly
      exact hpoly)
  intro π hπ
  have hcj := hkey ⟨π, hπ⟩
  simpa using congrArg (fun q : F[X] => q.coeff 0) hcj

/-! ## The simple-pole separation (exp port; `denom v` keeps only the special factor `X`) -/

omit [CharZero F] in
/-- A simple-pole sum times the common denominator `∏_{ρ∈S} ρ` is a polynomial. -/
theorem simplePole_mul_prod_mem_range (u : F) (S : Finset F[X]) (r : F[X] → F)
    (hmon : ∀ π ∈ S, π.Monic) :
    letI := expDifferential u
    ((∑ π ∈ S, algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
        * logDeriv (algebraMap F[X] (RatFunc F) π))
        * algebraMap F[X] (RatFunc F) (∏ ρ ∈ S, ρ))
      ∈ (algebraMap F[X] (RatFunc F)).range := by
  classical
  letI := expDifferential u
  refine ⟨∑ π ∈ S, Polynomial.C (r π) * expDerivPoly u π * ∏ ρ ∈ S.erase π, ρ, ?_⟩
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun π hπ => ?_
  have hπne : algebraMap F[X] (RatFunc F) π ≠ 0 :=
    RatFunc.algebraMap_ne_zero (hmon π hπ).ne_zero
  have hprod : (∏ ρ ∈ S, ρ) = π * ∏ ρ ∈ S.erase π, ρ := (Finset.mul_prod_erase S _ hπ).symm
  rw [logDeriv_algebraMap_eq u π, hprod, map_mul, map_mul, map_mul]
  field_simp

/-- The pole of `v′` cannot be cancelled at `π ≠ X`: for monic irreducible `π ∣ D`, `π ≠ X`, `N`
coprime to `D`, `G = ∏_{ρ∈S} ρ`, `D² ∤ (D·DN − N·DD)·G` (`DN = expDerivPoly u N`, `DD = expDerivPoly u D`). -/
theorem not_dvd_sq_mul_of_pole (u : F) (hnd : NondegenerateExp u) {N D π : F[X]}
    (hπmon : π.Monic) (hπirr : Irreducible π) (hπX : π ≠ Polynomial.X) (hDne0 : D ≠ 0)
    (hcop : IsCoprime N D) (hπdvdD : π ∣ D) {S : Finset F[X]}
    (hSmon : ∀ ρ ∈ S, ρ.Monic) (hSirr : ∀ ρ ∈ S, Irreducible ρ) :
    ¬ D * D ∣ (D * expDerivPoly u N - N * expDerivPoly u D) * (∏ ρ ∈ S, ρ) := by
  intro hdvd
  set DN := expDerivPoly u N with hDNdef
  set DD := expDerivPoly u D with hDDdef
  set G := ∏ ρ ∈ S, ρ with hGdef
  have hπprime : Prime π := hπirr.prime
  have hfinD : FiniteMultiplicity π D := Polynomial.finiteMultiplicity_of_degree_pos_of_monic
    (hπirr.degree_pos) hπmon hDne0
  set k := multiplicity π D with hkdef
  have hmultD : emultiplicity π D = (k : ℕ∞) := hfinD.emultiplicity_eq_multiplicity
  have hk1 : 1 ≤ k := hfinD.le_multiplicity_of_pow_dvd (by simpa using hπdvdD)
  have hπnDπ : ¬ π ∣ expDerivPoly u π := not_dvd_expDerivPoly_of_ne_X u hnd hπmon hπirr hπX
  have hmultDD : emultiplicity π DD = ((k - 1 : ℕ) : ℕ∞) :=
    emultiplicity_expDerivPoly_eq u hπirr hπnDπ hk1 hmultD
  have hmultN : emultiplicity π N = 0 := by
    rw [emultiplicity_eq_zero]
    intro hπN
    exact hπirr.1 (hcop.isUnit_of_dvd' hπN hπdvdD)
  have hmultG : emultiplicity π G ≤ 1 :=
    ((squarefree_iff_emultiplicity_le_one G).mp
      (squarefree_prod_of_monic_irreducible S ⟨hSmon, hSirr⟩) π).resolve_right hπirr.1
  have hmult_NDD : emultiplicity π (N * DD) = ((k - 1 : ℕ) : ℕ∞) := by
    rw [emultiplicity_mul hπprime, hmultN, hmultDD, zero_add]
  have hmult_DDN_ge : (k : ℕ∞) ≤ emultiplicity π (D * DN) := by
    rw [emultiplicity_mul hπprime, hmultD]
    exact le_add_right le_rfl
  have hk1lt : ((k - 1 : ℕ) : ℕ∞) < (k : ℕ∞) := by
    rw [Nat.cast_lt]; omega
  have hne : emultiplicity π (D * DN) ≠ emultiplicity π (N * DD) := by
    rw [hmult_NDD]; exact (lt_of_lt_of_le hk1lt hmult_DDN_ge).ne'
  have hmult_diff : emultiplicity π (D * DN - N * DD) = ((k - 1 : ℕ) : ℕ∞) := by
    rw [sub_eq_add_neg, emultiplicity_add_eq_min (by rwa [emultiplicity_neg]),
      emultiplicity_neg, hmult_NDD, min_eq_right (le_of_lt (lt_of_lt_of_le hk1lt hmult_DDN_ge))]
  have hdvd2 : (D : F[X]) ^ 2 ∣ (D * DN - N * DD) * G := by rw [sq]; exact hdvd
  have hle : emultiplicity π (D ^ 2) ≤ emultiplicity π ((D * DN - N * DD) * G) :=
    emultiplicity_le_emultiplicity_of_dvd_right hdvd2
  rw [emultiplicity_pow hπprime, hmultD, emultiplicity_mul hπprime, hmult_diff] at hle
  have hk_succ : ((k - 1 : ℕ) : ℕ∞) + 1 = ((k : ℕ) : ℕ∞) := by
    rw [show ((k - 1 : ℕ) : ℕ∞) + 1 = (((k - 1) + 1 : ℕ) : ℕ∞) by push_cast; ring,
      show (k - 1) + 1 = k from by omega]
  have hG1 : ((k - 1 : ℕ) : ℕ∞) + emultiplicity π G ≤ ((k : ℕ) : ℕ∞) :=
    le_trans (add_le_add le_rfl hmultG) (le_of_eq hk_succ)
  have hfinal : ((2 : ℕ) : ℕ∞) * ((k : ℕ) : ℕ∞) ≤ ((k : ℕ) : ℕ∞) := le_trans hle hG1
  rw [← Nat.cast_mul, Nat.cast_le] at hfinal
  omega

/-- `denom v` keeps only the special factor `X`: if `v′ + (≠X simple-pole sum)` is a polynomial, then
`denom v = X^(natDegree)`. -/
theorem denom_eq_X_pow_of_deriv_add_simplePole (u : F) (hnd : NondegenerateExp u)
    (v : RatFunc F) (S : Finset F[X]) (r : F[X] → F)
    (hmon : ∀ π ∈ S, π.Monic) (hirr : ∀ π ∈ S, Irreducible π)
    (hpoly : letI := expDifferential u
      (v′ + ∑ π ∈ S, algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
          * logDeriv (algebraMap F[X] (RatFunc F) π))
        ∈ (algebraMap F[X] (RatFunc F)).range) :
    RatFunc.denom v = Polynomial.X ^ (RatFunc.denom v).natDegree := by
  classical
  letI := expDifferential u
  rcases eq_or_ne v 0 with rfl | hv0
  · rw [RatFunc.denom_zero, Polynomial.natDegree_one, pow_zero]
  set N := RatFunc.num v with hNdef
  set D := RatFunc.denom v with hDdef
  set G := ∏ ρ ∈ S, ρ with hGdef
  have hDmon : D.Monic := RatFunc.monic_denom v
  have hDne0 : D ≠ 0 := RatFunc.denom_ne_zero v
  have hNne0 : N ≠ 0 := RatFunc.num_ne_zero hv0
  have hcop : IsCoprime N D := RatFunc.isCoprime_num_denom v
  have hNA : algebraMap F[X] (RatFunc F) N ≠ 0 := RatFunc.algebraMap_ne_zero hNne0
  have hDA : algebraMap F[X] (RatFunc F) D ≠ 0 := RatFunc.algebraMap_ne_zero hDne0
  set DN := expDerivPoly u N with hDNdef
  set DD := expDerivPoly u D with hDDdef
  obtain ⟨NQ, hNQ⟩ := simplePole_mul_prod_mem_range u S r hmon
  obtain ⟨Rp, hRp⟩ := hpoly
  set Q : RatFunc F := ∑ π ∈ S, algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
      * logDeriv (algebraMap F[X] (RatFunc F) π) with hQdef
  have hveq : v = algebraMap F[X] (RatFunc F) N / algebraMap F[X] (RatFunc F) D := by
    rw [← RatFunc.num_div_denom v, ← hNdef, ← hDdef]
  have hlogv : logDeriv v
      = algebraMap F[X] (RatFunc F) DN / algebraMap F[X] (RatFunc F) N
        - algebraMap F[X] (RatFunc F) DD / algebraMap F[X] (RatFunc F) D := by
    have hsplit : logDeriv v = logDeriv (algebraMap F[X] (RatFunc F) N)
        - logDeriv (algebraMap F[X] (RatFunc F) D) := by
      conv_lhs => rw [hveq]; exact logDeriv_div _ _ hNA hDA
    rw [hsplit, logDeriv_algebraMap_eq u N, logDeriv_algebraMap_eq u D]
  have hv'eq : v′ = v * logDeriv v := by rw [logDeriv, mul_div_cancel₀ _ hv0]
  have hGA : algebraMap F[X] (RatFunc F) G ≠ 0 :=
    RatFunc.algebraMap_ne_zero (Polynomial.Monic.ne_zero (by
      rw [hGdef]; exact monic_prod_of_monic _ _ (fun π hπ => hmon π hπ)))
  have hclear : v′ * algebraMap F[X] (RatFunc F) D * algebraMap F[X] (RatFunc F) D
      = algebraMap F[X] (RatFunc F) D * algebraMap F[X] (RatFunc F) DN
        - algebraMap F[X] (RatFunc F) N * algebraMap F[X] (RatFunc F) DD := by
    rw [hv'eq, hlogv, hveq]
    field_simp
  have hNQval : algebraMap F[X] (RatFunc F) NQ
      = (algebraMap F[X] (RatFunc F) Rp - v′) * algebraMap F[X] (RatFunc F) G := by
    rw [hNQ, ← hGdef]
    have hQval : Q = algebraMap F[X] (RatFunc F) Rp - v′ := by rw [hRp]; ring
    rw [hQval]
  have hpolyid : (D * DN - N * DD) * G = (D * D) * (Rp * G - NQ) := by
    apply FaithfulSMul.algebraMap_injective F[X] (RatFunc F)
    simp only [map_mul, map_sub]
    rw [hNQval]
    linear_combination (-(algebraMap F[X] (RatFunc F) G)) * hclear
  have hdvd : D * D ∣ (D * DN - N * DD) * G := ⟨Rp * G - NQ, hpolyid⟩
  -- Every monic irreducible factor of `D` must be `X`.
  have hfac_eq : ∀ {π : F[X]}, π ∈ UniqueFactorizationMonoid.normalizedFactors D → π = Polynomial.X := by
    intro π hπmem
    have hπmon : π.Monic := monic_of_mem_normalizedFactors hπmem
    have hπirr : Irreducible π := UniqueFactorizationMonoid.irreducible_of_normalized_factor _ hπmem
    have hπdvdD : π ∣ D := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hπmem
    by_contra hπX
    exact absurd hdvd
      (not_dvd_sq_mul_of_pole u hnd hπmon hπirr hπX hDne0 hcop hπdvdD hmon hirr)
  obtain ⟨i, hassoc⟩ :=
    UniqueFactorizationMonoid.exists_associated_prime_pow_of_unique_normalized_factor
      (p := Polynomial.X) (r := D) (fun {m} hm => hfac_eq hm) hDne0
  have hXmon : (Polynomial.X ^ i : F[X]).Monic := monic_X.pow i
  have heq : Polynomial.X ^ i = D := eq_of_monic_of_associated hXmon hDmon hassoc
  have hdeg : D.natDegree = i := by rw [← heq, natDegree_pow, natDegree_X, mul_one]
  rw [hdeg, ← heq]

omit [CharZero F] in
/-- `v′` times an `X`-power denominator is a polynomial: if `denom v = X^k`, then
`v′ · ↑(X^k) ∈ (algebraMap F[X]).range`. -/
theorem deriv_mul_X_pow_mem_range (u : F) {v : RatFunc F} {k : ℕ}
    (hdXk : RatFunc.denom v = Polynomial.X ^ k) :
    letI := expDifferential u
    v′ * algebraMap F[X] (RatFunc F) (Polynomial.X ^ k) ∈ (algebraMap F[X] (RatFunc F)).range := by
  letI := expDifferential u
  letI := expDifferentialAlgebra u
  rcases eq_or_ne v 0 with rfl | hv0
  · refine ⟨0, ?_⟩
    rw [map_zero, show (0 : RatFunc F)′ = 0 from map_zero _, zero_mul]
  set N := RatFunc.num v with hNdef
  have hNne0 : N ≠ 0 := RatFunc.num_ne_zero hv0
  have hNA : algebraMap F[X] (RatFunc F) N ≠ 0 := RatFunc.algebraMap_ne_zero hNne0
  have hXkA : algebraMap F[X] (RatFunc F) (Polynomial.X ^ k) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
  have hveq : v = algebraMap F[X] (RatFunc F) N / algebraMap F[X] (RatFunc F) (Polynomial.X ^ k) := by
    rw [← RatFunc.num_div_denom v, ← hNdef, hdXk]
  have hlogv : logDeriv v
      = algebraMap F[X] (RatFunc F) (expDerivPoly u N) / algebraMap F[X] (RatFunc F) N
        - algebraMap F (RatFunc F) ((k : F) * u′) := by
    have hsplit : logDeriv v = logDeriv (algebraMap F[X] (RatFunc F) N)
        - logDeriv (algebraMap F[X] (RatFunc F) (Polynomial.X ^ k)) := by
      conv_lhs => rw [hveq]
      exact logDeriv_div _ _ hNA hXkA
    rw [hsplit, logDeriv_algebraMap_eq u N]
    congr 1
    rw [map_pow, logDeriv_pow, logDeriv_X_eq, map_mul, map_natCast]
  have hv'eq : v′ = v * logDeriv v := by rw [logDeriv, mul_div_cancel₀ _ hv0]
  set M : F[X] := expDerivPoly u N - Polynomial.C ((k : F) * u′) * N with hMdef
  have hclear : v′ * algebraMap F[X] (RatFunc F) (Polynomial.X ^ k)
      = algebraMap F[X] (RatFunc F) M := by
    rw [hv'eq, hlogv, hveq, hMdef, map_sub, map_mul, ratFunc_algebraMap_eq_algebraMap_C]
    field_simp
    congr 1
    rw [Polynomial.C_mul, map_mul, map_mul, ratFunc_algebraMap_eq_algebraMap_C, map_natCast]
    ring
  exact ⟨M, hclear.symm⟩

/-- Simple-pole separation: if `v′ + (≠X simple-pole sum Q)` is a polynomial, then `Q` itself is a
polynomial. -/
theorem simplePole_mem_range_of_deriv_add (u : F) (hnd : NondegenerateExp u)
    (v : RatFunc F) (S : Finset F[X]) (r : F[X] → F)
    (hmon : ∀ π ∈ S, π.Monic) (hirr : ∀ π ∈ S, Irreducible π) (hXS : Polynomial.X ∉ S)
    (hpoly : letI := expDifferential u
      (v′ + ∑ π ∈ S, algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
          * logDeriv (algebraMap F[X] (RatFunc F) π))
        ∈ (algebraMap F[X] (RatFunc F)).range) :
    letI := expDifferential u
    (∑ π ∈ S, algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
        * logDeriv (algebraMap F[X] (RatFunc F) π))
      ∈ (algebraMap F[X] (RatFunc F)).range := by
  classical
  letI := expDifferential u
  set G := ∏ ρ ∈ S, ρ with hGdef
  set Q : RatFunc F := ∑ π ∈ S, algebraMap F[X] (RatFunc F) (Polynomial.C (r π))
      * logDeriv (algebraMap F[X] (RatFunc F) π) with hQdef
  set k := (RatFunc.denom v).natDegree with hkdef
  -- `denom v = X^k`.
  have hdXk : RatFunc.denom v = Polynomial.X ^ k :=
    denom_eq_X_pow_of_deriv_add_simplePole u hnd v S r hmon hirr hpoly
  -- `v′·↑(X^k) ∈ F[t]`.
  have hv'Xk : v′ * algebraMap F[X] (RatFunc F) (Polynomial.X ^ k)
      ∈ (algebraMap F[X] (RatFunc F)).range := deriv_mul_X_pow_mem_range u hdXk
  -- `Q·↑(X^k) = (v′+Q)·↑(X^k) − v′·↑(X^k) ∈ F[t]`.
  have hQXk : Q * algebraMap F[X] (RatFunc F) (Polynomial.X ^ k)
      ∈ (algebraMap F[X] (RatFunc F)).range := by
    have hrw : Q * algebraMap F[X] (RatFunc F) (Polynomial.X ^ k)
        = (v′ + Q) * algebraMap F[X] (RatFunc F) (Polynomial.X ^ k)
          - v′ * algebraMap F[X] (RatFunc F) (Polynomial.X ^ k) := by ring
    rw [hrw]
    exact sub_mem (mul_mem hpoly ⟨Polynomial.X ^ k, rfl⟩) hv'Xk
  -- `Q·↑G ∈ F[t]`.
  have hQG : Q * algebraMap F[X] (RatFunc F) G ∈ (algebraMap F[X] (RatFunc F)).range :=
    simplePole_mul_prod_mem_range u S r hmon
  -- `X^k` and `G` are coprime (`X ∉ S` ⟹ `X ∤ G`, `X` prime).
  have hXG : IsCoprime (Polynomial.X ^ k) G := by
    apply IsCoprime.pow_left
    rw [Polynomial.irreducible_X.coprime_iff_not_dvd]
    rw [hGdef, Prime.dvd_finsetProd_iff Polynomial.prime_X _]
    rintro ⟨ρ, hρS, hXρ⟩
    exact hXS ((eq_of_monic_of_associated monic_X (hmon ρ hρS)
      ((Polynomial.irreducible_X.associated_of_dvd (hirr ρ hρS) hXρ))) ▸ hρS)
  -- `Q = p·(Q·X^k) + q·(Q·G) ∈ F[t]` from the Bézout combination of `X^k`, `G`.
  obtain ⟨p, q, hpq⟩ := hXG
  obtain ⟨PXk, hPXk⟩ := hQXk
  obtain ⟨PG, hPG⟩ := hQG
  refine ⟨p * PXk + q * PG, ?_⟩
  rw [map_add, map_mul, map_mul, hPXk, hPG]
  calc algebraMap F[X] (RatFunc F) p * (Q * algebraMap F[X] (RatFunc F) (Polynomial.X ^ k))
        + algebraMap F[X] (RatFunc F) q * (Q * algebraMap F[X] (RatFunc F) G)
      = Q * (algebraMap F[X] (RatFunc F) p * algebraMap F[X] (RatFunc F) (Polynomial.X ^ k)
          + algebraMap F[X] (RatFunc F) q * algebraMap F[X] (RatFunc F) G) := by ring
    _ = Q := by rw [← map_mul, ← map_mul, ← map_add, hpq, map_one, mul_one]

/-! ## The exp pole-matching assembly (the ported keystone residual) -/

omit [CharZero F] in
/-- The signed pole multiplicity is a constant: `(poleMult w π)′ = 0`. -/
theorem deriv_poleMult_eq_zero [DecidableEq F] (w : RatFunc F) (π : F[X]) : (poleMult w π)′ = 0 := by
  rw [poleMult, Derivation.map_sub, Derivation.map_natCast, Derivation.map_natCast, sub_zero]

omit [CharZero F] in
/-- For a constant `K` (`K′ = 0`), `(algebraMap (K · u))′ = algebraMap (K · u')` in `RatFunc F`. -/
theorem deriv_algebraMap_const_mul_self (u : F) {K : F} (hK : K′ = 0) :
    letI := expDifferential u
    letI := expDifferentialAlgebra u
    (algebraMap F (RatFunc F) (K * u))′ = algebraMap F (RatFunc F) (K * u′) := by
  letI := expDifferential u
  letI := expDifferentialAlgebra u
  rw [deriv_algebraMap]
  congr 1
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hK, mul_zero, add_zero]

/-- `ExpPoleMatching u` from `NondegenerateExp u`: the pole-matching residual the exp keystone waits
on. -/
theorem expPoleMatching_of_nondegenerateExp (u : F) (hnd : NondegenerateExp u) :
    ExpPoleMatching u := by
  letI := expDifferential u
  letI := expDifferentialAlgebra u
  classical
  intro a ι _ c hc w v h
  -- Replace zero `wᵢ` by `1`.
  set w' : ι → RatFunc F := fun i => if w i = 0 then 1 else w i with hw'def
  have hw'ne : ∀ i, w' i ≠ 0 := by
    intro i; rw [hw'def]; dsimp only; split
    · exact one_ne_zero
    · assumption
  have hlog_eq : ∀ i, logDeriv (w' i) = logDeriv (w i) := by
    intro i; rw [hw'def]; dsimp only; split
    · rename_i h0; rw [h0, logDeriv_one, Differential.logDeriv_zero]
    · rfl
  -- Collection over `S = ⋃ᵢ factorsFinset w'ᵢ`.
  set S := Finset.univ.biUnion (fun i => factorsFinset (w' i)) with hSdef
  have hcollect := sum_const_logDeriv_eq_wConst_add_pole u c w' hw'ne
  simp_rw [hlog_eq] at hcollect
  set res : F[X] → F := fun π => ∑ i, c i * poleMult (w' i) π with hresdef
  -- Split the collected pole sum at the special factor `X`.
  have hsplit := sum_pole_split_X u S res
  -- The `F`-part is a polynomial; so is `↑a`.
  have hFpart : (∑ i, algebraMap F (RatFunc F) (c i)
      * logDeriv (algebraMap F (RatFunc F) (wConst (w' i))))
      ∈ (algebraMap F[X] (RatFunc F)).range :=
    sum_const_logDeriv_algebraMap_mem_range u c (fun i => wConst (w' i))
  obtain ⟨pF, hpF⟩ := hFpart
  obtain ⟨pa, hpa⟩ : algebraMap F (RatFunc F) a ∈ (algebraMap F[X] (RatFunc F)).range :=
    ⟨Polynomial.C a, (ratFunc_algebraMap_eq_algebraMap_C a).symm⟩
  -- The constant `K = res X = ∑ᵢ cᵢ poleMult w'ᵢ X` and the `X`-term `↑(K·u')`.
  set K : F := res Polynomial.X with hKdef
  have hKconst : K′ = 0 := by
    rw [hKdef, hresdef, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hc i, mul_zero,
      deriv_poleMult_eq_zero, mul_zero, add_zero]
  -- The `X`-term equals `↑(K·u')` uniformly (when `X ∉ S`, `K = 0` since no `w'ᵢ` has factor `X`).
  set Xterm : RatFunc F :=
    if Polynomial.X ∈ S then algebraMap F (RatFunc F) (res Polynomial.X * u′) else 0 with hXtermdef
  have hXterm_eq : Xterm = algebraMap F (RatFunc F) (K * u′) := by
    rw [hXtermdef]
    by_cases hX : Polynomial.X ∈ S
    · rw [if_pos hX, hKdef]
    · rw [if_neg hX]
      have hK0 : K = 0 := by
        rw [hKdef, hresdef]
        refine Finset.sum_eq_zero fun i _ => ?_
        have : poleMult (w' i) Polynomial.X = 0 := by
          apply poleMult_eq_zero_of_notMem
          intro hmem
          exact hX (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hmem⟩)
        rw [this, mul_zero]
      rw [hK0, zero_mul, map_zero]
  -- The genuine pole sum `Q` over `S.erase X` (the special factor removed).
  set Q : RatFunc F := ∑ π ∈ S.erase Polynomial.X,
      algebraMap F[X] (RatFunc F) (Polynomial.C (res π))
        * logDeriv (algebraMap F[X] (RatFunc F) π) with hQdef
  -- `↑a = F-part + Xterm + Q + v′`.
  have hmain : algebraMap F (RatFunc F) a
      = (∑ i, algebraMap F (RatFunc F) (c i)
          * logDeriv (algebraMap F (RatFunc F) (wConst (w' i)))) + Xterm + Q + v′ := by
    rw [h, hcollect, hsplit, hXtermdef, hQdef]; ring
  -- `v′ + Q ∈ F[t]` (the `F`-part, `Xterm`, and `↑a` are polynomials).
  have hvQ : v′ + Q ∈ (algebraMap F[X] (RatFunc F)).range := by
    have hXtermR : Xterm ∈ (algebraMap F[X] (RatFunc F)).range := by
      rw [hXterm_eq]; exact ⟨Polynomial.C (K * u′), (ratFunc_algebraMap_eq_algebraMap_C _).symm⟩
    obtain ⟨pX, hpX⟩ := hXtermR
    refine ⟨pa - pF - pX, ?_⟩
    rw [map_sub, map_sub, hpa, hpF, hpX]
    have : v′ + Q = algebraMap F (RatFunc F) a
        - (∑ i, algebraMap F (RatFunc F) (c i)
          * logDeriv (algebraMap F (RatFunc F) (wConst (w' i)))) - Xterm := by
      rw [hmain]; ring
    rw [this]
  -- Membership: every `π ∈ S.erase X` is monic irreducible (and `≠ X`).
  have hmonS : ∀ π ∈ S.erase Polynomial.X, π.Monic := fun π hπ => by
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (Finset.mem_of_mem_erase hπ)
    exact (factorsFinset_monic_irreducible hi).1
  have hirrS : ∀ π ∈ S.erase Polynomial.X, Irreducible π := fun π hπ => by
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (Finset.mem_of_mem_erase hπ)
    exact (factorsFinset_monic_irreducible hi).2
  have hXnotS : Polynomial.X ∉ S.erase Polynomial.X := Finset.notMem_erase _ _
  -- Simple-pole separation: `Q` is itself a polynomial.
  have hQpoly : Q ∈ (algebraMap F[X] (RatFunc F)).range :=
    simplePole_mem_range_of_deriv_add u hnd v (S.erase Polynomial.X) res hmonS hirrS hXnotS
      (by rw [← hQdef]; exact hvQ)
  -- Pole-independence over `π ≠ X`: every residue `res π = 0`, so `Q = 0`.
  have hres0 : ∀ π ∈ S.erase Polynomial.X, res π = 0 :=
    poleIndependence_finset_const_ne_X u hnd (S.erase Polynomial.X) hmonS hirrS hXnotS res
      (by rw [← hQdef]; exact hQpoly)
  have hQ0 : Q = 0 := by
    rw [hQdef]
    refine Finset.sum_eq_zero fun π hπ => ?_
    rw [hres0 π hπ]; simp
  -- The `F`-part is `↑xF` for the `F`-element `xF`.
  set xF : F := ∑ i, c i * logDeriv (wConst (w' i)) with hxFdef
  have hFpart_eq : (∑ i, algebraMap F (RatFunc F) (c i)
      * logDeriv (algebraMap F (RatFunc F) (wConst (w' i))))
      = algebraMap F (RatFunc F) xF := by
    rw [hxFdef, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [logDeriv_algebraMap, ← map_mul]
  -- Conclude: `w₀ = wConst ∘ w'`, `v₀ = v + ↑(K·u)`.
  refine ⟨fun i => wConst (w' i), v + algebraMap F (RatFunc F) (K * u), ?_, ?_⟩
  · -- `↑a = F-part + v₀′` (`Q = 0`, and `v₀′ = v′ + Xterm`).
    have hv₀' : (v + algebraMap F (RatFunc F) (K * u))′ = v′ + Xterm := by
      rw [map_add, deriv_algebraMap_const_mul_self u hKconst, hXterm_eq]
    rw [hv₀', hmain, hQ0]; ring
  · -- `v₀′ = ↑a − F-part = ↑(a − xF) ∈ range (algebraMap F)`.
    have hv₀' : (v + algebraMap F (RatFunc F) (K * u))′ = v′ + Xterm := by
      rw [map_add, deriv_algebraMap_const_mul_self u hKconst, hXterm_eq]
    refine ⟨a - xF, ?_⟩
    have hh : algebraMap F (RatFunc F) a
        = algebraMap F (RatFunc F) xF + (v′ + Xterm) := by
      rw [hmain, hFpart_eq, hQ0]; ring
    rw [map_sub, hh, hv₀']; ring

/-! ## The unconditional exp keystone (composition with the proven `isLiouville_of_expPoleMatching`) -/

/-- The transcendental-exp Liouville keystone: `F(exp u) = RatFunc F` is a Liouville extension of `F`
for every genuine new exp monomial (`NondegenerateExp u`). -/
theorem isLiouville_expExtension_uncond (u : F) (hnd : NondegenerateExp u) :
    letI := expDifferential u
    letI := expDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouville_of_expPoleMatching u hnd (expPoleMatching_of_nondegenerateExp u hnd)

/-! ### Restatements pinning the ported results -/

-- The ported pole-matching: `ExpPoleMatching u` holds from `NondegenerateExp u` alone.
example (u : F) (hnd : NondegenerateExp u) : ExpPoleMatching u :=
  expPoleMatching_of_nondegenerateExp u hnd
-- The UNCONDITIONAL exp keystone: `F(exp u) = RatFunc F` is Liouville over `F` for every genuine new
-- exp monomial — modulo only the necessary transcendence `NondegenerateExp u`.
example (u : F) (hnd : NondegenerateExp u) :
    letI := expDifferential u
    letI := expDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouville_expExtension_uncond u hnd

/-- A nondegenerate exp monomial introduces no new constants in `RatFunc F` (`ContainConstants`): a
constant `x` (with `x′ = 0 ∈ range(algebraMap F …)`) already lies in `F`, immediately from
`expDeriv_mem_range_imp_mem_range` (the exp `v′ ∈ F ⟹ v ∈ F` descent). The exp sibling of
`containConstants_of_nondegenerateLog`; the exp case is direct — no linear `v`-reduction needed. -/
theorem containConstants_of_nondegenerateExp (u : F) (hnd : NondegenerateExp u) :
    letI := expDifferential u
    Differential.ContainConstants F (RatFunc F) := by
  letI := expDifferential u
  letI := expDifferentialAlgebra u
  refine ⟨fun {x} hx => ?_⟩
  exact expDeriv_mem_range_imp_mem_range u hnd (by rw [hx]; exact ⟨0, by rw [map_zero]⟩)

end ExpPole

end DeepWiki.SymbolicIntegration.LiouvilleExpBridge
