import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import DeepWiki.Algebra.PolynomialNormalization
import DeepWiki.Algebra.SquarefreeDeflation
import DeepWiki.ComputableAlgebra.PolySquarefreeTheory.Derivative
import DeepWiki.ComputableAlgebra.PolySquarefreeTheory.PartDerivatives
import DeepWiki.ComputableAlgebra.PolySquarefreeTheory.Parts
import DeepWiki.ComputableAlgebra.PolySquarefreeTheory.YunLoop
import DeepWiki.ComputableAlgebra.PolySquarefreeTheory.Initialization

/-! # Squarefree factorization via the derivative criterion
The squarefree part and deflations of `A ∈ D[x]` are computed by gcds with `dA/dx`, since a prime
factor `P` divides `dA/dx` exactly once less than it divides `A`. Includes the deflation theory,
the squarefree-factorization parts, and the executable factorization algorithm with its
correctness. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

section SquarefreeAlgorithm

open UniqueFactorizationMonoid

variable {K : Type*} [Field K]

open Classical

/-- Over a field, `gcd((A⁻⁽ᵏ⁻¹⁾)*, A⁻ᵏ)` is associated to the deflation squarefree part
`(A⁻ᵏ)*` (`1 ≤ k`). -/
theorem gcd_squarefreePart_deflation (A : K[X]) (k : ℕ) (hk : 1 ≤ k) (hA : A.primPart ≠ 0) :
    Associated (gcd (squarefreePart (deflation A (k - 1))) (deflation A k))
      (squarefreePart (deflation A k)) := by
  have hcop : IsCoprime (sqfreeFactPart A k) (deflation A k) := by
    rw [deflation_eq_prod_sqfreeFactPart A k]
    refine IsCoprime.prod_right (fun i _ => ?_)
    by_cases hik : i = k
    · rw [hik, Nat.sub_self, pow_zero]; exact isCoprime_one_right
    · exact ((sqfreeFactPart_isRelPrime A (Ne.symm hik)).isCoprime).pow_right
  have h15 : squarefreePart (deflation A (k - 1))
      = sqfreeFactPart A k * squarefreePart (deflation A k) := by
    rw [← squarefreePart_deflation_mul_sqfreeFactPart A k hk hA, mul_comm]
  have hWdvd : squarefreePart (deflation A k) ∣ deflation A k :=
    (dvd_mul_right _ (deflation A (k + 1))).trans (squarefreePart_mul_deflation_succ A k hA).dvd
  rw [h15]
  refine associated_of_dvd_dvd ?_ (dvd_gcd (dvd_mul_left _ _) hWdvd)
  have hgc : IsCoprime (gcd (sqfreeFactPart A k * squarefreePart (deflation A k)) (deflation A k))
      (sqfreeFactPart A k) := hcop.symm.of_isCoprime_of_dvd_left (gcd_dvd_right _ _)
  exact hgc.dvd_of_dvd_mul_left (gcd_dvd_left _ _)

/-- Executable squarefree-factorization loop on `fuel`: while `Sminus` is non-constant, emit
`Sstar / gcd(Sstar, Sminus)` and recurse on `(gcd, Sminus/gcd)`; otherwise emit `Sstar`. -/
noncomputable def squarefreeLoop (Sstar Sminus : K[X]) : ℕ → List K[X]
  | 0 => [Sstar]
  | (n + 1) =>
    if Sminus.natDegree = 0 then [Sstar]
    else (Sstar / gcd Sstar Sminus)
      :: squarefreeLoop (gcd Sstar Sminus) (Sminus / gcd Sstar Sminus) n

/-- The squarefree-factorization parts of `A`, computed by `squarefreeLoop` from
`gcd(pp A, d pp A/dx)` and `pp A / gcd`. -/
noncomputable def squarefreeFactorization (A : K[X]) : List K[X] :=
  squarefreeLoop (A.primPart / gcd A.primPart (derivative A.primPart))
    (gcd A.primPart (derivative A.primPart)) A.primPart.natDegree

/-- Division by an associate, up to associates: for `Y ∣ X` (`Y ≠ 0`), `X/Y ~ c ↔ X ~ Y·c`. -/
theorem associated_div_iff {X Y c : K[X]} (hY : Y ≠ 0) (hdvd : Y ∣ X) :
    Associated (X / Y) c ↔ Associated X (Y * c) := by
  have hmul : Y * (X / Y) = X := EuclideanDomain.mul_div_cancel' hY hdvd
  constructor
  · intro h; exact hmul ▸ h.mul_left Y
  · intro h; exact (hmul.symm ▸ h).of_mul_left (Associated.refl Y) hY

/-- The emitted loop part `(A⁻⁽ᵏ⁻¹⁾)* / gcd((A⁻⁽ᵏ⁻¹⁾)*, A⁻ᵏ)` is associated to `Aₖ` (`1 ≤ k`). -/
theorem squarefreeLoop_head_assoc (A : K[X]) (k : ℕ) (hk : 1 ≤ k) (hA : A.primPart ≠ 0) :
    Associated (squarefreePart (deflation A (k - 1))
        / gcd (squarefreePart (deflation A (k - 1))) (deflation A k))
      (sqfreeFactPart A k) := by
  have hYass : Associated
      (gcd (squarefreePart (deflation A (k - 1))) (deflation A k))
      (squarefreePart (deflation A k)) :=
    gcd_squarefreePart_deflation A k hk hA
  have hY : gcd (squarefreePart (deflation A (k - 1))) (deflation A k) ≠ 0 :=
    fun h => deflation_ne_zero A k (eq_zero_of_zero_dvd (h ▸ gcd_dvd_right _ _))
  have hsplit : squarefreePart (deflation A k) * sqfreeFactPart A k =
      squarefreePart (deflation A (k - 1)) :=
    squarefreePart_deflation_mul_sqfreeFactPart A k hk hA
  have hdvd : gcd (squarefreePart (deflation A (k - 1))) (deflation A k) ∣
      squarefreePart (deflation A (k - 1)) :=
    hYass.dvd.trans ⟨sqfreeFactPart A k, hsplit.symm⟩
  exact (associated_div_iff hY hdvd).2
    ((Associated.of_eq hsplit.symm).trans
      (hYass.symm.mul_right (sqfreeFactPart A k)))

/-- The updated loop deflation `A⁻ᵏ / gcd((A⁻⁽ᵏ⁻¹⁾)*, A⁻ᵏ)` is associated to `A⁻⁽ᵏ⁺¹⁾` (`1 ≤ k`). -/
theorem squarefreeLoop_tail_assoc (A : K[X]) (k : ℕ) (hk : 1 ≤ k) (hA : A.primPart ≠ 0) :
    Associated (deflation A k
        / gcd (squarefreePart (deflation A (k - 1))) (deflation A k))
      (deflation A (k + 1)) := by
  have hYass := gcd_squarefreePart_deflation A k hk hA
  have hY : gcd (squarefreePart (deflation A (k - 1))) (deflation A k) ≠ 0 :=
    fun h => deflation_ne_zero A k (eq_zero_of_zero_dvd (h ▸ gcd_dvd_right _ _))
  have h13 := squarefreePart_mul_deflation_succ A k hA
  rw [associated_div_iff hY (hYass.dvd.trans ((dvd_mul_right _ _).trans h13.dvd))]
  exact h13.symm.trans (hYass.symm.mul_right (deflation A (k + 1)))

/-! ### Total correctness of the executable algorithm
`squarefreeFactorization A` equals the squarefree-factorization parts `[A₁, …, Aₘ]` up to
associates. -/

private theorem deflation_natDegree_eq_zero_iff (A : K[X]) (k : ℕ) :
    (deflation A k).natDegree = 0 ↔ ∀ P ∈ (normalizedFactors A.primPart).toFinset,
      (normalizedFactors A.primPart).count P ≤ k := by
  rw [deflation, natDegree_prod _ _ (fun P hP => pow_ne_zero _
    (irreducible_of_normalized_factor P (Multiset.mem_toFinset.mp hP)).ne_zero),
    Finset.sum_eq_zero_iff]
  refine forall₂_congr (fun P hP => ?_)
  rw [natDegree_pow, Nat.mul_eq_zero]
  have := (irreducible_of_normalized_factor P (Multiset.mem_toFinset.mp hP)).natDegree_pos
  omega

theorem squarefreePart_deflation_natDegree_eq_zero_iff (A : K[X]) (k : ℕ)
    (hA : A.primPart ≠ 0) :
    (squarefreePart (deflation A k)).natDegree = 0 ↔ ∀ P ∈ (normalizedFactors A.primPart).toFinset,
      (normalizedFactors A.primPart).count P ≤ k := by
  rw [squarefreePart_deflation A k hA, natDegree_prod _ _ (fun P hP =>
    (irreducible_of_normalized_factor P
      (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hP).1)).ne_zero), Finset.sum_eq_zero_iff]
  constructor
  · intro h P hP
    by_contra hlt
    exact absurd (h P (Finset.mem_filter.mpr ⟨hP, by omega⟩))
      (irreducible_of_normalized_factor P (Multiset.mem_toFinset.mp hP)).natDegree_pos.ne'
  · intro h P hP
    have h1 := h P (Finset.mem_filter.mp hP).1
    have h2 := (Finset.mem_filter.mp hP).2
    omega

/-- The remaining Yun radical `squarefreePart (deflation A k)` is constant iff `k` has reached the
maximum multiplicity: `natDegree = 0 ↔ maxmult ≤ k`. Governs when Yun's loop terminates. -/
theorem squarefreePart_deflation_natDegree_eq_zero_iff_maxmult (A : K[X]) (k : ℕ)
    (hA : A.primPart ≠ 0) :
    (squarefreePart (deflation A k)).natDegree = 0 ↔
      (normalizedFactors A.primPart).toFinset.sup
        (fun P => (normalizedFactors A.primPart).count P) ≤ k :=
  (squarefreePart_deflation_natDegree_eq_zero_iff A k hA).trans Finset.sup_le_iff.symm

open UniqueFactorizationMonoid in
/-- The maximum multiplicity is bounded by the degree of the primitive part:
`maxmult ≤ natDegree pp(A)`. A prime `P` of multiplicity `m` contributes `P^m ∣ pp(A)`, and
`m ≤ m·deg P ≤ deg pp(A)`. -/
theorem sup_count_le_natDegree_primPart (A : K[X]) (hA : A.primPart ≠ 0) :
    (normalizedFactors A.primPart).toFinset.sup
        (fun P => (normalizedFactors A.primPart).count P) ≤ A.primPart.natDegree := by
  apply Finset.sup_le
  intro P hP
  have hmem := Multiset.mem_toFinset.mp hP
  have hle : Multiset.replicate ((normalizedFactors A.primPart).count P) P
      ≤ normalizedFactors A.primPart := Multiset.le_count_iff_replicate_le.mp le_rfl
  have hdvd1 : P ^ (normalizedFactors A.primPart).count P
      ∣ (normalizedFactors A.primPart).prod := by
    rw [← Multiset.prod_replicate]; exact Multiset.prod_dvd_prod_of_le hle
  have hdvd : P ^ (normalizedFactors A.primPart).count P ∣ A.primPart :=
    hdvd1.trans (prod_normalizedFactors hA).dvd
  have hnd := natDegree_le_of_dvd hdvd hA
  rw [natDegree_pow] at hnd
  have hpos : 1 ≤ P.natDegree := (irreducible_of_normalized_factor P hmem).natDegree_pos
  nlinarith [hnd, hpos]

private theorem natDegree_eq_of_associated {p q : K[X]} (h : Associated p q) (hq : q ≠ 0) :
    p.natDegree = q.natDegree :=
  le_antisymm (natDegree_le_of_dvd h.dvd hq)
    (natDegree_le_of_dvd h.symm.dvd (fun hp => hq (h.eq_zero_iff.mp hp)))

private theorem squarefreePart_deflation_ne_zero (A : K[X]) (k : ℕ) (hA : A.primPart ≠ 0) :
    squarefreePart (deflation A k) ≠ 0 := by
  rw [squarefreePart_deflation A k hA, Finset.prod_ne_zero_iff]
  exact fun P hP => (irreducible_of_normalized_factor P
    (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hP).1)).ne_zero

private theorem head_gen (A : K[X]) (k : ℕ) (hk : 1 ≤ k) (hA : A.primPart ≠ 0)
    {Sstar Sminus : K[X]} (hSs : Associated Sstar (squarefreePart (deflation A (k - 1))))
    (hSm : Associated Sminus (deflation A k)) :
    Associated (Sstar / gcd Sstar Sminus) (sqfreeFactPart A k) := by
  have hSmne : Sminus ≠ 0 := fun h => deflation_ne_zero A k (hSm.eq_zero_iff.mp h)
  have hY : gcd Sstar Sminus ≠ 0 := fun h => hSmne (eq_zero_of_zero_dvd (h ▸ gcd_dvd_right _ _))
  have hgcd : Associated (gcd Sstar Sminus) (squarefreePart (deflation A k)) :=
    (hSs.gcd hSm).trans (gcd_squarefreePart_deflation A k hk hA)
  have hsplit := squarefreePart_deflation_mul_sqfreeFactPart A k hk hA
  rw [associated_div_iff hY
    (hgcd.dvd.trans (dvd_trans (show squarefreePart (deflation A k)
        ∣ squarefreePart (deflation A (k - 1)) from ⟨sqfreeFactPart A k, hsplit.symm⟩)
      hSs.symm.dvd))]
  exact hSs.trans (hsplit ▸ hgcd.symm.mul_right (sqfreeFactPart A k))

private theorem tail_gen (A : K[X]) (k : ℕ) (hk : 1 ≤ k) (hA : A.primPart ≠ 0)
    {Sstar Sminus : K[X]} (hSs : Associated Sstar (squarefreePart (deflation A (k - 1))))
    (hSm : Associated Sminus (deflation A k)) :
    Associated (Sminus / gcd Sstar Sminus) (deflation A (k + 1)) := by
  have hSmne : Sminus ≠ 0 := fun h => deflation_ne_zero A k (hSm.eq_zero_iff.mp h)
  have hY : gcd Sstar Sminus ≠ 0 := fun h => hSmne (eq_zero_of_zero_dvd (h ▸ gcd_dvd_right _ _))
  have hgcd : Associated (gcd Sstar Sminus) (squarefreePart (deflation A k)) :=
    (hSs.gcd hSm).trans (gcd_squarefreePart_deflation A k hk hA)
  have h13 := squarefreePart_mul_deflation_succ A k hA
  rw [associated_div_iff hY
    (hgcd.dvd.trans ((dvd_mul_right _ _).trans (h13.dvd.trans hSm.symm.dvd)))]
  exact hSm.trans (h13.symm.trans (hgcd.symm.mul_right (deflation A (k + 1))))

private theorem deflation_succ_natDegree_lt (A : K[X]) (k : ℕ) (hA : A.primPart ≠ 0)
    (hpos : (deflation A k).natDegree ≠ 0) :
    (deflation A (k + 1)).natDegree < (deflation A k).natDegree := by
  have h13 := squarefreePart_mul_deflation_succ A k hA
  have heq : (deflation A k).natDegree
      = (squarefreePart (deflation A k)).natDegree + (deflation A (k + 1)).natDegree :=
    (natDegree_eq_of_associated h13.symm (mul_ne_zero
        (squarefreePart_deflation_ne_zero A k hA) (deflation_ne_zero A (k + 1)))).trans
      (natDegree_mul (squarefreePart_deflation_ne_zero A k hA) (deflation_ne_zero A (k + 1)))
  have hsd : (squarefreePart (deflation A k)).natDegree ≠ 0 := by
    rw [ne_eq, squarefreePart_deflation_natDegree_eq_zero_iff A k hA,
      ← deflation_natDegree_eq_zero_iff A k]
    exact hpos
  omega

private theorem squarefreePart_deflation_eq_one (A : K[X]) (k : ℕ) (hA : A.primPart ≠ 0)
    (h : ∀ P ∈ (normalizedFactors A.primPart).toFinset, (normalizedFactors A.primPart).count P ≤ k) :
    squarefreePart (deflation A k) = 1 := by
  rw [squarefreePart_deflation A k hA,
    Finset.filter_eq_empty_iff.mpr (fun P hP => not_lt.mpr (h P hP)), Finset.prod_empty]

private theorem loop_correct (A : K[X]) (hA : A.primPart ≠ 0) (m : ℕ)
    (hterm : ∀ k, (deflation A k).natDegree = 0 ↔ m ≤ k)
    (hbase : squarefreePart (deflation A (m - 1)) = sqfreeFactPart A m) :
    ∀ (fuel k : ℕ) (Sstar Sminus : K[X]), 1 ≤ k → k ≤ m →
      Associated Sstar (squarefreePart (deflation A (k - 1))) →
      Associated Sminus (deflation A k) → (deflation A k).natDegree ≤ fuel →
      List.Forall₂ Associated (squarefreeLoop Sstar Sminus fuel)
        ((List.range (m + 1 - k)).map (fun i => sqfreeFactPart A (k + i))) := by
  intro fuel
  induction fuel with
  | zero =>
    intro k Sstar Sminus hk hkm hSs hSm hfuel
    have hkeq : k = m := le_antisymm hkm ((hterm k).mp (Nat.le_zero.mp hfuel))
    subst hkeq
    rw [squarefreeLoop, show k + 1 - k = 1 from by omega]
    simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero]
    rw [hbase] at hSs
    exact List.Forall₂.cons hSs List.Forall₂.nil
  | succ n ih =>
    intro k Sstar Sminus hk hkm hSs hSm hfuel
    rw [squarefreeLoop]
    have hdeg : Sminus.natDegree = (deflation A k).natDegree :=
      natDegree_eq_of_associated hSm (deflation_ne_zero A k)
    by_cases hd0 : Sminus.natDegree = 0
    · rw [if_pos hd0]
      have hkeq : k = m := le_antisymm hkm ((hterm k).mp (hdeg ▸ hd0))
      subst hkeq
      rw [show k + 1 - k = 1 from by omega]
      simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero]
      rw [hbase] at hSs
      exact List.Forall₂.cons hSs List.Forall₂.nil
    · rw [if_neg hd0]
      have hpos : (deflation A k).natDegree ≠ 0 := hdeg ▸ hd0
      have hkm' : k < m := lt_of_not_ge (fun hge => hpos ((hterm k).mpr hge))
      have htgt : (List.range (m + 1 - k)).map (fun i => sqfreeFactPart A (k + i))
          = sqfreeFactPart A k
            :: (List.range (m + 1 - (k + 1))).map (fun i => sqfreeFactPart A (k + 1 + i)) := by
        rw [show m + 1 - k = (m - k) + 1 from by omega, List.range_succ_eq_map, List.map_cons]
        refine congrArg₂ _ (by simp) ?_
        rw [List.map_map, show m + 1 - (k + 1) = m - k from by omega]
        exact List.map_congr_left (fun i _ => by simp only [Function.comp_apply]; congr 1; omega)
      rw [htgt]
      refine List.Forall₂.cons (head_gen A k hk hA hSs hSm) ?_
      refine ih (k + 1) (gcd Sstar Sminus) (Sminus / gcd Sstar Sminus)
        (by omega) (by omega)
        ((hSs.gcd hSm).trans (gcd_squarefreePart_deflation A k hk hA))
        (tail_gen A k hk hA hSs hSm) ?_
      have := deflation_succ_natDegree_lt A k hA hpos
      omega

theorem squarefreeFactorization_forall₂ [CharZero K] (A : K[X]) (hA : A.primPart ≠ 0)
    (hm1 : 1 ≤ (normalizedFactors A.primPart).toFinset.sup
      (fun P => (normalizedFactors A.primPart).count P)) :
    List.Forall₂ Associated (squarefreeFactorization A)
      ((List.range ((normalizedFactors A.primPart).toFinset.sup
        (fun P => (normalizedFactors A.primPart).count P))).map
        (fun i => sqfreeFactPart A (i + 1))) := by
  set m := (normalizedFactors A.primPart).toFinset.sup
    (fun P => (normalizedFactors A.primPart).count P) with hmdef
  have hterm : ∀ k, (deflation A k).natDegree = 0 ↔ m ≤ k :=
    fun k => (deflation_natDegree_eq_zero_iff A k).trans Finset.sup_le_iff.symm
  have hbase : squarefreePart (deflation A (m - 1)) = sqfreeFactPart A m := by
    have h1 := squarefreePart_deflation_eq_one A m hA (fun P hP => Finset.le_sup (f := fun P => (normalizedFactors A.primPart).count P) hP)
    have h15 := squarefreePart_deflation_mul_sqfreeFactPart A m hm1 hA
    rw [h1, one_mul] at h15; exact h15.symm
  have hg14 := deflation_one_eq_gcd A hA
  have hgne : gcd A.primPart (derivative A.primPart) ≠ 0 :=
    fun h => hA (eq_zero_of_zero_dvd (h ▸ gcd_dvd_left _ _))
  have hSstar : Associated (A.primPart / gcd A.primPart (derivative A.primPart))
      (squarefreePart (deflation A 0)) := by
    rw [associated_div_iff hgne (gcd_dvd_left _ _)]
    refine ((deflation_zero A hA).symm.trans (squarefreePart_mul_deflation_succ A 0 hA).symm).trans ?_
    exact (hg14.symm.mul_left (squarefreePart (deflation A 0))).trans (by rw [mul_comm])
  have key := loop_correct A hA m hterm hbase A.primPart.natDegree 1
    (A.primPart / gcd A.primPart (derivative A.primPart)) (gcd A.primPart (derivative A.primPart))
    (le_refl 1) hm1 hSstar hg14
    (natDegree_le_of_dvd (deflation_dvd_primPart A 1 hA) hA)
  rw [squarefreeFactorization]
  simpa [show m + 1 - 1 = m from by omega, Nat.add_comm] using key

end SquarefreeAlgorithm

end DeepWiki.SymbolicIntegration
