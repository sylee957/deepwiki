import DeepWiki.Algebra.PseudoDivision
import DeepWiki.Algebra.SubresultantPRS

/-! # The Euclidean pseudo-remainder sequence — a concrete `IsPRS`
Constructs the Euclidean pseudo-remainder sequence `R₀ = A`, `R₁ = B`, `R_{i+2} = prem(Rᵢ, R_{i+1})`
(β-scalars all `1`), proves it is an `IsPRS` with strictly decreasing degrees that terminates, and
relates its subresultants and last nonzero element to `gcd(A, B)`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {R : Type*} [CommRing R] [IsDomain R]

open Classical in
/-- The Euclidean pseudo-remainder sequence of `A, B`: `R₀ = A`, `R₁ = B`, and `R_{i+2}` is a chosen
pseudo-remainder of `Rᵢ` by `R_{i+1}` (or `0` once `R_{i+1} = 0`). The `β`-scalars are all `1`. -/
noncomputable def euclideanPRS (A B : R[X]) : ℕ → R[X]
  | 0 => A
  | 1 => B
  | (n + 2) =>
      if h : euclideanPRS A B (n + 1) = 0 then 0
      else Classical.choose
        (isPseudoRemainder_exists (euclideanPRS A B n) (euclideanPRS A B (n + 1)) h)

/-- The zeroth Euclidean PRS term is `A`. -/
@[simp] theorem euclideanPRS_zero (A B : R[X]) : euclideanPRS A B 0 = A := rfl

/-- The first Euclidean PRS term is `B`. -/
@[simp] theorem euclideanPRS_one (A B : R[X]) : euclideanPRS A B 1 = B := rfl

/-- Unfolding of `R_{n+2}` when `R_{n+1} ≠ 0`. -/
theorem euclideanPRS_succ_succ (A B : R[X]) (n : ℕ) (h : euclideanPRS A B (n + 1) ≠ 0) :
    euclideanPRS A B (n + 2)
      = Classical.choose (isPseudoRemainder_exists (euclideanPRS A B n) (euclideanPRS A B (n + 1)) h) := by
  rw [euclideanPRS]; exact dif_neg h

/-- Once a term vanishes, the next term is `0`. -/
theorem euclideanPRS_succ_succ_zero (A B : R[X]) (n : ℕ) (h : euclideanPRS A B (n + 1) = 0) :
    euclideanPRS A B (n + 2) = 0 := by
  rw [euclideanPRS]; exact dif_pos h

/-- Each `R_{i+2}` (with `R_{i+1} ≠ 0`) is a pseudo-remainder of `Rᵢ` by `R_{i+1}`. -/
theorem isPseudoRemainder_euclideanPRS (A B : R[X]) (n : ℕ) (h : euclideanPRS A B (n + 1) ≠ 0) :
    IsPseudoRemainder (euclideanPRS A B n) (euclideanPRS A B (n + 1)) (euclideanPRS A B (n + 2)) := by
  rw [euclideanPRS_succ_succ A B n h]
  exact Classical.choose_spec (isPseudoRemainder_exists _ _ h)

/-- The Euclidean pseudo-remainder sequence is a polynomial remainder sequence (`IsPRS`) with all
`β`-scalars equal to `1`. -/
theorem isPRS_euclideanPRS (A B : R[X]) : IsPRS A B (euclideanPRS A B) (fun _ => 1) := by
  refine ⟨rfl, rfl, fun i => ⟨fun hi => ⟨one_ne_zero, ?_⟩, fun hi => ?_⟩⟩
  · simpa using isPseudoRemainder_euclideanPRS A B i hi
  · rw [euclideanPRS_succ_succ_zero A B i hi]; simp

/-- The degrees strictly decrease: `deg R_{i+2} < deg R_{i+1}` whenever `R_{i+1} ≠ 0` (the pseudo-remainder
has degree below its divisor). -/
theorem euclideanPRS_degree_lt (A B : R[X]) (n : ℕ) (h : euclideanPRS A B (n + 1) ≠ 0) :
    (euclideanPRS A B (n + 2)).degree < (euclideanPRS A B (n + 1)).degree :=
  (isPseudoRemainder_euclideanPRS A B n h).choose_spec.choose_spec.2

/-- Degree budget: if `R₁, …, R_{n+1}` are all nonzero, then `deg R_{n+1} + n ≤ deg B` (each step drops
the degree by at least one). -/
theorem euclideanPRS_natDegree_add_le (A B : R[X]) :
    ∀ n, (∀ j, 1 ≤ j → j ≤ n + 1 → euclideanPRS A B j ≠ 0) →
      (euclideanPRS A B (n + 1)).natDegree + n ≤ B.natDegree := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hne
    have h1 : (euclideanPRS A B (n + 1)).natDegree + n ≤ B.natDegree :=
      ih (fun j hj1 hj2 => hne j hj1 (by omega))
    have hnz1 : euclideanPRS A B (n + 1) ≠ 0 := hne (n + 1) (by omega) (by omega)
    have hnz2 : euclideanPRS A B (n + 2) ≠ 0 := hne (n + 2) (by omega) (by omega)
    have hlt : (euclideanPRS A B (n + 2)).natDegree < (euclideanPRS A B (n + 1)).natDegree :=
      natDegree_lt_natDegree hnz2 (euclideanPRS_degree_lt A B n hnz1)
    show (euclideanPRS A B (n + 2)).natDegree + (n + 1) ≤ B.natDegree
    omega

/-- The sequence terminates: some `R_{N+1} = 0` (the strictly-decreasing degrees are bounded below). -/
theorem exists_euclideanPRS_eq_zero (A B : R[X]) :
    ∃ N, euclideanPRS A B (N + 1) = 0 := by
  by_contra hcon
  simp only [not_exists] at hcon
  have hall : ∀ j, 1 ≤ j → j ≤ (B.natDegree + 1) + 1 → euclideanPRS A B j ≠ 0 := by
    intro j hj1 _
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact hcon j'
  have := euclideanPRS_natDegree_add_le A B (B.natDegree + 1) hall
  omega

/-- The last nonzero element: there is `k ≥ 1` with `R_{k+1} = 0` and `R₁, …, R_k ≠ 0`. -/
theorem exists_last_euclideanPRS_nonzero (A B : R[X]) (hB : B ≠ 0) :
    ∃ k, 1 ≤ k ∧ euclideanPRS A B (k + 1) = 0 ∧ ∀ j, 1 ≤ j → j ≤ k → euclideanPRS A B j ≠ 0 := by
  classical
  have hex : ∃ N, euclideanPRS A B (N + 1) = 0 := exists_euclideanPRS_eq_zero A B
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, fun j hj1 hjk => ?_⟩
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · exfalso; have hs := Nat.find_spec hex; rw [h0] at hs; simp at hs; exact hB hs
    · exact hpos
  · have hlt : j - 1 < Nat.find hex := by omega
    have := Nat.find_min hex hlt
    rwa [show j - 1 + 1 = j from by omega] at this

/-- Strict degree decrease across the nonzero range: `deg R_b < deg R_a` for `1 ≤ a < b ≤ k` (with all
intermediate terms nonzero). -/
theorem euclideanPRS_natDegree_strictAnti (A B : R[X]) {k : ℕ}
    (hknz : ∀ j, 1 ≤ j → j ≤ k → euclideanPRS A B j ≠ 0) :
    ∀ a b, 1 ≤ a → a < b → b ≤ k →
      (euclideanPRS A B b).natDegree < (euclideanPRS A B a).natDegree := by
  intro a b ha hab hbk
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_or_ge a b with hab' | hab'
    · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      have hstep : (euclideanPRS A B (b' + 2)).natDegree < (euclideanPRS A B (b' + 1)).natDegree :=
        natDegree_lt_natDegree (hknz (b' + 2) (by omega) hbk)
          (euclideanPRS_degree_lt A B b' (hknz (b' + 1) (by omega) (by omega)))
      exact lt_trans hstep (ih (by omega) (by omega))
    · have ha' : a = b := by omega
      subst ha'
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      exact natDegree_lt_natDegree (hknz (a' + 2) (by omega) hbk)
        (euclideanPRS_degree_lt A B a' (hknz (a' + 1) (by omega) (by omega)))

set_option maxHeartbeats 1000000 in
/-- Subresultant ↔ gcd, concretely: for the Euclidean p.r.s. of `A, B` (`deg B ≤ deg A`) with last
nonzero element `R_k` (`k ≥ 2`), the subresultant of `A, B` of degree `deg R_k` is similar to
`gcd(A, B)`. -/
theorem subresultant_euclideanPRS_isSimilar_gcd [GCDMonoid R[X]] (A B : R[X]) (hA : A ≠ 0)
    (hAB : B.natDegree ≤ A.natDegree) {k : ℕ} (hk2 : 2 ≤ k) (hk0 : euclideanPRS A B (k + 1) = 0)
    (hknz : ∀ j, 1 ≤ j → j ≤ k → euclideanPRS A B j ≠ 0) :
    IsSimilar (subresultant A B A.natDegree B.natDegree (euclideanPRS A B k).natDegree) (gcd A B) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  set F := euclideanPRS A B with hF
  have hnz : ∀ l ≤ m, F (l + 1) ≠ 0 := fun l hl => hknz (l + 1) (by omega) (by omega)
  have hFlne : ∀ l ≤ m, F l ≠ 0 := by
    intro l hl
    rcases Nat.eq_zero_or_pos l with rfl | hlpos
    · exact hA
    · exact hknz l (by omega) (by omega)
  have hdle : ∀ l ≤ m, (F (l + 1)).natDegree ≤ (F l).natDegree := by
    intro l hl
    rcases Nat.eq_zero_or_pos l with rfl | hlpos
    · exact hAB
    · obtain ⟨a, rfl⟩ : ∃ a, l = a + 1 := ⟨l - 1, by omega⟩
      exact le_of_lt (natDegree_lt_natDegree (hknz (a + 2) (by omega) (by omega))
        (euclideanPRS_degree_lt A B a (hknz (a + 1) (by omega) (by omega))))
  -- choose the pseudo-division exponent `e l` and quotient `q l`
  have hpr : ∀ l, ∃ p : ℕ × R[X], l ≤ m →
      C ((F (l + 1)).leadingCoeff) ^ p.1 * F l = F (l + 1) * p.2 + F (l + 2) := by
    intro l
    by_cases hl : l ≤ m
    · obtain ⟨e, qq, he, _⟩ := isPseudoRemainder_euclideanPRS A B l (hnz l hl)
      exact ⟨(e, qq), fun _ => he⟩
    · exact ⟨(0, 0), fun h => absurd h hl⟩
  choose eq hq using hpr
  have hrel : ∀ l ≤ m, C ((F (l + 1)).leadingCoeff ^ (eq l).1) * F l
      = C (1 : R) * F (l + 2) + F (l + 1) * (eq l).2 := by
    intro l hl
    rw [C_pow, hq l hl, map_one, one_mul]; ring
  have hQbound : ∀ l ≤ m, ((eq l).2).natDegree + (F (l + 1)).natDegree ≤ (F l).natDegree := by
    intro l hl
    have hl1 : F (l + 1) ≠ 0 := hnz l hl
    have hFl : F l ≠ 0 := hFlne l hl
    by_cases hql : (eq l).2 = 0
    · simp only [hql, natDegree_zero, zero_add]; exact hdle l hl
    · have hr := hrel l hl
      rw [map_one, one_mul] at hr
      have heqfq : F (l + 1) * (eq l).2 = C ((F (l + 1)).leadingCoeff ^ (eq l).1) * F l - F (l + 2) := by
        linear_combination -hr
      have hd1 : (C ((F (l + 1)).leadingCoeff ^ (eq l).1) * F l).degree ≤ (F l).degree := by
        refine le_trans (degree_mul_le _ _) ?_
        calc (C ((F (l + 1)).leadingCoeff ^ (eq l).1)).degree + (F l).degree
            ≤ 0 + (F l).degree := add_le_add_left degree_C_le _
          _ = (F l).degree := zero_add _
      have hd2 : (F (l + 2)).degree ≤ (F l).degree := by
        have hdle' : (F (l + 1)).degree ≤ (F l).degree := by
          rw [degree_eq_natDegree hl1, degree_eq_natDegree hFl]; exact_mod_cast hdle l hl
        exact le_trans (le_of_lt (euclideanPRS_degree_lt A B l hl1)) hdle'
      have hdeg : (F (l + 1) * (eq l).2).degree ≤ (F l).degree := by
        rw [heqfq]; exact le_trans (degree_sub_le _ _) (max_le hd1 hd2)
      have hnatle : (F (l + 1) * (eq l).2).natDegree ≤ (F l).natDegree := natDegree_le_natDegree hdeg
      rw [natDegree_mul hl1 hql] at hnatle
      omega
  have key := subresultant_isSimilar_gcd F (fun l => (F (l + 1)).leadingCoeff ^ (eq l).1) (fun _ => 1)
    (fun l => (eq l).2) m
    (fun l hl => pow_ne_zero _ (leadingCoeff_ne_zero.mpr (hnz l hl))) (fun _ _ => one_ne_zero)
    (fun l hl => leadingCoeff_ne_zero.mpr (hnz l hl))
    (fun l hl => natDegree_lt_natDegree (hknz (l + 2) (by omega) (by omega))
      (euclideanPRS_degree_lt A B l (hnz l hl)))
    (fun l hl => euclideanPRS_natDegree_strictAnti A B hknz (l + 2) (m + 2) (by omega) (by omega) le_rfl)
    hQbound hrel (hknz (m + 2) (by omega) le_rfl)
    ((isPRS_euclideanPRS A B).isSimilar_gcd hk0 (fun j hj1 hjk => hknz j hj1 hjk))
  exact key

/-- A divisor of the same degree is similar to it: `g ∣ p`, `p ≠ 0`, `deg g = deg p` → `IsSimilar g p`. -/
theorem isSimilar_of_dvd_of_natDegree_eq {K : Type*} [Field K] {g p : K[X]}
    (hdvd : g ∣ p) (hp : p ≠ 0) (hdeg : g.natDegree = p.natDegree) : IsSimilar g p := by
  obtain ⟨q, rfl⟩ := hdvd
  have hg : g ≠ 0 := left_ne_zero_of_mul hp
  have hq : q ≠ 0 := right_ne_zero_of_mul hp
  rw [natDegree_mul hg hq] at hdeg
  obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp (by omega : q.natDegree = 0)
  have hc : c ≠ 0 := by rintro rfl; simp at hq
  exact ⟨c, 1, hc, one_ne_zero, by rw [map_one, one_mul, mul_comm]⟩

/-- One-step termination ⇒ divisibility: over a field, if `euclideanPRS D E 2 = 0` with `E ≠ 0`,
then `E ∣ D`. -/
theorem dvd_of_euclideanPRS_two_eq_zero {K : Type*} [Field K] (D E : K[X]) (hE : E ≠ 0)
    (h0 : euclideanPRS D E 2 = 0) : E ∣ D := by
  obtain ⟨k, Q, hEq, _⟩ :=
    isPseudoRemainder_euclideanPRS D E 0 (by simpa using hE)
  rw [euclideanPRS_zero, euclideanPRS_one, h0, add_zero] at hEq
  have hu : IsUnit (C E.leadingCoeff ^ k) :=
    (isUnit_C.mpr (Ne.isUnit (leadingCoeff_ne_zero.mpr hE))).pow k
  have hEd : E ∣ C E.leadingCoeff ^ k * D := hEq ▸ Dvd.intro Q rfl
  exact (hu.dvd_mul_left).mp hEd

/-- One-step termination ⇒ `gcd(D, E) ~ E`: over a field, if `euclideanPRS D E 2 = 0` with `E ≠ 0`,
then `IsSimilar (gcd D E) E`. -/
theorem isSimilar_gcd_right_of_euclideanPRS_two_eq_zero {K : Type*} [Field K] [GCDMonoid K[X]]
    (D E : K[X]) (hE : E ≠ 0) (h0 : euclideanPRS D E 2 = 0) : IsSimilar (gcd D E) E := by
  have hED : E ∣ D := dvd_of_euclideanPRS_two_eq_zero D E hE h0
  exact IsSimilar.of_associated
    (associated_of_dvd_dvd (gcd_dvd_right D E) (dvd_gcd hED dvd_rfl))

-- One-step termination: `R₂ = 0` ⟹ `E ∣ D` and `gcd(D, E) ~ E` (the LRT `k = 1` boundary).
/-- When `gcd(C, E)` has full degree `deg C`, it is similar to `C`. -/
theorem isSimilar_gcd_left_of_natDegree_eq {K : Type*} [Field K] [GCDMonoid K[X]] {C E : K[X]}
    (hC : C ≠ 0) (hdeg : (gcd C E).natDegree = C.natDegree) : IsSimilar (gcd C E) C :=
  isSimilar_of_dvd_of_natDegree_eq (gcd_dvd_left C E) hC hdeg

-- At the full-multiplicity LRT boundary, the gcd `gcd(D, A − a·D')` is similar to `D`.
end DeepWiki.SymbolicIntegration
