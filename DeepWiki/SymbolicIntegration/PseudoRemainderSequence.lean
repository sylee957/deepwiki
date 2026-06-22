import DeepWiki.SymbolicIntegration.PseudoDivision
import DeepWiki.SymbolicIntegration.SubresultantPRS

/-! # The Euclidean pseudo-remainder sequence — a concrete `IsPRS` (Bronstein §1.5)
The abstract subresultant ↔ gcd theory (`SubresultantPRS.lean`) is stated over an arbitrary p.r.s.
`F : ℕ → R[X]`. To *apply* it (e.g. for the Lazard–Rioboo–Trager correctness, Thm 2.5.1) one needs a
concrete p.r.s. This file constructs the **Euclidean pseudo-remainder sequence** `R₀ = A`, `R₁ = B`,
`R_{i+2} = prem(Rᵢ, R_{i+1})` (β-scalars all `1`), proves it satisfies `IsPRS`, that its degrees strictly
decrease, and that it terminates — yielding a last nonzero element similar to `gcd(A, B)`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {R : Type*} [CommRing R] [IsDomain R]

open Classical in
/-- The **Euclidean pseudo-remainder sequence** of `A, B`: `R₀ = A`, `R₁ = B`, and `R_{i+2}` is a chosen
pseudo-remainder of `Rᵢ` by `R_{i+1}` (or `0` once `R_{i+1} = 0`). The `β`-scalars are all `1`. -/
noncomputable def euclideanPRS (A B : R[X]) : ℕ → R[X]
  | 0 => A
  | 1 => B
  | (n + 2) =>
      if h : euclideanPRS A B (n + 1) = 0 then 0
      else Classical.choose
        (isPseudoRemainder_exists (euclideanPRS A B n) (euclideanPRS A B (n + 1)) h)

@[simp] theorem euclideanPRS_zero (A B : R[X]) : euclideanPRS A B 0 = A := rfl

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

/-- The **last nonzero element**: there is `k ≥ 1` with `R_{k+1} = 0` and `R₁, …, R_k ≠ 0`. `R_k` is the
last nonzero term — by Theorem 1.5.1 it is similar to `gcd(A, B)`. -/
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

end DeepWiki.SymbolicIntegration
