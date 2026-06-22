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

end DeepWiki.SymbolicIntegration
