import DeepWiki.SymbolicIntegration.PartialFraction
import DeepWiki.SymbolicIntegration.Residues
import DeepWiki.Algebra.PseudoDivision

/-! # Gcd log-form for rational integrals
For split squarefree `D = ∏_{α∈s}(X−α)`, the gcd `gcd(D, A − a·D')` equals the Rothstein-Trager
factor `∏_{res(α)=a}(X−α)`, so the grouped logarithmic sum can be written with the gcd inside each
`logDeriv`. The log-form is stated against the abstract gcd (any `IsSimilar`-to-the-gcd polynomial), so
a specific gcd algorithm — subresultant PRS, Euclidean PRS, or Mathlib's `gcd` — is switchable
(`ratFunc_eq_sum_residue_of_isSimilar_gcd`). -/

open Polynomial

open scoped Differential

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

open scoped Classical in
/-- For `deg A < #s` over split squarefree `D`, `A/D = ∑_a a · logDeriv(gcd(D, A − a·D'))` in `K(x)`. -/
theorem ratFunc_eq_sum_residue_gcd (s : Finset K) (A : K[X]) (hA : A.degree < s.card) :
    algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
      = ∑ a ∈ s.image (fun α => A.eval α / eval α (derivative (Lagrange.nodal s id))),
          algebraMap K[X] (RatFunc K) (C a)
            * Differential.logDeriv (algebraMap K[X] (RatFunc K)
                (gcd (Lagrange.nodal s id)
                  (A - C a * derivative (Lagrange.nodal s id)))) := by
  rw [ratFunc_eq_sum_residue_grouped s A hA]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [gcd_nodal_eq_prod_residue]

open scoped Differential in
/-- **`logDeriv` is `IsSimilar`-invariant.** If `p` is similar to a nonzero `q` (`C a·p = C b·q`), their
logarithmic derivatives over `K(x)` coincide — `p = C(a⁻¹b)·q` differs by a nonzero constant, which
`logDeriv` kills. This is the bridge that lets any gcd algorithm's output stand in for the gcd. -/
theorem logDeriv_algebraMap_eq_of_isSimilar {p q : K[X]} (hq : q ≠ 0) (h : IsSimilar p q) :
    Differential.logDeriv (algebraMap K[X] (RatFunc K) p)
      = Differential.logDeriv (algebraMap K[X] (RatFunc K) q) := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  have hp_eq : p = C (a⁻¹ * b) * q := by
    have h1 : C a⁻¹ * (C a * p) = C a⁻¹ * (C b * q) := by rw [hab]
    rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, C_1, one_mul, ← mul_assoc, ← C_mul] at h1
  rw [hp_eq, logDeriv_algebraMap_C_mul_eq (a⁻¹ * b) (mul_ne_zero (inv_ne_zero ha) hb) q hq]

open scoped Classical in
/-- **The switchable gcd log-form.** For `deg A < #s` over split squarefree `D`, and *any* family `g`
whose `g a` is similar to the Rothstein–Trager gcd `gcd(D, A − a·D')`, `A/D = ∑_a a · logDeriv(g a)`.
The specific gcd algorithm (subresultant PRS, Euclidean PRS, Mathlib `gcd`) is thus an interchangeable
instance: supply the `IsSimilar`-to-the-gcd proof and the log-form holds. `ratFunc_eq_sum_residue_gcd`
is the `g = gcd` case. -/
theorem ratFunc_eq_sum_residue_of_isSimilar_gcd (s : Finset K) (A : K[X]) (hA : A.degree < s.card)
    (g : K → K[X])
    (hg : ∀ a, IsSimilar (g a)
      (gcd (Lagrange.nodal s id) (A - C a * derivative (Lagrange.nodal s id)))) :
    algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
      = ∑ a ∈ s.image (fun α => A.eval α / eval α (derivative (Lagrange.nodal s id))),
          algebraMap K[X] (RatFunc K) (C a)
            * Differential.logDeriv (algebraMap K[X] (RatFunc K) (g a)) := by
  rw [ratFunc_eq_sum_residue_gcd s A hA]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hnodal : Lagrange.nodal s id ≠ 0 := Lagrange.nodal_ne_zero
  have hgcd : gcd (Lagrange.nodal s id) (A - C a * derivative (Lagrange.nodal s id)) ≠ 0 :=
    fun h => hnodal (gcd_eq_zero_iff _ _ |>.mp h).1
  rw [logDeriv_algebraMap_eq_of_isSimilar hgcd (hg a)]

end DeepWiki.SymbolicIntegration
