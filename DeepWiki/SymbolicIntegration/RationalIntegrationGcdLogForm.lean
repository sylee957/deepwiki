import DeepWiki.SymbolicIntegration.PartialFraction
import DeepWiki.SymbolicIntegration.Residues

/-! # Gcd log-form for rational integrals
For split squarefree `D = ∏_{α∈s}(X−α)`, the gcd `gcd(D, A − a·D')` equals the Rothstein-Trager
factor `∏_{res(α)=a}(X−α)`, so the grouped logarithmic sum can be written with the gcd inside each
`logDeriv`. -/

open Polynomial

open scoped Differential

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

open scoped Classical in
-- The gcd factor is the product of the linear factors whose roots have residue `a`.
example (s : Finset K) (A : K[X]) (a : K) :
    gcd (Lagrange.nodal s id) (A - C a * derivative (Lagrange.nodal s id))
      = ∏ α ∈ s.filter
          (fun α => A.eval α / eval α (derivative (Lagrange.nodal s id)) = a), (X - C α) :=
  gcd_nodal_eq_prod_residue s A a

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

open scoped Classical in
-- The grouped logarithmic derivative form can be written with the residue gcd in each summand.
example (s : Finset K) (A : K[X]) (hA : A.degree < s.card) :
    algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
      = ∑ a ∈ s.image (fun α => A.eval α / eval α (derivative (Lagrange.nodal s id))),
          algebraMap K[X] (RatFunc K) (C a)
            * Differential.logDeriv (algebraMap K[X] (RatFunc K)
                (gcd (Lagrange.nodal s id)
                  (A - C a * derivative (Lagrange.nodal s id)))) :=
  ratFunc_eq_sum_residue_gcd s A hA

end DeepWiki.SymbolicIntegration
