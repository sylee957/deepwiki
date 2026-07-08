import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.RtResultant

/-! # Lazard-Rioboo-Trager subresultant primitives

Subresultant kernels and log-part data for grouping rational logarithmic terms
by residue multiplicity.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- The `j`-th subresultant of `D` and `A - t * D'` over coefficient ring `K[t]`. -/
noncomputable def lrtSubresultant (A D : K[X]) (j : ℕ) : (K[X])[X] :=
  subresultant (D.map (C : K →+* K[X]))
    (A.map (C : K →+* K[X]) - C Polynomial.X * (derivative D).map (C : K →+* K[X]))
    D.natDegree (D.natDegree - 1) j

/-- Specializing `lrtSubresultant A D j` at `t = a` gives the corresponding parameter subresultant over `K`. -/
theorem lrtSubresultant_eval (A D : K[X]) (a : K) (j : ℕ) :
    (lrtSubresultant A D j).map (Polynomial.evalRingHom a)
      = subresultant D (A - C a * derivative D) D.natDegree (D.natDegree - 1) j := by
  have hcomp : (Polynomial.evalRingHom a).comp (C : K →+* K[X]) = RingHom.id K := by ext k; simp
  rw [lrtSubresultant, ← subresultant_map]
  congr 1
  · rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  · simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_C, hcomp,
      Polynomial.map_id]
    simp

open Classical in
/-- The Lazard-Rioboo-Trager log-part data pairs squarefree residue factors with subresultant log arguments. -/
noncomputable def lazardRiobooTrager (A D : K[X]) : List (K[X] × (K[X])[X]) :=
  (squarefreeFactorization (rtResultant A D)).zipIdx.filterMap fun p =>
    let i := p.2 + 1
    if p.1.natDegree = 0 then none
    else some (p.1, if i = D.natDegree then D.map (C : K →+* K[X]) else lrtSubresultant A D i)

end DeepWiki.SymbolicIntegration
