import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms

/-! # General-derivation Rothstein–Trager / Lazard–Rioboo–Trager

The abstract RT/LRT theory (`rtResultant`, `lrtSubresultant`, …) is stated with the plain polynomial
`derivative D`. This file generalizes the *residue-object* layer to an **arbitrary** `B : K[X]` in place
of `derivative D` — the setting needed for a general derivation, where `B = D_tower(D)` (`= implicitDeriv`).
The residue resultant becomes `resultant_x(D, A − z·B)`; residues are `c = A(β)/B(β)` at roots `β` of `D`.

Per the `derivative`-dependence map (see `docs/generalize-lrt-derivation.md`): the resultant/subresultant
*defs and evaluation lemmas* treat `derivative D` **opaquely**, so they generalize verbatim. The residue↔root
theory (next phase) replaces the single essential fact `D.Separable → D'(β) ≠ 0` with a **normality**
hypothesis `IsCoprime D B` (equivalently `B(β) ≠ 0` at roots), keeping `Squarefree D`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- **General-derivation Rothstein–Trager resultant.** `resultant_x(D, A − z·B)` as a polynomial in `z`,
for an arbitrary `B` (the derivation image). Specializes to `rtResultant A D` at `B = derivative D`. -/
noncomputable def rtResultantGen (A D B : K[X]) : K[X] :=
  Polynomial.resultant (D.map (C : K →+* K[X]))
    (A.map (C : K →+* K[X]) - C Polynomial.X * B.map (C : K →+* K[X]))
    D.natDegree (D.natDegree - 1)

/-- `rtResultantGen A D (derivative D) = rtResultant A D`: the plain-derivative case. -/
@[simp] theorem rtResultantGen_derivative (A D : K[X]) :
    rtResultantGen A D (derivative D) = rtResultant A D := rfl

/-- Evaluating `rtResultantGen A D B` at `a` gives `resultant_x(D, A − C a·B)`. -/
theorem rtResultantGen_eval (A D B : K[X]) (a : K) :
    (rtResultantGen A D B).eval a
      = Polynomial.resultant D (A - C a * B) D.natDegree (D.natDegree - 1) := by
  have hcomp : (Polynomial.evalRingHom a).comp (C : K →+* K[X]) = RingHom.id K := by ext k; simp
  show Polynomial.evalRingHom a (rtResultantGen A D B) = _
  rw [rtResultantGen, ← Polynomial.resultant_map_map]
  congr 1
  · rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  · simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_C, hcomp,
      Polynomial.map_id]
    simp

/-- **General-derivation LRT subresultant.** The `j`-th subresultant of `D` and `A − z·B` over `K[z]`.
Specializes to `lrtSubresultant A D j` at `B = derivative D`. -/
noncomputable def lrtSubresultantGen (A D B : K[X]) (j : ℕ) : (K[X])[X] :=
  subresultant (D.map (C : K →+* K[X]))
    (A.map (C : K →+* K[X]) - C Polynomial.X * B.map (C : K →+* K[X]))
    D.natDegree (D.natDegree - 1) j

/-- `lrtSubresultantGen A D (derivative D) j = lrtSubresultant A D j`. -/
@[simp] theorem lrtSubresultantGen_derivative (A D : K[X]) (j : ℕ) :
    lrtSubresultantGen A D (derivative D) j = lrtSubresultant A D j := rfl

/-- Specializing `lrtSubresultantGen A D B j` at `z = a` gives the parameter subresultant over `K`. -/
theorem lrtSubresultantGen_eval (A D B : K[X]) (a : K) (j : ℕ) :
    (lrtSubresultantGen A D B j).map (Polynomial.evalRingHom a)
      = subresultant D (A - C a * B) D.natDegree (D.natDegree - 1) j := by
  have hcomp : (Polynomial.evalRingHom a).comp (C : K →+* K[X]) = RingHom.id K := by ext k; simp
  rw [lrtSubresultantGen, ← subresultant_map]
  congr 1
  · rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  · simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_C, hcomp,
      Polynomial.map_id]
    simp

end DeepWiki.SymbolicIntegration
