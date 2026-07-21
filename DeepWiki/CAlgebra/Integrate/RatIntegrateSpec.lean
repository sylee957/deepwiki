import DeepWiki.CAlgebra.Integrate.RatIntegrate
import DeepWiki.CAlgebra.Diff.Frac
import DeepWiki.CAlgebra.Integrate.LogPartSpec

/-! # Soundness and completeness of the full rational integral

The capstones of the CAlgebra rational-integration pipeline: `D(∫ f) = f`
(hypothesis-free — the LRT detection completeness absorbs the zero log part), and the
computable integrability decision on the record. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

open scoped Differential FormalDiff

variable {R : Type u} [Field R] [DecidableEq R] [CharZero R] [DensePolyGcd R]
  [DensePolySquarefree R] [IsAlgClosed R]

/-- **The derivative of a rational integral**: the formal derivative of the represented
antiderivative `rational + ∫poly + ∑ᵢ ∑_{Qᵢ(α)=0} α · log Sᵢ(α, x)` — the rational and
polynomial contributions are denotations of computable engine derivatives. -/
noncomputable def RatIntegral.deriv (res : RatIntegral R) : RatFunc R :=
  DenseFrac.toRatFunc (res.rational′) + toRatFuncHom (res.poly′)
    + res.logs.deriv

/-- **Soundness of rational integration**, hypothesis-free: `D(∫ f) = f`. The zero log
part is absorbed by the LRT detection completeness. -/
theorem ratIntegrate_sound (f : DenseFrac R) :
    (ratIntegrate f).deriv = DenseFrac.toRatFunc f := by
  have hsound := hermiteReduce_sound f
  show DenseFrac.toRatFunc (((hermiteReduce f).rational)′)
      + toRatFuncHom ((polyIntegrate (hermiteReduce f).poly)′)
      + (lrtIntegrate (hermiteReduce f).logPart).deriv = _
  rw [polyIntegrate_deriv]
  rcases eq_or_ne (hermiteReduce f).logPart.num 0 with hnum0 | hnum0
  · have hnil : (lrtIntegrate (hermiteReduce f).logPart).terms = [] :=
      (lrtIntegrate_terms_eq_nil_iff _ (hermiteReduce f).logPart_den_squarefree
        (hermiteReduce f).logPart_isProper).mpr hnum0
    have hlp0 : DenseFrac.toRatFunc (hermiteReduce f).logPart = 0 := by
      rw [DenseFrac.eq_zero_of_num_eq_zero hnum0, DenseFrac.toRatFunc_zero]
    rw [show (lrtIntegrate (hermiteReduce f).logPart).deriv
        = ((lrtIntegrate (hermiteReduce f).logPart).terms.map lrtPairTerm).sum from rfl,
      hnil, List.map_nil, List.sum_nil, hsound, hlp0, add_zero]
  · rw [lrtIntegrate_sound _ hnum0 (hermiteReduce f).logPart_den_squarefree
      (hermiteReduce f).logPart_isProper]
    exact hsound.symm

/-- **Completeness of rational integration**: every canonical fraction has an
integration result — a record whose derivative is the fraction. Rational functions never
fail to integrate; `ratIntegrate` produces the witness. -/
theorem ratIntegrate_complete (f : DenseFrac R) :
    ∃ res : RatIntegral R, res.deriv = DenseFrac.toRatFunc f :=
  ⟨ratIntegrate f, ratIntegrate_sound f⟩

end DensePoly

end DeepWiki.CAlgebra
