import DeepWiki.CAlgebra.Integrate.LogPartSpec
import DeepWiki.SymbolicIntegration.LiouvilleStructure.ElementaryTower

/-! # The log part is elementary

The summed log-part soundness, read as a base weak Liouville form: the log part is
`∑ a · logDeriv S(a, x)` with constant coefficients, hence has an elementary
antiderivative (`IsElementary`). The Liouville layer's tower carriers live in `Type`, so
this file is universe-monomorphic (`R : Type`). -/

namespace DeepWiki.CAlgebra

namespace DensePoly

open DeepWiki.SymbolicIntegration DeepWiki.SymbolicIntegration.LiouvilleStructure

variable {R : Type} [Field R] [DecidableEq R] [CharZero R] [DensePolyGcd R]
  [DensePolySquarefree R] [IsAlgClosed R]

/-- **The log part has a base weak Liouville form**: the summed log-part soundness, in the
Liouville layer's shape — `toRatFunc g = ∑ cᵢ · logDeriv uᵢ + v′` over `RatFunc R` itself,
with the residues as constant coefficients and `v = 0`. -/
theorem lrtLogPart_hasWeakLiouvilleForm (g : DenseFrac R) (hnum : g.num ≠ 0)
    (hsf : Squarefree g.den.toPoly)
    (hprop : RatFunc.IsProper (DenseFrac.toRatFunc g)) :
    HasWeakLiouvilleForm (RatFunc R) (RatFunc R) (DenseFrac.toRatFunc g) := by
  refine ⟨↥(residueSet g), inferInstance,
    fun a => algebraMap (Polynomial R) (RatFunc R) (Polynomial.C (a : R)),
    fun a => deriv_algebraMap_C (a : R),
    fun a => algebraMap (Polynomial R) (RatFunc R) (lrtLogArg g.num g.den.toPoly (a : R)),
    0, ?_⟩
  have hsum : (∑ x : ↥(residueSet g), lrtLogTerm g (x : R))
      = ∑ a ∈ residueSet g, lrtLogTerm g a := Finset.sum_coe_sort _ _
  have hkey := (lrtLogTerms_sum_sound g hnum hsf hprop).trans
    ((logSumDeriv_lrtLogArg g).trans hsum.symm)
  simpa [map_zero, lrtLogTerm] using hkey

/-- **The log part has an elementary antiderivative**: a base weak Liouville form
certifies `IsElementary` outright. -/
theorem lrtLogPart_isElementary (g : DenseFrac R) (hnum : g.num ≠ 0)
    (hsf : Squarefree g.den.toPoly)
    (hprop : RatFunc.IsProper (DenseFrac.toRatFunc g)) :
    IsElementary (RatFunc R) (DenseFrac.toRatFunc g) :=
  IsElementary.of_hasWeakLiouvilleForm (lrtLogPart_hasWeakLiouvilleForm g hnum hsf hprop)

open scoped Differential in
/-- **Every canonical fraction has a base weak Liouville form**: Hermite reduction plus
the log stage give `f = ∑ residues · logDeriv Sₐ + (rational + ∫poly + v₀)′`. -/
theorem denseFrac_hasWeakLiouvilleForm (f : DenseFrac R) :
    HasWeakLiouvilleForm (RatFunc R) (RatFunc R) (DenseFrac.toRatFunc f) := by
  have hsound := hermiteReduce_sound f
  rw [RatFunc.differential_apply, ratFunc_deriv_eq_deriv] at hsound
  have hpoly := toRatFuncHom_polyIntegrate_deriv (hermiteReduce f).poly
  set w : RatFunc R := DenseFrac.toRatFunc (hermiteReduce f).rational
    + toRatFuncHom (polyIntegrate (hermiteReduce f).poly) with hw
  rcases eq_or_ne (hermiteReduce f).logPart.num 0 with hnum0 | hnum0
  · -- the log part vanishes: `f` is a pure derivative
    have hlp0 : DenseFrac.toRatFunc (hermiteReduce f).logPart = 0 := by
      rw [DenseFrac.toRatFunc, hnum0, toPolynomial_zero, map_zero, zero_div]
    refine hasWeakLiouvilleForm_tower_of_isDeriv _ _ _ w ?_
    rw [hw, map_add, hpoly]
    simpa [hlp0] using hsound
  · -- the log part contributes the residue family; the derivative parts fold into `v`
    obtain ⟨ι, fι, c, hc, u, v₀, hform⟩ := lrtLogPart_hasWeakLiouvilleForm
      (hermiteReduce f).logPart hnum0 (hermiteReduce f).logPart_den_squarefree
      (hermiteReduce f).logPart_isProper
    refine ⟨ι, fι, c, hc, u, v₀ + w, ?_⟩
    rw [map_add, hw, map_add, hpoly]
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at hform ⊢
    rw [hsound, hform]
    ring

/-- **Liouville's theorem for rational functions, constructively**: every canonical
fraction over an algebraically closed field of characteristic zero has an elementary
antiderivative — produced by `hermiteReduce` and the LRT log stage. -/
theorem denseFrac_isElementary (f : DenseFrac R) :
    IsElementary (RatFunc R) (DenseFrac.toRatFunc f) :=
  IsElementary.of_hasWeakLiouvilleForm (denseFrac_hasWeakLiouvilleForm f)

open scoped Differential in
open DeepWiki.SymbolicIntegration.LiouvilleTower in
/-- **The engine's integral, as an element**: every canonical fraction has an actual
antiderivative element `v` in a log-tower stage over `RatFunc R` — `D v = f`, with `v`
assembled from `hermiteReduce`'s rational and polynomial parts plus one adjoined
logarithm per nondegenerate residue. -/
theorem denseFrac_exists_antiderivative (f : DenseFrac R) :
    ∃ (S : LiouvilleStage (RatFunc R)) (v : S.carrier),
      algebraMap (RatFunc R) S.carrier (DenseFrac.toRatFunc f) = v′ :=
  hasWeakLiouvilleForm_exists_antiderivative (denseFrac_hasWeakLiouvilleForm f)

end DensePoly

end DeepWiki.CAlgebra
