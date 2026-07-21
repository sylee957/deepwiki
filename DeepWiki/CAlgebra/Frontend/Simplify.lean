import DeepWiki.CAlgebra.Frontend.IntegralExpr
import DeepWiki.CAlgebra.Poly.Bivariate
import DeepWiki.Algebra.ListSums

/-! # A sound simplifier for antiderivative expressions

Computable simplification of `IntegralExpr` — dropping zero terms and collapsing linear
`RootSum`s to explicit `α₀ · log u` terms (a linear factor's root is rational) — with
**proved derivative-preservation**: `(e.simplify).deriv = e.deriv`. -/

namespace DeepWiki.CAlgebra

universe u

variable {R : Type u} [Field R] [DecidableEq R]

namespace IntegralExpr

/-- Flatten an antiderivative expression into its summand atoms. -/
def atoms : IntegralExpr R → List (IntegralExpr R)
  | .add a b => a.atoms ++ b.atoms
  | e => [e]

/-- Simplify one atom: drop zeros, collapse a linear `RootSum` to its explicit log. -/
def simplifyAtom : IntegralExpr R → Option (IntegralExpr R)
  | .frac f => if f = 0 then none else some (.frac f)
  | .smulLog a u => if a = 0 then none else some (.smulLog a u)
  | .rootSum Q S =>
      if Q.size = 2 then
        let α₀ := -(Q.coeff 0) / Q.coeff 1
        if α₀ = 0 then none else some (.smulLog α₀ (zEval α₀ S))
      else some (.rootSum Q S)
  | .add a b => some (.add a b)

/-- Rebuild a sum from atoms (`frac 0` for the empty sum). -/
def rebuild : List (IntegralExpr R) → IntegralExpr R
  | [] => .frac 0
  | [a] => a
  | a :: b :: rest => .add a (rebuild (b :: rest))

/-- **The simplifier**: flatten, simplify each atom, rebuild. -/
def simplify (e : IntegralExpr R) : IntegralExpr R :=
  rebuild (e.atoms.filterMap simplifyAtom)

/-! ## Soundness: simplification preserves the derivative -/

section Soundness

variable [CharZero R] [DensePolyGcd R] [DensePolySquarefree R] [IsAlgClosed R]

open scoped Differential FormalDiff

omit [CharZero R] [DensePolySquarefree R] [IsAlgClosed R] in
/-- Rebuilding sums the atom derivatives. -/
theorem deriv_rebuild : ∀ l : List (IntegralExpr R), (rebuild l).deriv = (l.map deriv).sum
  | [] => by
      show (IntegralExpr.frac (0 : DenseFrac R)).deriv = _
      simp only [IntegralExpr.deriv]
      rw [show ((0 : DenseFrac R)′) = 0 from map_zero _, DenseFrac.toRatFunc_zero,
        List.map_nil, List.sum_nil]
  | [a] => by
      rw [rebuild, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  | a :: b :: rest => by
      show (IntegralExpr.add a (rebuild (b :: rest))).deriv = _
      simp only [IntegralExpr.deriv]
      rw [deriv_rebuild (b :: rest)]
      simp only [List.map_cons, List.sum_cons]

omit [CharZero R] [DensePolySquarefree R] [IsAlgClosed R] in
/-- Flattening preserves the derivative. -/
theorem deriv_atoms : ∀ e : IntegralExpr R, (e.atoms.map deriv).sum = e.deriv
  | .frac f => by
      show (([IntegralExpr.frac f]).map deriv).sum = _
      rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  | .rootSum Q S => by
      show (([IntegralExpr.rootSum Q S]).map deriv).sum = _
      rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  | .smulLog a u => by
      show (([IntegralExpr.smulLog a u]).map deriv).sum = _
      rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  | .add a b => by
      show (((a.atoms ++ b.atoms)).map deriv).sum = _
      rw [List.map_append, List.sum_append, deriv_atoms a, deriv_atoms b]
      rfl

omit [CharZero R] [DensePolyGcd R] [DensePolySquarefree R] [IsAlgClosed R] in
/-- **Linear `RootSum` collapse**: a linear factor has the single rational root
`α₀ = −q₀/q₁`, and the class specializes to `α₀ · log S(α₀, x)`. -/
theorem lrtPairTerm_linear (Q : DensePoly R) (S : DensePoly (DensePoly R))
    (hQ : Q.size = 2) :
    DensePoly.lrtPairTerm (Q, S)
      = algebraMap (Polynomial R) (RatFunc R) (Polynomial.C (-(Q.coeff 0) / Q.coeff 1))
        * @Differential.logDeriv (RatFunc R) _
            SymbolicIntegration.instDifferentialRatFunc_deepWiki
            (algebraMap (Polynomial R) (RatFunc R)
              (toPolynomial (zEval (-(Q.coeff 0) / Q.coeff 1) S))) := by
  have hQ0 : Q ≠ 0 := fun h => by rw [h, DensePoly.size_zero] at hQ; omega
  have hPne : toPolynomial Q ≠ 0 := toPolynomial_ne_zero hQ0
  have hdeg : (toPolynomial Q).natDegree = 1 := by
    rw [natDegree_toPolynomial_eq_size_sub_one, hQ]
  have hq1 : Q.coeff 1 ≠ 0 := by
    have hlc := Polynomial.leadingCoeff_ne_zero.mpr hPne
    rw [Polynomial.leadingCoeff, hdeg, coeff_toPolynomial] at hlc
    exact hlc
  set α₀ := -(Q.coeff 0) / Q.coeff 1 with hα₀
  have hroots : (toPolynomial Q).roots.toFinset = {α₀} := by
    ext β
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne, Finset.mem_singleton]
    have hP : toPolynomial Q
        = Polynomial.C ((toPolynomial Q).coeff 1) * Polynomial.X
          + Polynomial.C ((toPolynomial Q).coeff 0) :=
      Polynomial.eq_X_add_C_of_natDegree_le_one (by omega)
    rw [Polynomial.IsRoot, hP]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, coeff_toPolynomial]
    constructor
    · intro h
      rw [hα₀]
      field_simp
      linear_combination h
    · intro h
      rw [h, hα₀]
      field_simp
      ring
  rw [show DensePoly.lrtPairTerm (Q, S)
      = DensePoly.rootSum (toPolynomial Q) _ from rfl, DensePoly.rootSum, hroots,
    Finset.sum_singleton, toPolynomial_zEval]

omit [CharZero R] [DensePolySquarefree R] [IsAlgClosed R] in
/-- Per-atom simplification preserves the derivative (`none` means zero). -/
theorem simplifyAtom_deriv : ∀ a : IntegralExpr R,
    (((simplifyAtom a).map deriv).getD 0) = a.deriv
  | .frac f => by
      rw [simplifyAtom]
      by_cases hf : f = 0
      · rw [if_pos hf, Option.map_none, Option.getD_none, hf]
        simp only [IntegralExpr.deriv]
        rw [show ((0 : DenseFrac R)′) = 0 from map_zero _, DenseFrac.toRatFunc_zero]
      · rw [if_neg hf, Option.map_some, Option.getD_some]
  | .smulLog a u => by
      rw [simplifyAtom]
      by_cases ha : a = 0
      · rw [if_pos ha, Option.map_none, Option.getD_none, ha]
        simp only [IntegralExpr.deriv]
        rw [map_zero, map_zero, zero_mul]
      · rw [if_neg ha, Option.map_some, Option.getD_some]
  | .rootSum Q S => by
      rw [simplifyAtom]
      by_cases hQ : Q.size = 2
      · rw [if_pos hQ]
        by_cases hα : -(Q.coeff 0) / Q.coeff 1 = 0
        · rw [if_pos hα]
          show (0 : RatFunc R) = _
          simp only [IntegralExpr.deriv]
          rw [lrtPairTerm_linear Q S hQ, hα, map_zero, map_zero, zero_mul]
        · rw [if_neg hα, Option.map_some, Option.getD_some]
          show _ = (IntegralExpr.rootSum Q S).deriv
          simp only [IntegralExpr.deriv]
          exact (lrtPairTerm_linear Q S hQ).symm
      · rw [if_neg hQ, Option.map_some, Option.getD_some]
  | .add a b => by rw [simplifyAtom, Option.map_some, Option.getD_some]

omit [CharZero R] [DensePolySquarefree R] [IsAlgClosed R] in
/-- **Soundness of the simplifier**: simplification preserves the derivative. -/
theorem simplify_deriv (e : IntegralExpr R) : (simplify e).deriv = e.deriv := by
  rw [simplify, deriv_rebuild, DeepWiki.sum_map_filterMap]
  calc (e.atoms.map fun a => (((simplifyAtom a).map deriv).getD 0)).sum
      = (e.atoms.map deriv).sum := by
        congr 1
        exact List.map_congr_left fun a _ => simplifyAtom_deriv a
    _ = e.deriv := deriv_atoms e

end Soundness

end IntegralExpr

end DeepWiki.CAlgebra
