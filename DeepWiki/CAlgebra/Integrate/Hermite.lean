import DeepWiki.CAlgebra.Diff.RatFunc
import DeepWiki.CAlgebra.Frac.Field

/-! # Hermite reduction (rational-function base case)

Quadratic Hermite reduction over a characteristic-zero field: `a/p` splits as the derivative
of a rational function plus a remainder with squarefree denominators,
`a/p = (G)′ + poly + Σᵢ bᵢ/dᵢ`. Each partial-fraction term `c/dʲ` with `j ≥ 2` sheds one
power of `d` by the Bézout split `c = t·d′ + b·d` and integration by parts
(`t·d′/dʲ = (−t/((j−1)dʲ⁻¹))′ + t′/((j−1)dʲ⁻¹)`), accumulating the rational part in the
canonical fraction field `DenseFrac`. The spec is stated in `RatFunc R` with the
quotient-rule derivative. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R] [DensePolyGcd R]

open scoped Differential

/-- One factor's Hermite sweep over **descending** numerators `[aⱼ, …, a₁]` for a squarefree
`d`: each head sheds one power of `d` into the accumulated rational part; the exponent-1
numerator remains. -/
def hermiteFactorAux (d : DensePoly R) : List (DensePoly R) → DenseFrac R × DensePoly R
  | [] => (0, 0)
  | [a] => (0, a)
  | c :: r :: rs =>
      let t := (splitCoprime c d (deriv d)).1
      let b := (splitCoprime c d (deriv d)).2
      let res := hermiteFactorAux d
        ((r + b + C (((rs.length + 1 : ℕ) : R))⁻¹ * deriv t) :: rs)
      (res.1 + DenseFrac.normalize (-(C (((rs.length + 1 : ℕ) : R))⁻¹ * t))
          (d ^ (rs.length + 1)),
        res.2)
  termination_by l => l.length

variable [CharZero R]

/-- **The Hermite step**: a term `c/dⁿ⁺²` is the derivative of `−t/((n+1)·dⁿ⁺¹)` plus the
pushed-down term `(b + t′/(n+1))/dⁿ⁺¹`, where `c = t·d′ + b·d` is the Bézout split against
the squarefree `d`. -/
theorem hermite_step {d : DensePoly R} (hd0 : d ≠ 0) (hdsf : Squarefree d)
    (c : DensePoly R) (n : ℕ) :
    toRatFuncHom c / toRatFuncHom d ^ (n + 2)
      = (DenseFrac.toRatFunc (DenseFrac.normalize
          (-(C (((n + 1 : ℕ) : R))⁻¹ * (splitCoprime c d (deriv d)).1)) (d ^ (n + 1))))′
        + toRatFuncHom ((splitCoprime c d (deriv d)).2
            + C (((n + 1 : ℕ) : R))⁻¹ * deriv (splitCoprime c d (deriv d)).1)
          / toRatFuncHom d ^ (n + 1) := by
  have hcop : IsCoprime d (deriv d) := squarefree_iff_isCoprime_deriv.mp hdsf
  have hsp := splitCoprime_spec hcop c
  set t := (splitCoprime c d (deriv d)).1 with ht
  set b := (splitCoprime c d (deriv d)).2 with hb
  have hk : (((n + 1 : ℕ) : R)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hdm0 : (d ^ (n + 1) : DensePoly R) ≠ 0 := pow_ne_zero _ hd0
  have hF0 : toRatFuncHom d ≠ (0 : RatFunc R) := toRatFuncHom_ne_zero hd0
  rw [DenseFrac.toRatFunc_normalize, RatFunc.differential_apply,
    RatFunc.deriv_div (toPolynomial_ne_zero hdm0)]
  rw [← toPolynomial_deriv, ← toPolynomial_deriv, ← toRatFuncHom_apply, ← toRatFuncHom_apply,
    ← toRatFuncHom_apply, ← toRatFuncHom_apply]
  have hgderiv : deriv (-(C (((n + 1 : ℕ) : R))⁻¹ * t))
      = -(C (((n + 1 : ℕ) : R))⁻¹ * deriv t) := by
    rw [deriv_neg, deriv_C_mul]
  have hdmderiv : deriv (d ^ (n + 1)) = C (((n + 1 : ℕ)) : R) * d ^ n * deriv d :=
    deriv_pow_succ d n
  rw [hgderiv, hdmderiv]
  simp only [map_neg, map_mul, map_pow, map_add]
  have hv0 : toRatFuncHom (C (((n + 1 : ℕ)) : R)) ≠ (0 : RatFunc R) :=
    toRatFuncHom_ne_zero (C_ne_zero hk)
  have huv : toRatFuncHom (C ((((n + 1 : ℕ)) : R))⁻¹)
      * toRatFuncHom (C (((n + 1 : ℕ)) : R)) = 1 := by
    rw [← map_mul, ← C_mul, inv_mul_cancel₀ hk, ← one_def, map_one]
  have hu : toRatFuncHom (C ((((n + 1 : ℕ)) : R))⁻¹)
      = (toRatFuncHom (C (((n + 1 : ℕ)) : R)))⁻¹ := eq_inv_of_mul_eq_one_left huv
  have hspT : toRatFuncHom t * toRatFuncHom (deriv d)
      + toRatFuncHom b * toRatFuncHom d = toRatFuncHom c := by
    rw [← map_mul, ← map_mul, ← map_add, hsp]
  rw [hu]
  field_simp
  linear_combination
    (-(toRatFuncHom (C (((n + 1 : ℕ)) : R)) * toRatFuncHom d ^ (2 * n + 2))) * hspT

omit [DensePolyGcd R] [CharZero R] in
/-- Peeling the head of a descending list off its `invPowSum`: the head sits at the top
exponent. -/
private theorem invPowSum_map_reverse_cons {d : DensePoly R} (x : DensePoly R)
    (L : List (DensePoly R)) :
    invPowSum (toRatFuncHom d) (((x :: L).reverse).map toRatFuncHom)
      = invPowSum (toRatFuncHom d) ((L.reverse).map toRatFuncHom)
        + toRatFuncHom x / toRatFuncHom d ^ (L.length + 1) := by
  rw [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.map_reverse,
    invPowSum_reverse_cons, List.length_map, ← List.map_reverse]

/-- The per-factor sweep is exact: the descending term sum is the derivative of the
accumulated rational part plus the exponent-1 remainder. -/
theorem hermiteFactorAux_spec {d : DensePoly R} (hd0 : d ≠ 0) (hdsf : Squarefree d) :
    ∀ l : List (DensePoly R),
      invPowSum (toRatFuncHom d) ((l.reverse).map toRatFuncHom)
        = (DenseFrac.toRatFunc (hermiteFactorAux d l).1)′
          + toRatFuncHom (hermiteFactorAux d l).2 / toRatFuncHom d := by
  intro l
  induction l using hermiteFactorAux.induct (d := d) with
  | case1 =>
      simp [hermiteFactorAux, invPowSum, RatFunc.differential_apply]
  | case2 a =>
      rw [hermiteFactorAux]
      show (toRatFuncHom a + 0) / toRatFuncHom d = _
      simp [RatFunc.differential_apply]
  | case3 c r rs t b ih =>
      have hstep := hermite_step hd0 hdsf c rs.length
      rw [show (splitCoprime c d (deriv d)).1 = t from rfl,
        show (splitCoprime c d (deriv d)).2 = b from rfl] at hstep
      have hunfold : hermiteFactorAux d (c :: r :: rs)
          = ((hermiteFactorAux d ((r + b + C (((rs.length + 1 : ℕ) : R))⁻¹ * deriv t) :: rs)).1
              + DenseFrac.normalize (-(C (((rs.length + 1 : ℕ) : R))⁻¹ * t))
                  (d ^ (rs.length + 1)),
             (hermiteFactorAux d
                ((r + b + C (((rs.length + 1 : ℕ) : R))⁻¹ * deriv t) :: rs)).2) := by
        simp only [hermiteFactorAux]
        rfl
      rw [invPowSum_map_reverse_cons, invPowSum_map_reverse_cons, hunfold]
      rw [invPowSum_map_reverse_cons] at ih
      simp only [List.length_cons] at *
      simp only [DenseFrac.toRatFunc_add, RatFunc.differential_apply,
        map_add, map_mul] at *
      linear_combination ih + hstep

variable [DensePolySquarefree R]

/-- **Hermite reduction** of `a/p`: the accumulated rational part (a canonical fraction whose
derivative absorbs all higher-power denominators), the polynomial part, and the remainder
numerators over the squarefree factors — `a/p = G′ + poly + Σᵢ bᵢ/dᵢ`. -/
def hermiteReduce (a p : DensePoly R) :
    DenseFrac R × DensePoly R × List (DensePoly R × DensePoly R) :=
  (((sqfPartFrac a p).2.map fun fa => (hermiteFactorAux fa.1 fa.2.reverse).1).sum,
   (sqfPartFrac a p).1,
   (sqfPartFrac a p).2.map fun fa => (fa.1, (hermiteFactorAux fa.1 fa.2.reverse).2))

omit [DensePolySquarefree R] in
/-- Summed per-factor sweeps: the partial-fraction table's value is the derivative of the
summed rational parts plus the squarefree-denominator remainders. -/
private theorem partsSum_hermite (parts : List (DensePoly R × List (DensePoly R)))
    (h : ∀ fa ∈ parts, fa.1 ≠ 0 ∧ Squarefree fa.1) :
    partsSum parts
      = (DenseFrac.toRatFunc
          ((parts.map fun fa => (hermiteFactorAux fa.1 fa.2.reverse).1).sum))′
        + ((parts.map fun fa => (fa.1, (hermiteFactorAux fa.1 fa.2.reverse).2)).map
            fun db => toRatFuncHom db.2 / toRatFuncHom db.1).sum := by
  induction parts with
  | nil => simp [partsSum, RatFunc.differential_apply]
  | cons fa T ihp =>
      obtain ⟨hne, hsf⟩ := h fa (by simp)
      have hfa := hermiteFactorAux_spec hne hsf fa.2.reverse
      rw [List.reverse_reverse] at hfa
      simp only [partsSum, List.map_cons, List.sum_cons] at *
      rw [hfa, ihp (fun x hx => h x (by simp [hx]))]
      simp only [DenseFrac.toRatFunc_add, RatFunc.differential_apply, RatFunc.deriv_add]
      ring

/-- **The Hermite identity**: `a/p = G′ + poly + Σᵢ bᵢ/dᵢ` in `RatFunc R`. -/
theorem hermiteReduce_spec {p : DensePoly R} (hp : p ≠ 0) (a : DensePoly R) :
    toRatFuncHom a / toRatFuncHom p
      = (DenseFrac.toRatFunc (hermiteReduce a p).1)′
        + toRatFuncHom (hermiteReduce a p).2.1
        + ((hermiteReduce a p).2.2.map fun db =>
            toRatFuncHom db.2 / toRatFuncHom db.1).sum := by
  have hprops : ∀ fa ∈ (sqfPartFrac a p).2, fa.1 ≠ 0 ∧ Squarefree fa.1 := by
    intro fa hfa
    have hsf := squarefree_of_mem_sqfPartFrac hfa
    exact ⟨fun h0 => not_squarefree_zero (h0 ▸ hsf), hsf⟩
  rw [sqfPartFrac_ratFunc hp a, partsSum_hermite _ hprops, hermiteReduce]
  ring

omit [CharZero R] in
/-- Every remainder denominator of the Hermite reduction is squarefree. -/
theorem hermiteReduce_denom_squarefree {p a : DensePoly R}
    {db : DensePoly R × DensePoly R} (hdb : db ∈ (hermiteReduce a p).2.2) :
    Squarefree db.1 := by
  simp only [hermiteReduce, List.mem_map] at hdb
  obtain ⟨fa, hfa, rfl⟩ := hdb
  exact squarefree_of_mem_sqfPartFrac hfa

end DensePoly

end DeepWiki.CAlgebra
