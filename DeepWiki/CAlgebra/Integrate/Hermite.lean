import DeepWiki.CAlgebra.Diff.RatFunc
import DeepWiki.CAlgebra.Frac.Field
import DeepWiki.Algebra.RatFuncProper

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

open scoped Differential FormalDiff

/-- One factor's Hermite sweep over **descending** numerators `[aⱼ, …, a₁]` for a squarefree
`d`: each head sheds one power of `d` into the accumulated rational part; the exponent-1
numerator remains. -/
private def hermiteFactorAux (d : DensePoly R) : List (DensePoly R) → DenseFrac R × DensePoly R
  | [] => (0, 0)
  | [a] => (0, a)
  | c :: r :: rs =>
      let t := (splitCoprime c d (d′)).1
      let b := (splitCoprime c d (d′)).2
      let res := hermiteFactorAux d
        ((r + b + C (((rs.length + 1 : ℕ) : R))⁻¹ * t′) :: rs)
      (res.1 + DenseFrac.normalize (-(C (((rs.length + 1 : ℕ) : R))⁻¹ * t))
          (d ^ (rs.length + 1)),
        res.2)
  termination_by l => l.length

variable [CharZero R]

/-- **The Hermite step**: a term `c/dⁿ⁺²` is the derivative of `−t/((n+1)·dⁿ⁺¹)` plus the
pushed-down term `(b + t′/(n+1))/dⁿ⁺¹`, where `c = t·d′ + b·d` is the Bézout split against
the squarefree `d`. -/
private theorem hermite_step {d : DensePoly R} (hd0 : d ≠ 0) (hdsf : Squarefree d)
    (c : DensePoly R) (n : ℕ) :
    toRatFuncHom c / toRatFuncHom d ^ (n + 2)
      = (DenseFrac.toRatFunc (DenseFrac.normalize
          (-(C (((n + 1 : ℕ) : R))⁻¹ * (splitCoprime c d (d′)).1)) (d ^ (n + 1))))′
        + toRatFuncHom ((splitCoprime c d (d′)).2
            + C (((n + 1 : ℕ) : R))⁻¹ * ((splitCoprime c d (d′)).1)′)
          / toRatFuncHom d ^ (n + 1) := by
  have hcop : IsCoprime d (d′) := squarefree_iff_isCoprime_deriv.mp hdsf
  have hsp := splitCoprime_spec hcop c
  set t := (splitCoprime c d (d′)).1 with ht
  set b := (splitCoprime c d (d′)).2 with hb
  have hk : (((n + 1 : ℕ) : R)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hdm0 : (d ^ (n + 1) : DensePoly R) ≠ 0 := pow_ne_zero _ hd0
  have hF0 : toRatFuncHom d ≠ (0 : RatFunc R) := toRatFuncHom_ne_zero hd0
  rw [DenseFrac.toRatFunc_normalize, RatFunc.differential_apply,
    RatFunc.deriv_div (toPolynomial_ne_zero hdm0)]
  rw [← toPolynomial_deriv, ← toPolynomial_deriv, ← toRatFuncHom_apply, ← toRatFuncHom_apply,
    ← toRatFuncHom_apply, ← toRatFuncHom_apply]
  have hgderiv : (-(C (((n + 1 : ℕ) : R))⁻¹ * t))′
      = -(C (((n + 1 : ℕ) : R))⁻¹ * t′) := by
    rw [deriv_neg, deriv_C_mul]
  have hdmderiv : (d ^ (n + 1))′ = C (((n + 1 : ℕ)) : R) * d ^ n * d′ :=
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
  have hspT : toRatFuncHom t * toRatFuncHom (d′)
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
private theorem hermiteFactorAux_spec {d : DensePoly R} (hd0 : d ≠ 0) (hdsf : Squarefree d) :
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
      rw [show (splitCoprime c d (d′)).1 = t from rfl,
        show (splitCoprime c d (d′)).2 = b from rfl] at hstep
      have hunfold : hermiteFactorAux d (c :: r :: rs)
          = ((hermiteFactorAux d ((r + b + C (((rs.length + 1 : ℕ) : R))⁻¹ * t′) :: rs)).1
              + DenseFrac.normalize (-(C (((rs.length + 1 : ℕ) : R))⁻¹ * t))
                  (d ^ (rs.length + 1)),
             (hermiteFactorAux d
                ((r + b + C (((rs.length + 1 : ℕ) : R))⁻¹ * t′) :: rs)).2) := by
        simp only [hermiteFactorAux]
        rfl
      rw [invPowSum_map_reverse_cons, invPowSum_map_reverse_cons, hunfold]
      rw [invPowSum_map_reverse_cons] at ih
      simp only [List.length_cons] at *
      simp only [DenseFrac.toRatFunc_add, RatFunc.differential_apply,
        map_add, map_mul] at *
      linear_combination ih + hstep

variable [DensePolySquarefree R]

/-- Bundled Hermite output: `f = rational′ + poly + logPart`, with the log part **proper**
and its canonical (monic, coprime) denominator additionally **squarefree** — the input
contract of the logarithmic stage, carried as invariants rather than side theorems. -/
structure HermiteResult (R : Type u) [Field R] [DecidableEq R] where
  /-- The integrated rational part `G`; its derivative is its contribution. -/
  rational : DenseFrac R
  /-- The polynomial part. -/
  poly : DensePoly R
  /-- The remaining fraction, destined for the logarithmic stage. -/
  logPart : DenseFrac R
  /-- The log part's denominator is squarefree. -/
  logPart_den_squarefree : Squarefree logPart.den.toPoly
  /-- The log part is proper. -/
  logPart_isProper : RatFunc.IsProper (DenseFrac.toRatFunc logPart)

omit [CharZero R] in
/-- The factor column of `sqfPartFrac` is the squarefree decomposition itself. -/
private theorem sqfPartFrac_fst (a p : DensePoly R) :
    ((sqfPartFrac a p).2.map Prod.fst) = DensePolySquarefree.sqfDecomp p := by
  rw [sqfPartFrac]
  exact partFracAux_fst _ _ 1

omit [CharZero R] [DensePolySquarefree R] in
/-- The denominator of the summed log fractions divides the factor product. -/
private theorem logden_dvd (g : DensePoly R × List (DensePoly R) → DensePoly R) :
    ∀ parts : List (DensePoly R × List (DensePoly R)), (∀ fa ∈ parts, fa.1 ≠ 0) →
      ((parts.map fun fa => DenseFrac.normalize (g fa) fa.1).sum).den.toPoly ∣
        (parts.map Prod.fst).prod := by
  intro parts
  induction parts with
  | nil =>
      intro _
      simp only [List.map_nil, List.sum_nil, List.prod_nil]
      exact one_dvd _
  | cons fa T ih =>
      intro h
      simp only [List.map_cons, List.sum_cons, List.prod_cons]
      exact (DenseFrac.den_add_dvd _ _).trans
        (mul_dvd_mul (DenseFrac.den_normalize_dvd (h fa (by simp)))
          (ih fun x hx => h x (by simp [hx])))

omit [CharZero R] in
/-- Nonzero, squarefree factors of the partial-fraction table (from the contract). -/
private theorem sqfPartFrac_factor_props (a p : DensePoly R) :
    ∀ fa ∈ (sqfPartFrac a p).2, fa.1 ≠ 0 ∧ Squarefree fa.1 := by
  intro fa hfa
  have hsf := squarefree_of_mem_sqfPartFrac hfa
  exact ⟨fun h0 => not_squarefree_zero (h0 ▸ hsf), hsf⟩

/-- The log part of the Hermite reduction: the summed normalized log fractions. -/
def hermiteLogPart (f : DenseFrac R) : DenseFrac R :=
  ((sqfPartFrac f.num f.den.toPoly).2.map
    fun fa => DenseFrac.normalize (hermiteFactorAux fa.1 fa.2.reverse).2 fa.1).sum

/-- The summed log fractions have squarefree denominator: it divides the product of the
decomposition factors, which is associated to the squarefree part. -/
private theorem logden_squarefree (f : DenseFrac R) :
    Squarefree (hermiteLogPart f).den.toPoly := by
  unfold hermiteLogPart
  have hp : f.den.toPoly ≠ 0 := f.den.ne_zero
  have hLsf : Squarefree (DensePolySquarefree.sqfDecomp (R := R) f.den.toPoly).prod :=
    squarefree_of_associated (DensePolySquarefree.associated_prod hp)
      (squarefree_sqfreePart hp)
  have hdvd := logden_dvd (fun fa => (hermiteFactorAux fa.1 fa.2.reverse).2)
    (sqfPartFrac f.num f.den.toPoly).2
    (fun fa hfa => (sqfPartFrac_factor_props f.num f.den.toPoly fa hfa).1)
  rw [sqfPartFrac_fst] at hdvd
  exact hLsf.squarefree_of_dvd hdvd

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

omit [DensePolyGcd R] [CharZero R] [DensePolySquarefree R] in
/-- Size comparisons transport to degree comparisons through the bridge. -/
private theorem toPoly_degree_lt_of_size_lt {a b : DensePoly R} (hb : b ≠ 0)
    (h : a.size < b.size) : (toPolynomial a).degree < (toPolynomial b).degree := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [toPolynomial_zero, Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr fun hbb =>
      toPolynomial_ne_zero hb (Polynomial.degree_eq_bot.mp hbb)
  · rw [Polynomial.degree_eq_natDegree (toPolynomial_ne_zero ha),
      Polynomial.degree_eq_natDegree (toPolynomial_ne_zero hb)]
    have h1 := size_eq_natDegree_add_one ha
    have h2 := size_eq_natDegree_add_one hb
    exact_mod_cast (by omega : (toPolynomial a).natDegree < (toPolynomial b).natDegree)

omit [CharZero R] [DensePolySquarefree R] in
/-- The accumulated rational part of a factor sweep is proper. -/
private theorem isProper_factorAux_rational {d : DensePoly R} (hd0 : d ≠ 0) :
    ∀ l : List (DensePoly R),
      RatFunc.IsProper (DenseFrac.toRatFunc (hermiteFactorAux d l).1) := by
  intro l
  induction l using hermiteFactorAux.induct (d := d) with
  | case1 => rw [hermiteFactorAux]; simpa using RatFunc.isProper_zero
  | case2 a => rw [hermiteFactorAux]; simpa using RatFunc.isProper_zero
  | case3 c r rs t b ih =>
      have hunfold : (hermiteFactorAux d (c :: r :: rs)).1
          = (hermiteFactorAux d
              ((r + b + C (((rs.length + 1 : ℕ) : R))⁻¹ * t′) :: rs)).1
            + DenseFrac.normalize (-(C (((rs.length + 1 : ℕ) : R))⁻¹ * t))
                (d ^ (rs.length + 1)) := by
        simp only [hermiteFactorAux]
        rfl
      rw [hunfold, DenseFrac.toRatFunc_add]
      refine RatFunc.IsProper.add ih ?_
      rw [DenseFrac.toRatFunc_normalize]
      refine RatFunc.isProper_of_eq_div
        (toPolynomial_ne_zero (pow_ne_zero _ hd0)) ?_ rfl
      have hsize : t.size < d.size :=
        splitCoprime_size_lt (fun h0 => hd0 (eq_zero_of_size_zero h0)) c (d′)
      calc (toPolynomial (-(C (((rs.length + 1 : ℕ) : R))⁻¹ * t))).degree
          = (Polynomial.C ((((rs.length + 1 : ℕ) : R))⁻¹) * toPolynomial t).degree := by
            rw [toPolynomial_neg, toPolynomial_mul, toPolynomial_C, Polynomial.degree_neg]
        _ ≤ (toPolynomial t).degree := by
            calc (Polynomial.C ((((rs.length + 1 : ℕ) : R))⁻¹) * toPolynomial t).degree
                ≤ (Polynomial.C ((((rs.length + 1 : ℕ) : R))⁻¹)).degree
                  + (toPolynomial t).degree := Polynomial.degree_mul_le _ _
              _ ≤ 0 + (toPolynomial t).degree :=
                  add_le_add Polynomial.degree_C_le le_rfl
              _ = (toPolynomial t).degree := zero_add _
        _ < (toPolynomial d).degree := toPoly_degree_lt_of_size_lt hd0 hsize
        _ ≤ (toPolynomial (d ^ (rs.length + 1))).degree :=
            Polynomial.degree_le_of_dvd
              (toPolynomial_dvd (dvd_pow_self d (Nat.succ_ne_zero rs.length)))
              (toPolynomial_ne_zero (pow_ne_zero _ hd0))

omit [DensePolyGcd R] [CharZero R] [DensePolySquarefree R] in
/-- A descending-term sum over bounded numerators is proper. -/
private theorem isProper_invPowSum {d : DensePoly R} (hd0 : d ≠ 0) :
    ∀ l : List (DensePoly R), (∀ b ∈ l, b.size < d.size) →
      RatFunc.IsProper (invPowSum (toRatFuncHom d) (l.map toRatFuncHom)) := by
  intro l
  induction l with
  | nil => intro _; exact RatFunc.isProper_zero
  | cons x tl ih =>
      intro h
      show RatFunc.IsProper
        ((toRatFuncHom x + invPowSum (toRatFuncHom d) (tl.map toRatFuncHom)) / toRatFuncHom d)
      rw [add_div]
      refine RatFunc.IsProper.add ?_ ?_
      · exact RatFunc.isProper_of_eq_div (toPolynomial_ne_zero hd0)
          (toPoly_degree_lt_of_size_lt hd0 (h x (by simp)))
          (by rw [toRatFuncHom_apply, toRatFuncHom_apply])
      · exact RatFunc.IsProper.div_algebraMap (toPolynomial_ne_zero hd0)
          (ih fun y hy => h y (by simp [hy]))

omit [DensePolySquarefree R] in
/-- The exponent-1 remainder of a factor sweep is proper over its factor. -/
private theorem isProper_factor_term {d : DensePoly R} (hd0 : d ≠ 0) (hdsf : Squarefree d)
    {l : List (DensePoly R)} (hl : ∀ b ∈ l, b.size < d.size) :
    RatFunc.IsProper (toRatFuncHom (hermiteFactorAux d l.reverse).2 / toRatFuncHom d) := by
  have hspec := hermiteFactorAux_spec hd0 hdsf l.reverse
  rw [List.reverse_reverse, RatFunc.differential_apply] at hspec
  have h1 : toRatFuncHom (hermiteFactorAux d l.reverse).2 / toRatFuncHom d
      = invPowSum (toRatFuncHom d) (l.map toRatFuncHom)
        - RatFunc.deriv (DenseFrac.toRatFunc (hermiteFactorAux d l.reverse).1) :=
    (eq_sub_of_add_eq' hspec.symm)
  rw [h1]
  exact (isProper_invPowSum hd0 l hl).sub ((isProper_factorAux_rational hd0 _).deriv)

/-- The summed log fractions are proper. -/
private theorem logsum_isProper (f : DenseFrac R) :
    RatFunc.IsProper (DenseFrac.toRatFunc (hermiteLogPart f)) := by
  unfold hermiteLogPart
  rw [DenseFrac.toRatFunc_list_sum]
  apply RatFunc.isProper_list_sum
  intro x hx
  rw [List.map_map] at hx
  obtain ⟨fa, hfa, rfl⟩ := List.mem_map.mp hx
  have hprops := sqfPartFrac_factor_props f.num f.den.toPoly fa hfa
  have hbound := sqfPartFrac_size_lt (p := f.den.toPoly) f.num fa hfa
  have hterm := isProper_factor_term hprops.1 hprops.2 hbound
  simpa [Function.comp, DenseFrac.toRatFunc_normalize, ← toRatFuncHom_apply] using hterm

/-- **Hermite reduction** of a canonical fraction: the bundled result — no nonzeroness
hypotheses anywhere, since the canonical denominator is monic. -/
def hermiteReduce (f : DenseFrac R) : HermiteResult R where
  rational := ((sqfPartFrac f.num f.den.toPoly).2.map
    fun fa => (hermiteFactorAux fa.1 fa.2.reverse).1).sum
  poly := (sqfPartFrac f.num f.den.toPoly).1
  logPart := hermiteLogPart f
  logPart_den_squarefree := logden_squarefree f
  logPart_isProper := logsum_isProper f

/-- **The Hermite identity**, hypothesis-free: `f = rational′ + poly + logPart` in
`RatFunc R`. -/
theorem hermiteReduce_sound (f : DenseFrac R) :
    DenseFrac.toRatFunc f
      = (DenseFrac.toRatFunc (hermiteReduce f).rational)′
        + toRatFuncHom (hermiteReduce f).poly
        + DenseFrac.toRatFunc (hermiteReduce f).logPart := by
  have hp : f.den.toPoly ≠ 0 := f.den.ne_zero
  have hold := sqfPartFrac_ratFunc hp f.num
  have hpartsum := partsSum_hermite (sqfPartFrac f.num f.den.toPoly).2
    (sqfPartFrac_factor_props f.num f.den.toPoly)
  have hlog : ((( sqfPartFrac f.num f.den.toPoly).2.map
        fun fa => (fa.1, (hermiteFactorAux fa.1 fa.2.reverse).2)).map
          fun db => toRatFuncHom db.2 / toRatFuncHom db.1).sum
      = DenseFrac.toRatFunc (hermiteReduce f).logPart := by
    show _ = DenseFrac.toRatFunc (((sqfPartFrac f.num f.den.toPoly).2.map
      fun fa => DenseFrac.normalize (hermiteFactorAux fa.1 fa.2.reverse).2 fa.1).sum)
    rw [DenseFrac.toRatFunc_list_sum, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro fa _
    simp only [Function.comp_apply, DenseFrac.toRatFunc_normalize, toRatFuncHom_apply]
  show toRatFuncHom f.num / toRatFuncHom f.den.toPoly = _
  rw [hold, hpartsum, hlog]
  show _ = (DenseFrac.toRatFunc (((sqfPartFrac f.num f.den.toPoly).2.map
      fun fa => (hermiteFactorAux fa.1 fa.2.reverse).1).sum))′
    + toRatFuncHom (sqfPartFrac f.num f.den.toPoly).1
    + DenseFrac.toRatFunc (hermiteReduce f).logPart
  ring

/-! ### Completeness: rational integrability is decided by the log part -/

/-- **Completeness of Hermite reduction**: a canonical fraction has a rational-function
antiderivative exactly when the log part vanishes — a decidable test, with a constructive
antiderivative in the affirmative case. -/
theorem hermiteReduce_complete (f : DenseFrac R) :
    (∃ g : RatFunc R, g′ = DenseFrac.toRatFunc f) ↔ (hermiteReduce f).logPart = 0 := by
  constructor
  · rintro ⟨g, hg⟩
    rw [RatFunc.differential_apply] at hg
    have hderiv : RatFunc.deriv (g - DenseFrac.toRatFunc (hermiteReduce f).rational
        - toRatFuncHom (polyIntegrate (hermiteReduce f).poly))
        = DenseFrac.toRatFunc (hermiteReduce f).logPart := by
      rw [RatFunc.deriv_sub, RatFunc.deriv_sub, hg,
        show RatFunc.deriv (toRatFuncHom (polyIntegrate (hermiteReduce f).poly))
            = toRatFuncHom (hermiteReduce f).poly from by
          rw [← RatFunc.differential_apply, toRatFuncHom_deriv, polyIntegrate_deriv],
        hermiteReduce_sound f, RatFunc.differential_apply]
      ring
    have hsf : Squarefree (DenseFrac.toRatFunc (hermiteReduce f).logPart).denom := by
      have hassoc := RatFunc.denom_associated_of_eq_div
        (toPolynomial_ne_zero (hermiteReduce f).logPart.den.ne_zero)
        (isCoprime_toPolynomial_iff.mpr (hermiteReduce f).logPart.coprime)
        (x := DenseFrac.toRatFunc (hermiteReduce f).logPart) rfl
      exact squarefree_of_associated hassoc.symm
        (squarefree_toPolynomial_iff.mpr (hermiteReduce f).logPart_den_squarefree)
    have h0 := RatFunc.eq_zero_of_deriv_of_squarefree_denom hderiv hsf
      (hermiteReduce f).logPart_isProper
    apply DenseFrac.toRatFunc_injective
    rw [DenseFrac.toRatFunc_zero]
    exact h0
  · intro h0
    refine ⟨DenseFrac.toRatFunc (hermiteReduce f).rational
      + toRatFuncHom (polyIntegrate (hermiteReduce f).poly), ?_⟩
    rw [RatFunc.differential_apply, RatFunc.deriv_add,
      show RatFunc.deriv (toRatFuncHom (polyIntegrate (hermiteReduce f).poly))
          = toRatFuncHom (hermiteReduce f).poly from by
        rw [← RatFunc.differential_apply, toRatFuncHom_deriv, polyIntegrate_deriv],
      hermiteReduce_sound f, h0, DenseFrac.toRatFunc_zero, RatFunc.differential_apply]
    ring

end DensePoly

end DeepWiki.CAlgebra
