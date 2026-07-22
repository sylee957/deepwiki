import DeepWiki.CAlgebra.IntegrateRisch.Special
import DeepWiki.CAlgebra.IntegrateRisch.DiffRing
import DeepWiki.CAlgebra.PartFrac
import DeepWiki.CAlgebra.Frac.Field

/-! # Derivation-generic Hermite reduction

Hermite reduction over a monomial level `(K, d, t)` with derivation
`D = extendDeriv d Dt`: a fraction splits as `f = D(rational) + simple + reduced` with
`simple` a squarefree-normal-denominator remainder (the log-part feed) and `reduced` a
special-denominator remainder including the polynomial part (the per-case stage feed).
Each squarefree denominator factor splits into normal and special parts; the normal side
sheds multiplicities by the Bézout integration-by-parts sweep, the special side passes
through untouched. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {K : Type u} [Field K] [DecidableEq K] [DensePolyGcd K]

/-! ### Power sums -/

/-- Descending power sum `Σⱼ cⱼ/pʲ`, head at the top exponent. -/
def powSumDesc (p : DensePoly K) : List (DensePoly K) → DenseFrac K
  | [] => 0
  | c :: cs => DenseFrac.ofPoly c / DenseFrac.ofPoly p ^ (cs.length + 1) + powSumDesc p cs

/-- Ascending power sum `Σⱼ cⱼ/pʲ`, head at exponent one (Horner in `1/p`). -/
def powSumAsc (p : DensePoly K) : List (DensePoly K) → DenseFrac K
  | [] => 0
  | c :: cs => DenseFrac.ofPoly c / DenseFrac.ofPoly p
      + powSumAsc p cs / DenseFrac.ofPoly p

/-- Appending at the bottom exponent shifts the rest up. -/
private theorem powSumDesc_append_singleton (p x : DensePoly K)
    (l : List (DensePoly K)) :
    powSumDesc p (l ++ [x])
      = powSumDesc p l / DenseFrac.ofPoly p + DenseFrac.ofPoly x / DenseFrac.ofPoly p := by
  induction l with
  | nil =>
      show DenseFrac.ofPoly x / DenseFrac.ofPoly p ^ (0 + 1) + 0 = _
      rw [powSumDesc, zero_div, zero_add, pow_one]
      ring
  | cons c l ih =>
      show DenseFrac.ofPoly c / DenseFrac.ofPoly p ^ ((l ++ [x]).length + 1)
          + powSumDesc p (l ++ [x]) = _
      rw [ih, List.length_append]
      simp only [List.length_cons, List.length_nil]
      show _ = (DenseFrac.ofPoly c / DenseFrac.ofPoly p ^ (l.length + 1) + powSumDesc p l)
          / DenseFrac.ofPoly p + DenseFrac.ofPoly x / DenseFrac.ofPoly p
      rw [add_div, div_div, ← pow_succ]
      ring

/-- The descending sum of a reversed list is the ascending sum. -/
theorem powSumDesc_reverse (p : DensePoly K) (cs : List (DensePoly K)) :
    powSumDesc p cs.reverse = powSumAsc p cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      rw [List.reverse_cons, powSumDesc_append_singleton, ih, powSumAsc, add_comm]

/-- The ascending power sum reads as the partial-fraction `invPowSum`. -/
theorem toRatFunc_powSumAsc (p : DensePoly K) (cs : List (DensePoly K)) :
    DenseFrac.toRatFunc (powSumAsc p cs)
      = invPowSum (toRatFuncHom p) (cs.map toRatFuncHom) := by
  induction cs with
  | nil => simp [powSumAsc, invPowSum]
  | cons c cs ih =>
      show DenseFrac.toRatFunc (DenseFrac.ofPoly c / DenseFrac.ofPoly p
          + powSumAsc p cs / DenseFrac.ofPoly p) = _
      rw [DenseFrac.toRatFunc_add,
        show DenseFrac.toRatFunc (DenseFrac.ofPoly c / DenseFrac.ofPoly p)
            = DenseFrac.toRatFunc (DenseFrac.ofPoly c)
              / DenseFrac.toRatFunc (DenseFrac.ofPoly p) from
          map_div₀ (DenseFrac.equivRatFunc (R := K)) _ _,
        show DenseFrac.toRatFunc (powSumAsc p cs / DenseFrac.ofPoly p)
            = DenseFrac.toRatFunc (powSumAsc p cs)
              / DenseFrac.toRatFunc (DenseFrac.ofPoly p) from
          map_div₀ (DenseFrac.equivRatFunc (R := K)) _ _,
        DenseFrac.toRatFunc_ofPoly, DenseFrac.toRatFunc_ofPoly, ih]
      show _ = (toRatFuncHom c + invPowSum (toRatFuncHom p) (cs.map toRatFuncHom))
          / toRatFuncHom p
      rw [add_div, toRatFuncHom_apply]
      rfl

/-! ### The Hermite step and sweep -/

variable [CharZero K]

/-- **The Hermite step** at level data `(d, Dt)`: a term `c/facⁿ⁺²` over a normal `fac`
is the level derivative of `−t/((n+1)·facⁿ⁺¹)` plus the pushed-down term
`(b + D t/(n+1))/facⁿ⁺¹`, where `c = t·(D fac) + b·fac` is the Bézout split. -/
private theorem hermite_stepD {d : K → K} (hd : IsDerivation d) (Dt : DensePoly K)
    {fac : DensePoly K} (hfac0 : fac ≠ 0)
    (hnorm : IsNormal (extendDeriv d Dt) fac) (c : DensePoly K) (n : ℕ) :
    DenseFrac.ofPoly c / DenseFrac.ofPoly fac ^ (n + 2)
      = DenseFrac.extendDeriv d Dt
          (DenseFrac.ofPoly (-(C (((n + 1 : ℕ) : K))⁻¹
              * (splitCoprime c fac (extendDeriv d Dt fac)).1))
            / DenseFrac.ofPoly fac ^ (n + 1))
        + DenseFrac.ofPoly ((splitCoprime c fac (extendDeriv d Dt fac)).2
            + C (((n + 1 : ℕ) : K))⁻¹
              * extendDeriv d Dt (splitCoprime c fac (extendDeriv d Dt fac)).1)
          / DenseFrac.ofPoly fac ^ (n + 1) := by
  have hsp := splitCoprime_spec hnorm c
  set t := (splitCoprime c fac (extendDeriv d Dt fac)).1 with ht
  set b := (splitCoprime c fac (extendDeriv d Dt fac)).2 with hb
  set k : K := ((n + 1 : ℕ) : K) with hkdef
  have hk : k ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hdkinv : d k⁻¹ = 0 := hd.map_inv_of_map_zero (hd.map_natCast (n + 1))
  have hpder := isDerivation_extendDeriv hd Dt
  have hDf := DenseFrac.isDerivation_extendDeriv hd Dt
  have hF0 : DenseFrac.ofPoly fac ≠ (0 : DenseFrac K) := DenseFrac.ofPoly_ne_zero hfac0
  have hM0 : DenseFrac.ofPoly fac ^ (n + 1) ≠ (0 : DenseFrac K) := pow_ne_zero _ hF0
  rw [hDf.map_div _ _ hM0, DenseFrac.extendDeriv_ofPoly hd]
  have hnum : extendDeriv d Dt (-(C k⁻¹ * t)) = -(C k⁻¹ * extendDeriv d Dt t) := by
    rw [hpder.map_neg, hpder.leibniz, extendDeriv_C hd, hdkinv, C_zero, zero_mul, zero_add]
  rw [hnum]
  have hpow : DenseFrac.extendDeriv d Dt (DenseFrac.ofPoly fac ^ (n + 1))
      = ((n + 1 : ℕ) : DenseFrac K) * DenseFrac.ofPoly fac ^ n
          * DenseFrac.ofPoly (extendDeriv d Dt fac) := by
    rw [hDf.map_pow_succ, DenseFrac.extendDeriv_ofPoly hd]
  rw [hpow]
  have hcast : ((n + 1 : ℕ) : DenseFrac K) = DenseFrac.ofPoly (C k) := by
    refine DenseFrac.toRatFunc_injective ?_
    have h1 : DenseFrac.toRatFunc ((n + 1 : ℕ) : DenseFrac K) = ((n + 1 : ℕ) : RatFunc K) :=
      map_natCast (DenseFrac.equivRatFunc (R := K)) (n + 1)
    rw [h1, DenseFrac.toRatFunc_ofPoly, toPolynomial_C, Polynomial.C_eq_natCast, map_natCast]
  have hspF : DenseFrac.ofPoly t * DenseFrac.ofPoly (extendDeriv d Dt fac)
      + DenseFrac.ofPoly b * DenseFrac.ofPoly fac = DenseFrac.ofPoly c := by
    rw [← DenseFrac.ofPoly_mul, ← DenseFrac.ofPoly_mul, ← DenseFrac.ofPoly_add, hsp]
  have hC1 : (C (1 : K) : DensePoly K) = 1 := by
    ext m
    rw [coeff_C, coeff_one]
  have hkinv : DenseFrac.ofPoly (C k⁻¹) * DenseFrac.ofPoly (C k) = 1 := by
    rw [← DenseFrac.ofPoly_mul, ← C_mul, inv_mul_cancel₀ hk, hC1, DenseFrac.ofPoly_one]
  have hkC0 : DenseFrac.ofPoly (C k) ≠ (0 : DenseFrac K) :=
    DenseFrac.ofPoly_ne_zero (fun h0 => hk (by
      have := congrArg (fun q => DensePoly.coeff q 0) h0
      simpa [coeff_C] using this))
  have hu : DenseFrac.ofPoly (C k⁻¹) = (DenseFrac.ofPoly (C k))⁻¹ :=
    eq_inv_of_mul_eq_one_left hkinv
  simp only [DenseFrac.ofPoly_add, DenseFrac.ofPoly_neg, DenseFrac.ofPoly_mul, hcast, hu]
  field_simp
  linear_combination (-(DenseFrac.ofPoly (C k)
      * DenseFrac.ofPoly fac ^ (2 * n + 2))) * hspF

/-- One factor's Hermite sweep over descending numerators for a normal factor: each head
sheds one power of `fac` into the accumulated rational part; the exponent-1 numerator
remains. -/
def hermiteFactorAuxD (d : K → K) (Dt : DensePoly K) (fac : DensePoly K) :
    List (DensePoly K) → DenseFrac K × DensePoly K
  | [] => (0, 0)
  | [a] => (0, a)
  | c :: r :: rs =>
      let t := (splitCoprime c fac (extendDeriv d Dt fac)).1
      let res := hermiteFactorAuxD d Dt fac
        ((r + (splitCoprime c fac (extendDeriv d Dt fac)).2
            + C (((rs.length + 1 : ℕ) : K))⁻¹ * extendDeriv d Dt t) :: rs)
      (res.1 + DenseFrac.ofPoly (-(C (((rs.length + 1 : ℕ) : K))⁻¹ * t))
          / DenseFrac.ofPoly fac ^ (rs.length + 1),
        res.2)
  termination_by l => l.length

/-- **The sweep identity**: the descending power sum is the level derivative of the
accumulated rational part plus the residual exponent-1 term. -/
private theorem hermiteFactorAuxD_spec {d : K → K} (hd : IsDerivation d)
    (Dt : DensePoly K) {fac : DensePoly K} (hfac0 : fac ≠ 0)
    (hnorm : IsNormal (extendDeriv d Dt) fac) (cs : List (DensePoly K)) :
    powSumDesc fac cs
      = DenseFrac.extendDeriv d Dt (hermiteFactorAuxD d Dt fac cs).1
        + DenseFrac.ofPoly (hermiteFactorAuxD d Dt fac cs).2 / DenseFrac.ofPoly fac := by
  have hDf := DenseFrac.isDerivation_extendDeriv hd Dt
  induction cs using hermiteFactorAuxD.induct d Dt fac with
  | case1 =>
      rw [hermiteFactorAuxD]
      show (0 : DenseFrac K) = DenseFrac.extendDeriv d Dt 0
          + DenseFrac.ofPoly 0 / DenseFrac.ofPoly fac
      rw [hDf.map_zero, DenseFrac.ofPoly_zero, zero_div, add_zero]
  | case2 a =>
      rw [hermiteFactorAuxD]
      show DenseFrac.ofPoly a / DenseFrac.ofPoly fac ^ (0 + 1) + 0
          = DenseFrac.extendDeriv d Dt 0 + DenseFrac.ofPoly a / DenseFrac.ofPoly fac
      rw [hDf.map_zero, pow_one, add_zero, zero_add]
  | case3 c r rs tlet ih =>
      rw [hermiteFactorAuxD]
      simp only []
      rw [show tlet = (splitCoprime c fac (extendDeriv d Dt fac)).1 from rfl] at ih
      rw [show powSumDesc fac (c :: r :: rs)
          = DenseFrac.ofPoly c / DenseFrac.ofPoly fac ^ (rs.length + 1 + 1)
            + (DenseFrac.ofPoly r / DenseFrac.ofPoly fac ^ (rs.length + 1)
              + powSumDesc fac rs) from rfl]
      rw [show powSumDesc fac ((r + (splitCoprime c fac (extendDeriv d Dt fac)).2
            + C (((rs.length + 1 : ℕ) : K))⁻¹
              * extendDeriv d Dt (splitCoprime c fac (extendDeriv d Dt fac)).1) :: rs)
          = DenseFrac.ofPoly (r + (splitCoprime c fac (extendDeriv d Dt fac)).2
              + C (((rs.length + 1 : ℕ) : K))⁻¹
                * extendDeriv d Dt (splitCoprime c fac (extendDeriv d Dt fac)).1)
            / DenseFrac.ofPoly fac ^ (rs.length + 1) + powSumDesc fac rs from rfl] at ih
      rw [hDf.map_add]
      have hstep := hermite_stepD hd Dt hfac0 hnorm c rs.length
      rw [DenseFrac.ofPoly_add, add_div] at hstep
      rw [DenseFrac.ofPoly_add, DenseFrac.ofPoly_add, add_div, add_div] at ih
      linear_combination hstep + ih

/-! ### Per-factor processing: the normal/special split -/

/-- Power sum starting at exponent `e+1`: `Σⱼ cⱼ/p^(e+j+1)`. -/
def powSumFrom (p : DensePoly K) : ℕ → List (DensePoly K) → DenseFrac K
  | _, [] => 0
  | e, c :: cs => DenseFrac.ofPoly c / DenseFrac.ofPoly p ^ (e + 1)
      + powSumFrom p (e + 1) cs

omit [CharZero K] in
/-- The started power sum is the ascending sum shifted down. -/
private theorem powSumFrom_eq (p : DensePoly K) (cs : List (DensePoly K)) : ∀ e,
    powSumFrom p e cs = powSumAsc p cs / DenseFrac.ofPoly p ^ e := by
  induction cs with
  | nil => intro e; rw [powSumFrom, powSumAsc, zero_div]
  | cons c cs ih =>
      intro e
      rw [powSumFrom, powSumAsc, ih (e + 1), add_div, div_div, ← pow_succ', div_div,
        ← pow_succ']

omit [CharZero K] in
/-- The started power sum at zero is the ascending sum. -/
private theorem powSumFrom_zero (p : DensePoly K) (cs : List (DensePoly K)) :
    powSumFrom p 0 cs = powSumAsc p cs := by
  rw [powSumFrom_eq, pow_zero, div_one]

/-- Split ascending numerators against coprime normal/special power pairs. -/
def splitNumers (nn s : DensePoly K) : List (DensePoly K) → ℕ →
    List (DensePoly K) × List (DensePoly K)
  | [], _ => ([], [])
  | c :: cs, e =>
      let tb := splitCoprime c (nn ^ (e + 1)) (s ^ (e + 1))
      let rest := splitNumers nn s cs (e + 1)
      (tb.1 :: rest.1, tb.2 :: rest.2)

omit [CharZero K] in
/-- **The split identity**: the power sum over `nn·s` is the sum of the split power
sums over `nn` and `s`. -/
private theorem splitNumers_spec {nn s : DensePoly K} (hcop : IsCoprime nn s)
    (hnn0 : nn ≠ 0) (hs0 : s ≠ 0) (cs : List (DensePoly K)) : ∀ e,
    powSumFrom (nn * s) e cs
      = powSumFrom nn e (splitNumers nn s cs e).1
        + powSumFrom s e (splitNumers nn s cs e).2 := by
  induction cs with
  | nil => intro e; rw [splitNumers, powSumFrom, powSumFrom, powSumFrom, add_zero]
  | cons c cs ih =>
      intro e
      rw [splitNumers]
      simp only []
      rw [powSumFrom, powSumFrom, powSumFrom, ih (e + 1)]
      have hsp := splitCoprime_spec (hcop.pow (n := e + 1) (m := e + 1)) c
      have hterm : DenseFrac.ofPoly c / DenseFrac.ofPoly (nn * s) ^ (e + 1)
          = DenseFrac.ofPoly (splitCoprime c (nn ^ (e + 1)) (s ^ (e + 1))).1
              / DenseFrac.ofPoly nn ^ (e + 1)
            + DenseFrac.ofPoly (splitCoprime c (nn ^ (e + 1)) (s ^ (e + 1))).2
              / DenseFrac.ofPoly s ^ (e + 1) := by
        have hN : DenseFrac.ofPoly nn ^ (e + 1) ≠ (0 : DenseFrac K) :=
          pow_ne_zero _ (DenseFrac.ofPoly_ne_zero hnn0)
        have hS : DenseFrac.ofPoly s ^ (e + 1) ≠ (0 : DenseFrac K) :=
          pow_ne_zero _ (DenseFrac.ofPoly_ne_zero hs0)
        have hspF : DenseFrac.ofPoly (splitCoprime c (nn ^ (e + 1)) (s ^ (e + 1))).1
              * DenseFrac.ofPoly s ^ (e + 1)
            + DenseFrac.ofPoly (splitCoprime c (nn ^ (e + 1)) (s ^ (e + 1))).2
              * DenseFrac.ofPoly nn ^ (e + 1)
            = DenseFrac.ofPoly c := by
          have := congrArg DenseFrac.ofPoly hsp
          rw [DenseFrac.ofPoly_add, DenseFrac.ofPoly_mul, DenseFrac.ofPoly_mul] at this
          rw [DenseFrac.ofPoly_pow, DenseFrac.ofPoly_pow] at this
          exact this
        rw [DenseFrac.ofPoly_mul, mul_pow]
        rw [div_add_div _ _ hN hS, ← hspF]
        ring
      rw [hterm]
      ring

/-- Process one squarefree factor: split into normal and special parts, sweep the
normal side, division-reduce the residual numerator. Returns the accumulated rational
part, the simple term (proper over the normal part), and the reduced term (polynomial
spill-over plus the special-denominator sum). -/
def hermiteFactorD (d : K → K) (Dt : DensePoly K) (fac : DensePoly K)
    (cs : List (DensePoly K)) : DenseFrac K × DenseFrac K × DenseFrac K :=
  let s := specialPart (extendDeriv d Dt) fac
  let nn := normalPart (extendDeriv d Dt) fac
  let tb := splitNumers nn s cs 0
  let sweep := hermiteFactorAuxD d Dt nn tb.1.reverse
  (sweep.1,
   DenseFrac.ofPoly (sweep.2 % nn) / DenseFrac.ofPoly nn,
   DenseFrac.ofPoly (sweep.2 / nn) + powSumAsc s tb.2)

/-- **The per-factor identity**: the factor's power sum is the level derivative of the
accumulated rational part plus the simple and reduced terms. -/
private theorem hermiteFactorD_spec {d : K → K} (hd : IsDerivation d) (Dt : DensePoly K)
    {fac : DensePoly K} (hfac0 : fac ≠ 0) (hsf : Squarefree fac)
    (cs : List (DensePoly K)) :
    powSumAsc fac cs
      = DenseFrac.extendDeriv d Dt (hermiteFactorD d Dt fac cs).1
        + (hermiteFactorD d Dt fac cs).2.1 + (hermiteFactorD d Dt fac cs).2.2 := by
  have hpd := isDerivation_extendDeriv hd Dt
  simp only [hermiteFactorD]
  set nn := normalPart (extendDeriv d Dt) fac with hnndef
  set sp := specialPart (extendDeriv d Dt) fac with hsdef
  set tb := splitNumers nn sp cs 0 with htbdef
  set SW := (hermiteFactorAuxD d Dt nn tb.1.reverse).2 with hSWdef
  have hs0 : sp ≠ 0 := specialPart_ne_zero hfac0
  have hnn0 : nn ≠ 0 := normalPart_ne_zero hfac0
  have hmul : nn * sp = fac := normalPart_mul_specialPart hfac0
  have hcop : IsCoprime nn sp := isCoprime_normalPart_specialPart hfac0 hsf
  have hnorm : IsNormal (extendDeriv d Dt) nn := isNormal_normalPart hpd hfac0 hsf
  conv_lhs => rw [← powSumFrom_zero, ← hmul]
  rw [splitNumers_spec hcop hnn0 hs0 cs 0, powSumFrom_zero, powSumFrom_zero,
    ← powSumDesc_reverse, hermiteFactorAuxD_spec hd Dt hnn0 hnorm]
  have hdm := EuclideanDomain.div_add_mod SW nn
  have hsplit : DenseFrac.ofPoly SW / DenseFrac.ofPoly nn
      = DenseFrac.ofPoly (SW / nn) + DenseFrac.ofPoly (SW % nn) / DenseFrac.ofPoly nn := by
    conv_lhs => rw [← hdm]
    rw [DenseFrac.ofPoly_add, DenseFrac.ofPoly_mul, add_div,
      mul_div_cancel_left₀ _ (DenseFrac.ofPoly_ne_zero hnn0)]
  linear_combination hsplit

/-! ### The bundled reduction -/

/-- **Bundled derivation-generic Hermite result** at level data `(d, Dt)`:
`f = D(rational) + simple + reduced`, with the simple part's denominator squarefree and
normal (the log-part feed) and the reduced part's denominator dividing a special
polynomial (the per-case stage feed, including the polynomial part). -/
structure ResultHermiteD (K : Type u) [Field K] [DecidableEq K] [DensePolyGcd K]
    (d : K → K) (Dt : DensePoly K) where
  /-- The integrated-by-parts rational part. -/
  rational : DenseFrac K
  /-- The simple remainder: squarefree normal denominator. -/
  simple : DenseFrac K
  /-- The reduced remainder: special denominator, including the polynomial part. -/
  reduced : DenseFrac K
  /-- The simple denominator is squarefree. -/
  simple_den_squarefree : Squarefree simple.den.toPoly
  /-- The simple denominator is normal. -/
  simple_den_normal : IsNormal (extendDeriv d Dt) simple.den.toPoly
  /-- The reduced denominator divides a nonzero special polynomial. -/
  reduced_den_special : ∃ S : DensePoly K, S ≠ 0 ∧ IsSpecial (extendDeriv d Dt) S
    ∧ reduced.den.toPoly ∣ S

section Assembly

variable {d : K → K} (Dt : DensePoly K)

/-- Sum of the per-factor identities over a parts table. -/
private theorem sum_factor_split (hd : IsDerivation d)
    (parts : List (DensePoly K × List (DensePoly K)))
    (hprops : ∀ fa ∈ parts, fa.1 ≠ 0 ∧ Squarefree fa.1) :
    (parts.map fun fa => powSumAsc fa.1 fa.2).sum
      = DenseFrac.extendDeriv d Dt
          ((parts.map fun fa => (hermiteFactorD d Dt fa.1 fa.2).1).sum)
        + (parts.map fun fa => (hermiteFactorD d Dt fa.1 fa.2).2.1).sum
        + (parts.map fun fa => (hermiteFactorD d Dt fa.1 fa.2).2.2).sum := by
  induction parts with
  | nil =>
      simp only [List.map_nil, List.sum_nil]
      rw [(DenseFrac.isDerivation_extendDeriv hd Dt).map_zero, add_zero, add_zero]
  | cons fa rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [(DenseFrac.isDerivation_extendDeriv hd Dt).map_add,
        hermiteFactorD_spec hd Dt (hprops fa List.mem_cons_self).1
          (hprops fa List.mem_cons_self).2,
        ih (fun x hx => hprops x (List.mem_cons_of_mem _ hx))]
      ring

/-- The partial-fraction front end, data-level. -/
private theorem sqfPartFrac_sum [DensePolySquarefree K] (f : DenseFrac K) :
    f = DenseFrac.ofPoly (sqfPartFrac f.num f.den.toPoly).1
      + ((sqfPartFrac f.num f.den.toPoly).2.map fun fa => powSumAsc fa.1 fa.2).sum := by
  refine DenseFrac.toRatFunc_injective ?_
  rw [DenseFrac.toRatFunc_add, DenseFrac.toRatFunc_ofPoly, DenseFrac.toRatFunc_list_sum,
    show DenseFrac.toRatFunc f = toRatFuncHom f.num / toRatFuncHom f.den.toPoly from rfl,
    sqfPartFrac_ratFunc f.den.ne_zero f.num, partsSum, List.map_map,
    show (List.map (DenseFrac.toRatFunc ∘ fun fa => powSumAsc fa.1 fa.2)
          (sqfPartFrac f.num f.den.toPoly).2)
        = (sqfPartFrac f.num f.den.toPoly).2.map
            (fun fa => invPowSum (toRatFuncHom fa.1) (fa.2.map toRatFuncHom)) from
      List.map_congr_left fun fa _ => by
        rw [Function.comp_apply, toRatFunc_powSumAsc]]
  rfl

omit [CharZero K] in
/-- Per-part properties from the decomposition contract. -/
private theorem parts_props [DensePolySquarefree K] (f : DenseFrac K) :
    ∀ fa ∈ (sqfPartFrac f.num f.den.toPoly).2, fa.1 ≠ 0 ∧ Squarefree fa.1 := by
  intro fa hfa
  have hsf := squarefree_of_mem_sqfPartFrac hfa
  exact ⟨fun h0 => not_squarefree_zero (h0 ▸ hsf), hsf⟩

/-- The factor column of the decomposition has squarefree product. -/
private theorem squarefree_parts_prod [DensePolySquarefree K] (f : DenseFrac K) :
    Squarefree (((sqfPartFrac f.num f.den.toPoly).2.map Prod.fst).prod) := by
  have hp : f.den.toPoly ≠ 0 := f.den.ne_zero
  rw [show (sqfPartFrac f.num f.den.toPoly).2.map Prod.fst
      = DensePolySquarefree.sqfDecomp f.den.toPoly from partFracAux_fst _ _ _]
  exact squarefree_of_associated (DensePolySquarefree.associated_prod hp)
    (squarefree_sqfreePart hp)

omit [CharZero K] in
/-- The simple sum's denominator divides the product of the normal parts. -/
private theorem den_simple_sum_dvd (parts : List (DensePoly K × List (DensePoly K)))
    (hne : ∀ fa ∈ parts, fa.1 ≠ 0) :
    ((parts.map fun fa => (hermiteFactorD d Dt fa.1 fa.2).2.1).sum).den.toPoly
      ∣ (parts.map fun fa => normalPart (extendDeriv d Dt) fa.1).prod := by
  induction parts with
  | nil =>
      show ((0 : DenseFrac K)).den.toPoly ∣ 1
      exact dvd_refl 1
  | cons fa rest ih =>
      simp only [List.map_cons, List.sum_cons, List.prod_cons]
      exact (DenseFrac.den_add_dvd _ _).trans
        (mul_dvd_mul (DenseFrac.den_ofPoly_div_dvd _
            (normalPart_ne_zero (hne fa List.mem_cons_self)))
          (ih (fun x hx => hne x (List.mem_cons_of_mem _ hx))))

omit [CharZero K] in
/-- The normal-part product divides the factor product. -/
private theorem prod_normalPart_dvd (parts : List (DensePoly K × List (DensePoly K)))
    (hne : ∀ fa ∈ parts, fa.1 ≠ 0) :
    (parts.map fun fa => normalPart (extendDeriv d Dt) fa.1).prod
      ∣ (parts.map Prod.fst).prod := by
  induction parts with
  | nil => exact dvd_refl 1
  | cons fa rest ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_dvd_mul (normalPart_dvd (hne fa List.mem_cons_self))
        (ih (fun x hx => hne x (List.mem_cons_of_mem _ hx)))

omit [CharZero K] in
/-- The normal-part product is normal (from squarefreeness of the factor product). -/
private theorem isNormal_prod_normalPart (hd : IsDerivation d)
    (parts : List (DensePoly K × List (DensePoly K)))
    (hne : ∀ fa ∈ parts, fa.1 ≠ 0)
    (hsfp : Squarefree ((parts.map Prod.fst).prod)) :
    IsNormal (extendDeriv d Dt)
      ((parts.map fun fa => normalPart (extendDeriv d Dt) fa.1).prod) := by
  have hpd := isDerivation_extendDeriv hd Dt
  induction parts with
  | nil =>
      show IsNormal (extendDeriv d Dt) 1
      exact isCoprime_one_left
  | cons fa rest ih =>
      simp only [List.map_cons, List.prod_cons] at hsfp ⊢
      have hfa0 := hne fa List.mem_cons_self
      have hsf1 : Squarefree fa.1 := hsfp.of_mul_left
      have hrest : Squarefree ((rest.map Prod.fst).prod) := hsfp.of_mul_right
      have hcop0 : IsCoprime fa.1 ((rest.map Prod.fst).prod) :=
        isCoprime_of_squarefree_mul hsfp
      refine IsNormal.mul hpd (isNormal_normalPart hpd hfa0 hsf1)
        (ih (fun x hx => hne x (List.mem_cons_of_mem _ hx)) hrest) ?_
      exact (hcop0.of_isCoprime_of_dvd_left (normalPart_dvd hfa0)).of_isCoprime_of_dvd_right
        (prod_normalPart_dvd Dt rest (fun x hx => hne x (List.mem_cons_of_mem _ hx)))

omit [CharZero K] in
/-- Special-divisor witnesses compose across sums. -/
private theorem exists_special_den_add (hd : IsDerivation d) {a b : DenseFrac K}
    (h1 : ∃ S : DensePoly K, S ≠ 0 ∧ IsSpecial (extendDeriv d Dt) S ∧ a.den.toPoly ∣ S)
    (h2 : ∃ S : DensePoly K, S ≠ 0 ∧ IsSpecial (extendDeriv d Dt) S ∧ b.den.toPoly ∣ S) :
    ∃ S : DensePoly K, S ≠ 0 ∧ IsSpecial (extendDeriv d Dt) S
      ∧ (a + b).den.toPoly ∣ S := by
  obtain ⟨S1, h10, h1s, h1d⟩ := h1
  obtain ⟨S2, h20, h2s, h2d⟩ := h2
  exact ⟨S1 * S2, mul_ne_zero h10 h20,
    IsSpecial.mul (isDerivation_extendDeriv hd Dt) h1s h2s,
    (DenseFrac.den_add_dvd a b).trans (mul_dvd_mul h1d h2d)⟩

omit [DensePolyGcd K] [CharZero K] in
/-- The trivial special witness for a polynomial term. -/
private theorem exists_special_den_ofPoly (q : DensePoly K) :
    ∃ S : DensePoly K, S ≠ 0 ∧ IsSpecial (extendDeriv d Dt) S
      ∧ (DenseFrac.ofPoly q).den.toPoly ∣ S :=
  ⟨1, one_ne_zero, one_dvd _, one_dvd 1⟩

omit [CharZero K] in
/-- Denominator bound for a quotient by an embedded polynomial. -/
private theorem den_div_ofPoly_dvd (x : DenseFrac K) {s : DensePoly K} (hs : s ≠ 0) :
    (x / DenseFrac.ofPoly s).den.toPoly ∣ x.den.toPoly * s := by
  apply DenseFrac.den_dvd_of_eq_div (n := x.num) (mul_ne_zero x.den.ne_zero hs)
  rw [show DenseFrac.toRatFunc (x / DenseFrac.ofPoly s)
      = DenseFrac.toRatFunc x / DenseFrac.toRatFunc (DenseFrac.ofPoly s) from
      map_div₀ (DenseFrac.equivRatFunc (R := K)) _ _,
    DenseFrac.toRatFunc_ofPoly,
    show DenseFrac.toRatFunc x
      = algebraMap (Polynomial K) (RatFunc K) (toPolynomial x.num)
        / algebraMap (Polynomial K) (RatFunc K) (toPolynomial x.den.toPoly) from rfl,
    toPolynomial_mul, map_mul, div_div]

omit [CharZero K] in
/-- Special-divisor witness for a special-denominator power sum. -/
private theorem exists_special_den_powSumAsc (hd : IsDerivation d) {s : DensePoly K}
    (hs0 : s ≠ 0) (hspec : IsSpecial (extendDeriv d Dt) s) (bs : List (DensePoly K)) :
    ∃ S : DensePoly K, S ≠ 0 ∧ IsSpecial (extendDeriv d Dt) S
      ∧ (powSumAsc s bs).den.toPoly ∣ S := by
  induction bs with
  | nil => exact ⟨1, one_ne_zero, one_dvd _, one_dvd 1⟩
  | cons b bs ih =>
      obtain ⟨S, hS0, hSs, hSd⟩ := ih
      refine exists_special_den_add Dt hd
        ⟨s, hs0, hspec, DenseFrac.den_ofPoly_div_dvd b hs0⟩
        ⟨S * s, mul_ne_zero hS0 hs0,
          IsSpecial.mul (isDerivation_extendDeriv hd Dt) hSs hspec,
          (den_div_ofPoly_dvd _ hs0).trans (mul_dvd_mul hSd dvd_rfl)⟩

omit [CharZero K] in
/-- Special-divisor witness for one factor's reduced term. -/
private theorem exists_special_den_factor (hd : IsDerivation d) {fac : DensePoly K}
    (hfac0 : fac ≠ 0) (hsf : Squarefree fac) (cs : List (DensePoly K)) :
    ∃ S : DensePoly K, S ≠ 0 ∧ IsSpecial (extendDeriv d Dt) S
      ∧ ((hermiteFactorD d Dt fac cs).2.2).den.toPoly ∣ S := by
  simp only [hermiteFactorD]
  exact exists_special_den_add Dt hd (exists_special_den_ofPoly Dt _)
    (exists_special_den_powSumAsc Dt hd (specialPart_ne_zero hfac0)
      (isSpecial_specialPart (isDerivation_extendDeriv hd Dt) hfac0 hsf) _)

omit [CharZero K] in
/-- Special-divisor witness for the summed reduced terms. -/
private theorem exists_special_den_sum (hd : IsDerivation d)
    (parts : List (DensePoly K × List (DensePoly K)))
    (hprops : ∀ fa ∈ parts, fa.1 ≠ 0 ∧ Squarefree fa.1) :
    ∃ S : DensePoly K, S ≠ 0 ∧ IsSpecial (extendDeriv d Dt) S
      ∧ (((parts.map fun fa => (hermiteFactorD d Dt fa.1 fa.2).2.2).sum)).den.toPoly
        ∣ S := by
  induction parts with
  | nil => exact ⟨1, one_ne_zero, one_dvd _, one_dvd 1⟩
  | cons fa rest ih =>
      simp only [List.map_cons, List.sum_cons]
      exact exists_special_den_add Dt hd
        (exists_special_den_factor Dt hd (hprops fa List.mem_cons_self).1
          (hprops fa List.mem_cons_self).2 fa.2)
        (ih (fun x hx => hprops x (List.mem_cons_of_mem _ hx)))

end Assembly

variable [DensePolySquarefree K]

/-- **Derivation-generic Hermite reduction** of a canonical fraction at level data
`(d, Dt)`: partial fractions over the squarefree decomposition, per-factor
normal/special split, and the Bézout sweep on the normal side. -/
def hermiteReduceD (F : DenseDiffRing K) (Dt : DensePoly K)
    (f : DenseFrac K) : ResultHermiteD K F.d Dt where
  rational := ((sqfPartFrac f.num f.den.toPoly).2.map
    fun fa => (hermiteFactorD F.d Dt fa.1 fa.2).1).sum
  simple := ((sqfPartFrac f.num f.den.toPoly).2.map
    fun fa => (hermiteFactorD F.d Dt fa.1 fa.2).2.1).sum
  reduced := DenseFrac.ofPoly (sqfPartFrac f.num f.den.toPoly).1
    + ((sqfPartFrac f.num f.den.toPoly).2.map
        fun fa => (hermiteFactorD F.d Dt fa.1 fa.2).2.2).sum
  simple_den_squarefree := by
    have hdvd := (den_simple_sum_dvd (d := F.d) Dt (sqfPartFrac f.num f.den.toPoly).2
        (fun fa hfa => (parts_props f fa hfa).1)).trans
      (prod_normalPart_dvd (d := F.d) Dt (sqfPartFrac f.num f.den.toPoly).2
        (fun fa hfa => (parts_props f fa hfa).1))
    exact (squarefree_parts_prod f).squarefree_of_dvd hdvd
  simple_den_normal := by
    refine IsNormal.of_dvd (isDerivation_extendDeriv F.isDerivation Dt) ?_
      (den_simple_sum_dvd (d := F.d) Dt (sqfPartFrac f.num f.den.toPoly).2
        (fun fa hfa => (parts_props f fa hfa).1))
    exact isNormal_prod_normalPart Dt F.isDerivation (sqfPartFrac f.num f.den.toPoly).2
      (fun fa hfa => (parts_props f fa hfa).1) (squarefree_parts_prod f)
  reduced_den_special := by
    exact exists_special_den_add Dt F.isDerivation (exists_special_den_ofPoly Dt _)
      (exists_special_den_sum Dt F.isDerivation (sqfPartFrac f.num f.den.toPoly).2
        (parts_props f))

/-- **Soundness of the derivation-generic Hermite reduction**, data-level:
`f = D(rational) + simple + reduced`. -/
theorem hermiteReduceD_sound (F : DenseDiffRing K) (Dt : DensePoly K)
    (f : DenseFrac K) :
    f = DenseFrac.extendDeriv F.d Dt (hermiteReduceD F Dt f).rational
      + (hermiteReduceD F Dt f).simple + (hermiteReduceD F Dt f).reduced := by
  have hfront := sqfPartFrac_sum f
  have hsplit := sum_factor_split Dt F.isDerivation (sqfPartFrac f.num f.den.toPoly).2
    (parts_props f)
  show f = DenseFrac.extendDeriv F.d Dt (((sqfPartFrac f.num f.den.toPoly).2.map
      fun fa => (hermiteFactorD F.d Dt fa.1 fa.2).1).sum)
    + ((sqfPartFrac f.num f.den.toPoly).2.map
        fun fa => (hermiteFactorD F.d Dt fa.1 fa.2).2.1).sum
    + (DenseFrac.ofPoly (sqfPartFrac f.num f.den.toPoly).1
        + ((sqfPartFrac f.num f.den.toPoly).2.map
            fun fa => (hermiteFactorD F.d Dt fa.1 fa.2).2.2).sum)
  conv_lhs => rw [hfront, hsplit]
  ring

end DensePoly

end DeepWiki.CAlgebra
