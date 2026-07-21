import DeepWiki.CAlgebra.Poly.DivisionPseudo
import DeepWiki.CAlgebra.Poly.Euclid
import DeepWiki.CAlgebra.Resultant.Euclidean
import DeepWiki.Algebra.SubresultantPRS

/-! # Polynomial gcd via the subresultant pseudo-remainder sequence

`gcdSubresultant p q` iterates pseudo-division, dividing each pseudo-remainder by the subresultant
factor `β = (−1)^(δ+1) · g · h^δ` (`g` the previous divisor's leading coefficient, `h` the running
subresultant `h`-value, `δ` the degree drop). Over a field every `β` is a nonzero constant — a unit
`C β` of `DensePoly R` — so the sequence satisfies the gcd universal property, agreeing up to a
unit with Mathlib's generic Euclidean-domain gcd (`gcdSubresultant_associated_euclideanDomainGcd`)
and bridging to the `Polynomial` gcd under `toPolynomial`. The `β`-bookkeeping keeps intermediate
coefficients small when the field elements are themselves big objects (tower carriers). -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R]

/-- Subresultant-PRS accumulator: `g` is the previous divisor's leading coefficient and `h` the
running subresultant `h`-value; each pseudo-remainder is divided by `β = (−1)^(δ+1) · g · h^δ`. -/
private def gcdSubAux (r₁ r₂ : DensePoly R) (g h : R) : DensePoly R :=
  if r₂.size = 0 then r₁
  else
    gcdSubAux r₂
      (C ((-1 : R) ^ (r₁.size - r₂.size + 1) * g * h ^ (r₁.size - r₂.size))⁻¹ * pseudoMod r₁ r₂)
      r₂.leadingCoeff
      (if r₁.size - r₂.size = 0 then h
       else r₂.leadingCoeff ^ (r₁.size - r₂.size) / h ^ (r₁.size - r₂.size - 1))
  termination_by r₂.size
  decreasing_by
    rename_i hr
    exact lt_of_le_of_lt (size_C_mul_le _ _) (pseudoMod_size_lt hr r₁)

/-- Polynomial gcd by the subresultant pseudo-remainder sequence. -/
def gcdSubresultant (p q : DensePoly R) : DensePoly R := gcdSubAux p q 1 1

/-- The accumulator divides both sequence entries when `g` and `h` are nonzero (each `β` is then a
unit constant, so pseudo-division steps preserve divisors up to units). -/
private theorem gcdSubAux_dvd (r₁ r₂ : DensePoly R) (g h : R) (hg : g ≠ 0) (hh : h ≠ 0) :
    gcdSubAux r₁ r₂ g h ∣ r₁ ∧ gcdSubAux r₁ r₂ g h ∣ r₂ := by
  revert hg hh
  induction r₁, r₂, g, h using gcdSubAux.induct with
  | case1 r₁ r₂ g h hr =>
      intro _ _
      rw [gcdSubAux.eq_def, if_pos hr]
      exact ⟨dvd_refl r₁, by rw [eq_zero_of_size_zero hr]; exact dvd_zero r₁⟩
  | case2 r₁ r₂ g h hr ih =>
      intro hg hh
      have hg' : r₂.leadingCoeff ≠ 0 := leadingCoeff_ne_zero hr
      have hh' : (if r₁.size - r₂.size = 0 then h
          else r₂.leadingCoeff ^ (r₁.size - r₂.size) / h ^ (r₁.size - r₂.size - 1)) ≠ 0 := by
        split
        · exact hh
        · exact div_ne_zero (pow_ne_zero _ hg') (pow_ne_zero _ hh)
      have hβ : ((-1 : R) ^ (r₁.size - r₂.size + 1) * g * h ^ (r₁.size - r₂.size)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hg)
          (pow_ne_zero _ hh)
      obtain ⟨ih₂, ihrem⟩ := ih hg' hh'
      rw [gcdSubAux.eq_def, if_neg hr]
      refine ⟨?_, ih₂⟩
      apply dvd_of_dvd_C_mul (pow_ne_zero (r₁.size + 1 - r₂.size) hg')
      rw [← pseudoDivMod_spec hr r₁]
      exact dvd_add (ih₂.mul_left _) (dvd_of_dvd_C_mul (inv_ne_zero hβ) ihrem)

/-- Any common divisor of the sequence entries divides the accumulator (no side conditions:
this direction never cancels a constant). -/
private theorem dvd_gcdSubAux {d : DensePoly R} (r₁ r₂ : DensePoly R) (g h : R)
    (h₁ : d ∣ r₁) (h₂ : d ∣ r₂) : d ∣ gcdSubAux r₁ r₂ g h := by
  revert h₁ h₂
  induction r₁, r₂, g, h using gcdSubAux.induct with
  | case1 r₁ r₂ g h hr =>
      intro h₁ _
      rw [gcdSubAux.eq_def, if_pos hr]
      exact h₁
  | case2 r₁ r₂ g h hr ih =>
      intro h₁ h₂
      rw [gcdSubAux.eq_def, if_neg hr]
      refine ih h₂ ?_
      have hrem : d ∣ pseudoMod r₁ r₂ := by
        rw [pseudoMod_eq_sub hr]
        exact dvd_sub (h₁.mul_left _) (h₂.mul_left _)
      exact hrem.mul_left _

/-- The subresultant-PRS gcd divides its left argument. -/
theorem gcdSubresultant_dvd_left (p q : DensePoly R) : gcdSubresultant p q ∣ p :=
  (gcdSubAux_dvd p q 1 1 one_ne_zero one_ne_zero).1

/-- The subresultant-PRS gcd divides its right argument. -/
theorem gcdSubresultant_dvd_right (p q : DensePoly R) : gcdSubresultant p q ∣ q :=
  (gcdSubAux_dvd p q 1 1 one_ne_zero one_ne_zero).2

/-- Any common divisor divides the subresultant-PRS gcd. -/
theorem dvd_gcdSubresultant {d : DensePoly R} (p q : DensePoly R) (h₁ : d ∣ p) (h₂ : d ∣ q) :
    d ∣ gcdSubresultant p q :=
  dvd_gcdSubAux p q 1 1 h₁ h₂

/-- **Agreement with Mathlib's generic Euclidean-domain gcd**: both satisfy the same universal
property, so they coincide up to a unit. -/
theorem gcdSubresultant_associated_euclideanDomainGcd (p q : DensePoly R) :
    Associated (gcdSubresultant p q) (EuclideanDomain.gcd p q) :=
  associated_of_dvd_dvd
    (EuclideanDomain.dvd_gcd (gcdSubresultant_dvd_left p q) (gcdSubresultant_dvd_right p q))
    (dvd_gcdSubresultant p q (EuclideanDomain.gcd_dvd_left p q) (EuclideanDomain.gcd_dvd_right p q))

end DensePoly

/-! ### Mathlib correspondence, via the agreement with the Euclidean gcd -/

open Polynomial in
variable {R : Type u} [Field R] [DecidableEq R] in
/-- The subresultant-PRS gcd is `Associated` to Mathlib's polynomial gcd under `toPolynomial`
(soundness by forward transport, completeness by reverse transport). -/
theorem toPolynomial_gcdSubresultant_associated (p q : DensePoly R) :
    Associated (toPolynomial (DensePoly.gcdSubresultant p q))
      (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) := by
  apply associated_of_dvd_dvd
  · apply EuclideanDomain.dvd_gcd
    · exact toPolynomial_dvd (DensePoly.gcdSubresultant_dvd_left p q)
    · exact toPolynomial_dvd (DensePoly.gcdSubresultant_dvd_right p q)
  · have hgp : ofPolynomial (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) ∣ p :=
      dvd_of_toPolynomial_dvd (by rw [toPolynomial_ofPolynomial]; exact EuclideanDomain.gcd_dvd_left _ _)
    have hgq : ofPolynomial (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) ∣ q :=
      dvd_of_toPolynomial_dvd (by rw [toPolynomial_ofPolynomial]; exact EuclideanDomain.gcd_dvd_right _ _)
    have hfin := toPolynomial_dvd (DensePoly.dvd_gcdSubresultant p q hgp hgq)
    rwa [toPolynomial_ofPolynomial] at hfin

namespace DensePoly

/-! ### The subresultant-divisor resultant -/

section SubresultantResultant

variable {S : Type u} [EuclideanDomain S] [DecidableEq S]

/-- The **reduced-PRS cleanup** (Collins): the state carries the pending divisor `α` — the
previous step's `lc^{δ+1}`, initially `1` — and each pseudo-remainder is divided by it,
coefficient-wise and unchecked. The divisions are exact along genuine descents: each reduced
remainder is a constant multiple of a determinantal subresultant
(`DeepWiki/Algebra/SubresultantSpec`), which is the exactness invariant being discharged
(normal chains first — `subresultant_prs_normal_eq` is stated in exactly this
normalization). -/
def cleanReduced (st : S) (f g r : DensePoly S) : S × DensePoly S × S :=
  (st, ofList (r.coeffs.map (· / st)), g.leadingCoeff ^ (f.size - g.size + 1))

private theorem cleanReduced_size (st : S) (f g r : DensePoly S) :
    (cleanReduced st f g r).2.1.size ≤ r.size := by
  simp only [cleanReduced]
  set l := r.coeffs.map (· / st) with hl
  show (ofList l).size ≤ r.size
  have h1 : (ofList l).size ≤ l.length := trimTrailingZeros_length_le l
  have h2 : l.length = r.size := by rw [hl, List.length_map]; rfl
  omega

/-- **Resultant by the reduced pseudo-remainder sequence** (Collins): fraction-free without
any content gcds along the way. -/
def resultantPRSReduced (f g : DensePoly S) : S :=
  resultantDescent cleanReduced cleanReduced_size 1 f g (f.size - 1) (g.size - 1)

/-- The reduced-PRS resultant agrees with the Sylvester-determinant resultant at the
canonical degrees, **given** an exactness invariant for the carried divisors — the
hypothesis being discharged from the subresultant chain theorems
(`DeepWiki/Algebra/SubresultantPRS`; normal chains first). -/
theorem resultantPRSReduced_eq_of_invariant
    (I : S → DensePoly S → DensePoly S → Prop)
    (hclean : ∀ st f g, 2 ≤ g.size → g.size ≤ f.size → I st f g →
      C (cleanReduced st f g (pseudoMod f g)).1
          * (cleanReduced st f g (pseudoMod f g)).2.1
        = pseudoMod f g)
    (hstep : ∀ st f g, 2 ≤ g.size → g.size ≤ f.size → I st f g →
      I (cleanReduced st f g (pseudoMod f g)).2.2 g
        (cleanReduced st f g (pseudoMod f g)).2.1)
    (hswap : ∀ st f g, f.size < g.size → I st f g → I st g f)
    (f g : DensePoly S) (hI : I 1 f g) :
    resultantPRSReduced f g = (toPolynomial f).resultant (toPolynomial g)
      (toPolynomial f).natDegree (toPolynomial g).natDegree := by
  rw [resultantPRSReduced, natDegree_toPolynomial_eq_size_sub_one,
    natDegree_toPolynomial_eq_size_sub_one]
  exact resultantDescent_eq_of_invariant cleanReduced cleanReduced_size I
    hclean hstep hswap 1 f g _ _ hI
    (le_of_eq (natDegree_toPolynomial_eq_size_sub_one f))
    (le_of_eq (natDegree_toPolynomial_eq_size_sub_one g))

/-- Exact division certified semantically: if the bridged polynomial is a `C a`-multiple,
the coefficient-wise division reconstructs. -/
theorem exact_div_of_toPolynomial_C_mul {a : S} {r : DensePoly S} {P : Polynomial S}
    (h : toPolynomial r = Polynomial.C a * P) :
    C a * ofList (r.coeffs.map (· / a)) = r := by
  have hdvd : ∀ i, a ∣ r.coeff i := by
    intro i
    have hc := congrArg (fun q => Polynomial.coeff q i) h
    simp only [coeff_toPolynomial, Polynomial.coeff_C_mul] at hc
    exact ⟨P.coeff i, hc⟩
  apply toPolynomial_injective
  ext i
  rw [toPolynomial_mul, toPolynomial_C, Polynomial.coeff_C_mul, coeff_toPolynomial,
    coeff_toPolynomial, coeff_ofList, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hi : i < r.coeffs.length
  · rw [List.getElem?_eq_getElem hi]
    show a * (r.coeffs[i] / a) = r.coeff i
    have hco : r.coeff i = r.coeffs[i] := by
      rw [coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      rfl
    rcases eq_or_ne a 0 with rfl | ha0
    · have h0 : r.coeffs[i] = 0 := by
        have := hdvd i
        rw [zero_dvd_iff, hco] at this
        exact this
      rw [h0, EuclideanDomain.zero_div, mul_zero, hco, h0]
    · rw [EuclideanDomain.mul_div_cancel' ha0 (by rw [← hco]; exact hdvd i), hco]
  · rw [List.getElem?_eq_none (by omega)]
    show a * 0 = r.coeff i
    rw [mul_zero, coeff_eq_zero_of_size_le r (by show r.coeffs.length ≤ i; omega)]

/-- **The reduced-PRS exactness invariant**: every division the descent will perform from
this state is exact — the pending divisor `C`-factors out of the bridged pseudo-remainder,
persistently along the mod steps and the entry swap. Mirrors the descent's recursion; the
running arc discharges `ReducedExact 1 f g` from the subresultant chain theorems. -/
def ReducedExact (α : S) (f g : DensePoly S) : Prop :=
  (∃ P : Polynomial S, toPolynomial (pseudoMod f g) = Polynomial.C α * P) ∧
  (2 ≤ g.size → g.size ≤ f.size →
    ReducedExact (g.leadingCoeff ^ (f.size - g.size + 1)) g
      (ofList ((pseudoMod f g).coeffs.map (· / α)))) ∧
  (f.size < g.size → ReducedExact α g f)
  termination_by f.size + 2 * g.size
  decreasing_by
    · have h1 : (pseudoMod f g).size < g.size := pseudoMod_size_lt (by omega) f
      have h2 : (ofList ((pseudoMod f g).coeffs.map (· / α))).size
          ≤ (pseudoMod f g).size := by
        calc (ofList ((pseudoMod f g).coeffs.map (· / α))).size
            ≤ ((pseudoMod f g).coeffs.map (· / α)).length :=
              trimTrailingZeros_length_le _
          _ = (pseudoMod f g).size := (List.length_map _).trans rfl
      omega
    · omega

/-- The descent computes the resultant from any `ReducedExact` entry state — the
single-hypothesis form; discharging the hypothesis is the running arc. -/
theorem resultantPRSReduced_eq_of_exact (f g : DensePoly S) (hI : ReducedExact 1 f g) :
    resultantPRSReduced f g = (toPolynomial f).resultant (toPolynomial g)
      (toPolynomial f).natDegree (toPolynomial g).natDegree := by
  refine resultantPRSReduced_eq_of_invariant ReducedExact ?_ ?_ ?_ f g hI
  · intro st f' g' _ _ hI'
    rw [ReducedExact] at hI'
    obtain ⟨⟨P, hP⟩, -, -⟩ := hI'
    show C st * ofList ((pseudoMod f' g').coeffs.map (· / st)) = pseudoMod f' g'
    exact exact_div_of_toPolynomial_C_mul hP
  · intro st f' g' hg2 hgf hI'
    rw [ReducedExact] at hI'
    exact hI'.2.1 hg2 hgf
  · intro st f' g' hlt hI'
    rw [ReducedExact] at hI'
    exact hI'.2.2 hlt

/-! ### The exactness discharge, brick one: the first pseudo-remainder is a subresultant -/

open DeepWiki.SymbolicIntegration in
/-- **The first pseudo-remainder is (±) a determinantal subresultant**: instantiating the
migrated `subresultant_eq_pseudoRem` at the bridged pseudo-division identity. Together with
the telescopes this grounds the exactness of every reduced-PRS division. -/
theorem subresultant_eq_pseudoMod {f g : DensePoly S} (hg0 : g ≠ 0)
    (hgf : g.size ≤ f.size) (hg2 : 2 ≤ g.size) :
    subresultant (toPolynomial f) (toPolynomial g) (f.size - 1) (g.size - 1) (g.size - 2)
      = Polynomial.C ((-1 : S) ^ (f.size - g.size + 1))
          * toPolynomial (pseudoMod f g) := by
  have hgz : g.size ≠ 0 := fun h0 => hg0 (eq_zero_of_size_zero h0)
  have hf0 : f ≠ 0 := fun h0 => by rw [h0, size_zero] at hgf; omega
  have hlc : (toPolynomial g).coeff (g.size - 1) ≠ 0 := by
    rw [coeff_toPolynomial]
    exact leadingCoeff_ne_zero hgz
  have hid := pseudo_identity (f := f) hgz
  set k := f.size - g.size + 1 with hk
  have hkeq : f.size + 1 - g.size = k := by omega
  set Rem := Polynomial.C ((-1 : S) ^ k) * toPolynomial (pseudoMod f g) with hRem
  have hsq : Polynomial.C ((-1 : S) ^ k) * Polynomial.C ((-1 : S) ^ k)
      = (1 : Polynomial S) := by
    rw [← map_mul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, map_one]
  have hRdeg : Rem.natDegree < g.size - 1 := by
    calc Rem.natDegree ≤ (toPolynomial (pseudoMod f g)).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
      _ = (pseudoMod f g).size - 1 := natDegree_toPolynomial_eq_size_sub_one _
      _ < g.size - 1 := by
          have := pseudoMod_size_lt hgz f
          omega
  have hQdeg : (toPolynomial (pseudoDiv f g)).natDegree + (g.size - 1) ≤ f.size - 1 := by
    rcases eq_or_ne (pseudoDiv f g) 0 with hq0 | hq0
    · rw [hq0, toPolynomial_zero, Polynomial.natDegree_zero, zero_add]
      omega
    · exact pseudoDiv_natDegree_le hg0 hgf hq0
  have hrel : Polynomial.C ((toPolynomial g).coeff (g.size - 1)
        ^ ((f.size - 1) - (g.size - 1) + 1)) * toPolynomial f
      = Polynomial.C ((-1 : S) ^ ((f.size - 1) - (g.size - 1) + 1)) * Rem
        + toPolynomial g * toPolynomial (pseudoDiv f g) := by
    have he : (f.size - 1) - (g.size - 1) + 1 = k := by omega
    rw [he, hRem, ← mul_assoc, hsq, one_mul, coeff_toPolynomial]
    show Polynomial.C (g.leadingCoeff ^ k) * toPolynomial f
      = toPolynomial (pseudoMod f g) + toPolynomial g * toPolynomial (pseudoDiv f g)
    rw [← hkeq, ← hid]
    ring
  have hmain := subresultant_eq_pseudoRem (toPolynomial f) (toPolynomial g) Rem
    (toPolynomial (pseudoDiv f g)) (f.size - 1) (g.size - 1) Rem.natDegree
    hlc (by omega) rfl
    (le_of_eq (natDegree_toPolynomial_eq_size_sub_one g)) hQdeg hrel
  rw [show g.size - 2 = (g.size - 1) - 1 from by omega]
  exact hmain

end SubresultantResultant

end DensePoly

end DeepWiki.CAlgebra
