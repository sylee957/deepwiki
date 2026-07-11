import DeepWiki.SymbolicIntegration.CanonicalRepresentation.Classify
import DeepWiki.SymbolicIntegration.Core.Differential.Gcd.PrimeFactors
import DeepWiki.SymbolicIntegration.CanonicalRepresentation.NormalSqfree
import DeepWiki.SymbolicIntegration.Core.Differential.ImplicitDerivLinearFactors
import DeepWiki.ComputableAlgebra.PolySquarefreeTheory

/-! # Canonical split-factor algorithm

Split-factor recursion and correctness for canonical representations. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section SplitFactor
variable {K : Type*} [Field K] [Differential K]

open Classical in
/-- The squarefree special factor extracted at one `splitFactor` step:
`S = gcd(p, Dp) / gcd(p, dp/dt)` (`Dt = v`) — the product of the *distinct* special irreducible
factors of `p`. -/
noncomputable def splitFactorStep (v p : K[X]) : K[X] :=
  gcd p (Differential.implicitDeriv v p) / gcd p (derivative p)

open Classical in
/-- The `fuel`-bounded splitting recursion: each step extracts the squarefree special factor
`S = gcd(p,Dp)/gcd(p,dp/dt)`, recursing on `p/S`, and returns `(pₙ, pₛ)`. -/
noncomputable def splitFactorAux (v : K[X]) : K[X] → ℕ → K[X] × K[X]
  | p, 0 => (p, 1)
  | p, (n + 1) =>
    let S := splitFactorStep v p
    if S.natDegree = 0 then (p, 1)
    else
      let q := splitFactorAux v (p / S) n
      (q.1, S * q.2)

open Classical in
/-- The splitting of `p` into its normal part `pₙ` and special part `pₛ` w.r.t. the monomial
derivation `D` (`Dt = v`), with `p = pₙ·pₛ`. Iterates
`S ← gcd(p, Dp)/gcd(p, dp/dt)` until the remaining factor is normal. -/
noncomputable def splitFactor (v p : K[X]) : K[X] × K[X] :=
  splitFactorAux v p p.natDegree

open Classical in
/-- One-step property of the `splitFactor` step `S`: if `S` is constant then `q` is normal;
if non-constant then `S` is a special factor of `q` with strictly smaller-degree quotient. -/
def IsSplitFactorStep (v q : K[X]) : Prop :=
  ((splitFactorStep v q).natDegree = 0 → @IsNormal _ _ ⟨Differential.implicitDeriv v⟩ q) ∧
  (0 < (splitFactorStep v q).natDegree →
    (splitFactorStep v q ∣ q ∧
     (q / splitFactorStep v q).natDegree < q.natDegree ∧
     @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ (splitFactorStep v q)))

open Classical in
/-- Under the one-step property holding everywhere, for fuel `≥ deg p`, `splitFactorAux v p fuel`
returns a splitting factorization `(pₙ, pₛ)` of `p` (`p = pₛ·pₙ`, `pₛ` special, `pₙ` normal). -/
theorem splitFactorAux_isSplittingFactorization (v : K[X])
    (hstep : ∀ q : K[X], IsSplitFactorStep v q) :
    ∀ (fuel : ℕ) (p : K[X]), p.natDegree ≤ fuel →
      @IsSplittingFactorization _ _ ⟨Differential.implicitDeriv v⟩ p
        (splitFactorAux v p fuel).2 (splitFactorAux v p fuel).1 := by
  letI : Differential K[X] := ⟨Differential.implicitDeriv v⟩
  intro fuel
  induction fuel with
  | zero =>
    intro p hp
    rw [Nat.le_zero, Polynomial.natDegree_eq_zero] at hp
    obtain ⟨c, rfl⟩ := hp
    have hdeg0 : (splitFactorStep v (C c)).natDegree = 0 := by
      rcases eq_or_ne c 0 with rfl | hc
      · simp only [map_zero, splitFactorStep, map_zero, gcd_zero_left,
          EuclideanDomain.div_zero, natDegree_zero]
      · have hCcu : IsUnit (C c) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
        have hnum : IsUnit (gcd (C c) (Differential.implicitDeriv v (C c))) :=
          isUnit_of_dvd_unit (gcd_dvd_left _ _) hCcu
        have hden : IsUnit (gcd (C c) (derivative (C c))) :=
          isUnit_of_dvd_unit (gcd_dvd_left _ _) hCcu
        have hSu : IsUnit (splitFactorStep v (C c)) :=
          isUnit_of_dvd_unit (EuclideanDomain.div_dvd_of_dvd hden.dvd) hnum
        exact Polynomial.natDegree_eq_zero_of_isUnit hSu
    have hnorm : IsNormal (C c) := (hstep (C c)).1 hdeg0
    simp only [splitFactorAux]
    exact ⟨(one_mul (C c)).symm, isSpecial_one, hnorm⟩
  | succ n ih =>
    intro p hp
    rw [splitFactorAux]
    simp only
    set S := splitFactorStep v p with hS
    by_cases hdeg : S.natDegree = 0
    · rw [if_pos hdeg]
      exact ⟨(one_mul p).symm, isSpecial_one, (hstep p).1 hdeg⟩
    · rw [if_neg hdeg]
      have hSpos : 0 < S.natDegree := Nat.pos_of_ne_zero hdeg
      obtain ⟨hSdvd, hdrop, hSspec⟩ := (hstep p).2 hSpos
      rw [← hS] at hdrop hSdvd hSspec
      have hSne : S ≠ 0 := fun h => hdeg (by rw [h]; simp)
      have hpS : (p / S).natDegree ≤ n := by omega
      obtain ⟨heq, hq2spec, hq1norm⟩ := ih (p / S) hpS
      refine ⟨?_, hSspec.mul hq2spec, hq1norm⟩
      rw [mul_assoc, ← heq, EuclideanDomain.mul_div_cancel' hSne hSdvd]

open Classical in
/-- `splitFactor` correctness: under the one-step property `IsSplitFactorStep`
holding at every polynomial, `splitFactor v p = (pₙ, pₛ)` is a splitting
factorization of `p` w.r.t. `D` (`Dt = v`) — `p = pₛ·pₙ`, `pₛ` special, `pₙ` normal. -/
theorem splitFactor_isSplittingFactorization (v p : K[X])
    (hstep : ∀ q : K[X], IsSplitFactorStep v q) :
    @IsSplittingFactorization _ _ ⟨Differential.implicitDeriv v⟩ p
      (splitFactor v p).2 (splitFactor v p).1 :=
  splitFactorAux_isSplittingFactorization v hstep p.natDegree p le_rfl

end SplitFactor

section SplitFactorSplit
variable {K : Type*} [Field K] [CharZero K] [Differential K]

open Classical in
/-- For a fully-split `q = ∏_{a∈s}(X − a)^{eₐ}` (char `0`), the step `S` is the squarefree special
part `S ~ ∏_{a : v(a)=a′}(X − a)`. -/
theorem splitFactorStep_prod_X_sub_C_pow_associated (v : K[X]) (s : Finset K) (e : K → ℕ)
    (he : ∀ a ∈ s, 1 ≤ e a) :
    Associated (splitFactorStep v (∏ a ∈ s, (X - C a) ^ e a))
      (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a)) := by
  set q := ∏ a ∈ s, (X - C a) ^ e a with hq
  have hform := gcd_implicitDeriv_associated_gcd_derivative_mul_special v s e he
  rw [← hq] at hform
  have hgne : gcd q (derivative q) ≠ 0 := by
    refine fun h => ?_
    have hq0 : q = 0 := eq_zero_of_zero_dvd (h ▸ gcd_dvd_left q (derivative q))
    rw [hq, Finset.prod_eq_zero_iff] at hq0
    obtain ⟨a, _, ha⟩ := hq0
    exact (pow_ne_zero _ (X_sub_C_ne_zero a)) ha
  -- `gcd(q,dq/dt) ∣ gcd(q,Dq)` from the associated product formula.
  have hdvd : gcd q (derivative q) ∣ gcd q (Differential.implicitDeriv v q) :=
    (dvd_mul_right _ _).trans hform.symm.dvd
  rw [splitFactorStep]
  -- divide both sides of the associated formula by `gcd(q,dq/dt)`.
  exact (associated_div_iff hgne hdvd).mpr hform

open Classical in
/-- For a squarefree fully-split `q = ∏_{a∈s}(X − a)`, the `splitFactor` step `S` is the special
part `∏_{a : v(a)=a′}(X − a)`; specializes `splitFactorStep_prod_X_sub_C_pow_associated` at `eₐ=1`. -/
theorem splitFactorStep_prod_X_sub_C_associated (v : K[X]) (s : Finset K) :
    Associated (splitFactorStep v (∏ a ∈ s, (X - C a)))
      (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a)) := by
  have h := splitFactorStep_prod_X_sub_C_pow_associated v s (fun _ => 1) (fun _ _ => le_rfl)
  simpa using h

open Classical in
/-- The one-step property `IsSplitFactorStep` holds for every squarefree fully-split
`q = ∏_{a∈s}(X − a)`. -/
theorem isSplitFactorStep_prod_X_sub_C (v : K[X]) (s : Finset K) :
    IsSplitFactorStep v (∏ a ∈ s, (X - C a)) := by
  letI : Differential K[X] := ⟨Differential.implicitDeriv v⟩
  set q := ∏ a ∈ s, (X - C a) with hq
  set sp := ∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a) with hsp
  have hassoc : Associated (splitFactorStep v q) sp := splitFactorStep_prod_X_sub_C_associated v s
  have hqne : q ≠ 0 := by
    rw [hq, Finset.prod_ne_zero_iff]; exact fun a _ => X_sub_C_ne_zero a
  -- `q` factors as `sp · (normal part)`.
  have hsplit := splittingFactorization_prod_X_sub_C v s
  rw [← hq, ← hsp] at hsplit
  obtain ⟨hqeq, hspspec, hnpnorm⟩ := hsplit
  set np := ∏ a ∈ s.filter (fun a => ¬ v.eval a = a′), (X - C a) with hnp
  have hspne : sp ≠ 0 := by
    rw [hsp, Finset.prod_ne_zero_iff]; exact fun a _ => X_sub_C_ne_zero a
  refine ⟨fun hdeg0 => ?_, fun hpos => ?_⟩
  · -- `S` constant ⟹ `sp` constant (associated) ⟹ `sp` is a unit ⟹ `q ~ np` normal.
    have hSne0 : splitFactorStep v q ≠ 0 := fun h => hspne (hassoc.eq_zero_iff.mp h)
    have hspdeg : sp.natDegree = 0 :=
      Nat.le_zero.mp (hdeg0 ▸ natDegree_le_of_dvd hassoc.symm.dvd hSne0)
    have hspc0 : sp.coeff 0 ≠ 0 := fun h => hspne (by rw [eq_C_of_natDegree_eq_zero hspdeg, h, map_zero])
    have hspu : IsUnit sp := by
      rw [eq_C_of_natDegree_eq_zero hspdeg]; exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr hspc0)
    have hnormal : IsNormal np := (isCoprime_prod_X_sub_C_implicitDeriv_iff v _).mpr
      (fun a ha => (Finset.mem_filter.mp ha).2)
    rw [hqeq]; exact (IsNormal.unit_mul_iff hspu np).mpr hnormal
  · -- `S` non-constant ⟹ `S ∣ q`, `IsSpecial S`, and degree of `q/S` drops.
    have hspdvdq : sp ∣ q := hqeq ▸ dvd_mul_right sp np
    have hSdvd : splitFactorStep v q ∣ q := hassoc.dvd.trans hspdvdq
    have hSspec : IsSpecial (splitFactorStep v q) := IsSpecial.of_associated hassoc.symm hspspec
    have hSne : splitFactorStep v q ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
    refine ⟨hSdvd, ?_, hSspec⟩
    -- degree drop: `(q/S).natDegree + S.natDegree = q.natDegree`.
    have hmul : splitFactorStep v q * (q / splitFactorStep v q) = q :=
      EuclideanDomain.mul_div_cancel' hSne hSdvd
    have hdeg : (splitFactorStep v q).natDegree + (q / splitFactorStep v q).natDegree
        = q.natDegree := by
      rw [← natDegree_mul hSne (fun h => hqne (by rw [← hmul, h, mul_zero])), hmul]
    omega

end SplitFactorSplit

section GeneralSplitFactorStep
variable {K : Type*} [Field K] [CharZero K] [Differential K]

open UniqueFactorizationMonoid

open Classical in
/-- For general `p` (char `0`), the step `S = gcd(p, Dp)/gcd(p, dp/dt)` is associated to the
squarefree product of the special prime factors of `p`: `S ~ ∏_{π : π ∣ Dπ} π`. -/
theorem splitFactorStep_associated_prod_special (v : K[X]) {p : K[X]} (hp : p ≠ 0) :
    Associated (splitFactorStep v p)
      (∏ π ∈ (primeFactors p).filter
        (fun π => @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ π), π) := by
  have hunit := fun π (hπ : π ∈ primeFactors p) => isUnit_natCast_count_primeFactors hπ
  -- numerator: gcd(p, Dp) under D = implicitDeriv v.
  have hnum : Associated (gcd p (Differential.implicitDeriv v p))
      ((∏ π ∈ primeFactors p, π ^ ((normalizedFactors p).count π - 1))
        * ∏ π ∈ (primeFactors p).filter
            (fun π => @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ π), π) :=
    @associated_gcd_deriv_special_part K _ ⟨Differential.implicitDeriv v⟩ p hp hunit
  -- denominator: gcd(p, dp/dt) under D = derivative; the special filter is empty.
  letI : Differential K[X] := ⟨(Polynomial.derivative' (R := K)).restrictScalars ℤ⟩
  have hfilt : (primeFactors p).filter
      (fun π => @IsSpecial _ _ ⟨(Polynomial.derivative' (R := K)).restrictScalars ℤ⟩ π) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro π hπ
    have hirr : Irreducible π := irreducible_of_normalized_factor π (mem_primeFactors.mp hπ)
    exact not_isSpecial_derivative_of_irreducible hirr
  have hden : Associated (gcd p (derivative p))
      (∏ π ∈ primeFactors p, π ^ ((normalizedFactors p).count π - 1)) := by
    have h := @associated_gcd_deriv_special_part K _
      ⟨(Polynomial.derivative' (R := K)).restrictScalars ℤ⟩ p hp hunit
    rw [hfilt, Finset.prod_empty, mul_one] at h
    -- under this instance, `p′ = derivative p`.
    exact h
  set defect := ∏ π ∈ primeFactors p, π ^ ((normalizedFactors p).count π - 1) with hdefect
  set special := ∏ π ∈ (primeFactors p).filter
    (fun π => @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ π), π with hspecial
  -- `gcd(p, dp/dt) ≠ 0` and `gcd(p, dp/dt) ∣ gcd(p, Dp)`.
  have hYne : gcd p (derivative p) ≠ 0 := fun h => hp (eq_zero_of_zero_dvd (h ▸ gcd_dvd_left _ _))
  have hYdvdX : gcd p (derivative p) ∣ gcd p (Differential.implicitDeriv v p) := by
    refine (hden.dvd).trans ?_
    exact (dvd_mul_right defect special).trans hnum.symm.dvd
  rw [splitFactorStep, associated_div_iff hYne hYdvdX]
  -- `gcd(p, Dp) ~ defect·special ~ gcd(p, dp/dt)·special`.
  exact hnum.trans (hden.symm.mul_right special)

open Classical in
omit [CharZero K] in
/-- If every prime factor of `p` is normal (w.r.t. `D`), then `p` is `IsNormalSqfree`. -/
theorem isNormalSqfree_of_forall_prime_normal (v : K[X]) {p : K[X]}
    (h : ∀ π : K[X], Prime π → π ∣ p → @IsNormal _ _ ⟨Differential.implicitDeriv v⟩ π) :
    @IsNormalSqfree _ _ ⟨Differential.implicitDeriv v⟩ p := by
  letI : Differential K[X] := ⟨Differential.implicitDeriv v⟩
  intro q hsf hqp
  have hq0 : q ≠ 0 := hsf.ne_zero
  -- `q ~ ∏ π ∈ primeFactors q, π` (q squarefree ⇒ radical).
  have hrad : Associated (∏ π ∈ primeFactors q, π) q := by
    have hAssoc : Associated (radical q) q :=
      radical_associated ((isRadical_iff_squarefree_of_ne_zero hq0).mpr hsf) hq0
    rwa [radical] at hAssoc
  refine IsNormal.of_associated hrad ?_
  refine IsNormal.prod (primeFactors q) (fun π => π) (fun π hπ => ?_) (fun π hπ ρ hρ hπρ => ?_)
  · -- each prime factor of q is normal: it is prime and divides q ∣ p.
    have hprime : Prime π := prime_of_normalized_factor π (mem_primeFactors.mp hπ)
    have hdvd : π ∣ p := (dvd_of_mem_normalizedFactors (mem_primeFactors.mp hπ)).trans hqp
    exact h π hprime hdvd
  · exact (((pairwise_primeFactors_isRelPrime (a := q)) hπ hρ hπρ)).isCoprime

open Classical in
/-- If the `splitFactor` step `S` is constant (`deg S = 0`), then `p` is `IsNormalSqfree`. -/
theorem isNormalSqfree_of_splitFactorStep_natDegree_zero (v : K[X]) {p : K[X]} (hp : p ≠ 0)
    (hdeg : (splitFactorStep v p).natDegree = 0) :
    @IsNormalSqfree _ _ ⟨Differential.implicitDeriv v⟩ p := by
  letI : Differential K[X] := ⟨Differential.implicitDeriv v⟩
  have hassoc := splitFactorStep_associated_prod_special v hp
  -- `S` is a nonzero constant, hence a unit; so `∏_{special}π` is a unit.
  have hspne : (∏ π ∈ (primeFactors p).filter
      (fun π => @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ π), π) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    exact fun π hπ => (prime_of_normalized_factor π
      (mem_primeFactors.mp (Finset.mem_of_mem_filter π hπ))).ne_zero
  have hSne : splitFactorStep v p ≠ 0 := fun hS => hspne (hassoc.eq_zero_iff.mp hS)
  have hSu : IsUnit (splitFactorStep v p) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hSne, hdeg]; rfl
  have hspu : IsUnit (∏ π ∈ (primeFactors p).filter
      (fun π => @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ π), π) :=
    hassoc.isUnit hSu
  -- a unit product of primes forces an empty filter: no special prime factor.
  have hnospec : ∀ π ∈ primeFactors p, ¬ @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ π := by
    intro π hπ hπspec
    have hmem : π ∈ (primeFactors p).filter
        (fun π => @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ π) := Finset.mem_filter.mpr ⟨hπ, hπspec⟩
    have hπdvd : π ∣ ∏ ρ ∈ (primeFactors p).filter
        (fun ρ => @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ ρ), ρ := Finset.dvd_prod_of_mem _ hmem
    exact (prime_of_normalized_factor π (mem_primeFactors.mp hπ)).not_unit
      (isUnit_of_dvd_unit hπdvd hspu)
  -- every prime factor of `p` is normal.
  refine isNormalSqfree_of_forall_prime_normal v (fun π hprime hdvd => ?_)
  -- find a normalized associate `ρ ∈ primeFactors p`; `ρ` is not special, so neither is `π`.
  obtain ⟨ρ, hρmem, hρassoc⟩ := exists_mem_normalizedFactors_of_dvd hp hprime.irreducible hdvd
  have hρpf : ρ ∈ primeFactors p := mem_primeFactors.mpr hρmem
  have hρnospec : ¬ @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ ρ := hnospec ρ hρpf
  have hπnospec : ¬ @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ π :=
    fun hπs => hρnospec (IsSpecial.of_associated hρassoc hπs)
  have hgcdu : IsUnit (gcd π π′) :=
    hprime.irreducible.isUnit_gcd_iff.mpr (fun hd => hπnospec (hd : @IsSpecial _ _ _ π))
  exact (gcd_isUnit_iff_isRelPrime.mp hgcdu).isCoprime

open Classical in
/-- The `splitFactor` step `S` is always *special*: `S ~ ∏_{special}π`, a product of special primes,
hence special (`IsSpecial.prod`/`of_associated`). -/
theorem isSpecial_splitFactorStep (v : K[X]) {p : K[X]} (hp : p ≠ 0) :
    @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ (splitFactorStep v p) := by
  letI : Differential K[X] := ⟨Differential.implicitDeriv v⟩
  have hassoc := splitFactorStep_associated_prod_special v hp
  refine IsSpecial.of_associated hassoc.symm ?_
  refine IsSpecial.prod _ _ (fun π hπ => ?_)
  -- each special prime factor is special.
  exact (Finset.mem_filter.mp hπ).2

open Classical in
/-- The `splitFactor` step `S` divides `p`: `S ~ ∏_{special}π` and each special prime divides `p`. -/
theorem splitFactorStep_dvd (v : K[X]) {p : K[X]} (hp : p ≠ 0) :
    splitFactorStep v p ∣ p := by
  have hassoc := splitFactorStep_associated_prod_special v hp
  refine hassoc.dvd.trans (Finset.prod_dvd_of_isRelPrime ?_ ?_)
  · intro π hπ ρ hρ hπρ
    exact (pairwise_primeFactors_isRelPrime (a := p))
      (Finset.mem_of_mem_filter π hπ) (Finset.mem_of_mem_filter ρ hρ) hπρ
  · intro π hπ
    exact dvd_of_mem_normalizedFactors (mem_primeFactors.mp (Finset.mem_of_mem_filter π hπ))

open Classical in
/-- Hypothesis-free `splitFactorAux` correctness: for fuel `≥ deg p` and `p ≠ 0`, it returns a
general splitting factorization `(pₙ, pₛ)` — `p = pₛ·pₙ`, `pₛ` special, `pₙ` `IsNormalSqfree`. -/
theorem splitFactorAux_isSplittingFactorizationGen (v : K[X]) :
    ∀ (fuel : ℕ) (p : K[X]), p ≠ 0 → p.natDegree ≤ fuel →
      @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv v⟩ p
        (splitFactorAux v p fuel).2 (splitFactorAux v p fuel).1 := by
  letI : Differential K[X] := ⟨Differential.implicitDeriv v⟩
  intro fuel
  induction fuel with
  | zero =>
    intro p hp0 hp
    rw [Nat.le_zero, Polynomial.natDegree_eq_zero] at hp
    obtain ⟨c, rfl⟩ := hp
    have hc : c ≠ 0 := fun h => hp0 (by rw [h, map_zero])
    -- a nonzero constant `C c` is a unit, hence normal-squarefree.
    have hnorm : IsNormalSqfree (C c) :=
      (isNormal_of_isUnit (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc))).isNormalSqfree
    simp only [splitFactorAux]
    exact ⟨(one_mul (C c)).symm, isSpecial_one, hnorm⟩
  | succ n ih =>
    intro p hp0 hp
    rw [splitFactorAux]
    simp only
    set S := splitFactorStep v p with hS
    by_cases hdeg : S.natDegree = 0
    · rw [if_pos hdeg]
      exact ⟨(one_mul p).symm, isSpecial_one,
        isNormalSqfree_of_splitFactorStep_natDegree_zero v hp0 hdeg⟩
    · rw [if_neg hdeg]
      have hSpos : 0 < S.natDegree := Nat.pos_of_ne_zero hdeg
      have hSdvd : S ∣ p := splitFactorStep_dvd v hp0
      have hSspec : IsSpecial S := isSpecial_splitFactorStep v hp0
      have hSne : S ≠ 0 := fun h => hdeg (by rw [h]; simp)
      -- degree drop and `p / S ≠ 0`.
      have hmul : S * (p / S) = p := EuclideanDomain.mul_div_cancel' hSne hSdvd
      have hpSne : p / S ≠ 0 := fun h => hp0 (by rw [← hmul, h, mul_zero])
      have hdegsum : S.natDegree + (p / S).natDegree = p.natDegree := by
        rw [← natDegree_mul hSne hpSne, hmul]
      have hpS : (p / S).natDegree ≤ n := by omega
      obtain ⟨heq, hq2spec, hq1norm⟩ := ih (p / S) hpSne hpS
      refine ⟨?_, hSspec.mul hq2spec, hq1norm⟩
      rw [mul_assoc, ← heq, hmul]

open Classical in
/-- Hypothesis-free `splitFactor` correctness: for `p ≠ 0`,
`splitFactor v p = (pₙ, pₛ)` is a general splitting factorization — `p = pₛ·pₙ`, `pₛ` special,
every squarefree factor of `pₙ` normal. -/
theorem splitFactor_isSplittingFactorizationGen (v p : K[X]) (hp : p ≠ 0) :
    @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv v⟩ p
      (splitFactor v p).2 (splitFactor v p).1 :=
  splitFactorAux_isSplittingFactorizationGen v p.natDegree p hp le_rfl

end GeneralSplitFactorStep

end DeepWiki.SymbolicIntegration
