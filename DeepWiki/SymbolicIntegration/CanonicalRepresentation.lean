import DeepWiki.SymbolicIntegration.MonomialExtensions
import DeepWiki.SymbolicIntegration.SquarefreeFactorization
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Radical.Basic

/-! # The canonical representation
For a monomial extension `(k(t), D)` with `Dt = v`, the unique split `f = fₚ + fₛ + fₙ` of
`f ∈ k(t)` into polynomial, reduced (special-denominator), and simple (normal-denominator) parts.
Provides the classifying predicates `IsSimple`/`IsReduced`, the `splitFactor` denominator
splitting, its squarefree variant `splitSquarefreeFactor`, `canonicalRepresentation`, and the
root characterization of the split. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section Classify
variable {K : Type*} [Field K] [Differential K]

/-- `f ∈ k(t)` is *simple* w.r.t. the monomial derivation `D` (`Dt = v`) if its denominator is
normal — coprime to its `D`-derivative `D(denom f)`. -/
def IsSimple (v : K[X]) (f : RatFunc K) : Prop :=
  IsCoprime f.denom (Differential.implicitDeriv v f.denom)

/-- `f ∈ k(t)` is *reduced* w.r.t. the monomial derivation `D` (`Dt = v`) if its denominator is
special — it divides its `D`-derivative `D(denom f)`. The reduced elements form the subfield
`k⟨t⟩`. -/
def IsReduced (v : K[X]) (f : RatFunc K) : Prop :=
  f.denom ∣ Differential.implicitDeriv v f.denom

/-- `IsSimple` is exactly `IsNormal` of the denominator under the monomial derivation. -/
theorem isSimple_iff_isNormal_denom (v : K[X]) (f : RatFunc K) :
    IsSimple v f ↔ @IsNormal _ _ ⟨Differential.implicitDeriv v⟩ f.denom :=
  Iff.rfl

/-- `IsReduced` is exactly `IsSpecial` of the denominator under the monomial derivation. -/
theorem isReduced_iff_isSpecial_denom (v : K[X]) (f : RatFunc K) :
    IsReduced v f ↔ @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ f.denom :=
  Iff.rfl

/-- A polynomial `p ∈ k[t]` is simple: its denominator is `1`, which is normal. -/
theorem isSimple_algebraMap (v : K[X]) (p : K[X]) :
    IsSimple v (algebraMap K[X] (RatFunc K) p) := by
  rw [IsSimple, RatFunc.denom_algebraMap]
  exact (@isNormal_one _ _ ⟨Differential.implicitDeriv v⟩)

/-- A polynomial `p ∈ k[t]` is reduced: its denominator is `1`, which is special. -/
theorem isReduced_algebraMap (v : K[X]) (p : K[X]) :
    IsReduced v (algebraMap K[X] (RatFunc K) p) := by
  rw [IsReduced, RatFunc.denom_algebraMap]
  exact (@isSpecial_one _ _ ⟨Differential.implicitDeriv v⟩)

/-- `IsReduced` from a special denominator: if `denom f` divides its `D`-derivative, `f` is
reduced (the defining condition, stated as an intro rule). -/
theorem isReduced_of_dvd_implicitDeriv {v : K[X]} {f : RatFunc K}
    (h : f.denom ∣ Differential.implicitDeriv v f.denom) : IsReduced v f := h

/-- `IsSimple` from a normal denominator: if `denom f` is coprime to its `D`-derivative, `f` is
simple (the defining condition, stated as an intro rule). -/
theorem isSimple_of_isCoprime_implicitDeriv {v : K[X]} {f : RatFunc K}
    (h : IsCoprime f.denom (Differential.implicitDeriv v f.denom)) : IsSimple v f := h

/-- `0` is both simple and reduced (denominator `1`). -/
theorem isSimple_zero (v : K[X]) : IsSimple v (0 : RatFunc K) := by
  rw [IsSimple, RatFunc.denom_zero]
  exact (@isNormal_one _ _ ⟨Differential.implicitDeriv v⟩)

/-- `0` is reduced (denominator `1`). -/
theorem isReduced_zero (v : K[X]) : IsReduced v (0 : RatFunc K) := by
  rw [IsReduced, RatFunc.denom_zero]
  exact (@isSpecial_one _ _ ⟨Differential.implicitDeriv v⟩)

end Classify

section BookFaithfulNormal
variable {R : Type*} [CommRing R] [Differential R]

/-- `pn` has every squarefree factor normal. Strictly weaker than `IsNormal pn` (which forces
`pn` squarefree): a normal prime power `π²` satisfies `IsNormalSqfree` but not `IsNormal`. -/
def IsNormalSqfree (pn : R) : Prop := ∀ q : R, Squarefree q → q ∣ pn → IsNormal q

/-- General splitting factorization: `p = pₛ·pₙ` with `pₛ` special and every squarefree factor of
`pₙ` normal (weaker than `IsSplittingFactorization`, which demands `pₙ` itself `IsNormal`, hence
squarefree). -/
def IsSplittingFactorizationGen (p ps pn : R) : Prop :=
  p = ps * pn ∧ IsSpecial ps ∧ IsNormalSqfree pn

/-- `IsNormal pn` implies `IsNormalSqfree pn`: squarefree factors of a normal polynomial are
normal (`IsNormal.of_dvd`). -/
theorem IsNormal.isNormalSqfree {pn : R} (h : IsNormal pn) : IsNormalSqfree pn :=
  fun _ _ hq => h.of_dvd hq

/-- An `IsSplittingFactorization` is an `IsSplittingFactorizationGen`. -/
theorem IsSplittingFactorization.toGen {p ps pn : R}
    (h : IsSplittingFactorization p ps pn) : IsSplittingFactorizationGen p ps pn :=
  ⟨h.1, h.2.1, h.2.2.isNormalSqfree⟩

/-- On a *squarefree* `pn` the two normality notions agree: `IsNormalSqfree pn ↔ IsNormal pn`
(a squarefree polynomial is its own squarefree factor). -/
theorem isNormalSqfree_iff_isNormal_of_squarefree {pn : R} (hsf : Squarefree pn) :
    IsNormalSqfree pn ↔ IsNormal pn :=
  ⟨fun h => h pn hsf dvd_rfl, IsNormal.isNormalSqfree⟩

end BookFaithfulNormal

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
    -- `splitFactorStep v (C c)` has degree 0 (a constant's gcds are constants), so `C c` is normal.
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

section GeneralSplitFactor
variable {K : Type*} [Field K] [Differential K]

open UniqueFactorizationMonoid

open Classical in
omit [Differential K] in
/-- Prime-power decomposition of a nonzero polynomial: `p ~ ∏_{π ∈ primeFactors p} π^{m_π}` with
`m_π = count π (normalizedFactors p)`. -/
theorem associated_prod_primeFactors_pow {p : K[X]} (hp : p ≠ 0) :
    Associated p (∏ π ∈ primeFactors p, π ^ (normalizedFactors p).count π) := by
  have h1 : Associated (normalizedFactors p).prod p := prod_normalizedFactors hp
  rw [Finset.prod_multiset_count] at h1
  have hpf : primeFactors p = (normalizedFactors p).toFinset := by
    rw [primeFactors]; congr 1; exact Subsingleton.elim _ _
  rw [hpf]
  exact h1.symm

end GeneralSplitFactor

section GcdDerivAssoc
variable {R : Type*} [CommRing R] [NormalizedGCDMonoid R] [Differential R]

/-- gcd-with-derivative is an associate invariant: `Associated p q → gcd(p, Dp) ~ gcd(q, Dq)`. -/
theorem associated_gcd_deriv_of_associated {p q : R} (h : Associated p q) :
    Associated (gcd p p′) (gcd q q′) := by
  obtain ⟨u, rfl⟩ := h
  have hugcd : IsUnit (gcd p (u : R)) := isUnit_of_dvd_unit (gcd_dvd_right _ _) u.isUnit
  have hbase := associated_gcd_deriv_mul (a := p) (b := (u : R)) hugcd
  have huu : IsUnit (gcd (u : R) ((u : R)′)) :=
    isUnit_of_dvd_unit (gcd_dvd_left _ _) u.isUnit
  refine (hbase.trans ?_).symm
  exact (associated_mul_unit_right _ _ huu).symm

end GcdDerivAssoc

section GeneralGcdFormula
variable {K : Type*} [Field K] [Differential K[X]]

open UniqueFactorizationMonoid

open Classical in
/-- gcd-with-derivative over arbitrary irreducibles: for `p ≠ 0` with every multiplicity a unit
(char `0`), `gcd(p, Dp) ~ (∏_π π^{m_π−1})·∏_π gcd(π, Dπ)`. -/
theorem associated_gcd_deriv_prod_primeFactors {p : K[X]} (hp : p ≠ 0)
    (hunit : ∀ π ∈ primeFactors p, IsUnit (((normalizedFactors p).count π : ℕ) : K[X])) :
    Associated (gcd p p′)
      ((∏ π ∈ primeFactors p, π ^ ((normalizedFactors p).count π - 1))
        * ∏ π ∈ primeFactors p, gcd π π′) := by
  set m : K[X] → ℕ := fun π => (normalizedFactors p).count π with hm
  -- bridge `gcd p (Dp)` to the decomposition.
  have hbridge := associated_gcd_deriv_of_associated (associated_prod_primeFactors_pow hp)
  refine hbridge.trans ?_
  -- pairwise coprimality of distinct prime powers.
  have hco : ∀ π ∈ primeFactors p, ∀ ρ ∈ primeFactors p, π ≠ ρ →
      IsUnit (gcd (π ^ m π) (ρ ^ m ρ)) := by
    intro π hπ ρ hρ hπρ
    refine gcd_isUnit_iff_isRelPrime.mpr ?_
    exact ((pairwise_primeFactors_isRelPrime (a := p)) hπ hρ hπρ).pow
  -- split over the prime powers, then compute each power.
  refine (associated_gcd_deriv_prod (primeFactors p) (fun π => π ^ m π) hco).trans ?_
  have heach : Associated (∏ π ∈ primeFactors p, gcd (π ^ m π) ((π ^ m π)′))
      (∏ π ∈ primeFactors p, π ^ (m π - 1) * gcd π π′) := by
    refine Associated.prod (primeFactors p) _ _ (fun π hπ => ?_)
    rcases Nat.eq_zero_or_pos (m π) with hm0 | hmpos
    · exfalso
      have hmem : π ∈ normalizedFactors p := mem_primeFactors.mp hπ
      have hcount : 0 < (normalizedFactors p).count π := Multiset.count_pos.mpr hmem
      simp only [hm] at hm0; omega
    · exact associated_gcd_deriv_pow hmpos (hunit π hπ)
  refine heach.trans ?_
  rw [Finset.prod_mul_distrib]

open Classical in
/-- Per-prime gcd collapse: `∏_π gcd(π, Dπ) ~ ∏_{π special} π` over the prime factors of `p`. -/
theorem associated_prod_gcd_deriv_primeFactors {p : K[X]} :
    Associated (∏ π ∈ primeFactors p, gcd π π′)
      (∏ π ∈ (primeFactors p).filter (fun π => @IsSpecial _ _ ⟨(Differential.deriv : _)⟩ π), π) := by
  rw [Finset.prod_filter]
  refine Associated.prod (primeFactors p) _ _ (fun π hπ => ?_)
  have hirr : Irreducible π := irreducible_of_normalized_factor π (mem_primeFactors.mp hπ)
  by_cases h : @IsSpecial _ _ ⟨(Differential.deriv : _)⟩ π
  · rw [if_pos h]
    exact (associated_gcd_left_iff.mpr (h : π ∣ π′)).symm
  · rw [if_neg h]
    exact associated_one_iff_isUnit.mpr (hirr.isUnit_gcd_iff.mpr (h : ¬ π ∣ π′))

open Classical in
/-- General gcd formula over arbitrary irreducibles: for `p ≠ 0` with every multiplicity a unit
(char `0`), `gcd(p, Dp) ~ (∏_π π^{m_π−1})·∏_{π special} π`. -/
theorem associated_gcd_deriv_special_part {p : K[X]} (hp : p ≠ 0)
    (hunit : ∀ π ∈ primeFactors p, IsUnit (((normalizedFactors p).count π : ℕ) : K[X])) :
    Associated (gcd p p′)
      ((∏ π ∈ primeFactors p, π ^ ((normalizedFactors p).count π - 1))
        * ∏ π ∈ (primeFactors p).filter (fun π => @IsSpecial _ _ ⟨(Differential.deriv : _)⟩ π), π) :=
  (associated_gcd_deriv_prod_primeFactors hp hunit).trans
    (Associated.mul_left _ associated_prod_gcd_deriv_primeFactors)

end GeneralGcdFormula

section GeneralGcdFormulaCharZero
variable {K : Type*} [Field K] [CharZero K]

open UniqueFactorizationMonoid

open Classical in
/-- In characteristic `0`, a positive prime-factor multiplicity is a unit in `K[X]`. -/
theorem isUnit_natCast_count_primeFactors {p : K[X]} {π : K[X]}
    (hπ : π ∈ primeFactors p) :
    IsUnit (((normalizedFactors p).count π : ℕ) : K[X]) := by
  have hcount : 0 < (normalizedFactors p).count π := Multiset.count_pos.mpr (mem_primeFactors.mp hπ)
  rw [← map_natCast (C : K →+* K[X])]
  exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))

/-- In characteristic `0`, no irreducible polynomial is special under `d/dt`: `π ∤ dπ/dt`. -/
theorem not_isSpecial_derivative_of_irreducible {π : K[X]} (hπ : Irreducible π) :
    ¬ π ∣ derivative π := by
  intro hdvd
  exact hπ.not_isUnit (hπ.separable.isUnit_of_dvd' dvd_rfl hdvd)

end GeneralGcdFormulaCharZero

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
    -- a nonzero constant `C c` is a unit, hence book-normal.
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

section SplitSquarefreeFactor
variable {K : Type*} [Field K] [Differential K]

open Classical in
/-- The special part `S = gcd(p, Dp)` of a squarefree `p` (`Dt = v`). Since `p` is squarefree
(`gcd(p, dp/dt) = 1`), the `splitFactor` step's denominator is trivial and `gcd(p, Dp)` is the
whole special part. -/
noncomputable def squarefreeSpecialPart (v p : K[X]) : K[X] :=
  gcd p (Differential.implicitDeriv v p)

open Classical in
/-- The normal part of a squarefree `p`: `N = p / gcd(p, Dp)`. -/
noncomputable def squarefreeNormalPart (v p : K[X]) : K[X] :=
  p / gcd p (Differential.implicitDeriv v p)

open Classical in
/-- The normal/special split of one squarefree factor: `(N, S)` with `N` the normal part
`p/gcd(p,Dp)` and `S = gcd(p,Dp)` the special part. -/
noncomputable def splitSquarefreeFactor (v p : K[X]) : K[X] × K[X] :=
  (squarefreeNormalPart v p, squarefreeSpecialPart v p)

end SplitSquarefreeFactor

section SplitSquarefreeFactorSplit
variable {K : Type*} [Field K] [CharZero K] [Differential K]

open Classical in
omit [CharZero K] in
/-- For a squarefree fully-split `p = ∏_{a∈s}(X − a)`, the special part `gcd(p, Dp)` is exactly the
special factor `∏_{a : v(a)=a′}(X − a)`. -/
theorem squarefreeSpecialPart_prod_X_sub_C_associated (v : K[X]) (s : Finset K) :
    Associated (squarefreeSpecialPart v (∏ a ∈ s, (X - C a)))
      (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a)) :=
  gcd_prod_X_sub_C_implicitDeriv v s

open Classical in
omit [CharZero K] in
/-- `splitSquarefreeFactor` correctness on one squarefree factor: for a squarefree
fully-split `p = ∏_{a∈s}(X − a)`, `splitSquarefreeFactor v p = (N, S)` is a splitting factorization
of `p` (`p = S·N`, `S` special, `N` normal) with both `N, S` squarefree and coprime. -/
theorem splitSquarefreeFactor_prod_X_sub_C (v : K[X]) (s : Finset K) :
    @IsSplittingFactorization _ _ ⟨Differential.implicitDeriv v⟩
        (∏ a ∈ s, (X - C a))
        (splitSquarefreeFactor v (∏ a ∈ s, (X - C a))).2
        (splitSquarefreeFactor v (∏ a ∈ s, (X - C a))).1
      ∧ Squarefree (splitSquarefreeFactor v (∏ a ∈ s, (X - C a))).1
      ∧ Squarefree (splitSquarefreeFactor v (∏ a ∈ s, (X - C a))).2
      ∧ IsCoprime (splitSquarefreeFactor v (∏ a ∈ s, (X - C a))).1
          (splitSquarefreeFactor v (∏ a ∈ s, (X - C a))).2 := by
  letI : Differential K[X] := ⟨Differential.implicitDeriv v⟩
  set p := ∏ a ∈ s, (X - C a) with hp
  set S := squarefreeSpecialPart v p with hS
  set sp := ∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a) with hsp
  set np := ∏ a ∈ s.filter (fun a => ¬ v.eval a = a′), (X - C a) with hnp
  have hSassoc : Associated S sp := squarefreeSpecialPart_prod_X_sub_C_associated v s
  have hsplit := splittingFactorization_prod_X_sub_C v s
  rw [← hp, ← hsp, ← hnp] at hsplit
  obtain ⟨hpeq, hspspec, hnpcop⟩ := hsplit
  have hSne : S ≠ 0 := by
    rw [hS, squarefreeSpecialPart]
    exact fun h => by
      have : p = 0 := eq_zero_of_zero_dvd (h ▸ gcd_dvd_left p _)
      rw [hp, Finset.prod_eq_zero_iff] at this
      obtain ⟨a, _, ha⟩ := this; exact X_sub_C_ne_zero a ha
  have hSdvdp : S ∣ p := gcd_dvd_left _ _
  -- `N = p/S`, and `S · N = p`.
  have hNval : squarefreeNormalPart v p = p / S := rfl
  have hmul : S * squarefreeNormalPart v p = p := by
    rw [hNval, EuclideanDomain.mul_div_cancel' hSne hSdvdp]
  -- splitting factorization: `p = S · N`, S special, N normal.
  have hSspec : IsSpecial S := IsSpecial.of_associated hSassoc.symm hspspec
  have hNassoc : Associated (squarefreeNormalPart v p) np := by
    have : Associated (S * squarefreeNormalPart v p) (sp * np) := by rw [hmul, hpeq]
    exact (Associated.of_mul_left this hSassoc hSne)
  have hNnorm : IsNormal (squarefreeNormalPart v p) :=
    IsNormal.of_associated hNassoc.symm
      ((isCoprime_prod_X_sub_C_implicitDeriv_iff v _).mpr
        (fun a ha => (Finset.mem_filter.mp ha).2))
  refine ⟨⟨(hmul.symm), hSspec, hNnorm⟩, ?_, ?_, ?_⟩
  · -- N squarefree (associated to a squarefree product of distinct linear factors).
    exact hNassoc.squarefree_iff.mpr (squarefree_prod_X_sub_C _)
  · -- S squarefree.
    exact hSassoc.squarefree_iff.mpr (squarefree_prod_X_sub_C _)
  · -- N, S coprime (associated to the coprime normal/special parts).
    exact ((isCoprime_splitting_parts v s).symm.of_isCoprime_of_dvd_left hNassoc.dvd).of_isCoprime_of_dvd_right hSassoc.dvd

end SplitSquarefreeFactorSplit

section CanonicalRep
variable {K : Type*} [Field K] [Differential K]

/-- The Bézout split of `r` over coprime `dₙ, dₛ` given `u·dₙ + w·dₛ = 1`: returns `(b, c)` solving
`b·dₙ + c·dₛ = r` with `deg b < deg dₛ` (`b = (u·r) %ₘ dₛ`, `c = w·r + (u·r /ₘ dₛ)·dₙ`). -/
noncomputable def extendedEuclideanSplit (dn ds r u w : K[X]) : K[X] × K[X] :=
  ((u * r) %ₘ ds, w * r + (u * r /ₘ ds) * dn)

omit [Differential K] in
/-- The Bézout split solves `b·dₙ + c·dₛ = r` whenever `u·dₙ + w·dₛ = 1`. -/
theorem extendedEuclideanSplit_spec (dn ds r u w : K[X])
    (hbez : u * dn + w * ds = 1) :
    (extendedEuclideanSplit dn ds r u w).1 * dn
        + (extendedEuclideanSplit dn ds r u w).2 * ds = r := by
  simp only [extendedEuclideanSplit]
  have hmod : (u * r) %ₘ ds = u * r - ds * (u * r /ₘ ds) := by
    have := modByMonic_add_div (u * r) ds
    linear_combination this
  rw [hmod]
  have hr : (u * dn + w * ds) * r = r := by rw [hbez, one_mul]
  linear_combination hr

omit [Differential K] in
/-- The `b` part of the Bézout split has degree `< deg dₛ` (`b = (u·r) %ₘ dₛ`, a remainder modulo
the monic `dₛ`). -/
theorem extendedEuclideanSplit_degree_lt (dn ds r u w : K[X]) (hds : ds.Monic) :
    (extendedEuclideanSplit dn ds r u w).1.degree < ds.degree := by
  simp only [extendedEuclideanSplit]
  exact degree_modByMonic_lt (u * r) hds

open Classical in
/-- A Bézout pair `(u, w)` with `u·a + w·b = 1` for coprime `a, b`; `(0, 0)` otherwise. -/
noncomputable def bezoutOne (a b : K[X]) : K[X] × K[X] :=
  if h : IsCoprime a b then (h.choose, h.choose_spec.choose) else (0, 0)

omit [Differential K] in
/-- `bezoutOne a b` solves `u·a + w·b = 1` when `a, b` are coprime. -/
theorem bezoutOne_spec {a b : K[X]} (h : IsCoprime a b) :
    (bezoutOne a b).1 * a + (bezoutOne a b).2 * b = 1 := by
  rw [bezoutOne, dif_pos h]
  exact h.choose_spec.choose_spec

open Classical in
/-- The canonical representation of `f ∈ k(t)` as `(q, b/dₛ, c/dₙ)` — polynomial, reduced, and
simple parts — from the polynomial division `num f = q·d + r`, the denominator split
`(dₙ, dₛ) = splitFactor v d`, and the Bézout split `(b, c)` of `r`. -/
noncomputable def canonicalRepresentation (v : K[X]) (f : RatFunc K) :
    K[X] × RatFunc K × RatFunc K :=
  let a := f.num
  let d := f.denom
  let q := a /ₘ d
  let r := a %ₘ d
  let dn := (splitFactor v d).1
  let ds := (splitFactor v d).2
  let uw := bezoutOne dn ds
  let bc := extendedEuclideanSplit dn ds r uw.1 uw.2
  (q, algebraMap K[X] (RatFunc K) bc.1 / algebraMap K[X] (RatFunc K) ds,
      algebraMap K[X] (RatFunc K) bc.2 / algebraMap K[X] (RatFunc K) dn)

omit [Differential K] in
open Classical in
/-- `canonicalRepresentation` correctness (additive form): given `denom f = dₛ·dₙ` and a Bézout
pair `u·dₙ + w·dₛ = 1`, the canonical pieces sum back to `f = q + b/dₛ + c/dₙ`. -/
theorem canonicalRepresentation_add_eq (f : RatFunc K)
    {dn ds u w : K[X]} (hsplit : f.denom = ds * dn)
    (hdn : dn ≠ 0) (hds : ds ≠ 0) (hbez : u * dn + w * ds = 1) :
    (algebraMap K[X] (RatFunc K) (f.num /ₘ f.denom))
        + algebraMap K[X] (RatFunc K) (extendedEuclideanSplit dn ds (f.num %ₘ f.denom) u w).1
            / algebraMap K[X] (RatFunc K) ds
        + algebraMap K[X] (RatFunc K) (extendedEuclideanSplit dn ds (f.num %ₘ f.denom) u w).2
            / algebraMap K[X] (RatFunc K) dn
      = f := by
  set A := algebraMap K[X] (RatFunc K) with hA
  set d := f.denom with hd
  set a := f.num with ha
  set r := a %ₘ d with hr
  set q := a /ₘ d with hq
  set b := (extendedEuclideanSplit dn ds r u w).1 with hb
  set c := (extendedEuclideanSplit dn ds r u w).2 with hc
  have hbcr : b * dn + c * ds = r := extendedEuclideanSplit_spec dn ds r u w hbez
  have hdne : d ≠ 0 := RatFunc.denom_ne_zero f
  have hAdn : A dn ≠ 0 := by rw [hA]; exact (RatFunc.algebraMap_ne_zero hdn)
  have hAds : A ds ≠ 0 := by rw [hA]; exact (RatFunc.algebraMap_ne_zero hds)
  have hAd : A d ≠ 0 := by rw [hA]; exact (RatFunc.algebraMap_ne_zero hdne)
  -- `f = A a / A d`
  have hf : f = A a / A d := by rw [hA, hd, ha, RatFunc.num_div_denom]
  -- `a = q * d + r` from `modByMonic_add_div` (d monic)
  have hadiv : a = q * d + r := by
    have := modByMonic_add_div a d
    rw [← hr, ← hq] at this; linear_combination -this
  -- combine into the field identity
  rw [hf, hadiv, hsplit]
  rw [map_add, map_mul]
  have hAdsdn : A (ds * dn) = A ds * A dn := map_mul A ds dn
  rw [hAdsdn]
  -- now everything is over A ds, A dn; clear denominators
  field_simp
  -- goal is a polynomial identity in RatFunc; reduce to the Bézout identity
  rw [← hbcr]
  push_cast [hA]
  ring

open Classical in
/-- `canonicalRepresentation` correctness: the three pieces `(q, fₛ, fₙ)` sum to `f`, given that
the `splitFactor` output splits the denominator (`denom f = dₛ·dₙ`) and is coprime. -/
theorem canonicalRepresentation_sum_eq (v : K[X]) (f : RatFunc K)
    (hsplit : f.denom = (splitFactor v f.denom).2 * (splitFactor v f.denom).1)
    (hcop : IsCoprime (splitFactor v f.denom).1 (splitFactor v f.denom).2)
    (hdn : (splitFactor v f.denom).1 ≠ 0) (hds : (splitFactor v f.denom).2 ≠ 0) :
    algebraMap K[X] (RatFunc K) (canonicalRepresentation v f).1
        + (canonicalRepresentation v f).2.1 + (canonicalRepresentation v f).2.2 = f := by
  set dn := (splitFactor v f.denom).1 with hdndef
  set ds := (splitFactor v f.denom).2 with hdsdef
  have hbez := bezoutOne_spec hcop
  simp only [canonicalRepresentation, ← hdndef, ← hdsdef]
  exact canonicalRepresentation_add_eq f hsplit hdn hds hbez

end CanonicalRep

section RootCharacterization
variable {K : Type*} [Field K] [CharZero K] [Differential K]

open Classical in
/-- A root `α` of a special polynomial `pₛ` (w.r.t. the coefficient-lifting derivation, `Dt = 0`)
is a constant: `Dα = 0`. -/
theorem deriv_eq_zero_of_isSpecial_of_isRoot {ps : K[X]} (hps0 : ps ≠ 0)
    (hps : @IsSpecial _ _ ⟨Differential.implicitDeriv 0⟩ ps) {α : K} (hα : ps.IsRoot α) :
    α′ = 0 := by
  letI : Differential K[X] := ⟨Differential.implicitDeriv 0⟩
  have hdvd : (X - C α) ∣ ps := dvd_iff_isRoot.mpr hα
  have hprime : Prime (X - C α) := prime_X_sub_C α
  have hmult : IsUnit ((multiplicity (X - C α) ps : K[X])) := by
    rw [← map_natCast (C : K →+* K[X])]
    exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr
      (by have := multiplicity_pos_of_dvd hdvd; omega)))
  have hspX : IsSpecial (X - C α) := isSpecial_of_prime_dvd hprime hdvd hps0 hps hmult
  have := (dvd_X_sub_C_implicitDeriv_iff (0 : K[X]) α).mp hspX
  simpa using this.symm

omit [CharZero K] in
open Classical in
/-- A root `α` of a normal polynomial `pₙ` (w.r.t. the coefficient-lifting derivation, `Dt = 0`)
is nonconstant: `Dα ≠ 0`. -/
theorem deriv_ne_zero_of_isNormal_of_isRoot {pn : K[X]}
    (hpn : @IsNormal _ _ ⟨Differential.implicitDeriv 0⟩ pn) {α : K} (hα : pn.IsRoot α) :
    α′ ≠ 0 := by
  letI : Differential K[X] := ⟨Differential.implicitDeriv 0⟩
  have hdvd : (X - C α) ∣ pn := dvd_iff_isRoot.mpr hα
  have hnX : IsNormal (X - C α) := IsNormal.of_dvd hpn hdvd
  have := (isCoprime_X_sub_C_implicitDeriv_iff (0 : K[X]) α).mp hnX
  simp only [eval_zero] at this
  exact fun h => this h.symm

open Classical in
/-- Root characterization: for a splitting factorization `p = pₛ·pₙ` (coefficient-lifting
derivation, char `0`), a root `α` of `p` is constant iff a root of the special part:
`Dα = 0 ↔ pₛ(α) = 0`. -/
theorem deriv_eq_zero_iff_isRoot_special {p ps pn : K[X]} (hps0 : ps ≠ 0)
    (hfact : @IsSplittingFactorization _ _ ⟨Differential.implicitDeriv 0⟩ p ps pn)
    {α : K} (hα : p.IsRoot α) :
    α′ = 0 ↔ ps.IsRoot α := by
  obtain ⟨hpeq, hspec, hnorm⟩ := hfact
  have hroot : ps.IsRoot α ∨ pn.IsRoot α := by
    have : (ps * pn).IsRoot α := hpeq ▸ hα
    rw [IsRoot, eval_mul, mul_eq_zero] at this
    exact this
  constructor
  · intro hd0
    rcases hroot with hs | hn
    · exact hs
    · exact absurd hd0 (deriv_ne_zero_of_isNormal_of_isRoot hnorm hn)
  · intro hs
    exact deriv_eq_zero_of_isSpecial_of_isRoot hps0 hspec hs

open Classical in
/-- Nonconstant dual of the root characterization: a root `α` of `p` is nonconstant iff it is a
root of the normal part — `Dα ≠ 0 ↔ pₙ(α) = 0`. -/
theorem deriv_ne_zero_iff_isRoot_normal {p ps pn : K[X]} (hps0 : ps ≠ 0)
    (hfact : @IsSplittingFactorization _ _ ⟨Differential.implicitDeriv 0⟩ p ps pn)
    {α : K} (hα : p.IsRoot α) :
    α′ ≠ 0 ↔ pn.IsRoot α := by
  have hpeq := hfact.1
  have hroot : ps.IsRoot α ∨ pn.IsRoot α := by
    have : (ps * pn).IsRoot α := hpeq ▸ hα
    rw [IsRoot, eval_mul, mul_eq_zero] at this
    exact this
  constructor
  · intro hd
    rcases hroot with hs | hn
    · exact absurd ((deriv_eq_zero_iff_isRoot_special hps0 hfact hα).mpr hs) hd
    · exact hn
  · intro hn
    exact deriv_ne_zero_of_isNormal_of_isRoot hfact.2.2 hn

end RootCharacterization

end DeepWiki.SymbolicIntegration
