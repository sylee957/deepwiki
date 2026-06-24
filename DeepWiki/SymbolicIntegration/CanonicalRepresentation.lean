import DeepWiki.SymbolicIntegration.MonomialExtensions
import DeepWiki.SymbolicIntegration.SquarefreeFactorization
import Mathlib.FieldTheory.RatFunc.Basic

/-! # The canonical representation (Bronstein §3.5)
For a monomial extension `(k(t), D)` with `Dt = v ∈ k[t]`, every `f ∈ k(t)` splits *uniquely* as
`f = fₚ + fₛ + fₙ` — a polynomial part `fₚ`, a *reduced* (special-denominator) part `fₛ ∈ k⟨t⟩`,
and a *simple* (normal-denominator) part `fₙ`. We give the classifying predicates (`IsSimple`,
`IsReduced`), the splitting-factorization routine `splitFactor` that separates the special and
normal parts of a polynomial denominator, the squarefree variant `splitSquarefreeFactor` built on
Yun's factorization, the `canonicalRepresentation` of a rational function, and the root
characterization (a splitting factor `pₛ`/`pₙ` collects the constant/nonconstant roots). The
derivation on `k[X]` is the monomial derivation `implicitDeriv v` (`Dt = v`). -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section Classify
variable {K : Type*} [Field K] [Differential K]

/-- **Definition 3.5.2** (§3.5, p.100): `f ∈ k(t)` is *simple* w.r.t. the monomial derivation
`D` (`Dt = v`) if its denominator is normal — coprime to its `D`-derivative `D(denom f)`. -/
def IsSimple (v : K[X]) (f : RatFunc K) : Prop :=
  IsCoprime f.denom (Differential.implicitDeriv v f.denom)

/-- **Definition 3.5.2** (§3.5, p.100): `f ∈ k(t)` is *reduced* w.r.t. the monomial derivation
`D` (`Dt = v`) if its denominator is special — it divides its `D`-derivative `D(denom f)`. The
reduced elements form the subfield `k⟨t⟩`. -/
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

section SplitFactor
variable {K : Type*} [Field K] [Differential K]

open Classical in
/-- The squarefree special factor extracted at one `SplitFactor` step:
`S = gcd(p, Dp) / gcd(p, dp/dt)` (`Dt = v`). By Theorem 3.5.1 this is the product of the
*distinct* special irreducible factors of `p`. -/
noncomputable def splitFactorStep (v p : K[X]) : K[X] :=
  gcd p (Differential.implicitDeriv v p) / gcd p (derivative p)

open Classical in
/-- `SplitFactor` recursion (§3.5, p.100), as a `fuel`-bounded computation. Each step extracts the
squarefree special factor `S = gcd(p,Dp)/gcd(p,dp/dt)`; if `deg S = 0` the polynomial is normal and
`(p, 1)` is returned, otherwise recurse on `p/S` and multiply `S` back into the special part. The
result is `(pₙ, pₛ)`: the normal part and the special part. -/
noncomputable def splitFactorAux (v : K[X]) : K[X] → ℕ → K[X] × K[X]
  | p, 0 => (p, 1)
  | p, (n + 1) =>
    let S := splitFactorStep v p
    if S.natDegree = 0 then (p, 1)
    else
      let q := splitFactorAux v (p / S) n
      (q.1, S * q.2)

open Classical in
/-- **`SplitFactor`** (§3.5, p.100): the splitting of `p` into its normal part `pₙ` and special
part `pₛ` w.r.t. the monomial derivation `D` (`Dt = v`), with `p = pₙ·pₛ`. Iterates
`S ← gcd(p, Dp)/gcd(p, dp/dt)` until the remaining factor is normal. -/
noncomputable def splitFactor (v p : K[X]) : K[X] × K[X] :=
  splitFactorAux v p p.natDegree

open Classical in
/-- **Theorem 3.5.1(i)** (§3.5, p.99), one-step property of `SplitFactor`, as a property `P` of a
polynomial `q`. It bundles exactly what the book proves about `S = gcd(q,Dq)/gcd(q,dq/dt)`: if `S`
is constant then `q` is normal; if `S` is non-constant then `S` is a special factor of `q` with
strictly smaller-degree quotient. `splitFactorAux` is correct on any `p` for which this holds at
every polynomial (`IsSplitFactorStep` everywhere — discharged for fully-split `p` below). -/
def IsSplitFactorStep (v q : K[X]) : Prop :=
  ((splitFactorStep v q).natDegree = 0 → @IsNormal _ _ ⟨Differential.implicitDeriv v⟩ q) ∧
  (0 < (splitFactorStep v q).natDegree →
    (splitFactorStep v q ∣ q ∧
     (q / splitFactorStep v q).natDegree < q.natDegree ∧
     @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ (splitFactorStep v q)))

open Classical in
/-- Correctness of the `SplitFactor` recursion under the one-step property holding everywhere: for
fuel `≥ deg p`, `splitFactorAux v p fuel` returns a splitting factorization `(pₙ, pₛ)` of `p`
(`p = pₛ·pₙ`, `pₛ` special, `pₙ` normal) — w.r.t. the monomial derivation `D` (`Dt = v`). -/
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
/-- **`SplitFactor` correctness** (§3.5, p.100): under the one-step property `IsSplitFactorStep`
holding at every polynomial (Theorem 3.5.1(i)), `splitFactor v p = (pₙ, pₛ)` is a splitting
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
/-- For a fully-split `q = ∏_{a∈s}(X − a)^{eₐ}` (each `eₐ ≥ 1`, char `0`), the `SplitFactor` step
`S = gcd(q,Dq)/gcd(q,dq/dt)` is the squarefree special part — `S ~ ∏_{a : v(a)=a′}(X − a)`. By the
gcd formula `gcd(q,Dq) ~ gcd(q,dq/dt)·∏_{special}(X − a)` the division is exact and yields the
special factor. -/
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
/-- For a squarefree fully-split `q = ∏_{a∈s}(X − a)`, the `SplitFactor` step `S` is the special
part `∏_{a : v(a)=a′}(X − a)`; specializes `splitFactorStep_prod_X_sub_C_pow_associated` at `eₐ=1`. -/
theorem splitFactorStep_prod_X_sub_C_associated (v : K[X]) (s : Finset K) :
    Associated (splitFactorStep v (∏ a ∈ s, (X - C a)))
      (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a)) := by
  have h := splitFactorStep_prod_X_sub_C_pow_associated v s (fun _ => 1) (fun _ _ => le_rfl)
  simpa using h

open Classical in
/-- The `SplitFactor` one-step property `IsSplitFactorStep` holds for every squarefree fully-split
`q = ∏_{a∈s}(X − a)`: the step `S` is the special factor `∏_{special}(X − a)`, which (when
non-constant) is a special divisor of `q` with strictly smaller-degree quotient, and (when constant)
`q` is normal (no special roots). This discharges the hypothesis of `splitFactor` correctness on
squarefree split inputs. -/
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

section SplitSquarefreeFactor
variable {K : Type*} [Field K] [Differential K]

open Classical in
/-- One factor of **`SplitSquarefreeFactor`** (§3.5, p.102): for a squarefree `p`, its special part
is `S = gcd(p, Dp)` and its normal part is `N = p/S` (`Dt = v`). Since `p` is squarefree
(`gcd(p, dp/dt) = 1`), the `SplitFactor` step's denominator is trivial and `gcd(p, Dp)` is the
whole special part (Theorem 3.5.1(ii)). -/
noncomputable def squarefreeSpecialPart (v p : K[X]) : K[X] :=
  gcd p (Differential.implicitDeriv v p)

open Classical in
/-- The normal part of a squarefree `p`: `N = p / gcd(p, Dp)`. -/
noncomputable def squarefreeNormalPart (v p : K[X]) : K[X] :=
  p / gcd p (Differential.implicitDeriv v p)

open Classical in
/-- **`SplitSquarefreeFactor`** on one squarefree factor (§3.5, p.102): `(N, S)` with `N` the
normal part `p/gcd(p,Dp)` and `S = gcd(p,Dp)` the special part. -/
noncomputable def splitSquarefreeFactor (v p : K[X]) : K[X] × K[X] :=
  (squarefreeNormalPart v p, squarefreeSpecialPart v p)

end SplitSquarefreeFactor

section SplitSquarefreeFactorSplit
variable {K : Type*} [Field K] [CharZero K] [Differential K]

open Classical in
omit [CharZero K] in
/-- For a squarefree fully-split `p = ∏_{a∈s}(X − a)`, the special part `gcd(p, Dp)` is exactly the
special factor `∏_{a : v(a)=a′}(X − a)` (Theorem 3.5.1, squarefree case). -/
theorem squarefreeSpecialPart_prod_X_sub_C_associated (v : K[X]) (s : Finset K) :
    Associated (squarefreeSpecialPart v (∏ a ∈ s, (X - C a)))
      (∏ a ∈ s.filter (fun a => v.eval a = a′), (X - C a)) :=
  gcd_prod_X_sub_C_implicitDeriv v s

open Classical in
omit [CharZero K] in
/-- **`SplitSquarefreeFactor` correctness on one squarefree factor** (§3.5, p.102): for a squarefree
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

/-- The Bézout split underlying `ExtendedEuclidean(dₙ, dₛ, r)`: for coprime `dₙ, dₛ` and any `r`,
returns `(b, c)` with `b·dₙ + c·dₙ`… given a Bézout identity `u·dₙ + w·dₛ = 1`, reduce `u·r` mod
`dₛ` to keep `deg b < deg dₛ`. (`b = (u·r) %ₘ dₛ`, `c = w·r + (u·r /ₘ dₛ)·dₙ`.) -/
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
/-- A Bézout pair `(u, w)` with `u·a + w·b = 1` for coprime `a, b` (the `ExtendedEuclidean` output),
chosen via the existential `IsCoprime`; `(0, 0)` otherwise. -/
noncomputable def bezoutOne (a b : K[X]) : K[X] × K[X] :=
  if h : IsCoprime a b then (h.choose, h.choose_spec.choose) else (0, 0)

omit [Differential K] in
/-- `bezoutOne a b` solves `u·a + w·b = 1` when `a, b` are coprime. -/
theorem bezoutOne_spec {a b : K[X]} (h : IsCoprime a b) :
    (bezoutOne a b).1 * a + (bezoutOne a b).2 * b = 1 := by
  rw [bezoutOne, dif_pos h]
  exact h.choose_spec.choose_spec

open Classical in
/-- **`CanonicalRepresentation`** (§3.5, p.103) of `f ∈ k(t)`: with `d = denom f` (monic) and
`a = num f`, polynomial-divide `a = q·d + r` (`q = a /ₘ d`, `r = a %ₘ d`), split the denominator
`(dₙ, dₛ) = splitFactor v d`, run extended Euclid on `(dₙ, dₛ, r)` (Bézout `u·dₙ + w·dₛ = 1`) to get
`(b, c)`, and return `(q, b/dₛ, c/dₙ)` — polynomial part, reduced part, simple part. -/
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
/-- **`CanonicalRepresentation` correctness, additive split** (§3.5, p.103). Given the denominator
splitting `d = dₛ·dₙ` of `f` (`d = denom f`) and a Bézout pair `u·dₙ + w·dₛ = 1` from extended
Euclid, the canonical pieces sum back to `f`: `f = q + b/dₛ + c/dₙ` with `q = (num f) /ₘ d` the
polynomial part and `(b, c)` the Bézout split of `r = (num f) %ₘ d`. -/
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
/-- **`CanonicalRepresentation` correctness** (§3.5, p.103): the three pieces of
`canonicalRepresentation v f = (q, fₛ, fₙ)` sum to `f` — `(q : k(t)) + fₛ + fₙ = f`. Hypotheses: the
`splitFactor`-output `(dₙ, dₛ)` genuinely splits the denominator (`denom f = dₛ·dₙ`) and is coprime
(`IsCoprime dₙ dₛ`), as guaranteed by `splitFactor` correctness. -/
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

end DeepWiki.SymbolicIntegration
