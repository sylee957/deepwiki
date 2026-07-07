import DeepWiki.SymbolicIntegration.CanonicalRepresentation.Classify
import DeepWiki.SymbolicIntegration.CanonicalRepresentation.GcdFormula
import DeepWiki.SymbolicIntegration.CanonicalRepresentation.NormalSqfree
import DeepWiki.SymbolicIntegration.CanonicalRepresentation.SplitFactor
import DeepWiki.SymbolicIntegration.CanonicalRepresentation.SplitFactorCorrect
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
