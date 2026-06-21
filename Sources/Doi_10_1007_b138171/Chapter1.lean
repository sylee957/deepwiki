import DeepWiki.SymbolicIntegration.AlgebraicPreliminaries
import DeepWiki.SymbolicIntegration.PseudoDivision
import DeepWiki.SymbolicIntegration.Subresultants
import DeepWiki.SymbolicIntegration.SquarefreeFactorization
import DeepWiki.SymbolicIntegration.MonomialExtensions
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Algebra.Squarefree.Basic
import Sources.Doi_10_1007_b138171.Source

/-! # Symbolic Integration catalog — Chapter 1: Algebraic Preliminaries
Chapter 1 is standard constructive algebra, almost all of it already in Mathlib; the catalog
aliases the Mathlib concept for each book definition and discharges each book theorem with
Mathlib (or with the `DeepWiki.SymbolicIntegration` library where the book states a new
predicate, e.g. `IsGCD`). The book numbering lives here in the catalog, never in the library. -/

open Polynomial DeepWiki.SymbolicIntegration

namespace DeepWiki.Si

/-! ## §1.1 Groups, Rings and Fields -/

/-- **Definition 1.1.1** (§1.1, p.1), a *group* `(G, ∘)`: associative, with identity and
inverses. A *commutative (abelian) group* is `CommGroup`. -/
abbrev def_1_1_1 := @Group

/-- **Definition 1.1.2** (§1.1, p.2), a *ring* (with multiplicative identity); a *commutative
ring* is `CommRing`, its *characteristic* is `ringChar`, a *ring homomorphism* is `RingHom`. -/
abbrev def_1_1_2 := @Ring

/-- **Definition 1.1.2**: the characteristic of a ring. -/
noncomputable abbrev def_1_1_2_char := @ringChar

/-- **Definition 1.1.2**: a ring homomorphism. -/
abbrev def_1_1_2_hom := @RingHom

/-- **Definition 1.1.3** (§1.1, p.3), an *integral domain*: a commutative ring with `0 ≠ 1` and
no zero divisors. -/
abbrev def_1_1_3 := @IsDomain

/-- **Definition 1.1.4** (§1.1, p.3): `x` *divides* `y`. -/
abbrev def_1_1_4_dvd := @Dvd.dvd

/-- **Definition 1.1.4**: `x` is a *unit* (`R*` is the group of units `Units`). -/
abbrev def_1_1_4_unit := @IsUnit

/-- **Definition 1.1.4**: the group of units `R* = Units R`. -/
abbrev def_1_1_4_units := @Units

/-- **Definition 1.1.4**, a *greatest common divisor* (as the library predicate `IsGCD`). -/
abbrev def_1_1_4_gcd := @IsGCD

/-- **Theorem 1.1.1** (§1.1, p.4): a gcd is unique up to a unit factor (`Associated`). -/
theorem thm_1_1_1 {R : Type*} [CommMonoidWithZero R] [IsCancelMulZero R] {x y z t : R}
    (hz : IsGCD x y z) (ht : IsGCD x y t) : Associated z t :=
  hz.associated ht

/-- **Definition 1.1.5** (§1.1, p.4): `p` is *prime* if `p ∣ ab → p ∣ a ∨ p ∣ b`. -/
abbrev def_1_1_5_prime := @Prime

/-- **Definition 1.1.5**: `p` is *irreducible* if `p = ab → IsUnit a ∨ IsUnit b`. -/
abbrev def_1_1_5_irreducible := @Irreducible

/-- **Definition 1.1.6** (§1.1, p.4), a *unique factorization domain* (UFD). -/
abbrev def_1_1_6 := @UniqueFactorizationMonoid

/-- **Theorem 1.1.2** (§1.1, p.4), forward: in any integral domain a prime is irreducible. -/
theorem thm_1_1_2_prime_irreducible {R : Type*} [CommMonoidWithZero R] [IsCancelMulZero R]
    {p : R} (hp : Prime p) : Irreducible p :=
  hp.irreducible

/-- **Theorem 1.1.2**, converse: in a UFD an irreducible element is prime. -/
theorem thm_1_1_2_irreducible_prime {R : Type*} [CommMonoidWithZero R]
    [UniqueFactorizationMonoid R] {p : R} (hp : Irreducible p) : Prime p :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp hp

/-- **Theorem 1.1.3** (§1.1, p.4): in a UFD any two elements have a gcd. -/
theorem thm_1_1_3 {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (x y : R) : ∃ z, IsGCD x y z := by
  classical
  letI := UniqueFactorizationMonoid.toGCDMonoid R
  exact ⟨gcd x y, gcd_dvd_left x y, gcd_dvd_right x y, fun t h1 h2 => dvd_gcd h1 h2⟩

/-- **Theorem 1.1.4** (§1.1, p.5): if `R` is a UFD then so is the polynomial ring `R[X]`
(hence, by iteration, `R[X₁,…,Xₙ]`). -/
theorem thm_1_1_4 {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    UniqueFactorizationMonoid R[X] :=
  inferInstance

/-- **Definition 1.1.7** (§1.1, p.5), a *subgroup* `H ⊆ G`. -/
abbrev def_1_1_7 := @Subgroup

/-- **Definition 1.1.8** (§1.1, p.6), an *ideal* `I ⊆ R`; an ideal is *principal* if generated
by one element (`Submodule.IsPrincipal`). -/
abbrev def_1_1_8 := @Ideal

/-- **Definition 1.1.8**: a principal ideal. -/
abbrev def_1_1_8_principal := @Submodule.IsPrincipal

/-- **Theorem 1.1.5** (§1.1, p.6): the ideal generated by `x₁,…,xₙ` is the set of all
`R`-linear combinations `∑ aᵢxᵢ`. -/
theorem thm_1_1_5 {R : Type*} [CommRing R] (s : Finset R) (y : R) :
    y ∈ Ideal.span (s : Set R) ↔
      ∃ f : R → R, Function.support f ⊆ s ∧ ∑ i ∈ s, f i * i = y :=
  Submodule.mem_span_finset

/-- **Definition 1.1.9** (§1.1, p.6), a *principal ideal domain* (PID): an integral domain in
which every ideal is principal. -/
abbrev def_1_1_9 := @IsPrincipalIdealRing

/-- **Definition 1.1.10** (§1.1, p.6), a *Euclidean domain*: an integral domain with a size
function `ν` admitting Euclidean division. -/
abbrev def_1_1_10 := @EuclideanDomain

/-- **Theorem 1.1.6** (§1.1, p.7): every Euclidean domain is a PID. -/
theorem thm_1_1_6 {R : Type*} [EuclideanDomain R] : IsPrincipalIdealRing R :=
  inferInstance

/-- **Theorem 1.1.7** (§1.1, p.7): every PID is a UFD. -/
theorem thm_1_1_7 {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    UniqueFactorizationMonoid R :=
  inferInstance

/-- **Theorem 1.1.8** (§1.1, p.7): in a PID the ideal `(x, y)` is generated by `gcd(x, y)`. -/
theorem thm_1_1_8 {R : Type*} [CommRing R] [IsDomain R] [IsBezout R] (x y : R) :
    Ideal.span ({x, y} : Set R) = Ideal.span {IsBezout.gcd x y} :=
  (IsBezout.span_gcd x y).symm

/-- **Definition 1.1.11** (§1.1, p.7), a *field*: a commutative ring whose nonzero elements form
a group under multiplication. -/
abbrev def_1_1_11 := @Field

/-- **Definition 1.1.12** (§1.1, p.7): `α` is *algebraic* over `F` if `p(α) = 0` for some
nonzero `p ∈ F[X]`; *transcendental* otherwise; `E` is an *algebraic extension* of `F` if every
element of `E` is algebraic over `F`. -/
abbrev def_1_1_12_algebraic := @IsAlgebraic

/-- **Definition 1.1.12**: a transcendental element. -/
abbrev def_1_1_12_transcendental := @Transcendental

/-- **Definition 1.1.12**: an algebraic extension. -/
abbrev def_1_1_12_extension := @Algebra.IsAlgebraic

/-- **Definition 1.1.13** (§1.1, p.7), an *algebraically closed* field; an *algebraic closure*. -/
abbrev def_1_1_13_algClosed := @IsAlgClosed

/-- **Definition 1.1.13**: an algebraic closure. -/
abbrev def_1_1_13_algClosure := @IsAlgClosure

/-- **Theorem 1.1.9** (§1.1, p.8), existence: every field `k` has an algebraic closure
(`AlgebraicClosure k`). -/
theorem thm_1_1_9_exists (k : Type*) [Field k] : IsAlgClosure k (AlgebraicClosure k) :=
  inferInstance

/-- **Theorem 1.1.9** (§1.1, p.8), uniqueness: any two algebraic closures of `F` are
`F`-isomorphic. -/
noncomputable def thm_1_1_9_unique (F K L : Type*) [Field F] [Field K] [Field L] [Algebra F K]
    [Algebra F L] [IsAlgClosure F K] [IsAlgClosure F L] : K ≃ₐ[F] L :=
  IsAlgClosure.equiv F K L

/-- **Theorem 1.1.11** (§1.1, p.8), Hilbert's Nullstellensatz over an algebraically closed field:
`vanishingIdeal (zeroLocus I) = √I`; equivalently, if `p` vanishes on `V(I)` then `pᵐ ∈ I` for
some `m > 0`. -/
theorem thm_1_1_11 {k : Type*} [Field k] [IsAlgClosed k] {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ k)) :
    MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k I) = I.radical :=
  MvPolynomial.vanishingIdeal_zeroLocus_eq_radical I

/-- **Theorem 1.1.10** (§1.1, p.8), the weak Nullstellensatz: over an algebraically closed field,
`V(I) = ∅ ⟺ 1 ∈ I`. -/
theorem thm_1_1_10 {k : Type*} [Field k] [IsAlgClosed k] {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ k)) :
    MvPolynomial.zeroLocus k I = ∅ ↔ (1 : MvPolynomial σ k) ∈ I := by
  rw [← Ideal.eq_top_iff_one]
  constructor
  · intro h
    have key : MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k I) = I.radical :=
      MvPolynomial.vanishingIdeal_zeroLocus_eq_radical I
    rw [h, MvPolynomial.vanishingIdeal_empty] at key
    exact Ideal.radical_eq_top.mp key.symm
  · intro h
    rw [h, MvPolynomial.zeroLocus_top (K := k), Set.bot_eq_empty]

/-! ### Worked examples (§1.1) -/

open Matrix in
/-- **Example 1.1.1** (§1.1, p.2): `GL₂(ℚ)` is a group but *not* commutative — e.g.
`[[1,1],[0,1]]` and `[[0,1],[1,0]]` do not commute. -/
example : ∃ A B : GL (Fin 2) ℚ, A * B ≠ B * A := by
  have hne : ∃ S T : SpecialLinearGroup (Fin 2) ℚ, S * T ≠ T * S := by
    refine ⟨⟨of ![![1, 1], ![0, 1]], by rw [Matrix.det_fin_two]; simp⟩,
            ⟨of ![![1, 0], ![1, 1]], by rw [Matrix.det_fin_two]; simp⟩, ?_⟩
    intro h
    have := congrFun (congrFun (congrArg (·.1) h) 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, SpecialLinearGroup.coe_mul] at this
  obtain ⟨S, T, hST⟩ := hne
  exact ⟨S.toGL, T.toGL,
    fun h => hST (SpecialLinearGroup.toGL_injective (by rw [map_mul, map_mul, h]))⟩

open Matrix in
/-- **Example 1.1.3** (§1.1, p.2): `M₂(ℚ)` is a ring but *not* commutative. -/
example : ∃ A B : Matrix (Fin 2) (Fin 2) ℚ, A * B ≠ B * A := by
  refine ⟨of ![![0, 1], ![0, 0]], of ![![0, 0], ![1, 0]], ?_⟩
  intro h
  have := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at this

/-- **Example 1.1.2** (§1.1, p.2): the 2×2 rational matrices form a commutative group under
addition. -/
example : AddCommGroup (Matrix (Fin 2) (Fin 2) ℚ) := inferInstance

/-- **Example 1.1.4** (§1.1, p.3): `ℤ₆ = ZMod 6` is a commutative ring of characteristic `6`
with zero divisors — `2 · 3 = 0` while `2 ≠ 0` and `3 ≠ 0`. -/
example : CharP (ZMod 6) 6 := inferInstance

/-- **Example 1.1.4**: the zero divisors of `ℤ₆`. -/
theorem ex_1_1_4_zero_divisors :
    (2 : ZMod 6) * 3 = 0 ∧ (2 : ZMod 6) ≠ 0 ∧ (3 : ZMod 6) ≠ 0 := by decide

/-- **Example 1.1.5** (§1.1, p.3): `ℤ[√−5] = Zsqrtd (-5)` is an integral domain. (Mathlib's
`Zsqrtd` `IsDomain` instance is keyed to *positive* nonsquare `d`; for `d = -5` we get it from
the norm `N(a + b√−5) = a² + 5b²`, which is multiplicative and vanishes only at `0`.) -/
example : IsDomain (Zsqrtd (-5)) := by
  haveI : NoZeroDivisors (Zsqrtd (-5)) := ⟨fun {a b} hab => by
    have h : a.norm * b.norm = 0 := by rw [← Zsqrtd.norm_mul, hab, Zsqrtd.norm_zero]
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl ((Zsqrtd.norm_eq_zero_iff (by norm_num) a).mp h)
    · exact Or.inr ((Zsqrtd.norm_eq_zero_iff (by norm_num) b).mp h)⟩
  exact NoZeroDivisors.to_isDomain _

/-- No element of `ℤ[√−5]` has norm `2` or `3`: `N(a+b√−5) = a² + 5b² ≡ a² (mod 5)`, and `2, 3`
are not squares mod `5`. -/
private theorem zsqrtNeg5_norm_ne_two_three (z : Zsqrtd (-5)) : z.norm ≠ 2 ∧ z.norm ≠ 3 := by
  have hsq : ∀ a : ZMod 5, a * a ≠ 2 ∧ a * a ≠ 3 := by decide
  have hmod : (z.norm : ZMod 5) = (z.re : ZMod 5) * (z.re : ZMod 5) := by
    rw [Zsqrtd.norm_def]; push_cast
    have h5 : (5 : ZMod 5) = 0 := by decide
    ring_nf; rw [h5]; ring
  refine ⟨fun h => (hsq (z.re : ZMod 5)).1 ?_, fun h => (hsq (z.re : ZMod 5)).2 ?_⟩ <;>
    rw [← hmod, h] <;> rfl

/-- An element of `ℤ[√−5]` whose norm is `4`, `6`, or `9` is irreducible: a non-trivial factor
would have norm `2` or `3`, which is impossible. -/
private theorem zsqrtNeg5_irreducible_of_norm (z : Zsqrtd (-5))
    (hN : z.norm = 4 ∨ z.norm = 6 ∨ z.norm = 9) : Irreducible z := by
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · rw [← Zsqrtd.norm_eq_one_iff' (by norm_num : (-5 : ℤ) ≤ 0)]
    rcases hN with h | h | h <;> omega
  · intro a b hab
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hna, hnb⟩ := hcon
    have hnorm : z.norm = a.norm * b.norm := by rw [hab, Zsqrtd.norm_mul]
    have hna1 : a.norm ≠ 1 := fun h => hna ((Zsqrtd.norm_eq_one_iff' (by norm_num) a).mp h)
    have hnb1 : b.norm ≠ 1 := fun h => hnb ((Zsqrtd.norm_eq_one_iff' (by norm_num) b).mp h)
    have hna0 : 0 ≤ a.norm := Zsqrtd.norm_nonneg (by norm_num) a
    have hnb0 : 0 ≤ b.norm := Zsqrtd.norm_nonneg (by norm_num) b
    obtain ⟨h2a, h2b⟩ := zsqrtNeg5_norm_ne_two_three a
    obtain ⟨h3a, h3b⟩ := zsqrtNeg5_norm_ne_two_three b
    have hNz : z.norm ≠ 0 := by rcases hN with h | h | h <;> omega
    have hanz : a.norm ≠ 0 := by rintro h0; rw [hnorm, h0, zero_mul] at hNz; exact hNz rfl
    have hbnz : b.norm ≠ 0 := by rintro h0; rw [hnorm, h0, mul_zero] at hNz; exact hNz rfl
    have ha4 : 4 ≤ a.norm := by omega
    have hb4 : 4 ≤ b.norm := by omega
    rcases hN with h | h | h <;> (rw [h] at hnorm; nlinarith [hnorm, ha4, hb4])

/-- **Example 1.1.7** (§1.1, p.4): `2`, `3`, `1+√−5`, `1−√−5` are all irreducible in `ℤ[√−5]`
(norms `4, 9, 6, 6`); since `6 = 2·3 = (1+√−5)(1−√−5)`, the same element has two genuinely
different factorizations into irreducibles, so `ℤ[√−5]` is not a UFD. -/
example : Irreducible (⟨2, 0⟩ : Zsqrtd (-5)) :=
  zsqrtNeg5_irreducible_of_norm _ (Or.inl (by rw [Zsqrtd.norm_def]; norm_num))
example : Irreducible (⟨3, 0⟩ : Zsqrtd (-5)) :=
  zsqrtNeg5_irreducible_of_norm _ (Or.inr (Or.inr (by rw [Zsqrtd.norm_def]; norm_num)))
example : Irreducible (⟨1, 1⟩ : Zsqrtd (-5)) :=
  zsqrtNeg5_irreducible_of_norm _ (Or.inr (Or.inl (by rw [Zsqrtd.norm_def]; norm_num)))
example : Irreducible (⟨1, -1⟩ : Zsqrtd (-5)) :=
  zsqrtNeg5_irreducible_of_norm _ (Or.inr (Or.inl (by rw [Zsqrtd.norm_def]; norm_num)))

/-- If `u ∣ v` in `ℤ[√d]` then `N(u) ∣ N(v)` in `ℤ` (norm multiplicativity). -/
private theorem zsqrtd_norm_dvd_norm {d : ℤ} {u v : Zsqrtd d} (h : u ∣ v) : u.norm ∣ v.norm := by
  obtain ⟨w, rfl⟩ := h; rw [Zsqrtd.norm_mul]; exact dvd_mul_right _ _

/-- **Example 1.1.6** (§1.1, p.3): `6` and `2 + 2√−5` have *no* gcd in `ℤ[√−5]`. If `z` were a gcd
then `N(z) ∣ gcd(N 6, N(2+2√−5)) = gcd(36, 24) = 12`; but `2` and `1+√−5` are common divisors, so
`N(2)=4 ∣ N(z)` and `N(1+√−5)=6 ∣ N(z)`, forcing `N(z) = 12` — impossible, as `a²+5b² = 12` has no
solution (`12 ≡ 2 (mod 5)`, a non-square). This is the concrete failure of unique factorization. -/
example : ¬ ∃ z : Zsqrtd (-5), IsGCD (⟨6, 0⟩ : Zsqrtd (-5)) (⟨2, 2⟩ : Zsqrtd (-5)) z := by
  rintro ⟨z, hzx, hzy, hmax⟩
  have h2x : (⟨2, 0⟩ : Zsqrtd (-5)) ∣ ⟨6, 0⟩ :=
    ⟨⟨3, 0⟩, by ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]⟩
  have h2y : (⟨2, 0⟩ : Zsqrtd (-5)) ∣ ⟨2, 2⟩ :=
    ⟨⟨1, 1⟩, by ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]⟩
  have hsx : (⟨1, 1⟩ : Zsqrtd (-5)) ∣ ⟨6, 0⟩ :=
    ⟨⟨1, -1⟩, by ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]⟩
  have hsy : (⟨1, 1⟩ : Zsqrtd (-5)) ∣ ⟨2, 2⟩ :=
    ⟨⟨2, 0⟩, by ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]⟩
  have hn36 : z.norm ∣ 36 := by have := zsqrtd_norm_dvd_norm hzx; simpa [Zsqrtd.norm_def] using this
  have hn24 : z.norm ∣ 24 := by have := zsqrtd_norm_dvd_norm hzy; simpa [Zsqrtd.norm_def] using this
  have h4n : (4 : ℤ) ∣ z.norm := by
    have := zsqrtd_norm_dvd_norm (hmax _ h2x h2y); simpa [Zsqrtd.norm_def] using this
  have h6n : (6 : ℤ) ∣ z.norm := by
    have := zsqrtd_norm_dvd_norm (hmax _ hsx hsy); simpa [Zsqrtd.norm_def] using this
  have hge : 0 ≤ z.norm := Zsqrtd.norm_nonneg (by norm_num) z
  have hn12 : z.norm ∣ 12 := by simpa using dvd_sub hn36 hn24
  have h12n : (12 : ℤ) ∣ z.norm := by omega
  have hn : z.norm = 12 := Int.dvd_antisymm hge (by norm_num) hn12 h12n
  have hmod : (z.norm : ZMod 5) = (z.re : ZMod 5) * (z.re : ZMod 5) := by
    rw [Zsqrtd.norm_def]; push_cast
    have h5 : (5 : ZMod 5) = 0 := by decide
    ring_nf; rw [h5]; ring
  rw [hn] at hmod
  have hsq : ∀ a : ZMod 5, a * a ≠ ((12 : ℤ) : ZMod 5) := by decide
  exact hsq _ hmod.symm

/-- **Example 1.1.8** (§1.1, p.4): `ℚ[X, Y]` (here `ℚ[X][Y]`) is a unique factorization
domain. -/
example : UniqueFactorizationMonoid (Polynomial (Polynomial ℚ)) := inferInstance

/-- **Example 1.1.9** (§1.1, p.5): `SL₂(ℚ)` embeds in `GL₂(ℚ)` (a subgroup) via the injective
group homomorphism `toGL`. -/
example : Function.Injective (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := ℚ)) :=
  Matrix.SpecialLinearGroup.toGL_injective

/-- **Example 1.1.10** (§1.1, p.6): in `ℚ[X, Y]` the ideal `(X, Y)` is *not* principal — so not
every ideal of an integral domain is principal (motivating the PID definition). -/
example :
    ¬ (Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ), MvPolynomial.X 1}).IsPrincipal := by
  rintro ⟨f, hf⟩
  rw [show (MvPolynomial (Fin 2) ℚ ∙ f) = Ideal.span {f} from rfl] at hf
  have hX0dvd : ¬ (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ∣ MvPolynomial.X 1 := by
    rintro ⟨g, hg⟩
    have h := congrArg (MvPolynomial.eval ![0, 1]) hg
    simp [MvPolynomial.eval_X] at h
  have hfX0 : f ∣ MvPolynomial.X 0 := by
    have hm : MvPolynomial.X 0 ∈
        Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ), MvPolynomial.X 1} :=
      Ideal.subset_span (by left; rfl)
    rw [hf, Ideal.mem_span_singleton] at hm; exact hm
  have h1notmem : (1 : MvPolynomial (Fin 2) ℚ) ∉
      Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ), MvPolynomial.X 1} := by
    intro hmem
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hmem
    have h := congrArg MvPolynomial.constantCoeff hab
    simp [MvPolynomial.constantCoeff_X] at h
  have hfnu : ¬ IsUnit f := by
    intro hu
    exact h1notmem (by rw [hf, Ideal.span_singleton_eq_top.mpr hu]; exact Submodule.mem_top)
  obtain ⟨c, hc⟩ := hfX0
  rcases (MvPolynomial.X_prime).irreducible.isUnit_or_isUnit hc with hu | hcu
  · exact hfnu hu
  have hassoc : Associated f (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) :=
    ⟨hcu.unit, by rw [IsUnit.unit_spec]; exact hc.symm⟩
  apply hX0dvd
  have hm : MvPolynomial.X 1 ∈
      Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ), MvPolynomial.X 1} :=
    Ideal.subset_span (by right; rfl)
  rw [hf, Ideal.span_singleton_eq_span_singleton.mpr hassoc, Ideal.mem_span_singleton] at hm
  exact hm

/-- **Example 1.1.11** (§1.1, p.6): `ℚ[X]` is a principal ideal domain. -/
example : IsPrincipalIdealRing (Polynomial ℚ) := inferInstance

/-- **Example 1.1.12** (§1.1, p.6): `ℤ` is a Euclidean domain (size function `ν a = |a|`). -/
example : EuclideanDomain ℤ := inferInstance

/-- **Example 1.1.13** (§1.1, p.7): `ℤ₅ = ZMod 5` is a field. -/
example : Field (ZMod 5) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  infer_instance

/-- **Example 1.1.14** (§1.1, p.7): the *quotient field* of an integral domain is a field; e.g.
the quotient field of `ℤ` is (isomorphic to) `ℚ`. -/
noncomputable example : Field (FractionRing ℤ) := inferInstance

/-! ## §1.2 Euclidean Division and Pseudo-Division
The classical `PolyDivide` algorithm divides `A` by `B ≠ 0` over a field `K`, producing a unique
quotient and remainder with `A = BQ + R` and `R = 0` or `deg R < deg B`. We catalog the
degree-bounded division of Mathlib (`divByMonic`/`modByMonic`); over a field a general `B ≠ 0`
is `lc(B)` times a monic polynomial, so the monic case is the essential content. The
*pseudo-division* of an integral domain (`PolyPseudoDivide`) is genuinely new — not in Mathlib —
and is proved in the `DeepWiki.SymbolicIntegration` library (`pseudoDivision_exists`). -/

/-- **`PolyDivide` quotient** (§1.2, p.8): the quotient `A /ₘ B` of Euclidean division by a monic
divisor. -/
noncomputable abbrev alg_1_2_quotient := @Polynomial.divByMonic

/-- **`PolyDivide` remainder** (§1.2, p.8): the remainder `A %ₘ B`. -/
noncomputable abbrev alg_1_2_remainder := @Polynomial.modByMonic

/-- **Euclidean polynomial division** (§1.2, p.8): for a monic `B`, `A = B·(A /ₘ B) + (A %ₘ B)`
with the remainder either `0` or of degree `< deg B`. -/
theorem thm_1_2_polyDivide {K : Type*} [Field K] (A B : Polynomial K) (hB : B.Monic) :
    A = B * (A /ₘ B) + (A %ₘ B) ∧ ((A %ₘ B) = 0 ∨ (A %ₘ B).degree < B.degree) := by
  refine ⟨?_, ?_⟩
  · rw [eq_comm, add_comm]; exact Polynomial.modByMonic_add_div A B
  · rcases eq_or_ne (A %ₘ B) 0 with h | h
    · exact Or.inl h
    · exact Or.inr (Polynomial.degree_modByMonic_lt A hB)

/-- **Pseudo-division** `PolyPseudoDivide` (§1.2, p.9): over an integral domain, for `B ≠ 0`
there is a power `n`, a pseudo-quotient `Q` and pseudo-remainder `Rem` with
`lc(B)ⁿ · A = B·Q + Rem` and `deg Rem < deg B`. (The minimal `n` is `max(0, deg A − deg B + 1)`,
the `bᵈ⁺¹` of the book.) -/
theorem thm_1_2_pseudoDivide {R : Type*} [CommRing R] [IsDomain R] (A B : R[X]) (hB : B ≠ 0) :
    ∃ (n : ℕ) (Q Rem : R[X]),
      Polynomial.C B.leadingCoeff ^ n * A = B * Q + Rem ∧ Rem.degree < B.degree :=
  pseudoDivision_exists A B hB

/-! ## §1.3 The Euclidean Algorithm -/

/-- **`Euclidean` algorithm** (§1.3, p.10): `EuclideanDomain.gcd`, computed by repeated Euclidean
division. -/
abbrev alg_1_3_euclidean := @EuclideanDomain.gcd

/-- **`ExtendedEuclidean` algorithm** (§1.3, p.11): the Bézout cofactors `(gcdA, gcdB)`. -/
abbrev alg_1_3_extended := @EuclideanDomain.xgcd

/-- **Euclidean algorithm correctness** (§1.3, p.10): `EuclideanDomain.gcd a b` is a greatest
common divisor of `a` and `b` (the library predicate `IsGCD`). -/
theorem thm_1_3_euclidean {R : Type*} [EuclideanDomain R] [DecidableEq R] (a b : R) :
    IsGCD a b (EuclideanDomain.gcd a b) :=
  ⟨EuclideanDomain.gcd_dvd_left a b, EuclideanDomain.gcd_dvd_right a b,
    fun _ h1 h2 => EuclideanDomain.dvd_gcd h1 h2⟩

/-- **Extended Euclidean correctness** (§1.3, p.11), Bézout's identity:
`gcd(a, b) = s·a + t·b` for `s = gcdA a b`, `t = gcdB a b`. -/
theorem thm_1_3_extended {R : Type*} [EuclideanDomain R] [DecidableEq R] (a b : R) :
    EuclideanDomain.gcd a b = a * EuclideanDomain.gcdA a b + b * EuclideanDomain.gcdB a b :=
  EuclideanDomain.gcd_eq_gcd_ab a b

/-! ## §1.4 Resultants and Subresultants -/

/-- **Definition 1.4.1** (§1.4, p.18): the *Sylvester matrix* `S(A,B)`. -/
noncomputable abbrev def_1_4_1_sylvester := @Polynomial.sylvester

/-- **Definition 1.4.1** (§1.4, p.18): the *resultant* `res(A,B) = det S(A,B)`. -/
noncomputable abbrev def_1_4_1 := @Polynomial.resultant

/-- **Theorem 1.4.1** (§1.4, p.19), symmetry: `res(A,B) = (-1)^{deg A · deg B} · res(B,A)`. -/
theorem thm_1_4_1_comm {R : Type*} [CommRing R] (f g : R[X]) :
    Polynomial.resultant f g = (-1) ^ (f.natDegree * g.natDegree) * Polynomial.resultant g f :=
  Polynomial.resultant_comm f g f.natDegree g.natDegree

/-- **Theorem 1.4.1** (§1.4, p.19), the root form: for `f` that splits,
`res(A,B) = lc(A)^{deg B} · ∏_{α root of A} B(α)`. -/
theorem thm_1_4_1_prod {R : Type*} [CommRing R] [IsDomain R] (f g : R[X]) (n : ℕ)
    (hg : g.natDegree ≤ n) (hf : f.Splits) :
    Polynomial.resultant f g f.natDegree n = f.leadingCoeff ^ n * (f.roots.map g.eval).prod :=
  Polynomial.resultant_eq_prod_eval f g n hg hf

/-- **Theorem 1.4.1** (§1.4, p.19), multiplicativity: `res(A₁·A₂, B) = res(A₁, B) · res(A₂, B)`. -/
theorem thm_1_4_1_mul {R : Type*} [CommRing R] (f₁ f₂ g : R[X]) (n : ℕ) (hn : g.natDegree ≤ n) :
    Polynomial.resultant (f₁ * f₂) g (f₁.natDegree + f₂.natDegree) n
      = Polynomial.resultant f₁ g f₁.natDegree n * Polynomial.resultant f₂ g f₂.natDegree n :=
  Polynomial.resultant_mul_left f₁ f₂ g n hn

/-- **Corollary 1.4.2** (§1.4, p.19), field case: `res(A,B) = 0 ⟺ A, B` are not coprime — i.e.
`deg gcd(A,B) > 0` — provided `A` and `B` are not both zero. -/
theorem cor_1_4_2 {K : Type*} [Field K] {f g : K[X]} :
    Polynomial.resultant f g = 0 ↔ (f ≠ 0 ∨ g ≠ 0) ∧ ¬ IsCoprime f g :=
  Polynomial.resultant_eq_zero_iff

/-- **Corollary 1.4.1** (§1.4, p.19): for nonzero `A` that splits, `res(A, B) = 0` iff `A` and `B`
have a common root (some root `α` of `A` with `B(α) = 0`) — the vanishing of `res = lc(A)^{deg B}·∏
B(αᵢ)` in a domain. -/
theorem cor_1_4_1 {R : Type*} [CommRing R] [IsDomain R] {f g : R[X]} (n : ℕ)
    (hg : g.natDegree ≤ n) (hf : f.Splits) (hf0 : f ≠ 0) :
    Polynomial.resultant f g f.natDegree n = 0 ↔ ∃ α ∈ f.roots, g.eval α = 0 :=
  resultant_eq_zero_iff_exists_root n hg hf hf0

/-- **Theorem 1.4.2** (§1.4, p.19): the resultant lies in the ideal `(A, B)` — there exist
`S, T` with `deg S < deg B`, `deg T < deg A` and `A·S + B·T = res(A, B)` (the Bézout/Sylvester
identity). -/
theorem thm_1_4_2 {R : Type*} [CommRing R] (f g : R[X]) (m n : ℕ) (hf : f.natDegree ≤ m)
    (hg : g.natDegree ≤ n) (H : m ≠ 0 ∨ n ≠ 0) :
    ∃ p q : R[X], p.degree < (n : WithBot ℕ) ∧ q.degree < (m : WithBot ℕ)
      ∧ f * p + g * q = C (Polynomial.resultant f g m n) :=
  Polynomial.exists_mul_add_mul_eq_C_resultant f g hf hg H

/-- **Example 1.4.2** (§1.4, p.19): `res(x²+1, x²−1) = 4` in `ℤ[x]`, the determinant of the `4×4`
Sylvester matrix (here in Mathlib's column layout: the two `x²−1`-columns then the two
`x²+1`-columns). The first subresultant `S₁ = −2` is *defective* — that part needs the
subresultant operator (Definition 1.4.2), deferred below. -/
theorem ex_1_4_2 :
    Polynomial.sylvester (X ^ 2 + 1 : ℤ[X]) (X ^ 2 - 1) 2 2
        = !![-1, 0, 1, 0; 0, -1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1]
      ∧ Polynomial.resultant (X ^ 2 + 1 : ℤ[X]) (X ^ 2 - 1) 2 2 = 4 := by
  have hS : Polynomial.sylvester (X ^ 2 + 1 : ℤ[X]) (X ^ 2 - 1) 2 2
      = !![-1, 0, 1, 0; 0, -1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Polynomial.sylvester, Fin.addCases, coeff_X_pow, coeff_sub, coeff_add, coeff_one]
  exact ⟨hS, by rw [Polynomial.resultant, hS]; decide⟩

/-- **Definition 1.4.2** (§1.4, p.20): the `j`-th *subresultant* `Sⱼ(A,B) = ∑_{i=0}^j det(ⱼSᵢ)·xⁱ`
(the library `subresultant`, on Bronstein's Sylvester layout `bSylvester`). The regular case
`S₀ = det(Sylvester) = res(A,B)` is `subresultant_zero`. -/
noncomputable abbrev def_1_4_2 := @subresultant

/-- **Theorem 1.4.3** (§1.4, p.21), degree-preserving case ("Note in particular"): subresultants
commute with a coefficient ring homomorphism, `Sⱼ(σ̄A, σ̄B) = σ̄(Sⱼ(A,B))` (the library
`subresultant_map`). -/
abbrev thm_1_4_3 := @subresultant_map

/-- **Example 1.4.3** (§1.4, p.21): specializing `t ↦ 1` (`σ : ℤ[t] → ℤ`) sends
`A = 3tx²−t³−4 ↦ 3x²−5` and `B = x²+t³x−9 ↦ x²+x−9`; by Theorem 1.4.3 (`thm_1_4_3`) their
subresultants are the specialized ones — `S₀ = res(3x²−5, x²+x−9) = 469` and `S₁ = 3x − 22`. -/
theorem ex_1_4_3 :
    subresultant (C 3 * X ^ 2 - C 5 : ℤ[X]) (X ^ 2 + X - C 9) 2 2 0 = 469
      ∧ subresultant (C 3 * X ^ 2 - C 5 : ℤ[X]) (X ^ 2 + X - C 9) 2 2 1 = 3 * X - 22 := by
  have hM : bSylvester (C 3 * X ^ 2 - C 5 : ℤ[X]) (X ^ 2 + X - C 9) 2 2
      = !![3, 0, -5, 0; 0, 3, 0, -5; 1, 1, -9, 0; 0, 1, 1, -9] := by
    ext i l; fin_cases i <;> fin_cases l <;>
      simp [bSylvester, coeff_X_pow, coeff_sub, coeff_add, coeff_X]
  refine ⟨?_, ?_⟩
  · rw [subresultant_zero, hM]; norm_num [show (!![3, 0, -5, 0; 0, 3, 0, -5; 1, 1, -9, 0; 0, 1, 1, -9] :
      Matrix (Fin 4) (Fin 4) ℤ).det = 469 from by decide]
  · have hd0 : ((!![3, 0, -5, 0; 0, 3, 0, -5; 1, 1, -9, 0; 0, 1, 1, -9] : Matrix (Fin 4) (Fin 4) ℤ).submatrix
        (subRow 2 2 1) (subCol 2 2 1 0)).det = -22 := by decide
    have hd1 : ((!![3, 0, -5, 0; 0, 3, 0, -5; 1, 1, -9, 0; 0, 1, 1, -9] : Matrix (Fin 4) (Fin 4) ℤ).submatrix
        (subRow 2 2 1) (subCol 2 2 1 1)).det = 3 := by decide
    simp only [subresultant, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hM, hd0, hd1]
    simp only [pow_zero, mul_one, pow_one, map_neg, map_ofNat]
    ring

/-- **Example 1.4.1** (§1.4, p.18): the Sylvester matrix of `A = 3tx² − t³ − 4` and
`B = x² + t³x − 9` in `ℤ[t][x]`, and its determinant — the resultant
`res(A,B) = −3t¹⁰ − 12t⁷ + t⁶ − 54t⁴ + 8t³ + 729t² − 216t + 16`. -/
theorem ex_1_4_1 :
    bSylvester (C (3 * X) * X ^ 2 - C (X ^ 3 + 4) : (ℤ[X])[X]) (X ^ 2 + C (X ^ 3) * X - C 9) 2 2
        = !![3 * X, 0, -X ^ 3 - 4, 0; 0, 3 * X, 0, -X ^ 3 - 4; 1, X ^ 3, -9, 0; 0, 1, X ^ 3, -9]
      ∧ (bSylvester (C (3 * X) * X ^ 2 - C (X ^ 3 + 4) : (ℤ[X])[X]) (X ^ 2 + C (X ^ 3) * X - C 9) 2 2).det
        = -3 * X ^ 10 - 12 * X ^ 7 + X ^ 6 - 54 * X ^ 4 + 8 * X ^ 3 + 729 * X ^ 2 - 216 * X + 16 := by
  have hM : bSylvester (C (3 * X) * X ^ 2 - C (X ^ 3 + 4) : (ℤ[X])[X]) (X ^ 2 + C (X ^ 3) * X - C 9) 2 2
      = !![3 * X, 0, -X ^ 3 - 4, 0; 0, 3 * X, 0, -X ^ 3 - 4; 1, X ^ 3, -9, 0; 0, 1, X ^ 3, -9] := by
    refine Matrix.ext fun i l => ?_
    fin_cases i <;> fin_cases l <;>
      simp [bSylvester, coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X,
        -map_mul, -map_pow] <;> ring
  refine ⟨hM, ?_⟩
  rw [hM, det_fin_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.of_apply]
  ring

-- **Deferred — not in Mathlib (library work):** the *general* Theorem 1.4.3 with the
-- `σ(lc A)^(deg B − deg σ̄B)` scaling factor when `σ` lowers `deg B` (subresultants of different
-- sizes). [Theorem 1.4.2 = `thm_1_4_2`; Definition 1.4.2 = `def_1_4_2`; degree-preserving 1.4.3 =
-- `thm_1_4_3`.]

/-! ## §1.5 Polynomial Remainder Sequences -/

/-- **Definition 1.5.1** (§1.5, p.21): a *Polynomial Remainder Sequence* of `A, B` with scalar
sequence `β` (the library predicate `IsPRS`); the pseudo-remainder step uses `IsPseudoRemainder`. -/
abbrev def_1_5_1 := @IsPRS

/-- **Definition 1.5.2** (§1.5, p.22): `A` is *similar* to `B` over `D[x]` when `a·A = b·B` for
nonzero scalars `a, b ∈ D` (the library predicate `IsSimilar`). -/
abbrev def_1_5_2 := @IsSimilar

/-- **Theorem 1.5.1** (§1.5, p.22): for `D` a UFD, the last nonzero element `Rₖ` of any PRS of
`A, B` is similar to `gcd(A, B)` (the library theorem `IsPRS.isSimilar_gcd`; `D[x]` is given its
`GCDMonoid` structure via `UniqueFactorizationMonoid.toGCDMonoid`). -/
abbrev thm_1_5_1 := @IsPRS.isSimilar_gcd

/-- **Example 1.5.1** (§1.5, p.25): the subresultants of `A = x²+1` and `B = x²−1` in `ℤ[x]` are
`S₀ = 4 = res(A,B)` and `S₁ = −2` (defective, a nonzero constant). -/
theorem ex_1_5_1 :
    subresultant (X ^ 2 + 1 : ℤ[X]) (X ^ 2 - 1) 2 2 0 = 4
      ∧ subresultant (X ^ 2 + 1 : ℤ[X]) (X ^ 2 - 1) 2 2 1 = -2 := by
  have hM : bSylvester (X ^ 2 + 1 : ℤ[X]) (X ^ 2 - 1) 2 2
      = !![1, 0, 1, 0; 0, 1, 0, 1; 1, 0, -1, 0; 0, 1, 0, -1] := by
    ext i l; fin_cases i <;> fin_cases l <;>
      simp [bSylvester, coeff_X_pow, coeff_sub, coeff_add, coeff_one]
  refine ⟨?_, ?_⟩
  · rw [subresultant_zero, hM]; norm_num [show (!![1, 0, 1, 0; 0, 1, 0, 1; 1, 0, -1, 0; 0, 1, 0, -1] :
      Matrix (Fin 4) (Fin 4) ℤ).det = 4 from by decide]
  · have hd0 : ((!![1, 0, 1, 0; 0, 1, 0, 1; 1, 0, -1, 0; 0, 1, 0, -1] : Matrix (Fin 4) (Fin 4) ℤ).submatrix
        (subRow 2 2 1) (subCol 2 2 1 0)).det = -2 := by decide
    have hd1 : ((!![1, 0, 1, 0; 0, 1, 0, 1; 1, 0, -1, 0; 0, 1, 0, -1] : Matrix (Fin 4) (Fin 4) ℤ).submatrix
        (subRow 2 2 1) (subCol 2 2 1 1)).det = 0 := by decide
    simp only [subresultant, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hM, hd0, hd1,
      pow_zero, mul_one, pow_one, map_zero, zero_mul, add_zero]
    norm_num

/-- **Example 1.5.2** (§1.5, p.25): the subresultants of `A = 3tx² − t³ − 4` and `B = x² + t³x − 9`
over `ℤ[t]` are `S₀ = res(A,B) = −3t¹⁰ − 12t⁷ + t⁶ − 54t⁴ + 8t³ + 729t² − 216t + 16` and
`S₁ = 3t⁴x + t³ − 27t + 4`. The degree-10 `S₀` determinant is computed by `det_fin_four`. -/
theorem ex_1_5_2 :
    subresultant (C (3 * X) * X ^ 2 - C (X ^ 3 + 4) : (ℤ[X])[X]) (X ^ 2 + C (X ^ 3) * X - C 9) 2 2 0
        = C (-3 * X ^ 10 - 12 * X ^ 7 + X ^ 6 - 54 * X ^ 4 + 8 * X ^ 3 + 729 * X ^ 2 - 216 * X + 16)
      ∧ subresultant (C (3 * X) * X ^ 2 - C (X ^ 3 + 4) : (ℤ[X])[X]) (X ^ 2 + C (X ^ 3) * X - C 9) 2 2 1
        = C (X ^ 3 - 27 * X + 4) + C (3 * X ^ 4) * X := by
  have hM : bSylvester (C (3 * X) * X ^ 2 - C (X ^ 3 + 4) : (ℤ[X])[X]) (X ^ 2 + C (X ^ 3) * X - C 9) 2 2
      = !![3 * X, 0, -X ^ 3 - 4, 0; 0, 3 * X, 0, -X ^ 3 - 4; 1, X ^ 3, -9, 0; 0, 1, X ^ 3, -9] := by
    refine Matrix.ext fun i l => ?_
    fin_cases i <;> fin_cases l <;>
      simp [bSylvester, coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X,
        -map_mul, -map_pow] <;> ring
  refine ⟨?_, ?_⟩
  · rw [subresultant_zero, hM]
    congr 1
    rw [det_fin_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.of_apply]
    ring
  · simp only [subresultant, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hM]
    have hd0 : ((!![3 * X, 0, -X ^ 3 - 4, 0; 0, 3 * X, 0, -X ^ 3 - 4; 1, X ^ 3, -9, 0; 0, 1, X ^ 3, -9] :
        Matrix (Fin 4) (Fin 4) (ℤ[X])).submatrix (subRow 2 2 1) (subCol 2 2 1 0)).det
        = X ^ 3 - 27 * X + 4 := by
      rw [Matrix.det_fin_two]
      simp only [Matrix.submatrix_apply, show subRow 2 2 1 0 = (0 : Fin 4) from rfl,
        show subRow 2 2 1 1 = (2 : Fin 4) from rfl, show subCol 2 2 1 0 0 = (0 : Fin 4) from rfl,
        show subCol 2 2 1 0 1 = (2 : Fin 4) from rfl, Matrix.cons_val, Matrix.of_apply]
      ring
    have hd1 : ((!![3 * X, 0, -X ^ 3 - 4, 0; 0, 3 * X, 0, -X ^ 3 - 4; 1, X ^ 3, -9, 0; 0, 1, X ^ 3, -9] :
        Matrix (Fin 4) (Fin 4) (ℤ[X])).submatrix (subRow 2 2 1) (subCol 2 2 1 1)).det = 3 * X ^ 4 := by
      rw [Matrix.det_fin_two]
      simp only [Matrix.submatrix_apply, show subRow 2 2 1 0 = (0 : Fin 4) from rfl,
        show subRow 2 2 1 1 = (2 : Fin 4) from rfl, show subCol 2 2 1 1 0 = (0 : Fin 4) from rfl,
        show subCol 2 2 1 1 1 = (1 : Fin 4) from rfl, Matrix.cons_val, Matrix.of_apply]
      ring
    rw [hd0, hd1]
    simp only [pow_zero, mul_one, pow_one]

/-- **Exercise 1.11** (§1, p.33): similarity (Definition 1.5.2) is an equivalence relation on
`D[x]` when `D` is an integral domain (`isSimilar_equivalence`). -/
theorem ex_1_11 {R : Type*} [CommRing R] [IsDomain R] : Equivalence (IsSimilar (R := R)) :=
  isSimilar_equivalence

/-! ## §1.6 Primitive Polynomials -/

/-- **Definition 1.6.1** (§1.6, p.25), the *content* `content(A) = gcd(a₀, …, aₙ)` of a
polynomial over a UFD. -/
abbrev def_1_6_1_content := @Polynomial.content

/-- **Definition 1.6.1**: `A` is *primitive* if `content(A)` is a unit. -/
abbrev def_1_6_1_primitive := @Polynomial.IsPrimitive

/-- **Definition 1.6.1**: the *primitive part* `pp(A) = A / content(A)`. -/
noncomputable abbrev def_1_6_1_primPart := @Polynomial.primPart

/-- **Definition 1.6.1**: the decomposition `A = content(A) · pp(A)`. -/
theorem def_1_6_1_decomp {R : Type*} [CommRing R] [NormalizedGCDMonoid R] (A : R[X]) :
    A = Polynomial.C A.content * A.primPart :=
  Polynomial.eq_C_content_mul_primPart A

/-- **Lemma 1.6.1** (§1.6, p.26), Gauss's Lemma: the content is multiplicative,
`content(AB) = content(A) · content(B)`. -/
theorem lem_1_6_1 {R : Type*} [CommRing R] [NormalizedGCDMonoid R] (A B : R[X]) :
    (A * B).content = A.content * B.content :=
  Polynomial.content_mul

/-- **Theorem 1.6.1(i)** (§1.6, p.27): a prime factor divides the derivative one less time —
if `Pⁿ⁺¹ ∣ A` then `Pⁿ ∣ gcd(A, dA/dx)` (for any gcd `G` of `A` and its derivative). -/
theorem thm_1_6_1_i {R : Type*} [CommRing R] {A P G : R[X]} {n : ℕ} (h : P ^ (n + 1) ∣ A)
    (hG : IsGCD A (derivative A) G) : P ^ n ∣ G :=
  pow_dvd_gcd_of_pow_succ_dvd h hG

/-- **Theorem 1.6.1(ii)** (§1.6, p.27): the characteristic-`0` converse — for a prime `P` of
positive degree and `n > 0`, if `Pⁿ` divides both `A` and `dA/dx` then `Pⁿ⁺¹ ∣ A`. -/
theorem thm_1_6_1_ii {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {A P : R[X]} {n : ℕ}
    (hn : 0 < n) (hP : Prime P) (hPdeg : 0 < P.natDegree) (hA : P ^ n ∣ A)
    (hA' : P ^ n ∣ derivative A) : P ^ (n + 1) ∣ A :=
  pow_succ_dvd_of_pow_dvd_derivative hn hP hPdeg hA hA'

/-- **Theorem 1.6.1** (§1.6, p.27), combined: in characteristic `0`, for a prime `P` of positive
degree and `n > 0`, `Pⁿ⁺¹ ∣ A ⟺ Pⁿ ∣ A ∧ Pⁿ ∣ dA/dx`. -/
theorem thm_1_6_1 {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {A P : R[X]} {n : ℕ}
    (hn : 0 < n) (hP : Prime P) (hPdeg : 0 < P.natDegree) :
    P ^ (n + 1) ∣ A ↔ P ^ n ∣ A ∧ P ^ n ∣ derivative A :=
  pow_succ_dvd_iff hn hP hPdeg

open Classical Polynomial in
/-- **Equation 1.14** (§1.6, p.28): the squarefree part `A* = A/gcd(A, dA/dx)` of `A` is its
radical. For `A = ∏_{a∈s}(X − a)^{eₐ}` (char `0`), stated multiplicatively,
`A ~ gcd(A, dA/dx) · ∏_{a∈s}(X − a)` — so `A*` is the squarefree product `∏(X − a)`. -/
theorem eq_1_14 {K : Type*} [Field K] [CharZero K] (s : Finset K) (e : K → ℕ)
    (he : ∀ a ∈ s, 1 ≤ e a) :
    Associated (∏ a ∈ s, (X - C a) ^ e a)
      (gcd (∏ a ∈ s, (X - C a) ^ e a) (derivative (∏ a ∈ s, (X - C a) ^ e a))
        * ∏ a ∈ s, (X - C a)) :=
  prod_X_sub_C_pow_associated_gcd_mul_radical s e he

/-- **Definition 1.6.2** (§1.6, p.26): the *squarefree part* `A* = ∏ Pᵢ` (the library
`squarefreePart`). -/
noncomputable abbrev def_1_6_2_squarefreePart := @squarefreePart

/-- **Definition 1.6.2** (§1.6, p.26): the *`k`-deflation* `A⁻ᵏ = ∏ Pᵢ^max(0,eᵢ−k)` (the library
`deflation`); the `1`-deflation is the *deflation* `A⁻`. -/
noncomputable abbrev def_1_6_2_deflation := @deflation

/-- **Relation (1.11)** (§1.6, p.26): `A* · A⁻ = pp(A)` (up to associates). -/
abbrev rel_1_11 := @squarefreePart_mul_deflation

/-- **Relation (1.12)** (§1.6, p.27): `A⁻⁽ᵏ⁺¹⁾ = (A⁻ᵏ)⁻`. -/
abbrev rel_1_12 := @deflation_succ

/-- **Relation (1.13)** (§1.6, p.27): `A⁻⁽ᵏ⁺¹⁾ = A⁻ᵏ / (A⁻ᵏ)*` (multiplicative form,
up to associates). -/
abbrev rel_1_13 := @squarefreePart_mul_deflation_succ

/-! ## §1.7 Squarefree Factorization -/

/-- **Definition 1.7.1** (§1.7, p.28): `A` is *squarefree* if no non-unit `B` satisfies
`B² ∣ A`. -/
abbrev def_1_7_1 := @Squarefree

/-- **Squarefree criterion** (§1.7; a consequence of Theorem 1.6.1 over a characteristic-`0` field,
used to justify the `Squarefree` algorithm): `A` is squarefree iff `gcd(A, dA/dx) = 1` — i.e. `A`
and its derivative are coprime. -/
theorem squarefree_iff_coprime_derivative {K : Type*} [Field K] [CharZero K] {A : K[X]} :
    Squarefree A ↔ IsCoprime A (derivative A) :=
  squarefree_iff_isCoprime_derivative

/-- **Squarefree-factorization part** `Aᵢ = ∏_{eₚ = i} P` (§1.7, Lemma 1.7.1). -/
noncomputable abbrev def_sqfreeFactPart := @sqfreeFactPart

/-- **Lemma 1.7.1 (i)** (§1.7, p.28): `A⁻ᵏ = ∏_{i>k} Aᵢ^(i-k)` — the deflation regrouped by
multiplicity. -/
abbrev lem_1_7_1_i := @deflation_eq_prod_sqfreeFactPart

/-- **Lemma 1.7.1 (ii)** (§1.7, p.28, equation 1.15): `Aᵢ = (A⁻⁽ⁱ⁻¹⁾)* / (A⁻ⁱ)*` — multiplicatively,
`(A⁻ⁱ)* · Aᵢ = (A⁻⁽ⁱ⁻¹⁾)*`. -/
abbrev lem_1_7_1_ii := @squarefreePart_deflation_mul_sqfreeFactPart

/-- **Lemma 1.7.1 (iii)** (§1.7, p.28), the factorization identity: `pp(A) = ∏ᵢ Aᵢⁱ` (up to
associates). -/
abbrev lem_1_7_1_iii := @primPart_associated_prod_sqfreeFactPart

/-- **Lemma 1.7.1 (iii)** (§1.7, p.28), squarefree qualifier: each `Aᵢ` is squarefree. -/
abbrev lem_1_7_1_iii_squarefree := @sqfreeFactPart_squarefree

/-- **Lemma 1.7.1 (iii)** (§1.7, p.28), coprimality qualifier: the `Aᵢ` are pairwise coprime
(`gcd(Aᵢ, Aⱼ) ∈ D`, as `IsRelPrime`). -/
abbrev lem_1_7_1_iii_coprime := @sqfreeFactPart_isRelPrime

/-- **Yun's polynomial** (§1.7, equation 1.16): `Yₖ = ∑_{i≥k} (i−k+1)·(dAᵢ/dx)·∏_{l≥k,l≠i} Aₗ`. -/
noncomputable abbrev def_yun := @Yun

/-- **Lemma 1.7.2** (§1.7, p.30, equation 1.17): Yun's derivative recurrence
`d(A⁻⁽ⁱ⁻¹⁾)/dx = A⁻ⁱ · Yᵢ`. -/
abbrev lem_1_7_2 := @derivative_deflation_pred

/-- **Lemma 1.7.2** (§1.7, p.30, equation 1.18): `Yᵢ − d(A⁻⁽ⁱ⁻¹⁾)*/dx = Aᵢ · Y_{i+1}` — the
squarefree-part form of Yun's recurrence. -/
abbrev lem_1_7_2_eq_18 := @Yun_sub_derivative_squarefreePart

/-- **Lemma 1.7.2** (§1.7, p.30, equation 1.17): the gcd clause `gcd((A⁻⁽ⁱ⁻¹⁾)*, Yᵢ) ∈ K` over a
characteristic-`0` field — `(A⁻⁽ⁱ⁻¹⁾)*` and `Yᵢ` are relatively prime. -/
abbrev lem_1_7_2_eq_17_gcd := @isRelPrime_squarefreePart_Yun

open Classical Polynomial in
/-- **Definition 1.7.2** (§1.7, p.30): the *squarefree factorization* `A = ∏ₖ Aₖᵏ` of
`A = ∏_{a∈s}(X − a)^{eₐ}`, where `Aₖ = ∏_{a : eₐ=k}(X − a)` is the (squarefree) product of the roots
of multiplicity exactly `k`. -/
theorem def_1_7_2 {K : Type*} [CommRing K] (s : Finset K) (e : K → ℕ) :
    (∏ a ∈ s, (X - C a) ^ e a)
      = ∏ k ∈ s.image e, (∏ a ∈ s.filter (fun a => e a = k), (X - C a)) ^ k :=
  prod_X_sub_C_pow_eq_squarefree_factorization s e

open Classical Polynomial in
/-- **Definition 1.7.2** (§1.7, p.30): the squarefree-factorization parts `Aₖ` are pairwise
coprime — `Aₖ ⊥ Aₖ'` for `k ≠ k'` (their roots have distinct multiplicities, hence are disjoint). -/
theorem def_1_7_2_coprime {K : Type*} [Field K] (s : Finset K) (e : K → ℕ) {k k' : ℕ}
    (hkk : k ≠ k') :
    IsCoprime (∏ a ∈ s.filter (fun a => e a = k), (X - C a))
      (∏ a ∈ s.filter (fun a => e a = k'), (X - C a)) :=
  squarefree_factorization_pairwise_coprime s e hkk

open Classical Polynomial in
/-- **Definition 1.7.2** (§1.7, p.30): each squarefree-factorization part `Aₖ = ∏_{a:eₐ=k}(X − a)`
is squarefree (a product of distinct linear factors). -/
theorem def_1_7_2_squarefree {K : Type*} [Field K] (s : Finset K) (e : K → ℕ) (k : ℕ) :
    Squarefree (∏ a ∈ s.filter (fun a => e a = k), (X - C a)) :=
  squarefree_prod_X_sub_C _

/-! ## Exercises -/

/-- **Exercise 1.1** (§1, p.32): `gcd(217, 413) = 7` in `ℤ` (Euclidean algorithm). -/
theorem ex_1_1 : Int.gcd 217 413 = 7 := by decide

/-- **Exercise 1.2** (§1, p.32): the linear Diophantine equations `12x + 19y = 1` and `3x + 2y = 5`
have integer solutions (`(8, −5)` and `(1, 1)`; found by the Extended Euclidean algorithm). -/
theorem ex_1_2 : (∃ x y : ℤ, 12 * x + 19 * y = 1) ∧ (∃ x y : ℤ, 3 * x + 2 * y = 5) :=
  ⟨⟨8, -5, by norm_num⟩, ⟨1, 1, by norm_num⟩⟩

/-- **Exercise 1.13** (§1, p.33): the resultant lies in the ideal `(A, B)` (proved with the
Extended Euclidean algorithm + Theorem 1.4.1) — this is exactly **Theorem 1.4.2** (`thm_1_4_2`). -/
theorem ex_1_13 {R : Type*} [CommRing R] (f g : R[X]) (m n : ℕ) (hf : f.natDegree ≤ m)
    (hg : g.natDegree ≤ n) (H : m ≠ 0 ∨ n ≠ 0) :
    ∃ p q : R[X], p.degree < (n : WithBot ℕ) ∧ q.degree < (m : WithBot ℕ)
      ∧ f * p + g * q = C (Polynomial.resultant f g m n) :=
  thm_1_4_2 f g m n hf hg H

/-- **Exercise 1.14** (§1, p.33): correctness of the Extended Euclidean algorithm via its loop
invariant. The cofactor relations `a₁·A + a₂·B = a` and `b₁·A + b₂·B = b` are established by the
initialization `(a₁,a₂,b₁,b₂) = (1,0,0,1)` and preserved by one Euclidean-division step
`a = q·b + r` (the new lower row is `(a₁ − q·b₁, a₂ − q·b₂)`), so on termination the returned
cofactors express `gcd(A,B) = s·A + t·B`. -/
theorem ex_1_14 {R : Type*} [CommRing R] (A B : R) :
    ((1 : R) * A + 0 * B = A ∧ (0 : R) * A + 1 * B = B)
    ∧ (∀ a b q r a₁ a₂ b₁ b₂ : R, a₁ * A + a₂ * B = a → b₁ * A + b₂ * B = b → a = q * b + r →
        b₁ * A + b₂ * B = b ∧ (a₁ - q * b₁) * A + (a₂ - q * b₂) * B = r) := by
  refine ⟨⟨by ring, by ring⟩, fun a b q r a₁ a₂ b₁ b₂ ha hb hdiv => ⟨hb, ?_⟩⟩
  linear_combination ha - q * hb + hdiv

/-- **Example 1.7.1 / 1.7.2** (§1.7, p.30–32): the squarefree factorization Yun's algorithm computes
for `A = x⁸ + 6x⁶ + 12x⁴ + 8x²` is `A = x²·(x²+2)³`. -/
theorem ex_1_7_1 :
    (X ^ 8 + 6 * X ^ 6 + 12 * X ^ 4 + 8 * X ^ 2 : ℚ[X]) = X ^ 2 * (X ^ 2 + 2) ^ 3 := by ring

/-- **Exercise 1.9** (§1, p.33): the squarefree factorization of `x⁸ − 5x⁶ + 6x⁴ + 4x² − 8` is
`(x²+1)·(x²−2)³` (squarefree parts `x²+1` at multiplicity 1, `x²−2` at multiplicity 3). -/
theorem ex_1_9 :
    (X ^ 8 - 5 * X ^ 6 + 6 * X ^ 4 + 4 * X ^ 2 - 8 : ℚ[X]) = (X ^ 2 + 1) * (X ^ 2 - 2) ^ 3 := by ring

/-- **Exercise 1.5** (§1, p.33): the pseudo-quotient and pseudo-remainder of `x⁴ − 7x + 7` by
`3x² − 7` in `ℤ[x]` are `9x² + 21` and `−189x + 336` — i.e. `3³·(x⁴ − 7x + 7) =
(3x² − 7)(9x² + 21) + (−189x + 336)` with the remainder of degree `< 2`. -/
theorem ex_1_5 :
    (27 : ℤ[X]) * (X ^ 4 - 7 * X + 7) = (3 * X ^ 2 - 7) * (9 * X ^ 2 + 21) + (-189 * X + 336)
      ∧ (-189 * X + 336 : ℤ[X]).natDegree < (3 * X ^ 2 - 7 : ℤ[X]).natDegree := by
  refine ⟨by ring, ?_⟩
  have h2 : (3 * X ^ 2 - 7 : ℤ[X]).natDegree = 2 := by compute_degree!
  rw [h2]; compute_degree!

/-- **Exercise 1.6** (§1, p.33): dividing `7x⁵ + 4x³ + 2x + 1` by `2x³ + 3`. Over the *fields*
`ℚ`, `ℤ/5`, `ℤ/11` the leading coefficient `2` is a unit, so this is ordinary division with a
remainder of degree `< 3`: `Q = (7/2)x²+2, R = −(21/2)x²+2x−5` over `ℚ`; `Q = x²+2, R = 2x²+2x`
over `ℤ/5`; `Q = 9x²+2, R = 6x²+2x+6` over `ℤ/11`. Over the *ring* `ℤ` the coefficient `2` is not
a unit, so only pseudo-division applies: `2³·A = (2x³+3)(28x²+16) + (−84x²+16x−40)`. -/
theorem ex_1_6 :
    ((7 * X ^ 5 + 4 * X ^ 3 + 2 * X + 1 : ℚ[X])
        = (2 * X ^ 3 + 3) * (C (7 / 2) * X ^ 2 + 2) + (-C (21 / 2) * X ^ 2 + 2 * X - 5)
      ∧ (-C (21 / 2) * X ^ 2 + 2 * X - 5 : ℚ[X]).natDegree < 3)
    ∧ ((7 * X ^ 5 + 4 * X ^ 3 + 2 * X + 1 : (ZMod 5)[X])
        = (2 * X ^ 3 + 3) * (X ^ 2 + 2) + (2 * X ^ 2 + 2 * X)
      ∧ (2 * X ^ 2 + 2 * X : (ZMod 5)[X]).natDegree < 3)
    ∧ ((7 * X ^ 5 + 4 * X ^ 3 + 2 * X + 1 : (ZMod 11)[X])
        = (2 * X ^ 3 + 3) * (9 * X ^ 2 + 2) + (6 * X ^ 2 + 2 * X + 6)
      ∧ (6 * X ^ 2 + 2 * X + 6 : (ZMod 11)[X]).natDegree < 3)
    ∧ ((8 : ℤ[X]) * (7 * X ^ 5 + 4 * X ^ 3 + 2 * X + 1)
        = (2 * X ^ 3 + 3) * (28 * X ^ 2 + 16) + (-84 * X ^ 2 + 16 * X - 40)
      ∧ (-84 * X ^ 2 + 16 * X - 40 : ℤ[X]).natDegree < 3) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply Polynomial.funext; intro x
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat, eval_neg,
      eval_one]; ring
  · compute_degree!
  · ring_nf; reduce_mod_char
  · compute_degree!
  · ring_nf; reduce_mod_char
  · compute_degree!
  · ring
  · compute_degree!

/-- **Example 1.2.1** (§1.2, p.9): the Euclidean division of `3x³ + x² + x + 5` by `5x² − 3x + 1`
in `ℚ[x]` (a field) gives quotient `(3/5)x + 14/25` and remainder `(52/25)x + 111/25`. -/
theorem ex_1_2_1 :
    (3 * X ^ 3 + X ^ 2 + X + 5 : ℚ[X])
        = (5 * X ^ 2 - 3 * X + 1) * (C (3 / 5) * X + C (14 / 25)) + (C (52 / 25) * X + C (111 / 25))
      ∧ (C (52 / 25) * X + C (111 / 25) : ℚ[X]).natDegree < 2 := by
  refine ⟨?_, ?_⟩
  · apply Polynomial.funext; intro x
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat, eval_one]; ring
  · compute_degree!

/-- **Example 1.2.2** (§1.2, p.9): pseudo-division of the same `A, B` over the *ring* `ℤ` (where
`lc(B) = 5` is not a unit) gives `5²·A = (5x² − 3x + 1)(15x + 14) + (52x + 111)` — pseudo-quotient
`15x + 14`, pseudo-remainder `52x + 111`. -/
theorem ex_1_2_2 :
    (25 : ℤ[X]) * (3 * X ^ 3 + X ^ 2 + X + 5)
        = (5 * X ^ 2 - 3 * X + 1) * (15 * X + 14) + (52 * X + 111)
      ∧ (52 * X + 111 : ℤ[X]).natDegree < 2 :=
  ⟨by ring, by compute_degree!⟩

/-- **Example 1.3.1** (§1.3, p.10): the Euclidean algorithm computes the gcd of
`x⁴ − 2x³ − 6x² + 12x + 15 = (x+1)(x³−3x²−3x+15)` and `x³ + x² − 4x − 4 = (x+1)(x²−4)` in `ℚ[x]`
as `5x + 5 ~ x + 1` (the cofactors `x³−3x²−3x+15` and `x²−4` are coprime, via Bézout
`−(x−3)(x³−3x²−3x+15) + (x²−6x+10)(x²−4) = 5`). -/
theorem ex_1_3_1 :
    Associated (gcd (X ^ 4 - 2*X^3 - 6*X^2 + 12*X + 15 : ℚ[X]) (X^3 + X^2 - 4*X - 4)) (X + 1) := by
  have hf : (X ^ 4 - 2*X^3 - 6*X^2 + 12*X + 15 : ℚ[X]) = (X + 1) * (X^3 - 3*X^2 - 3*X + 15) := by ring
  have hg : (X^3 + X^2 - 4*X - 4 : ℚ[X]) = (X + 1) * (X^2 - 4) := by ring
  have hcop : IsCoprime (X^3 - 3*X^2 - 3*X + 15 : ℚ[X]) (X^2 - 4) := by
    refine ⟨C (1/5) * (-(X - 3) : ℚ[X]), C (1/5) * (X^2 - 6*X + 10 : ℚ[X]), ?_⟩
    have hb : (-(X - 3) : ℚ[X]) * (X^3 - 3*X^2 - 3*X + 15) + (X^2 - 6*X + 10) * (X^2 - 4) = 5 := by
      ring
    calc C (1/5) * (-(X - 3) : ℚ[X]) * (X^3 - 3*X^2 - 3*X + 15)
          + C (1/5) * (X^2 - 6*X + 10 : ℚ[X]) * (X^2 - 4)
        = C (1/5) * ((-(X - 3) : ℚ[X]) * (X^3 - 3*X^2 - 3*X + 15) + (X^2 - 6*X + 10) * (X^2 - 4)) := by
          ring
      _ = C (1/5) * 5 := by rw [hb]
      _ = 1 := by rw [← map_ofNat C 5, ← C_mul]; norm_num
  have hu : IsUnit (gcd (X^3 - 3*X^2 - 3*X + 15 : ℚ[X]) (X^2 - 4)) :=
    hcop.isUnit_of_dvd' (gcd_dvd_left _ _) (gcd_dvd_right _ _)
  have hg1 : gcd (X^3 - 3*X^2 - 3*X + 15 : ℚ[X]) (X^2 - 4) = 1 :=
    (normalize_gcd _ _).symm.trans (normalize_eq_one.mpr hu)
  rw [hf, hg, gcd_mul_left, hg1, mul_one]
  exact normalize_associated _

/-- **Example 1.3.2** (§1.3, p.11): the *extended* Euclidean algorithm on the same `a, b` yields
the Bézout cofactors `s = −x + 3`, `t = x² − 6x + 10` with `s·a + t·b = 5x + 5` (equation 1.4). -/
theorem ex_1_3_2 :
    (-X + 3) * (X ^ 4 - 2*X^3 - 6*X^2 + 12*X + 15 : ℚ[X]) + (X^2 - 6*X + 10) * (X^3 + X^2 - 4*X - 4)
      = 5*X + 5 := by ring

/-- **Example 1.3.3** (§1.3, p.12): the *half*-extended Euclidean route recovers the second
cofactor by the exact division `t = (g − s·a)/b`. With `s = −x+3`, `g = 5x+5`, the dividend is
`g − s·a = x⁵ − 5x⁴ + 30x² − 16x − 40` (the book's printed value drops the `−40`), and dividing
by `b` is exact with quotient `t = x² − 6x + 10` — recovering equation 1.4. -/
theorem ex_1_3_3 :
    (5*X + 5 : ℚ[X]) - (-X + 3) * (X ^ 4 - 2*X^3 - 6*X^2 + 12*X + 15)
        = X^5 - 5*X^4 + 30*X^2 - 16*X - 40
      ∧ (5*X + 5 : ℚ[X]) - (-X + 3) * (X ^ 4 - 2*X^3 - 6*X^2 + 12*X + 15)
        = (X^2 - 6*X + 10) * (X^3 + X^2 - 4*X - 4) :=
  ⟨by ring, by ring⟩

/-- **Example 1.3.4** (§1.3, p.13): solving the diophantine equation `s·a + t·b = x² − 1` in `ℚ[x]`
(eq 1.6) for the `a, b` of Example 1.3.1 — scaling the gcd-Bézout by `(x−1)/5` gives
`s = (−x²+4x−3)/5` and `t = (x³−7x²+16x−10)/5`. -/
theorem ex_1_3_4 :
    C (1/5) * (-X^2 + 4*X - 3 : ℚ[X]) * (X ^ 4 - 2*X^3 - 6*X^2 + 12*X + 15)
        + C (1/5) * (X^3 - 7*X^2 + 16*X - 10 : ℚ[X]) * (X^3 + X^2 - 4*X - 4)
      = X^2 - 1 := by
  apply Polynomial.funext; intro x
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat, eval_neg,
    eval_one]; ring

/-- **Example 1.3.5** (§1.3, p.14): the *half*-extended diophantine route to `s·a + t·b = x² − 1`
(Example 1.3.4) — `s = (−x²+4x−3)/5`, then `c − s·a = (x⁶−6x⁵+5x⁴+30x³−46x²−24x+40)/5` divides by
`b` exactly with quotient `t = (x³−7x²+16x−10)/5`, recovering equation 1.6. -/
theorem ex_1_3_5 :
    (X^2 - 1 : ℚ[X]) - C (1/5) * (-X^2 + 4*X - 3) * (X^4 - 2*X^3 - 6*X^2 + 12*X + 15)
        = C (1/5) * (X^6 - 6*X^5 + 5*X^4 + 30*X^3 - 46*X^2 - 24*X + 40)
      ∧ (X^2 - 1 : ℚ[X]) - C (1/5) * (-X^2 + 4*X - 3) * (X^4 - 2*X^3 - 6*X^2 + 12*X + 15)
        = C (1/5) * (X^3 - 7*X^2 + 16*X - 10) * (X^3 + X^2 - 4*X - 4) := by
  refine ⟨?_, ?_⟩ <;>
  · apply Polynomial.funext; intro x
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat, eval_neg,
      eval_one]; ring

/-- **Example 1.3.7** (§1.3, p.17): the complete partial fraction decomposition of
`f = (x²+3x)/(x³−x²−x+1)` over `ℚ(x)`. The denominator factors as `(x+1)(x−1)²`, and
`f = −(1/2)/(x+1) + 2/(x−1)² + (3/2)/(x−1)` — equivalently, clearing denominators,
`x² + 3x = (−1/2)(x−1)² + 2(x+1) + (3/2)(x−1)(x+1)`. -/
theorem ex_1_3_7 :
    (X ^ 3 - X ^ 2 - X + 1 : ℚ[X]) = (X + 1) * (X - 1) ^ 2
      ∧ (X ^ 2 + 3 * X : ℚ[X])
        = C (-1/2) * (X - 1) ^ 2 + 2 * (X + 1) + C (3/2) * (X - 1) * (X + 1) := by
  refine ⟨by ring, ?_⟩
  apply Polynomial.funext; intro x
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat, eval_one]; ring

/-- **Exercise 1.4** (§1, p.33): the gcd of `2x³ − (19/5)x² − x + 6/5 = (x−2)(2x²+(1/5)x−3/5)` and
`x² + (1/3)x − 14/3 = (x−2)(x+7/3)` in `ℚ[x]` is `x − 2` (the cofactors `2x²+(1/5)x−3/5` and
`x+7/3` are coprime — they share no root). The fractional-coefficient identities are discharged
pointwise via `Polynomial.funext` (`ℚ` is infinite), then the `gcd_mul_left` reduction applies. -/
theorem ex_1_4 :
    Associated
      (gcd (2 * X ^ 3 - C (19 / 5) * X ^ 2 - X + C (6 / 5) : ℚ[X]) (X ^ 2 + C (1 / 3) * X - C (14 / 3)))
      (X - 2) := by
  have hf : (2 * X ^ 3 - C (19 / 5) * X ^ 2 - X + C (6 / 5) : ℚ[X])
      = (X - 2) * (2 * X ^ 2 + C (1 / 5) * X - C (3 / 5)) := by
    apply Polynomial.funext; intro x
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat]
    ring
  have hg : (X ^ 2 + C (1 / 3) * X - C (14 / 3) : ℚ[X]) = (X - 2) * (X + C (7 / 3)) := by
    apply Polynomial.funext; intro x
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat]
    ring
  have hcop : IsCoprime (2 * X ^ 2 + C (1 / 5) * X - C (3 / 5) : ℚ[X]) (X + C (7 / 3)) := by
    refine ⟨C (45 / 442), C (45 / 442) * (C (67 / 15) - 2 * X), ?_⟩
    apply Polynomial.funext; intro x
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat, eval_one]
    ring
  have hu : IsUnit (gcd (2 * X ^ 2 + C (1 / 5) * X - C (3 / 5) : ℚ[X]) (X + C (7 / 3))) :=
    hcop.isUnit_of_dvd' (gcd_dvd_left _ _) (gcd_dvd_right _ _)
  have hg1 : gcd (2 * X ^ 2 + C (1 / 5) * X - C (3 / 5) : ℚ[X]) (X + C (7 / 3)) = 1 :=
    (normalize_gcd _ _).symm.trans (normalize_eq_one.mpr hu)
  rw [hf, hg, gcd_mul_left, hg1, mul_one]
  exact normalize_associated _

/-- **Exercise 1.8** (§1, p.33): the gcd of `4x⁴ + 13x³ + 15x² + 7x + 1 = (x+1)³(4x+1)` and
`2x³ + x² − 4x − 3 = (x+1)²(2x−3)` in `ℚ[x]` is `(x+1)²` (the cofactors `(x+1)(4x+1)` and
`2x−3` are coprime, via Bézout `2·(x+1)(4x+1) + (−4x−11)(2x−3) = 35`). -/
theorem ex_1_8 :
    Associated
      (gcd (4 * X ^ 4 + 13 * X ^ 3 + 15 * X ^ 2 + 7 * X + 1 : ℚ[X]) (2 * X ^ 3 + X ^ 2 - 4 * X - 3))
      ((X + 1) ^ 2) := by
  have hf : (4 * X ^ 4 + 13 * X ^ 3 + 15 * X ^ 2 + 7 * X + 1 : ℚ[X])
      = (X + 1) ^ 2 * ((X + 1) * (4 * X + 1)) := by ring
  have hg : (2 * X ^ 3 + X ^ 2 - 4 * X - 3 : ℚ[X]) = (X + 1) ^ 2 * (2 * X - 3) := by ring
  have hcop : IsCoprime ((X + 1) * (4 * X + 1) : ℚ[X]) (2 * X - 3) := by
    refine ⟨C (1 / 35) * 2, C (1 / 35) * (-4 * X - 11), ?_⟩
    have hb : (2 : ℚ[X]) * ((X + 1) * (4 * X + 1)) + (-4 * X - 11) * (2 * X - 3) = 35 := by ring
    calc C (1 / 35) * 2 * ((X + 1) * (4 * X + 1)) + C (1 / 35) * (-4 * X - 11) * (2 * X - 3)
        = C (1 / 35) * ((2 : ℚ[X]) * ((X + 1) * (4 * X + 1)) + (-4 * X - 11) * (2 * X - 3)) := by ring
      _ = C (1 / 35) * 35 := by rw [hb]
      _ = 1 := by rw [← map_ofNat C 35, ← C_mul]; norm_num
  have hu : IsUnit (gcd ((X + 1) * (4 * X + 1) : ℚ[X]) (2 * X - 3)) :=
    hcop.isUnit_of_dvd' (gcd_dvd_left _ _) (gcd_dvd_right _ _)
  have hg1 : gcd ((X + 1) * (4 * X + 1) : ℚ[X]) (2 * X - 3) = 1 :=
    (normalize_gcd _ _).symm.trans (normalize_eq_one.mpr hu)
  rw [hf, hg, gcd_mul_left, hg1, mul_one]
  exact normalize_associated _

/-- **Exercise 1.3** (§1, p.33): the inverse of `14` in `ℤ/37` is `8` (i.e. `14·8 ≡ 1`). -/
theorem ex_1_3 : (14 : ZMod 37) * 8 = 1 := by decide

/-- **Exercise 1.12** (§1, p.33): in a commutative ring, if `a = q·b + r` then `a, b` and `b, r`
have the same gcds — `gcd(a, b) = gcd(b, r)` (the invariant driving the Euclidean algorithm). -/
theorem ex_1_12 {R : Type*} [CommRing R] {a b q r z : R} (h : a = q * b + r) :
    IsGCD a b z ↔ IsGCD b r z := by
  have hr : r = a - q * b := by rw [h]; ring
  constructor
  · intro hab
    refine ⟨hab.dvd_right, ?_, fun t htb htr => ?_⟩
    · rw [hr]; exact dvd_sub hab.dvd_left (hab.dvd_right.mul_left q)
    · exact hab.dvd (h.symm ▸ dvd_add (htb.mul_left q) htr) htb
  · intro hbr
    refine ⟨?_, hbr.dvd_left, fun t hta htb => ?_⟩
    · rw [h]; exact dvd_add (hbr.dvd_left.mul_left q) hbr.dvd_right
    · exact hbr.dvd htb (hr ▸ dvd_sub hta (htb.mul_left q))

/-- **Exercise 1.10** (§1, p.33): `2` is irreducible but **not prime** in `ℤ[√−5]` — the concrete
failure of "irreducible ⟹ prime". Irreducible since `N(2) = 4` (the helper for Ex 1.1.7); not
prime since `2 ∣ (1+√−5)(1−√−5) = 6` yet `2 ∤ 1±√−5` (else `N(2)=4 ∣ N(1±√−5)=6`). -/
theorem ex_1_10 : Irreducible (2 : Zsqrtd (-5)) ∧ ¬ Prime (2 : Zsqrtd (-5)) := by
  have h2 : (2 : Zsqrtd (-5)) = ⟨2, 0⟩ := by ext <;> simp
  have hn4 : (⟨2, 0⟩ : Zsqrtd (-5)).norm = 4 := by rw [Zsqrtd.norm_def]; norm_num
  refine ⟨h2 ▸ zsqrtNeg5_irreducible_of_norm _ (Or.inl hn4), fun hp => ?_⟩
  have hdvd : (2 : Zsqrtd (-5)) ∣ (⟨1, 1⟩ : Zsqrtd (-5)) * ⟨1, -1⟩ := by
    rw [h2]; exact ⟨⟨3, 0⟩, by ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]⟩
  have hn6p : (⟨1, 1⟩ : Zsqrtd (-5)).norm = 6 := by rw [Zsqrtd.norm_def]; norm_num
  have hn6m : (⟨1, -1⟩ : Zsqrtd (-5)).norm = 6 := by rw [Zsqrtd.norm_def]; norm_num
  rcases hp.2.2 _ _ hdvd with h | h <;> rw [h2] at h
  · exact absurd (hn4 ▸ hn6p ▸ zsqrtd_norm_dvd_norm h) (by decide)
  · exact absurd (hn4 ▸ hn6m ▸ zsqrtd_norm_dvd_norm h) (by decide)

/-- **Exercise 1.16** (§1, p.33): in a UFD, any two elements `x, y` have a least common multiple —
a common multiple dividing every common multiple (the `lcm` of the UFD's `GCDMonoid` structure). -/
theorem ex_1_16 {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R] (x y : R) :
    ∃ z, x ∣ z ∧ y ∣ z ∧ ∀ t, x ∣ t → y ∣ t → z ∣ t := by
  letI := UniqueFactorizationMonoid.toGCDMonoid R
  exact ⟨lcm x y, dvd_lcm_left x y, dvd_lcm_right x y, fun _ hx hy => lcm_dvd hx hy⟩

/-- **Exercise 1.15** (§1, p.33), Gauss's-lemma consequence: for `A` *primitive* and any `B` in
`D[x]` (`D` a UFD, `F = Frac(D)`), `A ∣ B` in `D[x]` iff `A ∣ B` in `F[x]`. Forward is
`map_dvd`; the converse reduces `B` to `content(B)·primPart(B)` — the content maps to a unit of
`F` — and applies Gauss's lemma to the two primitive polynomials `A, primPart(B)`. -/
theorem ex_1_15 {D K : Type*} [CommRing D] [IsDomain D] [NormalizedGCDMonoid D]
    [Field K] [Algebra D K] [IsFractionRing D K] {A B : D[X]} (hA : A.IsPrimitive) :
    A ∣ B ↔ A.map (algebraMap D K) ∣ B.map (algebraMap D K) := by
  refine ⟨fun h => map_dvd (Polynomial.mapRingHom (algebraMap D K)) h, fun h => ?_⟩
  rcases eq_or_ne B 0 with rfl | hB0
  · simp
  rw [← hA.dvd_primPart_iff_dvd hB0,
      hA.dvd_iff_fraction_map_dvd_fraction_map K B.isPrimitive_primPart]
  have hc : IsUnit (C (algebraMap D K B.content)) :=
    isUnit_C.mpr (Ne.isUnit (by
      simpa using (IsFractionRing.injective D K).ne (mt content_eq_zero_iff.mp hB0)))
  have hBeq : B.map (algebraMap D K)
      = C (algebraMap D K B.content) * (B.primPart).map (algebraMap D K) := by
    conv_lhs => rw [B.eq_C_content_mul_primPart]
    rw [Polynomial.map_mul, Polynomial.map_C]
  rwa [hBeq, hc.dvd_mul_left] at h

/- ## NOT YET FORMALIZED (audit 2026-06-21; subtractive — delete each item once it is formalized)
§1.4: Thm 1.4.3 — only the general scaling-factor case `σ(lc A)^(deg B − deg σ̄B)` (degrees
  lowered, subresultants of different sizes); the degree-preserving case is `thm_1_4_3`.
§1.5: Thm 1.5.2 [infra, in progress] (Fundamental PRS Theorem — the explicit subresultant↔PRS
  similarity coefficients ηᵢ/τᵢ of eq 1.9/1.10); Thm 1.5.3 [infra, in progress] (the
  subresultant-PRS specialization ηᵢ=1). Bronstein proves neither, citing [39 Ch.7], [60], [16 §7],
  [23]; built from Geddes–Czapor–Labahn [39] §7.3 Thm 7.4. Foundations DONE: scaling law
  `subresultant_C_mul`; the polynomial-column determinant form `subresultant_eq_det_polyCol`
  (eq 7.12); the row-reduction engines `det_updateCol_sum'`/`det_updateRow_add_sum_smul_self`; and
  BOTH halves of Lemma 7.1 in full: (a) ROW REDUCTION — `subresultant_add_monomial_mul` (single
  monomial `A + a·Xᵈ·B`, unipotent transvection `1 + a•P`), `subresultant_add_const_mul` (constant),
  `subresultant_add_mul` (`Sⱼ(A + B·p, B) = Sⱼ(A,B)`, any `p` with `deg p + m ≤ n`; `p = −Q` gives
  `Sⱼ(A,B) = Sⱼ(rem(A,B),B)`); (b) SWAP-WITH-SIGN — `subresultant_swap`
  (`Sⱼ(A,B) = (-1)^((m-j)(n-j))·Sⱼ(B,A)`), via the block-swap permutation `bSylvester_swap` +
  `bSylvester_submatrix_det_swap` whose sign is read off `(finRotate (n+m-2j))^(m-j)` (keystone
  `finRotate_pow_val`). Both halves combine in `subresultant_rem` (Lemma 7.1's engine): for a division
  step `A = Rem + B·Q`, `Sⱼ(A,B) = (-1)^((m-j)(n-j))·Sⱼ(B,Rem)`. The DEGREE PADDING is also DONE:
  `subresultant_pad_step`/`subresultant_padding` (`Sⱼ(B,Rem; m,n) = (lc B)^(n-k)·Sⱼ(B,Rem; m,k)`, by
  cofactor-expanding each `ⱼSᵢ` along its first column = `lc B · e₀`), assembled in `subresultant_rem_lt`
  = **Lemma 7.1 case `0≤j<k` complete**: `Sⱼ(A,B) = (-1)^((m-j)(n-j))·(lc B)^(n-k)·Sⱼ(B,Rem)` at `Rem`'s
  true degree `k`. Remaining: the degenerate cases `j=k`/`k<j<n-1`/`j=n-1` of Thm 7.4 (det becomes
  triangular → diagonal product) → Lemma 7.2 (=7.1 + scaling) → Thm 7.4 (iterate down the PRS).
§1.7: the Musser/Yun `Squarefree` algorithm. (Yun's `Yₖ` = `def_yun`; eq 1.17's derivative
  `d(A⁻⁽ⁱ⁻¹⁾) = A⁻ⁱ·Yᵢ` = `lem_1_7_2`; eq 1.18 `Yᵢ − d(A⁻⁽ⁱ⁻¹⁾)*/dx = Aᵢ·Y_{i+1}` = `lem_1_7_2_eq_18`;
  eq 1.17's gcd clause `gcd((A⁻⁽ⁱ⁻¹⁾)*, Yᵢ) ∈ K` (char-0 field) = `lem_1_7_2_eq_17_gcd`. Lemma 1.7.1 done.)
Examples: Ex 1.7.2 (the step-by-step Yun trace; the resulting factorization is `ex_1_7_1`).
Exercises: Ex 1.7. -/

end DeepWiki.Si
