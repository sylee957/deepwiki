import DeepWiki.SymbolicIntegration.AlgebraicPreliminaries
import DeepWiki.SymbolicIntegration.PseudoDivision
import DeepWiki.SymbolicIntegration.SquarefreeFactorization
import DeepWiki.SymbolicIntegration.MonomialExtensions
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
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
predicate, e.g. `IsGCD`). The book numbering lives here in the catalog, never in the library.

All of §1.1 — including the `ℤ[√−5]` and matrix examples — is now formalized. -/

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

-- **Deferred — not in Mathlib (library work):** Theorem 1.4.2 (`res ∈ (A,B)`, i.e.
-- `res = SA + TB`), and the entire *subresultant* theory: Definition 1.4.2 (`Sⱼ(A,B)` from
-- Sylvester submatrices), Theorem 1.4.3 (subresultant specialization under ring homomorphisms),
-- and §1.5 polynomial remainder sequences.

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

/-! ## §1.7 Squarefree Factorization -/

/-- **Definition 1.7.1** (§1.7, p.28): `A` is *squarefree* if no non-unit `B` satisfies
`B² ∣ A`. -/
abbrev def_1_7_1 := @Squarefree

/-- **Lemma 1.7.1** (§1.7, p.29): over a characteristic-`0` field, `A` is squarefree iff
`gcd(A, dA/dx) = 1` — i.e. `A` and its derivative are coprime. -/
theorem lem_1_7_1 {K : Type*} [Field K] [CharZero K] {A : K[X]} :
    Squarefree A ↔ IsCoprime A (derivative A) :=
  squarefree_iff_isCoprime_derivative

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

-- **Deferred — `DeepWiki.SymbolicIntegration` library work (not in Mathlib), to be built in
-- dedicated iterations:**
--   • §1.4 the subresultant PRS (`Polynomial.resultant` IS in Mathlib; the subresultant
--     sequence Sⱼ and its specialization theorem are not).
--   • §1.5 polynomial remainder sequences (Examples 1.5.1/1.5.2).
--   • §1.6 the deflation theory — squarefree part `A*`, `k`-deflations `A⁻ᵏ` (Def 1.6.2),
--     relations (1.11)–(1.13), and eq (1.14) `A⁻ = gcd(A, dA/dx)` (needs the `A⁻` definition).
--     [Theorem 1.6.1 — both parts and the combined iff — is done: `thm_1_6_1_i`/`_ii`/`thm_1_6_1`.]
--   • §1.7 squarefree factorization (Def 1.7.2), Lemma 1.7.2, and the Musser/Yun
--     `Squarefree` algorithm (Example 1.7.1) — the squarefree-factorization routine the
--     integration algorithm uses. [Lemma 1.7.1 is done: `lem_1_7_1`.]

end DeepWiki.Si
