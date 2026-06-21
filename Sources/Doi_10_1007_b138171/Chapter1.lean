import DeepWiki.SymbolicIntegration.AlgebraicPreliminaries
import DeepWiki.SymbolicIntegration.PseudoDivision
import DeepWiki.SymbolicIntegration.SquarefreeFactorization
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.Polynomial.UniqueFactorization
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

A few concrete worked examples that need substantial bespoke computation are deferred (noted
inline): the non-commutativity of `GL₂(ℚ)`/`M₂(ℚ)` (Ex 1.1.1, 1.1.3), the `ℤ[√−5]` facts (Ex 1.1.5
domain — Mathlib's `Nonsquare` is ℕ-keyed and does not resolve for `-5 : ℤ` — and the failure
of unique factorization / gcd, Ex 1.1.6, 1.1.7), and the non-principal ideal `(X,Y)`
(Ex 1.1.10). -/

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

-- **Theorem 1.1.10** (§1.1, p.8), the weak Nullstellensatz (`V(I) = ∅ ⟺ 1 ∈ I`), is deferred:
-- Mathlib's `MvPolynomial.zeroLocus` carries a separate points-field parameter, so the
-- specialized statement leaves `IsAlgClosed` instance metavariables. The book notes it (like the
-- strong form `thm_1_1_11`) is not needed by the integration algorithm.

/-! ### Worked examples (§1.1) -/

/-- **Example 1.1.2** (§1.1, p.2): the 2×2 rational matrices form a commutative group under
addition. -/
example : AddCommGroup (Matrix (Fin 2) (Fin 2) ℚ) := inferInstance

/-- **Example 1.1.4** (§1.1, p.3): `ℤ₆ = ZMod 6` is a commutative ring of characteristic `6`
with zero divisors — `2 · 3 = 0` while `2 ≠ 0` and `3 ≠ 0`. -/
example : CharP (ZMod 6) 6 := inferInstance

/-- **Example 1.1.4**: the zero divisors of `ℤ₆`. -/
theorem ex_1_1_4_zero_divisors :
    (2 : ZMod 6) * 3 = 0 ∧ (2 : ZMod 6) ≠ 0 ∧ (3 : ZMod 6) ≠ 0 := by decide

/-- **Example 1.1.8** (§1.1, p.4): `ℚ[X, Y]` (here `ℚ[X][Y]`) is a unique factorization
domain. -/
example : UniqueFactorizationMonoid (Polynomial (Polynomial ℚ)) := inferInstance

/-- **Example 1.1.9** (§1.1, p.5): `SL₂(ℚ)` embeds in `GL₂(ℚ)` (a subgroup) via the injective
group homomorphism `toGL`. -/
example : Function.Injective (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := ℚ)) :=
  Matrix.SpecialLinearGroup.toGL_injective

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

/-! ## §1.7 Squarefree Factorization -/

/-- **Definition 1.7.1** (§1.7, p.28): `A` is *squarefree* if no non-unit `B` satisfies
`B² ∣ A`. -/
abbrev def_1_7_1 := @Squarefree

-- **Deferred — `DeepWiki.SymbolicIntegration` library work (not in Mathlib), to be built in
-- dedicated iterations:**
--   • §1.4 the subresultant PRS (`Polynomial.resultant` IS in Mathlib; the subresultant
--     sequence and Cor 1.4.1/1.4.2 linking it to the resultant are not).
--   • §1.5 polynomial remainder sequences (Examples 1.5.1/1.5.2).
--   • §1.6 the deflation theory — squarefree part `A*`, `k`-deflations `A⁻ᵏ` (Def 1.6.2),
--     relations (1.11)–(1.14), and Theorem 1.6.1(ii) — the char-`0` converse
--     (`Pⁿ ∣ gcd(A, dA/dx) ⟹ Pⁿ⁺¹ ∣ A`) and eq (1.14) `A⁻ = gcd(A, dA/dx)`.
--     [Theorem 1.6.1(i) is done — `thm_1_6_1_i`.]
--   • §1.7 squarefree factorization (Def 1.7.2), Lemmas 1.7.1/1.7.2, and the Musser/Yun
--     `Squarefree` algorithm (Example 1.7.1) — the squarefree-factorization routine the
--     integration algorithm uses.

end DeepWiki.Si
