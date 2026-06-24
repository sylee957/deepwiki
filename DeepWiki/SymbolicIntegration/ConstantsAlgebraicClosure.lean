import DeepWiki.SymbolicIntegration.AlgebraicConstants
import DeepWiki.SymbolicIntegration.DifferentialExtensions
import Mathlib.RingTheory.Nullstellensatz

/-! # Constants of algebraic and rational extensions (Bronstein §3.3)
The constants of a separable algebraic differential extension are exactly the algebraic closure
of the initial constant field (Corollary 3.3.1), the constant field is preserved when passing to
algebraic closures of a perfect base (Lemma 3.3.3), the constants of a transcendental extension
`F(t)` adjoin only the new constant `t` (Lemma 3.3.4), and over an algebraically-closed constant
field a polynomial system solvable by constants of the extension is already solvable by constants
of the base (Lemma 3.3.6). -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section AlgebraicClosureConstants
variable {F E : Type*} [Field F] [Field E] [Differential F] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E]

/-- `IsAlgebraicOverConst c` : the element `c ∈ E` is algebraic over the constants — a root of a
nonzero polynomial in `E[X]` all of whose coefficients are constants (so the polynomial lies in
`Const_Δ(E)[X]`, in particular over the image of `Const_D F`). -/
def IsAlgebraicOverConst (c : E) : Prop :=
  ∃ q : E[X], q ≠ 0 ∧ (∀ i, (q.coeff i)′ = 0) ∧ q.eval c = 0

/-- **Corollary 3.3.1** (§3.3), forward inclusion `Const_Δ(E) ⊆ C̄ᴱ`: in a separable algebraic
differential extension, every constant of `E` is algebraic over the constants. (It is algebraic
over `F` since `E/F` is algebraic, then Lemma 3.3.2(i) lifts the witness to constant
coefficients.) -/
theorem isAlgebraicOverConst_of_deriv_eq_zero_of_integral {c : E} (hc : c′ = 0)
    (hint : IsIntegral F c) : IsAlgebraicOverConst c :=
  isAlgebraicOverConst_of_deriv_eq_zero hc hint

/-- **Corollary 3.3.1** (§3.3), backward inclusion `C̄ᴱ ⊆ Const_Δ(E)`: an element that is a root of
a *separable* (`q'(c) ≠ 0`) nonzero polynomial with constant coefficients is itself a constant.
(Lemma 3.3.2(ii): differentiate `q(c) = 0` to get `q'(c)·c′ = 0`, then cancel `q'(c)`.) -/
theorem deriv_eq_zero_of_isAlgebraicOverConst {c : E} (q : E[X]) (hq : ∀ i, (q.coeff i)′ = 0)
    (hroot : q.eval c = 0) (hsep : q.derivative.eval c ≠ 0) : c′ = 0 :=
  deriv_eq_zero_of_separable_algebraic_const q hq hroot hsep

/-- **Corollary 3.3.1** (§3.3), the constant-field characterisation `Const_Δ(E) = C̄ᴱ`: in char `0`
a constant of `E` is exactly an element that is a root of a *separable* nonzero polynomial with
constant coefficients. Forward — the minimal polynomial of `c` over `F` (separable in char `0`),
mapped into `E[X]`, has constant coefficients (Lemma 3.3.2(i)) and a nonvanishing derivative at
`c`. Backward — a separable algebraic constant is a constant (Lemma 3.3.2(ii)). -/
theorem deriv_eq_zero_iff_isAlgebraicOverConst_separable [CharZero F] {c : E}
    (hint : IsIntegral F c) :
    c′ = 0 ↔ ∃ q : E[X], q ≠ 0 ∧ (∀ i, (q.coeff i)′ = 0) ∧ q.eval c = 0 ∧
      q.derivative.eval c ≠ 0 := by
  constructor
  · intro hc
    set p := minpoly F c with hpdef
    have hsep : p.Separable := (minpoly.irreducible hint).separable
    have hconst : ∀ i, ((p.map (algebraMap F E)).coeff i)′ = 0 := by
      intro i
      rw [Polynomial.coeff_map, deriv_algebraMap]
      have hmc0 : (Differential.mapCoeffs p) = 0 := by
        have hkappa : Polynomial.aeval c (Differential.mapCoeffs p) = 0 := by
          have hchain := Differential.deriv_aeval_eq (A := F) (R := E) c p
          rw [minpoly.aeval, map_zero, hc, mul_zero, add_zero] at hchain
          exact hchain.symm
        by_contra hne
        have hle := minpoly.degree_le_of_ne_zero F c hne hkappa
        rw [← hpdef] at hle
        exact absurd (lt_of_le_of_lt hle (degree_mapCoeffs_lt (minpoly.monic hint)))
          (lt_irrefl _)
      have hci : (p.coeff i)′ = 0 := by
        have := congrArg (fun r => Polynomial.coeff r i) hmc0
        rwa [Differential.coeff_mapCoeffs, Polynomial.coeff_zero] at this
      rw [hci, map_zero]
    refine ⟨p.map (algebraMap F E), ?_, hconst, ?_, ?_⟩
    · rw [Ne, Polynomial.map_eq_zero_iff (algebraMap F E).injective]
      exact (minpoly.monic hint).ne_zero
    · rw [Polynomial.eval_map, ← Polynomial.aeval_def, minpoly.aeval]
    · rw [Polynomial.derivative_map, Polynomial.eval_map, ← Polynomial.aeval_def]
      exact hsep.aeval_derivative_ne_zero (minpoly.aeval F c)
  · rintro ⟨q, _, hq, hroot, hsep⟩
    exact deriv_eq_zero_of_isAlgebraicOverConst q hq hroot hsep

end AlgebraicClosureConstants

section RationalExtensionConstants
variable {F : Type*} [Field F] [Differential F]

/-- On `F[t]` (`t` transcendental, `Δt = 0`) the extended derivation is the coefficient map
`κ_D = mapCoeffs`. The constant-`u/v` step of Lemma 3.3.4: a coprime pair `u, v` with `v` monic and
`v·κ_D(u) = u·κ_D(v)` (the `vΔu = uΔv` relation extracted from `Δ(u/v) = 0`) forces both `κ_D(u)`
and `κ_D(v)` to vanish — i.e. `u, v ∈ Const_D(F)[t]`. (Coprimality gives `v ∣ κ_D(v)`, but
`deg κ_D(v) < deg v`, so `κ_D(v) = 0`, then `v ≠ 0` cancels to `κ_D(u) = 0`.) -/
theorem mapCoeffs_eq_zero_of_coprime_of_relation {u v : F[X]} (hcop : IsCoprime u v)
    (hv : v.Monic) (hrel : v * Differential.mapCoeffs u = u * Differential.mapCoeffs v) :
    Differential.mapCoeffs u = 0 ∧ Differential.mapCoeffs v = 0 := by
  -- `v ∣ u · κ_D(v)` since it equals `v · κ_D(u)`; coprimality gives `v ∣ κ_D(v)`.
  have hdvd : v ∣ Differential.mapCoeffs v :=
    hcop.symm.dvd_of_dvd_mul_left ⟨Differential.mapCoeffs u, hrel.symm⟩
  -- but `deg κ_D(v) < deg v`, so `κ_D(v) = 0`.
  have hv0 : Differential.mapCoeffs v = 0 :=
    eq_zero_of_dvd_of_degree_lt hdvd (degree_mapCoeffs_lt hv)
  -- then `v · κ_D(u) = 0`, and `v ≠ 0`, so `κ_D(u) = 0`.
  have hu0 : Differential.mapCoeffs u = 0 := by
    have : v * Differential.mapCoeffs u = 0 := by rw [hrel, hv0, mul_zero]
    exact (mul_eq_zero.mp this).resolve_left hv.ne_zero
  exact ⟨hu0, hv0⟩

/-- **Lemma 3.3.4** (§3.3), hard inclusion `Const_Δ(F(t)) ⊆ Const_D(F)(t)`, the transcendental
core: with `t` transcendental (`Δt = 0`), a constant `c = u/v ∈ F(t)` in lowest terms (`u, v`
coprime, `v` monic) has *both* numerator and denominator with constant coefficients —
`∀ i, (u.coeff i)′ = 0` and `∀ i, (v.coeff i)′ = 0`. So `c ∈ Const_D(F)(t)`. The relation
`hrel : v·κ_D(u) = u·κ_D(v)` is the `vΔu = uΔv` obtained from `Δ(u/v) = (vΔu − uΔv)/v² = 0`. -/
theorem coeff_deriv_eq_zero_of_coprime_of_relation {u v : F[X]} (hcop : IsCoprime u v)
    (hv : v.Monic) (hrel : v * Differential.mapCoeffs u = u * Differential.mapCoeffs v) :
    (∀ i, (u.coeff i)′ = 0) ∧ (∀ i, (v.coeff i)′ = 0) := by
  obtain ⟨hu0, hv0⟩ := mapCoeffs_eq_zero_of_coprime_of_relation hcop hv hrel
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := congrArg (fun r => Polynomial.coeff r i) hu0
    rwa [Differential.coeff_mapCoeffs, Polynomial.coeff_zero] at this
  · have := congrArg (fun r => Polynomial.coeff r i) hv0
    rwa [Differential.coeff_mapCoeffs, Polynomial.coeff_zero] at this

end RationalExtensionConstants

section AlgebraicallyClosedConstants
variable {E : Type*} [Field E] [Differential E] [CharZero E]

/-- The constant subfield inherits characteristic `0` from `E` (its subtype injection preserves and
reflects `natCast`). -/
instance charZero_constantsSubfield : CharZero (constantsSubfield E) where
  cast_injective m n h := by
    have hι := (constantsSubfield E).subtype.injective
    apply Nat.cast_injective (R := E)
    have := congrArg (constantsSubfield E).subtype h
    rwa [map_natCast, map_natCast] at this

/-- **Corollary 3.3.1** (§3.3), the algebraically-closed clause `Const_Δ(E) = C̄` (and the core of
Lemma 3.3.3): when `E` is an algebraically closed char-`0` differential field, its constant subfield
`Const_D(E)` is itself algebraically closed. (A monic irreducible polynomial over the constants —
separable in char `0` — has a root `c ∈ E`; its constant coefficients make `c` a separable algebraic
constant, so `c′ = 0` by Lemma 3.3.2(ii), i.e. the root already lies in the constant subfield.) -/
instance isAlgClosed_constantsSubfield [IsAlgClosed E] :
    IsAlgClosed (constantsSubfield E) := by
  apply IsAlgClosed.of_exists_root
  intro p hpmonic hpirr
  set ι : (constantsSubfield E) →+* E := (constantsSubfield E).subtype with hι
  set q : E[X] := p.map ι with hqdef
  -- `q`'s coefficients are constants (they are images of elements of `constantsSubfield E`).
  have hqconst : ∀ i, (q.coeff i)′ = 0 := by
    intro i
    rw [hqdef, Polynomial.coeff_map]
    exact (p.coeff i).property
  -- `q ≠ 0` and `deg q ≥ 1`, so it has a root `c ∈ E`.
  have hq0 : q ≠ 0 := by
    rw [hqdef, Ne, Polynomial.map_eq_zero_iff ι.injective]; exact hpmonic.ne_zero
  have hpsep : p.Separable := hpirr.separable
  have hdegq : q.degree ≠ 0 := by
    rw [hqdef, Polynomial.degree_map_eq_of_injective ι.injective]
    exact (Polynomial.degree_pos_of_irreducible hpirr).ne'
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root q hdegq
  -- `q = p.map ι` is separable (char `0` irreducible `p`), so its derivative is nonzero at `c`.
  have hqsep : q.Separable := hpsep.map
  have hroot : q.eval c = 0 := hc
  have hsep : q.derivative.eval c ≠ 0 := by
    have := hqsep.eval₂_derivative_ne_zero (RingHom.id E) (x := c)
      (by rwa [Polynomial.eval₂_id])
    rwa [Polynomial.eval₂_id] at this
  -- the root is a constant (Lemma 3.3.2(ii)), so it lies in the constant subfield.
  have hcconst : c′ = 0 := deriv_eq_zero_of_separable_algebraic_const q hqconst hroot hsep
  refine ⟨⟨c, hcconst⟩, ?_⟩
  -- `p.eval ⟨c, _⟩ = 0` because `ι` is injective and `ι (p.eval ⟨c,_⟩) = q.eval c = 0`.
  apply ι.injective
  rw [map_zero, hι, ← Polynomial.eval₂_at_apply, Polynomial.eval₂_eq_eval_map, ← hqdef]
  exact hroot

end AlgebraicallyClosedConstants

section SystemTransfer

/-- **Lemma 3.3.6** (§3.3), the post-reduction Nullstellensatz transfer: over an algebraically
closed constant field `C = Const_D(F)`, a polynomial system with *constant* coefficients
(`S, g ⊆ C[X₁,…,Xₘ]`) that is satisfied by a point `c` whose coordinates are constants of a
differential extension `E` (`f(c) = 0` for all `f ∈ S`, `g(c) ≠ 0`) is already satisfied by a point
`a` with coordinates in `C` itself. (If `g` lay in the radical of `⟨S⟩`, then `gⁿ ∈ ⟨S⟩` for some
`n`, so `g(c)ⁿ = 0` — impossible; hence by Hilbert's Nullstellensatz over the algebraically closed
`C`, `g` does not vanish on the whole zero locus, giving the required `C`-point. The book's full
statement first uses a `C`-basis of `F` and Corollary 3.3.2 to reduce arbitrary `F[X]`-coefficients
to this constant-coefficient case.) -/
theorem exists_const_point_of_exists_extension_point {C E : Type*} [Field C] [Field E]
    [Algebra C E] [IsAlgClosed C] {σ : Type*} [Finite σ] (S : Set (MvPolynomial σ C))
    (g : MvPolynomial σ C) (c : σ → E) (hf : ∀ f ∈ S, MvPolynomial.aeval c f = 0)
    (hg : MvPolynomial.aeval c g ≠ 0) :
    ∃ a : σ → C, (∀ f ∈ S, MvPolynomial.aeval a f = 0) ∧ MvPolynomial.aeval a g ≠ 0 := by
  -- `g ∉ radical ⟨S⟩`: otherwise `gⁿ ∈ ⟨S⟩` evaluates to `0` at `c`, so `g(c)ⁿ = 0`.
  have hgrad : g ∉ (Ideal.span S).radical := by
    rw [Ideal.mem_radical_iff]
    rintro ⟨n, hn⟩
    have hzero : MvPolynomial.aeval c (g ^ n) = 0 := by
      refine Submodule.span_induction (p := fun x _ => MvPolynomial.aeval c x = 0)
        (fun f hf' => hf f hf') (by simp) (fun x y _ _ hx hy => by simp [hx, hy])
        (fun r x _ hx => by simp [hx]) hn
    rw [map_pow, pow_eq_zero_iff'] at hzero
    exact hg hzero.1
  -- strong Nullstellensatz over the algebraically closed `C`: `g` is not in the vanishing ideal of
  -- the zero locus, so it does not vanish at some `C`-point of the locus.
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := C)] at hgrad
  rw [MvPolynomial.mem_vanishingIdeal_iff] at hgrad
  push Not at hgrad
  obtain ⟨a, ha, hga⟩ := hgrad
  refine ⟨a, fun f hf' => ?_, hga⟩
  exact ha f (Ideal.subset_span hf')

end SystemTransfer

end DeepWiki.SymbolicIntegration
