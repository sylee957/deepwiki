import DeepWiki.SymbolicIntegration.AlgebraicConstants
import DeepWiki.SymbolicIntegration.DifferentialExtensions

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

end DeepWiki.SymbolicIntegration
