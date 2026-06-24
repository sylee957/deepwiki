import DeepWiki.SymbolicIntegration.SpecialFirstKind

/-! # Constants of a monomial extension and base change (Bronstein §3.4)
For a monomial `t` over `(k, D)` (so `Dt = v ∈ k[t]`), this file relates the *constants* of
`k(t)` to the *special* polynomials. When `Dt ∈ k` a nonzero `p ∈ k[t]` is special iff its monic
associate is a constant (`isSpecial_iff_deriv_monic_eq_zero`); this is the engine behind the fact
that any new constant in `k(t) ∖ k` makes `Sⁱʳʳ` nonempty. We also complete the base-change
corollary (normal polynomials stay normal under an algebraic extension `k ⊆ E`), and record the
constant-field case `Da = 0`. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {k : Type*} [Field k] [Differential k]

section ScalarMonomial
-- The base case of §3.4: the monomial derivation with `Dt = w ∈ k`, i.e. the implicit derivation
-- whose `t`-component is the *constant* polynomial `C w`.
variable (w : k)

/-- For the monomial derivation with `Dt = w ∈ k` (so `D = κ_D + w·d/dt`), the `t`-component does
not raise degree: `deg(Dp) ≤ deg p` (`κ_D` preserves degree shape; `w·dp/dt` drops a degree). -/
theorem natDegree_implicitDeriv_C_le (p : k[X]) :
    (Differential.implicitDeriv (C w) p).natDegree ≤ p.natDegree := by
  refine (natDegree_implicitDeriv_le (C w) p).trans ?_
  rw [natDegree_C]; simp

/-- The top coefficient of `Dp` is `D(lc p)`: when `Dt = w ∈ k`, the degree-`deg p` coefficient of
`Differential.implicitDeriv (C w) p` is the derivative of the leading coefficient of `p`. -/
theorem coeff_natDegree_implicitDeriv_C (p : k[X]) :
    (Differential.implicitDeriv (C w) p).coeff p.natDegree = (p.coeff p.natDegree)′ := by
  have happly : Differential.implicitDeriv (C w) p
      = Differential.mapCoeffs p + C w * derivative p := by
    simp [Differential.implicitDeriv, derivative']
  rw [happly, coeff_add, Differential.coeff_mapCoeffs, coeff_C_mul]
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | h0
  · rw [h0, eq_C_of_natDegree_eq_zero h0, derivative_C, coeff_zero, mul_zero, add_zero, coeff_C,
      if_pos rfl]
  · have hd : (derivative p).coeff p.natDegree = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_derivative_le p) (by omega))
    rw [hd, mul_zero, add_zero]

end ScalarMonomial

/-- For the monomial derivation with `Dt = w ∈ k`, a *monic* polynomial has `deg(Dq) < deg q`
unless `Dq = 0` (the top coefficient `D(lc q) = D(1) = 0`). -/
theorem deriv_monic_eq_zero_or_natDegree_lt {w : k} {q : k[X]} (hq : q.Monic) :
    Differential.implicitDeriv (C w) q = 0
      ∨ (Differential.implicitDeriv (C w) q).natDegree < q.natDegree := by
  by_cases h0 : Differential.implicitDeriv (C w) q = 0
  · exact Or.inl h0
  · refine Or.inr (lt_of_le_of_ne (natDegree_implicitDeriv_C_le w q) ?_)
    intro heq
    have htop : (Differential.implicitDeriv (C w) q).coeff
        (Differential.implicitDeriv (C w) q).natDegree = 0 := by
      rw [heq, coeff_natDegree_implicitDeriv_C, hq.coeff_natDegree,
        (Differential.deriv : Derivation ℤ k k).map_one_eq_zero]
    exact (mt leadingCoeff_eq_zero.mp h0) htop

/-- **Constants vs special, monic-associate form** (§3.4, p.96): with `Dt = w ∈ k`, a *monic*
`q ∈ k[t]` is special iff it is a constant of `k(t)` — `q ∣ Dq ⟺ Dq = 0`. (Forward: `q ∣ Dq` and
`deg(Dq) < deg q` force `Dq = 0`; backward: `Dq = 0 ⟹ q ∣ Dq`.) -/
theorem isSpecial_iff_deriv_eq_zero_of_monic {w : k} {q : k[X]} (hq : q.Monic) :
    q ∣ Differential.implicitDeriv (C w) q ↔ Differential.implicitDeriv (C w) q = 0 := by
  constructor
  · intro hdvd
    rcases deriv_monic_eq_zero_or_natDegree_lt hq with h | hlt
    · exact h
    · by_contra hne
      exact absurd (natDegree_le_of_dvd hdvd hne) (by omega)
  · intro h; rw [h]; exact dvd_zero q

omit [Differential k] in
/-- The monic normalization `p/lc(p)` of a nonzero `p` is an associate of `p` and monic. -/
theorem associated_mul_C_inv_leadingCoeff {p : k[X]} (hp : p ≠ 0) :
    Associated p (p * C p.leadingCoeff⁻¹) ∧ (p * C p.leadingCoeff⁻¹).Monic := by
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  refine ⟨(associated_mul_unit_right p _ (isUnit_C.mpr (Ne.isUnit (inv_ne_zero hlc)))),
    monic_mul_C_of_leadingCoeff_mul_eq_one (mul_inv_cancel₀ hlc)⟩

/-- **Constants and special polynomials** (§3.4, p.96, Lemma 3.4.6): when `Dt ∈ k`, a nonzero
`p ∈ k[t]` is special iff its monic normalization `p/lc(p)` is a constant of `k(t)` —
`p ∣ Dp ⟺ D(p/lc(p)) = 0`. (Specialness is an associate invariant, reducing to the monic case
`isSpecial_iff_deriv_eq_zero_of_monic`.) -/
theorem isSpecial_iff_deriv_normalize_eq_zero {w : k} {p : k[X]} (hp : p ≠ 0) :
    p ∣ Differential.implicitDeriv (C w) p
      ↔ Differential.implicitDeriv (C w) (p * C p.leadingCoeff⁻¹) = 0 := by
  letI : Differential k[X] := ⟨Differential.implicitDeriv (C w)⟩
  obtain ⟨hassoc, hmonic⟩ := associated_mul_C_inv_leadingCoeff hp
  rw [← isSpecial_iff_deriv_eq_zero_of_monic hmonic]
  exact ⟨fun h => IsSpecial.of_associated hassoc h, fun h => IsSpecial.of_associated hassoc.symm h⟩

section AlgebraicExtension
-- `E` an algebraic differential extension of `k`. The *special half* of base change
-- (`isSpecial_map_of_isSpecial`) lives in `SpecialFirstKind`; here is the *normal half*.
variable {E : Type*} [Field E] [Differential E] [Algebra k E] [DifferentialAlgebra k E]

/-- **Corollary 3.4.1** (§3.4, p.95), normal half: a normal polynomial stays normal after an
algebraic base change — `IsCoprime p (Dp)` in `k[t]` gives `IsCoprime (p.map) (D(p.map))` in `E[t]`
(coprimality lifts along the ring hom `map`, and `D` commutes with `map` via `implicitDeriv_map`).
Combined with `isSpecial_map_of_isSpecial`, normal and special polynomials remain such over `E`. -/
theorem isCoprime_map_implicitDeriv_of_isCoprime {v p : k[X]}
    (hp : IsCoprime p (Differential.implicitDeriv v p)) :
    IsCoprime (p.map (algebraMap k E))
      (Differential.implicitDeriv (v.map (algebraMap k E)) (p.map (algebraMap k E))) := by
  rw [← implicitDeriv_map]
  have := hp.map (Polynomial.mapRingHom (algebraMap k E))
  simpa only [coe_mapRingHom] using this

end AlgebraicExtension

end DeepWiki.SymbolicIntegration
