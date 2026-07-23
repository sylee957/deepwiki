import Mathlib.RingTheory.Nullstellensatz

/-! # Nullstellensatz transfer for polynomial systems

Transfer of polynomial-system solvability from a field extension to an algebraically closed base.
-/

namespace DeepWiki

section SystemTransfer

/-- Over an algebraically closed constant field `C`, a polynomial system `S`, `g` with coefficients
in `C` satisfied by an `E`-point (`f(c) = 0` for `f ∈ S`, `g(c) ≠ 0`) is satisfied by a `C`-point. -/
theorem exists_base_point_of_exists_extension_point {C E : Type*} [Field C] [Field E]
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

end DeepWiki
