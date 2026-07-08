import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.AutoReduction
import DeepWiki.SymbolicIntegration.Core.Polynomial.Groebner.ReducedBasis.Minimize

/-! # Existence of reduced Gröbner bases

Assembles monicization, minimization, and auto-reduction into a finite reduced
Gröbner basis existence theorem.
-/

open MvPolynomial MonomialOrder

namespace DeepWiki.SymbolicIntegration

variable {σ : Type*} {m : MonomialOrder σ} {R : Type*} [CommRing R]

/-- Over a field with finitely many variables, every ideal `I` has a finite reduced Gröbner basis. -/
theorem exists_isReducedGroebnerBasis {σ K : Type*} [Finite σ] [Field K] (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ K)) :
    ∃ B : Finset (MvPolynomial σ K), IsReducedGroebnerBasis m I (↑B : Set (MvPolynomial σ K)) := by
  classical
  -- Step 0: a Gröbner basis exists.
  obtain ⟨B₀, hB₀⟩ := exists_isGroebnerBasis m I
  -- Step 1: monicize it.
  obtain ⟨hB₁, hmonic₁⟩ := isGroebnerBasis_monicize hB₀
  -- Step 2: minimize it (monic GB with pairwise non-dividing leading monomials).
  obtain ⟨hB₂, hmonic₂, hpair₂⟩ := isGroebnerBasis_minimize hB₁ hmonic₁
  -- Step 3: auto-reduce, yielding a reduced Gröbner basis.
  have hBu₂ : ∀ b ∈ minimize m (monicize m B₀), IsUnit (m.leadingCoeff b) :=
    fun b hb => by rw [hmonic₂ b (Finset.mem_coe.mpr hb)]; exact isUnit_one
  exact ⟨autoReduce m hBu₂, isReducedGroebnerBasis_autoReduce hBu₂ hB₂ hmonic₂ hpair₂⟩

end DeepWiki.SymbolicIntegration
