import DeepWiki.SymbolicIntegration.Core.Polynomial.LocalPrincipalAssembly
import DeepWiki.SymbolicIntegration.Core.Polynomial.LocalPrincipalDerivatives
import DeepWiki.SymbolicIntegration.Core.Polynomial.LocalPrincipalUniqueness
import DeepWiki.SymbolicIntegration.LaurentCoefficients.RootBridge

/-! # Laurent coefficient assembly

Engine-form partial-fraction assembly for Laurent coefficients. -/


open Polynomial MvPolynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ## The coefficient bridge chained to the engine: `localCoeff = Hᵢ,(i−d)(α)` -/

/-- `hFracα A Ei Diα i = algebraMap A / algebraMap (lDenomα Ei Diα i 0)`. -/
theorem hFracα_eq_div_lDenomα (A Ei Diα : K[X]) (i : ℕ) :
    hFracα A Ei Diα i
      = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i 0) := rfl

/-- The coefficient bridge chained to the engine: at a root `α` of `Dᵢ = (x−α)·Dᵢ,α`, with `M = Dᵢ,α^i·Eᵢ`
and `d < i`, `localCoeff A M α i d = (laurentH A D Di i (i−d)).eval α`. -/
theorem localCoeff_eq_laurentH [CharZero K] (A D Di Diα : K[X]) {α : K} (i d : ℕ)
    (hi : 0 < i) (hd : d < i) (hroot : IsLaurentRegularRoot D Di Diα α i) :
    localCoeff A (lDenomα (laurentE D Di i) Diα i 0) α i d
      = (laurentH A D Di i (i - d)).eval α := by
  set Ei := laurentE D Di i with hEidef
  set M := lDenomα Ei Diα i 0 with hMdef
  -- `M(α) ≠ 0`: `M = Diα^i·Ei`
  have hM : M.eval α ≠ 0 := by
    rw [hMdef, lDenomα, Nat.add_zero, Nat.zero_add, pow_one, Polynomial.eval_mul, Polynomial.eval_pow]
    exact mul_ne_zero (pow_ne_zero _ hroot.cofactor_eval_ne) hroot.laurentE_eval_ne
  -- the engine side: `Hᵢ,(i−d)(α) = (1/(i−(i−d))!)·(d/dx)^[i−(i−d)] hᵢ,α (α)`, with `i−(i−d)=d`
  have hji : i - d ≤ i := by omega
  rw [eval_laurentH_eq_taylor_coeff (Diα := Diα) i (i - d) hi hji hroot]
  rw [show i - (i - d) = d from by omega, ← hEidef]
  -- the `localCoeff` side via the Hasse bridge, with `hFracα = A/M`
  rw [localCoeff_eq_taylor_coeff A M i d hM hd, hFracα_eq_div_lDenomα, ← hMdef]

/-! ## Stage O — principal-part intrinsicity and the engine-form conclusion -/

/-- The principal part of `A/D` at `α` is the engine sum
`∑ j, (laurentH A D Dᵢ i j)(α)/(X - α)^j`. -/
theorem localPrincipalPart_eq_engineSum [CharZero K] (A D Di Diα : K[X]) {α : K} (i : ℕ)
    (hi : 0 < i) (hroot : IsLaurentRegularRoot D Di Diα α i) :
    localPrincipalPart A (lDenomα (laurentE D Di i) Diα i 0) α i
      = ∑ j ∈ Finset.Icc 1 i,
          algebraMap K[X] (RatFunc K) (Polynomial.C ((laurentH A D Di i j).eval α))
            / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ j := by
  rw [localPrincipalPart]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_Icc] at hj
  -- the `j`-th Laurent coefficient `localCoeff A M α i (i−j) = Hᵢⱼ(α)`
  rw [localCoeff_eq_laurentH A D Di Diα i (i - j) hi (by omega) hroot,
    show i - (i - j) = j from by omega]

/-- Any principal part whose difference from `A/D` is regular at `α` equals the
engine sum built from `laurentH A D Dᵢ i`. -/
theorem principalPart_eq_engineSum_of_regular [CharZero K] {A A' M' N Md D Di Diα : K[X]} {α : K}
    (i : ℕ) (hi : 0 < i) (hroot : IsLaurentRegularRoot D Di Diα α i) (hMd : Md.eval α ≠ 0)
    (hreg : algebraMap K[X] (RatFunc K) A
              / algebraMap K[X] (RatFunc K)
                  ((Polynomial.X - Polynomial.C α) ^ i * lDenomα (laurentE D Di i) Diα i 0)
            - localPrincipalPart A' M' α i
          = algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) Md) :
    localPrincipalPart A' M' α i
      = ∑ j ∈ Finset.Icc 1 i,
          algebraMap K[X] (RatFunc K) (Polynomial.C ((laurentH A D Di i j).eval α))
            / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ j := by
  set M := lDenomα (laurentE D Di i) Diα i 0 with hMdef
  have hM : M.eval α ≠ 0 := by
    rw [hMdef, lDenomα, Nat.add_zero, Nat.zero_add, pow_one, Polynomial.eval_mul, Polynomial.eval_pow]
    exact mul_ne_zero (pow_ne_zero _ hroot.cofactor_eval_ne) hroot.laurentE_eval_ne
  -- `q` and `localPrincipalPart A M α i` are both principal parts of `A/D` at `α`, rest regular at `α`
  have hcanon := subtract_localPrincipalPart_eq A M i hM
  -- `q + N/Md = localPrincipalPart A M α i + R/M` (both equal `A/D`)
  have heq : localPrincipalPart A' M' α i
        + algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) Md
      = localPrincipalPart A M α i
        + algebraMap K[X] (RatFunc K) (localRemainder A M α i) / algebraMap K[X] (RatFunc K) M := by
    -- both sides equal `A/D = A/((x−α)^i·M)`: `hreg` gives the LHS, `hcanon` the RHS
    linear_combination hcanon - hreg
  -- uniqueness: `q = localPrincipalPart A M α i`, then engine form
  rw [principalPart_unique i hMd hM heq,
    localPrincipalPart_eq_engineSum A D Di Diα i hi hroot]

/-! ## Stage Q — regularity at `α` and the fully-assembled engine-form capstone -/

open Classical in
/-- Engine-form complete partial fractions over a split denominator, with coefficients
`laurentH A D Dᵢ (mult α) j` at each pole `α`. -/
theorem completePartialFraction_engineForm [CharZero K] (A : K[X]) (mult : K → ℕ) (R : Finset K)
    {c : K} (hc : c ≠ 0)
    (Di Diα : K → K[X])
    (pole : ∀ α ∈ R, 0 < mult α ∧ (Di α).Monic ∧ (Di α).eval α = 0
      ∧ Di α = (Polynomial.X - Polynomial.C α) * Diα α
      ∧ IsCoprime (laurentE (rootProd R mult * Polynomial.C c) (Di α) (mult α)) (Di α)
      ∧ IsCoprime (derivative (Di α)) (Di α)
      ∧ (laurentE (rootProd R mult * Polynomial.C c) (Di α) (mult α)).eval α ≠ 0
      ∧ (Diα α).eval α ≠ 0
      ∧ rootProd R mult * Polynomial.C c
          = (Polynomial.X - Polynomial.C α) ^ mult α
            * lDenomα (laurentE (rootProd R mult * Polynomial.C c) (Di α) (mult α)) (Diα α) (mult α) 0) :
    ∃ (P : K[X]),
      algebraMap K[X] (RatFunc K) A
          / algebraMap K[X] (RatFunc K) (rootProd R mult * Polynomial.C c)
        = algebraMap K[X] (RatFunc K) P
          + ∑ α ∈ R, ∑ j ∈ Finset.Icc 1 (mult α),
              algebraMap K[X] (RatFunc K)
                  (Polynomial.C ((laurentH A (rootProd R mult * Polynomial.C c) (Di α) (mult α) j).eval α))
                / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ j := by
  set D := rootProd R mult * Polynomial.C c with hDdef
  have hpolefree : ∀ α ∈ R, (Polynomial.C c).eval α ≠ 0 := fun α _ => by
    rw [Polynomial.eval_C]; exact hc
  obtain ⟨PP, Rem, hdecomp, hreg, hstruct⟩ :=
    exists_sum_localPrincipalPart_regular (Polynomial.C c) mult R hpolefree A
  refine ⟨Polynomial.C c⁻¹ * Rem, ?_⟩
  -- each `PP α` equals its engine sum, by intrinsicity
  have hPPeng : ∀ α ∈ R, PP α
      = ∑ j ∈ Finset.Icc 1 (mult α),
          algebraMap K[X] (RatFunc K) (Polynomial.C ((laurentH A D (Di α) (mult α) j).eval α))
            / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ j := by
    intro α hα
    obtain ⟨hi, hDimonic, hDiα0root, hfac, hcopE, hcopD, hEi, hDiαα, hDfac⟩ := pole α hα
    obtain ⟨A', M', hPPeq⟩ := hstruct α hα
    obtain ⟨N, Md, hMd, hregdiv⟩ := (hreg α hα).exists_div
    rw [hPPeq]
    -- assemble the `hreg`-certificate into the input shape of `principalPart_eq_engineSum_of_regular`
    apply principalPart_eq_engineSum_of_regular (D := D) (mult α) hi
      ⟨hDimonic, hDiα0root, hfac, hcopE, hcopD, hEi, hDiαα⟩ hMd
    -- the goal denominator `(x−α)^{mult α}·lDenomα… = D` (`hDfac`); rest is `hreg`'s certificate
    rw [← hDfac, ← hPPeq]
    exact hregdiv
  -- rewrite the sum and fold the constant remainder into the polynomial part
  rw [hdecomp, div_C_eq_algebraMap hc, add_comm]
  congr 1
  exact Finset.sum_congr rfl hPPeng

end DeepWiki.SymbolicIntegration
