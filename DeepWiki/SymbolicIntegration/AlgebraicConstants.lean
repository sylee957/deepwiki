import DeepWiki.SymbolicIntegration.Constants

/-! # Constants of differential extensions (Bronstein §3.3)
The Wronskian criterion for linear dependence over the constants, in full generality, and the
permanence of linear independence over the constants under differential extension (Corollary
3.3.2). The hard direction of the Wronskian test — a vanishing Wronskian forces linear
dependence over the *constants* — is proved by induction on the number of functions, recasting
the classical analytic argument purely algebraically. -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

section Wronskian
variable {F : Type*} [Field F] [Differential F]

/-- `linearDependentOverConst y` : the family `y` is linearly dependent over the constants —
some nonzero constant tuple `c` (`∀ j, (c j)′ = 0`, `c ≠ 0`) has `∑ⱼ cⱼ·yⱼ = 0`. -/
def linearDependentOverConst {n : ℕ} (y : Fin n → F) : Prop :=
  ∃ c : Fin n → F, (∀ j, (c j)′ = 0) ∧ c ≠ 0 ∧ ∑ j, c j * y j = 0

/-- Dropping an index keeps a constant dependence: a constant dependence of the `n` functions
`y ∘ j₀.succAbove` lifts to a constant dependence of all `n+1` functions `y` (pad the `j₀`
coordinate with `0`). -/
theorem linearDependentOverConst_succAbove {n : ℕ} (y : Fin (n + 1) → F) (j₀ : Fin (n + 1))
    (h : linearDependentOverConst (fun i : Fin n => y (j₀.succAbove i))) :
    linearDependentOverConst y := by
  obtain ⟨d, hd, hdne, hdep⟩ := h
  refine ⟨Fin.insertNth j₀ 0 d, ?_, ?_, ?_⟩
  · intro k
    refine j₀.succAboveCases ?_ (fun i => ?_) k
    · rw [Fin.insertNth_apply_same]; simp
    · rw [Fin.insertNth_apply_succAbove]; exact hd i
  · intro hcontra
    apply hdne
    funext i
    have := congrFun hcontra (j₀.succAbove i)
    rwa [Fin.insertNth_apply_succAbove, Pi.zero_apply] at this
  · rw [Fin.sum_univ_succAbove _ j₀, Fin.insertNth_apply_same, zero_mul, zero_add]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans hdep
    rw [Fin.insertNth_apply_succAbove]

/-- Scaling an annihilating tuple by a field element preserves the row-annihilation
`∑ⱼ cⱼ·Dⁱyⱼ = 0`. -/
theorem dependent_iterDeriv_smul {n : ℕ} (y c : Fin n → F) (a : F)
    (hc : ∀ i : Fin n, ∑ j, c j * iterDeriv (i : ℕ) (y j) = 0) (i : Fin n) :
    ∑ j, (a * c j) * iterDeriv (i : ℕ) (y j) = 0 := by
  simp_rw [mul_assoc, ← Finset.mul_sum, hc i, mul_zero]

/-- **Lemma 3.3.5 converse, all `n`** (over rows): if a nonzero tuple `c` annihilates every
derivative row, `∀ i, ∑ⱼ cⱼ·Dⁱyⱼ = 0`, then `y` is linearly dependent over the constants.
Induction on `n`: normalise a nonzero coordinate to `1`, then either the derivative tuple
vanishes (all coefficients are already constants — done) or it is a *shorter* nonzero
annihilator of the family with that coordinate dropped (recurse). -/
theorem linearDependentOverConst_of_dependent_iterDeriv {n : ℕ} (y c : Fin n → F) (hcne : c ≠ 0)
    (hc : ∀ i : Fin n, ∑ j, c j * iterDeriv (i : ℕ) (y j) = 0) :
    linearDependentOverConst y := by
  induction n with
  | zero => exact absurd (Subsingleton.elim c 0) hcne
  | succ n IH =>
    -- pick a nonzero coordinate `j₀`
    obtain ⟨j₀, hj₀⟩ : ∃ j₀, c j₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hcne (funext h)
    -- normalise: `c1 j₀ = 1`
    set c1 : Fin (n + 1) → F := fun j => (c j₀)⁻¹ * c j with hc1def
    have hc1row : ∀ i : Fin (n + 1), ∑ j, c1 j * iterDeriv (i : ℕ) (y j) = 0 :=
      fun i => dependent_iterDeriv_smul y c (c j₀)⁻¹ hc i
    have hc1j₀ : c1 j₀ = 1 := by rw [hc1def]; field_simp
    have hc1ne : c1 ≠ 0 := fun h => by
      have := congrFun h j₀; rw [hc1j₀] at this; exact one_ne_zero this
    -- derivative tuple annihilates the lower rows
    have hder : ∀ i : Fin (n + 1), (i : ℕ) + 1 < n + 1 →
        ∑ j, (c1 j)′ * iterDeriv (i : ℕ) (y j) = 0 :=
      fun i hi => deriv_dependent_iterDeriv y c1 hc1row i hi
    have hderj₀ : (c1 j₀)′ = 0 := by rw [hc1j₀]; simp
    by_cases hzero : (fun j => (c1 j)′) = 0
    · -- all coefficients are constants: row 0 is the dependence
      refine ⟨c1, fun j => congrFun hzero j, hc1ne, ?_⟩
      have := hc1row 0
      simpa using this
    · -- derivative tuple is a shorter nonzero annihilator
      refine linearDependentOverConst_succAbove y j₀ (IH (fun i => y (j₀.succAbove i))
        (fun i => (c1 (j₀.succAbove i))′) ?_ ?_)
      · -- nonzero on the dropped family
        intro h
        apply hzero
        funext k
        refine j₀.succAboveCases ?_ (fun i => ?_) k
        · exact hderj₀
        · exact congrFun h i
      · -- annihilates rows `0..n-1` of the dropped family
        intro i
        have hi : (i.castSucc : ℕ) + 1 < n + 1 := by rw [Fin.val_castSucc]; omega
        have hrow := hder i.castSucc hi
        rw [Fin.sum_univ_succAbove _ j₀, hderj₀, zero_mul, zero_add] at hrow
        simpa [Fin.val_castSucc] using hrow

/-- **Lemma 3.3.5** (§3.3), full converse, all `n`: a vanishing Wronskian forces the `yⱼ` to be
linearly dependent *over the constants* `Const_D F` — a nonzero constant tuple `c` with
`∑ⱼ cⱼ·yⱼ = 0`. (The classical analysis test, proved purely algebraically.) -/
theorem linearDependentOverConst_of_wronskian_eq_zero {n : ℕ} [NeZero n] (y : Fin n → F)
    (h : wronskian y = 0) : linearDependentOverConst y := by
  obtain ⟨c, hcne, hrows⟩ := wronskian_eq_zero_dependent_iterDeriv y h
  exact linearDependentOverConst_of_dependent_iterDeriv y c hcne hrows

/-- **Lemma 3.3.5** (§3.3), full statement: for `y₁,…,yₙ ∈ F`, the Wronskian vanishes iff the
`yⱼ` are linearly dependent over the constants `Const_D F`. -/
theorem wronskian_eq_zero_iff_linearDependentOverConst {n : ℕ} [NeZero n] (y : Fin n → F) :
    wronskian y = 0 ↔ linearDependentOverConst y := by
  refine ⟨linearDependentOverConst_of_wronskian_eq_zero y, ?_⟩
  rintro ⟨c, hc, hcne, hdep⟩
  exact wronskian_eq_zero_of_linearDependent y c hc hcne hdep

/-- **Lemma 3.3.5** contrapositive: the Wronskian is nonzero iff the `yⱼ` are linearly
*independent* over the constants. -/
theorem wronskian_ne_zero_iff_not_linearDependentOverConst {n : ℕ} [NeZero n] (y : Fin n → F) :
    wronskian y ≠ 0 ↔ ¬ linearDependentOverConst y :=
  (wronskian_eq_zero_iff_linearDependentOverConst y).not

end Wronskian

section Extension
variable {F E : Type*} [Field F] [Field E] [Differential F] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E]

/-- Iterated derivative commutes with a differential extension: `Dⁱ(algebraMap c) = algebraMap (Dⁱ c)`. -/
theorem iterDeriv_algebraMap (i : ℕ) (x : F) :
    iterDeriv i (algebraMap F E x) = algebraMap F E (iterDeriv i x) := by
  induction i with
  | zero => rfl
  | succ n ih => rw [iterDeriv_succ, ih, deriv_algebraMap, iterDeriv_succ]

/-- The Wronskian commutes with a differential extension: `W(algebraMap ∘ y) = algebraMap (W y)`. -/
theorem wronskian_algebraMap {n : ℕ} (y : Fin n → F) :
    wronskian (fun j => algebraMap F E (y j)) = algebraMap F E (wronskian y) := by
  rw [wronskian, wronskian, RingHom.map_det]
  congr 1
  ext i j
  simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, iterDeriv_algebraMap]

/-- **Corollary 3.3.2** (§3.3): linear independence over the constants is preserved by a
differential extension — if `y₁,…,yₙ ∈ F` are *not* linearly dependent over `Const_D F`, then
their images in `E` are not linearly dependent over `Const_Δ E`. (Both are read off the same
Wronskian, which is nonzero in `F` hence nonzero in `E`.) -/
theorem not_linearDependentOverConst_algebraMap {n : ℕ} [NeZero n] (y : Fin n → F)
    (h : ¬ linearDependentOverConst y) :
    ¬ linearDependentOverConst (fun j => algebraMap F E (y j)) := by
  rw [← wronskian_ne_zero_iff_not_linearDependentOverConst] at h ⊢
  rw [wronskian_algebraMap]
  exact fun hcontra => h ((map_eq_zero (algebraMap F E)).mp hcontra)

end Extension

section SeparableAlgebraic
variable {E : Type*} [Field E] [Differential E]

/-- **Lemma 3.3.2(ii)** (§3.3): a separable algebraic element over the constants is a constant.
If `c ∈ E` is a root of a polynomial `p` with constant coefficients (algebraic over the
constants) and `p` is separable at `c` (`p'(c) ≠ 0`, the separability witness), then `c′ = 0`.
From the chain rule `Δ(p(c)) = p'(c)·Δc` (the `κ_D(p)` term drops as `p`'s coefficients are
constants), and `p(c) = 0`, so `p'(c)·Δc = 0`, forcing `Δc = 0`. -/
theorem deriv_eq_zero_of_separable_algebraic_const {c : E} (p : E[X])
    (hp : ∀ i, (p.coeff i)′ = 0) (hroot : p.eval c = 0) (hsep : p.derivative.eval c ≠ 0) :
    c′ = 0 := by
  have hchain : (p.eval c)′ = p.derivative.eval c * c′ := deriv_eval_of_const_coeffs p c hp
  rw [hroot, map_zero] at hchain
  exact (mul_eq_zero.mp hchain.symm).resolve_left hsep

end SeparableAlgebraic

end DeepWiki.SymbolicIntegration
