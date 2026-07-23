import DeepWiki.SymbolicIntegration.Core.Polynomial.Diophantine
import DeepWiki.SymbolicIntegration.RationalIntegration
import DeepWiki.SymbolicIntegration.DifferentialAlgebra.RationalFunctionDerivative
import DeepWiki.ComputableAlgebra.PolySquarefreeTheory

/-! # Hermite prime-power reduction

The single-squarefree-factor Hermite recurrence and degree bound for rational integration. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

open scoped Differential in
/-- The Hermite lowering identity transported from a differential field to rational functions `K(x)`. -/
theorem hermiteReduce_step_ratFunc {A B Cc V : K[X]} (hV : V ≠ 0) (m : ℕ)
    (hrel : B * derivative V + Cc * V = A) :
    (-((m : RatFunc K) + 1) * algebraMap K[X] (RatFunc K) A)
        / algebraMap K[X] (RatFunc K) V ^ (m + 2)
      = (algebraMap K[X] (RatFunc K) B / algebraMap K[X] (RatFunc K) V ^ (m + 1))′
        + (-((m : RatFunc K) + 1) * algebraMap K[X] (RatFunc K) Cc
            - algebraMap K[X] (RatFunc K) (derivative B))
          / algebraMap K[X] (RatFunc K) V ^ (m + 1) := by
  have hv : algebraMap K[X] (RatFunc K) V ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hV
  have key := hermite_reduction_step (algebraMap K[X] (RatFunc K) B)
    (algebraMap K[X] (RatFunc K) Cc) (algebraMap K[X] (RatFunc K) V) hv m
  rw [show (algebraMap K[X] (RatFunc K) V)′ = algebraMap K[X] (RatFunc K) (derivative V) from
        ratFuncDeriv_algebraMap V,
      show (algebraMap K[X] (RatFunc K) B)′ = algebraMap K[X] (RatFunc K) (derivative B) from
        ratFuncDeriv_algebraMap B,
      ← map_mul, ← map_mul, ← map_add, hrel] at key
  exact key

open Classical in
/-- Hermite prime-power reduction returning a rational part and a residual numerator over `V`. -/
noncomputable def hermiteReducePower (V : K[X]) : ℕ → K[X] → RatFunc K × K[X]
  | 0,     A => (0, A)
  | 1,     A => (0, A)
  | (m+2), A =>
      let c : K[X] := -A * Polynomial.C (((m : K) + 1)⁻¹)
      let B : K[X] := (diophantineSolveReduced (derivative V) V c).1
      let Cc : K[X] := (diophantineSolveReduced (derivative V) V c).2
      let r : K[X] := -(Polynomial.C ((m : K) + 1)) * Cc - derivative B
      (algebraMap K[X] (RatFunc K) B / algebraMap K[X] (RatFunc K) V ^ (m + 1)
          + (hermiteReducePower V (m + 1) r).1,
       (hermiteReducePower V (m + 1) r).2)

open scoped Differential in
open Classical in
/-- `hermiteReducePower V k A` splits `A / V^k` as a derivative plus a residual over `V`. -/
theorem hermiteReducePower_spec [CharZero K] (V : K[X]) (hV : Squarefree V) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (A : K[X]),
      algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) V ^ k
        = ((hermiteReducePower V k A).1)′
          + algebraMap K[X] (RatFunc K) (hermiteReducePower V k A).2
            / algebraMap K[X] (RatFunc K) V := by
  have hV0 : V ≠ 0 := hV.ne_zero
  have hcop : IsCoprime (derivative V) V := (squarefree_iff_isCoprime_derivative.mp hV).symm
  have e1 : ∀ k : K, algebraMap K[X] (RatFunc K) (Polynomial.C k) = algebraMap K (RatFunc K) k := by
    intro k
    rw [← Polynomial.algebraMap_eq]
    exact (IsScalarTower.algebraMap_apply K K[X] (RatFunc K) k).symm
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro hk A
    obtain _ | _ | m := k
    · exact absurd hk (by norm_num)
    · simp only [hermiteReducePower, pow_one, map_zero, zero_add]
    · have hm1 : ((m : K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
      have hc1 : algebraMap K (RatFunc K) ((m : K) + 1) = (m : RatFunc K) + 1 := by
        rw [map_add, map_natCast, map_one]
      simp only [hermiteReducePower]
      set c : K[X] := -A * Polynomial.C (((m : K) + 1)⁻¹) with hc
      set B : K[X] := (diophantineSolveReduced (derivative V) V c).1 with hB
      set Cc : K[X] := (diophantineSolveReduced (derivative V) V c).2 with hCc
      set r : K[X] := -(Polynomial.C ((m : K) + 1)) * Cc - derivative B with hr
      have hrel : B * derivative V + Cc * V = c := by
        have h := diophantineSolveReduced_spec hcop c
        rw [hB, hCc]; linear_combination h
      have hkey : algebraMap K (RatFunc K) ((m : K) + 1)
          * algebraMap K (RatFunc K) (((m : K) + 1)⁻¹) = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hm1, map_one]
      have hcoef : -((m : RatFunc K) + 1) * algebraMap K[X] (RatFunc K) c
          = algebraMap K[X] (RatFunc K) A := by
        rw [hc, map_mul, map_neg, e1, ← hc1]
        linear_combination (algebraMap K[X] (RatFunc K) A) * hkey
      have hnum : -((m : RatFunc K) + 1) * algebraMap K[X] (RatFunc K) Cc
            - algebraMap K[X] (RatFunc K) (derivative B)
          = algebraMap K[X] (RatFunc K) r := by
        rw [hr]; simp only [map_sub, map_mul, map_neg, e1, hc1]
      have key := hermiteReduce_step_ratFunc hV0 m hrel
      rw [hcoef, hnum] at key
      have IHr := IH (m + 1) (by omega) (by omega) r
      rw [map_add,
        add_assoc (algebraMap K[X] (RatFunc K) B / algebraMap K[X] (RatFunc K) V ^ (m + 1))′,
        ← IHr]
      exact key

/-- If `(p * V).degree < n` and `V.degree = d`, then `p.degree < n - d`. -/
private theorem degree_lt_of_mul_degree_lt {p V : K[X]} {d n : ℕ} (hV : V.degree = (d : WithBot ℕ))
    (hd : d ≤ n) (h : (p * V).degree < (n : WithBot ℕ)) : p.degree < ((n - d : ℕ) : WithBot ℕ) := by
  rw [Polynomial.degree_mul, hV] at h
  rcases eq_or_ne p 0 with hp | hp
  · rw [hp, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
  · rw [Polynomial.degree_eq_natDegree hp] at h ⊢
    rw [← Nat.cast_add, Nat.cast_lt] at h
    rw [Nat.cast_lt]; omega

/-- A strict degree bound below a positive natural degree gives a predecessor non-strict bound. -/
private theorem degree_le_pred_of_lt {p : K[X]} {d : ℕ} (hd : 0 < d) (h : p.degree < (d : WithBot ℕ)) :
    p.degree ≤ ((d - 1 : ℕ) : WithBot ℕ) := by
  rcases eq_or_ne p 0 with hp | hp
  · rw [hp, Polynomial.degree_zero]; exact bot_le
  · rw [Polynomial.degree_eq_natDegree hp, Nat.cast_le]
    rw [Polynomial.degree_eq_natDegree hp, Nat.cast_lt] at h; omega

open Classical in
/-- Hermite prime-power reduction preserves properness of the final squarefree residual. -/
theorem hermiteReducePower_remainder_degree [CharZero K] (V : K[X]) (hV : Squarefree V)
    (hdpos : 0 < V.natDegree) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (A : K[X]), A.degree < ((k * V.natDegree : ℕ) : WithBot ℕ) →
      (hermiteReducePower V k A).2.degree < V.degree := by
  have hV0 : V ≠ 0 := hV.ne_zero
  have hcop : IsCoprime (derivative V) V := (squarefree_iff_isCoprime_derivative.mp hV).symm
  set d : ℕ := V.natDegree with hd
  have hVdeg : V.degree = (d : WithBot ℕ) := Polynomial.degree_eq_natDegree hV0
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro hk A hA
    obtain _ | _ | m := k
    · exact absurd hk (by norm_num)
    · rw [hermiteReducePower, hVdeg]
      rwa [Nat.one_mul] at hA
    · have hm1 : ((m : K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
      have hinv : ((m : K) + 1)⁻¹ ≠ 0 := inv_ne_zero hm1
      simp only [hermiteReducePower]
      set c : K[X] := -A * Polynomial.C (((m : K) + 1)⁻¹) with hc
      set B : K[X] := (diophantineSolveReduced (derivative V) V c).1 with hB
      set Cc : K[X] := (diophantineSolveReduced (derivative V) V c).2 with hCc
      set r : K[X] := -(Polynomial.C ((m : K) + 1)) * Cc - derivative B with hr
      -- `deg c = deg A < (m+2)·d`.
      have hcdeg : c.degree < (((m + 2) * d : ℕ) : WithBot ℕ) := by
        rw [hc, Polynomial.degree_mul_C hinv, Polynomial.degree_neg]; exact hA
      -- `deg B < deg V = d` (reduced solver).
      have hBdeg : B.degree < (d : WithBot ℕ) := by
        rw [hB, ← hVdeg]; exact diophantineSolveReduced_fst_degree_lt hV0 c
      -- `deg V' < d`, so `deg V' ≤ d − 1`.
      have hV'le : (derivative V).degree ≤ ((d - 1 : ℕ) : WithBot ℕ) :=
        degree_le_pred_of_lt hdpos (by rw [← hVdeg]; exact Polynomial.degree_derivative_lt hV0)
      -- `deg B < d`, so `deg B ≤ d − 1`.
      have hBle : B.degree ≤ ((d - 1 : ℕ) : WithBot ℕ) := degree_le_pred_of_lt hdpos hBdeg
      -- the Bézout relation `B·V' + Cc·V = c`.
      have hrel : B * derivative V + Cc * V = c := by
        have h := diophantineSolveReduced_spec hcop c
        rw [hB, hCc]; linear_combination h
      -- `deg (B·V') ≤ (d−1) + (d−1) < (m+2)·d`, so `deg (Cc·V) < (m+2)·d`.
      have h2d : (d - 1 : ℕ) + (d - 1 : ℕ) < (m + 2) * d := by
        have : 2 * d ≤ (m + 2) * d := Nat.mul_le_mul_right d (by omega)
        omega
      have hBV' : (B * derivative V).degree < (((m + 2) * d : ℕ) : WithBot ℕ) := by
        refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
        refine lt_of_le_of_lt (add_le_add hBle hV'le) ?_
        rw [← Nat.cast_add, Nat.cast_lt]; exact h2d
      have hCcV : (Cc * V).degree < (((m + 2) * d : ℕ) : WithBot ℕ) := by
        have : Cc * V = c - B * derivative V := by linear_combination hrel
        rw [this]
        exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hcdeg hBV')
      -- cancel `V` to bound `deg Cc < (m+1)·d`.
      have hCcdeg : Cc.degree < (((m + 1) * d : ℕ) : WithBot ℕ) := by
        have hdle : d ≤ (m + 2) * d := Nat.le_mul_of_pos_left d (by omega)
        have hkey := degree_lt_of_mul_degree_lt hVdeg hdle hCcV
        rwa [show (m + 2) * d - d = (m + 1) * d by
          have : (m + 2) * d = (m + 1) * d + d := by ring
          omega] at hkey
      -- `deg r ≤ max (deg Cc) (deg B') < (m+1)·d`.
      have hdle1 : (d - 1 : ℕ) < (m + 1) * d := by
        have : d ≤ (m + 1) * d := Nat.le_mul_of_pos_left d (by omega)
        omega
      have hrdeg : r.degree < (((m + 1) * d : ℕ) : WithBot ℕ) := by
        rw [hr]
        refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
        · rw [neg_mul, Polynomial.degree_neg, Polynomial.degree_C_mul hm1]; exact hCcdeg
        · refine lt_of_le_of_lt (Polynomial.degree_derivative_le.trans hBle) ?_
          rw [Nat.cast_lt]; exact hdle1
      -- recurse on `r` at power `m+1`.
      exact IH (m + 1) (by omega) (by omega) r hrdeg

end DeepWiki.SymbolicIntegration
