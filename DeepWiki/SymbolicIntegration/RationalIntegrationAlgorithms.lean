import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.Diophantine
import DeepWiki.SymbolicIntegration.RationalIntegration
import DeepWiki.SymbolicIntegration.RationalFunctionDerivative
import DeepWiki.SymbolicIntegration.Residues
import DeepWiki.SymbolicIntegration.SquarefreeFactorization
import DeepWiki.SymbolicIntegration.Subresultants
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Radical.Basic
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.PartialFractions

/-! # Rational-function integration algorithms
Functional kernels for rational integration over `K[X]`: Diophantine solves, Hermite reduction,
resultants, subresultants, polynomial parts, and Horowitz denominator splitting. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ## Rothstein-Trager Primitives
Resultant and gcd primitives for residue-based logarithmic terms of rational integrals. -/

/-- The Rothstein-Trager resultant `resultant_x(D, A - t * D')` as a polynomial in `t`. -/
noncomputable def rtResultant (A D : K[X]) : K[X] :=
  Polynomial.resultant (D.map (C : K →+* K[X]))
    (A.map (C : K →+* K[X]) - C Polynomial.X * (derivative D).map (C : K →+* K[X]))
    D.natDegree (D.natDegree - 1)

/-- Evaluating `rtResultant A D` at `a` gives `resultant_x(D, A - C a * D')`. -/
theorem rtResultant_eval (A D : K[X]) (a : K) :
    (rtResultant A D).eval a
      = Polynomial.resultant D (A - C a * derivative D) D.natDegree (D.natDegree - 1) := by
  have hcomp : (Polynomial.evalRingHom a).comp (C : K →+* K[X]) = RingHom.id K := by
    ext k; simp
  show Polynomial.evalRingHom a (rtResultant A D) = _
  rw [rtResultant, ← Polynomial.resultant_map_map]
  congr 1
  · rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  · simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_C, hcomp,
      Polynomial.map_id]
    simp

open Classical in
/-- The residue gcd `gcd(D, A - C a * D')`. -/
noncomputable def rtLogGcd (A D : K[X]) (a : K) : K[X] :=
  gcd D (A - C a * derivative D)

open Classical in
/-- At a simple `D`-root, `rtLogGcd A D a` vanishes exactly when the residue of `A / D` is `a`. -/
theorem rtLogGcd_isRoot_iff (A D : K[X]) (a α : K) (hα : (derivative D).eval α ≠ 0) :
    (rtLogGcd A D a).IsRoot α ↔ (D.IsRoot α ∧ A.eval α / (derivative D).eval α = a) :=
  isRoot_gcd_iff_residue A D a α hα

/-- For separable `D`, roots of `rtResultant A D` are residues of `A / D`. -/
theorem rtResultant_eval_eq_zero_iff [IsAlgClosed K] (A D : K[X]) (hD : D.Separable) (a : K)
    (hdeg : (A - C a * derivative D).natDegree = D.natDegree - 1) :
    (rtResultant A D).eval a = 0 ↔ ∃ α, D.IsRoot α ∧ A.eval α / (derivative D).eval α = a := by
  rw [rtResultant_eval, ← hdeg, ← residue_iff_resultant_eq_zero A D hD a]

/-- `rtResultant A D` evaluates to a leading-coefficient factor times the product over roots of `D`. -/
theorem rtResultant_eval_eq_prod_roots [IsAlgClosed K] (A D : K[X]) (a : K)
    (hA : A.natDegree < D.natDegree) :
    (rtResultant A D).eval a
      = D.leadingCoeff ^ (D.natDegree - 1) *
        (D.roots.map (fun α => A.eval α - a * (derivative D).eval α)).prod := by
  have hg : (A - C a * derivative D).natDegree ≤ D.natDegree - 1 :=
    (natDegree_sub_le _ _).trans
      (max_le (by omega) ((natDegree_C_mul_le _ _).trans (natDegree_derivative_le D)))
  rw [rtResultant_eval, Polynomial.resultant_eq_prod_eval D (A - C a * derivative D)
    (D.natDegree - 1) hg (IsAlgClosed.splits D)]
  exact congrArg (D.leadingCoeff ^ (D.natDegree - 1) * ·)
    (congrArg Multiset.prod (Multiset.map_congr rfl (fun α _ => by simp [eval_sub, eval_mul, eval_C])))

/-! ## Lazard-Rioboo-Trager Subresultants
Functional subresultant primitives used to group logarithmic terms by residue multiplicity. -/

/-- The `j`-th subresultant of `D` and `A - t * D'` over coefficient ring `K[t]`. -/
noncomputable def lrtSubresultant (A D : K[X]) (j : ℕ) : (K[X])[X] :=
  subresultant (D.map (C : K →+* K[X]))
    (A.map (C : K →+* K[X]) - C Polynomial.X * (derivative D).map (C : K →+* K[X]))
    D.natDegree (D.natDegree - 1) j

/-- Specializing `lrtSubresultant A D j` at `t = a` gives the corresponding parameter subresultant over `K`. -/
theorem lrtSubresultant_eval (A D : K[X]) (a : K) (j : ℕ) :
    (lrtSubresultant A D j).map (Polynomial.evalRingHom a)
      = subresultant D (A - C a * derivative D) D.natDegree (D.natDegree - 1) j := by
  have hcomp : (Polynomial.evalRingHom a).comp (C : K →+* K[X]) = RingHom.id K := by ext k; simp
  rw [lrtSubresultant, ← subresultant_map]
  congr 1
  · rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  · simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_C, hcomp,
      Polynomial.map_id]
    simp

open Classical in
/-- The Lazard-Rioboo-Trager log-part data pairs squarefree residue factors with subresultant log arguments. -/
noncomputable def lazardRiobooTrager (A D : K[X]) : List (K[X] × (K[X])[X]) :=
  (squarefreeFactorization (rtResultant A D)).zipIdx.filterMap fun p =>
    let i := p.2 + 1
    if p.1.natDegree = 0 then none
    else some (p.1, if i = D.natDegree then D.map (C : K →+* K[X]) else lrtSubresultant A D i)

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

open Classical in
/-- For coprime nonzero `P` and `Q`, `A / (P * Q)` splits into `B / Q + C / P`. -/
theorem ratFunc_partialFraction_coprime {P Q A : K[X]} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hPQ : IsCoprime P Q) :
    algebraMap K[X] (RatFunc K) A
        / (algebraMap K[X] (RatFunc K) P * algebraMap K[X] (RatFunc K) Q)
      = algebraMap K[X] (RatFunc K) (diophantineSolve P Q A).1 / algebraMap K[X] (RatFunc K) Q
        + algebraMap K[X] (RatFunc K) (diophantineSolve P Q A).2 / algebraMap K[X] (RatFunc K) P := by
  have hp : algebraMap K[X] (RatFunc K) P ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hP
  have hq : algebraMap K[X] (RatFunc K) Q ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hQ
  have hspec : algebraMap K[X] (RatFunc K) A
      = algebraMap K[X] (RatFunc K) P * algebraMap K[X] (RatFunc K) (diophantineSolve P Q A).1
        + algebraMap K[X] (RatFunc K) Q * algebraMap K[X] (RatFunc K) (diophantineSolve P Q A).2 := by
    rw [← map_mul, ← map_mul, ← map_add, diophantineSolve_spec hPQ A]
  rw [hspec]; field_simp

open Classical in
/-- A nonempty product of pairwise-coprime nonzero factors admits a partial-fraction decomposition. -/
theorem ratFunc_partialFraction_prod {ι : Type*} (P : ι → K[X]) :
    ∀ (s : Finset ι), s.Nonempty → (∀ i ∈ s, P i ≠ 0) →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (P i) (P j)) → ∀ (A : K[X]),
      ∃ B : ι → K[X],
        algebraMap K[X] (RatFunc K) A / ∏ i ∈ s, algebraMap K[X] (RatFunc K) (P i)
          = ∑ i ∈ s, algebraMap K[X] (RatFunc K) (B i) / algebraMap K[X] (RatFunc K) (P i) := by
  intro s hs
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => exact fun _ _ A => ⟨fun _ => A, by simp⟩
  | cons a s ha hs ih =>
      intro hP hcop A
      have hmem : ∀ i ∈ s, i ∈ Finset.cons a s ha := fun i hi => Finset.mem_cons.mpr (Or.inr hi)
      have hPa : P a ≠ 0 := hP a (Finset.mem_cons_self a s)
      have hP' : ∀ i ∈ s, P i ≠ 0 := fun i hi => hP i (hmem i hi)
      have hcop' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (P i) (P j) :=
        fun i hi j hj hij => hcop i (hmem i hi) j (hmem j hj) hij
      have hQ0 : (∏ i ∈ s, P i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hP'
      have hcopaQ : IsCoprime (P a) (∏ i ∈ s, P i) :=
        IsCoprime.prod_right fun i hi =>
          hcop a (Finset.mem_cons_self a s) i (hmem i hi) (by rintro rfl; exact ha hi)
      obtain ⟨B', hB'⟩ := ih hP' hcop' (diophantineSolve (P a) (∏ i ∈ s, P i) A).1
      refine ⟨fun i => if i = a then (diophantineSolve (P a) (∏ i ∈ s, P i) A).2 else B' i, ?_⟩
      have hsplit := ratFunc_partialFraction_coprime (A := A) hPa hQ0 hcopaQ
      rw [map_prod] at hsplit
      have hsumeq : (∑ i ∈ s, algebraMap K[X] (RatFunc K)
            (if i = a then (diophantineSolve (P a) (∏ i ∈ s, P i) A).2 else B' i)
            / algebraMap K[X] (RatFunc K) (P i))
          = ∑ i ∈ s, algebraMap K[X] (RatFunc K) (B' i) / algebraMap K[X] (RatFunc K) (P i) :=
        Finset.sum_congr rfl fun i hi => by
          rw [if_neg (fun (h : i = a) => ha (h ▸ hi))]
      rw [Finset.prod_cons, Finset.sum_cons]
      dsimp only
      rw [hsumeq, if_pos rfl, hsplit, hB', add_comm]

open scoped Differential in
open Classical in
/-- A sum of prime-power fractions Hermite-reduces to a derivative plus squarefree residuals. -/
theorem hermiteReduce_sum_spec [CharZero K] {ι : Type*} (s : Finset ι) (D : ι → K[X])
    (e : ι → ℕ) (A : ι → K[X]) (hD : ∀ i ∈ s, Squarefree (D i)) (he : ∀ i ∈ s, 1 ≤ e i) :
    ∑ i ∈ s, algebraMap K[X] (RatFunc K) (A i) / algebraMap K[X] (RatFunc K) (D i) ^ e i
      = (∑ i ∈ s, (hermiteReducePower (D i) (e i) (A i)).1)′
        + ∑ i ∈ s, algebraMap K[X] (RatFunc K) (hermiteReducePower (D i) (e i) (A i)).2
            / algebraMap K[X] (RatFunc K) (D i) := by
  rw [map_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i hi =>
    hermiteReducePower_spec (D i) (hD i hi) (e i) (he i hi) (A i)

open scoped Differential in
open Classical in
/-- A coprime squarefree-power denominator admits a full Hermite reduction. -/
theorem hermiteReduce_full [CharZero K] {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (D : ι → K[X]) (e : ι → ℕ) (hD : ∀ i ∈ s, Squarefree (D i)) (he : ∀ i ∈ s, 1 ≤ e i)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (D i) (D j)) (A : K[X]) :
    ∃ (g : RatFunc K) (r : ι → K[X]),
      algebraMap K[X] (RatFunc K) A / ∏ i ∈ s, algebraMap K[X] (RatFunc K) (D i) ^ e i
        = g′ + ∑ i ∈ s, algebraMap K[X] (RatFunc K) (r i) / algebraMap K[X] (RatFunc K) (D i) := by
  obtain ⟨B, hB⟩ := ratFunc_partialFraction_prod (fun i => D i ^ e i) s hs
    (fun i hi => pow_ne_zero _ (hD i hi).ne_zero)
    (fun i hi j hj hij => (hcop i hi j hj hij).pow) A
  simp only [map_pow] at hB
  exact ⟨_, _, hB.trans (hermiteReduce_sum_spec s D e B hD he)⟩

/-! ## Polynomial Part
Termwise polynomial antiderivatives and the polynomial-division split for rational functions. -/

/-- Termwise polynomial antiderivative `∑ aₙ/(n+1) * X^(n+1)`. -/
noncomputable def polyIntegral (Q : K[X]) : K[X] :=
  Q.sum fun n a => C (a / ((n : K) + 1)) * X ^ (n + 1)

/-- Over a characteristic-zero field, `polyIntegral Q` differentiates to `Q`. -/
theorem polyIntegral_derivative [CharZero K] (Q : K[X]) : derivative (polyIntegral Q) = Q := by
  rw [polyIntegral, Polynomial.sum_def, derivative_sum]
  rw [show (∑ n ∈ Q.support, derivative (C (Q.coeff n / ((n : K) + 1)) * X ^ (n + 1)))
        = ∑ n ∈ Q.support, C (Q.coeff n) * X ^ n from Finset.sum_congr rfl fun n _ => ?_]
  · conv_rhs => rw [← Polynomial.sum_C_mul_X_pow_eq Q, Polynomial.sum_def]
  · rw [derivative_C_mul_X_pow, Nat.add_sub_cancel]
    have hn1 : ((n + 1 : ℕ) : K) = (n : K) + 1 := by push_cast; ring
    rw [hn1, div_mul_cancel₀ _ (by exact_mod_cast Nat.succ_ne_zero n)]

-- `∫ Q dx` is a genuine antiderivative of `Q`.
example [CharZero K] (Q : K[X]) : derivative (polyIntegral Q) = Q := polyIntegral_derivative Q

/-- In `K(x)`, `A / Den` splits into its polynomial quotient plus remainder fraction. -/
theorem ratFunc_polyDivide_split (A Den : K[X]) (hDen : Den ≠ 0) :
    algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) Den
      = algebraMap K[X] (RatFunc K) (A / Den)
        + algebraMap K[X] (RatFunc K) (A % Den) / algebraMap K[X] (RatFunc K) Den := by
  have hd : algebraMap K[X] (RatFunc K) Den ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hDen
  have hAeq : algebraMap K[X] (RatFunc K) A
      = algebraMap K[X] (RatFunc K) Den * algebraMap K[X] (RatFunc K) (A / Den)
        + algebraMap K[X] (RatFunc K) (A % Den) := by
    rw [← map_mul, ← map_add, EuclideanDomain.div_add_mod]
  rw [hAeq]; field_simp

open scoped Differential in
open Classical in
/-- A squarefree-power rational function reduces to derivative, polynomial, and squarefree residual parts. -/
theorem integrateRationalFunction_reduction [CharZero K] {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (D : ι → K[X]) (e : ι → ℕ) (hD : ∀ i ∈ s, Squarefree (D i)) (he : ∀ i ∈ s, 1 ≤ e i)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (D i) (D j)) (A : K[X]) :
    ∃ (g : RatFunc K) (p : K[X]) (r : ι → K[X]),
      algebraMap K[X] (RatFunc K) A / ∏ i ∈ s, algebraMap K[X] (RatFunc K) (D i) ^ e i
        = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
          + ∑ i ∈ s, algebraMap K[X] (RatFunc K) (r i) / algebraMap K[X] (RatFunc K) (D i) := by
  set Den : K[X] := ∏ i ∈ s, D i ^ e i with hDen
  have hDenne : Den ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hD i hi).ne_zero
  have hDenmap : (∏ i ∈ s, algebraMap K[X] (RatFunc K) (D i) ^ e i)
      = algebraMap K[X] (RatFunc K) Den := by
    rw [hDen, map_prod]; exact Finset.prod_congr rfl fun i _ => (map_pow _ _ _).symm
  -- PolyDivide: split off the polynomial quotient `A / Den`.
  rw [hDenmap, ratFunc_polyDivide_split A Den hDenne]
  -- Hermite-reduce the proper remainder `(A % Den) / Den`.
  obtain ⟨g, r, hg⟩ := hermiteReduce_full s hs D e hD he hcop (A % Den)
  rw [← hDenmap, hg]
  -- The polynomial quotient integrates to `polyIntegral (A / Den)`.
  refine ⟨g, A / Den, r, ?_⟩
  have hpi : (algebraMap K[X] (RatFunc K) (polyIntegral (A / Den)))′
      = algebraMap K[X] (RatFunc K) (A / Den) := by
    show ratFuncDeriv _ = _
    rw [ratFuncDeriv_algebraMap (polyIntegral (A / Den)), polyIntegral_derivative]
  rw [hpi]; ring

open scoped Differential in
open Classical in
-- `∫ A/Den` reduces to a rational part, a polynomial-integral part, and a squarefree-denominator sum.
example [CharZero K] {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (D : ι → K[X]) (e : ι → ℕ)
    (hD : ∀ i ∈ s, Squarefree (D i)) (he : ∀ i ∈ s, 1 ≤ e i)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (D i) (D j)) (A : K[X]) :
    ∃ (g : RatFunc K) (p : K[X]) (r : ι → K[X]),
      algebraMap K[X] (RatFunc K) A / ∏ i ∈ s, algebraMap K[X] (RatFunc K) (D i) ^ e i
        = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
          + ∑ i ∈ s, algebraMap K[X] (RatFunc K) (r i) / algebraMap K[X] (RatFunc K) (D i) :=
  integrateRationalFunction_reduction s hs D e hD he hcop A

open scoped Differential in
open Classical in
/-- The rational-function reduction can choose squarefree residual numerators proper below each factor. -/
theorem integrateRationalFunction_reduction_proper [CharZero K] {ι : Type*} (s : Finset ι)
    (D : ι → K[X]) (e : ι → ℕ) (hmonic : ∀ i ∈ s, (D i).Monic) (hsf : ∀ i ∈ s, Squarefree (D i))
    (hnd : ∀ i ∈ s, 0 < (D i).natDegree) (he : ∀ i ∈ s, 1 ≤ e i)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (D i) (D j)) (A : K[X]) :
    ∃ (g : RatFunc K) (p : K[X]) (r : ι → K[X]),
      (∀ i ∈ s, (r i).degree < (D i).degree) ∧
      algebraMap K[X] (RatFunc K) A / ∏ i ∈ s, algebraMap K[X] (RatFunc K) (D i) ^ e i
        = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
          + ∑ i ∈ s, algebraMap K[X] (RatFunc K) (r i) / algebraMap K[X] (RatFunc K) (D i) := by
  -- Degree-bounded partial fraction over the monic powers `g i = (D i)^(e i)`.
  have hgmonic : ∀ i ∈ s, ((D i) ^ e i).Monic := fun i hi => (hmonic i hi).pow _
  have hgcop : Set.Pairwise (↑s : Set ι) fun i j => IsCoprime ((D i) ^ e i) ((D j) ^ e j) :=
    fun i hi j hj hij => (hcop i hi j hj hij).pow
  obtain ⟨p, B, hBdeg, hpf⟩ :=
    Polynomial.div_prod_eq_quo_add_sum_rem_div (R := K) (K := RatFunc K) A hgmonic hgcop
  -- Reduce each proper prime power `Bᵢ/(Dᵢ^eᵢ)` by the Hermite loop.
  refine ⟨∑ i ∈ s, (hermiteReducePower (D i) (e i) (B i)).1, p,
    fun i => (hermiteReducePower (D i) (e i) (B i)).2, fun i hi => ?_, ?_⟩
  · -- properness: `deg rᵢ < deg Dᵢ` from the degree-tracking lemma.
    simp only []
    refine hermiteReducePower_remainder_degree (D i) (hsf i hi) (hnd i hi) (e i) (he i hi) (B i) ?_
    have hd : ((D i) ^ e i).degree = ((e i * (D i).natDegree : ℕ) : WithBot ℕ) := by
      rw [Polynomial.degree_pow, Polynomial.degree_eq_natDegree (hmonic i hi).ne_zero,
        nsmul_eq_mul, ← Nat.cast_mul]
    exact (hBdeg i hi).trans_eq hd
  · -- assemble: partial fraction → `hermiteReduce_sum_spec` → `polyIntegral`.
    have hsumeq := hermiteReduce_sum_spec s D e B hsf he
    -- normalize the Mathlib casts `↑` to `algebraMap`, with `↑(Dᵢ^eᵢ) = (algebraMap Dᵢ)^eᵢ`.
    have hpf' : algebraMap K[X] (RatFunc K) A
          / ∏ i ∈ s, algebraMap K[X] (RatFunc K) (D i) ^ e i
        = algebraMap K[X] (RatFunc K) p
          + ∑ i ∈ s, algebraMap K[X] (RatFunc K) (B i) / algebraMap K[X] (RatFunc K) (D i) ^ e i := by
      have e1 : (∏ i ∈ s, algebraMap K[X] (RatFunc K) (D i) ^ e i)
          = ∏ i ∈ s, (algebraMap K[X] (RatFunc K) ((D i) ^ e i) : RatFunc K) :=
        Finset.prod_congr rfl fun i _ => (map_pow _ _ _).symm
      have e2 : (∑ i ∈ s, algebraMap K[X] (RatFunc K) (B i)
            / algebraMap K[X] (RatFunc K) (D i) ^ e i)
          = ∑ i ∈ s, (algebraMap K[X] (RatFunc K) (B i) : RatFunc K)
              / algebraMap K[X] (RatFunc K) ((D i) ^ e i) :=
        Finset.sum_congr rfl fun i _ => by rw [map_pow]
      rw [e1, e2]; exact hpf
    rw [hpf', hsumeq]
    have hpi : (algebraMap K[X] (RatFunc K) (polyIntegral p))′
        = algebraMap K[X] (RatFunc K) p := by
      show ratFuncDeriv _ = _
      rw [ratFuncDeriv_algebraMap (polyIntegral p), polyIntegral_derivative]
    rw [hpi]; ring

/-! ## Horowitz-Ostrogradsky Split
Denominator splitting and rational-function identity for one-shot rational-part extraction. -/

open Classical in
/-- Horowitz-Ostrogradsky denominator split `(gcd(D, D'), D / gcd(D, D'))`. -/
noncomputable def hoSplit (D : K[X]) : K[X] × K[X] :=
  (gcd D (derivative D), D / gcd D (derivative D))

open Classical in
/-- `gcd(D, D') ≠ 0` for `D ≠ 0`. -/
private theorem gcd_derivative_ne_zero {D : K[X]} (hD : D ≠ 0) : gcd D (derivative D) ≠ 0 :=
  fun h => hD (zero_dvd_iff.mp (h ▸ gcd_dvd_left D (derivative D)))

open Classical in
/-- The Horowitz-Ostrogradsky split factors `D` when `D ≠ 0`. -/
theorem hoSplit_mul (D : K[X]) (hD : D ≠ 0) : (hoSplit D).1 * (hoSplit D).2 = D :=
  EuclideanDomain.mul_div_cancel' (gcd_derivative_ne_zero hD) (gcd_dvd_left _ _)

open Classical in
/-- In characteristic zero, the second component of `hoSplit D` is squarefree. -/
theorem hoSplit_snd_squarefree [CharZero K] (D : K[X]) (hD : D ≠ 0) :
    Squarefree (hoSplit D).2 := by
  have hprim : D.IsPrimitive := (isPrimitive_iff_ne_zero D).mpr hD
  have hpp : D.primPart = D := by
    have h := eq_C_content_mul_primPart D
    rw [hprim.content_eq_one, map_one, one_mul] at h; exact h.symm
  have hppne : D.primPart ≠ 0 := by rw [hpp]; exact hD
  have hmul : gcd D (derivative D) * (hoSplit D).2 = D := hoSplit_mul D hD
  have h1 : Associated (squarefreePart D * deflation D 1) D := by
    have := squarefreePart_mul_deflation D hppne; rwa [hpp] at this
  have h2 : Associated (gcd D (derivative D)) (deflation D 1) := by
    have := deflation_one_eq_gcd D hppne; rwa [hpp] at this
  -- cancel the common factor gcd ~ deflation to get D* ~ squarefreePart
  have hcomb : Associated (gcd D (derivative D) * (hoSplit D).2)
      (deflation D 1 * squarefreePart D) := by
    rw [hmul, mul_comm (deflation D 1) (squarefreePart D)]; exact h1.symm
  have hAD : Associated (hoSplit D).2 (squarefreePart D) :=
    Associated.of_mul_left hcomb h2 (gcd_derivative_ne_zero hD)
  have hsqfp : squarefreePart D = UniqueFactorizationMonoid.radical D := by
    unfold squarefreePart UniqueFactorizationMonoid.radical UniqueFactorizationMonoid.primeFactors
    rw [hpp]; congr!
  rw [hAD.squarefree_iff, hsqfp]
  exact UniqueFactorizationMonoid.squarefree_radical

open Classical in
/-- The first component of `hoSplit D` divides its derivative times the second component. -/
theorem hoSplit_fst_dvd_deriv_mul_snd (D : K[X]) (hD : D ≠ 0) :
    (hoSplit D).1 ∣ derivative (hoSplit D).1 * (hoSplit D).2 := by
  have hmul : (hoSplit D).1 * (hoSplit D).2 = D := hoSplit_mul D hD
  have hderiv : derivative D
      = derivative (hoSplit D).1 * (hoSplit D).2 + (hoSplit D).1 * derivative (hoSplit D).2 := by
    conv_lhs => rw [← hmul]
    rw [derivative_mul]
  have hdvdD' : (hoSplit D).1 ∣ derivative D := gcd_dvd_right D (derivative D)
  have key : (hoSplit D).1 ∣ derivative D - (hoSplit D).1 * derivative (hoSplit D).2 :=
    dvd_sub hdvdD' (dvd_mul_right _ _)
  rwa [hderiv, add_sub_cancel_right] at key

open scoped Differential in
/-- The Horowitz-Ostrogradsky reduction identity transported to rational functions `K(x)`. -/
theorem horowitzReduce_step_ratFunc {A B C Dminus Dstar E : K[X]} (hDm : Dminus ≠ 0) (hDs : Dstar ≠ 0)
    (hE : E * Dminus = derivative Dminus * Dstar)
    (hA : derivative B * Dstar - B * E + C * Dminus = A) :
    algebraMap K[X] (RatFunc K) A
        / (algebraMap K[X] (RatFunc K) Dminus * algebraMap K[X] (RatFunc K) Dstar)
      = (algebraMap K[X] (RatFunc K) B / algebraMap K[X] (RatFunc K) Dminus)′
        + algebraMap K[X] (RatFunc K) C / algebraMap K[X] (RatFunc K) Dstar := by
  have hm : algebraMap K[X] (RatFunc K) Dminus ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hDm
  have hs : algebraMap K[X] (RatFunc K) Dstar ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hDs
  have hE' : algebraMap K[X] (RatFunc K) E * algebraMap K[X] (RatFunc K) Dminus
      = (algebraMap K[X] (RatFunc K) Dminus)′ * algebraMap K[X] (RatFunc K) Dstar := by
    rw [show (algebraMap K[X] (RatFunc K) Dminus)′
          = algebraMap K[X] (RatFunc K) (derivative Dminus) from ratFuncDeriv_algebraMap Dminus,
        ← map_mul, ← map_mul, hE]
  have key := horowitz_reduction_step (algebraMap K[X] (RatFunc K) B) (algebraMap K[X] (RatFunc K) C)
    (algebraMap K[X] (RatFunc K) Dminus) (algebraMap K[X] (RatFunc K) Dstar)
    (algebraMap K[X] (RatFunc K) E) hm hs hE'
  have hnum : (algebraMap K[X] (RatFunc K) B)′ * algebraMap K[X] (RatFunc K) Dstar
        - algebraMap K[X] (RatFunc K) B * algebraMap K[X] (RatFunc K) E
        + algebraMap K[X] (RatFunc K) C * algebraMap K[X] (RatFunc K) Dminus
      = algebraMap K[X] (RatFunc K) A := by
    rw [show (algebraMap K[X] (RatFunc K) B)′
          = algebraMap K[X] (RatFunc K) (derivative B) from ratFuncDeriv_algebraMap B,
        ← map_mul, ← map_mul, ← map_mul, ← map_sub, ← map_add, hA]
  rw [hnum] at key
  exact key

end DeepWiki.SymbolicIntegration
