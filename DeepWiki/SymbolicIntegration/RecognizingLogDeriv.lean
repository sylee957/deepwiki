import DeepWiki.Algebra.RatFuncEvaluation
import DeepWiki.SymbolicIntegration.PartialFraction
import DeepWiki.SymbolicIntegration.Residues
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.ResidueMultiplicity

/-! # Recognizing logarithmic derivatives
For `f = A/D ∈ K(x)` with `D` squarefree and `deg A < deg D`, `f` is the logarithmic derivative of a
nonzero rational function iff every residue `A(α)/D'(α)` is an integer in `K`
(`isLogDeriv_iff_integer_residues`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

open scoped Classical in
open scoped Differential in
/-- `algebraMap K[X] (RatFunc K) (C (n : K)) = (n : RatFunc K)` for `n : ℤ`. -/
theorem algebraMap_C_intCast (n : ℤ) :
    algebraMap K[X] (RatFunc K) (C (n : K)) = (n : RatFunc K) := by
  rw [show (C (n : K)) = ((n : K[X])) from by simp, map_intCast]

open scoped Classical in
open scoped Differential in
/-- The logarithmic-derivative witness `u = ∏ₐ Gₐ^{nₐ}`, over the distinct residue values of `A/D`. -/
noncomputable def intResiduesWitness (s : Finset K) (A : K[X]) (n : K → ℤ) : RatFunc K :=
  ∏ a ∈ s.image (fun α => A.eval α / eval α (derivative (Lagrange.nodal s id))),
    (algebraMap K[X] (RatFunc K)
        (∏ α ∈ s.filter (fun α => A.eval α / eval α (derivative (Lagrange.nodal s id)) = a),
          (X - C α))) ^ n a

open scoped Classical in
/-- `intResiduesWitness s A n ≠ 0`. -/
theorem intResiduesWitness_ne_zero (s : Finset K) (A : K[X]) (n : K → ℤ) :
    intResiduesWitness s A n ≠ 0 := by
  rw [intResiduesWitness]
  refine Finset.prod_ne_zero_iff.mpr fun a _ => zpow_ne_zero _ ?_
  refine (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr ?_
  exact Finset.prod_ne_zero_iff.mpr fun α _ => X_sub_C_ne_zero α

open scoped Classical in
open scoped Differential in
/-- If every residue is an integer (`(n a : K) = a`), then `A/D = logDeriv (intResiduesWitness s A n)`. -/
theorem logDeriv_intResiduesWitness (s : Finset K) (A : K[X]) (hA : A.degree < s.card)
    (n : K → ℤ)
    (hn : ∀ α ∈ s, ((n (A.eval α / eval α (derivative (Lagrange.nodal s id))) : K))
      = A.eval α / eval α (derivative (Lagrange.nodal s id))) :
    algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
      = Differential.logDeriv (intResiduesWitness s A n) := by
  set res : K → K := fun α => A.eval α / eval α (derivative (Lagrange.nodal s id)) with hres
  -- nonzero of each grouped factor `Ḡₐ`
  have hGne : ∀ a ∈ s.image res, algebraMap K[X] (RatFunc K)
      (∏ α ∈ s.filter (fun α => res α = a), (X - C α)) ≠ 0 := fun a _ =>
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (Finset.prod_ne_zero_iff.mpr fun α _ => X_sub_C_ne_zero α)
  -- residue values in the image are integers
  have hint : ∀ a ∈ s.image res, ((n a : K)) = a := by
    intro a ha
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp ha
    exact hn α hα
  rw [ratFunc_eq_sum_residue_grouped s A hA, intResiduesWitness, ← hres,
    logDeriv_prod_zpow _ _ _ hGne]
  refine Finset.sum_congr rfl fun a ha => ?_
  congr 1
  rw [← algebraMap_C_intCast (n a), hint a ha]

open scoped Classical in
open scoped Differential in
/-- If every residue `A(α)/D'(α)` is an integer in `K`, then `∃ u ≠ 0, A/D = logDeriv u`. -/
theorem isLogDeriv_of_integer_residues (s : Finset K) (A : K[X]) (hA : A.degree < s.card)
    (hint : ∀ α ∈ s, ∃ m : ℤ, ((m : K)) = A.eval α / eval α (derivative (Lagrange.nodal s id))) :
    ∃ u : RatFunc K, u ≠ 0 ∧
      algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
        = Differential.logDeriv u := by
  classical
  -- choose an integer exponent for each residue value
  set res : K → K := fun α => A.eval α / eval α (derivative (Lagrange.nodal s id)) with hres
  have hex : ∀ a : K, (∃ α ∈ s, res α = a) → ∃ m : ℤ, ((m : K)) = a := by
    rintro a ⟨α, hα, rfl⟩; exact hint α hα
  let n : K → ℤ := fun a => if h : ∃ α ∈ s, res α = a then (hex a h).choose else 0
  have hn : ∀ α ∈ s, ((n (res α) : K)) = res α := by
    intro α hα
    have h : ∃ β ∈ s, res β = res α := ⟨α, hα, rfl⟩
    simp only [n, dif_pos h]
    exact (hex (res α) h).choose_spec
  refine ⟨intResiduesWitness s A n, intResiduesWitness_ne_zero s A n,
    logDeriv_intResiduesWitness s A hA n hn⟩

open scoped Classical in
open scoped Differential in
-- The `⟸` direction: integer residues give a logarithmic-derivative witness for `A/D`.
/-! ## Numerator log-derivative as a sum over roots (toward the `⟹` direction) -/

open scoped Classical in
open scoped Differential in
/-- Over an algebraically closed field, `logDeriv N = ∑_{β ∈ N.roots} logDeriv(X − β)` for `N ≠ 0`. -/
theorem logDeriv_algebraMap_eq_sum_roots [IsAlgClosed K] (N : K[X]) (hN : N ≠ 0) :
    Differential.logDeriv (algebraMap K[X] (RatFunc K) N)
      = (N.roots.map (fun β => Differential.logDeriv
          (algebraMap K[X] (RatFunc K) (X - C β)))).sum := by
  have hsplit : N.Splits := IsAlgClosed.splits N
  have hlc : N.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hN
  -- the constant `C lc` has zero log-derivative
  have hCconst : Differential.logDeriv (algebraMap K[X] (RatFunc K) (C N.leadingCoeff)) = 0 := by
    rw [Differential.logDeriv_eq_zero,
      show (algebraMap K[X] (RatFunc K) (C N.leadingCoeff))′
        = ratFuncDeriv _ from rfl, ratFuncDeriv_algebraMap, derivative_C, map_zero]
  -- nonzero of the constant and the product factors
  have hCne : algebraMap K[X] (RatFunc K) (C N.leadingCoeff) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (by simpa using hlc)
  have hProd : ((N.roots.map (X - C ·)).prod : K[X]) ≠ 0 := by
    refine Multiset.prod_ne_zero ?_
    simp only [Multiset.mem_map, not_exists]
    exact fun β => fun ⟨_, h⟩ => X_sub_C_ne_zero β h
  have hPne : algebraMap K[X] (RatFunc K) ((N.roots.map (X - C ·)).prod) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hProd
  -- `N = C lc · ∏_β (X − β)`, push through `algebraMap` on the LHS only
  conv_lhs => rw [hsplit.eq_prod_roots]
  rw [map_mul, Differential.logDeriv_mul _ _ hCne hPne, hCconst, zero_add, map_multiset_prod,
    Multiset.map_map, Differential.logDeriv_multisetProd]
  · exact congrArg Multiset.sum (Multiset.map_congr rfl fun β _ => rfl)
  · exact fun x _ => (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (X_sub_C_ne_zero x)

open scoped Classical in
open scoped Differential in
-- `logDeriv(N) = ∑_{β ∈ N.roots} logDeriv(X−β)`: the numerator log-derivative is the root sum.
/-! ## The simple-pole residue functional
`residueAt α f = ((X − α)·f)(α)` extracts the residue at a simple pole `α`. -/

/-- The simple-pole residue functional `residueAt α f = ((X − α)·f)(α)`. -/
noncomputable def residueAt (α : K) (f : RatFunc K) : K :=
  RatFunc.eval (RingHom.id K) α (algebraMap K[X] (RatFunc K) (X - C α) * f)

open scoped Classical in
/-- If `(X − α)·f = g/h` with `h(α) ≠ 0`, then `residueAt α f = g(α)/h(α)`. -/
theorem residueAt_of_mul_X_sub_C (α : K) (f : RatFunc K) (g h : K[X]) (hh : h.eval α ≠ 0)
    (heq : algebraMap K[X] (RatFunc K) (X - C α) * f
      = algebraMap K[X] (RatFunc K) g / algebraMap K[X] (RatFunc K) h) :
    residueAt α f = g.eval α / h.eval α := by
  rw [residueAt, heq, eval_algebraMap_div α g h hh]

open scoped Classical in
/-- The residue vanishes on a function regular at `α`. If `f = A/B` with `B(α) ≠ 0` (no pole at `α`), then
`residueAt α f = 0` — `(X−α)·f = (X−α)A/B` has a zero at `α`. This is the `Res(D g) = 0`-from-regularity step
of the residue criterion in field-residue form (`D g` regular at `α` ⟹ no residue there). -/
theorem residueAt_eq_zero_of_regular (α : K) (A B : K[X]) (hB : B.eval α ≠ 0) :
    residueAt α (algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) B) = 0 := by
  have heq : algebraMap K[X] (RatFunc K) (X - C α)
        * (algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) B)
      = algebraMap K[X] (RatFunc K) ((X - C α) * A) / algebraMap K[X] (RatFunc K) B := by
    rw [map_mul, mul_div_assoc]
  rw [residueAt_of_mul_X_sub_C α _ ((X - C α) * A) B hB heq, eval_mul, eval_sub, eval_X, eval_C,
    sub_self, zero_mul, zero_div]

open scoped Classical in
/-- For `D = (X − α)·E` with `E(α) ≠ 0`, `residueAt α (A/D) = A(α)/D'(α)`. -/
theorem residueAt_div_eq_residue (A E : K[X]) (α : K) (hE : E.eval α ≠ 0) :
    residueAt α (algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) ((X - C α) * E))
      = A.eval α / (derivative ((X - C α) * E)).eval α := by
  rw [residue_eq_eval_div_eval_derivative]
  refine residueAt_of_mul_X_sub_C α _ A E hE ?_
  have hXne : algebraMap K[X] (RatFunc K) (X - C α) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (X_sub_C_ne_zero α)
  have hEne : algebraMap K[X] (RatFunc K) E ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (fun h0 => hE (by rw [h0, eval_zero]))
  rw [map_mul]
  field_simp

/-- For `N = (X − α)^k · N₁`, `(X − α)·N' = (X − α)^k · (k·N₁ + (X − α)·N₁')`. -/
theorem mul_X_sub_C_derivative_pow_mul (α : K) (k : ℕ) (N₁ : K[X]) :
    (X - C α) * derivative ((X - C α) ^ k * N₁)
      = (X - C α) ^ k * (C (k : K) * N₁ + (X - C α) * derivative N₁) := by
  rw [derivative_mul, derivative_pow, derivative_X_sub_C, mul_one]
  cases k with
  | zero => simp
  | succ m => rw [Nat.add_sub_cancel]; ring

open scoped Differential in
/-- `logDeriv (algebraMap N) = algebraMap (N') / algebraMap N` in `K(x)`. -/
theorem logDeriv_algebraMap_eq (N : K[X]) :
    Differential.logDeriv (algebraMap K[X] (RatFunc K) N)
      = algebraMap K[X] (RatFunc K) (derivative N) / algebraMap K[X] (RatFunc K) N := by
  rw [Differential.logDeriv,
    show (algebraMap K[X] (RatFunc K) N)′ = ratFuncDeriv _ from rfl, ratFuncDeriv_algebraMap]

open scoped Classical in
open scoped Differential in
/-- `residueAt α (logDeriv N) = (rootMultiplicity α N : K)` for `N ≠ 0`. -/
theorem residueAt_logDeriv_eq_rootMultiplicity (N : K[X]) (hN : N ≠ 0) (α : K) :
    residueAt α (Differential.logDeriv (algebraMap K[X] (RatFunc K) N))
      = (N.rootMultiplicity α : K) := by
  set k := N.rootMultiplicity α with hk
  obtain ⟨N₁, hNeq, hndvd⟩ := N.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hN α
  rw [← hk] at hNeq
  -- `N₁(α) ≠ 0` from `¬(X − α) ∣ N₁`
  have hN₁ : N₁.eval α ≠ 0 := fun h0 => hndvd (dvd_iff_isRoot.mpr h0)
  have hN₁0 : N₁ ≠ 0 := fun h0 => hN₁ (by rw [h0, eval_zero])
  rw [logDeriv_algebraMap_eq]
  -- reduce to the regular quotient `(k·N₁ + (X−α)·N₁')/N₁`
  refine (residueAt_of_mul_X_sub_C α _ (C (k : K) * N₁ + (X - C α) * derivative N₁) N₁ hN₁ ?_).trans ?_
  · -- the RatFunc identity, from the polynomial factorization, canceling `(X−α)^k`
    have hpoly : (X - C α) * derivative N
        = (X - C α) ^ k * (C (k : K) * N₁ + (X - C α) * derivative N₁) := by
      rw [hNeq]; exact mul_X_sub_C_derivative_pow_mul α k N₁
    have hN₁ne : algebraMap K[X] (RatFunc K) N₁ ≠ 0 :=
      (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hN₁0
    have hNne : algebraMap K[X] (RatFunc K) N ≠ 0 :=
      (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hN
    have hpkne : algebraMap K[X] (RatFunc K) ((X - C α) ^ k) ≠ 0 :=
      (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (pow_ne_zero _ (X_sub_C_ne_zero α))
    rw [← mul_div_assoc, ← map_mul, hpoly, hNeq]
    simp only [map_mul]
    rw [mul_div_mul_left (G₀ := RatFunc K) _ _ hpkne]
  · -- evaluate `(k·N₁ + (X−α)·N₁')/N₁` at `α`: numerator `= k·N₁(α)`, ratio `= k`
    simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X, sub_self, zero_mul, add_zero]
    rw [mul_div_assoc, div_self hN₁, mul_one]

open scoped Classical in
/-- If `(X − α)·f = a/b` and `(X − α)·g = c/d` with `b(α), d(α) ≠ 0`, then
`residueAt α (f − g) = a(α)/b(α) − c(α)/d(α)`. -/
theorem residueAt_sub_of_witnesses (α : K) (f g : RatFunc K) (a b c d : K[X])
    (hb : b.eval α ≠ 0) (hd : d.eval α ≠ 0)
    (hf : algebraMap K[X] (RatFunc K) (X - C α) * f
      = algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) b)
    (hg : algebraMap K[X] (RatFunc K) (X - C α) * g
      = algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) d) :
    residueAt α (f - g) = a.eval α / b.eval α - c.eval α / d.eval α := by
  have hbne : algebraMap K[X] (RatFunc K) b ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (fun h0 => hb (by rw [h0, eval_zero]))
  have hdne : algebraMap K[X] (RatFunc K) d ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (fun h0 => hd (by rw [h0, eval_zero]))
  have hbd : (b * d).eval α ≠ 0 := by rw [eval_mul]; exact mul_ne_zero hb hd
  rw [residueAt_of_mul_X_sub_C α (f - g) (a * d - c * b) (b * d) hbd ?_]
  · rw [eval_sub, eval_mul, eval_mul, eval_mul, div_sub_div _ _ hb hd]
    ring_nf
  · rw [mul_sub, hf, hg, map_sub, map_mul, map_mul, map_mul, div_sub_div _ _ hbne hdne,
      mul_comm (algebraMap K[X] (RatFunc K) c)]

open scoped Classical in
open scoped Differential in
/-- Pole-free witness: `(X − α)·logDeriv N = (k·N₁ + (X − α)·N₁')/N₁` with `N₁(α) ≠ 0`,
`k = rootMultiplicity α N`. -/
theorem mul_X_sub_C_logDeriv_reduced (N : K[X]) (hN : N ≠ 0) (α : K) :
    ∃ N₁ : K[X], N₁.eval α ≠ 0 ∧
      algebraMap K[X] (RatFunc K) (X - C α)
          * Differential.logDeriv (algebraMap K[X] (RatFunc K) N)
        = algebraMap K[X] (RatFunc K) (C (N.rootMultiplicity α : K) * N₁ + (X - C α) * derivative N₁)
          / algebraMap K[X] (RatFunc K) N₁ := by
  set k := N.rootMultiplicity α with hk
  obtain ⟨N₁, hNeq, hndvd⟩ := N.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hN α
  rw [← hk] at hNeq
  have hN₁ : N₁.eval α ≠ 0 := fun h0 => hndvd (dvd_iff_isRoot.mpr h0)
  refine ⟨N₁, hN₁, ?_⟩
  have hN₁0 : N₁ ≠ 0 := fun h0 => hN₁ (by rw [h0, eval_zero])
  have hpoly : (X - C α) * derivative N
      = (X - C α) ^ k * (C (k : K) * N₁ + (X - C α) * derivative N₁) := by
    rw [hNeq]; exact mul_X_sub_C_derivative_pow_mul α k N₁
  have hpkne : algebraMap K[X] (RatFunc K) ((X - C α) ^ k) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (pow_ne_zero _ (X_sub_C_ne_zero α))
  rw [logDeriv_algebraMap_eq, ← mul_div_assoc, ← map_mul, hpoly, hNeq]
  simp only [map_mul]
  rw [mul_div_mul_left (G₀ := RatFunc K) _ _ hpkne]

open scoped Classical in
open scoped Differential in
/-- `residueAt α (logDeriv (N/M)) = (rootMultiplicity α N − rootMultiplicity α M : K)` for `N, M ≠ 0`. -/
theorem residueAt_logDeriv_div_eq_int (N M : K[X]) (hN : N ≠ 0) (hM : M ≠ 0) (α : K) :
    residueAt α (Differential.logDeriv (algebraMap K[X] (RatFunc K) N
        / algebraMap K[X] (RatFunc K) M))
      = ((N.rootMultiplicity α : ℤ) - (M.rootMultiplicity α : ℤ) : K) := by
  obtain ⟨N₁, hN₁, hNwit⟩ := mul_X_sub_C_logDeriv_reduced N hN α
  obtain ⟨M₁, hM₁, hMwit⟩ := mul_X_sub_C_logDeriv_reduced M hM α
  have hdiv : Differential.logDeriv (algebraMap K[X] (RatFunc K) N
        / algebraMap K[X] (RatFunc K) M)
      = Differential.logDeriv (algebraMap K[X] (RatFunc K) N)
        - Differential.logDeriv (algebraMap K[X] (RatFunc K) M) :=
    Differential.logDeriv_div _ _
      ((map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hN)
      ((map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hM)
  rw [hdiv, residueAt_sub_of_witnesses α _ _ _ N₁ _ M₁ hN₁ hM₁ hNwit hMwit]
  simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X, sub_self, zero_mul, add_zero]
  rw [mul_div_assoc, div_self hN₁, mul_one, mul_div_assoc, div_self hM₁, mul_one]
  push_cast
  ring

open scoped Classical in
open scoped Differential in
/-- Over an algebraically closed field, if `A/D = logDeriv u` (`D` separable, `u ≠ 0`), then every
residue `A(α)/D'(α)` at a root `α` of `D` is an integer in `K`. -/
theorem integer_residues_of_isLogDeriv [IsAlgClosed K] (A D : K[X]) (hD : D.Separable)
    (u : RatFunc K) (hu : u ≠ 0)
    (hlog : algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) D
      = Differential.logDeriv u) (α : K) (hα : D.IsRoot α) :
    ∃ n : ℤ, A.eval α / (derivative D).eval α = (n : K) := by
  -- `D = (X − α)·E` with `E(α) ≠ 0` (`α` a simple root of squarefree `D`)
  have hD0 : D ≠ 0 := hD.ne_zero
  have hmult : D.rootMultiplicity α = 1 :=
    le_antisymm (rootMultiplicity_le_one_of_separable hD α)
      ((rootMultiplicity_pos hD0).mpr hα)
  obtain ⟨E, hDeq, hndvd⟩ := D.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hD0 α
  rw [hmult, pow_one] at hDeq
  have hE : E.eval α ≠ 0 := fun h0 => hndvd (dvd_iff_isRoot.mpr h0)
  -- write `u = num u / denom u` (both nonzero)
  have hNu : RatFunc.num u ≠ 0 := RatFunc.num_ne_zero hu
  have hMu : RatFunc.denom u ≠ 0 := RatFunc.denom_ne_zero u
  refine ⟨(RatFunc.num u).rootMultiplicity α - (RatFunc.denom u).rootMultiplicity α, ?_⟩
  -- the residue read two ways via the hypothesis `A/D = logDeriv u`
  have hres1 : residueAt α (algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) D)
      = A.eval α / (derivative D).eval α := by
    rw [hDeq]; exact residueAt_div_eq_residue A E α hE
  have hres2 : residueAt α (Differential.logDeriv u)
      = (((RatFunc.num u).rootMultiplicity α : ℤ)
          - ((RatFunc.denom u).rootMultiplicity α : ℤ) : K) := by
    conv_lhs => rw [← RatFunc.num_div_denom u]
    exact residueAt_logDeriv_div_eq_int (RatFunc.num u) (RatFunc.denom u) hNu hMu α
  rw [← hres1, hlog, hres2]
  push_cast
  ring

open scoped Classical in
open scoped Differential in
-- The `⟹` direction: a logarithmic-derivative `A/D` has integer residues at the roots of `D`.
/-- `Lagrange.nodal s id` is separable. -/
theorem separable_nodal (s : Finset K) : (Lagrange.nodal s id).Separable := by
  rw [Lagrange.nodal_eq]
  exact separable_prod_X_sub_C_iff'.mpr (fun x _ y _ h => h)

open scoped Classical in
open scoped Differential in
/-- Over an algebraically closed field, `A / (Lagrange.nodal s id)` (`deg A < #s`) is a logarithmic
derivative of some nonzero `u` iff every residue `A(α)/D'(α)` (`α ∈ s`) is an integer in `K`. -/
theorem isLogDeriv_iff_integer_residues [IsAlgClosed K] (s : Finset K) (A : K[X])
    (hA : A.degree < s.card) :
    (∃ u : RatFunc K, u ≠ 0 ∧
        algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
          = Differential.logDeriv u)
      ↔ (∀ α ∈ s, ∃ n : ℤ,
          A.eval α / eval α (derivative (Lagrange.nodal s id)) = (n : K)) := by
  constructor
  · rintro ⟨u, hu, hlog⟩ α hα
    refine integer_residues_of_isLogDeriv A (Lagrange.nodal s id) (separable_nodal s) u hu hlog α ?_
    exact Lagrange.eval_nodal_at_node (v := id) hα
  · intro hint
    obtain ⟨u, hu, hlog⟩ := isLogDeriv_of_integer_residues s A hA
      (fun α hα => (hint α hα).imp fun _ h => h.symm)
    exact ⟨u, hu, hlog⟩

end DeepWiki.SymbolicIntegration
