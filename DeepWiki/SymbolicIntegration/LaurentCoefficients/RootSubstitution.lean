import DeepWiki.SymbolicIntegration.LaurentCoefficients.FractionInvariant

/-! # Laurent root-substitution bridge

Root-evaluation and Taylor-coefficient bridges for the Laurent-coefficient engine. -/


open Polynomial MvPolynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ## The root-evaluation `Qᵢⱼ(α) = Pᵢⱼ(α, Dᵢ,α(α), …)` -/

/-- `(laurentSubst ((x−α)·Diα) (some k)).eval α = (derivative^[k] Diα).eval α`: the substitution's root
value. -/
theorem eval_laurentSubst_some [CharZero K] (Diα : K[X]) (α : K) (k : ℕ) :
    (laurentSubst ((Polynomial.X - Polynomial.C α) * Diα) (some k)).eval α
      = (derivative^[k] Diα).eval α := by
  unfold laurentSubst
  rw [Polynomial.eval_mul, Polynomial.eval_C, eval_iterate_derivative_X_sub_C_mul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_add_one_ne_zero (R := K) k), one_mul]

/-- `Qᵢⱼ(α) = Pᵢⱼ(α, Dᵢ,α(α), …)`: at a root `α` of `Dᵢ = (x−α)·Dᵢ,α`, the `Qᵢⱼ` substitution evaluates
to `aeval (substEvalAt Diα α) (laurentNum …)`. -/
theorem laurentQ_eval_at_root [CharZero K] (A D Diα : K[X]) (α : K) (i j : ℕ) :
    (laurentQ A D ((Polynomial.X - Polynomial.C α) * Diα) i j).eval α
      = MvPolynomial.aeval (substEvalAt Diα α)
          (laurentNum A (laurentE D ((Polynomial.X - Polynomial.C α) * Diα) i) i (i - j)) := by
  unfold laurentQ
  rw [eval_aeval_diffPoly]
  have hfg : (fun v => (laurentSubst ((Polynomial.X - Polynomial.C α) * Diα) v).eval α) = substEvalAt Diα α := by
    funext v
    cases v with
    | none => simp [laurentSubst, substEvalAt]
    | some k => rw [eval_laurentSubst_some]; rfl
  rw [hfg]

/-! ## The specialized recursion invariant in `K(x) = RatFunc K` -/

/-- The genuine `hᵢ,α`-denominator `Dᵢ,α^{i+d}·Eᵢ^{d+1} ∈ K[x]` (`= σα (lDenom Ei i d)`). -/
noncomputable def lDenomα (Ei Diα : K[X]) (i d : ℕ) : K[X] := Diα ^ (i + d) * Ei ^ (d + 1)

/-- `diffSubst Diα (lDenom Ei i d) = lDenomα Ei Diα i d`. -/
theorem diffSubst_lDenom (Ei Diα : K[X]) (i d : ℕ) :
    diffSubst Diα (lDenom Ei i d) = lDenomα Ei Diα i d := by
  unfold lDenom lDenomα
  rw [map_mul, map_pow, map_pow, diffSubst_X_some Diα 0, diffSubst_dpEmbed,
    Function.iterate_zero_apply]

/-- `lDenomα Ei Diα i d ≠ 0` for `Ei, Diα ≠ 0`. -/
theorem lDenomα_ne_zero {Ei Diα : K[X]} (i d : ℕ) (hEi : Ei ≠ 0) (hDiα : Diα ≠ 0) :
    lDenomα Ei Diα i d ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ hDiα) (pow_ne_zero _ hEi)

/-- The genuine `hᵢ,α^{(d)}/d!` fraction `σα(Pᵢ,d)/(Dᵢ,α^{i+d}·Eᵢ^{d+1}) ∈ K(x)`. -/
noncomputable def lFracα (A Ei Diα : K[X]) (i d : ℕ) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (diffSubst Diα (laurentNum A Ei i d)) /
    algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i d)

/-- `hᵢ,α = A/(Dᵢ,α^i·Eᵢ)` in `K(x)`: the genuine rational function the engine differentiates. -/
noncomputable def hFracα (A Ei Diα : K[X]) (i : ℕ) : RatFunc K :=
  algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i 0)

/-- `lFracα` base case: `lFracα A Ei Diα i 0 = hFracα A Ei Diα i`. -/
theorem lFracα_zero (A Ei Diα : K[X]) (i : ℕ) : lFracα A Ei Diα i 0 = hFracα A Ei Diα i := by
  unfold lFracα hFracα; rw [laurentNum_zero, diffSubst_dpEmbed]

/-- The reduced quotient-rule numerator in `K[x]` (`= σα` of `reduced_num`):
`(σα Pᵢ,d)'·denomα_d − (σα Pᵢ,d)·denomα_d' = Dᵢ,α^m·Eᵢ^d·((d+1)·σα Pᵢ,d₊₁)`. -/
theorem reduced_numα [CharZero K] (A Ei Diα : K[X]) (i d m : ℕ) (hm : i + d = m + 1) :
    derivative (diffSubst Diα (laurentNum A Ei i d)) * lDenomα Ei Diα i d
        - diffSubst Diα (laurentNum A Ei i d) * derivative (lDenomα Ei Diα i d)
      = Diα ^ m * Ei ^ d *
          (((d : K[X]) + 1) * diffSubst Diα (laurentNum A Ei i (d + 1))) := by
  have h := congrArg (diffSubst Diα) (reduced_num A Ei i d m hm)
  rw [map_sub, map_mul, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow,
    diffSubst_X_some Diα 0, Function.iterate_zero_apply, diffSubst_dpEmbed] at h
  -- convert both `ddx`-images to genuine derivatives and the `lDenom`-image to `lDenomα`
  rw [diffSubst_ddx, diffSubst_ddx, diffSubst_lDenom] at h
  -- `diffSubst (C ((d:K)+1)) = C ((d:K)+1)` as a constant in `K[x]`
  rw [h, diffSubst_C, Polynomial.C_add, Polynomial.C_eq_natCast, Polynomial.C_1]

/-- The recursion step in `K(x)`: `ratFuncKDeriv (lFracα A Ei Diα i d) = (d+1)·lFracα A Ei Diα i (d+1)`.
Requires `0 < i`, `Ei ≠ 0`, `Diα ≠ 0`. -/
theorem ratFuncKDeriv_lFracα [CharZero K] (A Ei Diα : K[X]) (i d : ℕ) (hi : 0 < i) (hEi : Ei ≠ 0)
    (hDiα : Diα ≠ 0) :
    ratFuncKDeriv (lFracα A Ei Diα i d) = ((d : K) + 1) • lFracα A Ei Diα i (d + 1) := by
  obtain ⟨m, hm⟩ : ∃ m, i + d = m + 1 := ⟨i + d - 1, by omega⟩
  have hden : (algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i d)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (lDenomα_ne_zero i d hEi hDiα)
  have hden1 : (algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i (d + 1))) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (lDenomα_ne_zero i (d + 1) hEi hDiα)
  -- the bundled `ratFuncKDeriv` on an embedded polynomial is the embedded `derivative`
  have hk : ∀ p : K[X], ratFuncKDeriv (algebraMap K[X] (RatFunc K) p)
      = algebraMap K[X] (RatFunc K) (derivative p) := fun p => ratFuncDeriv_algebraMap p
  rw [lFracα, lFracα, Derivation.leibniz_div, hk, hk]
  -- all `•` on `RatFunc K` are the field self-action; the RHS `K`-smul becomes `algebraMap`
  simp only [smul_eq_mul, Algebra.smul_def]
  -- combine the numerator with the polynomial identity, clear denominators
  set Pd := diffSubst Diα (laurentNum A Ei i d)
  set Pd1 := diffSubst Diα (laurentNum A Ei i (d + 1))
  set bd := algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i d) with hbd
  set bd1 := algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i (d + 1)) with hbd1
  have hnum : bd⁻¹ ^ 2 * (bd * algebraMap K[X] (RatFunc K) (derivative Pd)
        - algebraMap K[X] (RatFunc K) Pd * algebraMap K[X] (RatFunc K) (derivative (lDenomα Ei Diα i d)))
      = bd⁻¹ ^ 2 * algebraMap K[X] (RatFunc K)
          (derivative Pd * lDenomα Ei Diα i d - Pd * derivative (lDenomα Ei Diα i d)) := by
    rw [map_sub, map_mul, map_mul, hbd]; ring
  rw [hnum, reduced_numα A Ei Diα i d m hm]
  -- convert the `K`-scalar `algebraMap K (RatFunc K) ((d:K)+1)` to `algebraMap K[X] (Polynomial.C …)`
  rw [hbd, hbd1, show (algebraMap K (RatFunc K) ((d : K) + 1))
      = algebraMap K[X] (RatFunc K) (Polynomial.C ((d : K) + 1)) by
        rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]]
  have hbd2 : (algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i d)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (lDenomα_ne_zero i d hEi hDiα)
  have hbd12 : (algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i (d + 1))) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (lDenomα_ne_zero i (d + 1) hEi hDiα)
  have hbd2sq : (algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i d ^ 2)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero 2 (lDenomα_ne_zero i d hEi hDiα))
  rw [inv_pow, ← map_pow, ← div_eq_inv_mul, ← mul_div_assoc, ← map_mul,
    div_eq_div_iff hbd2sq hbd12, ← map_mul, ← map_mul]
  congr 1
  -- the `K[x]` polynomial identity
  have hsucc : lDenomα Ei Diα i (d + 1) = Diα ^ m * Ei ^ d * (Diα * Ei) ^ 2 := by
    unfold lDenomα; rw [show i + (d + 1) = m + 1 + 1 from by omega,
      show d + 1 + 1 = (d + 1) + 1 from rfl, pow_succ, pow_succ, pow_succ, pow_succ]; ring
  have hdfac : lDenomα Ei Diα i d = Diα ^ m * Ei ^ d * (Diα * Ei) := by
    unfold lDenomα; rw [hm, pow_succ]; ring
  rw [hsucc, hdfac, Polynomial.C_add, Polynomial.C_eq_natCast, Polynomial.C_1]
  ring

/-- The specialized recursion invariant in `K(x)`:
`(d/dx)^[d] hᵢ,α = d! · (σα(laurentNum A Eᵢ i d) / (Dᵢ,α^{i+d}·Eᵢ^{d+1}))` for `hᵢ,α = A/(Dᵢ,α^i·Eᵢ)`.
Requires `0 < i`, `Ei ≠ 0`, `Diα ≠ 0`. -/
theorem iterate_ratFuncKDeriv_hFracα [CharZero K] (A Ei Diα : K[X]) (i : ℕ) (hi : 0 < i)
    (hEi : Ei ≠ 0) (hDiα : Diα ≠ 0) (d : ℕ) :
    (ratFuncKDeriv^[d]) (hFracα A Ei Diα i) = (d.factorial : K) • lFracα A Ei Diα i d := by
  induction d with
  | zero => rw [Function.iterate_zero_apply, Nat.factorial_zero, Nat.cast_one, one_smul, lFracα_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.map_smul,
      ratFuncKDeriv_lFracα A Ei Diα i n hi hEi hDiα, smul_smul, Nat.factorial_succ]
    congr 1
    push_cast; ring

/-! ## The root-value bridge `σα(Pᵢ,d)(α) = Qᵢⱼ(α)` -/

/-- The bridge `(σα(laurentNum …)).eval α = (laurentQ …).eval α`: both are
`aeval (substEvalAt Diα α) (laurentNum …)`. -/
theorem eval_diffSubst_laurentNum_eq_laurentQ_eval [CharZero K] (A D Diα : K[X]) (α : K) (i j : ℕ) :
    Polynomial.eval α
        (diffSubst Diα (laurentNum A (laurentE D ((Polynomial.X - Polynomial.C α) * Diα) i) i (i - j)))
      = (laurentQ A D ((Polynomial.X - Polynomial.C α) * Diα) i j).eval α := by
  rw [eval_diffSubst, laurentQ_eval_at_root]

/-- The general engine-output evaluation
`(laurentH A D Di i j).eval α = Qᵢⱼ(α)·(1/Eᵢ(α))^{i−j+1}·(1/Dᵢ'(α))^{2i−j}` at a root `α` of the monic
`Dᵢ`, using `Bᵢ(α) = 1/Eᵢ(α)`, `Cᵢ(α) = 1/Dᵢ'(α)`. -/
theorem eval_laurentH {A D Di : K[X]} {α : K} (i j : ℕ) (hDi : Di.Monic) (hα : Di.eval α = 0)
    (hcopE : IsCoprime (laurentE D Di i) Di) (hcopD : IsCoprime (derivative Di) Di) :
    (laurentH A D Di i j).eval α
      = (laurentQ A D Di i j).eval α * (1 / (laurentE D Di i).eval α) ^ (i - j + 1)
          * (1 / (derivative Di).eval α) ^ (2 * i - j) := by
  rw [laurentH, eval_modByMonic_of_root hDi hα, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_pow]
  have hB : (bezoutE D Di i).eval α = 1 / (laurentE D Di i).eval α :=
    eq_one_div_of_mul_eq_one_left (bezoutE_mul_laurentE_eval i hDi hα hcopE)
  have hC : (bezoutDeriv Di).eval α = 1 / (derivative Di).eval α :=
    eq_one_div_of_mul_eq_one_left (bezoutDeriv_mul_derivative_eval hDi hα hcopD)
  rw [hB, hC]

/-- The engine output from the genuine `hᵢ,α`-numerator: for `Dᵢ = (x−α)·Dᵢ,α`,
`(laurentH A D Di i j).eval α = (diffSubst Diα (laurentNum …)).eval α · (1/Eᵢ(α))^{i−j+1}·(1/Dᵢ'(α))^{2i−j}`. -/
theorem eval_laurentH_eq_diffSubst_laurentNum [CharZero K] {A D Di Diα : K[X]} {α : K} (i j : ℕ)
    (hDi : Di.Monic) (hα : Di.eval α = 0) (hfac : Di = (Polynomial.X - Polynomial.C α) * Diα)
    (hcopE : IsCoprime (laurentE D Di i) Di) (hcopD : IsCoprime (derivative Di) Di) :
    (laurentH A D Di i j).eval α
      = Polynomial.eval α (diffSubst Diα (laurentNum A (laurentE D Di i) i (i - j)))
        * (1 / (laurentE D Di i).eval α) ^ (i - j + 1)
        * (1 / (derivative Di).eval α) ^ (2 * i - j) := by
  rw [eval_laurentH i j hDi hα hcopE hcopD]
  congr 2
  -- `Qᵢⱼ(α) = σα(Pᵢ,i−j)(α)`: the engine substitution value equals the genuine-hom numerator value
  rw [laurentQ, eval_aeval_diffPoly, eval_diffSubst]
  have hf : (fun v => Polynomial.eval α (laurentSubst Di v)) = substEvalAt Diα α := by
    funext v
    cases v with
    | none => simp [laurentSubst, substEvalAt]
    | some k => subst hfac; rw [eval_laurentSubst_some]; simp [substEvalAt]
  rw [hf]

/-! ## `Hᵢⱼ(α)` is the order-`(i−j)` Taylor coefficient of `hᵢ,α` -/

/-- `(lDenomα Ei Diα i d).eval α ≠ 0` when `Ei(α), Diα(α) ≠ 0`. -/
theorem eval_lDenomα_ne_zero {Ei Diα : K[X]} {α : K} (i d : ℕ) (hEi : Ei.eval α ≠ 0)
    (hDiα : Diα.eval α ≠ 0) : (lDenomα Ei Diα i d).eval α ≠ 0 := by
  unfold lDenomα
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_pow]
  exact mul_ne_zero (pow_ne_zero _ hDiα) (pow_ne_zero _ hEi)

/-- Eval of `lFracα` at `α`:
`RatFunc.eval id α (lFracα A Ei Diα i d) = (diffSubst Diα (laurentNum …)).eval α / (lDenomα …).eval α`. -/
theorem eval_lFracα {A Ei Diα : K[X]} {α : K} (i d : ℕ) (hEi : Ei.eval α ≠ 0)
    (hDiα : Diα.eval α ≠ 0) :
    RatFunc.eval (RingHom.id K) α (lFracα A Ei Diα i d)
      = (diffSubst Diα (laurentNum A Ei i d)).eval α / (lDenomα Ei Diα i d).eval α := by
  rw [lFracα, eval_algebraMap_div α _ _ (eval_lDenomα_ne_zero i d hEi hDiα)]

/-- Eval of a `K`-scaled `lFracα` at `α`:
`RatFunc.eval id α (c • lFracα A Ei Diα i d) = c · ((diffSubst Diα (laurentNum …)).eval α / (lDenomα …).eval α)`. -/
theorem eval_smul_lFracα {A Ei Diα : K[X]} {α : K} (c : K) (i d : ℕ) (hEi : Ei.eval α ≠ 0)
    (hDiα : Diα.eval α ≠ 0) :
    RatFunc.eval (RingHom.id K) α (c • lFracα A Ei Diα i d)
      = c * ((diffSubst Diα (laurentNum A Ei i d)).eval α / (lDenomα Ei Diα i d).eval α) := by
  have hsmul : c • lFracα A Ei Diα i d
      = algebraMap K[X] (RatFunc K) (Polynomial.C c * diffSubst Diα (laurentNum A Ei i d))
        / algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i d) := by
    rw [lFracα, RatFunc.smul_eq_C_mul, ← RatFunc.algebraMap_C, map_mul, mul_div_assoc]
  rw [hsmul, eval_algebraMap_div α _ _ (eval_lDenomα_ne_zero i d hEi hDiα),
    Polynomial.eval_mul, Polynomial.eval_C, mul_div_assoc]

/-- The specialized invariant evaluated at the root `α`:
`RatFunc.eval id α ((ratFuncKDeriv^[d]) (hFracα A Ei Diα i)) = d!·(diffSubst Diα (laurentNum …)).eval α / (lDenomα …).eval α`,
for `0 < i`, `Ei(α), Diα(α) ≠ 0`. -/
theorem eval_ratFuncKDeriv_iterate_hFracα_at_root [CharZero K] {A Ei Diα : K[X]} {α : K} (i : ℕ)
    (hi : 0 < i) (hEi0 : Ei ≠ 0) (hDiα0 : Diα ≠ 0) (hEi : Ei.eval α ≠ 0) (hDiα : Diα.eval α ≠ 0)
    (d : ℕ) :
    RatFunc.eval (RingHom.id K) α ((ratFuncKDeriv^[d]) (hFracα A Ei Diα i))
      = (d.factorial : K) * (diffSubst Diα (laurentNum A Ei i d)).eval α
          / (lDenomα Ei Diα i d).eval α := by
  rw [iterate_ratFuncKDeriv_hFracα A Ei Diα i hi hEi0 hDiα0 d,
    eval_smul_lFracα _ i d hEi hDiα, mul_div_assoc]

/-- A regular root setup for the Laurent coefficient engine at multiplicity `i`. -/
structure IsLaurentRegularRoot (D Di Diα : K[X]) (α : K) (i : ℕ) : Prop where
  /-- `Di` is monic. -/
  monic : Di.Monic
  /-- `α` is a root of `Di`. -/
  root : Di.eval α = 0
  /-- `Di` factors as `(X - C α) * Diα`. -/
  factor : Di = (Polynomial.X - Polynomial.C α) * Diα
  /-- The complementary factor `Eᵢ` is coprime to `Di`. -/
  coprime_laurentE : IsCoprime (laurentE D Di i) Di
  /-- The derivative `Di'` is coprime to `Di`. -/
  coprime_derivative : IsCoprime (derivative Di) Di
  /-- The complementary factor `Eᵢ` does not vanish at `α`. -/
  laurentE_eval_ne : (laurentE D Di i).eval α ≠ 0
  /-- The linear cofactor `Diα` does not vanish at `α`. -/
  cofactor_eval_ne : Diα.eval α ≠ 0

/-- `Hᵢⱼ(α)` is the order-`(i−j)` Taylor coefficient of `hᵢ,α = (A/D)(x−α)ⁱ`:
`(laurentH A D Di i j).eval α = ((i−j)!)⁻¹ · RatFunc.eval id α ((ratFuncKDeriv^[i−j]) (hFracα A Eᵢ Diα i))`,
for `Dᵢ = (x−α)·Dᵢ,α` monic, `j ≤ i`, `Eᵢ(α), Dᵢ,α(α) ≠ 0`. -/
theorem eval_laurentH_eq_taylor_coeff [CharZero K] {A D Di Diα : K[X]} {α : K} (i j : ℕ)
    (hi : 0 < i) (hji : j ≤ i) (hroot : IsLaurentRegularRoot D Di Diα α i) :
    (laurentH A D Di i j).eval α
      = (((i - j).factorial : K))⁻¹
          * RatFunc.eval (RingHom.id K) α
              ((ratFuncKDeriv^[i - j]) (hFracα A (laurentE D Di i) Diα i)) := by
  -- abbreviations
  set Ei := laurentE D Di i with hEidef
  have hEi0 : Ei ≠ 0 := fun h => hroot.laurentE_eval_ne (by rw [← hEidef, h, Polynomial.eval_zero])
  have hDiα0 : Diα ≠ 0 := fun h => hroot.cofactor_eval_ne (by rw [h, Polynomial.eval_zero])
  -- evaluate Stage I at the root
  rw [eval_ratFuncKDeriv_iterate_hFracα_at_root i hi hEi0 hDiα0
    hroot.laurentE_eval_ne hroot.cofactor_eval_ne (i - j)]
  -- the engine output, via Steps 2+3+5
  rw [eval_laurentH_eq_diffSubst_laurentNum i j hroot.monic hroot.root hroot.factor
    hroot.coprime_laurentE hroot.coprime_derivative, ← hEidef]
  -- the `(derivative Di)(α) = Diα(α)` cofactor identity
  rw [eval_derivative_of_X_sub_C_mul hroot.factor]
  -- the denominator `lDenomα Ei Diα i (i-j) (α) = Diα(α)^{i+(i-j)}·Ei(α)^{(i-j)+1}`
  unfold lDenomα
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_pow]
  -- index arithmetic: `i + (i-j) = 2i - j`
  have hidx : i + (i - j) = 2 * i - j := by omega
  rw [hidx]
  -- abbreviate the evaluated numerator and the two base values
  set N := (diffSubst Diα (laurentNum A Ei i (i - j))).eval α with hN
  set e := Ei.eval α with he
  set g := Diα.eval α with hg
  have hfact : ((i - j).factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (i - j)
  -- both sides are `N / (e^{i-j+1}·g^{2i-j})` (the `(i-j)!⁻¹·(i-j)!` cancels)
  rw [one_div, one_div, inv_pow, inv_pow]
  field_simp


end DeepWiki.SymbolicIntegration
