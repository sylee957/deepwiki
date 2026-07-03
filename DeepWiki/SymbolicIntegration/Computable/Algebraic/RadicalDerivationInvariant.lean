import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalExtension

/-! # The radical derivation invariant: `radDeriv` is a genuine derivation

`radDeriv` is additive and Leibniz over `K = CFieldSpec.K α` through the Horner bridge
`toPolyG : RadElem α → K[X]`: `toPolyG_radDeriv` identifies it with `Differential.implicitDeriv` for
`y' = ℓ·y` (`ℓ = f'/(nf)`); additivity is exact, and Leibniz holds modulo `radIdeal n f = (Xⁿ − C(toK f))`
when `n·toK f ≠ 0`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace RadElem

variable {α : Type*} [CField α]

/-! ### The natural-cast bridge `toK (cnatCastG k) = (k : K)` -/

variable [CFieldSpec α]

/-- `toK (cnatCastG k) = (k : K)`: the `k`-fold `CField.one` sum reads as the genuine natural cast in
`K`. The bridge that turns `radDeriv`'s `cnatCastG i` index-multiplier into `(i : K)`. -/
@[denote] theorem toK_cnatCastG (k : ℕ) : CFieldSpec.toK (CPolyG.cnatCastG k : α) = (k : CFieldSpec.K α) := by
  induction k with
  | zero => rw [CPolyG.cnatCastG, CFieldSpec.toK_zero, Nat.cast_zero]
  | succ n ih => rw [CPolyG.cnatCastG, CFieldSpec.toK_add, CFieldSpec.toK_one, ih, Nat.cast_succ,
      add_comm]

end RadElem

/-! ### The keystone: `radDeriv` realizes `implicitDeriv (C (toK ℓ) · X)`

Read through `toPolyG`, `radDeriv n f p` is `Differential.implicitDeriv (C(toK ℓ)·X) (toPolyG p)`, the
derivation extending the base coefficient derivation by `y' = ℓ·y`. -/

namespace RadElem

variable {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]

/-- The index-generalized diagonal map `radDerivFrom ℓ k p` = `(List.zipIdx p k).map (fun (a,i) ↦
D(a) + a·(i·ℓ))`: the body of `radDeriv` with the `zipIdx` start index exposed as `k` (so `radDeriv n f =
radDerivFrom (logDerRadicand n f) 0`). Generalizing `k` is what lets the closed-form `toPolyG` recursion
go through. -/
def radDerivFrom (ℓ : α) (k : ℕ) (p : RadElem α) : RadElem α :=
  (List.zipIdx p k).map (fun a =>
    CField.add (CDiffField.cderiv a.1) (CField.mul a.1 (CField.mul (CPolyG.cnatCastG a.2) ℓ)))

omit [CFieldSpec α] [CDiffFieldSpec α] in
/-- `radDeriv n f p = radDerivFrom (logDerRadicand n f) 0 p`: unfolds `radDeriv`'s `zipIdx`
(`List.zipIdx p = List.zipIdx p 0`) to the index-generalized form. -/
theorem radDeriv_eq_radDerivFrom (n : ℕ) (f : α) (p : RadElem α) :
    radDeriv n f p = radDerivFrom (logDerRadicand n f) 0 p := by
  rw [radDeriv, radDerivFrom]

/-- The closed `K[X]` form of the index-generalized diagonal map: `toPolyG (radDerivFrom ℓ k p) =
mapCoeffs(toPolyG p) + C(toK ℓ)·(X·derivative(toPolyG p) + (k:K[X])·toPolyG p)`. The `(k:K[X])·toPolyG p`
term is the contribution of the running `zipIdx` index. -/
theorem toPolyG_radDerivFrom (ℓ : α) (k : ℕ) (p : RadElem α) :
    CPolyG.toPolyG (radDerivFrom ℓ k p)
      = Differential.mapCoeffs (CPolyG.toPolyG p)
        + Polynomial.C (CFieldSpec.toK ℓ)
          * (X * Polynomial.derivative (CPolyG.toPolyG p)
              + (k : (CFieldSpec.K α)[X]) * CPolyG.toPolyG p) := by
  induction p generalizing k with
  | nil => simp [radDerivFrom]
  | cons a as ih =>
    rw [radDerivFrom, List.zipIdx_cons, List.map_cons]
    show CPolyG.toPolyG (CField.add (CDiffField.cderiv a)
          (CField.mul a (CField.mul (CPolyG.cnatCastG k) ℓ)) :: radDerivFrom ℓ (k + 1) as) = _
    rw [CPolyG.toPolyG_cons, CFieldSpec.toK_add, CFieldSpec.toK_mul, CFieldSpec.toK_mul,
      CDiffFieldSpec.toK_cderiv, toK_cnatCastG]
    rw [ih (k + 1), CPolyG.toPolyG_cons]
    -- expand `mapCoeffs (C(toK a) + X·toPolyG as)` and `derivative (C(toK a) + X·toPolyG as)` by the
    -- derivation/derivative product rules (`mapCoeffs X = 0`, `derivative X = 1`, `derivative C = 0`).
    have hmc : Differential.mapCoeffs (Polynomial.C (CFieldSpec.toK a) + X * CPolyG.toPolyG as)
        = Polynomial.C (Differential.deriv (CFieldSpec.toK a))
          + X * Differential.mapCoeffs (CPolyG.toPolyG as) := by
      rw [map_add, Differential.mapCoeffs_C, Derivation.leibniz, Differential.mapCoeffs_X, smul_zero,
        add_zero, smul_eq_mul]
    have hder : Polynomial.derivative (Polynomial.C (CFieldSpec.toK a) + X * CPolyG.toPolyG as)
        = CPolyG.toPolyG as + X * Polynomial.derivative (CPolyG.toPolyG as) := by
      rw [derivative_add, derivative_C, zero_add, derivative_mul, derivative_X, one_mul]
    rw [hmc, hder]
    simp only [map_add, map_mul, Polynomial.C_eq_natCast, Nat.cast_succ]
    ring

/-- `toPolyG (radDeriv n f p) = Differential.implicitDeriv (C (toK ℓ) · X) (toPolyG p)`
(`ℓ = f'/(nf)`): the diagonal derivation realizes `implicitDeriv` for `y' = ℓ·y`. -/
theorem toPolyG_radDeriv (n : ℕ) (f : α) (p : RadElem α) :
    CPolyG.toPolyG (radDeriv n f p)
      = Differential.implicitDeriv
          (Polynomial.C (CFieldSpec.toK (logDerRadicand n f)) * X) (CPolyG.toPolyG p) := by
  rw [radDeriv_eq_radDerivFrom, toPolyG_radDerivFrom]
  -- `implicitDeriv v q = mapCoeffs q + v · derivative q`; here `v = C(toK ℓ)·X`, and the `k = 0` index
  -- term `0·toPolyG p` vanishes.
  rw [Differential.implicitDeriv]
  simp only [Derivation.add_apply, Derivation.smul_apply, Derivation.restrictScalars_apply,
    Nat.cast_zero, zero_mul, add_zero, smul_eq_mul, derivative'_apply]
  ring

/-! ### Additivity: `radDeriv` commutes with `radAdd` -/

/-- `radDeriv` is additive: `toPolyG (radDeriv n f (radAdd a b)) = toPolyG (radDeriv n f a) +
toPolyG (radDeriv n f b)` in `K[X]`. -/
@[denote] theorem toPolyG_radDeriv_radAdd (n : ℕ) (f : α) (a b : RadElem α) :
    CPolyG.toPolyG (radDeriv n f (radAdd a b))
      = CPolyG.toPolyG (radDeriv n f a) + CPolyG.toPolyG (radDeriv n f b) := by
  rw [toPolyG_radDeriv, toPolyG_radDeriv, toPolyG_radDeriv, radAdd, CPolyG.toPolyG_caddG, map_add]

/-! ### Leibniz for `radMul`, modulo `Xⁿ − C(toK f)`

`radMul = radReduce ∘ cmulG` uses the `yⁿ = f` reduction, so the product rule holds in the carrier, i.e.
modulo the defining ideal `I = (Xⁿ − C(toK f))`: `radReduce` preserves the quotient, the crux
`D(Xⁿ − C(toK f)) ∈ I` lets `D` descend to `K[X] ⧸ I`, and free-polynomial Leibniz pushes through. -/

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **The top-coefficient split through `toPolyG`**: `toPolyG (p ++ q) = toPolyG p + X^(p.length) ·
toPolyG q`. The `append` homomorphism for the Horner bridge, the tool for peeling the top coefficient in
`radReduce`. -/
theorem toPolyG_append (p q : RadElem α) :
    CPolyG.toPolyG (p ++ q)
      = CPolyG.toPolyG p + X ^ (p : List α).length * CPolyG.toPolyG q := by
  induction p with
  | nil => simp
  | cons a as ih =>
    show CPolyG.toPolyG (a :: (as ++ q)) = _
    rw [CPolyG.toPolyG_cons, ih, CPolyG.toPolyG_cons]
    simp only [List.length_cons, pow_succ]
    ring

/-- **The radicand-defining ideal** `radIdeal n f = (Xⁿ − C(toK f)) ⊆ K[X]`: the principal ideal whose
quotient is the carrier `K[X]/(Xⁿ − C(toK f)) ≅ K(y)` with `yⁿ = toK f`. Leibniz for `radMul` holds
modulo this ideal. -/
noncomputable def radIdeal (n : ℕ) (f : α) : Ideal (CFieldSpec.K α)[X] :=
  Ideal.span {X ^ n - Polynomial.C (CFieldSpec.toK f)}

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **The radicand generator lies in its ideal** — `Xⁿ − C(toK f) ∈ radIdeal n f`. -/
theorem radicand_mem (n : ℕ) (f : α) :
    X ^ n - Polynomial.C (CFieldSpec.toK f) ∈ radIdeal n f :=
  Ideal.subset_span (Set.mem_singleton _)

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **`c · (Xⁿ − C(toK f)) ∈ radIdeal n f`** for any cofactor — the multiples of the radicand generator
used by the `radReduce` fold step. -/
theorem mul_radicand_mem (n : ℕ) (f : α) (c : (CFieldSpec.K α)[X]) :
    c * (X ^ n - Polynomial.C (CFieldSpec.toK f)) ∈ radIdeal n f :=
  Ideal.mul_mem_left _ _ (radicand_mem n f)

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **`Ideal.Quotient.mk` collapses `Xⁿ` to `C(toK f)`** — `mk (radIdeal n f) (Xⁿ) = mk (radIdeal n f)
(C(toK f))`: the defining relation `yⁿ = f` in the quotient `K[X] ⧸ (Xⁿ − C(toK f))`. -/
theorem mk_X_pow (n : ℕ) (f : α) :
    Ideal.Quotient.mk (radIdeal n f) (X ^ n)
      = Ideal.Quotient.mk (radIdeal n f) (Polynomial.C (CFieldSpec.toK f)) := by
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]; exact radicand_mem n f

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **One `radReduce` fold preserves the quotient**, in the form needed for the fuel induction: for a
**normalized** nonempty `q` of length `> n`, `mk (toPolyG (caddG (dropLast q) (cshiftG (len−1−n)
[am·f]))) = mk (toPolyG q)` with `am = getLast q`. The fold replaces the top coefficient `aₘ·X^{n+k}`
(index `m = len−1 ≥ n`) by `aₘ·f·Xᵏ`, subtracting `aₘ·Xᵏ·(Xⁿ − C(toK f)) ∈ radIdeal n f`. -/
theorem mk_toPolyG_radReduce_step (n : ℕ) (f : α) (q : RadElem α)
    (hqne : (q : List α) ≠ []) (hlen : n < (q : List α).length) :
    Ideal.Quotient.mk (radIdeal n f)
        (CPolyG.toPolyG (CPolyG.caddG (q : List α).dropLast
          (CPolyG.cshiftG ((q : List α).length - 1 - n)
            [CField.mul ((q : List α).getLast hqne) f])))
      = Ideal.Quotient.mk (radIdeal n f) (CPolyG.toPolyG q) := by
  -- the top-coefficient decomposition `q = dropLast q ++ [getLast q]`
  set am := (q : List α).getLast hqne with hamdef
  have hsplit : (q : List α).dropLast ++ [am] = q := List.dropLast_append_getLast hqne
  set m := (q : List α).dropLast.length with hmdef
  have hlenq : (q : List α).length = m + 1 := by
    conv_lhs => rw [← hsplit]; rw [List.length_append, List.length_singleton]
  have hge : n ≤ m := by rw [hlenq] at hlen; omega
  -- `toPolyG q = toPolyG (dropLast q) + X^m · C(toK am)`
  have htop : CPolyG.toPolyG q
      = CPolyG.toPolyG (q : List α).dropLast + X ^ m * Polynomial.C (CFieldSpec.toK am) := by
    conv_lhs => rw [← hsplit]
    rw [toPolyG_append, CPolyG.toPolyG_cons, CPolyG.toPolyG_nil, mul_zero, add_zero, ← hmdef]
  -- `toPolyG fold = toPolyG (dropLast q) + X^(m−n)·(C(toK am)·C(toK f))`
  have hkeq : (q : List α).length - 1 - n = m - n := by rw [hlenq]; omega
  have hfold : CPolyG.toPolyG (CPolyG.caddG (q : List α).dropLast
        (CPolyG.cshiftG ((q : List α).length - 1 - n) [CField.mul am f]))
      = CPolyG.toPolyG (q : List α).dropLast
        + X ^ (m - n) * (Polynomial.C (CFieldSpec.toK am) * Polynomial.C (CFieldSpec.toK f)) := by
    rw [hkeq]; simp [CFieldSpec.toK_mul]
  -- the `X^m` term of `toPolyG q` collapses, in the quotient, to `X^(m−n)·C(toK f)` (since `X^n ≡ C f`)
  have hXm : Ideal.Quotient.mk (radIdeal n f) (X ^ m)
      = Ideal.Quotient.mk (radIdeal n f) (X ^ (m - n)) * Ideal.Quotient.mk (radIdeal n f)
          (Polynomial.C (CFieldSpec.toK f)) := by
    rw [← mk_X_pow, ← map_mul, ← pow_add, show m - n + n = m by omega]
  rw [hfold, htop, map_add, map_add, map_mul, map_mul, map_mul, hXm]
  ring

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **`radReduce` preserves the quotient `K[X] ⧸ (Xⁿ − C(toK f))`**: `mk (toPolyG (radReduce n f fuel
p)) = mk (toPolyG p)` for any fuel. Each fold step preserves it (`mk_toPolyG_radReduce_step`); a fuel
induction over the loop. This is what makes `radMul ≡ ·` modulo the radicand ideal. -/
theorem mk_toPolyG_radReduce (n : ℕ) (f : α) (fuel : ℕ) (p : RadElem α) :
    Ideal.Quotient.mk (radIdeal n f) (CPolyG.toPolyG (radReduce n f fuel p))
      = Ideal.Quotient.mk (radIdeal n f) (CPolyG.toPolyG p) := by
  induction fuel generalizing p with
  | zero => rw [radReduce]
  | succ fuel ih =>
    rw [radReduce]
    by_cases hlen : (CPolyG.cnormG p : List α).length ≤ n
    · simp only [hlen, if_true, CPolyG.toPolyG_cnormG]
    · -- the loop folds the top coefficient and recurses; `ih` + one step + `toPolyG_cnormG`
      have hlt : n < (CPolyG.cnormG p : List α).length := Nat.lt_of_not_le hlen
      have hqne : (CPolyG.cnormG p : List α) ≠ [] := by
        intro h; rw [h] at hlt; simp at hlt
      simp only [hlen, if_false]
      rw [ih]
      -- match `radReduce`'s `getLast?.getD zero` to the step lemma's `getLast hqne`
      have hgl : (CPolyG.cnormG p : List α).getLast?.getD CField.zero
          = (CPolyG.cnormG p : List α).getLast hqne := by
        rw [List.getLast?_eq_some_getLast hqne, Option.getD_some]
      rw [hgl, mk_toPolyG_radReduce_step n f (CPolyG.cnormG p) hqne hlt, CPolyG.toPolyG_cnormG]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **`radMul` realizes the product modulo the ideal**: `mk (radIdeal n f) (toPolyG (radMul n f a b)) =
mk (radIdeal n f) (toPolyG a) · mk (radIdeal n f) (toPolyG b)`. `radMul = radReduce ∘ cmulG`, and
`radReduce` preserves the quotient (`mk_toPolyG_radReduce`) while `cmulG` realizes `K[X]`-multiplication
exactly (`toPolyG_cmulG`). The ring structure of the carrier `K[X] ⧸ (Xⁿ − C(toK f))`. -/
theorem mk_toPolyG_radMul (n : ℕ) (f : α) (a b : RadElem α) :
    Ideal.Quotient.mk (radIdeal n f) (CPolyG.toPolyG (radMul n f a b))
      = Ideal.Quotient.mk (radIdeal n f) (CPolyG.toPolyG a)
        * Ideal.Quotient.mk (radIdeal n f) (CPolyG.toPolyG b) := by
  rw [radMul, mk_toPolyG_radReduce, CPolyG.toPolyG_cmulG, map_mul]

/-! ### The crux `D(Xⁿ − C(toK f)) ∈ I` and the descent of `D` to the quotient

`D := implicitDeriv (C(toK ℓ)·X)` maps the defining ideal into itself, via the scalar identity
`n·ℓ·f = f'` (valid when `n·toK f ≠ 0`), so it descends to the quotient carrier. -/

omit [CDiffFieldSpec α] in
/-- **The defining scalar identity** `n · toK ℓ · toK f = toK f'` in `K` (with `ℓ = logDerRadicand n f =
f'/(nf)`), valid when `n·toK f ≠ 0` — the `nⁿ·y^{n−1}·y' = f'` relation read on `ℓ`. The algebraic heart
of the crux. -/
theorem toK_logDerRadicand_mul (n : ℕ) (f : α)
    (hnf : (n : CFieldSpec.K α) * CFieldSpec.toK f ≠ 0) :
    (n : CFieldSpec.K α) * CFieldSpec.toK (logDerRadicand n f) * CFieldSpec.toK f
      = CFieldSpec.toK (CDiffField.cderiv f) := by
  rw [logDerRadicand, CFieldSpec.toK_div, CFieldSpec.toK_mul, toK_cnatCastG]
  rw [mul_comm ((n : CFieldSpec.K α)) _, mul_assoc, div_mul_cancel₀ _ hnf]

/-- The crux: `D(Xⁿ − C(toK f)) ∈ radIdeal n f` for `D = implicitDeriv (C(toK ℓ)·X)`. Computes
`D(Xⁿ) = n·C(toK ℓ)·Xⁿ`, `D(C(toK f)) = C(toK f')`, collapses `Xⁿ ≡ C(toK f)`, and uses `n·ℓ·f = f'`
(needs `n·toK f ≠ 0`) — the relation making `y' = ℓ·y` a consistent derivation. -/
theorem implicitDeriv_radicand_mem (n : ℕ) (f : α)
    (hnf : (n : CFieldSpec.K α) * CFieldSpec.toK f ≠ 0) :
    Differential.implicitDeriv (Polynomial.C (CFieldSpec.toK (logDerRadicand n f)) * X)
        (X ^ n - Polynomial.C (CFieldSpec.toK f)) ∈ radIdeal n f := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, Derivation.leibniz_pow, Differential.implicitDeriv_X,
    Differential.implicitDeriv_C]
  -- turn the `n • X^(n-1) • (C ℓ · X)` term into pure multiplication INSIDE `mk`
  rw [nsmul_eq_mul, smul_eq_mul]
  -- collapse `X^(n-1)·X = X^n ≡ C(toK f)` in the quotient, and identify `n·ℓ·f = f'`
  rw [show (n : (CFieldSpec.K α)[X]) * (X ^ (n - 1) * (Polynomial.C (CFieldSpec.toK (logDerRadicand n f))
        * X))
      = Polynomial.C (CFieldSpec.toK (logDerRadicand n f)) * (n : (CFieldSpec.K α)[X]) * (X ^ (n - 1) * X)
      from by ring]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- `n = 0`: but `hnf` would force `0 ≠ 0`, contradiction
    rw [hn, Nat.cast_zero, zero_mul] at hnf; exact absurd rfl hnf
  · -- fold `X^(n-1)·X = X^n`, write `↑n = C(↑n:K)`, collapse `X^n ≡ C(toK f)`, combine to one `C`
    rw [← pow_succ, show n - 1 + 1 = n by omega, ← Polynomial.C_eq_natCast,
      show Polynomial.C (CFieldSpec.toK (logDerRadicand n f)) * Polynomial.C ((n : ℕ) : CFieldSpec.K α)
          * X ^ n
        = (Polynomial.C (CFieldSpec.toK (logDerRadicand n f)) * Polynomial.C ((n : ℕ) : CFieldSpec.K α))
          * X ^ n from by ring]
    rw [map_sub, map_mul, mk_X_pow, ← map_mul, ← map_mul, ← map_sub]
    -- the argument is `C (ℓ · n · f − f') = C 0 = 0` (`(toK f)′ = toK f'` via the spec bridge)
    rw [Ideal.Quotient.eq_zero_iff_mem, ← map_mul, ← map_sub, ← CDiffFieldSpec.toK_cderiv,
      show CFieldSpec.toK (logDerRadicand n f) * (n : CFieldSpec.K α) * CFieldSpec.toK f
            - CFieldSpec.toK (CDiffField.cderiv f) = 0 from by
        rw [← toK_logDerRadicand_mul n f hnf]; ring, map_zero]
    exact Ideal.zero_mem _

/-- **The `radDeriv` derivation maps `radIdeal n f` into itself** (`n·toK f ≠ 0`): for any `x ∈ radIdeal
n f`, `D x ∈ radIdeal n f` with `D = implicitDeriv (C(toK ℓ)·X)`. Since `radIdeal` is principal
(`x = c·(Xⁿ − C f)`) and `D` is a derivation, `D x = Dc·(Xⁿ − C f) + c·D(Xⁿ − C f) ∈ radIdeal n f` (both
summands, the second by the crux `implicitDeriv_radicand_mem`). This is the descent of `D` to the
quotient carrier. -/
theorem implicitDeriv_mem_radIdeal (n : ℕ) (f : α)
    (hnf : (n : CFieldSpec.K α) * CFieldSpec.toK f ≠ 0)
    {x : (CFieldSpec.K α)[X]} (hx : x ∈ radIdeal n f) :
    Differential.implicitDeriv (Polynomial.C (CFieldSpec.toK (logDerRadicand n f)) * X) x
      ∈ radIdeal n f := by
  rw [radIdeal, Ideal.mem_span_singleton'] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  -- `D(c·g) = c·D g + g·D c`: first summand in `I` by the crux (`D g ∈ I`), second since `g ∈ I`
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_right _ _ ?_)
  · exact implicitDeriv_radicand_mem n f hnf
  · exact radicand_mem n f

/-- **`D` descends to the quotient**: if `mk (radIdeal n f) p = mk (radIdeal n f) q`, then `mk (D p) =
mk (D q)` (with `D = implicitDeriv (C(toK ℓ)·X)`). The two arguments differ by an element of `radIdeal n
f`, which `D` keeps in `radIdeal n f` (`implicitDeriv_mem_radIdeal`); the derivation is ℤ-linear so the
difference of images is `D(p − q) ∈ radIdeal n f`. -/
theorem mk_implicitDeriv_congr (n : ℕ) (f : α)
    (hnf : (n : CFieldSpec.K α) * CFieldSpec.toK f ≠ 0) {p q : (CFieldSpec.K α)[X]}
    (hpq : Ideal.Quotient.mk (radIdeal n f) p = Ideal.Quotient.mk (radIdeal n f) q) :
    Ideal.Quotient.mk (radIdeal n f)
        (Differential.implicitDeriv (Polynomial.C (CFieldSpec.toK (logDerRadicand n f)) * X) p)
      = Ideal.Quotient.mk (radIdeal n f)
        (Differential.implicitDeriv (Polynomial.C (CFieldSpec.toK (logDerRadicand n f)) * X) q) := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  apply implicitDeriv_mem_radIdeal n f hnf
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hpq, sub_self]

/-! ### The Leibniz law for `radDeriv`, modulo the radicand ideal -/

/-- `radDeriv` is Leibniz modulo the radicand ideal — the product rule in `K[X] ⧸ (Xⁿ − C(toK f))`:
`mk (toPolyG (radDeriv n f (radMul n f a b))) = mk (toPolyG (radMul n f (radDeriv n f a) b)) +
mk (toPolyG (radMul n f a (radDeriv n f b)))`, valid when `n·toK f ≠ 0`. -/
theorem mk_toPolyG_radDeriv_radMul (n : ℕ) (f : α)
    (hnf : (n : CFieldSpec.K α) * CFieldSpec.toK f ≠ 0) (a b : RadElem α) :
    Ideal.Quotient.mk (radIdeal n f) (CPolyG.toPolyG (radDeriv n f (radMul n f a b)))
      = Ideal.Quotient.mk (radIdeal n f) (CPolyG.toPolyG (radMul n f (radDeriv n f a) b))
        + Ideal.Quotient.mk (radIdeal n f) (CPolyG.toPolyG (radMul n f a (radDeriv n f b))) := by
  -- abbreviations
  set ℓX := Polynomial.C (CFieldSpec.toK (logDerRadicand n f)) * X with hℓX
  set A := CPolyG.toPolyG a with hA
  set B := CPolyG.toPolyG b with hB
  -- LHS: radDeriv realizes `D`, then `radMul ≡ A·B`, then `D` descends
  rw [toPolyG_radDeriv, ← hℓX]
  rw [mk_implicitDeriv_congr n f hnf (mk_toPolyG_radMul n f a b)]
  -- RHS: each `radMul` is a product; each inner `radDeriv` realizes `D`
  rw [mk_toPolyG_radMul, mk_toPolyG_radMul, toPolyG_radDeriv, toPolyG_radDeriv, ← hℓX, ← hA, ← hB]
  -- free-polynomial Leibniz of `D` (a Mathlib derivation), pushed through `mk`
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
  ring

/-! ### `radDeriv` kills `radZero` and `radOne` -/

/-- **`radDeriv` kills `radZero`** — `toPolyG (radDeriv n f radZero) = 0` in `K[X]` (`radZero = []`,
`toPolyG [] = 0`, and `implicitDeriv v 0 = 0`). -/
@[denote] theorem toPolyG_radDeriv_radZero (n : ℕ) (f : α) :
    CPolyG.toPolyG (radDeriv n f (radZero : RadElem α)) = 0 := by
  rw [toPolyG_radDeriv, show (radZero : RadElem α) = [] from rfl, CPolyG.toPolyG_nil, map_zero]

/-- **`radDeriv` kills `radOne`** — `toPolyG (radDeriv n f radOne) = 0` in `K[X]` (`radOne = [1]`,
`toPolyG [1] = 1`, and `implicitDeriv v 1 = 0`: a derivation annihilates the unit). -/
@[denote] theorem toPolyG_radDeriv_radOne (n : ℕ) (f : α) :
    CPolyG.toPolyG (radDeriv n f (radOne : RadElem α)) = 0 := by
  rw [toPolyG_radDeriv]
  have h1 : CPolyG.toPolyG (radOne : RadElem α) = 1 := by
    show CPolyG.toPolyG [CField.one] = 1
    rw [CPolyG.toPolyG_cons, CPolyG.toPolyG_nil, mul_zero, add_zero, CFieldSpec.toK_one, map_one]
  rw [h1, Derivation.map_one_eq_zero]

end RadElem

/-! ### `#print axioms` -/

#print axioms RadElem.toPolyG_radDeriv
#print axioms RadElem.toPolyG_radDeriv_radAdd
#print axioms RadElem.implicitDeriv_radicand_mem
#print axioms RadElem.mk_toPolyG_radDeriv_radMul
