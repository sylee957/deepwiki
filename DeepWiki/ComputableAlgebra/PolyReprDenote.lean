import DeepWiki.ComputableAlgebra.PolyRepr
import DeepWiki.ComputableAlgebra.Field
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Derivative

/-! # Representation-generic denotation for `CPoly` (Step 3)

The denotation `toPoly : P α → (CRingSpec.R α)[X]` reads a representation-independent computable
polynomial as a genuine Mathlib polynomial, via `coeff` alone. The fundamental bridge
`(toPoly p).coeff k = toR (coeff p k)` makes every homomorphism square (`toPoly (add p q) =
toPoly p + toPoly q`, …) fall out coefficient-wise — with **no `List` induction**, so they hold for
every representation at once. See `docs/representation-independent-poly.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.CPoly

variable {P : Type u → Type u} [CPoly P] {α : Type u} [CCommRing α] [CRingSpec α]

/-- Representation-generic denotation into `(CRingSpec.R α)[X]`: `∑ i<degBound, C(toR(coeff p i))·Xⁱ`. -/
noncomputable def toPoly (p : P α) : (CRingSpec.R α)[X] :=
  ∑ i ∈ Finset.range (degBound p), Polynomial.C (CRingSpec.toR (coeff p i)) * X ^ i

/-- **The fundamental coefficient bridge:** `(toPoly p).coeff k = toR (coeff p k)` for every `k`
(past `degBound`, both are `0`). Every homomorphism square reduces to this. -/
theorem coeff_toPoly (p : P α) (k : ℕ) : (toPoly p).coeff k = CRingSpec.toR (coeff p k) := by
  rw [toPoly, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_range]
  split
  · rfl
  · rename_i h; simp only [not_lt] at h; rw [coeff_ge p k h, CRingSpec.toR_zero]

/-- `((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i` (list-sum ↔ finset-sum bridge). -/
theorem sum_list_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) (n : ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- `toPoly` is additive. -/
theorem toPoly_add (p q : P α) : toPoly (add p q) = toPoly p + toPoly q := by
  apply Polynomial.ext; intro k
  rw [coeff_toPoly, Polynomial.coeff_add, coeff_toPoly, coeff_toPoly, toR_coeff_add]

/-- `toPoly` commutes with negation. -/
theorem toPoly_neg (p : P α) : toPoly (neg p) = - toPoly p := by
  apply Polynomial.ext; intro k
  rw [coeff_toPoly, Polynomial.coeff_neg, coeff_toPoly, toR_coeff_neg]

/-- `toPoly` realizes scalar multiplication. -/
theorem toPoly_scale (c : α) (p : P α) :
    toPoly (scale c p) = Polynomial.C (CRingSpec.toR c) * toPoly p := by
  apply Polynomial.ext; intro k
  rw [coeff_toPoly, Polynomial.coeff_C_mul, coeff_toPoly, toR_coeff_scale]

/-- `toPoly` is multiplicative: the convolution `mul` realizes polynomial multiplication. -/
theorem toPoly_mul (p q : P α) : toPoly (mul p q) = toPoly p * toPoly q := by
  apply Polynomial.ext; intro k
  rw [coeff_toPoly, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => (toPoly p).coeff a * (toPoly q).coeff b)]
  by_cases hk : k < degBound p + degBound q
  · rw [toR_coeff_mul p q k hk, sum_list_range]
    apply Finset.sum_congr rfl; intro j _; rw [coeff_toPoly, coeff_toPoly]
  · simp only [not_lt] at hk
    rw [mul, coeff_ofFn, if_neg (by omega), CRingSpec.toR_zero]
    symm; apply Finset.sum_eq_zero; intro x hx; rw [Finset.mem_range] at hx
    rw [coeff_toPoly, coeff_toPoly]
    rcases le_or_gt (degBound p) x with h | h
    · rw [coeff_ge p x h, CRingSpec.toR_zero, zero_mul]
    · rw [coeff_ge q (k - x) (by omega), CRingSpec.toR_zero, mul_zero]

/-! ### A first generic *algorithm* on the interface: polynomial power

`cpow p n = pⁿ`, built from the generic `mul`, with `toPoly_cpow : toPoly (cpow p n) = (toPoly p)^n`.
It runs on any `CPoly` (dense or sparse) and is correct by the multiplicative square — the pattern
every higher algorithm (division, gcd, …) follows when built bottom-up on the interface. -/

omit [CRingSpec α] in
/-- The zero polynomial as a length-0 representation. -/
def czero : P α := ofFn 0 (fun _ => CCommRing.zero)

/-- The multiplicative unit `1` as a length-1 representation. -/
def one : P α := ofFn 1 (fun _ => CCommRing.one)

/-- Generic polynomial power `cpow p n = pⁿ` by `ℕ`-recursion on the generic `mul`. -/
def cpow (p : P α) : ℕ → P α
  | 0 => one
  | n + 1 => mul p (cpow p n)

/-- `toPoly one = 1`. -/
theorem toPoly_one : (toPoly (one : P α)) = 1 := by
  apply Polynomial.ext; intro k
  rw [coeff_toPoly, one, coeff_ofFn]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [CRingSpec.toR_one]
  · rw [if_neg (by omega), CRingSpec.toR_zero, Polynomial.coeff_one, if_neg (by omega)]

/-- `toPoly czero = 0`. -/
theorem toPoly_czero : (toPoly (czero : P α)) = 0 := by
  apply Polynomial.ext
  intro k
  rw [coeff_toPoly, czero, coeff_ofFn, if_neg (by omega), CRingSpec.toR_zero,
    Polynomial.coeff_zero]

/-- A singleton zero coefficient list denotes the zero polynomial. -/
@[simp] theorem toPoly_ofList_zero : toPoly (ofList (P := P) [(CCommRing.zero : α)]) = 0 := by
  apply Polynomial.ext
  intro k
  rw [coeff_toPoly, coeff_ofList]
  cases k <;> simp [CRingSpec.toR_zero]

/-- A singleton unit coefficient list denotes the constant polynomial `1`. -/
@[simp] theorem toPoly_ofList_one : toPoly (ofList (P := P) [(CCommRing.one : α)]) = 1 := by
  apply Polynomial.ext
  intro k
  rw [coeff_toPoly, coeff_ofList]
  cases k with
  | zero => simp [CRingSpec.toR_one]
  | succ k =>
    simp only [List.getD_cons_succ, List.getD_nil, CRingSpec.toR_zero,
      Polynomial.coeff_one, if_neg (Nat.succ_ne_zero k)]

/-- **`cpow` correctness:** `toPoly (cpow p n) = (toPoly p) ^ n` — representation-generic. -/
theorem toPoly_cpow (p : P α) (n : ℕ) : toPoly (cpow p n) = (toPoly p) ^ n := by
  induction n with
  | zero => rw [cpow, toPoly_one, pow_zero]
  | succ n ih => rw [cpow, toPoly_mul, ih, pow_succ, mul_comm]

/-! ### Division-support ops: subtraction, monomials, degree shift (generic)

`csub`, `cmonomial c k = c·Xᵏ`, and `cshift k p = Xᵏ·p` — the pieces a Euclidean division step needs,
each with its denotation square, representation-generic. -/

/-- Generic polynomial subtraction `csub p q = p - q`. -/
def csub (p q : P α) : P α := add p (neg q)

/-- `toPoly` realizes subtraction. -/
theorem toPoly_csub (p q : P α) : toPoly (csub p q) = toPoly p - toPoly q := by
  rw [csub, toPoly_add, toPoly_neg, sub_eq_add_neg]

/-- The monomial `c·Xᵏ` as a length-`k+1` representation. -/
def cmonomial (c : α) (k : ℕ) : P α := ofFn (k + 1) (fun i => if i = k then c else CCommRing.zero)

/-- `toPoly (cmonomial c k) = C (toR c) · Xᵏ`. -/
theorem toPoly_cmonomial (c : α) (k : ℕ) :
    toPoly (cmonomial (P := P) c k) = Polynomial.C (CRingSpec.toR c) * X ^ k := by
  apply Polynomial.ext; intro j
  rw [coeff_toPoly, cmonomial, coeff_ofFn, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hj : j = k
  · subst hj; rw [if_pos (Nat.lt_succ_self _), if_pos rfl, if_pos rfl, mul_one]
  · rw [if_neg hj, ite_self, CRingSpec.toR_zero, if_neg hj, mul_zero]

/-- Degree shift `cshift k p = Xᵏ·p` (multiply by `Xᵏ`). -/
def cshift (k : ℕ) (p : P α) : P α :=
  ofFn (degBound p + k) (fun i => if k ≤ i then coeff p (i - k) else CCommRing.zero)

/-- Reverse coefficients after padding through degree `k`, retaining a larger representation bound. -/
def creverseDeg (k : ℕ) (p : P α) : P α :=
  let n := max (k + 1) (degBound p)
  ofFn n (fun i => coeff p (n - 1 - i))

omit [CRingSpec α] in
/-- Coefficient reading for `creverseDeg`. -/
theorem coeff_creverseDeg (k i : ℕ) (p : P α) :
    coeff (creverseDeg k p) i =
      if i < max (k + 1) (degBound p) then
        coeff p (max (k + 1) (degBound p) - 1 - i)
      else CCommRing.zero := by
  rw [creverseDeg, coeff_ofFn]

/-- `toPoly (cshift k p) = Xᵏ · toPoly p`. -/
theorem toPoly_cshift (k : ℕ) (p : P α) : toPoly (cshift k p) = X ^ k * toPoly p := by
  rw [mul_comm]
  apply Polynomial.ext; intro j
  rw [coeff_toPoly, cshift, coeff_ofFn, Polynomial.coeff_mul_X_pow']
  by_cases hkj : k ≤ j
  · by_cases hb : j < degBound p + k
    · rw [if_pos hb, if_pos hkj, if_pos hkj, ← coeff_toPoly]
    · rw [if_neg hb, if_pos hkj, CRingSpec.toR_zero, coeff_toPoly,
        coeff_ge p (j - k) (by omega), CRingSpec.toR_zero]
  · simp only [if_neg hkj, ite_self, CRingSpec.toR_zero]

/-! ### Formal derivative (generic)

`cderiv p = p'` — the coefficient of `Xⁱ` in `p'` is `(i+1)·(coeff p (i+1))`, where the `ℕ`-multiple is
the ring's own repeated addition `natMul` (`CCommRing` has no `ℕ`-`SMul`). The denotation square
`toPoly_cderiv : toPoly (cderiv p) = (toPoly p)'` matches Mathlib's `Polynomial.derivative`. -/

/-- Ring `ℕ`-multiple by repeated addition (`CCommRing` supplies no `SMul ℕ`). -/
def natMul (x : α) : ℕ → α
  | 0 => CCommRing.zero
  | n + 1 => CCommRing.add x (natMul x n)

/-- `toR (natMul x n) = n · toR x` — `toR` carries the ℕ-multiple to `natCast` multiplication. -/
theorem toR_natMul (x : α) (n : ℕ) :
    CRingSpec.toR (natMul x n) = (n : (CRingSpec.R α)) * CRingSpec.toR x := by
  induction n with
  | zero => rw [natMul, CRingSpec.toR_zero]; push_cast; ring
  | succ m ih => rw [natMul, CRingSpec.toR_add, ih]; push_cast; ring

/-- Generic formal derivative: coefficient of `Xⁱ` is `(i+1)·coeff p (i+1)`. -/
def cderiv (p : P α) : P α := ofFn (degBound p) (fun i => natMul (coeff p (i + 1)) (i + 1))

/-- **`cderiv` correctness:** `toPoly (cderiv p) = (toPoly p).derivative`. Representation-generic. -/
theorem toPoly_cderiv (p : P α) : toPoly (cderiv p) = (toPoly p).derivative := by
  apply Polynomial.ext; intro k
  rw [coeff_toPoly, cderiv, coeff_ofFn, Polynomial.coeff_derivative]
  by_cases hk : k < degBound p
  · rw [if_pos hk, toR_natMul, coeff_toPoly]; push_cast; ring
  · rw [if_neg hk, CRingSpec.toR_zero, coeff_toPoly, coeff_ge p (k + 1) (by omega),
      CRingSpec.toR_zero, zero_mul]

/-! ### Evaluation (generic)

`ceval x p = ∑ᵢ (coeff p i)·xⁱ`, summed with the ring's own `foldr`/`add` (no Mathlib `Finset.sum`
on `α`, which is not a bundled semiring), with `toR_ceval : toR (ceval x p) = (toPoly p).eval (toR x)`. -/

/-- Ring power by repeated multiplication (`α` is not a bundled `Monoid`). -/
def cpowElem (x : α) : ℕ → α
  | 0 => CCommRing.one
  | n + 1 => CCommRing.mul x (cpowElem x n)

/-- Generic evaluation `ceval x p = ∑ᵢ (coeff p i)·xⁱ` via the ring's own fold. -/
def ceval (x : α) (p : P α) : α :=
  ((List.range (degBound p)).map (fun i => CCommRing.mul (coeff p i) (cpowElem x i))).foldr
    CCommRing.add CCommRing.zero

/-- `toR (cpowElem x n) = (toR x) ^ n`. -/
theorem toR_cpowElem (x : α) (n : ℕ) : CRingSpec.toR (cpowElem x n) = (CRingSpec.toR x) ^ n := by
  induction n with
  | zero => rw [cpowElem, CRingSpec.toR_one, pow_zero]
  | succ m ih => rw [cpowElem, CRingSpec.toR_mul, ih, pow_succ, mul_comm]

/-- **`ceval` correctness:** `toR (ceval x p) = (toPoly p).eval (toR x)`. Representation-generic. -/
theorem toR_ceval (x : α) (p : P α) :
    CRingSpec.toR (ceval x p) = (toPoly p).eval (CRingSpec.toR x) := by
  rw [ceval, toR_foldr_add, List.map_map]
  rw [show ((List.range (degBound p)).map
        (CRingSpec.toR ∘ fun i => CCommRing.mul (coeff p i) (cpowElem x i)))
      = (List.range (degBound p)).map
        (fun i => CRingSpec.toR (coeff p i) * (CRingSpec.toR x) ^ i) from by
    apply List.map_congr_left; intro i _
    rw [Function.comp_apply, CRingSpec.toR_mul, toR_cpowElem]]
  rw [sum_list_range, toPoly, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl; intro i _
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- `ceval` is additive under `toR`: `toR (ceval x (p + q)) = toR (ceval x p) + toR (ceval x q)`. -/
theorem toR_ceval_add (x : α) (p q : P α) :
    CRingSpec.toR (ceval x (add p q)) = CRingSpec.toR (ceval x p) + CRingSpec.toR (ceval x q) := by
  rw [toR_ceval, toR_ceval, toR_ceval, toPoly_add, Polynomial.eval_add]

/-- `ceval` is multiplicative under `toR`: `toR (ceval x (p * q)) = toR (ceval x p) * toR (ceval x q)`. -/
theorem toR_ceval_mul (x : α) (p q : P α) :
    CRingSpec.toR (ceval x (mul p q)) = CRingSpec.toR (ceval x p) * CRingSpec.toR (ceval x q) := by
  rw [toR_ceval, toR_ceval, toR_ceval, toPoly_mul, Polynomial.eval_mul]

/-- **Factor theorem:** `r` is a root (`ceval r p` denotes `0`) iff `(X − r) ∣ toPoly p`. -/
theorem ceval_eq_zero_iff_dvd (r : α) (p : P α) :
    CRingSpec.toR (ceval r p) = 0 ↔ (X - Polynomial.C (CRingSpec.toR r)) ∣ toPoly p := by
  rw [toR_ceval]
  exact (Polynomial.dvd_iff_isRoot (a := CRingSpec.toR r) (p := toPoly p)).symm

end DeepWiki.SymbolicIntegration.CPoly
