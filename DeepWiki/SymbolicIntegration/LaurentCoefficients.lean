import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Derivative
import DeepWiki.SymbolicIntegration.SquarefreeFactorization
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms

/-! # The Bronstein–Salvy differential-variable Laurent-coefficient engine (Bronstein §2.7, Theorem 2.7.1, eqs 2.10–2.12)

For `A, D ∈ K[x]` with `D` monic nonzero, `gcd(A,D)=1`, and a squarefree factorization `D = ∏ᵢ Dᵢ^i`,
Theorem 2.7.1 computes the partial-fraction Laurent coefficients `Hᵢⱼ ∈ K[x]` **rationally** — using only
rational operations over `K`, without factoring `Dᵢ` — such that
`A/D = P + ∑ᵢ ∑_{α|Dᵢ(α)=0} (Hᵢᵢ(α)/(x−α)ⁱ + ⋯ + Hᵢ₁(α)/(x−α))`.

This file builds the engine. The clean model: the **differential polynomial ring** `K(x)⟨u⟩` numerators
live in `R := MvPolynomial (Option ℕ) K` — variable `none` is `x`, variable `some n` is `u^(n)` (the
`n`-th derivative of the differential indeterminate `u`). The `d/dx` derivation `ddx` is `K`-linear, fixed
by `ddx x = 1`, `ddx u^(n) = u^(n+1)`; it is `MvPolynomial.mkDerivation`.

* (2.10) `bezoutE`/`bezoutDeriv` (`= Bᵢ`/`Cᵢ`): extended-Euclidean cofactors with `Bᵢ·Eᵢ ≡ 1`,
  `Cᵢ·Dᵢ' ≡ 1 (mod Dᵢ)`, where `Eᵢ = D /ₘ Dᵢ^i`.
* (2.11) `laurentNum` (`= Pᵢⱼ ∈ R`): the numerator of `hᵢ^(i−j)/(i−j)!`, by the quotient-rule recursion.
* (2.12) `laurentQ` (`= Qᵢⱼ ∈ K[x]`, the `aeval` substitution `u^(k) ↦ Dᵢ^(k+1)/(k+1)`) and the engine
  `laurentH` (`= Hᵢⱼ = Qᵢⱼ·Bᵢ^(i−j+1)·Cᵢ^(2i−j) %ₘ Dᵢ`).

The `i=1` residue case `H₁₁(α) = A(α)/D'(α)` connects to `Residues.lean`. The full general correctness
(`Hᵢⱼ(α)` = the `1/(x−α)^j` Laurent coefficient, via the Taylor expansion of `hᵢ,α = (A/D)(x−α)^i`,
book p.56) is a documented follow-up. -/

open Polynomial MvPolynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ## Stage A — the differential polynomial ring `K⟨u⟩` and its `d/dx` derivation -/

/-- **The differential-variable numerator ring** (§2.7): `DiffPoly K = MvPolynomial (Option ℕ) K`, where
`X none` is the base variable `x` and `X (some n)` is `u^(n)`, the `n`-th derivative of the differential
indeterminate `u`. The Laurent-coefficient numerators `Pᵢⱼ` (eq 2.11) live here, as they have
`K`-coefficients. -/
abbrev DiffPoly (K : Type*) [Field K] : Type _ := MvPolynomial (Option ℕ) K

/-- **The base variable `x`** (`= X none`) in `DiffPoly K`. -/
noncomputable abbrev dpX : DiffPoly K := X none

/-- **The `n`-th derivative `u^(n)`** of the differential indeterminate (`= X (some n)`) in `DiffPoly K`;
`dpU 0 = u`, `dpU 1 = u'`, etc. -/
noncomputable abbrev dpU (n : ℕ) : DiffPoly K := X (some n)

/-- **The `K[x] → DiffPoly K` embedding** sending the polynomial variable `X` to `x = X none`; used to
inject `Eᵢ`, `Eᵢ'` and the input `A` into the differential numerator ring as coefficients of `u`. -/
noncomputable def dpEmbed : K[X] →+* DiffPoly K :=
  Polynomial.eval₂RingHom (MvPolynomial.C : K →+* DiffPoly K) (X none)

@[simp] theorem dpEmbed_X : dpEmbed (Polynomial.X : K[X]) = (X none : DiffPoly K) := by
  simp [dpEmbed]

@[simp] theorem dpEmbed_C (c : K) : dpEmbed (Polynomial.C c) = (MvPolynomial.C c : DiffPoly K) := by
  simp [dpEmbed]

/-- **The `d/dx` derivation on `DiffPoly K`** (§2.7): the `K`-linear derivation with `ddx x = 1` and
`ddx u^(n) = u^(n+1)`, built by `MvPolynomial.mkDerivation`. This is the engine's `d/dx`: it kills `K`,
fixes the base variable, and shifts each `u^(n)` to its successor `u^(n+1)`. -/
noncomputable def ddx : Derivation K (DiffPoly K) (DiffPoly K) :=
  MvPolynomial.mkDerivation K fun v => match v with
    | none => 1
    | some n => X (some (n + 1))

@[simp] theorem ddx_x : ddx (dpX : DiffPoly K) = 1 := by
  simp [ddx, dpX]

@[simp] theorem ddx_u (n : ℕ) : ddx (dpU n : DiffPoly K) = dpU (n + 1) := by
  simp [ddx, dpU]

@[simp] theorem ddx_C (c : K) : ddx (MvPolynomial.C c : DiffPoly K) = 0 := by
  rw [← MvPolynomial.algebraMap_eq]; exact (ddx (K := K)).map_algebraMap c

/-- **`ddx` commutes with `dpEmbed` and `Polynomial.derivative`** (§2.7): the `d/dx` of an embedded
`K[x]`-polynomial is the embedding of its formal derivative, `ddx (dpEmbed p) = dpEmbed (derivative p)`.
Both sides are `K`-derivations `K[X] → DiffPoly K` (the right composes `derivative` with `dpEmbed`) that
agree on `X`, hence on all of `K[X]` by `Polynomial.derivation_ext`. -/
theorem ddx_dpEmbed (p : K[X]) : ddx (dpEmbed p) = dpEmbed (derivative p) := by
  induction p using Polynomial.induction_on with
  | C c => simp [dpEmbed]
  | add p q hp hq => simp [hp, hq]
  | monomial n c _ih =>
      -- `derivative (C c * X^(n+1)) = C c * (n+1) * X^n`; embed and differentiate via Leibniz on `X^(n+1)`
      rw [Polynomial.derivative_C_mul_X_pow, Nat.add_sub_cancel]
      have hembed : dpEmbed (Polynomial.C c * Polynomial.X ^ (n + 1))
          = MvPolynomial.C c * (X none : DiffPoly K) ^ (n + 1) := by
        simp [dpEmbed]
      have hembedR : dpEmbed (Polynomial.C (c * (↑(n + 1) : K)) * Polynomial.X ^ n)
          = MvPolynomial.C c * (↑(n + 1) : DiffPoly K) * (X none : DiffPoly K) ^ n := by
        rw [map_mul, map_pow, dpEmbed_X, dpEmbed_C, map_mul, map_natCast]
      rw [hembed, hembedR, Derivation.leibniz, ddx_C, smul_zero, add_zero,
        Derivation.leibniz_pow, ddx_x, Nat.add_sub_cancel]
      simp only [smul_eq_mul, mul_one, nsmul_eq_mul]
      push_cast
      ring

/-! ## Stage B — (2.10) the extended-Euclidean Bézout cofactors `Bᵢ`, `Cᵢ` -/

/-- **The cofactor `Eᵢ = D /ₘ Dᵢ^i`** (§2.7): the part of `D` complementary to the prime power `Dᵢ^i`. -/
noncomputable def laurentE (D Di : K[X]) (i : ℕ) : K[X] := D /ₘ Di ^ i

/-- **The Bézout cofactor `Bᵢ`** (§2.7, eq 2.10): `Bᵢ = (diophantineSolve Eᵢ Dᵢ 1).1`, the cofactor of
`Eᵢ` in `Eᵢ·Bᵢ + Dᵢ·(…) = 1`, so `Bᵢ·Eᵢ ≡ 1 (mod Dᵢ)`. Needs `gcd(Eᵢ,Dᵢ)=1` (from squarefreeness). -/
noncomputable def bezoutE (D Di : K[X]) (i : ℕ) : K[X] :=
  (diophantineSolve (laurentE D Di i) Di 1).1

/-- **The Bézout cofactor `Cᵢ`** (§2.7, eq 2.10): `Cᵢ = (diophantineSolve Dᵢ' Dᵢ 1).1`, the cofactor of
`Dᵢ'` in `Dᵢ'·Cᵢ + Dᵢ·(…) = 1`, so `Cᵢ·Dᵢ' ≡ 1 (mod Dᵢ)`. Needs `gcd(Dᵢ',Dᵢ)=1` (squarefree). -/
noncomputable def bezoutDeriv (Di : K[X]) : K[X] :=
  (diophantineSolve (derivative Di) Di 1).1

/-- **(2.10), the `Bᵢ` congruence**: for `IsCoprime Eᵢ Dᵢ`, `Bᵢ·Eᵢ ≡ 1 (mod Dᵢ)`, i.e.
`(bezoutE D Di i * laurentE D Di i) %ₘ Di = 1 %ₘ Di`. From `Eᵢ·Bᵢ + Dᵢ·(…) = 1` reduced mod the monic
`Di`. -/
theorem bezoutE_mul_laurentE_modByMonic (D Di : K[X]) (i : ℕ) (hDi : Di.Monic)
    (hcop : IsCoprime (laurentE D Di i) Di) :
    (bezoutE D Di i * laurentE D Di i) %ₘ Di = (1 : K[X]) %ₘ Di := by
  have hspec := diophantineSolve_spec hcop (1 : K[X])
  -- `Eᵢ·Bᵢ + Dᵢ·s = 1`, so `Bᵢ·Eᵢ = 1 − Dᵢ·s`, and `Dᵢ·s ≡ 0 (mod Dᵢ)`
  have hkey : bezoutE D Di i * laurentE D Di i
      = (1 : K[X]) - Di * (diophantineSolve (laurentE D Di i) Di 1).2 := by
    rw [bezoutE]; linear_combination hspec
  rw [hkey, sub_modByMonic, self_mul_modByMonic hDi, sub_zero]

/-- **(2.10), the `Cᵢ` congruence**: for `IsCoprime Dᵢ' Dᵢ`, `Cᵢ·Dᵢ' ≡ 1 (mod Dᵢ)`, i.e.
`(bezoutDeriv Di * derivative Di) %ₘ Di = 1 %ₘ Di`. From `Dᵢ'·Cᵢ + Dᵢ·(…) = 1` reduced mod monic `Di`. -/
theorem bezoutDeriv_mul_derivative_modByMonic (Di : K[X]) (hDi : Di.Monic)
    (hcop : IsCoprime (derivative Di) Di) :
    (bezoutDeriv Di * derivative Di) %ₘ Di = (1 : K[X]) %ₘ Di := by
  have hspec := diophantineSolve_spec hcop (1 : K[X])
  have hkey : bezoutDeriv Di * derivative Di
      = (1 : K[X]) - Di * (diophantineSolve (derivative Di) Di 1).2 := by
    rw [bezoutDeriv]; linear_combination hspec
  rw [hkey, sub_modByMonic, self_mul_modByMonic hDi, sub_zero]

/-- **`gcd(Dᵢ', Dᵢ) = 1` from squarefreeness** (§2.7): a squarefree `Dᵢ` over a `CharZero` field is
coprime to its derivative, `IsCoprime Dᵢ' Dᵢ` — the (2.10) hypothesis for `Cᵢ`. -/
theorem isCoprime_derivative_of_squarefree [CharZero K] {Di : K[X]} (hsf : Squarefree Di) :
    IsCoprime (derivative Di) Di :=
  (squarefree_iff_isCoprime_derivative.mp hsf).symm

/-! ## Stage C — (2.11) the `Pᵢⱼ` numerator recursion -/

/-- **The numerator-recursion step** (§2.7, differentiating eq 2.11): from the numerator `P` of
`hᵢ^d/d! = P/(u^a·Eᵢ^b)` (with `a = i+d`, `b = d+1`), one `d/dx` and a `1/(d+1)` factor give the numerator
of `hᵢ^(d+1)/(d+1)!`, namely
`(1/(d+1))·(ddx P · u · Eᵢ − P·(a·u'·Eᵢ + b·u·Eᵢ'))` over `u^(a+1)·Eᵢ^(b+1)`. Here `Eᵢ = dpEmbed Ei`,
`Eᵢ' = dpEmbed (derivative Ei)`, `u = X (some 0)`, `u' = X (some 1)`. -/
noncomputable def laurentNumStep (Ei : K[X]) (a b : ℕ) (P : DiffPoly K) : DiffPoly K :=
  MvPolynomial.C ((a + 1 : K)⁻¹) *
    (ddx P * X (some 0) * dpEmbed Ei
      - P * ((a : DiffPoly K) * X (some 1) * dpEmbed Ei
              + (b : DiffPoly K) * X (some 0) * dpEmbed (derivative Ei)))

/-- **The Laurent numerator `Pᵢⱼ`** (§2.7, eq 2.11), indexed by the derivative count `d = i − j` running
`0,1,…`: `laurentNum A Ei i 0 = dpEmbed A` (the numerator of `hᵢ = A/(uⁱ·Eᵢ)`), and each successive `d`
applies `laurentNumStep` with denominator exponents `a = i+d`, `b = d+1`. So `laurentNum A Ei i d` is the
`Pᵢⱼ` with `j = i − d`, the numerator of `hᵢ^d/d! = Pᵢⱼ/(u^(i+d)·Eᵢ^(d+1))`. -/
noncomputable def laurentNum (A Ei : K[X]) (i : ℕ) : ℕ → DiffPoly K
  | 0 => dpEmbed A
  | d + 1 => laurentNumStep Ei (i + d) (d + 1) (laurentNum A Ei i d)

@[simp] theorem laurentNum_zero (A Ei : K[X]) (i : ℕ) :
    laurentNum A Ei i 0 = dpEmbed A := rfl

theorem laurentNum_succ (A Ei : K[X]) (i d : ℕ) :
    laurentNum A Ei i (d + 1)
      = laurentNumStep Ei (i + d) (d + 1) (laurentNum A Ei i d) := rfl

/-- **The cleared quotient-rule step** (§2.7, eq 2.11 differentiated, denominator-free form): over a
characteristic-`0` field the `1/(d+1)` in `laurentNumStep` clears, giving the polynomial identity
`(i+d+1)·Pᵢ,d₊₁ = ddx Pᵢ,d · u · Eᵢ − Pᵢ,d·((i+d)·u'·Eᵢ + (d+1)·u·Eᵢ')` in `DiffPoly K`. This is the
numerator of the quotient rule `d/dx (P/(uᵃ·Eᵢᵇ)) = (ddx P·u·Eᵢ − P·(a·u'·Eᵢ + b·u·Eᵢ'))/(uᵃ⁺¹·Eᵢᵇ⁺¹)`
with `a = i+d`, `b = d+1`, validating the `Pᵢⱼ` recursion against the genuine `d/dx` of `hᵢ`. -/
theorem laurentNum_cleared_step [CharZero K] (A Ei : K[X]) (i d : ℕ) :
    MvPolynomial.C ((i + d : K) + 1) * laurentNum A Ei i (d + 1)
      = ddx (laurentNum A Ei i d) * X (some 0) * dpEmbed Ei
        - laurentNum A Ei i d
            * ((i + d : DiffPoly K) * X (some 1) * dpEmbed Ei
                + (d + 1 : DiffPoly K) * X (some 0) * dpEmbed (derivative Ei)) := by
  rw [laurentNum_succ, laurentNumStep, ← mul_assoc, ← MvPolynomial.C_mul]
  have hne : ((i + d : ℕ) : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
  rw [show ((i : K) + d + 1) = (((i + d : ℕ) : K) + 1) by push_cast; ring,
      mul_inv_cancel₀ hne, MvPolynomial.C_1, one_mul]
  push_cast; ring

/-! ## Stage D — (2.12) the engine: `Qᵢⱼ` substitution and `Hᵢⱼ` -/

/-- **The `Qᵢⱼ` substitution map** (§2.7): the `K`-algebra map `DiffPoly K → K[x]` realizing
`Pᵢⱼ(x, Dᵢ', Dᵢ''/2, Dᵢ^(3)/3, …)`, i.e. `x ↦ X`, `u^(k) = X (some k) ↦ Dᵢ^(k+1)/(k+1)`
(the `(k+1)`-th derivative of `Dᵢ` scaled by `1/(k+1)`). -/
noncomputable def laurentSubst (Di : K[X]) : Option ℕ → K[X] := fun v =>
  match v with
  | none => Polynomial.X
  | some k => Polynomial.C ((k + 1 : K)⁻¹) * (derivative^[k + 1] Di)

/-- **The polynomial `Qᵢⱼ ∈ K[x]`** (§2.7): `Qᵢⱼ = aeval (laurentSubst Dᵢ) Pᵢⱼ`, substituting the scaled
derivatives of `Dᵢ` for the differential variables in the numerator `Pᵢⱼ = laurentNum A Eᵢ i (i−j)`. -/
noncomputable def laurentQ (A Di : K[X]) (i j : ℕ) : K[X] :=
  aeval (laurentSubst Di) (laurentNum A (laurentE A Di i) i (i - j))

/-- **The Bronstein–Salvy Laurent coefficient `Hᵢⱼ ∈ K[x]`** (§2.7, eq 2.12, **the engine**):
`Hᵢⱼ = Qᵢⱼ·Bᵢ^(i−j+1)·Cᵢ^(2i−j) (mod Dᵢ)`, computed by purely rational operations over `K` without
factoring `Dᵢ`. The Laurent coefficient of `1/(x−α)^j` at a root `α` of `Dᵢ` is `Hᵢⱼ(α)`. -/
noncomputable def laurentH (A D Di : K[X]) (i j : ℕ) : K[X] :=
  (laurentQ A Di i j * bezoutE D Di i ^ (i - j + 1) * bezoutDeriv Di ^ (2 * i - j)) %ₘ Di

theorem laurentH_def (A D Di : K[X]) (i j : ℕ) :
    laurentH A D Di i j
      = (laurentQ A Di i j * bezoutE D Di i ^ (i - j + 1) * bezoutDeriv Di ^ (2 * i - j)) %ₘ Di :=
  rfl

/-! ## Stage E — the `i=1` residue: `H₁₁(α) = A(α)/D'(α)` -/

/-- **`aeval (laurentSubst Di) ∘ dpEmbed = id`** on `K[x]`: the `Qᵢⱼ` substitution undoes the embedding
of a pure-`x` polynomial (no differential variables), since both fix `X` and `C`. -/
theorem aeval_laurentSubst_dpEmbed (Di p : K[X]) :
    aeval (laurentSubst Di) (dpEmbed p) = p := by
  have h : ((aeval (laurentSubst Di) : DiffPoly K →ₐ[K] K[X]).toRingHom.comp dpEmbed)
      = RingHom.id K[X] := by
    apply Polynomial.ringHom_ext
    · intro c; simp [dpEmbed]
    · simp [dpEmbed, laurentSubst]
  exact congrArg (fun f : K[X] →+* K[X] => f p) h

/-- **`Q₁₁ = A`** (§2.7, the `i=j=1` base case): for `i=j=1` the derivative count is `i−j=0`, so
`P₁₁ = dpEmbed A` and `Q₁₁ = aeval (laurentSubst D₁) (dpEmbed A) = A` — the substitution fixes the base
variable `x ↦ X` and `A` has no differential variables. -/
theorem laurentQ_one_one (A Di : K[X]) : laurentQ A Di 1 1 = A := by
  rw [laurentQ, Nat.sub_self, laurentNum_zero, aeval_laurentSubst_dpEmbed]

/-- **`E₁ = D /ₘ D₁`** for `i=1`: the cofactor at multiplicity one. -/
theorem laurentE_one (D Di : K[X]) : laurentE D Di 1 = D /ₘ Di := by
  rw [laurentE, pow_one]

open scoped Classical in
/-- **`H₁₁` is the residue numerator `A·B₁·C₁ %ₘ D₁`** (§2.7, the `i=1` engine output): for `i=j=1`,
`laurentH A D D₁ 1 1 = (A · bezoutE D D₁ 1 · bezoutDeriv D₁) %ₘ D₁`, since `Q₁₁ = A`, the `Bᵢ`-exponent
`i−j+1 = 1` and the `Cᵢ`-exponent `2i−j = 1`. -/
theorem laurentH_one_one (A D Di : K[X]) :
    laurentH A D Di 1 1 = (A * bezoutE D Di 1 * bezoutDeriv Di) %ₘ Di := by
  rw [laurentH, laurentQ_one_one]
  norm_num

/-- **`%ₘ Dᵢ` is invisible at a root** of `Dᵢ`: for monic `Dᵢ` with `Dᵢ(α)=0`,
`(P %ₘ Dᵢ).eval α = P.eval α` — the quotient term `Dᵢ·(P /ₘ Dᵢ)` vanishes at `α`. Used to read engine
outputs (which are `%ₘ Dᵢ`-reduced) at the roots of `Dᵢ`. -/
theorem eval_modByMonic_of_root {P Di : K[X]} {α : K} (_hDi : Di.Monic) (hα : Di.eval α = 0) :
    (P %ₘ Di).eval α = P.eval α := by
  conv_rhs => rw [← modByMonic_add_div P Di]
  rw [Polynomial.eval_add, Polynomial.eval_mul, hα, zero_mul, add_zero]

/-- **`Bᵢ(α) = 1/Eᵢ(α)`** at a root `α` of `Dᵢ` (§2.7, the (2.10) evaluation): from `Bᵢ·Eᵢ ≡ 1 (mod Dᵢ)`,
evaluating at a root of the monic `Dᵢ` gives `Bᵢ(α)·Eᵢ(α) = 1`. -/
theorem bezoutE_mul_laurentE_eval {D Di : K[X]} {α : K} (i : ℕ) (hDi : Di.Monic)
    (hα : Di.eval α = 0) (hcop : IsCoprime (laurentE D Di i) Di) :
    (bezoutE D Di i).eval α * (laurentE D Di i).eval α = 1 := by
  have h := bezoutE_mul_laurentE_modByMonic D Di i hDi hcop
  have := congrArg (fun p => p.eval α) h
  simpa [eval_modByMonic_of_root hDi hα, Polynomial.eval_mul] using this

/-- **`Cᵢ(α) = 1/Dᵢ'(α)`** at a root `α` of `Dᵢ` (§2.7, the (2.10) evaluation): from `Cᵢ·Dᵢ' ≡ 1 (mod Dᵢ)`,
evaluating at a root of the monic `Dᵢ` gives `Cᵢ(α)·Dᵢ'(α) = 1`. -/
theorem bezoutDeriv_mul_derivative_eval {Di : K[X]} {α : K} (hDi : Di.Monic)
    (hα : Di.eval α = 0) (hcop : IsCoprime (derivative Di) Di) :
    (bezoutDeriv Di).eval α * (derivative Di).eval α = 1 := by
  have h := bezoutDeriv_mul_derivative_modByMonic Di hDi hcop
  have := congrArg (fun p => p.eval α) h
  simpa [eval_modByMonic_of_root hDi hα, Polynomial.eval_mul] using this

/-- **`H₁₁(α) = A(α)/D'(α)`**, the Rothstein–Trager residue (§2.7, the `i=1` correctness, book p.56):
for a simple factor `D = D₁·E₁` (`E₁ = D /ₘ D₁`) and a root `α` of the monic squarefree `D₁`
(with `E₁(α) ≠ 0`, `D₁'(α) ≠ 0`), the engine output evaluates to `H₁₁(α) = A(α)/(E₁(α)·D₁'(α))`. Since
`D'(α) = D₁'(α)·E₁(α)` at a root of `D₁` (the `D₁·E₁'` term vanishes), this is exactly the residue
`A(α)/D'(α)` of `A/D` at the simple root `α` — the value collected in the Rothstein–Trager logarithmic
sum (`Residues.residue_eq_eval_div_eval_derivative`). -/
theorem eval_laurentH_one_one {A D Di : K[X]} {α : K} (hDi : Di.Monic) (hα : Di.eval α = 0)
    (hcopE : IsCoprime (laurentE D Di 1) Di) (hcopD : IsCoprime (derivative Di) Di)
    (hE : (laurentE D Di 1).eval α ≠ 0) (hD' : (derivative Di).eval α ≠ 0) :
    (laurentH A D Di 1 1).eval α
      = A.eval α / ((laurentE D Di 1).eval α * (derivative Di).eval α) := by
  rw [laurentH_one_one, eval_modByMonic_of_root hDi hα, Polynomial.eval_mul, Polynomial.eval_mul]
  have hB : (bezoutE D Di 1).eval α = 1 / (laurentE D Di 1).eval α :=
    eq_one_div_of_mul_eq_one_left (bezoutE_mul_laurentE_eval 1 hDi hα hcopE)
  have hC : (bezoutDeriv Di).eval α = 1 / (derivative Di).eval α :=
    eq_one_div_of_mul_eq_one_left (bezoutDeriv_mul_derivative_eval hDi hα hcopD)
  rw [hB, hC]
  field_simp
/-- **`H₁₁(α) = A(α)/D'(α)`, in terms of the genuine `D'`** (§2.7, the residue, book p.56): when
`D = D₁·E₁` with `E₁ = D /ₘ D₁` and `α` a root of the monic squarefree `D₁`, the residue denominator
`E₁(α)·D₁'(α)` equals `D'(α)` (since `D' = D₁'·E₁ + D₁·E₁'` and `D₁(α)=0`), so the engine output is the
Rothstein–Trager residue `H₁₁(α) = A(α)/D'(α)`. -/
theorem eval_laurentH_one_one_eq_residue {A D Di : K[X]} {α : K} (hDi : Di.Monic)
    (hα : Di.eval α = 0) (hfac : D = Di * laurentE D Di 1) (hcopE : IsCoprime (laurentE D Di 1) Di)
    (hcopD : IsCoprime (derivative Di) Di) (hE : (laurentE D Di 1).eval α ≠ 0)
    (hD' : (derivative Di).eval α ≠ 0) :
    (laurentH A D Di 1 1).eval α = A.eval α / (derivative D).eval α := by
  rw [eval_laurentH_one_one hDi hα hcopE hcopD hE hD']
  congr 1
  -- `D'(α) = D₁'(α)·E₁(α)`: differentiate `D = D₁·E₁`, the `D₁·E₁'` term vanishes at the root `α`
  conv_rhs => rw [hfac, derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_mul, hα, zero_mul, add_zero]
  rw [mul_comm]

/-! ## Stage F — the `d/dx` derivation on `K(x)⟨u⟩ = Frac (DiffPoly K)`, validating the `Pᵢⱼ`
recursion (eq 2.11 as a fraction-field invariant)

Mathlib has no derivation on a field of fractions, so — exactly as `RationalFunctionDerivative.lean`
does for `K(x)` — we build `d/dx` on `Frac (DiffPoly K) = Localization (nonZeroDivisors (DiffPoly K))`
directly by the quotient rule `(p/q)' = (ddx p·q − p·ddx q)/q²`, lifting the engine's `ddx`. The
well-definedness on `Localization.liftOn` follows from differentiating the localization relation. With
the resulting derivation `fracKDeriv`, eq 2.11's claim `hᵢ^(d)/d! = Pᵢⱼ/(u^(2i−j)·Eᵢ^(i−j+1))` (`d=i−j`)
becomes a clean fraction-field identity `(fracKDeriv^[d] hᵢ) = d!·(Pᵢ,d/(u^(i+d)·Eᵢ^(d+1)))`, proved by
induction via `laurentNum_cleared_step` and Mathlib's `Derivation.leibniz_div`. -/

/-- The quotient-rule numerator/denominator pair `(ddx p·q − p·ddx q, q²)` as an element of
`Frac (DiffPoly K)`. -/
private noncomputable def fracDerivAux (p : DiffPoly K) (q : nonZeroDivisors (DiffPoly K)) :
    FractionRing (DiffPoly K) :=
  Localization.mk (ddx p * (q : DiffPoly K) - p * ddx (q : DiffPoly K))
    ⟨(q : DiffPoly K) ^ 2, pow_mem q.2 2⟩

private theorem fracDerivAux_wd {p p' : DiffPoly K} {q q' : nonZeroDivisors (DiffPoly K)}
    (h : (Localization.r (nonZeroDivisors (DiffPoly K))) (p, q) (p', q')) :
    fracDerivAux p q = fracDerivAux p' q' := by
  rw [Localization.r_iff_exists] at h
  obtain ⟨c, hc⟩ := h
  have hc0 : (c : DiffPoly K) ≠ 0 := nonZeroDivisors.coe_ne_zero c
  have key : (q' : DiffPoly K) * p = (q : DiffPoly K) * p' := mul_left_cancel₀ hc0 (by simpa using hc)
  have keyd := congrArg ddx key
  rw [Derivation.leibniz, Derivation.leibniz] at keyd
  simp only [smul_eq_mul] at keyd
  unfold fracDerivAux
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul]
  show ((q' : DiffPoly K) ^ 2) * (ddx p * (q : DiffPoly K) - p * ddx (q : DiffPoly K))
      = ((q : DiffPoly K) ^ 2) * (ddx p' * (q' : DiffPoly K) - p' * ddx (q' : DiffPoly K))
  linear_combination ((q : DiffPoly K) * (q' : DiffPoly K)) * keyd
    - ((q : DiffPoly K) * ddx (q' : DiffPoly K) + (q' : DiffPoly K) * ddx (q : DiffPoly K)) * key

/-- **`d/dx` on `Frac (DiffPoly K)`** (§2.7): the quotient-rule derivative `(p/q)' = (ddx p·q − p·ddx q)/q²`
extending the engine's `ddx`, defined via `Localization.liftOn` (well-defined by `fracDerivAux_wd`). -/
noncomputable def fracDeriv (x : FractionRing (DiffPoly K)) : FractionRing (DiffPoly K) :=
  Localization.liftOn x fracDerivAux (fun h => fracDerivAux_wd h)

/-- **Quotient rule** for `fracDeriv`: `(mk p q)' = (ddx p·q − p·ddx q)/q²`. -/
theorem fracDeriv_mk (p : DiffPoly K) (q : nonZeroDivisors (DiffPoly K)) :
    fracDeriv (Localization.mk p q) = fracDerivAux p q :=
  Localization.liftOn_mk _ _ _ _

/-- **`mk a b = mk c d` from the cross-multiplication** `d·a = b·c` in `DiffPoly K`. -/
private theorem mk_eq_of {a c : DiffPoly K} {b d : nonZeroDivisors (DiffPoly K)}
    (h : (d : DiffPoly K) * a = (b : DiffPoly K) * c) :
    (Localization.mk a b : FractionRing (DiffPoly K)) = Localization.mk c d := by
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [OneMemClass.coe_one, one_mul]; exact h⟩

/-- **`fracDeriv` extends `ddx`**: on an embedded numerator (as a fraction over `1`), `d/dx` on `Frac`
is the engine's `ddx`, `fracDeriv (algebraMap p) = algebraMap (ddx p)`. -/
theorem fracDeriv_algebraMap (p : DiffPoly K) :
    fracDeriv (algebraMap (DiffPoly K) (FractionRing (DiffPoly K)) p)
      = algebraMap (DiffPoly K) (FractionRing (DiffPoly K)) (ddx p) := by
  rw [← Localization.mk_one_eq_algebraMap, fracDeriv_mk]
  unfold fracDerivAux
  rw [← Localization.mk_one_eq_algebraMap]
  apply mk_eq_of
  simp

/-- **Additivity of `fracDeriv`** on `Frac (DiffPoly K)`: `(x + y)' = x' + y'`. -/
theorem fracDeriv_add (x y : FractionRing (DiffPoly K)) :
    fracDeriv (x + y) = fracDeriv x + fracDeriv y := by
  induction x using Localization.induction_on with | _ px =>
  induction y using Localization.induction_on with | _ py =>
  obtain ⟨p, q⟩ := px; obtain ⟨r, s⟩ := py
  rw [Localization.add_mk, fracDeriv_mk, fracDeriv_mk, fracDeriv_mk]
  unfold fracDerivAux
  rw [Localization.add_mk]
  apply mk_eq_of
  push_cast
  simp only [map_add, Derivation.leibniz, smul_eq_mul]
  ring

/-- **Leibniz rule for `fracDeriv`** on `Frac (DiffPoly K)`: `(x·y)' = x'·y + x·y'`. -/
theorem fracDeriv_mul (x y : FractionRing (DiffPoly K)) :
    fracDeriv (x * y) = fracDeriv x * y + x * fracDeriv y := by
  induction x using Localization.induction_on with | _ px =>
  induction y using Localization.induction_on with | _ py =>
  obtain ⟨p, q⟩ := px; obtain ⟨r, s⟩ := py
  rw [Localization.mk_mul, fracDeriv_mk, fracDeriv_mk, fracDeriv_mk]
  unfold fracDerivAux
  rw [Localization.mk_mul, Localization.mk_mul, Localization.add_mk]
  apply mk_eq_of
  push_cast
  simp only [Derivation.leibniz, smul_eq_mul]
  ring

/-- **`K`-linearity of `fracDeriv`** on `Frac (DiffPoly K)`: `(c • x)' = c • x'` for `c : K`. -/
theorem fracDeriv_smul (c : K) (x : FractionRing (DiffPoly K)) :
    fracDeriv (c • x) = c • fracDeriv x := by
  induction x using Localization.induction_on with | _ px =>
  obtain ⟨p, q⟩ := px
  rw [Localization.smul_mk, fracDeriv_mk, fracDeriv_mk]
  unfold fracDerivAux
  rw [Localization.smul_mk]
  apply mk_eq_of
  have hc : ddx (c • p) = c • ddx p := map_smul ddx.toLinearMap c p
  rw [hc, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
  ring

/-- **The `d/dx` `K`-derivation on `K(x)⟨u⟩ = Frac (DiffPoly K)`** (§2.7): `fracDeriv` bundled as a
`Derivation K (Frac) (Frac)`, so Mathlib's `Derivation.leibniz_div`/`leibniz_pow` apply. -/
noncomputable def fracKDeriv :
    Derivation K (FractionRing (DiffPoly K)) (FractionRing (DiffPoly K)) :=
  Derivation.mk'
    { toFun := fracDeriv, map_add' := fracDeriv_add,
      map_smul' := fun c x => by simpa using fracDeriv_smul c x }
    fun a b => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]; rw [fracDeriv_mul]; ring

@[simp] theorem fracKDeriv_apply (x : FractionRing (DiffPoly K)) : fracKDeriv x = fracDeriv x := rfl

/-- **`fracKDeriv` extends `ddx`** (the bundled form of `fracDeriv_algebraMap`). -/
theorem fracKDeriv_algebraMap (p : DiffPoly K) :
    fracKDeriv (algebraMap (DiffPoly K) (FractionRing (DiffPoly K)) p)
      = algebraMap (DiffPoly K) (FractionRing (DiffPoly K)) (ddx p) :=
  fracDeriv_algebraMap p

/-- **`dpEmbed Ei ≠ 0`** for `Ei ≠ 0`: the embedding `K[x] → DiffPoly K` is injective (with left inverse
`aeval (laurentSubst _)`), so it does not kill a nonzero polynomial. -/
theorem dpEmbed_ne_zero {Ei : K[X]} (hEi : Ei ≠ 0) : dpEmbed Ei ≠ (0 : DiffPoly K) := by
  intro h
  apply hEi
  have := congrArg (MvPolynomial.aeval (laurentSubst (0 : K[X]))) h
  rwa [aeval_laurentSubst_dpEmbed, map_zero] at this

/-- **The `hᵢ^(d)` denominator** `u^(i+d)·Eᵢ^(d+1) ∈ DiffPoly K` (eq 2.11, `d = i−j`, denominator
`u^(2i−j)·Eᵢ^(i−j+1)`). -/
noncomputable def lDenom (Ei : K[X]) (i d : ℕ) : DiffPoly K :=
  (X (some 0)) ^ (i + d) * (dpEmbed Ei) ^ (d + 1)

/-- **`u^(i+d)·Eᵢ^(d+1) ≠ 0`** for `Ei ≠ 0`. -/
theorem lDenom_ne_zero {Ei : K[X]} (i d : ℕ) (hEi : Ei ≠ 0) : lDenom Ei i d ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ (dpEmbed_ne_zero hEi))
  simp [MvPolynomial.X_ne_zero]

/-- **Denominator recursion**: `denom_{d+1} = denom_d · u · Eᵢ` (the new `u`/`Eᵢ` factor each step). -/
theorem lDenom_succ (Ei : K[X]) (i d : ℕ) :
    lDenom Ei i (d + 1) = lDenom Ei i d * X (some 0) * dpEmbed Ei := by
  unfold lDenom
  rw [show i + (d + 1) = (i + d) + 1 from by ring]
  ring

/-- **`hᵢ = A/(uⁱ·Eᵢ)`** as an element of `K(x)⟨u⟩` (eq 2.11 base): the differential-variable fraction
the engine differentiates. -/
noncomputable def hFrac (A Ei : K[X]) (i : ℕ) : FractionRing (DiffPoly K) :=
  algebraMap (DiffPoly K) (FractionRing (DiffPoly K)) (dpEmbed A) /
    algebraMap (DiffPoly K) (FractionRing (DiffPoly K)) (lDenom Ei i 0)

/-- **The candidate `hᵢ^(d)/d!` fraction** `Pᵢ,d/(u^(i+d)·Eᵢ^(d+1))` (eq 2.11, RHS). -/
noncomputable def lFrac (A Ei : K[X]) (i d : ℕ) : FractionRing (DiffPoly K) :=
  algebraMap (DiffPoly K) (FractionRing (DiffPoly K)) (laurentNum A Ei i d) /
    algebraMap (DiffPoly K) (FractionRing (DiffPoly K)) (lDenom Ei i d)

/-- **`lFrac` base case** `d=0`: `Pᵢ,0/denom₀ = A/(uⁱ·Eᵢ) = hᵢ` (`Pᵢ,0 = A`). -/
theorem lFrac_zero (A Ei : K[X]) (i : ℕ) : lFrac A Ei i 0 = hFrac A Ei i := by
  unfold lFrac hFrac; rw [laurentNum_zero]

/-! ## Restatements against the book's wording -/

/-- Restatement of (2.10), the `Bᵢ` congruence `Bᵢ·Eᵢ ≡ 1 (mod Dᵢ)`. -/
example (D Di : K[X]) (i : ℕ) (hDi : Di.Monic) (hcop : IsCoprime (laurentE D Di i) Di) :
    (bezoutE D Di i * laurentE D Di i) %ₘ Di = (1 : K[X]) %ₘ Di :=
  bezoutE_mul_laurentE_modByMonic D Di i hDi hcop

/-- Restatement of (2.10), the `Cᵢ` congruence `Cᵢ·Dᵢ' ≡ 1 (mod Dᵢ)`. -/
example (Di : K[X]) (hDi : Di.Monic) (hcop : IsCoprime (derivative Di) Di) :
    (bezoutDeriv Di * derivative Di) %ₘ Di = (1 : K[X]) %ₘ Di :=
  bezoutDeriv_mul_derivative_modByMonic Di hDi hcop

/-- Restatement of (2.12): the engine `Hᵢⱼ = Qᵢⱼ·Bᵢ^(i−j+1)·Cᵢ^(2i−j) (mod Dᵢ)`. -/
example (A D Di : K[X]) (i j : ℕ) :
    laurentH A D Di i j
      = (laurentQ A Di i j * bezoutE D Di i ^ (i - j + 1) * bezoutDeriv Di ^ (2 * i - j)) %ₘ Di :=
  laurentH_def A D Di i j

/-- Restatement of the `i=1` residue (book p.56): `H₁₁(α) = A(α)/D'(α)` at a simple root `α` of `D`. -/
example {A D Di : K[X]} {α : K} (hDi : Di.Monic) (hα : Di.eval α = 0)
    (hfac : D = Di * laurentE D Di 1) (hcopE : IsCoprime (laurentE D Di 1) Di)
    (hcopD : IsCoprime (derivative Di) Di)
    (hE : (laurentE D Di 1).eval α ≠ 0) (hD' : (derivative Di).eval α ≠ 0) :
    (laurentH A D Di 1 1).eval α = A.eval α / (derivative D).eval α :=
  eval_laurentH_one_one_eq_residue hDi hα hfac hcopE hcopD hE hD'

end DeepWiki.SymbolicIntegration
