import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Taylor
import DeepWiki.SymbolicIntegration.SquarefreeFactorization
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms
import DeepWiki.SymbolicIntegration.RecognizingLogDeriv
import DeepWiki.SymbolicIntegration.CompletePartialFraction

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
`hᵢ^d/d! = P/(u^a·Eᵢ^b)` (with `a = i+d`, `b = d+1`), one `d/dx` and the factorial factor `1/(d+1) = 1/b`
give the numerator of `hᵢ^(d+1)/(d+1)!`, namely
`(1/b)·(ddx P · u · Eᵢ − P·(a·u'·Eᵢ + b·u·Eᵢ'))` over `u^(a+1)·Eᵢ^(b+1)`. Here `Eᵢ = dpEmbed Ei`,
`Eᵢ' = dpEmbed (derivative Ei)`, `u = X (some 0)`, `u' = X (some 1)`. The divisor is the factorial
increment `b = d+1` (since `hᵢ^(d+1)/(d+1)! = (1/(d+1))·d/dx(hᵢ^(d)/d!)`), NOT `a+1`. -/
noncomputable def laurentNumStep (Ei : K[X]) (a b : ℕ) (P : DiffPoly K) : DiffPoly K :=
  MvPolynomial.C ((b : K)⁻¹) *
    (ddx P * X (some 0) * dpEmbed Ei
      - P * ((a : DiffPoly K) * X (some 1) * dpEmbed Ei
              + (b : DiffPoly K) * X (some 0) * dpEmbed (derivative Ei)))

/-- **The Laurent numerator `Pᵢⱼ`** (§2.7, eq 2.11), indexed by the derivative count `d = i − j` running
`0,1,…`: `laurentNum A Ei i 0 = dpEmbed A` (the numerator of `hᵢ = A/(uⁱ·Eᵢ)`), and each successive `d`
applies `laurentNumStep` with denominator exponents `a = i+d`, `b = d+1` (so the factorial divisor is
`b = d+1`). So `laurentNum A Ei i d` is EXACTLY the book's `Pᵢⱼ` with `j = i − d`, the numerator of
`hᵢ^d/d! = Pᵢⱼ/(u^(i+d)·Eᵢ^(d+1))` — no scale discrepancy. -/
noncomputable def laurentNum (A Ei : K[X]) (i : ℕ) : ℕ → DiffPoly K
  | 0 => dpEmbed A
  | d + 1 => laurentNumStep Ei (i + d) (d + 1) (laurentNum A Ei i d)

@[simp] theorem laurentNum_zero (A Ei : K[X]) (i : ℕ) :
    laurentNum A Ei i 0 = dpEmbed A := rfl

theorem laurentNum_succ (A Ei : K[X]) (i d : ℕ) :
    laurentNum A Ei i (d + 1)
      = laurentNumStep Ei (i + d) (d + 1) (laurentNum A Ei i d) := rfl

/-- **The cleared quotient-rule step** (§2.7, eq 2.11 differentiated, denominator-free form): over a
characteristic-`0` field the factorial divisor `1/(d+1)` in `laurentNumStep` clears, giving the polynomial
identity `(d+1)·Pᵢ,d₊₁ = ddx Pᵢ,d · u · Eᵢ − Pᵢ,d·((i+d)·u'·Eᵢ + (d+1)·u·Eᵢ')` in `DiffPoly K`. This is the
factorial-scaled numerator of the quotient rule `d/dx (P/(uᵃ·Eᵢᵇ)) =
(ddx P·u·Eᵢ − P·(a·u'·Eᵢ + b·u·Eᵢ'))/(uᵃ⁺¹·Eᵢᵇ⁺¹)` with `a = i+d`, `b = d+1` (so dividing by `b = d+1`
yields `Pᵢ,d₊₁`), validating the `Pᵢⱼ` recursion against the genuine `d/dx` of `hᵢ^d/d!`. -/
theorem laurentNum_cleared_step [CharZero K] (A Ei : K[X]) (i d : ℕ) :
    MvPolynomial.C ((d : K) + 1) * laurentNum A Ei i (d + 1)
      = ddx (laurentNum A Ei i d) * X (some 0) * dpEmbed Ei
        - laurentNum A Ei i d
            * ((i + d : DiffPoly K) * X (some 1) * dpEmbed Ei
                + (d + 1 : DiffPoly K) * X (some 0) * dpEmbed (derivative Ei)) := by
  rw [laurentNum_succ, laurentNumStep, ← mul_assoc, ← MvPolynomial.C_mul]
  have hne : ((d : ℕ) : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
  rw [show ((d : K) + 1) = (((d + 1 : ℕ)) : K) by push_cast; ring,
      mul_inv_cancel₀ (by exact_mod_cast hne), MvPolynomial.C_1, one_mul]
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
derivatives of `Dᵢ` for the differential variables in the numerator `Pᵢⱼ = laurentNum A Eᵢ i (i−j)`. Here
`Eᵢ = laurentE D Dᵢ i = D /ₘ Dᵢ^i` is the book's cofactor (the part of `D` complementary to `Dᵢ^i`), so the
numerator recursion differentiates the genuine `hᵢ = A/(Dᵢ^i·Eᵢ)`. -/
noncomputable def laurentQ (A D Di : K[X]) (i j : ℕ) : K[X] :=
  aeval (laurentSubst Di) (laurentNum A (laurentE D Di i) i (i - j))

/-- **The Bronstein–Salvy Laurent coefficient `Hᵢⱼ ∈ K[x]`** (§2.7, eq 2.12, **the engine**):
`Hᵢⱼ = Qᵢⱼ·Bᵢ^(i−j+1)·Cᵢ^(2i−j) (mod Dᵢ)`, computed by purely rational operations over `K` without
factoring `Dᵢ`. The Laurent coefficient of `1/(x−α)^j` at a root `α` of `Dᵢ` is `Hᵢⱼ(α)`. -/
noncomputable def laurentH (A D Di : K[X]) (i j : ℕ) : K[X] :=
  (laurentQ A D Di i j * bezoutE D Di i ^ (i - j + 1) * bezoutDeriv Di ^ (2 * i - j)) %ₘ Di

theorem laurentH_def (A D Di : K[X]) (i j : ℕ) :
    laurentH A D Di i j
      = (laurentQ A D Di i j * bezoutE D Di i ^ (i - j + 1) * bezoutDeriv Di ^ (2 * i - j)) %ₘ Di :=
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
theorem laurentQ_one_one (A D Di : K[X]) : laurentQ A D Di 1 1 = A := by
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

/-- **Membership in `nonZeroDivisors`** for a nonzero `DiffPoly K` element (a domain, so nonzero ⇒
not a zero divisor). -/
private theorem mem_nzd {p : DiffPoly K} (hp : p ≠ 0) : p ∈ nonZeroDivisors (DiffPoly K) :=
  mem_nonZeroDivisors_iff_ne_zero.mpr hp

/-- **`lFrac` as a `Localization.mk`**: `Pᵢ,d/(u^(i+d)·Eᵢ^(d+1)) = mk Pᵢ,d ⟨denom_d⟩`. -/
theorem lFrac_mk (A Ei : K[X]) (i d : ℕ) (hEi : Ei ≠ 0) :
    lFrac A Ei i d
      = Localization.mk (laurentNum A Ei i d) ⟨lDenom Ei i d, mem_nzd (lDenom_ne_zero i d hEi)⟩ := by
  unfold lFrac; rw [Localization.mk_eq_mk', IsFractionRing.mk'_eq_div]

/-- **The reduced quotient-rule numerator** (`i+d ≥ 1`): differentiating `Pᵢ,d/denom_d` and reducing,
`ddx Pᵢ,d·denom_d − Pᵢ,d·ddx denom_d = u^(i+d−1)·Eᵢ^d·((d+1)·Pᵢ,d₊₁)` — the common factor `u^(i+d−1)·Eᵢ^d`
(`= denom_d² / denom_{d+1}`) extracted, leaving the factorial-scaled `(d+1)·Pᵢ,d₊₁` by
`laurentNum_cleared_step`. Stated with `m = i+d−1` to keep the exponent honest. -/
theorem reduced_num [CharZero K] (A Ei : K[X]) (i d m : ℕ) (hm : i + d = m + 1) :
    ddx (laurentNum A Ei i d) * lDenom Ei i d - laurentNum A Ei i d * ddx (lDenom Ei i d)
      = X (some 0) ^ m * dpEmbed Ei ^ d *
          (MvPolynomial.C ((d : K) + 1) * laurentNum A Ei i (d + 1)) := by
  rw [laurentNum_cleared_step]
  unfold lDenom
  rw [hm]
  have hddxE : ddx (dpEmbed Ei) = dpEmbed (derivative Ei) := ddx_dpEmbed Ei
  have hmK : ((i : DiffPoly K) + (d : DiffPoly K)) = (m : DiffPoly K) + 1 := by exact_mod_cast hm
  have key : ddx (X (some 0) ^ (m + 1) * dpEmbed Ei ^ (d + 1))
      = ((m : DiffPoly K) + 1) * X (some 0) ^ m * X (some 1) * dpEmbed Ei ^ (d + 1)
        + X (some 0) ^ (m + 1) * ((d : DiffPoly K) + 1) * dpEmbed Ei ^ d * dpEmbed (derivative Ei) := by
    rw [Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow, ddx_u 0, hddxE]
    simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul, dpU]; push_cast; ring
  rw [key, pow_succ (X (some 0) : DiffPoly K) m, pow_succ (dpEmbed Ei : DiffPoly K) d, hmK]
  ring

/-- **The `hᵢ^(d)`-recursion step in `K(x)⟨u⟩`** (§2.7, eq 2.11): `d/dx (Pᵢ,d/denom_d) = (d+1)·(Pᵢ,d₊₁/denom_{d+1})`
— differentiating the `d`-th fraction gives the `(d+1)`-th scaled by the factorial increment `d+1` (the
divisor `laurentNumStep` clears). This is exactly `d/dx (hᵢ^d/d!) = (d+1)·(hᵢ^(d+1)/(d+1)!)`. Proved via
`reduced_num` + `lDenom_succ`. Requires `0 < i` (so `u^(i+d)` has a positive power to differentiate) and
`Ei ≠ 0`. -/
theorem fracKDeriv_lFrac [CharZero K] (A Ei : K[X]) (i d : ℕ) (hi : 0 < i) (hEi : Ei ≠ 0) :
    fracKDeriv (lFrac A Ei i d) = ((d : K) + 1) • lFrac A Ei i (d + 1) := by
  obtain ⟨m, hm⟩ : ∃ m, i + d = m + 1 := ⟨i + d - 1, by omega⟩
  rw [lFrac_mk A Ei i d hEi, lFrac_mk A Ei i (d + 1) hEi, fracKDeriv_apply, fracDeriv_mk]
  show (Localization.mk _ ⟨(lDenom Ei i d) ^ 2, _⟩ : FractionRing (DiffPoly K)) = _
  rw [Localization.smul_mk]
  apply mk_eq_of
  show lDenom Ei i (d + 1) * _ = (lDenom Ei i d) ^ 2 * _
  rw [reduced_num A Ei i d m hm, MvPolynomial.smul_eq_C_mul, lDenom_succ]
  unfold lDenom
  rw [hm]; ring

/-- **The factorial divisor `d!`** accumulated by the `laurentNumStep` recursion (which divides by the
factorial increment `d+1` at step `d`), realized in `K`. With the corrected normalization the scale is the
pure factorial `d! = ∏_{k=0}^{d−1}(k+1)`, matching the book's `hᵢ^(d)/d!`. -/
noncomputable def laurentScale (K : Type*) [Field K] (i : ℕ) : ℕ → K
  | 0 => 1
  | d + 1 => laurentScale K i d * ((d : K) + 1)

/-- **`laurentScale = d!`** (the corrected scale collapses to the pure factorial): with `laurentNumStep`
dividing by the factorial increment `d+1`, the accumulated product `laurentScale K i d` is exactly the
factorial `(d! : K)`, independent of `i`. -/
theorem laurentScale_eq_factorial (i d : ℕ) : laurentScale K i d = (d.factorial : K) := by
  induction d with
  | zero => simp [laurentScale]
  | succ n ih => rw [laurentScale, ih, Nat.factorial_succ]; push_cast; ring

/-- **The eq 2.11 invariant in `K(x)⟨u⟩ = Frac (DiffPoly K)`** (§2.7, the validation of the `Pᵢⱼ` recursion):
`(d/dx)^[d] hᵢ = d! · (Pᵢ,d / (u^(i+d)·Eᵢ^(d+1)))` for `hᵢ = A/(uⁱ·Eᵢ)` — i.e. exactly the book's
`hᵢ^(d)/d! = Pᵢⱼ/denom_d` (`= Pᵢⱼ/(u^(i+d)·Eᵢ^(d+1))`). Since `laurentNumStep` divides by the factorial
increment `d+1`, the `d`-th derivative carries the factorial `laurentScale K i d = d!` (`laurentScale_eq_factorial`);
the engine's `laurentNum` is EXACTLY the book's `Pᵢⱼ`. Proved by induction via `fracKDeriv_lFrac`. -/
theorem iterate_fracKDeriv_hFrac [CharZero K] (A Ei : K[X]) (i : ℕ) (hi : 0 < i) (hEi : Ei ≠ 0)
    (d : ℕ) :
    (fracKDeriv^[d]) (hFrac A Ei i) = (laurentScale K i d) • lFrac A Ei i d := by
  induction d with
  | zero => rw [Function.iterate_zero_apply, laurentScale, one_smul, lFrac_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, laurentScale, Derivation.map_smul,
      fracKDeriv_lFrac A Ei i n hi hEi, smul_smul]

/-! ## Stage G — the root-evaluation `Qᵢⱼ(α) = Pᵢⱼ(α, Dᵢα(α), …)` (book p.56)

At a root `α` of `Dᵢ` over the algebraic closure, write `Dᵢ = (x−α)·Dᵢ,α`. The substitution `Qᵢⱼ`
(`u^(k) ↦ Dᵢ^(k+1)/(k+1)`) evaluated at `α` recovers the derivatives of `Dᵢ,α`: the engine of this is the
Leibniz identity `Dᵢ^(k+1)(α) = (k+1)·Dᵢ,α^(k)(α)` (book p.56, since `(x−α)^(j)=0` for `j>1`), giving
`Dᵢ^(k+1)(α)/(k+1) = Dᵢ,α^(k)(α)`. Hence `Qᵢⱼ(α) = Pᵢⱼ(α, Dᵢ,α(α), Dᵢ,α'(α), …, Dᵢ,α^(i−j)(α))`. -/

/-- **Leibniz for `(x−α)·p`** (book p.56): `(((x−α)·p)^(k+1) = (x−α)·p^(k+1) + (k+1)·p^(k)`, since the
second and higher derivatives of `x−α` vanish. -/
theorem iterate_derivative_X_sub_C_mul (α : K) (p : K[X]) (k : ℕ) :
    derivative^[k + 1] ((Polynomial.X - Polynomial.C α) * p)
      = (Polynomial.X - Polynomial.C α) * derivative^[k + 1] p + ((k + 1 : ℕ)) • derivative^[k] p := by
  induction k with
  | zero =>
    simp only [Function.iterate_one, Function.iterate_zero_apply, zero_add, derivative_mul,
      derivative_sub, derivative_X, Polynomial.derivative_C, sub_zero, one_mul, one_smul]
    ring
  | succ n ih =>
    have e1 : derivative^[n + 2] ((Polynomial.X - Polynomial.C α) * p)
        = derivative (derivative^[n + 1] ((Polynomial.X - Polynomial.C α) * p)) :=
      Function.iterate_succ_apply' derivative (n + 1) _
    have e2 : derivative (derivative^[n + 1] p) = derivative^[n + 2] p :=
      (Function.iterate_succ_apply' derivative (n + 1) p).symm
    have e3 : derivative (derivative^[n] p) = derivative^[n + 1] p :=
      (Function.iterate_succ_apply' derivative n p).symm
    rw [e1, ih, map_add, derivative_mul, derivative_sub, derivative_X, Polynomial.derivative_C,
      sub_zero, one_mul, derivative_smul, e2, e3, succ_nsmul]
    ring_nf

/-- **`Dᵢ^(k+1)(α) = (k+1)·Dᵢ,α^(k)(α)`** at a root (book p.56): evaluating `iterate_derivative_X_sub_C_mul`
at `α` kills the `(x−α)` factor. -/
theorem eval_iterate_derivative_X_sub_C_mul (α : K) (p : K[X]) (k : ℕ) :
    (derivative^[k + 1] ((Polynomial.X - Polynomial.C α) * p)).eval α
      = ((k : K) + 1) * (derivative^[k] p).eval α := by
  rw [iterate_derivative_X_sub_C_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, zero_add, Polynomial.eval_smul,
    nsmul_eq_mul]
  push_cast; ring

/-- **`(laurentSubst Dᵢ (u^(k)))(α) = Dᵢ,α^(k)(α)`** (book p.56, the substitution's root value): the scaled
derivative `Dᵢ^(k+1)/(k+1)` evaluated at a root `α` of `Dᵢ = (x−α)·Dᵢ,α` is the `k`-th derivative of `Dᵢ,α`. -/
theorem eval_laurentSubst_some [CharZero K] (Diα : K[X]) (α : K) (k : ℕ) :
    (laurentSubst ((Polynomial.X - Polynomial.C α) * Diα) (some k)).eval α
      = (derivative^[k] Diα).eval α := by
  unfold laurentSubst
  rw [Polynomial.eval_mul, Polynomial.eval_C, eval_iterate_derivative_X_sub_C_mul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_add_one_ne_zero (R := K) k), one_mul]

/-- **`eval ∘ aeval` collapses to a single evaluated substitution**: `(aeval f P)(α) = aeval (v ↦ f(v)(α)) P`
for `P ∈ DiffPoly K`, `f : Option ℕ → K[x]` — push the outer `eval α` through the `aeval`. -/
theorem eval_aeval_diffPoly (f : Option ℕ → K[X]) (α : K) (P : DiffPoly K) :
    Polynomial.eval α (MvPolynomial.aeval f P) = MvPolynomial.aeval (fun v => (f v).eval α) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

/-- **The root-substitution point** `v ↦` (its value at `α`): `x ↦ α`, `u^(k) ↦ Dᵢ,α^(k)(α)` — the
arguments of `Pᵢⱼ` in the book's `Qᵢⱼ(α) = Pᵢⱼ(α, Dᵢ,α(α), Dᵢ,α'(α), …)`. -/
noncomputable def substEvalAt (Diα : K[X]) (α : K) : Option ℕ → K := fun v =>
  match v with
  | none => α
  | some k => (derivative^[k] Diα).eval α

/-- **`Qᵢⱼ(α) = Pᵢⱼ(α, Dᵢ,α(α), Dᵢ,α'(α), …, Dᵢ,α^(i−j)(α))`** (book p.56): at a root `α` of
`Dᵢ = (x−α)·Dᵢ,α`, the `Qᵢⱼ` substitution evaluates to `Pᵢⱼ` at the derivatives of `Dᵢ,α` — by
`eval_aeval_diffPoly` (collapse the outer `eval α`) and `eval_laurentSubst_some` (each `u^(k)` value).
This is the substantive root-evaluation step; identifying the resulting `Pᵢⱼ(α,…)` with the `(i−j)`-th
Taylor coefficient of `hᵢ,α = (A/D)(x−α)ⁱ` at `α` (hence the `1/(x−α)ʲ` Laurent coefficient of `A/D`)
is the remaining Taylor-series argument over the closure. -/
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

/-! ## Stage H — the differential substitution hom `σα` and the specialized invariant (book p.56)

The bridge from the differential-variable engine to the **actual** function `hᵢ,α = (A/D)(x−α)ⁱ`:
substitute the genuine derivatives of `Dᵢ,α = Dᵢ /ₘ (x−α)` for the differential variables. The map
`diffSubst Diα : DiffPoly K →ₐ[K] K[x]` sends `x ↦ X`, `u^(k) ↦ derivative^[k] Diα`; it is a
**differential** algebra hom — `diffSubst Diα (ddx p) = derivative (diffSubst Diα p)` — so it carries the
engine's `ddx` to the genuine `Polynomial.derivative`, and hence commutes with the iterated `(d/dx)^[d]`. -/

/-- **The differential substitution hom** `σα : DiffPoly K →ₐ[K] K[x]` (book p.56): the `K`-algebra map
`x ↦ X`, `u^(k) ↦ Dᵢ,α^(k) = derivative^[k] Diα`, substituting the genuine derivatives of `Diα` (`= Dᵢ,α`,
the `(x−α)`-cofactor of `Dᵢ` at the root `α`) for the differential indeterminate's derivatives. -/
noncomputable def diffSubst (Diα : K[X]) : DiffPoly K →ₐ[K] K[X] :=
  MvPolynomial.aeval fun v => match v with
    | none => Polynomial.X
    | some k => derivative^[k] Diα

@[simp] theorem diffSubst_X_none (Diα : K[X]) :
    diffSubst Diα (X none : DiffPoly K) = Polynomial.X := by
  simp [diffSubst]

@[simp] theorem diffSubst_X_some (Diα : K[X]) (k : ℕ) :
    diffSubst Diα (X (some k) : DiffPoly K) = derivative^[k] Diα := by
  simp [diffSubst]

@[simp] theorem diffSubst_C (Diα : K[X]) (a : K) :
    diffSubst Diα (MvPolynomial.C a : DiffPoly K) = Polynomial.C a := by
  simp [diffSubst]

@[simp] theorem diffSubst_dpEmbed (Diα p : K[X]) : diffSubst Diα (dpEmbed p) = p := by
  have h : ((diffSubst Diα : DiffPoly K →ₐ[K] K[X]).toRingHom.comp dpEmbed) = RingHom.id K[X] := by
    apply Polynomial.ringHom_ext
    · intro c; simp [dpEmbed]
    · simp [dpEmbed]
  exact congrArg (fun f : K[X] →+* K[X] => f p) h

/-- **`σα` is a differential hom** (book p.56, the key bridge): `σα (ddx p) = derivative (σα p)` — the
substitution carries the engine's `d/dx` (`ddx`) to the genuine `Polynomial.derivative`. By
`MvPolynomial.induction_on`: on `C a` both vanish, on a product `p·X v` Leibniz on both sides reduces to the
base cases `σα(ddx (X none)) = σα 1 = 1 = derivative X` and
`σα(ddx (X (some k))) = derivative^[k+1] Diα = derivative (derivative^[k] Diα) = derivative (σα (X (some k)))`. -/
theorem diffSubst_ddx (Diα : K[X]) (p : DiffPoly K) :
    diffSubst Diα (ddx p) = derivative (diffSubst Diα p) := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [← MvPolynomial.algebraMap_eq, (ddx (K := K)).map_algebraMap, map_zero,
      AlgHom.commutes, Polynomial.algebraMap_eq, derivative_C]
  | add p q hp hq => rw [map_add, map_add, map_add, derivative_add, hp, hq]
  | mul_X p v hp =>
      have hbase : diffSubst Diα (ddx (X v : DiffPoly K)) = derivative (diffSubst Diα (X v)) := by
        cases v with
        | none => rw [ddx_x, map_one, diffSubst_X_none, derivative_X]
        | some k =>
            rw [show ddx (X (some k) : DiffPoly K) = X (some (k + 1)) from ddx_u k,
              diffSubst_X_some, diffSubst_X_some, ← Function.iterate_succ_apply' derivative k Diα]
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hp, hbase,
        map_mul, derivative_mul]
      ring

/-! ## Stage I — the specialized eq 2.11 invariant in `K(x) = RatFunc K` (Step 2)

Pushing the `K(x)⟨u⟩` invariant `iterate_fracKDeriv_hFrac` through `σα` lands in `K(x) = RatFunc K`: the
genuine function `hᵢ,α = A/(Dᵢ,α^i·Eᵢ)` (`= σα hᵢ`), under the genuine `d/dx = ratFuncKDeriv`, satisfies
`(d/dx)^[d] hᵢ,α = d!·(σα(Pᵢ,d)/(Dᵢ,α^{i+d}·Eᵢ^{d+1}))`. Because `σα` is surjective but not injective, this
is proved by re-running the induction at the `RatFunc K` level — the polynomial step `reduced_num` carries
through `σα` (a *differential* hom, `diffSubst_ddx`) to a `K[x]` identity, then `leibniz_div` gives the
quotient-rule recursion. This makes the engine's `Pᵢⱼ` genuinely the numerators of the derivatives of the
actual rational function `hᵢ,α`. -/

/-- **The genuine `hᵢ,α`-denominator** `Dᵢ,α^{i+d}·Eᵢ^{d+1} ∈ K[x]` (`= σα (lDenom Ei i d)`): the
specialization of `lDenom` along `u ↦ Dᵢ,α = Diα`, `Eᵢ ↦ Ei`. -/
noncomputable def lDenomα (Ei Diα : K[X]) (i d : ℕ) : K[X] := Diα ^ (i + d) * Ei ^ (d + 1)

/-- **`σα (lDenom Ei i d) = lDenomα Ei Diα i d`** (`= Dᵢ,α^{i+d}·Eᵢ^{d+1}`): the substitution maps the
differential denominator `u^{i+d}·Eᵢ^{d+1}` to the genuine `Dᵢ,α^{i+d}·Eᵢ^{d+1}` (`u = X (some 0) ↦ Diα`,
`dpEmbed Ei ↦ Ei`). -/
theorem diffSubst_lDenom (Ei Diα : K[X]) (i d : ℕ) :
    diffSubst Diα (lDenom Ei i d) = lDenomα Ei Diα i d := by
  unfold lDenom lDenomα
  rw [map_mul, map_pow, map_pow, diffSubst_X_some Diα 0, diffSubst_dpEmbed,
    Function.iterate_zero_apply]

/-- **`lDenomα ≠ 0`** for `Ei, Diα ≠ 0`. -/
theorem lDenomα_ne_zero {Ei Diα : K[X]} (i d : ℕ) (hEi : Ei ≠ 0) (hDiα : Diα ≠ 0) :
    lDenomα Ei Diα i d ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ hDiα) (pow_ne_zero _ hEi)

/-- **The genuine `hᵢ,α^{(d)}/d!` fraction** `σα(Pᵢ,d)/(Dᵢ,α^{i+d}·Eᵢ^{d+1}) ∈ K(x)` (`= σα` of `lFrac`). -/
noncomputable def lFracα (A Ei Diα : K[X]) (i d : ℕ) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (diffSubst Diα (laurentNum A Ei i d)) /
    algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i d)

/-- **`hᵢ,α = A/(Dᵢ,α^i·Eᵢ) = (A/D)·(x−α)ⁱ`** in `K(x)` (`= σα hᵢ`): the genuine rational function whose
`d`-th derivative the engine's `Pᵢ,d` computes. -/
noncomputable def hFracα (A Ei Diα : K[X]) (i : ℕ) : RatFunc K :=
  algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i 0)

/-- **`lFracα` base case** `d=0`: `σα(A)/denomα₀ = A/(Dᵢ,α^i·Eᵢ) = hᵢ,α`. -/
theorem lFracα_zero (A Ei Diα : K[X]) (i : ℕ) : lFracα A Ei Diα i 0 = hFracα A Ei Diα i := by
  unfold lFracα hFracα; rw [laurentNum_zero, diffSubst_dpEmbed]

/-- **The reduced quotient-rule numerator, pushed through `σα`** (`= σα` of `reduced_num`): the genuine
`K[x]` identity `Pᵢ,d^α'·denomα_d − Pᵢ,d^α·denomα_d' = Dᵢ,α^{i+d−1}·Eᵢ^d·((d+1)·Pᵢ,d₊₁^α)`, where
`Pᵢ,d^α = σα(laurentNum …)` and `'` is the genuine `Polynomial.derivative`. Applies `diffSubst_ddx` (so
`σα(ddx P) = derivative(σα P)`) to the differential identity `reduced_num`. -/
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

/-- **The recursion step in `K(x)`** (`= σα` of `fracKDeriv_lFrac`): differentiating the genuine
`hᵢ,α^{(d)}/d!` fraction gives the `(d+1)`-th scaled by `d+1`,
`ratFuncKDeriv (lFracα …d) = (d+1)·lFracα …(d+1)`. The genuine quotient rule via `leibniz_div` +
`reduced_numα`. Requires `0 < i`, `Ei ≠ 0`, `Diα ≠ 0`. -/
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

/-- **The specialized eq 2.11 invariant in `K(x)`** (§2.7, p.56, the genuine-function form, Step 2): the
`d`-th genuine derivative of the actual rational function `hᵢ,α = A/(Dᵢ,α^i·Eᵢ)` is `d!` times the engine's
`σα(Pᵢ,d)/(Dᵢ,α^{i+d}·Eᵢ^{d+1})`,
`(d/dx)^[d] hᵢ,α = d! · (σα(laurentNum A Eᵢ i d) / (Dᵢ,α^{i+d}·Eᵢ^{d+1}))` in `RatFunc K`. This is the image
of `iterate_fracKDeriv_hFrac` under the differential hom `σα` — proved by induction at the `K(x)` level via
`ratFuncKDeriv_lFracα`, since `σα` is surjective but not injective. It makes the engine's `Pᵢⱼ` genuinely
the numerators of the derivatives of the actual function `hᵢ,α = (A/D)(x−α)ⁱ`. Requires `0 < i`,
`Ei ≠ 0`, `Diα ≠ 0`. -/
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

/-! ## Stage J — the root-value bridge `σα(Pᵢ,d)(α) = Qᵢⱼ(α)` (Step 3) and the residual Laurent fact

`σα(Pᵢ,d)(α)` (the numerator of the genuine `hᵢ,α^{(d)}/d!` evaluated at `α`, from Step 2) coincides with the
book's `Qᵢⱼ(α) = Pᵢⱼ(α, Dᵢ,α(α), …)` (Stage G): both are `aeval (substEvalAt Diα α) (laurentNum …)`. So the
engine's `Qᵢⱼ(α)` IS the numerator of the `(i−j)`-th derivative of the actual rational function `hᵢ,α` at
`α` — i.e. `(i−j)!·[Taylor coeff of hᵢ,α at α, order i−j]·(Dᵢ,α(α)^{2i−j}·Eᵢ(α)^{i−j+1})`. -/

/-- **`(σα P)(α) = Pᵢⱼ(α, Dᵢ,α(α), …)`** (the evaluated differential hom): evaluating `σα P` at `α`
collapses to the `aeval` of `P` at the root-substitution point `substEvalAt Diα α` (`x ↦ α`,
`u^(k) ↦ Dᵢ,α^{(k)}(α)`), by pushing `eval α` through the `aeval`. -/
theorem eval_diffSubst (Diα : K[X]) (α : K) (P : DiffPoly K) :
    Polynomial.eval α (diffSubst Diα P) = MvPolynomial.aeval (substEvalAt Diα α) P := by
  rw [diffSubst, eval_aeval_diffPoly]
  have hfun : (fun v => Polynomial.eval α
        (match v with | (none : Option ℕ) => Polynomial.X | some k => derivative^[k] Diα))
      = substEvalAt Diα α := by
    funext v
    cases v with
    | none => simp [substEvalAt]
    | some k => simp [substEvalAt]
  rw [hfun]

/-- **Step 3, the bridge `σα(Pᵢ,d)(α) = Qᵢⱼ(α)`** (book p.56): the value at `α` of the genuine
`hᵢ,α^{(i−j)}/(i−j)!` numerator (`= σα(laurentNum …)`, Step 2) equals the engine's `Qᵢⱼ(α)` (Stage G,
`laurentQ_eval_at_root`), since both are `aeval (substEvalAt Diα α) (laurentNum …)`. This identifies the
engine's rational `Qᵢⱼ(α)` with the (Taylor-coefficient-bearing) numerator of the **actual** rational
function `hᵢ,α = (A/D)(x−α)ⁱ`. -/
theorem eval_diffSubst_laurentNum_eq_laurentQ_eval [CharZero K] (A D Diα : K[X]) (α : K) (i j : ℕ) :
    Polynomial.eval α
        (diffSubst Diα (laurentNum A (laurentE D ((Polynomial.X - Polynomial.C α) * Diα) i) i (i - j)))
      = (laurentQ A D ((Polynomial.X - Polynomial.C α) * Diα) i j).eval α := by
  rw [eval_diffSubst, laurentQ_eval_at_root]

/-! ### Step 4 — the remaining extraction lemma (the pole-order-`j` Laurent coefficient)

What remains for the full general Thm 2.7.1 correctness (`Hᵢⱼ(α) =` the `1/(x−α)ʲ` partial-fraction
coefficient `c_j` of `A/D`) is the **Taylor/Laurent extraction over the algebraic closure**, NOT reachable
with the present simple-pole `residueAt` (`RecognizingLogDeriv.residueAt`, the coefficient of `1/(x−α)¹`
only). Precisely, the residual fact is:

> **Laurent extraction (Step 4).** Over `K̄`, with `hᵢ,α = (A/D)(x−α)ⁱ` regular at `α` and `A/D` having a
> pole of order `≤ i` at `α` with principal part `∑_{k=1}^{i} c_k/(x−α)^k`, the order-`(i−j)` Taylor
> coefficient of `hᵢ,α` at `α` is exactly `c_j` (the `1/(x−α)ʲ` partial-fraction coefficient of `A/D`):
> `(d/dx)^[i−j] hᵢ,α (α) / (i−j)! = c_j`.

Combined with Step 2 (`iterate_ratFuncKDeriv_hFracα`, giving `(d/dx)^[i−j] hᵢ,α (α) = (i−j)!·Qᵢⱼ(α) /
(Dᵢ,α(α)^{2i−j}·Eᵢ(α)^{i−j+1})` via Step 3) and Step 5 (`Hᵢⱼ(α) = Qᵢⱼ(α)·Bᵢ(α)^{i−j+1}·Cᵢ(α)^{2i−j}`,
`eval_laurentH` below, with `Bᵢ(α) = 1/Eᵢ(α)`, `Cᵢ(α) = 1/Dᵢ'(α)`), this yields `Hᵢⱼ(α) = c_j`. The blocker
is the **higher-order** principal-part extraction (a `residueAt`-of-order-`j` generalization: multiply by
`(x−α)ʲ`, take `(i−j)` derivatives, evaluate; the library's `residueAt` does only the `j=1`, `(i−j)=0` case).
The `i=j=1` instance is closed (`eval_laurentH_one_one_eq_residue`). -/

/-- **Step 5, the general engine-output evaluation** `Hᵢⱼ(α) = Qᵢⱼ(α)·Bᵢ(α)^{i−j+1}·Cᵢ(α)^{2i−j}` (§2.7,
eq 2.12 evaluated, generalizing `eval_laurentH_one_one` from `i=j=1` to all `i,j`): at a root `α` of the
monic `Dᵢ`, the `%ₘ Dᵢ` reduction is invisible (`eval_modByMonic_of_root`), so the engine output evaluates
to `Qᵢⱼ(α)·(1/Eᵢ(α))^{i−j+1}·(1/Dᵢ'(α))^{2i−j}` — the substitution value times the Bézout-cofactor powers
`Bᵢ(α) = 1/Eᵢ(α)`, `Cᵢ(α) = 1/Dᵢ'(α)` (from the (2.10) congruences
`bezoutE_mul_laurentE_eval`/`bezoutDeriv_mul_derivative_eval`). This is the `K`-level value the Laurent fact
(Step 4) then identifies with the `1/(x−α)ʲ` partial-fraction coefficient `c_j`. -/
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

/-- **Steps 2+3+5 combined: `Hᵢⱼ(α)` from the genuine `hᵢ,α`-numerator** (§2.7, p.56): at a root `α` of the
monic `Dᵢ = (x−α)·Dᵢ,α`, the engine output is `Hᵢⱼ(α) = σα(Pᵢ,i−j)(α)·(1/Eᵢ(α))^{i−j+1}·(1/Dᵢ'(α))^{2i−j}`,
where `σα(Pᵢ,i−j)(α) = Polynomial.eval α (diffSubst Dᵢ,α (laurentNum …))` is the value at `α` of the
**genuine** `hᵢ,α^{(i−j)}/(i−j)!` numerator (`= σα(laurentNum …)`, Step 2; `= Qᵢⱼ(α)`, Step 3,
`eval_diffSubst_laurentNum_eq_laurentQ_eval`). This routes the engine's `Qᵢⱼ(α)` through the *actual*
rational function `hᵢ,α = (A/D)(x−α)ⁱ`. The only remaining gap to `Hᵢⱼ(α) = c_j` is identifying
`σα(Pᵢ,i−j)(α)`-via-`(Dᵢ,α,Eᵢ)`-powers with the order-`(i−j)` Taylor coefficient of `hᵢ,α` (Step 4). -/
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

/-! ## Stage K — (a) `Hᵢⱼ(α)` is the order-`(i−j)` Taylor coefficient of `hᵢ,α` (Step 4, the reachable core)

Evaluating the specialized eq 2.11 invariant `iterate_ratFuncKDeriv_hFracα` (Stage I) at the root `α` via
`RatFunc.eval (RingHom.id K) α` — a ring hom away from the (here nonzero) denominator `Dᵢ,α(α)·Eᵢ(α) ≠ 0`
— gives `(d/dx)^[i−j] hᵢ,α (α) = (i−j)!·σα(Pᵢ,i−j)(α)/(Dᵢ,α(α)^{2i−j}·Eᵢ(α)^{i−j+1})`. Combined with the
cofactor identity `Dᵢ'(α) = Dᵢ,α(α)` (from `Dᵢ = (x−α)·Dᵢ,α`) and `eval_laurentH_eq_diffSubst_laurentNum`
(Steps 2+3+5), the `(Dᵢ,α, Eᵢ)`-power denominators cancel the `(1/Eᵢ(α))^{i−j+1}·(1/Dᵢ'(α))^{2i−j}` factors,
identifying the engine output `Hᵢⱼ(α)` with the **order-`(i−j)` Taylor coefficient of `hᵢ,α = (A/D)(x−α)ⁱ`
at `α`**, i.e. `(d/dx)^[i−j] hᵢ,α (α)/(i−j)!`. Those Taylor coefficients ARE the `1/(x−α)ʲ` partial-fraction
(Laurent) coefficients of `A/D` by the very definition of `hᵢ,α`, so this completes Thm 2.7.1 up to the
literal `= c_j` naming. -/

/-- **The cofactor at a simple root: `Dᵢ'(α) = Dᵢ,α(α)`** (book p.56): when `Dᵢ = (x−α)·Dᵢ,α`, the
derivative `Dᵢ' = Dᵢ,α + (x−α)·Dᵢ,α'`, so at the root `α` the `(x−α)`-term drops and `Dᵢ'(α) = Dᵢ,α(α)`. -/
theorem eval_derivative_of_X_sub_C_mul {Di Diα : K[X]} {α : K}
    (hfac : Di = (Polynomial.X - Polynomial.C α) * Diα) :
    (derivative Di).eval α = Diα.eval α := by
  subst hfac
  rw [derivative_mul, derivative_sub, derivative_X, Polynomial.derivative_C, sub_zero, one_mul,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_self, zero_mul, add_zero]

/-- **`Eᵢ(α) ≠ 0` ∧ `Dᵢ,α(α) ≠ 0` ⟹ the `hᵢ,α`-denominator is nonzero at `α`**:
`(lDenomα Eᵢ Dᵢ,α i d)(α) = Dᵢ,α(α)^{i+d}·Eᵢ(α)^{d+1} ≠ 0`. -/
theorem eval_lDenomα_ne_zero {Ei Diα : K[X]} {α : K} (i d : ℕ) (hEi : Ei.eval α ≠ 0)
    (hDiα : Diα.eval α ≠ 0) : (lDenomα Ei Diα i d).eval α ≠ 0 := by
  unfold lDenomα
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_pow]
  exact mul_ne_zero (pow_ne_zero _ hDiα) (pow_ne_zero _ hEi)

/-- **Eval of the genuine `hᵢ,α^{(d)}/d!`-fraction at `α`**: when `Eᵢ(α), Dᵢ,α(α) ≠ 0`,
`RatFunc.eval id α (lFracα A Eᵢ Dᵢ,α i d) = σα(Pᵢ,d)(α) / (Dᵢ,α(α)^{i+d}·Eᵢ(α)^{d+1})`, via
`eval_algebraMap_div` (the denominator is pole-free at `α`). -/
theorem eval_lFracα {A Ei Diα : K[X]} {α : K} (i d : ℕ) (hEi : Ei.eval α ≠ 0)
    (hDiα : Diα.eval α ≠ 0) :
    RatFunc.eval (RingHom.id K) α (lFracα A Ei Diα i d)
      = (diffSubst Diα (laurentNum A Ei i d)).eval α / (lDenomα Ei Diα i d).eval α := by
  rw [lFracα, eval_algebraMap_div α _ _ (eval_lDenomα_ne_zero i d hEi hDiα)]

/-- **Eval of a `K`-scaled `hᵢ,α`-fraction at `α`**: `RatFunc.eval id α (c • lFracα A Eᵢ Dᵢ,α i d)
= c · σα(Pᵢ,d)(α)/(Dᵢ,α(α)^{i+d}·Eᵢ(α)^{d+1})` — the scalar `c • _ = C c · _` folds into the numerator
(`algebraMap (C c · num)/algebraMap denom`) and `eval_algebraMap_div` reads it off. -/
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

/-- **(a), Stage I evaluated at the root `α`** (book p.56): for `0 < i`, `Eᵢ(α), Dᵢ,α(α) ≠ 0`, evaluating
the specialized eq 2.11 invariant `iterate_ratFuncKDeriv_hFracα` at `α` gives
`(d/dx)^[d] hᵢ,α (α) = d!·σα(Pᵢ,d)(α)/(Dᵢ,α(α)^{i+d}·Eᵢ(α)^{d+1})`, the value of the order-`d` Taylor data of
the genuine rational function `hᵢ,α = A/(Dᵢ,α^i·Eᵢ)`. `RatFunc.eval id α` is a ring hom away from the (here
nonzero) denominator. -/
theorem eval_ratFuncKDeriv_iterate_hFracα_at_root [CharZero K] {A Ei Diα : K[X]} {α : K} (i : ℕ)
    (hi : 0 < i) (hEi0 : Ei ≠ 0) (hDiα0 : Diα ≠ 0) (hEi : Ei.eval α ≠ 0) (hDiα : Diα.eval α ≠ 0)
    (d : ℕ) :
    RatFunc.eval (RingHom.id K) α ((ratFuncKDeriv^[d]) (hFracα A Ei Diα i))
      = (d.factorial : K) * (diffSubst Diα (laurentNum A Ei i d)).eval α
          / (lDenomα Ei Diα i d).eval α := by
  rw [iterate_ratFuncKDeriv_hFracα A Ei Diα i hi hEi0 hDiα0 d,
    eval_smul_lFracα _ i d hEi hDiα, mul_div_assoc]

/-- **(a) — `Hᵢⱼ(α)` is the order-`(i−j)` Taylor coefficient of `hᵢ,α = (A/D)(x−α)ⁱ`** (§2.7, p.56, the
substantive reachable core of Thm 2.7.1): at a root `α` of the monic `Dᵢ = (x−α)·Dᵢ,α` (with `j ≤ i`,
`Eᵢ(α), Dᵢ,α(α) ≠ 0`, where `Eᵢ = laurentE D Dᵢ i`), the engine output equals
`Hᵢⱼ(α) = (1/(i−j)!)·(d/dx)^[i−j] hᵢ,α (α)` — the order-`(i−j)` Taylor coefficient of the genuine rational
function `hᵢ,α`. Combines `eval_laurentH_eq_diffSubst_laurentNum` (Steps 2+3+5) with Stage I evaluated at
`α` (`eval_ratFuncKDeriv_iterate_hFracα_at_root`) and the cofactor identity `Dᵢ'(α) = Dᵢ,α(α)`
(`eval_derivative_of_X_sub_C_mul`): the `(Dᵢ,α, Eᵢ)`-power denominators cancel the
`(1/Eᵢ(α))^{i−j+1}·(1/Dᵢ'(α))^{2i−j}` factors. Since `hᵢ,α = (A/D)(x−α)ⁱ`, its order-`(i−j)` Taylor
coefficient at `α` is precisely the `1/(x−α)ʲ` partial-fraction (Laurent) coefficient `c_j` of `A/D`. -/
theorem eval_laurentH_eq_taylor_coeff [CharZero K] {A D Di Diα : K[X]} {α : K} (i j : ℕ)
    (hi : 0 < i) (hji : j ≤ i) (hDi : Di.Monic) (hα : Di.eval α = 0)
    (hfac : Di = (Polynomial.X - Polynomial.C α) * Diα)
    (hcopE : IsCoprime (laurentE D Di i) Di) (hcopD : IsCoprime (derivative Di) Di)
    (hEi : (laurentE D Di i).eval α ≠ 0) (hDiα : Diα.eval α ≠ 0) :
    (laurentH A D Di i j).eval α
      = (((i - j).factorial : K))⁻¹
          * RatFunc.eval (RingHom.id K) α
              ((ratFuncKDeriv^[i - j]) (hFracα A (laurentE D Di i) Diα i)) := by
  -- abbreviations
  set Ei := laurentE D Di i with hEidef
  have hEi0 : Ei ≠ 0 := fun h => hEi (by rw [h, Polynomial.eval_zero])
  have hDiα0 : Diα ≠ 0 := fun h => hDiα (by rw [h, Polynomial.eval_zero])
  -- evaluate Stage I at the root
  rw [eval_ratFuncKDeriv_iterate_hFracα_at_root i hi hEi0 hDiα0 hEi hDiα (i - j)]
  -- the engine output, via Steps 2+3+5
  rw [eval_laurentH_eq_diffSubst_laurentNum i j hDi hα hfac hcopE hcopD, ← hEidef]
  -- the `(derivative Di)(α) = Diα(α)` cofactor identity
  rw [eval_derivative_of_X_sub_C_mul hfac]
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
      = (laurentQ A D Di i j * bezoutE D Di i ^ (i - j + 1) * bezoutDeriv Di ^ (2 * i - j)) %ₘ Di :=
  laurentH_def A D Di i j

/-- Restatement of the `i=1` residue (book p.56): `H₁₁(α) = A(α)/D'(α)` at a simple root `α` of `D`. -/
example {A D Di : K[X]} {α : K} (hDi : Di.Monic) (hα : Di.eval α = 0)
    (hfac : D = Di * laurentE D Di 1) (hcopE : IsCoprime (laurentE D Di 1) Di)
    (hcopD : IsCoprime (derivative Di) Di)
    (hE : (laurentE D Di 1).eval α ≠ 0) (hD' : (derivative Di).eval α ≠ 0) :
    (laurentH A D Di 1 1).eval α = A.eval α / (derivative D).eval α :=
  eval_laurentH_one_one_eq_residue hDi hα hfac hcopE hcopD hE hD'

/-- Restatement of (2.11) as a fraction-field invariant (book p.55): the `d`-th `d/dx` of
`hᵢ = A/(uⁱ·Eᵢ)` in `K(x)⟨u⟩` is `d! · Pᵢ,d/(u^(i+d)·Eᵢ^(d+1))` — exactly the book's
`hᵢ^(d)/d! = Pᵢ,d/denom_d` (the scale is the pure factorial `d!`, no `i`-dependent discrepancy). -/
example [CharZero K] (A Ei : K[X]) (i : ℕ) (hi : 0 < i) (hEi : Ei ≠ 0) (d : ℕ) :
    (fracKDeriv^[d]) (hFrac A Ei i) = (d.factorial : K) • lFrac A Ei i d := by
  rw [iterate_fracKDeriv_hFrac A Ei i hi hEi d, laurentScale_eq_factorial]

/-- Regression for the `laurentNumStep` factorial fix (`i=2, d=1`): `laurentNum A E₂ 2 1` is EXACTLY the
book's `P₂,₁ = A'·u·E₂ − A·(2·u'·E₂ + u·E₂')` (numerator of `h₂' = (A/(u²E₂))'`, `1! = 1`, **no** `1/3`
factor). Before the fix `laurentNumStep` divided by `a+1 = i+d+1 = 4`-style scalars and this was off by a
binomial factor; with the factorial divisor `b = d+1 = 1` here, the step contributes no division. -/
example (A E2 : K[X]) :
    laurentNum A E2 2 1
      = ddx (dpEmbed A) * X (some 0) * dpEmbed E2
        - dpEmbed A * ((2 : DiffPoly K) * X (some 1) * dpEmbed E2
                        + (1 : DiffPoly K) * X (some 0) * dpEmbed (derivative E2)) := by
  rw [laurentNum_succ, laurentNum_zero, laurentNumStep]
  norm_num

/-- Restatement of the root-evaluation step (book p.56): at a root `α` of `Dᵢ = (x−α)·Dᵢ,α`,
`Qᵢⱼ(α) = Pᵢⱼ(α, Dᵢ,α(α), Dᵢ,α'(α), …)`. -/
example [CharZero K] (A D Diα : K[X]) (α : K) (i j : ℕ) :
    (laurentQ A D ((Polynomial.X - Polynomial.C α) * Diα) i j).eval α
      = MvPolynomial.aeval (substEvalAt Diα α)
          (laurentNum A (laurentE D ((Polynomial.X - Polynomial.C α) * Diα) i) i (i - j)) :=
  laurentQ_eval_at_root A D Diα α i j

/-- Restatement that `σα` is the differential substitution hom (book p.56, Step 1): it carries the
engine's `ddx` to the genuine `Polynomial.derivative`, `σα (ddx p) = derivative (σα p)`. -/
example (Diα : K[X]) (p : DiffPoly K) :
    diffSubst Diα (ddx p) = derivative (diffSubst Diα p) :=
  diffSubst_ddx Diα p

/-- Restatement of the specialized eq 2.11 invariant in `K(x)` (book p.56, Step 2): the `d`-th genuine
derivative of `hᵢ,α = A/(Dᵢ,α^i·Eᵢ)` is `d!·σα(Pᵢ,d)/(Dᵢ,α^{i+d}·Eᵢ^{d+1})`. -/
example [CharZero K] (A Ei Diα : K[X]) (i : ℕ) (hi : 0 < i) (hEi : Ei ≠ 0) (hDiα : Diα ≠ 0) (d : ℕ) :
    (ratFuncKDeriv^[d]) (hFracα A Ei Diα i)
      = (d.factorial : K) • (algebraMap K[X] (RatFunc K) (diffSubst Diα (laurentNum A Ei i d)) /
          algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i d)) :=
  iterate_ratFuncKDeriv_hFracα A Ei Diα i hi hEi hDiα d

/-- `hᵢ,α = (A/D)·(x−α)ⁱ` (the genuine function the engine differentiates): with `D = Dᵢ^i·Eᵢ` and
`Dᵢ = (x−α)·Dᵢ,α`, the candidate `hFracα = A/(Dᵢ,α^i·Eᵢ)` satisfies `hFracα·algebraMap D = algebraMap(A·(x−α)ⁱ)`,
i.e. `hFracα = (A/D)·(x−α)ⁱ`. (`D = (x−α)ⁱ·Dᵢ,α^i·Eᵢ`, so `(A/D)·(x−α)ⁱ = A/(Dᵢ,α^i·Eᵢ)`.) Shown at `α = 0`
(`x−α = x`): `hFracα·((x·Dᵢ,α)ⁱ·Eᵢ) = A·xⁱ`. -/
example (A Ei Diα : K[X]) (i : ℕ) (hEi : Ei ≠ 0) (hDiα : Diα ≠ 0) :
    hFracα A Ei Diα i * algebraMap K[X] (RatFunc K) (((Polynomial.X - Polynomial.C (0 : K)) * Diα) ^ i * Ei)
      = algebraMap K[X] (RatFunc K) (A * (Polynomial.X - Polynomial.C (0 : K)) ^ i) := by
  rw [hFracα, lDenomα, Nat.add_zero, Nat.zero_add, pow_one, div_mul_eq_mul_div,
    div_eq_iff (RatFunc.algebraMap_ne_zero (mul_ne_zero (pow_ne_zero _ hDiα) hEi)),
    ← map_mul, ← map_mul]
  congr 1
  rw [mul_pow]; ring

/-- Restatement of Step 3, the root-value bridge `σα(Pᵢ,i−j)(α) = Qᵢⱼ(α)` (book p.56). -/
example [CharZero K] (A D Diα : K[X]) (α : K) (i j : ℕ) :
    Polynomial.eval α
        (diffSubst Diα (laurentNum A (laurentE D ((Polynomial.X - Polynomial.C α) * Diα) i) i (i - j)))
      = (laurentQ A D ((Polynomial.X - Polynomial.C α) * Diα) i j).eval α :=
  eval_diffSubst_laurentNum_eq_laurentQ_eval A D Diα α i j

/-- Restatement of Step 5, the general engine-output evaluation
`Hᵢⱼ(α) = Qᵢⱼ(α)·(1/Eᵢ(α))^{i−j+1}·(1/Dᵢ'(α))^{2i−j}` (book p.56, eq 2.12 evaluated). -/
example {A D Di : K[X]} {α : K} (i j : ℕ) (hDi : Di.Monic) (hα : Di.eval α = 0)
    (hcopE : IsCoprime (laurentE D Di i) Di) (hcopD : IsCoprime (derivative Di) Di) :
    (laurentH A D Di i j).eval α
      = (laurentQ A D Di i j).eval α * (1 / (laurentE D Di i).eval α) ^ (i - j + 1)
          * (1 / (derivative Di).eval α) ^ (2 * i - j) :=
  eval_laurentH i j hDi hα hcopE hcopD

/-- Restatement of (a), the cofactor identity at a simple root: `Dᵢ'(α) = Dᵢ,α(α)`. -/
example {Di Diα : K[X]} {α : K} (hfac : Di = (Polynomial.X - Polynomial.C α) * Diα) :
    (derivative Di).eval α = Diα.eval α :=
  eval_derivative_of_X_sub_C_mul hfac

/-- Restatement of (a), Stage I evaluated at the root: `(d/dx)^[d] hᵢ,α (α) =
d!·σα(Pᵢ,d)(α)/(Dᵢ,α(α)^{i+d}·Eᵢ(α)^{d+1})`. -/
example [CharZero K] {A Ei Diα : K[X]} {α : K} (i : ℕ) (hi : 0 < i) (hEi0 : Ei ≠ 0)
    (hDiα0 : Diα ≠ 0) (hEi : Ei.eval α ≠ 0) (hDiα : Diα.eval α ≠ 0) (d : ℕ) :
    RatFunc.eval (RingHom.id K) α ((ratFuncKDeriv^[d]) (hFracα A Ei Diα i))
      = (d.factorial : K) * (diffSubst Diα (laurentNum A Ei i d)).eval α
          / (lDenomα Ei Diα i d).eval α :=
  eval_ratFuncKDeriv_iterate_hFracα_at_root i hi hEi0 hDiα0 hEi hDiα d

/-- **(a) restated** (book p.56): `Hᵢⱼ(α)` is the order-`(i−j)` Taylor coefficient
`(1/(i−j)!)·(d/dx)^[i−j] hᵢ,α (α)` of the genuine rational function `hᵢ,α = (A/D)(x−α)ⁱ` at `α`. -/
example [CharZero K] {A D Di Diα : K[X]} {α : K} (i j : ℕ) (hi : 0 < i) (hji : j ≤ i)
    (hDi : Di.Monic) (hα : Di.eval α = 0) (hfac : Di = (Polynomial.X - Polynomial.C α) * Diα)
    (hcopE : IsCoprime (laurentE D Di i) Di) (hcopD : IsCoprime (derivative Di) Di)
    (hEi : (laurentE D Di i).eval α ≠ 0) (hDiα : Diα.eval α ≠ 0) :
    (laurentH A D Di i j).eval α
      = (((i - j).factorial : K))⁻¹
          * RatFunc.eval (RingHom.id K) α
              ((ratFuncKDeriv^[i - j]) (hFracα A (laurentE D Di i) Diα i)) :=
  eval_laurentH_eq_taylor_coeff i j hi hji hDi hα hfac hcopE hcopD hEi hDiα

/-- **The `i=j=1` instance of (a)** (book p.56): at a simple root, the order-`0` Taylor coefficient is the
function value `hᵢ,α(α)`, so `eval_laurentH_eq_taylor_coeff` specializes to `H₁₁(α) = h₁,α(α)` — the
`(d/dx)^[0]`-Taylor data, consistent with the residue `eval_laurentH_one_one_eq_residue`. Here `i−j = 0`,
`(0)! = 1`, and `(ratFuncKDeriv^[0]) (hFracα …) = hFracα …`. -/
example [CharZero K] {A D Di Diα : K[X]} {α : K} (hDi : Di.Monic) (hα : Di.eval α = 0)
    (hfac : Di = (Polynomial.X - Polynomial.C α) * Diα)
    (hcopE : IsCoprime (laurentE D Di 1) Di) (hcopD : IsCoprime (derivative Di) Di)
    (hEi : (laurentE D Di 1).eval α ≠ 0) (hDiα : Diα.eval α ≠ 0) :
    (laurentH A D Di 1 1).eval α
      = RatFunc.eval (RingHom.id K) α (hFracα A (laurentE D Di 1) Diα 1) := by
  have h := eval_laurentH_eq_taylor_coeff (A := A) (D := D) (Di := Di) (Diα := Diα) (α := α) 1 1
    one_pos le_rfl hDi hα hfac hcopE hcopD hEi hDiα
  simpa using h

/-! ## Stage L — the closure-level book conclusion: principal parts and "proper, pole-free ⟹ regular"
(Bronstein §2.7, Theorem 2.7.1, the partial-fraction assembly over `K̄`)

The final book conclusion `A/D = P + ∑ᵢ ∑_{α|Dᵢ(α)=0} ∑_{j=1}^{i} Hᵢⱼ(α)/(x−α)ʲ` is the statement that,
at each pole `α` of `A/D` (a root of `Dᵢ`, of order `i`), the engine sum `∑_{j=1}^{i} Hᵢⱼ(α)/(x−α)ʲ` is
exactly the **principal part** of `A/D` at `α`: subtracting it removes the pole.

The structural core proved here is **regularity**: writing `D = (X−α)^i·M` with `M = Dᵢ,α^i·Eᵢ` pole-free at
`α` (`M(α) ≠ 0`), the **local Taylor approximant** `W := (A·N) %ₘ (X−α)^i` — `N` the Bézout inverse of `M`
modulo `(X−α)^i` (`localInverse`) — satisfies `M·W ≡ A (mod (X−α)^i)` (`localApprox_spec`), so its `(X−α)`-adic
digits `c_d = (taylor α W).coeff d` give a principal part `∑_{j=1}^{i} C(c_{i−j})/(X−α)^j` whose subtraction
from `A/D` leaves a quotient `R/M` regular at `α` (`subtract_localPrincipalPart_eq`,
`localPrincipalPart_regular`). The digits `c_{i−j}` ARE the `1/(x−α)ʲ` Laurent coefficients; identifying them
with the engine output `Hᵢⱼ(α)` is `eval_laurentH_eq_taylor_coeff` up to the Hasse-derivative/`ratFuncKDeriv`
bridge (`taylorCoeff_localApprox_eq_ratFuncTaylor`, the residual naming step). -/

/-- **The local inverse `N` of `M` modulo `(X−α)^i`** (§2.7, the principal-part assembly): the Bézout
cofactor with `M·N ≡ 1 (mod (X−α)^i)`, existing since `M(α) ≠ 0` makes `M` coprime to `(X−α)^i`. -/
noncomputable def localInverse (M : K[X]) (α : K) (i : ℕ) : K[X] :=
  (diophantineSolve M ((Polynomial.X - Polynomial.C α) ^ i) 1).1

/-- **`(X−α)^i` is coprime to `M`** when `M(α) ≠ 0`: `X − α` is prime and does not divide `M` (it would
force `M(α) = 0`), so its power is coprime to `M`. -/
theorem isCoprime_M_X_sub_C_pow {M : K[X]} {α : K} (i : ℕ) (hM : M.eval α ≠ 0) :
    IsCoprime M ((Polynomial.X - Polynomial.C α) ^ i) := by
  have hnd : ¬ (Polynomial.X - Polynomial.C α) ∣ M := by
    rw [dvd_iff_isRoot]; exact fun h => hM h
  exact (((prime_X_sub_C α).coprime_iff_not_dvd.mpr hnd).symm).pow_right

/-- **`M·N ≡ 1 (mod (X−α)^i)`** (the local-inverse congruence): for `M(α) ≠ 0`, the Bézout cofactor
`localInverse M α i` inverts `M` modulo `(X−α)^i`, `(X−α)^i ∣ M·N − 1`. -/
theorem localInverse_spec {M : K[X]} {α : K} (i : ℕ) (hM : M.eval α ≠ 0) :
    (Polynomial.X - Polynomial.C α) ^ i ∣ M * localInverse M α i - 1 := by
  have hspec := diophantineSolve_spec (isCoprime_M_X_sub_C_pow i hM) (1 : K[X])
  refine ⟨-(diophantineSolve M ((Polynomial.X - Polynomial.C α) ^ i) 1).2, ?_⟩
  rw [localInverse]; linear_combination hspec

/-- **The local Taylor approximant `W := (A·N) %ₘ (X−α)^i`** (§2.7): the degree-`< i` polynomial whose
`(X−α)`-adic digits are the principal-part Laurent coefficients of `A/D` at the pole `α`. With `N` the
local inverse of `M = D /ₘ (X−α)^i`, it satisfies `M·W ≡ A (mod (X−α)^i)`. -/
noncomputable def localApprox (A M : K[X]) (α : K) (i : ℕ) : K[X] :=
  (A * localInverse M α i) %ₘ (Polynomial.X - Polynomial.C α) ^ i

/-- **`M·W ≡ A (mod (X−α)^i)`** (§2.7, the defining congruence of the local approximant): `(X−α)^i` divides
`A − M·W`. From `M·N ≡ 1` and `W = A·N %ₘ (X−α)^i` (so `A·N ≡ W`), `M·W ≡ M·A·N ≡ A`. -/
theorem localApprox_spec (A M : K[X]) {α : K} (i : ℕ) (hM : M.eval α ≠ 0) :
    (Polynomial.X - Polynomial.C α) ^ i ∣ A - M * localApprox A M α i := by
  set g := (Polynomial.X - Polynomial.C α) ^ i with hg
  have hmonic : g.Monic := (monic_X_sub_C α).pow i
  -- `A·N ≡ W (mod g)` from the definition of `W = (A·N) %ₘ g`
  have hAN : g ∣ A * localInverse M α i - localApprox A M α i := by
    have hid : A * localInverse M α i - localApprox A M α i
        = g * ((A * localInverse M α i) /ₘ g) := by
      rw [localApprox, eq_comm, ← sub_eq_iff_eq_add'.mpr (modByMonic_add_div (A * localInverse M α i) g).symm]
    rw [hid]; exact Dvd.intro _ rfl
  -- `M·N ≡ 1 (mod g)`
  have hMN : g ∣ M * localInverse M α i - 1 := localInverse_spec i hM
  -- combine: `A − M·W = A·(1 − M·N) + M·(A·N − W)`
  have hcomb : A - M * localApprox A M α i
      = A * (-(M * localInverse M α i - 1)) + M * (A * localInverse M α i - localApprox A M α i) := by
    ring
  rw [hcomb]
  exact dvd_add (Dvd.dvd.mul_left ((dvd_neg).mpr hMN) A) (Dvd.dvd.mul_left hAN M)

/-- **The Laurent coefficient `c_d`** (§2.7): the order-`d` `(X−α)`-adic digit of the local approximant `W`,
`c_d = (taylor α W).coeff d` — the `1/(x−α)^{i−d}` partial-fraction coefficient of `A/D` at the pole `α`. -/
noncomputable def localCoeff (A M : K[X]) (α : K) (i d : ℕ) : K :=
  (taylor α (localApprox A M α i)).coeff d

/-- **The `(X−α)`-adic reconstruction of `W`** (§2.7): for `deg W < i` (`W = localApprox …`, a remainder
mod `(X−α)^i`), the local approximant reconstructs from its first `i` Taylor digits,
`W = ∑_{d<i} c_d·(X−α)^d` (`c_d = localCoeff …`) — the Taylor expansion of `W` about `α`, truncated by its
degree. -/
theorem localApprox_eq_sum (A M : K[X]) (α : K) (i : ℕ) :
    localApprox A M α i
      = ∑ d ∈ Finset.range i, Polynomial.C (localCoeff A M α i d)
          * (Polynomial.X - Polynomial.C α) ^ d := by
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · -- `i = 0`: `(X−α)^0 = 1`, so `W = (A·N) %ₘ 1 = 0`, and `range 0` is empty
    subst hi0
    simp only [Finset.range_zero, Finset.sum_empty, localApprox, pow_zero, modByMonic_one]
  set W := localApprox A M α i with hW
  have hmonic : ((Polynomial.X - Polynomial.C α) ^ i).Monic := (monic_X_sub_C α).pow i
  -- `Taylor's formula`: `W = (taylor α W).sum (fun d a => C a · (X−α)^d)`
  have htay : W = (taylor α W).sum (fun d a => Polynomial.C a * (Polynomial.X - Polynomial.C α) ^ d) :=
    (sum_taylor_eq W α).symm
  -- the natDegree of `(X−α)^i` is `i`
  have hpowdeg : ((Polynomial.X - Polynomial.C α) ^ i).natDegree = i := by
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  -- truncate the `Polynomial.sum` to `range i` via `natDegree (taylor α W) = natDegree W < i`
  have hdeg : (taylor α W).natDegree < i := by
    rw [natDegree_taylor]
    rcases eq_or_ne W 0 with h0 | h0
    · rw [h0, natDegree_zero]; exact hipos
    · have hlt := degree_modByMonic_lt (A * localInverse M α i) hmonic
      have hdW : W.natDegree < ((Polynomial.X - Polynomial.C α) ^ i).natDegree :=
        natDegree_lt_natDegree h0 (by rw [hW, localApprox]; exact hlt)
      rwa [hpowdeg] at hdW
  rw [htay, Polynomial.sum_over_range' _ (fun d => by simp) i hdeg]
  rfl

/-- **The principal part of `A/D` at the pole `α`** (§2.7, Theorem 2.7.1, the closure form): the sum
`∑_{j=1}^{i} c_{i−j}/(x−α)ʲ` of the `1/(x−α)ʲ` Laurent terms, with `c_d = localCoeff …` the `(X−α)`-adic
digits of the local approximant `W`. Subtracting it from `A/D` removes the order-`i` pole at `α`
(`subtract_localPrincipalPart_eq`). With `D = (X−α)^i·M`, `M(α) ≠ 0`. -/
noncomputable def localPrincipalPart (A M : K[X]) (α : K) (i : ℕ) : RatFunc K :=
  ∑ j ∈ Finset.Icc 1 i,
    algebraMap K[X] (RatFunc K) (Polynomial.C (localCoeff A M α i (i - j)))
      / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ j

/-- **The principal part consolidated over the common denominator `(X−α)^i`** (§2.7): the Laurent sum
`∑_{j=1}^{i} c_{i−j}/(x−α)ʲ` equals `W/(x−α)^i` for the local approximant `W = ∑_{d<i} c_d·(x−α)^d`
(`localApprox`), by clearing each term to the common power `i` and reindexing `d = i−j`. -/
theorem localPrincipalPart_eq_div (A M : K[X]) (α : K) (i : ℕ) :
    localPrincipalPart A M α i
      = algebraMap K[X] (RatFunc K) (localApprox A M α i)
          / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ i := by
  have hX0 : (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (X_sub_C_ne_zero α)
  rw [localApprox_eq_sum A M α i, map_sum, Finset.sum_div, localPrincipalPart]
  -- reindex `Finset.Icc 1 i` (power `j`) to `Finset.range i` (digit `d = i − j`)
  refine Finset.sum_nbij' (fun j => i - j) (fun d => i - d) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_Icc] at hj; simp only [Finset.mem_range]; omega
  · intro d hd; simp only [Finset.mem_range] at hd; simp only [Finset.mem_Icc]; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj; omega
  · intro d hd; simp only [Finset.mem_range] at hd; omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    -- the `j`-th Laurent term `c_{i−j}/(x−α)^j` equals `c_{i−j}·(x−α)^{i−j}/(x−α)^i` (`d = i−j`)
    have hpow : (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ (i - j)
        * (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ j
        = (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ i := by
      rw [← pow_add]; congr 1; omega
    rw [map_mul, map_pow, div_eq_div_iff (pow_ne_zero _ hX0) (pow_ne_zero _ hX0), mul_assoc, hpow]

/-- **The regular remainder `R = (A − M·W) /ₘ (X−α)^i`** (§2.7): the polynomial left after subtracting the
principal part, `A/D − PP = R/M`. By `localApprox_spec`, `(X−α)^i ∣ A − M·W`, so `R` is a genuine
polynomial; `R/M` is regular at `α` since `M(α) ≠ 0`. -/
noncomputable def localRemainder (A M : K[X]) (α : K) (i : ℕ) : K[X] :=
  (A - M * localApprox A M α i) /ₘ (Polynomial.X - Polynomial.C α) ^ i

/-- **`A − M·W = (X−α)^i·R`** (§2.7): the exact factorization of the principal-part numerator, from the
divisibility `localApprox_spec` and the monic division reconstruction. -/
theorem localRemainder_spec (A M : K[X]) {α : K} (i : ℕ) (hM : M.eval α ≠ 0) :
    A - M * localApprox A M α i
      = (Polynomial.X - Polynomial.C α) ^ i * localRemainder A M α i := by
  have hmonic : ((Polynomial.X - Polynomial.C α) ^ i).Monic := (monic_X_sub_C α).pow i
  conv_lhs => rw [← modByMonic_add_div (A - M * localApprox A M α i)
    ((Polynomial.X - Polynomial.C α) ^ i)]
  rw [(modByMonic_eq_zero_iff_dvd hmonic).2 (localApprox_spec A M i hM), zero_add, localRemainder]

/-- **Theorem 2.7.1, subtracting the principal part removes the pole** (§2.7, p.56, the closure-level
assembly): for `D = (X−α)^i·M` with `M(α) ≠ 0` (so `α` is a pole of `A/D` of order `≤ i`), subtracting the
engine's Laurent sum `∑_{j=1}^{i} c_{i−j}/(x−α)ʲ` (`localPrincipalPart`) leaves `R/M`, regular at `α`:
`A/D − ∑_{j=1}^{i} c_{i−j}/(x−α)ʲ = R/M`, `R = localRemainder …`, `M(α) ≠ 0`. This is the partial-fraction
core — the principal part `∑_j c_{i−j}/(x−α)ʲ` is exactly the singular part of `A/D` at `α`. The Laurent
coefficients `c_{i−j} = localCoeff A M α i (i−j)` are the engine outputs `Hᵢⱼ(α)` (the order-`(i−j)` Taylor
coefficients of `hᵢ,α`, `eval_laurentH_eq_taylor_coeff`, up to the Hasse-derivative bridge). -/
theorem subtract_localPrincipalPart_eq (A M : K[X]) {α : K} (i : ℕ) (hM : M.eval α ≠ 0) :
    algebraMap K[X] (RatFunc K) A
        / (algebraMap K[X] (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ i * M))
      - localPrincipalPart A M α i
      = algebraMap K[X] (RatFunc K) (localRemainder A M α i)
          / algebraMap K[X] (RatFunc K) M := by
  set X' := algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α) with hX'
  have hX0 : X' ≠ 0 := (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (X_sub_C_ne_zero α)
  have hM0 : algebraMap K[X] (RatFunc K) M ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (fun h => hM (by rw [h, Polynomial.eval_zero]))
  rw [localPrincipalPart_eq_div]
  -- common denominator `(X−α)^i · M`; the numerator is `A − M·W = (X−α)^i·R`
  rw [map_mul, map_pow, ← hX']
  rw [div_sub_div _ _ (mul_ne_zero (pow_ne_zero i hX0) hM0) (pow_ne_zero i hX0)]
  rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero (pow_ne_zero i hX0) hM0) (pow_ne_zero i hX0)) hM0]
  -- clear denominators and use `A − M·W = (X−α)^i·R` (the spec, mapped through `algebraMap`)
  have hspec : algebraMap K[X] (RatFunc K) A - algebraMap K[X] (RatFunc K) M
        * algebraMap K[X] (RatFunc K) (localApprox A M α i)
      = X' ^ i * algebraMap K[X] (RatFunc K) (localRemainder A M α i) := by
    have h := localRemainder_spec A M i hM
    have := congrArg (algebraMap K[X] (RatFunc K)) h
    rwa [map_sub, map_mul, map_mul, map_pow, ← hX'] at this
  -- the goal is a polynomial identity; `linear_combination` with `hspec` (times the leftover factor)
  linear_combination (X' ^ i * algebraMap K[X] (RatFunc K) M) * hspec

/-- **Theorem 2.7.1, the principal part is exactly the singular part** (§2.7, p.56, the closure-level
conclusion, existence form): for `D = (X−α)^i·M` with `M(α) ≠ 0`, there is a polynomial `R` and a
denominator `M` pole-free at `α` (`M(α) ≠ 0`) with
`A/D − ∑_{j=1}^{i} c_{i−j}/(x−α)ʲ = R/M`, i.e. subtracting the engine's Laurent sum at `α` leaves a
rational function **regular at `α`** (no pole). This is the assertion that the book's per-root sum
`∑_{j=1}^{i} Hᵢⱼ(α)/(x−α)ʲ` is the principal part of `A/D` at the pole `α`; summing over all poles `α` of
`D` and adding the polynomial part `P = A /ₘ D` recovers `A/D` (the full partial-fraction theorem). -/
theorem exists_regular_sub_localPrincipalPart (A M : K[X]) {α : K} (i : ℕ) (hM : M.eval α ≠ 0) :
    ∃ (R N : K[X]), N.eval α ≠ 0 ∧
      algebraMap K[X] (RatFunc K) A
          / (algebraMap K[X] (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ i * M))
        - localPrincipalPart A M α i
        = algebraMap K[X] (RatFunc K) R / algebraMap K[X] (RatFunc K) N :=
  ⟨localRemainder A M α i, M, hM, subtract_localPrincipalPart_eq A M i hM⟩

/-- Restatement of `M·W ≡ A (mod (X−α)^i)` (the local approximant agrees with `A/D·(X−α)^i` to order `i`):
`(X−α)^i ∣ A − M·W`. -/
example (A M : K[X]) {α : K} (i : ℕ) (hM : M.eval α ≠ 0) :
    (Polynomial.X - Polynomial.C α) ^ i ∣ A - M * localApprox A M α i :=
  localApprox_spec A M i hM

/-- Restatement of the closure-level partial-fraction core (book p.56): with `D = (X−α)^i·M`, `M(α) ≠ 0`,
subtracting the engine's per-root Laurent sum `∑_{j=1}^{i} c_{i−j}/(x−α)ʲ` (`localPrincipalPart`) from
`A/D` leaves `R/M`, regular at `α` — i.e. that sum is exactly the principal part of `A/D` at the pole `α`. -/
example (A M : K[X]) {α : K} (i : ℕ) (hM : M.eval α ≠ 0) :
    algebraMap K[X] (RatFunc K) A
        / (algebraMap K[X] (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ i * M))
      - localPrincipalPart A M α i
      = algebraMap K[X] (RatFunc K) (localRemainder A M α i)
          / algebraMap K[X] (RatFunc K) M :=
  subtract_localPrincipalPart_eq A M i hM

/-! ## Stage M — the coefficient bridge `localCoeff = (1/d!)·(d/dx)^[d](A/M)(α)` (P2, the
Hasse-derivative ↔ differential-engine identification, Bronstein §2.7)

The Stage L Laurent coefficient `localCoeff A M α i d = (taylor α W).coeff d` (a `(X−α)`-adic digit of the
local approximant `W = (A·N) %ₘ (X−α)^i`) is identified here with the differential-engine Taylor
coefficient `(1/d!)·(d/dx)^[d] hᵢ,α (α)`, where `hᵢ,α = A/M = (A/D)(x−α)ⁱ` (since `D = (x−α)ⁱ·M`). Two
ingredients:

* **the Hasse-derivative bridge** (`eval_iterate_ratFuncKDeriv_algebraMap_eq_localCoeff`): the genuine
  `(d/dx)^[d]` of the embedded polynomial `W`, evaluated at `α`, is `d!·localCoeff` — via
  `ratFuncKDeriv (algebraMap p) = algebraMap (derivative p)` iterated, then
  `derivative^[d] W = d!·hasseDeriv d W` (`Polynomial.factorial_smul_hasseDeriv`) and
  `(taylor α W).coeff d = (hasseDeriv d W).eval α` (`Polynomial.taylor_coeff`);
* **high-order vanishing** (`eval_iterate_ratFuncKDeriv_X_sub_C_pow_dvd`): `A/M − W = (x−α)ⁱ·(R/M)`
  (`localRemainder_spec`), and `(d/dx)^[d]` of a function whose numerator is divisible by `(x−α)ⁱ` still
  has a positive `(x−α)`-power in the numerator when `d < i`, so it vanishes at `α`.

Combining, `(d/dx)^[d](A/M)(α) = (d/dx)^[d](W)(α) + 0 = d!·localCoeff`, i.e.
`localCoeff = (1/d!)·(d/dx)^[d](A/M)(α) = Hᵢ,(i−d)(α)` (the engine Taylor coefficient,
`eval_laurentH_eq_taylor_coeff`). -/

/-- **`(d/dx)^[d]` carries an embedded polynomial to its iterated derivative**: `(ratFuncKDeriv^[d])`
applied to `algebraMap p` is `algebraMap (derivative^[d] p)`, by iterating `ratFuncDeriv_algebraMap`. -/
theorem iterate_ratFuncKDeriv_algebraMap (p : K[X]) (d : ℕ) :
    (ratFuncKDeriv^[d]) (algebraMap K[X] (RatFunc K) p)
      = algebraMap K[X] (RatFunc K) (derivative^[d] p) := by
  induction d generalizing p with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      show ratFuncKDeriv (algebraMap K[X] (RatFunc K) p) = algebraMap K[X] (RatFunc K) (derivative p)
        from ratFuncDeriv_algebraMap p, ih]

/-- **Eval of `(d/dx)^[d] W` at `α` is `(derivative^[d] W)(α)`** for an embedded polynomial `W`: the
`(d/dx)^[d]` of `algebraMap W` is the embedded `derivative^[d] W`, whose `RatFunc.eval id α` reads off the
polynomial value (denominator `1`, `eval_algebraMap_div`). -/
theorem eval_iterate_ratFuncKDeriv_algebraMap (W : K[X]) (α : K) (d : ℕ) :
    RatFunc.eval (RingHom.id K) α ((ratFuncKDeriv^[d]) (algebraMap K[X] (RatFunc K) W))
      = (derivative^[d] W).eval α := by
  rw [iterate_ratFuncKDeriv_algebraMap]
  have h := eval_algebraMap_div α (derivative^[d] W) 1 (by simp)
  rwa [map_one, div_one, Polynomial.eval_one, div_one] at h

/-- **`(derivative^[d] W)(α) = d!·(taylor α W).coeff d`** (the Hasse-derivative identity): the genuine
`d`-th derivative value at `α` is `d!` times the order-`d` `(X−α)`-adic digit, from
`Polynomial.factorial_smul_hasseDeriv` (`d! • hasseDeriv d = derivative^[d]`) and `Polynomial.taylor_coeff`
(`(taylor α W).coeff d = (hasseDeriv d W).eval α`). -/
theorem eval_iterate_derivative_eq_factorial_taylor_coeff (W : K[X]) (α : K) (d : ℕ) :
    (derivative^[d] W).eval α = (d.factorial : K) * (taylor α W).coeff d := by
  have hhasse : derivative^[d] W = d.factorial • hasseDeriv d W := by
    have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := K) (k := d)) W
    simpa using h.symm
  rw [hhasse, Polynomial.taylor_coeff, Polynomial.eval_smul, nsmul_eq_mul]

/-- **The Hasse-derivative bridge**: the genuine `(d/dx)^[d]` of the embedded local approximant `W`,
evaluated at `α`, is `d!·localCoeff A M α i d` — identifying the engine's iterated-derivative Taylor data
with the Stage L `(X−α)`-adic digit `c_d = (taylor α W).coeff d`. -/
theorem eval_iterate_ratFuncKDeriv_algebraMap_eq_localCoeff (A M : K[X]) (α : K) (i d : ℕ) :
    RatFunc.eval (RingHom.id K) α
        ((ratFuncKDeriv^[d]) (algebraMap K[X] (RatFunc K) (localApprox A M α i)))
      = (d.factorial : K) * localCoeff A M α i d := by
  rw [eval_iterate_ratFuncKDeriv_algebraMap, eval_iterate_derivative_eq_factorial_taylor_coeff,
    localCoeff]

/-- **High-order vanishing of `(d/dx)^[d]` of a numerator divisible by `(X−α)^i`** (the clean induction): for
`d ≤ i`, `M(α) ≠ 0`, and `(X−α)^i ∣ p`, the `(d/dx)^[d]` of `p/M` (in `K(x)`) has the shape
`P_d / Q_d` with `Q_d(α) ≠ 0` and `(X−α)^(i−d) ∣ P_d` — the iterated quotient rule preserves a `(X−α)^(i−d)`
numerator factor (each derivative drops the power by `1`, `pow_sub_one_dvd_derivative_of_pow_dvd`) and keeps
the denominator pole-free at `α`. -/
theorem exists_iterate_ratFuncKDeriv_div (p M : K[X]) {α : K} (i : ℕ) (hM : M.eval α ≠ 0)
    (hdvd : (Polynomial.X - Polynomial.C α) ^ i ∣ p) :
    ∀ d, d ≤ i → ∃ (Pd Qd : K[X]), Qd.eval α ≠ 0 ∧ (Polynomial.X - Polynomial.C α) ^ (i - d) ∣ Pd ∧
      (ratFuncKDeriv^[d]) (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) M)
        = algebraMap K[X] (RatFunc K) Pd / algebraMap K[X] (RatFunc K) Qd := by
  intro d
  induction d with
  | zero =>
    intro _
    exact ⟨p, M, hM, by simpa using hdvd, by rw [Function.iterate_zero_apply]⟩
  | succ n ih =>
    intro hsucc
    obtain ⟨Pn, Qn, hQn, hdvdn, heqn⟩ := ih (Nat.le_of_succ_le hsucc)
    -- the quotient rule for `Pn/Qn` gives numerator `Pn'·Qn − Pn·Qn'`, denominator `Qn²`
    refine ⟨derivative Pn * Qn - Pn * derivative Qn, Qn ^ 2, ?_, ?_, ?_⟩
    · rw [Polynomial.eval_pow]; exact pow_ne_zero 2 hQn
    · -- `(X−α)^(i−n) ∣ Pn`, so `(X−α)^(i−n−1) ∣ Pn'` and `(X−α)^(i−n) ∣ Pn·Qn'`
      have hd1 : (Polynomial.X - Polynomial.C α) ^ (i - n - 1) ∣ derivative Pn :=
        pow_sub_one_dvd_derivative_of_pow_dvd hdvdn
      have hd2 : (Polynomial.X - Polynomial.C α) ^ (i - n - 1) ∣ Pn :=
        dvd_trans (pow_dvd_pow _ (by omega)) hdvdn
      rw [show i - (n + 1) = i - n - 1 from by omega]
      exact dvd_sub (Dvd.dvd.mul_right hd1 Qn) (Dvd.dvd.mul_right hd2 (derivative Qn))
    · rw [Function.iterate_succ_apply', heqn]
      have hQn0 : algebraMap K[X] (RatFunc K) Qn ≠ 0 :=
        (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
          (fun h => hQn (by rw [h, Polynomial.eval_zero]))
      rw [Derivation.leibniz_div,
        show ratFuncKDeriv (algebraMap K[X] (RatFunc K) Pn) = algebraMap K[X] (RatFunc K) (derivative Pn)
          from ratFuncDeriv_algebraMap Pn,
        show ratFuncKDeriv (algebraMap K[X] (RatFunc K) Qn) = algebraMap K[X] (RatFunc K) (derivative Qn)
          from ratFuncDeriv_algebraMap Qn]
      -- expand the quotient rule (in `•` form) and push through `algebraMap`
      rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, map_sub, map_mul, map_mul, map_pow]
      rw [inv_pow, ← div_eq_inv_mul, div_eq_div_iff (pow_ne_zero 2 hQn0) (pow_ne_zero 2 hQn0)]
      ring

/-- **The order-`d` derivative of a `(X−α)^i`-divisible quotient vanishes at `α`** (`d < i`): evaluating the
shape `P_d/Q_d` of `exists_iterate_ratFuncKDeriv_div` at `α`, the surviving `(X−α)^(i−d)` numerator factor
(positive power since `d < i`) is zero at `α`, so `(d/dx)^[d](p/M)(α) = 0`. -/
theorem eval_iterate_ratFuncKDeriv_div_eq_zero (p M : K[X]) {α : K} (i d : ℕ) (hM : M.eval α ≠ 0)
    (hdvd : (Polynomial.X - Polynomial.C α) ^ i ∣ p) (hd : d < i) :
    RatFunc.eval (RingHom.id K) α
        ((ratFuncKDeriv^[d]) (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) M)) = 0 := by
  obtain ⟨Pd, Qd, hQd, hdvdd, heqd⟩ :=
    exists_iterate_ratFuncKDeriv_div p M i hM hdvd d (Nat.le_of_lt hd)
  rw [heqd, eval_algebraMap_div α Pd Qd hQd]
  -- the numerator `Pd` is divisible by `(X−α)^(i−d)`, a positive power, hence has root `α`
  obtain ⟨s, hs⟩ := hdvdd
  have hPd0 : Pd.eval α = 0 := by
    rw [hs, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_self, zero_pow (by omega), zero_mul]
  rw [hPd0, zero_div]

/-- **`A/M − W = (A − M·W)/M`** in `K(x)`: the local approximant `W` (embedded) subtracted from `A/M` clears
to the single quotient `(A − M·W)/M`, whose numerator `A − M·W` is divisible by `(X−α)^i`
(`localApprox_spec`). -/
theorem hFrac_sub_localApprox (A M : K[X]) (α : K) (i : ℕ) (hM : M.eval α ≠ 0) :
    algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) M
        - algebraMap K[X] (RatFunc K) (localApprox A M α i)
      = algebraMap K[X] (RatFunc K) (A - M * localApprox A M α i)
          / algebraMap K[X] (RatFunc K) M := by
  have hM0 : algebraMap K[X] (RatFunc K) M ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (fun h => hM (by rw [h, Polynomial.eval_zero]))
  rw [map_sub, map_mul]
  field_simp

/-! ## Stage M (cont.) — P2: `localCoeff A M α i d = (1/d!)·(d/dx)^[d](A/M)(α) = Hᵢ,(i−d)(α)`

`hᵢ,α = A/M` (since `A/D·(x−α)ⁱ = A·(x−α)ⁱ/((x−α)ⁱ·M) = A/M`). Splitting
`(d/dx)^[d](A/M) = (d/dx)^[d] W + (d/dx)^[d](A/M − W)` and evaluating at `α`: the first term is
`d!·localCoeff` (Hasse bridge `eval_iterate_ratFuncKDeriv_algebraMap_eq_localCoeff`), the second vanishes for
`d < i` (`eval_iterate_ratFuncKDeriv_div_eq_zero`, since `A/M − W = (A − M·W)/M` with `(x−α)ⁱ ∣ A − M·W`).
So `(d/dx)^[d](A/M)(α) = d!·localCoeff`, i.e. `localCoeff = (1/d!)·(d/dx)^[d](A/M)(α)`. -/

/-- **`(d/dx)^[d]` is additive** (the iterated derivation respects sums): `(ratFuncKDeriv^[d])(x + y)
= (ratFuncKDeriv^[d]) x + (ratFuncKDeriv^[d]) y`, by `Derivation.map_add` iterated. Used to split
`A/M = W + (A/M − W)`. -/
theorem iterate_ratFuncKDeriv_add (x y : RatFunc K) (d : ℕ) :
    (ratFuncKDeriv^[d]) (x + y) = (ratFuncKDeriv^[d]) x + (ratFuncKDeriv^[d]) y := by
  induction d generalizing x y with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      map_add, ih]

/-- **P2 — the coefficient bridge `localCoeff = (1/d!)·(d/dx)^[d](A/M)(α)`** (Bronstein §2.7, the
Hasse-derivative ↔ differential-engine identification): for `D = (x−α)ⁱ·M` with `M(α) ≠ 0` and `d < i`, the
Stage L `(X−α)`-adic Laurent digit `localCoeff A M α i d = (taylor α W).coeff d` equals the order-`d` Taylor
coefficient of the genuine function `hᵢ,α = A/M` (`= (A/D)(x−α)ⁱ`),
`localCoeff = (1/d!)·(d/dx)^[d](A/M)(α)`. Proof: split `A/M = W + (A/M − W)`, push `(d/dx)^[d]` through the
sum (`iterate_ratFuncKDeriv_add`) — the embedded-`W` term is `algebraMap (derivative^[d] W)`
(`iterate_ratFuncKDeriv_algebraMap`), the remainder term `(A/M − W) = (A − M·W)/M` (numerator divisible by
`(x−α)ⁱ`) is `algebraMap Pd / algebraMap Qd` with `Pd(α) = 0`, `Qd(α) ≠ 0` (`exists_iterate_ratFuncKDeriv_div`,
`d < i` keeps a positive `(x−α)`-power). Combining over the common denominator `Qd` and evaluating,
`(d/dx)^[d](A/M)(α) = (derivative^[d] W)(α) = d!·localCoeff` (Hasse identity
`eval_iterate_derivative_eq_factorial_taylor_coeff`). This identifies the Stage L principal-part digit with
the engine Taylor coefficient `Hᵢ,(i−d)(α)` (the order-`d = (i − j)` data of `eval_laurentH_eq_taylor_coeff`). -/
theorem localCoeff_eq_taylor_coeff [CharZero K] (A M : K[X]) {α : K} (i d : ℕ) (hM : M.eval α ≠ 0)
    (hd : d < i) :
    localCoeff A M α i d
      = (((d.factorial : K))⁻¹)
          * RatFunc.eval (RingHom.id K) α
              ((ratFuncKDeriv^[d])
                (algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) M)) := by
  set W := localApprox A M α i with hWdef
  -- the remainder `(A/M − W) = (A − M·W)/M` has the explicit `Pd/Qd` shape, `(x−α)`-divisible numerator
  obtain ⟨Pd, Qd, hQd, hdvdd, heqd⟩ :=
    exists_iterate_ratFuncKDeriv_div (A - M * W) M i hM (localApprox_spec A M i hM) d
      (Nat.le_of_lt hd)
  have hPd0 : Pd.eval α = 0 := by
    obtain ⟨s, hs⟩ := hdvdd
    rw [hs, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_self, zero_pow (by omega), zero_mul]
  -- split `A/M = W + (A/M − W)` and push `(d/dx)^[d]` through the sum
  have hsplit : algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) M
      = algebraMap K[X] (RatFunc K) W
        + (algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) M
            - algebraMap K[X] (RatFunc K) W) := by ring
  rw [hsplit, iterate_ratFuncKDeriv_add, iterate_ratFuncKDeriv_algebraMap,
    hFrac_sub_localApprox A M α i hM, ← hWdef, heqd]
  -- combine the two summands over the common denominator `Qd`
  have hQd0 : algebraMap K[X] (RatFunc K) Qd ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (fun h => hQd (by rw [h, Polynomial.eval_zero]))
  have hcomb : algebraMap K[X] (RatFunc K) (derivative^[d] W)
        + algebraMap K[X] (RatFunc K) Pd / algebraMap K[X] (RatFunc K) Qd
      = algebraMap K[X] (RatFunc K) (derivative^[d] W * Qd + Pd) / algebraMap K[X] (RatFunc K) Qd := by
    rw [map_add, map_mul, add_div, mul_div_assoc, div_self hQd0, mul_one]
  rw [hcomb, eval_algebraMap_div α _ _ hQd]
  -- evaluate: numerator `(derivative^[d] W · Qd + Pd)(α) = (derivative^[d] W)(α)·Qd(α)` (since `Pd(α)=0`)
  rw [Polynomial.eval_add, Polynomial.eval_mul, hPd0, add_zero,
    eval_iterate_derivative_eq_factorial_taylor_coeff, localCoeff, ← hWdef]
  have hfac : (d.factorial : K) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero (R := K)).mpr (Nat.factorial_ne_zero d)
  field_simp

/-- **`hᵢ,α = A/M` for `M = Dᵢ,α^i·Eᵢ`** (`= lDenomα Eᵢ Dᵢ,α i 0`): the genuine function the engine
differentiates is `A/M`, the same `A/M` whose order-`d` Taylor digits are `localCoeff` (Stage M).
`hFracα A Eᵢ Dᵢ,α i = algebraMap A / algebraMap (lDenomα Eᵢ Dᵢ,α i 0)` and `lDenomα Eᵢ Dᵢ,α i 0 = Dᵢ,α^i·Eᵢ`. -/
theorem hFracα_eq_div_lDenomα (A Ei Diα : K[X]) (i : ℕ) :
    hFracα A Ei Diα i
      = algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (lDenomα Ei Diα i 0) := rfl

/-- **P2, chained to the engine: `localCoeff = Hᵢ,(i−d)(α)`** (Bronstein §2.7, the full coefficient
identification): at a root `α` of the monic `Dᵢ = (x−α)·Dᵢ,α`, with `M = Dᵢ,α^i·Eᵢ` (`Eᵢ = laurentE D Dᵢ i`,
so `D = (x−α)ⁱ·M`) pole-free at `α` and `d < i`, the Stage L `(X−α)`-adic Laurent digit
`localCoeff A M α i d` equals the engine output `Hᵢ,(i−d)(α) = (laurentH A D Dᵢ i (i−d))(α)`. Both equal the
order-`d` Taylor coefficient `(1/d!)·(d/dx)^[d](A/M)(α)` of `hᵢ,α = A/M = (A/D)(x−α)ⁱ`: `localCoeff` by the
Hasse-derivative bridge `localCoeff_eq_taylor_coeff`, the engine output by the differential-engine invariant
`eval_laurentH_eq_taylor_coeff` (with `i − (i − d) = d`). This is the final unification of the Stage L
principal-part structure with the Stage K differential engine. -/
theorem localCoeff_eq_laurentH [CharZero K] (A D Di Diα : K[X]) {α : K} (i d : ℕ)
    (hi : 0 < i) (hd : d < i) (hDi : Di.Monic) (hα : Di.eval α = 0)
    (hfac : Di = (Polynomial.X - Polynomial.C α) * Diα)
    (hcopE : IsCoprime (laurentE D Di i) Di) (hcopD : IsCoprime (derivative Di) Di)
    (hEi : (laurentE D Di i).eval α ≠ 0) (hDiα : Diα.eval α ≠ 0) :
    localCoeff A (lDenomα (laurentE D Di i) Diα i 0) α i d
      = (laurentH A D Di i (i - d)).eval α := by
  set Ei := laurentE D Di i with hEidef
  set M := lDenomα Ei Diα i 0 with hMdef
  -- `M(α) ≠ 0`: `M = Diα^i·Ei`
  have hM : M.eval α ≠ 0 := by
    rw [hMdef, lDenomα, Nat.add_zero, Nat.zero_add, pow_one, Polynomial.eval_mul, Polynomial.eval_pow]
    exact mul_ne_zero (pow_ne_zero _ hDiα) hEi
  -- the engine side: `Hᵢ,(i−d)(α) = (1/(i−(i−d))!)·(d/dx)^[i−(i−d)] hᵢ,α (α)`, with `i−(i−d)=d`
  have hji : i - d ≤ i := by omega
  rw [eval_laurentH_eq_taylor_coeff (Diα := Diα) i (i - d) hi hji hDi hα hfac hcopE hcopD hEi hDiα]
  rw [show i - (i - d) = d from by omega, ← hEidef]
  -- the `localCoeff` side via the Hasse bridge, with `hFracα = A/M`
  rw [localCoeff_eq_taylor_coeff A M i d hM hd, hFracα_eq_div_lDenomα, ← hMdef]

/-- Restatement of P2 (the coefficient bridge): the Stage L Laurent digit `localCoeff` is the order-`d`
Taylor coefficient `(1/d!)·(d/dx)^[d](A/M)(α)` of `hᵢ,α = A/M`. -/
example [CharZero K] (A M : K[X]) {α : K} (i d : ℕ) (hM : M.eval α ≠ 0) (hd : d < i) :
    localCoeff A M α i d
      = (((d.factorial : K))⁻¹)
          * RatFunc.eval (RingHom.id K) α
              ((ratFuncKDeriv^[d])
                (algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) M)) :=
  localCoeff_eq_taylor_coeff A M i d hM hd

/-- Restatement of P2 chained to the engine: the Stage L Laurent digit `localCoeff` equals the
Bronstein–Salvy engine output `Hᵢ,(i−d)(α)` (book p.56). -/
example [CharZero K] (A D Di Diα : K[X]) {α : K} (i d : ℕ) (hi : 0 < i) (hd : d < i)
    (hDi : Di.Monic) (hα : Di.eval α = 0)
    (hfac : Di = (Polynomial.X - Polynomial.C α) * Diα)
    (hcopE : IsCoprime (laurentE D Di i) Di) (hcopD : IsCoprime (derivative Di) Di)
    (hEi : (laurentE D Di i).eval α ≠ 0) (hDiα : Diα.eval α ≠ 0) :
    localCoeff A (lDenomα (laurentE D Di i) Diα i 0) α i d
      = (laurentH A D Di i (i - d)).eval α :=
  localCoeff_eq_laurentH A D Di Diα i d hi hd hDi hα hfac hcopE hcopD hEi hDiα

/-! ## Stage N — P1: the multi-pole assembly (subtracting ALL principal parts) and the remainder-zero
fact (Bronstein §2.7, Theorem 2.7.1, the literal over-the-closure conclusion)

The literal conclusion `A/D = P + ∑ᵢ ∑_{α|Dᵢ(α)=0} ∑_{j=1}^{i} Hᵢⱼ(α)/(x−α)ʲ` follows from iterating the
per-pole `subtract_localPrincipalPart_eq` over **all** distinct roots `α` of `D` (over `K̄`), then observing
that the final remainder is a **proper** rational function with **no poles**, hence `0` (the polynomial part
`P = A /ₘ D` having been split off). The two reachable closing facts:

* **the remainder-zero fact** (`properRatFunc_const_denom_eq_zero`): a proper `N/M` (`deg N < deg M`) with `M`
  a nonzero **constant** (`deg M = 0`, all poles removed) is `0` — since `deg N < 0` forces `N = 0`;
* **the multi-pole telescoping** (the `Finset`-fold of `subtract_localPrincipalPart_eq`): for a denominator
  `∏_{α ∈ R} (x−α)^{i α} · M₀` with `M₀` having no root in `R`, subtracting the per-pole principal parts at
  every `α ∈ R` leaves a remainder regular at every `α ∈ R`.

The remainder-zero fact is proved here. The multi-pole telescoping (the `Finset` induction peeling one root
at a time) is the heavy bookkeeping piece — see the documented blocker below. -/

/-- **Proper `N/M` with constant nonzero denominator is `0`** (the remainder-zero fact for P1): if
`deg N < deg M` and `M` is a nonzero constant (`M.natDegree = 0`, i.e. all poles have been removed), then
`N = 0`, so `N/M = 0` in `K(x)`. The degree bound `deg N < deg M = 0` forces `N = 0` (`degree N = ⊥`). This
is the final step: after subtracting all principal parts at all poles, the remainder is proper and pole-free,
hence a proper polynomial over a constant — necessarily zero. -/
theorem properRatFunc_const_denom_eq_zero {N M : K[X]} (hM : M.natDegree = 0) (hM0 : M ≠ 0)
    (hdeg : N.degree < M.degree) :
    algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) M = 0 := by
  -- `deg M = 0` (nonzero constant), so `deg N < 0`, forcing `N = 0`
  have hMdeg : M.degree = 0 := by
    rw [Polynomial.degree_eq_natDegree hM0, hM]; rfl
  rw [hMdeg] at hdeg
  have hN0 : N = 0 := by
    by_contra hN
    rw [Polynomial.degree_eq_natDegree hN] at hdeg
    exact absurd hdeg (by exact_mod_cast Nat.not_lt_zero _)
  rw [hN0, map_zero, zero_div]

/-- **The per-pole principal part is exactly the singular part** (P1, the per-pole content, restated as the
building block of the multi-pole assembly): for `D = (x−α)ⁱ·M`, `M(α) ≠ 0`, the existence form
`A/D − localPrincipalPart A M α i = R/M` regular at `α` (`subtract_localPrincipalPart_eq`), with the Laurent
coefficients `localCoeff A M α i (i−j) = Hᵢⱼ(α)` (`localCoeff_eq_laurentH`). Iterating this over all distinct
roots of `D` and subtracting (the multi-pole telescoping) recovers `A/D = P + ∑ poles`. -/
theorem subtract_localPrincipalPart_regular (A M : K[X]) {α : K} (i : ℕ) (hM : M.eval α ≠ 0) :
    ∃ R : K[X],
      algebraMap K[X] (RatFunc K) A
          / (algebraMap K[X] (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ i * M))
        - localPrincipalPart A M α i
        = algebraMap K[X] (RatFunc K) R / algebraMap K[X] (RatFunc K) M :=
  ⟨localRemainder A M α i, subtract_localPrincipalPart_eq A M i hM⟩

/-- **The root-product `∏_{α∈R} (x−α)^{mult α}`** (§2.7, the closure-level denominator): the product of the
prime-power factors of `D` over a `Finset` `R` of distinct roots, with multiplicities `mult`. -/
noncomputable def rootProd (R : Finset K) (mult : K → ℕ) : K[X] :=
  ∏ α ∈ R, (Polynomial.X - Polynomial.C α) ^ mult α

@[simp] theorem rootProd_empty (mult : K → ℕ) : rootProd (∅ : Finset K) mult = 1 := by
  simp [rootProd]

theorem rootProd_insert [DecidableEq K] {α : K} {R : Finset K} (mult : K → ℕ) (hα : α ∉ R) :
    rootProd (insert α R) mult = (Polynomial.X - Polynomial.C α) ^ mult α * rootProd R mult := by
  rw [rootProd, Finset.prod_insert hα, rootProd]

/-- **`(rootProd R mult)(β) ≠ 0` for `β ∉ R`**: a product of `(β−α)^{mult α}` over `α ∈ R`, each factor
nonzero since `β ≠ α` (as `β ∉ R`). The peeled denominator stays pole-free at the not-yet-processed
roots. -/
theorem eval_rootProd_ne_zero {β : K} {R : Finset K} (mult : K → ℕ) (hβ : β ∉ R) :
    (rootProd R mult).eval β ≠ 0 := by
  rw [rootProd, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
  intro α hα
  rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact pow_ne_zero _ (sub_ne_zero.mpr (fun h => hβ (h ▸ hα)))

open Classical in
/-- **P1, the multi-pole telescoping** (Bronstein §2.7, Theorem 2.7.1, the closure-level assembly): for a
`Finset R` of distinct roots with multiplicities `mult` and a base `M₀` pole-free at every `α ∈ R`
(`M₀(α) ≠ 0`), subtracting the per-pole principal parts at every `α ∈ R` from `A/(∏_{α∈R}(x−α)^{mult α}·M₀)`
leaves a remainder `Rem/M₀` that is **regular at every `α ∈ R`** (its denominator `M₀` is pole-free there).
There is a per-pole principal-part family `PP : K → RatFunc K` (each `PP α` a genuine Laurent sum
`∑_{j=1}^{mult α} c/(x−α)ʲ`, namely `localPrincipalPart` of the running numerator) with
`A/(∏_{α∈R}(x−α)^{mult α}·M₀) = ∑_{α∈R} PP α + Rem/M₀`. Proved by `Finset` induction peeling one root at a
time via `subtract_localPrincipalPart_eq` (the numerator `A` is generalized so each peel can recurse on the
local remainder). NOTE: the principal part `PP α` is `localPrincipalPart` of the *peeled* numerator (a correct
singular part at `α`); identifying its coefficients with the original-`A` engine outputs `Hᵢⱼ(α)` is the
residual coefficient-matching step (the principal part is intrinsic, but the formula-level numerators differ —
see the §2.7 residual note). -/
theorem exists_sum_localPrincipalPart (M₀ : K[X]) (mult : K → ℕ) :
    ∀ (R : Finset K), (∀ α ∈ R, M₀.eval α ≠ 0) → ∀ (A : K[X]),
      ∃ (PP : K → RatFunc K) (Rem : K[X]),
        algebraMap K[X] (RatFunc K) A
            / algebraMap K[X] (RatFunc K) (rootProd R mult * M₀)
          = (∑ α ∈ R, PP α) + algebraMap K[X] (RatFunc K) Rem / algebraMap K[X] (RatFunc K) M₀ := by
  intro R
  induction R using Finset.induction_on with
  | empty =>
    intro _ A
    refine ⟨fun _ => 0, A, ?_⟩
    rw [rootProd_empty, one_mul, Finset.sum_empty, zero_add]
  | @insert α R hα ih =>
    intro hpolefree A
    -- the running denominator after peeling `α` is `N := rootProd R mult * M₀`, pole-free at `α`
    set N := rootProd R mult * M₀ with hNdef
    have hNα : N.eval α ≠ 0 := by
      rw [hNdef, Polynomial.eval_mul]
      exact mul_ne_zero (eval_rootProd_ne_zero mult hα)
        (hpolefree α (Finset.mem_insert_self α R))
    -- peel root `α`: `A/((x−α)^{mult α}·N) = PP(α) + localRemainder/N`
    have hpeel := subtract_localPrincipalPart_eq A N (mult α) hNα
    -- recurse on `R` with the peeled numerator `localRemainder A N α (mult α)`
    obtain ⟨PP, Rem, hrec⟩ :=
      ih (fun β hβ => hpolefree β (Finset.mem_insert_of_mem hβ)) (localRemainder A N α (mult α))
    refine ⟨fun β => if β = α then localPrincipalPart A N α (mult α) else PP β, Rem, ?_⟩
    -- the sum over `insert α R` splits as the `α` term + the rest, the rest matching `hrec` (β ≠ α on `R`)
    rw [Finset.sum_insert hα, if_pos rfl]
    have hsumR : (∑ β ∈ R, (if β = α then localPrincipalPart A N α (mult α) else PP β))
        = ∑ β ∈ R, PP β := by
      refine Finset.sum_congr rfl fun β hβ => ?_
      have hβα : β ≠ α := fun h => hα (h ▸ hβ)
      rw [if_neg hβα]
    rw [hsumR]
    -- denominator `rootProd (insert α R) mult * M₀ = (x−α)^{mult α}·N`
    have hden : rootProd (insert α R) mult * M₀
        = (Polynomial.X - Polynomial.C α) ^ mult α * N := by
      rw [rootProd_insert mult hα, hNdef]; ring
    rw [hden]
    -- `A/((x−α)^{mult α}·N) = PP(α) + localRemainder/N`, then `localRemainder/N = ∑ PP + Rem/M₀` (hrec)
    have hsplit : algebraMap K[X] (RatFunc K) A
          / algebraMap K[X] (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ mult α * N)
        = localPrincipalPart A N α (mult α)
          + algebraMap K[X] (RatFunc K) (localRemainder A N α (mult α))
              / algebraMap K[X] (RatFunc K) N := by
      have := hpeel
      rw [sub_eq_iff_eq_add] at this
      rw [this]; ring
    rw [hsplit, hrec]
    ring

/-- **`Rem/(C c) = algebraMap (c⁻¹ • Rem)`** for a nonzero constant `c`: a quotient by a nonzero scalar is
itself a polynomial (the polynomial part), no division left. Used to close the multi-pole assembly when the
base `M₀ = C c` is a constant (all roots extracted over `K̄`). -/
theorem div_C_eq_algebraMap {Rem : K[X]} {c : K} (hc : c ≠ 0) :
    algebraMap K[X] (RatFunc K) Rem / algebraMap K[X] (RatFunc K) (Polynomial.C c)
      = algebraMap K[X] (RatFunc K) (Polynomial.C c⁻¹ * Rem) := by
  have hCc : algebraMap K[X] (RatFunc K) (Polynomial.C c) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (by simpa using hc)
  rw [map_mul, div_eq_iff hCc, ← map_mul, ← map_mul]
  congr 1
  rw [mul_right_comm, ← Polynomial.C_mul, inv_mul_cancel₀ hc, Polynomial.C_1, one_mul]

open Classical in
/-- **P1 capstone — Theorem 2.7.1, the over-the-closure partial fraction with constant base** (Bronstein §2.7,
the literal closure-level conclusion when `D` splits completely): for `D = (∏_{α∈R}(x−α)^{mult α})·C c` with `c`
a nonzero constant (so `R` is the full root set of `D` over `K̄`), there is a polynomial part `P` and a per-pole
principal-part family `PP` (each `PP α = ∑_{j=1}^{mult α} c_{α,j}/(x−α)ʲ` a genuine Laurent sum) with
`A/D = P + ∑_{α∈R} PP α` — the complete partial-fraction decomposition. The constant base `M₀ = C c` makes the
telescoping remainder `Rem/(C c)` a pure polynomial (`div_C_eq_algebraMap`), the polynomial part `P`. The
principal-part coefficients are the engine outputs `Hᵢⱼ(α)` per `localCoeff_eq_laurentH` (up to the residual
peeled-vs-original numerator matching). -/
theorem completePartialFraction_over_closure (A : K[X]) (mult : K → ℕ) (R : Finset K) {c : K}
    (hc : c ≠ 0) :
    ∃ (P : K[X]) (PP : K → RatFunc K),
      algebraMap K[X] (RatFunc K) A
          / algebraMap K[X] (RatFunc K) (rootProd R mult * Polynomial.C c)
        = algebraMap K[X] (RatFunc K) P + ∑ α ∈ R, PP α := by
  have hpolefree : ∀ α ∈ R, (Polynomial.C c).eval α ≠ 0 := fun α _ => by
    rw [Polynomial.eval_C]; exact hc
  obtain ⟨PP, Rem, hdecomp⟩ := exists_sum_localPrincipalPart (Polynomial.C c) mult R hpolefree A
  refine ⟨Polynomial.C c⁻¹ * Rem, PP, ?_⟩
  rw [hdecomp, div_C_eq_algebraMap hc, add_comm]

/-- Restatement of the P1 remainder-zero fact: a proper `N/M` over a nonzero constant `M` is `0`. -/
example {N M : K[X]} (hM : M.natDegree = 0) (hM0 : M ≠ 0) (hdeg : N.degree < M.degree) :
    algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) M = 0 :=
  properRatFunc_const_denom_eq_zero hM hM0 hdeg

/-- Restatement of P1, the multi-pole telescoping (book p.56): subtracting the per-pole principal parts at
every root in `R` leaves a remainder `Rem/M₀` regular at every `α ∈ R`. -/
example (M₀ A : K[X]) (mult : K → ℕ) (R : Finset K) (hpf : ∀ α ∈ R, M₀.eval α ≠ 0) :
    ∃ (PP : K → RatFunc K) (Rem : K[X]),
      algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (rootProd R mult * M₀)
        = (∑ α ∈ R, PP α) + algebraMap K[X] (RatFunc K) Rem / algebraMap K[X] (RatFunc K) M₀ :=
  exists_sum_localPrincipalPart M₀ mult R hpf A

/-- Restatement of the P1 capstone (book p.56, the over-the-closure conclusion with split denominator):
`A/D = P + ∑_{α∈R} PP α` for `D = (∏_{α∈R}(x−α)^{mult α})·C c`, `c ≠ 0` (all roots of `D` over `K̄`). -/
example (A : K[X]) (mult : K → ℕ) (R : Finset K) {c : K} (hc : c ≠ 0) :
    ∃ (P : K[X]) (PP : K → RatFunc K),
      algebraMap K[X] (RatFunc K) A
          / algebraMap K[X] (RatFunc K) (rootProd R mult * Polynomial.C c)
        = algebraMap K[X] (RatFunc K) P + ∑ α ∈ R, PP α :=
  completePartialFraction_over_closure A mult R hc

/-! ## Stage O — principal-part intrinsicity (uniqueness of the principal part at `α`) and the literal
Theorem 2.7.1 conclusion (Bronstein §2.7, the final closing step)

The telescoping `exists_sum_localPrincipalPart` produces, at each pole `α`, the principal part
`PP α = localPrincipalPart A' N α i` of the **running (peeled) numerator** `A'` over the running cofactor
`N` — a correct singular part of `A/D` at `α`, but with numerators differing from the original-`A` engine
form. Principal-part **intrinsicity** closes this gap: the principal part of a rational function at `α` is
**unique** (independent of how the rest is split off), so `PP α` coincides with `localPrincipalPart A Mα α i`
for the original cofactor `Mα = D /ₘ (X−α)^i`, whose coefficients ARE the engine outputs `Hᵢⱼ(α)`
(`localCoeff_eq_laurentH`).

The mechanism: a principal part at `α` of order `i` consolidates (over the common denominator `(X−α)^i`) to
`W/(X−α)^i` with `deg W < i` (`localPrincipalPart_eq_div`, `degree_modByMonic_lt`). If such a `W/(X−α)^i`
equals a function `N/M` **regular at `α`** (`M(α) ≠ 0`), then cross-multiplying gives `(X−α)^i ∣ W·M`;
coprimality of `(X−α)^i` to `M` forces `(X−α)^i ∣ W`, and `deg W < i` forces `W = 0`. Hence two principal
parts at `α` whose difference is regular at `α` are equal (`principalPart_unique`). -/

/-- **A bounded-degree principal part `W/(X−α)^i` equal to a function regular at `α` is `0`** (§2.7, the
intrinsicity core): if `algebraMap W / (algebraMap (X−α))^i = algebraMap N / algebraMap M` with `M(α) ≠ 0`
and `deg W < i`, then `W = 0`. Cross-multiplying gives the polynomial identity `W·M = N·(X−α)^i`, so
`(X−α)^i ∣ W·M`; since `(X−α)^i` is coprime to `M` (`M(α) ≠ 0`), `(X−α)^i ∣ W`, and `deg W < i = deg (X−α)^i`
forces `W = 0` (`eq_zero_of_dvd_of_degree_lt`). -/
theorem eq_zero_of_div_pow_eq_regular {W N M : K[X]} {α : K} (i : ℕ) (hM : M.eval α ≠ 0)
    (hW : W.degree < ((Polynomial.X - Polynomial.C α) ^ i).degree)
    (heq : algebraMap K[X] (RatFunc K) W
            / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ i
          = algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) M) :
    W = 0 := by
  have hX0 : (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (X_sub_C_ne_zero α)
  have hM0 : algebraMap K[X] (RatFunc K) M ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (fun h => hM (by rw [h, Polynomial.eval_zero]))
  -- cross-multiply the `RatFunc` identity to a polynomial identity `W·M = N·(X−α)^i`
  rw [div_eq_div_iff (pow_ne_zero i hX0) hM0, ← map_pow, ← map_mul, ← map_mul] at heq
  have hpoly : W * M = N * (Polynomial.X - Polynomial.C α) ^ i :=
    RatFunc.algebraMap_injective K heq
  -- `(X−α)^i ∣ W·M`, coprime to `M`, so `(X−α)^i ∣ W`; then `deg W < i` forces `W = 0`
  have hdvd : (Polynomial.X - Polynomial.C α) ^ i ∣ W * M := ⟨N, by rw [hpoly]; ring⟩
  have hcop : IsCoprime ((Polynomial.X - Polynomial.C α) ^ i) M :=
    (isCoprime_M_X_sub_C_pow i hM).symm
  exact eq_zero_of_dvd_of_degree_lt (hcop.dvd_of_dvd_mul_right hdvd) hW

/-- **Principal-part intrinsicity / uniqueness at `α`** (§2.7, the closing step): two principal parts at `α`
of order `i` whose difference is regular at `α` are equal. Concretely, if
`localPrincipalPart A₁ M₁ α i + r₁ = localPrincipalPart A₂ M₂ α i + r₂` where `r₁, r₂` are functions regular
at `α` (here both `Nₖ/Mₖ` with `Mₖ(α) ≠ 0`), then `localPrincipalPart A₁ M₁ α i = localPrincipalPart A₂ M₂ α i`.
Consolidating both principal parts to `Wₖ/(X−α)^i` (`localPrincipalPart_eq_div`, `deg Wₖ < i`), their
difference `(W₁−W₂)/(X−α)^i` equals the regular `r₂ − r₁` (a single quotient `N/M`, `M(α) ≠ 0`), so
`W₁ − W₂ = 0` (`eq_zero_of_div_pow_eq_regular`); hence `W₁ = W₂` and the principal parts agree. -/
theorem principalPart_unique {A₁ M₁ A₂ M₂ N₁ N₂ Md₁ Md₂ : K[X]} {α : K} (i : ℕ)
    (hMd₁ : Md₁.eval α ≠ 0) (hMd₂ : Md₂.eval α ≠ 0)
    (heq : localPrincipalPart A₁ M₁ α i
            + algebraMap K[X] (RatFunc K) N₁ / algebraMap K[X] (RatFunc K) Md₁
          = localPrincipalPart A₂ M₂ α i
            + algebraMap K[X] (RatFunc K) N₂ / algebraMap K[X] (RatFunc K) Md₂) :
    localPrincipalPart A₁ M₁ α i = localPrincipalPart A₂ M₂ α i := by
  set W₁ := localApprox A₁ M₁ α i with hW₁
  set W₂ := localApprox A₂ M₂ α i with hW₂
  have hX0 : (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (X_sub_C_ne_zero α)
  have hMd₁0 : algebraMap K[X] (RatFunc K) Md₁ ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (fun h => hMd₁ (by rw [h, Polynomial.eval_zero]))
  have hMd₂0 : algebraMap K[X] (RatFunc K) Md₂ ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (fun h => hMd₂ (by rw [h, Polynomial.eval_zero]))
  have hDp0 : (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ i ≠ 0 :=
    pow_ne_zero i hX0
  have hMd₁₂0 : algebraMap K[X] (RatFunc K) (Md₁ * Md₂) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero hMd₁0 hMd₂0
  -- consolidate both principal parts to the common `(X−α)^i` denominator
  rw [localPrincipalPart_eq_div, localPrincipalPart_eq_div, ← hW₁, ← hW₂] at heq
  -- the polynomial cross-identity `(W₁ − W₂)·(Md₁·Md₂) = (N₂·Md₁ − N₁·Md₂)·(X−α)^i`, from `heq`
  -- rearrange `heq` so the shared `D^i` denominator combines on one side
  have heqsub : algebraMap K[X] (RatFunc K) (W₁ - W₂)
        / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ i
      = algebraMap K[X] (RatFunc K) N₂ / algebraMap K[X] (RatFunc K) Md₂
        - algebraMap K[X] (RatFunc K) N₁ / algebraMap K[X] (RatFunc K) Md₁ := by
    rw [map_sub, sub_div]
    linear_combination heq
  have hpolyid : (W₁ - W₂) * (Md₁ * Md₂)
      = (N₂ * Md₁ - N₁ * Md₂) * (Polynomial.X - Polynomial.C α) ^ i := by
    apply RatFunc.algebraMap_injective K
    rw [div_sub_div _ _ hMd₂0 hMd₁0,
      div_eq_div_iff hDp0 (mul_ne_zero hMd₂0 hMd₁0)] at heqsub
    simp only [map_mul, map_sub, map_pow] at heqsub ⊢
    ring_nf
    ring_nf at heqsub
    linear_combination heqsub
  -- `(W₁−W₂)/(X−α)^i = (N₂·Md₁ − N₁·Md₂)/(Md₁·Md₂)`, regular at `α`
  have hdiff : algebraMap K[X] (RatFunc K) (W₁ - W₂)
        / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ i
      = algebraMap K[X] (RatFunc K) (N₂ * Md₁ - N₁ * Md₂)
        / algebraMap K[X] (RatFunc K) (Md₁ * Md₂) := by
    rw [div_eq_div_iff hDp0 hMd₁₂0, ← map_pow, ← map_mul, ← map_mul, hpolyid]
  -- the difference numerator has degree `< i` (each `Wₖ` is a `%ₘ (X−α)^i`)
  have hdeg : (W₁ - W₂).degree < ((Polynomial.X - Polynomial.C α) ^ i).degree := by
    have hmonic : ((Polynomial.X - Polynomial.C α) ^ i).Monic := (monic_X_sub_C α).pow i
    have h1 : W₁.degree < ((Polynomial.X - Polynomial.C α) ^ i).degree := by
      rw [hW₁, localApprox]; exact degree_modByMonic_lt _ hmonic
    have h2 : W₂.degree < ((Polynomial.X - Polynomial.C α) ^ i).degree := by
      rw [hW₂, localApprox]; exact degree_modByMonic_lt _ hmonic
    exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt h1 h2)
  -- `W₁ − W₂ = 0` by the intrinsicity core, so the principal parts agree
  have hMM : (Md₁ * Md₂).eval α ≠ 0 := by
    rw [Polynomial.eval_mul]; exact mul_ne_zero hMd₁ hMd₂
  have hWeq : W₁ - W₂ = 0 := eq_zero_of_div_pow_eq_regular i hMM hdeg hdiff
  rw [localPrincipalPart_eq_div, localPrincipalPart_eq_div, ← hW₁, ← hW₂,
    sub_eq_zero.mp hWeq]

/-- **The principal part in engine form `∑_{j=1}^{i} Hᵢⱼ(α)/(x−α)ʲ`** (§2.7, Theorem 2.7.1, the literal
per-pole conclusion): at a root `α` of the monic `Dᵢ = (x−α)·Dᵢ,α`, the principal part of `A/D` at `α`
(`localPrincipalPart A M α i`, `M = Dᵢ,α^i·Eᵢ` the original cofactor with `D = (x−α)ⁱ·M`) is **literally** the
Bronstein–Salvy engine sum `∑_{j=1}^{i} (laurentH A D Dᵢ i j)(α)/(x−α)ʲ`. Each Laurent coefficient
`localCoeff A M α i (i−j)` is the engine output `Hᵢⱼ(α)` (`localCoeff_eq_laurentH`, with `i−(i−j)=j` for
`1 ≤ j ≤ i`, so the `i−j < i` hypothesis holds). This is the precise sense in which the engine `Hᵢⱼ` are the
partial-fraction Laurent coefficients of `A/D`. -/
theorem localPrincipalPart_eq_engineSum [CharZero K] (A D Di Diα : K[X]) {α : K} (i : ℕ)
    (hi : 0 < i) (hDi : Di.Monic) (hα : Di.eval α = 0)
    (hfac : Di = (Polynomial.X - Polynomial.C α) * Diα)
    (hcopE : IsCoprime (laurentE D Di i) Di) (hcopD : IsCoprime (derivative Di) Di)
    (hEi : (laurentE D Di i).eval α ≠ 0) (hDiα : Diα.eval α ≠ 0) :
    localPrincipalPart A (lDenomα (laurentE D Di i) Diα i 0) α i
      = ∑ j ∈ Finset.Icc 1 i,
          algebraMap K[X] (RatFunc K) (Polynomial.C ((laurentH A D Di i j).eval α))
            / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ j := by
  rw [localPrincipalPart]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_Icc] at hj
  -- the `j`-th Laurent coefficient `localCoeff A M α i (i−j) = Hᵢⱼ(α)`
  rw [localCoeff_eq_laurentH A D Di Diα i (i - j) hi (by omega) hDi hα hfac hcopE hcopD hEi hDiα,
    show i - (i - j) = j from by omega]

/-! ## Stage P — the literal Theorem 2.7.1 conclusion over the algebraic closure (engine form) -/

open Classical in
/-- **Theorem 2.7.1, the literal partial fraction `A/D = P + ∑ᵢ ∑_α ∑_{j=1}^{i} Hᵢⱼ(α)/(x−α)ʲ`** (Bronstein
§2.7, the closure-level conclusion, engine form): for `D = (∏_{α∈R}(x−α)^{mult α})·C c` split over `K̄`
(`c ≠ 0`), there is a polynomial part `P` and a per-pole principal-part family `PP` with
`A/D = P + ∑_{α∈R} PP α`, where each `PP α` is a genuine Laurent sum `∑_{j=1}^{mult α} c_{α,j}/(x−α)ʲ` (the
principal part of `A/D` at `α`). By `localPrincipalPart_eq_engineSum`, each such per-pole principal part is the
engine sum `∑_{j=1}^{mult α} Hᵢⱼ(α)/(x−α)ʲ` once `PP α` is identified (via principal-part intrinsicity,
`principalPart_unique`) with `localPrincipalPart` of the original numerator. This is the over-the-closure
`completePartialFraction_over_closure` packaged as the book conclusion. -/
theorem completePartialFraction_thm_2_7_1 (A : K[X]) (mult : K → ℕ) (R : Finset K) {c : K}
    (hc : c ≠ 0) :
    ∃ (P : K[X]) (PP : K → RatFunc K),
      algebraMap K[X] (RatFunc K) A
          / algebraMap K[X] (RatFunc K) (rootProd R mult * Polynomial.C c)
        = algebraMap K[X] (RatFunc K) P + ∑ α ∈ R, PP α :=
  completePartialFraction_over_closure A mult R hc

/-- **Per-pole intrinsic identification of any principal part with the engine sum** (§2.7, the bridge from
the telescoping's per-pole `PP α` to the literal engine form): at a root `α` of the monic
`Dᵢ = (x−α)·Dᵢ,α`, with `D = (x−α)ⁱ·M`, `M = Dᵢ,α^i·Eᵢ` (`Eᵢ = laurentE D Dᵢ i`) the original cofactor, IF a
candidate Laurent sum `q` (a principal part at `α`, given as `localPrincipalPart A' M' α i` for some peeled
data `A', M'`) has the property that `A/D − q` is **regular at `α`** (`= N/Md`, `Md(α) ≠ 0`), then `q` is
**literally** the engine sum `∑_{j=1}^{i} (laurentH A D Dᵢ i j)(α)/(x−α)ʲ`. By principal-part intrinsicity
(`principalPart_unique`, since `A/D − q` and `A/D − localPrincipalPart A M α i` are both regular at `α`),
`q = localPrincipalPart A M α i`, which is the engine sum by `localPrincipalPart_eq_engineSum`. This closes
the peeled-vs-original numerator matching: the intrinsic principal part is the original-`A` engine sum
regardless of how it was computed. -/
theorem principalPart_eq_engineSum_of_regular [CharZero K] {A A' M' N Md D Di Diα : K[X]} {α : K}
    (i : ℕ) (hi : 0 < i) (hDi : Di.Monic) (hα : Di.eval α = 0)
    (hfac : Di = (Polynomial.X - Polynomial.C α) * Diα)
    (hcopE : IsCoprime (laurentE D Di i) Di) (hcopD : IsCoprime (derivative Di) Di)
    (hEi : (laurentE D Di i).eval α ≠ 0) (hDiα : Diα.eval α ≠ 0) (hMd : Md.eval α ≠ 0)
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
    exact mul_ne_zero (pow_ne_zero _ hDiα) hEi
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
    localPrincipalPart_eq_engineSum A D Di Diα i hi hDi hα hfac hcopE hcopD hEi hDiα]

/-! ## Stage Q — regularity at `α` as a predicate, and the fully-assembled engine-form capstone -/

/-- **Regularity at `α`** (§2.7, the pole-free predicate): a `RatFunc K` is regular at `α` when it is some
`N/M` with `M(α) ≠ 0` (no pole at `α`). Closed under addition/subtraction and contains every principal part
at a *different* root `β ≠ α`. -/
def RegularAt (α : K) (f : RatFunc K) : Prop :=
  ∃ (N M : K[X]), M.eval α ≠ 0 ∧ f = algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) M

/-- **`0` is regular at `α`** (`N = 0`, `M = 1`). -/
theorem RegularAt.zero (α : K) : RegularAt α (0 : RatFunc K) :=
  ⟨0, 1, by simp, by simp⟩

/-- **`RegularAt` is closed under addition**: `N₁/M₁ + N₂/M₂ = (N₁·M₂ + N₂·M₁)/(M₁·M₂)`, denominator
`(M₁·M₂)(α) = M₁(α)·M₂(α) ≠ 0`. -/
theorem RegularAt.add {α : K} {f g : RatFunc K} (hf : RegularAt α f) (hg : RegularAt α g) :
    RegularAt α (f + g) := by
  obtain ⟨N₁, M₁, hM₁, rfl⟩ := hf
  obtain ⟨N₂, M₂, hM₂, rfl⟩ := hg
  have hM₁0 : algebraMap K[X] (RatFunc K) M₁ ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (fun h => hM₁ (by rw [h, Polynomial.eval_zero]))
  have hM₂0 : algebraMap K[X] (RatFunc K) M₂ ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (fun h => hM₂ (by rw [h, Polynomial.eval_zero]))
  refine ⟨N₁ * M₂ + M₁ * N₂, M₁ * M₂, by rw [Polynomial.eval_mul]; exact mul_ne_zero hM₁ hM₂, ?_⟩
  rw [div_add_div _ _ hM₁0 hM₂0, map_add, map_mul, map_mul, map_mul]

/-- **`RegularAt` is closed under finite sums** over a `Finset`. -/
theorem RegularAt.sum {α : K} {ι : Type*} {s : Finset ι} {f : ι → RatFunc K}
    (hf : ∀ i ∈ s, RegularAt α (f i)) : RegularAt α (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RegularAt.zero α
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- **A principal part at `β` is regular at every `α ≠ β`** (§2.7): `localPrincipalPart A M β i` consolidates
to `Wᵝ/(x−β)^i` (`localPrincipalPart_eq_div`), whose denominator `(x−β)^i` is `(α−β)^i ≠ 0` at `α ≠ β`. -/
theorem RegularAt.localPrincipalPart {α β : K} (hαβ : α ≠ β) (A M : K[X]) (i : ℕ) :
    RegularAt α (localPrincipalPart A M β i) := by
  refine ⟨localApprox A M β i, (Polynomial.X - Polynomial.C β) ^ i, ?_, ?_⟩
  · rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact pow_ne_zero _ (sub_ne_zero.mpr hαβ)
  · rw [localPrincipalPart_eq_div, map_pow]

/-- **A regular function as the `N/Md` certificate**: unpacks `RegularAt α f` to a concrete `N/Md` with
`Md(α) ≠ 0`, the input form of `principalPart_eq_engineSum_of_regular`. -/
theorem RegularAt.exists_div {α : K} {f : RatFunc K} (hf : RegularAt α f) :
    ∃ (N Md : K[X]), Md.eval α ≠ 0
      ∧ f = algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) Md := hf

open Classical in
/-- **P1, the multi-pole telescoping with per-pole regularity certificate** (§2.7, the strengthened
assembly): like `exists_sum_localPrincipalPart`, but additionally certifies that for **each** pole `α ∈ R`,
subtracting *only* its own principal part `PP α` from the whole fraction leaves a function **regular at `α`**
(`RegularAt α (A/(∏·M₀) − PP α)`). This is the hypothesis `principalPart_eq_engineSum_of_regular` needs to
upgrade each peeled `PP α` to the original-`A` engine sum. Proof: at each peel `α₀`, the whole minus its own
principal part is exactly the local remainder `localRemainder/N` (regular at `α₀` since `N(α₀) ≠ 0`); for the
already-processed `γ ≠ α₀`, the peeled `α₀`-principal part is regular at `γ` (`RegularAt.localPrincipalPart`)
and the recursive certificate gives the rest, so their sum is regular at `γ` (`RegularAt.add`). -/
theorem exists_sum_localPrincipalPart_regular (M₀ : K[X]) (mult : K → ℕ) :
    ∀ (R : Finset K), (∀ α ∈ R, M₀.eval α ≠ 0) → ∀ (A : K[X]),
      ∃ (PP : K → RatFunc K) (Rem : K[X]),
        algebraMap K[X] (RatFunc K) A
            / algebraMap K[X] (RatFunc K) (rootProd R mult * M₀)
          = (∑ α ∈ R, PP α) + algebraMap K[X] (RatFunc K) Rem / algebraMap K[X] (RatFunc K) M₀
        ∧ (∀ α ∈ R, RegularAt α
            (algebraMap K[X] (RatFunc K) A
                / algebraMap K[X] (RatFunc K) (rootProd R mult * M₀) - PP α))
        ∧ ∀ α ∈ R, ∃ (A' M' : K[X]), PP α = localPrincipalPart A' M' α (mult α) := by
  intro R
  induction R using Finset.induction_on with
  | empty =>
    intro _ A
    exact ⟨fun _ => 0, A, by rw [rootProd_empty, one_mul, Finset.sum_empty, zero_add],
      (fun α hα => by simp at hα), fun α hα => by simp at hα⟩
  | @insert α₀ R hα₀ ih =>
    intro hpolefree A
    set N := rootProd R mult * M₀ with hNdef
    have hNα₀ : N.eval α₀ ≠ 0 := by
      rw [hNdef, Polynomial.eval_mul]
      exact mul_ne_zero (eval_rootProd_ne_zero mult hα₀)
        (hpolefree α₀ (Finset.mem_insert_self α₀ R))
    have hpeel := subtract_localPrincipalPart_eq A N (mult α₀) hNα₀
    obtain ⟨PP, Rem, hrec, hregrec, hstructrec⟩ :=
      ih (fun β hβ => hpolefree β (Finset.mem_insert_of_mem hβ)) (localRemainder A N α₀ (mult α₀))
    refine ⟨fun β => if β = α₀ then localPrincipalPart A N α₀ (mult α₀) else PP β, Rem, ?_, ?_, ?_⟩
    · -- the decomposition equation (as in `exists_sum_localPrincipalPart`)
      simp only [Finset.sum_insert hα₀, if_pos]
      have hsumR : (∑ β ∈ R, (if β = α₀ then localPrincipalPart A N α₀ (mult α₀) else PP β))
          = ∑ β ∈ R, PP β :=
        Finset.sum_congr rfl fun β hβ => if_neg (show β ≠ α₀ from fun h => hα₀ (h ▸ hβ))
      rw [hsumR]
      have hden : rootProd (insert α₀ R) mult * M₀
          = (Polynomial.X - Polynomial.C α₀) ^ mult α₀ * N := by
        rw [rootProd_insert mult hα₀, hNdef]; ring
      rw [hden]
      have hsplit : algebraMap K[X] (RatFunc K) A
            / algebraMap K[X] (RatFunc K) ((Polynomial.X - Polynomial.C α₀) ^ mult α₀ * N)
          = localPrincipalPart A N α₀ (mult α₀)
            + algebraMap K[X] (RatFunc K) (localRemainder A N α₀ (mult α₀))
                / algebraMap K[X] (RatFunc K) N := by
        rw [sub_eq_iff_eq_add] at hpeel; rw [hpeel]; ring
      rw [hsplit, hrec]; ring
    · -- the per-pole regularity certificate
      intro γ hγ
      -- the whole fraction over `insert α₀ R`
      have hden : rootProd (insert α₀ R) mult * M₀
          = (Polynomial.X - Polynomial.C α₀) ^ mult α₀ * N := by
        rw [rootProd_insert mult hα₀, hNdef]; ring
      -- whole = PP(α₀) + localRemainder/N  (the peel)
      have hwhole : algebraMap K[X] (RatFunc K) A
            / algebraMap K[X] (RatFunc K) (rootProd (insert α₀ R) mult * M₀)
          = localPrincipalPart A N α₀ (mult α₀)
            + algebraMap K[X] (RatFunc K) (localRemainder A N α₀ (mult α₀))
                / algebraMap K[X] (RatFunc K) N := by
        rw [sub_eq_iff_eq_add] at hpeel; rw [hden, hpeel]; ring
      rw [hwhole]
      simp only []  -- beta-reduce the `PP'` lambda applied to `γ`
      rcases eq_or_ne γ α₀ with hγα₀ | hγα₀
      · -- γ = α₀: whole − PP(α₀) = localRemainder/N, regular at α₀ (`N(α₀) ≠ 0`)
        subst hγα₀
        rw [if_pos rfl, add_sub_cancel_left]
        exact ⟨localRemainder A N γ (mult γ), N, hNα₀, rfl⟩
      · -- γ ≠ α₀: whole − PP(γ) = PP(α₀) + (localRemainder/N − PP(γ)); both summands regular at γ
        rw [if_neg hγα₀]
        have hmemR : γ ∈ R := Finset.mem_of_mem_insert_of_ne hγ hγα₀
        have h1 : RegularAt γ (localPrincipalPart A N α₀ (mult α₀)) :=
          RegularAt.localPrincipalPart hγα₀ A N (mult α₀)
        have h2 : RegularAt γ
            (algebraMap K[X] (RatFunc K) (localRemainder A N α₀ (mult α₀))
                / algebraMap K[X] (RatFunc K) N - PP γ) := hregrec γ hmemR
        have hrw : localPrincipalPart A N α₀ (mult α₀)
              + algebraMap K[X] (RatFunc K) (localRemainder A N α₀ (mult α₀))
                  / algebraMap K[X] (RatFunc K) N - PP γ
            = localPrincipalPart A N α₀ (mult α₀)
              + (algebraMap K[X] (RatFunc K) (localRemainder A N α₀ (mult α₀))
                  / algebraMap K[X] (RatFunc K) N - PP γ) := by ring
        rw [hrw]
        exact h1.add h2
    · -- each `PP α` is a `localPrincipalPart` (explicitly for `α₀`, by IH for `α ∈ R`)
      intro γ hγ
      simp only []
      rcases eq_or_ne γ α₀ with hγα₀ | hγα₀
      · subst hγα₀; exact ⟨A, N, by rw [if_pos rfl]⟩
      · rw [if_neg hγα₀]
        exact hstructrec γ (Finset.mem_of_mem_insert_of_ne hγ hγα₀)

open Classical in
/-- **Theorem 2.7.1, the LITERAL engine-form partial fraction `A/D = P + ∑_α ∑_{j=1}^{mult α} Hᵢⱼ(α)/(x−α)ʲ`**
(Bronstein §2.7, the full closure-level conclusion): for `D = (∏_{α∈R}(x−α)^{mult α})·C c` split over `K̄`
(`c ≠ 0`), GIVEN per-pole squarefree-factorization data `pole α` (a monic `Dᵢ = (x−α)·Dᵢ,α` with `α` its root,
the cofactor coprimalities, the base-value nonvanishing, `0 < mult α`, and the original factorization
`D = (x−α)^{mult α}·(Dᵢ,α^{mult α}·Eᵢ)`), there is a polynomial part `P` with
`A/D = P + ∑_{α∈R} ∑_{j=1}^{mult α} (laurentH A D Dᵢ (mult α) j)(α)/(x−α)ʲ` — the engine outputs `Hᵢⱼ(α)` ARE
the partial-fraction Laurent coefficients. Each per-pole principal part from the telescoping
(`exists_sum_localPrincipalPart_regular`) is identified with the original-`A` engine sum by principal-part
intrinsicity (`principalPart_eq_engineSum_of_regular`), the per-pole `RegularAt α (A/D − PP α)` certificate
supplying the needed regularity. This is the complete, literal Theorem 2.7.1 over the algebraic closure. -/
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
    apply principalPart_eq_engineSum_of_regular (D := D) (mult α) hi hDimonic hDiα0root hfac hcopE hcopD
      hEi hDiαα hMd
    -- the goal denominator `(x−α)^{mult α}·lDenomα… = D` (`hDfac`); rest is `hreg`'s certificate
    rw [← hDfac, ← hPPeq]
    exact hregdiv
  -- rewrite the sum and fold the constant remainder into the polynomial part
  rw [hdecomp, div_C_eq_algebraMap hc, add_comm]
  congr 1
  exact Finset.sum_congr rfl hPPeng

/-- Restatement of the principal-part intrinsicity / uniqueness (book §2.7, the closing fact): two principal
parts at `α` of order `i` whose difference is regular at `α` are equal. -/
example {A₁ M₁ A₂ M₂ N₁ N₂ Md₁ Md₂ : K[X]} {α : K} (i : ℕ) (hMd₁ : Md₁.eval α ≠ 0)
    (hMd₂ : Md₂.eval α ≠ 0)
    (heq : localPrincipalPart A₁ M₁ α i
            + algebraMap K[X] (RatFunc K) N₁ / algebraMap K[X] (RatFunc K) Md₁
          = localPrincipalPart A₂ M₂ α i
            + algebraMap K[X] (RatFunc K) N₂ / algebraMap K[X] (RatFunc K) Md₂) :
    localPrincipalPart A₁ M₁ α i = localPrincipalPart A₂ M₂ α i :=
  principalPart_unique i hMd₁ hMd₂ heq

/-- Restatement of the literal per-pole engine form (book p.56): the principal part of `A/D` at a root `α` of
`Dᵢ` is `∑_{j=1}^{i} Hᵢⱼ(α)/(x−α)ʲ`, the Bronstein–Salvy engine sum. -/
example [CharZero K] (A D Di Diα : K[X]) {α : K} (i : ℕ) (hi : 0 < i) (hDi : Di.Monic)
    (hα : Di.eval α = 0) (hfac : Di = (Polynomial.X - Polynomial.C α) * Diα)
    (hcopE : IsCoprime (laurentE D Di i) Di) (hcopD : IsCoprime (derivative Di) Di)
    (hEi : (laurentE D Di i).eval α ≠ 0) (hDiα : Diα.eval α ≠ 0) :
    localPrincipalPart A (lDenomα (laurentE D Di i) Diα i 0) α i
      = ∑ j ∈ Finset.Icc 1 i,
          algebraMap K[X] (RatFunc K) (Polynomial.C ((laurentH A D Di i j).eval α))
            / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ j :=
  localPrincipalPart_eq_engineSum A D Di Diα i hi hDi hα hfac hcopE hcopD hEi hDiα

/-- Restatement of the literal Theorem 2.7.1 over `K̄` (book p.55–56), engine form:
`A/D = P + ∑ᵢ ∑_{α|Dᵢ(α)=0} (Hᵢᵢ(α)/(x−α)ⁱ + ⋯ + Hᵢ₁(α)/(x−α))`, the engine outputs `Hᵢⱼ(α)` being the
partial-fraction Laurent coefficients of `A/D`. -/
example [CharZero K] (A : K[X]) (mult : K → ℕ) (R : Finset K) {c : K} (hc : c ≠ 0)
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
                / (algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C α)) ^ j :=
  completePartialFraction_engineForm A mult R hc Di Diα pole

end DeepWiki.SymbolicIntegration
