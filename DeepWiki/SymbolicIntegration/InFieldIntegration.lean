import DeepWiki.SymbolicIntegration.DifferentialAlgebra.RationalFunctionDerivative
import DeepWiki.SymbolicIntegration.DifferentialAlgebra
import DeepWiki.ComputableAlgebra.PolySquarefreeTheory

/-! # Recognizing derivatives — the in-field-integration criterion
After the Hermite reduction `f = g′ + A/D` (`D` squarefree, `gcd(A, D) = 1`, `deg A < deg D`), `f` is
the derivative of a rational function iff `A = 0`. The substance is the negative half: a nonzero
log-part `A/D` is not the derivative of any rational function. -/

open Polynomial
open scoped Differential

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-- If `(B/E)′ = A/D` in `K(x)` (`D, E ≠ 0`), then `A·E² = (B'·E − B·E')·D`. -/
theorem ratFunc_mul_sq_eq_of_deriv_mk_eq {A D B E : K[X]} (hD : D ≠ 0) (hE : E ≠ 0)
    (h : (RatFunc.mk B E)′ = RatFunc.mk A D) :
    A * E ^ 2 = (derivative B * E - B * derivative E) * D := by
  rw [show (RatFunc.mk B E)′ = ratFuncDeriv (RatFunc.mk B E) from rfl, ratFuncDeriv_mk,
    RatFunc.mk_eq_mk (pow_ne_zero 2 hE) hD] at h
  exact h.symm

/-- A constant `c ≠ 0` is coprime to any `D` (its image `C c` is a unit in `K[X]`). -/
private theorem isCoprime_C_of_ne_zero (D : K[X]) {c : K} (hc : c ≠ 0) :
    IsCoprime D (C c) := by
  obtain ⟨v, hv⟩ := isUnit_C.mpr hc.isUnit
  exact ⟨0, ↑v.inv, by simp [← hv]⟩

/-- Descent step: with `D` squarefree, `gcd(A, D) = gcd(B, D) = 1`, char 0, and
`A·E² = (B'·E − B·E')·D`, if `D^{n+1} ∣ E` then `D^{n+2} ∣ E`. -/
private theorem dvd_succ_of_dvd [CharZero K] {A D B E : K[X]} (hD : Squarefree D) (hD0 : D ≠ 0)
    (hBD : IsCoprime B D)
    (hid : A * E ^ 2 = (derivative B * E - B * derivative E) * D)
    {n : ℕ} (hn : D ^ (n + 1) ∣ E) : D ^ (n + 2) ∣ E := by
  obtain ⟨G, rfl⟩ := hn
  -- `B'E − BE' = Dⁿ · (D·(B'G − BG') − (n+1)·B·D'·G)`.
  have hfac : derivative B * (D ^ (n + 1) * G) - B * derivative (D ^ (n + 1) * G)
      = D ^ n * (D * (derivative B * G - B * derivative G)
          - C ((n : K) + 1) * B * derivative D * G) := by
    rw [derivative_mul, derivative_pow]; push_cast; ring
  rw [hfac] at hid
  -- LHS `A·(D^{n+1}·G)² = D^{n+1}·(A·D^{n+1}·G²)`; cancel `D^{n+1}` from both sides.
  have hcancel : A * (D ^ (n + 1) * G) ^ 2
      = D ^ (n + 1) * (A * D ^ (n + 1) * G ^ 2) := by ring
  have hrhs : D ^ n * (D * (derivative B * G - B * derivative G)
        - C ((n : K) + 1) * B * derivative D * G) * D
      = D ^ (n + 1) * (D * (derivative B * G - B * derivative G)
          - C ((n : K) + 1) * B * derivative D * G) := by
    rw [pow_succ]; ring
  rw [hcancel, hrhs] at hid
  have hpow : D ^ (n + 1) ≠ 0 := pow_ne_zero _ hD0
  have hid' : A * D ^ (n + 1) * G ^ 2
      = D * (derivative B * G - B * derivative G)
        - C ((n : K) + 1) * B * derivative D * G :=
    mul_left_cancel₀ hpow hid
  -- `D | (n+1)·B·D'·G`: it equals `D·(...) − A·D^{n+1}·G²`, both terms divisible by `D`.
  have hDdvd : D ∣ C ((n : K) + 1) * B * derivative D * G := by
    have : C ((n : K) + 1) * B * derivative D * G
        = D * (derivative B * G - B * derivative G) - A * D ^ (n + 1) * G ^ 2 := by
      rw [hid']; ring
    rw [this]
    exact dvd_sub (Dvd.intro _ rfl)
      ⟨A * D ^ n * G ^ 2, by rw [pow_succ]; ring⟩
  -- `gcd(D, (n+1)·B·D') = 1`, so `D | G`.
  have hcopD' : IsCoprime D (derivative D) :=
    squarefree_iff_isCoprime_derivative.mp hD
  have hcn : IsCoprime D (C ((n : K) + 1)) :=
    isCoprime_C_of_ne_zero D (Nat.cast_add_one_ne_zero n)
  have hcop : IsCoprime D (C ((n : K) + 1) * B * derivative D) :=
    (hcn.mul_right hBD.symm).mul_right hcopD'
  have hDG : D ∣ G := hcop.dvd_of_dvd_mul_left (by rwa [mul_assoc] at hDdvd ⊢)
  obtain ⟨H, rfl⟩ := hDG
  exact ⟨H, by rw [pow_succ]; ring⟩

/-- Over a char-`0` field, if `D` is squarefree, `gcd(A, D) = 1`, `A ≠ 0` and `deg A < deg D`, then
`A/D` is not the derivative of any rational function: `∀ v : K(x), v′ ≠ A/D`. -/
theorem logPart_not_rational_derivative [CharZero K] {A D : K[X]} (hD : Squarefree D)
    (hAD : IsCoprime A D) (hA0 : A ≠ 0) (hdeg : A.degree < D.degree) (v : RatFunc K) :
    v′ ≠ algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) D := by
  intro hv
  have hD0 : D ≠ 0 := hD.ne_zero
  -- `D` is not a unit: `deg A < deg D` with `A ≠ 0` forces `deg D > 0`.
  have hDnu : ¬ IsUnit D := by
    intro hu
    rw [Polynomial.isUnit_iff_degree_eq_zero] at hu
    rw [hu] at hdeg
    exact absurd hdeg (not_lt.mpr (zero_le_degree_iff.mpr hA0))
  -- Write `v = B/E` with `gcd(B, E) = 1`, `E ≠ 0`.
  set B := v.num with hB
  set E := v.denom with hE
  have hEne : E ≠ 0 := RatFunc.denom_ne_zero v
  have hBE : IsCoprime B E := RatFunc.isCoprime_num_denom v
  have hvmk : v = RatFunc.mk B E := by rw [RatFunc.mk_eq_div]; exact (RatFunc.num_div_denom v).symm
  -- `gcd(B, D) = 1`: any common factor divides `A` (via the identity) and `D`, contradicting
  -- `gcd(A, D) = 1`.  We get it from `gcd(A, D) = 1` and the identity after establishing it.
  rw [hvmk, show algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) D = RatFunc.mk A D from
      (RatFunc.mk_eq_div A D).symm] at hv
  have hid : A * E ^ 2 = (derivative B * E - B * derivative E) * D :=
    ratFunc_mul_sq_eq_of_deriv_mk_eq hD0 hEne hv
  -- `gcd(B, D) = 1`: from `A·E² = (...)·D`, `D | A·E²`.  With `gcd(A,D)=1`, `D | E²`, so `gcd`
  -- of a common factor of `B,D` would divide `E` and `B` — but `gcd(B,E)=1`.  Direct route:
  -- a prime `p | gcd(B,D)`; `p | D | E²` (shown below) ⟹ `p | E`, with `p | B` contradicts
  -- `gcd(B,E)=1`.  We instead derive `gcd(B,D)=1` from `D | E` and `gcd(B,E)=1`.
  have hDAE2 : D ∣ A * E ^ 2 := ⟨derivative B * E - B * derivative E, by rw [hid]; ring⟩
  have hDE2 : D ∣ E ^ 2 := hAD.symm.dvd_of_dvd_mul_left hDAE2
  have hDE : D ∣ E := (hD.dvd_pow_iff_dvd (by norm_num)).mp hDE2
  have hBD : IsCoprime B D := IsCoprime.of_isCoprime_of_dvd_right hBE hDE
  -- Descent: `Dⁿ | E` for all `n`.
  have hall : ∀ n : ℕ, D ^ (n + 1) ∣ E := by
    intro n
    induction n with
    | zero => simpa using hDE
    | succ k ih => exact dvd_succ_of_dvd hD hD0 hBD hid ih
  -- Contradiction with finite multiplicity of `D` in the nonzero `E`.
  obtain ⟨m, hm⟩ := (FiniteMultiplicity.def).mp (FiniteMultiplicity.of_not_isUnit hDnu hEne)
  exact hm (hall m)

/-- After Hermite reduction `f = (algebraMap g)′ + A/D` (`D` squarefree, `gcd(A, D) = 1`,
`deg A < deg D`), `f` is the derivative of a rational function iff `A = 0`. -/
theorem isRationalDerivative_iff [CharZero K] {f : RatFunc K} {g : K[X]} {A D : K[X]}
    (hD : Squarefree D) (hAD : IsCoprime A D) (hdeg : A.degree < D.degree)
    (hf : f = (algebraMap K[X] (RatFunc K) g)′
          + algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) D) :
    (∃ v : RatFunc K, v′ = f) ↔ A = 0 := by
  constructor
  · rintro ⟨v, hvf⟩
    by_contra hA0
    -- `(v − g)′ = A/D` would contradict `logPart_not_rational_derivative`.
    refine logPart_not_rational_derivative hD hAD hA0 hdeg (v - algebraMap K[X] (RatFunc K) g) ?_
    rw [show (v - algebraMap K[X] (RatFunc K) g)′
          = v′ - (algebraMap K[X] (RatFunc K) g)′ from map_sub Differential.deriv _ _,
      hvf, hf]
    ring
  · rintro rfl
    -- `A = 0`: `f = g′`, so `f` is a rational derivative.
    refine ⟨algebraMap K[X] (RatFunc K) g, ?_⟩
    rw [hf, map_zero, zero_div, add_zero]

end DeepWiki.SymbolicIntegration
