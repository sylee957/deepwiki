import DeepWiki.ComputableAlgebra.PolyReprDegree
import DeepWiki.ComputableAlgebra.PolyReprSparse

/-! # Generic Euclidean division on `CPoly`

`cdivmod p q = (Q, R)` is fuel-less Euclidean division of `p` by `q` over a computable field: repeatedly
cancel `p`'s leading term with the monomial `(clead p / clead q)·X^(cdeg p − cdeg q)·q`. The public op is
a thin wrapper `cdivmod p q := cdivmodCore (cdeg p + 1) p q` over the fuel-threaded core `cdivmodCore`
(the `cdeg p + 1` fuel is always sufficient — each step strictly drops the degree — so it is hidden). The
**division identity** `toPoly p = toPoly q · toPoly Q + toPoly R` holds for *every* `fuel` on the core (by
pure algebra + induction, no degree argument) and specialises to the fuel-less `cdivmod`.
Representation-generic: runs on any `CPoly` (dense or sparse), reduces under `native_decide` (the core
is structural recursion — no well-founded recursion). See `docs/representation-independent-poly.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.CPoly

variable {P : Type u → Type u} [CPoly P] {α : Type u} [CCommRing α]

/-- The zero polynomial as a length-0 representation. -/
def czero : P α := ofFn 0 (fun _ => CCommRing.zero)

section Spec
variable [CRingSpec α]

/-- `toPoly czero = 0`. -/
theorem toPoly_czero : (toPoly (czero : P α)) = 0 := by
  apply Polynomial.ext; intro k
  rw [coeff_toPoly, czero, coeff_ofFn, if_neg (by omega), CRingSpec.toR_zero, Polynomial.coeff_zero]

end Spec

/-- Euclidean division `cdivmodCore fuel p q = (quotient, remainder)` over a computable field: each step
cancels `p`'s leading term against `q`. -/
def cdivmodCore [CField α] : ℕ → P α → P α → P α × P α
  | 0, p, _ => (czero, p)
  | fuel + 1, p, q =>
    if cdeg p < cdeg q ∨ cisZero p then (czero, p)
    else
      let t := cmonomial (CField.div (clead p) (clead q)) (cdeg p - cdeg q)
      let res := cdivmodCore fuel (csub p (mul t q)) q
      (add t res.1, res.2)

/-- **The division identity:** `toPoly p = toPoly q · toPoly Q + toPoly R` for `(Q, R) = cdivmodCore fuel
p q`, at *every* `fuel`. Pure algebra + induction — no degree argument. Representation-generic. -/
theorem toPoly_cdivmodCore [CField α] [CRingSpec α] :
    ∀ (fuel : ℕ) (p q : P α),
      toPoly p = toPoly q * toPoly (cdivmodCore fuel p q).1 + toPoly (cdivmodCore fuel p q).2
  | 0, p, q => by rw [cdivmodCore, toPoly_czero (P := P)]; ring
  | fuel + 1, p, q => by
    rw [cdivmodCore]
    by_cases h : cdeg p < cdeg q ∨ cisZero p
    · rw [if_pos h, toPoly_czero (P := P)]; ring
    · rw [if_neg h]
      set t := cmonomial (P := P) (CField.div (clead p) (clead q)) (cdeg p - cdeg q) with ht
      have ih := toPoly_cdivmodCore fuel (csub p (mul t q)) q
      rw [toPoly_csub, toPoly_mul, sub_eq_iff_eq_add] at ih
      simp only [toPoly_add]
      rw [ih]; ring

/-- **Fuel-less Euclidean division** `cdivmod p q = (quotient, remainder)`: the `cdeg p + 1` fuel is
always past `cdeg p`, so the remainder is fully reduced. The fuel is an internal constant, not a
parameter. -/
def cdivmod [CField α] (p q : P α) : P α × P α := cdivmodCore (cdeg p + 1) p q

/-- **The division identity** (fuel-less): `toPoly p = toPoly q · toPoly Q + toPoly R`. -/
theorem toPoly_cdivmod [CField α] [CRingSpec α] (p q : P α) :
    toPoly p = toPoly q * toPoly (cdivmod p q).1 + toPoly (cdivmod p q).2 :=
  toPoly_cdivmodCore (cdeg p + 1) p q

/-! ### `native_decide` showcase: `(x² − 1) / (x − 1) = (x + 1, 0)`

The generic algorithm runs on the dense `List` carrier and the sparse `SparsePoly` carrier alike. -/

/-- Dense: dividing `x² − 1` by `x − 1` leaves remainder `0`. -/
example : cisZero (cdivmod ([-1, 0, 1] : List ℚ) [-1, 1]).2 = true := by native_decide
/-- Dense: the quotient `(x² − 1)/(x − 1)` normalizes to `x + 1`. -/
example : cnorm (cdivmod ([-1, 0, 1] : List ℚ) [-1, 1]).1 = ([1, 1] : List ℚ) := by native_decide
/-- Sparse: the same division on the sparse carrier — remainder `0`, quotient of honest degree `1`
(`x + 1`). Same algorithm, different representation. -/
example : cisZero (cdivmod (SparsePoly.ofList [(0, -1), (2, 1)] : SparsePoly ℚ)
    (SparsePoly.ofList [(0, -1), (1, 1)])).2 = true := by native_decide
/-- Sparse: the quotient of `(x² − 1)/(x − 1)` has honest degree `1`. -/
example : cdeg (cdivmod (SparsePoly.ofList [(0, -1), (2, 1)] : SparsePoly ℚ)
    (SparsePoly.ofList [(0, -1), (1, 1)])).1 = 1 := by native_decide

/-! ### Computable divisibility test

A zero remainder witnesses divisibility — the soundness of deciding `q ∣ p` by `cdivmod`. -/

/-- **Divisibility from a zero remainder:** if `cdivmod p q` leaves remainder zero, then
`toPoly q ∣ toPoly p`. From the division identity. Representation-generic. -/
theorem dvd_of_cisZero_cdivmod_snd [CField α] [CRingSpec α] (p q : P α)
    (h : cisZero (P := P) (cdivmod p q).2 = true) : toPoly q ∣ toPoly p := by
  have hid := toPoly_cdivmod p q
  rw [(cisZero_iff _).mp h, add_zero] at hid
  exact hid ▸ dvd_mul_right _ _

/-! ### Euclidean GCD and the common-divisor property

`cgcd a b` (fuel-less, `:= cgcdCore (cdeg b + 1) a b`) is the Euclidean algorithm on `cdivmod`
remainders. Its **common-divisor direction** `dvd_cgcd` — every common divisor of `a` and `b` divides
`cgcd a b` — holds from the division identity alone (each remainder step preserves common divisors). The
converse (`cgcd` itself divides `a` and `b`) is `cgcd_dvd` (needs the remainder-degree termination
argument), in `PolyReprDivisionDegree.lean`. The core carries a `fuel`; `cgcd` fixes it to the always-
sufficient `cdeg b + 1`. -/

/-- Euclidean GCD via `cdivmodCore` remainders (inner division fuel `cdeg a + 1` is always sufficient). -/
def cgcdCore [CField α] : ℕ → P α → P α → P α
  | 0, a, _ => a
  | fuel + 1, a, b =>
    if cisZero b then a else cgcdCore fuel b (cdivmodCore (cdeg a + 1) a b).2

/-- **Common-divisor property:** every common divisor of `toPoly a` and `toPoly b` divides
`toPoly (cgcdCore fuel a b)`, at every `fuel`. From the division identity alone. Representation-generic. -/
theorem dvd_cgcdCore [CField α] [CRingSpec α] :
    ∀ (fuel : ℕ) (a b : P α) (d : (CRingSpec.R α)[X]),
      d ∣ toPoly a → d ∣ toPoly b → d ∣ toPoly (cgcdCore fuel a b)
  | 0, a, _, _, ha, _ => by rw [cgcdCore]; exact ha
  | fuel + 1, a, b, d, ha, hb => by
    rw [cgcdCore]
    by_cases h : cisZero b
    · rw [if_pos h]; exact ha
    · rw [if_neg h]
      have hrem : toPoly (cdivmodCore (cdeg a + 1) a b).2
          = toPoly a - toPoly b * toPoly (cdivmodCore (cdeg a + 1) a b).1 := by
        have hid := toPoly_cdivmodCore (cdeg a + 1) a b; rw [hid]; ring
      exact dvd_cgcdCore fuel b _ d hb (hrem ▸ dvd_sub ha (dvd_mul_of_dvd_left hb _))

/-- **Fuel-less Euclidean gcd** `cgcd a b`: the `cdeg b + 1` fuel bounds the Euclidean step count. -/
def cgcd [CField α] (a b : P α) : P α := cgcdCore (cdeg b + 1) a b

/-- **Common-divisor property** (fuel-less): every common divisor of `a`, `b` divides `cgcd a b`. -/
theorem dvd_cgcd [CField α] [CRingSpec α] (a b : P α) (d : (CRingSpec.R α)[X])
    (ha : d ∣ toPoly a) (hb : d ∣ toPoly b) : d ∣ toPoly (cgcd a b) :=
  dvd_cgcdCore (cdeg b + 1) a b d ha hb

/-- `cgcd` reduces (dense): `gcd(x² − 1, x − 1)` normalizes to `x − 1`. -/
example : cnorm (cgcd ([-1, 0, 1] : List ℚ) [-1, 1]) = ([-1, 1] : List ℚ) := by native_decide

/-! ### Extended Euclidean algorithm (Bézout coefficients)

`cgcdExt a b = (g, s, t)` (fuel-less, `:= cgcdExtCore (cdeg b + 1) a b`) with the **Bézout identity**
`s·a + t·b = g`, holding at *every* fuel on the core (pure algebra + the division identity, no degree
argument) and specialising to `cgcdExt`. The basis for partial fractions and coprime combination. -/

/-- Extended Euclidean: `cgcdExtCore fuel a b = (gcd, s, t)` with `s·a + t·b = gcd`. -/
def cgcdExtCore [CField α] : ℕ → P α → P α → P α × P α × P α
  | 0, a, _ => (a, one, czero)
  | fuel + 1, a, b =>
    if cisZero b then (a, one, czero)
    else
      let dm := cdivmodCore (cdeg a + 1) a b
      let res := cgcdExtCore fuel b dm.2
      (res.1, res.2.2, csub res.2.1 (mul res.2.2 dm.1))

/-- **The Bézout identity:** `toPoly s · toPoly a + toPoly t · toPoly b = toPoly g` for
`(g, s, t) = cgcdExtCore fuel a b`, at every `fuel`. From the division identity + induction. -/
theorem toPoly_cgcdExtCore [CField α] [CRingSpec α] :
    ∀ (fuel : ℕ) (a b : P α),
      toPoly (cgcdExtCore fuel a b).2.1 * toPoly a + toPoly (cgcdExtCore fuel a b).2.2 * toPoly b
        = toPoly (cgcdExtCore fuel a b).1
  | 0, a, b => by rw [cgcdExtCore, toPoly_one (P := P), toPoly_czero (P := P)]; ring
  | fuel + 1, a, b => by
    rw [cgcdExtCore]
    by_cases h : cisZero (P := P) b = true
    · rw [if_pos h, toPoly_one (P := P), toPoly_czero (P := P)]; ring
    · rw [if_neg h]
      set dm := cdivmodCore (cdeg a + 1) a b with hdm
      have hdiv := toPoly_cdivmodCore (cdeg a + 1) a b
      rw [← hdm] at hdiv
      set res := cgcdExtCore fuel b dm.2 with hres
      have ih := toPoly_cgcdExtCore fuel b dm.2
      rw [← hres] at ih
      rw [toPoly_csub, toPoly_mul, hdiv, ← ih]; ring

/-- **Fuel-less extended Euclidean** `cgcdExt a b = (g, s, t)`: the `cdeg b + 1` fuel bounds the
Euclidean step count. -/
def cgcdExt [CField α] (a b : P α) : P α × P α × P α := cgcdExtCore (cdeg b + 1) a b

/-- **The Bézout identity** (fuel-less): `toPoly s · a + toPoly t · b = toPoly g`. -/
theorem toPoly_cgcdExt [CField α] [CRingSpec α] (a b : P α) :
    toPoly (cgcdExt a b).2.1 * toPoly a + toPoly (cgcdExt a b).2.2 * toPoly b
      = toPoly (cgcdExt a b).1 :=
  toPoly_cgcdExtCore (cdeg b + 1) a b

/-- **Every common divisor divides the extended gcd** — immediate from the Bézout identity
`s·a + t·b = g` (no termination argument). -/
theorem dvd_cgcdExt [CField α] [CRingSpec α] (a b : P α) (d : (CRingSpec.R α)[X])
    (ha : d ∣ toPoly a) (hb : d ∣ toPoly b) : d ∣ toPoly (cgcdExt a b).1 := by
  rw [← toPoly_cgcdExt a b]
  exact dvd_add (Dvd.dvd.mul_left ha _) (Dvd.dvd.mul_left hb _)

/-- **Coprimality from Bézout:** if the extended-gcd component is a unit, `toPoly a` and `toPoly b`
are coprime (scale the Bézout identity by the inverse unit). -/
theorem isCoprime_of_cgcdExt_isUnit [CField α] [CRingSpec α] (a b : P α)
    (hu : IsUnit (toPoly (cgcdExt a b).1)) : IsCoprime (toPoly a) (toPoly b) := by
  obtain ⟨u, hu⟩ := hu
  refine ⟨(↑u⁻¹ : (CRingSpec.R α)[X]) * toPoly (cgcdExt a b).2.1,
    (↑u⁻¹ : (CRingSpec.R α)[X]) * toPoly (cgcdExt a b).2.2, ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add, toPoly_cgcdExt, ← hu, Units.inv_mul]

/-- **Partial-fraction existence:** for coprime `b, c`, every `a` splits as `a = e·c + f·b`
(i.e. `a/(b·c) = f/c + e/b`) — the algebraic basis of partial-fraction decomposition. -/
theorem exists_partialFraction [CField α] [CRingSpec α] (a b c : P α)
    (hcop : IsCoprime (toPoly b) (toPoly c)) :
    ∃ e f : (CRingSpec.R α)[X], toPoly a = e * toPoly c + f * toPoly b := by
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨toPoly a * v, toPoly a * u, ?_⟩
  calc toPoly a = toPoly a * 1 := (mul_one _).symm
    _ = toPoly a * (u * toPoly b + v * toPoly c) := by rw [huv]
    _ = toPoly a * v * toPoly c + toPoly a * u * toPoly b := by ring

/-- **Chinese Remainder Theorem:** for coprime moduli `m₁, m₂` and any residues `r₁, r₂` there is an
`x` congruent to `rᵢ` modulo `mᵢ` (`mᵢ ∣ x − rᵢ`). From Bézout. -/
theorem exists_crt [CField α] [CRingSpec α] (m₁ m₂ r₁ r₂ : P α)
    (hcop : IsCoprime (toPoly m₁) (toPoly m₂)) :
    ∃ x : (CRingSpec.R α)[X], toPoly m₁ ∣ (x - toPoly r₁) ∧ toPoly m₂ ∣ (x - toPoly r₂) := by
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨toPoly r₁ * (v * toPoly m₂) + toPoly r₂ * (u * toPoly m₁),
    ⟨u * (toPoly r₂ - toPoly r₁), ?_⟩, ⟨v * (toPoly r₁ - toPoly r₂), ?_⟩⟩
  · have h1 : v * toPoly m₂ = 1 - u * toPoly m₁ := by rw [← huv]; ring
    rw [h1]; ring
  · have h2 : u * toPoly m₁ = 1 - v * toPoly m₂ := by rw [← huv]; ring
    rw [h2]; ring

/-- `cgcdExtCore` reduces (dense): the Bézout combination `s·(x²−1) + t·(x−1)` equals the gcd. -/
example :
    cnorm (add (mul (cgcdExt ([-1, 0, 1] : List ℚ) [-1, 1]).2.1 [-1, 0, 1])
      (mul (cgcdExt ([-1, 0, 1] : List ℚ) [-1, 1]).2.2 [-1, 1]))
      = cnorm (cgcdExt ([-1, 0, 1] : List ℚ) [-1, 1]).1 := by native_decide
/-- Sparse: the extended Euclidean algorithm runs on the sparse carrier too — the gcd of
`x² − 1` and `x − 1` has honest degree `1`. -/
example : cdeg (cgcdExt (SparsePoly.ofList [(0, -1), (2, 1)] : SparsePoly ℚ)
    (SparsePoly.ofList [(0, -1), (1, 1)])).1 = 1 := by native_decide

end DeepWiki.SymbolicIntegration.CPoly
