import DeepWiki.SymbolicIntegration.Computable.GenericBezout
import DeepWiki.SymbolicIntegration.Computable.FieldGcd
import DeepWiki.SymbolicIntegration.Computable.FuelFreeDiophantine

/-! # Generic RDE glue lemmas (`cgcdFF`-free), shared by the `…CorrectG` tower correctness

The handful of carrier-agnostic algebraic glue lemmas the generic `QFunNZG ℚ` RDE correctness
(`ComputableRischDETowerCorrectG`) consumes. Each is **fully generic** — pure-Mathlib `Derivation`
algebra (`spde_step_glue`/`spde_const_base`/`rdeNormalDenominator_glue`) or generic-engine `toPolyG`
facts (`dvd_of_cdvdG`/`toPolyG_cdiophantineG`) plus their fuel-free companions
(`dvd_of_cdvdGWf`/`toPolyG_cdiophantineGWf`) — so they live here over the generic engine, kept
self-contained for the `…CorrectG` files. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-- **The Rothstein `SPDE`-step gluing identity** (commutative-ring `Derivation` algebra): with `D` a
derivation, divided coefficients `a, b, c`, a Bézout witness `b·r + a·z = c`, and a solution `h` of the
*reduced* equation `a·D(h) + (b + D(a))·h = z − D(r)`, the reconstruction `q = a·h + r` solves the
original divided equation `a·D(q) + b·q = c`. Pure `Derivation.leibniz` + `ring`; the algebraic core of
one `cSPDE` peel (Bronstein Theorem 6.4.1). -/
theorem spde_step_glue {R : Type*} [CommRing R] (D : Derivation ℤ R R)
    (a b c r z h : R)
    (hbez : b * r + a * z = c)
    (hred : a * D h + (b + D a) * h = z - D r) :
    a * D (a * h + r) + b * (a * h + r) = c := by
  have hD : D (a * h + r) = a * D h + D a * h + D r := by
    rw [map_add, Derivation.leibniz]; simp only [smul_eq_mul]; ring
  rw [hD]
  have : a * (a * D h + D a * h + D r) + b * (a * h + r)
      = a * (a * D h + (b + D a) * h) + (a * D r + b * r) := by ring
  rw [this, hred]
  linear_combination hbez

/-- **The constant-`a` base-case scaling identity** (commutative-ring): if `a₀ ≠ 0` is a nonzero scalar
and `h` solves the reduced `D(h) + (a₀⁻¹·b)·h = a₀⁻¹·c`, then `h` solves `a₀·D(h) + b·h = c` (multiply
through by `a₀`). The `deg(a) = 0` base case of `cSPDE`, where `α = 1`, `β = 0` (`q = h`). -/
theorem spde_const_base {K : Type*} [Field K] (D : Derivation ℤ K[X] K[X])
    (a0 : K) (b c h : K[X]) (ha0 : a0 ≠ 0)
    (hred : D h + (Polynomial.C a0⁻¹ * b) * h = Polynomial.C a0⁻¹ * c) :
    Polynomial.C a0 * D h + b * h = c := by
  have key : Polynomial.C a0 * (D h + (Polynomial.C a0⁻¹ * b) * h)
      = Polynomial.C a0 * (Polynomial.C a0⁻¹ * c) := by rw [hred]
  have hinv : Polynomial.C a0 * Polynomial.C a0⁻¹ = 1 := by
    rw [← Polynomial.C_mul, mul_inv_cancel₀ ha0, Polynomial.C_1]
  calc Polynomial.C a0 * D h + b * h
      = Polynomial.C a0 * (D h + (Polynomial.C a0⁻¹ * b) * h)
          - (Polynomial.C a0 * Polynomial.C a0⁻¹ - 1) * (b * h) := by ring
    _ = Polynomial.C a0 * (Polynomial.C a0⁻¹ * c) - (1 - 1) * (b * h) := by rw [key, hinv]
    _ = (Polynomial.C a0 * Polynomial.C a0⁻¹) * c := by ring
    _ = c := by rw [hinv, one_mul]

/-- **The §6.2 normal-denominator cleared lifting** (commutative-ring `Derivation` core): with `D` a
derivation, the normal part `DN ≠ 0`, the factorization `A = DN·H` and the two exact-division
certificates `B·FDEN = A·FNUM − DN·(D H)·FDEN`, `C·GDEN = DN·H²·GNUM`, a solution `Q` of the reduced
equation `A·D(Q) + B·Q = C` makes `y = Q/H` solve `D(y) + f·y = g` in the cleared form
`GDEN·FDEN·(D(Q)·H − Q·(D H)) + GDEN·FNUM·Q·H = GNUM·FDEN·H²`. Pure algebra: multiply the reduced
equation by `FDEN·GDEN`, the whole identity is `DN` times the goal, cancel the nonzero `DN`. -/
theorem rdeNormalDenominator_glue {R : Type*} [CommRing R] [NoZeroDivisors R]
    (D : Derivation ℤ R R) (DN H FNUM FDEN GNUM GDEN A B C Q : R)
    (hDN : DN ≠ 0)
    (hA : A = DN * H)
    (hB : B * FDEN = A * FNUM - DN * D H * FDEN)
    (hC : C * GDEN = DN * H ^ 2 * GNUM)
    (hred : A * D Q + B * Q = C) :
    GDEN * FDEN * (D Q * H - Q * D H) + GDEN * FNUM * Q * H = GNUM * FDEN * H ^ 2 := by
  have hmul : FDEN * GDEN * (A * D Q + B * Q) = FDEN * GDEN * C := by rw [hred]
  have hkey : DN * (GDEN * FDEN * (D Q * H - Q * D H) + GDEN * FNUM * Q * H)
      = DN * (GNUM * FDEN * H ^ 2) := by
    have e1 : FDEN * GDEN * (A * D Q + B * Q)
        = GDEN * (A * D Q * FDEN) + GDEN * Q * (B * FDEN) := by ring
    have e2 : FDEN * GDEN * C = FDEN * (C * GDEN) := by ring
    rw [e1, e2, hB, hC, hA] at hmul
    linear_combination hmul
  exact mul_left_cancel₀ hDN hkey

/-- **The §6.2 special-denominator substitution expansion** (commutative-ring `Derivation` core): for a
special irreducible `p` with `D p = E·p` (the hyperexponential case `p = t`, `E = η ∈ k`), the
reconstruction `r = q·pᵏ` of the special-denominator stage expands by Leibniz as
`a·D(r) + b·r = (a·D(q) + b·q + k·a·E·q)·pᵏ`. Pure `Derivation.leibniz` + `Derivation.leibniz_pow`; the
algebraic heart of Bronstein's §6.2 special-denominator substitution (`r = q·h`, `h = p^{−n} = pᵏ`,
`k = −n ≥ 0`). -/
theorem specialDenominatorSubst_expand {R : Type*} [CommRing R] (D : Derivation ℤ R R)
    (a b p E q : R) (k : ℕ) (hDp : D p = E * p) :
    a * D (q * p ^ k) + b * (q * p ^ k)
      = (a * D q + b * q + (k : R) * (a * E) * q) * p ^ k := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, hDp]
  cases k with
  | zero => simp
  | succ k => simp only [Nat.add_sub_cancel, smul_eq_mul, Nat.cast_succ, pow_succ]; ring

/-- **The §6.2 special-denominator cleared identity from the reduced obligation** (commutative-ring
`Derivation` core): with `D p = E·p`, if the substitution's *reduced* identity
`a·D(q) + b·q + k·a·E·q = c` holds — the fact Bronstein's §6.2 valuation bookkeeping (Lemma 6.2.1/6.2.2,
the `ν_p`-exponent relations) supplies — then `r = q·pᵏ` solves `a·D(r) + b·r = c·pᵏ`. Isolates the single
missing §6.2 obligation (`hreduced`) from the otherwise-mechanical `Derivation` algebra; the hyperexp
analogue of how `rdeNormalDenominator_glue` discharges the normal-denominator stage from its reduced
`a·D(Q) + b·Q = c`. -/
theorem specialDenominatorSubst_cleared {R : Type*} [CommRing R] (D : Derivation ℤ R R)
    (a b c p E q : R) (k : ℕ) (hDp : D p = E * p)
    (hreduced : a * D q + b * q + (k : R) * (a * E) * q = c) :
    a * D (q * p ^ k) + b * (q * p ^ k) = c * p ^ k := by
  rw [specialDenominatorSubst_expand D a b p E q k hDp, hreduced]

namespace CPolyG

/-- **`cdvdG = true` reads as honest divisibility**: `cdvdG fuel g c = true` and `cnormG g ≠ []` give
`toPolyG g ∣ toPolyG c` (the zero remainder in the Euclidean identity `c = quo·g + rem`). -/
theorem dvd_of_cdvdG {α : Type*} [CField α] [CFieldSpec α] (fuel : ℕ) (g c : CPolyG α)
    (hg0 : cnormG g ≠ []) (hdvd : cdvdG fuel g c = true) :
    toPolyG g ∣ toPolyG c := by
  have hrem0 : toPolyG (cmodG fuel c g) = 0 := (cdvdG_iff fuel g c).mp hdvd
  have hid := toPolyG_cdivmodG' fuel c g hg0
  rw [show (cdivmodG fuel c g).2 = cmodG fuel c g from rfl, hrem0, add_zero] at hid
  rw [hid]
  exact Dvd.intro_left _ rfl

/-- Restatement: the fuel-free divisibility check reads as honest divisibility. -/
example {α : Type*} [CField α] [CFieldSpec α] (q p : CPolyG α)
    (hq : cnormG q ≠ []) (hdvd : cdvdGWf q p = true) :
    toPolyG q ∣ toPolyG p :=
  dvd_of_cdvdGWf q p hq hdvd

/-- Restatement: the fuel-free generic Diophantine solver satisfies the Bézout identity. -/
example {α : Type*} [CField α] [CFieldSpec α] (p q rhs : CPolyG α)
    (hq0 : cnormG q ≠ [])
    (hgdeg : (toPolyG (cgcdWf p q).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf p q).1 ≠ 0) :
    toPolyG (cdiophantineGWf p q rhs).1 * toPolyG p
        + toPolyG (cdiophantineGWf p q rhs).2 * toPolyG q = toPolyG rhs :=
  toPolyG_cdiophantineGWf p q rhs hq0 hgdeg hgne

end CPolyG

/-! ### Restatement + axiom audit for the §6.2 special-denominator substitution glue -/

-- ★ The §6.2 special-denominator substitution reaches `a·D(r)+b·r = c·pᵏ` from the reduced obligation
-- `a·D(q)+b·q+k·a·E·q = c` (the `ν_p`-bookkeeping fact), with `r = q·pᵏ` and `Dp = E·p`.
example {R : Type*} [CommRing R] (D : Derivation ℤ R R) (a b c p E q : R) (k : ℕ)
    (hDp : D p = E * p) (hreduced : a * D q + b * q + (k : R) * (a * E) * q = c) :
    a * D (q * p ^ k) + b * (q * p ^ k) = c * p ^ k :=
  specialDenominatorSubst_cleared D a b c p E q k hDp hreduced

#print axioms specialDenominatorSubst_expand
#print axioms specialDenominatorSubst_cleared

end DeepWiki.SymbolicIntegration
