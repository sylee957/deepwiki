import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Div
import Mathlib.FieldTheory.RatFunc.Basic
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms

/-! # The complete partial fraction decomposition (Bronstein §2.7, Theorem 2.7.1, structural core)
For `A, D ∈ K[x]` with `D` monic nonzero, `gcd(A,D)=1`, and a squarefree factorization
`D = ∏ᵢ Dᵢ^{eᵢ}` (the `Dᵢ` monic, pairwise coprime), the **complete** partial fraction decomposition is
`A/D = P + ∑ᵢ ∑_{j=1}^{eᵢ} Hᵢⱼ/Dᵢ^j` with `deg Hᵢⱼ < deg Dᵢ` and `P = A /ₘ D`.

This file formalizes the `K[x]`-level structural conclusion of Theorem 2.7.1. The substantive new
ingredient is the **base-`Dᵢ` (`Dᵢ`-adic) digit expansion** of the per-prime-power numerator `Bᵢ`:
writing `Bᵢ = ∑_{j<eᵢ} Cⱼ·Dᵢ^j` with `deg Cⱼ < deg Dᵢ` via repeated division by the monic `Dᵢ`, so
`Bᵢ/Dᵢ^{eᵢ} = ∑_{k=1}^{eᵢ} C_{eᵢ−k}/Dᵢ^k`. Composed with the multi-factor coprime split
`ratFunc_partialFraction_prod` this gives the full decomposition.

The over-the-closure form `Hᵢⱼ(α)/(x−α)ʲ` and the rational `Hᵢⱼ` *algorithm* (the differential-variable
Laurent-coefficient construction, eqs 2.10–2.12) are out of scope. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ## §2.7 The base-`g` (`g`-adic) digit expansion -/

/-- **Iterated division by a monic power** (§2.7): dividing by `g^(j+1)` is dividing by `g` then by `g^j`,
`B /ₘ g^(j+1) = (B /ₘ g) /ₘ g^j`, for monic `g`. Proved by the uniqueness of the monic division pair:
`B = r + g^(j+1)·q` with `q = (B /ₘ g) /ₘ g^j` and `r = B %ₘ g + g·((B /ₘ g) %ₘ g^j)`, `deg r < deg g^(j+1)`. -/
theorem divByMonic_pow_succ (B g : K[X]) (hg : g.Monic) (j : ℕ) :
    B /ₘ g ^ (j + 1) = (B /ₘ g) /ₘ g ^ j := by
  refine (div_modByMonic_unique (q := (B /ₘ g) /ₘ g ^ j)
    (r := B %ₘ g + g * ((B /ₘ g) %ₘ g ^ j)) (hg.pow _) ⟨?_, ?_⟩).1
  · -- reconstruction `r + g^(j+1)·q = B`
    have h1 : (B /ₘ g) %ₘ g ^ j + g ^ j * ((B /ₘ g) /ₘ g ^ j) = B /ₘ g := modByMonic_add_div _ _
    have h2 : B %ₘ g + g * (B /ₘ g) = B := modByMonic_add_div _ _
    calc B %ₘ g + g * ((B /ₘ g) %ₘ g ^ j) + g ^ (j + 1) * ((B /ₘ g) /ₘ g ^ j)
        = B %ₘ g + g * ((B /ₘ g) %ₘ g ^ j + g ^ j * ((B /ₘ g) /ₘ g ^ j)) := by
          rw [pow_succ, mul_comm (g ^ j) g, mul_assoc]; ring
      _ = B %ₘ g + g * (B /ₘ g) := by rw [h1]
      _ = B := h2
  · -- degree bound `deg r < deg g^(j+1)`
    have hgpow : (g ^ (j + 1)).natDegree = (j + 1) * g.natDegree := hg.natDegree_pow _
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
    · refine lt_of_lt_of_le (degree_modByMonic_lt _ hg) ?_
      rw [degree_eq_natDegree hg.ne_zero, degree_eq_natDegree (hg.pow _).ne_zero,
        Nat.cast_le, hgpow]
      exact Nat.le_mul_of_pos_left _ (by omega)
    · rcases eq_or_ne ((B /ₘ g) %ₘ g ^ j) 0 with h0 | h0
      · rw [h0, mul_zero, degree_zero]
        exact bot_lt_iff_ne_bot.2 (fun h => (hg.pow (j + 1)).ne_zero (degree_eq_bot.mp h))
      · rw [degree_mul, degree_eq_natDegree hg.ne_zero, degree_eq_natDegree h0,
          degree_eq_natDegree (hg.pow _).ne_zero, ← Nat.cast_add, Nat.cast_lt, hgpow]
        have : ((B /ₘ g) %ₘ g ^ j).natDegree < (g ^ j).natDegree :=
          natDegree_lt_natDegree h0 (degree_modByMonic_lt _ (hg.pow _))
        rw [hg.natDegree_pow] at this
        have : (j + 1) * g.natDegree = g.natDegree + j * g.natDegree := by ring
        omega

/-- **`g`-adic digit** (§2.7): the `j`-th digit of `B` in base `g` is `(B /ₘ g^j) %ₘ g` — repeatedly
strip the lowest digit `B %ₘ g` after dividing out `g^j`. For monic `g` of positive degree these are the
coefficients of the base-`g` expansion `B = ∑ⱼ (digit j)·g^j`. -/
noncomputable def baseDigit (B g : K[X]) (j : ℕ) : K[X] := (B /ₘ g ^ j) %ₘ g

/-- **Digits are proper** (§2.7): each base-`g` digit has `degree < degree g` for monic `g` of positive
degree — it is a remainder modulo `g`. -/
theorem degree_baseDigit_lt (B g : K[X]) (hg : g.Monic) (j : ℕ) :
    (baseDigit B g j).degree < g.degree :=
  degree_modByMonic_lt _ hg

/-- The zeroth digit is the remainder `baseDigit B g 0 = B %ₘ g`. -/
@[simp] theorem baseDigit_zero (B g : K[X]) : baseDigit B g 0 = B %ₘ g := by
  rw [baseDigit, pow_zero, divByMonic_one]

/-- Higher digits recurse through `B /ₘ g`: `baseDigit B g (j+1) = baseDigit (B /ₘ g) g j`. -/
theorem baseDigit_succ (B g : K[X]) (hg : g.Monic) (j : ℕ) :
    baseDigit B g (j + 1) = baseDigit (B /ₘ g) g j := by
  rw [baseDigit, baseDigit, divByMonic_pow_succ B g hg]

/-- **Base-`g` reconstruction** (§2.7, the digit expansion): for monic `g` of positive degree, any `B`
with `degree B < e·degree g` reconstructs from its first `e` base-`g` digits,
`B = ∑_{j<e} (baseDigit B g j)·g^j` — the polynomial analogue of base-`g` positional notation, by
repeated division (`B = B %ₘ g + g·(B /ₘ g)`). The degree hypothesis guarantees `e` digits suffice. -/
theorem baseDigit_reconstruction (g : K[X]) (hg : g.Monic) :
    ∀ (e : ℕ) (B : K[X]), B.degree < ((e * g.natDegree : ℕ) : WithBot ℕ) →
      B = ∑ j ∈ Finset.range e, baseDigit B g j * g ^ j := by
  intro e
  induction e with
  | zero =>
      intro B hB
      simp only [Finset.range_zero, Finset.sum_empty]
      rw [Nat.zero_mul, Nat.cast_zero] at hB
      exact degree_eq_bot.mp (by simpa using Nat.WithBot.lt_zero_iff.mp hB)
  | succ n ih =>
      intro B hB
      -- degree bound for the recursion target `B /ₘ g`
      have hdivdeg : (B /ₘ g).degree < ((n * g.natDegree : ℕ) : WithBot ℕ) := by
        rcases eq_or_ne (B /ₘ g) 0 with h0 | h0
        · rw [h0, degree_zero]; exact (WithBot.bot_lt_coe _)
        · rw [degree_eq_natDegree h0, natDegree_divByMonic _ hg, Nat.cast_lt]
          have hB0 : B ≠ 0 := by rintro rfl; simp at h0
          have hgleB : g.natDegree ≤ B.natDegree := by
            by_contra h
            push Not at h
            exact h0 ((divByMonic_eq_zero_iff hg).2 (by
              rw [degree_eq_natDegree hB0, degree_eq_natDegree hg.ne_zero, Nat.cast_lt]; exact h))
          have hBlt : B.natDegree < (n + 1) * g.natDegree := by
            rwa [degree_eq_natDegree hB0, Nat.cast_lt] at hB
          have : (n + 1) * g.natDegree = n * g.natDegree + g.natDegree := by ring
          omega
      -- split off the lowest digit and recurse
      have ih' := ih (B /ₘ g) hdivdeg
      have hsplit : B = B %ₘ g + g * (B /ₘ g) := (modByMonic_add_div B g).symm
      rw [Finset.sum_range_succ', baseDigit_zero, pow_zero, mul_one]
      conv_lhs => rw [hsplit]
      rw [add_comm]
      congr 1
      conv_lhs => rw [ih', Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [baseDigit_succ B g hg, pow_succ]
      ring

/-! ## §2.7 The `Dᵢ`-adic expansion of a single prime-power fraction `B/g^e` -/

/-- **`Dᵢ`-adic Laurent expansion of `B/g^e`** (§2.7, Theorem 2.7.1, the single-prime-power core): for
monic `g` of positive degree and `B` with `deg B < e·deg g`, the fraction `B/g^e` decomposes as
`B/g^e = ∑_{k=1}^{e} Hₖ/g^k` with `deg Hₖ < deg g`, where `Hₖ = baseDigit B g (e−k)` is the `(e−k)`-th
base-`g` digit of `B` — i.e. the digit expansion `B = ∑_{j<e} Cⱼ·g^j` rewritten with descending powers
`Cⱼ/g^{e−j}` (reindexed `k = e−j`). This is the partial fraction of one prime-power summand `Dᵢ^{eᵢ}`. -/
theorem ratFunc_DadicExpansion (g : K[X]) (hg : g.Monic) (e : ℕ) (B : K[X])
    (hB : B.degree < ((e * g.natDegree : ℕ) : WithBot ℕ)) :
    (algebraMap K[X] (RatFunc K) B) / (algebraMap K[X] (RatFunc K) g) ^ e
      = ∑ k ∈ Finset.Icc 1 e, algebraMap K[X] (RatFunc K) (baseDigit B g (e - k))
          / (algebraMap K[X] (RatFunc K) g) ^ k := by
  have hg0 : algebraMap K[X] (RatFunc K) g ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hg.ne_zero
  -- expand `B` into its base-`g` digits in the numerator only
  conv_lhs => rw [baseDigit_reconstruction g hg e B hB, map_sum, Finset.sum_div]
  -- reindex `Finset.range e` (digit index `j`) to `Finset.Icc 1 e` (power index `k = e − j`)
  refine Finset.sum_nbij' (fun j => e - j) (fun k => e - k) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_range] at hj; simp only [Finset.mem_Icc]; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_range]; omega
  · intro j hj; simp only [Finset.mem_range] at hj; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    -- the `j`-th digit summand `Cⱼ·g^j/g^e` equals `Cⱼ/g^{e-j}`, matched to `k = e-j`
    have hkj : e - (e - j) = j := by omega
    have hpow : (algebraMap K[X] (RatFunc K) g) ^ j * (algebraMap K[X] (RatFunc K) g) ^ (e - j)
        = (algebraMap K[X] (RatFunc K) g) ^ e := by rw [← pow_add]; congr 1; omega
    rw [hkj, map_mul, map_pow]
    rw [div_eq_div_iff (pow_ne_zero _ hg0) (pow_ne_zero _ hg0), mul_assoc, hpow]

end DeepWiki.SymbolicIntegration
