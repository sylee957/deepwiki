import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Div
import Mathlib.FieldTheory.RatFunc.Basic
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms

/-! # The complete partial fraction decomposition
The `K[x]`-level structural decomposition `A/D = P + ∑ᵢ ∑_{j=1}^{eᵢ} Hᵢⱼ/Dᵢ^j` (with
`deg Hᵢⱼ < deg Dᵢ`) for a squarefree factorization `D = ∏ᵢ Dᵢ^{eᵢ}`, built from the base-`g`
(`g`-adic) digit expansion of each prime-power numerator. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

/-! ## The base-`g` (`g`-adic) digit expansion -/

/-- Iterated division by a monic power: `B /ₘ g^(j+1) = (B /ₘ g) /ₘ g^j` for monic `g`. -/
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

/-- The `j`-th base-`g` digit of `B`: `(B /ₘ g^j) %ₘ g`, the coefficient of `g^j` in the
base-`g` expansion `B = ∑ⱼ (digit j)·g^j`. -/
noncomputable def baseDigit (B g : K[X]) (j : ℕ) : K[X] := (B /ₘ g ^ j) %ₘ g

/-- Each base-`g` digit is proper: `degree (baseDigit B g j) < degree g` for monic `g`. -/
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

/-- Base-`g` reconstruction: for monic `g` of positive degree and `degree B < e·degree g`,
`B = ∑_{j<e} (baseDigit B g j)·g^j`. -/
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

/-! ## The `g`-adic expansion of a single prime-power fraction `B/g^e` -/

/-- `g`-adic Laurent expansion of `B/g^e`: for monic `g` of positive degree and `deg B < e·deg g`,
`B/g^e = ∑_{k=1}^{e} Hₖ/g^k` with `Hₖ = baseDigit B g (e−k)` and `deg Hₖ < deg g`. -/
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

/-! ## The complete partial fraction decomposition (`K[x]`-level structure) -/

open Classical in
/-- The complete partial fraction decomposition: for a squarefree factorization `D = ∏ᵢ Dᵢ^{eᵢ}`
(the `Dᵢ` monic of positive degree, pairwise coprime, `eᵢ ≥ 1`), there is a polynomial part `P`
and proper numerators `Hᵢⱼ` (`deg Hᵢⱼ < deg Dᵢ`) with `A/D = P + ∑ᵢ ∑_{j=1}^{eᵢ} Hᵢⱼ/Dᵢ^j`. -/
theorem ratFunc_completePartialFraction {ι : Type*} (s : Finset ι) (D : ι → K[X]) (e : ι → ℕ)
    (hD : ∀ i ∈ s, (D i).Monic) (_hd : ∀ i ∈ s, 0 < (D i).natDegree) (_he : ∀ i ∈ s, 1 ≤ e i)
    (hcop : Set.Pairwise ↑s fun i j => IsCoprime (D i) (D j)) (A : K[X]) :
    ∃ (P : K[X]) (H : ι → ℕ → K[X]),
      (∀ i ∈ s, ∀ k, (H i k).degree < (D i).degree) ∧
        algebraMap K[X] (RatFunc K) A
            / ∏ i ∈ s, (algebraMap K[X] (RatFunc K) (D i)) ^ e i
          = algebraMap K[X] (RatFunc K) P
            + ∑ i ∈ s, ∑ k ∈ Finset.Icc 1 (e i),
                algebraMap K[X] (RatFunc K) (H i k) / (algebraMap K[X] (RatFunc K) (D i)) ^ k := by
  -- the squarefree factors as monic, pairwise-coprime powers `gᵢ = Dᵢ^{eᵢ}`
  have hgmonic : ∀ i ∈ s, ((D i) ^ e i).Monic := fun i hi => (hD i hi).pow _
  have hgcop : Set.Pairwise ↑s fun i j => IsCoprime ((D i) ^ e i) ((D j) ^ e j) :=
    fun i hi j hj hij => ((hcop hi hj hij).pow)
  -- Mathlib's degree-bounded partial fraction over the `gᵢ`
  obtain ⟨P, r, hrdeg, hPF⟩ :=
    div_prod_eq_quo_add_sum_rem_div (K := RatFunc K) A hgmonic hgcop
  refine ⟨P, fun i k => baseDigit (r i) (D i) (e i - k), fun i hi k => ?_, ?_⟩
  · exact degree_baseDigit_lt _ _ (hD i hi) _
  · -- Mathlib's split, then expand each prime-power summand `rᵢ/Dᵢ^{eᵢ}` via the `Dᵢ`-adic expansion
    simp only [Algebra.cast, map_pow] at hPF
    rw [hPF]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hri : (r i).degree < ((e i * (D i).natDegree : ℕ) : WithBot ℕ) := by
      have hlt := hrdeg i hi
      rwa [degree_pow, degree_eq_natDegree (hD i hi).ne_zero, nsmul_eq_mul, ← Nat.cast_mul] at hlt
    exact ratFunc_DadicExpansion (D i) (hD i hi) (e i) (r i) hri

end DeepWiki.SymbolicIntegration
