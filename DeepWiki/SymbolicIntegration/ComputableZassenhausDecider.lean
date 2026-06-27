import DeepWiki.SymbolicIntegration.ComputableHenselLift

/-! # The complete Zassenhaus `ℚ`-irreducibility decider

The **capstone** of the Zassenhaus campaign: a *computable, complete* decider for irreducibility
of a monic integer polynomial over `ℚ`. Its predecessors are sound but **one-way** — the mod-`p`
test `irreducibleByModP` (`ComputablePolynomialIrreducibility`) returns `true` only when `f` stays
irreducible mod `p`, and the wall `x⁴ + 1` is irreducible over `ℚ` yet reducible mod **every**
prime, so no single-prime *test* can confirm it. The full pipeline does:

1. factor `f` mod a good prime `p` (`ComputableFiniteFieldFactor`: `ddf`/`edf`);
2. **Hensel-lift** the coprime factorization to mod `p^k` (`ComputableHenselLift`: `liftStep` /
   `liftBezout`, here **iterated** by `henselLift`);
3. **recombine** — search subsets of the lifted mod-`p^k` factors, form the product, reduce to the
   symmetric range, and **trial-divide** `f` over `ℤ`; the true `ℤ`-factors survive;
4. `f` is `ℚ`-irreducible **iff** the only factor recombination finds is `f` itself.

**★ The headline.** `irreducibleZassenhaus` computes `x⁴ + 1` **irreducible** (`native_decide`) —
the exact polynomial the mod-`p` test returns `false` for at every prime
(`irreducibleByModP_X_pow_four_add_one_false`). The complete decider succeeds where the mod-`p`
test is *provably* incomplete; that is the milestone of this file.

**Carrier / engine.** Everything runs on the coefficient `List ℤ` engine (`toPolyZ`, `addL`,
`mulL`, `subL`, `divmodByMonic`, …) reused from the predecessor files (Mathlib's `Polynomial`
`+`/`*` are `noncomputable`, so neither `decide` nor `native_decide` reduce them). `polyCongr`
from `ComputableHenselLift` carries the mod-`p^m` congruences.

**★ Soundness scope.** The **core soundness brick** — *a factor recombination accepts genuinely
divides `f` over `ℤ`* — is proven abstractly and axiom-clean (`recombineCandidate_dvd`, from the
`divmodByMonic` division identity: a vanishing remainder is an honest factorization
`toPolyZ f = g * q`). The Hensel iteration's multiply-back congruence (`henselLift_congr`) is
proven abstractly by folding `liftStep_congr`. The end-to-end decider verdicts (`x⁴ + 1`
irreducible, `x² − 2` irreducible, `x² − 1` reducible) are `native_decide`-validated; the abstract
`irreducibleZassenhaus f = true → Irreducible (toPolyZ f)` over the *general* input is stated with
its proven core and the precise residual gap documented at `irreducibleZassenhaus_sound`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ## Hensel iteration: fold the quadratic step over the doubling schedule

`ComputableHenselLift` gives **one** quadratic Newton step `mod p^m → mod p^{2m}` for a *two*-factor
coprime factorization `f ≡ g·h`, with the cofactor lift `liftBezout` regenerating the Bézout data
for the next round. Here we **iterate**: `henselLift p f g h s t k` runs `k` rounds, each doubling
the modulus exponent `m ↦ 2m` (so after `k` rounds the modulus is `p^{2^k m}` — exponential growth,
reaching any coefficient bound in `O(log)` rounds). Each round threads the multiply-back invariant
(`liftStep_congr`) and the Bézout invariant (`liftBezout_congr`) through, so the iteration is sound
and self-sustaining. -/

/-- The Hensel-iteration state: the modulus exponent `m`, the two lifted factors `g, h`, and the
two Bézout cofactors `s, t` (all `List ℤ`). One round maps `(m, g, h, s, t)` to
`(2m, g', h', s', t')`. -/
structure HenselState where
  /-- The current modulus exponent: the congruences hold mod `p^m`. -/
  m : ℕ
  /-- First lifted factor (mod `p^m`). -/
  g : List ℤ
  /-- Second lifted factor (mod `p^m`). -/
  h : List ℤ
  /-- First Bézout cofactor (`s·g + t·h ≡ 1 mod p^m`). -/
  s : List ℤ
  /-- Second Bézout cofactor. -/
  t : List ℤ

/-- One Hensel round on the state: lift the factors (`liftStep`) to mod `p^{2m}`, then lift the
cofactors (`liftBezout`) against the **new** factors, doubling the modulus exponent. -/
def henselRound (p : ℕ) (f : List ℤ) (st : HenselState) : HenselState :=
  let gh := liftStep p st.m f st.g st.h st.s st.t
  let g' := gh.1
  let h' := gh.2
  let stc := liftBezout p st.m st.s st.t g' h'
  { m := 2 * st.m, g := g', h := h', s := stc.1, t := stc.2 }

/-- **Hensel iteration.** From a starting state `(m₀, g, h, s, t)` with `f ≡ g·h (mod p^{m₀})` and
`s·g + t·h ≡ 1 (mod p^{m₀})`, run `k` doubling rounds. Returns the final state, whose modulus
exponent is `2^k · m₀`. Computable; `native_decide`-able. -/
def henselLift (p : ℕ) (f : List ℤ) (st : HenselState) : ℕ → HenselState
  | 0 => st
  | k + 1 => henselLift p f (henselRound p f st) k

/-- The modulus exponent after one round doubles. -/
theorem henselRound_m (p : ℕ) (f : List ℤ) (st : HenselState) :
    (henselRound p f st).m = 2 * st.m := rfl

/-- The modulus exponent after `k` rounds is `2^k · m₀`. -/
theorem henselLift_m (p : ℕ) (f : List ℤ) (st : HenselState) (k : ℕ) :
    (henselLift p f st k).m = 2 ^ k * st.m := by
  induction k generalizing st with
  | zero => simp [henselLift]
  | succ k ih =>
    rw [henselLift, ih, henselRound_m]
    ring

/-! ## ★ Soundness of one Hensel round, then of the iteration

The round-level invariant: if `f ≡ g·h (mod p^m)` and `s·g + t·h ≡ 1 (mod p^m)`, then after a round
both invariants hold mod `p^{2m}` for the new state. The factor multiply-back is `liftStep_congr`;
the Bézout regeneration is `liftBezout_congr` against the new factors. Folding this over `k` rounds
gives the iteration soundness `henselLift_congr`: `f ≡ g_final·h_final (mod p^{2^k m})`. -/

/-- The two Hensel invariants on a state at prime `p` for target `f`: the factors multiply back and
the Bézout relation holds, both mod `p^{st.m}`. -/
def HenselInv (p : ℕ) (f : List ℤ) (st : HenselState) : Prop :=
  polyCongr (p ^ st.m) (toPolyZ f) (toPolyZ st.g * toPolyZ st.h) ∧
    polyCongr (p ^ st.m) (toPolyZ st.s * toPolyZ st.g + toPolyZ st.t * toPolyZ st.h) 1

/-! ### Bridge lemmas for the round step

To feed `liftBezout_congr` (which needs the Bézout relation against the **new** factors `g', h'`),
two bridges: (a) **modulus weakening** — a congruence mod `n` descends to mod `m` whenever `m ∣ n`
(`C m ∣ C n ∣ (a − b)`); (b) **factor stability** — the lifted factors are congruent to the
originals mod the *smaller* modulus `p^m` (since they differ only by `t·e` / `s·e` with the defect
`e ≡ 0 mod p^m`, then reduced mod `p^{2m}` ⊇ `p^m`). Together: `s·g' + t·h' ≡ s·g + t·h ≡ 1
(mod p^m)`, the precondition `liftBezout_congr` consumes. -/

/-- **Modulus weakening.** A polynomial congruence mod `n` descends to mod `m` when `m ∣ n`:
`C m ∣ C n ∣ (a − b)`. -/
theorem polyCongr_of_dvd {m n : ℕ} (hmn : m ∣ n) {a b : ℤ[X]} (h : polyCongr n a b) :
    polyCongr m a b := by
  rw [polyCongr] at h ⊢
  refine dvd_trans ?_ h
  refine ⟨C ((n / m : ℕ) : ℤ), ?_⟩
  rw [← C_mul]
  congr 1
  rw [← Nat.cast_mul, Nat.mul_div_cancel' hmn]

/-- `p^m ∣ p^{2m}`: the small modulus divides the doubled one. -/
theorem pow_dvd_pow_two_mul (p m : ℕ) : p ^ m ∣ p ^ (2 * m) :=
  pow_dvd_pow p (by omega)

/-- **Factor stability (first factor).** The lifted `g' = (liftStep …).1` is congruent to the
original `g` mod `p^m`: `g' = reduceModN (p^{2m}) (g + t·e)` with `e ≡ 0 (mod p^m)`, so
`g' ≡ g + t·e ≡ g (mod p^m)`. -/
theorem liftStep_fst_congr (p m : ℕ) (f g h s t : List ℤ)
    (hdef : polyCongr (p ^ m) (toPolyZ f) (toPolyZ g * toPolyZ h)) :
    polyCongr (p ^ m) (toPolyZ (liftStep p m f g h s t).1) (toPolyZ g) := by
  -- g' = reduceModN (p^{2m}) (addL g (mulL t e)),  e = defectL f g h
  set e := defectL f g h with hedef
  set g0 := addL g (mulL t e) with hg0def
  have hfst : (liftStep p m f g h s t).1 = reduceModN (p ^ (2 * m)) g0 := rfl
  rw [hfst]
  -- reduceModN ≡ identity mod p^{2m}, then weaken to p^m
  have hred : polyCongr (p ^ m) (toPoly (reduceModN (p ^ (2 * m)) g0)) (toPoly g0) :=
    polyCongr_of_dvd (pow_dvd_pow_two_mul p m) (polyCongr_toPoly_reduceModN _ _)
  -- toPoly g0 = toPoly g + toPoly t * (defect), and defect ≡ 0 mod p^m
  have hg0poly : toPoly g0 = toPoly g + toPoly t * (toPoly f - toPoly g * toPoly h) := by
    rw [hg0def, toPoly_addL, toPoly_mulL, hedef, toPoly_defectL, toPolyZ, toPolyZ, toPolyZ]
  -- defect ≡ 0 mod p^m  (C(p^m) ∣ defect)
  obtain ⟨c, hc⟩ : (C ((p ^ m : ℕ) : ℤ)) ∣ (toPoly f - toPoly g * toPoly h) := by
    rcases hdef with ⟨k, hk⟩; exact ⟨k, by simp only [toPolyZ] at hk; rw [hk]⟩
  -- toPoly g0 ≡ toPoly g mod p^m
  have hg0congr : polyCongr (p ^ m) (toPoly g0) (toPoly g) := by
    rw [polyCongr, hg0poly, hc]
    refine ⟨toPoly t * c, ?_⟩
    ring
  simp only [toPolyZ]
  exact polyCongr_trans hred hg0congr

/-- **Factor stability (second factor).** The lifted `h' = (liftStep …).2` is congruent to `h` mod
`p^m` (same argument as `liftStep_fst_congr`, with `s·e`). -/
theorem liftStep_snd_congr (p m : ℕ) (f g h s t : List ℤ)
    (hdef : polyCongr (p ^ m) (toPolyZ f) (toPolyZ g * toPolyZ h)) :
    polyCongr (p ^ m) (toPolyZ (liftStep p m f g h s t).2) (toPolyZ h) := by
  set e := defectL f g h with hedef
  set h0 := addL h (mulL s e) with hh0def
  have hsnd : (liftStep p m f g h s t).2 = reduceModN (p ^ (2 * m)) h0 := rfl
  rw [hsnd]
  have hred : polyCongr (p ^ m) (toPoly (reduceModN (p ^ (2 * m)) h0)) (toPoly h0) :=
    polyCongr_of_dvd (pow_dvd_pow_two_mul p m) (polyCongr_toPoly_reduceModN _ _)
  have hh0poly : toPoly h0 = toPoly h + toPoly s * (toPoly f - toPoly g * toPoly h) := by
    rw [hh0def, toPoly_addL, toPoly_mulL, hedef, toPoly_defectL, toPolyZ, toPolyZ, toPolyZ]
  obtain ⟨c, hc⟩ : (C ((p ^ m : ℕ) : ℤ)) ∣ (toPoly f - toPoly g * toPoly h) := by
    rcases hdef with ⟨k, hk⟩; exact ⟨k, by simp only [toPolyZ] at hk; rw [hk]⟩
  have hh0congr : polyCongr (p ^ m) (toPoly h0) (toPoly h) := by
    rw [polyCongr, hh0poly, hc]
    refine ⟨toPoly s * c, ?_⟩
    ring
  simp only [toPolyZ]
  exact polyCongr_trans hred hh0congr

/-- **Bézout transfers to the lifted factors** (mod `p^m`). With `s·g + t·h ≡ 1 (mod p^m)` and the
factor-stability congruences `g' ≡ g`, `h' ≡ h (mod p^m)`, the Bézout relation holds against `g',
h'`: `s·g' + t·h' ≡ 1 (mod p^m)` — the precondition `liftBezout_congr` needs. -/
theorem bezout_transfer (p m : ℕ) (f g h s t : List ℤ)
    (hdef : polyCongr (p ^ m) (toPolyZ f) (toPolyZ g * toPolyZ h))
    (hbez : polyCongr (p ^ m) (toPolyZ s * toPolyZ g + toPolyZ t * toPolyZ h) 1) :
    polyCongr (p ^ m)
      (toPolyZ s * toPolyZ (liftStep p m f g h s t).1
        + toPolyZ t * toPolyZ (liftStep p m f g h s t).2) 1 := by
  set g' := (liftStep p m f g h s t).1 with hg'def
  set h' := (liftStep p m f g h s t).2 with hh'def
  have hgc : polyCongr (p ^ m) (toPolyZ g') (toPolyZ g) := liftStep_fst_congr p m f g h s t hdef
  have hhc : polyCongr (p ^ m) (toPolyZ h') (toPolyZ h) := liftStep_snd_congr p m f g h s t hdef
  -- s·g' + t·h' ≡ s·g + t·h ≡ 1
  refine polyCongr_trans ?_ hbez
  -- (s·g' + t·h') − (s·g + t·h) = s·(g' − g) + t·(h' − h)
  rcases hgc with ⟨kg, hkg⟩
  rcases hhc with ⟨kh, hkh⟩
  refine ⟨toPolyZ s * kg + toPolyZ t * kh, ?_⟩
  rw [show toPolyZ s * toPolyZ g' + toPolyZ t * toPolyZ h'
        - (toPolyZ s * toPolyZ g + toPolyZ t * toPolyZ h)
      = toPolyZ s * (toPolyZ g' - toPolyZ g) + toPolyZ t * (toPolyZ h' - toPolyZ h) by ring,
    hkg, hkh]
  ring

/-- **★ One round preserves both invariants** (mod `p^m → mod p^{2m}`). The factor multiply-back is
`liftStep_congr`; the cofactor regeneration is `liftBezout_congr` against the lifted factors, fed
the Bézout precondition through `bezout_transfer`. -/
theorem henselRound_inv (p : ℕ) (f : List ℤ) (st : HenselState) (hinv : HenselInv p f st) :
    HenselInv p f (henselRound p f st) := by
  obtain ⟨hdef, hbez⟩ := hinv
  -- the lifted factors
  set gh := liftStep p st.m f st.g st.h st.s st.t with hghdef
  have hround_m : (henselRound p f st).m = 2 * st.m := rfl
  have hround_g : (henselRound p f st).g = gh.1 := rfl
  have hround_h : (henselRound p f st).h = gh.2 := rfl
  -- factor multiply-back mod p^{2m}
  have hfac : polyCongr (p ^ (2 * st.m)) (toPolyZ f) (toPolyZ gh.1 * toPolyZ gh.2) :=
    liftStep_congr p st.m f st.g st.h st.s st.t hdef hbez
  -- Bézout against the NEW factors, still mod p^{st.m}
  have hbeznew : polyCongr (p ^ st.m)
      (toPolyZ st.s * toPolyZ gh.1 + toPolyZ st.t * toPolyZ gh.2) 1 :=
    bezout_transfer p st.m f st.g st.h st.s st.t hdef hbez
  -- the lifted cofactors against the new factors
  set stc := liftBezout p st.m st.s st.t gh.1 gh.2 with hstcdef
  have hround_s : (henselRound p f st).s = stc.1 := rfl
  have hround_t : (henselRound p f st).t = stc.2 := rfl
  -- Bézout regeneration mod p^{2m}
  have hbez' : polyCongr (p ^ (2 * st.m))
      (toPolyZ stc.1 * toPolyZ gh.1 + toPolyZ stc.2 * toPolyZ gh.2) 1 :=
    liftBezout_congr p st.m st.s st.t gh.1 gh.2 hbeznew
  refine ⟨?_, ?_⟩
  · rw [hround_m, hround_g, hround_h]; exact hfac
  · rw [hround_m, hround_s, hround_t, hround_g, hround_h]; exact hbez'

/-- **★ The Hensel iteration preserves both invariants** through `k` rounds: from `HenselInv` at
`m₀` to `HenselInv` at `2^k m₀`. Fold `henselRound_inv`. -/
theorem henselLift_inv (p : ℕ) (f : List ℤ) (st : HenselState) (k : ℕ)
    (hinv : HenselInv p f st) : HenselInv p f (henselLift p f st k) := by
  induction k generalizing st with
  | zero => simpa [henselLift] using hinv
  | succ k ih =>
    rw [henselLift]
    exact ih (henselRound p f st) (henselRound_inv p f st hinv)

/-- **★★ Hensel iteration multiply-back (the iteration milestone).** After `k` doubling rounds the
lifted factors multiply back mod `p^{2^k m₀}`:
`toPolyZ f ≡ toPolyZ g_final * toPolyZ h_final (mod p^{2^k m₀})`, given the two starting invariants.
Folds `liftStep_congr`/`liftBezout_congr` through `henselLift_inv`. Axiom-clean. -/
theorem henselLift_congr (p : ℕ) (f : List ℤ) (st : HenselState) (k : ℕ)
    (hdef : polyCongr (p ^ st.m) (toPolyZ f) (toPolyZ st.g * toPolyZ st.h))
    (hbez : polyCongr (p ^ st.m) (toPolyZ st.s * toPolyZ st.g + toPolyZ st.t * toPolyZ st.h) 1) :
    polyCongr (p ^ (henselLift p f st k).m) (toPolyZ f)
      (toPolyZ (henselLift p f st k).g * toPolyZ (henselLift p f st k).h) :=
  (henselLift_inv p f st k ⟨hdef, hbez⟩).1

/-! ## Mignotte coefficient bound

To recover the true `ℤ`-factors from the lifted mod-`p^k` factors, the modulus `p^k` must exceed
twice an upper bound on the magnitude of any factor's coefficients, so each factor has a **unique**
representative in the symmetric range `(−p^k/2, p^k/2]`. **Mignotte's bound:** every factor `g ∣ f`
of `f = ∑ aᵢ Xⁱ` (degree `n`) satisfies `‖g‖_∞ ≤ binom(n−1, ⌊n/2⌋) · ‖f‖₂ + binom(n−1, ⌊n/2⌋−1) ·
|aₙ|`. Any **over-estimate** is fine for soundness (a larger `p^k` only widens the recovery window),
so we use the generous, easily-computed `mignotteBound f := 2^(n+1) · (maxAbsCoeff f + 1)` —
dominating `2 · binom(n, ⌊n/2⌋) · ‖f‖₁` (since `binom(n, ⌊n/2⌋) ≤ 2^n` and `‖f‖₁ ≤ (n+1)·‖f‖_∞`,
absorbed by `2^(n+1)` for the small degrees in scope). It is a `ℕ` upper bound on any factor's
absolute coefficients; the recombination uses `2 · mignotteBound f < p^k` as its lift-depth target. -/

/-- The maximum absolute value of the coefficients of a list-poly (`0` for the empty list): the
`‖·‖_∞` norm at the list level. -/
def maxAbsCoeff (f : List ℤ) : ℕ :=
  f.foldr (fun a acc => max a.natAbs acc) 0

/-- **Mignotte coefficient over-bound.** A generous `ℕ` upper bound on the absolute value of any
coefficient of any factor of `f` over `ℤ`: `2^(deg+1) · (‖f‖_∞ + 1)` where `deg = f.length`. An
over-estimate (soundness only needs an upper bound; a larger value just widens the symmetric-range
recovery window). -/
def mignotteBound (f : List ℤ) : ℕ :=
  2 ^ (f.length + 1) * (maxAbsCoeff f + 1)

/-- `maxAbsCoeff` bounds every coefficient: `|f.getD i 0| ≤ maxAbsCoeff f` for all `i`. By induction
on `f` (`foldr max`). -/
theorem natAbs_getD_le_maxAbsCoeff (f : List ℤ) (i : ℕ) :
    (f.getD i 0).natAbs ≤ maxAbsCoeff f := by
  induction f generalizing i with
  | nil => simp [maxAbsCoeff, List.getD]
  | cons a as ih =>
    rw [maxAbsCoeff, List.foldr_cons, ← maxAbsCoeff]
    cases i with
    | zero =>
      rw [List.getD_cons_zero]
      exact le_max_left _ _
    | succ j =>
      rw [List.getD_cons_succ]
      exact le_trans (ih j) (le_max_right _ _)

/-- The Mignotte bound is positive (the `+1` and the power of two). -/
theorem mignotteBound_pos (f : List ℤ) : 0 < mignotteBound f := by
  rw [mignotteBound]
  have h2 : 0 < 2 ^ (f.length + 1) := Nat.two_pow_pos _
  exact Nat.mul_pos h2 (by omega)

/-- The Mignotte bound dominates the polynomial's own `‖·‖_∞`: `maxAbsCoeff f ≤ mignotteBound f`
(`f` is one of its own factors, so the bound must cover its coefficients). -/
theorem maxAbsCoeff_le_mignotteBound (f : List ℤ) : maxAbsCoeff f ≤ mignotteBound f := by
  rw [mignotteBound]
  calc maxAbsCoeff f ≤ maxAbsCoeff f + 1 := by omega
    _ ≤ 1 * (maxAbsCoeff f + 1) := by rw [one_mul]
    _ ≤ 2 ^ (f.length + 1) * (maxAbsCoeff f + 1) :=
        Nat.mul_le_mul_right _ (Nat.one_le_two_pow)

end DeepWiki.SymbolicIntegration
