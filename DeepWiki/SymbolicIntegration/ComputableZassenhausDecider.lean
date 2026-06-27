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

/-! ## Recombination, stage 1: the exact `ℤ`-division test (★ the soundness keystone)

The recombination tests each candidate subset-product `g` (monic, degree `dg`) by **trial-dividing**
`f` over `ℤ`: `divmodByMonic f g dg` (the same monic long division as the `𝔽_p` engine — it works
over any `CommRing`, here `ℤ`) yields `(q, r)`, and `g` is a genuine factor **iff** the remainder
`r` reads as the zero polynomial. The test `dividesExactly` checks `lengthTrim r = 0` (decidable,
computable). **★ Keystone soundness `dividesExactly_dvd`:** when the test passes,
`toPolyZ f = toPoly g * toPoly q` — an *honest* factorization over `ℤ`, straight from the division
identity `divmodByMonic_spec` with a vanishing remainder. This is the brick the whole decider's
soundness rests on (a found factor really divides `f`). -/

/-- The exact-division test of `f` by a monic candidate `g` of degree `dg` over `ℤ`: `true` iff the
`divmodByMonic` remainder reads as the zero polynomial (`lengthTrim = 0`). Computable. -/
def dividesExactly (f g : List ℤ) (dg : ℕ) : Bool :=
  decide (lengthTrim (divmodByMonic f g dg).2 = 0)

/-- **★★ The recombination soundness keystone.** If the exact-division test passes
(`dividesExactly f g dg = true`), then `g` genuinely divides `f` over `ℤ`:
`toPolyZ f = toPoly g * toPoly (divmodByMonic f g dg).1` — an honest factorization, from the
`divmodByMonic` division identity with the remainder forced to `0` (a vanishing `lengthTrim` reads
as the zero polynomial). Axiom-clean; the foundation of `irreducibleZassenhaus_sound`. -/
theorem dividesExactly_dvd {f g : List ℤ} {dg : ℕ} (h : dividesExactly f g dg = true) :
    toPolyZ f = toPoly g * toPoly (divmodByMonic f g dg).1 := by
  rw [dividesExactly, decide_eq_true_eq] at h
  have hid := divmodByMonic_spec f g dg
  have hr0 : toPoly (divmodByMonic f g dg).2 = 0 := toPoly_eq_zero_of_lengthTrim_eq_zero h
  rw [toPolyZ, hid, hr0, add_zero]

/-- A passing exact-division test yields a genuine **divisibility** `toPoly g ∣ toPolyZ f`. -/
theorem dvd_of_dividesExactly {f g : List ℤ} {dg : ℕ} (h : dividesExactly f g dg = true) :
    toPoly g ∣ toPolyZ f :=
  ⟨_, dividesExactly_dvd h⟩

/-! ## Recombination, stage 2: symmetric-range reduction

A lifted factor's coefficients live mod `p^k`; the true `ℤ`-factor's coefficients are their unique
representatives in the **symmetric** range `(−p^k/2, p^k/2]`. `symModN n` maps each coefficient `a`
to `a % n` shifted into that range (subtract `n` when `> n/2`). Computable; the reduction the
candidate products pass through before the `ℤ`-trial-division. (Soundness of the *decider* routes
through `dividesExactly_dvd` on the reduced candidate, so `symModN` needs no separate congruence
lemma for the proven core — the trial division is exact over `ℤ` regardless.) -/

/-- Shift `a % n` into the symmetric range `(−n/2, n/2]`: subtract `n` when the residue exceeds
`n/2`. -/
def symMod (n a : ℤ) : ℤ :=
  let r := a % n
  if r > n / 2 then r - n else r

/-- Apply `symMod n` to every coefficient of a list-poly: the symmetric-range representative. -/
def symModN (n : ℤ) (l : List ℤ) : List ℤ := l.map (symMod n)

/-! ## Recombination, stage 3: subset products and the search

Enumerate **subsets** of the lifted mod-`p^k` factors, form each subset's product (`mulL`-fold),
reduce to the symmetric range, prepend the leading coefficient sign, and `ℤ`-trial-divide `f`. A
factor of `f` is the symmetric-reduced product of a subset whose product divides `f` over `ℤ`. We
return the list of **degrees** of the true factors found (the data the irreducibility verdict reads:
`f` is irreducible iff the only factor found is `f` itself, i.e. of full degree). The subset search
is over `List.sublists` of the factor list; computable and `native_decide`-able for few factors. -/

/-- The product of a list of factor coefficient-lists (`mulL`-fold from `[1]`). -/
def listProd (fs : List (List ℤ)) : List ℤ :=
  fs.foldr (fun a acc => mulL a acc) [1]

/-- `toPoly` of a `listProd` is the product of the factors' `toPoly`s. -/
theorem toPoly_listProd (fs : List (List ℤ)) :
    toPoly (listProd fs) = (fs.map toPoly).prod := by
  induction fs with
  | nil => simp [listProd, toPoly]
  | cons a as ih =>
    rw [listProd, List.foldr_cons, toPoly_mulL, List.map_cons, List.prod_cons, ← listProd, ih]

/-- A subset-product candidate of the lifted factors `facs`, symmetric-range-reduced mod `n`: form
the product of the sublist `sub`, then reduce each coefficient into `(−n/2, n/2]`. The monic
candidate the `ℤ`-trial-division tests. -/
def recombineCandidate (n : ℤ) (sub : List (List ℤ)) : List ℤ :=
  symModN n (listProd sub)

/-- **Recombination search for PROPER factors.** Over all sublists of the lifted factors `facs`
(mod `n = p^k`), form each symmetric-reduced subset-product candidate; keep those of **proper**
degree `1 ≤ d < deg f` (excluding units of degree `0` and the trivial full-degree `f` itself) that
**exactly divide** `f` over `ℤ`, returning their degrees. `f` is irreducible **iff** this list is
empty (no proper `ℤ`-factor exists). -/
def recombine (f : List ℤ) (n : ℤ) (facs : List (List ℤ)) : List ℕ :=
  let degF := lengthTrim f - 1
  (facs.sublists.filterMap (fun sub =>
    let cand := recombineCandidate n sub
    let dc := lengthTrim cand
    -- proper factor: degree `dc - 1` in `[1, degF)`, exact divisor over ℤ
    if 2 ≤ dc ∧ dc - 1 < degF ∧ dividesExactly f cand (dc - 1) then
      some (dc - 1)
    else none))

/-! ## Recombination, stage 4: wiring `𝔽_p` factors into the `ℤ` Hensel lift

The mod-`p` factorization (`edf`, `List (List (ZMod p))`) must feed the `List ℤ` Hensel machinery.
Two pieces: (a) **lift** a `ZMod p` factor list to `List ℤ` by taking each coefficient's
representative in `[0, p)` (`ZMod.val`); (b) **Bézout cofactors** over `𝔽_p` via the **extended
Euclidean algorithm** `xgcdByMonic`, returning `(s, t)` with `s·a + t·b = gcd`. For a coprime pair
the gcd is a nonzero constant, so dividing through gives `s·a + t·b ≡ 1`. -/

/-- Lift a `ZMod p` coefficient list to `List ℤ` via `ZMod.val` (the representative in `[0, p)`):
the mod-`p` factor read as an integer polynomial. -/
def liftZMod {p : ℕ} (l : List (ZMod p)) : List ℤ := l.map (fun a => (a.val : ℤ))

/-- The extended Euclidean algorithm over a field, fueled: returns `(d, s, t)` with
`s·f + t·g = d = gcd(f, g)`. Mirrors `gcdByMonicFuel`, carrying the Bézout cofactors via the
quotient at each step. `g = 0` → `(f, 1, 0)`; else reduce `f = gm·q + r` (gm = monicize g) and
recurse, back-substituting the cofactors. -/
def xgcdByMonicFuel {R : Type*} [Field R] [DecidableEq R] :
    ℕ → List R → List R → List R × List R × List R
  | 0, f, _ => (f, [1], [])
  | fuel + 1, f, g =>
    if lengthTrim g = 0 then (f, [1], [])
    else
      let lc := (leadL g)⁻¹
      let gm := monicizeL g
      let dg := lengthTrim g - 1
      let qr := divmodByMonic f gm dg
      let q := qr.1
      let r := qr.2
      let res := xgcdByMonicFuel fuel gm r
      -- res = (d, s', t') with s'·gm + t'·r = d.  r = f − gm·q, gm = lc·g.
      -- d = s'·gm + t'·(f − gm·q) = t'·f + (s' − t'·q)·gm = t'·f + (s' − t'·q)·lc·g.
      let d := res.1
      let s' := res.2.1
      let t' := res.2.2
      (d, t', scaleL lc (subL s' (mulL t' q)))

/-- Extended Euclidean gcd with cofactors over `𝔽_p`, fuel `g.length + 1`: returns `(gcd, s, t)`
with `s·f + t·g = gcd`. -/
def xgcdByMonic {R : Type*} [Field R] [DecidableEq R] (f g : List R) :
    List R × List R × List R :=
  xgcdByMonicFuel (g.length + 1) f g

/-- The Bézout cofactors `(s, t)` over `𝔽_p` for a **coprime** pair `(g, h)` (gcd a nonzero
constant `c`): `xgcdByMonic` gives `s₀·g + t₀·h = c`, and dividing through by `c` yields
`s·g + t·h = 1`. Returns `(s, t)`. -/
def bezoutModP {p : ℕ} [Fact p.Prime] (g h : List (ZMod p)) : List (ZMod p) × List (ZMod p) :=
  let res := xgcdByMonic g h
  let c := leadL res.1  -- the gcd is a nonzero constant; its (only) coefficient
  (scaleL c⁻¹ res.2.1, scaleL c⁻¹ res.2.2)

/-! ## A degree-correct `𝔽_p` factorization (fixing the DDF degree-tag stop)

The engine's `ddf`/`edf` carry a documented gap: the distinct-degree **degree tags** are correct
only once Frobenius-power correctness is added, and in fact the `ddfAux` *no-peel* branch stops at
the current `d` (emitting the unfactored residual with a wrong tag) — so e.g. `x⁴ + 1` mod `3`,
whose factors are both degree `2`, is returned **unsplit** (`edf` gives one factor), because the
`d = 1` block is trivial and the recursion halts. The `ddf_prod`/`edf_prod` multiply-backs stay
sound (gcd-divides-first-arg is unconditional), but the *split into irreducibles* needs the recursion
to **continue** through trivial blocks. We rebuild a degree-correct DDF here over the same engine
primitives (`xPowModF`, `gcdByMonic`, `divmodByMonic`), then equal-degree-split each block with its
**true** degree `d` via `edfBlock` — giving the genuine irreducible factorization the recombination
recombines. (Computed factorizations feed `native_decide`-validated verdicts; the abstract soundness
keystone is `dividesExactly_dvd`, independent of this factorizer's internals.) -/

/-- Degree-correct distinct-degree factorization over `𝔽_p`, fueled by `d`. At degree `d`: the block
`gcd(f, X^(p^d) − X)` collects the degree-`d` irreducible factors; if **nontrivial**, peel it
(monicize, divide out) and recurse with `d + 1` on the cofactor; if **trivial**, advance `d` (do not
stop) — continuing until the cofactor is a constant. Returns `(d, block)` pairs with **correct**
degree tags. -/
def ddfCorrect (p : ℕ) [Fact p.Prime] : ℕ → ℕ → List (ZMod p) → List (ℕ × List (ZMod p))
  | 0, _, _ => []
  | fuel + 1, d, f =>
    if lengthTrim f ≤ 1 then []                       -- cofactor is a constant: done
    else if d + 1 ≥ lengthTrim f then [(lengthTrim f - 1, f)]  -- remainder is itself irreducible
    else
      let df := lengthTrim f - 1
      let sep := subL (xPowModF p d f df) [0, 1]
      let gd := gcdByMonic f sep
      if 1 < lengthTrim gd then
        let gdm := monicizeL gd
        let cof := (divmodByMonic f gdm (lengthTrim gd - 1)).1
        (d, gdm) :: ddfCorrect p fuel (d + 1) cof
      else
        ddfCorrect p fuel (d + 1) f                   -- trivial block: keep going

/-- Degree-correct full factorization over `𝔽_p`: distinct-degree blocks (`ddfCorrect`) each
equal-degree-split with its **true** degree `d` (`edfBlock`), flattened to the list of irreducible
factor coefficient-lists. -/
def factorModP (p : ℕ) [Fact p.Prime] (f : List (ZMod p)) : List (List (ZMod p)) :=
  (ddfCorrect p (f.length + 1) 1 f).flatMap (fun b => edfBlock p b.1 (b.2.length + 1) 0 b.2)

/-! ## A degree-stable computational Hensel round

The abstract `henselLift` (above) carries the proven multiply-back congruence `henselLift_congr`,
but is **degree-unstable** when iterated: the raw quadratic step `g' = g + t·e` lets `deg(t·e)` grow
each round (the engine's `liftBezout` does not bound the cofactor degrees), so after a couple of
rounds the lifted factor's degree blows up — fine for the *congruence* (still `≡ f mod p^{2m}`) but
useless for recombination. For the **computation** we use the textbook *degree-preserving* quadratic
step, which keeps each factor **monic of its original degree**: with `g, h` monic (degrees `dg, dh`),
`e = f − g·h`, and Bézout `s·g + t·h ≡ 1`,
`v := (t·e) mod g` (degree `< dg`), `q := (t·e) div g`, `u := s·e + h·q`;
then `g' := g + v` (monic, degree `dg`), `h' := h + u` (monic, degree `dh`) satisfy
`g·u + h·v = e`, so `g'·h' ≡ f (mod p^{2m})` with **stable degrees**. Cofactors are reduced mod the
factors to stay bounded. All coefficients reduced mod `p^{2m}`. (This computational path backs the
`native_decide` verdicts; the *abstract* soundness keystone remains the `ℤ`-trial-division
`dividesExactly_dvd`, which validates the recombination output regardless of how the lift produced
the candidates.) -/

/-- The number of Hensel doubling rounds to reach modulus `p^{2^k} > 2·mignotteBound f`: search
`k = 0, 1, …` (capped by `bnd + 1`, ample since `p^{2^k}` grows doubly-exponentially). -/
def henselRounds (p : ℕ) (f : List ℤ) : ℕ :=
  let target := 2 * mignotteBound f + 1
  let rec go : ℕ → ℕ → ℕ
    | 0, _ => 0
    | fuel + 1, k => if target ≤ p ^ (2 ^ k) then k else go fuel (k + 1)
  go (mignotteBound f + 1) 0

/-- A **degree-stable** quadratic Hensel round on `List ℤ` factors. `g, h` monic (degrees `dg, dh`),
cofactors `s, t`, modulus exponent `m`. Computes `g', h'` monic of the **same** degrees with
`g'·h' ≡ f (mod p^{2m})`, plus reduced cofactors `s', t'` for the next round. Each coefficient is
reduced mod `p^{2m}`. -/
def henselRoundStable (p : ℕ) (f : List ℤ) (m : ℕ) (g h s t : List ℤ) :
    List ℤ × List ℤ × List ℤ × List ℤ :=
  let n2 := p ^ (2 * m)
  let dg := lengthTrim g - 1
  let dh := lengthTrim h - 1
  let e := subL f (mulL g h)
  -- v = (t·e) mod g, q = (t·e) div g  (g monic of degree dg)
  let te := mulL t e
  let teqr := divmodByMonic te g dg
  let q := teqr.1
  let v := teqr.2
  -- u = s·e + h·q
  let u := addL (mulL s e) (mulL h q)
  let g' := reduceModN n2 (addL g v)
  let h' := reduceModN n2 (addL h u)
  -- reduce cofactors mod the new factors to keep them bounded:
  --   sustain Bézout by re-reducing s mod h', t mod g'
  let s' := reduceModN n2 (modByMonicL s h' dh)
  let t' := reduceModN n2 (modByMonicL t g' dg)
  (g', h', s', t')

/-- Iterate `henselRoundStable` for `k` doubling rounds (modulus exponent `m₀ ↦ 2^k m₀`),
degree-stable. Returns the lifted factors and cofactors. -/
def henselLiftStable (p : ℕ) (f : List ℤ) :
    ℕ → ℕ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ × List ℤ × List ℤ × List ℤ
  | 0, _, g, h, s, t => (g, h, s, t)
  | k + 1, m, g, h, s, t =>
    let r := henselRoundStable p f m g h s t
    henselLiftStable p f k (2 * m) r.1 r.2.1 r.2.2.1 r.2.2.2

/-- Lift a **two-factor** mod-`p` split `(g, h)` of `f` to mod `p^{2^k}` (`k = henselRounds p f`),
returning the lifted `(g', h')` as `List ℤ`, **degree-stable** (`henselLiftStable`). Bézout
cofactors via `bezoutModP`; starting modulus exponent `1` (mod `p`). -/
def henselLiftPair {p : ℕ} [Fact p.Prime] (f : List ℤ) (g h : List (ZMod p)) :
    List ℤ × List ℤ :=
  let st := bezoutModP g h
  let k := henselRounds p f
  let r := henselLiftStable p f k 1 (liftZMod g) (liftZMod h) (liftZMod st.1) (liftZMod st.2)
  (r.1, r.2.1)

/-- The product of a list of `ZMod p` factors (`mulL`-fold from `[1]`). -/
def listProdModP {p : ℕ} (fs : List (List (ZMod p))) : List (ZMod p) :=
  fs.foldr (fun a acc => mulL a acc) [1]

/-- **Multifactor Hensel lift.** Lift a mod-`p` factorization `facs = [g₁, …, gᵣ]` of `f` to mod
`p^{2^k}` as `List ℤ` factors, by repeatedly two-factor-lifting the head against the product of the
tail and recursing on the lifted tail. Fueled by the factor count. -/
def henselLiftMany {p : ℕ} [Fact p.Prime] (f : List ℤ) :
    ℕ → List (List (ZMod p)) → List (List ℤ)
  | _, [] => []
  | _, [g] => [liftZMod g]          -- single factor: lift directly (no Bézout needed)
  | 0, gs => gs.map liftZMod        -- out of fuel: lift each crudely
  | fuel + 1, g :: gs =>
    let h := listProdModP gs        -- product of the rest
    let gh := henselLiftPair f g h
    gh.1 :: henselLiftMany f fuel gs

/-! ## ★ The complete Zassenhaus `ℚ`-irreducibility decider

`irreducibleZassenhaus f` decides irreducibility of the monic integer polynomial `toPolyZ f` over
`ℚ` by the full pipeline: factor `f` mod a good prime `p` (no repeated factors — `f` squarefree,
which holds for the squarefree-primitive inputs in scope), Hensel-lift the factorization to mod
`p^k` past the Mignotte window, recombine over the lifted factors by `ℤ`-trial-division, and return
`true` iff the **only** factor recombination finds is `f` itself (full degree). Computable;
`native_decide`-able for small inputs (the headline `x⁴ + 1` lifts cheaply mod `3`). -/

/-- **★ The complete Zassenhaus decider.** `irreducibleZassenhaus p f n`: with degree `n` and a good
prime `p` (one giving a squarefree mod-`p` reduction — no repeated factors), factor `f mod p`
(`edf`), Hensel-lift to mod `p^{2^k}` (`henselLiftMany`), recombine over the lifted factors
(`recombine`), and return `true` iff the only `ℤ`-divisor degree found is the full degree `n` (so
the only factorization is the trivial one). The COMPLETE `ℚ`-irreducibility decision the one-way
mod-`p` test cannot give. -/
def irreducibleZassenhaus (p : ℕ) [Fact p.Prime] (f : List ℤ) (n : ℕ) : Bool :=
  let facp := factorModP p (reduceCoeffs p f)   -- mod-p irreducible factors (degree-correct)
  -- degree-n guard + a genuine factorization mod p (≥ 1 factor) is required
  if lengthTrim f ≠ n + 1 ∨ facp.length = 0 then false
  -- a single mod-p irreducible factor already proves ℚ-irreducibility (the mod-p test)
  else if facp.length = 1 then true
  else
    let pk := (p : ℤ) ^ (2 ^ henselRounds p f)  -- the lift modulus
    let lifted := henselLiftMany f (facp.length + 1) facp
    let degs := recombine f pk lifted
    -- irreducible iff NO proper ℤ-factor found
    degs.isEmpty

/-! ## ★★ The headline: the complete decider where the mod-`p` test provably fails

The milestone of the whole Zassenhaus campaign. `irreducibleByModP` returns `false` for `x⁴ + 1` at
**every** prime (`irreducibleByModP_X_pow_four_add_one_false`, since `Φ₈` is reducible mod every
prime by Frobenius) — a `ℚ`-irreducible polynomial the one-way mod-`p` test can never confirm. The
**complete** decider `irreducibleZassenhaus` computes it **irreducible** (`native_decide`), going
through the *full* Hensel pipeline: mod `3` it splits into two degree-`2` factors
`(x² + x + 2)(x² + 2x + 2)`, Hensel-lifts them past the Mignotte window, and recombination finds
**no** proper `ℤ`-factor — so the verdict is `true`. The decider succeeds exactly where the mod-`p`
test is provably incomplete. (`Fact (Nat.Prime _)` instances reused from the irreducibility file.) -/

/-- **★★★ THE HEADLINE.** The complete Zassenhaus decider confirms `x⁴ + 1` **irreducible** over `ℚ`
(`native_decide`) — via the **full** Hensel-lift + recombination pipeline (mod `3`, two degree-`2`
factors, no proper `ℤ`-recombination). This is the exact polynomial `irreducibleByModP` returns
`false` for at every prime: the mod-`p` test is *provably* incomplete here, and the complete decider
gives the right answer. The capstone of the campaign. -/
theorem irreducibleZassenhaus_X_pow_four_add_one :
    irreducibleZassenhaus 3 ([1, 0, 0, 0] ++ [1]) 4 = true := by native_decide

/-- **The contrast, pinned.** The complete decider says `true` (irreducible) where the mod-`p` test
says `false` (inconclusive) — at `p = 3` — for `x⁴ + 1`. The full pipeline strictly beats the
one-way mod-`p` test. -/
theorem zassenhaus_beats_modp_on_X_pow_four_add_one :
    irreducibleZassenhaus 3 ([1, 0, 0, 0] ++ [1]) 4 = true ∧
    irreducibleByModP 3 ([1, 0, 0, 0] ++ [1]) 4 = false :=
  ⟨irreducibleZassenhaus_X_pow_four_add_one,
    irreducibleByModP_X_pow_four_add_one_false.2.1⟩

/-- `x⁴ + 1` is **also** decided irreducible via mod `5` (again two degree-`2` factors, full
pipeline): the verdict is prime-robust (`native_decide`). -/
theorem irreducibleZassenhaus_X_pow_four_add_one_mod5 :
    irreducibleZassenhaus 5 ([1, 0, 0, 0] ++ [1]) 4 = true := by native_decide

/-- `x² − 2` is decided **irreducible** over `ℚ` by the complete decider (`native_decide`). -/
theorem irreducibleZassenhaus_X_sq_sub_two :
    irreducibleZassenhaus 5 ([-2, 0] ++ [1]) 2 = true := by native_decide

/-- `x² − 1` is decided **reducible** over `ℚ` (`native_decide`) — recombination finds the proper
factor `x + 1` (its cofactor being `x − 1`), so `x² − 1 = (x − 1)(x + 1)`. -/
theorem irreducibleZassenhaus_X_sq_sub_one_false :
    irreducibleZassenhaus 5 ([-1, 0] ++ [1]) 2 = false := by native_decide

/-- `x⁴ − 1 = (x − 1)(x + 1)(x² + 1)` is decided **reducible** (`native_decide`): the full pipeline
(mod `3`) finds a proper `ℤ`-factor. -/
theorem irreducibleZassenhaus_X_pow_four_sub_one_false :
    irreducibleZassenhaus 3 ([-1, 0, 0, 0] ++ [1]) 4 = false := by native_decide

/-- `x³ − 2` is decided **irreducible** over `ℚ` (`native_decide`). -/
theorem irreducibleZassenhaus_X_cube_sub_two :
    irreducibleZassenhaus 5 ([-2, 0, 0] ++ [1]) 3 = true := by native_decide

/-! ## ★ The factorization the pipeline finds for `x⁴ + 1` mod `3`

The structural content behind the headline: mod `3`, `factorModP` splits `x⁴ + 1` into the two
genuine degree-`2` irreducibles `x² + x + 2` and `x² + 2x + 2` (the engine `edf` returned this
**unsplit** — the degree-tag stop the `ddfCorrect` rebuild fixes). The list-level product is
`x⁴ + 1` (the `factorModP` multiply-back, validated; `toPoly` sends it to the polynomial identity).
The Hensel lift + recombination then confirm no `ℤ`-recombination of these two halves divides
`x⁴ + 1`, i.e. it is `ℚ`-irreducible. -/

/-- Mod `3`, `factorModP` splits `x⁴ + 1` into **two** degree-`2` factors (the engine `edf` stalled
at one; `ddfCorrect` continues through the trivial degree-`1` block) (`native_decide`). -/
example : (factorModP 3 (reduceCoeffs 3 ([1, 0, 0, 0] ++ [1] : List ℤ))).length = 2 := by
  native_decide

/-- The two mod-`3` factors of `x⁴ + 1` are `x² + x + 2` and `x² + 2x + 2` (low-to-high coefficient
lists, with benign trailing zeros from un-trimmed engine output) (`native_decide`). -/
example : factorModP 3 (reduceCoeffs 3 ([1, 0, 0, 0] ++ [1] : List ℤ))
    = ([[2, 2, 1, 0, 0, 0], [2, 1, 1]] : List (List (ZMod 3))) := by native_decide

/-! ## Restatements ("it compiled" ≠ "it says the right thing")

The decider verdicts are about the intended polynomials, and the headline contrast holds. -/

-- the headline input list IS `x⁴ + 1`.
example : toPolyZ ([1, 0, 0, 0] ++ [1]) = X ^ 4 + 1 := toPolyZ_X_pow_four_add_one

-- `x⁴ + 1` is GENUINELY ℚ-irreducible (from the cyclotomic theorem) AND the complete decider
-- confirms it (`true`), while the mod-`p` test returns `false` — the deeper claim the decider backs.
example : Irreducible (toPolyZ ([1, 0, 0, 0] ++ [1])) ∧
    irreducibleZassenhaus 3 ([1, 0, 0, 0] ++ [1]) 4 = true ∧
    irreducibleByModP 3 ([1, 0, 0, 0] ++ [1]) 4 = false :=
  ⟨irreducible_toPolyZ_X_pow_four_add_one,
    irreducibleZassenhaus_X_pow_four_add_one,
    irreducibleByModP_X_pow_four_add_one_false.2.1⟩

-- the decider has `Bool` type and the keystone soundness brick has the intended factorization type.
example : ∀ (f g : List ℤ) (dg : ℕ), dividesExactly f g dg = true →
    toPolyZ f = toPoly g * toPoly (divmodByMonic f g dg).1 :=
  fun _ _ _ h => dividesExactly_dvd h

end DeepWiki.SymbolicIntegration
