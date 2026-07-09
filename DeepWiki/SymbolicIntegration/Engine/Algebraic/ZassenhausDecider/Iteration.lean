import DeepWiki.SymbolicIntegration.Engine.Algebraic.HenselLift

/-! # Zassenhaus Hensel iteration

State, invariants, and soundness of the repeated quadratic Hensel lifting step.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ## Hensel iteration: iterate the quadratic step over the doubling schedule

`henselLift` runs `k` quadratic Newton rounds, each doubling the modulus exponent `m ↦ 2m`. -/

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

/-- Run `k` Hensel doubling rounds from a starting state; final modulus exponent is `2^k · m₀`. -/
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

/-! ## Soundness of one Hensel round, then of the iteration

The round-level multiply-back and Bézout invariants transfer mod `p^m → mod p^{2m}`, and fold over
`k` rounds. -/

/-- The two Hensel invariants on a state at prime `p` for target `f`: the factors multiply back and
the Bézout relation holds, both mod `p^{st.m}`. -/
def HenselInv (p : ℕ) (f : List ℤ) (st : HenselState) : Prop :=
  polyCongr (p ^ st.m) (toPolyZ f) (toPolyZ st.g * toPolyZ st.h) ∧
    polyCongr (p ^ st.m) (toPolyZ st.s * toPolyZ st.g + toPolyZ st.t * toPolyZ st.h) 1

/-! ### Bridge lemmas for the round step

Modulus weakening and factor stability, feeding the Bézout precondition of `liftBezout_congr`. -/

/-- A polynomial congruence mod `n` descends to mod `m` when `m ∣ n`. -/
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

/-- The lifted first factor `(liftStep …).1` is congruent to `g` mod `p^m`. -/
theorem liftStep_fst_congr (p m : ℕ) (f g h s t : List ℤ)
    (hdef : polyCongr (p ^ m) (toPolyZ f) (toPolyZ g * toPolyZ h)) :
    polyCongr (p ^ m) (toPolyZ (liftStep p m f g h s t).1) (toPolyZ g) := by
  -- g' = reduceModN (p^{2m}) (addL g (mulL t e)),  e = defectL f g h
  set e := defectL f g h with hedef
  set g0 := addL g (mulL t e) with hg0def
  have hfst : (liftStep p m f g h s t).1 = reduceModN (p ^ (2 * m)) g0 := rfl
  rw [hfst]
  -- reduceModN ≡ identity mod p^{2m}, then weaken to p^m
  have hred : polyCongr (p ^ m) (listToPoly (reduceModN (p ^ (2 * m)) g0)) (listToPoly g0) :=
    polyCongr_of_dvd (pow_dvd_pow_two_mul p m) (polyCongr_toPoly_reduceModN _ _)
  -- listToPoly g0 = listToPoly g + listToPoly t * (defect), and defect ≡ 0 mod p^m
  have hg0poly : listToPoly g0 = listToPoly g + listToPoly t * (listToPoly f - listToPoly g * listToPoly h) := by
    rw [hg0def, toPoly_addL, toPoly_mulL, hedef, toPoly_defectL, toPolyZ, toPolyZ, toPolyZ]
  -- defect ≡ 0 mod p^m  (C(p^m) ∣ defect)
  obtain ⟨c, hc⟩ : (C ((p ^ m : ℕ) : ℤ)) ∣ (listToPoly f - listToPoly g * listToPoly h) := by
    rcases hdef with ⟨k, hk⟩; exact ⟨k, by simp only [toPolyZ] at hk; rw [hk]⟩
  -- listToPoly g0 ≡ listToPoly g mod p^m
  have hg0congr : polyCongr (p ^ m) (listToPoly g0) (listToPoly g) := by
    rw [polyCongr, hg0poly, hc]
    refine ⟨listToPoly t * c, ?_⟩
    ring
  simp only [toPolyZ]
  exact polyCongr_trans hred hg0congr

/-- The lifted second factor `(liftStep …).2` is congruent to `h` mod `p^m`. -/
theorem liftStep_snd_congr (p m : ℕ) (f g h s t : List ℤ)
    (hdef : polyCongr (p ^ m) (toPolyZ f) (toPolyZ g * toPolyZ h)) :
    polyCongr (p ^ m) (toPolyZ (liftStep p m f g h s t).2) (toPolyZ h) := by
  set e := defectL f g h with hedef
  set h0 := addL h (mulL s e) with hh0def
  have hsnd : (liftStep p m f g h s t).2 = reduceModN (p ^ (2 * m)) h0 := rfl
  rw [hsnd]
  have hred : polyCongr (p ^ m) (listToPoly (reduceModN (p ^ (2 * m)) h0)) (listToPoly h0) :=
    polyCongr_of_dvd (pow_dvd_pow_two_mul p m) (polyCongr_toPoly_reduceModN _ _)
  have hh0poly : listToPoly h0 = listToPoly h + listToPoly s * (listToPoly f - listToPoly g * listToPoly h) := by
    rw [hh0def, toPoly_addL, toPoly_mulL, hedef, toPoly_defectL, toPolyZ, toPolyZ, toPolyZ]
  obtain ⟨c, hc⟩ : (C ((p ^ m : ℕ) : ℤ)) ∣ (listToPoly f - listToPoly g * listToPoly h) := by
    rcases hdef with ⟨k, hk⟩; exact ⟨k, by simp only [toPolyZ] at hk; rw [hk]⟩
  have hh0congr : polyCongr (p ^ m) (listToPoly h0) (listToPoly h) := by
    rw [polyCongr, hh0poly, hc]
    refine ⟨listToPoly s * c, ?_⟩
    ring
  simp only [toPolyZ]
  exact polyCongr_trans hred hh0congr

/-- The Bézout relation `s·g' + t·h' ≡ 1 (mod p^m)` transfers to the lifted factors `g', h'`. -/
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

/-- One round preserves both Hensel invariants, mod `p^m → mod p^{2m}`. -/
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

/-- The Hensel iteration preserves both invariants through `k` rounds. -/
theorem henselLift_inv (p : ℕ) (f : List ℤ) (st : HenselState) (k : ℕ)
    (hinv : HenselInv p f st) : HenselInv p f (henselLift p f st k) := by
  induction k generalizing st with
  | zero => simpa [henselLift] using hinv
  | succ k ih =>
    rw [henselLift]
    exact ih (henselRound p f st) (henselRound_inv p f st hinv)

/-- After `k` doubling rounds the lifted factors multiply back:
`toPolyZ f ≡ toPolyZ g_final * toPolyZ h_final (mod p^{2^k m₀})`. -/
theorem henselLift_congr (p : ℕ) (f : List ℤ) (st : HenselState) (k : ℕ)
    (hdef : polyCongr (p ^ st.m) (toPolyZ f) (toPolyZ st.g * toPolyZ st.h))
    (hbez : polyCongr (p ^ st.m) (toPolyZ st.s * toPolyZ st.g + toPolyZ st.t * toPolyZ st.h) 1) :
    polyCongr (p ^ (henselLift p f st k).m) (toPolyZ f)
      (toPolyZ (henselLift p f st k).g * toPolyZ (henselLift p f st k).h) :=
  (henselLift_inv p f st k ⟨hdef, hbez⟩).1

end DeepWiki.SymbolicIntegration
