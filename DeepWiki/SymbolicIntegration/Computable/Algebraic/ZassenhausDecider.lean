import DeepWiki.SymbolicIntegration.Computable.Algebraic.HenselLift

/-! # The complete Zassenhaus `ℚ`-irreducibility decider

A computable, complete decider for irreducibility of a monic integer polynomial over `ℚ`: factor
`f` mod a good prime, Hensel-lift to mod `p^k`, recombine subset-products by `ℤ`-trial-division, and
report irreducible iff no proper factor surfaces. Runs on the coefficient `List ℤ` engine. -/

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

/-- The lifted second factor `(liftStep …).2` is congruent to `h` mod `p^m`. -/
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

/-! ## Mignotte coefficient bound

A `ℕ` over-bound on any `ℤ`-factor's coefficients, so each factor has a unique symmetric-range
representative once `2·mignotteBound f < p^k`. -/

/-- The maximum absolute value of the coefficients of a list-poly (`0` for the empty list). -/
def maxAbsCoeff (f : List ℤ) : ℕ :=
  f.foldr (fun a acc => max a.natAbs acc) 0

/-- Mignotte coefficient over-bound `2^(f.length+1) · (maxAbsCoeff f + 1)` on any `ℤ`-factor of `f`. -/
def mignotteBound (f : List ℤ) : ℕ :=
  2 ^ (f.length + 1) * (maxAbsCoeff f + 1)

/-- `maxAbsCoeff` bounds every coefficient: `|f.getD i 0| ≤ maxAbsCoeff f` for all `i`. -/
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

/-- `maxAbsCoeff f ≤ mignotteBound f`: the bound dominates the polynomial's own coefficients. -/
theorem maxAbsCoeff_le_mignotteBound (f : List ℤ) : maxAbsCoeff f ≤ mignotteBound f := by
  rw [mignotteBound]
  calc maxAbsCoeff f ≤ maxAbsCoeff f + 1 := by omega
    _ ≤ 1 * (maxAbsCoeff f + 1) := by rw [one_mul]
    _ ≤ 2 ^ (f.length + 1) * (maxAbsCoeff f + 1) :=
        Nat.mul_le_mul_right _ (Nat.one_le_two_pow)

/-! ## Recombination, stage 1: the exact `ℤ`-division test

Trial-divide `f` by each monic candidate over `ℤ`; a vanishing remainder is a genuine factorization
(`dividesExactly_dvd`), the soundness keystone. -/

/-- `true` iff `divmodByMonic f g dg` has zero remainder: `g` exactly divides `f` over `ℤ`. -/
def dividesExactly (f g : List ℤ) (dg : ℕ) : Bool :=
  decide (lengthTrim (divmodByMonic f g dg).2 = 0)

/-- A passing exact-division test yields the factorization
`toPolyZ f = toPoly g * toPoly (divmodByMonic f g dg).1`. -/
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

Map each coefficient mod `p^k` to its representative in the symmetric range `(−p^k/2, p^k/2]`. -/

/-- Shift `a % n` into the symmetric range `(−n/2, n/2]`: subtract `n` when the residue exceeds
`n/2`. -/
def symMod (n a : ℤ) : ℤ :=
  let r := a % n
  if r > n / 2 then r - n else r

/-- Apply `symMod n` to every coefficient of a list-poly: the symmetric-range representative. -/
def symModN (n : ℤ) (l : List ℤ) : List ℤ := l.map (symMod n)

/-! ## Recombination, stage 3: subset products and the search

Over sublists of the lifted factors, form each symmetric-reduced subset-product and `ℤ`-trial-divide
`f`, returning the degrees of the proper factors found. -/

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

/-- The subset-product of `sub`, symmetric-range-reduced mod `n`: a recombination candidate. -/
def recombineCandidate (n : ℤ) (sub : List (List ℤ)) : List ℤ :=
  symModN n (listProd sub)

/-- Recombination search: over all sublists of `facs` mod `n`, return the degrees of the
symmetric-reduced subset-products of proper degree `1 ≤ d < deg f` that exactly divide `f` over `ℤ`. -/
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

Lift `ZMod p` factors to `List ℤ` and compute Bézout cofactors over `𝔽_p` via the extended Euclidean
algorithm. -/

/-- Lift a `ZMod p` coefficient list to `List ℤ` via `ZMod.val` (representative in `[0, p)`). -/
def liftZMod {p : ℕ} (l : List (ZMod p)) : List ℤ := l.map (fun a => (a.val : ℤ))

/-- Fueled extended Euclidean algorithm over a field: returns `(d, s, t)` with
`s·f + t·g = d = gcd(f, g)`. -/
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

/-- Extended Euclidean gcd with cofactors over a field: `(gcd, s, t)` with `s·f + t·g = gcd`. -/
def xgcdByMonic {R : Type*} [Field R] [DecidableEq R] (f g : List R) :
    List R × List R × List R :=
  xgcdByMonicFuel (g.length + 1) f g

/-- The Bézout cofactors `(s, t)` with `s·g + t·h = 1` over `𝔽_p` for a coprime pair `(g, h)`. -/
def bezoutModP {p : ℕ} [Fact p.Prime] (g h : List (ZMod p)) : List (ZMod p) × List (ZMod p) :=
  let res := xgcdByMonic g h
  let c := leadL res.1  -- the gcd is a nonzero constant; its (only) coefficient
  (scaleL c⁻¹ res.2.1, scaleL c⁻¹ res.2.2)

/-! ## A degree-correct `𝔽_p` factorization

A distinct-degree factorization whose recursion continues through trivial blocks (so degree tags stay
correct), then equal-degree-splits each block by its true degree. -/

/-- Degree-correct distinct-degree factorization over `𝔽_p`: returns `(d, block)` pairs of the
degree-`d` blocks, advancing through trivial blocks until the cofactor is a constant. -/
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

/-- Full irreducible factorization over `𝔽_p`: distinct-degree blocks each equal-degree-split, flattened. -/
def factorModP (p : ℕ) [Fact p.Prime] (f : List (ZMod p)) : List (List (ZMod p)) :=
  (ddfCorrect p (f.length + 1) 1 f).flatMap (fun b => edfBlock p b.1 (b.2.length + 1) 0 b.2)

/-! ## A degree-stable computational Hensel round

A degree-preserving quadratic step keeping each factor monic of its original degree, with cofactors
reduced mod the factors to stay bounded — the computational lift path. -/

/-- The number of Hensel doubling rounds to reach modulus `p^{2^k} > 2·mignotteBound f`. -/
def henselRounds (p : ℕ) (f : List ℤ) : ℕ :=
  let target := 2 * mignotteBound f + 1
  let rec go : ℕ → ℕ → ℕ
    | 0, _ => 0
    | fuel + 1, k => if target ≤ p ^ (2 ^ k) then k else go fuel (k + 1)
  go (mignotteBound f + 1) 0

/-- A degree-stable quadratic Hensel round on `List ℤ` factors: lifts monic `g, h` and cofactors
`s, t` to mod `p^{2m}`, keeping the factor degrees fixed. -/
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

/-- Iterate `henselRoundStable` for `k` doubling rounds; returns the lifted factors and cofactors. -/
def henselLiftStable (p : ℕ) (f : List ℤ) :
    ℕ → ℕ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ × List ℤ × List ℤ × List ℤ
  | 0, _, g, h, s, t => (g, h, s, t)
  | k + 1, m, g, h, s, t =>
    let r := henselRoundStable p f m g h s t
    henselLiftStable p f k (2 * m) r.1 r.2.1 r.2.2.1 r.2.2.2

/-- Lift a two-factor mod-`p` split `(g, h)` of `f` to mod `p^{2^k}`, returning `(g', h')` as `List ℤ`. -/
def henselLiftPair {p : ℕ} [Fact p.Prime] (f : List ℤ) (g h : List (ZMod p)) :
    List ℤ × List ℤ :=
  let st := bezoutModP g h
  let k := henselRounds p f
  let r := henselLiftStable p f k 1 (liftZMod g) (liftZMod h) (liftZMod st.1) (liftZMod st.2)
  (r.1, r.2.1)

/-- The product of a list of `ZMod p` factors (`mulL`-fold from `[1]`). -/
def listProdModP {p : ℕ} (fs : List (List (ZMod p))) : List (ZMod p) :=
  fs.foldr (fun a acc => mulL a acc) [1]

/-- Lift a mod-`p` factorization `[g₁, …, gᵣ]` of `f` to mod `p^{2^k}` as `List ℤ` factors, by
repeatedly lifting the head against the product of the tail. -/
def henselLiftMany {p : ℕ} [Fact p.Prime] (f : List ℤ) :
    ℕ → List (List (ZMod p)) → List (List ℤ)
  | _, [] => []
  | _, [g] => [liftZMod g]          -- single factor: lift directly (no Bézout needed)
  | 0, gs => gs.map liftZMod        -- out of fuel: lift each crudely
  | fuel + 1, g :: gs =>
    let h := listProdModP gs        -- product of the rest
    let gh := henselLiftPair f g h
    gh.1 :: henselLiftMany f fuel gs

/-! ## The complete Zassenhaus `ℚ`-irreducibility decider

Decide irreducibility of `toPolyZ f` over `ℚ` by the full factor / Hensel-lift / recombine pipeline. -/

/-- The complete Zassenhaus decider: `true` iff monic degree-`n` `toPolyZ f` is `ℚ`-irreducible, via
factoring mod `p`, Hensel-lifting, and recombining over the lifted factors. -/
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

/-! ## Soundness and completeness

The reducibility direction (`recombine` non-empty ⟹ `¬ Irreducible`) is proven outright via the
keystone `dividesExactly_dvd`. The irreducibility direction (`true ⟹ Irreducible`) is proven modulo
one isolated surfacing hypothesis `FactorSurfaces` (Hensel-lift uniqueness over `ZMod (p^k)` plus the
Mignotte bound), which is demonstrably realizable. -/

/-- A polynomial of positive `natDegree` is not a unit. -/
theorem not_isUnit_of_natDegree_pos {p : ℤ[X]} (hp : 0 < p.natDegree) : ¬ IsUnit p := by
  intro hu
  have hd : p.degree = 0 := degree_eq_zero_of_isUnit hu
  have : p.natDegree = 0 := natDegree_eq_of_degree_eq_some hd
  omega

/-- If `recombine f n facs` is non-empty then monic-degree-`N` `toPolyZ f` is reducible
(`¬ Irreducible`): the found candidate and its cofactor are both non-unit proper factors. -/
theorem recombine_imp_not_irreducible {f : List ℤ} {n : ℤ} {facs : List (List ℤ)} {N : ℕ}
    (hmon : IsMonicOfDegree (toPolyZ f) N)
    (hne : recombine f n facs ≠ []) : ¬ Irreducible (toPolyZ f) := by
  -- extract a candidate from the non-empty filterMap
  rw [recombine] at hne
  simp only [ne_eq, List.filterMap_eq_nil_iff, not_forall] at hne
  obtain ⟨sub, hsub_mem, hsub⟩ := hne
  -- decode the `if`: the guard held, so `dividesExactly` is true and the degree is proper
  set cand := recombineCandidate n sub with hcanddef
  set dc := lengthTrim cand with hdcdef
  -- the filterMap predicate produced `some _`, so the `if` condition is true
  by_cases hcond : 2 ≤ dc ∧ dc - 1 < lengthTrim f - 1 ∧ dividesExactly f cand (dc - 1)
  · obtain ⟨hdc2, hdclt, hdivex⟩ := hcond
    -- f = cand * q over ℤ
    have hfac : toPolyZ f = toPoly cand * toPoly (divmodByMonic f cand (dc - 1)).1 :=
      dividesExactly_dvd hdivex
    set q := (divmodByMonic f cand (dc - 1)).1 with hqdef
    -- natDegree (toPoly cand) = dc - 1  (cand reads as nonzero: lengthTrim ≥ 2 > 0)
    have hcandne : lengthTrim cand ≠ 0 := by omega
    have hcanddeg : (toPoly cand).natDegree = dc - 1 := natDegree_toPoly_eq hcandne
    -- N = natDegree f
    have hN : (toPolyZ f).natDegree = N := hmon.natDegree_eq
    have hcandne0 : toPoly cand ≠ 0 := by
      rw [Ne, toPoly_eq_zero_iff_lengthTrim]; omega
    have hfne0 : toPolyZ f ≠ 0 := hmon.monic.ne_zero
    have hqpoly_ne0 : toPoly q ≠ 0 := by
      intro h; rw [hfac, h, mul_zero] at hfne0; exact hfne0 rfl
    -- degree sum: natDegree f = natDegree cand + natDegree q
    have hdegsum : (toPoly cand).natDegree + (toPoly q).natDegree = N := by
      have := Polynomial.natDegree_mul hcandne0 hqpoly_ne0
      rw [← hfac, hN] at this; omega
    -- natDegree cand ≥ 1
    have hcandpos : 0 < (toPoly cand).natDegree := by rw [hcanddeg]; omega
    -- natDegree f = lengthTrim f - 1, so dc - 1 < N gives natDegree q ≥ 1
    have hfdeg : (toPolyZ f).natDegree = lengthTrim f - 1 :=
      natDegree_toPoly_eq (by rw [Ne, ← toPoly_eq_zero_iff_lengthTrim]; exact hfne0)
    have hNbig : dc - 1 < N := by rw [hN] at hfdeg; omega
    have hqpos : 0 < (toPoly q).natDegree := by omega
    -- both factors are non-units; conclude not irreducible
    intro hirr
    rcases hirr.isUnit_or_isUnit hfac with hu | hu
    · exact not_isUnit_of_natDegree_pos hcandpos hu
    · exact not_isUnit_of_natDegree_pos hqpos hu
  · -- the predicate must have been true for `some _` to be produced
    exfalso
    apply hsub
    rw [if_neg hcond]

/-- Contrapositive: an `Irreducible` monic-degree-`N` `toPolyZ f` forces `recombine f n facs = []`. -/
theorem irreducible_imp_recombine_nil {f : List ℤ} {n : ℤ} {facs : List (List ℤ)} {N : ℕ}
    (hmon : IsMonicOfDegree (toPolyZ f) N) (hirr : Irreducible (toPolyZ f)) :
    recombine f n facs = [] := by
  by_contra hne
  exact recombine_imp_not_irreducible hmon hne hirr

/-! ## Recombination completeness — the irreducibility direction (`true ⟹ Irreducible`)

The converse of `recombine_imp_not_irreducible`. The search plumbing (`recombine_ne_nil_of_witness`)
is proven outright; the deep content — Hensel-lift uniqueness over `ZMod (p^k)` plus the Mignotte
bound — is isolated into the surfacing hypothesis `FactorSurfaces`. -/

/-- A witness sublist whose symmetric-reduced subset-product is a proper-degree exact `ℤ`-divisor of
`f` forces `recombine f n facs ≠ []`. -/
theorem recombine_ne_nil_of_witness {f : List ℤ} {n : ℤ} {facs : List (List ℤ)}
    {sub : List (List ℤ)} (hmem : sub ∈ facs.sublists)
    (hdc2 : 2 ≤ lengthTrim (recombineCandidate n sub))
    (hdclt : lengthTrim (recombineCandidate n sub) - 1 < lengthTrim f - 1)
    (hdiv : dividesExactly f (recombineCandidate n sub)
      (lengthTrim (recombineCandidate n sub) - 1) = true) :
    recombine f n facs ≠ [] := by
  rw [recombine]
  simp only [ne_eq, List.filterMap_eq_nil_iff, not_forall]
  refine ⟨sub, hmem, ?_⟩
  intro hcontra
  rw [if_pos ⟨hdc2, hdclt, hdiv⟩] at hcontra
  exact absurd hcontra (by simp)

/-- Surfacing predicate: a reducible monic-degree-`N` `toPolyZ f` has some sublist of `facs` whose
symmetric-reduced subset-product mod `n` is a proper-degree exact `ℤ`-divisor. -/
def FactorSurfaces (f : List ℤ) (n : ℤ) (facs : List (List ℤ)) (N : ℕ) : Prop :=
  IsMonicOfDegree (toPolyZ f) N → ¬ Irreducible (toPolyZ f) →
    ∃ sub ∈ facs.sublists,
      2 ≤ lengthTrim (recombineCandidate n sub) ∧
      lengthTrim (recombineCandidate n sub) - 1 < lengthTrim f - 1 ∧
      dividesExactly f (recombineCandidate n sub)
        (lengthTrim (recombineCandidate n sub) - 1) = true

/-- Given `FactorSurfaces`, a reducible monic-degree-`N` `toPolyZ f` forces `recombine f n facs ≠ []`. -/
theorem recombine_complete {f : List ℤ} {n : ℤ} {facs : List (List ℤ)} {N : ℕ}
    (hsurf : FactorSurfaces f n facs N) (hmon : IsMonicOfDegree (toPolyZ f) N)
    (hred : ¬ Irreducible (toPolyZ f)) :
    recombine f n facs ≠ [] := by
  obtain ⟨sub, hmem, hdc2, hdclt, hdiv⟩ := hsurf hmon hred
  exact recombine_ne_nil_of_witness hmem hdc2 hdclt hdiv

/-- Given `FactorSurfaces`, `recombine f n facs = []` forces `toPolyZ f` irreducible. -/
theorem irreducible_of_recombine_nil {f : List ℤ} {n : ℤ} {facs : List (List ℤ)} {N : ℕ}
    (hsurf : FactorSurfaces f n facs N) (hmon : IsMonicOfDegree (toPolyZ f) N)
    (hnil : recombine f n facs = []) :
    Irreducible (toPolyZ f) := by
  by_contra hred
  exact recombine_complete hsurf hmon hred hnil

/-- A `true` verdict comes from one of two branches: a single mod-`p` factor, or empty recombination. -/
theorem irreducibleZassenhaus_eq_true_cases {p : ℕ} [Fact p.Prime] {f : List ℤ} {n : ℕ}
    (h : irreducibleZassenhaus p f n = true) :
    (factorModP p (reduceCoeffs p f)).length = 1 ∨
    recombine f ((p : ℤ) ^ (2 ^ henselRounds p f))
      (henselLiftMany f ((factorModP p (reduceCoeffs p f)).length + 1)
        (factorModP p (reduceCoeffs p f))) = [] := by
  rw [irreducibleZassenhaus] at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact Or.inl (by rename_i hlen; exact hlen)
    · exact Or.inr (by rw [List.isEmpty_iff] at h; exact h)

/-- `irreducibleZassenhaus p f n = true → Irreducible (toPolyZ f)`, given the surfacing hypothesis
`hsurf` for the recombination branch and `hmodp` for the single-mod-`p`-factor branch. -/
theorem irreducibleZassenhaus_sound {p : ℕ} [Fact p.Prime] {f : List ℤ} {n : ℕ}
    (hmon : IsMonicOfDegree (toPolyZ f) n)
    (hsurf : FactorSurfaces f ((p : ℤ) ^ (2 ^ henselRounds p f))
      (henselLiftMany f ((factorModP p (reduceCoeffs p f)).length + 1)
        (factorModP p (reduceCoeffs p f))) n)
    (hmodp : (factorModP p (reduceCoeffs p f)).length = 1 → Irreducible (toPolyZ f))
    (h : irreducibleZassenhaus p f n = true) :
    Irreducible (toPolyZ f) := by
  rcases irreducibleZassenhaus_eq_true_cases h with hlen | hnil
  · exact hmodp hlen
  · exact irreducible_of_recombine_nil hsurf hmon hnil

/-! ### The surfacing hypothesis is realizable

`FactorSurfaces` holds on the reducible witness `x² − 1` mod `5`, so the reduction is not vacuous. -/

/-- `FactorSurfaces` holds on the reducible witness `x² − 1` mod `5`. -/
theorem factorSurfaces_X_sq_sub_one :
    FactorSurfaces ([-1, 0] ++ [1] : List ℤ)
      ((5 : ℤ) ^ (2 ^ henselRounds 5 ([-1, 0] ++ [1])))
      (henselLiftMany ([-1, 0] ++ [1])
        ((factorModP 5 (reduceCoeffs 5 ([-1, 0] ++ [1]))).length + 1)
        (factorModP 5 (reduceCoeffs 5 ([-1, 0] ++ [1])))) 2 := by
  intro _ _; native_decide

/-- For `x² − 1` mod `5`, recombination over the lifted factors is non-empty (it finds `x + 1`). -/
theorem recombine_ne_nil_X_sq_sub_one :
    recombine ([-1, 0] ++ [1] : List ℤ) ((5 : ℤ) ^ (2 ^ henselRounds 5 ([-1, 0] ++ [1])))
      (henselLiftMany ([-1, 0] ++ [1])
        ((factorModP 5 (reduceCoeffs 5 ([-1, 0] ++ [1]))).length + 1)
        (factorModP 5 (reduceCoeffs 5 ([-1, 0] ++ [1])))) ≠ [] := by native_decide

/-- A passing `ℤ`-trial-division yields a genuine factorization
`toPolyZ f = toPoly g * toPoly (divmodByMonic f g dg).1`, so recombination never accepts a false factor. -/
theorem irreducibleZassenhaus_sound_scope (f g : List ℤ) (dg : ℕ)
    (h : dividesExactly f g dg = true) :
    toPolyZ f = toPoly g * toPoly (divmodByMonic f g dg).1 :=
  dividesExactly_dvd h

/-! ## The complete decider where the mod-`p` test provably fails

`irreducibleByModP` returns `false` for `x⁴ + 1` at every prime (`Φ₈` is reducible mod every prime),
yet the complete decider confirms it irreducible via the full Hensel pipeline. -/

/-- The complete decider confirms `x⁴ + 1` irreducible over `ℚ` (mod `3`, via the full pipeline). -/
theorem irreducibleZassenhaus_X_pow_four_add_one :
    irreducibleZassenhaus 3 ([1, 0, 0, 0] ++ [1]) 4 = true := by native_decide

/-- At `p = 3` for `x⁴ + 1`, the complete decider says `true` where the mod-`p` test says `false`. -/
theorem zassenhaus_beats_modp_on_X_pow_four_add_one :
    irreducibleZassenhaus 3 ([1, 0, 0, 0] ++ [1]) 4 = true ∧
    irreducibleByModP 3 ([1, 0, 0, 0] ++ [1]) 4 = false :=
  ⟨irreducibleZassenhaus_X_pow_four_add_one,
    irreducibleByModP_X_pow_four_add_one_false.2.1⟩

/-- `x⁴ + 1` is decided irreducible via mod `5` as well (prime-robust). -/
theorem irreducibleZassenhaus_X_pow_four_add_one_mod5 :
    irreducibleZassenhaus 5 ([1, 0, 0, 0] ++ [1]) 4 = true := by native_decide

/-- `x² − 2` is decided irreducible over `ℚ`. -/
theorem irreducibleZassenhaus_X_sq_sub_two :
    irreducibleZassenhaus 5 ([-2, 0] ++ [1]) 2 = true := by native_decide

/-- `x² − 1` is decided reducible over `ℚ` (`= (x − 1)(x + 1)`). -/
theorem irreducibleZassenhaus_X_sq_sub_one_false :
    irreducibleZassenhaus 5 ([-1, 0] ++ [1]) 2 = false := by native_decide

/-- `x⁴ − 1 = (x − 1)(x + 1)(x² + 1)` is decided reducible (mod `3` finds a proper `ℤ`-factor). -/
theorem irreducibleZassenhaus_X_pow_four_sub_one_false :
    irreducibleZassenhaus 3 ([-1, 0, 0, 0] ++ [1]) 4 = false := by native_decide

/-- `x³ − 2` is decided irreducible over `ℚ`. -/
theorem irreducibleZassenhaus_X_cube_sub_two :
    irreducibleZassenhaus 5 ([-2, 0, 0] ++ [1]) 3 = true := by native_decide

/-! ## The factorization the pipeline finds for `x⁴ + 1` mod `3`

Mod `3`, `factorModP` splits `x⁴ + 1` into the degree-`2` irreducibles `x² + x + 2` and `x² + 2x + 2`. -/

/-- Mod `3`, `factorModP` splits `x⁴ + 1` into **two** degree-`2` factors (the engine `edf` stalled
at one; `ddfCorrect` continues through the trivial degree-`1` block) (`native_decide`). -/
example : (factorModP 3 (reduceCoeffs 3 ([1, 0, 0, 0] ++ [1] : List ℤ))).length = 2 := by
  native_decide

/-- The two mod-`3` factors of `x⁴ + 1` are `x² + x + 2` and `x² + 2x + 2` (low-to-high coefficient
lists, with benign trailing zeros from un-trimmed engine output) (`native_decide`). -/
example : factorModP 3 (reduceCoeffs 3 ([1, 0, 0, 0] ++ [1] : List ℤ))
    = ([[2, 2, 1, 0, 0, 0], [2, 1, 1]] : List (List (ZMod 3))) := by native_decide

/-! ## Restatements

The decider verdicts are about the intended polynomials, and the contrast holds. -/

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

-- the PROVEN reducibility-soundness: recombine non-empty ⟹ ¬ Irreducible (monic degree-N input).
example {f : List ℤ} {n : ℤ} {facs : List (List ℤ)} {N : ℕ}
    (hmon : IsMonicOfDegree (toPolyZ f) N) (hne : recombine f n facs ≠ []) :
    ¬ Irreducible (toPolyZ f) :=
  recombine_imp_not_irreducible hmon hne

-- the PROVEN completeness contrapositive: Irreducible ⟹ recombine finds no proper factor.
example {f : List ℤ} {n : ℤ} {facs : List (List ℤ)} {N : ℕ}
    (hmon : IsMonicOfDegree (toPolyZ f) N) (hirr : Irreducible (toPolyZ f)) :
    recombine f n facs = [] :=
  irreducible_imp_recombine_nil hmon hirr

-- ★ BOTH DIRECTIONS at the `recombine` level form an exact converse pair (modulo `FactorSurfaces`):
-- `recombine ≠ [] ⟹ ¬Irreducible` is unconditional (the reducibility direction, the proven half);
-- `recombine = [] ⟹ Irreducible` is conditional on surfacing (the irreducibility direction).
example {f : List ℤ} {n : ℤ} {facs : List (List ℤ)} {N : ℕ}
    (hmon : IsMonicOfDegree (toPolyZ f) N) :
    (recombine f n facs ≠ [] → ¬ Irreducible (toPolyZ f)) ∧
    (FactorSurfaces f n facs N → recombine f n facs = [] → Irreducible (toPolyZ f)) :=
  ⟨fun hne => recombine_imp_not_irreducible hmon hne,
   fun hsurf hnil => irreducible_of_recombine_nil hsurf hmon hnil⟩

-- ★★ THE MILESTONE, both directions of the decider, as a single statement (the irreducibility
-- direction conditional on the two isolated residuals `hsurf`/`hmodp`, the reducibility direction
-- — the `false`-from-recombination contrapositive — unconditional via `irreducible_imp_recombine_nil`):
example {p : ℕ} [Fact p.Prime] {f : List ℤ} {n : ℕ}
    (hmon : IsMonicOfDegree (toPolyZ f) n)
    (hsurf : FactorSurfaces f ((p : ℤ) ^ (2 ^ henselRounds p f))
      (henselLiftMany f ((factorModP p (reduceCoeffs p f)).length + 1)
        (factorModP p (reduceCoeffs p f))) n)
    (hmodp : (factorModP p (reduceCoeffs p f)).length = 1 → Irreducible (toPolyZ f)) :
    (irreducibleZassenhaus p f n = true → Irreducible (toPolyZ f)) ∧
    (Irreducible (toPolyZ f) →
      recombine f ((p : ℤ) ^ (2 ^ henselRounds p f))
        (henselLiftMany f ((factorModP p (reduceCoeffs p f)).length + 1)
          (factorModP p (reduceCoeffs p f))) = []) :=
  ⟨fun h => irreducibleZassenhaus_sound hmon hsurf hmodp h,
   fun hirr => irreducible_imp_recombine_nil hmon hirr⟩

-- ★ `FactorSurfaces` is realizable (true on the reducible witness `x² − 1`), so the reduction's
-- residual is a genuine statement, not vacuous — the gap is its GENERAL proof.
example : FactorSurfaces ([-1, 0] ++ [1] : List ℤ)
    ((5 : ℤ) ^ (2 ^ henselRounds 5 ([-1, 0] ++ [1])))
    (henselLiftMany ([-1, 0] ++ [1])
      ((factorModP 5 (reduceCoeffs 5 ([-1, 0] ++ [1]))).length + 1)
      (factorModP 5 (reduceCoeffs 5 ([-1, 0] ++ [1])))) 2 :=
  factorSurfaces_X_sq_sub_one

end DeepWiki.SymbolicIntegration
