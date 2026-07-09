import DeepWiki.SymbolicIntegration.Engine.Algebraic.PolynomialIrreducibility

/-! # Computable `𝔽_p` polynomial factorization: distinct- and equal-degree (Cantor–Zassenhaus)

Over `𝔽_p` with polynomials as coefficient `List (ZMod p)`: the monic long-division primitives
(`divmodByMonic` + the division identity), the Euclidean `gcdByMonic`, the Frobenius power
`xPowModF`, distinct-degree factorization `ddf`, and equal-degree factorization `edf`, each with its
multiply-back soundness (`ddf_prod`, `edf_prod`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ## Degree of a list-poly and the leading entry -/

/-- Index one past the last nonzero coefficient (`0` for the zero poly): the effective length of a
list-poly, so `toPoly`'s `natDegree` is `lengthTrim l - 1` when nonzero. -/
def lengthTrim {R : Type*} [Zero R] [DecidableEq R] : List R → ℕ
  | [] => 0
  | a :: as =>
    let r := lengthTrim as
    if r = 0 then (if a = 0 then 0 else 1) else r + 1

/-- The trim length never exceeds the list length. -/
theorem lengthTrim_le_length {R : Type*} [Zero R] [DecidableEq R] :
    ∀ l : List R, lengthTrim l ≤ l.length
  | [] => by simp [lengthTrim]
  | a :: as => by
    simp only [lengthTrim, List.length_cons]
    split
    · split <;> omega
    · have := lengthTrim_le_length as; omega

/-- A list whose `lengthTrim` is `0` reads as the zero polynomial. -/
theorem toPoly_eq_zero_of_lengthTrim_eq_zero {R : Type*} [Semiring R] [DecidableEq R]
    {l : List R} (h : lengthTrim l = 0) : toPoly l = 0 := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [lengthTrim] at h
    split at h
    · rename_i hr
      split at h
      · rename_i ha; rw [toPoly_cons, ha, ih hr]; simp
      · exact absurd h one_ne_zero
    · exact absurd h (by omega)

/-! ## Subtraction of list-polys (over a ring carrier) -/

/-- Negate every coefficient. -/
def negL {R : Type*} [Neg R] : List R → List R
  | [] => []
  | a :: as => (-a) :: negL as

/-- Coefficient-wise difference (padding the shorter with zeros). -/
def subL {R : Type*} [Add R] [Neg R] (as bs : List R) : List R := addL as (negL bs)

/-- `toPoly` of a negated list is `-toPoly`. -/
theorem toPoly_negL {R : Type*} [CommRing R] (as : List R) :
    toPoly (negL as) = -toPoly as := by
  induction as with
  | nil => simp [negL]
  | cons a as ih => simp only [negL, toPoly_cons, ih, map_neg]; ring

/-- `toPoly` is subtractive on `subL`. -/
theorem toPoly_subL {R : Type*} [CommRing R] (as bs : List R) :
    toPoly (subL as bs) = toPoly as - toPoly bs := by
  rw [subL, toPoly_addL, toPoly_negL]; ring

/-! ## The monomial-times-poly building block of long division -/

/-- Prepend `k` zeros: multiply a list-poly by `X^k`. -/
def shiftL {R : Type*} [Zero R] (k : ℕ) (l : List R) : List R :=
  List.replicate k 0 ++ l

/-- `toPoly (shiftL k l) = X^k * toPoly l`. -/
theorem toPoly_shiftL {R : Type*} [CommSemiring R] (k : ℕ) (l : List R) :
    toPoly (shiftL k l) = X ^ k * toPoly l := by
  induction k with
  | zero => simp [shiftL]
  | succ k ih =>
    rw [shiftL, List.replicate_succ, List.cons_append, toPoly_cons, map_zero, zero_add,
      pow_succ]
    rw [show List.replicate k 0 ++ l = shiftL k l from rfl, ih]; ring

/-! ## Long division by a monic divisor -/

/-- One quotient monomial term `c · X^k` as a list-poly (lower `k` zeros, then `c`). -/
def monomialL {R : Type*} [Zero R] (c : R) (k : ℕ) : List R := shiftL k [c]

/-- `toPoly (monomialL c k) = C c * X^k`. -/
theorem toPoly_monomialL {R : Type*} [CommSemiring R] (c : R) (k : ℕ) :
    toPoly (monomialL c k) = C c * X ^ k := by
  rw [monomialL, toPoly_shiftL]; simp [toPoly]

/-- Long division of `f` by a monic `g` (`toPoly g` monic of degree `dg`), fueled; returns the
quotient/remainder pair `(q, r)`. -/
def divmodByMonicFuel {R : Type*} [CommRing R] [DecidableEq R]
    (g : List R) (dg : ℕ) : ℕ → List R → List R × List R
  | 0, f => ([], f)
  | fuel + 1, f =>
    let n := lengthTrim f
    if n ≤ dg then ([], f)
    else
      let k := n - 1 - dg
      let c := f.getD (n - 1) 0
      let term := monomialL c k
      let f' := subL f (mulL term g)
      let (q, r) := divmodByMonicFuel g dg fuel f'
      (addL term q, r)

/-- The division identity for the fueled long division: `toPoly f = toPoly g * toPoly q +
toPoly r`, where `(q, r) = divmodByMonicFuel g dg fuel f`. Proven by induction on `fuel`; the
inductive step is the algebraic tautology `f = g·term + (f − g·term)`. -/
theorem divmodByMonicFuel_spec {R : Type*} [CommRing R] [DecidableEq R]
    (g : List R) (dg : ℕ) (fuel : ℕ) (f : List R) :
    toPoly f =
      toPoly g * toPoly (divmodByMonicFuel g dg fuel f).1
        + toPoly (divmodByMonicFuel g dg fuel f).2 := by
  induction fuel generalizing f with
  | zero => simp [divmodByMonicFuel]
  | succ fuel ih =>
    rw [divmodByMonicFuel]
    simp only
    split
    · simp
    · -- recurse on f' = f − term·g
      set n := lengthTrim f
      set k := n - 1 - dg
      set c := f.getD (n - 1) 0
      set term := monomialL c k
      set f' := subL f (mulL term g)
      have hrec := ih f'
      -- the returned pair is (addL term q, r) with (q,r) the recursive result
      rcases hpair : divmodByMonicFuel g dg fuel f' with ⟨q, r⟩
      simp only
      rw [hpair] at hrec
      simp only at hrec
      -- toPoly f' = toPoly g * toPoly q + toPoly r
      rw [toPoly_addL]
      -- toPoly f = toPoly g * (toPoly term + toPoly q) + toPoly r
      have hf' : toPoly f' = toPoly f - toPoly g * toPoly term := by
        rw [show f' = subL f (mulL term g) from rfl, toPoly_subL, toPoly_mulL]; ring
      rw [hf'] at hrec
      -- now solve
      have : toPoly f = toPoly g * toPoly term + (toPoly g * toPoly q + toPoly r) := by
        linear_combination hrec
      rw [this]; ring

/-- Long division of `f` by a monic `g` of degree `dg`, with fuel `f.length + 1`. -/
def divmodByMonic {R : Type*} [CommRing R] [DecidableEq R]
    (f g : List R) (dg : ℕ) : List R × List R :=
  divmodByMonicFuel g dg (f.length + 1) f

/-- Division identity `toPoly f = toPoly g * toPoly q + toPoly r` for
`(q, r) = divmodByMonic f g dg`. -/
theorem divmodByMonic_spec {R : Type*} [CommRing R] [DecidableEq R]
    (f g : List R) (dg : ℕ) :
    toPoly f =
      toPoly g * toPoly (divmodByMonic f g dg).1 + toPoly (divmodByMonic f g dg).2 :=
  divmodByMonicFuel_spec g dg (f.length + 1) f

/-- Remainder of `f` by monic `g`: `f mod g`. -/
def modByMonicL {R : Type*} [CommRing R] [DecidableEq R] (f g : List R) (dg : ℕ) : List R :=
  (divmodByMonic f g dg).2

/-- `toPoly (modByMonicL f g dg) = toPoly f − toPoly g * toPoly (quotient)`. -/
theorem toPoly_modByMonicL {R : Type*} [CommRing R] [DecidableEq R] (f g : List R) (dg : ℕ) :
    toPoly (modByMonicL f g dg) =
      toPoly f - toPoly g * toPoly (divmodByMonic f g dg).1 := by
  rw [modByMonicL]
  have := divmodByMonic_spec f g dg
  linear_combination -this

/-! ## Making a list-poly monic -/

/-- The leading coefficient of a list-poly: the entry at `lengthTrim f - 1` (`0` for the zero
poly). -/
def leadL {R : Type*} [Zero R] [DecidableEq R] (f : List R) : R :=
  f.getD (lengthTrim f - 1) 0

/-- Scale `f` by the inverse of its leading coefficient: over a field a nonzero `f` becomes monic. -/
def monicizeL {R : Type*} [Zero R] [DecidableEq R] [Inv R] [Mul R] (f : List R) : List R :=
  scaleL (leadL f)⁻¹ f

/-- `toPoly (monicizeL f) = C (leadL f)⁻¹ * toPoly f`: monicization is `C (lead⁻¹) *` at the
polynomial level. -/
theorem toPoly_monicizeL {R : Type*} [Field R] [DecidableEq R] (f : List R) :
    toPoly (monicizeL f) = C (leadL f)⁻¹ * toPoly f := by
  rw [monicizeL, toPoly_scaleL]

/-- `toPoly f ∣ toPoly (monicizeL f)`: the original divides its monicization (it is
`C (lead⁻¹) *` it). -/
theorem dvd_toPoly_monicizeL {R : Type*} [Field R] [DecidableEq R] (f : List R) :
    toPoly f ∣ toPoly (monicizeL f) := by
  rw [toPoly_monicizeL]; exact Dvd.intro_left _ rfl

/-! ## `lengthTrim` ↔ degree bridges -/

/-- Entries past the trim length are the default `0`: `lengthTrim l ≤ i → l.getD i 0 = 0`. The
pure-`Nat` core of the degree bound. -/
theorem getD_eq_zero_of_lengthTrim_le {R : Type*} [Zero R] [DecidableEq R] :
    ∀ (l : List R) (i : ℕ), lengthTrim l ≤ i → l.getD i 0 = 0
  | [], i, _ => by simp [List.getD]
  | a :: as, i, hi => by
    simp only [lengthTrim] at hi
    split at hi
    · rename_i hr
      -- lengthTrim as = 0
      cases i with
      | zero =>
        -- need the head to be 0; split forced a = 0 (else trim length 1 > 0)
        split at hi
        · rename_i ha; simpa [List.getD] using ha
        · exact absurd hi (by omega)
      | succ j =>
        rw [List.getD_cons_succ]
        exact getD_eq_zero_of_lengthTrim_le as j (by omega)
    · rename_i hr
      -- lengthTrim as = r ≠ 0, trim length r + 1 ≤ i
      cases i with
      | zero => exact absurd hi (by omega)
      | succ j =>
        rw [List.getD_cons_succ]
        exact getD_eq_zero_of_lengthTrim_le as j (by omega)

/-- Sharper degree bound: `degree (toPoly l) < lengthTrim l` (all coefficients at index
`≥ lengthTrim l` vanish). -/
theorem toPoly_degree_lt_lengthTrim {R : Type*} [Semiring R] [DecidableEq R] (l : List R) :
    (toPoly l).degree < (lengthTrim l : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro i hi
  rw [coeff_toPoly]
  exact getD_eq_zero_of_lengthTrim_le l i (by exact_mod_cast hi)

/-- For a nonzero-reading list, the leading coefficient (`leadL`, the entry at `lengthTrim - 1`)
is exactly `(toPoly l).coeff (lengthTrim l - 1)`. -/
theorem coeff_lengthTrim_sub_one {R : Type*} [Semiring R] [DecidableEq R] (l : List R) :
    (toPoly l).coeff (lengthTrim l - 1) = leadL l := by
  rw [coeff_toPoly, leadL]

/-- The leading entry `leadL l` is nonzero whenever the trim length is positive (the entry at
`lengthTrim - 1` is by construction the last nonzero one). -/
theorem leadL_ne_zero_of_lengthTrim_pos {R : Type*} [Zero R] [DecidableEq R] :
    ∀ {l : List R}, 0 < lengthTrim l → leadL l ≠ 0
  | [], hpos, _ => by simp [lengthTrim] at hpos
  | a :: as, hpos, hc => by
    by_cases hr : lengthTrim as = 0
    · -- trim of tail is 0, so trim of (a::as) is `if a = 0 then 0 else 1`
      by_cases ha : a = 0
      · simp only [lengthTrim, if_pos hr, if_pos ha] at hpos; omega
      · simp only [leadL, lengthTrim, if_pos hr, if_neg ha, Nat.sub_self,
          List.getD_cons_zero] at hc
        exact ha hc
    · -- trim of tail is r ≠ 0, so trim of (a::as) is r + 1, leading entry is tail's leading
      have hp : 0 < lengthTrim as := Nat.pos_of_ne_zero hr
      refine leadL_ne_zero_of_lengthTrim_pos hp ?_
      simp only [leadL] at hc ⊢
      simp only [lengthTrim, if_neg hr] at hc
      rwa [show lengthTrim as + 1 - 1 = (lengthTrim as - 1) + 1 by omega,
        List.getD_cons_succ] at hc

/-- A list reads as the zero polynomial **iff** its trim length is `0`. -/
theorem toPoly_eq_zero_iff_lengthTrim {R : Type*} [Semiring R] [DecidableEq R] (l : List R) :
    toPoly l = 0 ↔ lengthTrim l = 0 := by
  refine ⟨fun h => ?_, toPoly_eq_zero_of_lengthTrim_eq_zero⟩
  by_contra hne
  have hpos : 0 < lengthTrim l := Nat.pos_of_ne_zero hne
  apply leadL_ne_zero_of_lengthTrim_pos hpos
  have := coeff_lengthTrim_sub_one l
  rw [h, coeff_zero] at this
  exact this.symm

/-- Converse degree bound: a small polynomial degree forces a small trim length. If
`degree (toPoly l) < d` then `lengthTrim l ≤ d` (else the nonzero leading entry at index
`lengthTrim l - 1 ≥ d` would witness a coefficient above the degree bound). -/
theorem lengthTrim_le_of_degree_lt {R : Type*} [Semiring R] [DecidableEq R] {l : List R} {d : ℕ}
    (h : (toPoly l).degree < (d : WithBot ℕ)) : lengthTrim l ≤ d := by
  by_contra hle
  have hlt : d < lengthTrim l := Nat.lt_of_not_le hle
  have hpos : 0 < lengthTrim l := Nat.lt_of_le_of_lt (Nat.zero_le d) hlt
  -- leading entry is nonzero
  have hlead : (toPoly l).coeff (lengthTrim l - 1) ≠ 0 := by
    rw [coeff_lengthTrim_sub_one]; exact leadL_ne_zero_of_lengthTrim_pos hpos
  -- but degree < d ≤ lengthTrim l - 1, so that coeff must vanish
  apply hlead
  apply coeff_eq_zero_of_degree_lt
  refine lt_of_lt_of_le h ?_
  exact_mod_cast Nat.le_sub_one_of_lt hlt

/-! ## The long-division step strictly drops the trim length -/

/-- Per-step trim decrease: with `toPoly g` monic of `natDegree dg`, `n := lengthTrim f`, `n > dg`,
`c := f.getD (n-1) 0`, `term := monomialL c (n-1-dg)`, the residue `subL f (mulL term g)` has
strictly smaller trim length than `f`. -/
theorem lengthTrim_subL_mulL_lt {R : Type*} [CommRing R] [DecidableEq R]
    {g : List R} {dg : ℕ} (hg : IsMonicOfDegree (toPoly g) dg)
    {f : List R} (hn : dg < lengthTrim f) :
    lengthTrim (subL f
        (mulL (monomialL (f.getD (lengthTrim f - 1) 0) (lengthTrim f - 1 - dg)) g))
      < lengthTrim f := by
  set n := lengthTrim f with hndef
  have hn1 : 1 ≤ n := by omega
  set c := f.getD (n - 1) 0 with hcdef
  set k := n - 1 - dg with hkdef
  set term := monomialL c k with htermdef
  -- the residue at the polynomial level
  have hpoly : toPoly (subL f (mulL term g))
      = toPoly f - C c * X ^ k * toPoly g := by
    rw [toPoly_subL, toPoly_mulL, toPoly_monomialL]
  -- it suffices that the residue's degree is < n - 1, since then lengthTrim ≤ n - 1 < n
  have hdeglt : (toPoly f - C c * X ^ k * toPoly g).degree < ((n - 1 : ℕ) : WithBot ℕ) := by
    rw [degree_lt_iff_coeff_zero]
    intro m hm
    have hmn : n - 1 ≤ m := by exact_mod_cast hm
    have hkm : k ≤ m := by omega
    rw [coeff_sub, show C c * X ^ k * toPoly g = C c * (X ^ k * toPoly g) by ring,
      coeff_C_mul, coeff_X_pow_mul', if_pos hkm]
    rcases eq_or_lt_of_le hmn with rfl | hmgt
    · -- m = n - 1 : leading coeffs both = c, cancel
      have hcf : (toPoly f).coeff (n - 1) = c := by rw [coeff_toPoly]
      have hmk : (n - 1) - k = dg := by omega
      have hgc : (toPoly g).coeff dg = 1 := by
        have := hg.monic.coeff_natDegree; rwa [hg.natDegree_eq] at this
      rw [hcf, hmk, hgc]
      ring
    · -- m > n - 1, i.e. m ≥ n : both coeffs vanish
      have hfm : (toPoly f).coeff m = 0 := by
        apply coeff_eq_zero_of_degree_lt
        refine lt_of_lt_of_le (toPoly_degree_lt_lengthTrim f) ?_
        rw [← hndef]; exact_mod_cast by omega
      have hgm : (toPoly g).coeff (m - k) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [hg.natDegree_eq]; omega
      rw [hfm, hgm, mul_zero, sub_zero]
  have hle : lengthTrim (subL f (mulL term g)) ≤ n - 1 := by
    refine lengthTrim_le_of_degree_lt ?_
    rw [hpoly]; exact hdeglt
  omega

/-- Remainder degree bound: with `toPoly g` monic of degree `dg` and `fuel ≥ lengthTrim f`, the
fueled long-division remainder has `lengthTrim ≤ dg`. -/
theorem lengthTrim_divmodByMonicFuel_snd_le {R : Type*} [CommRing R] [DecidableEq R]
    {g : List R} {dg : ℕ} (hg : IsMonicOfDegree (toPoly g) dg) :
    ∀ (fuel : ℕ) (f : List R), lengthTrim f ≤ fuel →
      lengthTrim (divmodByMonicFuel g dg fuel f).2 ≤ dg := by
  intro fuel
  induction fuel with
  | zero =>
    intro f hf
    simp only [divmodByMonicFuel]
    omega
  | succ fuel ih =>
    intro f hf
    rw [divmodByMonicFuel]
    simp only
    split
    · rename_i hstop; exact hstop
    · rename_i hstop
      -- lengthTrim f > dg, recurse on f' with smaller trim
      have hgt : dg < lengthTrim f := by omega
      set f' := subL f (mulL (monomialL (f.getD (lengthTrim f - 1) 0) (lengthTrim f - 1 - dg)) g)
        with hf'def
      have hdec : lengthTrim f' < lengthTrim f := lengthTrim_subL_mulL_lt hg hgt
      have hf'fuel : lengthTrim f' ≤ fuel := by omega
      have := ih f' hf'fuel
      -- the returned remainder is the recursive remainder
      rcases hpair : divmodByMonicFuel g dg fuel f' with ⟨q, r⟩
      simp only
      rw [hpair] at this
      simpa using this

/-- For a nonzero-reading list, `natDegree (toPoly l) = lengthTrim l - 1`. -/
theorem natDegree_toPoly_eq {R : Type*} [Semiring R] [DecidableEq R] {l : List R}
    (hl : lengthTrim l ≠ 0) : (toPoly l).natDegree = lengthTrim l - 1 := by
  have hpos : 0 < lengthTrim l := Nat.pos_of_ne_zero hl
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · refine Nat.le_sub_one_of_lt ?_
    have hd := toPoly_degree_lt_lengthTrim l
    have hne : toPoly l ≠ 0 := by
      rw [Ne, toPoly_eq_zero_iff_lengthTrim]; exact hl
    exact (Polynomial.natDegree_lt_iff_degree_lt hne).2 hd
  · rw [coeff_lengthTrim_sub_one]; exact leadL_ne_zero_of_lengthTrim_pos hpos

/-- The monicization of a nonzero-reading list is monic of degree `lengthTrim g - 1`
(scaling by the inverse leading coefficient, a unit). -/
theorem isMonicOfDegree_monicizeL {R : Type*} [Field R] [DecidableEq R] {g : List R}
    (hg : lengthTrim g ≠ 0) : IsMonicOfDegree (toPoly (monicizeL g)) (lengthTrim g - 1) := by
  have hpos : 0 < lengthTrim g := Nat.pos_of_ne_zero hg
  have hlead : leadL g ≠ 0 := leadL_ne_zero_of_lengthTrim_pos hpos
  have hgne : toPoly g ≠ 0 := by rw [Ne, toPoly_eq_zero_iff_lengthTrim]; exact hg
  -- the leading coefficient of `toPoly g` is `leadL g`
  have hlc : (toPoly g).leadingCoeff = leadL g := by
    rw [leadingCoeff, natDegree_toPoly_eq hg, coeff_lengthTrim_sub_one]
  rw [toPoly_monicizeL]
  refine ⟨?_, ?_⟩
  · -- natDegree (C lead⁻¹ * toPoly g) = lengthTrim g - 1
    rw [natDegree_C_mul (by simpa using hlead), natDegree_toPoly_eq hg]
  · -- monic: (leadL g)⁻¹ * leadingCoeff = 1
    exact monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [hlc]; exact inv_mul_cancel₀ hlead)

/-! ## Euclidean gcd over `𝔽_p` -/

/-- For a nonzero `g`, the monicization divides `g` (the scaling factor `C (leadL g)⁻¹` is a unit),
so `g` and `monicizeL g` are associated. -/
theorem toPoly_monicizeL_dvd {R : Type*} [Field R] [DecidableEq R] {g : List R}
    (hg : lengthTrim g ≠ 0) : toPoly (monicizeL g) ∣ toPoly g := by
  have hlead : leadL g ≠ 0 := leadL_ne_zero_of_lengthTrim_pos (Nat.pos_of_ne_zero hg)
  rw [toPoly_monicizeL]
  refine ⟨C (leadL g), ?_⟩
  rw [mul_comm (C (leadL g)⁻¹) (toPoly g), mul_assoc, ← C_mul, inv_mul_cancel₀ hlead, C_1,
    mul_one]

/-- The Euclidean gcd recursion over a field, fueled. `g = 0` → return `f`; otherwise reduce
`r = f mod (monicize g)` and recurse `gcd (monicize g) r`. -/
def gcdByMonicFuel {R : Type*} [Field R] [DecidableEq R] : ℕ → List R → List R → List R
  | 0, f, _ => f
  | fuel + 1, f, g =>
    if lengthTrim g = 0 then f
    else
      let gm := monicizeL g
      let r := modByMonicL f gm (lengthTrim g - 1)
      gcdByMonicFuel fuel gm r

/-- Two-sided gcd divisibility: with `lengthTrim g ≤ fuel`, the fueled Euclidean gcd
`d = gcdByMonicFuel fuel f g` divides both inputs, `toPoly d ∣ toPoly f ∧ toPoly d ∣ toPoly g`. -/
theorem gcdByMonicFuel_dvd {R : Type*} [Field R] [DecidableEq R] :
    ∀ (fuel : ℕ) (f g : List R), lengthTrim g ≤ fuel →
      toPoly (gcdByMonicFuel fuel f g) ∣ toPoly f ∧
        toPoly (gcdByMonicFuel fuel f g) ∣ toPoly g := by
  intro fuel
  induction fuel with
  | zero =>
    intro f g hfuel
    -- lengthTrim g = 0, so g reads 0; result is f
    have hg0 : lengthTrim g = 0 := Nat.le_zero.1 hfuel
    simp only [gcdByMonicFuel]
    refine ⟨dvd_rfl, ?_⟩
    rw [toPoly_eq_zero_of_lengthTrim_eq_zero hg0]; exact dvd_zero _
  | succ fuel ih =>
    intro f g hfuel
    rw [gcdByMonicFuel]
    split
    · rename_i hg0
      refine ⟨dvd_rfl, ?_⟩
      rw [toPoly_eq_zero_of_lengthTrim_eq_zero hg0]; exact dvd_zero _
    · rename_i hg0
      set dg := lengthTrim g - 1 with hdgdef
      set gm := monicizeL g with hgmdef
      set r := modByMonicL f gm dg with hrdef
      -- gm monic of degree dg
      have hgmmon : IsMonicOfDegree (toPoly gm) dg := isMonicOfDegree_monicizeL hg0
      -- remainder degree bound: lengthTrim r ≤ dg
      have hrbound : lengthTrim r ≤ dg := by
        rw [hrdef, modByMonicL, divmodByMonic]
        refine lengthTrim_divmodByMonicFuel_snd_le hgmmon (f.length + 1) f ?_
        have := lengthTrim_le_length f; omega
      -- so lengthTrim r ≤ fuel for the recursive call (dg = lengthTrim g - 1 < lengthTrim g ≤ fuel+1)
      have hgpos : 0 < lengthTrim g := Nat.pos_of_ne_zero hg0
      have hrfuel : lengthTrim r ≤ fuel := by omega
      obtain ⟨hdgm, hdr⟩ := ih gm r hrfuel
      refine ⟨?_, ?_⟩
      · -- d ∣ f : f = gm * q + r
        have hrem : toPoly f = toPoly gm * toPoly (divmodByMonic f gm dg).1 + toPoly r := by
          rw [hrdef, modByMonicL]
          have := divmodByMonic_spec f gm dg
          linear_combination this
        rw [hrem]
        exact dvd_add (hdgm.mul_right _) hdr
      · -- d ∣ g : d ∣ gm and gm ∣ g (associated)
        exact hdgm.trans (toPoly_monicizeL_dvd hg0)

/-- Euclidean gcd over `𝔽_p`, with fuel `g.length + 1` (always enough, since
`lengthTrim g ≤ g.length`). -/
def gcdByMonic {R : Type*} [Field R] [DecidableEq R] (f g : List R) : List R :=
  gcdByMonicFuel (g.length + 1) f g

/-- gcd divides its first argument: `toPoly (gcdByMonic f g) ∣ toPoly f`. -/
theorem gcdByMonic_dvd_left {R : Type*} [Field R] [DecidableEq R] (f g : List R) :
    toPoly (gcdByMonic f g) ∣ toPoly f :=
  (gcdByMonicFuel_dvd (g.length + 1) f g (by have := lengthTrim_le_length g; omega)).1

/-- gcd divides its second argument: `toPoly (gcdByMonic f g) ∣ toPoly g`. -/
theorem gcdByMonic_dvd_right {R : Type*} [Field R] [DecidableEq R] (f g : List R) :
    toPoly (gcdByMonic f g) ∣ toPoly g :=
  (gcdByMonicFuel_dvd (g.length + 1) f g (by have := lengthTrim_le_length g; omega)).2

/-! ## Exact division when the divisor divides the dividend -/

/-- Exact division: with `toPoly g` monic of degree `dg` dividing `toPoly f`, the remainder
vanishes and `toPoly f = toPoly g * toPoly (divmodByMonic f g dg).1`. -/
theorem toPoly_eq_mul_quotient_of_dvd {R : Type*} [Field R] [DecidableEq R]
    {g : List R} {dg : ℕ} (hg : IsMonicOfDegree (toPoly g) dg)
    {f : List R} (hdvd : toPoly g ∣ toPoly f) :
    toPoly f = toPoly g * toPoly (divmodByMonic f g dg).1 := by
  -- division identity: f = g*q + r
  have hid := divmodByMonic_spec f g dg
  set q := (divmodByMonic f g dg).1
  set r := (divmodByMonic f g dg).2
  -- r = f - g*q, so g ∣ r
  have hgr : toPoly g ∣ toPoly r := by
    have : toPoly r = toPoly f - toPoly g * toPoly q := by linear_combination -hid
    rw [this]; exact dvd_sub hdvd (Dvd.dvd.mul_right (dvd_refl _) _)
  -- degree r < dg = degree g
  have hgdeg : (toPoly g).degree = (dg : WithBot ℕ) := by
    rw [degree_eq_natDegree hg.monic.ne_zero, hg.natDegree_eq]
  have hrbound : lengthTrim r ≤ dg :=
    lengthTrim_divmodByMonicFuel_snd_le hg (f.length + 1) f
      (by have := lengthTrim_le_length f; omega)
  have hrdeg : (toPoly r).degree < (dg : WithBot ℕ) :=
    lt_of_lt_of_le (toPoly_degree_lt_lengthTrim r) (by exact_mod_cast hrbound)
  -- r = 0
  have hr0 : toPoly r = 0 := by
    refine eq_zero_of_dvd_of_degree_lt hgr ?_
    rw [hgdeg]; exact hrdeg
  -- conclude
  rw [hid, hr0, add_zero]

/-! ## The Frobenius power `X^(p^d) mod f` -/

/-- Modular product over a field: `(a * b) mod f`, with `f` monic of degree `df`. -/
def mulModL {R : Type*} [Field R] [DecidableEq R] (f : List R) (df : ℕ) (a b : List R) : List R :=
  modByMonicL (mulL a b) f df

/-- Binary exponentiation `base ^ e mod f` (`f` monic of degree `df`), fueled by the bit length
of `e`. Squares and conditionally multiplies, reducing mod `f` at each product. -/
def powModL {R : Type*} [Field R] [DecidableEq R]
    (f : List R) (df : ℕ) : ℕ → List R → ℕ → List R
  | 0, _, _ => [1]
  | fuel + 1, base, e =>
    if e = 0 then [1]
    else
      let half := powModL f df fuel (mulModL f df base base) (e / 2)
      if e % 2 = 1 then mulModL f df base half else half

/-- The Frobenius power `X^(p^d) mod f` over `𝔽_p`: repeated squaring of `[0, 1]` to the exponent
`p ^ d`, reduced mod the monic `f` of degree `df`. -/
def xPowModF (p d : ℕ) [Fact p.Prime] (f : List (ZMod p)) (df : ℕ) : List (ZMod p) :=
  powModL f df (p ^ d + 1) [0, 1] (p ^ d)

/-! ## Distinct-degree factorization (DDF) -/

/-- The product of DDF blocks (`mulL`-fold of the coefficient lists, from `[1]`). -/
def ddfProduct {R : Type*} [Zero R] [One R] [Add R] [Mul R]
    (bs : List (ℕ × List R)) : List R :=
  bs.foldr (fun b acc => mulL b.2 acc) [1]

/-- `toPoly` of a block product is the product of the blocks' `toPoly`s. -/
theorem toPoly_ddfProduct {R : Type*} [CommSemiring R] (bs : List (ℕ × List R)) :
    toPoly (ddfProduct bs) = (bs.map (fun b => toPoly b.2)).prod := by
  induction bs with
  | nil => simp [ddfProduct, toPoly]
  | cons b bs ih =>
    rw [ddfProduct, List.foldr_cons, toPoly_mulL, List.map_cons, List.prod_cons,
      ← ddfProduct, ih]

/-- The DDF recursion over `𝔽_p`: at degree `d`, peel the positive-degree block
`gcd(f, X^(p^d) − X)`, monicize, divide it out, recurse with `d + 1`; emit the residual as a
trailing block otherwise. -/
def ddfAux (p : ℕ) [Fact p.Prime] : ℕ → ℕ → List (ZMod p) → List (ℕ × List (ZMod p))
  | 0, _, f => [(0, f)]
  | fuel + 1, d, f =>
    let df := lengthTrim f - 1
    let sep := subL (xPowModF p d f df) [0, 1]
    let gd := gcdByMonic f sep
    if 1 < lengthTrim gd then
      let gdm := monicizeL gd
      let cof := (divmodByMonic f gdm (lengthTrim gd - 1)).1
      (d, gdm) :: ddfAux p fuel (d + 1) cof
    else
      [(d, f)]

/-- Distinct-degree factorization of `f` over `𝔽_p`, starting at degree `1` with fuel
`f.length + 1`. -/
def ddf (p : ℕ) [Fact p.Prime] (f : List (ZMod p)) : List (ℕ × List (ZMod p)) :=
  ddfAux p (f.length + 1) 1 f

/-- DDF multiply-back (recursion): the blocks of `ddfAux p fuel d f` multiply back to `f`,
`toPoly (ddfProduct (ddfAux p fuel d f)) = toPoly f`. -/
theorem ddfAux_prod (p : ℕ) [Fact p.Prime] :
    ∀ (fuel d : ℕ) (f : List (ZMod p)),
      toPoly (ddfProduct (ddfAux p fuel d f)) = toPoly f := by
  intro fuel
  induction fuel with
  | zero =>
    intro d f
    simp only [ddfAux, ddfProduct, List.foldr_cons, List.foldr_nil, toPoly_mulL, toPoly_cons,
      toPoly_nil]
    simp
  | succ fuel ih =>
    intro d f
    rw [ddfAux]
    simp only
    split
    · rename_i hgd
      -- peel branch
      set df := lengthTrim f - 1 with hdfdef
      set sep := subL (xPowModF p d f df) [0, 1] with hsepdef
      set gd := gcdByMonic f sep with hgddef
      set gdm := monicizeL gd with hgdmdef
      set dgd := lengthTrim gd - 1 with hdgddef
      set cof := (divmodByMonic f gdm dgd).1 with hcofdef
      -- product = toPoly gdm * toPoly (product of rest)
      rw [ddfProduct, List.foldr_cons, ← ddfProduct, toPoly_mulL]
      -- IH: product of rest = cof
      rw [ih (d + 1) cof]
      -- now: toPoly gdm * toPoly cof = toPoly f, via exact division
      have hgdne : lengthTrim gd ≠ 0 := by omega
      have hgdmmon : IsMonicOfDegree (toPoly gdm) dgd := isMonicOfDegree_monicizeL hgdne
      -- gdm ∣ f : gd ∣ f and gdm ∣ gd
      have hgddvd : toPoly gd ∣ toPoly f := gcdByMonic_dvd_left f sep
      have hgdmdvd : toPoly gdm ∣ toPoly f := (toPoly_monicizeL_dvd hgdne).trans hgddvd
      have := toPoly_eq_mul_quotient_of_dvd hgdmmon hgdmdvd
      rw [hcofdef]; exact this.symm
    · -- no-peel branch: [(d, f)]
      simp only [ddfProduct, List.foldr_cons, List.foldr_nil, toPoly_mulL, toPoly_cons,
        toPoly_nil]
      simp

/-- DDF multiply-back: `toPoly (ddfProduct (ddf p f)) = toPoly f` — the distinct-degree blocks
multiply back to the input. -/
theorem ddf_prod (p : ℕ) [Fact p.Prime] (f : List (ZMod p)) :
    toPoly (ddfProduct (ddf p f)) = toPoly f :=
  ddfAux_prod p (f.length + 1) 1 f

/-! ## `native_decide` validation of the multiply-back -/

/-- DDF blocks of `x² − 1` over `𝔽₃` multiply back to `x² − 1` (list-level, `native_decide`). -/
example : ddfProduct (ddf 3 ([2, 0, 1] : List (ZMod 3))) = ([2, 0, 1] : List (ZMod 3)) := by
  native_decide

/-- DDF blocks of `x⁴ − 1` over `𝔽₅` multiply back to `x⁴ − 1` (list-level, `native_decide`). -/
example : ddfProduct (ddf 5 ([4, 0, 0, 0, 1] : List (ZMod 5)))
    = ([4, 0, 0, 0, 1] : List (ZMod 5)) := by
  native_decide

/-- DDF blocks of the `𝔽₃`-irreducible `x² + 1` multiply back to `x² + 1` (list-level,
`native_decide`): multiply-back holds even when `f` is itself irreducible (a single block). -/
example : ddfProduct (ddf 3 ([1, 0, 1] : List (ZMod 3))) = ([1, 0, 1] : List (ZMod 3)) := by
  native_decide

/-- The Frobenius power `X³ mod (x² − 1)` over `𝔽₃` reduces to `X` (`native_decide`). -/
example : xPowModF 3 1 ([2, 0, 1] : List (ZMod 3)) 2 = ([0, 1, 0, 0] : List (ZMod 3)) := by
  native_decide

/-! ## Equal-degree factorization (EDF): the Cantor–Zassenhaus split polynomial -/

/-- The Cantor–Zassenhaus split polynomial `(X + a)^((p^d − 1)/2) − 1 mod f` over `𝔽_p` (`p` odd),
for a shift `a : ZMod p`, with `f` monic of degree `df`. Computed by modular exponentiation of the
base `X + a = [a, 1]` to the half-power `(p^d − 1)/2`, then subtracting `1`. -/
def edfSplitPoly (p d : ℕ) [Fact p.Prime] (f : List (ZMod p)) (df : ℕ) (a : ZMod p) :
    List (ZMod p) :=
  subL (powModL f df ((p ^ d - 1) / 2 + 1) [a, 1] ((p ^ d - 1) / 2)) [1]

/-- One Cantor–Zassenhaus split attempt `gcd(f, (X + a)^((p^d − 1)/2) − 1)`, a possibly-trivial
factor of `f` for the shift `a` (always divides `f`). -/
def edfSplitOne (p d : ℕ) [Fact p.Prime] (f : List (ZMod p)) (a : ZMod p) : List (ZMod p) :=
  gcdByMonic f (edfSplitPoly p d f (lengthTrim f - 1) a)

/-! ## The deterministic shift sweep -/

/-- The deterministic Cantor–Zassenhaus shift sweep for a DDF degree-`d` block: split `f` until
every factor has degree `≤ d`, sweeping the shift `a` and recursing on both halves of each proper
split. -/
def edfBlock (p d : ℕ) [Fact p.Prime] : ℕ → ℕ → List (ZMod p) → List (List (ZMod p))
  | 0, _, f => [f]
  | fuel + 1, a, f =>
    if lengthTrim f ≤ d + 1 then [f]
    else
      let g := edfSplitOne p d f (a : ZMod p)
      if 1 < lengthTrim g ∧ lengthTrim g < lengthTrim f then
        let gm := monicizeL g
        let cof := (divmodByMonic f gm (lengthTrim g - 1)).1
        edfBlock p d fuel (a + 1) gm ++ edfBlock p d fuel (a + 1) cof
      else
        edfBlock p d fuel (a + 1) f

/-! ## Full equal-degree factorization -/

/-- The product of EDF factors (`mulL`-fold of the coefficient lists, from `[1]`): the multiply-back
target for `edf` soundness. -/
def edfProduct {R : Type*} [Zero R] [One R] [Add R] [Mul R] (fs : List (List R)) : List R :=
  fs.foldr (fun b acc => mulL b acc) [1]

/-- `toPoly` of an EDF factor product is the product of the factors' `toPoly`s. -/
theorem toPoly_edfProduct {R : Type*} [CommSemiring R] (fs : List (List R)) :
    toPoly (edfProduct fs) = (fs.map toPoly).prod := by
  induction fs with
  | nil => simp [edfProduct, toPoly]
  | cons b fs ih =>
    rw [edfProduct, List.foldr_cons, toPoly_mulL, List.map_cons, List.prod_cons, ← edfProduct, ih]

/-- Full equal-degree factorization of `f` over `𝔽_p`: run the deterministic shift sweep `edfBlock`
on each DDF block (degree tag `b.1`, block `b.2`) starting at shift `0`, and flatten to the complete
list of factor coefficient-lists. -/
def edf (p : ℕ) [Fact p.Prime] (f : List (ZMod p)) : List (List (ZMod p)) :=
  (ddf p f).flatMap (fun b => edfBlock p b.1 (b.2.length + 1) 0 b.2)

/-! ## EDF multiply-back soundness -/

/-- `toPoly (edfProduct (xs ++ ys)) = toPoly (edfProduct xs) * toPoly (edfProduct ys)`: the factor
product is multiplicative over list concatenation (the two halves of a proper split). -/
theorem toPoly_edfProduct_append {R : Type*} [CommSemiring R] (xs ys : List (List R)) :
    toPoly (edfProduct (xs ++ ys)) =
      toPoly (edfProduct xs) * toPoly (edfProduct ys) := by
  rw [toPoly_edfProduct, toPoly_edfProduct, toPoly_edfProduct, List.map_append, List.prod_append]

/-- EDF per-block multiply-back: the factors `edfBlock p d fuel a f` produces multiply back to `f`,
`toPoly (edfProduct (edfBlock p d fuel a f)) = toPoly f`. -/
theorem edfBlock_prod (p d : ℕ) [Fact p.Prime] :
    ∀ (fuel a : ℕ) (f : List (ZMod p)),
      toPoly (edfProduct (edfBlock p d fuel a f)) = toPoly f := by
  intro fuel
  induction fuel with
  | zero =>
    intro a f
    simp only [edfBlock, edfProduct, List.foldr_cons, List.foldr_nil, toPoly_mulL, toPoly_cons,
      toPoly_nil]
    simp
  | succ fuel ih =>
    intro a f
    rw [edfBlock]
    simp only
    split
    · -- stop branch: [f]
      simp only [edfProduct, List.foldr_cons, List.foldr_nil, toPoly_mulL, toPoly_cons, toPoly_nil]
      simp
    · split
      · rename_i hsplit
        -- proper split: recurse on gm and cof
        set g := edfSplitOne p d f (a : ZMod p) with hgdef
        set gm := monicizeL g with hgmdef
        set cof := (divmodByMonic f gm (lengthTrim g - 1)).1 with hcofdef
        rw [toPoly_edfProduct_append, ih (a + 1) gm, ih (a + 1) cof]
        -- exact division: toPoly f = toPoly gm * toPoly cof
        have hgne : lengthTrim g ≠ 0 := by omega
        have hgmmon : IsMonicOfDegree (toPoly gm) (lengthTrim g - 1) :=
          isMonicOfDegree_monicizeL hgne
        have hgdvd : toPoly g ∣ toPoly f := gcdByMonic_dvd_left _ _
        have hgmdvd : toPoly gm ∣ toPoly f := (toPoly_monicizeL_dvd hgne).trans hgdvd
        have := toPoly_eq_mul_quotient_of_dvd hgmmon hgmdvd
        rw [hcofdef]; exact this.symm
      · -- no split: advance shift, recurse on f unchanged
        exact ih (a + 1) f

/-- The factor product of a `flatMap` telescopes to the product of the per-element factor products:
`toPoly (edfProduct (l.flatMap g)) = ∏ toPoly (edfProduct (g b))`. By induction on `l` via the
concatenation multiplicativity `toPoly_edfProduct_append`. -/
theorem toPoly_edfProduct_flatMap {R : Type*} [CommSemiring R] {α : Type*}
    (g : α → List (List R)) (l : List α) :
    toPoly (edfProduct (l.flatMap g)) =
      (l.map (fun b => toPoly (edfProduct (g b)))).prod := by
  induction l with
  | nil => simp [edfProduct, toPoly]
  | cons b l ih =>
    rw [List.flatMap_cons, toPoly_edfProduct_append, ih, List.map_cons, List.prod_cons]

/-- EDF multiply-back: `toPoly (edfProduct (edf p f)) = toPoly f` — the full equal-degree
factorization multiplies back to the input. -/
theorem edf_prod (p : ℕ) [Fact p.Prime] (f : List (ZMod p)) :
    toPoly (edfProduct (edf p f)) = toPoly f := by
  rw [edf, toPoly_edfProduct_flatMap]
  -- each block's EDF factor product is the block itself
  have hblk : (fun b : ℕ × List (ZMod p) =>
      toPoly (edfProduct (edfBlock p b.1 (b.2.length + 1) 0 b.2)))
        = fun b => toPoly b.2 := by
    funext b; exact edfBlock_prod p b.1 (b.2.length + 1) 0 b.2
  rw [hblk]
  -- ∏ toPoly b.2 over DDF blocks = toPoly (ddfProduct (ddf p f)) = toPoly f
  rw [← toPoly_ddfProduct, ddf_prod]

/-! ## `native_decide` validation of the equal-degree split -/

/-- The `d = 1` DDF block `(x − 1)(x − 2) = x² + 2x + 2` over `𝔽₅` splits into its two linear
factors `x − 1 = x + 4` (`[4, 1]`) and `x − 2 = x + 3` (`[3, 1]`) — a `k = 2` same-degree split
(`native_decide`; trailing zero from un-trimmed monicization). -/
example : edfBlock 5 1 4 0 ([2, 2, 1] : List (ZMod 5)) = [[4, 1, 0], [3, 1]] := by
  native_decide

/-- EDF multiply-back for `(x − 1)(x − 2)` over `𝔽₅`: the factor product is `x² + 2x + 2` (the
input, with a benign trailing zero; `toPoly` agrees, cf. `edf_prod`) (`native_decide`). -/
example : edfProduct (edf 5 ([2, 2, 1] : List (ZMod 5))) = [2, 2, 1, 0] := by
  native_decide

/-- The `d = 1` block `x⁴ − 1 = (x−1)(x−2)(x−3)(x−4)` over `𝔽₅` splits into all **four** distinct
linear factors (roots `{1, 2, 3, 4}`) — a `k = 4` same-degree split (`native_decide`). The trailing
`[1]` is the constant DDF block; the four `[c, 1]`/`[c, 1, 0]` are the linear factors. -/
example : edf 5 ([4, 0, 0, 0, 1] : List (ZMod 5))
    = [[1, 1, 0], [4, 1], [2, 1, 0], [3, 1], [1]] := by
  native_decide

/-- EDF multiply-back for `x⁴ − 1` over `𝔽₅`: the four linear factors re-multiply to `x⁴ − 1` (the
input, with benign trailing zeros; `toPoly` agrees, cf. `edf_prod`) (`native_decide`). -/
example : edfProduct (edf 5 ([4, 0, 0, 0, 1] : List (ZMod 5))) = [4, 0, 0, 0, 1, 0, 0] := by
  native_decide
