import DeepWiki.SymbolicIntegration.ComputablePolynomialIrreducibility

/-! # Computable `𝔽_p` polynomial factorization: distinct-degree factorization (Cantor–Zassenhaus)

The foundation layer of full Zassenhaus factorization — and hence of a **complete** `ℚ`-
irreducibility decider. `ComputablePolynomialIrreducibility` gives a *sound but one-way* mod-`p`
irreducibility **test**; the wall is `x⁴ + 1`, irreducible over `ℚ` yet reducible mod every
prime. Going from *testing* to *deciding* needs the full factorization of `f mod p`, then a
Hensel lift to mod `p^k`, then recombination to `ℤ`-factors. This file builds the **distinct-degree
factorization (DDF)** layer with its **multiply-back soundness** — the first half of the mod-`p`
factorization — on top of the monic **long-division primitives** (`divmodByMonic` + the division
identity `divmodByMonic_spec`). Now **built and gate-clean**: the long division, the
`lengthTrim`↔degree bridges, the Euclidean `gcd`, the Frobenius power, the DDF, and its
axiom-clean multiply-back invariant. Equal-degree splitting / Hensel factor-lift / recombination
remain the documented roadmap (bottom).

**Reused engine.** Polynomials are coefficient `List (ZMod p)`, low-to-high (Horner), with
`toPoly`/`addL`/`mulL`/`scaleL`/`coeff_toPoly` from `ComputablePolynomialIrreducibility`
(Mathlib's `Polynomial` `+`/`*` are `noncomputable`, so neither `decide` nor `native_decide`
reduce them). The computable primitives over the field `𝔽_p`:

* **`divmodByMonic`** — long division of a list-poly by a **monic** divisor (`ZMod p` is a
  field, so a monic divisor suffices for everything DDF needs), carrying the **division identity**
  `toPoly f = toPoly g * toPoly q + toPoly r`. The per-step trim decrease (`lengthTrim_subL_mulL_lt`,
  top-coefficient cancellation) gives the remainder degree bound and division termination.
* **`gcdByMonic`** — the Euclidean gcd, monic-normalized each step via `monicizeL`. Soundness
  `gcdByMonicFuel_dvd`: the result divides **both** inputs (left-divisibility is the DDF
  multiply-back invariant). When a monic divisor divides the dividend the division is exact
  (`toPoly_eq_mul_quotient_of_dvd`, remainder vanishes by degree).
* **`xPowModF`** — the Frobenius power `X^(p^d) mod f` by repeated squaring of the list `[0,1]`
  (`powModL`/`mulModL`), each product reduced `modByMonicL`-style. Computable,
  `native_decide`-able for small `p, d`.

**Distinct-degree factorization (`ddf`).** For `d = 1, 2, …`: `gcd(f, X^(p^d) − X)` is the
product of all degree-`d` irreducible factors of (squarefree) `f`; peel it off (monicize, divide
out), recurse on the cofactor. `ddf` returns `List (ℕ × List (ZMod p))`, each entry `(d, gₐ)` a
block. (The *value* `ddf` computes — the block list whose product is `f` — is sound; the degree
*tag* `d` is correct only once Frobenius-power correctness is added, see scope.)

**★ Soundness — multiply-back (`ddfAux_prod` / `ddf_prod`).** The DDF blocks multiply (via
`mulL`, mod `p`) **back to** `f`: `toPoly (ddfProduct (ddf p f)) = toPoly f`. This is the key
structural invariant, the engine being that each peel is an **exact** division (`gcd ∣ f`, monic
divisor ⇒ zero remainder). It is **axiom-clean** `[propext, Classical.choice, Quot.sound]` (no
`native`, no `sorry`); the `native_decide` lives only in the concrete examples (`x²−1` mod 3,
`x⁴−1` mod 5, the irreducible `x²+1` mod 3). The per-block **degree** soundness (each block is a
product of degree-`d` irreducibles, and the per-*factor* irreducibility) is the deeper claim that
needs Frobenius-power correctness plus equal-degree splitting — scoped below.

**★ The rest of Zassenhaus (scope, for the complete `ℚ`-decider).** After DDF:
0. **Frobenius-power correctness** (`toPoly (xPowModF p d f df) ≡ X^(p^d) (mod toPoly f)`) makes
   the DDF degree *tags* correct — the abstract `ddf_prod` multiply-back here does **not** need it
   (gcd-divides-first-arg is unconditional), but per-block degree structure does. Provable from
   `divmodByMonic_spec` (each reduction step is `≡ mod f`) by induction over the squaring.
1. **Equal-degree factorization (EDF)** splits a degree-`d` block (a product of `k` distinct
   degree-`d` irreducibles) into its `k` factors. The Cantor–Zassenhaus split: for `p` odd,
   `gcd(f, (X + a)^((p^d − 1)/2) − 1)` is a nontrivial factor for a "good" shift `a`. Lean has
   **no randomness**, so `a` is iterated deterministically (`a = 0, 1, 2, …`); a *good* shift is
   guaranteed to exist within `ZMod p` for `k ≥ 2`, but the *termination/completeness* of the
   deterministic sweep is the EDF proof obligation. (`p = 2` uses the trace-map variant.) This
   layer makes the per-factor irreducibility provable.
2. **Hensel FACTOR-lift mod `p^k`.** Lift the coprime mod-`p` factorization `f ≡ g·h` to mod
   `p^k`. *Mathlib status:* `hensels_lemma` (`Mathlib/NumberTheory/Padics/Hensel.lean`) and
   `Mathlib/RingTheory/Henselian.lean` are **root-finding** only — the polynomial *factor*-lift
   (quadratic lift of a coprime factorization, the Zassenhaus form) must be **built**: given
   `f ≡ g·h (mod p^m)` with `s·g + t·h ≡ 1 (mod p)`, produce `g', h'` mod `p^{2m}` with the
   same product. The Bézout cofactors lift alongside.
3. **Recombination.** Search subsets of the lifted mod-`p^k` factors whose product has small
   enough coefficients (bounded by `p^k / 2`, Mignotte bound) to be a true `ℤ`-factor.
   *Mathlib status:* **not present**; an exponential subset search (LLL later tames it), with a
   factorization-correctness predicate yielding the complete decider.
So the complete-`ℚ`-decider campaign is: **DDF (here)** → EDF → Hensel-factor-lift →
recombination. DDF + its multiply-back invariant is the tractable, high-value first brick. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ## Degree of a list-poly and the leading entry

For the division and gcd recursions we read a list's polynomial degree off its **last nonzero
entry**. `lengthTrim` is the index past the last nonzero entry (`= 0` for the zero poly); for a
nonzero list it is `natDegree + 1`. Working with `lengthTrim` keeps everything `Nat`-valued and
`Decidable`. -/

/-- Index one past the last nonzero coefficient (`0` if all coefficients vanish): the
"effective length" of a list-poly. `toPoly`'s `natDegree` is `lengthTrim l - 1` when nonzero. -/
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

/-! ## Subtraction of list-polys (over a ring carrier)

`ZMod p` is a `CommRing`, so the engine gains negation. `negL`/`subL` are computable; their
`toPoly` bridges follow from `toPoly_addL`/`toPoly_scaleL`. -/

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

/-! ## The monomial-times-poly building block of long division

A long-division step subtracts `c · X^k · g` from `f`. `shiftL k l` prepends `k` zeros
(multiply by `X^k`); `scaleL c` multiplies by `C c`. Their `toPoly` bridges are the two
identities the division identity is assembled from. -/

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

/-! ## Long division by a monic divisor

`divmodByMonic f g dg` divides the list-poly `f` by a **monic** divisor `g` whose `toPoly` is
monic of `natDegree = dg` (so `g`'s entry at index `dg` is `1`). It returns `(q, r)` with the
**division identity** `toPoly f = toPoly g * toPoly q + toPoly r`. The recursion is on the fuel
`Fin (f.length + 1)`-style decreasing measure given by `lengthTrim f`; we use an explicit fuel
parameter for a clean structural recursion, taking `fuel = f.length + 1` at the entry point.

Each step: if `lengthTrim f ≤ dg`, the quotient term is `0` and `r := f`. Otherwise set
`k := lengthTrim f - 1 - dg` and `c := f.getD (lengthTrim f - 1) 0` (the leading coeff; the
divisor's leading coeff is `1`), append `c·X^k` to the quotient and recurse on
`f − c·X^k·g`. The division identity holds **per step** as the tautology
`toPoly f = toPoly g * (c·X^k) + (toPoly f − toPoly g * (c·X^k))`, so soundness needs no
degree-decrease reasoning — only that the recursion terminates (the fuel). -/

/-- One quotient monomial term `c · X^k` as a list-poly (lower `k` zeros, then `c`). -/
def monomialL {R : Type*} [Zero R] (c : R) (k : ℕ) : List R := shiftL k [c]

/-- `toPoly (monomialL c k) = C c * X^k`. -/
theorem toPoly_monomialL {R : Type*} [CommSemiring R] (c : R) (k : ℕ) :
    toPoly (monomialL c k) = C c * X ^ k := by
  rw [monomialL, toPoly_shiftL]; simp [toPoly]

/-- Long division of `f` by a monic `g` (`toPoly g` monic of degree `dg`), fueled. Returns the
quotient/remainder pair `(q, r)`. Soundness is the carried division identity, not the size of
`r`. -/
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

/-- **★ Division identity.** `toPoly f = toPoly g * toPoly q + toPoly r` for
`(q, r) = divmodByMonic f g dg`. The structural multiply-back fact behind DDF soundness. -/
theorem divmodByMonic_spec {R : Type*} [CommRing R] [DecidableEq R]
    (f g : List R) (dg : ℕ) :
    toPoly f =
      toPoly g * toPoly (divmodByMonic f g dg).1 + toPoly (divmodByMonic f g dg).2 :=
  divmodByMonicFuel_spec g dg (f.length + 1) f

/-- Remainder of `f` by monic `g`: `f mod g`. -/
def modByMonicL {R : Type*} [CommRing R] [DecidableEq R] (f g : List R) (dg : ℕ) : List R :=
  (divmodByMonic f g dg).2

/-- `toPoly (modByMonicL f g dg) = toPoly f − toPoly g * toPoly (quotient)`: the remainder
differs from `f` by a multiple of `g`. -/
theorem toPoly_modByMonicL {R : Type*} [CommRing R] [DecidableEq R] (f g : List R) (dg : ℕ) :
    toPoly (modByMonicL f g dg) =
      toPoly f - toPoly g * toPoly (divmodByMonic f g dg).1 := by
  rw [modByMonicL]
  have := divmodByMonic_spec f g dg
  linear_combination -this

/-! ## Making a list-poly monic

`leadL f` reads the leading coefficient (`f.getD (lengthTrim f - 1) 0`); `monicizeL f` scales
`f` by its inverse, so over a field a nonzero `f` becomes monic. The `toPoly` bridge is the
scale bridge applied to the inverse leading coefficient. The gcd recursion below uses
`monicizeL` to normalize each divisor so `modByMonicL` (which assumes a monic divisor) applies. -/

/-- The leading coefficient of a list-poly: the entry at `lengthTrim f - 1` (`0` for the zero
poly). For nonzero `f`, this is `(toPoly f).leadingCoeff`. -/
def leadL {R : Type*} [Zero R] [DecidableEq R] (f : List R) : R :=
  f.getD (lengthTrim f - 1) 0

/-- Scale `f` by the inverse of its leading coefficient: over a field, a nonzero `f` becomes
monic. -/
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

/-! ## `lengthTrim` ↔ degree bridges

To prove the Euclidean gcd terminates and is sound we need `lengthTrim` to track the polynomial
degree: `degree (toPoly l) < lengthTrim l` (sharper than the `length` bound), the leading
coefficient `(toPoly l).coeff (lengthTrim l - 1) = leadL l`, and that this leading coefficient is
nonzero exactly when `toPoly l ≠ 0`. These convert the list-level recursion into a clean
polynomial-degree decrease. -/

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

/-! ## The long-division step strictly drops the trim length

The single fact that makes division terminate and gives the remainder its degree bound: when
`toPoly g` is monic of degree `dg` and `lengthTrim f = n > dg`, subtracting the matching leading
term `c·X^(n-1-dg)·g` (with `c = f`'s leading entry) **cancels the top coefficient**, so
`lengthTrim (subL f (mulL term g)) < n`. Proven by showing every coefficient of the difference at
index `≥ n-1` vanishes (`f` and `term·g` agree there: both `0` above `n-1`, both `c` at `n-1`). -/

/-- **★ Per-step trim decrease.** With `toPoly g` monic of `natDegree dg`, `n := lengthTrim f`,
`n > dg`, `c := f.getD (n-1) 0`, `term := monomialL c (n-1-dg)`: the long-division residue
`subL f (mulL term g)` has strictly smaller trim length than `f`. -/
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

/-- **Remainder degree bound.** With `toPoly g` monic of degree `dg` and `fuel ≥ lengthTrim f`,
the fueled long-division remainder has `lengthTrim ≤ dg` (the loop reaches its `≤ dg` stop before
running out of fuel, by the per-step decrease). -/
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

/-! ## Euclidean gcd over `𝔽_p`

`gcdByMonic f g` is the polynomial gcd over the field, normalizing the divisor with `monicizeL`
at each step so `modByMonicL` (monic divisor) applies. We recurse with explicit fuel; with
`fuel = g.length + 1` the loop always reaches the `g = 0` base (each remainder strictly drops in
`lengthTrim`). The carried invariant is **divisibility of both arguments** when fuel suffices:
`toPoly d ∣ toPoly f` and `toPoly d ∣ toPoly g`. The first is exactly what makes a DDF peel exact
(remainder `0`), the source of multiply-back soundness. -/

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

/-- **★ Two-sided gcd divisibility.** With sufficient fuel (`lengthTrim g ≤ fuel`), the fueled
Euclidean gcd divides **both** inputs: `toPoly d ∣ toPoly f ∧ toPoly d ∣ toPoly g`, where
`d = gcdByMonicFuel fuel f g`. By induction on `fuel`; the step uses the remainder degree bound
(to keep enough fuel for the recursive call), the remainder identity `f = gm * q + r`, and that
`gm = monicizeL g` is associated to `g`. The left half is the DDF multiply-back invariant. -/
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

/-- **★ gcd divides its first argument** — the DDF multiply-back invariant.
`toPoly (gcdByMonic f g) ∣ toPoly f`. -/
theorem gcdByMonic_dvd_left {R : Type*} [Field R] [DecidableEq R] (f g : List R) :
    toPoly (gcdByMonic f g) ∣ toPoly f :=
  (gcdByMonicFuel_dvd (g.length + 1) f g (by have := lengthTrim_le_length g; omega)).1

/-- gcd divides its second argument: `toPoly (gcdByMonic f g) ∣ toPoly g`. -/
theorem gcdByMonic_dvd_right {R : Type*} [Field R] [DecidableEq R] (f g : List R) :
    toPoly (gcdByMonic f g) ∣ toPoly g :=
  (gcdByMonicFuel_dvd (g.length + 1) f g (by have := lengthTrim_le_length g; omega)).2

/-! ## Exact division when the divisor divides the dividend

If a **monic** `g` (degree `dg`) divides `f`, the long division is exact: the remainder is the
zero polynomial and `toPoly f = toPoly g * toPoly q`. Proof: the carried remainder `r = f mod g`
satisfies `g ∣ r` (since `g ∣ f` and `g ∣ g*q`) but `degree r < dg = degree g`, so `r = 0` over
the field (a domain). This is what makes each DDF peel exact, the engine of multiply-back. -/

/-- **★ Exact division.** With `toPoly g` monic of degree `dg` (so `g ≠ 0`) dividing `toPoly f`,
the division is exact: `toPoly f = toPoly g * toPoly (divmodByMonic f g dg).1` (the remainder
vanishes). -/
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

/-! ## The Frobenius power `X^(p^d) mod f`

Modular multiplication `mulModL f df a b := (a * b) mod f` and binary exponentiation `powModL`
let us compute `X^(p^d) mod f` (`xPowModF`) by repeated squaring of `[0, 1]` (the list of `X`),
each product reduced mod the **monic** `f`. The reduction `mod f` keeps the intermediate degrees
bounded, so the values stay small — `native_decide`-able for small `p, d` (keep `p ≤ 7`, `d ≤ 4`:
`p^d` is the exponent and the squaring count is `log₂(p^d)`). The `mod toPoly f` reading
(`toPoly (mulModL f df a b) ≡ toPoly a * toPoly b`) follows from the division identity; the full
`X^(p^d)`-correctness is **not** needed for DDF multiply-back (gcd-divides-first-arg is
unconditional), only for the per-block degree structure. -/

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

/-- The Frobenius power `X^(p^d) mod f` over `𝔽_p`: repeated squaring of `[0, 1]` (the polynomial
`X`) to the exponent `p ^ d`, reduced mod the monic `f` of degree `df`. Computable; the basis of
the distinct-degree split `gcd(f, X^(p^d) − X)`. -/
def xPowModF (p d : ℕ) [Fact p.Prime] (f : List (ZMod p)) (df : ℕ) : List (ZMod p) :=
  powModL f df (p ^ d + 1) [0, 1] (p ^ d)

/-! ## Distinct-degree factorization (DDF)

For `d = 1, 2, …` the degree-`d` block of (squarefree) `f` is `gcd(f, X^(p^d) − X)` — the product
of all degree-`d` irreducible factors. `ddfAux` peels this block off, monicizes it (`gdm`), divides
`f` by it (`divmodByMonic`), and recurses on the cofactor with `d + 1`, accumulating `(d, gdm)`. To
keep the **multiply-back** invariant exact it only peels when the block has positive degree (so the
monic block has degree `≥ 1` and the division by it is exact, `gdm ∣ f`); otherwise the remaining
`f` is emitted as a single trailing block. The returned `List (ℕ × List (ZMod p))` is the list of
blocks (degree tag + coefficient list). -/

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

/-- The DDF recursion over `𝔽_p`: at degree `d` with current poly `f`, peel the positive-degree
block `gcd(f, X^(p^d) − X)`, monicize, divide it out, recurse with `d + 1`; emit the residual as a
trailing block when no positive-degree block remains. Fueled by recursion depth. -/
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

/-- **★ DDF multiply-back (recursion).** The blocks of `ddfAux p fuel d f` multiply back to `f`:
`toPoly (ddfProduct (ddfAux p fuel d f)) = toPoly f`. By induction on `fuel`; the peel step uses
that the monicized block `gdm` is monic of degree `≥ 1` dividing `f` (so the division is exact,
`f = gdm * cof`) and the IH `product(rest) = cof`. The key structural soundness of DDF; the trailing
emit and the no-peel branch are the trivial `product = f` cases. -/
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

/-- **★ DDF multiply-back.** `toPoly (ddfProduct (ddf p f)) = toPoly f` (mod `p`): the
distinct-degree blocks multiply back to the input. The key structural invariant of DDF, the
foundation of factorization correctness. -/
theorem ddf_prod (p : ℕ) [Fact p.Prime] (f : List (ZMod p)) :
    toPoly (ddfProduct (ddf p f)) = toPoly f :=
  ddfAux_prod p (f.length + 1) 1 f

/-! ## `native_decide` validation of the multiply-back

The concrete computational content behind `ddf_prod`: the **list-level** product of the DDF blocks
equals the input list (`toPoly` is `noncomputable`, so we validate the engine's `mulL`-fold output
directly, which `toPoly` then sends to the polynomial identity). Keep `p ≤ 7`, `d` small — `X^(p^d)`
grows fast. The `Fact (Nat.Prime _)` instances come from `ComputablePolynomialIrreducibility`. -/

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

/-! ## Equal-degree factorization (EDF): the Cantor–Zassenhaus split polynomial

A DDF block at degree `d` is a product of `k` **distinct** degree-`d` irreducibles; EDF splits it
into the `k` factors. For `p` odd the Cantor–Zassenhaus split uses the polynomial
`(X + a)^((p^d − 1)/2) − 1 mod f` for a shift `a ∈ 𝔽_p`. Over the residue field at each irreducible
factor, `(X + a)^((p^d − 1)/2)` is `±1` (Euler's criterion: it is a square root of `1`), so the gcd
of `f` with this polynomial selects exactly the factors on which the value is `+1` — a proper
factor for a "good" shift `a`. Lean has no randomness, so `a` is swept `0, 1, 2, …` deterministically.

`edfSplitPoly f d a` computes `(X + a)^((p^d − 1)/2) − 1 mod f` via the existing modular
exponentiation `powModL` (base `[a, 1]` = `X + a`, exponent `(p^d − 1)/2`, reduced mod the monic
`f`). Keep `p, d` small — the exponent `(p^d − 1)/2` drives the squaring count. -/

/-- The Cantor–Zassenhaus split polynomial `(X + a)^((p^d − 1)/2) − 1 mod f` over `𝔽_p` (`p` odd),
for a shift `a : ZMod p`, with `f` monic of degree `df`. Computed by modular exponentiation of the
base `X + a = [a, 1]` to the half-power `(p^d − 1)/2`, then subtracting `1`. -/
def edfSplitPoly (p d : ℕ) [Fact p.Prime] (f : List (ZMod p)) (df : ℕ) (a : ZMod p) :
    List (ZMod p) :=
  subL (powModL f df ((p ^ d - 1) / 2 + 1) [a, 1] ((p ^ d - 1) / 2)) [1]

/-- One Cantor–Zassenhaus split attempt: `gcd(f, (X + a)^((p^d − 1)/2) − 1)`, a (possibly trivial)
factor of `f` for the shift `a`. Always divides `f` (`gcdByMonic_dvd_left`), so peeling it is an
exact division — the source of EDF multiply-back soundness; whether it is a *proper* factor depends
on `a` being a "good" shift (the sweep below tries successive `a`). -/
def edfSplitOne (p d : ℕ) [Fact p.Prime] (f : List (ZMod p)) (a : ZMod p) : List (ZMod p) :=
  gcdByMonic f (edfSplitPoly p d f (lengthTrim f - 1) a)
