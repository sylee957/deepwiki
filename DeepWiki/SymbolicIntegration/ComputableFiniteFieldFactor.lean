import DeepWiki.SymbolicIntegration.ComputablePolynomialIrreducibility

/-! # Computable `𝔽_p` polynomial factorization: distinct-degree factorization (Cantor–Zassenhaus)

The foundation layer of full Zassenhaus factorization — and hence of a **complete** `ℚ`-
irreducibility decider. `ComputablePolynomialIrreducibility` gives a *sound but one-way* mod-`p`
irreducibility **test**; the wall is `x⁴ + 1`, irreducible over `ℚ` yet reducible mod every
prime. Going from *testing* to *deciding* needs the full factorization of `f mod p`, then a
Hensel lift to mod `p^k`, then recombination to `ℤ`-factors. This file builds the **first sub-brick**:
the monic **long-division primitives** over `𝔽_p` (`divmodByMonic` + the division identity
`toPoly f = toPoly g * toPoly q + toPoly r`, `divmodByMonic_spec`). The DDF itself, `gcd`, the
Frobenius power, and the multiply-back soundness described below are the **roadmap — NOT yet in
the body** (a prior build of those was lost to an infrastructure failure; this commit salvages
the gate-clean division-primitives brick, to be continued).

**Reused engine.** Polynomials are coefficient `List (ZMod p)`, low-to-high (Horner), with
`toPoly`/`addL`/`mulL`/`scaleL`/`coeff_toPoly` from `ComputablePolynomialIrreducibility`
(Mathlib's `Polynomial` `+`/`*` are `noncomputable`, so neither `decide` nor `native_decide`
reduce them). We add the two missing computable primitives over the field `𝔽_p`:

* **`divmodByMonic`** — long division of a list-poly by a **monic** divisor (`ZMod p` is a
  field, so a monic divisor suffices for everything DDF needs). The carried invariant is the
  **division identity** `toPoly f = toPoly g * toPoly q + toPoly r` — proven directly, since
  each long-division step rewrites `f` as `(term)·g + (f − term·g)`, an algebraic tautology at
  the `toPoly` level. This makes the *multiply-back* soundness structural, independent of any
  degree bookkeeping.
* **`gcdByMonic`** — the Euclidean gcd, monic-normalized, via `subResL`/`monicizeL`.
* **`xPowModF`** — the Frobenius power `X^(p^d) mod f` by repeated squaring of the list `[0,1]`,
  each square reduced `divmodByMonic`-style. Computable, `native_decide`-able for small `p, d`.

**Distinct-degree factorization (`ddf`).** For `d = 1, 2, …`: `gcd(f, X^(p^d) − X)` is the
product of all degree-`d` irreducible factors of (squarefree) `f`; peel it off, recurse on the
cofactor. `ddf` returns `List (ℕ × List (ZMod p))`, each entry `(d, gₐ)` a block whose factors
are exactly the degree-`d` irreducibles.

**★ Soundness — multiply-back (`ddfAux_prod` / `ddf_prod`).** The DDF blocks multiply (via
`mulL`, mod `p`) **back to** `f`: `toPoly (ddfProduct (ddf f n)) = toPoly f`. This is the key
structural invariant. It is **axiom-clean** `[propext, Classical.choice, Quot.sound]` (no
`native`, no `sorry`); the `native_decide` lives only in the concrete examples. The per-block
**degree** soundness (each block has degree a multiple of its index `d`, being a product of
degree-`d` irreducibles) is the deeper claim that needs equal-degree splitting for the
*per-factor* statement — scoped below.

**★ The rest of Zassenhaus (scope, for the complete `ℚ`-decider).** After DDF:
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

/-- **Remainder degree bound.** With `toPoly g` monic of degree `dg ≥ 1` and `fuel ≥ lengthTrim f`,
the fueled long-division remainder has `lengthTrim ≤ dg` (the loop reaches its `≤ dg` stop before
running out of fuel, by the per-step decrease). -/
theorem lengthTrim_divmodByMonicFuel_snd_le {R : Type*} [CommRing R] [DecidableEq R]
    {g : List R} {dg : ℕ} (hg : IsMonicOfDegree (toPoly g) dg) (hdg : 1 ≤ dg) :
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

/-! ## Euclidean gcd over `𝔽_p`

`gcdByMonic f g` is the polynomial gcd over the field, normalizing the divisor with `monicizeL`
at each step so `modByMonicL` (monic divisor) applies. We recurse with explicit fuel; with
`fuel = g.length + 1` the loop always reaches the `g = 0` base (each remainder strictly drops in
`lengthTrim`). The carried invariant is **divisibility of both arguments** when fuel suffices:
`toPoly d ∣ toPoly f` and `toPoly d ∣ toPoly g`. The first is exactly what makes a DDF peel exact
(remainder `0`), the source of multiply-back soundness. -/

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
