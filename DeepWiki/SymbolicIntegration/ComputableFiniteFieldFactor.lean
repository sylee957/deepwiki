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
