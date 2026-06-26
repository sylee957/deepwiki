import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-! # A computable, SOUND irreducibility test for `ℤ[X]` via mod-`p` reduction

The tractable, provably-sound core of Zassenhaus factorization: its first step is to
factor `f` modulo a prime `p`, and a monic integer polynomial that stays **irreducible**
after reduction mod `p` is already irreducible over `ℚ`. This gives a `native_decide`-able
**irreducibility certificate** generator: present `f` by its `ℤ`-coefficient list, reduce
mod a prime `p` into `ZMod p` (the SAME finite-field arithmetic the torsion files
`ComputableGeneralTorsionLight` / `ComputableDivisorOrder` use), decide irreducibility over
the **finite** field `𝔽_p`, and lift to `ℚ` by Gauss's lemma
(`Polynomial.Monic.irreducible_of_irreducible_map`).

**Why a coefficient-list engine.** Mathlib's `Polynomial` `+`/`*`/`map` are `noncomputable`
(they pick a `Classical.decEq`), so neither `decide` nor `native_decide` reduces them. Like
the torsion files, the *computation* therefore runs on a **coefficient `List (ZMod p)`**
(low-to-high, Horner form), with a tiny self-contained `toPoly : List R → R[X]` bridge. The
single primitive `coeff_toPoly` (`(toPoly l).coeff i = l.getD i 0`) gives both the
multiplicativity bridge `toPoly_mulL` and the reconstruction of a monic divisor as a
candidate list. The abstract irreducibility statement lives on Mathlib `Polynomial`.

**The 𝔽_p decision (fully computable).** A monic `fp : (ZMod p)[X]` of degree `n` is
irreducible iff it has **no** monic proper factor `q` of degree `1 ≤ d ≤ n/2`
(`Polynomial.Monic.irreducible_iff_lt_natDegree_lt`). Since `fp` is monic, such a factor
comes with a monic cofactor of degree `n − d`. Both monic factors are coefficient lists
ending in `1`; the search enumerates the lower coefficients (the `Fintype (ZMod p)` to the
power of the degree) and checks `mulL q g ≠ fcoeffs` by **list equality** — only `+`/`*` on
`ZMod p`, so it `native_decide`-compiles.

**★ Soundness** (`irreducibleByModP_sound`): `(toPolyZ cf).Monic → irreducibleByModP p cf =
true → Irreducible (toPolyZ cf)`, axiom-clean `[propext, Classical.choice, Quot.sound]` (no
`native`, no `sorry`). The `native_decide` lives only in the example certificates.

**★ 𝔽_p-level completeness** (`irreducibleListModP_iff_irreducible`): over the *finite field*
the decision is correct in **both** directions — `irreducibleListModP cf n ↔ Irreducible
(toPoly cf)` for a monic degree-`n` target. So the search neither over- nor under-reports
irreducibility *of the reduction*; the one-wayness is purely the `𝔽_p ⟹ ℚ` lift, never the
finite-field decision. (Reverse direction via the degree-bounded `toPoly_eq_of_padCoeffs_eq`:
a matching `padCoeffs` forces a genuine factorization, contradicting irreducibility.)

**Honest scope — sound, ONE-WAY over `ℚ`.** This is irreducibility **testing**: it can only
*confirm* `ℚ`-irreducibility. `ℚ`-completeness of the mod-`p` test is **fundamentally
impossible**, not a missing lemma: `x⁴ + 1` (= `Φ₈`) is `ℚ`-irreducible yet reducible mod
*every* prime (its Galois group `(ℤ/2)²` has no 4-cycle, so by Frobenius no prime is inert).
The witnesses `irreducible_toPolyZ_X_pow_four_add_one` (axiom-clean, via `cyclotomic.irreducible`)
and `irreducibleByModP_X_pow_four_add_one_false` (`native_decide`, `false` at `p = 2,3,5,7`)
pin this wall. So `irreducibleByModP = false` is **inconclusive** — never read it as "reducible".

**Full Zassenhaus / a COMPLETE `ℚ`-decider — scope.** Going from *testing* to *factoring*
(hence a complete `ℚ`-irreducibility decision: irreducible ⟺ only the trivial factorization)
needs the rest of Zassenhaus on top of this mod-`p` factorization:
1. **Hensel lifting** the mod-`p` factorization to mod `p^k` for `k` large enough that the
   integer factors are recovered (`p^k > 2·(coeff bound)`). *Mathlib status:* Hensel's lemma
   exists only in the **root-finding p-adic** form (`Mathlib/NumberTheory/Padics/Hensel.lean`,
   `hensels_lemma`; also `Mathlib/RingTheory/Henselian.lean`) — **not** the polynomial
   *factor*-lifting / quadratic-lift-of-a-coprime-factorization form Zassenhaus uses; that
   layer must be **built**.
2. **Combinatorial recombination** — search subsets of the lifted mod-`p^k` factors whose
   product has small enough coefficients to be a true `ℤ`-factor (the exponential step LLL
   later tames). *Mathlib status:* **not present**; must be built.
3. **A factorization-correctness predicate** then yields the complete decider. *Mathlib
   status:* the abstract `UniqueFactorizationMonoid` theory of `ℤ[X]`/`ℚ[X]` is present, but no
   *computable* `ℚ`-factorization algorithm.
So the complete-decider campaign is mapped — Hensel-factor-lift + recombination are the two
build items — and is a strictly larger follow-up. The irreducibility *test* here is the
high-value, sound, tractable piece: it removes per-radicand manual irreducibility discharge
by making `Irreducible` `native_decide`-able.

**De-pin connection.** Our radicands are `X² − f(x)` over the function field
`ℚ(x) = RatFunc ℚ`, not over `ℚ`. Two routes wire this test in later (documented, not forced
here): (a) **specialize** `x ↦ a` to drop `ℚ(x)[X] → ℚ[X]`; an irreducible specialization
forces the generic polynomial irreducible (specialization can only *add* factors); (b) the
cheaper `n = 2` route — if `f(a)` is a non-square in `ℚ` for some `a`, then `f` is a
non-square in `ℚ(x)`, so `X² − f` is irreducible. Route (b) is cleanest for the
square-radical de-pin; this file proves the `ℚ`-side engine both routes feed. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ## The computable coefficient-`List` polynomial engine

Coefficients low-to-high: `[a₀, a₁, …]` ↦ `a₀ + a₁ X + …`. `toPoly` is the Horner reading
`toPoly (a :: as) = C a + X * toPoly as`. `addL`/`mulL` are computable list arithmetic; the
bridges `toPoly_addL` / `toPoly_mulL` connect them to Mathlib `Polynomial` `+`/`*`. -/

/-- Horner reading of a coefficient list as a polynomial: `[a₀,…,aₖ] ↦ Σ aᵢ Xⁱ`.
(Noncomputable, as Mathlib `Polynomial` arithmetic is — used only for the soundness bridge,
never in the `native_decide` search.) -/
noncomputable def toPoly {R : Type*} [Semiring R] : List R → R[X]
  | [] => 0
  | a :: as => C a + X * toPoly as

/-- Scale every coefficient by `c` (the `C c * ·` action on lists). -/
def scaleL {R : Type*} [Mul R] (c : R) : List R → List R
  | [] => []
  | a :: as => (c * a) :: scaleL c as

/-- Coefficient-wise sum of two lists, padding the shorter with zeros. -/
def addL {R : Type*} [Add R] : List R → List R → List R
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: addL as bs

/-- Polynomial multiplication on coefficient lists (Horner / shift-and-add). -/
def mulL {R : Type*} [Zero R] [Add R] [Mul R] : List R → List R → List R
  | [], _ => []
  | a :: as, bs => addL (scaleL a bs) (0 :: mulL as bs)

@[simp] theorem toPoly_nil {R : Type*} [Semiring R] : toPoly ([] : List R) = 0 := rfl

@[simp] theorem toPoly_cons {R : Type*} [Semiring R] (a : R) (as : List R) :
    toPoly (a :: as) = C a + X * toPoly as := rfl

/-- **The engine primitive.** The `i`-th coefficient of `toPoly l` is `l.getD i 0`: the
Horner reading recovers exactly the list entries (default `0` past the end). Everything else
follows from this. -/
theorem coeff_toPoly {R : Type*} [Semiring R] (l : List R) (i : ℕ) :
    (toPoly l).coeff i = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp [toPoly]
  | cons a as ih =>
    rw [toPoly_cons, coeff_add]
    cases i with
    | zero => simp [coeff_C, List.getD]
    | succ i =>
      rw [coeff_C, if_neg (Nat.succ_ne_zero i), zero_add, coeff_X_mul, ih, List.getD]
      rfl

/-- `toPoly` of a scaled list is `C c *` the polynomial. -/
theorem toPoly_scaleL {R : Type*} [CommSemiring R] (c : R) (as : List R) :
    toPoly (scaleL c as) = C c * toPoly as := by
  induction as with
  | nil => simp [scaleL]
  | cons a as ih =>
    simp only [scaleL, toPoly_cons, ih, C_mul]
    ring

/-- `toPoly` is additive on `addL`. -/
theorem toPoly_addL {R : Type*} [CommSemiring R] (as bs : List R) :
    toPoly (addL as bs) = toPoly as + toPoly bs := by
  induction as generalizing bs with
  | nil => simp [addL]
  | cons a as ih =>
    cases bs with
    | nil => simp [addL]
    | cons b bs =>
      simp only [addL, toPoly_cons, ih, C_add]
      ring

/-- **★ Multiplicativity bridge.** `toPoly (mulL a b) = toPoly a * toPoly b`: the engine's
list multiplication realizes Mathlib polynomial multiplication. The homomorphism fact behind
the whole search. -/
theorem toPoly_mulL {R : Type*} [CommSemiring R] (as bs : List R) :
    toPoly (mulL as bs) = toPoly as * toPoly bs := by
  induction as with
  | nil => simp [mulL]
  | cons a as ih =>
    simp only [mulL, toPoly_addL, toPoly_scaleL, toPoly_cons, ih, map_zero, zero_add]
    ring

/-- **Length-matched injectivity.** Equal `toPoly` and equal length force equal lists (the
coefficient maps agree at every index `< length`). Lifts list equality from polynomial
equality, used to reach the search's list-equality contradiction. -/
theorem list_eq_of_toPoly_eq {R : Type*} [Semiring R] [Inhabited R] {l₁ l₂ : List R}
    (hlen : l₁.length = l₂.length) (h : toPoly l₁ = toPoly l₂) : l₁ = l₂ := by
  apply List.ext_getElem! hlen
  intro i
  by_cases hi : i < l₁.length
  · have h1 : l₁[i]! = l₁.getD i 0 := by
      rw [List.getD_eq_getElem _ _ hi, getElem!_pos l₁ i hi]
    have h2 : l₂[i]! = l₂.getD i 0 := by
      rw [List.getD_eq_getElem _ _ (hlen ▸ hi), getElem!_pos l₂ i (hlen ▸ hi)]
    rw [h1, h2, ← coeff_toPoly, ← coeff_toPoly, h]
  · rw [getElem!_neg l₁ i hi, getElem!_neg l₂ i (by omega)]

/-! ## Monic candidate lists and their degrees

A coefficient list `lower ++ [1]` (lower of length `d`) reads as a **monic** polynomial of
`natDegree` exactly `d`. These are the factor candidates the search enumerates. -/

/-- `toPoly lower` has `degree < lower.length` (a length-`d` list reads as a poly of degree
`< d`): all coefficients at index `≥ d` are `0`. -/
theorem toPoly_degree_lt {R : Type*} [Semiring R] (lower : List R) :
    (toPoly lower).degree < lower.length := by
  rw [degree_lt_iff_coeff_zero]
  intro i hi
  rw [coeff_toPoly, List.getD_eq_default]
  exact_mod_cast hi

/-- The polynomial of a candidate list `lower ++ [1]` is `X^d + (toPoly lower)`, where
`d = lower.length`. -/
theorem toPoly_append_one {R : Type*} [CommSemiring R] (lower : List R) :
    toPoly (lower ++ [1]) = toPoly lower + X ^ lower.length := by
  induction lower with
  | nil => simp [toPoly]
  | cons a as ih =>
    simp only [List.cons_append, toPoly_cons, ih, List.length_cons]
    ring

/-- A candidate list `lower ++ [1]` (lower of length `d`) reads as a monic poly of degree
exactly `d`. -/
theorem isMonicOfDegree_toPoly_append_one {R : Type*} [CommSemiring R] [Nontrivial R]
    (lower : List R) : IsMonicOfDegree (toPoly (lower ++ [1])) lower.length := by
  rw [toPoly_append_one]
  have hlt : (toPoly lower).degree < ((lower.length : ℕ) : WithBot ℕ) :=
    (toPoly_degree_lt lower)
  refine ⟨?_, ?_⟩
  · refine natDegree_eq_of_degree_eq_some ?_
    rw [add_comm]
    refine (degree_add_eq_left_of_degree_lt ?_).trans (degree_X_pow _)
    exact hlt.trans_le (degree_X_pow _).ge
  · rw [add_comm]
    exact monic_X_pow_add hlt

/-- **Reconstruction.** Any monic `q` of `natDegree` exactly `d` is `toPoly (lower ++ [1])`
for `lower = [q.coeff 0, …, q.coeff (d-1)]`. Proved coefficient-by-coefficient through
`coeff_toPoly`: below `d` the candidate is `q.coeff i`, at `d` it is the monic `1`, above `d`
both are `0`. The bridge from an abstract monic divisor to an enumerated candidate list. -/
theorem eq_toPoly_lower_append_one {R : Type*} [CommRing R] {q : R[X]} {d : ℕ}
    (hq : IsMonicOfDegree q d) :
    q = toPoly ((List.ofFn (fun i : Fin d => q.coeff i)) ++ [1]) := by
  apply Polynomial.ext
  intro i
  rw [coeff_toPoly]
  have hlen : (List.ofFn (fun i : Fin d => q.coeff i)).length = d := List.length_ofFn
  rcases lt_trichotomy i d with hi | hi | hi
  · rw [List.getD_append _ _ _ _ (by omega)]
    rw [List.getD_eq_getElem _ _ (by omega)]
    simp
  · subst hi
    rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self,
      List.getD_eq_getElem _ _ (by simp)]
    rw [List.getElem_singleton]
    rw [← hq.natDegree_eq, hq.monic.coeff_natDegree]
  · rw [List.getD_eq_default _ _ (by simp [hlen]; omega)]
    exact coeff_eq_zero_of_natDegree_lt (by rw [hq.natDegree_eq]; omega)

/-! ## Fixed-length coefficient comparison

To compare two coefficient lists as *polynomials* by a robust, length-insensitive
**computable** equality, normalize both to their first `m` coefficients
(`padCoeffs l m`, padding past the end with `0`). Two lists with equal `toPoly` have equal
`padCoeffs` (`padCoeffs_eq_of_toPoly_eq`) — the easy direction the soundness proof needs. -/

/-- The first `m` coefficients of `l` (padded with `0`): `[l.getD 0 0, …, l.getD (m-1) 0]`.
A computable, fixed-length normal form for polynomial-equality comparison. -/
def padCoeffs {R : Type*} [Zero R] (l : List R) (m : ℕ) : List R :=
  (List.range m).map (fun i => l.getD i 0)

/-- `padCoeffs l m` reads index `i < m` as `l.getD i 0 = (toPoly l).coeff i`. -/
theorem padCoeffs_getElem {R : Type*} [Zero R] (l : List R) (m i : ℕ) (hi : i < m) :
    (padCoeffs l m).getD i 0 = l.getD i 0 := by
  rw [padCoeffs, List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

/-- If two lists have equal `toPoly`, their fixed-length normal forms coincide: equal
polynomials have equal coefficients, hence equal `padCoeffs`. -/
theorem padCoeffs_eq_of_toPoly_eq {R : Type*} [Semiring R] {l₁ l₂ : List R} (m : ℕ)
    (h : toPoly l₁ = toPoly l₂) : padCoeffs l₁ m = padCoeffs l₂ m := by
  unfold padCoeffs
  apply List.map_congr_left
  intro i hi
  rw [← coeff_toPoly, ← coeff_toPoly, h]

/-- **Reverse bridge** (degree-bounded). If two lists agree on their first `m` coefficients
(`padCoeffs … m`) and both read as polynomials of `degree < m`, they read as the *same*
polynomial — equality below `m` plus vanishing at and above `m`. The completeness direction
needs this to turn a matching `padCoeffs` into a genuine polynomial factorization. -/
theorem toPoly_eq_of_padCoeffs_eq {R : Type*} [Semiring R] {l₁ l₂ : List R} {m : ℕ}
    (h1 : (toPoly l₁).degree < m) (h2 : (toPoly l₂).degree < m)
    (h : padCoeffs l₁ m = padCoeffs l₂ m) : toPoly l₁ = toPoly l₂ := by
  apply Polynomial.ext
  intro i
  by_cases hi : i < m
  · rw [coeff_toPoly, coeff_toPoly]
    have := congrArg (fun l => l.getD i 0) h
    rwa [padCoeffs_getElem _ _ _ hi, padCoeffs_getElem _ _ _ hi] at this
  · have hle : (m : WithBot ℕ) ≤ i := by exact_mod_cast Nat.not_lt.mp hi
    rw [coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h1 hle),
      coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h2 hle)]

/-! ## The finite-field factorization search (on coefficient lists)

`noFactor cf n d` asserts: no two candidate lists — `vq ++ [1]` (lower `vq` of length `d`)
and `vg ++ [1]` (lower `vg` of length `n − d`) — multiply (via `mulL`) to the same degree-`n`
polynomial as the target `cf`, checked through the length-`(n+1)` normal form `padCoeffs`.
Quantified over the `Fintype`s `Fin d → ZMod p` and `Fin (n − d) → ZMod p`, so `Decidable`
and fully computable (only `+`/`*` on `ZMod p` and list equality). -/

/-- The candidate-pair check at a fixed factor degree `d`: no monic degree-`d` factor times
monic degree-`(n−d)` cofactor (as coefficient lists) matches the target `cf` on its first
`n+1` coefficients. -/
def noFactor {p : ℕ} (cf : List (ZMod p)) (n d : ℕ) : Prop :=
  ∀ (vq : Fin d → ZMod p) (vg : Fin (n - d) → ZMod p),
    padCoeffs (mulL (List.ofFn vq ++ [1]) (List.ofFn vg ++ [1])) (n + 1) ≠ padCoeffs cf (n + 1)

instance {p : ℕ} [NeZero p] (cf : List (ZMod p)) (n d : ℕ) : Decidable (noFactor cf n d) :=
  inferInstanceAs (Decidable (∀ _, ∀ _, _ ≠ _))

/-- **The 𝔽_p irreducibility check** on a target coefficient list `cf` of degree `n` (so
`toPoly cf` is monic of `natDegree n`): `n ≥ 1` and no monic factor of any degree
`1 ≤ d ≤ n/2`. A finite decidable conjunction. -/
def irreducibleListModP {p : ℕ} (cf : List (ZMod p)) (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ d ∈ Finset.Ioc 0 (n / 2), noFactor cf n d

instance {p : ℕ} [NeZero p] (cf : List (ZMod p)) (n : ℕ) : Decidable (irreducibleListModP cf n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Soundness of the 𝔽_p decision -/

/-- **★ 𝔽_p soundness.** If the list search reports `cf` (a monic degree-`n` target, i.e.
`toPoly cf` monic of `natDegree n`) irreducible, then `toPoly cf` is `Irreducible` over
`𝔽_p`. Any hypothetical monic factorization `q * g = toPoly cf` is reconstructed
(`eq_toPoly_lower_append_one`) as candidate lists whose `mulL` product has, by `toPoly_mulL`,
the same `toPoly` as `cf` — hence the same `padCoeffs`, contradicting the search. -/
theorem irreducible_toPoly_of_irreducibleListModP {p : ℕ} [Fact p.Prime] {cf : List (ZMod p)}
    {n : ℕ} (hmon : IsMonicOfDegree (toPoly cf) n) (hirr : irreducibleListModP cf n) :
    Irreducible (toPoly cf) := by
  obtain ⟨hn, hsearch⟩ := hirr
  have hfp_mon : (toPoly cf).Monic := hmon.monic
  have hfp_deg : (toPoly cf).natDegree = n := hmon.natDegree_eq
  have hne1 : toPoly cf ≠ 1 := by
    intro h; rw [h, natDegree_one] at hfp_deg; omega
  rw [hfp_mon.irreducible_iff_lt_natDegree_lt hne1]
  rintro q hq hd ⟨g, hfac⟩
  -- `g` is the monic cofactor
  have hg : g.Monic := hq.of_mul_monic_left (hfac ▸ hfp_mon)
  rw [Finset.mem_Ioc, hfp_deg] at hd
  obtain ⟨hd1, hd2⟩ := hd
  -- degrees: natDegree q + natDegree g = n
  have hdegsum : q.natDegree + g.natDegree = n := by
    have h := hq.natDegree_mul hg
    rw [← hfac, hfp_deg] at h; omega
  -- both factors are monic of their respective degrees; cofactor degree = n − natDegree q
  have hqmon : IsMonicOfDegree q q.natDegree := ⟨rfl, hq⟩
  have hgdeg : n - q.natDegree = g.natDegree := by omega
  have hgmon : IsMonicOfDegree g (n - q.natDegree) := by rw [hgdeg]; exact ⟨rfl, hg⟩
  -- the search range covers `d = natDegree q`
  have hrange : q.natDegree ∈ Finset.Ioc 0 (n / 2) := Finset.mem_Ioc.mpr ⟨hd1, hd2⟩
  -- feed the lower-coefficient witnesses; product list ↦ same `toPoly` as `cf`
  refine hsearch q.natDegree hrange (fun i => q.coeff i)
    (fun i : Fin (n - q.natDegree) => g.coeff (i : ℕ)) ?_
  apply padCoeffs_eq_of_toPoly_eq
  rw [toPoly_mulL]
  rw [← eq_toPoly_lower_append_one hqmon, ← eq_toPoly_lower_append_one hgmon, hfac]

/-- **★ 𝔽_p completeness.** The converse of the soundness direction: a genuinely
`Irreducible` monic degree-`n` target `toPoly cf` *passes* the list search. So the finite-
field decision is correct in **both** directions (`irreducibleListModP_iff_irreducible`
below). Proof: a matching `padCoeffs` would, by the degree-bounded reverse bridge
`toPoly_eq_of_padCoeffs_eq`, give a real factorization `(candidate) ∣ toPoly cf` with the
candidate monic of degree `1 ≤ d ≤ n/2`, contradicting `irreducible_iff_lt_natDegree_lt`. -/
theorem irreducibleListModP_of_irreducible {p : ℕ} [Fact p.Prime] {cf : List (ZMod p)}
    {n : ℕ} (hmon : IsMonicOfDegree (toPoly cf) n) (hirr : Irreducible (toPoly cf)) :
    irreducibleListModP cf n := by
  have hfp_mon : (toPoly cf).Monic := hmon.monic
  have hfp_deg : (toPoly cf).natDegree = n := hmon.natDegree_eq
  have hne1 : toPoly cf ≠ 1 := by intro h; rw [h] at hirr; exact hirr.not_isUnit isUnit_one
  -- degree of an irreducible monic is ≥ 1 (else it is `1`, a unit)
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exact absurd (eq_one_of_monic_natDegree_zero hfp_mon (by rw [hfp_deg, h0])) hne1
    · exact h0
  refine ⟨hn, ?_⟩
  intro d hd vq vg hcontra
  rw [Finset.mem_Ioc] at hd
  obtain ⟨hd1, hd2⟩ := hd
  -- the two candidate polynomials and their degrees
  have hqlen : (List.ofFn vq).length = d := List.length_ofFn
  have hglen : (List.ofFn vg).length = n - d := List.length_ofFn
  have hqm : IsMonicOfDegree (toPoly (List.ofFn vq ++ [1])) d := by
    have := isMonicOfDegree_toPoly_append_one (List.ofFn vq); rwa [hqlen] at this
  have hgm : IsMonicOfDegree (toPoly (List.ofFn vg ++ [1])) (n - d) := by
    have := isMonicOfDegree_toPoly_append_one (List.ofFn vg); rwa [hglen] at this
  -- the product is monic of degree n
  have hprod : IsMonicOfDegree
      (toPoly (List.ofFn vq ++ [1]) * toPoly (List.ofFn vg ++ [1])) n := by
    have h := hqm.mul hgm
    rwa [Nat.add_sub_cancel' (le_trans hd2 (Nat.div_le_self n 2))] at h
  -- equal padCoeffs + degree bounds ⟹ equal polynomials ⟹ a real factorization
  have heq : toPoly (List.ofFn vq ++ [1]) * toPoly (List.ofFn vg ++ [1]) = toPoly cf := by
    rw [← toPoly_mulL]
    refine toPoly_eq_of_padCoeffs_eq ?_ ?_ hcontra
    · refine (degree_le_natDegree).trans_lt ?_
      rw [toPoly_mulL, hprod.natDegree_eq]
      exact_mod_cast Nat.lt_succ_self n
    · refine (degree_le_natDegree).trans_lt ?_
      rw [hfp_deg]
      exact_mod_cast Nat.lt_succ_self n
  -- `toPoly (ofFn vq ++ [1])` is a monic degree-d divisor with `1 ≤ d ≤ n/2`: contradiction
  rw [hfp_mon.irreducible_iff_lt_natDegree_lt hne1] at hirr
  refine hirr (toPoly (List.ofFn vq ++ [1])) hqm.monic ?_ ⟨_, heq.symm⟩
  rw [Finset.mem_Ioc, hqm.natDegree_eq, hfp_deg]
  exact ⟨hd1, hd2⟩

/-- **★ 𝔽_p decision correctness, both directions.** The list search decides irreducibility
of a monic degree-`n` target over `𝔽_p` exactly: sound *and* complete. -/
theorem irreducibleListModP_iff_irreducible {p : ℕ} [Fact p.Prime] {cf : List (ZMod p)}
    {n : ℕ} (hmon : IsMonicOfDegree (toPoly cf) n) :
    irreducibleListModP cf n ↔ Irreducible (toPoly cf) :=
  ⟨irreducible_toPoly_of_irreducibleListModP hmon, irreducibleListModP_of_irreducible hmon⟩

/-! ## Reduction `ℤ[X] → 𝔽_p[X]` and the lift to `ℚ` -/

/-- Read an integer coefficient list as `f : ℤ[X]` — the polynomial the certificate is about. -/
noncomputable def toPolyZ (cf : List ℤ) : ℤ[X] := toPoly cf

/-- Reduce a `ℤ`-coefficient list to a `(ZMod p)`-coefficient list (entrywise `Int.cast`):
the mod-`p` reduction at the list level. `toPoly` commutes with it
(`toPoly_reduceCoeffs`). -/
def reduceCoeffs (p : ℕ) (cf : List ℤ) : List (ZMod p) := cf.map (Int.cast)

/-- `toPoly` commutes with mod-`p` reduction: `toPoly (reduceCoeffs p cf) = (toPolyZ cf).map …`
(the entrywise `Int.cast` on coefficients is the `Polynomial.map` of `Int.castRingHom`). -/
theorem toPoly_reduceCoeffs (p : ℕ) (cf : List ℤ) :
    toPoly (reduceCoeffs p cf) = (toPolyZ cf).map (Int.castRingHom (ZMod p)) := by
  unfold reduceCoeffs toPolyZ
  induction cf with
  | nil => simp [toPoly]
  | cons a as ih =>
    simp only [List.map_cons, toPoly_cons, ih, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X]
    rfl

/-- **The mod-`p` irreducibility test** for an integer coefficient list `cf` of degree `n`:
reduce mod `p`, then run the finite-field factorization search. `true` is a *sound*
certificate of irreducibility over `ℚ` (when `toPolyZ cf` is monic); `false` is inconclusive.
Fully computable, so `native_decide`-able. -/
def irreducibleByModP (p : ℕ) [NeZero p] (cf : List ℤ) (n : ℕ) : Bool :=
  decide (irreducibleListModP (reduceCoeffs p cf) n)

/-- **★ SOUNDNESS.** If the mod-`p` test succeeds on a monic `f = toPolyZ cf` of degree `n`,
then `f` is `Irreducible` over `ℤ` (hence over `ℚ` by Gauss's lemma). The proof: the test
certifies the reduction `f mod p` irreducible over `𝔽_p`
(`irreducible_toPoly_of_irreducibleListModP`), and a monic polynomial irreducible after
mapping into an integral domain is irreducible (`Monic.irreducible_of_irreducible_map`).

This theorem carries **no** `native` axiom — the `native_decide` lives only in the
certificates below. -/
theorem irreducibleByModP_sound {p : ℕ} [Fact p.Prime] {cf : List ℤ} {n : ℕ}
    (hmon : IsMonicOfDegree (toPolyZ cf) n) (htest : irreducibleByModP p cf n = true) :
    Irreducible (toPolyZ cf) := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
  -- the reduction is monic of degree `n` over `𝔽_p`
  have hmon' : IsMonicOfDegree (toPoly (reduceCoeffs p cf)) n := by
    rw [toPoly_reduceCoeffs]
    refine ⟨?_, hmon.monic.map _⟩
    rw [hmon.monic.natDegree_map, hmon.natDegree_eq]
  -- decode the `Bool` test into the 𝔽_p irreducibility predicate, get 𝔽_p irreducibility
  have hirr_fp : Irreducible (toPoly (reduceCoeffs p cf)) :=
    irreducible_toPoly_of_irreducibleListModP hmon'
      (by rwa [irreducibleByModP, decide_eq_true_eq] at htest)
  -- lift to `ℤ` (hence `ℚ`) via Gauss's lemma
  refine Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod p)) (toPolyZ cf)
    hmon.monic ?_
  rwa [← toPoly_reduceCoeffs]

/-- A certificate list `lower ++ [1]` over `ℤ` reads as a monic poly of degree `lower.length`:
the `IsMonicOfDegree` hypothesis the certificates feed to `irreducibleByModP_sound`. -/
theorem isMonicOfDegree_toPolyZ_append_one (lower : List ℤ) :
    IsMonicOfDegree (toPolyZ (lower ++ [1])) lower.length :=
  isMonicOfDegree_toPoly_append_one lower

/-! ## ★ `native_decide` irreducibility certificates

Each positive certificate represents `f` by its `ℤ`-coefficient list `lower ++ [1]` (low-to-
high, last entry the monic `1`), `native_decide`s `irreducibleByModP p (lower ++ [1]) n =
true`, then concludes `Irreducible (toPolyZ (lower ++ [1]))` by `irreducibleByModP_sound`.
Primes are tiny (`p ∈ {2,3,5,7}`) and chosen so `f` is already irreducible mod that `p`,
keeping the finite search fast. -/

/-- `Fact (Nat.Prime 3)` for the mod-3 certificates (explicitly named to avoid the aggregator
auto-name clash with `ComputableDivisorOrder`'s anonymous `Fact (Nat.Prime _)` instances). -/
instance factPrime3_polyIrred : Fact (Nat.Prime 3) := ⟨by decide⟩
/-- `Fact (Nat.Prime 5)` for the mod-5 certificates. -/
instance factPrime5_polyIrred : Fact (Nat.Prime 5) := ⟨by decide⟩
/-- `Fact (Nat.Prime 7)` for the mod-7 certificates. -/
instance factPrime7_polyIrred : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- `x² + 1 = toPolyZ [1,0,1]` is irreducible over `ℤ` (irreducible mod `3`: no root in 𝔽₃). -/
theorem irreducible_toPolyZ_X_sq_add_one :
    Irreducible (toPolyZ ([1, 0] ++ [1])) :=
  irreducibleByModP_sound (p := 3) (isMonicOfDegree_toPolyZ_append_one [1, 0]) (by native_decide)

/-- `x² − 2 = toPolyZ [-2,0,1]` is irreducible over `ℤ` (irreducible mod `5`: `2` a non-square). -/
theorem irreducible_toPolyZ_X_sq_sub_two :
    Irreducible (toPolyZ ([-2, 0] ++ [1])) :=
  irreducibleByModP_sound (p := 5) (isMonicOfDegree_toPolyZ_append_one [-2, 0]) (by native_decide)

/-- `x³ − 2 = toPolyZ [-2,0,0,1]` is irreducible over `ℤ` (irreducible mod `7`: `2` is not a
cube mod 7, so no root; reducible mod `5` since `3³ ≡ 2`, hence `7` is used). -/
theorem irreducible_toPolyZ_X_cube_sub_two :
    Irreducible (toPolyZ ([-2, 0, 0] ++ [1])) :=
  irreducibleByModP_sound (p := 7) (isMonicOfDegree_toPolyZ_append_one [-2, 0, 0])
    (by native_decide)

/-- `x³ − x − 1 = toPolyZ [-1,-1,0,1]` is irreducible over `ℤ` (irreducible mod `3`). -/
theorem irreducible_toPolyZ_X_cube_sub_X_sub_one :
    Irreducible (toPolyZ ([-1, -1, 0] ++ [1])) :=
  irreducibleByModP_sound (p := 3) (isMonicOfDegree_toPolyZ_append_one [-1, -1, 0])
    (by native_decide)

/-- The 5th cyclotomic `x⁴ + x³ + x² + x + 1 = toPolyZ [1,1,1,1,1]` is irreducible over `ℤ`
(irreducible mod `2`, the smallest prime for which it stays irreducible — `2` is a primitive
root mod `5`). -/
theorem irreducible_toPolyZ_cyclotomic_five :
    Irreducible (toPolyZ ([1, 1, 1, 1] ++ [1])) :=
  irreducibleByModP_sound (p := 2) (isMonicOfDegree_toPolyZ_append_one [1, 1, 1, 1])
    (by native_decide)

/-! ## ★ The `x⁴ + 1` limit: SOUND but INCOMPLETE over `ℚ` (a fundamental wall)

`x⁴ + 1` is irreducible over `ℚ` (it is `Φ₈`, the 8th cyclotomic) yet **reducible modulo
every prime** — its Galois group `(ℤ/2)²` has no 4-cycle, so by Frobenius no prime gives an
inert (irreducible-mod-`p`) reduction. The mod-`p` test therefore returns `false` for *every*
`p` on a polynomial that *is* irreducible: the test is **sound but not complete** over `ℚ`,
and this is not a fixable gap in the criterion — it is a theorem of Galois theory. The two
facts below pin the wall: the mod-`p` evaluations (`native_decide`, `false` at `p = 2,3,5,7`,
and the same holds for all `p`) and the genuine `ℚ`-irreducibility (axiom-clean, via
`cyclotomic.irreducible`). A *complete* `ℚ`-irreducibility decider must go beyond mod-`p`
(see the Zassenhaus scope note below). -/

/-- `toPolyZ [1,0,0,0,1] = X⁴ + 1` (the lower part `[1,0,0,0]` reads as the constant `1`). -/
theorem toPolyZ_X_pow_four_add_one : toPolyZ ([1, 0, 0, 0] ++ [1]) = X ^ 4 + 1 := by
  show toPoly ([1, 0, 0, 0] ++ [1]) = X ^ 4 + 1
  rw [toPoly_append_one]
  simp only [toPoly, map_one, map_zero, mul_zero, add_zero, zero_add, List.length_cons,
    List.length_nil]
  ring

/-- `x⁴ + 1 = Φ₈`: the 8th cyclotomic polynomial over `ℤ` is `X⁴ + 1`
(`cyclotomic (2³) = ∑_{i<2} (X^4)^i = 1 + X⁴`). -/
theorem cyclotomic_eight_eq : cyclotomic 8 ℤ = X ^ 4 + 1 := by
  have h : (8 : ℕ) = 2 ^ (2 + 1) := by norm_num
  rw [h, cyclotomic_prime_pow_eq_geom_sum Nat.prime_two,
    Finset.sum_range_succ, Finset.sum_range_one]
  ring

/-- **★ `x⁴ + 1` IS irreducible over `ℤ`** (hence over `ℚ`) — it is `Φ₈`. Axiom-clean: this
side of the wall is a genuine theorem, no `native_decide`. -/
theorem irreducible_toPolyZ_X_pow_four_add_one :
    Irreducible (toPolyZ ([1, 0, 0, 0] ++ [1])) := by
  rw [toPolyZ_X_pow_four_add_one, ← cyclotomic_eight_eq]
  exact cyclotomic.irreducible (by norm_num)

/-- **★ …yet `x⁴ + 1` is REDUCIBLE mod every small prime** — the mod-`p` test returns `false`
at `p = 2, 3, 5, 7` (`native_decide`). With the previous theorem this exhibits the
sound-but-incomplete limit: a `ℚ`-irreducible polynomial the mod-`p` certificate can never
confirm. (The same `false` holds for *all* primes, by the Galois-group argument.) -/
theorem irreducibleByModP_X_pow_four_add_one_false :
    irreducibleByModP 2 ([1, 0, 0, 0] ++ [1]) 4 = false ∧
    irreducibleByModP 3 ([1, 0, 0, 0] ++ [1]) 4 = false ∧
    irreducibleByModP 5 ([1, 0, 0, 0] ++ [1]) 4 = false ∧
    irreducibleByModP 7 ([1, 0, 0, 0] ++ [1]) 4 = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Restatements ("it compiled" ≠ "it says the right thing")

The coefficient-list certificates do read as the intended polynomials, and soundness has the
intended type. -/

-- `irreducibleByModP_sound` has exactly the SOUND one-way type: `true ⟹ Irreducible`.
example : ∀ (p : ℕ) [Fact p.Prime] (cf : List ℤ) (n : ℕ),
    IsMonicOfDegree (toPolyZ cf) n → irreducibleByModP p cf n = true → Irreducible (toPolyZ cf) :=
  fun _ _ _ _ h ht => irreducibleByModP_sound h ht

-- the 𝔽_p decision is genuinely BOTH directions.
example {p : ℕ} [Fact p.Prime] (cf : List (ZMod p)) (n : ℕ)
    (h : IsMonicOfDegree (toPoly cf) n) :
    irreducibleListModP cf n ↔ Irreducible (toPoly cf) :=
  irreducibleListModP_iff_irreducible h

-- the certificate lists ARE the named polynomials.
example : toPolyZ ([1, 0] ++ [1]) = X ^ 2 + 1 := by
  show toPoly _ = _; rw [toPoly_append_one]; simp [toPoly]; ring
example : toPolyZ ([-2, 0, 0] ++ [1]) = X ^ 3 - 2 := by
  show toPoly _ = _; rw [toPoly_append_one]; simp [toPoly]; ring
example : toPolyZ ([-1, -1, 0] ++ [1]) = X ^ 3 - X - 1 := by
  show toPoly _ = _; rw [toPoly_append_one]; simp [toPoly]; ring
example : toPolyZ ([1, 1, 1, 1] ++ [1]) = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
  show toPoly _ = _; rw [toPoly_append_one]; simp [toPoly]; ring

-- the wall: `x⁴+1` is `ℚ`-irreducible AND fails the mod-`p` test at every small prime.
example : Irreducible (toPolyZ ([1, 0, 0, 0] ++ [1])) ∧
    irreducibleByModP 2 ([1, 0, 0, 0] ++ [1]) 4 = false :=
  ⟨irreducible_toPolyZ_X_pow_four_add_one, irreducibleByModP_X_pow_four_add_one_false.1⟩

end DeepWiki.SymbolicIntegration
