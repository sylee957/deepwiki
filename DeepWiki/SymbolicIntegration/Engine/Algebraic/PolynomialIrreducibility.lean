import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import DeepWiki.SymbolicIntegration.Engine.Algebraic.PrimeFacts

/-! # A computable, sound irreducibility test for `ℤ[X]` via mod-`p` reduction

A monic integer polynomial that stays irreducible after reduction mod a prime `p` is
irreducible over `ℚ` (Gauss's lemma). The test runs on coefficient `List (ZMod p)` (Horner
form, low-to-high) so it is `native_decide`-able, decides irreducibility over `𝔽_p` (both
directions), and lifts one-way to `ℚ`. The `𝔽_p ⟹ ℚ` lift cannot be a decision procedure —
`x⁴ + 1` is `ℚ`-irreducible yet reducible mod every prime — so `irreducibleByModP = false`
is inconclusive. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ## The computable coefficient-`List` polynomial engine

Coefficients low-to-high: `[a₀, a₁, …]` ↦ `a₀ + a₁ X + …`. `listToPoly` is the Horner reading
`listToPoly (a :: as) = C a + X * listToPoly as`. `addL`/`mulL` are computable list arithmetic; the
bridges `toPoly_addL` / `toPoly_mulL` connect them to Mathlib `Polynomial` `+`/`*`. -/

/-- Horner reading of a coefficient list as a polynomial: `[a₀,…,aₖ] ↦ Σ aᵢ Xⁱ`. -/
noncomputable def listToPoly {R : Type*} [Semiring R] : List R → R[X]
  | [] => 0
  | a :: as => C a + X * listToPoly as

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

@[simp] theorem toPoly_nil {R : Type*} [Semiring R] : listToPoly ([] : List R) = 0 := rfl

@[simp] theorem toPoly_cons {R : Type*} [Semiring R] (a : R) (as : List R) :
    listToPoly (a :: as) = C a + X * listToPoly as := rfl

/-- `(listToPoly l).coeff i = l.getD i 0`: the Horner reading recovers the list entries. -/
theorem coeff_toPoly {R : Type*} [Semiring R] (l : List R) (i : ℕ) :
    (listToPoly l).coeff i = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp [listToPoly]
  | cons a as ih =>
    rw [toPoly_cons, coeff_add]
    cases i with
    | zero => simp [coeff_C, List.getD]
    | succ i =>
      rw [coeff_C, if_neg (Nat.succ_ne_zero i), zero_add, coeff_X_mul, ih, List.getD]
      rfl

/-- `listToPoly` of a scaled list is `C c *` the polynomial. -/
theorem toPoly_scaleL {R : Type*} [CommSemiring R] (c : R) (as : List R) :
    listToPoly (scaleL c as) = C c * listToPoly as := by
  induction as with
  | nil => simp [scaleL]
  | cons a as ih =>
    simp only [scaleL, toPoly_cons, ih, C_mul]
    ring

/-- `listToPoly` is additive on `addL`. -/
theorem toPoly_addL {R : Type*} [CommSemiring R] (as bs : List R) :
    listToPoly (addL as bs) = listToPoly as + listToPoly bs := by
  induction as generalizing bs with
  | nil => simp [addL]
  | cons a as ih =>
    cases bs with
    | nil => simp [addL]
    | cons b bs =>
      simp only [addL, toPoly_cons, ih, C_add]
      ring

/-- `listToPoly (mulL a b) = listToPoly a * listToPoly b`: list multiplication realizes polynomial
multiplication. -/
theorem toPoly_mulL {R : Type*} [CommSemiring R] (as bs : List R) :
    listToPoly (mulL as bs) = listToPoly as * listToPoly bs := by
  induction as with
  | nil => simp [mulL]
  | cons a as ih =>
    simp only [mulL, toPoly_addL, toPoly_scaleL, toPoly_cons, ih, map_zero, zero_add]
    ring

/-- Equal `listToPoly` and equal length force equal lists. -/
theorem list_eq_of_toPoly_eq {R : Type*} [Semiring R] [Inhabited R] {l₁ l₂ : List R}
    (hlen : l₁.length = l₂.length) (h : listToPoly l₁ = listToPoly l₂) : l₁ = l₂ := by
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

A coefficient list `lower ++ [1]` (lower of length `d`) reads as a monic polynomial of
`natDegree` exactly `d`. -/

/-- `listToPoly lower` has `degree < lower.length` (a length-`d` list reads as a poly of degree
`< d`): all coefficients at index `≥ d` are `0`. -/
theorem toPoly_degree_lt {R : Type*} [Semiring R] (lower : List R) :
    (listToPoly lower).degree < lower.length := by
  rw [degree_lt_iff_coeff_zero]
  intro i hi
  rw [coeff_toPoly, List.getD_eq_default]
  exact_mod_cast hi

/-- The polynomial of a candidate list `lower ++ [1]` is `X^d + (listToPoly lower)`, where
`d = lower.length`. -/
theorem toPoly_append_one {R : Type*} [CommSemiring R] (lower : List R) :
    listToPoly (lower ++ [1]) = listToPoly lower + X ^ lower.length := by
  induction lower with
  | nil => simp [listToPoly]
  | cons a as ih =>
    simp only [List.cons_append, toPoly_cons, ih, List.length_cons]
    ring

/-- A candidate list `lower ++ [1]` (lower of length `d`) reads as a monic poly of degree
exactly `d`. -/
theorem isMonicOfDegree_toPoly_append_one {R : Type*} [CommSemiring R] [Nontrivial R]
    (lower : List R) : IsMonicOfDegree (listToPoly (lower ++ [1])) lower.length := by
  rw [toPoly_append_one]
  have hlt : (listToPoly lower).degree < ((lower.length : ℕ) : WithBot ℕ) :=
    (toPoly_degree_lt lower)
  refine ⟨?_, ?_⟩
  · refine natDegree_eq_of_degree_eq_some ?_
    rw [add_comm]
    refine (degree_add_eq_left_of_degree_lt ?_).trans (degree_X_pow _)
    exact hlt.trans_le (degree_X_pow _).ge
  · rw [add_comm]
    exact monic_X_pow_add hlt

/-- Any monic `q` of `natDegree` exactly `d` is `listToPoly (lower ++ [1])` for
`lower = [q.coeff 0, …, q.coeff (d-1)]`. -/
theorem eq_toPoly_lower_append_one {R : Type*} [CommRing R] {q : R[X]} {d : ℕ}
    (hq : IsMonicOfDegree q d) :
    q = listToPoly ((List.ofFn (fun i : Fin d => q.coeff i)) ++ [1]) := by
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

`padCoeffs l m` normalizes a list to its first `m` coefficients (padding with `0`), a
computable normal form for polynomial-equality comparison. -/

/-- The first `m` coefficients of `l` (padded with `0`): `[l.getD 0 0, …, l.getD (m-1) 0]`.
A computable, fixed-length normal form for polynomial-equality comparison. -/
def padCoeffs {R : Type*} [Zero R] (l : List R) (m : ℕ) : List R :=
  (List.range m).map (fun i => l.getD i 0)

/-- `padCoeffs l m` reads index `i < m` as `l.getD i 0 = (listToPoly l).coeff i`. -/
theorem padCoeffs_getElem {R : Type*} [Zero R] (l : List R) (m i : ℕ) (hi : i < m) :
    (padCoeffs l m).getD i 0 = l.getD i 0 := by
  rw [padCoeffs, List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

/-- If two lists have equal `listToPoly`, their fixed-length normal forms coincide: equal
polynomials have equal coefficients, hence equal `padCoeffs`. -/
theorem padCoeffs_eq_of_toPoly_eq {R : Type*} [Semiring R] {l₁ l₂ : List R} (m : ℕ)
    (h : listToPoly l₁ = listToPoly l₂) : padCoeffs l₁ m = padCoeffs l₂ m := by
  unfold padCoeffs
  apply List.map_congr_left
  intro i hi
  rw [← coeff_toPoly, ← coeff_toPoly, h]

/-- If two lists agree on their first `m` coefficients and both read as polynomials of
`degree < m`, they read as the same polynomial. -/
theorem toPoly_eq_of_padCoeffs_eq {R : Type*} [Semiring R] {l₁ l₂ : List R} {m : ℕ}
    (h1 : (listToPoly l₁).degree < m) (h2 : (listToPoly l₂).degree < m)
    (h : padCoeffs l₁ m = padCoeffs l₂ m) : listToPoly l₁ = listToPoly l₂ := by
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

`noFactor cf n d` asserts no monic degree-`d` factor and monic degree-`(n−d)` cofactor (as
coefficient lists) multiply to the target `cf`; quantified over the finite `Fin _ → ZMod p`,
so decidable and computable. -/

/-- The candidate-pair check at a fixed factor degree `d`: no monic degree-`d` factor times
monic degree-`(n−d)` cofactor (as coefficient lists) matches the target `cf` on its first
`n+1` coefficients. -/
def noFactor {p : ℕ} (cf : List (ZMod p)) (n d : ℕ) : Prop :=
  ∀ (vq : Fin d → ZMod p) (vg : Fin (n - d) → ZMod p),
    padCoeffs (mulL (List.ofFn vq ++ [1]) (List.ofFn vg ++ [1])) (n + 1) ≠ padCoeffs cf (n + 1)

instance {p : ℕ} [NeZero p] (cf : List (ZMod p)) (n d : ℕ) : Decidable (noFactor cf n d) :=
  inferInstanceAs (Decidable (∀ _, ∀ _, _ ≠ _))

/-- The `𝔽_p` irreducibility check on a monic degree-`n` target `cf`: `n ≥ 1` and no monic
factor of any degree `1 ≤ d ≤ n/2`. -/
def irreducibleListModP {p : ℕ} (cf : List (ZMod p)) (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ d ∈ Finset.Ioc 0 (n / 2), noFactor cf n d

instance {p : ℕ} [NeZero p] (cf : List (ZMod p)) (n : ℕ) : Decidable (irreducibleListModP cf n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Soundness of the 𝔽_p decision -/

/-- If the list search reports a monic degree-`n` target `cf` irreducible, then `listToPoly cf`
is `Irreducible` over `𝔽_p`. -/
theorem irreducible_toPoly_of_irreducibleListModP {p : ℕ} [Fact p.Prime] {cf : List (ZMod p)}
    {n : ℕ} (hmon : IsMonicOfDegree (listToPoly cf) n) (hirr : irreducibleListModP cf n) :
    Irreducible (listToPoly cf) := by
  obtain ⟨hn, hsearch⟩ := hirr
  have hfp_mon : (listToPoly cf).Monic := hmon.monic
  have hfp_deg : (listToPoly cf).natDegree = n := hmon.natDegree_eq
  have hne1 : listToPoly cf ≠ 1 := by
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
  -- feed the lower-coefficient witnesses; product list ↦ same `listToPoly` as `cf`
  refine hsearch q.natDegree hrange (fun i => q.coeff i)
    (fun i : Fin (n - q.natDegree) => g.coeff (i : ℕ)) ?_
  apply padCoeffs_eq_of_toPoly_eq
  rw [toPoly_mulL]
  rw [← eq_toPoly_lower_append_one hqmon, ← eq_toPoly_lower_append_one hgmon, hfac]

/-- The converse: a genuinely `Irreducible` monic degree-`n` target `listToPoly cf` passes the
list search. -/
theorem irreducibleListModP_of_irreducible {p : ℕ} [Fact p.Prime] {cf : List (ZMod p)}
    {n : ℕ} (hmon : IsMonicOfDegree (listToPoly cf) n) (hirr : Irreducible (listToPoly cf)) :
    irreducibleListModP cf n := by
  have hfp_mon : (listToPoly cf).Monic := hmon.monic
  have hfp_deg : (listToPoly cf).natDegree = n := hmon.natDegree_eq
  have hne1 : listToPoly cf ≠ 1 := by intro h; rw [h] at hirr; exact hirr.not_isUnit isUnit_one
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
  have hqm : IsMonicOfDegree (listToPoly (List.ofFn vq ++ [1])) d := by
    have := isMonicOfDegree_toPoly_append_one (List.ofFn vq); rwa [hqlen] at this
  have hgm : IsMonicOfDegree (listToPoly (List.ofFn vg ++ [1])) (n - d) := by
    have := isMonicOfDegree_toPoly_append_one (List.ofFn vg); rwa [hglen] at this
  -- the product is monic of degree n
  have hprod : IsMonicOfDegree
      (listToPoly (List.ofFn vq ++ [1]) * listToPoly (List.ofFn vg ++ [1])) n := by
    have h := hqm.mul hgm
    rwa [Nat.add_sub_cancel' (le_trans hd2 (Nat.div_le_self n 2))] at h
  -- equal padCoeffs + degree bounds ⟹ equal polynomials ⟹ a real factorization
  have heq : listToPoly (List.ofFn vq ++ [1]) * listToPoly (List.ofFn vg ++ [1]) = listToPoly cf := by
    rw [← toPoly_mulL]
    refine toPoly_eq_of_padCoeffs_eq ?_ ?_ hcontra
    · refine (degree_le_natDegree).trans_lt ?_
      rw [toPoly_mulL, hprod.natDegree_eq]
      exact_mod_cast Nat.lt_succ_self n
    · refine (degree_le_natDegree).trans_lt ?_
      rw [hfp_deg]
      exact_mod_cast Nat.lt_succ_self n
  -- `listToPoly (ofFn vq ++ [1])` is a monic degree-d divisor with `1 ≤ d ≤ n/2`: contradiction
  rw [hfp_mon.irreducible_iff_lt_natDegree_lt hne1] at hirr
  refine hirr (listToPoly (List.ofFn vq ++ [1])) hqm.monic ?_ ⟨_, heq.symm⟩
  rw [Finset.mem_Ioc, hqm.natDegree_eq, hfp_deg]
  exact ⟨hd1, hd2⟩

/-- The list search decides irreducibility of a monic degree-`n` target over `𝔽_p` exactly. -/
theorem irreducibleListModP_iff_irreducible {p : ℕ} [Fact p.Prime] {cf : List (ZMod p)}
    {n : ℕ} (hmon : IsMonicOfDegree (listToPoly cf) n) :
    irreducibleListModP cf n ↔ Irreducible (listToPoly cf) :=
  ⟨irreducible_toPoly_of_irreducibleListModP hmon, irreducibleListModP_of_irreducible hmon⟩

/-! ## Reduction `ℤ[X] → 𝔽_p[X]` and the lift to `ℚ` -/

/-- Read an integer coefficient list as `f : ℤ[X]` — the polynomial the certificate is about. -/
noncomputable def toPolyZ (cf : List ℤ) : ℤ[X] := listToPoly cf

/-- Reduce a `ℤ`-coefficient list to a `(ZMod p)`-coefficient list (entrywise `Int.cast`):
the mod-`p` reduction at the list level. `listToPoly` commutes with it
(`toPoly_reduceCoeffs`). -/
def reduceCoeffs (p : ℕ) (cf : List ℤ) : List (ZMod p) := cf.map (Int.cast)

/-- `listToPoly` commutes with mod-`p` reduction: `listToPoly (reduceCoeffs p cf) = (toPolyZ cf).map …`
(the entrywise `Int.cast` on coefficients is the `Polynomial.map` of `Int.castRingHom`). -/
theorem toPoly_reduceCoeffs (p : ℕ) (cf : List ℤ) :
    listToPoly (reduceCoeffs p cf) = (toPolyZ cf).map (Int.castRingHom (ZMod p)) := by
  unfold reduceCoeffs toPolyZ
  induction cf with
  | nil => simp [listToPoly]
  | cons a as ih =>
    simp only [List.map_cons, toPoly_cons, ih, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X]
    rfl

/-- The mod-`p` irreducibility test for a degree-`n` integer coefficient list `cf`: reduce
mod `p`, then run the finite-field search. `true` is a sound irreducibility certificate over
`ℚ` (when monic); `false` is inconclusive. -/
def irreducibleByModP (p : ℕ) [NeZero p] (cf : List ℤ) (n : ℕ) : Bool :=
  decide (irreducibleListModP (reduceCoeffs p cf) n)

/-- If the mod-`p` test succeeds on a monic `f = toPolyZ cf` of degree `n`, then `f` is
`Irreducible` over `ℤ` (hence over `ℚ` by Gauss's lemma). -/
theorem irreducibleByModP_sound {p : ℕ} [Fact p.Prime] {cf : List ℤ} {n : ℕ}
    (hmon : IsMonicOfDegree (toPolyZ cf) n) (htest : irreducibleByModP p cf n = true) :
    Irreducible (toPolyZ cf) := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
  -- the reduction is monic of degree `n` over `𝔽_p`
  have hmon' : IsMonicOfDegree (listToPoly (reduceCoeffs p cf)) n := by
    rw [toPoly_reduceCoeffs]
    refine ⟨?_, hmon.monic.map _⟩
    rw [hmon.monic.natDegree_map, hmon.natDegree_eq]
  -- decode the `Bool` test into the 𝔽_p irreducibility predicate, get 𝔽_p irreducibility
  have hirr_fp : Irreducible (listToPoly (reduceCoeffs p cf)) :=
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

/-! ## Irreducibility certificates

Each certificate represents `f` by its `ℤ`-coefficient list `lower ++ [1]`, checks
`irreducibleByModP p (lower ++ [1]) n = true`, and concludes irreducibility over `ℤ`. -/

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

/-! ## The `x⁴ + 1` limit: sound but incomplete over `ℚ`

`x⁴ + 1 = Φ₈` is irreducible over `ℚ` yet reducible modulo every prime (its Galois group
`(ℤ/2)²` has no 4-cycle), so the mod-`p` test returns `false` on a polynomial that is
irreducible. The two facts below pin this limit. -/

/-- `toPolyZ [1,0,0,0,1] = X⁴ + 1` (the lower part `[1,0,0,0]` reads as the constant `1`). -/
theorem toPolyZ_X_pow_four_add_one : toPolyZ ([1, 0, 0, 0] ++ [1]) = X ^ 4 + 1 := by
  show listToPoly ([1, 0, 0, 0] ++ [1]) = X ^ 4 + 1
  rw [toPoly_append_one]
  simp only [listToPoly, map_one, map_zero, mul_zero, add_zero, zero_add, List.length_cons,
    List.length_nil]
  ring

/-- `x⁴ + 1 = Φ₈`: the 8th cyclotomic polynomial over `ℤ` is `X⁴ + 1`
(`cyclotomic (2³) = ∑_{i<2} (X^4)^i = 1 + X⁴`). -/
theorem cyclotomic_eight_eq : cyclotomic 8 ℤ = X ^ 4 + 1 := by
  have h : (8 : ℕ) = 2 ^ (2 + 1) := by norm_num
  rw [h, cyclotomic_prime_pow_eq_geom_sum Nat.prime_two,
    Finset.sum_range_succ, Finset.sum_range_one]
  ring

/-- `x⁴ + 1` is irreducible over `ℤ` (hence over `ℚ`) — it is `Φ₈`. -/
theorem irreducible_toPolyZ_X_pow_four_add_one :
    Irreducible (toPolyZ ([1, 0, 0, 0] ++ [1])) := by
  rw [toPolyZ_X_pow_four_add_one, ← cyclotomic_eight_eq]
  exact cyclotomic.irreducible (by norm_num)

/-- The mod-`p` test returns `false` for `x⁴ + 1` at `p = 2, 3, 5, 7`: a `ℚ`-irreducible
polynomial the mod-`p` certificate can never confirm. -/
theorem irreducibleByModP_X_pow_four_add_one_false :
    irreducibleByModP 2 ([1, 0, 0, 0] ++ [1]) 4 = false ∧
    irreducibleByModP 3 ([1, 0, 0, 0] ++ [1]) 4 = false ∧
    irreducibleByModP 5 ([1, 0, 0, 0] ++ [1]) 4 = false ∧
    irreducibleByModP 7 ([1, 0, 0, 0] ++ [1]) 4 = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end DeepWiki.SymbolicIntegration
