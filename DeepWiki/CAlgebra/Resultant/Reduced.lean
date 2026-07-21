import DeepWiki.CAlgebra.Resultant.Euclidean
import DeepWiki.Algebra.SubresultantPRS

/-! # Resultant by Collins' reduced pseudo-remainder sequence

Fraction-free without content gcds: the carried divisor `lc^(δ+1)` is divided out of each
pseudo-remainder, unchecked — and proven exact through the α-divisibility ledger
(`SubresLedger`), the local form of Brown–Traub's *"the pseudo-remainder is exactly
divisible by βᵢ"*. This is the one resultant algorithm whose contract consumes the
determinantal subresultant theory (`DeepWiki/Algebra/SubresultantSpec`), so it lives apart
from the light policy files. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

/-! ### The subresultant-divisor resultant -/

section SubresultantResultant

variable {S : Type u} [EuclideanDomain S] [DecidableEq S]

/-- The **reduced-PRS cleanup** (Collins): the state carries the pending divisor `α` — the
previous step's `lc^{δ+1}`, initially `1` — and each pseudo-remainder is divided by it,
coefficient-wise and unchecked. The divisions are exact along genuine descents: each reduced
remainder is a constant multiple of a determinantal subresultant
(`DeepWiki/Algebra/SubresultantSpec`), which is the exactness invariant being discharged
(normal chains first — `subresultant_prs_normal_eq` is stated in exactly this
normalization). -/
def cleanReduced (st : S) (f g r : DensePoly S) : S × DensePoly S × S :=
  (st, ofList (r.coeffs.map (· / st)), g.leadingCoeff ^ (f.size - g.size + 1))

private theorem cleanReduced_size (st : S) (f g r : DensePoly S) :
    (cleanReduced st f g r).2.1.size ≤ r.size := by
  simp only [cleanReduced]
  set l := r.coeffs.map (· / st) with hl
  show (ofList l).size ≤ r.size
  have h1 : (ofList l).size ≤ l.length := trimTrailingZeros_length_le l
  have h2 : l.length = r.size := by rw [hl, List.length_map]; rfl
  omega

/-- **Resultant by the reduced pseudo-remainder sequence** (Collins): fraction-free without
any content gcds along the way. -/
def resultantPRSReduced (f g : DensePoly S) : S :=
  resultantDescent cleanReduced cleanReduced_size 1 f g (f.size - 1) (g.size - 1)

/-- The reduced-PRS resultant agrees with the Sylvester-determinant resultant at the
canonical degrees, **given** an exactness invariant for the carried divisors — the
hypothesis being discharged from the subresultant chain theorems
(`DeepWiki/Algebra/SubresultantPRS`; normal chains first). -/
theorem resultantPRSReduced_eq_of_invariant
    (I : S → DensePoly S → DensePoly S → Prop)
    (hclean : ∀ st f g, 2 ≤ g.size → g.size ≤ f.size → I st f g →
      C (cleanReduced st f g (pseudoMod f g)).1
          * (cleanReduced st f g (pseudoMod f g)).2.1
        = pseudoMod f g)
    (hstep : ∀ st f g, 2 ≤ g.size → g.size ≤ f.size → I st f g →
      I (cleanReduced st f g (pseudoMod f g)).2.2 g
        (cleanReduced st f g (pseudoMod f g)).2.1)
    (hswap : ∀ st f g, f.size < g.size → I st f g → I st g f)
    (f g : DensePoly S) (hI : I 1 f g) :
    resultantPRSReduced f g = (toPolynomial f).resultant (toPolynomial g)
      (toPolynomial f).natDegree (toPolynomial g).natDegree := by
  rw [resultantPRSReduced, natDegree_toPolynomial_eq_size_sub_one,
    natDegree_toPolynomial_eq_size_sub_one]
  exact resultantDescent_eq_of_invariant cleanReduced cleanReduced_size I
    hclean hstep hswap 1 f g _ _ hI
    (le_of_eq (natDegree_toPolynomial_eq_size_sub_one f))
    (le_of_eq (natDegree_toPolynomial_eq_size_sub_one g))

/-- Exact division certified semantically: if the bridged polynomial is a `C a`-multiple,
the coefficient-wise division reconstructs. -/
theorem exact_div_of_toPolynomial_C_mul {a : S} {r : DensePoly S} {P : Polynomial S}
    (h : toPolynomial r = Polynomial.C a * P) :
    C a * ofList (r.coeffs.map (· / a)) = r := by
  have hdvd : ∀ i, a ∣ r.coeff i := by
    intro i
    have hc := congrArg (fun q => Polynomial.coeff q i) h
    simp only [coeff_toPolynomial, Polynomial.coeff_C_mul] at hc
    exact ⟨P.coeff i, hc⟩
  apply toPolynomial_injective
  ext i
  rw [toPolynomial_mul, toPolynomial_C, Polynomial.coeff_C_mul, coeff_toPolynomial,
    coeff_toPolynomial, coeff_ofList, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hi : i < r.coeffs.length
  · rw [List.getElem?_eq_getElem hi]
    show a * (r.coeffs[i] / a) = r.coeff i
    have hco : r.coeff i = r.coeffs[i] := by
      rw [coeff, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      rfl
    rcases eq_or_ne a 0 with rfl | ha0
    · have h0 : r.coeffs[i] = 0 := by
        have := hdvd i
        rw [zero_dvd_iff, hco] at this
        exact this
      rw [h0, EuclideanDomain.zero_div, mul_zero, hco, h0]
    · rw [EuclideanDomain.mul_div_cancel' ha0 (by rw [← hco]; exact hdvd i), hco]
  · rw [List.getElem?_eq_none (by omega)]
    show a * 0 = r.coeff i
    rw [mul_zero, coeff_eq_zero_of_size_le r (by show r.coeffs.length ≤ i; omega)]

/-- **The reduced-PRS exactness invariant**: every division the descent will perform from
this state is exact — the pending divisor `C`-factors out of the bridged pseudo-remainder,
persistently along the mod steps and the entry swap. Mirrors the descent's recursion; the
running arc discharges `ReducedExact 1 f g` from the subresultant chain theorems. -/
def ReducedExact (α : S) (f g : DensePoly S) : Prop :=
  (2 ≤ g.size → g.size ≤ f.size →
    ∃ P : Polynomial S, toPolynomial (pseudoMod f g) = Polynomial.C α * P) ∧
  (2 ≤ g.size → g.size ≤ f.size →
    ReducedExact (g.leadingCoeff ^ (f.size - g.size + 1)) g
      (ofList ((pseudoMod f g).coeffs.map (· / α)))) ∧
  (f.size < g.size → ReducedExact α g f)
  termination_by f.size + 2 * g.size
  decreasing_by
    · have h1 : (pseudoMod f g).size < g.size := pseudoMod_size_lt (by omega) f
      have h2 : (ofList ((pseudoMod f g).coeffs.map (· / α))).size
          ≤ (pseudoMod f g).size := by
        calc (ofList ((pseudoMod f g).coeffs.map (· / α))).size
            ≤ ((pseudoMod f g).coeffs.map (· / α)).length :=
              trimTrailingZeros_length_le _
          _ = (pseudoMod f g).size := (List.length_map _).trans rfl
      omega
    · omega

/-- The descent computes the resultant from any `ReducedExact` entry state — the
single-hypothesis form; discharging the hypothesis is the running arc. -/
theorem resultantPRSReduced_eq_of_exact (f g : DensePoly S) (hI : ReducedExact 1 f g) :
    resultantPRSReduced f g = (toPolynomial f).resultant (toPolynomial g)
      (toPolynomial f).natDegree (toPolynomial g).natDegree := by
  refine resultantPRSReduced_eq_of_invariant ReducedExact ?_ ?_ ?_ f g hI
  · intro st f' g' hg2 hgf hI'
    rw [ReducedExact] at hI'
    obtain ⟨P, hP⟩ := hI'.1 hg2 hgf
    show C st * ofList ((pseudoMod f' g').coeffs.map (· / st)) = pseudoMod f' g'
    exact exact_div_of_toPolynomial_C_mul hP
  · intro st f' g' hg2 hgf hI'
    rw [ReducedExact] at hI'
    exact hI'.2.1 hg2 hgf
  · intro st f' g' hlt hI'
    rw [ReducedExact] at hI'
    exact hI'.2.2 hlt

/-! ### The exactness discharge, brick one: the first pseudo-remainder is a subresultant -/

open DeepWiki.SymbolicIntegration in
/-- **The first pseudo-remainder is (±) a determinantal subresultant**: instantiating the
migrated `subresultant_eq_pseudoRem` at the bridged pseudo-division identity. Together with
the telescopes this grounds the exactness of every reduced-PRS division. -/
theorem subresultant_eq_pseudoMod {f g : DensePoly S} (hg0 : g ≠ 0)
    (hgf : g.size ≤ f.size) (hg2 : 2 ≤ g.size) :
    subresultant (toPolynomial f) (toPolynomial g) (f.size - 1) (g.size - 1) (g.size - 2)
      = Polynomial.C ((-1 : S) ^ (f.size - g.size + 1))
          * toPolynomial (pseudoMod f g) := by
  have hgz : g.size ≠ 0 := fun h0 => hg0 (eq_zero_of_size_zero h0)
  have hf0 : f ≠ 0 := fun h0 => by rw [h0, size_zero] at hgf; omega
  have hlc : (toPolynomial g).coeff (g.size - 1) ≠ 0 := by
    rw [coeff_toPolynomial]
    exact leadingCoeff_ne_zero hgz
  have hid := pseudo_identity (f := f) hgz
  set k := f.size - g.size + 1 with hk
  have hkeq : f.size + 1 - g.size = k := by omega
  set Rem := Polynomial.C ((-1 : S) ^ k) * toPolynomial (pseudoMod f g) with hRem
  have hsq : Polynomial.C ((-1 : S) ^ k) * Polynomial.C ((-1 : S) ^ k)
      = (1 : Polynomial S) := by
    rw [← map_mul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, map_one]
  have hRdeg : Rem.natDegree < g.size - 1 := by
    calc Rem.natDegree ≤ (toPolynomial (pseudoMod f g)).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
      _ = (pseudoMod f g).size - 1 := natDegree_toPolynomial_eq_size_sub_one _
      _ < g.size - 1 := by
          have := pseudoMod_size_lt hgz f
          omega
  have hQdeg : (toPolynomial (pseudoDiv f g)).natDegree + (g.size - 1) ≤ f.size - 1 := by
    rcases eq_or_ne (pseudoDiv f g) 0 with hq0 | hq0
    · rw [hq0, toPolynomial_zero, Polynomial.natDegree_zero, zero_add]
      omega
    · exact pseudoDiv_natDegree_le hg0 hgf hq0
  have hrel : Polynomial.C ((toPolynomial g).coeff (g.size - 1)
        ^ ((f.size - 1) - (g.size - 1) + 1)) * toPolynomial f
      = Polynomial.C ((-1 : S) ^ ((f.size - 1) - (g.size - 1) + 1)) * Rem
        + toPolynomial g * toPolynomial (pseudoDiv f g) := by
    have he : (f.size - 1) - (g.size - 1) + 1 = k := by omega
    rw [he, hRem, ← mul_assoc, hsq, one_mul, coeff_toPolynomial]
    show Polynomial.C (g.leadingCoeff ^ k) * toPolynomial f
      = toPolynomial (pseudoMod f g) + toPolynomial g * toPolynomial (pseudoDiv f g)
    rw [← hkeq, ← hid]
    ring
  have hmain := subresultant_eq_pseudoRem (toPolynomial f) (toPolynomial g) Rem
    (toPolynomial (pseudoDiv f g)) (f.size - 1) (g.size - 1) Rem.natDegree
    hlc (by omega) rfl
    (le_of_eq (natDegree_toPolynomial_eq_size_sub_one g)) hQdeg hrel
  rw [show g.size - 2 = (g.size - 1) - 1 from by omega]
  exact hmain

/-! ### The exactness discharge: the α-divisibility ledger

The local invariant that closes Brown–Traub's exact-divisibility theorem without a global
telescope: at every descent state, the carried divisor `α` `C`-factors out of **every**
lower-index subresultant of the current pair, with exponent the index-distance. The ledger
holds trivially at the entry (`α = 1`), transfers across the mod step by
`subresultant_prs_step` (the exponent slack `(a−b)(b−c−1) ≥ 0` is Brown–Traub's eq.-37
nonnegativity, localized), and across the entry swap by `subresultant_swap`. The head of
`ReducedExact` is the ledger at index `deg g − 1` combined with
`subresultant_eq_pseudoMod`. -/

open DeepWiki.SymbolicIntegration in
/-- The α-divisibility ledger: `α ≠ 0`, and `C (α^{deg g − j})` factors out of every
subresultant `Sⱼ(tf, tg)` with `j < deg g`. -/
def SubresLedger (α : S) (f g : DensePoly S) : Prop :=
  α ≠ 0 ∧ ∀ j < (toPolynomial g).natDegree,
    ∃ P : Polynomial S,
      subresultant (toPolynomial f) (toPolynomial g)
        (toPolynomial f).natDegree (toPolynomial g).natDegree j
        = Polynomial.C (α ^ ((toPolynomial g).natDegree - j)) * P

/-- The ledger holds at the entry state `α = 1`. -/
theorem subresLedger_one (f g : DensePoly S) : SubresLedger 1 f g :=
  ⟨one_ne_zero, fun j _ =>
    ⟨_, by rw [one_pow, map_one, one_mul]⟩⟩

open DeepWiki.SymbolicIntegration in
/-- The ledger transfers across the entry swap. -/
theorem SubresLedger.swap {α : S} {f g : DensePoly S} (h : SubresLedger α f g)
    (hfg : f.size < g.size) : SubresLedger α g f := by
  obtain ⟨hα, hled⟩ := h
  refine ⟨hα, fun j hj => ?_⟩
  have hf0 : f ≠ 0 := fun h0 => by
    rw [h0, toPolynomial_zero, Polynomial.natDegree_zero] at hj
    omega
  have hg0 : g ≠ 0 := fun h0 => by rw [h0, size_zero] at hfg; omega
  have hdf := natDegree_toPolynomial_eq_size_sub_one f
  have hdg := natDegree_toPolynomial_eq_size_sub_one g
  have hfs : 2 ≤ f.size := by
    have : f.size ≠ 0 := fun h0 => hf0 (eq_zero_of_size_zero h0)
    omega
  have hlt : (toPolynomial f).natDegree < (toPolynomial g).natDegree := by omega
  obtain ⟨P, hP⟩ := hled j (by omega)
  refine ⟨(-1 : Polynomial S) ^ (((toPolynomial f).natDegree - j)
      * ((toPolynomial g).natDegree - j))
    * Polynomial.C (α ^ ((toPolynomial g).natDegree - (toPolynomial f).natDegree)) * P, ?_⟩
  rw [subresultant_swap (toPolynomial g) (toPolynomial f) _ _ j (by omega) (by omega), hP]
  rw [show (toPolynomial g).natDegree - j
      = ((toPolynomial f).natDegree - j)
        + ((toPolynomial g).natDegree - (toPolynomial f).natDegree) from by omega,
    pow_add, map_mul]
  ring

open DeepWiki.SymbolicIntegration in
/-- **The ledger step**: under the mod-branch guards, the pending division is exact (the
`ReducedExact` head) and the ledger transfers to the next state. -/
theorem SubresLedger.step {α : S} {f g : DensePoly S} (h : SubresLedger α f g)
    (hg2 : 2 ≤ g.size) (hgf : g.size ≤ f.size) :
    (∃ P : Polynomial S, toPolynomial (pseudoMod f g) = Polynomial.C α * P) ∧
    SubresLedger (g.leadingCoeff ^ (f.size - g.size + 1)) g
      (ofList ((pseudoMod f g).coeffs.map (· / α))) := by
  obtain ⟨hα, hled⟩ := h
  have hg0 : g ≠ 0 := fun h0 => by rw [h0, size_zero] at hg2; omega
  have hf0 : f ≠ 0 := fun h0 => by rw [h0, size_zero] at hgf; omega
  have hgz : g.size ≠ 0 := fun h0 => hg0 (eq_zero_of_size_zero h0)
  have hlcg : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero hgz
  have hdf := natDegree_toPolynomial_eq_size_sub_one f
  have hdg := natDegree_toPolynomial_eq_size_sub_one g
  -- the head: brick one + the ledger at index `deg g − 1`
  have hbrick := subresultant_eq_pseudoMod (S := S) hg0 hgf hg2
  obtain ⟨P0, hP0⟩ := hled ((toPolynomial g).natDegree - 1) (by omega)
  have hsq1 : Polynomial.C ((-1 : S) ^ (f.size - g.size + 1))
      * Polynomial.C ((-1 : S) ^ (f.size - g.size + 1)) = 1 := by
    rw [← map_mul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, map_one]
  have hhead : toPolynomial (pseudoMod f g)
      = Polynomial.C α * (Polynomial.C ((-1 : S) ^ (f.size - g.size + 1)) * P0) := by
    have h1 : Polynomial.C ((-1 : S) ^ (f.size - g.size + 1))
        * toPolynomial (pseudoMod f g)
        = Polynomial.C (α ^ ((toPolynomial g).natDegree
            - ((toPolynomial g).natDegree - 1))) * P0 := by
      rw [← hP0, ← hbrick]
      congr 1 <;> omega
    rw [show (toPolynomial g).natDegree - ((toPolynomial g).natDegree - 1) = 1 from by omega,
      pow_one] at h1
    calc toPolynomial (pseudoMod f g)
        = (Polynomial.C ((-1 : S) ^ (f.size - g.size + 1))
            * Polynomial.C ((-1 : S) ^ (f.size - g.size + 1)))
          * toPolynomial (pseudoMod f g) := by rw [hsq1, one_mul]
      _ = Polynomial.C ((-1 : S) ^ (f.size - g.size + 1))
          * (Polynomial.C ((-1 : S) ^ (f.size - g.size + 1))
            * toPolynomial (pseudoMod f g)) := by ring
      _ = Polynomial.C ((-1 : S) ^ (f.size - g.size + 1))
          * (Polynomial.C α * P0) := by rw [h1]
      _ = Polynomial.C α * (Polynomial.C ((-1 : S) ^ (f.size - g.size + 1)) * P0) := by ring
  refine ⟨⟨_, hhead⟩, ?_⟩
  -- the cleaned remainder and its bridged reading
  set h' := ofList ((pseudoMod f g).coeffs.map (· / α)) with hh'
  have hex : C α * h' = pseudoMod f g := exact_div_of_toPolynomial_C_mul hhead
  have hth : toPolynomial (pseudoMod f g) = Polynomial.C α * toPolynomial h' := by
    rw [← hex, toPolynomial_mul, toPolynomial_C]
  rcases eq_or_ne h' 0 with h0 | h0
  · rw [h0]
    exact ⟨pow_ne_zero _ hlcg, fun j hj => by
      rw [toPolynomial_zero, Polynomial.natDegree_zero] at hj
      omega⟩
  refine ⟨pow_ne_zero _ hlcg, fun j hj => ?_⟩
  -- degrees
  have hh'size : h'.size < g.size := by
    have h1 : (pseudoMod f g).size < g.size := pseudoMod_size_lt hgz f
    have h2 : h'.size ≤ (pseudoMod f g).size := by
      rw [hh']
      calc (ofList ((pseudoMod f g).coeffs.map (· / α))).size
          ≤ ((pseudoMod f g).coeffs.map (· / α)).length := trimTrailingZeros_length_le _
        _ = (pseudoMod f g).size := (List.length_map _).trans rfl
    omega
  have hdh := natDegree_toPolynomial_eq_size_sub_one h'
  have hh'z : h'.size ≠ 0 := fun hz => h0 (eq_zero_of_size_zero hz)
  have hc_lt : (toPolynomial h').natDegree < (toPolynomial g).natDegree := by omega
  -- the pseudo-division relation in step-lemma shape
  have hrel : Polynomial.C (g.leadingCoeff ^ (f.size + 1 - g.size)) * toPolynomial f
      = Polynomial.C α * toPolynomial h'
        + toPolynomial g * toPolynomial (pseudoDiv f g) := by
    calc Polynomial.C (g.leadingCoeff ^ (f.size + 1 - g.size)) * toPolynomial f
        = toPolynomial (pseudoDiv f g) * toPolynomial g + toPolynomial (pseudoMod f g) :=
          (pseudo_identity hgz).symm
      _ = Polynomial.C α * toPolynomial h'
          + toPolynomial g * toPolynomial (pseudoDiv f g) := by rw [hth]; ring
  have hQdeg : (toPolynomial (pseudoDiv f g)).natDegree + (toPolynomial g).natDegree
      ≤ (toPolynomial f).natDegree := by
    rcases eq_or_ne (pseudoDiv f g) 0 with hq0 | hq0
    · rw [hq0, toPolynomial_zero, Polynomial.natDegree_zero, zero_add]
      omega
    · have := pseudoDiv_natDegree_le hg0 hgf hq0
      omega
  obtain ⟨Pj, hPj⟩ := hled j (by omega)
  have hstep := subresultant_prs_step (toPolynomial f) (toPolynomial g) (toPolynomial h')
    (toPolynomial (pseudoDiv f g)) (g.leadingCoeff ^ (f.size + 1 - g.size)) α
    (toPolynomial f).natDegree (toPolynomial g).natDegree (toPolynomial h').natDegree j
    hα hj hc_lt rfl le_rfl hQdeg hrel
  -- rewrite `(tg).coeff (deg tg)` as `lc g`
  have hcoef : (toPolynomial g).coeff (toPolynomial g).natDegree = g.leadingCoeff := by
    rw [coeff_toPolynomial, hdg, leadingCoeff]
  rw [hcoef, hPj] at hstep
  -- abbreviations for the exponent algebra
  set a := (toPolynomial f).natDegree
  set b := (toPolynomial g).natDegree
  set c := (toPolynomial h').natDegree
  set L := g.leadingCoeff
  -- hstep : C ((L^{a−b+1})^{b−j}) * (C (α^{b−j}) * Pj)
  --   = (−1)^{(a−j)(b−j)} * (C L ^{a−c} * (C (α^{b−j}) * S'))
  -- cancel C (α^{b−j}), then split L-powers with the eq-37 slack
  have hLpow : f.size + 1 - g.size = a - b + 1 := by omega
  have hslack : (a - b + 1) * (b - j)
      = (a - c) + ((a - b + 1) * (c - j) + (a - b) * (b - c - 1)) := by
    obtain ⟨u, hu⟩ := Nat.le.dest (show b ≤ a from by omega)
    obtain ⟨v, hv⟩ := Nat.le.dest (Nat.succ_le_of_lt hc_lt)
    obtain ⟨w, hw⟩ := Nat.le.dest (Nat.succ_le_of_lt hj)
    have e1 : a - b + 1 = u + 1 := by omega
    have e2 : b - j = v + w + 2 := by omega
    have e3 : a - c = u + v + 1 := by omega
    have e4 : c - j = w + 1 := by omega
    have e5 : b - c - 1 = v := by omega
    have e6 : a - b = u := by omega
    rw [e1, e2, e3, e4, e5, e6]
    ring
  set S' := subresultant (toPolynomial g) (toPolynomial h') b c j with hS'
  set ε : Polynomial S := (-1 : Polynomial S) ^ ((a - j) * (b - j)) with hε
  have hLpow' : f.size + 1 - g.size = a - b + 1 := hLpow
  rw [hLpow'] at hstep
  rw [show ((Polynomial.C L) ^ (a - c) : Polynomial S) = Polynomial.C (L ^ (a - c)) from by
    rw [map_pow]] at hstep
  have hα' : (Polynomial.C (α ^ (b - j)) : Polynomial S) ≠ 0 := by
    rw [Ne, Polynomial.C_eq_zero]
    exact pow_ne_zero _ hα
  have hkey : Polynomial.C (α ^ (b - j))
        * (Polynomial.C ((L ^ (a - b + 1)) ^ (b - j)) * Pj)
      = Polynomial.C (α ^ (b - j)) * (ε * (Polynomial.C (L ^ (a - c)) * S')) := by
    calc Polynomial.C (α ^ (b - j)) * (Polynomial.C ((L ^ (a - b + 1)) ^ (b - j)) * Pj)
        = Polynomial.C ((L ^ (a - b + 1)) ^ (b - j))
          * (Polynomial.C (α ^ (b - j)) * Pj) := by ring
      _ = ε * (Polynomial.C (L ^ (a - c)) * (Polynomial.C (α ^ (b - j)) * S')) := hstep
      _ = Polynomial.C (α ^ (b - j)) * (ε * (Polynomial.C (L ^ (a - c)) * S')) := by ring
  have hmain := mul_left_cancel₀ hα' hkey
  have hLsplit : ((L ^ (a - b + 1)) ^ (b - j) : S)
      = L ^ (a - c) * L ^ ((a - b + 1) * (c - j) + (a - b) * (b - c - 1)) := by
    rw [← pow_mul, ← pow_add, ← hslack]
  rw [hLsplit, map_mul] at hmain
  have hL' : (Polynomial.C (L ^ (a - c)) : Polynomial S) ≠ 0 := by
    rw [Ne, Polynomial.C_eq_zero]
    exact pow_ne_zero _ hlcg
  have hmain2 : Polynomial.C (L ^ ((a - b + 1) * (c - j) + (a - b) * (b - c - 1))) * Pj
      = ε * S' := by
    apply mul_left_cancel₀ hL'
    calc Polynomial.C (L ^ (a - c))
          * (Polynomial.C (L ^ ((a - b + 1) * (c - j) + (a - b) * (b - c - 1))) * Pj)
        = Polynomial.C (L ^ (a - c))
            * Polynomial.C (L ^ ((a - b + 1) * (c - j) + (a - b) * (b - c - 1))) * Pj := by
          ring
      _ = ε * (Polynomial.C (L ^ (a - c)) * S') := hmain
      _ = Polynomial.C (L ^ (a - c)) * (ε * S') := by ring
  have hεsq : ε * ε = 1 := by
    rw [hε, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hsolve : S' = ε * (Polynomial.C (L ^ ((a - b + 1) * (c - j) + (a - b) * (b - c - 1)))
      * Pj) := by
    calc S' = (ε * ε) * S' := by rw [hεsq, one_mul]
      _ = ε * (ε * S') := by ring
      _ = ε * (Polynomial.C (L ^ ((a - b + 1) * (c - j) + (a - b) * (b - c - 1))) * Pj) := by
          rw [← hmain2]
  refine ⟨ε * Polynomial.C (L ^ ((a - b) * (b - c - 1))) * Pj, ?_⟩
  rw [hsolve, pow_add, map_mul]
  rw [show ((L ^ (f.size - g.size + 1)) ^ (c - j) : S)
      = L ^ ((a - b + 1) * (c - j)) from by
    rw [show f.size - g.size + 1 = a - b + 1 from by omega, ← pow_mul]]
  ring

/-- The ledger implies the full recursive exactness invariant, by descent on the
descent's own measure. -/
theorem reducedExact_of_ledger {α : S} {f g : DensePoly S} (h : SubresLedger α f g) :
    ReducedExact α f g := by
  rw [ReducedExact]
  exact ⟨fun hg2 hgf => (h.step hg2 hgf).1,
    fun hg2 hgf => reducedExact_of_ledger (h.step hg2 hgf).2,
    fun hfg => reducedExact_of_ledger (h.swap hfg)⟩
  termination_by f.size + 2 * g.size
  decreasing_by
    · have h1 : (pseudoMod f g).size < g.size := pseudoMod_size_lt (by omega) f
      have h2 : (ofList ((pseudoMod f g).coeffs.map (· / α))).size
          ≤ (pseudoMod f g).size := by
        calc (ofList ((pseudoMod f g).coeffs.map (· / α))).size
            ≤ ((pseudoMod f g).coeffs.map (· / α)).length :=
              trimTrailingZeros_length_le _
          _ = (pseudoMod f g).size := (List.length_map _).trans rfl
      omega
    · omega

/-- **Every reduced-PRS division is exact** (Brown–Traub: the pseudo-remainder is exactly
divisible by the carried `lc^{δ+1}`): the exactness invariant holds unconditionally. -/
theorem reducedExact_all (f g : DensePoly S) : ReducedExact 1 f g :=
  reducedExact_of_ledger (subresLedger_one f g)

/-- The reduced-PRS resultant agrees with the Sylvester-determinant resultant at the
canonical degrees — hypothesis-free. -/
theorem resultantPRSReduced_eq (f g : DensePoly S) :
    resultantPRSReduced f g = (toPolynomial f).resultant (toPolynomial g)
      (toPolynomial f).natDegree (toPolynomial g).natDegree :=
  resultantPRSReduced_eq_of_exact f g (reducedExact_all f g)

end SubresultantResultant

end DensePoly

end DeepWiki.CAlgebra
