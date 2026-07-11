import DeepWiki.ComputableAlgebra.PolyEuclidean
import DeepWiki.ComputableAlgebra.PolyReprBridge
import DeepWiki.ComputableAlgebra.PolySquarefree
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Tactic.LinearCombination

/-! # Dense well-founded Euclidean division and gcd

Euclidean division, extended gcd, and divisibility testing on `DensePoly`, by well-founded recursion
on the normalized list length. The defs are `[CField α]`-only (so they reduce under compiled decision
over noncomputable-`CFieldSpec` carriers); correctness through `toPoly` is proved by well-founded
induction on each def's own recursion. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

namespace DensePoly

variable {α : Type*} [CField α]

/-! ### Euclidean division `cdivmodWf`

Termination is by `(cnorm p).length`, strictly dropped each reduce step (`stepG_length_lt`). -/

/-- One reduce step of Euclidean division: replace `p` by the leading-term-cancelled
`cnorm (p − (clead p/clead q)·xᵏ·q)`. Recursion driver of `cdivmodWf`. -/
private def reduceStepWf (p q : DensePoly α) : DensePoly α :=
  cnorm (csub (cnorm p)
    (cmul (cshift ((cnorm p : List α).length - (cnorm q : List α).length)
      [CField.div (clead p) (clead q)]) (cnorm q)))

/-- Generic Euclidean division on `DensePoly`: `cdivmodWf p q = (quotient, remainder)` with
`p = quotient · q + remainder` over `K` (`q ≠ 0`). Well-founded on `(cnorm p).length`. -/
def cdivmodWf (p q : DensePoly α) : DensePoly α × DensePoly α :=
  let pn := cnorm p
  let qn := cnorm q
  if cisZero qn then ([], [])
  else if (pn : List α).length < (qn : List α).length then ([], pn)
  else
    let c := CField.div (clead pn) (clead qn)
    let k := (pn : List α).length - (qn : List α).length
    let term := cshift k [c]
    let p' := reduceStepWf p q
    if (cnorm p' : List α).length < (cnorm p : List α).length then
      let (quo, rem) := cdivmodWf p' q
      (cadd term quo, rem)
    else (term, p')   -- unreachable over a genuine field (`stepG_length_lt`)
termination_by (cnorm p).length
decreasing_by assumption

/-- Remainder of generic Euclidean division (`cdivmodWf`'s second component). -/
def cmodWf (p q : DensePoly α) : DensePoly α := (cdivmodWf p q).2

/-- Quotient of generic Euclidean division (`cdivmodWf`'s first component). -/
def cdivWf (p q : DensePoly α) : DensePoly α := (cdivmodWf p q).1

/-! ### Extended Euclidean algorithm `cgcdWf`

Termination is by `(cnorm b).length`, strictly dropped by the remainder (`cmodWf_length_lt`). -/

/-- Extended Euclidean algorithm on `DensePoly`: `cgcdWf a b = (g, s, t)` with `s·a + t·b = g` and
`g = gcd(a, b)` over `K`. Well-founded on `(cnorm b).length`. -/
def cgcdWf (a b : DensePoly α) : DensePoly α × DensePoly α × DensePoly α :=
  if cisZero b then (cnorm a, [CCommRing.one], [])
  else
    let q := cdivWf a b
    let r := cmodWf a b
    if (cnorm r : List α).length < (cnorm b : List α).length then
      let (g, s, t) := cgcdWf b r
      (g, t, csub s (cmul t q))
    else (cnorm a, [CCommRing.one], [])   -- unreachable over a genuine field (`cmodWf_length_lt`)
termination_by (cnorm b).length
decreasing_by assumption

/-- The gcd component of the extended Euclidean algorithm (`cgcdWf`'s first component). -/
def cgcdWfGcd (a b : DensePoly α) : DensePoly α := (cgcdWf a b).1

/-- Generic monic gcd: monic-normalize the gcd component of `cgcdWf`. -/
def cgcdMonicWf (p q : DensePoly α) : DensePoly α :=
  cmonic (cgcdWf p q).1

/-! ### The reduce step strictly shortens

The per-step length drop that discharges `cdivmodWf`'s own structural termination guard. -/

variable [CFieldSpec α]

/-- One Euclidean-division step strictly drops the degree in `(CFieldSpec.K α)[X]`: subtracting
`C (lcP/lcQ)·X^(degP−degQ)·Q` cancels the top coefficient. -/
theorem degreeG_reduce_step_lt {P Q : (CFieldSpec.K α)[X]} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree ≤ P.natDegree) :
    (P - C (P.leadingCoeff / Q.leadingCoeff)
        * X ^ (P.natDegree - Q.natDegree) * Q).degree < P.degree := by
  have hQlc : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hPlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hc0 : P.leadingCoeff / Q.leadingCoeff ≠ 0 := div_ne_zero hPlc hQlc
  have hCc : (C (P.leadingCoeff / Q.leadingCoeff)) ≠ 0 := by rwa [Ne, Polynomial.C_eq_zero]
  have hXk : (X ^ (P.natDegree - Q.natDegree) : (CFieldSpec.K α)[X]) ≠ 0 :=
    pow_ne_zero _ Polynomial.X_ne_zero
  set T := C (P.leadingCoeff / Q.leadingCoeff) * X ^ (P.natDegree - Q.natDegree) * Q with hT
  have hT0 : T ≠ 0 := mul_ne_zero (mul_ne_zero hCc hXk) hQ
  have hTnd : T.natDegree = P.natDegree := by
    rw [hT, Polynomial.natDegree_mul (mul_ne_zero hCc hXk) hQ,
      Polynomial.natDegree_mul hCc hXk, Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
    omega
  have hTlc : T.leadingCoeff = P.leadingCoeff := by
    rw [hT, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_X_pow, mul_one, div_mul_cancel₀ _ hQlc]
  exact Polynomial.degree_sub_lt
    (by rw [Polynomial.degree_eq_natDegree hP, Polynomial.degree_eq_natDegree hT0, hTnd]) hP
    hTlc.symm

/-- One reduce step strictly shortens the normalized list: `cnorm (p − (lcP/lcQ)·xᵏ·q)` has
strictly smaller normalized length than `p`. -/
private theorem stepG_length_lt (p q : DensePoly α) (hp : cnorm p ≠ []) (hq : cnorm q ≠ [])
    (hpq : (cnorm q : List α).length ≤ (cnorm p : List α).length) :
    (cnorm (csub (cnorm p)
        (cmul (cshift ((cnorm p : List α).length - (cnorm q : List α).length)
          [CField.div (clead p) (clead q)])
          (cnorm q))) : List α).length < (cnorm p : List α).length := by
  have hP : toPoly p ≠ 0 := fun h => hp ((cnormG_eq_nil_iff p).mpr h)
  have hQ : toPoly q ≠ 0 := fun h => hq ((cnormG_eq_nil_iff q).mpr h)
  have hk : (cnorm p : List α).length - (cnorm q : List α).length
      = (toPoly p).natDegree - (toPoly q).natDegree := by
    rw [length_cnormG_of_ne p hp, length_cnormG_of_ne q hq]; omega
  have hc : CFieldSpec.toK (CField.div (clead p) (clead q))
      = (toPoly p).leadingCoeff / (toPoly q).leadingCoeff := by
    rw [CFieldSpec.toK_div, toK_cleadG_eq_leadingCoeff, toK_cleadG_eq_leadingCoeff]
  set step := csub (cnorm p)
    (cmul (cshift ((cnorm p : List α).length - (cnorm q : List α).length)
      [CField.div (clead p) (clead q)]) (cnorm q))
    with hstepdef
  have hstep : toPoly step
      = toPoly p - C ((toPoly p).leadingCoeff / (toPoly q).leadingCoeff)
          * X ^ ((toPoly p).natDegree - (toPoly q).natDegree) * toPoly q := by
    rw [hstepdef]
    simp only [denote, hk]
    simp only [mul_zero, add_zero]
    have hcoef : CFieldSpec.toK (clead p) / CFieldSpec.toK (clead q)
        = (toPoly p).leadingCoeff / (toPoly q).leadingCoeff := by
      simpa [CFieldSpec.toK_div] using hc
    rw [hcoef]
    ring
  have hpq' : (toPoly q).natDegree ≤ (toPoly p).natDegree := by
    have e1 := length_cnormG_of_ne p hp
    have e2 := length_cnormG_of_ne q hq
    omega
  have hdeg : (toPoly step).degree < (toPoly p).degree := by
    rw [hstep]; exact degreeG_reduce_step_lt hP hQ hpq'
  by_cases hs0 : toPoly step = 0
  · rw [(cnormG_eq_nil_iff _).mpr hs0, List.length_nil]
    exact List.length_pos_iff.mpr hp
  · have hne : cnorm step ≠ [] := fun h => hs0 ((cnormG_eq_nil_iff _).mp h)
    have hlt := Polynomial.natDegree_lt_natDegree hs0 hdeg
    rw [length_cnormG_of_ne _ hne, length_cnormG_of_ne p hp]
    omega

/-- The reduce step strictly shortens the normalized list (over `[CFieldSpec α]`): discharges
`cdivmodWf`'s structural guard, so over a genuine field the reducing branch is always taken. -/
private theorem reduceStepWf_length_lt (p q : DensePoly α) (hcz : cisZero (cnorm q) = false)
    (hlen : ¬ (cnorm p : List α).length < (cnorm q : List α).length) :
    (cnorm (reduceStepWf p q) : List α).length < (cnorm p : List α).length := by
  have hq : cnorm q ≠ [] := by
    simpa [cisZero, List.isEmpty_iff] using hcz
  have hle : (cnorm q : List α).length ≤ (cnorm p : List α).length := Nat.le_of_not_lt hlen
  have hpn : cnorm p ≠ [] := by
    intro h
    rw [h, List.length_nil, Nat.le_zero] at hle
    exact hq (List.length_eq_zero_iff.mp hle)
  have hstep := stepG_length_lt (cnorm p) (cnorm q)
    (by simpa using hpn) (by simpa using hq) (by simpa using hle)
  rw [reduceStepWf]
  simpa only [cnormG_idem, cleadG_cnormG] using hstep

/-- Euclidean-division identity through `toPoly` for `cdivmodWf` (nonzero divisor):
`toPoly p = toPoly (quotient) · toPoly q + toPoly (remainder)`. -/
theorem toPolyG_cdivmodWf (p q : DensePoly α) (hq0 : cnorm q ≠ []) :
    toPoly p
      = toPoly (cdivmodWf p q).1 * toPoly q + toPoly (cdivmodWf p q).2 := by
  -- Direct well-founded induction on `cdivmodWf`'s own recursion: the four branches are the divisor-zero
  -- contradiction, the `deg p < deg q` base, the reduce step (IH on `p'`), and the unreachable branch.
  induction p using cdivmodWf.induct (q := q) with
  | case1 p =>
    -- divisor zero contradicts `cnorm q ≠ []`
    rename_i hcz
    have hcz' : cisZero (cnorm q) = true := hcz
    exact absurd (by simpa [cisZero, List.isEmpty_iff] using hcz') hq0
  | case2 p =>
    -- `deg p < deg q`: `cdivmodWf p q = ([], cnorm p)`
    rename_i hcz hlen
    have hcz' : cisZero (cnorm q) = false := by simpa using hcz
    have hlen' : (cnorm p : List α).length < (cnorm q : List α).length := hlen
    have hval : cdivmodWf p q = ([], cnorm p) := by
      rw [cdivmodWf.eq_def, if_neg (by simp [hcz']), if_pos hlen']
    rw [hval]
    simp [toPolyG_cnormG]
  | case3 p =>
    -- reducing branch: `p = term·q + p'`, then IH `p' = quo·q + rem`
    rename_i pn qn hcz hlen p' hdec quo rem hqr ih
    have hcz' : cisZero (cnorm q) = false := by simpa using hcz
    have hlen' : ¬ (cnorm p : List α).length < (cnorm q : List α).length := hlen
    set term := cshift ((cnorm p : List α).length - (cnorm q : List α).length)
      [CField.div (clead p) (clead q)] with hterm
    have hval : cdivmodWf p q = (cadd term quo, rem) := by
      rw [cdivmodWf.eq_def, if_neg (by simp [hcz']), if_neg hlen', if_pos hdec]
      simp only [cleadG_cnormG, hterm]
      rw [show (p.reduceStepWf q).cdivmodWf q = (quo, rem) from hqr]
    rw [hval]
    have hstep : toPoly (reduceStepWf p q) = toPoly p - toPoly term * toPoly q := by
      simp [reduceStepWf, hterm]
    have hih : toPoly (reduceStepWf p q)
        = toPoly quo * toPoly q + toPoly rem := by
      rw [ih, hqr]
    simp only [denote]
    rw [hstep] at hih
    linear_combination hih
  | case4 p =>
    -- unreachable over a genuine field (`reduceStepWf_length_lt`)
    rename_i pn qn hcz hlen p' hdec
    have hcz' : cisZero (cnorm q) = false := by simpa using hcz
    have hlen' : ¬ (cnorm p : List α).length < (cnorm q : List α).length := hlen
    exact absurd (reduceStepWf_length_lt p q hcz' hlen') hdec

/-- `toPoly p = toPoly (cdivWf p q) · toPoly q + toPoly (cmodWf p q)`: the Euclidean identity
in quotient/remainder form (nonzero divisor). -/
theorem toPolyG_cmodWf (p q : DensePoly α) (hq0 : cnorm q ≠ []) :
    toPoly p = toPoly (cdivWf p q) * toPoly q + toPoly (cmodWf p q) := by
  rw [cdivWf, cmodWf]; exact toPolyG_cdivmodWf p q hq0

/-! ### Remainder shortening and gcd correctness -/

/-- The remainder strictly shortens below `(cnorm b).length` for a nonzero divisor: discharges
`cgcdWf`'s structural guard, so over a genuine field the recursing branch is always taken. -/
theorem cmodWf_length_lt (a b : DensePoly α) (hb : cnorm b ≠ []) :
    (cnorm (cmodWf a b) : List α).length < (cnorm b : List α).length := by
  rw [cmodWf]
  induction a using cdivmodWf.induct (q := b) with
  | case1 a =>
    rename_i hcz
    have hcz' : cisZero (cnorm b) = true := hcz
    exact absurd (by simpa [cisZero, List.isEmpty_iff] using hcz') hb
  | case2 a =>
    rename_i hcz hlen
    have hcz' : cisZero (cnorm b) = false := by simpa using hcz
    have hlen' : (cnorm a : List α).length < (cnorm b : List α).length := hlen
    have hval : cdivmodWf a b = ([], cnorm a) := by
      rw [cdivmodWf.eq_def, if_neg (by simp [hcz']), if_pos hlen']
    rw [hval, cnormG_idem]
    exact hlen'
  | case3 a =>
    rename_i pn qn hcz hlen a' hdec quo rem hqr ih
    have hcz' : cisZero (cnorm b) = false := by simpa using hcz
    have hlen' : ¬ (cnorm a : List α).length < (cnorm b : List α).length := hlen
    set term := cshift ((cnorm a : List α).length - (cnorm b : List α).length)
      [CField.div (clead a) (clead b)] with hterm
    have hval : cdivmodWf a b = (cadd term quo, rem) := by
      rw [cdivmodWf.eq_def, if_neg (by simp [hcz']), if_neg hlen', if_pos hdec]
      simp only [cleadG_cnormG, hterm]
      rw [show (a.reduceStepWf b).cdivmodWf b = (quo, rem) from hqr]
    rw [hval]
    rw [hqr] at ih
    exact ih
  | case4 a =>
    rename_i pn qn hcz hlen a' hdec
    have hcz' : cisZero (cnorm b) = false := by simpa using hcz
    have hlen' : ¬ (cnorm a : List α).length < (cnorm b : List α).length := hlen
    exact absurd (reduceStepWf_length_lt a b hcz' hlen') hdec

/-- Bézout identity through `toPoly` for `cgcdWf`: with `(g, s, t) = cgcdWf a b`,
`toPoly s · toPoly a + toPoly t · toPoly b = toPoly g`. -/
theorem toPolyG_cgcdWf (a b : DensePoly α) :
    toPoly (cgcdWf a b).2.1 * toPoly a + toPoly (cgcdWf a b).2.2 * toPoly b
      = toPoly (cgcdWf a b).1 := by
  induction a, b using cgcdWf.induct with
  | case1 a b =>
    -- `cisZero b`: `cgcdWf a b = (cnorm a, [1], [])`, Bézout `1·a + 0·b = a`
    rename_i hcz
    have hb0 : toPoly b = 0 := (cisZeroG_iff b).mp hcz
    have hval : cgcdWf a b = (cnorm a, [CCommRing.one], []) := by
      rw [cgcdWf.eq_def, if_pos hcz]
    rw [hval]
    simp [toPolyG_cnormG, toPolyG_cons, CFieldSpec.toK_one, hb0]
  | case2 a b =>
    -- recursing branch: `cgcdWf a b = (g, t, csub s (cmul t q))` with `(g,s,t) = cgcdWf b r`,
    -- `r = cmodWf a b`, `q = cdivWf a b`. IH: `s·b + t·r = g`. Euclid: `a = q·b + r`.
    -- the `have rr := a.cmodWf b` let-binder is auto-introduced between `hcz` and `hdec`; recover all.
    rename_i hcz rr hdec g s t hgst ih
    have hbne : cnorm b ≠ [] := by
      intro h; rw [cisZero] at hcz; simp [h] at hcz
    have hval : cgcdWf a b = (g, t, csub s (cmul t (cdivWf a b))) := by
      rw [cgcdWf.eq_def, if_neg hcz, if_pos hdec]
      show (let (g, s, t) := cgcdWf b (cmodWf a b); (g, t, csub s (cmul t (cdivWf a b)))) = _
      rw [show cgcdWf b (cmodWf a b) = (g, s, t) from hgst]
    have heuclid : toPoly a = toPoly (cdivWf a b) * toPoly b + toPoly (cmodWf a b) :=
      toPolyG_cmodWf a b hbne
    -- IH at the recursive pair `(b, cmodWf a b)`: `s·b + t·r = g`
    rw [show cgcdWf b (cmodWf a b) = (g, s, t) from hgst] at ih
    rw [hval]
    simp only [denote]
    simp only at ih
    linear_combination ih + toPoly t * heuclid
  | case3 a b =>
    -- unreachable over a genuine field (`cmodWf_length_lt`)
    rename_i hcz rr hdec
    have hbne : cnorm b ≠ [] := by
      intro h; rw [cisZero] at hcz; simp [h] at hcz
    exact absurd (cmodWf_length_lt a b hbne) hdec

/-- `cgcdWf`'s gcd is greatest among common divisors: any `d` dividing both `toPoly a` and
`toPoly b` divides `toPoly (cgcdWf a b).1`. Immediate from Bézout. -/
theorem toPolyG_dvd_cgcdWf {d : (CFieldSpec.K α)[X]} (a b : DensePoly α)
    (ha : d ∣ toPoly a) (hb : d ∣ toPoly b) :
    d ∣ toPoly (cgcdWf a b).1 := by
  rw [← toPolyG_cgcdWf a b]
  exact dvd_add (ha.mul_left _) (hb.mul_left _)

/-- `cgcdWf`'s gcd divides both inputs: `toPoly (cgcdWf a b).1` divides `toPoly a` and
`toPoly b`. With `toPolyG_dvd_cgcdWf` this characterizes it as an honest gcd in `K[X]`. -/
theorem toPolyG_cgcdWf_dvd (a b : DensePoly α) :
    toPoly (cgcdWf a b).1 ∣ toPoly a ∧ toPoly (cgcdWf a b).1 ∣ toPoly b := by
  induction a, b using cgcdWf.induct with
  | case1 a b =>
    -- `cisZero b`: `cgcdWf a b = (cnorm a, ...)`, so `g = cnorm a ∣ a` (refl) and `g ∣ b = 0`
    rename_i hcz
    have hb0 : toPoly b = 0 := (cisZeroG_iff b).mp hcz
    have hval : (cgcdWf a b).1 = cnorm a := by rw [cgcdWf.eq_def, if_pos hcz]
    rw [hval]
    simp only [denote]
    exact ⟨dvd_refl _, by rw [hb0]; exact dvd_zero _⟩
  | case2 a b =>
    -- recursing branch: `(cgcdWf a b).1 = (cgcdWf b r).1 = g`, IH `g ∣ b ∧ g ∣ r`, Euclid `a = q·b + r`
    rename_i hcz rr hdec g s t hgst ih
    have hbne : cnorm b ≠ [] := by
      intro h; rw [cisZero] at hcz; simp [h] at hcz
    have hgfst : (cgcdWf a b).1 = g := by
      rw [cgcdWf.eq_def, if_neg hcz, if_pos hdec]
      show (let (g, s, t) := cgcdWf b (cmodWf a b); (g, t, csub s (cmul t (cdivWf a b)))).1 = g
      rw [show cgcdWf b (cmodWf a b) = (g, s, t) from hgst]
    rw [show cgcdWf b (cmodWf a b) = (g, s, t) from hgst] at ih
    simp only at ih
    obtain ⟨hgb, hgr⟩ := ih
    have heuclid : toPoly a = toPoly (cdivWf a b) * toPoly b + toPoly (cmodWf a b) :=
      toPolyG_cmodWf a b hbne
    rw [hgfst]
    refine ⟨?_, hgb⟩
    rw [heuclid]
    exact dvd_add (hgb.mul_left _) hgr
  | case3 a b =>
    -- unreachable over a genuine field (`cmodWf_length_lt`)
    rename_i hcz rr hdec
    have hbne : cnorm b ≠ [] := by
      intro h; rw [cisZero] at hcz; simp [h] at hcz
    exact absurd (cmodWf_length_lt a b hbne) hdec

/-! ### Exact division through `toPoly`

When a polynomial divides another through the semantic bridge `toPoly`, Euclidean division has zero
remainder. -/

/-- The Euclidean remainder vanishes when the divisor divides the dividend (through `toPoly`). -/
theorem toPolyG_cmodWf_eq_zero_of_dvd (p q : DensePoly α) (hq0 : cnorm q ≠ [])
    (hdvd : toPoly q ∣ toPoly p) :
    toPoly (cmodWf p q) = 0 := by
  have hid : toPoly p = toPoly (cdivWf p q) * toPoly q + toPoly (cmodWf p q) :=
    toPolyG_cmodWf p q hq0
  have hdvdrem : toPoly q ∣ toPoly (cmodWf p q) := by
    have : toPoly (cmodWf p q)
        = toPoly p - toPoly (cdivWf p q) * toPoly q := by
      rw [hid]; ring
    rw [this]
    exact dvd_sub hdvd (Dvd.intro_left _ rfl)
  have hlen : (cnorm (cmodWf p q) : List α).length < (cnorm q : List α).length :=
    cmodWf_length_lt p q hq0
  by_contra hne
  have hdeg : (toPoly q).natDegree ≤ (toPoly (cmodWf p q)).natDegree :=
    Polynomial.natDegree_le_of_dvd hdvdrem hne
  have hrn : cnorm (cmodWf p q) ≠ [] := fun h => hne ((cnormG_eq_nil_iff _).mp h)
  rw [length_cnormG_of_ne _ hrn, length_cnormG_of_ne q hq0] at hlen
  omega

/-- Exact division through `toPoly`: if `toPoly q ∣ toPoly p`, the Euclidean quotient times the
divisor recovers the dividend. -/
theorem toPolyG_cdivWf_exact (p q : DensePoly α) (hq0 : cnorm q ≠ [])
    (hdvd : toPoly q ∣ toPoly p) :
    toPoly (cdivWf p q) * toPoly q = toPoly p := by
  have hid : toPoly p = toPoly (cdivWf p q) * toPoly q + toPoly (cmodWf p q) :=
    toPolyG_cmodWf p q hq0
  have hrem0 : toPoly (cmodWf p q) = 0 :=
    toPolyG_cmodWf_eq_zero_of_dvd p q hq0 hdvd
  rw [hid, hrem0, add_zero]

/-- `u·v^i = d` where `u = cdivWf d (v^i)`, given `v^i ∣ d` and `v ≠ 0`. -/
theorem toPolyG_cdivWf_pow_mul (d v : DensePoly α) (i : ℕ) (hv : toPoly v ≠ 0)
    (hdvd : toPoly v ^ i ∣ toPoly d) :
    toPoly (cdivWf d (cpow v i)) * toPoly v ^ i = toPoly d := by
  have hcn : cnorm (cpow v i) ≠ [] := by
    intro h
    have hz : toPoly (cpow v i) = 0 := (cisZeroG_iff _).mp (by simp [cisZero, h])
    simp only [denote] at hz
    exact pow_ne_zero i hv hz
  have hd2 : toPoly (cpow v i) ∣ toPoly d := by
    simp only [denote]
    exact hdvd
  have h := toPolyG_cdivWf_exact d (cpow v i) hcn hd2
  simp only [denote] at h
  exact h

/-! ### The monic gcd divides both inputs (through `toPoly`) -/

/-- The monic gcd divides both inputs (through `toPoly`). -/
theorem toPolyG_cgcdMonicWf_dvd (p q : DensePoly α) :
    toPoly (cgcdMonicWf p q) ∣ toPoly p ∧ toPoly (cgcdMonicWf p q) ∣ toPoly q := by
  obtain ⟨hp, hq⟩ := toPolyG_cgcdWf_dvd p q
  have hassoc : Associated (toPoly (cgcdMonicWf p q)) (toPoly (cgcdWf p q).1) := by
    rw [cgcdMonicWf]
    exact associated_toPolyG_cmonicG _
  exact ⟨hassoc.dvd.trans hp, hassoc.dvd.trans hq⟩

end DensePoly

open DensePoly

/-- Abstract correctness of the generic monic gcd `DensePoly.cgcdMonicWf`: over the genuine field
`K = CFieldSpec.K α`, `toPoly (DensePoly.cgcdMonicWf p q)` is associated to
`gcd (toPoly p) (toPoly q)` in `K[X]`. -/
theorem associated_toPolyG_cgcdMonicWf {α : Type*} [CField α] [CFieldSpec α] (p q : DensePoly α) :
    Associated (toPoly (DensePoly.cgcdMonicWf p q)) (gcd (toPoly p) (toPoly q)) := by
  obtain ⟨hdvd_p, hdvd_q⟩ := DensePoly.toPolyG_cgcdWf_dvd p q
  have hassoc : Associated (toPoly (DensePoly.cgcdMonicWf p q)) (toPoly (DensePoly.cgcdWf p q).1) := by
    rw [DensePoly.cgcdMonicWf]
    exact associated_toPolyG_cmonicG _
  refine hassoc.trans ?_
  apply associated_of_dvd_dvd
  · exact dvd_gcd hdvd_p hdvd_q
  · exact DensePoly.toPolyG_dvd_cgcdWf p q (gcd_dvd_left _ _) (gcd_dvd_right _ _)

/-- Dense polynomials select the well-founded Euclidean implementation. -/
instance instCPolyEuclideanDense : CPolyEuclidean DensePoly where
  divmod := DensePoly.cdivmodWf
  gcdExt := DensePoly.cgcdWf

/-- Dense polynomials default to the representation-generic Yun kernel over well-founded Euclidean operations. -/
instance (priority := low) instCPolySquarefreeDense {α : Type*} [CField α]
    [CPolyGcd DensePoly α] :
    CPolySquarefree DensePoly α where
  compute := CPolySquarefree.default

namespace CPoly

/-- The default dense Yun selection runs the generic kernel over the dense Euclidean engine. -/
@[simp] theorem squarefreeYun_dense_default_eq {α : Type*} [CField α] (p : DensePoly α) :
    squarefreeYun p = CPolySquarefree.default p := rfl

end CPoly

namespace CPolyEuclidean

/-- Dense Euclidean division selects `DensePoly.cdivmodWf`. -/
@[simp] theorem divmod_dense_eq {α : Type*} [CField α] (p q : DensePoly α) :
    CPolyEuclidean.divmod p q = DensePoly.cdivmodWf p q := rfl

/-- Dense quotient selection is `DensePoly.cdivWf`. -/
@[simp] theorem div_dense_eq {α : Type*} [CField α] (p q : DensePoly α) :
    CPolyEuclidean.div p q = DensePoly.cdivWf p q := rfl

/-- Dense remainder selection is `DensePoly.cmodWf`. -/
@[simp] theorem mod_dense_eq {α : Type*} [CField α] (p q : DensePoly α) :
    CPolyEuclidean.mod p q = DensePoly.cmodWf p q := rfl

/-- Dense extended gcd selects `DensePoly.cgcdWf`. -/
@[simp] theorem gcdExt_dense_eq {α : Type*} [CField α] (p q : DensePoly α) :
    CPolyEuclidean.gcdExt p q = DensePoly.cgcdWf p q := rfl

end CPolyEuclidean

/-- The dense well-founded Euclidean implementation satisfies the abstract laws. -/
instance instLawfulCPolyEuclideanDense : LawfulCPolyEuclidean DensePoly where
  divmod_spec := by
    intro α _ _ p q hq
    rw [toPoly_list_eq] at hq
    have hqnorm : DensePoly.cnorm q ≠ [] := fun h =>
      hq ((DensePoly.cnormG_eq_nil_iff q).mp h)
    simpa only [CPolyEuclidean.div, CPolyEuclidean.mod, CPolyEuclidean.divmod_dense_eq,
      toPoly_list_eq] using DensePoly.toPolyG_cdivmodWf p q hqnorm
  mod_degree_lt := by
    intro α _ _ p q hq
    rw [toPoly_list_eq] at hq ⊢
    have hqnorm : DensePoly.cnorm q ≠ [] := fun h =>
      hq ((DensePoly.cnormG_eq_nil_iff q).mp h)
    simpa only [CPolyEuclidean.mod_dense_eq, toPoly_list_eq] using
      DensePoly.toPolyG_degree_lt_of_length_lt (DensePoly.cmodWf p q) q hqnorm
        (DensePoly.cmodWf_length_lt p q hqnorm)
  div_exact := by
    intro α _ _ p q hq hdvd
    simp only [toPoly_list_eq] at hq hdvd
    have hqnorm : DensePoly.cnorm q ≠ [] := fun h =>
      hq ((DensePoly.cnormG_eq_nil_iff q).mp h)
    simpa only [CPolyEuclidean.div_dense_eq, toPoly_list_eq, mul_comm] using
      (DensePoly.toPolyG_cdivWf_exact p q hqnorm hdvd).symm
  gcdExt_bezout := by
    intro α _ _ p q
    simpa only [CPolyEuclidean.gcdExt_dense_eq, toPoly_list_eq] using
      DensePoly.toPolyG_cgcdWf p q
  gcdExt_dvd := by
    intro α _ _ p q
    simpa only [CPolyEuclidean.gcdExt_dense_eq, toPoly_list_eq] using
      DensePoly.toPolyG_cgcdWf_dvd p q

namespace DensePoly

/-- Selected dense quotient and remainder satisfy the Euclidean identity. -/
theorem toPolyG_divmod {α : Type*} [CField α] [CFieldSpec α] (p q : DensePoly α)
    (hq : cnorm q ≠ []) :
    toPoly p = toPoly (CPolyEuclidean.divmod p q).1 * toPoly q +
      toPoly (CPolyEuclidean.divmod p q).2 := by
  have hq' : CPoly.toPoly q ≠ 0 := fun h =>
    hq ((cnormG_eq_nil_iff q).mpr (by simpa only [toPoly_list_eq] using h))
  simpa only [CPolyEuclidean.div, CPolyEuclidean.mod, toPoly_list_eq] using
    LawfulCPolyEuclidean.divmod_spec (P := DensePoly) p q hq'

/-- Selected exact division reconstructs a dense dividend through the dense denotation. -/
theorem toPolyG_div_exact {α : Type*} [CField α] [CFieldSpec α] (p q : DensePoly α)
    (hq : cnorm q ≠ []) (hdvd : toPoly q ∣ toPoly p) :
    toPoly (CPolyEuclidean.div p q) * toPoly q = toPoly p := by
  have hq' : CPoly.toPoly q ≠ 0 := fun h =>
    hq ((cnormG_eq_nil_iff q).mpr (by simpa only [toPoly_list_eq] using h))
  have hdvd' : CPoly.toPoly q ∣ CPoly.toPoly p := by
    simpa only [toPoly_list_eq] using hdvd
  have hexact := LawfulCPolyEuclidean.div_exact (P := DensePoly) p q hq' hdvd'
  simpa only [toPoly_list_eq, mul_comm] using hexact.symm

end DensePoly

end DeepWiki.SymbolicIntegration
