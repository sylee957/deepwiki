import DeepWiki.SymbolicIntegration.ComputableWellFounded
import DeepWiki.SymbolicIntegration.ComputableResultantGeneric
import DeepWiki.SymbolicIntegration.ComputableGcdCorrect

/-! # Fuel-free (well-founded) generic resultant and concrete primitive-PRS gcd

This continues the fuel-free conversion of `ComputableWellFounded` to the next two leaf ops:

* **`cresultantWf`** (`[CField α]`-only) — the fuel-free companion of the generic Euclidean-PRS
  resultant `cresultantG` (`ComputableLogPartTower`). Its recursion has *two* shapes (a **swap**
  `(p,q)→(q,p)` and a **reduce** `(p,q)→(q, cmodWf p q)`), so the well-founded measure is the
  composite `cresultantMeasure p q = 2·(len p + len q) + len q` (the swap leaves `len p + len q`
  fixed, hence the `+ len q` tie-breaker). Each recursive call is taken only under its structural
  guard, so `decreasing_by` is `assumption` and the def stays `[CField α]`-only / `native_decide`-able
  over `QFunNZ`. The Sylvester-resultant identity `toPolyG_cresultantWf` is transported from
  `toPolyG_cresultantG` through the bridge **unconditionally**.

* **`primPRSgcdWf`** (concrete `BPoly`) — the fuel-free companion of the primitive polynomial-remainder
  sequence `primPRSgcd` (`ComputableSplitFactorFast`), recursing on the second argument's `t`-length,
  strictly dropped each step by `primPRSstep_length_lt`. The associated-to-`gcd` correctness is
  transported (still gated on `PrimPRSRegular`, the same gate the fuel'd version carries) through the
  bridge `primPRSgcdWf_eq_of_fuel`.

As in `ComputableWellFounded`, the fuel bounds live only inside the bridge proofs; the runtime WF ops
carry no fuel. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### Target A — the fuel-free generic resultant `cresultantWf`

`cresultantWf p q = res(p, q) ∈ α`, the fuel-free companion of `cresultantG`
(`ComputableLogPartTower`). The recursion has *two* shapes: a **swap** `(p, q) → (q, p)` taken when
`len p < len q` (q non-constant), and a **reduce** `(p, q) → (q, cmodWf p q)` taken when
`len q ≤ len p`. Neither single-argument length strictly drops on the swap, so the well-founded measure
is `cresultantMeasure p q = 2·(len p + len q) + len q`: the swap drops it by `len p − len q < 0` (sic),
the reduce by `2·(len r − len p) + (len r − len q) < 0`. Each recursive call is taken only under its
structural guard, so the `decreasing_by` is `assumption` and the def stays `[CField α]`-only. -/

/-- **Well-founded measure for `cresultantWf`** `cresultantMeasure p q = 2·(len p + len q) + len q`,
where `len` is the normalized-list length. Chosen so *both* the swap `(p,q)→(q,p)` (drops by
`len p − len q`) and the reduce `(p,q)→(q, cmodWf p q)` (drops by `2(len r − len p) + (len r − len q)`)
strictly decrease it; the swap alone leaves `len p + len q` fixed, hence the `+ len q` tie-breaker. -/
def cresultantMeasure (p q : CPolyG α) : ℕ :=
  2 * ((cnormG p : List α).length + (cnormG q : List α).length) + (cnormG q : List α).length

/-- **Fuel-free generic univariate resultant** `cresultantWf p q = res(p, q) ∈ α`, `[CField α]`-only:
the Euclidean-PRS resultant identity with no fuel at runtime. Base cases match `cresultantG`'s
`fuel+1` branch (`q = 0`: `1` if `p` constant else `0`; `q` a nonzero constant `c`: `cⁱ` with
`i = deg p`). The two recursive branches — the **swap** `(p,q)→(q,p)` (when `len p < len q`) and the
**reduce** `(p,q)→(q, cmodWf p q)` (when `len q ≤ len p`) — are each taken only under the structural
guard `cresultantMeasure (next) < cresultantMeasure p q`, so `decreasing_by` is `assumption` and the
def is `native_decide`-able over noncomputable-`CFieldSpec` carriers (`QFunNZ`). Over a genuine field
the guards never fail (`cresultantMeasure_swap_lt`/`cresultantMeasure_reduce_lt`), so `cresultantWf`
agrees with `cresultantG` (`cresultantWf_eq`). -/
def cresultantWf (p q : CPolyG α) : α :=
  let pn := cnormG p
  let qn := cnormG q
  if cisZeroG qn then
    if (pn : List α).length ≤ 1 then CField.one else CField.zero
  else if (qn : List α).length ≤ 1 then
    cfpow (cleadG qn) (cdegG pn)
  else if (pn : List α).length < (qn : List α).length then
    let s := cfpow (CField.neg CField.one) (cdegG pn * cdegG qn)
    if cresultantMeasure q p < cresultantMeasure p q then
      CField.mul s (cresultantWf q p)
    else s   -- unreachable over a genuine field (`cresultantMeasure_swap_lt`)
  else
    let r := cnormG (cmodWf p q)
    let sign := cfpow (CField.neg CField.one) (cdegG pn * cdegG qn)
    let lcpow := cfpow (cleadG qn) (cdegG pn - cdegG r)
    if cresultantMeasure q r < cresultantMeasure p q then
      CField.mul (CField.mul sign lcpow) (cresultantWf q r)
    else CField.mul sign lcpow   -- unreachable over a genuine field (`cresultantMeasure_reduce_lt`)
termination_by cresultantMeasure p q
decreasing_by · assumption
              · assumption

/-! ### Bridge of `cresultantWf` to the fuel'd `cresultantG`, and transported correctness

Over a genuine field (`[CFieldSpec α]`) the remainder always strictly shortens (`cmodWf_length_lt`),
so `cresultantWf`'s structural guards never fail and it coincides with `cresultantG fuel` whenever
`fuel` covers the descent. The bound lives only in the bridge proof; the runtime `cresultantWf` carries
no fuel. The Sylvester-resultant identity is then transported from `toPolyG_cresultantG`. -/

variable [CFieldSpec α]

omit [CFieldSpec α] in
/-- **The swap guard never fails**: when `len p < len q`, `cresultantMeasure q p < cresultantMeasure p q`
(it drops by `len q − len p ≥ 1`). Pure measure arithmetic — discharges the swap branch's structural
guard, so the swap is always taken. -/
theorem cresultantMeasure_swap_lt (p q : CPolyG α)
    (hpq : (cnormG p : List α).length < (cnormG q : List α).length) :
    cresultantMeasure q p < cresultantMeasure p q := by
  simp only [cresultantMeasure]
  omega

/-- **The reduce guard never fails** over `[CFieldSpec α]`: for a non-constant divisor `q` with
`len q ≤ len p`, the remainder `r = cnormG (cmodWf p q)` has `len r < len q`, so
`cresultantMeasure q r < cresultantMeasure p q`. Discharges the reduce branch's structural guard. -/
theorem cresultantMeasure_reduce_lt (p q : CPolyG α) (hq : cnormG q ≠ [])
    (hpq : ¬ (cnormG p : List α).length < (cnormG q : List α).length) :
    cresultantMeasure q (cnormG (cmodWf p q)) < cresultantMeasure p q := by
  have hr : (cnormG (cmodWf p q) : List α).length < (cnormG q : List α).length :=
    cmodWf_length_lt p q hq
  simp only [cresultantMeasure, cnormG_idem]
  omega

/-- **Bridge, the no-swap case** `len q ≤ len p`: `cresultantWf p q = cresultantG fuel p q` for
`(cnormG p).length + (cnormG q).length + 1 ≤ fuel`. The top step is never a swap, so the body's
recursion (reduce only) descends with strictly smaller `len q`, keeping `len(new q) ≤ len(new p)`. The
generic analogue of `toPolyG_cresultantG_of_ge`'s fuel accounting; the `+1` margin (one cheaper than the
general `+2`) is what funds the descent without an extra swap. By strong induction on `fuel`. -/
theorem cresultantWf_eq_of_ge : ∀ (fuel : ℕ) (p q : CPolyG α),
    (cnormG q : List α).length ≤ (cnormG p : List α).length →
    (cnormG p : List α).length + (cnormG q : List α).length + 1 ≤ fuel →
      cresultantWf p q = cresultantG fuel p q := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ihf =>
    intro p q hge hfuel
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [cresultantWf.eq_def, cresultantG]
      by_cases h0 : cisZeroG (cnormG q) = true
      · -- q = 0: both branch on `len p ≤ 1`
        simp only [h0, if_true]
      · have hcz : cisZeroG (cnormG q) = false := by simpa using h0
        have hq : cnormG q ≠ [] := fun h => by simp [cisZeroG, h] at hcz
        simp only [hcz, Bool.false_eq_true, if_false]
        by_cases hqc : (cnormG q : List α).length ≤ 1
        · -- q a nonzero constant: res(p, c) = c^(deg p)
          simp only [if_pos hqc, cleadG_cnormG, cdegG_cnormG]
        · -- non-constant divisor, `len q ≤ len p`: the reduce branch (no swap)
          have hpq : ¬ (cnormG p : List α).length < (cnormG q : List α).length := by omega
          simp only [if_neg hqc, if_neg hpq]
          have hmod : cmodWf p q = cmodG (fuel + 1) p q :=
            cmodWf_eq_cmodG_succ fuel p q (by omega)
          have hdec := cresultantMeasure_reduce_lt p q hq hpq
          rw [hmod] at hdec
          have hrlt : (cnormG (cmodG (fuel + 1) p q) : List α).length
              < (cnormG q : List α).length := by rw [← hmod]; exact cmodWf_length_lt p q hq
          rw [hmod]
          simp only [if_pos hdec, cleadG_cnormG, cdegG_cnormG, cmodG_cnormG_both]
          -- recurse on `(q, r)` with `len r < len q ≤ len(new p) = len q`
          have ihstep := ihf fuel (by omega) q (cnormG (cmodG (fuel + 1) p q))
            (by rw [cnormG_idem]; omega) (by rw [cnormG_idem]; omega)
          rw [cresultantG_cnormG, ihstep]
          have hrec : cresultantG fuel q (cnormG (cmodG (fuel + 1) p q))
              = cresultantG fuel q (cmodG (fuel + 1) p q) := by
            rw [← cresultantG_cnormG fuel q (cnormG (cmodG (fuel + 1) p q)), cnormG_idem,
              cresultantG_cnormG]
          rw [hrec]

/-- **Bridge — `cresultantWf` equals `cresultantG` at any sufficient fuel.** With
`(cnormG p).length + (cnormG q).length + 2 ≤ fuel`, `cresultantWf p q = cresultantG fuel p q`. The
fuel bound appears only here; `cresultantWf` carries none. The `len q ≤ len p` case is
`cresultantWf_eq_of_ge`; the `len p < len q` case swaps once (consuming the extra `+1` of fuel) into it,
mirroring `toPolyG_cresultantG`'s top swap into `toPolyG_cresultantG_of_ge`. -/
theorem cresultantWf_eq_of_fuel (fuel : ℕ) (p q : CPolyG α)
    (hfuel : (cnormG p : List α).length + (cnormG q : List α).length + 2 ≤ fuel) :
    cresultantWf p q = cresultantG fuel p q := by
  by_cases hge : (cnormG q : List α).length ≤ (cnormG p : List α).length
  · exact cresultantWf_eq_of_ge fuel p q hge (by omega)
  · have hpq : (cnormG p : List α).length < (cnormG q : List α).length := by omega
    have hq : cnormG q ≠ [] := by intro h; rw [h, List.length_nil] at hpq; omega
    have hcz : cisZeroG (cnormG q) = false := by simpa [cisZeroG] using hq
    obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [cresultantWf.eq_def, cresultantG]
    by_cases hqc : (cnormG q : List α).length ≤ 1
    · -- q a nonzero constant, p = 0: no recursion, both compute `c^(deg p)`
      simp only [hcz, Bool.false_eq_true, if_false, if_pos hqc, cleadG_cnormG,
        cdegG_cnormG]
    · -- swap once into the no-swap bridge
      have hdec := cresultantMeasure_swap_lt p q hpq
      simp only [hcz, Bool.false_eq_true, if_false, if_neg hqc, if_pos hpq,
        if_pos hdec, cdegG_cnormG]
      rw [cresultantWf_eq_of_ge fuel' q p (le_of_lt hpq) (by omega),
        ← cresultantG_cnormG fuel' q p]

/-- **Bridge at the self-sufficient fuel**: `cresultantWf p q = cresultantG (max+2) p q` with
`max = (cnormG p).length + (cnormG q).length`. -/
theorem cresultantWf_eq (p q : CPolyG α) :
    cresultantWf p q
      = cresultantG ((cnormG p : List α).length + (cnormG q : List α).length + 2) p q :=
  cresultantWf_eq_of_fuel _ p q le_rfl

/-- **Sylvester-resultant identity through `toPolyG`** for the fuel-free `cresultantWf` (no fuel
hypothesis): `toK (cresultantWf p q) = Polynomial.resultant (toPolyG p) (toPolyG q) (deg p) (deg q)`.
Transported from `toPolyG_cresultantG` through the self-sufficient-fuel bridge, **unconditionally**. -/
theorem toPolyG_cresultantWf (p q : CPolyG α) :
    CFieldSpec.toK (cresultantWf p q)
      = Polynomial.resultant (toPolyG p) (toPolyG q) (cdegG p) (cdegG q) := by
  rw [cresultantWf_eq]; exact toPolyG_cresultantG _ p q (by omega)

/-- Restatement: the fuel-free generic resultant `cresultantWf` is the honest Sylvester resultant under
the Horner bridge `toPolyG`, **with no fuel hypothesis**. -/
example (p q : CPolyG α) :
    CFieldSpec.toK (cresultantWf p q)
      = Polynomial.resultant (toPolyG p) (toPolyG q) (cdegG p) (cdegG q) :=
  toPolyG_cresultantWf p q

end CPolyG

-- The fuel-free resultant headline carries only the standard axioms (no `native` axiom): the
-- `native_decide` smoke tests below carry `Lean.ofReduceBool` separately.
#print axioms CPolyG.toPolyG_cresultantWf

/-! ### `native_decide` smoke tests for `cresultantWf` -/

namespace CPolyG

/-- `cresultantWf` over `ℚ`: `res(x² − 1, x − 1) = 0` (they share the root `x = 1`). -/
example : CPolyG.cresultantWf [(-1 : ℚ), 0, 1] [(-1 : ℚ), 1] = 0 := by native_decide

/-- `cresultantWf` over `ℚ`: `res(x² + 1, x) = 1` (no common root). -/
example : CPolyG.cresultantWf [(1 : ℚ), 0, 1] [(0 : ℚ), 1] = 1 := by native_decide

/-- `cresultantWf` over the ℚ(x) tower `QFunNZ`: `res(t² − 1, t − 1)` is zero (`CField.isZero`) — the
whole fuel-free PRS resultant executes in native code over `QFunNZ`. -/
example :
    CField.isZero (CPolyG.cresultantWf [(CField.neg CField.one : QFunNZ), CField.zero, CField.one]
      [CField.neg CField.one, CField.one]) = true := by native_decide

end CPolyG

/-! ### Target B — the fuel-free concrete primitive-PRS gcd `primPRSgcdWf`

`primPRSgcdWf P Q ∈ BPoly`, the fuel-free companion of the primitive polynomial-remainder sequence
`primPRSgcd` (`ComputableSplitFactorFast`). Unlike `cresultantWf`/`cgcdWf`, `BPoly = List CPoly` is a
*concrete* (fully computable) carrier — the `[CField α]`-only concern does not apply — but the
runtime-guard structural-WF technique still gives the cleanest `decreasing_by`. The recursion runs only
on the second argument `Q`, whose normalized `t`-length `(bnorm Q).length` strictly drops each step by
`primPRSstep_length_lt` (pseudo-remainder degree drop ∘ primitive-part non-raising). The
associated-to-`gcd` correctness `associated_toPolyB_primPRSgcdWf` is transported from
`associated_toPolyB_primPRSgcd` through the bridge `primPRSgcdWf_eq_of_fuel`, still gated on
`PrimPRSRegular` (the same gate the fuel'd version carries). -/

open Compute Classical

namespace CPolyG

/-- **`bprimitivePartX` is `bnorm`-invariant in its argument** `bprimitivePartX fuel (bnorm p) =
bprimitivePartX fuel p` (it normalizes its argument internally, `bnorm_idem`). Reconciles the fuel'd
`primPRSgcd`'s un-normalized base `bprimitivePartX 30 P` with the WF def's normalized one. -/
theorem bprimitivePartX_bnorm (fuel : ℕ) (p : Compute.BPoly) :
    Compute.bprimitivePartX fuel (Compute.bnorm p) = Compute.bprimitivePartX fuel p := by
  rw [bprimitivePartX, bprimitivePartX, bnorm_idem]

/-- **Fuel-free primitive polynomial-remainder-sequence gcd** `primPRSgcdWf P Q ∈ BPoly`: the gcd of
`P, Q` in `t` over ℚ[x] up to a ℚ[x]-content factor, with **no fuel at runtime**. Mirrors `primPRSgcd`'s
body — normalize `P, Q`; if `Q = 0` return the primitive part of `P`, else take the next PRS node
`r = bprimitivePartX 30 (bpsremainder 60 P Q)` and recurse on `(Q, r)`. The recursion is taken only under
the structural guard `(bnorm r).length < (bnorm Q).length`, so `decreasing_by` is `assumption`. Over a
real run the guard never fails (`primPRSstep_length_lt`, needs `(bnorm P).length ≤ 60`), so `primPRSgcdWf`
agrees with `primPRSgcd` (`primPRSgcdWf_eq_of_fuel`). -/
def primPRSgcdWf (P Q : Compute.BPoly) : Compute.BPoly :=
  let P := Compute.bnorm P
  let Q := Compute.bnorm Q
  if Compute.bisZero Q then Compute.bprimitivePartX 30 P
  else
    let r := Compute.bprimitivePartX 30 (Compute.bpsremainder 60 P Q)
    if (Compute.bnorm r).length < (Compute.bnorm Q).length then
      primPRSgcdWf Q r
    else Compute.bprimitivePartX 30 P   -- unreachable on a real run (`primPRSstep_length_lt`)
termination_by (Compute.bnorm Q).length
decreasing_by exact Nat.lt_of_lt_of_le ‹_ < _› (le_of_eq (by rw [Compute.bnorm_idem]))

/-! ### Bridge of `primPRSgcdWf` to the fuel'd `primPRSgcd`, and transported correctness

Over a real PRS run the next node always has strictly smaller `t`-degree (`primPRSstep_length_lt`, under
the transparent per-node bound `(bnorm P).length ≤ 60`), so `primPRSgcdWf`'s structural guard never
fails and it coincides with `primPRSgcd fuel` whenever `fuel` covers the descent. The bound lives only
in the bridge proof; the runtime `primPRSgcdWf` carries no fuel. The associated-to-`gcd` correctness is
then transported from `associated_toPolyB_primPRSgcd`, still gated on `PrimPRSRegular`. -/

/-- **Bridge — `primPRSgcdWf` equals `primPRSgcd` at any sufficient fuel.** With the divisor's
normalized `t`-length bounded by `fuel` (`(bnorm Q).length ≤ fuel`), `deg Q ≤ deg P`, and the per-node
pseudo-remainder bound `(bnorm P).length ≤ 60` preserved along the descent, `primPRSgcdWf P Q =
primPRSgcd fuel P Q`. The fuel bound lives only here; `primPRSgcdWf` carries none. By induction on
`fuel`, mirroring `primPRSInputs_of_nodeRegular`: at each step `primPRSstep_length_lt` discharges the
guard and the three invariants (`≤ fuel`, `deg Q ≤ deg P`, `≤ 60`) are preserved (divisors shrink). -/
theorem primPRSgcdWf_eq_of_fuel : ∀ (fuel : ℕ) (P Q : Compute.BPoly),
    (Compute.bnorm Q).length ≤ fuel →
    (Compute.bnorm Q).length ≤ (Compute.bnorm P).length →
    (Compute.bnorm P).length ≤ 60 →
      primPRSgcdWf P Q = CPolyG.primPRSgcd fuel P Q := by
  intro fuel
  induction fuel with
  | zero =>
    intro P Q hfuel _ _
    have hQnil : Compute.bnorm Q = [] := List.length_eq_zero_iff.mp (by omega)
    have hQz : Compute.bisZero (Compute.bnorm Q) = true := by
      rw [bisZero, bnorm_idem, beq_iff_eq, hQnil]
    rw [primPRSgcdWf.eq_def, primPRSgcd]
    simp only [hQz, if_true, bprimitivePartX_bnorm]
  | succ fuel ih =>
    intro P Q hfuel hdeg hP60
    rw [primPRSgcdWf.eq_def, primPRSgcd]
    by_cases hQz : Compute.bisZero (Compute.bnorm Q) = true
    · -- terminal: `Q = 0` (both sides `bprimitivePartX 30 (bnorm P)`)
      simp only [hQz, if_true]
    · -- recursive step
      -- the next PRS node `r` strictly shortens `(bnorm Q).length`
      have hstep : (Compute.bnorm
            (Compute.bprimitivePartX 30 (Compute.bpsremainder 60 (Compute.bnorm P)
              (Compute.bnorm Q)))).length < (Compute.bnorm Q).length :=
        primPRSstep_length_lt P Q hQz (by simpa [bnorm_idem] using hP60)
      have hstep' : (Compute.bnorm
            (Compute.bprimitivePartX 30 (Compute.bpsremainder 60 (Compute.bnorm P)
              (Compute.bnorm Q)))).length < (Compute.bnorm (Compute.bnorm Q)).length := by
        rwa [bnorm_idem]
      simp only [hQz, Bool.false_eq_true, if_false, if_pos hstep']
      -- recurse on `(bnorm Q, r)`: `len(new Q) = len r < len Q ≤ fuel`, `len(new P) = len Q ≤ 60`
      have ihstep := ih (Compute.bnorm Q)
        (Compute.bprimitivePartX 30 (Compute.bpsremainder 60 (Compute.bnorm P) (Compute.bnorm Q)))
        (by omega) (by rw [bnorm_idem]; omega) (by rw [bnorm_idem]; omega)
      rw [ihstep]

/-- **Bridge at the self-sufficient fuel**: `primPRSgcdWf P Q = primPRSgcd (bnorm Q).length P Q`, given
the per-node bounds `deg Q ≤ deg P` and `(bnorm P).length ≤ 60` a real run meets. -/
theorem primPRSgcdWf_eq (P Q : Compute.BPoly)
    (hdeg : (Compute.bnorm Q).length ≤ (Compute.bnorm P).length)
    (hP60 : (Compute.bnorm P).length ≤ 60) :
    primPRSgcdWf P Q = CPolyG.primPRSgcd (Compute.bnorm Q).length P Q :=
  primPRSgcdWf_eq_of_fuel _ P Q le_rfl hdeg hP60

/-- **The primitive-PRS gcd invariant for the fuel-free `primPRSgcdWf`** (the transported headline): for a
regular run (`PrimPRSRegular fuel P Q` at any covering fuel, with the per-node bounds `deg Q ≤ deg P`,
`(bnorm P).length ≤ 60`), `primPRSgcdWf P Q` is `Associated` over ℚ(x) to `gcd (toPolyB P) (toPolyB Q)`.
The `PrimPRSRegular` gate is the *same* gate the fuel'd `associated_toPolyB_primPRSgcd` carries; the WF
bridge only removes the explicit `fuel` from the runtime, not the regularity hypothesis. -/
theorem associated_toPolyB_primPRSgcdWf (fuel : ℕ) (P Q : Compute.BPoly)
    (hdeg : (Compute.bnorm Q).length ≤ (Compute.bnorm P).length)
    (hP60 : (Compute.bnorm P).length ≤ 60)
    (hfuel : (Compute.bnorm Q).length ≤ fuel)
    (hreg : PrimPRSRegular fuel P Q) :
    Associated (toPolyB (primPRSgcdWf P Q)) (gcd (toPolyB P) (toPolyB Q)) := by
  rw [primPRSgcdWf_eq_of_fuel fuel P Q hfuel hdeg hP60]
  exact associated_toPolyB_primPRSgcd fuel P Q hreg

/-- **`primPRSgcdWf` correct from algorithmic inputs** (the gate discharged): under `PrimPRSInputs`
(the genuine algorithmic preconditions, no leftover content-gcd assumption) at a covering fuel with the
per-node bounds, `primPRSgcdWf P Q` is `Associated` over ℚ(x) to `gcd (toPolyB P) (toPolyB Q)`. The
fuel-free analogue of `associated_toPolyB_primPRSgcd_of_inputs`. -/
theorem associated_toPolyB_primPRSgcdWf_of_inputs (fuel : ℕ) (P Q : Compute.BPoly)
    (hdeg : (Compute.bnorm Q).length ≤ (Compute.bnorm P).length)
    (hP60 : (Compute.bnorm P).length ≤ 60)
    (hfuel : (Compute.bnorm Q).length ≤ fuel)
    (hin : PrimPRSInputs fuel P Q) :
    Associated (toPolyB (primPRSgcdWf P Q)) (gcd (toPolyB P) (toPolyB Q)) :=
  associated_toPolyB_primPRSgcdWf fuel P Q hdeg hP60 hfuel
    (primPRSRegular_of_inputs fuel P Q hin)

end CPolyG

-- The fuel-free primitive-PRS gcd headline (`PrimPRSRegular`-gated, as the fuel'd version) carries only
-- the standard axioms.
#print axioms CPolyG.associated_toPolyB_primPRSgcdWf

/-! ### `native_decide` smoke tests for `primPRSgcdWf` -/

namespace CPolyG

/-- `primPRSgcdWf` over `BPoly` (ℚ[x][t]): `gcd_t(t² − 1, t − 1)` matches the fuel'd `primPRSgcd`'s result
— the whole fuel-free primitive PRS executes in native code. (`t² − 1` and `t − 1` as `List CPoly`, each
`x`-coefficient a constant `CPoly = List ℚ`.) -/
example :
    CPolyG.primPRSgcdWf [([(-1 : ℚ)] : Compute.CPoly), [], [(1 : ℚ)]] [[(-1 : ℚ)], [(1 : ℚ)]]
      = CPolyG.primPRSgcd 2 [([(-1 : ℚ)] : Compute.CPoly), [], [(1 : ℚ)]] [[(-1 : ℚ)], [(1 : ℚ)]] := by
  native_decide

/-- `primPRSgcdWf` over `BPoly`: `gcd_t(t² − 1, t − 1)` is a nonzero (degree-1) primitive polynomial in
`t` — the fuel-free run terminates and returns a genuine gcd. -/
example :
    (Compute.bnorm (CPolyG.primPRSgcdWf [([(-1 : ℚ)] : Compute.CPoly), [], [(1 : ℚ)]]
      [[(-1 : ℚ)], [(1 : ℚ)]])).length = 2 := by native_decide

end CPolyG

end DeepWiki.SymbolicIntegration
