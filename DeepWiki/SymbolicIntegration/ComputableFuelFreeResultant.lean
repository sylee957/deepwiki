import DeepWiki.SymbolicIntegration.ComputableFuelFreeGcd
import DeepWiki.SymbolicIntegration.ComputableResultantGenericCore

/-! # Fuel-free (well-founded) generic resultant `cresultantWf`

This continues the fuel-free conversion of `ComputableFuelFreeGcd` to the generic resultant leaf op:

* **`cresultantWf`** (`[CField α]`-only) — the fuel-free companion of the generic Euclidean-PRS
  resultant `cresultantG` (`ComputableGenericBezout`). Its recursion has *two* shapes (a **swap**
  `(p,q)→(q,p)` and a **reduce** `(p,q)→(q, cmodWf p q)`), so the well-founded measure is the
  composite `cresultantMeasure p q = 2·(len p + len q) + len q` (the swap leaves `len p + len q`
  fixed, hence the `+ len q` tie-breaker). Each recursive call is taken only under its structural
  guard, so `decreasing_by` is `assumption` and the def stays `[CField α]`-only / `native_decide`-able
  over `QFunNZ`. The Sylvester-resultant identity `toPolyG_cresultantWf` is transported from
  `toPolyG_cresultantG` (`ComputableResultantGenericCore`) through the bridge **unconditionally** —
  this file imports only the engine-only resultant core, so the fuel-free resultant stays free of the
  §5.6 residue / `cgcdFF` layer.

The concrete `BPoly` primitive-PRS gcd `primPRSgcdWf` (§3.5, which *does* need the `cgcdFF` layer) lives
in `ComputablePrimPRSWf`. As in `ComputableFuelFreeGcd`, the fuel bounds live only inside the bridge
proofs; the runtime WF op carries no fuel. -/

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

end DeepWiki.SymbolicIntegration
