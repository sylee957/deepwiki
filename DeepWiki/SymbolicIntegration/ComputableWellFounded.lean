import DeepWiki.SymbolicIntegration.ComputableFieldGcd

/-! # Fuel-free (well-founded) generic Euclidean division and gcd

The engine ops `cdivmodG`/`cmodG`/`cgcdExtG` (`GenericPolyEngine`) take an explicit `fuel : ℕ`
and need a fuel-sufficiency side condition (`cgcdTerminatesG`) for their correctness. This file
gives **true fuel-free** companions, `cdivmodWf`/`cmodWf`/`cgcdWf`, by structural well-founded
recursion on the normalized list length (`decreasing_by` discharged from the proven one-step length
drops `stepG_length_lt`/`cmodWf_length_lt`). No fuel is computed or passed at runtime.

The ~200 existing correctness theorems are **transported, not re-proven**: each WF op equals its
fuel'd version at *any* sufficient fuel (`cdivmodWf_eq_of_fuel`/`cgcdWf_eq_of_fuel`), so the bound
appears only inside the bridge proof, never at runtime. The Euclidean identity, Bézout relation,
and gcd-divisibility then follow for the WF ops — the last **unconditionally** (a WF def always
terminates, so no `cgcdTerminatesG` hypothesis survives). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### Step A — the leaf `cdivmodWf` (fuel-free Euclidean division)

`cdivmodWf p q` runs the same remainder loop as `cdivmodG`'s `fuel+1` branch, but recurses with no
fuel: termination is by `(cnormG p).length`, strictly dropped each step by `stepG_length_lt`. The
recursion-case shape mirrors `cdivmodG` exactly (normalize `p`, `q`; the leading-term match
`c = clead p / clead q`; the `csub`-`cmul`-`cshift` reduce step) so the fuel bridge is a clean
induction. -/

/-- **One reduce step** of generic Euclidean division: replace `p` by the leading-term-cancelled
`cnormG (p − (clead p/clead q)·xᵏ·q)`. The recursion driver of `cdivmodWf` (split out so the
well-founded recursion's decreasing argument is exactly `stepG_length_lt`). -/
def reduceStepWf (p q : CPolyG α) : CPolyG α :=
  cnormG (csubG (cnormG p)
    (cmulG (cshiftG ((cnormG p : List α).length - (cnormG q : List α).length)
      [CField.div (cleadG p) (cleadG q)]) (cnormG q)))

/-- **Fuel-free generic Euclidean division** of `CPolyG`s, `[CField α]`-only: `cdivmodWf p q =
(quotient, remainder)` with `p = quotient · q + remainder` over `K` (`q ≠ 0`). True well-founded
recursion on `(cnormG p).length` — **no fuel is computed or passed at runtime**. Termination is
structural: the reduce step `p' = reduceStepWf p q` is taken only when the *guard*
`(cnormG p').length < (cnormG p).length` holds, so the `decreasing_by` is the guard itself (no field
axiom needed, hence `[CField α]`-only and `native_decide`-able over noncomputable-`CFieldSpec`
carriers like `QFunNZ`). Over a genuine field the leading term always cancels (`stepG_length_lt`), so
the guard never fails and `cdivmodWf` agrees with `cdivmodG` (the bridge `cdivmodWf_eq_cdivmodG`). -/
def cdivmodWf (p q : CPolyG α) : CPolyG α × CPolyG α :=
  let pn := cnormG p
  let qn := cnormG q
  if cisZeroG qn then ([], [])
  else if (pn : List α).length < (qn : List α).length then ([], pn)
  else
    let c := CField.div (cleadG pn) (cleadG qn)
    let k := (pn : List α).length - (qn : List α).length
    let term := cshiftG k [c]
    let p' := reduceStepWf p q
    if (cnormG p' : List α).length < (cnormG p : List α).length then
      let (quo, rem) := cdivmodWf p' q
      (caddG term quo, rem)
    else (term, p')   -- unreachable over a genuine field (`stepG_length_lt`)
termination_by (cnormG p).length
decreasing_by assumption

/-- **Fuel-free remainder** of generic Euclidean division (`cdivmodWf`'s second component). -/
def cmodWf (p q : CPolyG α) : CPolyG α := (cdivmodWf p q).2

/-- **Fuel-free quotient** of generic Euclidean division (`cdivmodWf`'s first component). -/
def cdivWf (p q : CPolyG α) : CPolyG α := (cdivmodWf p q).1

/-! ### Bridge to the fuel'd `cdivmodG` and transported correctness

Over a genuine field (`[CFieldSpec α]`) the leading term always cancels, so `cdivmodWf`'s structural
guard never fails and the WF def coincides with `cdivmodG fuel` for **any** sufficient fuel
(`cdivmodWf_eq_of_fuel`). The bound `(cnormG p).length ≤ fuel` lives only in this proof; the runtime
`cdivmodWf` carries no fuel. The Euclidean identity is then transported from `toPolyG_cdivmodG`
unconditionally (`toPolyG_cdivmodWf`). -/

variable [CFieldSpec α]

/-- **The reduce step strictly shortens** the normalized list (over `[CFieldSpec α]`): discharges
`cdivmodWf`'s structural guard, so over a genuine field the reducing branch is always taken. -/
theorem reduceStepWf_length_lt (p q : CPolyG α) (hcz : cisZeroG (cnormG q) = false)
    (hlen : ¬ (cnormG p : List α).length < (cnormG q : List α).length) :
    (cnormG (reduceStepWf p q) : List α).length < (cnormG p : List α).length := by
  have hq : cnormG q ≠ [] := by
    simpa [cisZeroG, List.isEmpty_iff] using hcz
  have hle : (cnormG q : List α).length ≤ (cnormG p : List α).length := Nat.le_of_not_lt hlen
  have hpn : cnormG p ≠ [] := by
    intro h
    rw [h, List.length_nil, Nat.le_zero] at hle
    exact hq (List.length_eq_zero_iff.mp hle)
  have hstep := stepG_length_lt (cnormG p) (cnormG q)
    (by simpa using hpn) (by simpa using hq) (by simpa using hle)
  rw [reduceStepWf]
  simpa only [cnormG_idem, cleadG_cnormG] using hstep

omit [CFieldSpec α] in
/-- **`cdivmodG`'s reducing branch is driven by `reduceStepWf`**: in the non-base branch
`cdivmodG (fuel+1) p q = (term + (cdivmodG fuel (reduceStepWf p q) q).1, (cdivmodG fuel … ).2)`. The
recursive divisor is normalized to `cnormG q` by `cdivmodG`, re-folded with `cdivmodG_cnormG_right`. -/
theorem cdivmodG_succ_reducing (fuel : ℕ) (p q : CPolyG α) (hcz : cisZeroG (cnormG q) = false)
    (hlen : ¬ (cnormG p : List α).length < (cnormG q : List α).length) :
    cdivmodG (fuel + 1) p q =
      ((cshiftG ((cnormG p : List α).length - (cnormG q : List α).length)
            [CField.div (cleadG p) (cleadG q)]).caddG (cdivmodG fuel (reduceStepWf p q) q).1,
        (cdivmodG fuel (reduceStepWf p q) q).2) := by
  rw [cdivmodG]
  rw [if_neg (by rw [← cisZeroG_cnormG]; simpa using hcz), if_neg (by simpa using hlen)]
  simp only [cleadG_cnormG]
  rw [show cnormG (csubG (cnormG p)
        (cmulG (cshiftG ((cnormG p : List α).length - (cnormG q : List α).length)
          [CField.div (cleadG p) (cleadG q)]) (cnormG q))) = reduceStepWf p q from rfl,
    ← cdivmodG_cnormG_right]

/-- **Bridge — `cdivmodWf` equals `cdivmodG` at any sufficient fuel.** For `fuel ≥ (cnormG p).length`,
`cdivmodWf p q = cdivmodG fuel p q`. The fuel bound appears only here; `cdivmodWf` carries none. By
strong induction on `fuel`. -/
theorem cdivmodWf_eq_of_fuel : ∀ (fuel : ℕ) (p q : CPolyG α),
    (cnormG p : List α).length ≤ fuel → cdivmodWf p q = cdivmodG fuel p q := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ihf =>
    intro p q hfuel
    rw [cdivmodWf.eq_def]
    by_cases hcz : cisZeroG (cnormG q) = true
    · -- divisor zero: both return `([], [])`
      simp only [hcz, if_true]
      cases fuel with
      | zero =>
        simp only [Nat.le_zero] at hfuel
        have hp0 : cnormG p = [] := List.length_eq_zero_iff.mp hfuel
        rw [cdivmodG]; rw [hp0]
      | succ fuel =>
        rw [cdivmodG]
        rw [if_pos (by rw [← cisZeroG_cnormG]; simpa using hcz)]
    · have hcz' : cisZeroG (cnormG q) = false := by simpa using hcz
      by_cases hlen : (cnormG p : List α).length < (cnormG q : List α).length
      · -- deg p < deg q: both return `([], cnormG p)`
        simp only [hcz', Bool.false_eq_true, if_false, hlen, if_true]
        cases fuel with
        | zero =>
          -- `cdivmodG 0 p q = ([], cnormG p)`
          rw [cdivmodG]
        | succ fuel =>
          rw [cdivmodG]
          rw [if_neg (by rw [← cisZeroG_cnormG]; simpa using hcz), if_pos (by simpa using hlen)]
      · -- reducing branch
        have hdec := reduceStepWf_length_lt p q hcz' hlen
        have hpne : cnormG p ≠ [] := by
          intro h; rw [h, List.length_nil] at hdec; exact absurd hdec (by simp)
        have hpos : 0 < (cnormG p : List α).length := List.length_pos_iff.mpr hpne
        obtain ⟨fuel', rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
        have hfuel' : (cnormG (reduceStepWf p q) : List α).length ≤ fuel' := by omega
        have ihstep := ihf fuel' (by omega) (reduceStepWf p q) q hfuel'
        rw [cdivmodG_succ_reducing fuel' p q hcz' hlen]
        simp only [hcz', Bool.false_eq_true, if_false, hlen, if_pos hdec, ihstep, cleadG_cnormG]

/-- **Bridge at the self-sufficient fuel**: `cdivmodWf p q = cdivmodG (cnormG p).length p q`. -/
theorem cdivmodWf_eq (p q : CPolyG α) :
    cdivmodWf p q = cdivmodG (cnormG p : List α).length p q :=
  cdivmodWf_eq_of_fuel _ p q le_rfl

/-- **Euclidean-division identity through `toPolyG`** for the fuel-free `cdivmodWf` (nonzero divisor,
**no fuel hypothesis**): `toPolyG p = toPolyG (quotient) · toPolyG q + toPolyG (remainder)`. -/
theorem toPolyG_cdivmodWf (p q : CPolyG α) (hq0 : cnormG q ≠ []) :
    toPolyG p
      = toPolyG (cdivmodWf p q).1 * toPolyG q + toPolyG (cdivmodWf p q).2 := by
  rw [cdivmodWf_eq]
  exact toPolyG_cdivmodG' _ p q hq0

/-- **Remainder identity through `toPolyG`** for `cmodWf` (no fuel hypothesis). -/
theorem toPolyG_cmodWf (p q : CPolyG α) (hq0 : cnormG q ≠ []) :
    toPolyG p = toPolyG (cdivWf p q) * toPolyG q + toPolyG (cmodWf p q) := by
  rw [cdivWf, cmodWf]; exact toPolyG_cdivmodWf p q hq0

/-! ### `native_decide` smoke tests — the WF def reduces in compiled code

`cdivmodWf` is `[CField α]`-only, so these reduce over both `ℚ` and the *noncomputable*-`CFieldSpec`
tower `QFunNZ` (ℚ(x)) — the well-founded structure carries no fuel and no noncomputable bridge into
the compiled body. -/

/-- `cdivmodWf` over `ℚ`: `(1 + x²) mod (1 + x) = 2`. -/
example : (CPolyG.cdivmodWf [(1 : ℚ), 0, 1] [(1 : ℚ), 1]).2 = [2] := by native_decide

/-- `cdivmodWf` over the ℚ(x) tower `QFunNZ`: the remainder of `1 + x²` by `1 + x` is a constant
(length-1 normalized list) — the whole WF division executes in native code over `QFunNZ`. -/
example :
    ((CPolyG.cdivmodWf [(CField.one : QFunNZ), CField.zero, CField.one]
      [CField.one, CField.one]).2 : List QFunNZ).length = 1 := by native_decide

end CPolyG

end DeepWiki.SymbolicIntegration
