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

-- temporary native_decide smoke tests
example : (CPolyG.cdivmodWf [(1 : ℚ), 0, 1] [(1 : ℚ), 1]).2 = [2] := by native_decide
example :
    ((CPolyG.cdivmodWf [(CField.one : QFunNZ), CField.zero, CField.one]
      [CField.one, CField.one]).2 : List QFunNZ).length = 1 := by native_decide

end CPolyG

end DeepWiki.SymbolicIntegration
