import DeepWiki.SymbolicIntegration.ComputableWellFounded2
import DeepWiki.SymbolicIntegration.ComputableGcdCorrect

/-! # The fuel-free concrete primitive-PRS gcd `primPRSgcdWf` (§3.5)

`primPRSgcdWf P Q ∈ BPoly`, the fuel-free companion of the primitive polynomial-remainder sequence
`primPRSgcd` (`ComputableSplitFactorFast`). Unlike the leaf `cresultantWf`/`cgcdWf` (`[CField α]`-only),
`BPoly = List CPoly` is a *concrete* (fully computable) carrier, so this lives apart from the generic
leaf ops in `ComputableWellFounded2` (which stays `cgcdFF`-free); the runtime-guard structural-WF
technique still gives the cleanest `decreasing_by`. The recursion runs only on the second argument `Q`,
whose normalized `t`-length `(bnorm Q).length` strictly drops each step by `primPRSstep_length_lt`
(pseudo-remainder degree drop ∘ primitive-part non-raising). The associated-to-`gcd` correctness
`associated_toPolyB_primPRSgcdWf` is transported from `associated_toPolyB_primPRSgcd` through the bridge
`primPRSgcdWf_eq_of_fuel`, still gated on `PrimPRSRegular` (the same gate the fuel'd version carries). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

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
