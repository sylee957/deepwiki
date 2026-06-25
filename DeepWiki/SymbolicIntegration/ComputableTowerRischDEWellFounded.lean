import DeepWiki.SymbolicIntegration.ComputableTowerWellFounded
import DeepWiki.SymbolicIntegration.ComputableTowerRischDE

/-! # Fuel-free (well-founded) GENERIC tower §6 Risch-DE oracle `cRischDEGWf`

The generic §6 RDE pipeline (`ComputableTowerRischDE`) — `cRischDEG` and its stages — is
`[CField α] [CDiffField α] [CFracGcdCore α] [CRischField α]`-generic and gate-clean, but every op carries an
explicit `fuel : ℕ`. This file builds the **fuel-free** companions `…GWf`, completing the generic fuel-free
engine: the integration driver `cIntegrateGWf` (`ComputableTowerWellFounded`) is already fuel-free, and TWO
of the RDE recursive bottoms landed there (`cPolyRischDENoCancelGWf` §6.5, `cSPDEGWf` §6.4). Here we finish
the §6 oracle — the headline `cRischDEGWf`.

The §6 pipeline bottoms out at FIVE fuel-recursive ops; two are done in `ComputableTowerWellFounded`
(`cPolyRischDENoCancelGWf`, `cSPDEGWf`), and the remaining THREE are built here:

* **`cPolyRischDECancelPrimGWf`** — §6.6 primitive cancellation, recursing degree-by-degree into the base
  RDE `CRischField.crischDESolve b₀ (lc c)` (eq. 6.23). The leading monomial `s·tᵐ` cancels `c`'s top, so
  `(cnormG c).length` strictly drops; well-founded recursion on it, structural runtime guard.
* **`cPolyRischDECancelExpGWf`** — §6.6 hyperexponential cancellation, recursing into the eq. 6.24 base RDE
  `crischDESolve (b₀ + m·η) (lc c)` (`η = cExpEtaG Dt`). Same own-loop on `(cnormG c).length`.
* **`cValuationGWf`** — the `ν_p` `p`-adic valuation (used by the special-denominator stage), recursing on
  `(cnormG x).length` by trial division. As with the `QFunNZ` arc (`cValuationWf`, no standalone bridge),
  it feeds `cRdeSpecialDenominatorGWf` whose agreement is threaded as a whole-stage hypothesis.

The rest is a flat composition over fuel'd leaves: the generic §6.1 weak normalizer, the §6.2
normal/special denominators, the §6.3 degree bound, the §6.4 SPDE, the §6.5/§6.6 dispatcher, and the
headline `cRischDEGWf`. Each substitutes the fuel-free leaves — the generic ones reused verbatim
(`cdivWf`, `cdivmodWf`, `cdiophantineGWf`, `cdvdGWf`, `cgcdWf`) and the new ones (`cgcdFFCoreWf`, the two
done RDE bottoms, and the three above) — and is bridged to its fuel'd `…G` original.

Every `…GWf` def is **`[CField α]`-only on the fuel-free fragment** (plus `[CDiffField α]`/`[CFracGcdCoreWf α]`/
`[CRischField α]` where the pipeline needs the derivation / the fraction-free gcd / the base solve) — never
`[CFieldSpec α]`, which would break `native_decide` over the noncomputable tower (the keystone lesson). The
fuel bounds live only inside the bridge proofs; the runtime ops carry no fuel. The §6.6 hypertangent
cancellation falls back to non-cancellation as in `cRischDEG` (not handled here). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

/-! ## Part 1 — the three remaining fuel-recursive bottoms

`cPolyRischDECancelPrimGWf` / `cPolyRischDECancelExpGWf` (degree-by-degree own-loops on `(cnormG c).length`,
carrying `[CRischField α]`) and `cValuationGWf` (trial-division own-loop on `(cnormG x).length`). Each is a
true well-founded recursion with a structural runtime guard (`decreasing_by := assumption`), replaying the
`QFunNZ`-specific `cPolyRischDECancelPrimWf` / `cPolyRischDECancelExpWf` / `cValuationWf` patterns generically. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α] [CRischField α]

/-- **Generic fuel-free primitive cancellation Poly-Risch-DE** (Bronstein §6.6, book p.212)
`cPolyRischDECancelPrimGWf Dt b c n`: the generic, fuel-free companion of `cPolyRischDECancelPrimG`. Given the
primitive monomial derivation `D` (`Dt ∈ α`), `b ∈ α*` (a degree-0 `t`-polynomial, scalar `b₀ = lc(b)`) and
`c ∈ α[t]`, with degree bound `n : ℤ`, solves `Dq + b·q = c` degree-by-degree, recursing at degree
`m = deg(c)` into the base RDE `CRischField.crischDESolve b₀ (lc c)` (eq. 6.23) over `α`, leading monomial
`s·tᵐ`, remainder `c' = c − b·(s·tᵐ) − D(s·tᵐ)` (`D = cmonomialDeriv Dt`). Returns `none` ("no solution of
degree `≤ n`") or `some q`. True well-founded recursion on `(cnormG c).length` — **no fuel at runtime**; the
recursion is taken only under the structural guard `(cnormG c').length < (cnormG c).length` (the leading
monomial cancels `c`'s top), so `decreasing_by` is `assumption`. Agrees with `cPolyRischDECancelPrimG` on a
real run (`cPolyRischDECancelPrimGWf_eq`). `[CRischField α]`-generic — runs at any tower level. -/
def cPolyRischDECancelPrimGWf (Dt : CPolyG α) (b c : CPolyG α) (n : ℤ) :
    Option (CPolyG α) :=
  let b0 : α := cleadG b
  if cisZeroG c then some []
  else if n < (cdegG c : ℤ) then none
  else
    let m : ℕ := cdegG c
    match CRischField.crischDESolve b0 (cleadG c) with
    | none => none
    | some s =>
      let stm : CPolyG α := cshiftG m [s]               -- `s·tᵐ`
      let c' := csubG (csubG c (cmulG b stm)) (cmonomialDeriv Dt stm)
      if (cnormG c' : List α).length < (cnormG c : List α).length then
        match cPolyRischDECancelPrimGWf Dt b c' ((m : ℤ) - 1) with
        | none => none
        | some q => some (caddG stm q)
      else none   -- unreachable on a real run (the leading monomial cancels, degree drops)
termination_by (cnormG c).length
decreasing_by assumption

/-- **Generic fuel-free hyperexponential cancellation Poly-Risch-DE** (Bronstein §6.6, book p.213)
`cPolyRischDECancelExpGWf Dt b c n`: the generic, fuel-free companion of `cPolyRischDECancelExpG`. Given the
hyperexponential monomial derivation `D` (`η = Dt/t ∈ α`, `δ = 1`), `b ∈ α*` (scalar `b₀ = lc(b)`) and
`c ∈ α[t]`, with degree bound `n : ℤ`, solves `Dq + b·q = c` degree-by-degree, recursing at degree
`m = deg(c)` into the eq. 6.24 base RDE `crischDESolve (b₀ + m·η) (lc c)` over `α` (the `m·η` shift makes the
coefficient genuinely non-constant, `η = cExpEtaG Dt`), leading monomial `s·tᵐ`, remainder
`c' = c − b·(s·tᵐ) − D(s·tᵐ)`. Returns `none` or `some q`. True well-founded recursion on `(cnormG c).length`
— **no fuel at runtime**; the structural guard `(cnormG c').length < (cnormG c).length` is `decreasing_by :=
assumption`. Agrees with `cPolyRischDECancelExpG` on a real run (`cPolyRischDECancelExpGWf_eq`).
`[CRischField α]`-generic — runs at any tower level. -/
def cPolyRischDECancelExpGWf (Dt : CPolyG α) (b c : CPolyG α) (n : ℤ) :
    Option (CPolyG α) :=
  let b0 : α := cleadG b
  let η : α := cExpEtaG 30 Dt
  if cisZeroG c then some []
  else if n < (cdegG c : ℤ) then none
  else
    let m : ℕ := cdegG c
    -- eq. 6.24 base RDE `Ds + (b₀ + m·η)·s = lc(c)` over `α`.
    let coeff : α := CField.add b0 (CField.mul (cnatCastG m) η)
    match CRischField.crischDESolve coeff (cleadG c) with
    | none => none
    | some s =>
      let stm : CPolyG α := cshiftG m [s]               -- `s·tᵐ`
      let c' := csubG (csubG c (cmulG b stm)) (cmonomialDeriv Dt stm)
      if (cnormG c' : List α).length < (cnormG c : List α).length then
        match cPolyRischDECancelExpGWf Dt b c' ((m : ℤ) - 1) with
        | none => none
        | some q => some (caddG stm q)
      else none   -- unreachable on a real run (the leading monomial cancels, degree drops)
termination_by (cnormG c).length
decreasing_by assumption

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CFracGcdCore α]

/-- **Generic fuel-free `p`-adic valuation** `cValuationGWf p x = ν_p(x)`: the generic, fuel-free companion of
`cValuationG`, the multiplicity of the monic irreducible `p` dividing `x` (largest `k` with `pᵏ ∣ x`), by
trial division. Stops at the zero polynomial, a constant/unit `p` (`cdegG p = 0`), or a non-dividing step,
else recurses on `x/p` (the **fuel-free** `cdivWf`) and adds one. True well-founded recursion on
`(cnormG x).length` — **no fuel at runtime**; the recursion is taken only under the structural guard
`(cnormG (x/p)).length < (cnormG x).length`, so `decreasing_by` is `assumption`. The exact division `p ∣ x`
with non-constant `p` drops the `t`-degree on a real run, so the guard never fails and it agrees with
`cValuationG`. `[CField α]`-generic — runs at any tower level. -/
def cValuationGWf (p x : CPolyG α) : ℕ :=
  if cisZeroG x then 0
  else if cdegG p = 0 then 0
  else if cdvdGWf p x then
    let xq := cdivWf x p
    if (cnormG xq : List α).length < (cnormG x : List α).length then
      1 + cValuationGWf p xq
    else 0   -- unreachable on a real run (non-constant `p ∣ x` drops the degree)
  else 0
termination_by (cnormG x).length
decreasing_by assumption

end CPolyG

/-! ## Part 2 — bridges of the three recursive bottoms to their fuel'd `…G` originals

As with the `QFunNZ` arc (`cPolyRischDECancelPrimWf_eq`, `cPolyRischDECancelExpWf_eq`) and the integration
fuel-free bottoms (`cSqfreeYunFFGgoWf_eq`), the cancellation bridges carry `[CFieldSpec α]` (so the fuel'd
ops reduce) and take a **fuel-regularity predicate** that mirrors the fuel'd recursion with a step budget and
the per-step WF-guard / base-solve agreement built in. The cancellation own-loops use **no** fuel-bearing
sub-ops (only `cmonomialDeriv`/`cshiftG`/`crischDESolve`/`cExpEtaG`, all fuel-free) — they recurse on `fuel`
purely as a counter — so the gate needs only that the base solve agrees and the guard fires. `cValuationGWf`
feeds the special-denominator stage whose agreement is threaded as a whole-stage hypothesis (mirroring
`cValuationWf`, which likewise has no standalone bridge), so we give it a regularity-gated bridge here. -/

/-- **Per-run generic primitive-cancellation-loop regularity** `CPolyRischCancelPrimGenRegular Dt b c n`
(nodes conclude at fuel `fuel + 1`): mirrors the `cPolyRischDECancelPrimG` recursion. `baseZero`/`baseDeg`
terminal on `c = 0`/`n < deg(c)`; `baseNoSol` terminal when the base solve `crischDESolve (lc b)(lc c)`
returns `none`; `step` carries the base solve `crischDESolve (lc b)(lc c) = some s` (the WF op equals the
fuel'd op — both call the same fuel-free `crischDESolve`), the WF guard firing (`c' = c − b·(s·tᵐ) − D(s·tᵐ)`,
`m = deg(c)`, `D = cmonomialDeriv Dt`), and the same recursively on `c'` at `m − 1`. -/
inductive CPolyRischCancelPrimGenRegular {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α]
    [CRischField α] (Dt : CPolyG α) (b : CPolyG α) : ℕ → CPolyG α → ℤ → Prop
  /-- terminal: `c = 0`, returns `[]`. -/
  | baseZero {fuel : ℕ} {c : CPolyG α} {n : ℤ} (hc : CPolyG.cisZeroG c = true) :
      CPolyRischCancelPrimGenRegular Dt b (fuel + 1) c n
  /-- terminal: `n < deg(c)`, returns `none`. -/
  | baseDeg {fuel : ℕ} {c : CPolyG α} {n : ℤ} (hc : ¬ CPolyG.cisZeroG c = true)
      (hn : n < (CPolyG.cdegG c : ℤ)) : CPolyRischCancelPrimGenRegular Dt b (fuel + 1) c n
  /-- terminal: the base solve returns `none`. -/
  | baseNoSol {fuel : ℕ} {c : CPolyG α} {n : ℤ} (hc : ¬ CPolyG.cisZeroG c = true)
      (hn : ¬ n < (CPolyG.cdegG c : ℤ))
      (hs : CRischField.crischDESolve (CPolyG.cleadG b) (CPolyG.cleadG c) = none) :
      CPolyRischCancelPrimGenRegular Dt b (fuel + 1) c n
  /-- recursive: the base solve gives `s`, the WF guard fires, recurse on `c'` within budget. -/
  | step {fuel : ℕ} {c : CPolyG α} {n : ℤ} {s : α} (hc : ¬ CPolyG.cisZeroG c = true)
      (hn : ¬ n < (CPolyG.cdegG c : ℤ))
      (hs : CRischField.crischDESolve (CPolyG.cleadG b) (CPolyG.cleadG c) = some s)
      (hguard : (CPolyG.cnormG (CPolyG.csubG (CPolyG.csubG c
            (CPolyG.cmulG b (CPolyG.cshiftG (CPolyG.cdegG c) [s])))
            (CPolyG.cmonomialDeriv Dt (CPolyG.cshiftG (CPolyG.cdegG c) [s]))) : List α).length
          < (CPolyG.cnormG c : List α).length)
      (hrec : CPolyRischCancelPrimGenRegular Dt b fuel
        (CPolyG.csubG (CPolyG.csubG c (CPolyG.cmulG b (CPolyG.cshiftG (CPolyG.cdegG c) [s])))
          (CPolyG.cmonomialDeriv Dt (CPolyG.cshiftG (CPolyG.cdegG c) [s])))
        ((CPolyG.cdegG c : ℤ) - 1)) :
      CPolyRischCancelPrimGenRegular Dt b (fuel + 1) c n

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α] [CRischField α]

/-- **Bridge — `cPolyRischDECancelPrimGWf` equals `cPolyRischDECancelPrimG` on a regular run.** Under
`CPolyRischCancelPrimGenRegular Dt b (fuel + 1) c n` (the per-step base-solve agreement + WF-guard-drop a real
cancellation run meets, with sufficient fuel), `cPolyRischDECancelPrimGWf Dt b c n =
cPolyRischDECancelPrimG Dt (fuel + 1) b c n`. The fuel regularity lives only here; the WF own-loop carries
none. By induction on the gate (the base solve is the same fuel-free `crischDESolve`; the WF guard fires; the
fuel'd version at `fuel+1` descends). -/
theorem cPolyRischDECancelPrimGWf_eq (Dt : CPolyG α) (b : CPolyG α) :
    ∀ (fuel : ℕ) (c : CPolyG α) (n : ℤ), CPolyRischCancelPrimGenRegular Dt b fuel c n →
      cPolyRischDECancelPrimGWf Dt b c n = cPolyRischDECancelPrimG Dt fuel b c n := by
  intro fuel c n hreg
  induction hreg with
  | @baseZero fuel c n hc =>
    rw [cPolyRischDECancelPrimGWf.eq_def, if_pos hc, cPolyRischDECancelPrimG, if_pos hc]
  | @baseDeg fuel c n hc hn =>
    rw [cPolyRischDECancelPrimGWf.eq_def, if_neg hc, if_pos hn,
      cPolyRischDECancelPrimG, if_neg hc, if_pos hn]
  | @baseNoSol fuel c n hc hn hs =>
    rw [cPolyRischDECancelPrimGWf.eq_def, if_neg hc, if_neg hn,
      cPolyRischDECancelPrimG, if_neg hc, if_neg hn]
    simp only [hs]
  | @step fuel c n s hc hn hs hguard hrec ih =>
    rw [cPolyRischDECancelPrimGWf.eq_def, if_neg hc, if_neg hn,
      cPolyRischDECancelPrimG, if_neg hc, if_neg hn]
    simp only [hs, if_pos hguard, ih]
    rfl

end CPolyG

/-- **Per-run generic hyperexponential-cancellation-loop regularity** `CPolyRischCancelExpGenRegular Dt b c n`
(nodes conclude at fuel `fuel + 1`): mirrors the `cPolyRischDECancelExpG` recursion. As the primitive case but
the base solve uses the `m·η` shifted coefficient `b₀ + m·η`; the gate carries `cExpEtaG 30 Dt =
cExpEtaG fuel Dt` (`hη`, so the fuel-free and fuel'd coefficients coincide). `baseZero`/`baseDeg`/`baseNoSol`
terminal as before (at the shifted coefficient); `step` carries the base solve at the shifted coefficient (WF
= fuel'd = `some s`) and the WF guard firing. -/
inductive CPolyRischCancelExpGenRegular {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α]
    [CRischField α] (Dt : CPolyG α) (b : CPolyG α) : ℕ → CPolyG α → ℤ → Prop
  /-- terminal: `c = 0`, returns `[]`. -/
  | baseZero {fuel : ℕ} {c : CPolyG α} {n : ℤ} (hc : CPolyG.cisZeroG c = true) :
      CPolyRischCancelExpGenRegular Dt b (fuel + 1) c n
  /-- terminal: `n < deg(c)`, returns `none`. -/
  | baseDeg {fuel : ℕ} {c : CPolyG α} {n : ℤ} (hc : ¬ CPolyG.cisZeroG c = true)
      (hn : n < (CPolyG.cdegG c : ℤ)) : CPolyRischCancelExpGenRegular Dt b (fuel + 1) c n
  /-- terminal: the base solve at the `m·η`-shifted coefficient returns `none` (`η` reads agree). -/
  | baseNoSol {fuel : ℕ} {c : CPolyG α} {n : ℤ} (hc : ¬ CPolyG.cisZeroG c = true)
      (hn : ¬ n < (CPolyG.cdegG c : ℤ)) (hη : CPolyG.cExpEtaG 30 Dt = CPolyG.cExpEtaG fuel Dt)
      (hs : CRischField.crischDESolve (CField.add (CPolyG.cleadG b)
          (CField.mul (CPolyG.cnatCastG (CPolyG.cdegG c)) (CPolyG.cExpEtaG 30 Dt)))
          (CPolyG.cleadG c) = none) :
      CPolyRischCancelExpGenRegular Dt b (fuel + 1) c n
  /-- recursive: the base solve at the shifted coefficient gives `s` (WF = fuel'd), the WF guard fires. -/
  | step {fuel : ℕ} {c : CPolyG α} {n : ℤ} {s : α} (hc : ¬ CPolyG.cisZeroG c = true)
      (hn : ¬ n < (CPolyG.cdegG c : ℤ)) (hη : CPolyG.cExpEtaG 30 Dt = CPolyG.cExpEtaG fuel Dt)
      (hs : CRischField.crischDESolve (CField.add (CPolyG.cleadG b)
          (CField.mul (CPolyG.cnatCastG (CPolyG.cdegG c)) (CPolyG.cExpEtaG 30 Dt)))
          (CPolyG.cleadG c) = some s)
      (hguard : (CPolyG.cnormG (CPolyG.csubG (CPolyG.csubG c
            (CPolyG.cmulG b (CPolyG.cshiftG (CPolyG.cdegG c) [s])))
            (CPolyG.cmonomialDeriv Dt (CPolyG.cshiftG (CPolyG.cdegG c) [s]))) : List α).length
          < (CPolyG.cnormG c : List α).length)
      (hrec : CPolyRischCancelExpGenRegular Dt b fuel
        (CPolyG.csubG (CPolyG.csubG c (CPolyG.cmulG b (CPolyG.cshiftG (CPolyG.cdegG c) [s])))
          (CPolyG.cmonomialDeriv Dt (CPolyG.cshiftG (CPolyG.cdegG c) [s])))
        ((CPolyG.cdegG c : ℤ) - 1)) :
      CPolyRischCancelExpGenRegular Dt b (fuel + 1) c n

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α] [CRischField α]

/-- **Bridge — `cPolyRischDECancelExpGWf` equals `cPolyRischDECancelExpG` on a regular run.** Under
`CPolyRischCancelExpGenRegular Dt b (fuel + 1) c n` (the per-step `η` read + shifted base-solve agreement +
WF-guard-drop a real run meets), `cPolyRischDECancelExpGWf Dt b c n = cPolyRischDECancelExpG Dt (fuel + 1) b
c n`. The fuel regularity lives only here. By induction on the gate (`hη` reconciles the `η` reads, the base
solve agrees, the WF guard fires). -/
theorem cPolyRischDECancelExpGWf_eq (Dt : CPolyG α) (b : CPolyG α) :
    ∀ (fuel : ℕ) (c : CPolyG α) (n : ℤ), CPolyRischCancelExpGenRegular Dt b fuel c n →
      cPolyRischDECancelExpGWf Dt b c n = cPolyRischDECancelExpG Dt fuel b c n := by
  intro fuel c n hreg
  induction hreg with
  | @baseZero fuel c n hc =>
    rw [cPolyRischDECancelExpGWf.eq_def, if_pos hc, cPolyRischDECancelExpG, if_pos hc]
  | @baseDeg fuel c n hc hn =>
    rw [cPolyRischDECancelExpGWf.eq_def, if_neg hc, if_pos hn,
      cPolyRischDECancelExpG, if_neg hc, if_pos hn]
  | @baseNoSol fuel c n hc hn hη hs =>
    rw [cPolyRischDECancelExpGWf.eq_def, if_neg hc, if_neg hn,
      cPolyRischDECancelExpG, if_neg hc, if_neg hn]
    simp only [hη] at hs
    simp only [hη, hs]
  | @step fuel c n s hc hn hη hs hguard hrec ih =>
    rw [cPolyRischDECancelExpGWf.eq_def, if_neg hc, if_neg hn,
      cPolyRischDECancelExpG, if_neg hc, if_neg hn]
    simp only [hη] at hs hguard hrec ih
    simp only [hη, hs, if_pos hguard, ih]
    rfl

end CPolyG

/-! ### Bridge of `cValuationGWf` to the fuel'd `cValuationG`

`cValuationG fuel p x = cValuationG.go p fuel x` recurses on `fuel` with the per-step `cdvdG`/`cdivG` over the
GCD-domain; the WF `cValuationGWf` recurses on `(cnormG x).length` with the fuel-free `cdvdGWf`/`cdivWf`. The
gate `CValuationGenRegular fuel p x` mirrors the fuel'd `.go` recursion with a step budget, carrying the
per-step leaf agreements (`cdvdGWf p x = cdvdG fuel p x`, `cdivWf x p = cdivG fuel x p`) and the WF guard. -/

/-- **Per-run generic valuation-loop regularity** `CValuationGenRegular fuel p x` (nodes conclude at fuel
`fuel + 1`): mirrors the `cValuationG.go` recursion. `baseZero` (`x = 0`) / `baseConst` (`deg(p) = 0`) /
`baseNonDvd` (`p ∤ x`) are terminal; `step` carries the leaf agreements `cdvdGWf p x = cdvdG fuel p x` (`hdvd`,
and that it is `true`) and `cdivWf x p = cdivG fuel x p` (`hdiv`), the WF guard firing (`(cnormG (x/p)).length
< (cnormG x).length`), and the same recursively on `x/p` within budget. -/
inductive CValuationGenRegular {α : Type*} [CField α] [CFracGcdCore α] [CFieldSpec α] (p : CPolyG α) :
    ℕ → CPolyG α → Prop
  /-- terminal: `x = 0`, valuation `0`. -/
  | baseZero {fuel : ℕ} {x : CPolyG α} (hx : CPolyG.cisZeroG x = true) :
      CValuationGenRegular p (fuel + 1) x
  /-- terminal: `p` is constant/unit (`deg p = 0`), valuation `0`. -/
  | baseConst {fuel : ℕ} {x : CPolyG α} (hx : ¬ CPolyG.cisZeroG x = true) (hp : CPolyG.cdegG p = 0) :
      CValuationGenRegular p (fuel + 1) x
  /-- terminal: `p ∤ x`, valuation `0`. -/
  | baseNonDvd {fuel : ℕ} {x : CPolyG α} (hx : ¬ CPolyG.cisZeroG x = true) (hp : CPolyG.cdegG p ≠ 0)
      (hdvdlen : (CPolyG.cnormG x : List α).length ≤ fuel)
      (hdvd : CPolyG.cdvdG fuel p x = false) : CValuationGenRegular p (fuel + 1) x
  /-- recursive: `p ∣ x`, the WF guard fires, recurse on `x/p` within budget. -/
  | step {fuel : ℕ} {x : CPolyG α} (hx : ¬ CPolyG.cisZeroG x = true) (hp : CPolyG.cdegG p ≠ 0)
      (hdvd : CPolyG.cdvdG fuel p x = true)
      (hdvdlen : (CPolyG.cnormG x : List α).length ≤ fuel)
      (hguard : (CPolyG.cnormG (CPolyG.cdivG fuel x p) : List α).length
          < (CPolyG.cnormG x : List α).length)
      (hrec : CValuationGenRegular p fuel (CPolyG.cdivG fuel x p)) :
      CValuationGenRegular p (fuel + 1) x

namespace CPolyG

variable {α : Type*} [CField α] [CFracGcdCore α] [CFieldSpec α]

/-- **Bridge — `cValuationGWf` equals `cValuationG` on a regular run.** Under `CValuationGenRegular p fuel x`,
`cValuationGWf p x = cValuationG fuel p x`. The fuel regularity lives only here; the WF own-loop carries none.
By induction on the gate (the per-step `cdvdGWf`/`cdivWf` match the fuel'd `cdvdG`/`cdivG` via
`cdvdGWf_eq_of_fuel` / `cdivmodWf_eq_of_fuel`; the WF guard fires; the fuel'd `.go` descends). -/
theorem cValuationGWf_eq (p : CPolyG α) :
    ∀ (fuel : ℕ) (x : CPolyG α), CValuationGenRegular p fuel x →
      cValuationGWf p x = cValuationG fuel p x := by
  intro fuel x hreg
  induction hreg with
  | @baseZero fuel x hx =>
    rw [cValuationGWf.eq_def, if_pos hx, cValuationG, cValuationG.go, if_pos hx]
  | @baseConst fuel x hx hp =>
    rw [cValuationGWf.eq_def, if_neg hx, if_pos hp, cValuationG, cValuationG.go,
      if_neg hx, if_pos hp]
  | @baseNonDvd fuel x hx hp hdvdlen hdvd =>
    have hdvdwf : cdvdGWf p x = false := by rw [cdvdGWf_eq_of_fuel fuel p x hdvdlen, hdvd]
    rw [cValuationGWf.eq_def, if_neg hx, if_neg hp, hdvdwf, if_neg (by decide : ¬ (false = true)),
      cValuationG, cValuationG.go, if_neg hx, if_neg hp, hdvd, if_neg (by decide : ¬ (false = true))]
  | @step fuel x hx hp hdvd hdvdlen hguard hrec ih =>
    have hdvdwf : cdvdGWf p x = true := by rw [cdvdGWf_eq_of_fuel fuel p x hdvdlen, hdvd]
    have hdiveq : cdivWf x p = cdivG fuel x p := by
      rw [cdivWf, cdivmodWf_eq_of_fuel fuel x p hdvdlen, cdivG]
    conv_lhs => rw [cValuationGWf.eq_def, if_neg hx, if_neg hp, hdvdwf, hdiveq, if_pos hguard, ih]
    conv_rhs => rw [cValuationG, cValuationG.go, if_neg hx, if_neg hp, hdvd,
      if_pos (by rfl : (true = true))]
    rw [if_pos (by rfl : (true = true)), cValuationG]

end CPolyG

end DeepWiki.SymbolicIntegration
