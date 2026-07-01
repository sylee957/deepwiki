import DeepWiki.SymbolicIntegration.ComputableTowerWellFounded
import DeepWiki.SymbolicIntegration.ComputableTowerRischDE

/-! # Fuel-free (well-founded) GENERIC tower §6 Risch-DE oracle `cRischDEGWf`

The generic §6 RDE pipeline (`ComputableTowerRischDE`) — `cRischDEG` and its stages — is
`[CField α] [CDiffField α] [CFracGcdCore α] [CRischField α]`-generic and gate-clean, but every op carries an
explicit `fuel : ℕ`. This file builds the **fuel-free** companions `…GWf`, completing the generic fuel-free
engine: the reduced-case driver `cIntegrateReducedGWf` (`ComputableTowerWellFounded`) is already fuel-free, and TWO
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
  `(cnormG x).length` by trial division. It has no standalone bridge; it
  feeds `cRdeSpecialDenominatorGWf` whose agreement is threaded as a whole-stage hypothesis.

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
true well-founded recursion with a structural runtime guard (`decreasing_by := assumption`) — the generic
primitive-cancellation, hyperexponential-cancellation, and valuation own-loops. -/

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

Like the integration fuel-free bottoms (`cSqfreeYunFFGgoWf_eq`), the cancellation bridges carry
`[CFieldSpec α]` (so the fuel'd
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
    rw [hdiveq]

end CPolyG

/-! ## Part 3 — the flat-composition §6 pipeline (fuel-free leaf substitution)

Everything past the five recursive bottoms is a flat composition over fuel'd leaves. The fuel-free companions
substitute the fuel-free leaves — the generic ones reused verbatim (`cdivWf`, `cdivmodWf`, `cdiophantineGWf`,
`cdvdGWf`, `cgcdWf`, the §5.6 `cResidueResultantTowerGWf`/`cinterpolateG`/`cHornerG`) and the new ones from
Parts 1–2 plus the integration fuel-free file (`cgcdFFCoreWf`, `cSplitFactorFastGWf`, the two done RDE
bottoms `cPolyRischDENoCancelGWf`/`cSPDEGWf`, and the three Part-1 bottoms). Each `…GWf` mirrors its `…G`
original op-for-op with the fuel dropped — a pure composition, no new recursion. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α] [CFracGcdCoreWf α]

/-- **Generic fuel-free weak normalizer** `cWeakNormalizerGWf Dt fnum fden = q ∈ α[t]` (Bronstein §6.1, book
p.183): the generic, fuel-free companion of `cWeakNormalizerG`. Split the denominator into its normal part
`dₙ` (`cSplitFactorFastGWf`), form `d₁ = (dₙ/g)/gcd(dₙ/g, g)` with `g = gcd(dₙ, dₙ')`, solve the residue
numerator `a` via `cdiophantineGWf`, build the residue resultant `r = res_t(a − z·Dd₁, d₁)`
(`cResidueResultantTowerGWf`), and return `∏ᵢ gcd(a − nᵢ·Dd₁, d₁)^{nᵢ}` over the positive integer roots `nᵢ`
of `r` (`cPosIntRootsG`, nodes lifted by `cnatCastG`). Every gcd is the fuel-free `cgcdFFCoreWf`, every
division the fuel-free `cdivWf` — **no fuel at runtime**. For an already-weakly-normalized `f`, `q = 1`.
`[CField α] [CDiffField α] [CFracGcdCoreWf α]`-generic — runs at any tower level. -/
def cWeakNormalizerGWf (Dt : CPolyG α) (fnum fden : CPolyG α) (boundRoots : ℕ := 16) : CPolyG α :=
  let dn := (cSplitFactorFastGWf Dt fden).1
  let g := CFracGcdCoreWf.cgcdFFCoreWf dn (cderivG dn)
  let dstar := cdivWf dn g
  let d1 := cdivWf dstar (CFracGcdCoreWf.cgcdFFCoreWf dstar g)
  let fdenOverD1 := cdivWf fden d1
  let a := (cdiophantineGWf fdenOverD1 d1 fnum).1
  let Dd1 := cmonomialDeriv Dt d1
  let r := cResidueResultantTowerGWf Dt a d1
  let roots := cPosIntRootsG r boundRoots
  roots.foldl (fun (acc : CPolyG α) (n : ℕ) =>
    let gi := CFracGcdCoreWf.cgcdFFCoreWf (csubG a (cscaleG (cnatCastG n) Dd1)) d1
    cmulG acc (cpowG gi n)) [CField.one]

/-- **Generic fuel-free normal-denominator reduction** `cRdeNormalDenominatorGWf Dt fnum fden gnum gden`
(Bronstein §6.2, book p.185): the generic, fuel-free companion of `cRdeNormalDenominatorG`, for weakly
normalized `f = fnum/fden`, `g = gnum/gden`. Returns `none` ("no solution") or `some (a, b, c, h)` reducing
`Dy + fy = g` to `a·Dq + b·q = c` with `q = y·h`. Split the denominators into normal parts `dₙ, eₙ`
(`cSplitFactorFastGWf`); `p = gcd(dₙ, eₙ)`, `h = gcd(eₙ, eₙ')/gcd(p, p')`; if `eₙ ∤ dₙh²` then `none`; else
`a = dₙh`, `b = (dₙh·fnum − dₙ·Dh·fden)/fden`, `c = dₙh²·gnum/gden`. Every gcd/division/divisibility is the
fuel-free `cgcdFFCoreWf`/`cdivWf`/`cdvdGWf` — **no fuel at runtime**. -/
def cRdeNormalDenominatorGWf (Dt : CPolyG α) (fnum fden gnum gden : CPolyG α) :
    Option (CPolyG α × CPolyG α × CPolyG α × CPolyG α) :=
  let dn := (cSplitFactorFastGWf Dt fden).1
  let en := (cSplitFactorFastGWf Dt gden).1
  let p := CFracGcdCoreWf.cgcdFFCoreWf dn en
  let h := cdivWf (CFracGcdCoreWf.cgcdFFCoreWf en (cderivG en))
    (CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p))
  let dnh2 := cmulG (cmulG dn h) h
  if cdvdGWf en dnh2 then
    let a := cmulG dn h
    let Dh := cmonomialDeriv Dt h
    let b := cdivWf (csubG (cmulG a fnum) (cmulG (cmulG dn Dh) fden)) fden
    let c := cdivWf (cmulG dnh2 gnum) gden
    some (a, b, c, h)
  else none

/-- **Generic fuel-free special monic irreducible of the monomial** `cSpecialPolyGWf Dt = p`: the generic,
fuel-free companion of `cSpecialPolyG`, the monic special part of the monomial derivative `Dt` (`t²+1`
hypertangent, `t` hyperexponential, `1` primitive) via the fuel-free splitting-factorization
`cSplitFactorFastGWf` — **no fuel at runtime**. -/
def cSpecialPolyGWf (Dt : CPolyG α) : CPolyG α :=
  cmonicG (cSplitFactorFastGWf Dt Dt).2

/-- **Generic fuel-free special-denominator reduction** `cRdeSpecialDenominatorGWf Dt a b c` (Bronstein §6.2,
book p.190/192): the generic, fuel-free companion of `cRdeSpecialDenominatorG`. Given `a·Dq + b·q = c` with
`a` free of special factors, returns the special-cleared quadruplet `(ā, b̄, c̄, h)` (`h = p^{−n}`) so
`r = q·h ∈ α[t]` solves `ā·Dr + b̄·r = c̄`. Steps: `p ← cSpecialPolyGWf Dt` (constant ⇒ trivial, returns
`(a,b,c,1)`); `n_b = ν_p(b)`, `n_c = ν_p(c)` (fuel-free `cValuationGWf`), `n = min(0, n_c − min(0, n_b))`,
`N = max(0, −n_b, n − n_c)`; return `(a·pᴺ, (b + n·a·Dp/p)·pᴺ, c·p^{N−n}, p^{−n})`, the `Dp/p` division the
fuel-free `cdivWf`. The cancellation refinement (`n_b = 0` branch) is the documented continuation. The
scalar `−negn` is lifted by `cnatCastG` (negated). **No fuel at runtime**. -/
def cRdeSpecialDenominatorGWf (Dt : CPolyG α) (a b c : CPolyG α) :
    CPolyG α × CPolyG α × CPolyG α × CPolyG α :=
  let p := cSpecialPolyGWf Dt
  if cdegG p = 0 then (a, b, c, [CField.one])
  else
    let nb : ℤ := (cValuationGWf p b : ℤ)
    let nc : ℤ := (cValuationGWf p c : ℤ)
    let n : ℤ := min 0 (nc - min 0 nb)
    let N : ℤ := max (max 0 (-nb)) (n - nc)
    let Nnat : ℕ := N.toNat
    let negn : ℕ := (-n).toNat
    let Nminusn : ℕ := (N - n).toNat
    let pN := cpowG p Nnat
    let abar := cmulG a pN
    let DpOverp := cdivWf (cmonomialDeriv Dt p) p
    let bterm := cscaleG (CField.neg (cnatCastG negn)) (cmulG a DpOverp)
    let bbar := cmulG (caddG b bterm) pN
    let cbar := cmulG c (cpowG p Nminusn)
    let h := cpowG p negn
    (abar, bbar, cbar, h)

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

/-- **Generic fuel-free degree bound** `cRdeBoundDegreeGWf Dt a b c = n ∈ ℕ` (Bronstein §6.3, book p.198–201):
the generic, fuel-free companion of `cRdeBoundDegreeG`. An upper bound on `deg_t(q)` for any polynomial
solution `q ∈ α[t]` of `a·Dq + b·q = c`, by pure list-degree arithmetic (`cRdeBoundDegreeG` already ignores
its fuel argument): with `d_a, d_b, d_c` the degrees and `δ = deg(Dt)`, nonlinear (`δ ≥ 2`)
`max(0, d_c − max(d_a + δ − 1, d_b))`; hyperexponential (`δ = 1`) `max(0, d_c − max(d_b, d_a))`; primitive
(`δ = 0`) `max(0, d_c − d_b)` if `d_b > d_a` else `max(0, d_c − d_a + 1)`. **No fuel at runtime**. -/
def cRdeBoundDegreeGWf (Dt : CPolyG α) (a b c : CPolyG α) : ℕ :=
  let da : ℤ := (cdegG a : ℤ)
  let db : ℤ := (cdegG b : ℤ)
  let dc : ℤ := (cdegG c : ℤ)
  let δ : ℤ := (cdegG Dt : ℤ)
  let n : ℤ :=
    if 2 ≤ δ then
      max 0 (dc - max (da + δ - 1) db)
    else if δ = 1 then
      max 0 (dc - max db da)
    else
      if da < db then max 0 (dc - db) else max 0 (dc - da + 1)
  n.toNat

/-- **Generic fuel-free hyperexponential coefficient `η = Dt/t ∈ α`** `cExpEtaGWf Dt`: the generic, fuel-free
companion of `cExpEtaG`. For a hyperexponential monomial `Dt = η·t` (`δ = 1`), divide `Dt` by `t`
(`cshiftG 1 [1]`) with the fuel-free `cdivWf` and read the resulting degree-0 `t`-polynomial's coefficient
`η ∈ α`. **No fuel at runtime**. -/
def cExpEtaGWf (Dt : CPolyG α) : α :=
  cleadG (cdivWf Dt (cshiftG 1 [CField.one]))

/-- **Generic fuel-free polynomial antiderivative** `cIntegratePolyGWf c = q` with `Dq = c` and `q(0) = 0`,
for the canonical primitive monomial (`Dt = 1`) and constant coefficients: termwise
`∫ Σ cᵢtⁱ = Σ (cᵢ/(i+1)) t^{i+1}` (`cᵢ/(i+1) = CField.div cᵢ (cnatCastG (i+1))`). The fuel-free companion of
`cIntegratePolyG` (which already carries no fuel) — **no fuel at runtime**. -/
def cIntegratePolyGWf (c : CPolyG α) : CPolyG α :=
  CField.zero :: ((c : List α).zipIdx.map (fun (a, i) => CField.div a (cnatCastG (i + 1))))

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CRischField α]

/-- **Generic fuel-free Poly-Risch-DE dispatcher** `cPolyRischDEGWf Dt b c n` (Bronstein §6.5 + §6.6): the
generic, fuel-free companion of `cPolyRischDEG`. Solves `Dq + b·q = c` for `q ∈ α[t]`, `deg(q) ≤ n`, routing
by monomial type and `deg(b)` (Lemma 6.5.1): `b = 0` ⇒ pure integration (`cIntegratePolyGWf`, with the
`deg(c)+1 ≤ n` check — the primitive base branch); `deg(b) > max(0, δ−1)` ⇒ non-cancellation
(`cPolyRischDENoCancelGWf`); `δ = 0, deg(b) = 0` ⇒ primitive cancellation (`cPolyRischDECancelPrimGWf`);
`δ = 1, deg(b) = 0` ⇒ hyperexponential cancellation (`cPolyRischDECancelExpGWf`); else (hypertangent
`δ ≥ 2`) ⇒ falls back to the non-cancellation loop. Every branch runs fuel-free — **no fuel at runtime**.
`[CRischField α]`-generic — runs at any tower level. -/
def cPolyRischDEGWf (Dt : CPolyG α) (b c : CPolyG α) (n : ℤ) : Option (CPolyG α) :=
  let δ : ℤ := (cdegG Dt : ℤ)
  let db : ℤ := (cdegG b : ℤ)
  if cisZeroG b then
    if cisZeroG c then some []
    else if (cdegG c : ℤ) + 1 > n then none
    else some (cIntegratePolyGWf c)
  else if db > max 0 (δ - 1) then
    cPolyRischDENoCancelGWf Dt b c n
  else if δ = 0 ∧ db = 0 then
    cPolyRischDECancelPrimGWf Dt b c n
  else if δ = 1 ∧ db = 0 then
    cPolyRischDECancelExpGWf Dt b c n
  else
    cPolyRischDENoCancelGWf Dt b c n

end CPolyG

/-! ## Part 4 — ★ THE HEADLINE: the generic fuel-free Risch-DE oracle `cRischDEGWf`

`cRischDEGWf` threads the fuel-free §6 stages, the fuel-free companion of `cRischDEG`. For `f = fnum/fden`,
`g = gnum/gden ∈ α(t)` it returns `some (ynum, yden)` with `y = ynum/yden` solving `Dy + f·y = g`, or `none`.
The base solve inside the cancellation cases is the typeclass `crischDESolve` (through the Part-1 own-loops),
so a *level-`n+1`* call recurses into the *level-`n`* `crischDESolve`. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α] [CFracGcdCoreWf α] [CRischField α]

/-- **★ THE HEADLINE — the generic fuel-free Risch differential equation solver** `cRischDEGWf Dt fnum fden
gnum gden` (Bronstein Ch. 6, assembled): the generic, fuel-free companion of `cRischDEG`. For `f = fnum/fden`,
`g = gnum/gden ∈ α(t)` and the monomial derivation `D = cmonomialDeriv Dt`, returns `some (ynum, yden)` with
`y = ynum/yden ∈ α(t)` solving `Dy + f·y = g`, or `none`. Stages: §6.2 normal denominator
(`cRdeNormalDenominatorGWf`) → §6.2 special denominator (`cRdeSpecialDenominatorGWf`) → §6.3 degree bound
(`cRdeBoundDegreeGWf`) → §6.4 SPDE (`cSPDEGWf`) → §6.5/§6.6 PolyRischDE dispatch (`cPolyRischDEGWf`), with the
polynomial unknown `Q = α'·v + β` reassembled to `y = Q·h₁ / h₀`. The cancellation cases recurse into
`CRischField.crischDESolve` over `α` — at level `n+1` this is the level-`n` oracle. **No fuel at runtime in
any regime**; `native_decide`-able over the noncomputable tower. `[CField α] [CDiffField α]
[CFracGcdCoreWf α] [CRischField α]`-generic — runs at any tower level. (`f` is assumed weakly normalized —
the post-Hermite RDE input; `cWeakNormalizerGWf` returns `q = 1` on such `f`.) -/
def cRischDEGWf (Dt : CPolyG α) (fnum fden gnum gden : CPolyG α) :
    Option (CPolyG α × CPolyG α) :=
  match cRdeNormalDenominatorGWf Dt fnum fden gnum gden with
  | none => none
  | some (a0, b0, c0, h0) =>
    let (a, b, c, h1) := cRdeSpecialDenominatorGWf Dt a0 b0 c0
    let N := cRdeBoundDegreeGWf Dt a b c
    match cSPDEGWf Dt a b c (N : ℤ) with
    | none => none
    | some (bbar, cbar, _m, α', β) =>
      match cPolyRischDEGWf Dt bbar cbar _m with
      | none => none
      | some v =>
        let Q := caddG (cmulG α' v) β
        some (cmulG Q h1, h0)

end CPolyG

/-! ## Part 5 — bridges of the flat-composition pipeline + the headline to the fuel'd `…G` originals

Each flat-composition `…GWf` op mirrors its `…G` original with the fuel dropped, so its bridge is a pure
rewrite threading the per-leaf sub-agreements (every fuel'd sub-op replaced by its fuel-free companion at
sufficient fuel). Following the integration pipeline's pattern (`cIntegrateGWf_eq`, `cLogPartGWf_eq`), the
sub-agreements are taken as **hypotheses** — the fuel bounds they carry live only there; the runtime `…GWf`
carries none. The recursive-bottom agreements (`cValuationGWf`/`cPolyRischDECancel*GWf`/`cSplitFactorFastGWf`/
`cgcdFFCoreWf`) feed in through their own regularity gates. The `cWeakNormalizerGWf` / `cRdeNormalDenominator`
/ `cRdeSpecialDenominator` stage agreements are taken as whole-stage hypotheses (the valuation own-loop
`cValuationGWf` has no standalone bridge, feeding the special-denominator stage instead). -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

omit [CDiffField α] in
/-- **Bridge — `cExpEtaGWf` equals `cExpEtaG`.** Both read the degree-0 coefficient of the same fuel-free
quotient `Dt / t`. -/
theorem cExpEtaGWf_eq (Dt : CPolyG α) (fuel : ℕ) :
    cExpEtaGWf Dt = cExpEtaG fuel Dt := by
  rw [cExpEtaGWf, cExpEtaG]

omit [CDiffField α] in
/-- **Bridge — `cRdeBoundDegreeGWf` equals `cRdeBoundDegreeG` at any fuel** (definitional). Both are the same
pure list-degree arithmetic (`cRdeBoundDegreeG` ignores its fuel argument), so they coincide unconditionally
— `cRdeBoundDegreeGWf Dt a b c = cRdeBoundDegreeG Dt fuel a b c`. -/
theorem cRdeBoundDegreeGWf_eq (Dt : CPolyG α) (fuel : ℕ) (a b c : CPolyG α) :
    cRdeBoundDegreeGWf Dt a b c = cRdeBoundDegreeG Dt fuel a b c := by
  rw [cRdeBoundDegreeGWf, cRdeBoundDegreeG]

omit [CDiffField α] in
/-- **Bridge — `cIntegratePolyGWf` equals `cIntegratePolyG`** (definitional). Both are the same termwise
antiderivative (neither carries fuel), so `cIntegratePolyGWf c = cIntegratePolyG c`. -/
theorem cIntegratePolyGWf_eq (c : CPolyG α) : cIntegratePolyGWf c = cIntegratePolyG c := by
  rw [cIntegratePolyGWf, cIntegratePolyG]

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CRischField α]

/-- **Bridge — `cPolyRischDEGWf` equals `cPolyRischDEG` at any sufficient fuel** (composition). The two
dispatchers share the same case-split on `deg(b)` vs `max(0, δ−1)`, the monomial type, and the `b = 0`
integration branch; given the per-branch own-loop agreements (`hnocancel`: the non-cancellation loop;
`hprim`: the primitive cancellation loop; `hexp`: the hyperexponential cancellation loop), and noting the
`b = 0` branch agrees definitionally (`cIntegratePolyGWf_eq`), they agree. A pure case-split rewrite. -/
theorem cPolyRischDEGWf_eq (Dt : CPolyG α) (fuel : ℕ) (b c : CPolyG α) (n : ℤ)
    (hnocancel : cPolyRischDENoCancelGWf Dt b c n = cPolyRischDENoCancelG Dt fuel b c n)
    (hprim : cPolyRischDECancelPrimGWf Dt b c n = cPolyRischDECancelPrimG Dt fuel b c n)
    (hexp : cPolyRischDECancelExpGWf Dt b c n = cPolyRischDECancelExpG Dt fuel b c n) :
    cPolyRischDEGWf Dt b c n = cPolyRischDEG Dt fuel b c n := by
  rw [cPolyRischDEGWf, cPolyRischDEG]
  by_cases hb : cisZeroG b = true
  · simp only [hb, if_true, cIntegratePolyGWf_eq]
  · simp only [hb, Bool.false_eq_true, if_false]
    by_cases h1 : (cdegG b : ℤ) > max 0 ((cdegG Dt : ℤ) - 1)
    · rw [if_pos h1, if_pos h1, hnocancel]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : (cdegG Dt : ℤ) = 0 ∧ (cdegG b : ℤ) = 0
      · rw [if_pos h2, if_pos h2, hprim]
      · rw [if_neg h2, if_neg h2]
        by_cases h3 : (cdegG Dt : ℤ) = 1 ∧ (cdegG b : ℤ) = 0
        · rw [if_pos h3, if_pos h3, hexp]
        · rw [if_neg h3, if_neg h3, hnocancel]

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCore α] [CFracGcdCoreWf α] [CRischField α]

/-- **★ Bridge — the headline `cRischDEGWf` equals `cRischDEG` at sufficient fuel on any regular run**
(transparent composition, all regimes). From the §6.2 stage agreements (`hnorm`: the normal denominator;
`hspec`: the special denominator on the normal-denominator output), the §6.3 degree bound
(`cRdeBoundDegreeGWf_eq`, already fuel-free), the §6.4 SPDE bridge (`hspde`), and the §6.5/§6.6 polynomial
**dispatcher** agreement (`hpoly`: `cPolyRischDEGWf = cPolyRischDEG fuel` on the SPDE output) —
`cRischDEGWf Dt fnum fden gnum gden = cRischDEG Dt fuel fnum fden gnum gden`. The fuel bounds live only in the
hypotheses; the headline `cRischDEGWf` carries none. A pure composition rewrite: rewrite each stage to its
fuel'd form and the two drivers collapse. -/
theorem cRischDEGWf_eq (Dt : CPolyG α) (fuel : ℕ) (fnum fden gnum gden : CPolyG α)
    (hnorm : cRdeNormalDenominatorGWf Dt fnum fden gnum gden
      = cRdeNormalDenominatorG Dt fuel fnum fden gnum gden)
    (hspec : ∀ a0 b0 c0, cRdeSpecialDenominatorGWf Dt a0 b0 c0
      = cRdeSpecialDenominatorG Dt fuel a0 b0 c0)
    (hspde : ∀ a b c n, cSPDEGWf Dt a b c n = cSPDEG Dt fuel a b c n)
    (hpoly : ∀ bbar cbar (m : ℤ), cPolyRischDEGWf Dt bbar cbar m = cPolyRischDEG Dt fuel bbar cbar m) :
    cRischDEGWf Dt fnum fden gnum gden = cRischDEG Dt fuel fnum fden gnum gden := by
  rw [cRischDEGWf, cRischDEG, hnorm]
  rcases hn : cRdeNormalDenominatorG Dt fuel fnum fden gnum gden with _ | ⟨a0, b0, c0, h0⟩
  · rfl
  · simp only []
    rw [hspec a0 b0 c0]
    rcases hs : cRdeSpecialDenominatorG Dt fuel a0 b0 c0 with ⟨a, b, c, h1⟩
    simp only [cRdeBoundDegreeGWf_eq Dt fuel a b c,
      hspde a b c (cRdeBoundDegreeG Dt fuel a b c : ℤ)]
    rcases hsp : cSPDEG Dt fuel a b c (cRdeBoundDegreeG Dt fuel a b c : ℤ) with
      _ | ⟨bbar, cbar, m, α', β⟩
    · rfl
    · simp only [hpoly bbar cbar m]
      rcases hpr : cPolyRischDEG Dt fuel bbar cbar m with _ | v <;> rfl

end CPolyG

/-! ## Part 6 — ★ `native_decide` smoke test: the headline `cRischDEGWf` computes fuel-free

The deliverable: the generic fuel-free RDE oracle `cRischDEGWf` *runs in native code* over the tower. We solve
a small Risch differential equation over `CPolyG (QFunNZG ℚ) = ℚ(x)[t₁]` with the primitive monomial `t₁`
(`Dt₁ = [1]`, `D(t₁) = 1`): `Dy + 0·y = 1` (`f = 0/1`, `g = 1/1`), whose solution is `y = t₁`. The fuel-free
oracle — normal denominator → special denominator → degree bound → SPDE → the §6.5/§6.6 dispatch (here the
`b = 0` primitive-integration branch) — returns `some (ynum, yden)` with **no fuel at runtime**, and the
returned `y = ynum/yden` is verified to **actually solve** the equation by the cleared polynomial identity
`gden·fden·(D(ynum)·yden − ynum·D(yden)) + gden·fnum·ynum·yden = gnum·fden·yden²` reading to `0`
(`cisZeroG`, the generic analogue of `rdeClearedCheck`, not merely pinning the output). Everything stays
`[CField …]`/`[CDiffField …]`/`[CFracGcdCoreWf …]`/`[CRischField …]`-computable with `Prop`-erased subtype
proofs, so nothing noncomputable reaches the native compiler — `native_decide` reduces, the oracle genuinely
running the fuel-free §6 pipeline over ℚ(x)[t₁]. -/

open CPolyG in
/-- The level-1 monomial derivative `Dt₁ = 1` over `CPolyG (QFunNZG ℚ) = ℚ(x)[t₁]` (`t₁` primitive). -/
def towerRdeGWfDt : CPolyG (QFunNZG ℚ) := [CField.one]

open CPolyG in
/-- **★ The generic fuel-free RDE oracle `cRischDEGWf` solves `Dy = 1` over ℚ(x)(t₁), fuel-free**
(`native_decide`, the smoke-test deliverable). `cRischDEGWf [1] 0 1 1 1` over `CPolyG (QFunNZG ℚ) = ℚ(x)[t₁]`
(monomial `t₁`, `Dt₁ = 1`, primitive) returns `some (ynum, yden)` with **no fuel at runtime**, and the
returned `y = ynum/yden` is verified to **actually solve** `Dy + 0·y = 1` by the cleared polynomial identity
(`= 0` via `cisZeroG`) — the solution `y = t₁`. This certifies the headline generic fuel-free oracle computes
end-to-end over the tower: the §6 pipeline (down to the `b = 0` integration branch of `cPolyRischDEGWf`) runs
fuel-free over ℚ(x)[t₁]. -/
theorem towerRdeGWf_solves_Dy_eq_one :
    (match cRischDEGWf towerRdeGWfDt ([] : CPolyG (QFunNZG ℚ)) [CField.one] [CField.one] [CField.one] with
      | some (ynum, yden) =>
          let Dyn := cmonomialDeriv towerRdeGWfDt ynum
          let Dyd := cmonomialDeriv towerRdeGWfDt yden
          let fnum : CPolyG (QFunNZG ℚ) := []
          let fden : CPolyG (QFunNZG ℚ) := [CField.one]
          let gnum : CPolyG (QFunNZG ℚ) := [CField.one]
          let gden : CPolyG (QFunNZG ℚ) := [CField.one]
          let lhs := caddG
            (cmulG (cmulG gden fden) (csubG (cmulG Dyn yden) (cmulG ynum Dyd)))
            (cmulG (cmulG (cmulG gden fnum) ynum) yden)
          let rhs := cmulG (cmulG gnum fden) (cmulG yden yden)
          cisZeroG (csubG lhs rhs)
      | none => false) = true := by native_decide

-- The headline fuel-free RDE-oracle bridge carries only the standard axioms (no fuel, no `sorry`);
-- the `native_decide` smoke test carries `Lean.ofReduceBool` separately.
#print axioms CPolyG.cRischDEGWf_eq
#print axioms towerRdeGWf_solves_Dy_eq_one

end DeepWiki.SymbolicIntegration
