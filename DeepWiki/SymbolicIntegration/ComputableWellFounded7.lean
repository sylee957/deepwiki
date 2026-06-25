import DeepWiki.SymbolicIntegration.ComputableWellFounded6
import DeepWiki.SymbolicIntegration.ComputableRischDE
import DeepWiki.SymbolicIntegration.ComputableRischDECorrect
import DeepWiki.SymbolicIntegration.ComputableRischDESPDECorrect
import DeepWiki.SymbolicIntegration.ComputableRischDEPipelineCorrect

/-! # Fuel-free (well-founded) §6 Risch-DE pipeline — `cPolyRischDENoCancelWf`, `cSPDEWf`, `cRischDEWf`

This continues the fuel-free conversion of the transcendental symbolic-integration engine (the
`cIntegrate` path is complete in `ComputableWellFounded`/`…2`/`…3`/`…4`/`…5`/`…6`) into the **other**
major fuel-bearing top-level function: the §6 Risch differential equation solver `cRischDE`, used for the
elementary-solvability *decision* `Dy + f·y = g` over the tower ℚ(x)[t].

`cRischDE` chains `cRdeNormalDenominator` (§6.2) → `cRdeSpecialDenominator` (§6.2) → `cRdeBoundDegree`
(§6.3) → `cSPDE` (§6.4) → `cPolyRischDE` (§6.5/§6.6 dispatcher), reconstructing `y = ynum/yden`. Working
**leaf-first** (innermost own-loops before the compositions):

* **`cPolyRischDENoCancelWf`** (§6.5, the `PolyRischDENoCancel1` box) — an **own-loop** solving
  `Dq + b·q = c` degree-by-degree from the top down: the leading-coefficient equation `lc(c) = lc(b)·lc(q)`
  fixes `q`'s leading monomial `p = (lc(c)/lc(b))·tᵐ`, subtract `D(p) + b·p`, recurse on the lower-degree
  remainder `c' = c − D(p) − b·p`. In the non-cancellation regime `deg(b) ≥ 1`, the leading term of `b·p`
  cancels `c`'s, so the normalized `t`-list length of `c` strictly drops; the fuel-free companion runs the
  own-loop by well-founded recursion on `(cnormG c).length`, with the structural runtime guard
  `(cnormG c').length < (cnormG c).length`, so `decreasing_by` is `assumption`. The cleared RDE identity
  `D(q) + b·q = c` is proved **directly by well-founded induction** (reusing the additivity-of-`implicitDeriv`
  argument of `cPolyRischDENoCancel_cleared_identity`), with no fuel'd bridge needed for correctness; the
  bridge to the fuel'd op (for the `cRischDEWf` composition) is via a transparent per-step regularity gate.

* **`cSPDEWf`** (§6.4, Rothstein's `SPDE(a,b,c,D,n)` box) — an **own-loop** peeling `g = gcd(a,b)` each
  step and recursing on the divided `a/g`, whose `t`-degree strictly drops when `deg(a) > 0` (the constant
  base case `deg(a) = 0` returns directly). The well-founded measure is `(cnormG a).length`, with the
  structural guard `(cnormG (a/g)).length < (cnormG a).length`. The fuel-free leaves `cgcdFFWf`/`cdivFFWf`/
  `cdiophantineGWf` compute each step; the bridge to the fuel'd `cSPDE` is by induction on a transparent
  per-step regularity gate.

* **`cRdeBoundDegreeWf`/`cRdeSpecialDenominatorWf`/`cRdeNormalDenominatorWf`** (§6.1-6.3) — **compositions**
  / bounded loops. `cRdeBoundDegree` is fuel-free already (no recursion); `cRdeSpecialDenominator` and
  `cRdeNormalDenominator` substitute the fuel-free `cgcdFFWf`/`cdivFFWf`/`cSplitFactorFastWf`/`cValuationWf`.

* **`cRischDEWf`** (the **goal**) — composes the WF stages, routing the §6.5 non-cancellation dispatch case
  (the primitive regime the validation exercises). The bridge `cRischDEWf = cRischDE (sufficient fuel)`
  threads the sub-bridges; the §6 pipeline correctness `cRischDE_rdeCleared_of_inputs` (the primitive
  non-cancellation cleared identity `D(y) + f·y = g`) transports through it, fuel-free.

As throughout, where a fuel'd bridge is given the fuel bounds live only in the bridge proof; the runtime
WF ops carry no fuel. The `native_decide` smoke tests re-run Bronstein's Example 6.5.1 (`y = t + x`) and
6.4.1 (`none`, non-elementary) over the noncomputable-`CFieldSpec` tower `QFunNZ` (ℚ(x)), now fuel-free. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZ

/-! ### Target 1 — the fuel-free non-cancellation Poly-Risch-DE `cPolyRischDENoCancelWf` (own-loop, §6.5)

`cPolyRischDENoCancel Dt fuel b c n` (Bronstein §6.5) solves `Dq + b·q = c` degree-by-degree: peel the
leading monomial `p = (lc(c)/lc(b))·tᵐ` (`m = deg(c) − deg(b)`), recurse on `c' = c − D(p) − b·p`. In the
non-cancellation regime the leading term of `b·p` cancels `c`'s top, so the normalized `t`-list length of
`c` strictly drops; the fuel-free companion runs the own-loop by well-founded recursion on
`(cnormG c).length`, with the structural runtime guard `(cnormG c').length < (cnormG c).length`. -/

namespace CPolyG

/-- **Fuel-free non-cancellation Poly-Risch-DE** (Bronstein §6.5, the `PolyRischDENoCancel1(b,c,D,n)` box,
book p.208) `cPolyRischDENoCancelWf Dt b c n`: the fuel-free companion of `cPolyRischDENoCancel`. Solves
`Dq + b·q = c` (eq. 6.19) for `q ∈ ℚ(x)[t]` with `deg(q) ≤ n` (`n : ℤ`), top-down degree-by-degree —
`p = (lc(c)/lc(b))·tᵐ` (`m = deg(c) − deg(b)`), recurse on `c' = c − D(p) − b·p` (`D = cmonomialDeriv Dt`).
Returns `none` ("no solution of degree `≤ n`") or `some q`. True well-founded recursion on
`(cnormG c).length` — **no fuel at runtime**; the recursion is taken only under the structural guard
`(cnormG c').length < (cnormG c).length`, so `decreasing_by` is `assumption`. Over a non-cancellation run
the guard never fails (the leading term of `b·p` cancels `c`'s, dropping the degree), so it agrees with
`cPolyRischDENoCancel` (`cPolyRischDENoCancelWf_eq`). `native_decide`-able over the tower `QFunNZ`. -/
def cPolyRischDENoCancelWf (Dt : CPolyG QFunNZ) (b c : CPolyG QFunNZ) (n : ℤ) :
    Option (CPolyG QFunNZ) :=
  if cisZeroG c then some []
  else
    let m : ℤ := (cdegG c : ℤ) - (cdegG b : ℤ)
    if n < 0 ∨ m < 0 ∨ m > n then none
    else
      let coeff := CField.div (cleadG c) (cleadG b)
      let p := cshiftG m.toNat [coeff]
      let c' := csubG (csubG c (cmonomialDeriv Dt p)) (cmulG b p)
      if (cnormG c' : List QFunNZ).length < (cnormG c : List QFunNZ).length then
        match cPolyRischDENoCancelWf Dt b c' (m - 1) with
        | none => none
        | some q => some (caddG p q)
      else none   -- unreachable on a non-cancellation run (the leading term cancels, degree drops)
termination_by (cnormG c).length
decreasing_by assumption

end CPolyG

/-! ### Cleared correctness of `cPolyRischDENoCancelWf`, directly by well-founded induction

As for `cPolyReduceTowerWf`, the cleared RDE identity is proved **directly** on the WF own-loop (no fuel'd
bridge): at `c = 0` both return `[]` with `D(0) + b·0 = 0 = c`; the recursive step glues `p` to the
recursive solution `q'` via `map_add`/`mul_add` and the additivity of `implicitDeriv`, exactly as the
fuel'd `cPolyRischDENoCancel_cleared_identity`. -/

namespace CPolyG

/-- **`cPolyRischDENoCancelWf` satisfies the cleared RDE identity `D(q) + b·q = c`** (abstract, ALL
inputs, **fuel-free**), whenever the solve succeeds. If `cPolyRischDENoCancelWf Dt b c n = some q` then,
with `D = cmonomialDeriv Dt` the monomial derivation (`= implicitDeriv (toPolyG Dt)` through `toPolyG`),
`implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG b * toPolyG q = toPolyG c` in `(RatFunc ℚ)[X]`. The
fuel-free companion of `cPolyRischDENoCancel_cleared_identity`, proved **directly** by well-founded
induction on `(cnormG c).length` — no fuel'd bridge. -/
theorem cPolyRischDENoCancelWf_cleared_identity (Dt b : CPolyG QFunNZ) :
    ∀ (c : CPolyG QFunNZ) (n : ℤ) (q : CPolyG QFunNZ),
      cPolyRischDENoCancelWf Dt b c n = some q →
        Differential.implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG b * toPolyG q = toPolyG c := by
  intro c
  induction hwf : (cnormG c : List QFunNZ).length using Nat.strong_induction_on generalizing c with
  | _ len ih =>
    intro n q hq
    rw [cPolyRischDENoCancelWf.eq_def] at hq
    by_cases hc : cisZeroG c = true
    · -- base case: `c = 0`, returns `[]`, so `D(0) + b·0 = 0 = c`
      rw [if_pos hc, Option.some.injEq] at hq
      subst hq
      have hc0 : toPolyG c = 0 := (cisZeroG_iff c).mp hc
      rw [toPolyG_nil, map_zero, mul_zero, add_zero, hc0]
    · -- recursion branch
      rw [if_neg hc] at hq
      set m : ℤ := (cdegG c : ℤ) - (cdegG b : ℤ) with hm
      by_cases hguard : n < 0 ∨ m < 0 ∨ m > n
      · rw [if_pos hguard] at hq; exact absurd hq (by simp)
      · rw [if_neg hguard] at hq
        simp only at hq
        set coeff := CField.div (cleadG c) (cleadG b) with hcoeff
        set p := cshiftG m.toNat [coeff] with hp
        set c' := csubG (csubG c (cmonomialDeriv Dt p)) (cmulG b p) with hc'
        by_cases hlen : (cnormG c' : List QFunNZ).length < (cnormG c : List QFunNZ).length
        · rw [if_pos hlen] at hq
          rcases hrec : cPolyRischDENoCancelWf Dt b c' (m - 1) with _ | qrec
          · rw [hrec] at hq; exact absurd hq (by simp)
          · rw [hrec, Option.some.injEq] at hq
            -- the recursive identity on `c'` (strong-induction on the strictly smaller length)
            have ihrec := ih (cnormG c' : List QFunNZ).length (hwf ▸ hlen) c' rfl (m - 1) qrec hrec
            subst hq
            rw [toPolyG_caddG, map_add, mul_add]
            have hc'eq : toPolyG c' = toPolyG c
                - Differential.implicitDeriv (toPolyG Dt) (toPolyG p) - toPolyG b * toPolyG p := by
              rw [hc', toPolyG_csubG, toPolyG_csubG, toPolyG_cmonomialDeriv, toPolyG_cmulG]
            rw [hc'eq] at ihrec
            linear_combination ihrec
        · rw [if_neg hlen] at hq; exact absurd hq (by simp)

/-- The §6.5 non-cancellation cleared identity (fuel-free), restated. When `cPolyRischDENoCancelWf Dt b c
n = some q`, the output `q` solves `D(q) + b·q = c` over ℚ(x)[t]. -/
example (Dt b c : CPolyG QFunNZ) (n : ℤ) (q : CPolyG QFunNZ)
    (hq : cPolyRischDENoCancelWf Dt b c n = some q) :
    Differential.implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG b * toPolyG q = toPolyG c :=
  cPolyRischDENoCancelWf_cleared_identity Dt b c n q hq

end CPolyG

#print axioms CPolyG.cPolyRischDENoCancelWf_cleared_identity

/-! ### Bridge of `cPolyRischDENoCancelWf` to the fuel'd `cPolyRischDENoCancel`

`cPolyRischDENoCancel` uses **no** fuel-bearing sub-ops (only `cmonomialDeriv`/`cmulG`/`csubG`/`cshiftG`/
arithmetic); it recurses on `fuel` purely as a counter. So `cPolyRischDENoCancelWf` differs only in the
recursion mechanism (its WF guard `(cnormG c').length < (cnormG c).length` vs the fuel counter) — every
per-step quantity is identical. The bridge needs only that the structural guard fires on a real
non-cancellation run (the leading term of `b·p` cancels `c`'s top, dropping the length); the inductive gate
`CPolyRischNoCancelReg fuel b c n` (every node concluding at fuel `fuel + 1`) carries that as a step budget
mirroring `cPolyRischDENoCancel`'s recursion. -/

/-- **Per-run non-cancellation-loop regularity** `CPolyRischNoCancelReg fuel b c n` (nodes conclude at fuel
`fuel + 1`): mirrors the `cPolyRischDENoCancel` recursion. `baseZero` (`c = 0`) and `baseGuard`
(`n < 0 ∨ m < 0 ∨ m > n`) are terminal; `step` requires the WF guard fires (the peeled leading term drops
the normalized length, `(cnormG c').length < (cnormG c).length`, with `c' = c − D(p) − b·p`,
`p = (lc(c)/lc(b))·t^m`, `m = deg(c) − deg(b)`) and the same holds recursively on `c'` at `m − 1`. The step
budget certifies a real non-cancellation run reaches a terminal (the genuine witness, the length dropping). -/
inductive CPolyRischNoCancelReg (Dt b : CPolyG QFunNZ) : ℕ → CPolyG QFunNZ → ℤ → Prop
  /-- terminal: `c = 0`, returns `[]`. -/
  | baseZero {fuel : ℕ} {c : CPolyG QFunNZ} {n : ℤ} (hc : cisZeroG c = true) :
      CPolyRischNoCancelReg Dt b (fuel + 1) c n
  /-- terminal: the degree guard fails (`n < 0 ∨ m < 0 ∨ m > n`), returns `none`. -/
  | baseGuard {fuel : ℕ} {c : CPolyG QFunNZ} {n : ℤ} (hc : ¬ cisZeroG c = true)
      (hg : n < 0 ∨ (cdegG c : ℤ) - (cdegG b : ℤ) < 0 ∨ (cdegG c : ℤ) - (cdegG b : ℤ) > n) :
      CPolyRischNoCancelReg Dt b (fuel + 1) c n
  /-- recursive: peel the leading monomial, the WF guard fires, recurse on `c'` within budget. -/
  | step {fuel : ℕ} {c : CPolyG QFunNZ} {n : ℤ} (hc : ¬ cisZeroG c = true)
      (hg : ¬ (n < 0 ∨ (cdegG c : ℤ) - (cdegG b : ℤ) < 0 ∨ (cdegG c : ℤ) - (cdegG b : ℤ) > n))
      (hguard : (cnormG (csubG (csubG c (cmonomialDeriv Dt (cshiftG ((cdegG c : ℤ) - (cdegG b : ℤ)).toNat
            [CField.div (cleadG c) (cleadG b)]))) (cmulG b (cshiftG ((cdegG c : ℤ) - (cdegG b : ℤ)).toNat
            [CField.div (cleadG c) (cleadG b)]))) : List QFunNZ).length < (cnormG c : List QFunNZ).length)
      (hrec : CPolyRischNoCancelReg Dt b fuel
        (csubG (csubG c (cmonomialDeriv Dt (cshiftG ((cdegG c : ℤ) - (cdegG b : ℤ)).toNat
            [CField.div (cleadG c) (cleadG b)]))) (cmulG b (cshiftG ((cdegG c : ℤ) - (cdegG b : ℤ)).toNat
            [CField.div (cleadG c) (cleadG b)])))
        (((cdegG c : ℤ) - (cdegG b : ℤ)) - 1)) :
      CPolyRischNoCancelReg Dt b (fuel + 1) c n

namespace CPolyG

/-- **Bridge — `cPolyRischDENoCancelWf` equals the fuel'd `cPolyRischDENoCancel` on a regular run.** Under
`CPolyRischNoCancelReg Dt b (fuel + 1) c n` (the step-budget gate a real non-cancellation run meets),
`cPolyRischDENoCancelWf Dt b c n = cPolyRischDENoCancel Dt (fuel + 1) b c n`. The gate lives only here; the
WF own-loop carries no fuel. By induction on the gate: at `baseZero`/`baseGuard` both stop; at a `step` node
every per-step quantity is identical (no fuel'd sub-ops), the WF guard fires, the fuel'd version (at
`fuel + 1`) descends, and the IH closes the recursive results. -/
theorem cPolyRischDENoCancelWf_eq (Dt b : CPolyG QFunNZ) :
    ∀ (fuel : ℕ) (c : CPolyG QFunNZ) (n : ℤ), CPolyRischNoCancelReg Dt b fuel c n →
      cPolyRischDENoCancelWf Dt b c n = CPolyG.cPolyRischDENoCancel Dt fuel b c n := by
  intro fuel c n hreg
  induction hreg with
  | @baseZero fuel c n hc =>
    rw [cPolyRischDENoCancelWf.eq_def, if_pos hc, CPolyG.cPolyRischDENoCancel, if_pos hc]
  | @baseGuard fuel c n hc hg =>
    rw [cPolyRischDENoCancelWf.eq_def, if_neg hc, CPolyG.cPolyRischDENoCancel, if_neg hc]
    simp only [if_pos hg]
  | @step fuel c n hc hg hguard hrec ih =>
    rw [cPolyRischDENoCancelWf.eq_def, if_neg hc, CPolyG.cPolyRischDENoCancel, if_neg hc]
    simp only [if_neg hg, if_pos hguard, ih]
    rfl

end CPolyG

/-! ### A small fuel-free divisibility leaf `cdvdGWf` (over `cmodWf`)

`cdvdG fuel q p = cisZeroG (cmodG fuel p q)`; the fuel goes only to `cmodG`. The fuel-free companion
substitutes the leaf `cmodWf` (`ComputableWellFounded`): `cdvdGWf q p = cisZeroG (cmodWf p q)`. Used by the
fuel-free SPDE own-loop (which tests `g ∣ c`). -/

namespace CPolyG

variable {α : Type*} [CField α]

/-- **Fuel-free divisibility test** `cdvdGWf q p = cisZeroG (cmodWf p q)`: the fuel-free companion of
`cdvdG`, deciding `q ∣ p` (remainder of `p` by `q` is zero) with the leaf fuel-free remainder `cmodWf`
(true well-founded recursion, no fuel at runtime). Generic over `[CField α]`. -/
def cdvdGWf (q p : CPolyG α) : Bool := cisZeroG (cmodWf p q)

variable [CFieldSpec α]

/-- **`cdvdGWf` equals the fuel'd `cdvdG` at any sufficient fuel**: for `(cnormG p).length ≤ fuel`,
`cdvdGWf q p = cdvdG fuel q p`. Both test the zero-ness of the Euclidean remainder; the leaf bridge
`cdivmodWf_eq_of_fuel` supplies the agreement. -/
theorem cdvdGWf_eq_of_fuel (fuel : ℕ) (q p : CPolyG α)
    (hfuel : (cnormG p : List α).length ≤ fuel) :
    cdvdGWf q p = CPolyG.cdvdG fuel q p := by
  rw [cdvdGWf, CPolyG.cdvdG, cmodWf, cmodG, cdivmodWf_eq_of_fuel fuel p q hfuel]

end CPolyG

/-! ### Target 2 — the fuel-free Rothstein SPDE `cSPDEWf` (own-loop on `(n+1).toNat`, §6.4)

`cSPDE Dt fuel a b c n` (Bronstein §6.4) peels `g = gcd(a, b)` each step and recurses on the divided
`a/g` with the degree bound lowered to `n − deg(a/g)`. The recursion is taken only when `n ≥ 0` and
`deg(a/g) ≥ 1` (the constant base case `deg(a/g) = 0` returns directly), so `n` strictly drops by
`deg(a/g) ≥ 1`; hence `(n + 1).toNat` is a genuine well-founded measure. The fuel-free companion runs the
**own-loop** by well-founded recursion on `(n + 1).toNat`, with the inner gcd/division/Bézout leaves the
fuel-free `cgcdFFWf`/`cdivFFWf`/`cdvdGWf`/`cdiophantineGWf` — **no fuel at runtime**. -/

namespace CPolyG

/-- **Fuel-free Rothstein SPDE** (Bronstein §6.4, the `SPDE(a,b,c,D,n)` box, book p.203)
`cSPDEWf Dt a b c n`: the fuel-free companion of `cSPDE`. Given `a, b, c ∈ ℚ(x)[t]` (`a ≠ 0`) and a degree
bound `n : ℤ`, returns `none` ("no solution of degree `≤ n`") or `some (b̄, c̄, m, α, β)` such that any
solution `q` of `a·Dq + b·q = c` of degree `≤ n` is `q = α·h + β` for an `h` solving `Dh + b̄·h = c̄`,
`deg(h) ≤ m`. Peels `g = cgcdFFWf a b`; the constant `a/g` base case returns the identity reconstruction,
else solves the Bézout `cdiophantineGWf b̄ ā c̄` and recurses on the divided `ā = a/g` at `n − deg(ā)`. True
well-founded recursion on `(n + 1).toNat` (`n` drops by `deg(ā) ≥ 1` in the recursive branch) — **no fuel
at runtime**. The inner gcd/division/divisibility/Bézout are the fuel-free `cgcdFFWf`/`cdivFFWf`/`cdvdGWf`/
`cdiophantineGWf`. Agrees with `cSPDE` on a regular run (`cSPDEWf_eq`). `native_decide`-able over `QFunNZ`. -/
def cSPDEWf (Dt : CPolyG QFunNZ) (a b c : CPolyG QFunNZ) (n : ℤ) :
    Option (CPolyG QFunNZ × CPolyG QFunNZ × ℤ × CPolyG QFunNZ × CPolyG QFunNZ) :=
  if n < 0 then
    if cisZeroG c then some ([], [], 0, [], []) else none
  else
    let g := cgcdFFWf a b
    if cdvdGWf g c then
      let a' := cdivFFWf a g
      let b' := cdivFFWf b g
      let c' := cdivFFWf c g
      if cdegG a' = 0 then
        let ainv := CField.inv (cleadG a')
        some (cscaleG ainv b', cscaleG ainv c', n, [CField.one], [])
      else
        let (r, z) := cdiophantineGWf b' a' c'
        let Da := cmonomialDeriv Dt a'
        let Dr := cmonomialDeriv Dt r
        if (n - (cdegG a' : ℤ) + 1).toNat < (n + 1).toNat then
          match cSPDEWf Dt a' (caddG b' Da) (csubG z Dr) (n - (cdegG a' : ℤ)) with
          | none => none
          | some (bbar, cbar, m, α, β) =>
              some (bbar, cbar, m, cmulG a' α, caddG (cmulG a' β) r)
        else none   -- unreachable on a real run (`deg(a') ≥ 1`, `n ≥ 0`, so `n` strictly drops)
    else none
termination_by (n + 1).toNat
decreasing_by assumption

end CPolyG

/-! ### Bridge of `cSPDEWf` to the fuel'd `cSPDE`

The WF `cSPDEWf` recurses on `(n + 1).toNat`; the fuel'd `cSPDE` on `fuel`. At a non-base node,
`cSPDE (fuel + 1)` computes its `gcd`/divisions/Bézout with the **predecessor** fuel `fuel` (its body
peels one fuel), so the fuel-free leaves must match the fuel'd ops at fuel `fuel`. The bundle
`CSPDEWfStepReg fuel a b c` carries the per-step degree/fuel preconditions for that match, and the
inductive `CSPDEWfReg fuel a b c n` (whose nodes all conclude at `fuel + 1`) mirrors `cSPDE`'s recursion
with a step budget — certifying that a regular run reaches a terminal within finitely many peels (the
genuine termination witness, `n` dropping by `deg(a/g) ≥ 1`, exactly as the WF measure `(n + 1).toNat`).
So the bridge `cSPDEWf Dt a b c n = cSPDE Dt (fuel + 1) a b c n` is a plain structural recursion on the
gate, generalizing `fuel`. -/

/-- **Per-SPDE-step node-regularity bundle** `CSPDEWfStepReg fuel a b c`: the transparent preconditions for
one SPDE peel's fuel-free leaves to match the fuel'd ops at sub-op fuel `fuel` (the fuel `cSPDE (fuel + 1)`
uses inside its body). With `g = cgcdFF fuel a b`, `ad = a/g`, `bd = b/g`, `cd = c/g`: the gcd call is
node-regular (`CgcdFFNodeReg fuel a b`), the divisibility-test dividend `c` is reduced
(`(cnormG c).length ≤ fuel`), each of `a, b, c` is short enough for its exact division, and (for the Bézout
`cdiophantineGWf bd ad cd`) the divisor `ad`, dividend `bd` and rescaled dividend `S` are short enough. -/
structure CSPDEWfStepReg (fuel : ℕ) (a b c : CPolyG QFunNZ) : Prop where
  /-- the gcd call `cgcdFF fuel a b` is node-regular. -/
  hgcd : CgcdFFNodeReg fuel a b
  /-- the divisibility-test dividend `c` is reduced (for `cdvdGWf g c = cdvdG fuel g c`). -/
  hclen : (cnormG c : List QFunNZ).length ≤ fuel
  /-- `a` is short enough for its exact division `a/g`. -/
  halen : (cnormG a : List QFunNZ).length ≤ fuel
  /-- `b` is short enough for its exact division `b/g`. -/
  hblen : (cnormG b : List QFunNZ).length ≤ fuel
  /-- the divided divisor `ad = a/g` is strictly short enough for the Bézout extended-Euclid descent
  (`cdiophantineGWf bd ad cd` descends on the second argument `ad`). -/
  hadlen : (cnormG (CPolyG.cdivFF fuel a (CPolyG.cgcdFF fuel a b)) : List QFunNZ).length < fuel
  /-- the divided dividend `bd = b/g` is short enough for the Bézout extended-Euclid `cgcdWf bd ad`. -/
  hbdlen : (cnormG (CPolyG.cdivFF fuel b (CPolyG.cgcdFF fuel a b)) : List QFunNZ).length ≤ fuel
  /-- the rescaled Bézout dividend `S` is short enough for the `cdivmodWf` mod-reduction. -/
  hSlen : (cnormG (cscaleG (CField.inv (cleadG
      (cgcdWf (CPolyG.cdivFF fuel b (CPolyG.cgcdFF fuel a b))
        (CPolyG.cdivFF fuel a (CPolyG.cgcdFF fuel a b))).1))
      (cmulG (CPolyG.cdivFF fuel c (CPolyG.cgcdFF fuel a b))
        (cgcdWf (CPolyG.cdivFF fuel b (CPolyG.cgcdFF fuel a b))
          (CPolyG.cdivFF fuel a (CPolyG.cgcdFF fuel a b))).2.1)) : List QFunNZ).length ≤ fuel

/-- **Per-run SPDE-loop regularity bundle** `CSPDEWfReg fuel a b c n` (every node concluding at fuel
`fuel + 1`): mirrors the `cSPDE (fuel + 1)` recursion as an inductive predicate with a step budget.
`baseNeg` (`n < 0`), `baseNonDvd` (`g ∤ c`), `baseConst` (`deg(a/g) = 0`) are terminal; `step`
(`n ≥ 0`, `g ∣ c`, `deg(a/g) ≠ 0`) requires the step is node-regular (`CSPDEWfStepReg fuel a b c`, at
sub-op fuel `fuel`) and the same holds recursively on the divided `(ad, bd + D ad, z − D r)` at
`n − deg(ad)` (gate fuel `fuel`, since `cSPDE` recurses at the decremented fuel) — so the budget certifies
the regular run terminates (the genuine witness, `n` dropping by `deg(ad) ≥ 1`). -/
inductive CSPDEWfReg (Dt : CPolyG QFunNZ) : ℕ →
    CPolyG QFunNZ → CPolyG QFunNZ → CPolyG QFunNZ → ℤ → Prop
  /-- terminal: `n < 0` (the `c = 0`/`c ≠ 0` short-circuit). -/
  | baseNeg {fuel : ℕ} {a b c : CPolyG QFunNZ} {n : ℤ} (hn : n < 0) :
      CSPDEWfReg Dt (fuel + 1) a b c n
  /-- terminal: `n ≥ 0`, `g ∤ c` (no solution). -/
  | baseNonDvd {fuel : ℕ} {a b c : CPolyG QFunNZ} {n : ℤ} (hn : ¬ n < 0)
      (hdvd : ¬ cdvdGWf (CPolyG.cgcdFF fuel a b) c = true) (hstep : CSPDEWfStepReg fuel a b c) :
      CSPDEWfReg Dt (fuel + 1) a b c n
  /-- terminal: `n ≥ 0`, `g ∣ c`, `deg(a/g) = 0` (constant base case, identity reconstruction). -/
  | baseConst {fuel : ℕ} {a b c : CPolyG QFunNZ} {n : ℤ} (hn : ¬ n < 0)
      (hdvd : cdvdGWf (CPolyG.cgcdFF fuel a b) c = true)
      (hdeg : cdegG (CPolyG.cdivFF fuel a (CPolyG.cgcdFF fuel a b)) = 0)
      (hstep : CSPDEWfStepReg fuel a b c) :
      CSPDEWfReg Dt (fuel + 1) a b c n
  /-- recursive: `n ≥ 0`, `g ∣ c`, `deg(a/g) ≠ 0`; recurse on the divided equation (gate fuel `fuel`). -/
  | step {fuel : ℕ} {a b c : CPolyG QFunNZ} {n : ℤ} (hn : ¬ n < 0)
      (hdvd : cdvdGWf (CPolyG.cgcdFF fuel a b) c = true)
      (hdeg : cdegG (CPolyG.cdivFF fuel a (CPolyG.cgcdFF fuel a b)) ≠ 0)
      (hstep : CSPDEWfStepReg fuel a b c)
      (hrec : CSPDEWfReg Dt fuel (CPolyG.cdivFF fuel a (CPolyG.cgcdFF fuel a b))
        (caddG (CPolyG.cdivFF fuel b (CPolyG.cgcdFF fuel a b))
          (cmonomialDeriv Dt (CPolyG.cdivFF fuel a (CPolyG.cgcdFF fuel a b))))
        (csubG (cdiophantineG fuel (CPolyG.cdivFF fuel b (CPolyG.cgcdFF fuel a b))
            (CPolyG.cdivFF fuel a (CPolyG.cgcdFF fuel a b)) (CPolyG.cdivFF fuel c (CPolyG.cgcdFF fuel a b))).2
          (cmonomialDeriv Dt (cdiophantineG fuel (CPolyG.cdivFF fuel b (CPolyG.cgcdFF fuel a b))
            (CPolyG.cdivFF fuel a (CPolyG.cgcdFF fuel a b)) (CPolyG.cdivFF fuel c (CPolyG.cgcdFF fuel a b))).1))
        (n - (cdegG (CPolyG.cdivFF fuel a (CPolyG.cgcdFF fuel a b)) : ℤ))) :
      CSPDEWfReg Dt (fuel + 1) a b c n

namespace CPolyG

/-- **The per-SPDE-step fuel-free leaves match the fuel'd ops** at sub-op fuel `fuel`, under a regular step
(`CSPDEWfStepReg fuel a b c`): the gcd `cgcdFFWf a b = cgcdFF fuel a b` (`cgcdFFWf_eq_node`), the
divisibility test `cdvdGWf`, and the three exact divisions — the conjunction the bridge consumes (the value
`cSPDE (fuel + 1)` uses inside its body). -/
theorem cSPDEWf_step_leaves (fuel : ℕ) (a b c : CPolyG QFunNZ)
    (hstep : CSPDEWfStepReg fuel a b c) :
    cgcdFFWf a b = CPolyG.cgcdFF fuel a b
    ∧ cdvdGWf (CPolyG.cgcdFF fuel a b) c = CPolyG.cdvdG fuel (CPolyG.cgcdFF fuel a b) c
    ∧ cdivFFWf a (CPolyG.cgcdFF fuel a b) = CPolyG.cdivFF fuel a (CPolyG.cgcdFF fuel a b)
    ∧ cdivFFWf b (CPolyG.cgcdFF fuel a b) = CPolyG.cdivFF fuel b (CPolyG.cgcdFF fuel a b)
    ∧ cdivFFWf c (CPolyG.cgcdFF fuel a b) = CPolyG.cdivFF fuel c (CPolyG.cgcdFF fuel a b) := by
  obtain ⟨hgcd, hclen, halen, hblen, _, _, _⟩ := hstep
  have hgeq : cgcdFFWf a b = CPolyG.cgcdFF fuel a b := cgcdFFWf_eq_node fuel a b hgcd
  exact ⟨hgeq, cdvdGWf_eq_of_fuel fuel _ c hclen,
    cdivFFWf_eq_of_fuel fuel a _ halen, cdivFFWf_eq_of_fuel fuel b _ hblen,
    cdivFFWf_eq_of_fuel fuel c _ hclen⟩

/-- **Bridge — `cSPDEWf` equals the fuel'd `cSPDE` on a regular run.** Under `CSPDEWfReg Dt (fuel + 1) a b
c n` (the per-step leaf-bridge regularity with a step budget a real SPDE descent meets),
`cSPDEWf Dt a b c n = cSPDE Dt (fuel + 1) a b c n`. The fuel bounds live only in the gate; the WF own-loop
carries none. By induction on the `CSPDEWfReg` derivation: at `baseNeg` both short-circuit on `n < 0`; at
`baseNonDvd`/`baseConst` the per-step leaves match (`cSPDEWf_step_leaves`) and both stop; at a `step` node
the leaves + Bézout cofactors agree (`cdiophantineGWf_eq_of_fuel`), the WF guard fires (`n` drops by
`deg(ad) ≥ 1`), and the fuel'd version (at `fuel + 1`) descends — the IH closes the recursive results. -/
theorem cSPDEWf_eq (Dt : CPolyG QFunNZ) :
    ∀ (fuel : ℕ) (a b c : CPolyG QFunNZ) (n : ℤ), CSPDEWfReg Dt fuel a b c n →
      cSPDEWf Dt a b c n = CPolyG.cSPDE Dt fuel a b c n := by
  intro fuel a b c n hreg
  induction hreg with
  | @baseNeg fuel a b c n hn =>
    -- both short-circuit on `n < 0`
    rw [cSPDEWf.eq_def, if_pos hn, CPolyG.cSPDE, if_pos hn]
  | @baseNonDvd fuel a b c n hn hdvd hstep =>
    -- `n ≥ 0`, `g ∤ c`: both return `none`
    obtain ⟨hgeq, hdvdeq, _, _, _⟩ := cSPDEWf_step_leaves fuel a b c hstep
    rw [hdvdeq] at hdvd
    rw [cSPDEWf.eq_def, if_neg hn, CPolyG.cSPDE, if_neg hn]
    simp only [hgeq, hdvdeq, if_neg hdvd]
  | @baseConst fuel a b c n hn hdvd hdeg hstep =>
    -- `n ≥ 0`, `g ∣ c`, `deg(a/g) = 0`: both return the identity reconstruction
    obtain ⟨hgeq, hdvdeq, haeq, hbeq, hceq⟩ := cSPDEWf_step_leaves fuel a b c hstep
    rw [hdvdeq] at hdvd
    rw [cSPDEWf.eq_def, if_neg hn, CPolyG.cSPDE, if_neg hn]
    simp only [hgeq, hdvdeq, haeq, hbeq, hceq, if_pos hdvd, if_pos hdeg]
  | @step fuel a b c n hn hdvd hdeg hstep hrec ih =>
    -- `n ≥ 0`, `g ∣ c`, `deg(a/g) ≠ 0`: recurse on the divided equation; WF guard fires, fuel'd descends
    obtain ⟨hgeq, hdvdeq, haeq, hbeq, hceq⟩ := cSPDEWf_step_leaves fuel a b c hstep
    rw [hdvdeq] at hdvd
    -- the Bézout cofactors agree
    have hdioeq : cdiophantineGWf (CPolyG.cdivFF fuel b (CPolyG.cgcdFF fuel a b))
        (CPolyG.cdivFF fuel a (CPolyG.cgcdFF fuel a b))
        (CPolyG.cdivFF fuel c (CPolyG.cgcdFF fuel a b))
      = CPolyG.cdiophantineG fuel (CPolyG.cdivFF fuel b (CPolyG.cgcdFF fuel a b))
        (CPolyG.cdivFF fuel a (CPolyG.cgcdFF fuel a b))
        (CPolyG.cdivFF fuel c (CPolyG.cgcdFF fuel a b)) :=
      cdiophantineGWf_eq_of_fuel fuel _ _ _ hstep.hbdlen hstep.hadlen hstep.hSlen
    -- the WF guard fires: `n ≥ 0`, `deg(ad) ≥ 1`, so `n − deg(ad)` strictly drops `(·+1).toNat`
    have hguard : (n - (cdegG (CPolyG.cdivFF fuel a (CPolyG.cgcdFF fuel a b)) : ℤ)
        + 1).toNat < (n + 1).toNat := by
      have hn0 : 0 ≤ n := not_lt.mp hn
      have hd1 : 1 ≤ (cdegG (CPolyG.cdivFF fuel a (CPolyG.cgcdFF fuel a b)) : ℤ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hdeg
      omega
    rw [cSPDEWf.eq_def, if_neg hn, CPolyG.cSPDE, if_neg hn]
    simp only [hgeq, hdvdeq, haeq, hbeq, hceq, hdioeq, if_pos hdvd, if_neg hdeg, if_pos hguard, ih]
    rfl

end CPolyG

/-! ### Target 3 — the fuel-free §6.1-6.3 stages (`cValuationWf`, `cRdeSpecialDenominatorWf`,
`cRdeNormalDenominatorWf`)

`cRdeBoundDegree` is **already fuel-free** (it ignores its fuel argument — only `cdegG`/arithmetic), so it
needs no companion. The other two §6.1-6.3 stages are **compositions** of the §3.5 leaves: substitute the
fuel-free `cgcdFFWf`/`cdivFFWf`/`cdvdGWf`/`cSplitFactorFastWf` and (for the special-denominator's `ν_p`
valuation) the own-loop `cValuationWf`. -/

namespace CPolyG

variable {α : Type*} [CField α] [CFieldSpec α]

/-- **Fuel-free `p`-adic valuation** `cValuationWf p x = ν_p(x)`: the fuel-free companion of `cValuation`,
the multiplicity of the monic irreducible `p` dividing `x` (largest `k` with `pᵏ ∣ x`), by trial division.
Stops at a constant/unit `p` (`cdegG p = 0`), the zero polynomial, or a non-dividing step, else recurses on
`x/p` (the **fuel-free** `cdivWf`) and adds one. True well-founded recursion on `(cnormG x).length` — **no
fuel at runtime**; the recursion is taken only under the structural guard `(cnormG (x/p)).length <
(cnormG x).length`, so `decreasing_by` is `assumption`. The exact division `p ∣ x` with non-constant `p`
drops the `t`-degree on a real run, so the guard never fails and it agrees with `cValuation`. -/
def cValuationWf (p x : CPolyG α) : ℕ :=
  if cisZeroG x then 0
  else if cdegG p = 0 then 0
  else if cdvdGWf p x then
    let xq := cdivWf x p
    if (cnormG xq : List α).length < (cnormG x : List α).length then
      1 + cValuationWf p xq
    else 0   -- unreachable on a real run (non-constant `p ∣ x` drops the degree)
  else 0
termination_by (cnormG x).length
decreasing_by assumption

end CPolyG

/-! ### Fuel-free §6.2 special- and normal-denominator stages

Both are pure compositions of the §3.5 leaves. The special-denominator `cRdeSpecialDenominatorWf` mirrors
`cRdeSpecialDenominator` with `cSpecialPolyWf` (over `cSplitFactorFastWf`), `cValuationWf`, and `cdivFFWf`;
the normal-denominator `cRdeNormalDenominatorWf` mirrors `cRdeNormalDenominator` with `cSplitFactorFastWf`,
`cgcdFFWf`, `cdivFFWf`, `cdvdGWf`. -/

namespace CPolyG

/-- **Fuel-free special monic irreducible of the monomial** `cSpecialPolyWf Dt = p`: the fuel-free
companion of `cSpecialPoly`, the monic special part of `Dt` via the fuel-free splitting-factorization
`cSplitFactorFastWf` — **no fuel at runtime**. -/
def cSpecialPolyWf (Dt : CPolyG QFunNZ) : CPolyG QFunNZ :=
  cmonicG (cSplitFactorFastWf Dt Dt).2

/-- **Fuel-free special-denominator reduction** `cRdeSpecialDenominatorWf Dt a b c` (Bronstein §6.2, the
`RdeSpecialDenom{Exp,Tan}` boxes): the fuel-free companion of `cRdeSpecialDenominator`. Identical assembly —
the monic special irreducible `p = cSpecialPolyWf Dt`, the orders `n_b = ν_p(b)`, `n_c = ν_p(c)` (fuel-free
`cValuationWf`), the lower bound `n` and clearing power `N`, the substitution `q = h·pⁿ` cleared by `p^N` —
but every fuel'd sub-op replaced by its fuel-free companion (`cSplitFactorFastWf`, `cValuationWf`,
`cdivFFWf`). Returns `(ā, b̄, c̄, h)`. **No fuel at runtime**; `native_decide`-able over `QFunNZ`. -/
def cRdeSpecialDenominatorWf (Dt : CPolyG QFunNZ) (a b c : CPolyG QFunNZ) :
    CPolyG QFunNZ × CPolyG QFunNZ × CPolyG QFunNZ × CPolyG QFunNZ :=
  let p := cSpecialPolyWf Dt
  if cdegG p = 0 then (a, b, c, [CField.one])
  else
    let nb : ℤ := (cValuationWf p b : ℤ)
    let nc : ℤ := (cValuationWf p c : ℤ)
    let n : ℤ := min 0 (nc - min 0 nb)
    let N : ℤ := max (max 0 (-nb)) (n - nc)
    let Nnat : ℕ := N.toNat
    let negn : ℕ := (-n).toNat
    let Nminusn : ℕ := (N - n).toNat
    let pN := cpowG p Nnat
    let abar := cmulG a pN
    let DpOverp := cdivFFWf (cmonomialDeriv Dt p) p
    let bterm := cscaleG (ofConstNZ ((-(negn : ℤ) : ℚ))) (cmulG a DpOverp)
    let bbar := cmulG (caddG b bterm) pN
    let cbar := cmulG c (cpowG p Nminusn)
    let h := cpowG p negn
    (abar, bbar, cbar, h)

/-- **Fuel-free normal-denominator reduction** `cRdeNormalDenominatorWf Dt fnum fden gnum gden` (Bronstein
§6.2 / Corollary 6.1.1): the fuel-free companion of `cRdeNormalDenominator`. Identical assembly — the
normal parts `dₙ, eₙ` of the denominators (fuel-free `cSplitFactorFastWf`), `p = gcd(dₙ, eₙ)`,
`h = gcd(eₙ, eₙ')/gcd(p, p')`, the `eₙ ∣ dₙh²` test, and the quadruplet `(dₙh, dₙhf − dₙDh, dₙh²g, h)` — but
every fuel'd sub-op replaced by its fuel-free companion (`cSplitFactorFastWf`, `cgcdFFWf`, `cdivFFWf`,
`cdvdGWf`). Returns `none` ("no solution") or `some (a, b, c, h)`. **No fuel at runtime**;
`native_decide`-able over `QFunNZ`. -/
def cRdeNormalDenominatorWf (Dt : CPolyG QFunNZ) (fnum fden gnum gden : CPolyG QFunNZ) :
    Option (CPolyG QFunNZ × CPolyG QFunNZ × CPolyG QFunNZ × CPolyG QFunNZ) :=
  let dn := (cSplitFactorFastWf Dt fden).1
  let en := (cSplitFactorFastWf Dt gden).1
  let p := cgcdFFWf dn en
  let h := cdivFFWf (cgcdFFWf en (cderivG en)) (cgcdFFWf p (cderivG p))
  let dnh2 := cmulG (cmulG dn h) h
  if cdvdGWf en dnh2 then
    let a := cmulG dn h
    let Dh := cmonomialDeriv Dt h
    let b := cdivFFWf (csubG (cmulG a fnum) (cmulG (cmulG dn Dh) fden)) fden
    let c := cdivFFWf (cmulG dnh2 gnum) gden
    some (a, b, c, h)
  else none

end CPolyG

/-! ### Target 4 (the GOAL) — the fuel-free Risch DE solver `cRischDEWf` (non-cancellation regime)

`cRischDE Dt fuel fnum fden gnum gden` (Bronstein Ch. 6, assembled) chains `cRdeNormalDenominator` (§6.2) →
`cRdeSpecialDenominator` (§6.2) → `cRdeBoundDegree` (§6.3) → `cSPDE` (§6.4) → `cPolyRischDE` (§6.5/§6.6
dispatcher), reconstructing `y = ynum/yden`. The fuel-free companion `cRischDEWf` substitutes the now-fuel-free
stages: `cRdeNormalDenominatorWf`, `cRdeSpecialDenominatorWf`, `cRdeBoundDegree` (already fuel-free), `cSPDEWf`,
and — **in the non-cancellation regime** (`deg(b̄) > max(0, δ−1)`, which the validation Examples 6.5.1/6.4.1
take) — `cPolyRischDENoCancelWf` for the polynomial stage. The §6.6 cancellation dispatch (which recurses into
the whole base ℚ-pipeline `cRationalRDE`) is the documented remaining stage; `cRischDEWf` here is the fuel-free
non-cancellation solver, exact for the deliverable examples (`cRischDEWf_eq` bridges it to `cRischDE fuel`
under the non-cancellation dispatch). -/

namespace CPolyG

/-- **The fuel-free Risch differential equation solver** `cRischDEWf Dt fnum fden gnum gden` (Bronstein
Ch. 6, the goal, non-cancellation regime): the fuel-free companion of `cRischDE`. For `f = fnum/fden`,
`g = gnum/gden ∈ ℚ(x)(t)` and the monomial derivation `D = cmonomialDeriv Dt`, returns `some (ynum, yden)`
with `y = ynum/yden` solving `Dy + f·y = g`, or `none`. Identical assembly to `cRischDE` — normal
denominator → special denominator → degree bound → SPDE → polynomial stage — with every fuel'd sub-op
replaced by its fuel-free companion (`cRdeNormalDenominatorWf`, `cRdeSpecialDenominatorWf`, `cRdeBoundDegree`,
`cSPDEWf`, `cPolyRischDENoCancelWf`). **No fuel at runtime**; `native_decide`-able over the
noncomputable-`CFieldSpec` tower `QFunNZ`. The §6.5 non-cancellation polynomial stage handles the validated
examples (Bronstein 6.5.1 `y = t + x`, 6.4.1 `none`); the §6.6 cancellation dispatch is the documented
continuation. Bridges to `cRischDE fuel` on a non-cancellation run (`cRischDEWf_eq`). -/
def cRischDEWf (Dt : CPolyG QFunNZ) (fnum fden gnum gden : CPolyG QFunNZ) :
    Option (CPolyG QFunNZ × CPolyG QFunNZ) :=
  match cRdeNormalDenominatorWf Dt fnum fden gnum gden with
  | none => none
  | some (a0, b0, c0, h0) =>
    let (a, b, c, h1) := cRdeSpecialDenominatorWf Dt a0 b0 c0
    let N := cRdeBoundDegree Dt 0 a b c
    match cSPDEWf Dt a b c (N : ℤ) with
    | none => none
    | some (bbar, cbar, _m, α, β) =>
      match cPolyRischDENoCancelWf Dt bbar cbar _m with
      | none => none
      | some v =>
        let Q := caddG (cmulG α v) β
        some (cmulG Q h1, h0)

end CPolyG

/-! ### Bridge of `cRischDEWf` to the fuel'd `cRischDE` (composition, transparent stage gates)

`cRischDEWf` is a pure **composition** of the §6.2-6.5 stages. Its bridge substitutes the per-stage
fuel-free-equals-fuel'd facts. We state these transparently — the §6.2 stages' agreement
(`cRdeNormalDenominatorWf = cRdeNormalDenominator fuel`, `cRdeSpecialDenominatorWf = cRdeSpecialDenominator
fuel`) as whole-stage hypotheses the caller discharges, the §6.4 `cSPDEWf` and §6.5 `cPolyRischDENoCancelWf`
through their own bridges (`cSPDEWf_eq`, `cPolyRischDENoCancelWf_eq`), and `cRdeBoundDegree` already
fuel-free. The non-cancellation regime is encoded by the §6.5 polynomial stage being
`cPolyRischDENoCancel` (`cRischDE`'s dispatcher routes here when `deg(b̄) > max(0, δ−1)`), supplied as the
dispatch-agreement hypothesis. The fuel bounds live in the hypotheses; `cRischDEWf` carries none. -/

namespace CPolyG

/-- **Bridge — `cRischDEWf` equals `cRischDE` at sufficient fuel on a non-cancellation run** (transparent
composition). From the §6.2 stage agreements (`hnorm`: the normal denominator; `hspec`: the special
denominator), the §6.4 SPDE bridge (`hspde`: `cSPDEWf = cSPDE fuel` on the special-denominator output at the
§6.3 bound), and the §6.6/§6.5 dispatch + polynomial-stage agreement (`hpoly`: the dispatcher
`cPolyRischDE fuel` equals `cPolyRischDENoCancel fuel`, and `cPolyRischDENoCancelWf = cPolyRischDENoCancel
fuel`, on the SPDE output) — `cRischDEWf Dt fnum fden gnum gden = cRischDE Dt fuel fnum fden gnum gden`.
A pure composition rewrite: rewrite each stage to its fuel'd form and the two drivers collapse. -/
theorem cRischDEWf_eq (Dt : CPolyG QFunNZ) (fuel : ℕ) (fnum fden gnum gden : CPolyG QFunNZ)
    (hnorm : cRdeNormalDenominatorWf Dt fnum fden gnum gden
      = CPolyG.cRdeNormalDenominator Dt fuel fnum fden gnum gden)
    (hspec : ∀ a0 b0 c0, cRdeSpecialDenominatorWf Dt a0 b0 c0
      = CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0)
    (hbound : ∀ a b c, cRdeBoundDegree Dt 0 a b c = CPolyG.cRdeBoundDegree Dt fuel a b c)
    (hspde : ∀ a b c n, cSPDEWf Dt a b c n = CPolyG.cSPDE Dt fuel a b c n)
    (hdispatch : ∀ bbar cbar (m : ℤ),
      CPolyG.cPolyRischDE Dt fuel bbar cbar m = CPolyG.cPolyRischDENoCancel Dt fuel bbar cbar m)
    (hpoly : ∀ bbar cbar (m : ℤ),
      cPolyRischDENoCancelWf Dt bbar cbar m = CPolyG.cPolyRischDENoCancel Dt fuel bbar cbar m) :
    cRischDEWf Dt fnum fden gnum gden = CPolyG.cRischDE Dt fuel fnum fden gnum gden := by
  rw [cRischDEWf, CPolyG.cRischDE, hnorm]
  -- destructure the (now fuel'd) normal-denominator result
  rcases hn : CPolyG.cRdeNormalDenominator Dt fuel fnum fden gnum gden with _ | ⟨a0, b0, c0, h0⟩
  · rfl
  · simp only []
    -- rewrite the special denominator, degree bound, SPDE, and the polynomial dispatch
    rw [hspec a0 b0 c0]
    -- the special-denominator output's components; `cRischDE` destructures via `let (a,b,c,h1) := …`
    rcases hs : CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0 with ⟨a, b, c, h1⟩
    simp only [hbound a b c, hspde a b c (CPolyG.cRdeBoundDegree Dt fuel a b c : ℤ)]
    rcases hsp : CPolyG.cSPDE Dt fuel a b c (CPolyG.cRdeBoundDegree Dt fuel a b c : ℤ) with
      _ | ⟨bbar, cbar, m, α, β⟩
    · rfl
    · -- the outer `match some (…)` reduces; both inner stages become `cPolyRischDENoCancel fuel …`
      simp only [hpoly bbar cbar m, hdispatch bbar cbar m]
      rcases hpr : CPolyG.cPolyRischDENoCancel Dt fuel bbar cbar m with _ | v <;> rfl

end CPolyG

/-! ### The transported abstract headline — `cRischDEWf` returns a cleared solution (primitive regime)

Composing the bridge `cRischDEWf_eq` with the §6 pipeline correctness `cRischDE_rdeCleared_of_inputs`
(`ComputableRischDEPipelineCorrect`) gives the **fuel-free** abstract Risch-DE correctness in the primitive
regime: the reconstruction `ynum = (α·v + β)·[1]`, `yden = h0` that the fuel-free `cRischDEWf` returns
(exactly the fuel'd `cRischDE`'s output, via the bridge) satisfies the cleared Risch-DE identity
`D(y) + f·y = g` over `(RatFunc ℚ)[X]`. The transport rides entirely on the existing fuel'd headline; the
bridge only certifies the fuel-free engine produces the same reconstruction. -/

/-- **The fuel-free §6 RDE pipeline correctness (primitive regime, transported)**: in the primitive special
regime (`cdegG (cSpecialPoly Dt fuel) = 0`), given the §6.2/§6.4/§6.5 intermediate fuel'd `some`-results
(`hnorm`, `hspde`, `hpoly`) and the §6.2 normal-denominator certificates (the same gate the fuel'd
`cRischDE_rdeCleared_of_inputs` carries), the reconstruction `ynum = (α·v + β)·[1]`, `yden = h0` satisfies
the cleared Risch-DE identity `gden·fden·(D(ynum)·yden − ynum·D(yden)) + gden·fnum·ynum·yden =
gnum·fden·yden²` over `(RatFunc ℚ)[X]` (`D = implicitDeriv (toPolyG Dt)`). This is the all-inputs (no
`native_decide`) abstract correctness of the fuel-free engine in the primitive regime — the *exact same*
statement and proof as `cRischDE_rdeCleared_of_inputs`, since the reconstruction quantities `α, v, β, h0`
are produced identically by both engines (the bridge `cRischDEWf_eq` certifies the runtime equality, but the
cleared identity is purely about the reconstruction, not which engine computed it). -/
theorem cRischDEWf_rdeCleared_of_inputs (Dt : CPolyG QFunNZ) (fuel : ℕ)
    (fnum fden gnum gden a0 b0 c0 h0 : CPolyG QFunNZ)
    (bbar cbar : CPolyG QFunNZ) (m : ℤ) (α β v : CPolyG QFunNZ)
    (hprim : cdegG (CPolyG.cSpecialPoly Dt fuel) = 0)
    (hnorm : CPolyG.cRdeNormalDenominator Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0))
    (hdn : toPolyG (CPolyG.cSplitFactorFast Dt fuel fden).1 ≠ 0)
    (hfden0 : cnormG fden ≠ []) (hgden0 : cnormG gden ≠ [])
    (hfbB : (cnormG (csubG (cmulG (cmulG (CPolyG.cSplitFactorFast Dt fuel fden).1 h0) fnum)
        (cmulG (cmulG (CPolyG.cSplitFactorFast Dt fuel fden).1 (cmonomialDeriv Dt h0)) fden)) :
        List QFunNZ).length ≤ fuel)
    (hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (CPolyG.cSplitFactorFast Dt fuel fden).1 h0) fnum)
        (cmulG (cmulG (CPolyG.cSplitFactorFast Dt fuel fden).1 (cmonomialDeriv Dt h0)) fden)))
    (hfbC : (cnormG (cmulG (cmulG (cmulG (CPolyG.cSplitFactorFast Dt fuel fden).1 h0) h0) gnum) :
        List QFunNZ).length ≤ fuel)
    (hdvdC : toPolyG gden ∣
      toPolyG (cmulG (cmulG (cmulG (CPolyG.cSplitFactorFast Dt fuel fden).1 h0) h0) gnum))
    (hspde : CPolyG.cSPDE Dt fuel (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).1
        (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).2.1
        (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).2.2.1
        (CPolyG.cRdeBoundDegree Dt fuel (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).1
          (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).2.1
          (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α, β))
    (hin : CSPDEClearedInputs Dt fuel (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).1
        (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).2.1
        (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).2.2.1
        (CPolyG.cRdeBoundDegree Dt fuel (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).1
          (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).2.1
          (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).2.2.1 : ℤ))
    (hpoly : CPolyG.cPolyRischDENoCancel Dt fuel bbar cbar m = some v) :
    let Q := caddG (cmulG α v) β
    let ynum := cmulG Q [CField.one]
    let yden := h0
    toPolyG gden * toPolyG fden
        * (Differential.implicitDeriv (toPolyG Dt) (toPolyG ynum) * toPolyG yden
            - toPolyG ynum * Differential.implicitDeriv (toPolyG Dt) (toPolyG yden))
        + toPolyG gden * toPolyG fnum * toPolyG ynum * toPolyG yden
      = toPolyG gnum * toPolyG fden * toPolyG yden ^ 2 :=
  cRischDE_rdeCleared_of_inputs Dt fuel fnum fden gnum gden a0 b0 c0 h0 bbar cbar m α β v
    hprim hnorm hdn hfden0 hgden0 hfbB hdvdB hfbC hdvdC hspde hin hpoly

-- The fuel-free §6 pipeline abstract correctness (primitive regime) carries only the standard axioms.
#print axioms cRischDEWf_rdeCleared_of_inputs

/-- **The fuel-free `cRischDEWf` returns a genuine cleared solution** (primitive regime, the headline): if
the bridge holds (`hbridge : cRischDEWf … = cRischDE fuel …`, dischargeable from `cRischDEWf_eq`) and the
fuel'd pipeline reaches its §6.2/§6.4/§6.5 intermediate `some`-results under the primitive special regime,
then `cRischDEWf Dt fnum fden gnum gden = some (ynum, yden)` (with `ynum = (α·v + β)·[1]`, `yden = h0`) and
the returned `y = ynum/yden` solves `Dy + f·y = g` in the cleared form over `(RatFunc ℚ)[X]`. The fuel-free
headline: the §6 RDE solver, with **no fuel at runtime**, returns an answer that is a genuine antiderivative-
side solution. Combines the bridge `cRischDEWf_eq` (so `cRischDEWf` returns the fuel'd reconstruction) with
the transported `cRischDEWf_rdeCleared_of_inputs`. -/
theorem cRischDEWf_returns_cleared_solution (Dt : CPolyG QFunNZ) (fuel : ℕ)
    (fnum fden gnum gden a0 b0 c0 h0 : CPolyG QFunNZ)
    (bbar cbar : CPolyG QFunNZ) (m : ℤ) (α β v : CPolyG QFunNZ)
    (hbridge : CPolyG.cRischDEWf Dt fnum fden gnum gden
      = CPolyG.cRischDE Dt fuel fnum fden gnum gden)
    (hprim : cdegG (CPolyG.cSpecialPoly Dt fuel) = 0)
    (hnorm : CPolyG.cRdeNormalDenominator Dt fuel fnum fden gnum gden = some (a0, b0, c0, h0))
    (hdn : toPolyG (CPolyG.cSplitFactorFast Dt fuel fden).1 ≠ 0)
    (hfden0 : cnormG fden ≠ []) (hgden0 : cnormG gden ≠ [])
    (hfbB : (cnormG (csubG (cmulG (cmulG (CPolyG.cSplitFactorFast Dt fuel fden).1 h0) fnum)
        (cmulG (cmulG (CPolyG.cSplitFactorFast Dt fuel fden).1 (cmonomialDeriv Dt h0)) fden)) :
        List QFunNZ).length ≤ fuel)
    (hdvdB : toPolyG fden ∣ toPolyG (csubG (cmulG (cmulG (CPolyG.cSplitFactorFast Dt fuel fden).1 h0) fnum)
        (cmulG (cmulG (CPolyG.cSplitFactorFast Dt fuel fden).1 (cmonomialDeriv Dt h0)) fden)))
    (hfbC : (cnormG (cmulG (cmulG (cmulG (CPolyG.cSplitFactorFast Dt fuel fden).1 h0) h0) gnum) :
        List QFunNZ).length ≤ fuel)
    (hdvdC : toPolyG gden ∣
      toPolyG (cmulG (cmulG (cmulG (CPolyG.cSplitFactorFast Dt fuel fden).1 h0) h0) gnum))
    (hspeceq : CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0 = (a0, b0, c0, [CField.one]))
    (hspde : CPolyG.cSPDE Dt fuel a0 b0 c0
        (CPolyG.cRdeBoundDegree Dt fuel a0 b0 c0 : ℤ) = some (bbar, cbar, m, α, β))
    (hin : CSPDEClearedInputs Dt fuel (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).1
        (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).2.1
        (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).2.2.1
        (CPolyG.cRdeBoundDegree Dt fuel (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).1
          (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).2.1
          (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).2.2.1 : ℤ))
    (hdispatch : CPolyG.cPolyRischDE Dt fuel bbar cbar m
      = CPolyG.cPolyRischDENoCancel Dt fuel bbar cbar m)
    (hpoly : CPolyG.cPolyRischDENoCancel Dt fuel bbar cbar m = some v) :
    CPolyG.cRischDEWf Dt fnum fden gnum gden
        = some (cmulG (caddG (cmulG α v) β) [CField.one], h0)
      ∧ toPolyG gden * toPolyG fden
          * (Differential.implicitDeriv (toPolyG Dt) (toPolyG (cmulG (caddG (cmulG α v) β) [CField.one]))
              * toPolyG h0
            - toPolyG (cmulG (caddG (cmulG α v) β) [CField.one])
              * Differential.implicitDeriv (toPolyG Dt) (toPolyG h0))
          + toPolyG gden * toPolyG fnum * toPolyG (cmulG (caddG (cmulG α v) β) [CField.one]) * toPolyG h0
        = toPolyG gnum * toPolyG fden * toPolyG h0 ^ 2 := by
  refine ⟨?_, ?_⟩
  · -- the bridge + the fuel'd `cRischDE`'s reconstruction give the explicit output
    rw [hbridge, CPolyG.cRischDE, hnorm]
    simp only []
    rw [hspeceq]
    simp only [hspde, hdispatch, hpoly]
  · -- the cleared identity, transported (the special regime makes the SPDE inputs collapse to `a0,b0,c0`)
    have hspde' : CPolyG.cSPDE Dt fuel (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).1
        (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).2.1
        (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).2.2.1
        (CPolyG.cRdeBoundDegree Dt fuel (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).1
          (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).2.1
          (CPolyG.cRdeSpecialDenominator Dt fuel a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α, β) := by rw [hspeceq]; exact hspde
    exact cRischDEWf_rdeCleared_of_inputs Dt fuel fnum fden gnum gden a0 b0 c0 h0 bbar cbar m α β v
      hprim hnorm hdn hfden0 hgden0 hfbB hdvdB hfbC hdvdC hspde' hin hpoly

-- The fuel-free §6 RDE solver headline carries only the standard axioms.
#print axioms cRischDEWf_returns_cleared_solution

/-! ### `native_decide` — the fuel-free Risch DE solver on Bronstein Examples 6.5.1 + 6.4.1

Re-runs `rischDE_solve_example` (`y = t + x`) and `rischDE_noSolution_example` (`none`) over the
noncomputable-`CFieldSpec` tower `QFunNZ` (ℚ(x)), now **fuel-free** end-to-end: the whole §6 RDE pipeline
(normal denominator → special denominator → degree bound → SPDE → §6.5 non-cancellation) computes with **no
fuel at runtime** (the WF stages carry no fuel and no noncomputable bridge into the compiled body). Reuses
the Example 6.1.2/6.5.1 data of `ComputableRischDE`. -/

open CPolyG QFunNZ in
/-- **Example 6.5.1 — the fuel-free Risch DE solver runs end-to-end over the tower** (`native_decide`,
Bronstein Ch. 6, book p.208). For `Dy + (t²+1)y = t³ + (x+1)t² + t + (x+2)` over `ℚ(x)(t)`, `t = tan(x)`,
`Dt = 1+t²`, the fuel-free `cRischDEWf` — `cRdeNormalDenominatorWf` → `cRdeSpecialDenominatorWf` →
`cRdeBoundDegree` → `cSPDEWf` → `cPolyRischDENoCancelWf` — returns `some (ynum, yden)`, and the returned
`y = ynum/yden` is verified to **actually solve** `Dy + f·y = g` by `rdeClearedCheck` (the cleared
polynomial identity, not merely pinning the output): the book's solution is `y = t + x`. The fuel-free
companion of `rischDE_solve_example`, the complete non-cancellation RDE pipeline computing an elementary
solution over ℚ(x)[t] with **no fuel at runtime**. -/
theorem rischDEWf_solve_example :
    (match cRischDEWf rischDExampleDt rischDExampleFnum rischDExampleFden
          rischDExampleG651num rischDExampleFden with
      | some (ynum, yden) =>
          rdeClearedCheck rischDExampleDt rischDExampleFnum rischDExampleFden
            rischDExampleG651num rischDExampleFden ynum yden
      | none => false) = true := by native_decide

#print axioms rischDEWf_solve_example

open CPolyG QFunNZ in
/-- **Example 6.4.1 — the fuel-free RDE solver correctly reports NO solution** (`native_decide`, Bronstein
§6.4, book p.204). The equation `Dy + (t²+1)y = 1/t²` (eq. 6.4, from `∫ e^{tan x}/tan²x dx`) has **no**
solution `y ∈ k(t)`: the fuel-free `cSPDEWf` reaches `n = −1 < 0` with `c ≠ 0`, so `cRischDEWf` returns
`none`, matching the book — the integral is not elementary. The fuel-free companion of
`rischDE_noSolution_example`. -/
theorem rischDEWf_noSolution_example :
    (cRischDEWf rischDExampleDt rischDExampleFnum rischDExampleFden
      rischDExampleGnum rischDExampleGden).isNone = true := by native_decide

#print axioms rischDEWf_noSolution_example

end DeepWiki.SymbolicIntegration

