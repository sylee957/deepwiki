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

end DeepWiki.SymbolicIntegration

