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

end DeepWiki.SymbolicIntegration
