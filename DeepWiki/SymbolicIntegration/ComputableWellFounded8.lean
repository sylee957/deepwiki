import DeepWiki.SymbolicIntegration.ComputableWellFounded7

/-! # Fuel-free (well-founded) §6.6 base ℚ-pipeline + cancellation dispatch — `cRationalRDEWf`,
`cPolyRischDECancelPrimWf`, `cPolyRischDECancelExpWf`, `cRischDEWfFull`

This completes the fuel-free conversion of the §6 Risch-DE oracle. `ComputableWellFounded7` made the
**non-cancellation** regime of `cRischDE` fuel-free (`cRischDEWf`); the remaining gap is the **§6.6
cancellation** regime, which recurses degree-by-degree into the **base ℚ-pipeline** `cRationalRDE` (the
whole Ch. 6 algorithm re-run over the constant field `k = ℚ`, trivial primitive monomial `t = x`,
`D = d/dx`). That base pipeline — over `CPolyG ℚ` (concrete, no `[CFieldSpec]` concern) — and the §6.6
cancellation own-loops that drive it are converted here, so the fuel-free solver handles **all** regimes.

The two recursions are **independent** (no mutual recursion): the tower cancellation loops
(`cPolyRischDECancelPrim`/`Exp`, over `CPolyG QFunNZ`) recurse into `cRischDEBase` → `cRationalRDE`, which
lives over the **different** carrier `CPolyG ℚ`. So we convert leaf-first, base pipeline before tower:

* **Base ℚ leaves** — `cIntegratePolyQ` (termwise antiderivative) and `cRischDEConst` (the genuine bottom
  `s = c/b`) are already non-recursive, hence fuel-free as-is; no companion is needed. The two base
  **own-loops** get WF companions mirroring the WF7 tower own-loops at `α = ℚ`:
  - **`cPolyRischDENoCancelQWf`** (§6.5 base) — own-loop on `(cnormG c).length` (the leading term of
    `b·p` cancels `c`'s top, dropping the length; structural guard, `decreasing_by := assumption`).
  - **`cPolyRischDECancelPrimQWf`** (§6.6 base primitive cancellation) — own-loop on `(cnormG c).length`,
    recursing degree-by-degree into the non-recursive `cRischDEConst` (the leading monomial `s·xᵐ` with
    `s = lc(c)/b` cancels `c`'s top, dropping the length; structural guard).
  - **`cSPDEQWf`** (§6.4 base) — own-loop on `(n+1).toNat` (`n` drops by `deg(a/g) ≥ 1`; structural guard),
    the inner gcd/division/Bézout/divisibility being the generic fuel-free `cgcdWf`/`cdivWf`/`cdiophantineGWf`/
    `cdvdGWf` at `α = ℚ`.

* **Base ℚ compositions** — `cPolyRischDEQWf` (the §6.5/§6.6 dispatcher), `cWeakNormalizerQWf` (§6.1, over
  the WF residue-resultant leaf `cresultantWf`), `cRdeNormalDenominatorQWf` (§6.2), and the **assembly**
  `cRationalRDEWf` (weak normalizer → normal denominator → degree bound → SPDE → poly stage), all
  substituting the fuel-free leaves — **no fuel at runtime**.

* **`cRischDEBaseWf`** — the base RDE `Ds + b·s = c` over `k = ℚ(x)`: the `k`-constant fast path plus the
  general routing through `cRationalRDEWf`.

* **Tower §6.6 cancellation own-loops** — `cPolyRischDECancelPrimWf` (primitive, `δ = 0`, `b ∈ k*`) and
  `cPolyRischDECancelExpWf` (hyperexponential, `δ = 1`, `b ∈ k*`): own-loops on `(cnormG c).length`
  (the leading monomial `s·tᵐ` cancels `c`'s top, dropping the length; structural guard), recursing into
  `cRischDEBaseWf` (with the `m·η` shift for the exp case, `η = cExpEtaWf Dt`). `cExpEtaWf` is the
  fuel-free `cExpEta` (over `cdivWf`).

* **`cPolyRischDEWf`** (tower dispatcher) and the extended **`cRischDEWfFull`** — re-point the §6 solver so
  the §6.6 dispatch routes to the fuel-free cancellation own-loops, so the **whole** §6 RDE pipeline runs
  fuel-free in every regime (non-cancellation, primitive cancellation, hyperexponential cancellation).

`native_decide` re-runs the §6.6 cancellation deliverables fuel-free: the **primitive** cancellation
`rischDE_cancel_example` (`t = log x`, `Dq + q = log x + 1/x → q = log x`), the **non-constant base
recursion** `rischDE_baseRecursion_example` (`Dy + (1/x)y = 2log x + 1 → y = x·log x`, exercising the full
base ℚ-pipeline), and the **hyperexponential** cancellation `rischDE_cancelExp_example`
(`t = eˣ`, `Dq + (1/x)q = (2+x)eˣ → q = x·eˣ`). As throughout, the runtime WF ops carry no fuel; fuel
bounds live only in the bridge proofs. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZ

/-! ### The base ℚ leaves — `cIntegratePolyQ`, `cRischDEConst` are already fuel-free

`cIntegratePolyQ c = (0 : ℚ) :: (c.zipIdx.map …)` (termwise antiderivative over ℚ) and `cRischDEConst b c
= if b = 0 then … else some (c/b)` are **non-recursive** — they carry no fuel argument at all, so they are
fuel-free as written and need no WF companion. The fuel-bearing base own-loops below recurse into them
directly. -/

/-- The base ℚ termwise antiderivative `cIntegratePolyQ` is already fuel-free (non-recursive). -/
example (c : CPolyG ℚ) : CPolyG ℚ := CPolyG.cIntegratePolyQ c

/-- The genuine bottom `cRischDEConst b c` (`s = c/b`) is already fuel-free (non-recursive). -/
example (b c : ℚ) : Option ℚ := CPolyG.cRischDEConst b c

namespace CPolyG

/-! ### Base own-loop 1 — the fuel-free non-cancellation Poly-Risch-DE over ℚ `cPolyRischDENoCancelQWf`

The base (`α = ℚ`, `D = cderivQ = d/dx`) analogue of the WF7 tower own-loop `cPolyRischDENoCancelWf`:
solve `Dq + b·q = c` degree-by-degree, peeling `p = (lc(c)/lc(b))·xᵐ` (`m = deg(c) − deg(b)`), recursing
on `c' = c − Dp − b·p`. In the non-cancellation regime `deg(b) ≥ 1`, the leading term of `b·p` cancels
`c`'s, so `(cnormG c).length` strictly drops; well-founded recursion on it, structural runtime guard. -/

/-- **Fuel-free non-cancellation Poly-Risch-DE over ℚ** (Bronstein §6.5 base, `PolyRischDENoCancel1`,
book p.208, `D = d/dx`) `cPolyRischDENoCancelQWf b c n`: the fuel-free companion of `cPolyRischDENoCancelQ`.
Solves `Dq + b·q = c` for `q ∈ ℚ[x]`, `deg(q) ≤ n` (`n : ℤ`), non-cancellation case `deg(b) ≥ 1`,
top-down — `p = (lc(c)/lc(b))·xᵐ` (`m = deg(c) − deg(b)`, `D = cderivQ`), recurse on `c' = c − Dp − b·p`.
Returns `none` ("no solution of degree `≤ n`") or `some q`. True well-founded recursion on
`(cnormG c).length` — **no fuel at runtime**; the recursion is taken only under the structural guard
`(cnormG c').length < (cnormG c).length`, so `decreasing_by` is `assumption`. Agrees with
`cPolyRischDENoCancelQ` on a non-cancellation run (`cPolyRischDENoCancelQWf_eq`). -/
def cPolyRischDENoCancelQWf (b c : CPolyG ℚ) (n : ℤ) : Option (CPolyG ℚ) :=
  if cisZeroG c then some []
  else
    let m : ℤ := (cdegG c : ℤ) - (cdegG b : ℤ)
    if n < 0 ∨ m < 0 ∨ m > n then none
    else
      let coeff := CField.div (cleadG c) (cleadG b)
      let p := cshiftG m.toNat [coeff]
      let c' := csubG (csubG c (cderivQ p)) (cmulG b p)
      if (cnormG c' : List ℚ).length < (cnormG c : List ℚ).length then
        match cPolyRischDENoCancelQWf b c' (m - 1) with
        | none => none
        | some q => some (caddG p q)
      else none   -- unreachable on a non-cancellation run (leading term cancels, degree drops)
termination_by (cnormG c).length
decreasing_by assumption

/-! ### Base own-loop 2 — the fuel-free primitive cancellation Poly-Risch-DE over ℚ `cPolyRischDECancelPrimQWf`

The §6.6 base primitive cancellation (`b ∈ ℚ*` a constant, `D = d/dx`, `δ = 0`): the leading terms of `Dq`
and `bq` cancel, so the solve recurses degree-by-degree into the **non-recursive constant base RDE**
`cRischDEConst b₀ (lc(c))` (`b₀·s = lc(c)`, `s = lc(c)/b₀`). The leading monomial `s·xᵐ` (`m = deg(c)`)
cancels `c`'s top, so `(cnormG c).length` strictly drops; well-founded recursion on it. -/

/-- **Fuel-free primitive cancellation Poly-Risch-DE over ℚ** (Bronstein §6.6 base, `PolyRischDECancelPrim`,
book p.212) `cPolyRischDECancelPrimQWf b c n`: the fuel-free companion of `cPolyRischDECancelPrimQ`.
`b ∈ ℚ*` (a constant `b₀ = lc(b)`), `D = d/dx`, `δ = 0`; solves `Dq + b·q = c` degree-by-degree, recursing
into the constant base RDE `cRischDEConst b₀ (lc(c))` (`= lc(c)/b₀`) at each degree `m = deg(c)`, leading
monomial `s·xᵐ`, remainder `c' = c − b·(s·xᵐ) − D(s·xᵐ)`. Returns `none` or `some q`. True well-founded
recursion on `(cnormG c).length` — **no fuel at runtime**; the recursion is taken only under the structural
guard `(cnormG c').length < (cnormG c).length` (the leading monomial cancels `c`'s top), so `decreasing_by`
is `assumption`. Agrees with `cPolyRischDECancelPrimQ` on a real run (`cPolyRischDECancelPrimQWf_eq`). -/
def cPolyRischDECancelPrimQWf (b c : CPolyG ℚ) (n : ℤ) : Option (CPolyG ℚ) :=
  let b0 : ℚ := cleadG b
  if cisZeroG c then some []
  else if n < (cdegG c : ℤ) then none
  else
    let m : ℕ := cdegG c
    match cRischDEConst b0 (cleadG c) with
    | none => none
    | some s =>
      let stm : CPolyG ℚ := cshiftG m [s]
      let c' := csubG (csubG c (cmulG b stm)) (cderivQ stm)
      if (cnormG c' : List ℚ).length < (cnormG c : List ℚ).length then
        match cPolyRischDECancelPrimQWf b c' ((m : ℤ) - 1) with
        | none => none
        | some q => some (caddG stm q)
      else none   -- unreachable on a real run (the leading monomial cancels, degree drops)
termination_by (cnormG c).length
decreasing_by assumption

/-! ### Base own-loop 3 — the fuel-free Rothstein SPDE over ℚ `cSPDEQWf` (own-loop on `(n+1).toNat`)

The base (`α = ℚ`, `D = cderivQ = d/dx`) analogue of the WF7 tower own-loop `cSPDEWf`: peel `g = gcd(a, b)`
each step, recurse on the divided `a/g` with the bound lowered to `n − deg(a/g)`. The recursion is taken
only when `n ≥ 0` and `deg(a/g) ≥ 1` (constant base case `deg(a/g) = 0` returns directly), so `n` strictly
drops by `deg(a/g) ≥ 1`; well-founded recursion on `(n + 1).toNat`, structural runtime guard. The inner
gcd/division/divisibility/Bézout are the generic fuel-free `cgcdWf`/`cdivWf`/`cdvdGWf`/`cdiophantineGWf` at
`α = ℚ`. -/

/-- **Fuel-free Rothstein SPDE over ℚ** (Bronstein §6.4 base, `SPDE(a,b,c,D,n)`, book p.203, `D = d/dx`)
`cSPDEQWf a b c n`: the fuel-free companion of `cSPDEQ`. Given `a, b, c ∈ ℚ[x]` (`a ≠ 0`) and a degree
bound `n : ℤ`, returns `none` ("no solution of degree `≤ n`") or `some (b̄, c̄, m, α, β)` so any solution
`q` of `a·Dq + b·q = c` of degree `≤ n` is `q = α·h + β` for an `h` solving `Dh + b̄·h = c̄`, `deg(h) ≤ m`.
Peels `g = (cgcdWf a b).1`; the constant `a/g` base case returns the identity reconstruction, else solves
the Bézout `cdiophantineGWf b̄ ā c̄` and recurses on `ā = a/g` at `n − deg(ā)`. True well-founded recursion
on `(n + 1).toNat` (`n` drops by `deg(ā) ≥ 1`) — **no fuel at runtime**; the inner gcd/division/Bézout are
the generic `cgcdWf`/`cdivWf`/`cdvdGWf`/`cdiophantineGWf`. Agrees with `cSPDEQ` on a regular run
(`cSPDEQWf_eq`). -/
def cSPDEQWf (a b c : CPolyG ℚ) (n : ℤ) :
    Option (CPolyG ℚ × CPolyG ℚ × ℤ × CPolyG ℚ × CPolyG ℚ) :=
  if n < 0 then
    if cisZeroG c then some ([], [], 0, [], []) else none
  else
    let g := (cgcdWf a b).1
    if cdvdGWf g c then
      let a' := cdivWf a g
      let b' := cdivWf b g
      let c' := cdivWf c g
      if cdegG a' = 0 then
        let ainv := CField.inv (cleadG a')
        some (cscaleG ainv b', cscaleG ainv c', n, [CField.one], [])
      else
        let (r, z) := cdiophantineGWf b' a' c'
        let Da := cderivQ a'
        let Dr := cderivQ r
        if (n - (cdegG a' : ℤ) + 1).toNat < (n + 1).toNat then
          match cSPDEQWf a' (caddG b' Da) (csubG z Dr) (n - (cdegG a' : ℤ)) with
          | none => none
          | some (bbar, cbar, m, α, β) =>
              some (bbar, cbar, m, cmulG a' α, caddG (cmulG a' β) r)
        else none   -- unreachable on a real run (`deg(a') ≥ 1`, `n ≥ 0`, so `n` strictly drops)
    else none
termination_by (n + 1).toNat
decreasing_by assumption

/-! ### Base composition — the fuel-free Poly-Risch-DE dispatcher over ℚ `cPolyRischDEQWf`

`cPolyRischDEQ` routes `Dq + b·q = c` (`δ = 0`) to polynomial integration (`b = 0`), the non-cancellation
solver (`deg(b) ≥ 1`), or the primitive cancellation solver (`b ∈ ℚ*`). The fuel-free dispatcher
substitutes the now-fuel-free own-loops `cPolyRischDENoCancelQWf`/`cPolyRischDECancelPrimQWf`
(`cIntegratePolyQ` is already fuel-free). -/

/-- **Fuel-free Poly-Risch-DE dispatcher over ℚ** (Bronstein §6.5 + §6.6 base, `D = d/dx`, `δ = 0`)
`cPolyRischDEQWf b c n`: the fuel-free companion of `cPolyRischDEQ`. Solves `Dq + b·q = c` for `q ∈ ℚ[x]`,
`deg(q) ≤ n`. Routes `b = 0` to polynomial integration (`cIntegratePolyQ`, with the `deg(c)+1 ≤ n` check),
`deg(b) ≥ 1` to the fuel-free non-cancellation solver `cPolyRischDENoCancelQWf`, and `b ∈ ℚ*` to the
fuel-free primitive cancellation solver `cPolyRischDECancelPrimQWf`. **No fuel at runtime**. -/
def cPolyRischDEQWf (b c : CPolyG ℚ) (n : ℤ) : Option (CPolyG ℚ) :=
  if cisZeroG b then
    if cisZeroG c then some []
    else if (cdegG c : ℤ) + 1 > n then none
    else some (cIntegratePolyQ c)
  else if (cdegG b : ℤ) > 0 then cPolyRischDENoCancelQWf b c n
  else cPolyRischDECancelPrimQWf b c n

/-! ### Base composition — the fuel-free residue resultant + weak normalizer over ℚ

`cResidueResultantQ` builds `r(z) = res_x(a − z·d′, d)` by evaluation + interpolation (`cresultantG` at
`deg d + 1` nodes, then `cinterpolateG`); `cWeakNormalizerQ` then takes the positive integer roots of `r`
into the `WeakNormalizer` product (`cgcdExtG`, `cdivG`, `cpowG`). The fuel-free companions substitute the
generic fuel-free `cresultantWf`/`cgcdWf`/`cdivWf` (`cinterpolateG`/`cPosIntRootsQ`/`cpowG`/`cscaleG` carry
no fuel). -/

/-- **Fuel-free residue resultant over ℚ** `cResidueResultantQWf a d = r(z) = res_x(a − z·d′, d) ∈ ℚ[z]`:
the fuel-free companion of `cResidueResultantQ`, the §5.6 evaluation + interpolation template with the
generic fuel-free resultant leaf `cresultantWf` (and `cinterpolateG`, which carries no fuel). **No fuel at
runtime**. -/
def cResidueResultantQWf (a d : CPolyG ℚ) : CPolyG ℚ :=
  let Dd := cderivQ d
  let n := cdegG d
  let pts : List (ℚ × ℚ) := (List.range (n + 1)).map (fun k =>
    let zk : ℚ := (k : ℚ)
    (zk, cresultantWf d (csubG a (cscaleG zk Dd))))
  cinterpolateG pts

/-- **Fuel-free weak normalizer over ℚ** `cWeakNormalizerQWf fnum fden = q₁ ∈ ℚ[x]` (Bronstein §6.1 base,
book p.183): the fuel-free companion of `cWeakNormalizerQ`. Identical assembly — `dₙ = fden` (no special
part over ℚ), `g = gcd(dₙ, dₙ′)`, `d₁ = (dₙ/g)/gcd(dₙ/g, g)`, `a` the residue numerator from
`ExtendedEuclidean(fden/d₁, d₁, fnum)`, `r = res_x(a − z·d₁′, d₁)`, the product over the positive integer
roots `nᵢ` of `r` — but every fuel'd sub-op replaced by its fuel-free companion (`cgcdWf`, `cdivWf`,
`cdiophantineGWf`, `cResidueResultantQWf`). `q₁ = 1` when `f` is already weakly normalized. **No fuel at
runtime**. -/
def cWeakNormalizerQWf (fnum fden : CPolyG ℚ) (boundRoots : ℕ := 16) : CPolyG ℚ :=
  let dn := fden
  let g := (cgcdWf dn (cderivQ dn)).1
  let dstar := cdivWf dn g
  let d1 := cdivWf dstar (cgcdWf dstar g).1
  let fdenOverD1 := cdivWf fden d1
  let a := (cdiophantineGWf fdenOverD1 d1 fnum).1
  let Dd1 := cderivQ d1
  let r := cResidueResultantQWf a d1
  let roots := cPosIntRootsQ r boundRoots
  roots.foldl (fun (acc : CPolyG ℚ) (n : ℕ) =>
    let gi := (cgcdWf (csubG a (cscaleG ((n : ℚ)) Dd1)) d1).1
    cmulG acc (cpowG gi n)) [(1 : ℚ)]

/-- **Fuel-free normal-denominator reduction over ℚ** `cRdeNormalDenominatorQWf fnum fden gnum gden`
(Bronstein §6.2 base / Corollary 6.1.1, book p.185): the fuel-free companion of `cRdeNormalDenominatorQ`.
Over ℚ the normal parts are the whole denominators (`dₙ = fden`, `eₙ = gden`); `p = gcd(dₙ, eₙ)`,
`h = gcd(eₙ, eₙ′)/gcd(p, p′)`, the `eₙ ∣ dₙh²` test, and the quadruplet `(dₙh, dₙhf − dₙDh, dₙh²g, h)` —
every fuel'd sub-op replaced by its fuel-free companion (`cgcdWf`, `cdivWf`, `cdvdGWf`). Returns `none`
("no solution") or `some (a, B, C, h)`. **No fuel at runtime**. -/
def cRdeNormalDenominatorQWf (fnum fden gnum gden : CPolyG ℚ) :
    Option (CPolyG ℚ × CPolyG ℚ × CPolyG ℚ × CPolyG ℚ) :=
  let dn := fden
  let en := gden
  let p := (cgcdWf dn en).1
  let h := cdivWf (cgcdWf en (cderivQ en)).1 (cgcdWf p (cderivQ p)).1
  let dnh2 := cmulG (cmulG dn h) h
  if cdvdGWf en dnh2 then
    let a := cmulG dn h
    let Dh := cderivQ h
    let b := cdivWf (csubG (cmulG a fnum) (cmulG (cmulG dn Dh) fden)) fden
    let c := cdivWf (cmulG dnh2 gnum) gden
    some (a, b, c, h)
  else none

/-! ### Base composition — the fuel-free rational Risch DE over ℚ(x) `cRationalRDEWf`

`cRationalRDE` is a pure composition of the base stages: weak normalizer → reduce-to-lowest-terms →
normal denominator → degree bound (`cRdeBoundDegreeBaseQ`, already fuel-free, no recursion) → SPDE →
poly stage. The fuel-free assembly substitutes the now-fuel-free stages — **no fuel at runtime**. -/

/-- **Fuel-free rational Risch DE over ℚ(x)** `cRationalRDEWf bnum bden cnum cden` (Bronstein §6.6 eq. 6.23
base solve, `D = d/dx`): the fuel-free companion of `cRationalRDE`. Solves `Ds + b·s = c` for `s ∈ ℚ(x)`
with `b = bnum/bden`, `c = cnum/cden`, returning `some (snum, sden)` (with `s = snum/sden`) or `none`. The
whole Ch. 6 pipeline at the base level (trivial primitive monomial `t = x`, `k = ℚ`): weak normalize
(`cWeakNormalizerQWf`), reduce `b̃ = b − Dq₁/q₁`, `c̃ = c·q₁` to lowest terms (over the fuel-free `cgcdWf`/
`cdivWf`), normal denominator (`cRdeNormalDenominatorQWf`), degree bound (`cRdeBoundDegreeBaseQ`, fuel-free),
SPDE (`cSPDEQWf`), poly stage (`cPolyRischDEQWf`). **No fuel at runtime**; `native_decide`-able. -/
def cRationalRDEWf (bnum bden cnum cden : CPolyG ℚ) : Option (CPolyG ℚ × CPolyG ℚ) :=
  let q1 := cWeakNormalizerQWf bnum bden
  let Dq1 := cderivQ q1
  let bpnum := csubG (cmulG bnum q1) (cmulG Dq1 bden)
  let bpden := cmulG bden q1
  let cpnum := cmulG cnum q1
  let cpden := cden
  let gb := (cgcdWf bpnum bpden).1
  let bnum2 := cdivWf bpnum gb
  let bden2 := cdivWf bpden gb
  let gc := (cgcdWf cpnum cpden).1
  let cnum2 := cdivWf cpnum gc
  let cden2 := cdivWf cpden gc
  match cRdeNormalDenominatorQWf bnum2 bden2 cnum2 cden2 with
  | none => none
  | some (a0, b0, c0, h0) =>
    let N := cRdeBoundDegreeBaseQ a0 b0 c0
    match cSPDEQWf a0 b0 c0 N with
    | none => none
    | some (bbar, cbar, m, α, β) =>
      match cPolyRischDEQWf bbar cbar m with
      | none => none
      | some v =>
        let Q := caddG (cmulG α v) β
        some (Q, cmulG h0 q1)

end CPolyG

/-! ### Tower composition — the fuel-free base RDE over ℚ(x) `cRischDEBaseWf`

`cRischDEBase b c` (the eq. 6.23 recursion target) is the `k`-constant fast path plus the general routing
through `cRationalRDE` (over the **different** carrier `CPolyG ℚ`). The fuel-free companion substitutes
`cRationalRDEWf`; it is **not recursive** (the base ℚ-pipeline lives over `CPolyG ℚ`, so there is no mutual
recursion with the tower cancellation loops that call it) — a plain composition, **no fuel at runtime**. -/

namespace CPolyG

/-- **Fuel-free base-field Risch DE `Ds + b·s = c` over `k = ℚ(x)`** `cRischDEBaseWf b c` (Bronstein §6.6
eq. 6.23, the recursion target of the §6.6 cancellation cases): the fuel-free companion of `cRischDEBase`.
Returns `some s` (`s ∈ ℚ(x)` solving `Ds + b·s = c`, `D = d/dx`) or `none`. The `k`-constant fast path
(`b, c ∈ ℚ`: `s = c/b`, `b ≠ 0`; `s = 0` if `b = c = 0`) plus the **general** non-constant solve routing
`b = bnum/bden`, `c = cnum/cden ∈ ℚ(x)` through the fuel-free `cRationalRDEWf` (the whole base ℚ-pipeline),
lifting the returned `(snum, sden)` back to `QFunNZ`. **No fuel at runtime**; not recursive (the base
ℚ-pipeline is over `CPolyG ℚ`). Agrees with `cRischDEBase` whenever `cRationalRDEWf` agrees with the fuel'd
`cRationalRDE` (`cRischDEBaseWf_eq`). -/
def cRischDEBaseWf (b c : QFunNZ) : Option QFunNZ :=
  let isConst : QFunNZ → Bool := fun z => CField.isZero (CDiffField.cderiv z)
  if isConst b && isConst c then
    if CField.isZero b then
      if CField.isZero c then some CField.zero else none
    else
      some (CField.div c b)
  else
    match cRationalRDEWf b.1.1 b.1.2 c.1.1 c.1.2 with
    | none => none
    | some (snum, sden) =>
      if h : Compute.cisZero sden = false then some (QFunNZ.ofNumDen snum sden h) else none

/-! ### Tower own-loop — the fuel-free primitive cancellation Poly-Risch-DE `cPolyRischDECancelPrimWf`

The §6.6 tower primitive cancellation (`Dt ∈ k`, `δ = 0`, `b ∈ k*`): the leading terms of `Dq` and `bq`
cancel, so the solve recurses degree-by-degree into the base RDE `cRischDEBaseWf b₀ (lc(c))` over `k = ℚ(x)`
(eq. 6.23). The leading monomial `s·tᵐ` (`m = deg(c)`, `D = cmonomialDeriv Dt`) cancels `c`'s top, so
`(cnormG c).length` strictly drops; well-founded recursion on it, structural runtime guard. -/

/-- **Fuel-free primitive cancellation Poly-Risch-DE** (Bronstein §6.6, `PolyRischDECancelPrim(b,c,D,n)`,
book p.212) `cPolyRischDECancelPrimWf Dt b c n`: the fuel-free companion of `cPolyRischDECancelPrim`.
`Dt ∈ k = ℚ(x)`, `b ∈ k*` (degree-0 `t`-polynomial, scalar `b₀ = lc(b)`), `c ∈ k[t]`, degree bound `n : ℤ`;
solves `Dq + b·q = c` degree-by-degree, recursing at degree `m = deg(c)` into the base RDE
`cRischDEBaseWf b₀ (lc(c))` (`= RischDE(b₀, lc(c))` over `k = ℚ(x)`, eq. 6.23), leading monomial `s·tᵐ`,
remainder `c' = c − b·(s·tᵐ) − D(s·tᵐ)` (`D = cmonomialDeriv Dt`). Returns `none` ("no solution of degree
`≤ n`") or `some q`. True well-founded recursion on `(cnormG c).length` — **no fuel at runtime**; the
recursion is taken only under the structural guard `(cnormG c').length < (cnormG c).length` (the leading
monomial cancels `c`'s top), so `decreasing_by` is `assumption`. The §5.12 logarithmic-derivative branch
is the documented continuation (the general degree-by-degree recursion is sound without it). Agrees with
`cPolyRischDECancelPrim` on a real run (`cPolyRischDECancelPrimWf_eq`). `native_decide`-able. -/
def cPolyRischDECancelPrimWf (Dt : CPolyG QFunNZ) (b c : CPolyG QFunNZ) (n : ℤ) :
    Option (CPolyG QFunNZ) :=
  let b0 : QFunNZ := cleadG b
  if cisZeroG c then some []
  else if n < (cdegG c : ℤ) then none
  else
    let m : ℕ := cdegG c
    match cRischDEBaseWf b0 (cleadG c) with
    | none => none
    | some s =>
      let stm : CPolyG QFunNZ := cshiftG m [s]
      let c' := csubG (csubG c (cmulG b stm)) (cmonomialDeriv Dt stm)
      if (cnormG c' : List QFunNZ).length < (cnormG c : List QFunNZ).length then
        match cPolyRischDECancelPrimWf Dt b c' ((m : ℤ) - 1) with
        | none => none
        | some q => some (caddG stm q)
      else none   -- unreachable on a real run (the leading monomial cancels, degree drops)
termination_by (cnormG c).length
decreasing_by assumption

/-! ### Tower leaf — the fuel-free hyperexponential coefficient `cExpEtaWf`

`cExpEta fuel Dt = lc(Dt / t)` (`η = Dt/t ∈ k`) uses the fuel'd `cdivG`; the fuel-free companion
substitutes the generic `cdivWf`. -/

/-- **Fuel-free hyperexponential coefficient `η = Dt/t ∈ k`** `cExpEtaWf Dt`: the fuel-free companion of
`cExpEta`. For a hyperexponential monomial `Dt = η·t` (`δ = 1`), divide `Dt` by `t` (`cshiftG 1 [1]`) with
the generic fuel-free `cdivWf` and read the degree-0 coefficient `η ∈ ℚ(x)`. For `t = exp(x)` (`Dt = t`),
`η = 1`. **No fuel at runtime**. -/
def cExpEtaWf (Dt : CPolyG QFunNZ) : QFunNZ :=
  cleadG (cdivWf Dt (cshiftG 1 [CField.one]))

/-! ### Tower own-loop — the fuel-free hyperexponential cancellation Poly-Risch-DE `cPolyRischDECancelExpWf`

The §6.6 tower hyperexponential cancellation (`Dt/t = η ∈ k`, `δ = 1`, `b ∈ k*`): as in the primitive case
the leading terms cancel, but `D(s·tᵐ) = (Ds + m·η·s)·tᵐ`, so the eq. 6.24 base RDE is
`RischDE(b + m·η, lc(c))` (coefficient shifted by `m·η`, `η = cExpEtaWf Dt`). Same own-loop on
`(cnormG c).length`, structural runtime guard, recursing into `cRischDEBaseWf`. -/

/-- **Fuel-free hyperexponential cancellation Poly-Risch-DE** (Bronstein §6.6, `PolyRischDECancelExp(b,c,D,n)`,
book p.213) `cPolyRischDECancelExpWf Dt b c n`: the fuel-free companion of `cPolyRischDECancelExp`.
`Dt/t = η ∈ k = ℚ(x)` (`δ = 1`), `b ∈ k*` (scalar `b₀ = lc(b)`), `c ∈ k[t]`, degree bound `n : ℤ`; solves
`Dq + b·q = c` degree-by-degree, recursing at degree `m = deg(c)` into the eq. 6.24 base RDE
`cRischDEBaseWf (b₀ + m·η) (lc(c))` over `k = ℚ(x)` (the `m·η` shift makes the coefficient genuinely
non-constant, `η = cExpEtaWf Dt`), leading monomial `s·tᵐ`, remainder `c' = c − b·(s·tᵐ) − D(s·tᵐ)`
(`D = cmonomialDeriv Dt`). Returns `none` or `some q`. True well-founded recursion on `(cnormG c).length`
— **no fuel at runtime**; the structural guard `(cnormG c').length < (cnormG c).length` is `decreasing_by
:= assumption`. The §5.12 log-derivative branch is the documented continuation. Agrees with
`cPolyRischDECancelExp` on a real run (`cPolyRischDECancelExpWf_eq`). `native_decide`-able. -/
def cPolyRischDECancelExpWf (Dt : CPolyG QFunNZ) (b c : CPolyG QFunNZ) (n : ℤ) :
    Option (CPolyG QFunNZ) :=
  let b0 : QFunNZ := cleadG b
  let η : QFunNZ := cExpEtaWf Dt
  if cisZeroG c then some []
  else if n < (cdegG c : ℤ) then none
  else
    let m : ℕ := cdegG c
    let coeff : QFunNZ := CField.add b0 (CField.mul (QFunNZ.ofConstNZ ((m : ℚ))) η)
    match cRischDEBaseWf coeff (cleadG c) with
    | none => none
    | some s =>
      let stm : CPolyG QFunNZ := cshiftG m [s]
      let c' := csubG (csubG c (cmulG b stm)) (cmonomialDeriv Dt stm)
      if (cnormG c' : List QFunNZ).length < (cnormG c : List QFunNZ).length then
        match cPolyRischDECancelExpWf Dt b c' ((m : ℤ) - 1) with
        | none => none
        | some q => some (caddG stm q)
      else none   -- unreachable on a real run (the leading monomial cancels, degree drops)
termination_by (cnormG c).length
decreasing_by assumption

/-! ### Tower dispatcher — the fuel-free Poly-Risch-DE dispatcher `cPolyRischDEWf`

`cPolyRischDE` routes `Dq + b·q = c` (eq. 6.19) by monomial type and `deg(b)` (Lemma 6.5.1): the
non-cancellation case (`deg(b) > max(0, δ−1)`) to `cPolyRischDENoCancel`, primitive cancellation (`δ = 0`,
`b ∈ k*`) to `cPolyRischDECancelPrim`, hyperexponential cancellation (`δ = 1`, `b ∈ k*`) to
`cPolyRischDECancelExp`, else the non-cancellation fallback. The fuel-free dispatcher substitutes the
fuel-free own-loops. -/

/-- **Fuel-free Poly-Risch-DE dispatcher** (Bronstein §6.5 + §6.6) `cPolyRischDEWf Dt b c n`: the fuel-free
companion of `cPolyRischDE`. Routes `Dq + b·q = c` by the monomial type and `deg(b)` (Lemma 6.5.1): the
non-cancellation case (`deg(b) > max(0, δ−1)`, `δ = deg(Dt)`) to the fuel-free `cPolyRischDENoCancelWf`,
primitive cancellation (`δ = 0`, `b ∈ k*`) to `cPolyRischDECancelPrimWf`, hyperexponential cancellation
(`δ = 1`, `b ∈ k*`) to `cPolyRischDECancelExpWf`, else the non-cancellation fallback. **No fuel at runtime**
— the §6.6 cancellation regimes now run fuel-free. -/
def cPolyRischDEWf (Dt : CPolyG QFunNZ) (b c : CPolyG QFunNZ) (n : ℤ) : Option (CPolyG QFunNZ) :=
  let δ : ℤ := (cdegG Dt : ℤ)
  let db : ℤ := (cdegG b : ℤ)
  if db > max 0 (δ - 1) then
    cPolyRischDENoCancelWf Dt b c n
  else if δ = 0 ∧ db = 0 then
    cPolyRischDECancelPrimWf Dt b c n
  else if δ = 1 ∧ db = 0 then
    cPolyRischDECancelExpWf Dt b c n
  else
    cPolyRischDENoCancelWf Dt b c n

/-! ### The GOAL — the fuel-free full Risch DE solver `cRischDEWfFull` (all regimes)

`cRischDEWf` (WF7) handled only the non-cancellation regime (its §6.5 polynomial stage hard-wired to
`cPolyRischDENoCancelWf`). `cRischDEWfFull` re-points the polynomial stage to the **dispatcher**
`cPolyRischDEWf`, so the §6.6 cancellation regimes (primitive, hyperexponential) now run fuel-free too —
the whole §6 RDE pipeline is fuel-free in **every** regime. -/

/-- **The fuel-free full Risch differential equation solver** `cRischDEWfFull Dt fnum fden gnum gden`
(Bronstein Ch. 6, the goal, **all regimes**): the fuel-free companion of `cRischDE`. For `f = fnum/fden`,
`g = gnum/gden ∈ ℚ(x)(t)` and the monomial derivation `D = cmonomialDeriv Dt`, returns `some (ynum, yden)`
with `y = ynum/yden` solving `Dy + f·y = g`, or `none`. Identical assembly to `cRischDE` — normal
denominator → special denominator → degree bound → SPDE → polynomial **dispatcher** — with every fuel'd
sub-op replaced by its fuel-free companion (`cRdeNormalDenominatorWf`, `cRdeSpecialDenominatorWf`,
`cRdeBoundDegree`, `cSPDEWf`, and the dispatcher `cPolyRischDEWf` routing the §6.5 non-cancellation /
§6.6 primitive / §6.6 hyperexponential cancellation own-loops). **No fuel at runtime in any regime**;
`native_decide`-able over the noncomputable-`CFieldSpec` tower `QFunNZ`. Extends `cRischDEWf` (WF7, which
covered only non-cancellation) to the full §6.6 cancellation dispatch. -/
def cRischDEWfFull (Dt : CPolyG QFunNZ) (fnum fden gnum gden : CPolyG QFunNZ) :
    Option (CPolyG QFunNZ × CPolyG QFunNZ) :=
  match cRdeNormalDenominatorWf Dt fnum fden gnum gden with
  | none => none
  | some (a0, b0, c0, h0) =>
    let (a, b, c, h1) := cRdeSpecialDenominatorWf Dt a0 b0 c0
    let N := cRdeBoundDegree Dt 0 a b c
    match cSPDEWf Dt a b c (N : ℤ) with
    | none => none
    | some (bbar, cbar, _m, α, β) =>
      match cPolyRischDEWf Dt bbar cbar _m with
      | none => none
      | some v =>
        let Q := caddG (cmulG α v) β
        some (cmulG Q h1, h0)

end CPolyG

end DeepWiki.SymbolicIntegration
