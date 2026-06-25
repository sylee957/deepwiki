import DeepWiki.SymbolicIntegration.ComputableTowerField
import DeepWiki.SymbolicIntegration.ComputableSplitFactorFast
import DeepWiki.SymbolicIntegration.ComputableTowerBench

/-! # Generic fraction-free gcd over a tower level — the flat unification of `cgcdFF`
The benchmark (`ComputableTowerBench`) proved the generic Euclidean gcd `cgcdExtG` over the fraction
field ℚ(x) suffers **super-exponential** coefficient swell (stored size 147 → 2.6·10¹¹ at cofactor
degree 3→4), while the QFunNZ-specific fraction-free `cgcdFF` (`ComputableSplitFactorFast`) stays
**flat** (size 36). This file generalizes `cgcdFF`'s fraction-free strategy off its `ℚ[x][t]`-specific
`BPoly` to an **arbitrary** tower level.

The math (why this stays flat). The fraction-free gcd over `α[t]` where `α = Frac(R)` (`R` a GCD
domain): (1) CLEAR DENOMINATORS — multiply each `α`-coefficient through by the product of the
denominators, landing in `R[t]`; (2) PRIMITIVE PRS over `R[t]` — pseudo-remainder, then strip the
`R`-content (gcd of the `R`-coefficients) each step, so coefficients never accumulate fractions. For the
TOWER, `α = QFunNZG β = β(s) = Frac(CPolyG β = β[s])`, so `R = CPolyG β = β[s]`, and the content-gcd over
`R` is the fraction-free gcd over `β[s]` — which **recurses** to level `β`, bottoming at ℚ[x] (content
over ℚ trivial). This recursion has the SAME shape as the working `CRischField` RDE oracle.

The pieces:
* **Generic BPoly** `GBPoly B := List (CPolyG B)` = `(B[s])[t]` — a `t`-polynomial whose coefficients
  are `CPolyG B = B[s]`. The `gb*` ops (`gbnorm`/`gbpsremainder`/`gbcontent`/`gbprimitivePart`) are the
  generalizations of `Compute.bnorm`/`bpsremainder`/`bcontentX`/`bprimitivePartX` (which were hardwired
  to `CPoly = CPolyG ℚ` coefficients) to generic `[CField B]` `CPolyG B`-coefficients, with the
  content-gcd `cgcdB : CPolyG B → CPolyG B → CPolyG B` PASSED IN.
* **`cprimPRSgcdGen cgcdB`** — the generic primitive PRS, mirroring `primPRSgcd`.
* **`class CFracGcd α`** — the recursive fraction-free gcd `cgcdFFGen : ℕ → CPolyG α → CPolyG α →
  CPolyG α` over `α[t]`, base instance at the bottom (Euclidean over ℚ[x]), recursive
  `instance CFracGcd (QFunNZG β) [CFracGcd β]` running `cprimPRSgcdGen` with the level-`β` `cgcdFFGen` as
  content-gcd — exactly mirroring `instCRischFieldQFunNZG`.

The deliverables (validated by `native_decide`, like the rest of the tower engine — abstract
correctness is the documented next step): the generic FF gcd AGREES with `cgcdFF` at level 1, and a
swell-flatness witness shows its stored size stays O(1) in cofactor degree where `cgcdExtG` blows up. -/

namespace DeepWiki.SymbolicIntegration

open Compute

variable {B : Type*} [CField B]

/-! ### The generic bivariate carrier `GBPoly B = List (CPolyG B)` (`(B[s])[t]`)

`GBPoly B := List (CPolyG B)` is a `t`-polynomial whose coefficients are `CPolyG B = B[s]` (index =
`t`-degree, low→high), the generic mirror of `Compute.BPoly = List CPoly = ℚ[t][x]` but with the inner
ring `CPolyG B` instead of the concrete `CPoly = CPolyG ℚ`. The `gb*` arithmetic delegates each
coefficient operation to the generic engine `caddG`/`cmulG`/`cnegG`/`cisZeroG`/`cnormG` over `CPolyG B`,
so it needs only `[CField B]` and reduces in the native compiler. -/

/-- **Generic bivariate dense carrier** `GBPoly B := List (CPolyG B)` = a `t`-polynomial whose
coefficients are `CPolyG B = B[s]` (index = `t`-degree, low→high). The generic mirror of `Compute.BPoly`,
with the inner ring `CPolyG B` in place of `CPoly = CPolyG ℚ`. -/
abbrev GBPoly (B : Type*) [CField B] := List (CPolyG B)

namespace GBPoly

/-- **Normalize** a `GBPoly`: `cnormG` each coefficient, then strip trailing (high-`t`-degree)
`cisZeroG` coefficients, so the zero polynomial becomes `[]`. The generic mirror of `Compute.bnorm`. -/
def gbnorm : GBPoly B → GBPoly B
  | [] => []
  | a :: as =>
    let a := CPolyG.cnormG a
    match gbnorm as with
    | [] => if CPolyG.cisZeroG a then [] else [a]
    | r => a :: r

/-- **Coefficientwise addition** of two `GBPoly`s in `t` (each `t`-coefficient added via `caddG`). -/
def gbadd : GBPoly B → GBPoly B → GBPoly B
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => CPolyG.caddG a b :: gbadd as bs

/-- **Negation** of a `GBPoly`, each `t`-coefficient negated via `cnegG`. -/
def gbneg (p : GBPoly B) : GBPoly B := p.map CPolyG.cnegG

/-- **Subtraction** of `GBPoly`s, `p − q := p + (−q)`. -/
def gbsub (p q : GBPoly B) : GBPoly B := gbadd p (gbneg q)

/-- **Scale by a `CPolyG B`** (a `B[s]` scalar) `gbscaleC c p`: multiply every `t`-coefficient by `c`
via the inner `cmulG`. -/
def gbscaleC (c : CPolyG B) (p : GBPoly B) : GBPoly B := p.map (CPolyG.cmulG c)

/-- **Shift in `t`** `gbshift k p = tᵏ · p`: prepend `k` zero (`= []`) `t`-coefficients. -/
def gbshift : ℕ → GBPoly B → GBPoly B
  | 0, p => p
  | n + 1, p => [] :: gbshift n p

/-- **Zero test** for a `GBPoly`: `true` iff it normalizes to `[]` (via `List.isEmpty`, so no `BEq B`
is needed — matching `cisZeroG`). -/
def gbisZero (p : GBPoly B) : Bool := (gbnorm p).isEmpty

/-- **`t`-degree** of a `GBPoly` as a `ℕ`: `(length of gbnorm p) − 1`, with `gbdeg 0 = 0` (paired with
`gbisZero` at call sites). -/
def gbdeg (p : GBPoly B) : ℕ := (gbnorm p).length - 1

/-- **Leading `t`-coefficient** `gblc p ∈ CPolyG B` (`= B[s]`): the top nonzero `t`-coefficient, `[]`
(zero) for the zero polynomial. -/
def gblc (p : GBPoly B) : CPolyG B := (gbnorm p).getLast?.getD []

/-! ### Pseudo-division over the coefficient ring `CPolyG B = B[s]` -/

/-- **Pseudo-remainder** `gbpsremainder fuel p q = prem(p, q)` over the non-field coefficient ring
`CPolyG B = B[s]`: while `deg p ≥ deg q`, replace `p` by `lc(q)·p − lc(p)·tᵏ·q` (`k = deg p − deg q`),
staying in `GBPoly B` (no `B[s]` division). The generic mirror of `Compute.bpsremainder`. Fuel-bounded
(one step per `t`-degree drop). -/
def gbpsremainder : ℕ → GBPoly B → GBPoly B → GBPoly B
  | 0, p, _ => gbnorm p
  | fuel + 1, p, q =>
    let p := gbnorm p
    let q := gbnorm q
    if gbisZero q then gbnorm p
    else if p.length < q.length then p
    else
      let k := p.length - q.length
      let lcq := gblc q
      let lcp := gblc p
      -- `lc(q)·p − lc(p)·tᵏ·q`: kills the leading term, stays in `B[s][t]`.
      let p' := gbnorm (gbsub (gbscaleC lcq p) (gbscaleC lcp (gbshift k q)))
      gbpsremainder fuel p' q

/-! ### `B[s]`-content management (`cgcdB` = the content-gcd, passed in)

The content-gcd `cgcdB : CPolyG B → CPolyG B → CPolyG B` over the coefficient ring `CPolyG B = B[s]` is
PASSED IN — for the tower it is the level-`β` fraction-free gcd `cgcdFFGen`, recursing one level down.
The content division is the generic Euclidean `cdivG` over `CPolyG B` (exact: the content divides every
coefficient). -/

/-- **`B[s]`-content** of a `GBPoly` (relative to a content-gcd `cgcdB`): fold `cgcdB` over all the
`t`-coefficients — the common `CPolyG B = B[s]` factor of the polynomial in `t`. The generic mirror of
`Compute.bcontentX`, with `cgcdB` in place of the hardwired `cgcdExt`. -/
def gbcontent (cgcdB : CPolyG B → CPolyG B → CPolyG B) (p : GBPoly B) : CPolyG B :=
  (gbnorm p).foldl (fun g c => cgcdB g c) []

/-- **Strip the `B[s]`-content in `t`** `gbprimitivePart fuel cgcdB p = p / content_t(p)`: divide every
`t`-coefficient by the content (exact generic Euclidean `cdivG` over `CPolyG B`), giving the `B[s]`-
primitive part. Leaves `[]` (and content `[]`) unchanged. The generic mirror of
`Compute.bprimitivePartX`. -/
def gbprimitivePart (fuel : ℕ) (cgcdB : CPolyG B → CPolyG B → CPolyG B) (p : GBPoly B) : GBPoly B :=
  let p := gbnorm p
  let g := gbcontent cgcdB p
  if CPolyG.cisZeroG g then p else gbnorm (p.map (fun c => CPolyG.cdivG fuel c g))

end GBPoly

/-! ### The generic fraction-free gcd kernel — the primitive PRS over `CPolyG B = B[s]`

`cprimPRSgcdGen cgcdB fuel P Q` is the gcd of `P, Q` in `t` (over the coefficient ring `CPolyG B = B[s]`),
up to a `B[s]`-content factor, the generic mirror of `primPRSgcd` (`ComputableSplitFactorFast`). Each step
takes the **primitive part** of the **pseudo-remainder** (`gbprimitivePart (gbpsremainder P Q)`), keeping
every coefficient in `B[s]` (no field division, so no `β(s)` swell); the last nonzero primitive remainder
is the gcd. The content-gcd `cgcdB` is passed in (for the tower, the level-`β` `cgcdFFGen`). -/

/-- **Generic primitive polynomial-remainder sequence** `cprimPRSgcdGen cgcdB fuel P Q ∈ GBPoly B`: the
gcd of `P, Q` in `t` (over the coefficient ring `CPolyG B = B[s]`), up to a `B[s]`-content factor. Each
step takes the primitive part of the pseudo-remainder; the last nonzero primitive remainder is the gcd.
Requires `gbdeg P ≥ gbdeg Q`; fuel-bounded (one step per `t`-degree drop). The generic mirror of
`primPRSgcd`, with `cgcdB` the content-gcd. -/
def cprimPRSgcdGen (cgcdB : CPolyG B → CPolyG B → CPolyG B) : ℕ → GBPoly B → GBPoly B → GBPoly B
  | 0, P, _ => GBPoly.gbprimitivePart 30 cgcdB P
  | fuel + 1, P, Q =>
    let P := GBPoly.gbnorm P
    let Q := GBPoly.gbnorm Q
    if GBPoly.gbisZero Q then GBPoly.gbprimitivePart 30 cgcdB P
    else
      let r := GBPoly.gbprimitivePart 30 cgcdB (GBPoly.gbpsremainder 60 P Q)
      cprimPRSgcdGen cgcdB fuel Q r

/-! ### Clear denominators `CPolyG (QFunNZG β) ↔ GBPoly β` (`β(s)[t] ↔ (β[s])[t]`)

For the tower level `α = QFunNZG β = Frac(CPolyG β = β[s])`, a `t`-polynomial over `α` is a `CPolyG α`
whose coefficients are `QFunNZG β` fractions (numerator/denominator pairs in `CPolyG β`). `cclearDenomsG`
multiplies through by the product of the coefficient denominators, landing in `GBPoly β = (β[s])[t]`
(each `t`-coefficient a `CPolyG β = β[s]`) — the generic mirror of `CPolyG.clearDenoms`. The embed-back
`liftGBPolyG` re-reads a `GBPoly β` coefficient `c : CPolyG β` as the fraction `c/1 ∈ QFunNZG β`. -/

namespace CPolyG

variable {β : Type*} [CField β] [CFieldDomain β]

/-- The numerator `CPolyG β` of a `QFunNZG β` coefficient. -/
def qnumCoeffG (c : QFunNZG β) : CPolyG β := c.1.1

/-- The denominator `CPolyG β` of a `QFunNZG β` coefficient. -/
def qdenCoeffG (c : QFunNZG β) : CPolyG β := c.1.2

/-- **Clear denominators** `cclearDenomsG p ∈ GBPoly β` (`= (β[s])[t]`): multiply the `t`-polynomial `p`
over `α = QFunNZG β` through by the product of its coefficient denominators, so coefficient `i` becomes
`numᵢ · ∏_{j≠i} denⱼ ∈ CPolyG β = β[s]`. Carries `p` from `β(s)[t]` to `(β[s])[t]` up to the (cleared)
common-denominator unit. The generic mirror of `CPolyG.clearDenoms`. -/
def cclearDenomsG (p : CPolyG (QFunNZG β)) : GBPoly β :=
  let cs : List (QFunNZG β) := p
  let dens : List (CPolyG β) := cs.map qdenCoeffG
  cs.zipIdx.map (fun (ci, i) =>
    let prodOthers := (dens.zipIdx.filter (fun (_, j) => j ≠ i)).foldl
      (fun acc (d, _) => CPolyG.cmulG acc d) [CField.one]
    CPolyG.cmulG (qnumCoeffG ci) prodOthers)

/-- **Lift back** `liftGBPolyG p ∈ CPolyG (QFunNZG β)`: read each `CPolyG β = β[s]` coefficient `c` of a
`GBPoly β` as the `QFunNZG β` fraction `c/1` (numerator `c`, denominator `[1]`). The generic mirror of
`CPolyG.liftBPolyToQFunNZ`. -/
def liftGBPolyG (p : GBPoly β) : CPolyG (QFunNZG β) :=
  p.map (fun c => (⟨(c, [CField.one]), QFunNZG.cisZeroG_one_singleton⟩ : QFunNZG β))

end CPolyG

/-! ### `class CFracGcd α` — the recursive fraction-free gcd over `α[t]`

The recursion that ties the tower, mirroring `CRischField` / `instCRischFieldQFunNZG` exactly:
* **`class CFracGcd α`** (one method `cgcdFFGen : ℕ → CPolyG α → CPolyG α → CPolyG α`, the fraction-free,
  monic-normalized gcd over `α[t]`).
* **Base `instance CFracGcd ℚ`** — the bottom. A `t`-polynomial over `ℚ` is `ℚ[t]`; `ℚ` is a field, so the
  content is trivial and the fraction-free gcd is the monic Euclidean gcd `cgcdMonicG`.
* **Recursive `instance CFracGcd (QFunNZG β) [CFracGcd β]`** — clear denominators of both inputs into
  `GBPoly β = (β[s])[t]`, run `cprimPRSgcdGen` with the content-gcd `cgcdB :=` the level-`β` `cgcdFFGen`
  (recursing one level down, over `CPolyG β = β[s]`), lift back, monic-normalize. Bottoms at `CFracGcd ℚ`.

This is `cgcdFF`'s strategy generalized off the concrete `ℚ(x)` carrier: the Euclidean work stays
**fraction-free** in the GCD-domain `CPolyG β`, so the coefficients do not swell the way `cgcdExtG` over
the fraction field `β(s)` does. -/

/-- **Recursive fraction-free gcd over a tower level**: one method `cgcdFFGen fuel p q` = the
fraction-free, monic-normalized gcd of `p, q ∈ CPolyG α = α[t]`. At the bottom (`α = ℚ`) it is the monic
Euclidean gcd (trivial content over a field); at `α = QFunNZG β` it clears denominators into the
GCD-domain `β[s]` and runs the primitive PRS, using the level-`β` `cgcdFFGen` as the content-gcd. The
fraction-free mirror of `CRischField` — the recursion bottoms at `CFracGcd ℚ`. -/
class CFracGcd (α : Type*) [CField α] where
  /-- The fraction-free, monic-normalized gcd over `α[t]`. -/
  cgcdFFGen : ℕ → CPolyG α → CPolyG α → CPolyG α

/-- **Base `CFracGcd ℚ`** — the bottom of the tower. A `t`-polynomial over `ℚ` is `ℚ[t]`; since `ℚ` is a
field the `ℚ`-content is a unit, so the fraction-free gcd is just the monic Euclidean gcd
`CPolyG.cgcdMonicG` over `ℚ[t]`. The recursion's base case (`cgcdExtG`/`cmonicG`, small Euclid — no
swell at the constant field). -/
instance instCFracGcdQ : CFracGcd ℚ where
  cgcdFFGen fuel p q := CPolyG.cgcdMonicG fuel p q

section
variable {β : Type*} [CField β] [CFieldDomain β] [CFracGcd β]

/-- **★ `CFracGcd (QFunNZG β)`** — the fraction-free gcd over `β(s)[t]`, **built by running
`cprimPRSgcdGen` over the GCD-domain `CPolyG β = β[s]`** with the level-`β` `cgcdFFGen` as the content-gcd.
This ties the tower recursion: clear denominators of both inputs into `GBPoly β = (β[s])[t]`, order them by
`t`-degree (the PRS needs the larger first), run the primitive PRS (gcd up to `β[s]`-content) with
`cgcdB := CFracGcd.cgcdFFGen` recursing one level down, lift the result back to `β(s)[t]` and
monic-normalize. The Euclidean work is fraction-free in the GCD-domain `β[s]`, avoiding the `β(s)`-
coefficient swell of `cgcdExtG`. Computable (`Prop`-erased subtype proofs), so it `native_decide`s;
recurses strictly one level down, bottoming at `CFracGcd ℚ`. The fraction-free mirror of
`instCRischFieldQFunNZG`. -/
instance instCFracGcdQFunNZG : CFracGcd (QFunNZG β) where
  cgcdFFGen fuel p q :=
    let P := CPolyG.cclearDenomsG p
    let Q := CPolyG.cclearDenomsG q
    let (P, Q) := if GBPoly.gbdeg P < GBPoly.gbdeg Q then (Q, P) else (P, Q)
    CPolyG.cmonicG (CPolyG.liftGBPolyG (cprimPRSgcdGen (CFracGcd.cgcdFFGen fuel) fuel P Q))

end

end DeepWiki.SymbolicIntegration
