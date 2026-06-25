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

/-- **Recursive fraction-free gcd over a tower level**: the *raw* (content-normalized, NOT monic) gcd
`cgcdFFRawGen fuel p q` of `p, q ∈ CPolyG α = α[t]`. The method is the RAW gcd, because that is what the
recursion consumes — the content-gcd `cgcdB` over `CPolyG β = β[s]` must NOT be monic-normalized: making a
GCD-domain content monic scales by `1/lead`, and over the primitive-PRS recursion those reciprocal scalars
COMPOUND (empirically `36 → 57 → 3613 → 10⁸` swell), defeating fraction-freeness. The raw gcd keeps the
natural Euclidean form whose leading coefficient cancels cleanly in pseudo-division (flat `36`). At the
bottom (`α = ℚ`) it is the raw Euclidean gcd `(cgcdExtG _).1` over `ℚ[t]`; at `α = QFunNZG β` it clears
denominators into the GCD-domain `β[s]` and runs the primitive PRS, using the level-`β` `cgcdFFRawGen` as
content-gcd. The public monic gcd is the wrapper `cgcdFFGen := cmonicG ∘ cgcdFFRawGen` (monic-normalize
only at the top). The fraction-free mirror of `CRischField` — bottoms at `CFracGcd ℚ`. -/
class CFracGcd (α : Type*) [CField α] where
  /-- The *raw* (content-normalized, non-monic) fraction-free gcd over `α[t]` — the form the recursion
  consumes as a content-gcd (monic normalization is applied only at the top, by `cgcdFFGen`). -/
  cgcdFFRawGen : ℕ → CPolyG α → CPolyG α → CPolyG α

namespace CFracGcd

variable {α : Type*} [CField α] [CFracGcd α]

/-- **The public monic fraction-free gcd** `cgcdFFGen fuel p q := cmonicG (cgcdFFRawGen fuel p q)` over
`α[t]`: monic-normalize the raw recursive gcd. This is the level-1-agreeing, flat counterpart of `cgcdFF`
— the monic normalization happens once at the top, never inside the recursion (which would compound
`1/lead` scalars and break flatness). -/
def cgcdFFGen (fuel : ℕ) (p q : CPolyG α) : CPolyG α := CPolyG.cmonicG (cgcdFFRawGen fuel p q)

end CFracGcd

/-- **Base `CFracGcd ℚ`** — the bottom of the tower. A `t`-polynomial over `ℚ` is `ℚ[t]`; since `ℚ` is a
field the `ℚ`-content is a unit, so the raw fraction-free gcd is the **raw** Euclidean gcd
`(CPolyG.cgcdExtG _).1` over `ℚ[t]` (NOT the monic `cgcdMonicG` — monic content compounds reciprocal
scalars up the recursion, breaking flatness). Small Euclid, no swell at the constant field. -/
instance instCFracGcdQ : CFracGcd ℚ where
  cgcdFFRawGen fuel p q := (CPolyG.cgcdExtG fuel p q).1

section
variable {β : Type*} [CField β] [CFieldDomain β] [CFracGcd β]

/-- **★ `CFracGcd (QFunNZG β)`** — the *raw* fraction-free gcd over `β(s)[t]`, **built by running
`cprimPRSgcdGen` over the GCD-domain `CPolyG β = β[s]`** with the level-`β` `cgcdFFRawGen` as the
content-gcd. This ties the tower recursion: clear denominators of both inputs into `GBPoly β = (β[s])[t]`,
order them by `t`-degree (the PRS needs the larger first), run the primitive PRS (gcd up to `β[s]`-content)
with `cgcdB := CFracGcd.cgcdFFRawGen` recursing one level down, and lift the result back to `β(s)[t]` — **no
`cmonicG`** (this is the raw method; the public `cgcdFFGen` monic-normalizes at the top). The Euclidean
work is fraction-free in the GCD-domain `β[s]`, avoiding the `β(s)`-coefficient swell of `cgcdExtG`.
Computable (`Prop`-erased subtype proofs), so it `native_decide`s; recurses strictly one level down,
bottoming at `CFracGcd ℚ`. The fraction-free mirror of `instCRischFieldQFunNZG`. -/
instance instCFracGcdQFunNZG : CFracGcd (QFunNZG β) where
  cgcdFFRawGen fuel p q :=
    let P := CPolyG.cclearDenomsG p
    let Q := CPolyG.cclearDenomsG q
    let (P, Q) := if GBPoly.gbdeg P < GBPoly.gbdeg Q then (Q, P) else (P, Q)
    CPolyG.liftGBPolyG (cprimPRSgcdGen (CFracGcd.cgcdFFRawGen fuel) fuel P Q)

end

/-! ### ★ MILESTONE — the generic FF gcd at LEVEL 1: agreement with `cgcdFF`, and FLATNESS

Level 1 is `α = QFunNZG ℚ ≅ ℚ(x)`. The recursive `instCFracGcdQFunNZG` clears denominators into the
GCD-domain `CPolyG ℚ = ℚ[x]` and runs `cprimPRSgcdGen` with the **base** content-gcd `CFracGcd.cgcdFFGen`
at `ℚ` = the monic Euclidean gcd over `ℚ[x]` — exactly the strategy `cgcdFF` hardwires for the concrete
`QFunNZ`. We replay `ComputableTowerBench`'s coefficient-swell witness over `QFunNZG ℚ`:

* **(a) AGREEMENT** — `cgcdFFGen` over `QFunNZG ℚ` returns the same monic gcd `cgcdFF` does (`commonFactor`,
  degree 2): both equal the monic `t² + (x − 1/x)·t − 1` of the benchmark, checked by `native_decide`.
* **(b) FLATNESS** — the raw stored size of `cgcdFFGen`'s result stays O(1) in cofactor degree (the same
  `36`-class as `cgcdFF`), where `cgcdExtG` swells `147 → 2.6·10¹¹`. THE perf deliverable.

The benchmark inputs are rebuilt over `QFunNZG ℚ` (carrier `QFunG ℚ = Compute.QFun`, `rfl`), with the
same `commonFactor`/cofactor structure as `Bench`. -/

namespace BenchG

open CPolyG QFunNZG

/-- Build a `QFunNZG ℚ` ℚ(x)-coefficient `num/den` (coefficient lists low→high in `x`), denominator
nonzero by `decide` — the level-1 generic mirror of `Bench.qc`. Falls back to `0/1` if the denominator
degenerates. -/
def gqc (num den : CPolyG ℚ) (h : CPolyG.cisZeroG den = false := by decide) : QFunNZG ℚ :=
  ⟨(num, den), h⟩

/-- The ℚ(x) coefficient `x` as a `QFunNZG ℚ`. -/
def gcX : QFunNZG ℚ := gqc [0, 1] [1]
/-- The ℚ(x) coefficient `1/x` (a genuine denominator). -/
def gcInvX : QFunNZG ℚ := gqc [1] [0, 1]
/-- The ℚ(x) coefficient `x + 1`. -/
def gcXp1 : QFunNZG ℚ := gqc [1, 1] [1]
/-- The ℚ(x) coefficient `1/(x + 1)`. -/
def gcInvXp1 : QFunNZG ℚ := gqc [1] [1, 1]
/-- The ℚ(x) coefficient `x − 1`. -/
def gcXm1 : QFunNZG ℚ := gqc [-1, 1] [1]

/-- `(1 : QFunNZG ℚ)` shorthand for building monic cofactors. -/
def gOne : QFunNZG ℚ := qoneNZG
/-- Negate a `QFunNZG ℚ` coefficient (denominator unchanged). -/
def gNeg (z : QFunNZG ℚ) : QFunNZG ℚ := qnegNZG z

/-- A linear `t`-polynomial `a0 + a1·t` as a `CPolyG (QFunNZG ℚ)` (low→high in `t`). -/
def glin (a0 a1 : QFunNZG ℚ) : CPolyG (QFunNZG ℚ) := [a0, a1]

/-- The fixed gcd target `(t + x)·(t − 1/x)` over `QFunNZG ℚ` — degree 2 in `t`, ℚ(x) coefficients with
genuine denominators (the level-1 mirror of `Bench.commonFactor`). -/
def gCommonFactor : CPolyG (QFunNZG ℚ) :=
  cmulG (glin gcX gOne) (glin (gNeg gcInvX) gOne)

/-- The cofactor-coefficient cycle for `p` (period 5: `x`, `1/x`, `x+1`, `1/(x+1)`, `x−1`). -/
def gcycCoefA : ℕ → QFunNZG ℚ
  | 0 => gcX | 1 => gcInvX | 2 => gcXp1 | 3 => gcInvXp1 | 4 => gcXm1 | n + 5 => gcycCoefA n

/-- The cofactor-coefficient cycle for `q` (phase-shifted, coprime to `gcycCoefA`). -/
def gcycCoefB : ℕ → QFunNZG ℚ
  | 0 => gcInvXp1 | 1 => gcXm1 | 2 => gcX | 3 => gcInvX | 4 => gcXp1 | n + 5 => gcycCoefB n

/-- The `p`-cofactor `∏_{i<k} (t + gcycCoefA i)`, a `t`-polynomial of degree `k`. -/
def glinProdA : ℕ → CPolyG (QFunNZG ℚ)
  | 0 => [gOne]
  | n + 1 => cmulG (glin (gcycCoefA n) gOne) (glinProdA n)

/-- The `q`-cofactor `∏_{i<k} (t − gcycCoefB i)`, a `t`-polynomial of degree `k` coprime to
`glinProdA k`. -/
def glinProdB : ℕ → CPolyG (QFunNZG ℚ)
  | 0 => [gOne]
  | n + 1 => cmulG (glin (gNeg (gcycCoefB n)) gOne) (glinProdB n)

/-- The benchmark dividend `p = gCommonFactor · glinProdA k` over `QFunNZG ℚ`, total `t`-degree `k + 2`. -/
def gBenchP (k : ℕ) : CPolyG (QFunNZG ℚ) := cmulG gCommonFactor (glinProdA k)

/-- The benchmark divisor `q = gCommonFactor · glinProdB k` over `QFunNZG ℚ`, total `t`-degree `k + 2`;
`gcd(gBenchP k, gBenchQ k) = gCommonFactor` (degree 2). -/
def gBenchQ (k : ℕ) : CPolyG (QFunNZG ℚ) := cmulG gCommonFactor (glinProdB k)

/-- The GENERIC fraction-free gcd of the benchmark pair over `QFunNZG ℚ` (`CFracGcd.cgcdFFGen`, level 1).
The flat kernel under test. -/
def gBenchFFGcd (k : ℕ) : CPolyG (QFunNZG ℚ) := CFracGcd.cgcdFFGen 60 (gBenchP k) (gBenchQ k)

/-! #### The swell measure over `QFunNZG ℚ` (mirror of `Bench.gcdSizeRaw`) -/

/-- The raw stored size of one `QFunNZG ℚ` coefficient: total numerator/denominator list lengths plus the
sum of `|num| + den` of each ℚ entry — the level-1 mirror of `Bench.coeffSizeRaw`. -/
def gCoeffSizeRaw (z : QFunNZG ℚ) : ℕ :=
  z.1.1.length + z.1.2.length +
    (z.1.1.foldl (fun a c => a + c.num.natAbs + c.den) 0) +
    (z.1.2.foldl (fun a c => a + c.num.natAbs + c.den) 0)

/-- The raw stored size of a whole `CPolyG (QFunNZG ℚ)` (`gCoeffSizeRaw` summed over coefficients, plus
the `t`-length) — the level-1 mirror of `Bench.gcdSizeRaw`. Forcing it fully evaluates the gcd. -/
def gGcdSizeRaw (g : CPolyG (QFunNZG ℚ)) : ℕ :=
  (g : List (QFunNZG ℚ)).foldl (fun a z => a + gCoeffSizeRaw z) g.length

/-- **Translate a concrete `QFunNZ` coefficient into `QFunNZG ℚ`** — the underlying pair carrier is the
same (`QFunG ℚ = Compute.QFun`, `rfl`); only the den-nonzero predicate changes from `toPoly _ ≠ 0` to the
equivalent `cisZeroG _ = false`, re-derived via `cisZeroG_eq_cisZero`/`cisZero_iff_toPoly_eq_zero`. Lets
the `cgcdFF` (over `QFunNZ`) answer be compared against the generic `cgcdFFGen` (over `QFunNZG ℚ`). -/
def ofQFunNZ (z : QFunNZ) : QFunNZG ℚ :=
  ⟨z.1, by
    rw [CPolyG.cisZeroG_eq_cisZero, Bool.eq_false_iff, Ne]
    intro hc
    exact z.2 ((Compute.cisZero_iff_toPoly_eq_zero z.1.2).mp hc)⟩

/-- The concrete `cgcdFF` answer (over `QFunNZ`), translated coefficientwise into `CPolyG (QFunNZG ℚ)` via
`ofQFunNZ`, for the level-1 agreement comparison. -/
def benchFFGcdG (k : ℕ) : CPolyG (QFunNZG ℚ) := (Bench.benchFFGcd k).map ofQFunNZ

end BenchG

/-! #### The pinned witnesses (`native_decide`) -/

open BenchG in
/-- **The generic FF gcd is degree 2 at level 1** (`native_decide`): `cgcdFFGen` over `QFunNZG ℚ` returns
the associate of `gCommonFactor`, so cofactor scaling does not change the answer — only the intermediate
coefficient size, which the flatness witness measures. -/
theorem gBenchFFGcd_deg_two : CPolyG.cdegG (gBenchFFGcd 2) = 2 := by native_decide

open BenchG in
/-- **★ (a) AGREEMENT — the generic `cgcdFFGen` matches `cgcdFF` at level 1** (`native_decide`). Both the
generic fraction-free gcd over `QFunNZG ℚ` (`gBenchFFGcd 2`, monic) and the QFunNZ-specific `cgcdFF`
(`Bench.benchFFGcd 2`, monic) equal the same monic degree-2 gcd `t² + (x − 1/x)·t − 1` of the benchmark
`commonFactor` — checked by `cisZeroG` of the difference, after re-reading the `QFunNZ` answer's
numerator/denominator pairs as `QFunNZG ℚ` coefficients (carrier `QFunG ℚ = Compute.QFun`, `rfl`). So the
generalized engine computes the **same gcd** as the working `cgcdFF`. -/
theorem gBenchFFGcd_agrees_cgcdFF :
    CPolyG.cisZeroG (CPolyG.csubG (CPolyG.cmonicG (gBenchFFGcd 2))
      (CPolyG.cmonicG (benchFFGcdG 2))) = true := by native_decide

open BenchG in
/-- **★ (b) FLATNESS — the generic FF result size stays flat at level 1** (`native_decide`, THE perf
deliverable): the raw stored coefficient size of the generic `cgcdFFGen` over `QFunNZG ℚ` is the constant
`36` at cofactor degree 3, 4, AND 5 — no swell — **exactly** the `cgcdFF` flat value (`36`/`36`,
`Bench.benchFFGcd_size_flat`), where the naive Euclidean `cgcdExtG` swells `147 → 2.6·10¹¹ → 10¹⁴⁷`
(`Bench.benchExtGcd_size_swells`). The generalized fraction-free strategy keeps the tower gcd
polynomial-sized — the QFunNZ-specific `cgcdFF` is no longer needed for flatness. -/
theorem gBenchFFGcd_size_flat :
    gGcdSizeRaw (gBenchFFGcd 1) = 36 ∧ gGcdSizeRaw (gBenchFFGcd 2) = 36
    ∧ gGcdSizeRaw (gBenchFFGcd 3) = 36 := by native_decide

end DeepWiki.SymbolicIntegration
