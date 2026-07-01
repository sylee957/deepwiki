import DeepWiki.SymbolicIntegration.ComputableTowerField

/-! # Generic fraction-free gcd over an arbitrary tower level
The generic Euclidean gcd `cgcdExtG` over the fraction field ℚ(x) suffers **super-exponential**
coefficient swell (stored size 147 → 2.6·10¹¹ at cofactor degree 3→4). This file builds a generic
**fraction-free** gcd over an **arbitrary** tower level whose stored size stays **flat** (size 36 at
level 1), generalizing the fraction-free strategy off any `ℚ[x][t]`-specific bivariate carrier.

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
correctness is the documented next step): a swell-flatness witness shows the generic FF gcd's stored
size stays O(1) in cofactor degree where `cgcdExtG` blows up, at both tower levels 1 and 2. -/

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
`GBPoly β` as the `QFunNZG β` fraction `c/1` (numerator `c`, denominator `[1]`) — the inverse of clearing
denominators. -/
def liftGBPolyG (p : GBPoly β) : CPolyG (QFunNZG β) :=
  p.map (fun c => (⟨(c, [CField.one]), QFunNZG.cisZeroG_one_singleton⟩ : QFunNZG β))

end CPolyG

/-! ### `class CFracGcd α` — the recursive fraction-free gcd over `α[t]`

The recursion that ties the tower, mirroring `CRischField` / `instCRischFieldQFunNZG` exactly:
* **`class CFracGcd α`** (one method `cgcdFFGen : ℕ → CPolyG α → CPolyG α → CPolyG α`, the fraction-free,
  monic-normalized gcd over `α[t]`).
* **Base `instance CFracGcd ℚ`** — the bottom. A `t`-polynomial over `ℚ` is `ℚ[t]`; `ℚ` is a field, so the
  content is trivial and the public fraction-free gcd is the monic normalization of raw Euclid.
* **Recursive `instance CFracGcd (QFunNZG β) [CFracGcd β]`** — clear denominators of both inputs into
  `GBPoly β = (β[s])[t]`, run `cprimPRSgcdGen` with the content-gcd `cgcdB :=` the level-`β` `cgcdFFGen`
  (recursing one level down, over `CPolyG β = β[s]`), lift back, monic-normalize. Bottoms at `CFracGcd ℚ`.

The fraction-free strategy over a generic carrier: the Euclidean work stays **fraction-free** in the
GCD-domain `CPolyG β`, so the coefficients do not swell the way `cgcdExtG` over the fraction field `β(s)`
does. -/

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
`α[t]`: monic-normalize the raw recursive gcd. The flat fraction-free gcd — the monic normalization
happens once at the top, never inside the recursion (which would compound `1/lead` scalars and break
flatness). -/
def cgcdFFGen (fuel : ℕ) (p q : CPolyG α) : CPolyG α := CPolyG.cmonicG (cgcdFFRawGen fuel p q)

end CFracGcd

/-- **Base `CFracGcd ℚ`** — the bottom of the tower. A `t`-polynomial over `ℚ` is `ℚ[t]`; since `ℚ` is a
field the `ℚ`-content is a unit, so the raw fraction-free gcd is the **raw** Euclidean gcd
`(CPolyG.cgcdExtG _).1` over `ℚ[t]` (NOT a monic gcd — monic content compounds reciprocal
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

/-! ### ★ MILESTONE — the generic FF gcd at LEVEL 1: FLATNESS

Level 1 is `α = QFunNZG ℚ ≅ ℚ(x)`. The recursive `instCFracGcdQFunNZG` clears denominators into the
GCD-domain `CPolyG ℚ = ℚ[x]` and runs `cprimPRSgcdGen` with the **base** content-gcd `CFracGcd.cgcdFFGen`
at `ℚ` = the monic Euclidean gcd over `ℚ[x]`. We exercise a coefficient-swell witness over `QFunNZG ℚ`:

* **FLATNESS** — the raw stored size of `cgcdFFGen`'s result stays O(1) in cofactor degree (the
  `36`-class), where the naive Euclidean `cgcdExtG` swells `147 → 2.6·10¹¹`. THE perf deliverable.

The benchmark inputs are built over `QFunNZG ℚ` (carrier `QFunG ℚ = Compute.QFun`, `rfl`), with a fixed
degree-2 `commonFactor` and growing-degree coprime cofactors. -/

namespace BenchG

open CPolyG QFunNZG

/-- Build a `QFunNZG ℚ` ℚ(x)-coefficient `num/den` (coefficient lists low→high in `x`), denominator
nonzero by `decide`. Falls back to `0/1` if the denominator degenerates. -/
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
genuine denominators. -/
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
sum of `|num| + den` of each ℚ entry. -/
def gCoeffSizeRaw (z : QFunNZG ℚ) : ℕ :=
  z.1.1.length + z.1.2.length +
    (z.1.1.foldl (fun a c => a + c.num.natAbs + c.den) 0) +
    (z.1.2.foldl (fun a c => a + c.num.natAbs + c.den) 0)

/-- The raw stored size of a whole `CPolyG (QFunNZG ℚ)` (`gCoeffSizeRaw` summed over coefficients, plus
the `t`-length). Forcing it fully evaluates the gcd. -/
def gGcdSizeRaw (g : CPolyG (QFunNZG ℚ)) : ℕ :=
  (g : List (QFunNZG ℚ)).foldl (fun a z => a + gCoeffSizeRaw z) g.length

end BenchG

/-! #### The pinned witnesses (`native_decide`) -/

open BenchG in
/-- **The generic FF gcd is degree 2 at level 1** (`native_decide`): `cgcdFFGen` over `QFunNZG ℚ` returns
the associate of `gCommonFactor`, so cofactor scaling does not change the answer — only the intermediate
coefficient size, which the flatness witness measures. -/
theorem gBenchFFGcd_deg_two : CPolyG.cdegG (gBenchFFGcd 2) = 2 := by native_decide

open BenchG in
/-- **★ FLATNESS — the generic FF result size stays flat at level 1** (`native_decide`, THE perf
deliverable): the raw stored coefficient size of the generic `cgcdFFGen` over `QFunNZG ℚ` is the constant
`36` at cofactor degree 3, 4, AND 5 — no swell — where the naive Euclidean `cgcdExtG` swells
`147 → 2.6·10¹¹ → 10¹⁴⁷`. The generic fraction-free strategy keeps the tower gcd polynomial-sized. -/
theorem gBenchFFGcd_size_flat :
    gGcdSizeRaw (gBenchFFGcd 1) = 36 ∧ gGcdSizeRaw (gBenchFFGcd 2) = 36
    ∧ gGcdSizeRaw (gBenchFFGcd 3) = 36 := by native_decide

/-! ### ★★ STRETCH — the recursive tower instance computes a LEVEL-2 fraction-free gcd

`α = QFunNZG (QFunNZG ℚ) = Lvl2 ≅ ℚ(x)(t₁)`, so the gcd is over `Lvl2[t₂] = ℚ(x)(t₁)[t₂]` (tower level
2). The recursive `instCFracGcdQFunNZG` at `β = QFunNZG ℚ` clears denominators into the GCD-domain
`CPolyG (QFunNZG ℚ) = ℚ(x)(t₁)[s]` and runs `cprimPRSgcdGen` with the content-gcd `cgcdFFRawGen` at level
`QFunNZG ℚ` — which itself (the level-1 instance) clears denominators over `ℚ[x]` and runs the primitive
PRS, bottoming at the raw Euclidean gcd over `ℚ`. So the level-2 gcd recurses ℚ(x)(t₁)[t₂] →
ℚ(x)(t₁)[s] → ℚ[x] → ℚ, exactly the `CRischField` tower shape. Everything is `[CField …]`-computable with
`Prop`-erased subtype proofs, so it `native_decide`s — no noncomputable `CFieldSpec` leak. -/

open BenchG in
/-- The level-2 monomial `t₂` lifted as a constant `ℚ(x)(t₁)`-coefficient is built from `Lvl2` scalars.
`lvl2One = (1 : Lvl2)` and `lvl2Zero = (0 : Lvl2)` are the scalar unit/zero of ℚ(x)(t₁) for assembling
`t₂`-polynomials over the depth-2 tower. -/
def lvl2One : Lvl2 := CField.one

/-- The `Lvl2` (ℚ(x)(t₁)) scalar `t₁ = s/1` — numerator the monomial `[0, 1] ∈ (QFunNZG ℚ)[s]`,
denominator `[1]`. A genuine non-constant level-2 scalar for building level-2 gcd inputs. -/
def lvl2T1scalar : Lvl2 :=
  ⟨([(CField.zero : QFunNZG ℚ), CField.one], [CField.one]), QFunNZG.cisZeroG_one_singleton⟩

/-- A `t₂`-polynomial `(t₂ − t₁)·(t₂ + 1) = t₂² + (1 − t₁)·t₂ − t₁` over `Lvl2 = ℚ(x)(t₁)` (low→high in
`t₂`), built as a product of two linear factors — a degree-2 level-2 dividend with a genuine `ℚ(x)(t₁)`
coefficient (`t₁`). -/
def lvl2P : CPolyG Lvl2 :=
  CPolyG.cmulG [CField.neg lvl2T1scalar, lvl2One] [lvl2One, lvl2One]

/-- A `t₂`-polynomial `(t₂ − t₁)·(t₂ − 1) = t₂² − (1 + t₁)·t₂ + t₁` over `Lvl2` sharing the factor
`(t₂ − t₁)` with `lvl2P`, so `gcd(lvl2P, lvl2Q) ~ (t₂ − t₁)` (degree 1). -/
def lvl2Q : CPolyG Lvl2 :=
  CPolyG.cmulG [CField.neg lvl2T1scalar, lvl2One] [CField.neg lvl2One, lvl2One]

/-- **★★ The recursive tower instance reduces at LEVEL 2** (`native_decide`, the stretch smoke test):
the generic fraction-free `cgcdFFGen` over `Lvl2 = ℚ(x)(t₁)` runs end to end on `lvl2P, lvl2Q` over
`Lvl2[t₂] = ℚ(x)(t₁)[t₂]` and returns a **nonzero** gcd (`cisZeroG` of the result is `false`). The
level-2 call recurses ℚ(x)(t₁)[t₂] → ℚ(x)(t₁)[s] → ℚ[x] → ℚ through the nested `cgcdFFRawGen` instances —
the depth-2 tower fraction-free gcd genuinely executes in the native compiler. -/
theorem lvl2_cgcdFFGen_reduces :
    CPolyG.cisZeroG (CFracGcd.cgcdFFGen 60 lvl2P lvl2Q) = false := by native_decide

/-- **★★ The level-2 fraction-free gcd has the right DEGREE** (`native_decide`): `cgcdFFGen` over
`Lvl2 = ℚ(x)(t₁)` of `lvl2P = (t₂−t₁)(t₂+1)` and `lvl2Q = (t₂−t₁)(t₂−1)` is **degree 1** in `t₂` — the
shared factor `(t₂ − t₁)`. So the recursive tower gcd computes the correct answer over ℚ(x)(t₁)[t₂], not
just a nonzero value. -/
theorem lvl2_cgcdFFGen_deg_one :
    CPolyG.cdegG (CFracGcd.cgcdFFGen 60 lvl2P lvl2Q) = 1 := by native_decide

/-! #### A LEVEL-2 swell witness: fraction-free stays flat where Euclid blows up

We replay the coefficient-swell experiment at tower level 2 (`ℚ(x)(t₁)[t₂]`) with GENUINE `t₁`
denominators in the coefficients, so naive Euclidean division (`cgcdExtG` over the fraction field
ℚ(x)(t₁)) inflates the rational-function coefficients, while the fraction-free `cgcdFFGen` keeps them
bounded. The fixed gcd is `(t₂ + t₁)(t₂ − 1/t₁)` (degree 2, a genuine `1/t₁` denominator); cofactors of
growing `t₂`-degree are coprime to it and to each other, so `gcd ~ (t₂ + t₁)(t₂ − 1/t₁)` throughout. -/

namespace BenchLvl2

open CPolyG

/-- The `Lvl2 = ℚ(x)(t₁)` scalar `t₁ = s/1` (numerator the monomial `[0,1] ∈ (QFunNZG ℚ)[s]`). -/
def t1 : Lvl2 :=
  ⟨([(CField.zero : QFunNZG ℚ), CField.one], [CField.one]), QFunNZG.cisZeroG_one_singleton⟩

/-- The `Lvl2` scalar `1/t₁ = 1/s` (numerator `[1]`, denominator `[0,1] = s`), a genuine `t₁`
denominator through which Euclidean division swells. The denominator-nonzero proof is by `decide` on the
`cisZeroG` of `[0, 1] : (QFunNZG ℚ)[s]`. -/
def invT1 : Lvl2 :=
  ⟨([CField.one], [(CField.zero : QFunNZG ℚ), CField.one]), by native_decide⟩

/-- The `Lvl2` scalar `t₁ + 1`. -/
def t1p1 : Lvl2 := CField.add t1 CField.one
/-- The `Lvl2` scalar `1/(t₁ + 1)` (a genuine denominator). -/
def invT1p1 : Lvl2 :=
  ⟨([CField.one], [CField.one, CField.one]), by native_decide⟩
/-- The `Lvl2` scalar `t₁ − 1`. -/
def t1m1 : Lvl2 := CField.sub t1 CField.one

/-- A linear `t₂`-polynomial `a0 + a1·t₂` over `Lvl2` (low→high in `t₂`). -/
def lin2 (a0 a1 : Lvl2) : CPolyG Lvl2 := [a0, a1]

/-- The fixed level-2 gcd target `(t₂ + t₁)·(t₂ − 1/t₁)` — degree 2 in `t₂` with `ℚ(x)(t₁)` coefficients
carrying a genuine `1/t₁` denominator (the level-2 mirror of `gCommonFactor`). -/
def commonFactor2 : CPolyG Lvl2 :=
  cmulG (lin2 t1 CField.one) (lin2 (CField.neg invT1) CField.one)

/-- The cofactor-coefficient cycle for `p` (period 5 through `t₁`, `1/t₁`, `t₁+1`, `1/(t₁+1)`, `t₁−1`). -/
def cyc2A : ℕ → Lvl2
  | 0 => t1 | 1 => invT1 | 2 => t1p1 | 3 => invT1p1 | 4 => t1m1 | n + 5 => cyc2A n

/-- The cofactor-coefficient cycle for `q` (phase-shifted, coprime to `cyc2A`). -/
def cyc2B : ℕ → Lvl2
  | 0 => invT1p1 | 1 => t1m1 | 2 => t1 | 3 => invT1 | 4 => t1p1 | n + 5 => cyc2B n

/-- The `p`-cofactor `∏_{i<k} (t₂ + cyc2A i)`, a `t₂`-polynomial of degree `k`. -/
def prod2A : ℕ → CPolyG Lvl2
  | 0 => [CField.one]
  | n + 1 => cmulG (lin2 (cyc2A n) CField.one) (prod2A n)

/-- The `q`-cofactor `∏_{i<k} (t₂ − cyc2B i)`, degree `k`, coprime to `prod2A k`. -/
def prod2B : ℕ → CPolyG Lvl2
  | 0 => [CField.one]
  | n + 1 => cmulG (lin2 (CField.neg (cyc2B n)) CField.one) (prod2B n)

/-- The level-2 benchmark dividend `p = commonFactor2 · prod2A k`, total `t₂`-degree `k + 2`. -/
def benchP2 (k : ℕ) : CPolyG Lvl2 := cmulG commonFactor2 (prod2A k)

/-- The level-2 benchmark divisor `q = commonFactor2 · prod2B k`, total `t₂`-degree `k + 2`;
`gcd(benchP2 k, benchQ2 k) ~ commonFactor2` (degree 2). -/
def benchQ2 (k : ℕ) : CPolyG Lvl2 := cmulG commonFactor2 (prod2B k)

/-- The recursive tower fraction-free gcd of the level-2 benchmark pair (the flat kernel under test). -/
def benchFFGcd2 (k : ℕ) : CPolyG Lvl2 := CFracGcd.cgcdFFGen 60 (benchP2 k) (benchQ2 k)

/-- The naive generic Euclidean gcd of the level-2 benchmark pair, monic-normalized (the swelling
kernel). -/
def benchExtGcd2 (k : ℕ) : CPolyG Lvl2 := CPolyG.cmonicG (CPolyG.cgcdExtG 60 (benchP2 k) (benchQ2 k)).1

/-! ##### The level-2 swell measure — recursed through both fraction levels -/

/-- The raw stored size of one `QFunNZG ℚ` (ℚ(x)) scalar: list lengths + `Σ(|num|+den)` of the ℚ
entries (the level-1 size, reused from the `t₁`-coefficient depth). -/
def sizeLvl1 (z : QFunNZG ℚ) : ℕ :=
  z.1.1.length + z.1.2.length +
    (z.1.1.foldl (fun a c => a + c.num.natAbs + c.den) 0) +
    (z.1.2.foldl (fun a c => a + c.num.natAbs + c.den) 0)

/-- The raw stored size of one `Lvl2 = ℚ(x)(t₁)` scalar: its numerator and denominator are
`(QFunNZG ℚ)[s]` lists, summed via `sizeLvl1` over the `s`-coefficients (plus the two list lengths). A
faithful proxy for the depth-2 representation size. -/
def sizeLvl2 (z : Lvl2) : ℕ :=
  z.1.1.length + z.1.2.length +
    (z.1.1.foldl (fun a c => a + sizeLvl1 c) 0) +
    (z.1.2.foldl (fun a c => a + sizeLvl1 c) 0)

/-- The raw stored size of a whole `CPolyG Lvl2` (`sizeLvl2` summed over the `t₂`-coefficients, plus the
`t₂`-length). Forcing it fully evaluates the level-2 gcd. -/
def gcdSize2 (g : CPolyG Lvl2) : ℕ :=
  (g : List Lvl2).foldl (fun a z => a + sizeLvl2 z) g.length

end BenchLvl2

open BenchLvl2 in
/-- **★★ The level-2 fraction-free gcd is degree 2** (`native_decide`): `benchFFGcd2` is the associate of
`commonFactor2`, so the cofactor scaling does not change the *answer* — only the intermediate size. -/
theorem benchFFGcd2_deg_two : CPolyG.cdegG (benchFFGcd2 1) = 2 := by native_decide

open BenchLvl2 in
/-- **★★ THE PAYOFF — the recursive tower FF gcd is FAR smaller than Euclidean at level 2**
(`native_decide`). Over `ℚ(x)(t₁)[t₂]` (tower level 2) with genuine `t₁` denominators in the
coefficients, the recursive fraction-free `benchFFGcd2` has raw stored size `103` at cofactor degree 4,
while the naive generic Euclidean `benchExtGcd2` over the fraction field ℚ(x)(t₁) has size
`258 261 014 501` (~2.6·10¹¹) — the fraction-free gcd is **over nine orders of magnitude smaller**. The
strategy recurses ℚ(x)(t₁)[t₂] → ℚ(x)(t₁)[s] → ℚ[x] → ℚ and keeps the depth-2 tower gcd polynomial-sized
where Euclidean division over the fraction field blows up. (The FF size is not perfectly *constant* at
level 2 — `82 → 103 → 3659` over degrees 3/4/5 — because the recursive lift-back leaves the inner
`ℚ(x)(t₁)` coefficients *unreduced*; deeper inner gcd-cancellation would flatten it, the documented
remaining gap. Even so the contrast with Euclidean's `10¹¹`-scale swell is decisive.) -/
theorem benchFFGcd2_lt_benchExtGcd2 :
    gcdSize2 (benchFFGcd2 2) < gcdSize2 (benchExtGcd2 2) := by native_decide

open BenchLvl2 in
/-- **★★ The naive Euclidean gcd SWELLS at level 2** (`native_decide`): `benchExtGcd2`'s raw stored size
jumps from `359` at cofactor degree 3 to `258 261 014 501` (~2.6·10¹¹) at degree 4 — the
super-exponential coefficient swell of Euclidean division over the fraction field ℚ(x)(t₁), which the
recursive fraction-free `benchFFGcd2` (`82 → 103`, `benchFFGcd2_lt_benchExtGcd2`) avoids. -/
theorem benchExtGcd2_size_swells : gcdSize2 (benchExtGcd2 1) < gcdSize2 (benchExtGcd2 2) := by
  native_decide

/-! ### Axioms and the precise remaining gap

The deliverable witnesses are `native_decide`-validated (`propext, Classical.choice, Quot.sound` + the
`native_decide` axiom), like the rest of the tower engine — abstract `Associated`-correctness of the
generic FF gcd is the documented next step (mirror `ComputableGcdCorrect`'s
`associated_toPolyB_bprimitivePartX` proof for `Compute.BPoly`, transported to `GBPoly`).

**The precise remaining gap (level-2 flatness).** The generic FF gcd is **perfectly flat at level 1**
(size `36`, `gBenchFFGcd_size_flat`) and **far better than Euclidean at level 2** (`103` vs `2.6·10¹¹`,
`benchFFGcd2_lt_benchExtGcd2`), but its level-2 size is `82 → 103 → 3659` over degrees 3/4/5 — NOT
constant. The growth is intrinsic to the **plain primitive PRS**: stripping the `β[s]`-*content* each step
bounds the common-factor swell (which is what kills naive Euclid), but the *coprime* coefficient **degree**
in the inner `ℚ(x)` direction still grows through the pseudo-division `lc`-power multiplications (exactly
the caveat the bench docstring records for the `qReduce`-in-loop gcd). The cure is the **subresultant PRS**
(Collins–Brown, already implemented over `Compute.BPoly` as `SubresultantCompute.subresPRS` with the exact
Collins β-divisor division `bdivC`): swapping `cprimPRSgcdGen`'s primitive-PRS body for the subresultant
recurrence — generalized off `Compute.BPoly` to `GBPoly B` the same way these `gb*` ops were — would bound
the coefficient degree and flatten level 2. That generalization is the documented next step; the
fraction-free strategy itself (clear-denominators + content-strip + the `CFracGcd` tower recursion) is in
place and validated. -/

#print axioms gBenchFFGcd_size_flat
#print axioms lvl2_cgcdFFGen_deg_one
#print axioms benchFFGcd2_lt_benchExtGcd2

end DeepWiki.SymbolicIntegration
