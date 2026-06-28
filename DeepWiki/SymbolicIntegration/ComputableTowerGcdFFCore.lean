import DeepWiki.SymbolicIntegration.ComputableTowerField

/-! # The generic fraction-free gcd, upstream of the integration pipeline
`ComputableTowerGcdFF` builds the flat, recursive, fraction-free gcd over an arbitrary tower level
(`class CFracGcd`, `cgcdFFGen`), validated against `cgcdFF` and the swell benchmark. But that file sits
**downstream** of the integration pipeline (it imports `ComputableTowerBench`, which transitively imports
`ComputableTowerIntegrate`), so the integration engine `cIntegrateGFull` cannot import it to *use* its flat
gcd.

This file lifts the **machinery** of that flat gcd to a position **upstream** of `ComputableTowerIntegrate`
— it depends on nothing past `ComputableTowerField` + `ComputableSplitFactorFast`, exactly the two files
`cgcdFFGen` actually needs. So the generic integration pipeline can import it and run its gcds **flat**
(`cprimPRSgcdGen` primitive PRS over the GCD-domain `CPolyG β = β[s]`, no fraction-field swell) instead of
through the super-exponentially-swelling Euclidean `cgcdMonicG`.

The content is a faithful copy of `ComputableTowerGcdFF`'s machinery under the names `gb*Core`,
`cprimPRSgcdGenCore`, `cclearDenomsCoreG`/`liftGBPolyCoreG`, the class `CFracGcdCore` (method
`cgcdFFRawCore`), and the public wrapper `cgcdFFCore` — distinct names so the two files coexist without
clashing (`ComputableTowerGcdFF` keeps its own `CFracGcd` for its benchmark validations). The math is
identical: clear denominators into the GCD-domain `CPolyG β`, run the primitive PRS stripping the
content each step (so coefficients never accumulate fractions), recurse one level down through the
content-gcd, bottoming at the raw Euclidean gcd over ℚ. -/

namespace DeepWiki.SymbolicIntegration

open Compute

variable {B : Type*} [CField B]

/-! ### The generic bivariate carrier `GBPolyCore B = List (CPolyG B)` (`(B[s])[t]`)

`GBPolyCore B := List (CPolyG B)` is a `t`-polynomial whose coefficients are `CPolyG B = B[s]` (index =
`t`-degree, low→high). The `gb*Core` arithmetic delegates each coefficient operation to the generic
engine over `CPolyG B`, so it needs only `[CField B]` and reduces in the native compiler. -/

/-- **Generic bivariate dense carrier** `GBPolyCore B := List (CPolyG B)` = a `t`-polynomial whose
coefficients are `CPolyG B = B[s]` (index = `t`-degree, low→high). The upstream copy of `GBPoly`. -/
abbrev GBPolyCore (B : Type*) [CField B] := List (CPolyG B)

namespace GBPolyCore

/-- **Normalize** a `GBPolyCore`: `cnormG` each coefficient, then strip trailing (high-`t`-degree)
`cisZeroG` coefficients, so the zero polynomial becomes `[]`. -/
def gbnormCore : GBPolyCore B → GBPolyCore B
  | [] => []
  | a :: as =>
    let a := CPolyG.cnormG a
    match gbnormCore as with
    | [] => if CPolyG.cisZeroG a then [] else [a]
    | r => a :: r

/-- **Coefficientwise addition** of two `GBPolyCore`s in `t` (each `t`-coefficient added via `caddG`). -/
def gbaddCore : GBPolyCore B → GBPolyCore B → GBPolyCore B
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => CPolyG.caddG a b :: gbaddCore as bs

/-- **Negation** of a `GBPolyCore`, each `t`-coefficient negated via `cnegG`. -/
def gbnegCore (p : GBPolyCore B) : GBPolyCore B := p.map CPolyG.cnegG

/-- **Subtraction** of `GBPolyCore`s, `p − q := p + (−q)`. -/
def gbsubCore (p q : GBPolyCore B) : GBPolyCore B := gbaddCore p (gbnegCore q)

/-- **Scale by a `CPolyG B`** (a `B[s]` scalar) `gbscaleCCore c p`: multiply every `t`-coefficient by `c`
via the inner `cmulG`. -/
def gbscaleCCore (c : CPolyG B) (p : GBPolyCore B) : GBPolyCore B := p.map (CPolyG.cmulG c)

/-- **Shift in `t`** `gbshiftCore k p = tᵏ · p`: prepend `k` zero (`= []`) `t`-coefficients. -/
def gbshiftCore : ℕ → GBPolyCore B → GBPolyCore B
  | 0, p => p
  | n + 1, p => [] :: gbshiftCore n p

/-- **Zero test** for a `GBPolyCore`: `true` iff it normalizes to `[]` (via `List.isEmpty`). -/
def gbisZeroCore (p : GBPolyCore B) : Bool := (gbnormCore p).isEmpty

/-- **`t`-degree** of a `GBPolyCore` as a `ℕ`: `(length of gbnormCore p) − 1`, with `gbdegCore 0 = 0`
(paired with `gbisZeroCore` at call sites). -/
def gbdegCore (p : GBPolyCore B) : ℕ := (gbnormCore p).length - 1

/-- **Leading `t`-coefficient** `gblcCore p ∈ CPolyG B` (`= B[s]`): the top nonzero `t`-coefficient, `[]`
(zero) for the zero polynomial. -/
def gblcCore (p : GBPolyCore B) : CPolyG B := (gbnormCore p).getLast?.getD []

/-! ### Pseudo-division over the coefficient ring `CPolyG B = B[s]` -/

/-- **Pseudo-remainder** `gbpsremainderCore fuel p q = prem(p, q)` over the non-field coefficient ring
`CPolyG B = B[s]`: while `deg p ≥ deg q`, replace `p` by `lc(q)·p − lc(p)·tᵏ·q` (`k = deg p − deg q`),
staying in `GBPolyCore B` (no `B[s]` division). Fuel-bounded (one step per `t`-degree drop). -/
def gbpsremainderCore : ℕ → GBPolyCore B → GBPolyCore B → GBPolyCore B
  | 0, p, _ => gbnormCore p
  | fuel + 1, p, q =>
    let p := gbnormCore p
    let q := gbnormCore q
    if gbisZeroCore q then gbnormCore p
    else if p.length < q.length then p
    else
      let k := p.length - q.length
      let lcq := gblcCore q
      let lcp := gblcCore p
      -- `lc(q)·p − lc(p)·tᵏ·q`: kills the leading term, stays in `B[s][t]`.
      let p' := gbnormCore (gbsubCore (gbscaleCCore lcq p) (gbscaleCCore lcp (gbshiftCore k q)))
      gbpsremainderCore fuel p' q

/-! ### `B[s]`-content management (`cgcdB` = the content-gcd, passed in)

The content-gcd `cgcdB : CPolyG B → CPolyG B → CPolyG B` over the coefficient ring `CPolyG B = B[s]` is
PASSED IN — for the tower it is the level-`β` fraction-free gcd, recursing one level down. The content
division is the generic Euclidean `cdivG` over `CPolyG B` (exact: the content divides every
coefficient). -/

/-- **`B[s]`-content** of a `GBPolyCore` (relative to a content-gcd `cgcdB`): fold `cgcdB` over all the
`t`-coefficients — the common `CPolyG B = B[s]` factor of the polynomial in `t`. -/
def gbcontentCore (cgcdB : CPolyG B → CPolyG B → CPolyG B) (p : GBPolyCore B) : CPolyG B :=
  (gbnormCore p).foldl (fun g c => cgcdB g c) []

/-- **Strip the `B[s]`-content in `t`** `gbprimitivePartCore fuel cgcdB p = p / content_t(p)`: divide
every `t`-coefficient by the content (exact generic Euclidean `cdivG` over `CPolyG B`), giving the
`B[s]`-primitive part. Leaves `[]` (and content `[]`) unchanged. -/
def gbprimitivePartCore (fuel : ℕ) (cgcdB : CPolyG B → CPolyG B → CPolyG B) (p : GBPolyCore B) :
    GBPolyCore B :=
  let p := gbnormCore p
  let g := gbcontentCore cgcdB p
  if CPolyG.cisZeroG g then p else gbnormCore (p.map (fun c => CPolyG.cdivG fuel c g))

end GBPolyCore

/-! ### The generic fraction-free gcd kernel — the primitive PRS over `CPolyG B = B[s]`

`cprimPRSgcdGenCore cgcdB fuel P Q` is the gcd of `P, Q` in `t` (over the coefficient ring
`CPolyG B = B[s]`), up to a `B[s]`-content factor. Each step takes the **primitive part** of the
**pseudo-remainder**, keeping every coefficient in `B[s]` (no field division, so no `β(s)` swell); the
last nonzero primitive remainder is the gcd. The content-gcd `cgcdB` is passed in. -/

/-- **Generic primitive polynomial-remainder sequence** `cprimPRSgcdGenCore cgcdB fuel P Q ∈ GBPolyCore B`:
the gcd of `P, Q` in `t` (over the coefficient ring `CPolyG B = B[s]`), up to a `B[s]`-content factor.
Each step takes the primitive part of the pseudo-remainder; the last nonzero primitive remainder is the
gcd. Requires `gbdegCore P ≥ gbdegCore Q`; fuel-bounded (one step per `t`-degree drop). -/
def cprimPRSgcdGenCore (cgcdB : CPolyG B → CPolyG B → CPolyG B) :
    ℕ → GBPolyCore B → GBPolyCore B → GBPolyCore B
  | 0, P, _ => GBPolyCore.gbprimitivePartCore 30 cgcdB P
  | fuel + 1, P, Q =>
    let P := GBPolyCore.gbnormCore P
    let Q := GBPolyCore.gbnormCore Q
    if GBPolyCore.gbisZeroCore Q then GBPolyCore.gbprimitivePartCore 30 cgcdB P
    else
      let r := GBPolyCore.gbprimitivePartCore 30 cgcdB (GBPolyCore.gbpsremainderCore 60 P Q)
      cprimPRSgcdGenCore cgcdB fuel Q r

/-! ### Clear denominators `CPolyG (QFunNZG β) ↔ GBPolyCore β` (`β(s)[t] ↔ (β[s])[t]`)

For the tower level `α = QFunNZG β = Frac(CPolyG β = β[s])`, a `t`-polynomial over `α` is a `CPolyG α`
whose coefficients are `QFunNZG β` fractions. `cclearDenomsCoreG` multiplies through by the product of the
coefficient denominators, landing in `GBPolyCore β = (β[s])[t]`. The embed-back `liftGBPolyCoreG` re-reads
a `GBPolyCore β` coefficient `c : CPolyG β` as the fraction `c/1 ∈ QFunNZG β`. -/

namespace CPolyG

variable {β : Type*} [CField β] [CFieldDomain β]

/-- The numerator `CPolyG β` of a `QFunNZG β` coefficient. -/
def qnumCoeffCoreG (c : QFunNZG β) : CPolyG β := c.1.1

/-- The denominator `CPolyG β` of a `QFunNZG β` coefficient. -/
def qdenCoeffCoreG (c : QFunNZG β) : CPolyG β := c.1.2

/-- **Clear denominators** `cclearDenomsCoreG p ∈ GBPolyCore β` (`= (β[s])[t]`): multiply the
`t`-polynomial `p` over `α = QFunNZG β` through by the product of its coefficient denominators, so
coefficient `i` becomes `numᵢ · ∏_{j≠i} denⱼ ∈ CPolyG β = β[s]`. Carries `p` from `β(s)[t]` to `(β[s])[t]`
up to the (cleared) common-denominator unit. -/
def cclearDenomsCoreG (p : CPolyG (QFunNZG β)) : GBPolyCore β :=
  let cs : List (QFunNZG β) := p
  let dens : List (CPolyG β) := cs.map qdenCoeffCoreG
  cs.zipIdx.map (fun (ci, i) =>
    let prodOthers := (dens.zipIdx.filter (fun (_, j) => j ≠ i)).foldl
      (fun acc (d, _) => CPolyG.cmulG acc d) [CField.one]
    CPolyG.cmulG (qnumCoeffCoreG ci) prodOthers)

/-- **Lift back** `liftGBPolyCoreG p ∈ CPolyG (QFunNZG β)`: read each `CPolyG β = β[s]` coefficient `c` of
a `GBPolyCore β` as the `QFunNZG β` fraction `c/1` (numerator `c`, denominator `[1]`). -/
def liftGBPolyCoreG (p : GBPolyCore β) : CPolyG (QFunNZG β) :=
  p.map (fun c => (⟨(c, [CField.one]), QFunNZG.cisZeroG_one_singleton⟩ : QFunNZG β))

end CPolyG

/-! ### `class CFracGcdCore α` — the recursive fraction-free gcd over `α[t]`

The recursion that ties the tower, mirroring `CFracGcd` exactly but upstream of the integration pipeline:
* **`class CFracGcdCore α`** (one method `cgcdFFRawCore`, the *raw* content-normalized fraction-free gcd).
* **Base `instance CFracGcdCore ℚ`** — a `t`-polynomial over `ℚ` is `ℚ[t]`; `ℚ` is a field, content is a
  unit, so the raw gcd is the *raw* Euclidean gcd `(cgcdExtG _).1` over `ℚ[t]` (NOT monic — monic content
  compounds reciprocal scalars up the recursion, breaking flatness).
* **Recursive `instance CFracGcdCore (QFunNZG β) [CFracGcdCore β]`** — clear denominators into
  `GBPolyCore β = (β[s])[t]`, run `cprimPRSgcdGenCore` with the level-`β` `cgcdFFRawCore` as content-gcd,
  lift back. Bottoms at `CFracGcdCore ℚ`.

The public **monic** gcd is the wrapper `cgcdFFCore := cmonicG ∘ cgcdFFRawCore` (monic-normalize only at
the top). The Euclidean work stays fraction-free in the GCD-domain `CPolyG β`, so coefficients do not
swell the way `cgcdExtG` over the fraction field `β(s)` does. -/

/-- **Recursive fraction-free gcd over a tower level** (upstream copy of `CFracGcd`): the *raw*
(content-normalized, NOT monic) gcd `cgcdFFRawCore fuel p q` of `p, q ∈ CPolyG α = α[t]`. The method is
the RAW gcd, because that is what the recursion consumes — the content-gcd over `CPolyG β = β[s]` must NOT
be monic-normalized (monic content scales by `1/lead`, and those reciprocal scalars COMPOUND up the
primitive-PRS recursion, defeating fraction-freeness). The public monic gcd is the wrapper
`cgcdFFCore := cmonicG ∘ cgcdFFRawCore`. Bottoms at `CFracGcdCore ℚ`. -/
class CFracGcdCore (α : Type*) [CField α] where
  /-- The *raw* (content-normalized, non-monic) fraction-free gcd over `α[t]` — the form the recursion
  consumes as a content-gcd (monic normalization is applied only at the top, by `cgcdFFCore`). -/
  cgcdFFRawCore : ℕ → CPolyG α → CPolyG α → CPolyG α

namespace CFracGcdCore

variable {α : Type*} [CField α] [CFracGcdCore α]

/-- **The public monic fraction-free gcd** `cgcdFFCore fuel p q := cmonicG (cgcdFFRawCore fuel p q)` over
`α[t]`: monic-normalize the raw recursive gcd. The flat, `cgcdFF`-agreeing counterpart of `cgcdMonicG` —
the monic normalization happens once at the top, never inside the recursion. -/
def cgcdFFCore (fuel : ℕ) (p q : CPolyG α) : CPolyG α := CPolyG.cmonicG (cgcdFFRawCore fuel p q)

end CFracGcdCore

/-- **Base `CFracGcdCore ℚ`** — the bottom of the tower. A `t`-polynomial over `ℚ` is `ℚ[t]`; since `ℚ` is
a field the `ℚ`-content is a unit, so the raw fraction-free gcd is the **raw** Euclidean gcd
`(CPolyG.cgcdExtG _).1` over `ℚ[t]` (NOT monic — monic content compounds reciprocal scalars up the
recursion, breaking flatness). Small Euclid, no swell at the constant field. -/
instance instCFracGcdCoreQ : CFracGcdCore ℚ where
  cgcdFFRawCore fuel p q := (CPolyG.cgcdExtG fuel p q).1

section
variable {β : Type*} [CField β] [CFieldDomain β] [CFracGcdCore β]

/-- **★ `CFracGcdCore (QFunNZG β)`** — the *raw* fraction-free gcd over `β(s)[t]`, built by running
`cprimPRSgcdGenCore` over the GCD-domain `CPolyG β = β[s]` with the level-`β` `cgcdFFRawCore` as the
content-gcd. Clear denominators of both inputs into `GBPolyCore β = (β[s])[t]`, order them by `t`-degree
(the PRS needs the larger first), run the primitive PRS (gcd up to `β[s]`-content) with
`cgcdB := CFracGcdCore.cgcdFFRawCore` recursing one level down, and lift the result back to `β(s)[t]` — no
`cmonicG` (this is the raw method; the public `cgcdFFCore` monic-normalizes at the top). Computable
(`Prop`-erased subtype proofs), so it `native_decide`s; recurses strictly one level down, bottoming at
`CFracGcdCore ℚ`. -/
instance instCFracGcdCoreQFunNZG : CFracGcdCore (QFunNZG β) where
  cgcdFFRawCore fuel p q :=
    let P := CPolyG.cclearDenomsCoreG p
    let Q := CPolyG.cclearDenomsCoreG q
    let (P, Q) := if GBPolyCore.gbdegCore P < GBPolyCore.gbdegCore Q then (Q, P) else (P, Q)
    CPolyG.liftGBPolyCoreG (cprimPRSgcdGenCore (CFracGcdCore.cgcdFFRawCore fuel) fuel P Q)

end

end DeepWiki.SymbolicIntegration
