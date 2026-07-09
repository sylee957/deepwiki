import DeepWiki.SymbolicIntegration.Engine.Tower.Field
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd

/-! # The generic fraction-free gcd, upstream of the integration pipeline
An upstream copy of the flat recursive fraction-free gcd (names `gb*Core`, `cprimPRSgcdGenCore`,
`cclearDenomsCoreG`/`liftGBPolyCoreG`, class `CFracGcdCore`, wrapper `cgcdFFCore`) positioned before the
integration engine so it can run its gcds flat: clear denominators into the GCD-domain `CPolyG β = β[s]`,
run a primitive PRS stripping the content each step, recurse one level down, bottoming at the raw
Euclidean gcd over ℚ. -/

namespace DeepWiki.SymbolicIntegration


variable {B : Type*} [CField B]

/-! ### The generic bivariate carrier `GBPolyCore B = List (CPolyG B)` (`(B[s])[t]`) -/

/-- Generic bivariate dense carrier `GBPolyCore B := List (CPolyG B)`: a `t`-polynomial with coefficients
in `CPolyG B = B[s]` (index = `t`-degree, low→high). -/
abbrev GBPolyCore (B : Type*) [CField B] := List (CPolyG B)

namespace GBPolyCore

/-- Normalize a `GBPolyCore`: `cnormG` each coefficient, then strip trailing `cisZeroG` coefficients. -/
def gbnormCore : GBPolyCore B → GBPolyCore B
  | [] => []
  | a :: as =>
    let a := CPolyG.cnormG a
    match gbnormCore as with
    | [] => if CPolyG.cisZeroG a then [] else [a]
    | r => a :: r

/-- Coefficientwise addition of two `GBPolyCore`s in `t` (each `t`-coefficient added via `caddG`). -/
def gbaddCore : GBPolyCore B → GBPolyCore B → GBPolyCore B
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => CPolyG.caddG a b :: gbaddCore as bs

/-- Negation of a `GBPolyCore`, each `t`-coefficient negated via `cnegG`. -/
def gbnegCore (p : GBPolyCore B) : GBPolyCore B := p.map CPolyG.cnegG

/-- Subtraction of `GBPolyCore`s, `p − q := p + (−q)`. -/
def gbsubCore (p q : GBPolyCore B) : GBPolyCore B := gbaddCore p (gbnegCore q)

/-- Scale `gbscaleCCore c p`: multiply every `t`-coefficient by the `B[s]` scalar `c` via `cmulG`. -/
def gbscaleCCore (c : CPolyG B) (p : GBPolyCore B) : GBPolyCore B := p.map (CPolyG.cmulG c)

/-- Shift in `t` `gbshiftCore k p = tᵏ · p`: prepend `k` zero (`= []`) `t`-coefficients. -/
def gbshiftCore : ℕ → GBPolyCore B → GBPolyCore B
  | 0, p => p
  | n + 1, p => [] :: gbshiftCore n p

/-- Zero test for a `GBPolyCore`: `true` iff it normalizes to `[]` (via `List.isEmpty`). -/
def gbisZeroCore (p : GBPolyCore B) : Bool := (gbnormCore p).isEmpty

/-- `t`-degree of a `GBPolyCore`: `(gbnormCore p).length − 1`, with `gbdegCore 0 = 0`. -/
def gbdegCore (p : GBPolyCore B) : ℕ := (gbnormCore p).length - 1

/-- Leading `t`-coefficient `gblcCore p ∈ CPolyG B`: the top nonzero `t`-coefficient, `[]` for zero. -/
def gblcCore (p : GBPolyCore B) : CPolyG B := (gbnormCore p).getLast?.getD []

/-! ### Pseudo-division over the coefficient ring `CPolyG B = B[s]` -/

/-- Pseudo-remainder `gbpsremainderCore fuel p q = prem(p, q)` over `CPolyG B = B[s]`: while
`deg p ≥ deg q`, replace `p` by `lc(q)·p − lc(p)·tᵏ·q` (no `B[s]` division). -/
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

/-! ### `B[s]`-content management (`cgcdB` = the content-gcd, passed in) -/

/-- `B[s]`-content of a `GBPolyCore` relative to a content-gcd `cgcdB`: fold `cgcdB` over the
`t`-coefficients. -/
def gbcontentCore (cgcdB : CPolyG B → CPolyG B → CPolyG B) (p : GBPolyCore B) : CPolyG B :=
  (gbnormCore p).foldl (fun g c => cgcdB g c) []

/-- Primitive part `gbprimitivePartCore cgcdB p = p / content_t(p)`: divide every `t`-coefficient by the
content via `cdivWf`. Leaves `[]` unchanged. -/
def gbprimitivePartCore (cgcdB : CPolyG B → CPolyG B → CPolyG B) (p : GBPolyCore B) :
    GBPolyCore B :=
  let p := gbnormCore p
  let g := gbcontentCore cgcdB p
  if CPolyG.cisZeroG g then p else gbnormCore (p.map (fun c => CPolyG.cdivWf c g))

end GBPolyCore

/-! ### The generic fraction-free gcd kernel — the primitive PRS over `CPolyG B = B[s]` -/

/-- Generic primitive polynomial-remainder sequence `cprimPRSgcdGenCore cgcdB fuel P Q`: the gcd of
`P, Q` in `t` up to a `B[s]`-content factor, taking the primitive part of each pseudo-remainder. -/
def cprimPRSgcdGenCore (cgcdB : CPolyG B → CPolyG B → CPolyG B) :
    ℕ → GBPolyCore B → GBPolyCore B → GBPolyCore B
  | 0, P, _ => GBPolyCore.gbprimitivePartCore cgcdB P
  | fuel + 1, P, Q =>
    let P := GBPolyCore.gbnormCore P
    let Q := GBPolyCore.gbnormCore Q
    if GBPolyCore.gbisZeroCore Q then GBPolyCore.gbprimitivePartCore cgcdB P
    else
      let r := GBPolyCore.gbprimitivePartCore cgcdB (GBPolyCore.gbpsremainderCore 60 P Q)
      cprimPRSgcdGenCore cgcdB fuel Q r

/-! ### Clear denominators `CPolyG (QFunNZG β) ↔ GBPolyCore β` (`β(s)[t] ↔ (β[s])[t]`) -/

namespace CPolyG

variable {β : Type*} [CField β] [CFieldDomain β]

/-- The numerator `CPolyG β` of a `QFunNZG β` coefficient. -/
def qnumCoeffCoreG (c : QFunNZG β) : CPolyG β := c.1.1

/-- The denominator `CPolyG β` of a `QFunNZG β` coefficient. -/
def qdenCoeffCoreG (c : QFunNZG β) : CPolyG β := c.1.2

/-- Clear denominators `cclearDenomsCoreG p ∈ GBPolyCore β`: multiply `p` over `α = QFunNZG β` by the
product of its coefficient denominators, so coefficient `i` becomes `numᵢ · ∏_{j≠i} denⱼ ∈ CPolyG β`. -/
def cclearDenomsCoreG (p : CPolyG (QFunNZG β)) : GBPolyCore β :=
  let cs : List (QFunNZG β) := p
  let dens : List (CPolyG β) := cs.map qdenCoeffCoreG
  cs.zipIdx.map (fun (ci, i) =>
    let prodOthers := (dens.zipIdx.filter (fun (_, j) => j ≠ i)).foldl
      (fun acc (d, _) => CPolyG.cmulG acc d) [CField.one]
    CPolyG.cmulG (qnumCoeffCoreG ci) prodOthers)

/-- Lift back `liftGBPolyCoreG p ∈ CPolyG (QFunNZG β)`: read each `CPolyG β` coefficient `c` as the
fraction `c/1`. -/
def liftGBPolyCoreG (p : GBPolyCore β) : CPolyG (QFunNZG β) :=
  p.map (fun c => (⟨(c, [CField.one]), QFunNZG.cisZeroG_one_singleton⟩ : QFunNZG β))

end CPolyG


end DeepWiki.SymbolicIntegration
