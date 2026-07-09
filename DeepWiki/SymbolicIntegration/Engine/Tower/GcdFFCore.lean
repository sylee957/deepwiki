import DeepWiki.SymbolicIntegration.Engine.Tower.Lvl2
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd

/-! # The generic fraction-free gcd, upstream of the integration pipeline
An upstream copy of the flat recursive fraction-free gcd (names `gb*Core`, `cprimPRSgcdGenCore`,
`cclearDenomsCore`/`liftGBPolyCore`, class `CFracGcdCore`, wrapper `cgcdFFCore`) positioned before the
integration engine so it can run its gcds flat: clear denominators into the GCD-domain `DensePoly β = β[s]`,
run a primitive PRS stripping the content each step, recurse one level down, bottoming at the raw
Euclidean gcd over ℚ. -/

namespace DeepWiki.SymbolicIntegration


variable {B : Type*} [CField B]

/-! ### The generic bivariate carrier `GBPolyCore B = List (DensePoly B)` (`(B[s])[t]`) -/

/-- Generic bivariate dense carrier `GBPolyCore B := List (DensePoly B)`: a `t`-polynomial with coefficients
in `DensePoly B = B[s]` (index = `t`-degree, low→high). -/
abbrev GBPolyCore (B : Type*) [CField B] := List (DensePoly B)

namespace GBPolyCore

/-- Normalize a `GBPolyCore`: `cnorm` each coefficient, then strip trailing `cisZero` coefficients. -/
def gbnormCore : GBPolyCore B → GBPolyCore B
  | [] => []
  | a :: as =>
    let a := DensePoly.cnorm a
    match gbnormCore as with
    | [] => if DensePoly.cisZero a then [] else [a]
    | r => a :: r

/-! The `GBPolyCore` arithmetic is the ring-generalized generic engine at coefficient `DensePoly B`
(`GBPolyCore B = DensePoly (DensePoly B)`, keystone `CCommRing (DensePoly B)`): each `gb*Core` is the generic `c*`. -/

/-- Coefficientwise addition of two `GBPolyCore`s in `t` — the generic `cadd` at coefficient `DensePoly B`. -/
def gbaddCore (p q : GBPolyCore B) : GBPolyCore B := DensePoly.cadd p q

/-- Negation of a `GBPolyCore` — the generic `cneg` at coefficient `DensePoly B`. -/
def gbnegCore (p : GBPolyCore B) : GBPolyCore B := DensePoly.cneg p

/-- Subtraction of `GBPolyCore`s — the generic `csub` at coefficient `DensePoly B`. -/
def gbsubCore (p q : GBPolyCore B) : GBPolyCore B := DensePoly.csub p q

/-- Scale `gbscaleCCore c p` — the generic `cscale` at coefficient `DensePoly B`. -/
def gbscaleCCore (c : DensePoly B) (p : GBPolyCore B) : GBPolyCore B := DensePoly.cscale c p

/-- Shift in `t` `gbshiftCore k p = tᵏ · p` — the generic `cshift` at coefficient `DensePoly B`. -/
def gbshiftCore (k : ℕ) (p : GBPolyCore B) : GBPolyCore B := DensePoly.cshift k p

/-- Zero test for a `GBPolyCore`: `true` iff it normalizes to `[]` (via `List.isEmpty`). -/
def gbisZeroCore (p : GBPolyCore B) : Bool := (gbnormCore p).isEmpty

/-- `t`-degree of a `GBPolyCore`: `(gbnormCore p).length − 1`, with `gbdegCore 0 = 0`. -/
def gbdegCore (p : GBPolyCore B) : ℕ := (gbnormCore p).length - 1

/-- Leading `t`-coefficient `gblcCore p ∈ DensePoly B`: the top nonzero `t`-coefficient, `[]` for zero. -/
def gblcCore (p : GBPolyCore B) : DensePoly B := (gbnormCore p).getLast?.getD []

/-! ### Pseudo-division over the coefficient ring `DensePoly B = B[s]` -/

/-- Pseudo-remainder `gbpsremainderCore fuel p q = prem(p, q)` over `DensePoly B = B[s]`: while
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
def gbcontentCore (cgcdB : DensePoly B → DensePoly B → DensePoly B) (p : GBPolyCore B) : DensePoly B :=
  (gbnormCore p).foldl (fun g c => cgcdB g c) []

/-- Primitive part `gbprimitivePartCore cgcdB p = p / content_t(p)`: divide every `t`-coefficient by the
content via `cdivWf`. Leaves `[]` unchanged. -/
def gbprimitivePartCore (cgcdB : DensePoly B → DensePoly B → DensePoly B) (p : GBPolyCore B) :
    GBPolyCore B :=
  let p := gbnormCore p
  let g := gbcontentCore cgcdB p
  if DensePoly.cisZero g then p else gbnormCore (p.map (fun c => DensePoly.cdivWf c g))

end GBPolyCore

/-! ### The generic fraction-free gcd kernel — the primitive PRS over `DensePoly B = B[s]` -/

/-- Generic primitive polynomial-remainder sequence `cprimPRSgcdGenCore cgcdB fuel P Q`: the gcd of
`P, Q` in `t` up to a `B[s]`-content factor, taking the primitive part of each pseudo-remainder. -/
def cprimPRSgcdGenCore (cgcdB : DensePoly B → DensePoly B → DensePoly B) :
    ℕ → GBPolyCore B → GBPolyCore B → GBPolyCore B
  | 0, P, _ => GBPolyCore.gbprimitivePartCore cgcdB P
  | fuel + 1, P, Q =>
    let P := GBPolyCore.gbnormCore P
    let Q := GBPolyCore.gbnormCore Q
    if GBPolyCore.gbisZeroCore Q then GBPolyCore.gbprimitivePartCore cgcdB P
    else
      let r := GBPolyCore.gbprimitivePartCore cgcdB (GBPolyCore.gbpsremainderCore 60 P Q)
      cprimPRSgcdGenCore cgcdB fuel Q r

/-! ### Clear denominators `DensePoly (CFrac β) ↔ GBPolyCore β` (`β(s)[t] ↔ (β[s])[t]`) -/

namespace DensePoly

variable {β : Type*} [CField β] [CFieldDomain β]

/-- The numerator `DensePoly β` of a `CFrac β` coefficient. -/
def qnumCoeffCore (c : CFrac β) : DensePoly β := c.1.1

/-- The denominator `DensePoly β` of a `CFrac β` coefficient. -/
def qdenCoeffCore (c : CFrac β) : DensePoly β := c.1.2

/-- Clear denominators `cclearDenomsCore p ∈ GBPolyCore β`: multiply `p` over `α = CFrac β` by the
product of its coefficient denominators, so coefficient `i` becomes `numᵢ · ∏_{j≠i} denⱼ ∈ DensePoly β`. -/
def cclearDenomsCore (p : DensePoly (CFrac β)) : GBPolyCore β :=
  let cs : List (CFrac β) := p
  let dens : List (DensePoly β) := cs.map qdenCoeffCore
  cs.zipIdx.map (fun (ci, i) =>
    let prodOthers := (dens.zipIdx.filter (fun (_, j) => j ≠ i)).foldl
      (fun acc (d, _) => DensePoly.cmul acc d) [CCommRing.one]
    DensePoly.cmul (qnumCoeffCore ci) prodOthers)

/-- Lift back `liftGBPolyCore p ∈ DensePoly (CFrac β)`: read each `DensePoly β` coefficient `c` as the
fraction `c/1`. -/
def liftGBPolyCore (p : GBPolyCore β) : DensePoly (CFrac β) :=
  p.map (fun c => (⟨(c, [CCommRing.one]), CFrac.cisZeroG_one_singleton⟩ : CFrac β))

end DensePoly


end DeepWiki.SymbolicIntegration
