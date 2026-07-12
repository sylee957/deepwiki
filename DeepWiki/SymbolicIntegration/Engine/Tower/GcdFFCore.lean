import DeepWiki.SymbolicIntegration.Engine.Tower.Lvl2
import DeepWiki.ComputableAlgebra.PolyEuclideanDense

/-! # The generic fraction-free gcd, upstream of the integration pipeline
An upstream copy of the flat recursive fraction-free gcd (names `gb*Core`, `cprimPRSgcdGenCore`,
`cclearDenomsCore`/`liftGBPolyCore`, class `CFracGcdCore`, wrapper `cgcdFFCore`) positioned before the
integration engine so it can run its gcds flat: clear denominators into the GCD-domain `DensePoly β = β[s]`,
run a primitive PRS stripping the content each step, recurse one level down, bottoming at the raw
Euclidean gcd over ℚ. -/

namespace DeepWiki.SymbolicIntegration


variable {B : Type*} [CField B]

/-! ### The generic bivariate carrier `GBPolyCore B = DensePoly (DensePoly B)` (`(B[s])[t]`) -/

/-- Generic bivariate dense carrier `GBPolyCore B := DensePoly (DensePoly B)`: a `t`-polynomial with
coefficients in `DensePoly B = B[s]` (index = `t`-degree, low→high). -/
abbrev GBPolyCore (B : Type*) := DensePoly (DensePoly B)

namespace GBPolyCore

/-- Normalize a `GBPolyCore`: `cnorm` each coefficient, then strip trailing `cisZero` coefficients. -/
def gbnormCore : GBPolyCore B → GBPolyCore B
  | [] => []
  | a :: as =>
    let a := DensePoly.cnorm a
    match gbnormCore as with
    | [] => if DensePoly.cisZero a then [] else [a]
    | r => a :: r

/-! `GBPolyCore B = DensePoly (DensePoly B)`, so its ring operations, zero test, and degree are the
generic `DensePoly.c*` operations at coefficient type `DensePoly B`; no bivariate aliases are needed. -/

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
    if DensePoly.cisZero q then gbnormCore p
    else if p.length < q.length then p
    else
      let k := p.length - q.length
      let lcq := gblcCore q
      let lcp := gblcCore p
      -- `lc(q)·p − lc(p)·tᵏ·q`: kills the leading term, stays in `B[s][t]`.
      let p' := gbnormCore
        (DensePoly.csub (DensePoly.cscale lcq p)
          (DensePoly.cscale lcp (DensePoly.cshift k q)))
      gbpsremainderCore fuel p' q

/-! ### `B[s]`-content management (`cgcdB` = the content-gcd, passed in) -/

/-- `B[s]`-content of a `GBPolyCore` relative to a content-gcd `cgcdB`: fold `cgcdB` over the
`t`-coefficients. -/
def gbcontentCore (cgcdB : DensePoly B → DensePoly B → DensePoly B) (p : GBPolyCore B) : DensePoly B :=
  (gbnormCore p).foldl (fun g c => cgcdB g c) []

/-- Primitive part `gbprimitivePartCore cgcdB p = p / content_t(p)`: divide every `t`-coefficient through
the selected Euclidean capability. Leaves `[]` unchanged. -/
def gbprimitivePartCore (cgcdB : DensePoly B → DensePoly B → DensePoly B) (p : GBPolyCore B) :
    GBPolyCore B :=
  let p := gbnormCore p
  let g := gbcontentCore cgcdB p
  if DensePoly.cisZero g then p else gbnormCore (p.map (fun c => CPolyEuclidean.div c g))

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
    if DensePoly.cisZero Q then GBPolyCore.gbprimitivePartCore cgcdB P
    else
      -- A normalized nonzero dividend has `natDegree < length`, so this fuel completes
      -- pseudo-division for arbitrary input degree rather than imposing a global cutoff.
      let r := GBPolyCore.gbprimitivePartCore cgcdB
        (GBPolyCore.gbpsremainderCore P.length P Q)
      cprimPRSgcdGenCore cgcdB fuel Q r

/-! ### Primitive-PRS termination predicate -/

/-- Per-run primitive-PRS regularity `CPrimPRSGenRegular cgcdB fuel P Q`: mirrors the recursive PRS
kernel. A terminal node has zero normalized divisor; a step has a nonzero divisor, a strict normalized
length drop for its degree-fuelled pseudo-remainder primitive part, and regularity of the next node. -/
inductive CPrimPRSGenRegular (cgcdB : DensePoly B → DensePoly B → DensePoly B) :
    ℕ → GBPolyCore B → GBPolyCore B → Prop
  /-- Terminal node: the next divisor is zero. -/
  | stop {fuel : ℕ} {P Q : GBPolyCore B} (hz : DensePoly.cisZero (GBPolyCore.gbnormCore Q) = true) :
      CPrimPRSGenRegular cgcdB fuel P Q
  /-- Recursive node: the next primitive pseudo-remainder strictly drops normalized `t`-length. -/
  | step {fuel : ℕ} {P Q : GBPolyCore B} (hz : DensePoly.cisZero (GBPolyCore.gbnormCore Q) = false)
      (hguard : (GBPolyCore.gbnormCore (GBPolyCore.gbprimitivePartCore cgcdB
          (GBPolyCore.gbpsremainderCore (GBPolyCore.gbnormCore P).length
            (GBPolyCore.gbnormCore P) (GBPolyCore.gbnormCore Q)))).length
        < (GBPolyCore.gbnormCore Q).length)
      (hrec : CPrimPRSGenRegular cgcdB fuel (GBPolyCore.gbnormCore Q)
        (GBPolyCore.gbprimitivePartCore cgcdB
          (GBPolyCore.gbpsremainderCore (GBPolyCore.gbnormCore P).length
            (GBPolyCore.gbnormCore P) (GBPolyCore.gbnormCore Q)))) :
      CPrimPRSGenRegular cgcdB (fuel + 1) P Q

/-! ### Clear denominators `DensePoly (DenseFrac β) ↔ GBPolyCore β` (`β(s)[t] ↔ (β[s])[t]`) -/

namespace DensePoly

variable {β : Type*} [CField β] [CFieldDomain β DensePoly]

/-- Clear denominators `cclearDenomsCore p ∈ GBPolyCore β`: multiply `p` over `α = DenseFrac β` by the
product of its coefficient denominators, so coefficient `i` becomes `numᵢ · ∏_{j≠i} denⱼ ∈ DensePoly β`. -/
def cclearDenomsCore (p : DensePoly (DenseFrac β)) : GBPolyCore β :=
  let cs : List (DenseFrac β) := p
  let dens : List (DensePoly β) := cs.map CFrac.den
  cs.zipIdx.map (fun (ci, i) =>
    let prodOthers := (dens.zipIdx.filter (fun (_, j) => j ≠ i)).foldl
      (fun acc (d, _) => DensePoly.cmul acc d) [CCommRing.one]
    DensePoly.cmul (CFrac.num ci) prodOthers)

/-- Lift back `liftGBPolyCore p ∈ DensePoly (DenseFrac β)`: read each `DensePoly β` coefficient `c` as the
fraction `c/1`. -/
def liftGBPolyCore (p : GBPolyCore β) : DensePoly (DenseFrac β) :=
  p.map CFrac.ofPoly

end DensePoly


end DeepWiki.SymbolicIntegration
