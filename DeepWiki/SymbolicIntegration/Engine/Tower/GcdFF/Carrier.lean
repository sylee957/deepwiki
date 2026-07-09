import DeepWiki.SymbolicIntegration.Engine.Tower.Field
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd

/-! # Bivariate dense carrier for fraction-free tower gcd benchmarks

Generic `GBPoly` operations and pseudo-division over coefficient polynomials.
-/

namespace DeepWiki.SymbolicIntegration


variable {B : Type*} [CField B]

/-! ### The generic bivariate carrier `GBPoly B = List (CPoly B)` (`(B[s])[t]`) -/

/-- Generic bivariate dense carrier `GBPoly B := List (CPoly B)`: a `t`-polynomial with coefficients in
`CPoly B = B[s]` (index = `t`-degree, low→high). -/
abbrev GBPoly (B : Type*) [CField B] := List (CPoly B)

namespace GBPoly

/-- Normalize a `GBPoly`: `cnormG` each coefficient, then strip trailing `cisZeroG` coefficients (zero
polynomial becomes `[]`). -/
def gbnorm : GBPoly B → GBPoly B
  | [] => []
  | a :: as =>
    let a := CPoly.cnormG a
    match gbnorm as with
    | [] => if CPoly.cisZeroG a then [] else [a]
    | r => a :: r

/-- Coefficientwise addition of two `GBPoly`s in `t` (each `t`-coefficient added via `caddG`). -/
def gbadd : GBPoly B → GBPoly B → GBPoly B
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => CPoly.caddG a b :: gbadd as bs

/-- Negation of a `GBPoly`, each `t`-coefficient negated via `cnegG`. -/
def gbneg (p : GBPoly B) : GBPoly B := p.map CPoly.cnegG

/-- Subtraction of `GBPoly`s, `p − q := p + (−q)`. -/
def gbsub (p q : GBPoly B) : GBPoly B := gbadd p (gbneg q)

/-- Scale `gbscaleC c p`: multiply every `t`-coefficient by the `B[s]` scalar `c` via `cmulG`. -/
def gbscaleC (c : CPoly B) (p : GBPoly B) : GBPoly B := p.map (CPoly.cmulG c)

/-- Shift in `t` `gbshift k p = tᵏ · p`: prepend `k` zero (`= []`) `t`-coefficients. -/
def gbshift : ℕ → GBPoly B → GBPoly B
  | 0, p => p
  | n + 1, p => [] :: gbshift n p

/-- Zero test for a `GBPoly`: `true` iff it normalizes to `[]`. -/
def gbisZero (p : GBPoly B) : Bool := (gbnorm p).isEmpty

/-- `t`-degree of a `GBPoly`: `(gbnorm p).length − 1`, with `gbdeg 0 = 0`. -/
def gbdeg (p : GBPoly B) : ℕ := (gbnorm p).length - 1

/-- Leading `t`-coefficient `gblc p ∈ CPoly B`: the top nonzero `t`-coefficient, `[]` for zero. -/
def gblc (p : GBPoly B) : CPoly B := (gbnorm p).getLast?.getD []

/-! ### Pseudo-division over the coefficient ring `CPoly B = B[s]` -/

/-- Pseudo-remainder `gbpsremainder fuel p q = prem(p, q)` over `CPoly B = B[s]`: while `deg p ≥ deg q`,
replace `p` by `lc(q)·p − lc(p)·tᵏ·q` (no `B[s]` division). -/
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

/-! ### `B[s]`-content management (`cgcdB` = the content-gcd, passed in) -/

/-- `B[s]`-content of a `GBPoly` relative to a content-gcd `cgcdB`: fold `cgcdB` over the
`t`-coefficients. -/
def gbcontent (cgcdB : CPoly B → CPoly B → CPoly B) (p : GBPoly B) : CPoly B :=
  (gbnorm p).foldl (fun g c => cgcdB g c) []

/-- Primitive part `gbprimitivePart cgcdB p = p / content_t(p)`: divide every `t`-coefficient by the
content via `cdivWf`. Leaves `[]` unchanged. -/
def gbprimitivePart (cgcdB : CPoly B → CPoly B → CPoly B) (p : GBPoly B) : GBPoly B :=
  let p := gbnorm p
  let g := gbcontent cgcdB p
  if CPoly.cisZeroG g then p else gbnorm (p.map (fun c => CPoly.cdivWf c g))

end GBPoly

end DeepWiki.SymbolicIntegration
