import DeepWiki.SymbolicIntegration.Compute.RtResultant

/-! # Computable bivariate subresultant gcd / log argument over `ℚ[t]`
The logarithmic part puts `S(t,x) = gcd_x(D(x), A(x) − t·D'(x))` inside the logarithms of
`∫ A/D = ∑_{R(a)=0} a·log(S(a,x))`. This bivariate `ℚ[t][x]` gcd is computed by the subresultant
polynomial-remainder sequence over the non-field ring `ℚ[t]`, on a `#eval`-able carrier
`BPoly := List CPoly`. Agreement with the noncomputable `lrtSubresultant` is proven in
`SubresultantCorrectness`. -/

namespace DeepWiki.SymbolicIntegration

namespace Compute

/-! ### The bivariate carrier `BPoly = List CPoly` (`ℚ[t][x]`) -/

/-- Bivariate dense carrier `BPoly := List CPoly`: a polynomial in `x` whose coefficients are `CPoly`
(`= ℚ[t]`), index = `x`-degree low→high. -/
abbrev BPoly := List CPoly

/-- Normalize a `BPoly`: normalize each `CPoly` coefficient, then strip trailing (high-`x`-degree)
zero coefficients. -/
def bnorm : BPoly → BPoly
  | [] => []
  | a :: as =>
    let a := cnorm a
    match bnorm as with
    | [] => if cisZero a then [] else [a]
    | r => a :: r

/-- Coefficientwise addition of two `BPoly`s in `x` (each `x`-coefficient added via `cadd`). -/
def badd : BPoly → BPoly → BPoly
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => cadd a b :: badd as bs

/-- Negation of a `BPoly`, each `x`-coefficient negated via `cneg`. -/
def bneg (p : BPoly) : BPoly := p.map cneg

/-- Subtraction of `BPoly`s, `p − q := p + (−q)`. -/
def bsub (p q : BPoly) : BPoly := badd p (bneg q)

/-- Scale by a `CPoly` (a `ℚ[t]` scalar) `bscaleC c p`: multiply every `x`-coefficient by `c`. -/
def bscaleC (c : CPoly) (p : BPoly) : BPoly := p.map (cmul c)

/-- Shift in `x` `bshift k p = xᵏ · p`: prepend `k` zero `x`-coefficients. -/
def bshift : ℕ → BPoly → BPoly
  | 0, p => p
  | n + 1, p => [] :: bshift n p

/-- Polynomial multiplication of `BPoly`s in `x` (schoolbook convolution over `CPoly` coefficients). -/
def bmul : BPoly → BPoly → BPoly
  | [], _ => []
  | a :: as, q => badd (bscaleC a q) ([] :: bmul as q)

/-- Zero test for a `BPoly`: `true` iff it normalizes to `[]`. -/
def bisZero (p : BPoly) : Bool := bnorm p == []

/-- `x`-degree of a `BPoly` as a `ℕ`: `(length of bnorm p) − 1`, with `bdeg 0 = 0`. -/
def bdeg (p : BPoly) : ℕ := (bnorm p).length - 1

/-- Leading `x`-coefficient `blc p ∈ CPoly` (`= ℚ[t]`): the top nonzero `x`-coefficient, `[]` for the
zero polynomial. -/
def blc (p : BPoly) : CPoly := (bnorm p).getLast?.getD []

/-! ### Pseudo-division over the coefficient ring `ℚ[t]` -/

/-- Pseudo-remainder `bpsremainder fuel p q = prem(p, q)` over the non-field ring `ℚ[t]`: satisfies
`lc(q)^(deg p − deg q + 1) · p = s·q + prem` with `deg prem < deg q`; fuel-bounded. -/
def bpsremainder : ℕ → BPoly → BPoly → BPoly
  | 0, p, _ => bnorm p
  | fuel + 1, p, q =>
    let p := bnorm p
    let q := bnorm q
    if bisZero q then bnorm p
    else if p.length < q.length then p
    else
      let k := p.length - q.length
      let lcq := blc q
      let lcp := blc p
      -- `lc(q)·p − lc(p)·xᵏ·q`: kills the leading term, stays in `ℚ[t][x]`.
      let p' := bnorm (bsub (bscaleC lcq p) (bscaleC lcp (bshift k q)))
      bpsremainder fuel p' q

/-! ### `ℚ[t]`-content management (so the LRT gcd comes out clean) -/

/-- `ℚ[t]`-content of a `BPoly`: the `CPoly`-gcd of all its `x`-coefficients. -/
def bcontentX (fuel : ℕ) (p : BPoly) : CPoly :=
  (bnorm p).foldl (fun g c => (cgcdExt fuel g c).1) []

/-- Strip the `ℚ[t]`-content in `x`: `bprimitivePartX fuel p = p / content_x(p)`, the
`ℚ[t]`-primitive part. -/
def bprimitivePartX (fuel : ℕ) (p : BPoly) : BPoly :=
  let p := bnorm p
  let g := bcontentX fuel p
  if cisZero g then p else bnorm (p.map (fun c => cdiv fuel c g))

/-! ### Reduction and inversion modulo a `ℚ[t]` factor `R(t)` (the residue ring `ℚ[t]/(R)`)
The degree-`j` subresultant reduced mod `R` and made monic in `x` over `ℚ[t]/(R)` is the normalized
log argument `S(t,x)`; the leading `x`-coefficient is a unit there, so monic normalization is exact
via the extended-Euclidean inverse. -/

/-- Reduce a `CPoly` modulo `R`: `credR fuel R c = c mod R`, the representative in `ℚ[t]/(R)`. -/
def credR (fuel : ℕ) (R c : CPoly) : CPoly := cmod fuel c R

/-- Reduce every `x`-coefficient of a `BPoly` modulo `R`: `bredR fuel R p`, the image of `p` in
`(ℚ[t]/(R))[x]`. -/
def bredR (fuel : ℕ) (R : CPoly) (p : BPoly) : BPoly := bnorm (p.map (credR fuel R))

/-- Inverse of a `CPoly` modulo `R`: `cinvMod fuel R c = c⁻¹` in `ℚ[t]/(R)` (assumes `c` a unit mod
`R`), via `c⁻¹ ≡ s/g (mod R)` from the Bézout relation `s·c + ·R = g`. -/
def cinvMod (fuel : ℕ) (R c : CPoly) : CPoly :=
  let (g, s, _) := cgcdExt fuel c R
  credR fuel R (cscale (clead g)⁻¹ s)

/-- Make a `BPoly` monic in `x` over `ℚ[t]/(R)`: `bmonicXmodR fuel R p` reduces mod `R` and scales by
the mod-`R` inverse of the leading `x`-coefficient. -/
def bmonicXmodR (fuel : ℕ) (R : CPoly) (p : BPoly) : BPoly :=
  let p := bredR fuel R p
  if bisZero p then []
  else
    let inv := cinvMod fuel R (blc p)
    bnorm (p.map (fun c => credR fuel R (cmul c inv)))

/-! ### Exact `ℚ[t]`-division of a `BPoly` by a `CPoly`, and `ℚ[t]` powers -/

/-- Exact `ℚ[t]`-scalar division `bdivC fuel p c = p / c`: divide every `x`-coefficient of `p` by the
`CPoly` scalar `c`. -/
def bdivC (fuel : ℕ) (p : BPoly) (c : CPoly) : BPoly := bnorm (p.map (fun a => cdiv fuel a c))

/-- `ℚ[t]`-power `cpowP c n = cⁿ` (`CPoly` power, by `ℕ`-recursion). -/
def cpowP (c : CPoly) : ℕ → CPoly
  | 0 => [1]
  | n + 1 => cmul c (cpowP c n)

/-! ### The subresultant PRS (Collins–Brown)
The subresultant polynomial-remainder sequence computes the whole gcd chain with exact `ℚ[t]`
divisions that strip the pseudo-remainder `lc`-power inflation, so the degree-`j` element is the true
subresultant. -/

/-- Subresultant polynomial-remainder sequence `subresPRS fuel P Q = [R₁, R₂, …]` with `R₁ = P`,
`R₂ = Q`; the degree-`j` element is the `j`-th subresultant up to sign. Fuel-bounded. -/
def subresPRS (fuel : ℕ) (P Q : BPoly) : List BPoly :=
  -- `go Ri_1 Ri psi delta_prev fuelOuter`: `delta_prev = δ` of the step that produced `Ri` from `Ri_1`.
  let rec go : ℕ → BPoly → BPoly → CPoly → ℕ → List BPoly
    | 0, _, _, _, _ => []
    | fo + 1, Ri_1, Ri, psi, deltaPrev =>
      if bisZero Ri then []
      else
        let lcRi_1 : CPoly := blc Ri_1
        -- update ψ: ψ' = (−lc Ri_1)^δ / ψ^{δ−1}  (δ = deltaPrev ≥ 1)
        let negLc : CPoly := cneg lcRi_1
        let psi' : CPoly :=
          if deltaPrev = 0 then psi
          else cdiv fuel (cpowP negLc deltaPrev) (cpowP psi (deltaPrev - 1))
        -- β = −lc(Ri_1) · ψ'^δ
        let beta : CPoly := cmul negLc (cpowP psi' deltaPrev)
        let pr : BPoly := bpsremainder fuel Ri_1 Ri
        let Ri1 : BPoly := bdivC fuel pr beta
        let deltaNew : ℕ := bdeg Ri - bdeg Ri1
        Ri :: go fo Ri Ri1 psi' deltaNew
  P :: go fuel P Q [-1] (bdeg P - bdeg Q)

/-- The subresultant at `x`-degree `j` `bsubresultantGcd fuel j P Q`: the element of `subresPRS`
whose `x`-degree is `j` (the subresultant `Sⱼ` up to sign), or `[]` if none. -/
def bsubresultantGcd (fuel : ℕ) (j : ℕ) (P Q : BPoly) : BPoly :=
  ((subresPRS fuel P Q).filter (fun R => decide (bdeg R = j ∧ ¬ bisZero R))).getLast?.getD []

/-! ### Lifting `ℚ[x]` (a `CPoly`) into `BPoly`, and building `A − t·D'` -/

/-- Lift a `CPoly` (`= ℚ[x]`) into `BPoly`: `liftCtoBPoly p` makes each `x`-coefficient `aᵢ` the
constant `ℚ[t]` polynomial `[aᵢ]`. -/
def liftCtoBPoly (p : CPoly) : BPoly := p.map cC

/-- The variable `t` as a `CPoly`: `ctVar = [0, 1]`. -/
def ctVar : CPoly := [0, 1]

/-- The log argument's second operand `bArgAmtD' A D = A − t·D'` as a `BPoly`: `A` lifted with
constant `t`-coefficients, minus `t · D'`. -/
def bArgAmtD' (A D : CPoly) : BPoly :=
  bsub (liftCtoBPoly A) (bscaleC ctVar (liftCtoBPoly (cderiv D)))

/-- The raw degree-`j` subresultant `lrtSubresultantCompute fuel j A D = Sⱼ(D, A − t·D')`: the
bivariate subresultant of `D` (lifted) and `A − t·D'` at `x`-degree `j`, `ℚ[t]`-primitive in `x`. -/
def lrtSubresultantCompute (fuel : ℕ) (j : ℕ) (A D : CPoly) : BPoly :=
  bprimitivePartX fuel (bsubresultantGcd fuel j (liftCtoBPoly D) (bArgAmtD' A D))

/-- The computable log argument `lrtGcdCompute fuel j R A D = S(t,x)`: the degree-`j` subresultant
reduced modulo `R(t)` and made monic in `x` over `ℚ[t]/(R)`, the `S(t,x)` inside the logarithms of
`∫ A/D = ∑_{R(a)=0} a·log(S(a,x))`. -/
def lrtGcdCompute (fuel : ℕ) (j : ℕ) (R A D : CPoly) : BPoly :=
  bmonicXmodR fuel R (lrtSubresultantCompute fuel j A D)


end Compute

end DeepWiki.SymbolicIntegration
