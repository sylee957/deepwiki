import DeepWiki.SymbolicIntegration.Compute.Squarefree

/-! # Computable bivariate subresultant gcd / log argument over `ℚ[t]`
The logarithmic part puts `S(t,x) = gcd_x(D(x), A(x) − t·D'(x))` inside the logarithms of
`∫ A/D = ∑_{R(a)=0} a·log(S(a,x))`. This bivariate `ℚ[t][x]` gcd is computed by the subresultant
polynomial-remainder sequence over the non-field ring `ℚ[t]`, on an executable carrier
`BPoly := List CPolyQ`. Agreement with the noncomputable `lrtSubresultant` is proven in
`SubresultantCorrectness`. -/

namespace DeepWiki.SymbolicIntegration

namespace Compute

/-! ### The bivariate carrier `BPoly = List CPolyQ` (`ℚ[t][x]`) -/

/-- Bivariate dense carrier `BPoly := List CPolyQ`: a polynomial in `x` whose coefficients are `CPolyQ`
(`= ℚ[t]`), index = `x`-degree low→high. -/
abbrev BPoly := List CPolyQ

/-- Normalize a `BPoly`: normalize each `CPolyQ` coefficient, then strip trailing (high-`x`-degree)
zero coefficients. -/
def bnorm : BPoly → BPoly
  | [] => []
  | a :: as =>
    let a := cnorm a
    match bnorm as with
    | [] => if cisZero a then [] else [a]
    | r => a :: r

/-! The `BPoly` arithmetic is the ring-generalized generic engine at coefficient `CPolyQ`
(`BPoly = CPoly CPolyQ`, keystone `CCommRing (CPoly ℚ)`): each `b*` is the corresponding `c*`. -/

/-- Coefficientwise addition of two `BPoly`s in `x` — the generic `cadd` at coefficient `CPolyQ`. -/
def badd : BPoly → BPoly → BPoly := CPoly.cadd

/-- Negation of a `BPoly` — the generic `cneg` at coefficient `CPolyQ`. -/
def bneg (p : BPoly) : BPoly := CPoly.cneg p

/-- Subtraction of `BPoly`s — the generic `csub` at coefficient `CPolyQ`. -/
def bsub (p q : BPoly) : BPoly := CPoly.csub p q

/-- Scale by a `CPolyQ` (a `ℚ[t]` scalar) — the generic `cscale` at coefficient `CPolyQ`. -/
def bscaleC (c : CPolyQ) (p : BPoly) : BPoly := CPoly.cscale c p

/-- Shift in `x` `bshift k p = xᵏ · p` — the generic `cshift` at coefficient `CPolyQ`. -/
def bshift (k : ℕ) (p : BPoly) : BPoly := CPoly.cshift k p

/-- Polynomial multiplication of `BPoly`s in `x` — the generic `cmul` at coefficient `CPolyQ`. -/
def bmul : BPoly → BPoly → BPoly := CPoly.cmul

/-- Zero test for a `BPoly`: `true` iff it normalizes to `[]`. -/
def bisZero (p : BPoly) : Bool := bnorm p == []

/-- `x`-degree of a `BPoly` as a `ℕ`: `(length of bnorm p) − 1`, with `bdeg 0 = 0`. -/
def bdeg (p : BPoly) : ℕ := (bnorm p).length - 1

/-- Leading `x`-coefficient `blc p ∈ CPolyQ` (`= ℚ[t]`): the top nonzero `x`-coefficient, `[]` for the
zero polynomial. -/
def blc (p : BPoly) : CPolyQ := (bnorm p).getLast?.getD []

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

/-- `ℚ[t]`-content of a `BPoly`: the `CPolyQ`-gcd of all its `x`-coefficients. -/
def bcontentX (fuel : ℕ) (p : BPoly) : CPolyQ :=
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

/-- Reduce a `CPolyQ` modulo `R`: `credR fuel R c = c mod R`, the representative in `ℚ[t]/(R)`. -/
def credR (fuel : ℕ) (R c : CPolyQ) : CPolyQ := cmod fuel c R

/-- Reduce every `x`-coefficient of a `BPoly` modulo `R`: `bredR fuel R p`, the image of `p` in
`(ℚ[t]/(R))[x]`. -/
def bredR (fuel : ℕ) (R : CPolyQ) (p : BPoly) : BPoly := bnorm (p.map (credR fuel R))

/-- Inverse of a `CPolyQ` modulo `R`: `cinvMod fuel R c = c⁻¹` in `ℚ[t]/(R)` (assumes `c` a unit mod
`R`), via `c⁻¹ ≡ s/g (mod R)` from the Bézout relation `s·c + ·R = g`. -/
def cinvMod (fuel : ℕ) (R c : CPolyQ) : CPolyQ :=
  let (g, s, _) := cgcdExt fuel c R
  credR fuel R (cscale (clead g)⁻¹ s)

/-- Make a `BPoly` monic in `x` over `ℚ[t]/(R)`: `bmonicXmodR fuel R p` reduces mod `R` and scales by
the mod-`R` inverse of the leading `x`-coefficient. -/
def bmonicXmodR (fuel : ℕ) (R : CPolyQ) (p : BPoly) : BPoly :=
  let p := bredR fuel R p
  if bisZero p then []
  else
    let inv := cinvMod fuel R (blc p)
    bnorm (p.map (fun c => credR fuel R (cmul c inv)))

/-! ### Exact `ℚ[t]`-division of a `BPoly` by a `CPolyQ`, and `ℚ[t]` powers -/

/-- Exact `ℚ[t]`-scalar division `bdivC fuel p c = p / c`: divide every `x`-coefficient of `p` by the
`CPolyQ` scalar `c`. -/
def bdivC (fuel : ℕ) (p : BPoly) (c : CPolyQ) : BPoly := bnorm (p.map (fun a => cdiv fuel a c))

/-- `ℚ[t]`-power `cpowP c n = cⁿ` (`CPolyQ` power, by `ℕ`-recursion). -/
def cpowP (c : CPolyQ) : ℕ → CPolyQ
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
  let rec go : ℕ → BPoly → BPoly → CPolyQ → ℕ → List BPoly
    | 0, _, _, _, _ => []
    | fo + 1, Ri_1, Ri, psi, deltaPrev =>
      if bisZero Ri then []
      else
        let lcRi_1 : CPolyQ := blc Ri_1
        -- update ψ: ψ' = (−lc Ri_1)^δ / ψ^{δ−1}  (δ = deltaPrev ≥ 1)
        let negLc : CPolyQ := cneg lcRi_1
        let psi' : CPolyQ :=
          if deltaPrev = 0 then psi
          else cdiv fuel (cpowP negLc deltaPrev) (cpowP psi (deltaPrev - 1))
        -- β = −lc(Ri_1) · ψ'^δ
        let beta : CPolyQ := cmul negLc (cpowP psi' deltaPrev)
        let pr : BPoly := bpsremainder fuel Ri_1 Ri
        let Ri1 : BPoly := bdivC fuel pr beta
        let deltaNew : ℕ := bdeg Ri - bdeg Ri1
        Ri :: go fo Ri Ri1 psi' deltaNew
  P :: go fuel P Q [-1] (bdeg P - bdeg Q)

/-- The subresultant at `x`-degree `j` `bsubresultantGcd fuel j P Q`: the element of `subresPRS`
whose `x`-degree is `j` (the subresultant `Sⱼ` up to sign), or `[]` if none. -/
def bsubresultantGcd (fuel : ℕ) (j : ℕ) (P Q : BPoly) : BPoly :=
  ((subresPRS fuel P Q).filter (fun R => decide (bdeg R = j ∧ ¬ bisZero R))).getLast?.getD []

/-! ### Lifting `ℚ[x]` (a `CPolyQ`) into `BPoly`, and building `A − t·D'` -/

/-- Lift a `CPolyQ` (`= ℚ[x]`) into `BPoly`: `liftCtoBPoly p` makes each `x`-coefficient `aᵢ` the
constant `ℚ[t]` polynomial `[aᵢ]`. -/
def liftCtoBPoly (p : CPolyQ) : BPoly := p.map cC

/-- The variable `t` as a `CPolyQ`: `ctVar = [0, 1]`. -/
def ctVar : CPolyQ := [0, 1]

/-- The log argument's second operand `bArgAmtD' A D = A − t·D'` as a `BPoly`: `A` lifted with
constant `t`-coefficients, minus `t · D'`. -/
def bArgAmtD' (A D : CPolyQ) : BPoly :=
  bsub (liftCtoBPoly A) (bscaleC ctVar (liftCtoBPoly (cderiv D)))

/-- The raw degree-`j` subresultant `lrtSubresultantCompute fuel j A D = Sⱼ(D, A − t·D')`: the
bivariate subresultant of `D` (lifted) and `A − t·D'` at `x`-degree `j`, `ℚ[t]`-primitive in `x`. -/
def lrtSubresultantCompute (fuel : ℕ) (j : ℕ) (A D : CPolyQ) : BPoly :=
  bprimitivePartX fuel (bsubresultantGcd fuel j (liftCtoBPoly D) (bArgAmtD' A D))

/-- The computable log argument `lrtGcdCompute fuel j R A D = S(t,x)`: the degree-`j` subresultant
reduced modulo `R(t)` and made monic in `x` over `ℚ[t]/(R)`, the `S(t,x)` inside the logarithms of
`∫ A/D = ∑_{R(a)=0} a·log(S(a,x))`. -/
def lrtGcdCompute (fuel : ℕ) (j : ℕ) (R A D : CPolyQ) : BPoly :=
  bmonicXmodR fuel R (lrtSubresultantCompute fuel j A D)

/-! ### Logarithmic-part assembly -/

/-- Logarithmic part of `∫A/D`: `lrtLogPart fuel A D` returns the `(Qᵢ, Sᵢ)` pairs meaning
`∫A/D = ∑ᵢ ∑_{Qᵢ(a)=0} a·log(Sᵢ(a,x))`, for squarefree `D`. -/
def lrtLogPart (fuel : ℕ) (A D : CPolyQ) : List (CPolyQ × BPoly) :=
  let R := rtResultantCompute fuel A D
  (csqfreeFactor fuel R).map (fun (Qi, i) => (Qi, lrtGcdCompute fuel i Qi A D))


end Compute

end DeepWiki.SymbolicIntegration
