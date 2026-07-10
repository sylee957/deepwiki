import DeepWiki.SymbolicIntegration.Engine.CoupledDE.Basic

/-! # Tangent RDE cancellation

Executable `t = tan(x)` coupled-system operations and the degree-dropping cancellation solver
`cCoupledDECancelTan`. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

namespace DensePoly

/-! ## Tangent `t`-polynomial operations -/

/-- `tanDeriv p`: tangent monomial derivation `D = ∂/∂x + (t²+1)·∂/∂t` on a `t`-polynomial over
`ℚ[x]` (`Dt = t²+1`). -/
def tanDeriv (p : List (DensePoly ℚ)) : List (DensePoly ℚ) :=
  -- κ_D: coefficientwise d/dx
  let kappa : List (DensePoly ℚ) := p.map cderiv
  -- (t²+1)·dp/dt : shift the formal t-derivative by t² and by t⁰.
  let dpdt : List (DensePoly ℚ) := (p.drop 1).zipIdx.map (fun (c, i) => cscale ((i : ℚ) + 1) c)
  -- multiply dpdt by (t²+1): result_k = dpdt_{k-2} + dpdt_k
  let mulDt : List (DensePoly ℚ) :=
    (List.range (dpdt.length + 2)).map (fun k =>
      let lo : DensePoly ℚ := if k ≥ 2 then dpdt.getD (k - 2) [] else []
      let hi : DensePoly ℚ := dpdt.getD k []
      cadd lo hi)
  -- add κ_D and (t²+1)dp/dt coefficientwise (over the t-degree).
  DensePoly.cadd kappa mulDt

/-- `cscaleListQ s p`: scale every `ℚ[x]`-coefficient of the `t`-polynomial `p` by `s ∈ ℚ`. -/
def cscaleListQ (s : ℚ) (p : List (DensePoly ℚ)) : List (DensePoly ℚ) := p.map (cscale s)

/-! ## Gaussian evaluation and exact division -/

/-- `evalAtI p = (re, im)`: evaluate a `k[t]`-polynomial at `t = √−1`, `p(√−1) = re + im·√−1`
(Horner mod `t²+1`). -/
def evalAtI (p : List (DensePoly ℚ)) : DensePoly ℚ × DensePoly ℚ :=
  p.foldr (fun (a : DensePoly ℚ) (acc : DensePoly ℚ × DensePoly ℚ) =>
    -- acc = (u, v) standing for u + v√−1; new = a + √−1·acc = a + (u + v√−1)√−1 = (a − v) + u√−1.
    (cadd a (cscale (-1) acc.2), acc.1)) ([], [])

/-- `cmulI (a,b) (c,d) = (ac − bd, ad + bc)`: `k(√−1)`-multiplication on pairs (`√−1² = −1`). -/
def cmulI (x y : DensePoly ℚ × DensePoly ℚ) : DensePoly ℚ × DensePoly ℚ :=
  (csub (cmul x.1 y.1) (cmul x.2 y.2), cadd (cmul x.1 y.2) (cmul x.2 y.1))

/-- `csubI (a,b) (c,d) = (a−c, b−d)`: `k(√−1)`-subtraction on pairs. -/
def csubI (x y : DensePoly ℚ × DensePoly ℚ) : DensePoly ℚ × DensePoly ℚ :=
  (csub x.1 y.1, csub x.2 y.2)

/-- `cisZeroI (a,b)`: `k(√−1)`-zero test on a pair (both parts vanish). -/
def cisZeroI (x : DensePoly ℚ × DensePoly ℚ) : Bool := cisZero x.1 && cisZero x.2

/-- `divByTminusI p = q` with `p = (t − √−1)·q`: synthetic (Ruffini) division of a `k(√−1)[t]`-poly
by `t − √−1`, exact when `p(√−1) = 0`; the remainder is dropped. -/
def divByTminusI (p : List (DensePoly ℚ × DensePoly ℚ)) : List (DensePoly ℚ × DensePoly ℚ) :=
  let I : DensePoly ℚ × DensePoly ℚ := ([], [CCommRing.one])     -- √−1
  -- Horner from the top: coefficients of the quotient, high→low, then reverse.
  let rec go : List (DensePoly ℚ × DensePoly ℚ) → DensePoly ℚ × DensePoly ℚ →
      List (DensePoly ℚ × DensePoly ℚ) → List (DensePoly ℚ × DensePoly ℚ)
    | [], _, acc => acc                                   -- last (lowest) coeff is the remainder, dropped
    | a :: rest, carry, acc =>
        -- current quotient coefficient = carry; next carry = a + √−1·carry.
        go rest (cadd' a (cmulI I carry)) (carry :: acc)
  -- `cadd'` on pairs:
  go (p.reverse) ([], []) [] |>.drop 0
where
  /-- pair addition for the synthetic-division carry. -/
  cadd' (x y : DensePoly ℚ × DensePoly ℚ) : DensePoly ℚ × DensePoly ℚ := (cadd x.1 y.1, cadd x.2 y.2)

/-! ## Tangent cancellation solver -/

/-- `cCoupledDECancelTan dbound b0 b2 c1 c2 n`: hypertangent RDE cancellation over `k = ℚ(x)`,
`t = tan(x)`, `η = 1`, `a = −1`, solving `(Dq₁; Dq₂) + [[b₀−nt, −b₂], [b₂, b₀−nt]]·(q₁; q₂) = (c₁; c₂)`
for `q₁, q₂ ∈ k[t]` of `t`-degree `≤ n` (`D = tanDeriv`). Recurses structurally on `n`: each level a
base `cCoupledDESystem` solve (ansatz degree `≤ dbound`) after evaluating the `cᵢ` at `t = √−1`, then a
`t − √−1` division dropping the degree. Returns `some (q₁, q₂)` or `none`. -/
def cCoupledDECancelTan (dbound : ℕ) (b0 b2 : DensePoly ℚ) :
    (c1 c2 : List (DensePoly ℚ)) → (n : ℕ) → Option (List (DensePoly ℚ) × List (DensePoly ℚ))
  | c1, c2, 0 =>
    -- n = 0: c₁, c₂ must be in k (degree-0 in t); solve the base coupled system directly.
    if cdeg c1 = 0 && cdeg c2 = 0 then
      match cCoupledDESystem (-1) b0 b2 (c1.getD 0 []) (c2.getD 0 []) dbound with
      | none => none
      | some (s1, s2) => some ([s1], [s2])
    else none
  | c1, c2, n + 1 =>
    let nN : ℚ := ((n : ℚ) + 1)                              -- n (as ℚ for nη scaling), η = 1
    -- z₁ + z₂√−1 = c₁(√−1) + c₂(√−1)√−1.
    let e1 := evalAtI c1                                     -- c₁(√−1) = (re, im)
    let e2 := evalAtI c2                                     -- c₂(√−1)
    -- c₂(√−1)·√−1 = (−e2.im, e2.re); z = e1 + that.
    let z1 := csub e1.1 e2.2
    let z2 := cadd e1.2 e2.1
    -- base solve CoupledDESystem(b₀, b₂ − nη, z₁, z₂), η = 1 ⇒ shift b₂ by −(n+1).
    let b2shift := csub b2 (cscale nN [CCommRing.one])
    match cCoupledDESystem (-1) b0 b2shift z1 z2 dbound with
    | none => none
    | some (s1, s2) =>
      -- numerator of c·p: real = c₁ − z₁ + nη(s₁t + s₂); imag = c₂ − z₂ + nη(s₂t − s₁).
      -- s₁t = [0, s₁], s₂t = [0, s₂] as t-polynomials.
      let s1t : List (DensePoly ℚ) := [[], s1]
      let s2t : List (DensePoly ℚ) := [[], s2]
      let realNum := DensePoly.cadd (DensePoly.csub c1 [z1]) (cscaleListQ nN (DensePoly.cadd s1t [s2]))
      let imagNum := DensePoly.cadd (DensePoly.csub c2 [z2]) (cscaleListQ nN (DensePoly.csub s2t [s1]))
      -- assemble the k(√−1)[t]-polynomial (pairs) and divide by t − √−1.
      let len := max realNum.length imagNum.length
      let cpairs : List (DensePoly ℚ × DensePoly ℚ) :=
        (List.range len).map (fun k => (realNum.getD k [], imagNum.getD k []))
      let quot := divByTminusI cpairs
      let d1 : List (DensePoly ℚ) := quot.map Prod.fst
      let d2 : List (DensePoly ℚ) := quot.map Prod.snd
      match cCoupledDECancelTan dbound b0 (cadd b2 [CCommRing.one]) d1 d2 n with
      | none => none
      | some (h1, h2) =>
        -- return (h₁t + h₂ + s₁, h₂t − h₁ + s₂).
        let h1t : List (DensePoly ℚ) := [[]] ++ h1     -- h₁·t (shift up by one t-degree)
        let h2t : List (DensePoly ℚ) := [[]] ++ h2
        let q1 := DensePoly.cadd (DensePoly.cadd h1t h2) [s1]
        let q2 := DensePoly.csub (DensePoly.cadd h2t [s2]) h1
        some (q1, q2)

end DensePoly

end DeepWiki.SymbolicIntegration
