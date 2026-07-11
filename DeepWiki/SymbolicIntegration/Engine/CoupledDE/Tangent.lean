import DeepWiki.SymbolicIntegration.Engine.CoupledDE.Basic

/-! # Tangent RDE cancellation

Executable `t = tan(x)` coupled-system operations and the degree-dropping cancellation solver
`cCoupledDECancelTan`. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly

namespace DensePoly

/-! ## Tangent `t`-polynomial operations -/

/-- `tanDeriv p`: tangent monomial derivation `D = ∂/∂x + (t²+1)·∂/∂t` on a represented-coefficient
`t`-polynomial (`Dt = t²+1`). -/
def tanDeriv {P : Type → Type} [CPoly P] [CPolyEngine P] (p : List (P ℚ)) : List (P ℚ) :=
  letI : CCommRing (P ℚ) := CPolyEngine.toCCommRing
  -- κ_D: coefficientwise d/dx
  let kappa : List (P ℚ) := p.map CPolyEngine.deriv
  -- (t²+1)·dp/dt : shift the formal t-derivative by t² and by t⁰.
  let dpdt : List (P ℚ) :=
    (p.drop 1).zipIdx.map (fun (c, i) => CPolyEngine.scale ((i : ℚ) + 1) c)
  -- multiply dpdt by (t²+1): result_k = dpdt_{k-2} + dpdt_k
  let mulDt : List (P ℚ) :=
    (List.range (dpdt.length + 2)).map (fun k =>
      let lo : P ℚ := if k ≥ 2 then dpdt.getD (k - 2) CPoly.czero else CPoly.czero
      let hi : P ℚ := dpdt.getD k CPoly.czero
      CPolyEngine.add lo hi)
  -- add κ_D and (t²+1)dp/dt coefficientwise (over the t-degree).
  DensePoly.cadd kappa mulDt

example :
    let x : CPoly.SparsePoly ℚ := CPoly.SparsePoly.ofList [(1, 1)]
    let out := tanDeriv [x]
    out.length = 2 ∧
      CPolyEngine.cdeg (out.getD 0 CPoly.czero) = 0 ∧
      CPolyEngine.cisZero (out.getD 0 CPoly.czero) = false ∧
      CPolyEngine.cisZero (out.getD 1 CPoly.czero) = true := by
  native_decide

end DensePoly

/-- `cscaleListQ s p`: scale every represented coefficient of `p` by `s ∈ ℚ`. -/
def cscaleListQ {P : Type → Type} [CPoly P] [CPolyEngine P]
    (s : ℚ) (p : List (P ℚ)) : List (P ℚ) :=
  p.map (CPolyEngine.scale s)

/-! ## Gaussian evaluation and exact division -/

/-- `evalAtI p = (re, im)`: evaluate a represented-coefficient polynomial at `t = √−1`. -/
def evalAtI {P : Type → Type} [CPoly P] [CPolyEngine P]
    (p : List (P ℚ)) : P ℚ × P ℚ :=
  p.foldr (fun (a : P ℚ) (acc : P ℚ × P ℚ) =>
    -- acc = (u, v) standing for u + v√−1; new = a + √−1·acc = a + (u + v√−1)√−1 = (a − v) + u√−1.
    (CPolyEngine.add a (CPolyEngine.scale (-1) acc.2), acc.1)) (CPoly.czero, CPoly.czero)

/-- `cmulI (a,b) (c,d) = (ac − bd, ad + bc)`: `k(√−1)`-multiplication on pairs (`√−1² = −1`). -/
def cmulI {P : Type → Type} [CPoly P] [CPolyEngine P]
    (x y : P ℚ × P ℚ) : P ℚ × P ℚ :=
  (CPolyEngine.sub (CPolyEngine.mul x.1 y.1) (CPolyEngine.mul x.2 y.2),
    CPolyEngine.add (CPolyEngine.mul x.1 y.2) (CPolyEngine.mul x.2 y.1))

/-- `csubI (a,b) (c,d) = (a−c, b−d)`: `k(√−1)`-subtraction on pairs. -/
def csubI {P : Type → Type} [CPoly P] [CPolyEngine P]
    (x y : P ℚ × P ℚ) : P ℚ × P ℚ :=
  (CPolyEngine.sub x.1 y.1, CPolyEngine.sub x.2 y.2)

/-- `cisZeroI (a,b)`: `k(√−1)`-zero test on a pair (both parts vanish). -/
def cisZeroI {P : Type → Type} [CPoly P] [CPolyEngine P] (x : P ℚ × P ℚ) : Bool :=
  CPolyEngine.cisZero x.1 && CPolyEngine.cisZero x.2

/-- `divByTminusI p = q` with `p = (t − √−1)·q`: synthetic (Ruffini) division of a `k(√−1)[t]`-poly
by `t − √−1`, exact when `p(√−1) = 0`; the remainder is dropped. -/
def divByTminusI {P : Type → Type} [CPoly P] [CPolyEngine P]
    (p : List (P ℚ × P ℚ)) : List (P ℚ × P ℚ) :=
  let I : P ℚ × P ℚ := (CPoly.czero, CPoly.one)     -- √−1
  -- Horner from the top: coefficients of the quotient, high→low, then reverse.
  let rec go : List (P ℚ × P ℚ) → P ℚ × P ℚ →
      List (P ℚ × P ℚ) → List (P ℚ × P ℚ)
    | [], _, acc => acc                                   -- last (lowest) coeff is the remainder, dropped
    | a :: rest, carry, acc =>
        -- current quotient coefficient = carry; next carry = a + √−1·carry.
        go rest (cadd' a (cmulI I carry)) (carry :: acc)
  -- `cadd'` on pairs:
  go (p.reverse) (CPoly.czero, CPoly.czero) [] |>.drop 0
where
  /-- pair addition for the synthetic-division carry. -/
  cadd' (x y : P ℚ × P ℚ) : P ℚ × P ℚ :=
    (CPolyEngine.add x.1 y.1, CPolyEngine.add x.2 y.2)

example :
    CPolyEngine.cisZero (cmulI
      ((CPoly.czero, CPoly.one) : CPoly.SparsePoly ℚ × CPoly.SparsePoly ℚ)
      (CPoly.czero, CPoly.one)).2 = true := by
  native_decide

namespace DensePoly

/-! ## Tangent cancellation solver -/

/-- `cCoupledDECancelTan dbound b0 b2 c1 c2 n`: hypertangent RDE cancellation over `k = ℚ(x)`,
`t = tan(x)`, `η = 1`, `a = −1`, solving `(Dq₁; Dq₂) + [[b₀−nt, −b₂], [b₂, b₀−nt]]·(q₁; q₂) = (c₁; c₂)`
for `q₁, q₂ ∈ k[t]` of `t`-degree `≤ n` (`D = tanDeriv`). Recurses structurally on `n`: each level a
base `cCoupledDESystem` solve (ansatz degree `≤ dbound`) after evaluating the `cᵢ` at `t = √−1`, then a
`t − √−1` division dropping the degree. Returns `some (q₁, q₂)` or `none`. -/
def cCoupledDECancelTan [CLinearSolve ℚ] (dbound : ℕ) (b0 b2 : DensePoly ℚ) :
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
