import DeepWiki.SymbolicIntegration.Engine.CoupledDE.Basic

/-! # Tangent RDE cancellation

Executable `t = tan(x)` coupled-system operations and the degree-dropping cancellation solver
`cCoupledDECancelTan`. -/

namespace DeepWiki.SymbolicIntegration

open CPoly

namespace CPoly

/-! ## Tangent `t`-polynomial operations -/

/-- `tanDeriv p`: tangent monomial derivation `D = ∂/∂x + (t²+1)·∂/∂t` on a `t`-polynomial over
`ℚ[x]` (`Dt = t²+1`). -/
def tanDeriv (p : List (CPoly ℚ)) : List (CPoly ℚ) :=
  -- κ_D: coefficientwise d/dx
  let kappa : List (CPoly ℚ) := p.map cderivQ
  -- (t²+1)·dp/dt : shift the formal t-derivative by t² and by t⁰.
  let dpdt : List (CPoly ℚ) := (p.drop 1).zipIdx.map (fun (c, i) => cscaleG ((i : ℚ) + 1) c)
  -- multiply dpdt by (t²+1): result_k = dpdt_{k-2} + dpdt_k
  let mulDt : List (CPoly ℚ) :=
    (List.range (dpdt.length + 2)).map (fun k =>
      let lo : CPoly ℚ := if k ≥ 2 then dpdt.getD (k - 2) [] else []
      let hi : CPoly ℚ := dpdt.getD k []
      caddG lo hi)
  -- add κ_D and (t²+1)dp/dt coefficientwise (over the t-degree).
  let n := max kappa.length mulDt.length
  (List.range n).map (fun k => caddG (kappa.getD k []) (mulDt.getD k []))

/-- `tcoeff p m`: the `tᵐ`-coefficient (in `ℚ(x)`) of a `t`-polynomial, `[]` (zero) past the end. -/
def tcoeff (p : List (CPoly ℚ)) (m : ℕ) : CPoly ℚ := p.getD m []

/-- `tdeg p`: the `t`-degree (highest index with a nonzero coefficient), `0` for the zero polynomial. -/
def tdeg (p : List (CPoly ℚ)) : ℕ :=
  ((p.zipIdx.filter (fun (c, _) => ¬ cisZeroG c)).map (fun (_, i) => i)).foldl max 0

/-- `t`-polynomial zero test `tisZero p`: every `ℚ(x)`-coefficient is zero. -/
def tisZero (p : List (CPoly ℚ)) : Bool := p.all cisZeroG

/-- `tshiftScale s m = s·tᵐ`: the single-term `t`-polynomial `[0,…,0,s]` with `m` leading zeros. -/
def tshiftScale (s : CPoly ℚ) (m : ℕ) : List (CPoly ℚ) :=
  (List.replicate m ([] : CPoly ℚ)) ++ [s]

/-- `tsub p q`: coefficientwise subtraction `pₖ − qₖ` of `t`-polynomials over `ℚ(x)`. -/
def tsub (p q : List (CPoly ℚ)) : List (CPoly ℚ) :=
  let n := max p.length q.length
  (List.range n).map (fun k => csubG (p.getD k []) (q.getD k []))

/-- `tadd p q`: coefficientwise addition `pₖ + qₖ` of `t`-polynomials over `ℚ(x)`. -/
def tadd (p q : List (CPoly ℚ)) : List (CPoly ℚ) :=
  let n := max p.length q.length
  (List.range n).map (fun k => caddG (p.getD k []) (q.getD k []))

/-- `cscaleListQ s p`: scale every `ℚ[x]`-coefficient of the `t`-polynomial `p` by `s ∈ ℚ`. -/
def cscaleListQ (s : ℚ) (p : List (CPoly ℚ)) : List (CPoly ℚ) := p.map (cscaleG s)

/-! ## Gaussian evaluation and exact division -/

/-- `evalAtI p = (re, im)`: evaluate a `k[t]`-polynomial at `t = √−1`, `p(√−1) = re + im·√−1`
(Horner mod `t²+1`). -/
def evalAtI (p : List (CPoly ℚ)) : CPoly ℚ × CPoly ℚ :=
  p.foldr (fun (a : CPoly ℚ) (acc : CPoly ℚ × CPoly ℚ) =>
    -- acc = (u, v) standing for u + v√−1; new = a + √−1·acc = a + (u + v√−1)√−1 = (a − v) + u√−1.
    (caddG a (cscaleG (-1) acc.2), acc.1)) ([], [])

/-- `cmulI (a,b) (c,d) = (ac − bd, ad + bc)`: `k(√−1)`-multiplication on pairs (`√−1² = −1`). -/
def cmulI (x y : CPoly ℚ × CPoly ℚ) : CPoly ℚ × CPoly ℚ :=
  (csubG (cmulG x.1 y.1) (cmulG x.2 y.2), caddG (cmulG x.1 y.2) (cmulG x.2 y.1))

/-- `csubI (a,b) (c,d) = (a−c, b−d)`: `k(√−1)`-subtraction on pairs. -/
def csubI (x y : CPoly ℚ × CPoly ℚ) : CPoly ℚ × CPoly ℚ :=
  (csubG x.1 y.1, csubG x.2 y.2)

/-- `cisZeroI (a,b)`: `k(√−1)`-zero test on a pair (both parts vanish). -/
def cisZeroI (x : CPoly ℚ × CPoly ℚ) : Bool := cisZeroG x.1 && cisZeroG x.2

/-- `divByTminusI p = q` with `p = (t − √−1)·q`: synthetic (Ruffini) division of a `k(√−1)[t]`-poly
by `t − √−1`, exact when `p(√−1) = 0`; the remainder is dropped. -/
def divByTminusI (p : List (CPoly ℚ × CPoly ℚ)) : List (CPoly ℚ × CPoly ℚ) :=
  let I : CPoly ℚ × CPoly ℚ := ([], [CField.one])     -- √−1
  -- Horner from the top: coefficients of the quotient, high→low, then reverse.
  let rec go : List (CPoly ℚ × CPoly ℚ) → CPoly ℚ × CPoly ℚ →
      List (CPoly ℚ × CPoly ℚ) → List (CPoly ℚ × CPoly ℚ)
    | [], _, acc => acc                                   -- last (lowest) coeff is the remainder, dropped
    | a :: rest, carry, acc =>
        -- current quotient coefficient = carry; next carry = a + √−1·carry.
        go rest (caddG' a (cmulI I carry)) (carry :: acc)
  -- `caddG'` on pairs:
  go (p.reverse) ([], []) [] |>.drop 0
where
  /-- pair addition for the synthetic-division carry. -/
  caddG' (x y : CPoly ℚ × CPoly ℚ) : CPoly ℚ × CPoly ℚ := (caddG x.1 y.1, caddG x.2 y.2)

/-! ## Tangent cancellation solver -/

/-- `cCoupledDECancelTan dbound b0 b2 c1 c2 n`: hypertangent RDE cancellation over `k = ℚ(x)`,
`t = tan(x)`, `η = 1`, `a = −1`, solving `(Dq₁; Dq₂) + [[b₀−nt, −b₂], [b₂, b₀−nt]]·(q₁; q₂) = (c₁; c₂)`
for `q₁, q₂ ∈ k[t]` of `t`-degree `≤ n` (`D = tanDeriv`). Recurses structurally on `n`: each level a
base `cCoupledDESystem` solve (ansatz degree `≤ dbound`) after evaluating the `cᵢ` at `t = √−1`, then a
`t − √−1` division dropping the degree. Returns `some (q₁, q₂)` or `none`. -/
def cCoupledDECancelTan (dbound : ℕ) (b0 b2 : CPoly ℚ) :
    (c1 c2 : List (CPoly ℚ)) → (n : ℕ) → Option (List (CPoly ℚ) × List (CPoly ℚ))
  | c1, c2, 0 =>
    -- n = 0: c₁, c₂ must be in k (degree-0 in t); solve the base coupled system directly.
    if tdeg c1 = 0 && tdeg c2 = 0 then
      match cCoupledDESystem (-1) b0 b2 (tcoeff c1 0) (tcoeff c2 0) dbound with
      | none => none
      | some (s1, s2) => some ([s1], [s2])
    else none
  | c1, c2, n + 1 =>
    let nN : ℚ := ((n : ℚ) + 1)                              -- n (as ℚ for nη scaling), η = 1
    -- z₁ + z₂√−1 = c₁(√−1) + c₂(√−1)√−1.
    let e1 := evalAtI c1                                     -- c₁(√−1) = (re, im)
    let e2 := evalAtI c2                                     -- c₂(√−1)
    -- c₂(√−1)·√−1 = (−e2.im, e2.re); z = e1 + that.
    let z1 := csubG e1.1 e2.2
    let z2 := caddG e1.2 e2.1
    -- base solve CoupledDESystem(b₀, b₂ − nη, z₁, z₂), η = 1 ⇒ shift b₂ by −(n+1).
    let b2shift := csubG b2 (cscaleG nN [CField.one])
    match cCoupledDESystem (-1) b0 b2shift z1 z2 dbound with
    | none => none
    | some (s1, s2) =>
      -- numerator of c·p: real = c₁ − z₁ + nη(s₁t + s₂); imag = c₂ − z₂ + nη(s₂t − s₁).
      -- s₁t = [0, s₁], s₂t = [0, s₂] as t-polynomials.
      let s1t : List (CPoly ℚ) := [[], s1]
      let s2t : List (CPoly ℚ) := [[], s2]
      let realNum := tadd (tsub c1 [z1]) (cscaleListQ nN (tadd s1t [s2]))
      let imagNum := tadd (tsub c2 [z2]) (cscaleListQ nN (tsub s2t [s1]))
      -- assemble the k(√−1)[t]-polynomial (pairs) and divide by t − √−1.
      let len := max realNum.length imagNum.length
      let cpairs : List (CPoly ℚ × CPoly ℚ) :=
        (List.range len).map (fun k => (realNum.getD k [], imagNum.getD k []))
      let quot := divByTminusI cpairs
      let d1 : List (CPoly ℚ) := quot.map Prod.fst
      let d2 : List (CPoly ℚ) := quot.map Prod.snd
      match cCoupledDECancelTan dbound b0 (caddG b2 [CField.one]) d1 d2 n with
      | none => none
      | some (h1, h2) =>
        -- return (h₁t + h₂ + s₁, h₂t − h₁ + s₂).
        let h1t : List (CPoly ℚ) := [[]] ++ h1     -- h₁·t (shift up by one t-degree)
        let h2t : List (CPoly ℚ) := [[]] ++ h2
        let q1 := tadd (tadd h1t h2) [s1]
        let q2 := tsub (tadd h2t [s2]) h1
        some (q1, q2)

end CPoly

end DeepWiki.SymbolicIntegration
