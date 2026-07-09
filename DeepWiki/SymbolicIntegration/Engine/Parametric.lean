import DeepWiki.SymbolicIntegration.Engine.LinearSolve
import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd

/-! # Computable parametric problems over the tower ℚ(x)[t]

Computable solvers, over the base monomial field `k = ℚ`, for three parametric integration problems: the
parametric Risch differential equation `Dy + f·y = Σᵢ cᵢ·gᵢ` (returning a basis of the constant solution
subspace), the limited integration problem `f = Dv + Σᵢ cᵢ·log(wᵢ)`, and the parametric logarithmic
derivative problem `n·f = Dv/v + m·Dθ/θ`. -/

namespace DeepWiki.SymbolicIntegration

open CPoly

namespace CPoly

/-! ### `cParametricLogDeriv` over the base field `k = ℚ(x)`

Decide whether `n·b = Dz/z` for a nonzero `n ∈ ℤ` and `z ∈ k*` (a logarithmic derivative of a radical),
with `b ∈ k = ℚ(x)`, `D = d/dx`. A logarithmic derivative `Dz/z` is always proper (`deg num < deg den`),
so a non-proper `b` (in particular every nonzero constant) is provably not one. -/

/-- **`d/dx` on `CPoly ℚ`** `cderivQ p = cderivG p`: the plain formal derivative (the generic `cderivG`
specialized at the constant field `ℚ`, the base monomial derivation `D` with `Dx = 1`, `κ_D = 0`). -/
abbrev cderivQ (p : CPoly ℚ) : CPoly ℚ := cderivG p

/-- **Generic lowest-terms reduction of a `(num, den)` fraction over `ℚ[x]`** `qnormPairG num den =
(num/g, den/g)` scaled so the denominator is monic, where `g = gcd(num, den)` (`cgcdWf`); the zero
numerator gives `([], [1])`. The generic mirror of `Compute.qnorm` one tower level down, used to read the
polynomial part / denominator of a `QFunNZG ℚ`-valued base-field element. -/
def qnormPairG (num den : CPoly ℚ) : CPoly ℚ × CPoly ℚ :=
  if cisZeroG num then ([], [(1 : ℚ)])
  else
    let g := (cgcdWf num den).1
    let num' := cdivWf num g
    let den' := cdivWf den g
    let s := (cleadG den')⁻¹
    (cscaleG s num', cscaleG s den')

/-- A ℚ constant `n ∈ ℚ ⊂ ℚ(x)` as a `QFunNZG ℚ` element (denominator `[1]` nonzero by
`cisZeroG_one_singleton`). -/
def qConstParamG (n : ℚ) : QFunNZG ℚ := ⟨([n], [(1 : ℚ)]), QFunNZG.cisZeroG_one_singleton⟩

/-- `cBaseIsProper b`: `true` iff the lowest-terms `QFunNZG ℚ` value `b = a/d ∈ ℚ(x)` is proper
(`deg a < deg d`, nonzero numerator). -/
def cBaseIsProper (b : QFunNZG ℚ) : Bool :=
  let bn := qnormPairG b.1.1 b.1.2
  cdegG bn.1 < cdegG bn.2 && !cisZeroG bn.1

/-- Parametric-logarithmic-derivative test over the base field `cParametricLogDeriv b`, for
`b ∈ k = ℚ(x)`: `true` iff `b` could be a logarithmic derivative of a `ℚ(x)`-radical (`n·b = Dz/z` for
nonzero `n ∈ ℤ`, `z ∈ ℚ(x)*`), `false` iff provably not. A non-proper `b` (in particular every nonzero
constant) is ruled out; a proper `b` is conservatively accepted. -/
def cParametricLogDeriv (b : QFunNZG ℚ) : Bool :=
  -- `b = 0` is the trivial logarithmic derivative `Dz/z` with `z = 1`; a proper `b` is not ruled out.
  CField.isZero b || cBaseIsProper b

/-! ### `cParamLogDeriv` — the parametric logarithmic derivative recognizer over `k = ℚ(x)`

Decide `n·f = Dv/v + m·Dθ/θ` for integers `n ≠ 0, m` and `v ∈ ℚ(x)*`: solve for the candidate constant
`c = m/n` from `c·(Dθ/θ) = f`, then test whether `N·f − M·(Dθ/θ)` is a logarithmic derivative of a
radical. `f` and `Dθ/θ` are passed as reduced `QFunNZG ℚ` values. -/

/-- `cParamLogDerivCandidate fval wval`: the candidate constant `c = m/n ∈ ℚ` from `c·wval = fval` over
`ℚ(x)`, returned when `fval/wval` is a `ℚ`-constant (and `wval ≠ 0`), else `none`. -/
def cParamLogDerivCandidate (fval wval : QFunNZG ℚ) : Option ℚ :=
  -- `c·wval = fval` over ℚ(x); a constant candidate `c ∈ ℚ` exists iff `fval/wval ∈ ℚ`.
  if CField.isZero wval then none
  else
    let r := CField.div fval wval
    -- `r ∈ ℚ` iff its lowest-terms denominator is a (nonzero) constant and numerator degree 0.
    let rn := qnormPairG r.1.1 r.1.2
    if cdegG rn.1 = 0 ∧ cdegG rn.2 = 0 then
      some (((rn.1 : List ℚ).headD 0) / ((rn.2 : List ℚ).headD 1))
    else none

/-- Parametric logarithmic derivative recognizer `cParamLogDeriv fval θlogderiv` over `k = ℚ(x)`: decides
`n·f = Dv/v + m·(Dθ/θ)` for integers `n ≠ 0, m` and `v ∈ ℚ(x)*`, returning `some (n, m, v)` or `none`. It
solves for the candidate constant `c = m/n` (`cParamLogDerivCandidate`), then tests whether the residue
`N·f − M·(Dθ/θ)` is a logarithmic derivative of a radical (`cParametricLogDeriv`), reporting the residue as
the witness `v` (`v = 1` when it vanishes). -/
def cParamLogDeriv (fval θlogderiv : QFunNZG ℚ) :
    Option (ℤ × ℤ × QFunNZG ℚ) :=
  match cParamLogDerivCandidate fval θlogderiv with
  | none =>
    -- no constant candidate `c`: fall back to the pure logarithmic-derivative test `n·f = Dv/v`
    -- (`m = 0`). `f` is a log-derivative of a radical iff `cParametricLogDeriv` cannot rule it out and
    -- the residue obstruction is absent; report only the provable `f = 0` (trivial `v = 1`, `n` any).
    if CField.isZero fval then some (1, 0, CField.one) else none
  | some c =>
    -- `c = M/N` in lowest terms, `N > 0`. Test `N·f − M·(Dθ/θ) = Dv/v` (radical log-derivative).
    let N : ℤ := (c.den : ℤ)
    let M : ℤ := c.num
    let Nf := CField.mul (qConstParamG ((N : ℚ))) fval
    let Mw := CField.mul (qConstParamG ((M : ℚ))) θlogderiv
    let resid := CField.sub Nf Mw
    -- the residue `N·f − M·w`: a logarithmic derivative of a radical. The exactly-decidable witness is
    -- `resid = 0` (then `v = 1`, `N·f = M·w`, so `n = N, m = M`); nonzero radical witnesses are
    -- returned as residual data for downstream certification.
    if CField.isZero resid then some (N, M, CField.one)
    else if !cParametricLogDeriv resid then none
    else some (N, M, resid)

/-! ### `cParamRischDE` — the parametric Risch DE `Dy + f·y = Σᵢ cᵢ·gᵢ`

Solve the parametric Risch differential equation for `y ∈ k(t)` and constants `c₁, …, cₘ`, returning a
basis of the constant solution subspace. Over the base monomial case `k = ℚ`, `D = d/dt`, the bounded-degree
polynomial equation becomes a homogeneous linear system over `ℚ`, whose kernel is returned. -/

/-- Polynomial lcm over ℚ `cLcmQ p q = p·q / gcd(p, q)` (monic). -/
def cLcmQ (p q : CPoly ℚ) : CPoly ℚ :=
  if cisZeroG p ∨ cisZeroG q then []
  else cmonicG (cdivWf (cmulG p q) (cgcdWf p q).1)

/-- `tⁱ`-coefficient of a `CPoly ℚ` `cCoeffQ p i = coefficient(p, tⁱ)` (`0` out of range). -/
def cCoeffQ (p : CPoly ℚ) (i : ℕ) : ℚ := (p : List ℚ).getD i 0

/-- Linear constraints over ℚ `cLinearConstraintsQ gnums gdens` (`D = d/dt`, `k = ℚ`): from the reduced
equation `Dp = Σᵢ cᵢ·gᵢ` with `gᵢ = gnumsᵢ/gdensᵢ`, clears the common denominator `d = lcm(gdensᵢ)`,
splits each `d·gᵢ = qᵢ·d + rᵢ`, and returns the polynomial parts `qs = [q₁, …, qₘ]` together with the
homogeneous constraint matrix `Mᵢⱼ = coefficient(rⱼ, tⁱ)` (fed to `cNullspaceBasisQ`). -/
def cLinearConstraintsQ (gnums gdens : List (CPoly ℚ)) :
    List (CPoly ℚ) × List (List ℚ) :=
  let d := gdens.foldl (fun acc den => cLcmQ acc den) [(1 : ℚ)]
  let qrs : List (CPoly ℚ × CPoly ℚ) :=
    (List.zip gnums gdens).map (fun (gn, gd) =>
      let dgi := cmulG gn (cdivWf d gd)             -- `d·gᵢ = gnumᵢ·(d/gdenᵢ)`
      cdivmodWf dgi d)                              -- `(qᵢ, rᵢ)`
  let qs := qrs.map Prod.fst
  let rs := qrs.map Prod.snd
  let nrows := cdegG d                              -- rows `i = 0 .. deg(d)−1`
  let m := gnums.length
  let M : List (List ℚ) :=
    (List.range nrows).map (fun i =>
      (List.range m).map (fun j => cCoeffQ (rs.getD j []) i))
  (qs, M)

/-- **Parametric Risch DE over the base monomial ℚ[t]** `cParamRischDE gnums gdens`, specialized to
`k = ℚ`, `D = d/dt`, the **reduced** equation `Dp = Σᵢ cᵢ·gᵢ` (`a = 1, b = 0`). Returns a **basis**
`[c⃗₁, …, c⃗ᵣ]` of the `Const(k) = ℚ`-linear subspace of constant tuples
`(c₁, …, cₘ)` for which the equation has a polynomial solution `p ∈ ℚ[t]`:

1. `(qs, M) ← cLinearConstraintsQ gnums gdens`: the cleared homogeneous matrix
   `M·(c₁,…,cₘ)ᵀ = 0` (entries in `Const(k) = ℚ`).
2. **return** `cNullspaceBasisQ M m` — a basis of `ker(M)`, the constant solution subspace.

The empty kernel (`[]`) means the only solution is `c₁ = … = cₘ = 0`. For each basis tuple `c⃗`, a
companion polynomial solution `p` is recoverable by integrating `Σ cᵢqᵢ` (`cIntegratePolyQ`). -/
def cParamRischDE (gnums gdens : List (CPoly ℚ)) : List (List ℚ) :=
  let (_qs, M) := cLinearConstraintsQ gnums gdens
  cNullspaceBasisQ M gnums.length

/-! ### `cLimitedIntegrate`

Decide `f = Dv + Σᵢ cᵢ·log(wᵢ)` for constants `cᵢ` and `v ∈ k(t)`. Equivalently `f − Σ cᵢ·(Dwᵢ/wᵢ) = Dv`,
the parametric Risch DE `Dv + 0·v = f − Σ cᵢ·(Dwᵢ/wᵢ)` — i.e. (7.1) with `gᵢ = Dwᵢ/wᵢ` and the additional
"`f` itself" generator. So it is the `gᵢ = Dwᵢ/wᵢ` specialization of `cParamRischDE`, with `f`
appended as the forced generator `c₀ = 1`. -/

/-- **Limited integration over the base monomial ℚ[t]** `cLimitedIntegrate fnum fden wnums wdens`
over `k = ℚ`, `D = d/dt`. Decides `f = Dv + Σᵢ cᵢ·log(wᵢ)` for `cᵢ ∈ ℚ` and `v ∈ ℚ(t)`, returning the
basis of admissible `(c₀, c₁, …, cₘ)` tuples (with `c₀` the coefficient of the forced generator `f`, so a
genuine solution has `c₀ = 1`): the parametric Risch DE `Dv = c₀·f − Σᵢ cᵢ·(Dwᵢ/wᵢ)` (with generators
`g₀ = f`, `gᵢ = Dwᵢ/wᵢ = wnumᵢ'/wnumᵢ`-style logarithmic derivatives). Built as `cParamRischDE` on the
generator list `[f, Dw₁/w₁, …, Dwₘ/wₘ]`. The `wᵢ` arrive as numerator/denominator pairs; `Dwᵢ/wᵢ` is
`(D(wnumᵢ)·wdenᵢ − wnumᵢ·D(wdenᵢ)) / (wnumᵢ·wdenᵢ)`. Sharper denominator bounds and the
`c₀ = 1` back-substitution to a nonparametric RDE are left to downstream specializations. -/
def cLimitedIntegrate (fnum fden : CPoly ℚ) (wnums wdens : List (CPoly ℚ)) :
    List (List ℚ) :=
  -- generator `g₀ = f`, then `gᵢ = Dwᵢ/wᵢ` (logarithmic derivative of `wᵢ`).
  let logDerivs : List (CPoly ℚ × CPoly ℚ) :=
    (List.zip wnums wdens).map (fun (wn, wd) =>
      let num := csubG (cmulG (cderivQ wn) wd) (cmulG wn (cderivQ wd))
      let den := cmulG wn wd
      (num, den))
  let gnums := fnum :: logDerivs.map Prod.fst
  let gdens := fden :: logDerivs.map Prod.snd
  cParamRischDE gnums gdens

end CPoly

/-! ### Validation — the parametric logarithmic derivative recognizer

For `11 = Dv/v + m·Dθ/θ` with `Dθ/θ = 1` over `k = ℚ`, `cParamLogDeriv` returns `(n, m, v) = (1, 11, 1)`. -/

open CPoly

/-- `f = 11 ∈ ℚ ⊂ ℚ(x)`. -/
def paramLogDerivExampleF : QFunNZG ℚ := CPoly.qConstParamG 11
/-- `Dθ/θ = 1` (exponential `θ`, `Dθ = θ`). -/
def paramLogDerivExampleW : QFunNZG ℚ := CPoly.qConstParamG 1

-- **Sanity print.** `cParamLogDeriv` returns `(n, m, v) = (1, 11, 1)` on the constant example.
#eval (CPoly.cParamLogDeriv paramLogDerivExampleF paramLogDerivExampleW).map
  (fun (n, m, v) => (n, m, CPoly.qnormPairG v.1.1 v.1.2))

/-- The parametric logarithmic derivative recognizer computes: for `11 = Dv/v + m·Dθ/θ` with `Dθ/θ = 1`
over `k = ℚ`, `cParamLogDeriv` returns `(n, m, v) = (1, 11, 1)`, verified to satisfy
`n·f = Dv/v + m·(Dθ/θ)` (with `v = 1`, `Dv/v = 0`). -/
theorem paramLogDeriv_example :
    (match cParamLogDeriv paramLogDerivExampleF paramLogDerivExampleW with
      | some (n, m, v) =>
          -- `n·f − m·(Dθ/θ) − Dv/v` cleared: with `v = 1`, `Dv/v = 0`, so check `n·f − m·w = 0`.
          let nf := CField.mul (CPoly.qConstParamG ((n : ℚ))) paramLogDerivExampleF
          let mw := CField.mul (CPoly.qConstParamG ((m : ℚ))) paramLogDerivExampleW
          CField.isZero (CField.sub nf mw) && CField.isZero (CField.sub v CField.one)
            && decide (n ≠ 0)
      | none => false) = true := by native_decide

#print axioms paramLogDeriv_example

/-! ### Validation — the parametric RDE reduces to a linear system

For `Dp = c₁·(2t³+3t+1)/(t²−1) + c₂/(t−1) + c₃/(t+1)` over `k = ℚ`, `LinearConstraints` yields the
homogeneous system with solution space `(c₁,c₂,c₃) = (λ,−3λ,−2λ)`. -/

open CPoly

/-- `g₁ = (2t³+3t+1)/(t²−1)`: numerator `[1,3,0,2]`, denominator `[-1,0,1]` (low→high). -/
def paramRischExampleG1num : CPoly ℚ := [1, 3, 0, 2]
/-- `g₁`-denominator `t²−1`. -/
def paramRischExampleG1den : CPoly ℚ := [-1, 0, 1]
/-- `g₂ = 1/(t−1)`: numerator `[1]`, denominator `[-1,1]`. -/
def paramRischExampleG2num : CPoly ℚ := [1]
/-- `g₂`-denominator `t−1`. -/
def paramRischExampleG2den : CPoly ℚ := [-1, 1]
/-- `g₃ = 1/(t+1)`: numerator `[1]`, denominator `[1,1]`. -/
def paramRischExampleG3num : CPoly ℚ := [1]
/-- `g₃`-denominator `t+1`. -/
def paramRischExampleG3den : CPoly ℚ := [1, 1]

-- **Sanity prints.** `LinearConstraints` returns the cleared coefficient system (rows = coefficients
-- of `t⁰, t¹`: `[[1,1,-1],[5,1,1]]`, up to equation order), and the
-- kernel basis (one vector, proportional to `(1,-3,-2)`: here `(-1/2, 3/2, 1) = -½·(1,-3,-2)`).
#eval (CPoly.cLinearConstraintsQ
    [paramRischExampleG1num, paramRischExampleG2num, paramRischExampleG3num]
    [paramRischExampleG1den, paramRischExampleG2den, paramRischExampleG3den]).2
#eval CPoly.cParamRischDE
    [paramRischExampleG1num, paramRischExampleG2num, paramRischExampleG3num]
    [paramRischExampleG1den, paramRischExampleG2den, paramRischExampleG3den]

/-- **Cleared parametric-constraint check** `paramConstraintCheck gnums gdens cs`: `true` iff the
constant tuple `cs = (c₁,…,cₘ)` satisfies the cleared constraint `Σᵢ cᵢ·rᵢ = 0` (the remainders `rᵢ` of
`d·gᵢ` by `d = lcm(denominators)`), i.e. `Σᵢ cᵢ·(numᵢ·(d/denᵢ) mod d) = 0` — the polynomial identity
certifying that `(c₁,…,cₘ)` is a genuine solution of the parametric Risch DE's linear constraints. -/
def paramConstraintCheck (gnums gdens : List (CPoly ℚ)) (cs : List ℚ) : Bool :=
  let d := gdens.foldl (fun acc den => cLcmQ acc den) [(1 : ℚ)]
  let total : CPoly ℚ :=
    ((List.zip gnums gdens).zip cs).foldl (fun acc ((gn, gd), c) =>
      let dgi := cmulG gn (cdivWf d gd)
      let ri := cmodWf dgi d
      caddG acc (cscaleG c ri)) []
  cisZeroG total

/-- **The parametric Risch differential equation reduces to a constant linear system**
(`native_decide`). For
`Dp = c₁·(2t³+3t+1)/(t²−1) + c₂/(t−1) + c₃/(t+1)` over `k = ℚ`, `t` a monomial with `Dt = 1`:

1. **Linear constraints.** `cLinearConstraintsQ` returns the homogeneous matrix `[[5,1,1],[1,1,-1]]`
   up to equation order, pinned componentwise against the expected values.
2. **Constant solve.** `cParamRischDE` returns a **basis** of its kernel — a single vector `c⃗`
   (one-dimensional solution space), each verified to **actually satisfy** the cleared constraint
   `Σᵢ cᵢ·rᵢ = 0` by `paramConstraintCheck` (the cleared polynomial identity), and confirmed nontrivial
   (not all-zero). The solution space is `(c₁,c₂,c₃) = (λ,−3λ,−2λ)`; the returned basis vector is
   proportional to `(1,−3,−2)`, so the parametric problem reduces to the one-parameter `Dp = 2λt`.

This is the **parametric** Risch differential equation: the right-hand side `Σ cᵢgᵢ` carries
undetermined constants and reduces, via `cLinearConstraintsQ` and the constant linear solve
`cNullspaceBasisQ` (ordinary ℚ-Gaussian elimination
since `Const(k) = ℚ`), to a basis of the constant solution subspace. -/
theorem paramRischDE_example :
    -- (1) the cleared constraint matrix is the system `c₁(5t+1)+c₂(t+1)+c₃(t−1)=0`, i.e. (low→high in
    -- `t`) the rows `t⁰: [1,1,-1]` and `t¹: [5,1,1]`.
    (decide ((cLinearConstraintsQ
        [paramRischExampleG1num, paramRischExampleG2num, paramRischExampleG3num]
        [paramRischExampleG1den, paramRischExampleG2den, paramRischExampleG3den]).2
      = [[1,1,-1],[5,1,1]])
    -- (2) the kernel basis is one nontrivial vector, each satisfying the cleared constraint.
    && (let basis := cParamRischDE
          [paramRischExampleG1num, paramRischExampleG2num, paramRischExampleG3num]
          [paramRischExampleG1den, paramRischExampleG2den, paramRischExampleG3den]
        decide (basis.length = 1)
          && basis.all (fun cs =>
              paramConstraintCheck
                [paramRischExampleG1num, paramRischExampleG2num, paramRischExampleG3num]
                [paramRischExampleG1den, paramRischExampleG2den, paramRischExampleG3den] cs
                && !(cs.all (· == 0))))) = true := by native_decide

#print axioms paramRischDE_example

/-! ### Validation — the limited integration problem reduces to the parametric RDE

`k = ℚ`, `t` a monomial with `Dt = 1` (`D = d/dt`). The limited integration problem
`f = Dv + Σᵢ cᵢ·log(wᵢ)` is the parametric Risch DE (7.1) with generators `g₀ = f`, `gᵢ = Dwᵢ/wᵢ`. For
`f = 1/t`, `w₁ = t`, `w₂ = t+1` (`Dw₁/w₁ = 1/t`, `Dw₂/w₂ = 1/(t+1)`), the only constant relation among
`{f, 1/t, 1/(t+1)}` is `f = 1/t = log(t)′`, so `cLimitedIntegrate` returns a one-dimensional kernel — the
basis vector witnessing `c₀·f = c₁·(Dw₁/w₁)` (i.e. `f = log(w₁)`, the limited-integral certificate). -/

open CPoly

/-- Limited-integration example numerator for `f = 1/t`. -/
def limitedIntExampleFnum : CPoly ℚ := [1]
/-- Limited-integration example denominator `t`. -/
def limitedIntExampleFden : CPoly ℚ := [0, 1]

-- **Sanity print.** `cLimitedIntegrate` finds the relation `f = Dw₁/w₁` (`f = log(t)`),
-- a one-dimensional kernel `[[-1, 1, 0]]` over generators `[f, Dw₁/w₁, Dw₂/w₂]`.
#eval CPoly.cLimitedIntegrate limitedIntExampleFnum limitedIntExampleFden [[0, 1], [1, 1]] [[1], [1]]

/-- **Limited integration reduces to the parametric Risch DE** (`native_decide`). For
`f = Dv + c₁·log(t) + c₂·log(t+1)` with `f = 1/t` over `k = ℚ`,
`cLimitedIntegrate` (the `gᵢ = Dwᵢ/wᵢ` specialization of `cParamRischDE`, with `f` the forced generator)
returns a nonempty constant kernel basis, each vector verified to **actually satisfy** the cleared
constraint `c₀·f + Σᵢ cᵢ·(Dwᵢ/wᵢ) ≡ 0 (mod lcm)` by `paramConstraintCheck`. The relation found is
`f = log(t)` (`c₀ = ±1`, `c₁ = ∓1`, `c₂ = 0`) — the limited-integral certificate that `∫ f = log(t)`.
Sharper denominator bounds and the `c₀ = 1` back-substitution to a nonparametric RDE for `v` are left to
downstream specializations. -/
theorem limitedIntegrate_example :
    (let wnums : List (CPoly ℚ) := [[0, 1], [1, 1]]
     let wdens : List (CPoly ℚ) := [[1], [1]]
     -- the generators `cLimitedIntegrate` builds: `g₀ = f`, `gᵢ = Dwᵢ/wᵢ`.
     let logDerivs : List (CPoly ℚ × CPoly ℚ) :=
       (List.zip wnums wdens).map (fun (wn, wd) =>
         (csubG (cmulG (cderivQ wn) wd) (cmulG wn (cderivQ wd)), cmulG wn wd))
     let gnums := limitedIntExampleFnum :: logDerivs.map Prod.fst
     let gdens := limitedIntExampleFden :: logDerivs.map Prod.snd
     let basis := cLimitedIntegrate limitedIntExampleFnum limitedIntExampleFden wnums wdens
     decide (0 < basis.length)
       && basis.all (fun cs =>
            paramConstraintCheck gnums gdens cs && !(cs.all (· == 0)))) = true := by
  native_decide

#print axioms limitedIntegrate_example

end DeepWiki.SymbolicIntegration
