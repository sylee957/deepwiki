import DeepWiki.SymbolicIntegration.Compute.LogToAtan
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded

/-! # Computable bivariate subresultant gcd / log argument over `ℚ[t]`
The logarithmic part puts `S(t,x) = gcd_x(D(x), A(x) − t·D'(x))` inside the logarithms of
`∫ A/D = ∑_{R(a)=0} a·log(S(a,x))`. This bivariate `ℚ[t][x]` gcd is computed by the subresultant
polynomial-remainder sequence over the non-field ring `ℚ[t]`, on an executable carrier
`GBPolyCore ℚ := List (DensePoly ℚ)`. Agreement with the noncomputable `lrtSubresultant` is proven in
`SubresultantCorrectness`. -/

namespace DeepWiki.SymbolicIntegration

namespace Compute

/-! ### Reduction and inversion modulo a `ℚ[t]` factor `R(t)` (the residue ring `ℚ[t]/(R)`)
The degree-`j` subresultant reduced mod `R` and made monic in `x` over `ℚ[t]/(R)` is the normalized
log argument `S(t,x)`; the leading `x`-coefficient is a unit there, so monic normalization is exact
via the extended-Euclidean inverse. -/

/-- Reduce every `x`-coefficient of a `GBPolyCore ℚ` modulo `R`: `bredR R p`, the image of `p` in
`(ℚ[t]/(R))[x]`. -/
def bredR (R : DensePoly ℚ) (p : GBPolyCore ℚ) : GBPolyCore ℚ :=
  GBPolyCore.gbnormCore (p.map (fun c => DensePoly.cmodWf c R))

/-- Inverse of a `DensePoly ℚ` modulo `R`: `cinvMod R c = c⁻¹` in `ℚ[t]/(R)` (assumes `c` a unit mod
`R`), via `c⁻¹ ≡ s/g (mod R)` from the Bézout relation `s·c + ·R = g`. -/
def cinvMod (R c : DensePoly ℚ) : DensePoly ℚ :=
  let (g, s, _) := DensePoly.cgcdWf c R
  DensePoly.cmodWf (cscale (clead g)⁻¹ s) R

/-- Make a `GBPolyCore ℚ` monic in `x` over `ℚ[t]/(R)`: `bmonicXmodR R p` reduces mod `R` and scales by
the mod-`R` inverse of the leading `x`-coefficient. -/
def bmonicXmodR (R : DensePoly ℚ) (p : GBPolyCore ℚ) : GBPolyCore ℚ :=
  let p := bredR R p
  if GBPolyCore.gbisZeroCore p then []
  else
    let inv := cinvMod R (GBPolyCore.gblcCore p)
    GBPolyCore.gbnormCore (p.map (fun c => DensePoly.cmodWf (cmul c inv) R))

/-! ### Exact `ℚ[t]`-division of a `GBPolyCore ℚ` by a `DensePoly ℚ` -/

/-- Exact `ℚ[t]`-scalar division `bdivC p c = p / c`: divide every `x`-coefficient of `p` by the
`DensePoly ℚ` scalar `c`. -/
def bdivC (p : GBPolyCore ℚ) (c : DensePoly ℚ) : GBPolyCore ℚ :=
  GBPolyCore.gbnormCore (p.map (fun a => DensePoly.cdivWf a c))

/-! ### The subresultant PRS (Collins–Brown)
The subresultant polynomial-remainder sequence computes the whole gcd chain with exact `ℚ[t]`
divisions that strip the pseudo-remainder `lc`-power inflation, so the degree-`j` element is the true
subresultant. -/

/-- Subresultant polynomial-remainder sequence `subresPRS fuel P Q = [R₁, R₂, …]` with `R₁ = P`,
`R₂ = Q`; the degree-`j` element is the `j`-th subresultant up to sign. Fuel-bounded. -/
def subresPRS (fuel : ℕ) (P Q : GBPolyCore ℚ) : List (GBPolyCore ℚ) :=
  -- `go Ri_1 Ri psi delta_prev fuelOuter`: `delta_prev = δ` of the step that produced `Ri` from `Ri_1`.
  let rec go : ℕ → GBPolyCore ℚ → GBPolyCore ℚ → DensePoly ℚ → ℕ → List (GBPolyCore ℚ)
    | 0, _, _, _, _ => []
    | fo + 1, Ri_1, Ri, psi, deltaPrev =>
      if GBPolyCore.gbisZeroCore Ri then []
      else
        let lcRi_1 : DensePoly ℚ := GBPolyCore.gblcCore Ri_1
        -- update ψ: ψ' = (−lc Ri_1)^δ / ψ^{δ−1}  (δ = deltaPrev ≥ 1)
        let negLc : DensePoly ℚ := cneg lcRi_1
        let psi' : DensePoly ℚ :=
          if deltaPrev = 0 then psi
          else DensePoly.cdivWf (DensePoly.cpow negLc deltaPrev)
            (DensePoly.cpow psi (deltaPrev - 1))
        -- β = −lc(Ri_1) · ψ'^δ
        let beta : DensePoly ℚ := cmul negLc (DensePoly.cpow psi' deltaPrev)
        let pr : GBPolyCore ℚ := GBPolyCore.gbpsremainderCore fuel Ri_1 Ri
        let Ri1 : GBPolyCore ℚ := bdivC pr beta
        let deltaNew : ℕ := GBPolyCore.gbdegCore Ri - GBPolyCore.gbdegCore Ri1
        Ri :: go fo Ri Ri1 psi' deltaNew
  P :: go fuel P Q [-1] (GBPolyCore.gbdegCore P - GBPolyCore.gbdegCore Q)

/-- The subresultant at `x`-degree `j` `bsubresultantGcd fuel j P Q`: the element of `subresPRS`
whose `x`-degree is `j` (the subresultant `Sⱼ` up to sign), or `[]` if none. -/
def bsubresultantGcd (fuel : ℕ) (j : ℕ) (P Q : GBPolyCore ℚ) : GBPolyCore ℚ :=
  ((subresPRS fuel P Q).filter (fun R => decide (GBPolyCore.gbdegCore R = j ∧ ¬ GBPolyCore.gbisZeroCore R))).getLast?.getD []

/-! ### Lifting `ℚ[x]` (a `DensePoly ℚ`) into `GBPolyCore ℚ`, and building `A − t·D'` -/

/-- Lift a `DensePoly ℚ` (`= ℚ[x]`) into `GBPolyCore ℚ`: `liftCtoBPoly p` makes each `x`-coefficient `aᵢ` the
constant `ℚ[t]` polynomial `[aᵢ]`. -/
def liftCtoBPoly (p : DensePoly ℚ) : GBPolyCore ℚ := p.map (fun c => cnorm [c])

/-- The variable `t` as a `DensePoly ℚ`: `ctVar = [0, 1]`. -/
def ctVar : DensePoly ℚ := [0, 1]

/-- The log argument's second operand `bArgAmtD' A D = A − t·D'` as a `GBPolyCore ℚ`: `A` lifted with
constant `t`-coefficients, minus `t · D'`. -/
def bArgAmtD' (A D : DensePoly ℚ) : GBPolyCore ℚ :=
  DensePoly.csub (liftCtoBPoly A)
    (DensePoly.cscale ctVar (liftCtoBPoly (cderiv D)))

/-- The raw degree-`j` subresultant `lrtSubresultantCompute fuel j A D = Sⱼ(D, A − t·D')`: the
bivariate subresultant of `D` (lifted) and `A − t·D'` at `x`-degree `j`, `ℚ[t]`-primitive in `x`. -/
def lrtSubresultantCompute (fuel : ℕ) (j : ℕ) (A D : DensePoly ℚ) : GBPolyCore ℚ :=
  GBPolyCore.gbprimitivePartCore DensePoly.cgcdWfGcd
    (bsubresultantGcd fuel j (liftCtoBPoly D) (bArgAmtD' A D))

/-- The computable log argument `lrtGcdCompute fuel j R A D = S(t,x)`: the degree-`j` subresultant
reduced modulo `R(t)` and made monic in `x` over `ℚ[t]/(R)`, the `S(t,x)` inside the logarithms of
`∫ A/D = ∑_{R(a)=0} a·log(S(a,x))`. -/
def lrtGcdCompute (fuel : ℕ) (j : ℕ) (R A D : DensePoly ℚ) : GBPolyCore ℚ :=
  bmonicXmodR R (lrtSubresultantCompute fuel j A D)

/-! ### Logarithmic-part assembly -/

/-- Logarithmic part of `∫A/D`: `lrtLogPart fuel A D` returns the `(Qᵢ, Sᵢ)` pairs meaning
`∫A/D = ∑ᵢ ∑_{Qᵢ(a)=0} a·log(Sᵢ(a,x))`, for squarefree `D`. -/
def lrtLogPart (fuel : ℕ) (A D : DensePoly ℚ) : List (DensePoly ℚ × GBPolyCore ℚ) :=
  let R := DensePoly.cResidueResultantTower ([1] : DensePoly ℚ) A D
  (DensePoly.cSqfreeYunFactors R).map (fun (Qi, i) => (Qi, lrtGcdCompute fuel i Qi A D))


end Compute

end DeepWiki.SymbolicIntegration
