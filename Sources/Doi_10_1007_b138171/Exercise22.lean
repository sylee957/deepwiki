import DeepWiki.SymbolicIntegration.Compute.Subresultant
import DeepWiki.SymbolicIntegration.Compute.Subresultant

/-! # Computing Bronstein Exercise 2.2 with the executable LRT engine (§2.9, p.72)
**Exercise 2.2** asks to compute, by the Lazard–Rioboo–Trager algorithm,
`∫ A/D dx` with
`A = 8x⁹+x⁸−12x⁷−4x⁶−26x⁵−6x⁴+30x³+23x²−2x−7`,
`D = x¹⁰−2x⁸−2x⁷−4x⁶+7x⁴+10x³+3x²−4x−2`.
We run the computable engine of `LogToAtanCompute`/`RtResultantCompute`/`SubresultantCompute`
end to end and `native_decide`-pin every step:

* **`D` is squarefree** (`gcd(D, D')` is constant), so NO Hermite reduction is needed —
  `∫A/D` is purely the LRT logarithmic part.
* The Rothstein–Trager resultant `R(t) = res_x(D, A − t·D')` is the **degree-10** integer
  polynomial `cR22` below, and it is itself **squarefree** — so it has a *single* squarefree
  factor `R` of multiplicity `1` (Yun factorization is trivial: `[(R, 1)]`); all ten residues
  are distinct of multiplicity one.
* Hence the LRT subresultant index is `j = 1` and the per-residue gcd `gcd(D, A − a·D')` is
  **linear in `x`**: the engine's `S₁(t,x) = lrtGcdCompute fuel 1 R A D` comes out monic in `x`,
  `S₁(t,x) = x + c₀(t)` with `c₀(t) ∈ ℚ[t]/(R)` a degree-`9` residue polynomial (`#eval`ed below).

So the computed answer is
`∫ A/D = ∑_{R(a)=0} a · log(x + c₀(a))`,
with `R` the degree-10 RT resultant and `c₀` the residue polynomial — the LRT log part, computed.
A small Yun `csqfreeFactor` is provided for the general assembly (`lrtLogPart`); for Exercise 2.2
it returns the single pair `(R, 1)`. -/

namespace DeepWiki.SymbolicIntegration

namespace Compute

/-! ### The Exercise 2.2 integrand `A/D` -/

/-- **`A = 8x⁹+x⁸−12x⁷−4x⁶−26x⁵−6x⁴+30x³+23x²−2x−7`** as a `DensePoly ℚ` (Exercise 2.2 numerator),
coefficients low→high. -/
def cA22 : DensePoly ℚ := [-7, -2, 23, 30, -6, -26, -4, -12, 1, 8]

/-- **`D = x¹⁰−2x⁸−2x⁷−4x⁶+7x⁴+10x³+3x²−4x−2`** as a `DensePoly ℚ` (Exercise 2.2 denominator),
coefficients low→high. -/
def cD22 : DensePoly ℚ := [-2, -4, 3, 10, 7, 0, -4, -2, 0, -2, 1]

/-! ### `D` is squarefree — no Hermite reduction, pure LRT log part -/

/-- **Exercise 2.2: `D` is squarefree** — the monic `gcd(D, D')` is `1`, so `D` has no repeated
factor and `∫A/D` is purely the LRT logarithmic part (no Hermite/rational part). Proved by
`native_decide`. -/
theorem ex_2_2_D_squarefree :
    cmonic (DensePoly.cgcdWf cD22 (cderiv cD22)).1 = [1] := by native_decide

/-! ### The Rothstein–Trager resultant `R(t)` and its squarefree factorization -/

/-- **The Rothstein–Trager resultant `R(t) = res_x(D, A − t·D')`** of Exercise 2.2 as a `DensePoly ℚ`
(degree 10, integer coefficients) — the polynomial whose roots are the residues of `A/D`. -/
def cR22 : DensePoly ℚ :=
  [148964442861521664, -1328822210596308992, 3776846888776593920, -4127327364012019200,
   3496864403205884928, -3396064845300158976, 3917651441502789888, -3496048353394587648,
   1973139744286936320, -665922498162245632, 83240312270280704]

/-- **Exercise 2.2: the engine computes `R(t) = cR22`** — `rtResultantCompute` on `A, D` returns the
degree-10 integer resultant `cR22`. Proved by `native_decide`. -/
theorem ex_2_2_resultant : rtResultantCompute 60 cA22 cD22 = cR22 := by native_decide

/-- **Exercise 2.2: `R(t)` is squarefree** — its Yun factorization is the single pair `(monic R, 1)`,
i.e. one squarefree factor of multiplicity one (all ten residues distinct). So no nontrivial
multiplicity splitting is needed; the LRT subresultant index is `j = 1`. Proved by `native_decide`. -/
theorem ex_2_2_resultant_squarefree :
    csqfreeFactor 60 cR22 = [(cmonic cR22, 1)] := by native_decide

/-! ### The LRT log argument `S₁(t,x)` and the assembled answer -/

/-- **The LRT log argument** `S₁(t,x) = lrtGcdCompute 60 1 (monic R) A D` for Exercise 2.2: the
degree-1 (in `x`) per-residue gcd, monic in `x`, reduced over `ℚ[t]/(R)`. It has the shape
`x + c₀(t)` with `c₀(t)` a degree-9 residue polynomial (`#eval`ed below). -/
def cS1_22 : BPoly := lrtGcdCompute 60 1 (cmonic cR22) cA22 cD22

/-- **Exercise 2.2: `S₁` is monic and linear in `x`** — `S₁(t,x) = x + c₀(t)`: it has `x`-degree `1`
(two `x`-coefficients) with leading `x`-coefficient `1`. So each residue gcd `gcd(D, A − a·D')` is
linear, as expected for a squarefree degree-10 `D` with distinct residues. Proved by `native_decide`. -/
theorem ex_2_2_S1_monic_linear :
    cS1_22.length = 2 ∧ blc cS1_22 = [1] := by native_decide

-- **Exercise 2.2, the assembled answer** `∫A/D = ∑_{R(a)=0} a·log(x + c₀(a))`: the single
-- `(Q₁, S₁) = (monic R, x + c₀(t))` pair. The `#eval` prints `c₀(t)` (a degree-9 polynomial in `t`,
-- the residues of `A/D` expressed mod `R`); the leading `x`-coefficient is `[1]` (monic in `x`).
#eval lrtLogPart 60 cA22 cD22

/-- **Exercise 2.2, the computed LRT logarithmic part** (§2.9, p.72): the full assembly
`lrtLogPart 60 A D` reduces to the **single** `(Qᵢ, Sᵢ)` pair `(monic R, S₁)`, where `R = cR22` is the
degree-10 Rothstein–Trager resultant (squarefree, multiplicity 1) and
`S₁ = lrtGcdCompute 60 1 (monic R) A D = x + c₀(t)` is the monic-in-`x` log argument. This **is** the
exercise's answer:
`∫ A/D = ∑_{R(a)=0} a · log(x + c₀(a))`,
with `c₀(t)` the degree-9 residue polynomial of `cS1_22` (`#eval`ed above). The proved computation is
the answer — `native_decide` runs the whole LRT pipeline (RT resultant, Yun factorization, subresultant
PRS, mod-`R` monic normalization) and pins the result. -/
theorem ex_2_2_logpart :
    lrtLogPart 60 cA22 cD22 = [(cmonic cR22, cS1_22)] := by native_decide

end Compute

end DeepWiki.SymbolicIntegration
