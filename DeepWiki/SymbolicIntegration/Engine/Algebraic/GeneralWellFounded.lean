import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralQuotient
import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralSetup
import DeepWiki.SymbolicIntegration.Engine.FuelFreeDiophantine

/-! # General algebraic-function integration

The integrator for a plane curve `K(x)[y]/(f)`: the rational part `v` and log
argument `u` are found by `K`-linear solves over the integral basis, with the
Bézout cofactor `f_y⁻¹ mod f` supplied by `afFyInvWf`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open DensePoly

namespace DensePoly

variable {α : Type*} [CField α]

/-! ## The general derivation `afDerivWf`

`CPoly.reduceMod`/`CPoly.mulMod` already carry a self-computed bound; the one recursive dependency, `f_y⁻¹ mod f`, is
computed by the well-founded `CPoly.diophantineReduced`. -/

/-- `f_y⁻¹ mod f` — `afFyInvWf f = (CPoly.diophantineReduced (cderiv f) f [1]).1`, the first Bézout cofactor `s` of
`s·f_y + t·f = 1`. The inverse of `∂f/∂y` in `K(x)[y]/(f)` (valid for separable `f`), degree `< deg f`. -/
def afFyInvWf (f : DensePoly α) : DensePoly α :=
  (CPoly.diophantineReduced (cderiv f) f [CCommRing.one]).1

variable [CDiffField α]

/-- The implicit derivative `afYprimeWf f = CPoly.reduceMod f (−f_x · afFyInvWf f)`:
`y' = −(∂f/∂x)·(∂f/∂y)⁻¹ mod f`. -/
def afYprimeWf (f : DensePoly α) : DensePoly α :=
  CPoly.reduceMod f (cmul (cneg (afFx f)) (afFyInvWf f))

/-- The general derivation `afDerivWf f u = CPoly.reduceMod f (u.map cderiv + cderiv u · afYprimeWf f)`: the
product rule `D(u) = Σᵢ aᵢ'·yⁱ + (Σᵢ aᵢ·i·yⁱ⁻¹)·y'`. `[CField α] [CDiffField α]`-generic. -/
def afDerivWf (f u : DensePoly α) : DensePoly α :=
  CPoly.reduceMod f (cadd (CPolyEngine.mapDeriv u) (cmul (cderiv u) (afYprimeWf f)))

section WfInvariant

variable [CFieldSpec α] [CDiffFieldSpec α]

/-! ### The Wf derivation invariant

The shared quotient API lives in `ComputableGeneralQuotient`; separability is phrased as the gcd
the selected extended gcd of `cderiv f` and `f` being a nonzero constant. -/

omit [CFieldSpec α] [CDiffFieldSpec α] in
/-- `afDerivWf = CPoly.reduceMod f ∘ CPolyEngine.monomialDeriv (afYprimeWf f)` definitionally. -/
theorem afDerivWf_eq_reduceMod_cmonomialDeriv (f u : DensePoly α) :
    afDerivWf f u = CPoly.reduceMod f (CPolyEngine.monomialDeriv (afYprimeWf f) u) := rfl

/-- The Wf keystone: `afDerivWf` realizes `implicitDeriv (toPoly (afYprimeWf f))` in the quotient. -/
theorem mk_toPolyG_afDerivWf (f u : DensePoly α) (hf : cnorm f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f u))
      = Ideal.Quotient.mk (afIdeal f)
          (Differential.implicitDeriv (toPoly (afYprimeWf f)) (toPoly u)) := by
  rw [afDerivWf_eq_reduceMod_cmonomialDeriv, mk_toPoly_reduceMod f _ hf]
  simp only [denote]

/-- `afDerivWf` is additive modulo the curve ideal. -/
theorem mk_toPolyG_afDerivWf_add (f a b : DensePoly α) (hf : cnorm f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f (cadd a b)))
      = Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f a))
        + Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f b)) := by
  rw [mk_toPolyG_afDerivWf f _ hf, mk_toPolyG_afDerivWf f a hf,
    mk_toPolyG_afDerivWf f b hf]
  simp only [denote, map_add]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- Bézout inverse of `f_y` in the quotient. -/
theorem mk_toPolyG_afFyInvWf_mul_afFy (f : DensePoly α) (hf : cnorm f ≠ [])
    (hgdeg : (toPoly (CPolyEuclidean.gcdExt (cderiv f) f).1).natDegree = 0)
    (hgne : toPoly (CPolyEuclidean.gcdExt (cderiv f) f).1 ≠ 0) :
    Ideal.Quotient.mk (afIdeal f)
        (toPoly (afFyInvWf f) * toPoly (cderiv f)) = 1 := by
  have hbez := toPolyG_diophantineReduced (cderiv f) f [CCommRing.one] hf hgdeg hgne
  have hone : toPoly ([CCommRing.one] : DensePoly α) = 1 := by
    simp only [denote]
    simp
  rw [hone] at hbez
  rw [show toPoly (afFyInvWf f) * toPoly (cderiv f)
      = 1 - toPoly (CPoly.diophantineReduced (cderiv f) f [CCommRing.one]).2 * toPoly f from by
        rw [afFyInvWf]; linear_combination hbez]
  have hmem : Ideal.Quotient.mk (afIdeal f)
      (toPoly (CPoly.diophantineReduced (cderiv f) f [CCommRing.one]).2 * toPoly f) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (mul_curve_mem f _)
  rw [map_sub, hmem, map_one, sub_zero]

/-- The implicit derivation kills the curve generator modulo its ideal. -/
theorem implicitDerivWf_curve_mem (f : DensePoly α) (hf : cnorm f ≠ [])
    (hgdeg : (toPoly (CPolyEuclidean.gcdExt (cderiv f) f).1).natDegree = 0)
    (hgne : toPoly (CPolyEuclidean.gcdExt (cderiv f) f).1 ≠ 0) :
    Differential.implicitDeriv (toPoly (afYprimeWf f)) (toPoly f) ∈ afIdeal f := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [show Differential.implicitDeriv (toPoly (afYprimeWf f)) (toPoly f)
      = Differential.mapCoeffs (toPoly f)
        + toPoly (afYprimeWf f) * Polynomial.derivative (toPoly f) from by
        simp [Differential.implicitDeriv, derivative']]
  rw [mapCoeffs_toPolyG_eq_afFx, ← toPolyG_cderivG]
  have hyp : Ideal.Quotient.mk (afIdeal f) (toPoly (afYprimeWf f))
      = Ideal.Quotient.mk (afIdeal f) (- toPoly (afFx f) * toPoly (afFyInvWf f)) := by
    rw [afYprimeWf, mk_toPoly_reduceMod f _ hf]
    simp only [denote, map_mul, map_neg]
  rw [map_add, map_mul, hyp, ← map_mul]
  have hfyinv := mk_toPolyG_afFyInvWf_mul_afFy f hf hgdeg hgne
  rw [show - toPoly (afFx f) * toPoly (afFyInvWf f) * toPoly (cderiv f)
      = - (toPoly (afFx f) * (toPoly (afFyInvWf f) * toPoly (cderiv f))) from by ring,
    map_neg, map_mul, hfyinv, mul_one, add_neg_cancel]

/-- The implicit derivation maps `afIdeal f` into itself. -/
theorem implicitDerivWf_mem_afIdeal (f : DensePoly α) (hf : cnorm f ≠ [])
    (hgdeg : (toPoly (CPolyEuclidean.gcdExt (cderiv f) f).1).natDegree = 0)
    (hgne : toPoly (CPolyEuclidean.gcdExt (cderiv f) f).1 ≠ 0)
    {x : (CFieldSpec.K α)[X]} (hx : x ∈ afIdeal f) :
    Differential.implicitDeriv (toPoly (afYprimeWf f)) x ∈ afIdeal f := by
  rw [afIdeal, Ideal.mem_span_singleton'] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_right _ _ ?_)
  · exact implicitDerivWf_curve_mem f hf hgdeg hgne
  · exact Ideal.subset_span (Set.mem_singleton _)

/-- The implicit derivation descends to the quotient by `afIdeal f`. -/
theorem mk_implicitDerivWf_congr (f : DensePoly α) (hf : cnorm f ≠ [])
    (hgdeg : (toPoly (CPolyEuclidean.gcdExt (cderiv f) f).1).natDegree = 0)
    (hgne : toPoly (CPolyEuclidean.gcdExt (cderiv f) f).1 ≠ 0)
    {p q : (CFieldSpec.K α)[X]}
    (hpq : Ideal.Quotient.mk (afIdeal f) p = Ideal.Quotient.mk (afIdeal f) q) :
    Ideal.Quotient.mk (afIdeal f)
        (Differential.implicitDeriv (toPoly (afYprimeWf f)) p)
      = Ideal.Quotient.mk (afIdeal f)
        (Differential.implicitDeriv (toPoly (afYprimeWf f)) q) := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  apply implicitDerivWf_mem_afIdeal f hf hgdeg hgne
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hpq, sub_self]

/-- `afDerivWf` is Leibniz modulo the curve ideal. -/
theorem mk_toPoly_afDerivWf_mulMod (f a b : DensePoly α) (hf : cnorm f ≠ [])
    (hgdeg : (toPoly (CPolyEuclidean.gcdExt (cderiv f) f).1).natDegree = 0)
    (hgne : toPoly (CPolyEuclidean.gcdExt (cderiv f) f).1 ≠ 0) :
    Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f (CPoly.mulMod f a b)))
      = Ideal.Quotient.mk (afIdeal f) (toPoly (CPoly.mulMod f (afDerivWf f a) b))
        + Ideal.Quotient.mk (afIdeal f) (toPoly (CPoly.mulMod f a (afDerivWf f b))) := by
  set yp := toPoly (afYprimeWf f) with hyp
  set A := toPoly a with hA
  set B := toPoly b with hB
  rw [mk_toPolyG_afDerivWf f _ hf, ← hyp]
  rw [mk_implicitDerivWf_congr f hf hgdeg hgne (mk_toPoly_mulMod f a b hf)]
  rw [mk_toPoly_mulMod _ _ _ hf, mk_toPoly_mulMod _ _ _ hf, mk_toPolyG_afDerivWf f a hf,
    mk_toPolyG_afDerivWf f b hf, ← hyp, ← hA, ← hB]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
  ring

/-- `afDerivWf` kills `1` modulo the curve ideal. -/
theorem mk_toPolyG_afDerivWf_one (f : DensePoly α) (hf : cnorm f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f [CCommRing.one])) = 0 := by
  rw [mk_toPolyG_afDerivWf f _ hf]
  have h1 : toPoly ([CCommRing.one] : DensePoly α) = 1 := by
    simp only [denote]
    simp
  rw [h1, Derivation.map_one_eq_zero, map_zero]

omit [CDiffFieldSpec α] in
/-- The `afDerivWf` round-trip certificate is the free-polynomial integrand identity. -/
theorem toPolyG_afDerivWf_eq_of_roundtrip (f v g : DensePoly α)
    (hcheck : cisZero (csub (afDerivWf f v) g) = true) :
    toPoly (afDerivWf f v) = toPoly g := by
  simpa [cisZeroG_iff, sub_eq_zero] using hcheck

end WfInvariant

end DensePoly

/-! ## The flat rational and log-argument solvers

Build a `ℚ`-matrix from `afDerivWf` and solve it with `CLinearSolve.nullspaceBasis`; specialized to
`DenseFrac ℚ`. -/

/-- Rational-part residual columns `afRatColumnsWf f basis degBound integrand`: the per-monomial
derivatives `afDerivWf f (xʲ wᵢ)` followed by the forced `−integrand` column. -/
def afRatColumnsWf (f : DensePoly (DenseFrac ℚ)) (basis : List (DensePoly (DenseFrac ℚ)))
    (degBound : ℕ) (integrand : DensePoly (DenseFrac ℚ)) : List (DensePoly (DenseFrac ℚ)) :=
  (afRatMonomials basis degBound).map (afDerivWf f) ++ [cneg integrand]

/-- `ℚ`-matrix of the rational-part system `afRatMatrixWf f basis degBound integrand`: clear each `K(x)`
coordinate of `afRatColumnsWf` to numerators over a common denominator, read off `x`-power coefficients. -/
def afRatMatrixWf (f : DensePoly (DenseFrac ℚ)) (basis : List (DensePoly (DenseFrac ℚ)))
    (degBound : ℕ) (integrand : DensePoly (DenseFrac ℚ)) : List (List ℚ) × ℕ :=
  let cols := afRatColumnsWf f basis degBound integrand
  let nCols := cols.length
  let n := cdeg f
  let rowsForCoord : ℕ → List (List ℚ) := fun i =>
    let entryOf : ℕ → DenseFrac ℚ := fun k => (cols[k]!).getD i CCommRing.zero
    let nums : List (DensePoly ℚ) :=
      (List.range nCols).map (fun k => cnorm (CFrac.num (entryOf k)))
    let dens : List (DensePoly ℚ) :=
      (List.range nCols).map (fun k => cnorm (CFrac.den (entryOf k)))
    let cleared : List (DensePoly ℚ) := (List.range nCols).map (fun k =>
      let prod := (List.range nCols).foldl (fun acc l =>
        if l = k then acc else cmul acc (dens[l]!)) [(1 : ℚ)]
      cnorm (cmul (nums[k]!) prod))
    let width := (cleared.foldl (fun acc p => max acc p.length) 0)
    (List.range width).map (fun r =>
      (List.range nCols).map (fun k => (cleared[k]!).getD r 0))
  let allRows := (List.range n).flatMap rowsForCoord
  let nonzero := allRows.filter (fun row => row.any (fun a => a ≠ 0))
  (nonzero, nCols)

/-- General rational-part solve `afRationalSolveWf f basis degBound integrand = some v`: the rational part
`v = Σ c_{ij} xʲ wᵢ` with `afDeriv f v = integrand`, by a `K`-linear solve over the integral basis (build
`afRatMatrixWf`, find a kernel vector with nonzero RHS coordinate, normalize, reassemble `v`). -/
def afRationalSolveWf [CLinearSolve ℚ]
    (f : DensePoly (DenseFrac ℚ)) (basis : List (DensePoly (DenseFrac ℚ)))
    (degBound : ℕ) (integrand : DensePoly (DenseFrac ℚ)) : Option (DensePoly (DenseFrac ℚ)) :=
  let (rows, nCols) := afRatMatrixWf f basis degBound integrand
  let kers := CLinearSolve.nullspaceBasis rows nCols
  match kers.find? (fun c => c.getD (nCols - 1) 0 ≠ 0) with
  | none => none
  | some c =>
    let rhs := c.getD (nCols - 1) 0
    let monos := afRatMonomials basis degBound
    let v : DensePoly (DenseFrac ℚ) :=
      (List.range monos.length).foldl (fun acc idx =>
        let coeff : ℚ := c.getD idx 0 / rhs
        cadd acc (cscale (CFrac.ofPoly [coeff]) (monos.getD idx []))) ([] : DensePoly (DenseFrac ℚ))
    some v

/-- Log-derivative residual `afLogResidualWf f integrand u = afDerivWf f u − CPoly.mulMod f u integrand`. -/
def afLogResidualWf (f integrand u : DensePoly (DenseFrac ℚ)) : DensePoly (DenseFrac ℚ) :=
  csub (afDerivWf f u) (CPoly.mulMod f u integrand)

/-- Log-argument residual columns `afLogColumnsWf f basis degBound integrand`: the per-monomial
log-derivative residuals `afLogResidualWf f integrand (xʲ wᵢ)` (no forced `−integrand` column — the log
system is homogeneous in `u`). -/
def afLogColumnsWf (f : DensePoly (DenseFrac ℚ)) (basis : List (DensePoly (DenseFrac ℚ)))
    (degBound : ℕ) (integrand : DensePoly (DenseFrac ℚ)) : List (DensePoly (DenseFrac ℚ)) :=
  (afRatMonomials basis degBound).map (afLogResidualWf f integrand)

/-- `ℚ`-matrix of the log-argument system `afLogMatrixWf f basis degBound integrand`: identical extraction
on the homogeneous columns `afLogColumnsWf`. -/
def afLogMatrixWf (f : DensePoly (DenseFrac ℚ)) (basis : List (DensePoly (DenseFrac ℚ)))
    (degBound : ℕ) (integrand : DensePoly (DenseFrac ℚ)) : List (List ℚ) × ℕ :=
  let cols := afLogColumnsWf f basis degBound integrand
  let nCols := cols.length
  let n := cdeg f
  let rowsForCoord : ℕ → List (List ℚ) := fun i =>
    let entryOf : ℕ → DenseFrac ℚ := fun k => (cols[k]!).getD i CCommRing.zero
    let nums : List (DensePoly ℚ) :=
      (List.range nCols).map (fun k => cnorm (CFrac.num (entryOf k)))
    let dens : List (DensePoly ℚ) :=
      (List.range nCols).map (fun k => cnorm (CFrac.den (entryOf k)))
    let cleared : List (DensePoly ℚ) := (List.range nCols).map (fun k =>
      let prod := (List.range nCols).foldl (fun acc l =>
        if l = k then acc else cmul acc (dens[l]!)) [(1 : ℚ)]
      cnorm (cmul (nums[k]!) prod))
    let width := (cleared.foldl (fun acc p => max acc p.length) 0)
    (List.range width).map (fun r =>
      (List.range nCols).map (fun k => (cleared[k]!).getD r 0))
  let allRows := (List.range n).flatMap rowsForCoord
  let nonzero := allRows.filter (fun row => row.any (fun a => a ≠ 0))
  (nonzero, nCols)

/-- General log-argument solve `afLogArgSolveWf f basis degBound integrand = some u`: the log argument
`u = Σ c_{ij} xʲ wᵢ` with `afDeriv f u = CPoly.mulMod f u integrand` (`∫ integrand = log u`), by the homogeneous
`K`-linear solve (build `afLogMatrixWf`, find the first nonzero kernel vector, reassemble `u`). -/
def afLogArgSolveWf [CLinearSolve ℚ]
    (f : DensePoly (DenseFrac ℚ)) (basis : List (DensePoly (DenseFrac ℚ)))
    (degBound : ℕ) (integrand : DensePoly (DenseFrac ℚ)) : Option (DensePoly (DenseFrac ℚ)) :=
  let (rows, nCols) := afLogMatrixWf f basis degBound integrand
  let kers := CLinearSolve.nullspaceBasis rows nCols
  match kers.find? (fun c => c.any (fun a => a ≠ 0)) with
  | none => none
  | some c =>
    let monos := afRatMonomials basis degBound
    let u : DensePoly (DenseFrac ℚ) :=
      (List.range monos.length).foldl (fun acc idx =>
        let coeff : ℚ := c.getD idx 0
        cadd acc (cscale (CFrac.ofPoly [coeff]) (monos.getD idx []))) ([] : DensePoly (DenseFrac ℚ))
    some u

/-! ## The top-level `afIntegrateAlgebraicWf` -/

/-- The general-curve integrator `afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand =
some (v, u)`: `∫ (ratIntegrand + logIntegrand) dx = v + log u` (principal case) — the rational part `v` by
`afRationalSolveWf` (`afDeriv f v = ratIntegrand`) and the log argument `u` by `afLogArgSolveWf`
(`afDeriv f u = CPoly.mulMod f u logIntegrand`), both `K`-linear solves through `afDerivWf`. `none` if either
solve fails. The general analogue of `cIntegrateAlgebraicWf`. -/
def afIntegrateAlgebraicWf [CLinearSolve ℚ]
    (f : DensePoly (DenseFrac ℚ)) (basis : List (DensePoly (DenseFrac ℚ)))
    (degBound : ℕ) (ratIntegrand logIntegrand : DensePoly (DenseFrac ℚ)) :
    Option (DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ)) :=
  match afRationalSolveWf f basis degBound ratIntegrand,
        afLogArgSolveWf f basis degBound logIntegrand with
  | some v, some u => some (v, u)
  | _, _ => none

/-! ## Cuspidal-cubic combined integral

`∫ (y + afDerivWf(y)/y) dx = (3/5)xy + log y` on `y³ = x²`, checked by `afDerivWf` (`native_decide`). -/

/-- The log-derivative input for the cuspidal-cubic combined validation. -/
def gcCombineLogIntegrandWf : DensePoly (DenseFrac ℚ) :=
  CPoly.mulMod gcuspCubicF (afDerivWf gcuspCubicF gcuspCubicY)
    [CCommRing.zero, CCommRing.zero, CFrac.ofFraction [1] [0, 0, 1] (by cfrac_nonzero)]

/-- The `afIntegrateAlgebraicWf` run for the cuspidal-cubic combined integral
`∫ (y + afDerivWf(y)/y) dx`. -/
def gcCombineSolvedWf : Option (DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ)) :=
  afIntegrateAlgebraicWf gcuspCubicF gcuspCubicBasis 2 gcuspCubicY gcCombineLogIntegrandWf

/-- The general-curve integrator integrates `∫ (y + afDeriv(y)/y) dx = (3/5)xy + log y`:
derives the rational part `v = (3/5)x·y` (`afDerivWf f v = y`) and the log argument `u` a nonzero multiple
of `y` (`afDerivWf f u = CPoly.mulMod f u logIntegrand`, `∫ afDeriv(y)/y = log y`) on the cuspidal cubic `y³ = x²`,
both by `K`-linear solves through `afDerivWf`. Checked by `afDerivWf f v − y` vanishing, `v = (3/5)xy`, the
log-residual vanishing on `u`, and `u` a nonzero multiple of `y`. -/
theorem afIntegrateAlgebraicWf_cuspCubic_combine :
    (gcCombineSolvedWf.map (fun p =>
      let v := p.1
      let u := p.2
      cisZero (csub (afDerivWf gcuspCubicF v) gcuspCubicY)
      && cisZero (csub v [CCommRing.zero, CFrac.ofPoly [0, 3/5]])
      && cisZero (afLogResidualWf gcuspCubicF gcCombineLogIntegrandWf u)
      && cisZero [u.getD 0 CCommRing.zero]
      && !cisZero [u.getD 1 CCommRing.zero])) = some true := by native_decide

end DeepWiki.SymbolicIntegration
