import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralQuotient
import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralSetup
import DeepWiki.SymbolicIntegration.Engine.FuelFreeDiophantine

/-! # General algebraic-function integration

The integrator for a plane curve `K(x)[y]/(f)`: the rational part `v` and log
argument `u` are found by `K`-linear solves over the integral basis, with the
Bézout cofactor `f_y⁻¹ mod f` supplied by `afFyInvWf`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open CPoly

namespace CPoly

variable {α : Type*} [CField α]

/-! ## The general derivation `afDerivWf`

`afReduce`/`afMul` already carry a self-computed bound; the one recursive dependency, `f_y⁻¹ mod f`, is
computed by the well-founded `cdiophantineG`. -/

/-- `f_y⁻¹ mod f` — `afFyInvWf f = (cdiophantineG (afFy f) f [1]).1`, the first Bézout cofactor `s` of
`s·f_y + t·f = 1`. The inverse of `∂f/∂y` in `K(x)[y]/(f)` (valid for separable `f`), degree `< deg f`. -/
def afFyInvWf (f : CPoly α) : CPoly α :=
  (cdiophantineG (afFy f) f [CField.one]).1

variable [CDiffField α]

/-- The implicit derivative `afYprimeWf f = afReduce f (−f_x · afFyInvWf f)`:
`y' = −(∂f/∂x)·(∂f/∂y)⁻¹ mod f`. -/
def afYprimeWf (f : CPoly α) : CPoly α :=
  afReduce f (cmulG (cnegG (afFx f)) (afFyInvWf f))

/-- The general derivation `afDerivWf f u = afReduce f (u.map cderiv + cderivG u · afYprimeWf f)`: the
product rule `D(u) = Σᵢ aᵢ'·yⁱ + (Σᵢ aᵢ·i·yⁱ⁻¹)·y'`. `[CField α] [CDiffField α]`-generic. -/
def afDerivWf (f u : CPoly α) : CPoly α :=
  afReduce f (caddG ((u : List α).map CDiffField.cderiv) (cmulG (cderivG u) (afYprimeWf f)))

section WfInvariant

variable [CFieldSpec α] [CDiffFieldSpec α]

/-! ### The Wf derivation invariant

The shared quotient API lives in `ComputableGeneralQuotient`; separability is phrased as the gcd
`cgcdWf (afFy f) f` being a nonzero constant. -/

omit [CFieldSpec α] [CDiffFieldSpec α] in
/-- `afDerivWf = afReduce f ∘ cmonomialDeriv (afYprimeWf f)` definitionally. -/
theorem afDerivWf_eq_afReduce_cmonomialDeriv (f u : CPoly α) :
    afDerivWf f u = afReduce f (cmonomialDeriv (afYprimeWf f) u) := rfl

/-- The Wf keystone: `afDerivWf` realizes `implicitDeriv (toPolyG (afYprimeWf f))` in the quotient. -/
theorem mk_toPolyG_afDerivWf (f u : CPoly α) (hf : cnormG f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f u))
      = Ideal.Quotient.mk (afIdeal f)
          (Differential.implicitDeriv (toPolyG (afYprimeWf f)) (toPolyG u)) := by
  rw [afDerivWf_eq_afReduce_cmonomialDeriv, mk_toPolyG_afReduce f _ hf]
  simp only [denote]

/-- `afDerivWf` is additive modulo the curve ideal. -/
theorem mk_toPolyG_afDerivWf_add (f a b : CPoly α) (hf : cnormG f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f (caddG a b)))
      = Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f a))
        + Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f b)) := by
  rw [mk_toPolyG_afDerivWf f _ hf, mk_toPolyG_afDerivWf f a hf,
    mk_toPolyG_afDerivWf f b hf]
  simp only [denote, map_add]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- Bézout inverse of `f_y` in the quotient. -/
theorem mk_toPolyG_afFyInvWf_mul_afFy (f : CPoly α) (hf : cnormG f ≠ [])
    (hgdeg : (toPolyG (cgcdWf (afFy f) f).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf (afFy f) f).1 ≠ 0) :
    Ideal.Quotient.mk (afIdeal f)
        (toPolyG (afFyInvWf f) * toPolyG (afFy f)) = 1 := by
  have hbez := toPolyG_cdiophantineG (afFy f) f [CField.one] hf hgdeg hgne
  have hone : toPolyG ([CField.one] : CPoly α) = 1 := by
    simp only [denote]
    simp
  rw [hone] at hbez
  rw [show toPolyG (afFyInvWf f) * toPolyG (afFy f)
      = 1 - toPolyG (cdiophantineG (afFy f) f [CField.one]).2 * toPolyG f from by
        rw [afFyInvWf]; linear_combination hbez]
  have hmem : Ideal.Quotient.mk (afIdeal f)
      (toPolyG (cdiophantineG (afFy f) f [CField.one]).2 * toPolyG f) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (mul_curve_mem f _)
  rw [map_sub, hmem, map_one, sub_zero]

/-- The implicit derivation kills the curve generator modulo its ideal. -/
theorem implicitDerivWf_curve_mem (f : CPoly α) (hf : cnormG f ≠ [])
    (hgdeg : (toPolyG (cgcdWf (afFy f) f).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf (afFy f) f).1 ≠ 0) :
    Differential.implicitDeriv (toPolyG (afYprimeWf f)) (toPolyG f) ∈ afIdeal f := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [show Differential.implicitDeriv (toPolyG (afYprimeWf f)) (toPolyG f)
      = Differential.mapCoeffs (toPolyG f)
        + toPolyG (afYprimeWf f) * Polynomial.derivative (toPolyG f) from by
        simp [Differential.implicitDeriv, derivative']]
  rw [mapCoeffs_toPolyG_eq_afFx, derivative_toPolyG_eq_afFy]
  have hyp : Ideal.Quotient.mk (afIdeal f) (toPolyG (afYprimeWf f))
      = Ideal.Quotient.mk (afIdeal f) (- toPolyG (afFx f) * toPolyG (afFyInvWf f)) := by
    rw [afYprimeWf, mk_toPolyG_afReduce f _ hf]
    simp only [denote, map_mul, map_neg]
  rw [map_add, map_mul, hyp, ← map_mul]
  have hfyinv := mk_toPolyG_afFyInvWf_mul_afFy f hf hgdeg hgne
  rw [show - toPolyG (afFx f) * toPolyG (afFyInvWf f) * toPolyG (afFy f)
      = - (toPolyG (afFx f) * (toPolyG (afFyInvWf f) * toPolyG (afFy f))) from by ring,
    map_neg, map_mul, hfyinv, mul_one, add_neg_cancel]

/-- The implicit derivation maps `afIdeal f` into itself. -/
theorem implicitDerivWf_mem_afIdeal (f : CPoly α) (hf : cnormG f ≠ [])
    (hgdeg : (toPolyG (cgcdWf (afFy f) f).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf (afFy f) f).1 ≠ 0)
    {x : (CFieldSpec.K α)[X]} (hx : x ∈ afIdeal f) :
    Differential.implicitDeriv (toPolyG (afYprimeWf f)) x ∈ afIdeal f := by
  rw [afIdeal, Ideal.mem_span_singleton'] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_right _ _ ?_)
  · exact implicitDerivWf_curve_mem f hf hgdeg hgne
  · exact Ideal.subset_span (Set.mem_singleton _)

/-- The implicit derivation descends to the quotient by `afIdeal f`. -/
theorem mk_implicitDerivWf_congr (f : CPoly α) (hf : cnormG f ≠ [])
    (hgdeg : (toPolyG (cgcdWf (afFy f) f).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf (afFy f) f).1 ≠ 0)
    {p q : (CFieldSpec.K α)[X]}
    (hpq : Ideal.Quotient.mk (afIdeal f) p = Ideal.Quotient.mk (afIdeal f) q) :
    Ideal.Quotient.mk (afIdeal f)
        (Differential.implicitDeriv (toPolyG (afYprimeWf f)) p)
      = Ideal.Quotient.mk (afIdeal f)
        (Differential.implicitDeriv (toPolyG (afYprimeWf f)) q) := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  apply implicitDerivWf_mem_afIdeal f hf hgdeg hgne
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hpq, sub_self]

/-- `afDerivWf` is Leibniz modulo the curve ideal. -/
theorem mk_toPolyG_afDerivWf_afMul (f a b : CPoly α) (hf : cnormG f ≠ [])
    (hgdeg : (toPolyG (cgcdWf (afFy f) f).1).natDegree = 0)
    (hgne : toPolyG (cgcdWf (afFy f) f).1 ≠ 0) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f (afMul f a b)))
      = Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f (afDerivWf f a) b))
        + Ideal.Quotient.mk (afIdeal f) (toPolyG (afMul f a (afDerivWf f b))) := by
  set yp := toPolyG (afYprimeWf f) with hyp
  set A := toPolyG a with hA
  set B := toPolyG b with hB
  rw [mk_toPolyG_afDerivWf f _ hf, ← hyp]
  rw [mk_implicitDerivWf_congr f hf hgdeg hgne (mk_toPolyG_afMul f a b hf)]
  rw [mk_toPolyG_afMul _ _ _ hf, mk_toPolyG_afMul _ _ _ hf, mk_toPolyG_afDerivWf f a hf,
    mk_toPolyG_afDerivWf f b hf, ← hyp, ← hA, ← hB]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
  ring

/-- `afDerivWf` kills `1` modulo the curve ideal. -/
theorem mk_toPolyG_afDerivWf_one (f : CPoly α) (hf : cnormG f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPolyG (afDerivWf f [CField.one])) = 0 := by
  rw [mk_toPolyG_afDerivWf f _ hf]
  have h1 : toPolyG ([CField.one] : CPoly α) = 1 := by
    simp only [denote]
    simp
  rw [h1, Derivation.map_one_eq_zero, map_zero]

omit [CDiffFieldSpec α] in
/-- The `afDerivWf` round-trip certificate is the free-polynomial integrand identity. -/
theorem toPolyG_afDerivWf_eq_of_roundtrip (f v g : CPoly α)
    (hcheck : cisZeroG (csubG (afDerivWf f v) g) = true) :
    toPolyG (afDerivWf f v) = toPolyG g := by
  simpa [cisZeroG_iff, sub_eq_zero] using hcheck

end WfInvariant

end CPoly

/-! ## The flat rational and log-argument solvers

Build a `ℚ`-matrix from `afDerivWf` and solve it with `kernelBasisG`; specialized to `QFunNZG ℚ`. -/

/-- Rational-part residual columns `afRatColumnsWf f basis degBound integrand`: the per-monomial
derivatives `afDerivWf f (xʲ wᵢ)` followed by the forced `−integrand` column. -/
def afRatColumnsWf (f : CPoly (QFunNZG ℚ)) (basis : List (CPoly (QFunNZG ℚ)))
    (degBound : ℕ) (integrand : CPoly (QFunNZG ℚ)) : List (CPoly (QFunNZG ℚ)) :=
  (afRatMonomials basis degBound).map (afDerivWf f) ++ [cnegG integrand]

/-- `ℚ`-matrix of the rational-part system `afRatMatrixWf f basis degBound integrand`: clear each `K(x)`
coordinate of `afRatColumnsWf` to numerators over a common denominator, read off `x`-power coefficients. -/
def afRatMatrixWf (f : CPoly (QFunNZG ℚ)) (basis : List (CPoly (QFunNZG ℚ)))
    (degBound : ℕ) (integrand : CPoly (QFunNZG ℚ)) : List (List ℚ) × ℕ :=
  let cols := afRatColumnsWf f basis degBound integrand
  let nCols := cols.length
  let n := cdegG f
  let rowsForCoord : ℕ → List (List ℚ) := fun i =>
    let entryOf : ℕ → QFunNZG ℚ := fun k => (cols[k]!).getD i CField.zero
    let nums : List (CPoly ℚ) := (List.range nCols).map (fun k => cnormG (entryOf k).1.1)
    let dens : List (CPoly ℚ) := (List.range nCols).map (fun k => cnormG (entryOf k).1.2)
    let cleared : List (CPoly ℚ) := (List.range nCols).map (fun k =>
      let prod := (List.range nCols).foldl (fun acc l =>
        if l = k then acc else cmulG acc (dens[l]!)) [(1 : ℚ)]
      cnormG (cmulG (nums[k]!) prod))
    let width := (cleared.foldl (fun acc p => max acc p.length) 0)
    (List.range width).map (fun r =>
      (List.range nCols).map (fun k => (cleared[k]!).getD r 0))
  let allRows := (List.range n).flatMap rowsForCoord
  let nonzero := allRows.filter (fun row => row.any (fun a => a ≠ 0))
  (nonzero, nCols)

/-- General rational-part solve `afRationalSolveWf f basis degBound integrand = some v`: the rational part
`v = Σ c_{ij} xʲ wᵢ` with `afDeriv f v = integrand`, by a `K`-linear solve over the integral basis (build
`afRatMatrixWf`, find a kernel vector with nonzero RHS coordinate, normalize, reassemble `v`). -/
def afRationalSolveWf (f : CPoly (QFunNZG ℚ)) (basis : List (CPoly (QFunNZG ℚ)))
    (degBound : ℕ) (integrand : CPoly (QFunNZG ℚ)) : Option (CPoly (QFunNZG ℚ)) :=
  let (rows, nCols) := afRatMatrixWf f basis degBound integrand
  let kers := kernelBasisG nCols rows
  match kers.find? (fun c => c.getD (nCols - 1) 0 ≠ 0) with
  | none => none
  | some c =>
    let rhs := c.getD (nCols - 1) 0
    let monos := afRatMonomials basis degBound
    let v : CPoly (QFunNZG ℚ) :=
      (List.range monos.length).foldl (fun acc idx =>
        let coeff : ℚ := c.getD idx 0 / rhs
        caddG acc (cscaleG (qxOfNum [coeff]) (monos.getD idx []))) ([] : CPoly (QFunNZG ℚ))
    some v

/-- Log-derivative residual `afLogResidualWf f integrand u = afDerivWf f u − afMul f u integrand`. -/
def afLogResidualWf (f integrand u : CPoly (QFunNZG ℚ)) : CPoly (QFunNZG ℚ) :=
  csubG (afDerivWf f u) (afMul f u integrand)

/-- Log-argument residual columns `afLogColumnsWf f basis degBound integrand`: the per-monomial
log-derivative residuals `afLogResidualWf f integrand (xʲ wᵢ)` (no forced `−integrand` column — the log
system is homogeneous in `u`). -/
def afLogColumnsWf (f : CPoly (QFunNZG ℚ)) (basis : List (CPoly (QFunNZG ℚ)))
    (degBound : ℕ) (integrand : CPoly (QFunNZG ℚ)) : List (CPoly (QFunNZG ℚ)) :=
  (afRatMonomials basis degBound).map (afLogResidualWf f integrand)

/-- `ℚ`-matrix of the log-argument system `afLogMatrixWf f basis degBound integrand`: identical extraction
on the homogeneous columns `afLogColumnsWf`. -/
def afLogMatrixWf (f : CPoly (QFunNZG ℚ)) (basis : List (CPoly (QFunNZG ℚ)))
    (degBound : ℕ) (integrand : CPoly (QFunNZG ℚ)) : List (List ℚ) × ℕ :=
  let cols := afLogColumnsWf f basis degBound integrand
  let nCols := cols.length
  let n := cdegG f
  let rowsForCoord : ℕ → List (List ℚ) := fun i =>
    let entryOf : ℕ → QFunNZG ℚ := fun k => (cols[k]!).getD i CField.zero
    let nums : List (CPoly ℚ) := (List.range nCols).map (fun k => cnormG (entryOf k).1.1)
    let dens : List (CPoly ℚ) := (List.range nCols).map (fun k => cnormG (entryOf k).1.2)
    let cleared : List (CPoly ℚ) := (List.range nCols).map (fun k =>
      let prod := (List.range nCols).foldl (fun acc l =>
        if l = k then acc else cmulG acc (dens[l]!)) [(1 : ℚ)]
      cnormG (cmulG (nums[k]!) prod))
    let width := (cleared.foldl (fun acc p => max acc p.length) 0)
    (List.range width).map (fun r =>
      (List.range nCols).map (fun k => (cleared[k]!).getD r 0))
  let allRows := (List.range n).flatMap rowsForCoord
  let nonzero := allRows.filter (fun row => row.any (fun a => a ≠ 0))
  (nonzero, nCols)

/-- General log-argument solve `afLogArgSolveWf f basis degBound integrand = some u`: the log argument
`u = Σ c_{ij} xʲ wᵢ` with `afDeriv f u = afMul f u integrand` (`∫ integrand = log u`), by the homogeneous
`K`-linear solve (build `afLogMatrixWf`, find the first nonzero kernel vector, reassemble `u`). -/
def afLogArgSolveWf (f : CPoly (QFunNZG ℚ)) (basis : List (CPoly (QFunNZG ℚ)))
    (degBound : ℕ) (integrand : CPoly (QFunNZG ℚ)) : Option (CPoly (QFunNZG ℚ)) :=
  let (rows, nCols) := afLogMatrixWf f basis degBound integrand
  let kers := kernelBasisG nCols rows
  match kers.find? (fun c => c.any (fun a => a ≠ 0)) with
  | none => none
  | some c =>
    let monos := afRatMonomials basis degBound
    let u : CPoly (QFunNZG ℚ) :=
      (List.range monos.length).foldl (fun acc idx =>
        let coeff : ℚ := c.getD idx 0
        caddG acc (cscaleG (qxOfNum [coeff]) (monos.getD idx []))) ([] : CPoly (QFunNZG ℚ))
    some u

/-! ## The top-level `afIntegrateAlgebraicWf` -/

/-- The general-curve integrator `afIntegrateAlgebraicWf f basis degBound ratIntegrand logIntegrand =
some (v, u)`: `∫ (ratIntegrand + logIntegrand) dx = v + log u` (principal case) — the rational part `v` by
`afRationalSolveWf` (`afDeriv f v = ratIntegrand`) and the log argument `u` by `afLogArgSolveWf`
(`afDeriv f u = afMul f u logIntegrand`), both `K`-linear solves through `afDerivWf`. `none` if either
solve fails. The general analogue of `cIntegrateAlgebraicWf`. -/
def afIntegrateAlgebraicWf (f : CPoly (QFunNZG ℚ)) (basis : List (CPoly (QFunNZG ℚ)))
    (degBound : ℕ) (ratIntegrand logIntegrand : CPoly (QFunNZG ℚ)) :
    Option (CPoly (QFunNZG ℚ) × CPoly (QFunNZG ℚ)) :=
  match afRationalSolveWf f basis degBound ratIntegrand,
        afLogArgSolveWf f basis degBound logIntegrand with
  | some v, some u => some (v, u)
  | _, _ => none

/-! ## Cuspidal-cubic combined integral

`∫ (y + afDerivWf(y)/y) dx = (3/5)xy + log y` on `y³ = x²`, checked by `afDerivWf` (`native_decide`). -/

/-- The rational summand input for the cuspidal-cubic combined validation. -/
def gcCombineRatIntegrandWf : CPoly (QFunNZG ℚ) := gcuspCubicY

/-- The log-derivative input for the cuspidal-cubic combined validation. -/
def gcCombineLogIntegrandWf : CPoly (QFunNZG ℚ) :=
  afMul gcuspCubicF (afDerivWf gcuspCubicF gcuspCubicY)
    [CField.zero, CField.zero, qxOfFrac [1] [0, 0, 1] (by decide)]

/-- The `afIntegrateAlgebraicWf` run for the cuspidal-cubic combined integral
`∫ (y + afDerivWf(y)/y) dx`. -/
def gcCombineSolvedWf : Option (CPoly (QFunNZG ℚ) × CPoly (QFunNZG ℚ)) :=
  afIntegrateAlgebraicWf gcuspCubicF gcuspCubicBasis 2 gcCombineRatIntegrandWf gcCombineLogIntegrandWf

/-- The general-curve integrator integrates `∫ (y + afDeriv(y)/y) dx = (3/5)xy + log y`:
derives the rational part `v = (3/5)x·y` (`afDerivWf f v = y`) and the log argument `u` a nonzero multiple
of `y` (`afDerivWf f u = afMul f u logIntegrand`, `∫ afDeriv(y)/y = log y`) on the cuspidal cubic `y³ = x²`,
both by `K`-linear solves through `afDerivWf`. Checked by `afDerivWf f v − y` vanishing, `v = (3/5)xy`, the
log-residual vanishing on `u`, and `u` a nonzero multiple of `y`. -/
theorem afIntegrateAlgebraicWf_cuspCubic_combine :
    (gcCombineSolvedWf.map (fun p =>
      let v := p.1
      let u := p.2
      cisZeroG (csubG (afDerivWf gcuspCubicF v) gcCombineRatIntegrandWf)
      && cisZeroG (csubG v [CField.zero, qxOfNum [0, 3/5]])
      && cisZeroG (afLogResidualWf gcuspCubicF gcCombineLogIntegrandWf u)
      && cisZeroG [u.getD 0 CField.zero]
      && !cisZeroG [u.getD 1 CField.zero])) = some true := by native_decide

end DeepWiki.SymbolicIntegration
