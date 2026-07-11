import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalExtension
import DeepWiki.SymbolicIntegration.Engine.Algebraic.HermiteNormalForm
import DeepWiki.SymbolicIntegration.Engine.Algebraic.BareissEngine
import DeepWiki.ComputableAlgebra.PolyResultantDense
import DeepWiki.ComputableAlgebra.PolyQuotient

/-! # The algebraic function field `K(x, y) = K(x)[y]/(f)`: trace and discriminant

The general carrier `K(x)[y]/(f)` for an arbitrary monic curve `f`, with the field trace
`Tr : K(x, y) → K(x)`, the trace matrix `[Tr(ωᵢωⱼ)]`, and the discriminant `det[Tr(ωᵢωⱼ)]`
cross-checked against `Resultant(f, f')`. Generalizes the radical carrier `RadExt`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u

namespace DensePoly

variable {α : Type*} [CField α]

/-- Drop column `j` from a row during file-local minor extraction. -/
private def dropCol (row : List α) (j : ℕ) : List α := row.eraseIdx j

/-- The `n×n` determinant over `α` by Laplace cofactor expansion along the first row, sized by an
explicit dimension `n`: `det M = Σⱼ (−1)ʲ · M[0][j] · det(minor₀ⱼ)`. Generic over `[CField α]`;
`n` decreases on each minor. Use `fieldDet M.length M` for an honest matrix. -/
private def fieldDetSized : ℕ → List (List α) → α
  | 0, _ => CCommRing.one
  | _, [] => CCommRing.one
  | n + 1, (row :: rows) =>
    (List.range (n + 1)).foldl (fun acc j =>
      let entry := row.getD j CCommRing.zero
      let minor := rows.map (fun r => dropCol r j)
      let cofactor := CCommRing.mul entry (fieldDetSized n minor)
      let signed := if j % 2 = 0 then cofactor else CCommRing.neg cofactor
      CCommRing.add acc signed) CCommRing.zero

/-- The `n×n` determinant over `α` by recursive Laplace expansion along the first row. -/
def fieldDet (M : List (List α)) : α := fieldDetSized M.length M

end DensePoly

namespace CFrac

/-- The trace-form discriminant of a monic curve, computed by the selected quotient and fraction-free
polynomial capabilities. -/
def discriminant
    {F : (α : Type) → [CField α] → Type} {X Y : Type → Type}
    [CPoly X] [CPolyEngine X] [CPolyGcd X ℚ] [CPolyEuclidean X]
    [CFrac F X] [LawfulCFrac F X] [CFieldDomain ℚ X]
    [CPoly Y] [CPolyEngine Y] [CPolyEuclidean Y]
    (f : Y (F ℚ)) : F ℚ :=
  qfDet (CPoly.traceMatrix f (CPoly.powerBasis f))

end CFrac

namespace CPoly

/-- `Resultant(f, f')` for a represented curve, computed by the selected derivative and resultant
capabilities. -/
def discResultant {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyResultant P]
    {α : Type u} [CField α] (f : P α) : α :=
  CPolyResultant.compute f (CPolyEngine.deriv f)

end CPoly

/-! The trace discriminant and derivative resultant execute through sparse fraction and polynomial
representations without dense adapters. -/

example :
    let x : CPoly.SparsePoly ℚ := CPoly.SparsePoly.ofList [(1, 1)]
    let f : CPoly.SparsePoly (SparseFrac ℚ) :=
      CPoly.SparsePoly.ofList
        [(0, CCommRing.neg (CFrac.ofPoly x)), (2, CCommRing.one)]
    CCommRing.isZero (CField.sub (CFrac.discriminant f)
      (CFrac.ofPoly (CPoly.SparsePoly.ofList [(1, 4)]))) = true ∧
    CCommRing.isZero (CField.sub (CPoly.discResultant f)
      (CFrac.ofPoly (CPoly.SparsePoly.ofList [(1, -4)]))) = true := by
  native_decide

/-! ### The non-radical curve `f = y² − x·y − x³` over `ℚ(x)` -/

open DensePoly

/-- The non-radical curve `f = y² − x·y − x³ ∈ ℚ(x)[y]` as a `DensePoly (DenseFrac ℚ)` `[−x³, −x, 1]`. -/
def afNonRadF : DensePoly (DenseFrac ℚ) :=
  [CFrac.ofPoly [0, 0, 0, -1], CFrac.ofPoly [0, -1], CCommRing.one]

/-- The generator `y` of `ℚ(x)[y]/(f)` (`CPoly.afBasisElem 1 = [0, 1]`). -/
def afNonRadY : DensePoly (DenseFrac ℚ) := CPoly.afBasisElem 1

/-- `Tr(y) = x` on the non-radical curve `y² − xy − x³`: the field trace of the generator `y` is the
`ℚ(x)` value `x`, nonzero unlike a radical curve. -/
theorem afNonRad_trace_y_eq_x :
    CCommRing.isZero (CField.sub (CPoly.trace afNonRadF afNonRadY) (CFrac.ofPoly [0, 1])) = true := by ccompute

/-- `Tr(1) = 2` on the non-radical curve: the trace of `1` is `n = 2`, the `ℚ(x)` constant `2`. -/
theorem afNonRad_trace_one_eq_two :
    CCommRing.isZero (CField.sub (CPoly.trace afNonRadF [CCommRing.one]) (CFrac.ofPoly [2])) = true := by ccompute

/-- `Tr(y²) = x² + 2x³` on the non-radical curve: reducing `y² ≡ xy + x³` and tracing gives the
`ℚ(x)` value `x² + 2x³`. -/
theorem afNonRad_trace_ysq :
    CCommRing.isZero (CField.sub (CPoly.trace afNonRadF (CPoly.mulMod afNonRadF afNonRadY afNonRadY))
      (CFrac.ofPoly [0, 0, 1, 2])) = true := by ccompute

/-- The trace matrix on `[1, y]` for the non-radical curve is `[[2, x], [x, x² + 2x³]]`, checked
entrywise. -/
theorem afNonRad_traceMatrix_entries :
    let T := CPoly.traceMatrix afNonRadF (CPoly.powerBasis afNonRadF)
    (CCommRing.isZero (CField.sub ((T.getD 0 []).getD 0 CCommRing.zero) (CFrac.ofPoly [2]))
      && CCommRing.isZero (CField.sub ((T.getD 0 []).getD 1 CCommRing.zero) (CFrac.ofPoly [0, 1]))
      && CCommRing.isZero (CField.sub ((T.getD 1 []).getD 0 CCommRing.zero) (CFrac.ofPoly [0, 1]))
      && CCommRing.isZero (CField.sub ((T.getD 1 []).getD 1 CCommRing.zero) (CFrac.ofPoly [0, 0, 1, 2])))
      = true := by ccompute

/-- The discriminant of `y² − xy − x³` is `det[Tr(ωᵢωⱼ)] = x² + 4x³`. -/
theorem afNonRad_discriminant_eq :
    CCommRing.isZero (CField.sub (CFrac.discriminant afNonRadF) (CFrac.ofPoly [0, 0, 1, 4])) = true := by
  ccompute

/-- The discriminant equals `± Resultant(f, f')` for the non-radical curve: `discriminant f +
discResultant f = 0`, so `Res(f, f') = −disc(f)`. -/
theorem afNonRad_discriminant_eq_neg_resultant :
    CCommRing.isZero
      (CCommRing.add (CFrac.discriminant afNonRadF) (CPoly.discResultant afNonRadF)) = true := by
  ccompute

/-! ### The trigonal curve `f = y³ + x·y + x` over `ℚ(x)` (`n = 3`) -/

/-- The trigonal curve `f = y³ + x·y + x ∈ ℚ(x)[y]` as the `DensePoly (DenseFrac ℚ)` `[x, x, 0, 1]`. -/
def afTrigF : DensePoly (DenseFrac ℚ) :=
  [CFrac.ofPoly [0, 1], CFrac.ofPoly [0, 1], CCommRing.zero, CCommRing.one]

/-- `Tr(1) = 3` on the trigonal curve: the trace of `1` is `n = 3`, the `ℚ(x)` constant `3`. -/
theorem afTrig_trace_one_eq_three :
    CCommRing.isZero (CField.sub (CPoly.trace afTrigF [CCommRing.one]) (CFrac.ofPoly [3])) = true := by ccompute

/-- `Tr(y²) = −2x` on the trigonal curve: the Newton power-sum trace, the `ℚ(x)` value `−2x`. -/
theorem afTrig_trace_ysq :
    CCommRing.isZero (CField.sub (CPoly.trace afTrigF (CPoly.mulMod afTrigF (CPoly.afBasisElem 1) (CPoly.afBasisElem 1)))
      (CFrac.ofPoly [0, -2])) = true := by ccompute

/-- The trigonal discriminant of `y³ + xy + x` is the depressed-cubic value `−4x³ − 27x²`. -/
theorem afTrig_discriminant_eq :
    CCommRing.isZero (CField.sub (CFrac.discriminant afTrigF) (CFrac.ofPoly [0, 0, -27, -4])) = true := by
  ccompute

/-- The trigonal discriminant equals `± Resultant(f, f')`: `discriminant f + discResultant f = 0`. -/
theorem afTrig_discriminant_eq_resultant :
    CCommRing.isZero
      (CCommRing.add (CFrac.discriminant afTrigF) (CPoly.discResultant afTrigF)) = true := by
  ccompute

/-! ### Conservativity: on a radical curve `f = y² − ρ`, `Tr(y) = 0` -/

/-- The radical curve `f = y² − (x³ + 1) ∈ ℚ(x)[y]` as the `DensePoly (DenseFrac ℚ)` `[−(x³+1), 0, 1]`,
i.e. `y = √(x³+1)` on the general carrier. -/
def afRadF : DensePoly (DenseFrac ℚ) :=
  [CFrac.ofPoly [-1, 0, 0, -1], CCommRing.zero, CCommRing.one]

/-- `Tr(y) = 0` on the radical curve `y² − (x³+1)`: a radical generator is traceless, agreeing with
the radical carrier. -/
theorem afRad_trace_y_eq_zero :
    CCommRing.isZero (CPoly.trace afRadF (CPoly.afBasisElem 1)) = true := by ccompute

/-- `CPoly.mulMod` agrees with the radical relation `y² = ρ`: `CPoly.mulMod f y y = ρ = x³ + 1` for `f = y² − ρ`. -/
theorem afRad_y_sq_eq_radicand :
    CPolyEngine.cisZero (CPolyEngine.sub
      (CPoly.mulMod afRadF (CPoly.afBasisElem 1) (CPoly.afBasisElem 1))
      [CFrac.ofPoly [1, 0, 0, 1]])
      = true := by ccompute

/-! ### Ring sanity on the general carrier -/

/-- `y · 1 = y` on the non-radical curve: the multiplicative identity holds in `ℚ(x)[y]/(f)`. -/
theorem afNonRad_mul_one :
    CPolyEngine.cisZero
      (CPolyEngine.sub (CPoly.mulMod afNonRadF afNonRadY [CCommRing.one]) afNonRadY) = true := by
  ccompute

/-- Multiplication is associative on the trigonal curve: `CPoly.mulMod f y (CPoly.mulMod f y y) = CPoly.mulMod f (CPoly.mulMod
f y y) y` in `ℚ(x)[y]/(y³+xy+x)`. -/
theorem afTrig_mul_assoc :
    CPolyEngine.cisZero (CPolyEngine.sub
        (CPoly.mulMod afTrigF (CPoly.afBasisElem 1) (CPoly.mulMod afTrigF (CPoly.afBasisElem 1) (CPoly.afBasisElem 1)))
        (CPoly.mulMod afTrigF (CPoly.mulMod afTrigF (CPoly.afBasisElem 1) (CPoly.afBasisElem 1)) (CPoly.afBasisElem 1)))
      = true := by ccompute

/-! ### `#print axioms` -/

-- The non-radical curve `y² − xy − x³`: nonzero trace, trace matrix, discriminant, resultant cross-check.
#print axioms afNonRad_trace_y_eq_x
#print axioms afNonRad_traceMatrix_entries
#print axioms afNonRad_discriminant_eq
#print axioms afNonRad_discriminant_eq_neg_resultant

-- The trigonal cubic curve `y³ + xy + x` (`n = 3`): discriminant and resultant cross-check.
#print axioms afTrig_discriminant_eq
#print axioms afTrig_discriminant_eq_resultant

-- Conservativity on the radical curve `y² − (x³+1)`: `Tr(y) = 0`, agreeing with `RadExt`.
#print axioms afRad_trace_y_eq_zero
#print axioms afRad_y_sq_eq_radicand

end DeepWiki.SymbolicIntegration
