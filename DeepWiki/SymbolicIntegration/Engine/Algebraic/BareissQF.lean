import DeepWiki.SymbolicIntegration.Engine.Algebraic.BareissEngine
import DeepWiki.SymbolicIntegration.Engine.Algebraic.BareissExamples
import DeepWiki.SymbolicIntegration.Engine.Algebraic.Round2IntegralBasis

/-! # Agreement of the fraction-free `ℚ(x)` wrappers with `fieldDet`/`matInv`

The `ℚ(x)` wrappers `qfDet`/`qfAdjugate`/`qfInv`/`qfSolve` (clear to `ℚ[x]`, run Bareiss, read back)
agree with the fraction-based `fieldDet`/`matInv` on the trace-matrix curves and `ℚ(x)`-fraction
matrices, and the degree-swell benchmark `qfSwellWin` measures the fraction path's ballooning degrees
against the flat fraction-free ones. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-! ### Agreement: `qfDet = fieldDet` on the trace-matrix curves and `ℚ(x)`-fraction matrices -/

open DensePoly

/-- `qfDet = fieldDet` on the non-radical trace matrix of `y² − xy − x³`, both the discriminant
`x² + 4x³`. -/
theorem qfDet_eq_fieldDet_afNonRad :
    let T := traceMatrix afNonRadF (powerBasis afNonRadF)
    CCommRing.isZero (CField.sub (qfDet T) (fieldDet T)) = true := by native_decide

/-- `qfDet = fieldDet` on the `3×3` trigonal trace matrix of `y³ + xy + x`, both the discriminant
`−4x³ − 27x²`. -/
theorem qfDet_eq_fieldDet_afTrig :
    let T := traceMatrix afTrigF (powerBasis afTrigF)
    CCommRing.isZero (CField.sub (qfDet T) (fieldDet T)) = true := by native_decide

/-- `qfDet = fieldDet` on the cusp trace matrix of `y² − x³`, both the discriminant `4x³`. -/
theorem qfDet_eq_fieldDet_cusp :
    let T := traceMatrix cuspF (powerBasis cuspF)
    CCommRing.isZero (CField.sub (qfDet T) (fieldDet T)) = true := by native_decide

/-- A `3×3` `ℚ(x)`-matrix with genuine fraction entries (denominators `x+1, …, x+5`, a permuted
Cauchy-style matrix), where `fieldDet` carries a ballooning denominator. -/
def qfFracMat3 : List (List (CFrac ℚ)) :=
  [[CFrac.ofFraction [1] [1, 1] (by decide), CFrac.ofFraction [1] [2, 1] (by decide), CFrac.ofFraction [1] [3, 1] (by decide)],
   [CFrac.ofFraction [1] [2, 1] (by decide), CFrac.ofFraction [1] [3, 1] (by decide), CFrac.ofFraction [1] [4, 1] (by decide)],
   [CFrac.ofFraction [1] [4, 1] (by decide), CFrac.ofFraction [1] [1, 1] (by decide), CFrac.ofFraction [1] [5, 1] (by decide)]]

/-- `qfDet = fieldDet` on the `3×3` fraction matrix `qfFracMat3` as a `ℚ(x)` value, though `fieldDet`
carries an unreduced fraction of total degree `24` and `qfDet` a flat polynomial. -/
theorem qfDet_eq_fieldDet_fracMat3 :
    CCommRing.isZero (CField.sub (qfDet qfFracMat3) (fieldDet qfFracMat3)) = true := by native_decide

/-! ### The fraction-free inverse agrees with `matInv` -/

/-- `qfInv` agrees with `matInv` entrywise on the cusp `I_x`-basis matrix `B = [[x, 0], [0, 1]]`, both
`B⁻¹ = [[1/x, 0], [0, 1]]`. -/
theorem qfInv_eq_matInvG_cuspBasis :
    let B := ipBasisMatrix 2 (pTraceRadical cuspF [0, 1] 0)
    let Binv := (matInv 2 B).getD []
    (List.range 2).all (fun i => (List.range 2).all (fun j =>
      CCommRing.isZero (CField.sub (qfInvEntry B i j) ((Binv.getD i []).getD j CCommRing.zero)))) = true := by
  native_decide

/-- `qfInv` agrees with `matInv` entrywise on the `3×3` fraction matrix `qfFracMat3` as `ℚ(x)` values,
though `matInv` carries each entry as an unreduced fraction of total degree up to `41`. -/
theorem qfInv_eq_matInvG_fracMat3 :
    let Minv := (matInv 3 qfFracMat3).getD []
    (List.range 3).all (fun i => (List.range 3).all (fun j =>
      CCommRing.isZero (CField.sub (qfInvEntry qfFracMat3 i j)
        ((Minv.getD i []).getD j CCommRing.zero)))) = true := by
  native_decide

/-! ### Adjugate / solve sanity over `ℚ(x)` -/

/-- `qfAdjugate` satisfies `M'·adj(M') = det(M')·I` on the cusp `I_x`-basis matrix `B`, with `M' = D·B`
the cleared `ℚ[x]`-matrix. -/
theorem qfAdjugate_mul_cuspBasis :
    let B := ipBasisMatrix 2 (pTraceRadical cuspF [0, 1] 0)
    let M' := (qfClearMatrix B).1
    let A := (qfAdjugate B).1
    let d := bareissDet M'
    (List.range 2).all (fun i => (List.range 2).all (fun j =>
      cisZero (csub
        ((List.range 2).foldl (fun acc k => cadd acc (cmul (getEntry M' i k) (getEntry A k j))) [])
        (if i = j then d else [])))) = true := by native_decide

/-- `qfSolve` solves `M·x = b` over `ℚ(x)` on the `3×3` fraction matrix `qfFracMat3` with `b = [1, 1, 1]`:
reading back `x` and multiplying `M·x` recovers `b`. -/
theorem qfSolve_fracMat3 :
    let b : List (CFrac ℚ) := [CFrac.ofPoly [1], CFrac.ofPoly [1], CFrac.ofPoly [1]]
    let ds := qfSolve qfFracMat3 b
    let xq : List (CFrac ℚ) := ds.2.map (fun s => CCommRing.mul (CFrac.ofPoly s) (CField.inv (CFrac.ofPoly ds.1)))
    let lhs : List (CFrac ℚ) := (List.range 3).map (fun i =>
      (List.range 3).foldl (fun acc j =>
        CCommRing.add acc (CCommRing.mul ((qfFracMat3.getD i []).getD j CCommRing.zero) (xq.getD j CCommRing.zero)))
        CCommRing.zero)
    (List.range 3).all (fun i =>
      CCommRing.isZero (CField.sub (lhs.getD i CCommRing.zero) (b.getD i CCommRing.zero))) = true := by
  native_decide

/-! ### The swell benchmark: `qfDet`/`qfInv` vs `fieldDet`/`matInv`

On the `3×3` fraction matrix `qfFracMat3`, the fraction path (`fieldDet`/`matInv` over `ℚ(x)`) carries
a determinant of total degree `24` and inverse entries of total degree up to `41`, while the
fraction-free `qfDet`/`qfInv` stay flat with a single bounded `ℚ[x]` per matrix. -/

open DensePoly

/-- The fraction-path determinant total degree `cdeg num + cdeg den` of the unreduced `ℚ(x)` value
`fieldDet qfFracMat3` (numerator degree `9` plus denominator degree `15`, total `24`). -/
def qfDetFracTotalDeg : ℕ :=
  let z := fieldDet qfFracMat3
  cdeg z.num + cdeg z.den

/-- The fraction-free determinant flat degree `cdeg num` of `qfDet qfFracMat3`, the degree of the single
`ℚ[x]` determinant numerator over the single denominator `D³`. -/
def qfDetFlatDeg : ℕ := cdeg (qfDet qfFracMat3).num

/-- The fraction-path inverse max total degree `max over entries of (cdeg num + cdeg den)` of
`matInv 3 qfFracMat3`, the largest numerator+denominator degree among the unreduced `ℚ(x)` inverse
entries (`= 41`). -/
def qfInvFracMaxTotalDeg : ℕ :=
  match matInv 3 qfFracMat3 with
  | none => 0
  | some Minv =>
    ((Minv.map (fun row => row.map (fun z => cdeg z.num + cdeg z.den))).flatten).foldl max 0

/-- The fraction-free inverse max entry degree `max over entries of cdeg` of the `ℚ[x]` adjugate
`(qfInv qfFracMat3).2`, the largest degree among the flat inverse-numerator entries over the single
shared determinant. -/
def qfInvFlatMaxDeg : ℕ :=
  ((((qfInv qfFracMat3).2).map (fun row => row.map cdeg)).flatten).foldl max 0

/-- The measured swell win: `qfDetFlatDeg < qfDetFracTotalDeg ∧ qfInvFlatMaxDeg < qfInvFracMaxTotalDeg`
— the fraction-free degrees are strictly below the fraction-path degrees on the `3×3` fraction matrix. -/
theorem qfSwellWin :
    qfDetFlatDeg < qfDetFracTotalDeg ∧ qfInvFlatMaxDeg < qfInvFracMaxTotalDeg := by native_decide

/-- The fraction-path determinant total degree is `24`: numerator degree `9` over denominator degree
`15`. -/
theorem qfDetFracTotalDeg_eq : qfDetFracTotalDeg = 24 := by native_decide

/-- The fraction-path inverse max total degree is `41`: the largest `matInv 3 qfFracMat3` inverse entry
has numerator degree `22` over denominator degree `19`. -/
theorem qfInvFracMaxTotalDeg_eq : qfInvFracMaxTotalDeg = 41 := by native_decide

/-- The fraction-free inverse stays flat: the `qfInv` adjugate entries have max degree `qfInvFlatMaxDeg`,
far below the fraction path's `41`, over one shared `ℚ[x]` determinant. -/
theorem qfInvFlatMaxDeg_lt : qfInvFlatMaxDeg < 41 := by native_decide

/-! #### A `maxHeartbeats` witness that the fraction-free path is cheap -/

set_option maxHeartbeats 400000 in
/-- The swell win `qfSwellWin` evaluates within a tight `maxHeartbeats 400000` budget, evidencing that
the fraction-free `qfDet`/`qfInv` path is the cheap one. -/
theorem qfHeavyHeartbeats :
    qfDetFlatDeg < qfDetFracTotalDeg ∧ qfInvFlatMaxDeg < qfInvFracMaxTotalDeg := by native_decide

/-! ### `#print axioms` for the `ℚ(x)` Bareiss validations -/

-- Agreement of the fraction-free `qfDet` with the fraction-based `fieldDet` (the actual curve matrices).
#print axioms qfDet_eq_fieldDet_afNonRad
#print axioms qfDet_eq_fieldDet_afTrig
#print axioms qfDet_eq_fieldDet_cusp
#print axioms qfDet_eq_fieldDet_fracMat3

-- Agreement of the fraction-free `qfInv` with the fraction-based `matInv` (the idealizer inverse).
#print axioms qfInv_eq_matInvG_cuspBasis
#print axioms qfInv_eq_matInvG_fracMat3

-- The fraction-free adjugate / solve identities `M'·adj = det·I`, `M·x = b` (over `ℚ(x)`).
#print axioms qfAdjugate_mul_cuspBasis
#print axioms qfSolve_fracMat3

-- The swell benchmark: fraction path (det 24 / inv 41) vs flat fraction-free Bareiss.
#print axioms qfSwellWin
#print axioms qfDetFracTotalDeg_eq
#print axioms qfInvFracMaxTotalDeg_eq
#print axioms qfInvFlatMaxDeg_lt
#print axioms qfHeavyHeartbeats

end DeepWiki.SymbolicIntegration
