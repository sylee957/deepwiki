import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalExtension
import DeepWiki.SymbolicIntegration.Engine.Algebraic.HermiteNormalForm
import DeepWiki.SymbolicIntegration.Engine.Algebraic.BareissEngine
import DeepWiki.SymbolicIntegration.Engine.FuelFreeResultant

/-! # The algebraic function field `K(x, y) = K(x)[y]/(f)`: trace and discriminant

The general carrier `K(x)[y]/(f)` for an arbitrary monic curve `f`, with the field trace
`Tr : K(x, y) → K(x)`, the trace matrix `[Tr(ωᵢωⱼ)]`, and the discriminant `det[Tr(ωᵢωⱼ)]`
cross-checked against `Resultant(f, f')`. Generalizes the radical carrier `RadExt`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPoly

variable {α : Type*} [CField α]

/-! ### The ring `K(x)[y]/(f)` for an arbitrary monic `f` (`afReduce`/`afMul`/`afPow`) -/

/-- Reduce `p` modulo `f` in `α[y]/(f)`: the Euclidean remainder `cmodWf p f`, the canonical
coset representative. -/
def afReduce (f p : CPoly α) : CPoly α := cmodWf p f

/-- Multiplication in `α[y]/(f)`: `cmul` then reduce `mod f` (`afReduce`). -/
def afMul (f a b : CPoly α) : CPoly α := afReduce f (cmul a b)

/-- The `i`-th power-basis element `yⁱ` of `α[y]/(f)` (`cshift i [1]`). -/
def afBasisElem (i : ℕ) : CPoly α := cshift i [CField.one]

/-- `toPoly (afBasisElem 1) = X`: the carrier generator `y` reads as the formal variable `X`. -/
theorem toPolyG_afBasisElem_one [CFieldSpec α] : toPoly (afBasisElem 1 : CPoly α) = X := by
  rw [afBasisElem]
  simp only [denote]
  rw [pow_one]
  simp

/-- Power in `α[y]/(f)`: `afPow f a k = aᵏ mod f` by `ℕ`-recursion, each step an `afMul`. -/
def afPow (f a : CPoly α) : ℕ → CPoly α
  | 0 => [CField.one]
  | k + 1 => afMul f a (afPow f a k)

/-! ### The multiplication matrix `M_w` and the trace `Tr(w)` -/

/-- The coefficient of `yⁱ` in `p : CPoly α` (the `α`-entry at index `i`, `CField.zero` past the
end). -/
def afCoeff (p : CPoly α) (i : ℕ) : α := (p : List α).getD i CField.zero

/-- The multiplication-by-`w` matrix `M_w` of `α[y]/(f)`, `n×n` over `α` (`n = deg f`): entry
`(r, c)` is the coefficient of `yʳ` in `w·y^c mod f`. Represented as `List (List α)`. -/
def multMatrix (f w : CPoly α) : List (List α) :=
  let n := cdeg f
  (List.range n).map (fun r =>
    (List.range n).map (fun c => afCoeff (afMul f w (afBasisElem c)) r))

/-- The field trace `Tr_{K(x,y)/K(x)}(w) = Σᵢ (M_w)ᵢᵢ`, the diagonal sum of the
multiplication-by-`w` matrix. -/
def trace (f w : CPoly α) : α :=
  let n := cdeg f
  (List.range n).foldl (fun acc i =>
    CField.add acc (afCoeff (afMul f w (afBasisElem i)) i)) CField.zero

/-! ### The trace matrix `[Tr(ωᵢωⱼ)]` and the discriminant `det[Tr(ωᵢωⱼ)]` -/

/-- The trace matrix `[Tr(ωᵢ·ωⱼ)]` of a `basis` for `α[y]/(f)`: the symmetric matrix over `α`
with `(i, j)` entry `trace f (afMul f ωᵢ ωⱼ)`, the Gram matrix of the trace form. -/
def traceMatrix (f : CPoly α) (basis : List (CPoly α)) : List (List α) :=
  basis.map (fun ωi => basis.map (fun ωj => trace f (afMul f ωi ωj)))

/-- The power basis `[1, y, …, yⁿ⁻¹]` (`n = deg f`) of `α[y]/(f)`. -/
def powerBasis (f : CPoly α) : List (CPoly α) := (List.range (cdeg f)).map afBasisElem

/-- Drop column `j` from a row (the `α`-list with index `j` removed), the minor-extraction
helper for `fieldDet`. -/
def dropCol (row : List α) (j : ℕ) : List α := row.eraseIdx j

/-- The `n×n` determinant over `α` by Laplace cofactor expansion along the first row, sized by an
explicit dimension `n`: `det M = Σⱼ (−1)ʲ · M[0][j] · det(minor₀ⱼ)`. Generic over `[CField α]`;
`n` decreases on each minor. Use `fieldDet M.length M` for an honest matrix. -/
def fieldDetSized : ℕ → List (List α) → α
  | 0, _ => CField.one
  | _, [] => CField.one
  | n + 1, (row :: rows) =>
    (List.range (n + 1)).foldl (fun acc j =>
      let entry := row.getD j CField.zero
      let minor := rows.map (fun r => dropCol r j)
      let cofactor := CField.mul entry (fieldDetSized n minor)
      let signed := if j % 2 = 0 then cofactor else CField.neg cofactor
      CField.add acc signed) CField.zero

/-- The `n×n` determinant over `α` by Laplace expansion (`fieldDetSized` with the matrix's own
row count as the dimension): `det M = Σⱼ (−1)ʲ · M[0][j] · det(minor₀ⱼ)`. -/
def fieldDet (M : List (List α)) : α := fieldDetSized M.length M

/-- The discriminant of the monic curve `f` over `ℚ(x) = CFrac ℚ`: `det[Tr(ωᵢ·ωⱼ)]` for the
power basis, computed fraction-free via `qfDet` (Bareiss over a common `ℚ[x]` denominator).
Equal to `fieldDet (traceMatrix f (powerBasis f))`, hence to `± Resultant(f, f')`. -/
def discriminant (f : CPoly (CFrac ℚ)) : CFrac ℚ :=
  qfDet (traceMatrix f (powerBasis f))

/-- `Resultant(f, f')` for the curve `f`: `cresultantWf` of `f` against its `y`-derivative
`cderiv f`. Equal to `± discriminant f`. -/
def discResultant (f : CPoly α) : α := cresultantWf f (cderiv f)

end CPoly

/-! ### The non-radical curve `f = y² − x·y − x³` over `ℚ(x)` -/

open CPoly

/-- The non-radical curve `f = y² − x·y − x³ ∈ ℚ(x)[y]` as a `CPoly (CFrac ℚ)` `[−x³, −x, 1]`. -/
def afNonRadF : CPoly (CFrac ℚ) :=
  [qxOfNum [0, 0, 0, -1], qxOfNum [0, -1], CField.one]

/-- The generator `y` of `ℚ(x)[y]/(f)` (`afBasisElem 1 = [0, 1]`). -/
def afNonRadY : CPoly (CFrac ℚ) := afBasisElem 1

/-- `Tr(y) = x` on the non-radical curve `y² − xy − x³`: the field trace of the generator `y` is the
`ℚ(x)` value `x`, nonzero unlike a radical curve. -/
theorem afNonRad_trace_y_eq_x :
    CField.isZero (CField.sub (trace afNonRadF afNonRadY) (qxOfNum [0, 1])) = true := by native_decide

/-- `Tr(1) = 2` on the non-radical curve: the trace of `1` is `n = 2`, the `ℚ(x)` constant `2`. -/
theorem afNonRad_trace_one_eq_two :
    CField.isZero (CField.sub (trace afNonRadF [CField.one]) (qxOfNum [2])) = true := by native_decide

/-- `Tr(y²) = x² + 2x³` on the non-radical curve: reducing `y² ≡ xy + x³` and tracing gives the
`ℚ(x)` value `x² + 2x³`. -/
theorem afNonRad_trace_ysq :
    CField.isZero (CField.sub (trace afNonRadF (afMul afNonRadF afNonRadY afNonRadY))
      (qxOfNum [0, 0, 1, 2])) = true := by native_decide

/-- The trace matrix on `[1, y]` for the non-radical curve is `[[2, x], [x, x² + 2x³]]`, checked
entrywise. -/
theorem afNonRad_traceMatrix_entries :
    let T := traceMatrix afNonRadF (powerBasis afNonRadF)
    (CField.isZero (CField.sub ((T.getD 0 []).getD 0 CField.zero) (qxOfNum [2]))
      && CField.isZero (CField.sub ((T.getD 0 []).getD 1 CField.zero) (qxOfNum [0, 1]))
      && CField.isZero (CField.sub ((T.getD 1 []).getD 0 CField.zero) (qxOfNum [0, 1]))
      && CField.isZero (CField.sub ((T.getD 1 []).getD 1 CField.zero) (qxOfNum [0, 0, 1, 2])))
      = true := by native_decide

/-- The discriminant of `y² − xy − x³` is `det[Tr(ωᵢωⱼ)] = x² + 4x³`. -/
theorem afNonRad_discriminant_eq :
    CField.isZero (CField.sub (discriminant afNonRadF) (qxOfNum [0, 0, 1, 4])) = true := by
  native_decide

/-- The discriminant equals `± Resultant(f, f')` for the non-radical curve: `discriminant f +
discResultant f = 0`, so `Res(f, f') = −disc(f)`. -/
theorem afNonRad_discriminant_eq_neg_resultant :
    CField.isZero (CField.add (discriminant afNonRadF) (discResultant afNonRadF)) = true := by
  native_decide

/-! ### The trigonal curve `f = y³ + x·y + x` over `ℚ(x)` (`n = 3`) -/

/-- The trigonal curve `f = y³ + x·y + x ∈ ℚ(x)[y]` as the `CPoly (CFrac ℚ)` `[x, x, 0, 1]`. -/
def afTrigF : CPoly (CFrac ℚ) :=
  [qxOfNum [0, 1], qxOfNum [0, 1], CField.zero, CField.one]

/-- `Tr(1) = 3` on the trigonal curve: the trace of `1` is `n = 3`, the `ℚ(x)` constant `3`. -/
theorem afTrig_trace_one_eq_three :
    CField.isZero (CField.sub (trace afTrigF [CField.one]) (qxOfNum [3])) = true := by native_decide

/-- `Tr(y²) = −2x` on the trigonal curve: the Newton power-sum trace, the `ℚ(x)` value `−2x`. -/
theorem afTrig_trace_ysq :
    CField.isZero (CField.sub (trace afTrigF (afMul afTrigF (afBasisElem 1) (afBasisElem 1)))
      (qxOfNum [0, -2])) = true := by native_decide

/-- The trigonal discriminant of `y³ + xy + x` is the depressed-cubic value `−4x³ − 27x²`. -/
theorem afTrig_discriminant_eq :
    CField.isZero (CField.sub (discriminant afTrigF) (qxOfNum [0, 0, -27, -4])) = true := by
  native_decide

/-- The trigonal discriminant equals `± Resultant(f, f')`: `discriminant f + discResultant f = 0`. -/
theorem afTrig_discriminant_eq_resultant :
    CField.isZero (CField.add (discriminant afTrigF) (discResultant afTrigF)) = true := by
  native_decide

/-! ### Conservativity: on a radical curve `f = y² − ρ`, `Tr(y) = 0` -/

/-- The radical curve `f = y² − (x³ + 1) ∈ ℚ(x)[y]` as the `CPoly (CFrac ℚ)` `[−(x³+1), 0, 1]`,
i.e. `y = √(x³+1)` on the general carrier. -/
def afRadF : CPoly (CFrac ℚ) :=
  [qxOfNum [-1, 0, 0, -1], CField.zero, CField.one]

/-- `Tr(y) = 0` on the radical curve `y² − (x³+1)`: a radical generator is traceless, agreeing with
the radical carrier. -/
theorem afRad_trace_y_eq_zero :
    CField.isZero (trace afRadF (afBasisElem 1)) = true := by native_decide

/-- `afMul` agrees with the radical relation `y² = ρ`: `afMul f y y = ρ = x³ + 1` for `f = y² − ρ`. -/
theorem afRad_y_sq_eq_radicand :
    cisZero (csub (afMul afRadF (afBasisElem 1) (afBasisElem 1)) [qxOfNum [1, 0, 0, 1]])
      = true := by native_decide

/-! ### Ring sanity on the general carrier -/

/-- `y · 1 = y` on the non-radical curve: the multiplicative identity holds in `ℚ(x)[y]/(f)`. -/
theorem afNonRad_mul_one :
    cisZero (csub (afMul afNonRadF afNonRadY [CField.one]) afNonRadY) = true := by native_decide

/-- Multiplication is associative on the trigonal curve: `afMul f y (afMul f y y) = afMul f (afMul
f y y) y` in `ℚ(x)[y]/(y³+xy+x)`. -/
theorem afTrig_mul_assoc :
    cisZero (csub
        (afMul afTrigF (afBasisElem 1) (afMul afTrigF (afBasisElem 1) (afBasisElem 1)))
        (afMul afTrigF (afMul afTrigF (afBasisElem 1) (afBasisElem 1)) (afBasisElem 1)))
      = true := by native_decide

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
