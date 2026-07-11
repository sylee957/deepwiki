import DeepWiki.SymbolicIntegration.Engine.Algebraic.BareissEngine.Polynomial
import DeepWiki.ComputableAlgebra.PolyGcdAlgorithms

/-! # Fraction-free rational-function Bareiss wrappers

The representation-independent wrappers `qfDet`/`qfAdjugate`/`qfInv`/`qfSolve` clear a represented
fraction matrix to a common polynomial denominator and run the generic polynomial Bareiss engine. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CFrac

universe u

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
variable {F : (α : Type u) → [CField α] → Type u} [CFrac F P] [LawfulCFrac F P]
variable {α : Type u} [CField α] [CPolyGcd P α] [CFieldDomain α P]

/-! ### Denominator-combining helpers -/

/-- The common denominator of a represented-fraction row, formed from its monic denominators by lcm. -/
def qfRowDen (row : List (F α)) : P α :=
  row.foldl (fun acc z => CPoly.lcm acc (CPolyEngine.cmonic (CFrac.den z))) CPoly.one

/-- The common denominator of a represented-fraction matrix, formed by combining its row denominators. -/
def qfMatDen (M : List (List (F α))) : P α :=
  M.foldl (fun acc row => CPoly.lcm acc (qfRowDen row)) CPoly.one

/-! ### Clearing represented-fraction rows and matrices -/

/-- Clear one represented fraction by `D`, returning `num(z) * (D / den(z))`. -/
def qfClearEntry (D : P α) (z : F α) : P α :=
  CPolyEngine.mul (CFrac.num z) (CPolyEuclidean.div D (CFrac.den z))

/-- Clear a represented-fraction row, returning its polynomial entries and clearing factor. -/
def qfClearRow (row : List (F α)) : List (P α) × P α :=
  let D := qfRowDen row
  (row.map (qfClearEntry D), D)

/-- Clear a represented-fraction matrix by one common denominator and return that clearing factor. -/
def qfClearMatrix (M : List (List (F α))) : List (List (P α)) × P α :=
  let D := qfMatDen M
  (M.map (fun row => row.map (qfClearEntry D)), D)

/-! ### Fraction-free determinant, adjugate, inverse, and solve -/

/-- The fraction-free determinant of a represented-fraction matrix, divided back by the clearing power. -/
def qfDet (M : List (List (F α))) : F α :=
  let n := M.length
  let (M', D) := qfClearMatrix M
  let detPoly := CPoly.bareissDet M'
  let Dn := CPoly.cpow D n
  CCommRing.mul (CFrac.ofPoly (F := F) detPoly) (CField.inv (CFrac.ofPoly (F := F) Dn))

/-- Return the polynomial adjugate of a cleared represented-fraction matrix and its clearing factor. -/
def qfAdjugate (M : List (List (F α))) : List (List (P α)) × P α :=
  let (M', D) := qfClearMatrix M
  (CPoly.bareissAdjugate M', D)

/-- Represent the inverse with the cleared determinant as one denominator and scaled adjugate numerators. -/
def qfInv (M : List (List (F α))) : P α × List (List (P α)) :=
  let (M', D) := qfClearMatrix M
  let detPoly := CPoly.bareissDet M'
  let adjPoly := CPoly.bareissAdjugate M'
  (detPoly, adjPoly.map (fun row => row.map (fun e => CPolyEngine.mul D e)))

/-- Read one entry of the fraction-free inverse representation back into the fraction carrier. -/
def qfInvEntry (M : List (List (F α))) (i j : ℕ) : F α :=
  let dn := qfInv M
  CCommRing.mul (CFrac.ofPoly (F := F) (CPoly.polyMatGet dn.2 i j))
    (CField.inv (CFrac.ofPoly (F := F) dn.1))

/-- Clear a represented-fraction system and run the representation-independent Bareiss Cramer solve. -/
def qfSolve (M : List (List (F α))) (b : List (F α)) : P α × List (P α) :=
  let (M', D) := qfClearMatrix M
  let b' := b.map (qfClearEntry D)
  CPoly.bareissSolve M' b'

end CFrac

end DeepWiki.SymbolicIntegration
