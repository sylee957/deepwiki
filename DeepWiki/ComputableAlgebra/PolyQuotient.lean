import DeepWiki.ComputableAlgebra.PolyEuclidean
import DeepWiki.ComputableAlgebra.PolyEngine

/-! # Representation-independent polynomial quotient operations

Canonical representatives, modular multiplication, power bases, multiplication matrices, and traces,
selected through `CPolyEngine` and `CPolyEuclidean`. -/

namespace DeepWiki.SymbolicIntegration

universe u v

namespace CPoly

/-- Reduce a represented polynomial modulo another using the selected Euclidean remainder. -/
def reduceMod {P : Type u → Type u} [CPoly P] [CPolyEuclidean P]
    {α : Type u} [CField α] (modulus p : P α) : P α :=
  CPolyEuclidean.mod p modulus

/-- Multiply represented polynomials and reduce the product modulo a polynomial. -/
def mulMod {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
    {α : Type u} [CField α] (modulus a b : P α) : P α :=
  reduceMod modulus (CPolyEngine.mul a b)

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
  {α : Type u} [CField α]

/-- The `i`-th represented power-basis element `yⁱ`. -/
def afBasisElem (i : ℕ) : P α := CPolyEngine.monomial CCommRing.one i

/-- The multiplication-by-`w` matrix on the represented power basis modulo `f`. -/
def multMatrix (f w : P α) : List (List α) :=
  let n := CPolyEngine.cdeg f
  (List.range n).map (fun r =>
    (List.range n).map (fun c => CPoly.coeff (mulMod f w (afBasisElem c)) r))

/-- The trace of multiplication by `w` on the represented power basis modulo `f`. -/
def trace (f w : P α) : α :=
  let n := CPolyEngine.cdeg f
  (List.range n).foldl (fun acc i =>
    CCommRing.add acc (CPoly.coeff (mulMod f w (afBasisElem i)) i)) CCommRing.zero

/-- The Gram matrix of the trace form on a represented quotient basis. -/
def traceMatrix (f : P α) (basis : List (P α)) : List (List α) :=
  basis.map (fun wi => basis.map (fun wj => trace f (mulMod f wi wj)))

/-- The represented power basis `[1, y, ..., y^(deg f - 1)]` modulo `f`. -/
def powerBasis (f : P α) : List (P α) :=
  (List.range (CPolyEngine.cdeg f)).map afBasisElem

variable [LawfulCPolyEuclidean.{u,v} P]
  [CFieldSpec.{u,v} α]

omit [CPolyEngine P] in
/-- Reduction modulo a nonzero polynomial produces a representative of smaller degree. -/
theorem reduceMod_degree_lt (modulus p : P α) (hmod : CPoly.toPoly modulus ≠ 0) :
    (CPoly.toPoly (reduceMod modulus p)).degree < (CPoly.toPoly modulus).degree :=
  LawfulCPolyEuclidean.mod_degree_lt p modulus hmod

omit [CPolyEngine P] in
/-- A reduced representative differs from its input by a multiple of the modulus. -/
theorem toPoly_reduceMod_sub (modulus p : P α) (hmod : CPoly.toPoly modulus ≠ 0) :
    CPoly.toPoly (reduceMod modulus p) - CPoly.toPoly p =
      -(CPoly.toPoly (CPolyEuclidean.div p modulus) * CPoly.toPoly modulus) := by
  have hspec := LawfulCPolyEuclidean.divmod_spec (P := P) p modulus hmod
  change CPoly.toPoly (CPolyEuclidean.mod p modulus) - CPoly.toPoly p = _
  rw [hspec]
  ring

variable [LawfulCPolyEngine.{u,v} P]

omit [CPolyEuclidean P] [LawfulCPolyEuclidean P] in
/-- The first represented power-basis element denotes the polynomial variable. -/
theorem toPoly_afBasisElem_one :
    CPoly.toPoly (afBasisElem (P := P) 1 : P α) =
      (Polynomial.X : Polynomial (CRingSpec.R α)) := by
  rw [afBasisElem, LawfulCPolyEngine.toPoly_monomial, pow_one]
  rw [CRingSpec.toR_one]
  simp

attribute [denote] toPoly_afBasisElem_one

/-- Modular multiplication differs from ordinary multiplication by a multiple of the modulus. -/
theorem toPoly_mulMod_sub (modulus a b : P α) (hmod : CPoly.toPoly modulus ≠ 0) :
    CPoly.toPoly (mulMod modulus a b) - CPoly.toPoly a * CPoly.toPoly b =
      -(CPoly.toPoly (CPolyEuclidean.div (CPolyEngine.mul a b) modulus) *
        CPoly.toPoly modulus) := by
  simpa only [mulMod, LawfulCPolyEngine.toPoly_mul] using
    toPoly_reduceMod_sub modulus (CPolyEngine.mul a b) hmod

end CPoly

end DeepWiki.SymbolicIntegration
