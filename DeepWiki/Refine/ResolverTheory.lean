import DeepWiki.Refine.Parametricity.Intrinsic.Core
import DeepWiki.Refine.Gcd

/-! # The first-order resolver as a multisorted parametricity fragment

Multisorted relational types identify the resolver's nested respectful arrows with the arrow fragment
of parametricity. Concrete polynomial and gcd witnesses exhibit both uniform and mixed relations. -/

namespace DeepWiki.Refine

universe u v w

/-- Multisorted simple types whose base nodes select possibly different relations. -/
inductive SortedType (Index : Type u) where
  /-- A base type selected by an index. -/
  | base (index : Index)
  /-- A function type between two sorted types. -/
  | arrow (domain codomain : SortedType Index)

/-- Interpret a multisorted type using a family of carriers. -/
@[reducible] def SortedType.interpret {Index : Type u} (Carrier : Index → Type v) :
    SortedType Index → Type v
  | .base index => Carrier index
  | .arrow domain codomain => domain.interpret Carrier → codomain.interpret Carrier

/-- Interpret a multisorted type relationally from one relation at each base index. -/
@[reducible] def SortedType.rel {Index : Type u} {Left : Index → Type v} {Right : Index → Type w}
    (Relation : ∀ index, Left index → Right index → Prop) :
    (type : SortedType Index) → type.interpret Left → type.interpret Right → Prop
  | .base index => Relation index
  | .arrow domain codomain => fun f g =>
      ∀ left right, domain.rel Relation left right → codomain.rel Relation (f left) (g right)

/-- A sorted base relation is exactly its selected relation. -/
theorem SortedType.rel_base_iff {Index : Type u} {Left : Index → Type v}
    {Right : Index → Type w} (Relation : ∀ index, Left index → Right index → Prop)
    (index : Index) (left : Left index) (right : Right index) :
    (SortedType.base index).rel Relation left right ↔ Relation index left right :=
  Iff.rfl

/-- A sorted arrow relation is exactly the existing respectful arrow. -/
theorem SortedType.rel_arrow_iff {Index : Type u} {Left : Index → Type v}
    {Right : Index → Type w} (Relation : ∀ index, Left index → Right index → Prop)
    (domain codomain : SortedType Index)
    (f : domain.interpret Left → codomain.interpret Left)
    (g : domain.interpret Right → codomain.interpret Right) :
    (SortedType.arrow domain codomain).rel Relation f g ↔
      Respectful (domain.rel Relation) (codomain.rel Relation) f g :=
  Iff.rfl

/-- Application in the multisorted relational interpretation is the proof underneath `Refines.app`. -/
theorem SortedType.relApp {Index : Type u} {Left : Index → Type v} {Right : Index → Type w}
    {Relation : ∀ index, Left index → Right index → Prop}
    {domain codomain : SortedType Index}
    {f : domain.interpret Left → codomain.interpret Left}
    {g : domain.interpret Right → codomain.interpret Right}
    (functionWitness : (SortedType.arrow domain codomain).rel Relation f g)
    {left : domain.interpret Left} {right : domain.interpret Right}
    (argumentWitness : domain.rel Relation left right) :
    codomain.rel Relation (f left) (g right) :=
  functionWitness left right argumentWitness

/-- `Refines` at a selected base relation is merely a class wrapper around the sorted relation. -/
theorem refines_iff_sortedBase {Index : Type u} {Left : Index → Type v}
    {Right : Index → Type w} {Relation : ∀ index, Left index → Right index → Prop}
    {index : Index} {left : Left index} {right : Right index} :
    Refines (Relation index) left right ↔ (SortedType.base index).rel Relation left right :=
  ⟨fun h => h.prf, fun h => ⟨h⟩⟩

/-- The two polynomial relations used by the resolver. -/
inductive PolynomialRelationKind where
  /-- Exact equality after denotation. -/
  | exact
  /-- Equality only up to a polynomial unit. -/
  | associated

/-- Both polynomial relation indices use dense polynomials on the concrete side. -/
abbrev polynomialConcreteCarrier (R : Type u) [Field R] [DecidableEq R]
    (_ : PolynomialRelationKind) :=
  DeepWiki.CAlgebra.DensePoly R

/-- Both polynomial relation indices use Mathlib polynomials on the abstract side. -/
abbrev polynomialAbstractCarrier (R : Type u) [Field R] [DecidableEq R]
    (_ : PolynomialRelationKind) :=
  Polynomial R

/-- Relation assignment matching the exact and associated resolver relations. -/
def polynomialRelation {R : Type u} [Field R] [DecidableEq R] :
    ∀ kind, polynomialConcreteCarrier R kind → polynomialAbstractCarrier R kind → Prop
  | .exact => RPoly (R := R)
  | .associated => RPolyU (R := R)

/-- The nested respectful-arrow shape of the mixed-relation gcd witness. -/
abbrev polynomialGcdType : SortedType PolynomialRelationKind :=
  .arrow (.base .exact) (.arrow (.base .exact) (.base .associated))

/-- The nested respectful-arrow shape of an exact binary polynomial operation. -/
abbrev polynomialBinaryExactType : SortedType PolynomialRelationKind :=
  .arrow (.base .exact) (.arrow (.base .exact) (.base .exact))

variable {R : Type u} [Field R] [DecidableEq R]

example : polynomialGcdType.rel (polynomialRelation (R := R))
    (fun p q : DeepWiki.CAlgebra.DensePoly R => DeepWiki.CAlgebra.DensePoly.gcd p q)
    (fun p q : Polynomial R => EuclideanDomain.gcd p q) :=
  refines_gcd.prf

example : polynomialBinaryExactType.rel (polynomialRelation (R := R))
    ((· * ·) : DeepWiki.CAlgebra.DensePoly R → _ → _)
    ((· * ·) : Polynomial R → _ → _) :=
  refines_mul.prf

end DeepWiki.Refine
