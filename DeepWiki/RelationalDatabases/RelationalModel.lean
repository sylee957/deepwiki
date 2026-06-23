import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert

/-! # The relational database model
The data model of the relational theory: primitive relation schemes and relation schemes,
tuples and relation instances, (primitive) database schemes and database instances, and the
dynamic (relation/database) schemes governing how instances evolve in time.

Attributes range over a type `Att` and values over a single universe `Val`; an attribute's
domain is a *set* of admissible values (the book's `dom : Ω → Δ`, with the finite set of
domains `Δ` recovered as the image of `dom`). The informal real-world *meaning* components of
a relation scheme and a database scheme refer to the world outside the formalism and are not
modelled. -/

namespace DeepWiki

universe u v w

variable {Att : Type u} {Val : Type v}

/-- A *primitive relation scheme* `(Ω, dom)`: a finite attribute set together with a domain
(a set of admissible values) for each attribute. -/
structure PrimRelScheme (Att : Type u) (Val : Type v) where
  /-- The finite attribute set `Ω`. -/
  attrs : Finset Att
  /-- The domain assignment `dom`: the admissible values of each attribute. -/
  dom : Att → Set Val

/-- A *row* over a finite attribute set `Ω`: one value for each attribute of `Ω`. -/
abbrev Tuple (Ω : Finset Att) (Val : Type v) : Type _ := {a : Att // a ∈ Ω} → Val

/-- The domain condition on a row `t` over a primitive relation scheme `P`: every entry lies
in its attribute's domain. -/
def IsTuple (P : PrimRelScheme Att Val) (t : Tuple P.attrs Val) : Prop :=
  ∀ a : {a // a ∈ P.attrs}, t a ∈ P.dom a.val

/-- The *tuples over* a primitive relation scheme `P`: rows respecting every attribute's
domain. -/
abbrev TupleOf (P : PrimRelScheme Att Val) : Type _ := {t : Tuple P.attrs Val // IsTuple P t}

/-- A *possible relation instance* of `P`: a set of tuples over `P`. -/
abbrev PossibleRelInstance (P : PrimRelScheme Att Val) : Type _ := Set (TupleOf P)

/-- A *relation constraint* of `P`: a boolean condition on possible relation instances, here a
predicate. -/
abbrev RelConstraint (P : PrimRelScheme Att Val) : Type _ := PossibleRelInstance P → Prop

/-- A *relation scheme* `(PRS, SC)` (the informal meaning component is omitted): a primitive
relation scheme together with its set `SC` of relation constraints. -/
structure RelScheme (Att : Type u) (Val : Type v) where
  /-- The underlying primitive relation scheme `PRS`. -/
  prim : PrimRelScheme Att Val
  /-- The set `SC` of relation constraints. -/
  constraints : Set (RelConstraint prim)

/-- `r` is a *relation instance* of the relation scheme `R`: a possible relation instance of
`R.prim` satisfying every constraint in `R.constraints`. -/
def IsRelInstance (R : RelScheme Att Val) (r : PossibleRelInstance R.prim) : Prop :=
  ∀ c ∈ R.constraints, c r

/-- A *primitive database scheme*: a finite indexed family of relation schemes whose shared
attributes carry equal domains, so the domain of an attribute is well defined across the
whole database. -/
structure PrimDbScheme (ι : Type w) (Att : Type u) (Val : Type v) [Fintype ι] where
  /-- The relation schemes of the database, indexed by `ι`. -/
  scheme : ι → RelScheme Att Val
  /-- Domain compatibility: an attribute shared by two schemes has the same domain in both. -/
  compat : ∀ i j (a : Att), a ∈ (scheme i).prim.attrs → a ∈ (scheme j).prim.attrs →
    (scheme i).prim.dom a = (scheme j).prim.dom a

/-- A *possible database instance* of a primitive database scheme `P`: one possible relation
instance for each relation scheme of the family. -/
abbrev PossibleDbInstance {ι : Type w} [Fintype ι] (P : PrimDbScheme ι Att Val) : Type _ :=
  (i : ι) → PossibleRelInstance (P.scheme i).prim

/-- A *database constraint*: a boolean condition on possible database instances, here a
predicate. -/
abbrev DbConstraint {ι : Type w} [Fintype ι] (P : PrimDbScheme ι Att Val) : Type _ :=
  PossibleDbInstance P → Prop

/-- A *database scheme* `(PDS, SDC)` (the informal meaning component is omitted): a primitive
database scheme together with its set `SDC` of database constraints. -/
structure DbScheme (ι : Type w) (Att : Type u) (Val : Type v) [Fintype ι] where
  /-- The underlying primitive database scheme `PDS`. -/
  prim : PrimDbScheme ι Att Val
  /-- The set `SDC` of database constraints. -/
  dbConstraints : Set (DbConstraint prim)

/-- `d` is a *database instance* of the database scheme `D`: a possible database instance
satisfying every database constraint of `SDC` and, componentwise, each relation scheme's own
constraints. -/
def IsDbInstance {ι : Type w} [Fintype ι] (D : DbScheme ι Att Val)
    (d : PossibleDbInstance D.prim) : Prop :=
  (∀ c ∈ D.dbConstraints, c d) ∧ ∀ i, IsRelInstance (D.prim.scheme i) (d i)

/-- A *dynamic relation constraint*: a boolean condition on sequences of relation instances,
here a predicate. -/
abbrev DynRelConstraint (R : RelScheme Att Val) : Type _ :=
  (ℕ → PossibleRelInstance R.prim) → Prop

/-- A *dynamic relation scheme* `(RS, SDYC)`: a relation scheme together with a set of dynamic
relation constraints on its sequences of instances. -/
structure DynRelScheme (Att : Type u) (Val : Type v) where
  /-- The underlying relation scheme `RS`. -/
  base : RelScheme Att Val
  /-- The set `SDYC` of dynamic relation constraints. -/
  dynConstraints : Set (DynRelConstraint base)

/-- `rs` is a *relation evolution* of the dynamic relation scheme `D`: a sequence of relation
instances of `D.base` satisfying every dynamic relation constraint of `SDYC`. -/
def IsRelEvolution (D : DynRelScheme Att Val)
    (rs : ℕ → PossibleRelInstance D.base.prim) : Prop :=
  (∀ n, IsRelInstance D.base (rs n)) ∧ ∀ c ∈ D.dynConstraints, c rs

/-- A *dynamic database constraint*: a boolean condition on sequences of database instances,
here a predicate. -/
abbrev DynDbConstraint {ι : Type w} [Fintype ι] (D : DbScheme ι Att Val) : Type _ :=
  (ℕ → PossibleDbInstance D.prim) → Prop

/-- A *dynamic database scheme* `(DS, SDYDC)`: a database scheme together with a set of dynamic
database constraints on its sequences of instances. -/
structure DynDbScheme (ι : Type w) (Att : Type u) (Val : Type v) [Fintype ι] where
  /-- The underlying database scheme `DS`. -/
  base : DbScheme ι Att Val
  /-- The set `SDYDC` of dynamic database constraints. -/
  dynConstraints : Set (DynDbConstraint base)

/-- `ds` is a *database evolution* of the dynamic database scheme `D`: a sequence of database
instances of `D.base` satisfying every dynamic database constraint of `SDYDC`. -/
def IsDbEvolution {ι : Type w} [Fintype ι] (D : DynDbScheme ι Att Val)
    (ds : ℕ → PossibleDbInstance D.base.prim) : Prop :=
  (∀ n, IsDbInstance D.base (ds n)) ∧ ∀ c ∈ D.dynConstraints, c ds

end DeepWiki
