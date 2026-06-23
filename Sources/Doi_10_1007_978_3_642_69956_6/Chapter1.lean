import DeepWiki.RelationalDatabases.RelationalModel
import DeepWiki.RelationalDatabases.ConstraintClassification
import DeepWiki.RelationalDatabases.ExampleDatabases
import Sources.Doi_10_1007_978_3_642_69956_6.Source

/-! # Relational Database Model catalog — Chapter 1: Relational Database Model
Chapter 1 fixes the data model: primitive relation schemes and relation schemes (Defs 1.1,
1.2), tuples and relation instances (Defs 1.3, 1.4), (primitive) database schemes and
database instances (Defs 1.5–1.8), and dynamic schemes and evolutions (Defs 1.9, 1.10). §1.5
classifies constraints (tuple ⊆ relation ⊆ database, and the dynamic liftings of Fig. 1.12).

The informal *meaning* components `M` (Def 1.2) and `DM` (Def 1.6) refer to the world outside
the formalism and are not modelled.

## NOT YET FORMALIZED (audit 2026-06-23; subtractive — delete each item once it is formalized)
The chapter's substance is its definitions plus the §1.5 classification and Exercise 1.7, all
cataloged below. The remaining exercises are concrete encodings of the book's running examples
or open-ended constructions, several with informal content:
Ex 1.1: the fourth ABSTRACT constraint — `A` is the first letter of the English word for the
  `B`-value [external: no formal object for "the English word for an integer"; the other three
  constraints are done].
Ex 1.5: the domain functions `domR,…,domE` of Example 1.10 (HOTELDB) [external: the book states
  them as "obvious"; the schemes here leave domains total].
Ex 1.8: a *second* database constraint (not equivalent to relation constraints) and a relation
  constraint that is a non-trivial consequence of the two — a non-trivial single-relation
  consequence of two cross-relation constraints [deferred: construction; the core, a database
  constraint not equivalent to relation constraints, is `ex_1_8`].
Ex 1.9: the same for a *second* dynamic relation constraint and a relation-constraint consequence
  [deferred: construction; the core, a dynamic relation constraint not equivalent to relation
  constraints, is `ex_1_9`].
Ex 1.11: the consequence relations among constraints 5, 6, 7 of Exercise 1.10 [deferred: the two
  clean consequences — `c2` from `c1 ∧ c3` and `c3` from `c2 ∧ c4` — are `ex_1_11_c2_of_c1_c3` /
  `ex_1_11_c3_of_c2_c4`; the status of 5/6/7 needs counterexample instances].
Ex 1.12: a dynamic relation scheme for the convex non-intersecting quadrilaterals [deferred:
  geometric/informal content]. -/

open DeepWiki

namespace DeepWiki.Rdb

/-! ## §1.1 Relation Schemes -/

/-- **Definition 1.1** (§1.1, p.3): a *primitive relation scheme* `PRS = (Ω, Δ, dom)` — a finite
attribute set `Ω` with a domain `dom A` for each attribute (`Δ` being the finite image of `dom`). -/
abbrev def_1_1 := @DeepWiki.PrimRelScheme

/-- **Definition 1.2** (§1.1, p.3): a *relation scheme* `RS = (PRS, M, SC)` — a primitive
relation scheme, an (informal) meaning `M`, and a set `SC` of relation constraints. -/
abbrev def_1_2 := @DeepWiki.RelScheme

/-! ## §1.2 Relation Instances -/

/-- **Definition 1.3** (§1.2, p.5), the tuple: a *tuple over* `PRS` is a function `t : Ω → ⋃Δ`
with `t(A) ∈ dom(A)`. Here a row `Tuple Ω Val` is a function on `Ω`; `IsTuple` is the domain
condition `t(A) ∈ dom(A)`. -/
abbrev def_1_3_tuple := @DeepWiki.Tuple

/-- **Definition 1.3** (§1.2, p.5), the domain condition `t(A) ∈ dom(A)` of a tuple over `PRS`. -/
abbrev def_1_3_isTuple := @DeepWiki.IsTuple

/-- **Definition 1.3** (§1.2, p.5), the tuples over `PRS`: rows satisfying the domain condition. -/
abbrev def_1_3_tupleOf := @DeepWiki.TupleOf

/-- **Definition 1.3** (§1.2, p.5): a *possible relation instance* of `PRS` is a set of tuples
over `PRS`. -/
abbrev def_1_3_possibleRelInstance := @DeepWiki.PossibleRelInstance

/-- **Definition 1.4** (§1.2, p.5), the relation constraint: a boolean function on the possible
relation instances of `PRS`. -/
abbrev def_1_4_relConstraint := @DeepWiki.RelConstraint

/-- **Definition 1.4** (§1.2, p.6): a *relation instance* of `RS` is a possible relation
instance of `PRS` satisfying all relation constraints of `SC`. -/
abbrev def_1_4_relInstance := @DeepWiki.IsRelInstance

/-! ## §1.3 Database Schemes and Database Instances -/

/-- **Definition 1.5** (§1.3, p.9): a *primitive database scheme* `PDS` — a finite set of
relation schemes whose shared attributes carry equal domains (`A ∈ Ωᵢ ∩ Ωⱼ ⟹ domᵢ(A) =
domⱼ(A)`), here a finite indexed family. -/
abbrev def_1_5 := @DeepWiki.PrimDbScheme

/-- **Definition 1.6** (§1.3, p.10): a *database scheme* `DS = (PDS, DM, SDC)` — a primitive
database scheme, an (informal) meaning `DM`, and a set `SDC` of database constraints. -/
abbrev def_1_6 := @DeepWiki.DbScheme

/-- **Definition 1.7** (§1.3, p.10): a *possible database instance* of `PDS` — one possible
relation instance for each relation scheme of the database. -/
abbrev def_1_7 := @DeepWiki.PossibleDbInstance

/-- **Definition 1.8** (§1.3, p.10), the database constraint: a boolean function on the
possible database instances of `DS`. -/
abbrev def_1_8_dbConstraint := @DeepWiki.DbConstraint

/-- **Definition 1.8** (§1.3, p.10): a *database instance* of `DS` is a possible database
instance satisfying all database constraints of `SDC` (and, componentwise, each scheme's `SC`). -/
abbrev def_1_8_dbInstance := @DeepWiki.IsDbInstance

/-! ## §1.4 Dynamic Schemes and Evolutions -/

/-- **Definition 1.9** (§1.4, p.11): a *dynamic relation scheme* `DYDS = (RS, SDYC)` — a
relation scheme with a set `SDYC` of dynamic relation constraints on sequences of instances. -/
abbrev def_1_9_dynRelScheme := @DeepWiki.DynRelScheme

/-- **Definition 1.9** (§1.4, p.11): a *relation evolution* — a sequence of relation instances
of `RS` satisfying every dynamic relation constraint of `SDYC`. -/
abbrev def_1_9_relEvolution := @DeepWiki.IsRelEvolution

/-- **Definition 1.10** (§1.4, p.12): a *dynamic database scheme* `DYDS = (DS, SDYDC)` — a
database scheme with a set `SDYDC` of dynamic database constraints on sequences of instances. -/
abbrev def_1_10_dynDbScheme := @DeepWiki.DynDbScheme

/-- **Definition 1.10** (§1.4, p.12): a *database evolution* — a sequence of database instances
of `DS` satisfying every dynamic database constraint of `SDYDC`. -/
abbrev def_1_10_dbEvolution := @DeepWiki.IsDbEvolution

/-! ## §1.5 Classification of Constraints -/

/-- **Tuple constraint** (§1.5, p.13): a relation constraint checkable tuple by tuple — it holds
of an instance exactly when every tuple satisfies a fixed predicate. -/
abbrev tupleConstraint := @DeepWiki.IsTupleConstraint

/-- **Tuple constraints are downward closed** (§1.5): a subset of a satisfying instance
satisfies the constraint. -/
abbrev tupleConstraint_downward_closed := @DeepWiki.IsTupleConstraint.downward_closed

/-- **Tuple constraints are union closed** (§1.5): the union of two satisfying instances
satisfies the constraint. -/
abbrev tupleConstraint_union_closed := @DeepWiki.IsTupleConstraint.union_closed

/-- **Figure 1.12** (§1.5, p.14): relation constraints embed into database constraints — a
relation constraint on the `i`-th scheme lifts to the database constraint checking that
relation. -/
abbrev fig_1_12_relToDb := @DeepWiki.liftRelToDb

/-- **Figure 1.12** (§1.5, p.14): relation constraints embed into dynamic relation constraints —
a relation constraint lifts to the dynamic one requiring it at every time. -/
abbrev fig_1_12_relToDyn := @DeepWiki.liftRelToDyn

/-- **Figure 1.12** (§1.5, p.14): database constraints embed into dynamic database constraints —
a database constraint lifts to the dynamic one requiring it at every time. -/
abbrev fig_1_12_dbToDyn := @DeepWiki.liftDbToDyn

/-! ## §1.7 Exercises -/

/-- **Exercise 1.7** (§1.7, p.16), true kernel: the conjunction of a set of tuple constraints is
a tuple constraint — so a set of tuple constraints is equivalent to a single tuple constraint. -/
abbrev ex_1_7_conjunction := @DeepWiki.isTupleConstraint_conjunction

/-- **Exercise 1.7** (§1.7, p.16), counterexample witness: a constraint that is a consequence of
a set of tuple constraints but is itself not a tuple constraint (it breaks union-closure). -/
abbrev ex_1_7_counterexample := @DeepWiki.exists_isConsequence_not_isTupleConstraint

/-- **Exercise 1.7** (§1.7, p.16) is **false as literally stated** (erratum): *not* every
consequence of a set of tuple constraints is a tuple constraint. The book's own example uses
"consequence" in the one-directional sense (`models(SC) ⊆ models(c)`), and a consequence may
satisfy more instances than any tuple constraint — dropping union-closure. The true result is
`ex_1_7_conjunction`. -/
abbrev ex_1_7_refuted := @DeepWiki.not_forall_isConsequence_isTupleConstraint

/-! ## §1.7 Exercises — concrete example constraints -/

/-- **Exercise 1.1** (§1.7, p.16), `B < C`: every `ABSTRACT` tuple's `B`-value is below its
`C`-value. -/
abbrev ex_1_1_bLtC := @DeepWiki.abstract_bLtC

/-- **Exercise 1.1** (§1.7, p.16), distinct `B`-values: no two `ABSTRACT` tuples share a
`B`-value. -/
abbrev ex_1_1_uniqueB := @DeepWiki.abstract_uniqueB

/-- **Exercise 1.1** (§1.7, p.16), the `C`-sum bound: per tuple, the `B`-values sharing its
`C`-value sum to more than that `C`-value. -/
abbrev ex_1_1_sumB := @DeepWiki.abstract_sumB

/-- **Exercise 1.2** (§1.7, p.16): every roommaid is responsible for exactly four rooms
(`ROOMMAIDS`). -/
abbrev ex_1_2_fourRooms := @DeepWiki.roommaids_fourRooms

/-- **Exercise 1.2** (§1.7, p.16): no two roommaids are responsible for the same room. -/
abbrev ex_1_2_uniqueRoom := @DeepWiki.roommaids_uniqueRoom

/-- **Exercise 1.3** (§1.7, p.16): the `noremove` dynamic relation constraint — a room with a
bath never loses it from one instance to the next. -/
abbrev ex_1_3_noremove := @DeepWiki.rooms_noremove

/-- **Exercise 1.8** (§1.7, p.16), core: the inclusion database constraint `R.A ⊆ S.A` is *not*
equivalent to relation constraints — some database constraints genuinely relate two relations and
cannot be expressed by constraints on the individual relations. -/
abbrev ex_1_8 := @DeepWiki.ex18_not_relationConstraintEquiv

/-- **Exercise 1.8** (§1.7, p.16): the notion underlying it — a database constraint is *equivalent
to relation constraints* when it factors as a conjunction of one constraint per relation. -/
abbrev ex_1_8_relationConstraintEquiv := @DeepWiki.IsRelationConstraintEquiv

/-- **Exercise 1.9** (§1.7, p.16), core: the monotone dynamic relation constraint (the relation
only grows) is *not* equivalent to relation constraints — it relates consecutive instances, so no
per-instance constraint can capture it. -/
abbrev ex_1_9 := @DeepWiki.ex18DynMono_not_relationConstraintEquiv

/-- **Exercise 1.9** (§1.7, p.16): the underlying notion — a dynamic relation constraint is
*equivalent to relation constraints* when it factors as a per-instance constraint at every step. -/
abbrev ex_1_9_relationConstraintEquivDyn := @DeepWiki.IsRelationConstraintEquivDyn

/-- **Exercise 1.10** (§1.7, p.17): the `THIRSTY` database instance — the relations `LIKES`,
`VISITS`, `SERVES`. -/
abbrev ex_1_10_thirsty := @DeepWiki.ThirstyInst

/-- **Exercise 1.10** (§1.7, p.17), constraint 1 (`SDC`): every drinker visits only bars serving
a beer he likes. -/
abbrev ex_1_10_c1 := @DeepWiki.thirsty_c1

/-- **Exercise 1.10** (§1.7, p.17), constraint 2 (`SC_S`): each bar serves at least one beer. -/
abbrev ex_1_10_c2 := @DeepWiki.thirsty_c2

/-- **Exercise 1.10** (§1.7, p.17), constraint 3 (`SC_V`): each bar has at least one visitor. -/
abbrev ex_1_10_c3 := @DeepWiki.thirsty_c3

/-- **Exercise 1.10** (§1.7, p.17), constraint 4 (`SDC`): each bar only serves beers liked by some
of its visitors. -/
abbrev ex_1_10_c4 := @DeepWiki.thirsty_c4

/-- **Exercise 1.10** (§1.7, p.17), constraint 5 (`SDC`): two drinkers visiting one bar share a
liked beer served there. -/
abbrev ex_1_10_c5 := @DeepWiki.thirsty_c5

/-- **Exercise 1.10** (§1.7, p.17), constraint 6 (`SDC`): a non-visited bar serves some beer the
drinker dislikes. -/
abbrev ex_1_10_c6 := @DeepWiki.thirsty_c6

/-- **Exercise 1.10** (§1.7, p.17), constraint 7 (`SDC`): liking a beer served in a bar visited by
another drinker forces a common bar. -/
abbrev ex_1_10_c7 := @DeepWiki.thirsty_c7

/-- **Exercise 1.4** (§1.7, p.16): a `HOTELDB` database instance (the relations relevant to the
`SDC`/`SDYDC` constraints). -/
abbrev ex_1_4_hotelDb := @DeepWiki.HotelDbInst

/-- **Exercise 1.4** (§1.7, p.16), SDYDC constraint 1: no visitor is deleted while `STAYS` still
holds information about him. -/
abbrev ex_1_4_noDeleteWithStay := @DeepWiki.sdydc_noDeleteWithStay

/-- **Exercise 1.4** (§1.7, p.16), SDYDC constraint 2: a visitor's phone bills are all paid when
he leaves the hotel. -/
abbrev ex_1_4_billsPaidOnLeave := @DeepWiki.sdydc_billsPaidOnLeave

/-- **Exercise 1.4** (§1.7, p.16), SDYDC constraint 3: a bath is never removed from a room (rooms
may be annulled). -/
abbrev ex_1_4_noBathRemoval := @DeepWiki.sdydc_noBathRemoval

/-- **Exercise 1.4** (§1.7, p.16), SDYDC constraint 4: only the stay with the oldest `LEAV-DATE`
may be removed from `STAYS`. -/
abbrev ex_1_4_onlyOldestRemoved := @DeepWiki.sdydc_onlyOldestRemoved

/-- **Exercise 1.11** (§1.7, p.17): THIRSTY constraint 2 is a consequence of constraints 1 and 3
(every bar has a visitor, who likes a beer served there, so the bar serves a beer). -/
abbrev ex_1_11_c2_of_c1_c3 := @DeepWiki.thirsty_c2_of_c1_c3

/-- **Exercise 1.11** (§1.7, p.17): THIRSTY constraint 3 is a consequence of constraints 2 and 4
(every bar serves a beer, liked by a visitor, so the bar has a visitor). -/
abbrev ex_1_11_c3_of_c2_c4 := @DeepWiki.thirsty_c3_of_c2_c4

/-! ### Exercise 1.6 — the `HOTELDB` constraints (Example 1.10).
`SC_C` is Exercise 1.2 (`ex_1_2_*`) and `SDYDC` is Exercise 1.4 (`ex_1_4_*`). -/

/-- **Exercise 1.6** (§1.7, p.16), `HOTELDB` six-relation database instance. -/
abbrev ex_1_6_hotelDb := @DeepWiki.HotelDbInst

/-- **Exercise 1.6**, `SC_R`/1: every room has a different number. -/
abbrev ex_1_6_scR_uniqueNumber := @DeepWiki.rooms_uniqueNumber

/-- **Exercise 1.6**, `SC_R`/2 (tuple constraint): eight floors, first room-number digit = floor. -/
abbrev ex_1_6_scR_floorDigit := @DeepWiki.rooms_floorDigit

/-- **Exercise 1.6**, `SC_R`/3 (tuple constraint): every room on floor 2 has a bath. -/
abbrev ex_1_6_scR_floor2Bath := @DeepWiki.rooms_floor2Bath

/-- **Exercise 1.6**, `SC_R`/4 (tuple constraint): a room with a bath costs over 150. -/
abbrev ex_1_6_scR_bathRate := @DeepWiki.rooms_bathRate

/-- **Exercise 1.6**, `SC_R`/5: no floor has more than 20 rooms. -/
abbrev ex_1_6_scR_floorCount := @DeepWiki.rooms_floorCount

/-- **Exercise 1.6**, `SC_R`/6: the average number of beds per room is at least 1.60. -/
abbrev ex_1_6_scR_bedAverage := @DeepWiki.rooms_bedAverage

/-- **Exercise 1.6**, `SC_V`/1: every visitor has a different number. -/
abbrev ex_1_6_scV_uniqueNumber := @DeepWiki.visitors_uniqueNumber

/-- **Exercise 1.6**, `SC_V`/2: same city implies same country. -/
abbrev ex_1_6_scV_cityCountry := @DeepWiki.visitors_cityCountry

/-- **Exercise 1.6**, `SC_S`/1: a visitor leaves later than he arrives. -/
abbrev ex_1_6_scS_leaveAfterArrival := @DeepWiki.stays_leaveAfterArrival

/-- **Exercise 1.6**, `SC_S`/2: a visitor cannot arrive a second time while still staying. -/
abbrev ex_1_6_scS_noSecondArrival := @DeepWiki.stays_noSecondArrival

/-- **Exercise 1.6**, `SC_P`: no two phone bills agree on room number, time and date. -/
abbrev ex_1_6_scP_key := @DeepWiki.phoneBills_key

/-- **Exercise 1.6**, `SC_E`: all employees have a different number. -/
abbrev ex_1_6_scE_uniqueNumber := @DeepWiki.employees_uniqueNumber

/-- **Exercise 1.6**, `SDC`/1: one roommaid is responsible for each hotel room. -/
abbrev ex_1_6_sdc_oneRoommaidPerRoom := @DeepWiki.sdc_oneRoommaidPerRoom

/-- **Exercise 1.6**, `SDC`/2: the rooms where visitors stay are hotel rooms. -/
abbrev ex_1_6_sdc_staysRoomsAreHotel := @DeepWiki.sdc_staysRoomsAreHotel

/-- **Exercise 1.6**, `SDC`/3: phone-bill room numbers are hotel rooms. -/
abbrev ex_1_6_sdc_phoneRoomsAreHotel := @DeepWiki.sdc_phoneRoomsAreHotel

/-- **Exercise 1.6**, `SDC`/4: a phone call from a room means it was occupied that date. -/
abbrev ex_1_6_sdc_phoneImpliesOccupied := @DeepWiki.sdc_phoneImpliesOccupied

/-- **Exercise 1.6**, `SDC`/5: each roommaid is an employee whose job is roommaid. -/
abbrev ex_1_6_sdc_roommaidIsEmployee := @DeepWiki.sdc_roommaidIsEmployee

end DeepWiki.Rdb
