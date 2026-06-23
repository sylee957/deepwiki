/-! # Source (book): The Structure of the Relational Database Model
Jan Paredaens, Paul De Bra, Marc Gyssens and Dirk Van Gucht's EATCS monograph on the theory
of the relational database model: the relational data model, query systems (relational
algebra, tuple calculus, SQL), dependency theory (functional, multivalued, join, inclusion,
generating dependencies), vertical and horizontal decompositions and normal forms, incomplete
information, the nested relational model, and updates. The `DeepWiki.RelationalDatabases`
library formalizes this theory.

Metadata for the source book that `DeepWiki.RelationalDatabases` formalizes. Its catalog files
(`Sources.Doi_10_1007_978_3_642_69956_6.*`) restate each book item — named by its book number —
and discharge it with the library. The book numbering lives here in the catalog, never in the
library. -/

namespace DeepWiki.Rdb

/-- DOI of the source book (Springer, *EATCS Monographs on Theoretical Computer Science*
Vol. 17, 1989). -/
def doi : String := "10.1007/978-3-642-69956-6"

/-- Title of the source book. -/
def title : String := "The Structure of the Relational Database Model"

/-- Publication reference of the source book (ISBN 3-540-13714-9). -/
def reference : String :=
  "Springer, EATCS Monographs on Theoretical Computer Science, Vol. 17, 1989 (ISBN 3-540-13714-9)"

/-- Authors of the source book. -/
def authors : List String := ["Jan Paredaens", "Paul De Bra", "Marc Gyssens", "Dirk Van Gucht"]

end DeepWiki.Rdb
