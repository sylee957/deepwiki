/-! # Source-catalog vocabulary
Bibliographic scaffolding shared by every source catalog. A `SourceRef`
points at one item — definition, theorem, exercise, remark — of a source
document, by DOI, location, label, and page. A source's catalog file
imports the relevant `DeepWiki` library declarations and, for each
formalized item, pairs its `SourceRef` with a restatement discharged by
the library: the book-faithful statement is then machine-checked against
the general theory, and the source's own numbering lives here in the
catalog, never in the library. -/

namespace DeepWiki.Catalog

/-- The kind of a catalogued source item (abbreviated to avoid the
reserved `definition`/`theorem`/`lemma`/`example` keywords). -/
inductive ItemKind where
  /-- A definition. -/
  | defn
  /-- A theorem. -/
  | thm
  /-- A proposition. -/
  | prop
  /-- A lemma. -/
  | lem
  /-- A corollary. -/
  | cor
  /-- A worked example. -/
  | exmp
  /-- An exercise. -/
  | exercise
  /-- A remark or piece of trivia. -/
  | remark
  deriving DecidableEq, Repr

/-- A bibliographic reference to one item of a source document. The
source's own numbering (`label`) and section (`location`) are recorded
here, decoupling the general library from any particular source. -/
structure SourceRef where
  /-- The source's DOI. -/
  doi : String
  /-- The location within the source, e.g. a section number. -/
  location : String
  /-- The source's own label for the item, e.g. `"Proposition 10.1"`. -/
  label : String
  /-- The kind of item. -/
  kind : ItemKind
  /-- The page in the source, if known. -/
  page : Option Nat := none
  deriving Repr

end DeepWiki.Catalog
