/-! # Source (book): Integration in Finite Terms — Fundamental Sources
The Raab–Singer edited volume (Springer, *Texts & Monographs in Symbolic Computation*, 2022)
reprinting the four foundational texts on integration in finite terms with commentaries. The
`DeepWiki.SymbolicIntegration` library takes the **structural completeness** (Liouville's theorem)
spine from its first reprint, **Maxwell Rosenlicht's "Integration in Finite Terms"** (Amer. Math.
Monthly 79 (1972), 963–972), which gives the purely-algebraic proof of Liouville's theorem.

The catalog folder is named by the sanitized book DOI (`Doi_10_1007_978_3_030_98767_1`); each reprinted
chapter has its own chapter DOI `…_<n>` (Rosenlicht is `…_1`), recorded in that chapter's catalog file.
The chapter author's short slug is the declaration namespace (`DeepWiki.Ros` for Rosenlicht), the
chapter §/page lives in the catalog docstrings, never in the library. -/

namespace DeepWiki.Ros

/-- DOI of the source book (Springer, *Texts & Monographs in Symbolic Computation*, 2022). -/
def doi : String := "10.1007/978-3-030-98767-1"

/-- Title of the source book. -/
def title : String := "Integration in Finite Terms: Fundamental Sources"

/-- Publication reference of the source book (ISBN 978-3-030-98766-4 print, 978-3-030-98767-1 eBook). -/
def reference : String :=
  "Texts & Monographs in Symbolic Computation, Springer, 2022 (ISBN 978-3-030-98766-4)"

/-- Editors of the source book. -/
def editors : List String := ["Clemens G. Raab", "Michael F. Singer"]

end DeepWiki.Ros
