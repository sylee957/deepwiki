/-! # Source (lecture notes): The Algebraic Theory of Integration
Erich Kaltofen's draft lecture notes (course CSC 2429 *Topics in Theory of Computation*, University of
Toronto, Fall 1983; transcribed by Markus Hitz; based in part on B. F. Caviness's AMS short-course
notes, 1980). The `DeepWiki.SymbolicIntegration` library takes from them the **Weak Liouville Theorem**
(Thm 3.2) and the two monomial degree lemmas (Lemmas 3.1a/3.1b) underpinning its structural-completeness
spine.

**No DOI.** These are unpublished draft lecture notes — no journal, publisher, or DOI. The catalog folder
is named by a descriptive slug (`Kaltofen_AlgebraicIntegration`) rather than a sanitized DOI, per the
no-stable-identifier convention. The author's short slug is the declaration namespace (`DeepWiki.Kal`);
the Thm/Lemma number of each cataloged item lives in the catalog docstrings, never in the library. -/

namespace DeepWiki.Kal

/-- No DOI: unpublished draft lecture notes (NCSU; course CSC 2429, U. Toronto, Fall 1983). The
descriptive slug is the stable identifier used for the catalog folder. -/
def doi : Option String := none

/-- Title of the source lecture notes. -/
def title : String := "The Algebraic Theory of Integration"

/-- Publication reference of the source lecture notes. -/
def reference : String :=
  "Draft lecture notes (no DOI), course CSC 2429, University of Toronto, Fall 1983"

/-- Author of the source lecture notes. -/
def authors : List String := ["Erich Kaltofen"]

end DeepWiki.Kal
