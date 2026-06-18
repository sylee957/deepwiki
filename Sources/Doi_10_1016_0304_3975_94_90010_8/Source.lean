/-! # Source (paper): A theory of timed automata
The foundational timed-automata paper. The Reactive Systems book (Aceto–Ingólfsdóttir–
Larsen–Srba, ch. 11) presents timed automata and the region graph but defers the region
construction — region equivalence, the region automaton, and the **time-successor** of a
clock region (Def 4.3/4.6, §4.2–4.3) — to this paper. Its catalog files point at the
`DeepWiki.ReactiveSystems` region machinery derived from it. -/

namespace DeepWiki.Ad

/-- DOI of the source paper (also ICALP 1990, LNCS 443, pp. 322–335, as
"Automata for modeling real-time systems"). -/
def doi : String := "10.1016/0304-3975(94)90010-8"

/-- Title of the source paper. -/
def title : String := "A theory of timed automata"

/-- Journal reference of the source paper. -/
def reference : String := "Theoretical Computer Science 126(2):183–235, 1994"

/-- Authors of the source paper. -/
def authors : List String := ["Rajeev Alur", "David L. Dill"]

end DeepWiki.Ad
