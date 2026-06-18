import DeepWiki.ReactiveSystems.CharacteristicFormulaTimed
import DeepWiki.ReactiveSystems.TimedBisimulationHmlStrict
import Sources.Doi_10_7146_brics_v2i2_19504.Source

/-! # Laroussinie–Larsen–Weise — timed Hennessy–Milner characterization — catalog
Pointers to the `DeepWiki.ReactiveSystems` theorems formalizing this paper's "to logic and back"
result: timed bisimilarity coincides with timed modal-logic (`Lν`) equivalence via characteristic
formulae. The Reactive Systems book defers its Theorems 12.4/12.5 to this paper; these are the
paper-side ("double reference") pointers complementing the book catalog's `Chapter12`. -/

namespace DeepWiki.Llw

open DeepWiki.ReactiveSystems
open scoped NNReal

/-- **Characteristic formula** (the `Lν`/timed-modal recursive formula of the "to logic" half):
the library's `charFormula` for the running timed automaton. -/
abbrev characteristicFormula := @DeepWiki.ReactiveSystems.TLTS.charFormula

/-- **"To logic and back" for the running automaton** (the paper's core; the book's Theorem 12.5):
a state satisfies the characteristic formula iff it is timed-bisimilar to the reference state — a
single timed-modal formula captures the whole timed-bisimilarity class. The library's
`mem_charFormula_iff_timedBisimilar`. -/
alias characteristicFormula_iff_timedBisimilar :=
  DeepWiki.ReactiveSystems.TLTS.mem_charFormula_iff_timedBisimilar

/-- **The automaton hypothesis is necessary** (the limit of the converse): over a general,
*non-automaton* timed transition system, timed-HML (`Lν`) equivalence does **not** imply timed
bisimilarity — the `√2` system satisfies the same timed-HML formulae at `(A,0)` and `(B,0)` yet is
not timed bisimilar there. Witnesses why the book's general Theorem 12.4 needs the automaton
hypothesis. The library's `timedHmlEquiv_and_not_timedBisimilar_sq2`. -/
alias timedHmlEquiv_not_timedBisimilar_sq2 :=
  DeepWiki.ReactiveSystems.timedHmlEquiv_and_not_timedBisimilar_sq2

end DeepWiki.Llw
