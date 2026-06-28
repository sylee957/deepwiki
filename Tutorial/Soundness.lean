import VersoManual

open Verso.Genre Manual

/-! Soundness chapter of the Risch-algorithm tutorial (prose-only stub). -/

#doc (Manual) "Soundness" =>

_Soundness_ is the guarantee that the algorithm never lies: whenever it returns an
antiderivative $`g` for an input $`f`, that answer is correct — $`D(g) = f`. This
is the a-priori correctness theorem, proved directly about the integration
function rather than checked after the fact.

This chapter will state the soundness result and walk through how it is
established across the three regimes (rational, exponential, primitive), citing
the integration-functions catalog that records exactly which inputs are covered.
The proven statements and the catalog are linked at `/deepwiki/api/`.
