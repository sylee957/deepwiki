import VersoManual

open Verso.Genre Manual

/-! Completeness chapter of the Risch-algorithm tutorial (prose-only stub). -/

#doc (Manual) "Completeness" =>

_Completeness_ is the harder direction: when the algorithm reports failure, there
really is no elementary integral. This is where Liouville's theorem does its work,
turning the absence of a solution to the Risch differential equation into the
non-existence of an elementary antiderivative.

This chapter will assemble the completeness argument: the RDE tower induction,
Liouville's theorem in its logarithmic, exponential, and multi-level forms, the
tangent case, and the honest new-monomial side conditions under which the result
is stated. It will be explicit about what is fully proved and what remains a
stated hypothesis. The relevant theorems are linked at `/deepwiki/api/`.
