import VersoManual

open Verso.Genre Manual

/-! Integration-problem chapter of the Risch-algorithm tutorial (prose-only stub). -/

#doc (Manual) "The Integration Problem and Liouville's Theorem" =>

What does it mean to integrate "in closed form"? The answer is made precise by
the class of _elementary functions_: those built from the rational functions by
finitely many algebraic operations, exponentials, and logarithms. The
integration problem asks for an elementary antiderivative, or a proof that none
exists.

This chapter will state _Liouville's theorem_, the structural result at the heart
of the whole subject: if an elementary function has an elementary integral, that
integral has a very restricted shape — a rational part plus a sum of constant
multiples of logarithms of elementary functions. Liouville's theorem is what
turns "find an integral" into a finite, decidable search, and it is the
foundation of the completeness argument formalized later. The supporting
declarations are linked at `/deepwiki/api/`.
