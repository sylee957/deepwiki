import VersoManual

open Verso.Genre Manual

/-! Differential-algebra chapter of the Risch-algorithm tutorial (prose-only stub). -/

#doc (Manual) "Differential Algebra" =>

The setting for symbolic integration is _differential algebra_: a ring or field
equipped with a _derivation_ $`D`, an additive map satisfying the Leibniz rule
$`D(ab) = a\,D(b) + b\,D(a)`. Integration is then the search for a preimage
under $`D`.

This chapter will introduce the differential rings and fields the algorithm
works over, the derivation and its basic identities, the _constants_ (the kernel
of $`D`), and the _logarithmic derivative_ $`D(a)/a` that organizes the
exponential and logarithmic cases. The library builds these on top of Mathlib's
differential-algebra hierarchy; the relevant declarations are linked at
`/deepwiki/api/`.
