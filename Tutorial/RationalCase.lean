import VersoManual

open Verso.Genre Manual

/-! Rational-case chapter of the Risch-algorithm tutorial (prose-only stub). -/

#doc (Manual) "The Rational Case" =>

Integration of rational functions $`f \in K(x)` is the base case and the model
for everything that follows. It splits into two parts: a _Hermite reduction_ that
extracts the rational part of the integral by reducing the denominator's
multiplicity, and a _logarithmic part_ that produces the residual sum of
logarithms.

This chapter will cover Hermite reduction and the Rothstein–Trager / Lazard–Rioboo–
Trager (LRT) construction of the logarithmic part — the resultant computation that
identifies the residues and the arguments of the logarithms. These are the
rational-case routines that the transcendental tower lifts and generalizes; the
formalized versions are linked at `/deepwiki/api/`.
