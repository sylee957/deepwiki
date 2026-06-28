import VersoManual

open Verso.Genre Manual

/-! Transcendental-tower chapter of the Risch-algorithm tutorial (prose-only stub). -/

#doc (Manual) "The Transcendental Tower" =>

Functions beyond the rational ones are reached by adjoining _monomials_ one at a
time, building a tower of differential field extensions $`K(x)(t_1)(t_2)\cdots`.
Each monomial $`t_i` is logarithmic, exponential, or tangent over the field below
it, and is characterized purely by how the derivation acts on it.

This chapter will describe the three kinds of monomial, the tower of extensions
they generate, and the concrete carriers and polynomial representation the
formalization uses to compute in them. The transcendental tower is the data
structure on which the Risch differential equation and the integration algorithm
both operate; the carrier types and their derivation are linked at
`/deepwiki/api/`.
