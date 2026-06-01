import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Introduction" =>
%%%
number := false
%%%

This is a Lean 4 + Mathlib formalization of the algebra of _(min,plus)_
dioids. The mathematical setting is the theory of _dioids_ (idempotent
semirings) and the complete (min,plus) dioids of functions that underlie
deterministic network calculus.

Every definition, lemma and proposition is stated and proved in Lean, in
the `NetworkCalculus` namespace. Each chapter pairs the narrative with the
corresponding Lean declarations inline, as elaborated code blocks whose
bodies _are_ the real formalization, so the rendered statements reflect
exactly what was proved. This document is its own source of truth: it
compiles as part of building it.

The chapters cover:

- _Dioids and complete dioids_ — the definition of a dioid, the canonical
  order, the order relation and isotony, and the complete dioid with lower
  semi-continuity.
- _The (min,plus) scalar dioids_ — the carriers $`R_{\min}`, $`R^+_{\min}` and $`\overline{R}_{\min}`.
- _The (min,plus) convolution and the function dioid_ — the (min,plus)
  functions, the convolution, its algebraic properties, and the function
  dioid.
- _Main subsets of functions_ — the non-negative, zero-at-zero and
  non-decreasing function classes, their stability, and why $`\mathcal{F}^+`/$`\mathcal{F}^\uparrow` are
  complete dioids while $`\mathcal{F}_0`/$`\mathcal{F}^\uparrow_0` are not.
- _Sub-additive closure_ — the Kleene star $`a^{\star} = \bigoplus_{i \ge 0} a^i` and its
  strict variant $`a^+`, their algebraic identities, monotonicity, and the
  Kleene star theorem: $`a^{\star} \otimes b` is the least solution of $`x = a \otimes x \oplus b`.

Throughout, the notation maps to Lean as $`\oplus = {+}` (the dioid sum, the
lattice join), $`\otimes = {*}` (the product), $`\mathbf{0} = 0`, $`\mathbf{1} = 1`, and the canonical
order $`\preceq` as $`\le`.
