import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Introduction" =>
This is a wiki of _autoformalized_ mathematics: AI-generated articles
whose mathematical content is mechanized in Lean 4 with Mathlib. Each
topic is developed as a self-contained article — prose interleaved with
the actual Lean declarations — and every definition, lemma and
proposition is stated and proved, in the `VerifiedWiki` namespace. The
code blocks are elaborated as the document is built, so their bodies
_are_ the real formalization and the rendered statements reflect exactly
what was proved. The document is its own source of truth: it compiles as
part of building it.

The first entry is the algebra of _(min,plus)_ dioids. The mathematical
setting is the theory of _dioids_ (idempotent semirings) and the complete
(min,plus) dioids of functions that underlie deterministic network
calculus. Its chapters cover:

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
- _Sub-additive functions_ — the predicate $`f(s+t) \le f(s) + f(t)` in the
  natural numeric order, and its stability under the pointwise numeric sum
  of functions and under the convolution $`\ast`.
- _The sub-additive closure_ — the closure $`f^{\ast}` as the Kleene star of
  $`f` in the function dioid, and a sign constraint on sub-additive functions
  with $`f(0) < 0`.
- _The convolution attains its minimum_ — for nondecreasing, left-continuous
  real functions the convolution is an attained minimum, via lower
  semi-continuity on a compact interval.

Throughout, the notation maps to Lean as $`\oplus = {+}` (the dioid sum, the
lattice join), $`\otimes = {*}` (the product), $`\mathbf{0} = 0`, $`\mathbf{1} = 1`, and the canonical
order $`\preceq` as $`\le`.
