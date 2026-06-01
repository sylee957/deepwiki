import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Introduction" =>

This document accompanies a Lean 4 + Mathlib formalization of §2.1 of
Bouillard, Boyer and Le Corronc, _Deterministic Network Calculus_. The
mathematical setting is the algebra of _dioids_ (idempotent semirings)
and the _(min,plus)_ algebra underlying network calculus.

Every definition, lemma and proposition of §2.1 is stated and proved in
Lean, in the `NetworkCalculus` namespace. Each chapter here pairs the
book's narrative with the corresponding Lean declarations inline, as
elaborated code blocks whose bodies _are_ the real formalization, so
the rendered statements reflect exactly what was proved. The book is
its own source of truth: it compiles as part of building the book.

The chapters cover:

- _Dioids and complete dioids_ — Definition 2.5, the canonical order,
  Theorem 2.1 (order relation and isotony), and the complete dioid with
  lower semi-continuity.
- _The (min,plus) scalar dioids_ — the carriers `Rmin`, `R⁺min` and
  `R̄min` (Theorem 2.2, Propositions 2.1–2.2).
- _The (min,plus) convolution and the function dioid_ — Definitions
  2.6–2.7, Lemmas 2.1–2.2, and Proposition 2.3.
- _Main subsets of functions_ — Definition 2.8, Lemma 2.3, and why
  `F⁺`/`F↑` are complete dioids while `F₀`/`F↑₀` are not.

Throughout, the book's notation maps to Lean as `⊕ = +` (the dioid sum,
the lattice join), `⊗ = *` (the product), `𝟘 = 0`, `𝟙 = 1`, and the
canonical order `≼` as `≤`.
