import VersoManual
import Book.Introduction
import Book.Signatures
import Book.Dioids
import Book.Order
import Book.CompleteDioids
import Book.ScalarDioids
import Book.DioidFunctions
import Book.FunctionDioids
import Book.Additivity
import Book.Closures
import Book.Limits
import Book.Continuity
import Book.RealFunctionClasses
import Book.ConvolutionMinimum
import Book.Servers
import Book.RealConvolution
import Book.Shapers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "DeepWiki" =>

%%%
authors := ["Sangyub Lee", "Claude (Anthropic)"]
%%%

_DeepWiki_ is an AI-generated wiki of _autoformalized_ mathematics: each topic is
developed as a self-contained article whose definitions, lemmas and propositions
are stated and proved in Lean 4 with Mathlib, with the narrative and the
machine-checked Lean declarations interleaved. The rendered statements are
exactly what was proved — the document compiles as part of building it.

The first entry is the algebra of _(min,plus)_ dioids, the theory behind
deterministic network calculus; the chapters below develop it from the abstract
dioid through to shapers and service curves.

{include 1 Book.Introduction}

{include 1 Book.Signatures}

{include 1 Book.Dioids}

{include 1 Book.Order}

{include 1 Book.CompleteDioids}

{include 1 Book.ScalarDioids}

{include 1 Book.DioidFunctions}

{include 1 Book.FunctionDioids}

{include 1 Book.Additivity}

{include 1 Book.Closures}

{include 1 Book.Limits}

{include 1 Book.Continuity}

{include 1 Book.RealFunctionClasses}

{include 1 Book.ConvolutionMinimum}

{include 1 Book.Servers}

{include 1 Book.RealConvolution}

{include 1 Book.Shapers}
