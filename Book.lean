import VersoManual
import Book.Introduction
import Book.Signatures
import Book.Dioids
import Book.Order
import Book.CompleteDioids
import Book.Scalars
import Book.Convolution
import Book.NaturalOrder
import Book.Subadditivity
import Book.SubadditiveClosure
import Book.LeftContinuity
import Book.PiecewiseContinuous
import Book.ConvolutionMinimum
import Book.Servers
import Book.RealConvolution
import Book.Shapers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The Autoformalization Wiki" =>

%%%
authors := ["S.Y. Lee"]
%%%

An AI-generated wiki of _autoformalized_ mathematics: each topic is developed as
a self-contained article whose definitions, lemmas and propositions are stated
and proved in Lean 4 with Mathlib, with the narrative and the machine-checked
Lean declarations interleaved. The rendered statements are exactly what was
proved — the document compiles as part of building it.

The first entry is the algebra of _(min,plus)_ dioids, the theory behind
deterministic network calculus; the chapters below develop it from the abstract
dioid through to shapers and service curves.

{include 1 Book.Introduction}

{include 1 Book.Signatures}

{include 1 Book.Dioids}

{include 1 Book.Order}

{include 1 Book.CompleteDioids}

{include 1 Book.Scalars}

{include 1 Book.Convolution}

{include 1 Book.NaturalOrder}

{include 1 Book.Subadditivity}

{include 1 Book.SubadditiveClosure}

{include 1 Book.LeftContinuity}

{include 1 Book.PiecewiseContinuous}

{include 1 Book.ConvolutionMinimum}

{include 1 Book.Servers}

{include 1 Book.RealConvolution}

{include 1 Book.Shapers}
