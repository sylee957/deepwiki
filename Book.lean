import VersoManual
import Book.Introduction
import Book.Dioids
import Book.Scalars
import Book.Convolution
import Book.FunctionClasses
import Book.SubadditiveClosure
import Book.SubadditiveFunctions
import Book.SubadditiveClosureOp
import Book.ConvolutionMinimum

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The (min,plus) Dioids in Lean" =>

%%%
number := false
authors := ["S.Y. Lee"]
%%%

A mechanized development of the _(min,plus)_ algebra. Each definition, lemma and
proposition of the (min,plus) algebra is stated and proved in Lean 4 with
Mathlib; this document pairs the narrative with the corresponding Lean
declarations.

{include 1 Book.Introduction}

{include 1 Book.Dioids}

{include 1 Book.Scalars}

{include 1 Book.Convolution}

{include 1 Book.FunctionClasses}

{include 1 Book.SubadditiveClosure}

{include 1 Book.SubadditiveFunctions}

{include 1 Book.SubadditiveClosureOp}

{include 1 Book.ConvolutionMinimum}
