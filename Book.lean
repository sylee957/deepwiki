import VersoManual
import Book.Introduction
import Book.Dioids
import Book.Scalars
import Book.Convolution
import Book.FunctionClasses

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Deterministic Network Calculus in Lean" =>

%%%
authors := ["S.Y. Lee"]
%%%

A mechanized companion to Chapter 2 of Bouillard, Boyer and Le Corronc,
*Deterministic Network Calculus*. Each definition, lemma and proposition of the
(min,plus) algebra is stated and proved in Lean 4 with Mathlib; this book pairs
the book's narrative with the corresponding Lean declarations.

{include 1 Book.Introduction}

{include 1 Book.Dioids}

{include 1 Book.Scalars}

{include 1 Book.Convolution}

{include 1 Book.FunctionClasses}
