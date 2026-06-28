import VersoManual

import Tutorial.Introduction
import Tutorial.DifferentialAlgebra
import Tutorial.IntegrationProblem
import Tutorial.RationalCase
import Tutorial.TranscendentalTower
import Tutorial.RischDifferentialEquation
import Tutorial.Soundness
import Tutorial.Completeness
import Tutorial.ProofStatus

open Verso.Genre Manual

/-! Root document of the Risch-algorithm tutorial Manual (prose-only). -/

#doc (Manual) "The Risch Algorithm, Formalized" =>

%%%
authors := ["Sangyub Lee"]
shortTitle := "The Risch Algorithm"
%%%

This is a guided tutorial through the DeepWiki formalization of the _Risch
algorithm_ for symbolic integration — the decision procedure that, given a
transcendental elementary function, computes an elementary antiderivative or
proves that none exists.

The tutorial develops the theory from differential algebra up to the soundness
and completeness results as they are mechanized in Lean 4 with Mathlib. It is a
prose companion to the machine-checked library; the full API documentation is
rendered separately at `/deepwiki/api/`.

{include 1 Tutorial.Introduction}

{include 1 Tutorial.DifferentialAlgebra}

{include 1 Tutorial.IntegrationProblem}

{include 1 Tutorial.RationalCase}

{include 1 Tutorial.TranscendentalTower}

{include 1 Tutorial.RischDifferentialEquation}

{include 1 Tutorial.Soundness}

{include 1 Tutorial.Completeness}

{include 1 Tutorial.ProofStatus}
