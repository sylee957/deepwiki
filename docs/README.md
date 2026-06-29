# The Risch Algorithm, Formalized

A guided tour of the DeepWiki formalization of the Risch algorithm in Lean 4 —
the decision procedure for symbolic integration of the transcendental elementary
functions. The tutorial builds the theory from differential algebra up through the
transcendental tower, and mechanizes both directions: _soundness_ ($D(\int f) = f$)
and _completeness_ (a `none` answer is a proof of non-elementarity), modulo the
honest Risch new-monomial side conditions stated explicitly.

Read the chapters in order:

1. [Introduction](introduction.md)
2. [Differential Algebra](differential-algebra.md)
3. [The Integration Problem and Liouville's Theorem](integration-problem.md)
4. [The Rational Case](rational-case.md)
5. [The Transcendental Tower](transcendental-tower.md)
6. [The Risch Differential Equation](risch-differential-equation.md)
7. [Soundness](soundness.md)
8. [Completeness](completeness.md)
9. [Proof Status](proof-status.md)

Throughout, each declaration name links to its definition in the local source tree.
