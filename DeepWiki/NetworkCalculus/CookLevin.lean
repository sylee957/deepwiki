import DeepWiki.NetworkCalculus.ComplexityNP
import DeepWiki.NetworkCalculus.BooleanSatisfiability

/-! # The Cook–Levin theorem — faithfully stated, with its tableau scoped
This file states **Cook–Levin** (SAT is NP-hard) over the genuine, Turing-machine-grounded NP class
`IsNPHard_TM` (`ComplexityNP.lean`), and exhibits its *use* — NP-hardness of any problem reachable from
SAT by a chain of Karp reductions.

**What is and isn't proved.** The statement is fully formalized over the real class. The *proof* — the
tableau construction encoding an arbitrary polynomial-time TM2 verifier's computation as a CNF formula
and showing satisfiability ⟺ acceptance, with a polynomial size bound — is a research-scale
formalization (the comparable Isabelle/AFP development is ~30,000 lines). It is **not** discharged here;
it is the single, clearly-labeled `axiom cookLevin`. Everything around it is genuine: the NP class, the
SAT model, the bridge to the DNC Theorem 10.2 framework, and the reduction-chain mechanism.
-/

namespace DeepWiki

/-- A literal serialized as `[variable index, sign bit]`. -/
def litEncode {n : ℕ} (l : Literal n) : List ℕ := [l.1.val, if l.2 then 1 else 0]

/-- A clause serialized length-prefixed (so the serialization is unambiguous). -/
def clauseEncode {n : ℕ} (c : Clause n) : List ℕ := c.length :: c.flatMap litEncode

/-- A faithful (length-prefixed, unambiguous) serialization of a CNF formula to `List ℕ` — the
encoding the poly-time bounds are measured against. -/
def cnfEncode (φ : CnfFormula) : List ℕ :=
  φ.numVars :: φ.clauses.length :: φ.clauses.flatMap clauseEncode

/-- **The Cook–Levin theorem** (SAT is NP-hard), scoped as an axiom. The tableau construction — encode
an arbitrary polynomial-time TM2 verifier's computation as a CNF formula, prove satisfiable ⟺ accepts
within the time bound, and bound the formula size by a polynomial — is research-scale (~30k lines in
comparable proof assistants) and is the SINGLE genuine gap. It is stated over the real NP class
`IsNPHard_TM`, so it is a theorem-shaped goal, not a placeholder. `[research]` -/
axiom cookLevin : IsNPHard_TM cnfEncode Satisfiable

/-- **Usability of Cook–Levin** (the shape every concrete NP-hardness result instantiates): any
decision problem `R` reached from SAT by a Karp reduction is NP-hard. The chain toward DNC Theorem
10.2's worst-case-backlog problem is exactly this — supply `SAT ≤ₖ R` (via `SAT ≤ₖ 3SAT ≤ₖ 3DM ≤ₖ X3C
≤ₖ worst-case-backlog`, of which `3DM ≤ₖ X3C` and `X3C ≤ₖ worst-case-backlog` are already proved; the
`SAT ≤ₖ 3SAT ≤ₖ 3DM` gadgets are the remaining `[infra]`). -/
theorem isNPHard_TM_of_satReduction {ρ ρΓ : Type} {ec : ρ → List ρΓ} {R : ρ → Prop}
    (red : KarpReduction (fun φ => (cnfEncode φ).length) (fun z => (ec z).length) Satisfiable R) :
    IsNPHard_TM ec R :=
  cookLevin.viaReduction red

end DeepWiki
