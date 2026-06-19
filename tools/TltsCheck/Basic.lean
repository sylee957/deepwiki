import DeepWiki.ReactiveSystems.TimedRegionSuccessorComplete

/-! # TltsCheck — a formally-verified timed model checker, as a callable function
`check A F` runs the DeepWiki executable timed-HML model checker (`SymSatCodeFull` with the
Alur–Dill region successor `regionCodeDelaySucc`) and returns `true` iff the timed automaton `A`
satisfies the timed-HML formula `F`. The agreement with the *semantic* satisfaction relation
`A ⊨ F` is the theorem `check_iff` (= `satisfiesMt_iff_decideFull_delaySucc`), so the Boolean the
CLI prints is a *proved-correct* answer. Evaluation is native/compiled (not kernel `decide`). -/

namespace TltsCheck

open DeepWiki.ReactiveSystems

/-- Run the verified checker: `true` iff `A.toTimedAutomaton ⊨ F`. Clocks (`C`), formula clocks
(`D`) and locations (`Loc`) are finite; actions need only `DecidableEq`. -/
def check {Loc Act C D : Type} [DecidableEq Loc] [DecidableEq Act] [DecidableEq C] [DecidableEq D]
    [Fintype Loc] [Fintype C] [Fintype D]
    (A : FinAutomaton Loc Act C) (F : Mt Act D) : Bool :=
  SymSatCodeFull (cmax := Sum.elim A.cmax F.formulaCmax) A regionCodeDelaySucc
    A.initial (RegionCode.initial _) F

/-- **Soundness + completeness of `check`**: it returns `true` exactly when the automaton
semantically satisfies the formula. -/
theorem check_iff {Loc Act C D : Type} [DecidableEq Loc] [DecidableEq Act] [DecidableEq C]
    [DecidableEq D] [Fintype Loc] [Fintype C] [Fintype D]
    (A : FinAutomaton Loc Act C) (F : Mt Act D) :
    check A F = true ↔ A.toTimedAutomaton.SatisfiesMt F :=
  (satisfiesMt_iff_decideFull_delaySucc A F).symm

end TltsCheck
