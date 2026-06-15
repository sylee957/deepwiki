import DeepWiki.ReactiveSystems.HmlRecursion
import Sources.Doi_10_1017_CBO9780511814105.Source

/-! # Reactive Systems catalog — Chapter 6: HML with recursion
Book-numbered restatements for Chapter 6, discharged by the
`DeepWiki.ReactiveSystems` library, with solved exercises. -/

namespace DeepWiki.Rs

open DeepWiki.ReactiveSystems
open DeepWiki.ReactiveSystems.LTS

variable {Proc Act : Type*}

/-! ## §6.2 Syntax and semantics of HML with recursion -/

/-- **§6.2** (p.109). HML with a single recursion variable `X`. The library's
`HMLR`. -/
abbrev hmlr := @HMLR

/-- **Definition 6.1** (§6.2, p.109). The semantic function `O_F(S)` of an HML
formula with recursion, interpreting `X` as `S`. The library's `LTS.denotR`. -/
abbrev def_6_1 := @LTS.denotR

/-- **§6.2** (p.113). The meaning of the recursive definition `X =ν F`: the
greatest fixed point of `O_F`. The library's `LTS.recMax`. -/
abbrev recMax := @LTS.recMax

/-- **§6.2** (p.113). The meaning of the recursive definition `X =μ F`: the
least fixed point of `O_F`. The library's `LTS.recMin`. -/
abbrev recMin := @LTS.recMin

/-! ## §6.3 Largest fixed points and invariant properties -/

/-- **§6.3** (p.113). The invariant property `Inv(F) = νX. (F ∧ [Act]X)`. The
library's `LTS.Inv`. -/
abbrev inv := @LTS.Inv

/-- **Theorem 6.1** (§6.3, p.114). `Inv(F)` is exactly the set of states from
which every reachable state satisfies `F`. -/
theorem thm_6_1 (L : LTS Proc Act) (F : HML Act) :
    LTS.Inv L F = {p | ∀ p', L.Reachable p p' → p' ∈ LTS.denot L F} := LTS.Inv_eq L F

/-! ## Solved exercises -/

/-- **Exercise 6.5** (§6.2, p.110). `O_F` is monotone for every formula `F`, so
its least and greatest fixed points exist (Tarski); introducing negation would
break monotonicity. -/
theorem ex_6_5 (L : LTS Proc Act) (F : HMLR Act) : Monotone (LTS.denotR L F) :=
  LTS.denotR_mono L F

end DeepWiki.Rs
