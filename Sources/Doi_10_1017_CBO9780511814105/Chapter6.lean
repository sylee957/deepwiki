import DeepWiki.ReactiveSystems.HmlRecursion
import DeepWiki.ReactiveSystems.FiniteLatticeIterate
import DeepWiki.ReactiveSystems.Chapter6Examples
import DeepWiki.ReactiveSystems.HmlRecursionGame
import DeepWiki.ReactiveSystems.HmlRecursionSystems
import DeepWiki.ReactiveSystems.HmlCharacteristic
import DeepWiki.ReactiveSystems.HmlCharacteristicSyntactic
import DeepWiki.ReactiveSystems.Chapter6Characteristic
import DeepWiki.ReactiveSystems.Chapter6PosReach
import Sources.Doi_10_1017_CBO9780511814105.Source

/-! # Reactive Systems catalog — Chapter 6: HML with recursion
Book-numbered restatements for Chapter 6, discharged by the
`DeepWiki.ReactiveSystems` library, with solved exercises. -/

namespace DeepWiki.Rs

open DeepWiki.ReactiveSystems
open DeepWiki.ReactiveSystems.LTS

variable {Proc V Act : Type*}

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

/-- **Theorem 6.2** (§6.3, p.114). `Inv(F) = FIX I`: `Inv(F)` is exactly the set of
states from which every reachable state satisfies `F`. (This is book Theorem 6.2,
not 6.1 — the genuine Theorem 6.1 is the finite-iteration fixed-point result
`thm_6_1` below.) -/
theorem thm_6_2 (L : LTS Proc Act) (F : HML Act) :
    LTS.Inv L F = {p | ∀ p', L.Reachable p p' → p' ∈ LTS.denot L F} := LTS.Inv_eq L F

/-- **Theorem 6.1** (§6.3, p.111). On a *finite* state space, the greatest solution
of a recursive property is reached by finite iteration: `recMax F = O_Fᴹ(⊤)` for
some `M` (and dually `recMin F = O_Fᵐ(∅)` for some `m`). A direct consequence of
Theorem 4.2 applied to the monotone semantic functional `O_F = denotRHom`. -/
theorem thm_6_1_max [Finite Proc] (L : LTS Proc Act) (F : HMLR Act) :
    ∃ M, LTS.recMax L F = (LTS.denotRHom L F)^[M] ⊤ :=
  DeepWiki.ReactiveSystems.gfp_eq_iterate_top (LTS.denotRHom L F)

/-- **Theorem 6.1** (§6.3, p.111). The least-solution form: `recMin F = O_Fᵐ(∅)`
for some `m`. -/
theorem thm_6_1_min [Finite Proc] (L : LTS Proc Act) (F : HMLR Act) :
    ∃ m, LTS.recMin L F = (LTS.denotRHom L F)^[m] ⊥ :=
  DeepWiki.ReactiveSystems.lfp_eq_iterate_bot (LTS.denotRHom L F)

/-! ## §6.4 A game characterization for HML with recursion -/

/-- **§6.4** (p.115). The model-checking game functional for HML with one
recursion variable `X` (body `F`): the one-step defender-favourable condition on
configurations `(state, subformula)`. The library's `LTS.defGameFun`. -/
abbrev defGameFun := @LTS.defGameFun

/-- **Theorem 6.3** (§6.4, p.116), largest-fixed-point case. For `X =ν F`, the
defender wins the game from `(s, G)` iff `s` satisfies `G` under the greatest
fixed point — i.e. `s ∈ O_G(recMax F)`. (The book defers the operational
infinite-play proof to Stirling 2001; this is the fixed-point characterization of
the defender's winning region, a safety game whose winning strategies are
post-fixed-point invariants `DefenderInvariant`.) -/
theorem thm_6_3_max (L : LTS Proc Act) (F : HMLR Act) (s : Proc) (G : HMLR Act) :
    LTS.DefenderWinsMax L F s G ↔ s ∈ LTS.denotR L G (LTS.recMax L F) :=
  LTS.defenderWinsMax_iff L F s G

/-- **Theorem 6.3** (§6.4, p.116), least-fixed-point case. For `X =μ F`, the
defender's winning region is the least fixed point of the game functional, equal
to the satisfaction set at `recMin F` (a reachability game). -/
theorem thm_6_3_min (L : LTS Proc Act) (F : HMLR Act) (s : Proc) (G : HMLR Act) :
    (s, G) ∈ (LTS.defGameFun L F).lfp ↔ s ∈ LTS.denotR L G (LTS.recMin L F) :=
  LTS.game_characterization_min L F s G

/-! ## Solved exercises -/

/-- **Exercise 6.5** (§6.2, p.110). `O_F` is monotone for every formula `F`, so
its least and greatest fixed points exist (Tarski); introducing negation would
break monotonicity. -/
theorem ex_6_5 (L : LTS Proc Act) (F : HMLR Act) : Monotone (LTS.denotR L F) :=
  LTS.denotR_mono L F

/-! ## §6.5 Mutually recursive equational systems -/

/-- **§6.5** (p.122). HML with recursion over a variable set `V`. The library's
`HMLV`. -/
abbrev hmlv := @HMLV

/-- **Definition 6.1, multivariable** (§6.5, p.123). The semantic function `O_F`
over an environment of variable interpretations. The library's `LTS.denotV`. -/
abbrev denotV := @LTS.denotV

/-- **Equation 6.9** (§6.5, p.122). The semantic function `⟦D⟧` of a declaration
on the product complete lattice `V → 2^Proc`. The library's `LTS.sysFun`. -/
abbrev eq_6_9 := @LTS.sysFun

/-- **§6.5** (p.122). The largest solution of an equational system (gfp of
`⟦D⟧`). The library's `LTS.sysMax`. -/
abbrev sysMax := @LTS.sysMax

/-- **§6.5** (p.122). The least solution of an equational system (lfp of `⟦D⟧`).
The library's `LTS.sysMin`. -/
abbrev sysMin := @LTS.sysMin

/-- **Exercise 6.8(1)** (§6.5, p.124). The product domain `(2^Proc)^V`, ordered
componentwise, is a complete lattice. -/
theorem ex_6_8_1 : Nonempty (CompleteLattice (V → Set Proc)) :=
  LTS.ex_6_8_completeLattice

/-- **Exercise 6.8(2)** (§6.5, p.124). The declaration's semantic function `⟦D⟧`
is monotone. -/
theorem ex_6_8_2 (L : LTS Proc Act) (D : V → HMLV V Act) : Monotone (LTS.sysFun L D) :=
  LTS.ex_6_8_mono L D

/-! ## §6.6 Characteristic properties -/

/-- **Equation 6.15** (§6.6, p.130). The characteristic-property functional. The
library's `LTS.charFun` (its greatest fixed point is the characteristic property
`X_p`). -/
abbrev eq_6_15 := @LTS.charFun

/-- **Lemma 6.1** (§6.6, p.131). `{(p,q) | q ⊨ X_p}` is a strong bisimulation. -/
theorem lemma_6_1 (L : LTS Proc Act) :
    LTS.IsBisimulation L (fun p q => q ∈ LTS.charProp L p) := LTS.charProp_isBisimulation L

/-- **Lemma 6.2** (§6.6, p.133). Each state satisfies its own characteristic
formula (bisimilarity is below the characteristic property). -/
theorem lemma_6_2 (L : LTS Proc Act) :
    (fun p => {q | p ~[L] q}) ≤ LTS.charProp L := LTS.bisimilar_le_charProp L

/-- **Theorem 6.4** (§6.6, p.130). The characteristic property of `p` is exactly
its strong-bisimilarity class: `q ⊨ X_p` iff `p ~ q`. -/
theorem thm_6_4 (L : LTS Proc Act) (p q : Proc) :
    q ∈ LTS.charProp L p ↔ (p ~[L] q) := LTS.charProp_eq_bisimilar L p q

/-- **§6.6** (Eq. 6.15, p.128), the *syntactic* characteristic formula: the
characteristic equation system assigns each state `p` the recursive formula
`(⋀_a ⋀_{p'∈Der a p} ⟨a⟩X_{p'}) ∧ (⋀_a [a]⋁_{p'∈Der a p} X_{p'})` — "every move
of `p` is matchable" and "no `a`-move escapes `p`'s `a`-successors". The library's
`LTS.charSys`. -/
noncomputable abbrev charSys := @LTS.charSys

/-- **Theorem 6.4** (§6.6, p.130), syntactic form. On a finite LTS, the greatest
solution of the characteristic equation system is exactly the strong-bisimilarity
class: `q ⊨ X_p` iff `p ~ q`. This realises the semantic characteristic property
as an explicit Hennessy–Milner formula with recursion. -/
theorem thm_6_4_syntactic (L : LTS Proc Act) [Fintype Act] [Fintype Proc]
    [∀ p a p', Decidable (L.step p a p')] (p q : Proc) :
    q ∈ LTS.sysMax L (LTS.charSys L) p ↔ (p ~[L] q) :=
  LTS.charSys_characterizes L p q

/-! ## §6.7 Mixing largest and least fixed points -/

/-- **Definition 6.2** (§6.7, p.137), the kind of a fixed-point equation
(`max`/`ν` or `min`/`μ`). The library's `FpKind`. -/
abbrev fpKind := @FpKind

/-- **§6.7** (p.135). The livelock property `LivelockNow =ν ⟨τ⟩LivelockNow`. The
library's `LTS.LivelockNow`. -/
abbrev livelockNow := @LTS.LivelockNow

/-- **Exercise 6.15** (§6.7, p.135). The least solution of `X = ⟨τ⟩X` is empty —
only the largest fixed point captures livelock. -/
theorem ex_6_15 (L : LTS Proc Act) (tau : Act) : (LTS.livelockFun L tau).lfp = ∅ :=
  LTS.ex_6_15 L tau

/-- **Exercise 6.16** (§6.7, p.135). On the given 4-state LTS, the only livelocked
state is the `τ`-self-loop `p`: `LivelockNow = {p}`. The library's `ex_6_16`. -/
theorem ex_6_16 :
    LTS.LivelockNow DeepWiki.ReactiveSystems.L616 .tau = {DeepWiki.ReactiveSystems.S616.p} :=
  DeepWiki.ReactiveSystems.ex_6_16

/-- **Exercise 6.17** (§6.7, p.135). On the given 4-state LTS every state has an
outgoing `τ`, so every state is livelocked: `LivelockNow = univ`. The library's
`ex_6_17`. -/
theorem ex_6_17 :
    LTS.LivelockNow DeepWiki.ReactiveSystems.L617 .tau = Set.univ :=
  DeepWiki.ReactiveSystems.ex_6_17

/-- **Exercise 6.4** (§6.2, p.110). On the Figure 6.2 LTS, the semantic functional
evaluates to `O_{[b]ff ∧ [a]X}({p₂}) = {p₂}`. The library's `ex_6_4`. -/
theorem ex_6_4 :
    LTS.denotR DeepWiki.ReactiveSystems.L62
        (HMLR.and (HMLR.box .b HMLR.ff) (HMLR.box .a HMLR.var)) {DeepWiki.ReactiveSystems.S62.p2}
      = {DeepWiki.ReactiveSystems.S62.p2} :=
  DeepWiki.ReactiveSystems.ex_6_4

/-- **Exercise 6.9** (§6.5, p.124). The largest solution of the equational system
`X =ν [a]Y`, `Y =ν ⟨a⟩X` over the 3-state LTS is `X = {p, r}`, `Y = {p, q}`. The
library's `ex_6_9`. -/
theorem ex_6_9 :
    LTS.sysMax DeepWiki.ReactiveSystems.L69 DeepWiki.ReactiveSystems.D69
      = DeepWiki.ReactiveSystems.sol69 :=
  DeepWiki.ReactiveSystems.ex_6_9

/-- **Exercise 6.6** (§6.3, p.111). The least solution of `Y =μ ⟨b⟩tt ∨ ⟨{a,b}⟩Y`
on the given 5-state LTS is the whole state space (every state reaches a `b`-looping
state). The library's `ex_6_6`. -/
theorem ex_6_6 :
    LTS.recMin DeepWiki.ReactiveSystems.L66 DeepWiki.ReactiveSystems.FY66 = Set.univ :=
  DeepWiki.ReactiveSystems.ex_6_6

/-- **Exercise 6.7** (§6.3, p.111). On one LTS: `s₁ ⊨ X =ν ⟨b⟩tt ∧ [b]X`;
`s ⊨ Y =μ ⟨b⟩tt ∨ ⟨{a,b}⟩Y` but `t ⊭ Y`; and `t` is `a`-livelocked
(`t ⊨ Z =ν ⟨a⟩Z`). The library's `ex_6_7_1`/`_2`/`_3`. -/
theorem ex_6_7 :
    (DeepWiki.ReactiveSystems.S67.s1 ∈
      LTS.recMax DeepWiki.ReactiveSystems.L67 DeepWiki.ReactiveSystems.F67) ∧
    (DeepWiki.ReactiveSystems.S67.s ∈
      LTS.recMin DeepWiki.ReactiveSystems.L67 DeepWiki.ReactiveSystems.FY67 ∧
      DeepWiki.ReactiveSystems.S67.t ∉
      LTS.recMin DeepWiki.ReactiveSystems.L67 DeepWiki.ReactiveSystems.FY67) ∧
    (DeepWiki.ReactiveSystems.S67.t ∈ LTS.LivelockNow DeepWiki.ReactiveSystems.L67 .a) :=
  ⟨DeepWiki.ReactiveSystems.ex_6_7_1, DeepWiki.ReactiveSystems.ex_6_7_2,
   DeepWiki.ReactiveSystems.ex_6_7_3⟩

/-- **Exercise 6.13** (§6.6, p.134). The characteristic formulae for the processes
`p` and `q` of Figure 6.1 (`p —a→ p`; `q —a→ q`, `q —a→ r`; `r` dead) are satisfied
by exactly `p` and `q` respectively: `⟦charSys p⟧ = {p}`, `⟦charSys q⟧ = {q}`, since
the three states are pairwise non-bisimilar. The library's `ex_6_13_p`/`ex_6_13_q`. -/
theorem ex_6_13 :
    sysMax DeepWiki.ReactiveSystems.L61 (charSys DeepWiki.ReactiveSystems.L61)
        DeepWiki.ReactiveSystems.P61.p = {DeepWiki.ReactiveSystems.P61.p} ∧
    sysMax DeepWiki.ReactiveSystems.L61 (charSys DeepWiki.ReactiveSystems.L61)
        DeepWiki.ReactiveSystems.P61.q = {DeepWiki.ReactiveSystems.P61.q} :=
  ⟨DeepWiki.ReactiveSystems.ex_6_13_p, DeepWiki.ReactiveSystems.ex_6_13_q⟩

/-- **Exercise 6.18** (§6.7, p.138). On the Exercise 6.17 LTS, the formula
`⟨Act⟩Pos(LivelockNow)` (the states from which a livelock is reachable, with `Pos`
the least-fixed-point reachability template (6.17)) denotes the whole state space —
every state is livelocked and can move. The library's `ex_6_18` (with `diaAll`/`posOf`
the `⟨Act⟩` and `Pos` set operators). -/
theorem ex_6_18 :
    DeepWiki.ReactiveSystems.diaAll DeepWiki.ReactiveSystems.L617
      (DeepWiki.ReactiveSystems.posOf DeepWiki.ReactiveSystems.L617
        (LTS.LivelockNow DeepWiki.ReactiveSystems.L617 DeepWiki.ReactiveSystems.Act6.tau)) =
      Set.univ :=
  DeepWiki.ReactiveSystems.ex_6_18

end DeepWiki.Rs
