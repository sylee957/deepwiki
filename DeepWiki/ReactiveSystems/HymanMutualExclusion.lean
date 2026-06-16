import DeepWiki.ReactiveSystems.Peterson

/-! # Hyman's mutual-exclusion algorithm in CCS (Exercise 7.3)
Hyman's 1966 'mutual exclusion' algorithm, modelled in CCS following the book's
Exercise 7.3 (§7, p.146). It uses the *same* shared variables as Peterson's —
the booleans `b1`, `b2` and the integer `k` — so we reuse the channel set
`PetChan` and the register processes. Each process `Pᵢ` runs

    bᵢ := true;
    while k ≠ j do begin  while bⱼ do skip;  k := i  end;
    critical;  bᵢ := false

(with `j` the other index). The outer loop `while k ≠ j` is read by trying the
two `k`-read ports; the inner busy-wait `while bⱼ do skip` loops on reading
`bⱼ = true` and falls through on `bⱼ = false`. (Hyman's algorithm is *not* a
correct mutual-exclusion algorithm — that analysis is Exercise 7.4; here we only
give the faithful model.) -/

namespace DeepWiki.ReactiveSystems

open PetChan

/-- Process constants of Hyman's algorithm: the register states (reusing
Peterson's `b1`, `b2`, `k`) and the control states of the two protocol processes.
For `P1`: `H1` (set `b1`), `H1outer` (test `k ≠ 2`), `H1inner` (busy-wait on
`b2`), `H1setk` (set `k := 1`), `H1crit` (critical section), `H1reset` (clear
`b1`); symmetrically for `P2`. -/
inductive HymanK
  | B1f | B1t | B2f | B2t | K1 | K2
  | H1 | H1outer | H1inner | H1setk | H1crit | H1reset
  | H2 | H2outer | H2inner | H2setk | H2crit | H2reset
  deriving DecidableEq

open HymanK

/-- The defining environment for Hyman's algorithm. The registers behave exactly
as in Peterson's algorithm; the protocol processes read `k`/`bⱼ` via complementary
read ports and write via the write ports. `P1`'s outer test `k ≠ 2` reads `k`:
reading `1` (`kr1`) re-enters the loop body, reading `2` (`kr2`) exits to the
critical section; the inner busy-wait reads `b2`, looping on `true` and exiting on
`false`, then sets `k := 1` and re-tests. -/
def hymanDefn : HymanK → CCS PetChan HymanK
  | B1f => .choice (.pre (.name b1rf) (.const B1f))
            (.choice (.pre (.name b1wf) (.const B1f)) (.pre (.name b1wt) (.const B1t)))
  | B1t => .choice (.pre (.name b1rt) (.const B1t))
            (.choice (.pre (.name b1wf) (.const B1f)) (.pre (.name b1wt) (.const B1t)))
  | B2f => .choice (.pre (.name b2rf) (.const B2f))
            (.choice (.pre (.name b2wf) (.const B2f)) (.pre (.name b2wt) (.const B2t)))
  | B2t => .choice (.pre (.name b2rt) (.const B2t))
            (.choice (.pre (.name b2wf) (.const B2f)) (.pre (.name b2wt) (.const B2t)))
  | K1 => .choice (.pre (.name kr1) (.const K1))
            (.choice (.pre (.name kw1) (.const K1)) (.pre (.name kw2) (.const K2)))
  | K2 => .choice (.pre (.name kr2) (.const K2))
            (.choice (.pre (.name kw1) (.const K1)) (.pre (.name kw2) (.const K2)))
  -- process 1: j = 2, exits the outer loop when k = 2, sets k := 1
  | H1 => .pre (.coname b1wt) (.const H1outer)
  | H1outer => .choice (.pre (.coname kr1) (.const H1inner)) (.pre (.coname kr2) (.const H1crit))
  | H1inner => .choice (.pre (.coname b2rt) (.const H1inner)) (.pre (.coname b2rf) (.const H1setk))
  | H1setk => .pre (.coname kw1) (.const H1outer)
  | H1crit => .pre (.name enter1) (.pre (.name exit1) (.const H1reset))
  | H1reset => .pre (.coname b1wf) (.const H1)
  -- process 2: j = 1, exits the outer loop when k = 1, sets k := 2
  | H2 => .pre (.coname b2wt) (.const H2outer)
  | H2outer => .choice (.pre (.coname kr2) (.const H2inner)) (.pre (.coname kr1) (.const H2crit))
  | H2inner => .choice (.pre (.coname b1rt) (.const H2inner)) (.pre (.coname b1rf) (.const H2setk))
  | H2setk => .pre (.coname kw2) (.const H2outer)
  | H2crit => .pre (.name enter2) (.pre (.name exit2) (.const H2reset))
  | H2reset => .pre (.coname b2wf) (.const H2)

/-- The restricted channel set for Hyman's algorithm: every read/write port (i.e.
all channels except the observable critical-section actions), reusing Peterson's
`petRestrict`. -/
def hymanRestrict : Set (Act PetChan) := petRestrict

/-- **Exercise 7.3** (§7, p.146). Hyman's algorithm as a CCS process, with `k`
initially `1`: `Hyman = (P₁ ∣ P₂ ∣ B1f ∣ B2f ∣ K1) ∖ L`. -/
def hyman : CCS PetChan HymanK :=
  .restrict (.par (.par (.par (.par (.const H1) (.const H2)) (.const B1f))
    (.const B2f)) (.const K1)) hymanRestrict

/-- Sanity check on the model: Hyman's first internal step is `P₁` writing `true`
to `b1` (synchronising with the register `B1f`, which moves to `B1t`) — an
internal `τ`-transition surviving the restriction, exactly as in Peterson's
algorithm. -/
theorem hyman_tau_writes_b1 :
    Step hymanDefn hyman Act.tau
      (.restrict (.par (.par (.par (.par (.const H1outer) (.const H2))
        (.const B1t)) (.const B2f)) (.const K1)) hymanRestrict) := by
  unfold hyman
  refine Step.res ?_ ?_ (Step.com1 (Step.com1 (Step.com3 (by simp [Act.IsLabel])
    (Step.com1 (Step.con (Step.act _ _)))
    (Step.con (Step.sumr (Step.sumr (Step.act _ _)))))))
  · simp [hymanRestrict, petRestrict]
  · simp [hymanRestrict, petRestrict]

end DeepWiki.ReactiveSystems
