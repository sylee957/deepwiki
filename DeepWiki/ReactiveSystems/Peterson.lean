import DeepWiki.ReactiveSystems.Ccs

/-! # Peterson's mutual-exclusion algorithm in CCS
Peterson's two-process mutual-exclusion algorithm, modelled in CCS following the
book. Shared variables become processes: the boolean
variables `b1`, `b2` and the integer `k` are registers offering read/write
synchronisations on `name` channels; the two protocol processes `P1`, `P2`
synchronise with them via the complementary `coname` channels and perform the
observable `enterᵢ`/`exitᵢ` actions. The whole system restricts all read/write
channels, leaving only the critical-section actions observable. The book also gives
the CCS specification `MutexSpec`. Full correctness (mutual exclusion) is checked
externally (the CWB; the system has 69 states); here we give the faithful model
and specification. -/

namespace DeepWiki.ReactiveSystems

/-- Communication channels of Peterson's algorithm: read/write ports for the
boolean variables `b1`, `b2` and the integer `k` (`b1rt` = "read true from b1",
`b1wf` = "write false to b1", `kr1` = "read 1 from k", etc.), plus the observable
critical-section actions. -/
inductive PetChan
  | b1rt | b1rf | b1wt | b1wf
  | b2rt | b2rf | b2wt | b2wf
  | kr1 | kr2 | kw1 | kw2
  | enter1 | exit1 | enter2 | exit2
  deriving DecidableEq

/-- Process constants of Peterson's algorithm: the two states of each variable
(`B1f`/`B1t` for `b1`, similarly `b2`, and `K1`/`K2` for `k`), the control states
of the two protocol processes (`P1`, `P11`, `P12` and the symmetric `P2`, `P21`,
`P22`), and the mutual-exclusion specification `MutexSpec`. -/
inductive PetK
  | B1f | B1t | B2f | B2t | K1 | K2
  | P1 | P11 | P12 | P2 | P21 | P22
  | MutexSpec
  deriving DecidableEq

open PetChan PetK

/-- The defining environment for Peterson's algorithm. The
registers (`B…`, `K…`) offer their read/write ports on `name` channels; the
protocol processes (`P…`) read/write via the complementary `coname` channels and
perform `enterᵢ`/`exitᵢ` on `name` channels. `MutexSpec` ignores the
registers. -/
def petDefn : PetK → CCS PetChan PetK
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
  | P1 => .pre (.coname b1wt) (.pre (.coname kw2) (.const P11))
  | P11 => .choice (.pre (.coname b2rf) (.const P12))
            (.pre (.coname b2rt) (.choice (.pre (.coname kr2) (.const P11))
              (.pre (.coname kr1) (.const P12))))
  | P12 => .pre (.name enter1) (.pre (.name exit1) (.pre (.coname b1wf) (.const P1)))
  | P2 => .pre (.coname b2wt) (.pre (.coname kw1) (.const P21))
  | P21 => .choice (.pre (.coname b1rf) (.const P22))
            (.pre (.coname b1rt) (.choice (.pre (.coname kr1) (.const P21))
              (.pre (.coname kr2) (.const P22))))
  | P22 => .pre (.name enter2) (.pre (.name exit2) (.pre (.coname b2wf) (.const P2)))
  | MutexSpec => .choice (.pre (.name enter1) (.pre (.name exit1) (.const MutexSpec)))
            (.pre (.name enter2) (.pre (.name exit2) (.const MutexSpec)))

/-- The restricted channel set `L`: all read/write ports — i.e. every
channel except the observable critical-section actions. -/
def petRestrict : Set (Act PetChan) :=
  { a | ∃ c : PetChan, a = Act.name c ∧ c ∉ ({enter1, exit1, enter2, exit2} : Set PetChan) }

/-- Peterson's algorithm as a CCS process, with `k` initially `1`:
`Peterson = (P₁ | P₂ | B1f | B2f | K1) \ L`. -/
def peterson : CCS PetChan PetK :=
  .restrict (.par (.par (.par (.par (.const P1) (.const P2)) (.const B1f))
    (.const B2f)) (.const K1)) petRestrict

/-- The CCS specification of a mutual-exclusion algorithm:
`MutexSpec = enter₁.exit₁.MutexSpec + enter₂.exit₂.MutexSpec`. Once one process
enters its critical section the other cannot enter until the first exits. -/
def mutexSpec : CCS PetChan PetK := .const MutexSpec

/-- Sanity check on the model: Peterson's first internal step is `P1` writing
`true` to `b1` by synchronising with the register `B1f` (which moves to `B1t`) —
an internal `τ`-transition. This exercises the model end to end: a `coname`
output of `P1` meets the complementary `name` input of `B1f` (rule `com3`) deep
inside the parallel composition, and the resulting `τ` survives the restriction. -/
theorem peterson_tau_writes_b1 :
    Step petDefn peterson Act.tau
      (.restrict (.par (.par (.par (.par (.pre (.coname kw2) (.const P11)) (.const P2))
        (.const B1t)) (.const B2f)) (.const K1)) petRestrict) := by
  unfold peterson
  refine Step.res ?_ ?_ (Step.com1 (Step.com1 (Step.com3 (by simp [Act.IsLabel])
    (Step.com1 (Step.con (Step.act _ _)))
    (Step.con (Step.sumr (Step.sumr (Step.act _ _)))))))
  · simp [petRestrict]
  · simp [petRestrict]

end DeepWiki.ReactiveSystems
