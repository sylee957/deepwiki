import DeepWiki.ReactiveSystems.LabelledTransitionSystems
import DeepWiki.ReactiveSystems.Ccs
import Mathlib.Data.Set.Insert

/-! # Worked examples of Chapter 2 (Exercises 2.5, 2.7)
The concrete labelled transition system of Figure 2.6 (reachability, Exercise
2.5) and the "Small University" CCS process `SmUni = (CM ∣ CS) ∖ {coin, coffee}`
(the coffee-machine/student of §2.1, whose LTS is Exercise 2.7). -/

namespace DeepWiki.ReactiveSystems

open LTS

/-! ## Figure 2.6 — reachability (Exercise 2.5) -/

/-- The three states of the Figure 2.6 LTS. -/
inductive Fig26 | p | p1 | p2
  deriving DecidableEq

/-- The action labels of the Figure 2.6 LTS. -/
inductive Fig26Act | a | b | c | d
  deriving DecidableEq

/-- The transitions of Figure 2.6: `p —a→ p₁`, `p₁ —b→ p`, `p₂ —d→ p₁`,
`p₂ —c→ p₂`. -/
inductive Fig26Step : Fig26 → Fig26Act → Fig26 → Prop
  | pa : Fig26Step .p .a .p1
  | p1b : Fig26Step .p1 .b .p
  | p2d : Fig26Step .p2 .d .p1
  | p2c : Fig26Step .p2 .c .p2

/-- The Figure 2.6 labelled transition system. -/
def fig26 : LTS Fig26 Fig26Act := ⟨Fig26Step⟩

/-- **Exercise 2.5** (§2.2.1, p.21). From `p₂` *every* state is reachable: the
reachable set is the whole `{p, p₁, p₂}` (`p₂ ⤳ p₁` via `d`, then `p₁ ⤳ p` via
`b`). -/
theorem fig26_reachable_from_p2 (q : Fig26) : fig26.Reachable .p2 q := by
  cases q with
  | p2 => exact fig26.reachable_refl _
  | p1 => exact fig26.reachable_single Fig26Step.p2d
  | p => exact fig26.reachable_tail (fig26.reachable_single Fig26Step.p2d) Fig26Step.p1b

/-- **Exercise 2.5** (contrast, Remark 2.1). From `p` only `{p, p₁}` is
reachable — `p₂` is *not* reachable (it has no incoming edge from `p` or `p₁`). -/
theorem fig26_p_not_reach_p2 : ¬ fig26.Reachable .p .p2 := by
  have inv : ∀ q, fig26.Reachable .p q → q = .p ∨ q = .p1 := by
    intro q h
    induction h with
    | refl => exact Or.inl rfl
    | tail _ hstep ih =>
        obtain ⟨_, hs⟩ := hstep
        rcases ih with rfl | rfl
        · cases hs; exact Or.inr rfl
        · cases hs; exact Or.inl rfl
  intro h
  rcases inv _ h with h' | h' <;> exact absurd h' (by decide)

/-! ## The Small University `SmUni` (Exercise 2.7) -/

/-- Channels of the coffee-machine example: `coin`, `coffee`, `pub`. -/
inductive SmuniName | coin | coffee | pub
  deriving DecidableEq

/-- Constants: coffee machine `CM`/`CM1`, student `CS`/`CS1`/`CS2`, and the
publication specification `Spec` (§3.4). -/
inductive SmuniK | CM | CM1 | CS | CS1 | CS2 | Spec
  deriving DecidableEq

/-- §2.1 environment: `CM ≝ coin.CM₁`, `CM₁ ≝ c̄offee.CM`; `CS ≝ pub.CS₁`,
`CS₁ ≝ c̄oin.CS₂`, `CS₂ ≝ coffee.CS`. The machine inputs the coin and outputs the
coffee; the student does the complementary actions (plus the free `pub`). The
specification `Spec ≝ pub.Spec` (§3.4) just publishes repeatedly. -/
def smuniDefn : SmuniK → CCS SmuniName SmuniK
  | .CM => .pre (.name .coin) (.const .CM1)
  | .CM1 => .pre (.coname .coffee) (.const .CM)
  | .CS => .pre (.name .pub) (.const .CS1)
  | .CS1 => .pre (.coname .coin) (.const .CS2)
  | .CS2 => .pre (.name .coffee) (.const .CS)
  | .Spec => .pre (.name .pub) (.const .Spec)

/-- The restricted channels `L = {coin, coffee}` (their co-names are blocked
through the `α.co ∉ L` side of RES; `pub` and `τ` pass). -/
def smuniRestrict : Set (Act SmuniName) :=
  {Act.name SmuniName.coin, Act.name SmuniName.coffee}

/-- **(2.4)** `SmUni ≝ (CM ∣ CS) ∖ {coin, coffee}`. -/
def smUni : CCS SmuniName SmuniK :=
  .restrict (.par (.const .CM) (.const .CS)) smuniRestrict

/-- **Exercise 2.7** (§2.1/§2.2, p.16/p.20). The SOS rules derive `SmUni`'s LTS: a
free `pub`, then two synchronisations. `SmUni —pub→ (CM∣CS₁)∖L —τ→ (CM₁∣CS₂)∖L
—τ→ (CM∣CS)∖L` (a three-transition cycle through four states). -/
theorem smUni_lts :
    ((ccsLTS smuniDefn) ⊢ smUni ⟶[Act.name SmuniName.pub]
      (.restrict (.par (.const .CM) (.const .CS1)) smuniRestrict)) ∧
    ((ccsLTS smuniDefn) ⊢ (.restrict (.par (.const .CM) (.const .CS1)) smuniRestrict) ⟶[Act.tau]
      (.restrict (.par (.const .CM1) (.const .CS2)) smuniRestrict)) ∧
    ((ccsLTS smuniDefn) ⊢ (.restrict (.par (.const .CM1) (.const .CS2)) smuniRestrict) ⟶[Act.tau]
      (.restrict (.par (.const .CM) (.const .CS)) smuniRestrict)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Step.res (by simp [smuniRestrict]) (by simp [smuniRestrict])
      (Step.com2 (Step.con (Step.act _ _)))
  · exact Step.res (by simp [smuniRestrict]) (by simp [smuniRestrict])
      (Step.com3 (by rintro ⟨⟩) (Step.con (Step.act _ _)) (Step.con (Step.act _ _)))
  · exact Step.res (by simp [smuniRestrict]) (by simp [smuniRestrict])
      (Step.com3 (by rintro ⟨⟩) (Step.con (Step.act _ _)) (Step.con (Step.act _ _)))

end DeepWiki.ReactiveSystems
