import DeepWiki.ReactiveSystems.TimedHennessyMilnerClocks

/-! # Negation of timed HML formulae
The timed logic `Mt` is closed under negation: every formula `F` has a *negation*
`Fᶜ` with `⟦Fᶜ⟧ = ES(Proc) \ ⟦F⟧`. The construction pushes
negation inwards by De Morgan duality — `tt ↔ ff`, `∧ ↔ ∨`, `⟨a⟩ ↔ [a]`,
`∃∃ ↔ ∀∀`, fixing `x in`. The one subtlety is negating an atomic clock constraint:
`¬(x = n)` is `x < n ∨ x > n` (not a single constraint), so guard negation lands
in the `∨`-closed formula language, not back in `B(D)`. -/

namespace DeepWiki.ReactiveSystems

open scoped NNReal

variable {Act D : Type*}

/-- Negate an atomic clock constraint `x ⋈ n` into an `Mt` formula. The `=` case
needs a disjunction `x < n ∨ x > n`. -/
def negAtom (x : D) (c : Cmp) (n : ℕ) : Mt Act D :=
  match c with
  | .le => .guard (.atom x .gt n)
  | .lt => .guard (.atom x .ge n)
  | .eq => .or (.guard (.atom x .lt n)) (.guard (.atom x .gt n))
  | .gt => .guard (.atom x .le n)
  | .ge => .guard (.atom x .lt n)

/-- Negate a clock constraint into an `Mt` formula (De Morgan on conjunctions,
`negAtom` on atoms). -/
def negGuard : ClockConstraint D → Mt Act D
  | .true_ => .ff
  | .atom x c n => negAtom x c n
  | .and g₁ g₂ => .or (negGuard g₁) (negGuard g₂)

/-- The *negation* `Fᶜ` of a timed HML formula. -/
def Mt.neg : Mt Act D → Mt Act D
  | .tt => .ff
  | .ff => .tt
  | .and F G => .or F.neg G.neg
  | .or F G => .and F.neg G.neg
  | .dia a F => .box a F.neg
  | .box a F => .dia a F.neg
  | .existsDelay F => .forallDelay F.neg
  | .forallDelay F => .existsDelay F.neg
  | .reset x F => .reset x F.neg
  | .guard g => negGuard g

namespace TLTS

variable {Proc : Type*}

/-- Negating an atomic constraint complements its satisfaction. -/
theorem mtSat_negAtom (T : TLTS Proc Act) (p : Proc) (u : Valuation D) (x : D) (c : Cmp)
    (n : ℕ) : MtSat T p u (negAtom x c n) ↔ ¬ Cmp.holds c (u x) n := by
  cases c with
  | le => simpa only [negAtom, MtSat, satisfies, Cmp.holds] using (not_le).symm
  | lt => simpa only [negAtom, MtSat, satisfies, Cmp.holds] using (not_lt).symm
  | eq => simpa only [negAtom, MtSat, satisfies, Cmp.holds] using ne_iff_lt_or_gt.symm
  | gt => simpa only [negAtom, MtSat, satisfies, Cmp.holds] using (not_lt).symm
  | ge => simpa only [negAtom, MtSat, satisfies, Cmp.holds] using (not_le).symm

/-- Negating a clock constraint complements its satisfaction. -/
theorem mtSat_negGuard (T : TLTS Proc Act) (p : Proc) (u : Valuation D)
    (g : ClockConstraint D) : MtSat T p u (negGuard g) ↔ ¬ satisfies u g := by
  induction g with
  | true_ => simp [negGuard, MtSat, satisfies]
  | atom x c n => exact mtSat_negAtom T p u x c n
  | and g₁ g₂ ih₁ ih₂ => simp only [negGuard, MtSat, satisfies, not_and_or]; rw [ih₁, ih₂]

/-- The negation `Fᶜ` exactly complements
`F`: `(p, u) ⊨ Fᶜ` iff `(p, u) ⊭ F`, i.e. `⟦Fᶜ⟧ = ES(Proc) \ ⟦F⟧`. Proved by
structural induction (classically, for the modal dualities). -/
theorem mtSat_neg (T : TLTS Proc Act) (F : Mt Act D) :
    ∀ (p : Proc) (u : Valuation D), MtSat T p u F.neg ↔ ¬ MtSat T p u F := by
  induction F with
  | tt => intro p u; simp [Mt.neg, MtSat]
  | ff => intro p u; simp [Mt.neg, MtSat]
  | and F G ihF ihG =>
      intro p u; simp only [Mt.neg, MtSat, ihF, ihG, not_and_or]
  | or F G ihF ihG =>
      intro p u; simp only [Mt.neg, MtSat, ihF, ihG, not_or]
  | dia a F ihF =>
      intro p u; simp only [Mt.neg, MtSat, ihF, not_exists, not_and]
  | box a F ihF =>
      intro p u; simp only [Mt.neg, MtSat, ihF, not_forall, exists_prop]
  | existsDelay F ihF =>
      intro p u; simp only [Mt.neg, MtSat, ihF, not_exists, not_and]
  | forallDelay F ihF =>
      intro p u; simp only [Mt.neg, MtSat, ihF, not_forall, exists_prop]
  | reset x F ihF => intro p u; simp only [Mt.neg, MtSat, ihF]
  | guard g => intro p u; exact mtSat_negGuard T p u g

/-- Double negation: `(Fᶜ)ᶜ` and `F` are satisfied by the
same extended states. -/
theorem mtSat_neg_neg (T : TLTS Proc Act) (F : Mt Act D) (p : Proc) (u : Valuation D) :
    MtSat T p u F.neg.neg ↔ MtSat T p u F := by
  rw [mtSat_neg T F.neg p u, mtSat_neg T F p u, not_not]

end TLTS

end DeepWiki.ReactiveSystems
