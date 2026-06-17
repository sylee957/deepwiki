import DeepWiki.ReactiveSystems.Bisimulation

/-! # Cross-system bisimilarity, the sum LTS, and the quotient LTS
General constructions used to compare states of *different* transition systems
and to build quotient systems. The **sum LTS** `L₁ ⊕ L₂` places two systems side
by side (no transition crosses between them), so a single strong bisimilarity
`inl p ~ inr q` expresses "`p` in `L₁` behaves as `q` in `L₂`"
(`CrossBisimilar`). The **quotient LTS** `L/≈` collapses states along a setoid,
with `⟦s⟧ —a→ ⟦s'⟧` iff some representatives step `s —a→ s'`. The key theorem
(`crossBisimilar_quot`): when the setoid relation is itself a strong bisimulation
on `L`, every state is bisimilar to its class — the engine behind the region
graph. Reachability transfers both ways under the same hypothesis
(`reachable_quot_iff`). -/

namespace DeepWiki.ReactiveSystems

namespace LTS

variable {S₁ S₂ S Act : Type*}

/-! ## The disjoint-union (sum) LTS and cross-system bisimilarity -/

/-- The **disjoint-union (sum) LTS** of two LTSs over the same actions: states are
`S₁ ⊕ S₂`, each summand keeps its own transitions, and no transition crosses
between the two halves. -/
def sum (L₁ : LTS S₁ Act) (L₂ : LTS S₂ Act) : LTS (S₁ ⊕ S₂) Act where
  step s a t :=
    match s, t with
    | .inl p, .inl p' => L₁.step p a p'
    | .inr q, .inr q' => L₂.step q a q'
    | _, _ => False

/-- A step out of an `inl` state of the sum stays in the left summand. -/
theorem sum_step_inl_iff (L₁ : LTS S₁ Act) (L₂ : LTS S₂ Act) (p : S₁) (a : Act)
    (t : S₁ ⊕ S₂) : (L₁.sum L₂).step (.inl p) a t ↔ ∃ p', t = .inl p' ∧ L₁.step p a p' := by
  cases t with
  | inl p' => exact ⟨fun h => ⟨p', rfl, h⟩, fun ⟨p'', heq, h⟩ => by cases heq; exact h⟩
  | inr q' => exact ⟨fun h => h.elim, fun ⟨_, heq, _⟩ => by cases heq⟩

/-- A step out of an `inr` state of the sum stays in the right summand. -/
theorem sum_step_inr_iff (L₁ : LTS S₁ Act) (L₂ : LTS S₂ Act) (q : S₂) (a : Act)
    (t : S₁ ⊕ S₂) : (L₁.sum L₂).step (.inr q) a t ↔ ∃ q', t = .inr q' ∧ L₂.step q a q' := by
  cases t with
  | inl p' => exact ⟨fun h => h.elim, fun ⟨_, heq, _⟩ => by cases heq⟩
  | inr q' => exact ⟨fun h => ⟨q', rfl, h⟩, fun ⟨q'', heq, h⟩ => by cases heq; exact h⟩

/-- `CrossBisimilar L₁ L₂ p q`: state `p` of `L₁` is strongly bisimilar to state
`q` of `L₂`, i.e. `inl p ~ inr q` in the disjoint-union LTS. -/
def CrossBisimilar (L₁ : LTS S₁ Act) (L₂ : LTS S₂ Act) (p : S₁) (q : S₂) : Prop :=
  Bisimilar (L₁.sum L₂) (.inl p) (.inr q)

/-- A relation lifted to the sum so that `inl`/`inr` pairs (in either order) carry
`R`; same-side pairs carry nothing. -/
def crossRel (R : S₁ → S₂ → Prop) : (S₁ ⊕ S₂) → (S₁ ⊕ S₂) → Prop
  | .inl a, .inr b => R a b
  | .inr b, .inl a => R a b
  | _, _ => False

/-- **Cross-bisimilarity builder.** A relation `R` between the two state spaces
whose `L₁`-moves are answered by `R`-related `L₂`-moves and vice versa witnesses
`CrossBisimilar` on every related pair. -/
theorem crossBisimilar_of {L₁ : LTS S₁ Act} {L₂ : LTS S₂ Act} {R : S₁ → S₂ → Prop}
    (hfwd : ∀ {a b}, R a b → ∀ l a', L₁.step a l a' → ∃ b', L₂.step b l b' ∧ R a' b')
    (hbwd : ∀ {a b}, R a b → ∀ l b', L₂.step b l b' → ∃ a', L₁.step a l a' ∧ R a' b')
    {p : S₁} {q : S₂} (h : R p q) : CrossBisimilar L₁ L₂ p q := by
  refine ⟨crossRel R, ?_, h⟩
  rintro (x | x) (y | y) hxy <;> simp only [crossRel] at hxy
  · -- inl a, inr b
    refine ⟨fun l s' hs => ?_, fun l s' hs => ?_⟩
    · rw [sum_step_inl_iff] at hs
      obtain ⟨a', rfl, ha'⟩ := hs
      obtain ⟨b', hb', hr⟩ := hfwd hxy l a' ha'
      exact ⟨.inr b', (sum_step_inr_iff _ _ _ _ _).mpr ⟨b', rfl, hb'⟩, hr⟩
    · rw [sum_step_inr_iff] at hs
      obtain ⟨b', rfl, hb'⟩ := hs
      obtain ⟨a', ha', hr⟩ := hbwd hxy l b' hb'
      exact ⟨.inl a', (sum_step_inl_iff _ _ _ _ _).mpr ⟨a', rfl, ha'⟩, hr⟩
  · -- inr b, inl a
    refine ⟨fun l s' hs => ?_, fun l s' hs => ?_⟩
    · rw [sum_step_inr_iff] at hs
      obtain ⟨b', rfl, hb'⟩ := hs
      obtain ⟨a', ha', hr⟩ := hbwd hxy l b' hb'
      exact ⟨.inl a', (sum_step_inl_iff _ _ _ _ _).mpr ⟨a', rfl, ha'⟩, hr⟩
    · rw [sum_step_inl_iff] at hs
      obtain ⟨a', rfl, ha'⟩ := hs
      obtain ⟨b', hb', hr⟩ := hfwd hxy l a' ha'
      exact ⟨.inr b', (sum_step_inr_iff _ _ _ _ _).mpr ⟨b', rfl, hb'⟩, hr⟩

/-! ## The quotient LTS -/

/-- The **quotient LTS** of `L` by a setoid `st`: states are equivalence classes,
and `⟦s⟧ —a→ ⟦s'⟧` iff some representatives take an `a`-step `s —a→ s'`. -/
def quot (L : LTS S Act) (st : Setoid S) : LTS (Quotient st) Act where
  step t a t' := ∃ s s', Quotient.mk st s = t ∧ Quotient.mk st s' = t' ∧ L.step s a s'

/-- A representative step lifts to a step between classes in the quotient LTS. -/
theorem quot_step_mk (L : LTS S Act) (st : Setoid S) {s s' : S} {a : Act}
    (h : L.step s a s') : (L.quot st).step (Quotient.mk st s) a (Quotient.mk st s') :=
  ⟨s, s', rfl, rfl, h⟩

/-- **The quotient-bisimilarity engine.** When the setoid relation is a strong
bisimulation on `L`, every state `s` is strongly bisimilar to its class `⟦s⟧` in
the quotient LTS (a cross-system bisimilarity). -/
theorem crossBisimilar_quot (L : LTS S Act) (st : Setoid S)
    (hbis : IsBisimulation L st.r) (s : S) :
    CrossBisimilar L (L.quot st) s (Quotient.mk st s) := by
  refine crossBisimilar_of (R := fun a t => Quotient.mk st a = t)
    (p := s) (q := Quotient.mk st s) ?_ ?_ rfl
  · rintro a t rfl l a' ha'
    exact ⟨Quotient.mk st a', quot_step_mk L st ha', rfl⟩
  · rintro a t rfl l t' ⟨s₀, s₁, hs0, hs1, hstep⟩
    have heq : st.r a s₀ := Quotient.exact hs0.symm
    obtain ⟨_, h2⟩ := hbis heq
    obtain ⟨a', ha', hrel⟩ := h2 l s₁ hstep
    exact ⟨a', ha', (Quotient.sound hrel).trans hs1⟩

/-- **Bisimilarity descends to and is reflected by the quotient.** When the
setoid is a strong bisimulation on `L`, two states are strongly bisimilar in `L`
iff their classes are strongly bisimilar in the quotient LTS. This reduces a
bisimilarity question on `L` to one on `L/≈` (e.g. an infinite timed system to a
finite region graph). -/
theorem bisimilar_quot_iff (L : LTS S Act) (st : Setoid S)
    (hbis : IsBisimulation L st.r) (s s' : S) :
    Bisimilar (L.quot st) (Quotient.mk st s) (Quotient.mk st s') ↔ Bisimilar L s s' := by
  constructor
  · intro hq
    refine IsBisimulation.le_bisimilar
      (R := fun x y => Bisimilar (L.quot st) (Quotient.mk st x) (Quotient.mk st y)) ?_ hq
    rintro x y hxy
    obtain ⟨h1, h2⟩ := isBisimulation_bisimilar hxy
    refine ⟨fun a x' hx => ?_, fun a y' hy => ?_⟩
    · obtain ⟨t', hQstep, hQrel⟩ := h1 a (Quotient.mk st x') (quot_step_mk L st hx)
      obtain ⟨y₀, y₁, hy0, hy1, hstepy⟩ := hQstep
      obtain ⟨_, hb2⟩ := hbis (Quotient.exact hy0.symm)
      obtain ⟨y', hy', hrel⟩ := hb2 a y₁ hstepy
      refine ⟨y', hy', ?_⟩
      show Bisimilar (L.quot st) (Quotient.mk st x') (Quotient.mk st y')
      rw [show Quotient.mk st y' = t' from (Quotient.sound hrel).trans hy1]; exact hQrel
    · obtain ⟨t', hQstep, hQrel⟩ := h2 a (Quotient.mk st y') (quot_step_mk L st hy)
      obtain ⟨x₀, x₁, hx0, hx1, hstepx⟩ := hQstep
      obtain ⟨_, hb2⟩ := hbis (Quotient.exact hx0.symm)
      obtain ⟨x', hx', hrel⟩ := hb2 a x₁ hstepx
      refine ⟨x', hx', ?_⟩
      show Bisimilar (L.quot st) (Quotient.mk st x') (Quotient.mk st y')
      rw [show Quotient.mk st x' = t' from (Quotient.sound hrel).trans hx1]; exact hQrel
  · intro hL
    refine IsBisimulation.le_bisimilar
      (R := fun u w => ∃ x y, Quotient.mk st x = u ∧ Quotient.mk st y = w ∧ Bisimilar L x y)
      ?_ ⟨s, s', rfl, rfl, hL⟩
    rintro u w ⟨x, y, rfl, rfl, hxy⟩
    refine ⟨fun a u' hu => ?_, fun a w' hw => ?_⟩
    · obtain ⟨x₀, x₁, hx0, hx1, hstepx⟩ := hu
      have hxx0 : Bisimilar L x x₀ := hbis.le_bisimilar (Quotient.exact hx0.symm)
      obtain ⟨_, hb2⟩ := isBisimulation_bisimilar hxx0
      obtain ⟨x₂, hx2, hx2rel⟩ := hb2 a x₁ hstepx
      obtain ⟨hf, _⟩ := isBisimulation_bisimilar hxy
      obtain ⟨y₂, hy2, hy2rel⟩ := hf a x₂ hx2
      exact ⟨Quotient.mk st y₂, quot_step_mk L st hy2, x₁, y₂, hx1, rfl,
        hx2rel.symm.trans hy2rel⟩
    · obtain ⟨y₀, y₁, hy0, hy1, hstepy⟩ := hw
      have hyy0 : Bisimilar L y y₀ := hbis.le_bisimilar (Quotient.exact hy0.symm)
      obtain ⟨_, hb2⟩ := isBisimulation_bisimilar hyy0
      obtain ⟨y₂, hy2, hy2rel⟩ := hb2 a y₁ hstepy
      obtain ⟨_, hbk⟩ := isBisimulation_bisimilar hxy
      obtain ⟨x₂, hx2, hx2rel⟩ := hbk a y₂ hy2
      exact ⟨Quotient.mk st x₂, quot_step_mk L st hx2, x₂, y₁, rfl, hy1,
        hx2rel.trans hy2rel⟩

/-! ## Reachability transfer through the quotient -/

/-- Forward: a reachability path lifts to the quotient LTS. -/
theorem reachable_quot_mk (L : LTS S Act) (st : Setoid S) {s s' : S}
    (h : L.Reachable s s') :
    (L.quot st).Reachable (Quotient.mk st s) (Quotient.mk st s') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      obtain ⟨a, ha⟩ := hstep
      exact ih.tail ⟨a, quot_step_mk L st ha⟩

/-- Backward (needs the setoid to be a bisimulation): a quotient reachability path
from `⟦s⟧` is realised by an `L`-path from `s` to some representative of the
target class. -/
theorem reachable_quot_reflect (L : LTS S Act) (st : Setoid S)
    (hbis : IsBisimulation L st.r) {s : S} {t : Quotient st}
    (h : (L.quot st).Reachable (Quotient.mk st s) t) :
    ∃ s', Quotient.mk st s' = t ∧ L.Reachable s s' := by
  induction h with
  | refl => exact ⟨s, rfl, Relation.ReflTransGen.refl⟩
  | @tail u v _ hstep ih =>
      obtain ⟨s₁, hs1, hreach⟩ := ih
      obtain ⟨l, a, b, ha, hb, hstepL⟩ := hstep
      have heq : st.r s₁ a := Quotient.exact (hs1.trans ha.symm)
      obtain ⟨_, h2⟩ := hbis heq
      obtain ⟨s₂, hs2, hrel⟩ := h2 l b hstepL
      exact ⟨s₂, (Quotient.sound hrel).trans hb, hreach.tail ⟨l, hs2⟩⟩

/-- **Reachability transfer** (needs the setoid to be a bisimulation): `s` reaches
a representative of class `t` in `L` iff `⟦s⟧` reaches `t` in the quotient LTS. -/
theorem reachable_quot_iff (L : LTS S Act) (st : Setoid S)
    (hbis : IsBisimulation L st.r) {s : S} {t : Quotient st} :
    (L.quot st).Reachable (Quotient.mk st s) t ↔
      ∃ s', Quotient.mk st s' = t ∧ L.Reachable s s' := by
  refine ⟨reachable_quot_reflect L st hbis, ?_⟩
  rintro ⟨s', rfl, hreach⟩
  exact reachable_quot_mk L st hreach

end LTS

end DeepWiki.ReactiveSystems
