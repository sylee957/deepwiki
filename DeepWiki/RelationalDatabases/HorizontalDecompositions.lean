import DeepWiki.RelationalDatabases.FunctionalDependencies

/-! # Horizontal decompositions and afunctional dependencies
A horizontal decomposition splits a relation into the tuples where a functional dependency holds
and the "exceptions" where it provably fails. The exception side is governed by an *afunctional
dependency* `X ↛ Y` (Def 5.4): every tuple has another tuple agreeing on `X` but differing on
`Y` (every `X`-value carries at least two `Y`-values). The sound mixed inference rules FA1, FA2
(turning a functional dependency and an ad into a new ad) and A1 are proved at the row-set level.

The conflict notion (a constraint set whose only model is empty, with the canonical conflict
`{X → Y, X ↛ Y}`) and Armstrong / strong-Armstrong relations are defined, with strong-Armstrong ⟹
Armstrong on a nonempty instance, and the existence of a strong Armstrong relation (Thm 5.1) is
proved by Fagin's direct-product construction. The membership algorithm and the inheritance of
dependencies under decomposition are layered on later. -/

namespace DeepWiki

universe u v

variable {Att : Type u} {Val : Type v} {Ω : Finset Att}

/-- A set of tuples `s ⊆ rs` is *X-complete* (Def 5.1): tuples of `s` have different `X`-values
from those outside `s`. -/
def IsXComplete (X : Finset Att) (s rs : Table Ω Val) : Prop :=
  s ⊆ rs ∧ ∀ t₁ ∈ s, ∀ t₂ ∈ rs \ s, ¬ Agree X t₁ t₂

/-- A set of tuples is *X-unique* (Def 5.1): all its tuples share one `X`-value. -/
def IsXUnique (X : Finset Att) (s : Table Ω Val) : Prop :=
  ∀ t₁ ∈ s, ∀ t₂ ∈ s, Agree X t₁ t₂

/-- A row set satisfies the *afunctional dependency* `X ↛ Y` (Def 5.4): every tuple has another
tuple agreeing on `X` but differing on `Y` — so every `X`-value carries at least two `Y`-values.
Holds vacuously on the empty instance. -/
def SatisfiesAd (r : Table Ω Val) (X Y : Finset Att) : Prop :=
  ∀ t ∈ r, ∃ t' ∈ r, Agree X t t' ∧ ¬ Agree Y t t'

variable {r : Table Ω Val} {X Y Z V W : Finset Att}

/-- Rule FA1 (Lemma 5.3): a functional dependency `X → Y` and an ad `X ↛ Z` give the ad
`Y ↛ Z`. -/
theorem satisfiesAd_fa1 (hfd : SatisfiesFd r X Y) (had : SatisfiesAd r X Z) :
    SatisfiesAd r Y Z := by
  intro t ht
  obtain ⟨t', ht', hX, hZ⟩ := had t ht
  exact ⟨t', ht', hfd t ht t' ht' hX, hZ⟩

/-- Rule FA2 (Lemma 5.3): a functional dependency `Y → Z` and an ad `X ↛ Z` give the ad
`X ↛ Y`. -/
theorem satisfiesAd_fa2 (hfd : SatisfiesFd r Y Z) (had : SatisfiesAd r X Z) :
    SatisfiesAd r X Y := by
  intro t ht
  obtain ⟨t', ht', hX, hZ⟩ := had t ht
  exact ⟨t', ht', hX, fun hY => hZ (hfd t ht t' ht' hY)⟩

/-- Rule A1 (Lemma 5.3): from the ad `X ∪ V ↛ Y ∪ W` with `W ⊆ V`, the ad `X ↛ Y`. -/
theorem satisfiesAd_a1 [DecidableEq Att] (hW : W ⊆ V)
    (had : SatisfiesAd r (X ∪ V) (Y ∪ W)) : SatisfiesAd r X Y := by
  intro t ht
  obtain ⟨t', ht', hXV, hYW⟩ := had t ht
  refine ⟨t', ht', Agree.mono Finset.subset_union_left hXV, fun hY => hYW ?_⟩
  exact agree_union.mpr ⟨hY, Agree.mono (hW.trans Finset.subset_union_right) hXV⟩

/-- A relation satisfying both the functional dependency `X → Y` and the afunctional dependency
`X ↛ Y` must be empty: a tuple would need a partner agreeing on `X` (hence on `Y`, by the fd) yet
differing on `Y`. So `{X → Y, X ↛ Y}` is the canonical conflicting set. -/
theorem eq_empty_of_satisfiesFd_satisfiesAd (h : SatisfiesFd r X Y) (had : SatisfiesAd r X Y) :
    r = ∅ := by
  ext t
  simp only [Set.mem_empty_iff_false, iff_false]
  intro ht
  obtain ⟨t', ht', hX, hnY⟩ := had t ht
  exact hnY (h t ht t' ht' hX)

/-- A set of functional dependencies `F` and afunctional dependencies `A` is *in conflict*
(Def 5.6): the empty instance is the only one satisfying all of them. -/
def InConflict (Ω : Finset Att) (Val : Type v) (F A : FdSet Att) : Prop :=
  ∀ r : Table Ω Val, (∀ fd ∈ F, SatisfiesFd r fd.1 fd.2) →
    (∀ ad ∈ A, SatisfiesAd r ad.1 ad.2) → r = ∅

/-- An instance is an *Armstrong relation* for `F` (Def 5.7): the functional dependencies holding
in it are exactly the consequences of `F`. -/
def IsArmstrongRelation (Ω : Finset Att) (Val : Type v) (F : FdSet Att) (r : Table Ω Val) : Prop :=
  ∀ X Y : Finset Att, SatisfiesFd r X Y ↔ Implies Ω Val F X Y

/-- An instance is a *strong Armstrong relation* for `F` (Def 5.8): every consequence fd of `F`
holds, and every non-consequence fd `X → Y` fails maximally — its afunctional dependency `X ↛ Y`
holds. -/
def IsStrongArmstrong (Ω : Finset Att) (Val : Type v) (F : FdSet Att) (r : Table Ω Val) : Prop :=
  (∀ X Y, Implies Ω Val F X Y → SatisfiesFd r X Y) ∧
    (∀ X Y, ¬ Implies Ω Val F X Y → SatisfiesAd r X Y)

/-- A nonempty strong Armstrong relation is an Armstrong relation: a non-consequence fd carries its
afunctional dependency, which (on a nonempty instance) forbids the fd from holding. -/
theorem isArmstrongRelation_of_isStrongArmstrong {F : FdSet Att} (hne : r.Nonempty)
    (h : IsStrongArmstrong Ω Val F r) : IsArmstrongRelation Ω Val F r := by
  refine fun X Y => ⟨fun hfd => ?_, h.1 X Y⟩
  by_contra hni
  exact (Set.nonempty_iff_ne_empty.mp hne)
    (eq_empty_of_satisfiesFd_satisfiesAd hfd (h.2 X Y hni))

open Classical in
/-- The *off-closure* factor tuple for `Z`: `false` on the fd-closure of `Z`, `true` elsewhere — the
non-trivial row of the two-tuple factor relation `r_Z`. -/
noncomputable def armOff [DecidableEq Att] (F : FdSet Att) (Z : Finset Att) : Tuple Ω Bool :=
  fun a => if Derives F Z {a.val} then false else true

open Classical in
/-- **Theorem 5.1** (§5.1, p.137): for every set `F` of functional dependencies (over `Ω`) there is
a strong Armstrong relation. The witness is Fagin's direct product `⊗_Z r_Z` of the two-tuple
factors `r_Z = {const false, armOff F Z}` over all attribute sets `Z`, realised with value type
`Finset Att → Bool` (one bit per factor): an fd holds in the product iff in every factor — so `F`
and all its consequences hold — and a non-consequence `X → Y` is refuted by factor `X`, giving the
afunctional dependency `X ↛ Y`. -/
theorem exists_strongArmstrong [DecidableEq Att] (F : FdSet Att)
    (hSC : ∀ fd ∈ F, fd.1 ⊆ Ω ∧ fd.2 ⊆ Ω) :
    ∃ r : Table Ω (Finset Att → Bool), IsStrongArmstrong Ω (Finset Att → Bool) F r := by
  classical
  set z0 : Tuple Ω Bool := (fun _ => false) with hz0
  set Arm : Table Ω (Finset Att → Bool) :=
    {T | ∀ Z, (fun a => T a Z) = z0 ∨ (fun a => T a Z) = armOff F Z} with hArm
  -- two factor rows agree at `a` exactly on the fd-closure of `Z`
  have hfeq : ∀ (Z : Finset Att) (a : {x // x ∈ Ω}),
      z0 a = armOff F Z a ↔ Derives F Z {a.val} := by
    intro Z a
    simp only [hz0, armOff]
    by_cases h : Derives F Z {a.val} <;> simp [h]
  -- on `X`, every factor row of `r_X` agrees with `const false`
  have honX : ∀ (X : Finset Att) (c : Tuple Ω Bool), (c = z0 ∨ c = armOff F X) →
      ∀ a : {x // x ∈ Ω}, a.val ∈ X → c a = z0 a := by
    intro X c hc a ha
    have haggr : z0 a = armOff F X a :=
      (hfeq X a).mpr (Derives.trivial (Finset.singleton_subset_iff.mpr ha))
    rcases hc with rfl | rfl
    · rfl
    · exact haggr.symm
  -- each factor relation satisfies every fd of `F`
  have hfactor : ∀ (Z V W : Finset Att), (V, W) ∈ F →
      ∀ c₁, (c₁ = z0 ∨ c₁ = armOff F Z) → ∀ c₂, (c₂ = z0 ∨ c₂ = armOff F Z) →
        Agree V c₁ c₂ → Agree W c₁ c₂ := by
    intro Z V W hVW c₁ hc₁ c₂ hc₂ hag
    have base : Agree V z0 (armOff F Z) → Agree W z0 (armOff F Z) := by
      intro hagV
      obtain ⟨hVΩ, _⟩ := hSC (V, W) hVW
      have hVcl : ∀ b ∈ V, Derives F Z {b} := fun b hb =>
        (hfeq Z ⟨b, hVΩ hb⟩).mp (hagV ⟨b, hVΩ hb⟩ hb)
      have hZW : Derives F Z W := (derives_of_forall_singleton hVcl).trans (Derives.base hVW)
      exact fun a ha =>
        (hfeq Z a).mpr (hZW.trans (Derives.trivial (Finset.singleton_subset_iff.mpr ha)))
    rcases hc₁ with rfl | rfl <;> rcases hc₂ with rfl | rfl
    · exact fun _ _ => rfl
    · exact base hag
    · exact (base hag.symm).symm
    · exact fun _ _ => rfl
  -- `Arm` satisfies `F`
  have hArmF : ∀ fd ∈ F, SatisfiesFd Arm fd.1 fd.2 := by
    rintro ⟨V, W⟩ hVW T₁ hT₁ T₂ hT₂ hag A hA
    funext Z
    exact hfactor Z V W hVW _ (hT₁ Z) _ (hT₂ Z)
      (fun a ha => congrFun (hag a ha) Z) A hA
  refine ⟨Arm, fun X Y h => h Arm hArmF, ?_⟩
  intro X Y hni
  -- a witness attribute of `Ω ∩ Y` off the fd-closure of `X`
  have hwit : ∃ a : {x // x ∈ Ω}, a.val ∈ Y ∧ ¬ Derives F X {a.val} := by
    by_contra hcon
    push Not at hcon
    exact hni fun r hr t₁ h₁ t₂ h₂ hag a ha =>
      derives_sound (hcon a ha) r hr t₁ h₁ t₂ h₂ hag a (Finset.mem_singleton_self _)
  obtain ⟨a₀, ha₀Y, ha₀nd⟩ := hwit
  have hne : z0 a₀ ≠ armOff F X a₀ := fun h => ha₀nd ((hfeq X a₀).mp h)
  intro T hT
  set cX : Tuple Ω Bool := (fun a => T a X) with hcX
  have hcXmem : cX = z0 ∨ cX = armOff F X := hT X
  set other : Tuple Ω Bool := (if cX = z0 then armOff F X else z0) with hother
  have hothermem : other = z0 ∨ other = armOff F X := by
    by_cases h : cX = z0 <;> simp [hother, h]
  refine ⟨fun a Z => if Z = X then other a else T a Z, ?_, ?_, ?_⟩
  · -- the renamed tuple is still in `Arm`
    intro Z
    by_cases hZX : Z = X
    · subst Z
      have he : (fun a => if X = X then other a else T a X) = other := by funext a; simp
      rw [he]; exact hothermem
    · have he : (fun a => if Z = X then other a else T a Z) = (fun a => T a Z) := by
        funext a; simp [hZX]
      rw [he]; exact hT Z
  · -- agrees with `T` on `X`
    intro a ha
    funext Z
    by_cases hZX : Z = X
    · subst Z
      show T a X = if X = X then other a else T a X
      rw [if_pos rfl]
      exact (honX X cX hcXmem a ha).trans (honX X other hothermem a ha).symm
    · simp only [if_neg hZX]
  · -- differs from `T` on `Y` (at `a₀`)
    intro hagY
    have heq : cX a₀ = other a₀ := by
      have := congrFun (hagY a₀ ha₀Y) X
      simpa [if_pos, hcX] using this
    rcases hcXmem with hc | hc
    · rw [hc] at heq
      rw [hother, if_pos hc] at heq
      exact hne heq
    · rw [hc] at heq
      have hcne : cX ≠ z0 := fun h => hne (by rw [← hc, h])
      rw [hother, if_neg hcne] at heq
      exact hne heq.symm

end DeepWiki
