import DeepWiki.ReactiveSystems.HmlRecursion

/-! # A game characterisation for HML with recursion
The model-checking game for Hennessy–Milner logic with one
recursion variable `X` (defined `X =max F` or `X =min F`). Game configurations
are `(state, subformula)` pairs; the attacker tries to refute `s ⊨ F`, the
defender to establish it. The book defers the operational (infinite-play)
soundness to Stirling (2001); here we characterise the defender's winning region
through the **fixed-point semantics** — the greatest fixed point of the game
functional for a largest-fixed-point variable (a safety game), the least for a
least-fixed-point variable (a reachability game) — which is the standard
equivalent of the operational formulation. A defender winning strategy is a
post-fixed-point *invariant* (`DefenderInvariant`), exactly as for the
bisimulation game. The winning region coincides with HML satisfaction:
`gfp_defGameFun_eq` / `lfp_defGameFun_eq`. -/

namespace DeepWiki.ReactiveSystems

namespace LTS

variable {Proc Act : Type*}

/-- The model-checking game functional for HML with one recursion variable `X`
whose body is `F`: the one-step defender-favourable condition on configurations
`(state, subformula)`. A configuration `(s, var)` unfolds to `(s, F)`. -/
def defGameFun (L : LTS Proc Act) (F : HMLR Act) :
    Set (Proc × HMLR Act) →o Set (Proc × HMLR Act) where
  toFun W := {c | (match c.2 with
    | HMLR.tt => True
    | HMLR.ff => False
    | HMLR.and G1 G2 => (c.1, G1) ∈ W ∧ (c.1, G2) ∈ W
    | HMLR.or G1 G2 => (c.1, G1) ∈ W ∨ (c.1, G2) ∈ W
    | HMLR.dia a H => ∃ s', L.step c.1 a s' ∧ (s', H) ∈ W
    | HMLR.box a H => ∀ s', L.step c.1 a s' → (s', H) ∈ W
    | HMLR.var => (c.1, F) ∈ W)}
  monotone' := by
    intro W W' hWW' c hc
    obtain ⟨s, G⟩ := c
    cases G with
    | var => exact hWW' hc
    | tt => exact hc
    | ff => exact hc
    | and G1 G2 => exact ⟨hWW' hc.1, hWW' hc.2⟩
    | or G1 G2 => exact hc.imp (fun h => hWW' h) (fun h => hWW' h)
    | dia a H => obtain ⟨s', hstep, hmem⟩ := hc; exact ⟨s', hstep, hWW' hmem⟩
    | box a H => exact fun s' hstep => hWW' (hc s' hstep)

/-- The satisfaction relation as a set of game configurations, with the recursion
variable interpreted as `S`: `(s, G)` holds iff `s ∈ O_G(S)`. -/
def satConfig (L : LTS Proc Act) (_F : HMLR Act) (S : Set Proc) :
    Set (Proc × HMLR Act) :=
  {c | c.1 ∈ denotR L c.2 S}

/-- For any fixed point `S` of `O_F`, the satisfaction set at `S` is a fixed point
of the game functional. -/
theorem defGameFun_satConfig (L : LTS Proc Act) (F : HMLR Act) {S : Set Proc}
    (hS : denotR L F S = S) :
    defGameFun L F (satConfig L F S) = satConfig L F S := by
  apply Set.ext
  intro c
  obtain ⟨s, G⟩ := c
  cases G with
  | var =>
    show (s, F) ∈ satConfig L F S ↔ s ∈ denotR L HMLR.var S
    show s ∈ denotR L F S ↔ s ∈ S
    rw [hS]
  | tt => exact Iff.rfl
  | ff => exact Iff.rfl
  | and G1 G2 => exact Iff.rfl
  | or G1 G2 => exact Iff.rfl
  | dia a H => exact Iff.rfl
  | box a H => exact Iff.rfl

/-! ## MAX characterisation (greatest fixed point) -/

/-- The defender's winning region — the greatest
fixed point of the game functional — is exactly the satisfaction set at the
greatest fixed point `recMax` of the body. -/
theorem gfp_defGameFun_eq (L : LTS Proc Act) (F : HMLR Act) :
    (defGameFun L F).gfp = satConfig L F (recMax L F) := by
  apply le_antisymm
  · -- gfp ≤ satConfig recMax
    set W := (defGameFun L F).gfp with hW
    set V : Set Proc := {s | (s, HMLR.var) ∈ W} with hV
    have hWeq : defGameFun L F W = W := (defGameFun L F).map_gfp
    have unfold : ∀ c : Proc × HMLR Act, c ∈ W ↔ c ∈ defGameFun L F W :=
      fun c => (Set.ext_iff.mp hWeq c).symm
    have key : ∀ (G : HMLR Act) (s : Proc), (s, G) ∈ W → s ∈ denotR L G V := by
      intro G
      induction G with
      | var => intro s hs; exact hs
      | tt => intro s _; exact Set.mem_univ s
      | ff =>
        intro s hs
        have : (s, HMLR.ff) ∈ defGameFun L F W := (unfold _).mp hs
        exact absurd this (by simp [defGameFun])
      | and G1 G2 ihG1 ihG2 =>
        intro s hs
        have hs' : (s, HMLR.and G1 G2) ∈ defGameFun L F W := (unfold _).mp hs
        exact ⟨ihG1 s hs'.1, ihG2 s hs'.2⟩
      | or G1 G2 ihG1 ihG2 =>
        intro s hs
        have hs' : (s, HMLR.or G1 G2) ∈ defGameFun L F W := (unfold _).mp hs
        exact hs'.imp (fun h => ihG1 s h) (fun h => ihG2 s h)
      | dia a H ihH =>
        intro s hs
        have hs' : (s, HMLR.dia a H) ∈ defGameFun L F W := (unfold _).mp hs
        obtain ⟨s', hstep, hmem⟩ := hs'
        exact ⟨s', hstep, ihH s' hmem⟩
      | box a H ihH =>
        intro s hs
        have hs' : (s, HMLR.box a H) ∈ defGameFun L F W := (unfold _).mp hs
        exact fun s' hstep => ihH s' (hs' s' hstep)
    have hVle : V ≤ denotR L F V := by
      intro s hs
      have hvar : (s, HMLR.var) ∈ W := hs
      have hvar' : (s, HMLR.var) ∈ defGameFun L F W := (unfold _).mp hvar
      have hF : (s, F) ∈ W := hvar'
      exact key F s hF
    have hVrecMax : V ≤ recMax L F := (denotRHom L F).le_gfp hVle
    intro c hc
    obtain ⟨s, G⟩ := c
    have : s ∈ denotR L G V := key G s hc
    exact denotR_mono L G hVrecMax this
  · -- satConfig recMax ≤ gfp
    have hfp : defGameFun L F (satConfig L F (recMax L F)) = satConfig L F (recMax L F) :=
      defGameFun_satConfig L F (denotR_recMax L F)
    exact (defGameFun L F).le_gfp (le_of_eq hfp.symm)

/-- The defender wins the game from `(s, G)` for
`X =max F` iff `s` satisfies `G` under the greatest-fixed-point interpretation of
`X`. -/
theorem game_characterization_max (L : LTS Proc Act) (F : HMLR Act) (s : Proc)
    (G : HMLR Act) :
    (s, G) ∈ (defGameFun L F).gfp ↔ s ∈ denotR L G (recMax L F) := by
  rw [gfp_defGameFun_eq]
  exact Iff.rfl

/-- A defender invariant in the model-checking game: a post-fixed point of the
game functional (every configuration is locally defender-favourable, staying in
the set). -/
def DefenderInvariant (L : LTS Proc Act) (F : HMLR Act)
    (W : Set (Proc × HMLR Act)) : Prop :=
  W ≤ defGameFun L F W

/-- The defender wins the `X =max F` game from `(s, G)`: some defender invariant
contains the configuration. -/
def DefenderWinsMax (L : LTS Proc Act) (F : HMLR Act) (s : Proc) (G : HMLR Act) :
    Prop :=
  ∃ W, DefenderInvariant L F W ∧ (s, G) ∈ W

/-- Strategy form, mirrors `DefenderWins`. The defender has
a winning invariant from `(s, G)` iff `s ∈ O_G(recMax F)`. -/
theorem defenderWinsMax_iff (L : LTS Proc Act) (F : HMLR Act) (s : Proc)
    (G : HMLR Act) :
    DefenderWinsMax L F s G ↔ s ∈ denotR L G (recMax L F) := by
  constructor
  · rintro ⟨W, hInv, hmem⟩
    have hle : W ≤ (defGameFun L F).gfp := (defGameFun L F).le_gfp hInv
    exact (game_characterization_max L F s G).mp (hle hmem)
  · intro hs
    refine ⟨satConfig L F (recMax L F), ?_, ?_⟩
    · have hfp : defGameFun L F (satConfig L F (recMax L F)) =
          satConfig L F (recMax L F) := defGameFun_satConfig L F (denotR_recMax L F)
      exact le_of_eq hfp.symm
    · exact hs

/-! ## MIN characterisation (least fixed point) -/

/-- The dual: the least fixed point of the game
functional is the satisfaction set at the least fixed point `recMin` of the body. -/
theorem lfp_defGameFun_eq (L : LTS Proc Act) (F : HMLR Act) :
    (defGameFun L F).lfp = satConfig L F (recMin L F) := by
  apply le_antisymm
  · -- lfp ≤ satConfig recMin
    have hfp : defGameFun L F (satConfig L F (recMin L F)) = satConfig L F (recMin L F) :=
      defGameFun_satConfig L F (denotR_recMin L F)
    exact (defGameFun L F).lfp_le (le_of_eq hfp)
  · -- satConfig recMin ≤ lfp
    set W := (defGameFun L F).lfp with hW
    set V : Set Proc := {s | (s, HMLR.var) ∈ W} with hV
    have hWeq : defGameFun L F W = W := (defGameFun L F).map_lfp
    have fold : ∀ c : Proc × HMLR Act, c ∈ defGameFun L F W → c ∈ W :=
      fun c => (Set.ext_iff.mp hWeq c).mp
    have key : ∀ (G : HMLR Act) (s : Proc), s ∈ denotR L G V → (s, G) ∈ W := by
      intro G
      induction G with
      | var => intro s hs; exact hs
      | tt =>
        intro s _
        exact fold _ (by simp [defGameFun])
      | ff => intro s hs; exact absurd hs (by simp [denotR])
      | and G1 G2 ihG1 ihG2 =>
        intro s hs
        exact fold _ ⟨ihG1 s hs.1, ihG2 s hs.2⟩
      | or G1 G2 ihG1 ihG2 =>
        intro s hs
        exact fold _ (hs.imp (fun h => ihG1 s h) (fun h => ihG2 s h))
      | dia a H ihH =>
        intro s hs
        obtain ⟨s', hstep, hmem⟩ := hs
        exact fold _ ⟨s', hstep, ihH s' hmem⟩
      | box a H ihH =>
        intro s hs
        exact fold _ (fun s' hstep => ihH s' (hs s' hstep))
    have hrecMinV : recMin L F ≤ V := by
      refine (denotRHom L F).lfp_le ?_
      intro s hs
      have hF : (s, F) ∈ W := key F s hs
      exact fold _ hF
    intro c hc
    obtain ⟨s, G⟩ := c
    have : s ∈ denotR L G V := denotR_mono L G hrecMinV hc
    exact key G s this

/-- For `X =min F`: `(s, G)` is in the least
fixed point of the game functional iff `s` satisfies `G` under the
least-fixed-point interpretation of `X`. -/
theorem game_characterization_min (L : LTS Proc Act) (F : HMLR Act) (s : Proc)
    (G : HMLR Act) :
    (s, G) ∈ (defGameFun L F).lfp ↔ s ∈ denotR L G (recMin L F) := by
  rw [lfp_defGameFun_eq]
  exact Iff.rfl

end LTS

end DeepWiki.ReactiveSystems
