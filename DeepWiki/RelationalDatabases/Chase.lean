import DeepWiki.RelationalDatabases.RelationalAlgebra
import DeepWiki.RelationalDatabases.JoinDependencies

/-! # The chase: tableaux and the initial tableau
The chase decides whether a join dependency is implied by a set of fds and jds (Algorithm 3.4). It
works on *tableaux* — sets of rows whose entries are symbols, *distinguished* (`αA`, one per
attribute) or *undistinguished* (`βᴬᵢ`, per attribute and row). This file builds the data model
(Def 3.11), the initial tableau of a join dependency (Def 3.12), the all-distinguished goal row
whose presence signals success, and the valuation bridge sending a tableau to a relation instance.

The chase steps (the fd- and jd-rules of Algorithm 3.4), their iteration to a fixpoint, termination
and the correctness Theorem 3.15 (`chase(τ(J))` contains the distinguished row iff `SC ⊨ J`) are
layered on later. -/

namespace DeepWiki

universe u v

variable {Att : Type u} [DecidableEq Att] {Val : Type v} {Ω : Finset Att}

/-- A chase symbol (Def 3.11): a *distinguished* variable `αA` (one per attribute) or an
*undistinguished* variable `βᴬᵢ` (per attribute `A` and row index `i`). -/
inductive ChaseSymbol (Att : Type u) where
  /-- The distinguished variable `αA`. -/
  | dist : Att → ChaseSymbol Att
  /-- The undistinguished variable `βᴬᵢ`. -/
  | undist : Att → ℕ → ChaseSymbol Att
  deriving DecidableEq

/-- A *row* of `PRS` (Def 3.11): an assignment of a chase symbol to each attribute of `Ω`. -/
abbrev ChaseRow (Ω : Finset Att) : Type u := {a // a ∈ Ω} → ChaseSymbol Att

/-- A *tableau* (Def 3.11): a set of rows. -/
abbrev Tableau (Ω : Finset Att) : Type u := Set (ChaseRow Ω)

/-- The all-distinguished row `R` with `R(A) = αA`: its presence in the chased tableau signals that
the join dependency is implied (Algorithm 3.4's success condition). -/
def distRow (Ω : Finset Att) : ChaseRow Ω := fun a => ChaseSymbol.dist a.val

/-- The *initial tableau* `τ(J)` of a join dependency with components `comp` (Def 3.12): one row per
component, distinguished on the component and freshly undistinguished elsewhere. -/
def initialTableau {k : ℕ} (comp : Fin k → Finset Att) : Tableau Ω :=
  Set.range fun (i : Fin k) (a : {x // x ∈ Ω}) =>
    if a.val ∈ comp i then ChaseSymbol.dist a.val else ChaseSymbol.undist a.val i.val

/-- The initial tableau already contains the all-distinguished row exactly when some component
covers `Ω` — i.e. the join dependency is trivial and the chase succeeds immediately. -/
theorem distRow_mem_initialTableau_iff {k : ℕ} (comp : Fin k → Finset Att) :
    distRow Ω ∈ initialTableau comp ↔ ∃ i, ∀ a : {x // x ∈ Ω}, a.val ∈ comp i := by
  rw [initialTableau, Set.mem_range]
  refine exists_congr fun i => ?_
  rw [funext_iff]
  refine forall_congr' fun a => ?_
  by_cases hc : a.val ∈ comp i <;> simp [distRow, hc]

/-- A *valuation* sends chase symbols to data values. -/
abbrev Valuation (Att : Type u) (Val : Type v) : Type _ := ChaseSymbol Att → Val

/-- A valuation turns a row into a tuple. -/
def applyRow (ρ : Valuation Att Val) (ℓ : ChaseRow Ω) : Tuple Ω Val := fun a => ρ (ℓ a)

/-- A valuation turns a tableau into a relation instance (the image of its rows) — the bridge used
to relate the chased tableau to relations in the correctness proof of the chase. -/
def applyTableau (ρ : Valuation Att Val) (T : Tableau Ω) : Table Ω Val := applyRow ρ '' T

omit [DecidableEq Att] in
/-- Membership in the image relation: `t` comes from some tableau row under the valuation. -/
@[simp] theorem mem_applyTableau (ρ : Valuation Att Val) (T : Tableau Ω) (t : Tuple Ω Val) :
    t ∈ applyTableau ρ T ↔ ∃ ℓ ∈ T, applyRow ρ ℓ = t := by
  simp [applyTableau, Set.mem_image]

/-- The *jd-rule* chase step for `⋈[comp]` (Algorithm 3.4): add every row glued from a family of
tableau rows that pairwise agree on the component intersections. -/
def jdChaseStep {ℓ : ℕ} (comp : Fin ℓ → Finset Att) (T : Tableau Ω) : Tableau Ω :=
  T ∪ {R | ∃ rows : Fin ℓ → ChaseRow Ω, (∀ i, rows i ∈ T) ∧
    (∀ i j, ∀ a : {x // x ∈ Ω}, a.val ∈ comp i ∩ comp j → rows i a = rows j a) ∧
    ∀ i, ∀ a : {x // x ∈ Ω}, a.val ∈ comp i → R a = rows i a}

/-- The jd-rule only adds rows (the chase is extensive). -/
theorem subset_jdChaseStep {ℓ : ℕ} (comp : Fin ℓ → Finset Att) (T : Tableau Ω) :
    T ⊆ jdChaseStep comp T := Set.subset_union_left

/-- **Soundness of the jd-rule**: if the join dependency `⋈[comp]` already holds in the relation
represented by a tableau (under a valuation `ρ`), the jd-rule adds nothing new — every glued row
maps to a tuple already present. This is the invariant behind the chase's correctness. -/
theorem applyTableau_jdChaseStep_subset {ℓ : ℕ} (ρ : Valuation Att Val)
    (comp : Fin ℓ → Finset Att) (T : Tableau Ω)
    (hcover : ∀ a : {x // x ∈ Ω}, ∃ i, a.val ∈ comp i)
    (hjd : SatisfiesJd (applyTableau ρ T) comp) :
    applyTableau ρ (jdChaseStep comp T) ⊆ applyTableau ρ T := by
  rintro t ht
  rw [mem_applyTableau] at ht
  obtain ⟨L, hL, rfl⟩ := ht
  rcases hL with hLT | ⟨rows, hrows, hagree, hglue⟩
  · exact (mem_applyTableau _ _ _).mpr ⟨L, hLT, rfl⟩
  · have hfam : ∀ i, applyRow ρ (rows i) ∈ applyTableau ρ T :=
      fun i => (mem_applyTableau _ _ _).mpr ⟨rows i, hrows i, rfl⟩
    have hpair : ∀ i j, Agree (comp i ∩ comp j) (applyRow ρ (rows i)) (applyRow ρ (rows j)) :=
      fun i j a ha => by simp only [applyRow]; rw [hagree i j a ha]
    obtain ⟨v, hv, hvfam⟩ := hjd (fun i => applyRow ρ (rows i)) hfam hpair
    have hLv : applyRow ρ L = v := by
      funext a
      obtain ⟨i, hi⟩ := hcover a
      rw [hvfam i a hi]
      simp only [applyRow]
      rw [hglue i a hi]
    rw [hLv]; exact hv

/-- Apply a symbol substitution to a row. -/
def substRow (σ : ChaseSymbol Att → ChaseSymbol Att) (ℓ : ChaseRow Ω) : ChaseRow Ω :=
  fun a => σ (ℓ a)

/-- Apply a symbol substitution to a tableau — the form of every fd-rule step (Algorithm 3.4). -/
def substTableau (σ : ChaseSymbol Att → ChaseSymbol Att) (T : Tableau Ω) : Tableau Ω :=
  substRow σ '' T

omit [DecidableEq Att] in
/-- A `ρ`-invisible substitution does not change a row's image. -/
theorem applyRow_substRow (ρ : Valuation Att Val) (σ : ChaseSymbol Att → ChaseSymbol Att)
    (ℓ : ChaseRow Ω) (hσ : ∀ s, ρ (σ s) = ρ s) : applyRow ρ (substRow σ ℓ) = applyRow ρ ℓ := by
  funext a; simp only [applyRow, substRow]; exact hσ (ℓ a)

omit [DecidableEq Att] in
/-- **Soundness of any fd-rule step**: a substitution the valuation `ρ` cannot distinguish
(`ρ ∘ σ = ρ`) leaves the represented relation unchanged. -/
theorem applyTableau_substTableau_of_consistent (ρ : Valuation Att Val)
    (σ : ChaseSymbol Att → ChaseSymbol Att) (T : Tableau Ω) (hσ : ∀ s, ρ (σ s) = ρ s) :
    applyTableau ρ (substTableau σ T) = applyTableau ρ T := by
  unfold applyTableau substTableau
  rw [Set.image_image]
  exact Set.image_congr' fun ℓ => applyRow_substRow ρ σ ℓ hσ

/-- The fd-rule's merge substitution: identify symbol `s` with `t`. -/
def mergeSubst (s t : ChaseSymbol Att) : ChaseSymbol Att → ChaseSymbol Att :=
  fun x => if x = s then t else x

/-- Merging two symbols of equal `ρ`-value is `ρ`-invisible. -/
theorem consistent_mergeSubst (ρ : Valuation Att Val) {s t : ChaseSymbol Att} (h : ρ s = ρ t)
    (x : ChaseSymbol Att) : ρ (mergeSubst s t x) = ρ x := by
  unfold mergeSubst
  split
  · next hx => rw [hx]; exact h.symm
  · rfl

/-- Merging two symbols of equal `ρ`-value leaves the represented relation unchanged — the fd-rule
step is sound. -/
theorem applyTableau_mergeSubst (ρ : Valuation Att Val) {s t : ChaseSymbol Att} (T : Tableau Ω)
    (h : ρ s = ρ t) : applyTableau ρ (substTableau (mergeSubst s t) T) = applyTableau ρ T :=
  applyTableau_substTableau_of_consistent ρ _ T (consistent_mergeSubst ρ h)

omit [DecidableEq Att] in
/-- **The fd justifies its merges**: if `X → Y` holds in the represented relation and two rows of
the tableau agree symbolically on `X`, then on each attribute of `Y` their symbols have equal
`ρ`-value — so merging them (via `mergeSubst`/`applyTableau_mergeSubst`) is sound. -/
theorem fdMerge_value_eq (ρ : Valuation Att Val) {X Y : Finset Att} {T : Tableau Ω}
    (hfd : SatisfiesFd (applyTableau ρ T) X Y) {R₁ R₂ : ChaseRow Ω} (h₁ : R₁ ∈ T) (h₂ : R₂ ∈ T)
    (hX : ∀ a : {x // x ∈ Ω}, a.val ∈ X → R₁ a = R₂ a) {a : {x // x ∈ Ω}} (ha : a.val ∈ Y) :
    ρ (R₁ a) = ρ (R₂ a) :=
  hfd (applyRow ρ R₁) ((mem_applyTableau _ _ _).mpr ⟨R₁, h₁, rfl⟩)
    (applyRow ρ R₂) ((mem_applyTableau _ _ _).mpr ⟨R₂, h₂, rfl⟩)
    (fun b hb => by simp only [applyRow]; rw [hX b hb]) a ha

/-- **Model soundness of the jd-rule**: if the represented relation already sits inside a model `r`
of the join dependency, so does the relation after a jd-rule step — the chase never escapes a model
of `SC`. -/
theorem applyTableau_jdChaseStep_subset_model {k : ℕ} (ρ : Valuation Att Val)
    (comp : Fin k → Finset Att) {T : Tableau Ω} {r : Table Ω Val}
    (hsub : applyTableau ρ T ⊆ r) (hcover : ∀ a : {x // x ∈ Ω}, ∃ i, a.val ∈ comp i)
    (hjd : SatisfiesJd r comp) : applyTableau ρ (jdChaseStep comp T) ⊆ r := by
  rintro t ht
  rw [mem_applyTableau] at ht
  obtain ⟨L, hL, rfl⟩ := ht
  rcases hL with hLT | ⟨rows, hrows, hagree, hglue⟩
  · exact hsub ((mem_applyTableau _ _ _).mpr ⟨L, hLT, rfl⟩)
  · have hfam : ∀ i, applyRow ρ (rows i) ∈ r :=
      fun i => hsub ((mem_applyTableau _ _ _).mpr ⟨rows i, hrows i, rfl⟩)
    have hpair : ∀ i j, Agree (comp i ∩ comp j) (applyRow ρ (rows i)) (applyRow ρ (rows j)) :=
      fun i j a ha => by simp only [applyRow]; rw [hagree i j a ha]
    obtain ⟨v, hv, hvfam⟩ := hjd (fun i => applyRow ρ (rows i)) hfam hpair
    have hLv : applyRow ρ L = v := by
      funext a
      obtain ⟨i, hi⟩ := hcover a
      rw [hvfam i a hi]
      simp only [applyRow]
      rw [hglue i a hi]
    rw [hLv]; exact hv

/-- **Model soundness of the fd-rule**: an fd-rule merge of two equal-valued symbols keeps the
represented relation inside any model `r`. -/
theorem applyTableau_mergeSubst_subset_model (ρ : Valuation Att Val) {s t : ChaseSymbol Att}
    {T : Tableau Ω} {r : Table Ω Val} (hsub : applyTableau ρ T ⊆ r) (h : ρ s = ρ t) :
    applyTableau ρ (substTableau (mergeSubst s t) T) ⊆ r := by
  rw [applyTableau_mergeSubst ρ T h]; exact hsub

omit [DecidableEq Att] in
/-- A functional dependency holding in a relation holds in every subrelation. -/
theorem satisfiesFd_subset {r s : Table Ω Val} (hsr : s ⊆ r) {X Y : Finset Att}
    (h : SatisfiesFd r X Y) : SatisfiesFd s X Y :=
  fun t₁ h₁ t₂ h₂ => h t₁ (hsr h₁) t₂ (hsr h₂)

/-- One step of the chase relative to a set of fds and a set of (covering) jds (Algorithm 3.4):
either a jd-rule application or a fd-rule merge of two rows that agree symbolically on the fd's
left side. -/
inductive ChaseStep (fds : Set (Finset Att × Finset Att))
    (jds : Set (Σ k : ℕ, Fin k → Finset Att)) : Tableau Ω → Tableau Ω → Prop
  /-- The jd-rule for a (covering) jd of the set. -/
  | jd {k : ℕ} {comp : Fin k → Finset Att} (hmem : (⟨k, comp⟩ : Σ k, Fin k → Finset Att) ∈ jds)
      (hcov : ∀ a : {x // x ∈ Ω}, ∃ i, a.val ∈ comp i) {T : Tableau Ω} :
      ChaseStep fds jds T (jdChaseStep comp T)
  /-- The fd-rule for an fd of the set: merge the `A`-symbols of two `X`-agreeing rows. -/
  | fd {X Y : Finset Att} (hmem : (X, Y) ∈ fds) {T : Tableau Ω} {R₁ R₂ : ChaseRow Ω}
      (h₁ : R₁ ∈ T) (h₂ : R₂ ∈ T) (hX : ∀ a : {x // x ∈ Ω}, a.val ∈ X → R₁ a = R₂ a)
      {a : {x // x ∈ Ω}} (ha : a.val ∈ Y) :
      ChaseStep fds jds T (substTableau (mergeSubst (R₁ a) (R₂ a)) T)

/-- **Chase soundness (multi-step), the soundness half of Theorem 3.15**: along any chase
derivation, the represented relation stays inside a model `r` of all the fds and jds — so the chase
never produces a tuple absent from a model of `SC`. -/
theorem applyTableau_subset_of_chaseStar (ρ : Valuation Att Val) {r : Table Ω Val}
    {fds : Set (Finset Att × Finset Att)} {jds : Set (Σ k : ℕ, Fin k → Finset Att)}
    (hfd : ∀ XY ∈ fds, SatisfiesFd r XY.1 XY.2) (hjd : ∀ kc ∈ jds, SatisfiesJd r kc.2)
    {T T' : Tableau Ω} (hstar : Relation.ReflTransGen (ChaseStep fds jds) T T')
    (hsub : applyTableau ρ T ⊆ r) : applyTableau ρ T' ⊆ r := by
  induction hstar with
  | refl => exact hsub
  | tail _ hstep ih =>
    cases hstep with
    | jd hmem hcov => exact applyTableau_jdChaseStep_subset_model ρ _ ih hcov (hjd _ hmem)
    | fd hmem h₁ h₂ hX ha =>
      exact applyTableau_mergeSubst_subset_model ρ ih
        (fdMerge_value_eq ρ (satisfiesFd_subset ih (hfd _ hmem)) h₁ h₂ hX ha)

end DeepWiki
