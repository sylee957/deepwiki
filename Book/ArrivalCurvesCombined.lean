import Book.ArrivalCurvesMaximal
import Book.ArrivalCurvesMinimal
import Book.Additivity

/-! # Combining minimal and maximal arrival curves
From a maximal arrival curve `αᵘ` and a minimal one `αˡ` for `A`, the
max-plus deconvolution `ηᵘ = αᵘ ⊘̄ αˡ` is a (refined) maximal arrival curve and
the min-plus deconvolution `ηˡ = αˡ ⊘ αᵘ` is a (refined) minimal one. Under
sub- and super-additivity with `αᵘ 0 = αˡ 0 = 0`, the refinement reaches a
fixpoint in one step, so the iteration `ηᵢ₊₁ᵘ = ηᵢᵘ ⊘̄ ηᵢˡ, ηᵢ₊₁ˡ = ηᵢˡ ⊘ ηᵢᵘ`
converges to `(ηᵘ, ηˡ)` from index `1`. The book's `ηᵘ ≥ ηˡ` hypothesis is
derived (`etaMin_le_etaMax`), not assumed. -/

namespace DeepWiki

open scoped Classical NNReal

/-! The refined maximal arrival curve is `ηᵘ = αᵘ ⊘̄ αˡ = maxDeconv αu αl` and the
refined minimal one is `ηˡ = αˡ ⊘ αᵘ = minDeconv αl αu`; these deconvolutions are
written inline throughout (note the argument swap in `ηˡ`). -/

/-- Cross subtraction bound on `ℝ≥0`: `a + b ≤ c + d` gives `a - c ≤ d - b`. -/
private theorem tsub_le_tsub_of_add_le {a b c d : ℝ≥0}
    (h : a + b ≤ c + d) : a - c ≤ d - b := by
  rcases le_total c a with hca | hca
  · rcases le_total b d with hbd | hbd
    · rw [← NNReal.coe_le_coe, NNReal.coe_sub hca, NNReal.coe_sub hbd]
      have h' : (a : ℝ) + b ≤ c + d := by exact_mod_cast h
      linarith
    · rw [tsub_eq_zero_of_le hbd]
      have hac : a + b ≤ c + b := le_trans h (by gcongr)
      rw [tsub_le_iff_right, zero_add]
      exact le_of_add_le_add_right hac
  · rw [tsub_eq_zero_of_le hca]; exact zero_le'

/-! ## The refined curves are arrival curves -/

/-- `ηᵘ = αᵘ ⊘̄ αˡ` is a maximal arrival curve for `A`: combining the maximal
bound `A (t+d+v) ≤ A t + αᵘ (d+v)` and the minimal bound
`A (t+d) + αˡ v ≤ A (t+d+v)` gives `A (t+d) - A t ≤ αᵘ (d+v) - αˡ v` for every
shift `v`, hence `A (t+d) ≤ A t + ηᵘ d`. -/
theorem isMaximalArrivalCurve_etaMax {A αu αl : ℝ≥0 → ℝ≥0}
    (hu : IsMaximalArrivalCurve A αu) (hl : IsMinimalArrivalCurve A αl)
    (hAmono : Monotone A) (hlmono : Monotone αl) :
    IsMaximalArrivalCurve A (maxDeconv αu αl) := by
  rw [isMaximalArrivalCurve_iff_increment] at hu
  rw [isMinimalArrivalCurve_iff_increment_of_monotone A αl hAmono hlmono] at hl
  rw [isMaximalArrivalCurve_iff_increment]
  intro t d
  -- `ηᵘ d = ⨅_v αᵘ (d+v) - αˡ v`; bound `A (t+d) - A t ≤ that ⨅`
  show A (t + d) ≤ A t + maxDeconv αu αl d
  rw [add_comm (A t), ← tsub_le_iff_right]
  refine le_ciInf (fun v => ?_)
  -- chain: `A (t+d) + αˡ v ≤ A (t+d+v) ≤ A t + αᵘ (d+v)`
  have hmin : A (t + d) + αl v ≤ A (t + d + v) := hl (t + d) v
  have hmax : A (t + d + v) ≤ A t + αu (d + v) := by
    have := hu t (d + v)
    rwa [← add_assoc] at this
  have hchain : A (t + d) + αl v ≤ A t + αu (d + v) := le_trans hmin hmax
  -- `A (t+d) - A t ≤ αᵘ (d+v) - αˡ v` from the chain `A (t+d) + αˡ v ≤ A t + αᵘ (d+v)`
  exact tsub_le_tsub_of_add_le hchain

/-- `ηˡ = αˡ ⊘ αᵘ` is a minimal arrival curve for `A`: combining the minimal
bound `A t + αˡ (d+v) ≤ A (t+d+v)` and the maximal bound
`A (t+d+v) ≤ A (t+d) + αᵘ v` gives `αˡ (d+v) - αᵘ v ≤ A (t+d) - A t` for every
shift `v`, hence `A t + ηˡ d ≤ A (t+d)`. -/
theorem isMinimalArrivalCurve_etaMin {A αu αl : ℝ≥0 → ℝ≥0}
    (hu : IsMaximalArrivalCurve A αu) (hl : IsMinimalArrivalCurve A αl)
    (hAmono : Monotone A) (hlmono : Monotone αl) :
    IsMinimalArrivalCurve A (minDeconv αl αu) := by
  rw [isMaximalArrivalCurve_iff_increment] at hu
  rw [isMinimalArrivalCurve_iff_increment_of_monotone A αl hAmono hlmono] at hl
  refine isMinimalArrivalCurve_of_increment A (minDeconv αl αu) (fun t d => ?_)
  -- `ηˡ d = ⨆_v αˡ (d+v) - αᵘ v`; bound `A t + that ⨆ ≤ A (t+d)`
  show A t + minDeconv αl αu d ≤ A (t + d)
  -- the supremum is `≤ A (t+d) - A t`, each term via the chain
  have hsup : minDeconv αl αu d ≤ A (t + d) - A t := by
    refine ciSup_le (fun v => ?_)
    -- chain: `A t + αˡ (d+v) ≤ A (t+d+v) ≤ A (t+d) + αᵘ v`
    have hmin : A t + αl (d + v) ≤ A (t + d + v) := by
      have := hl t (d + v)
      rwa [← add_assoc] at this
    have hmax : A (t + d + v) ≤ A (t + d) + αu v := hu (t + d) v
    have hchain : A t + αl (d + v) ≤ A (t + d) + αu v := le_trans hmin hmax
    -- `αˡ (d+v) - αᵘ v ≤ A (t+d) - A t` from the chain
    rw [add_comm (A t) (αl (d + v)), add_comm (A (t + d)) (αu v)] at hchain
    exact tsub_le_tsub_of_add_le hchain
  -- `A t + (A (t+d) - A t) = A (t+d)` since `A t ≤ A (t+d)`
  calc A t + minDeconv αl αu d ≤ A t + (A (t + d) - A t) := by gcongr
    _ = A (t + d) := add_tsub_cancel_of_le (hAmono le_self_add)

/-! ## One-step fixpoint -/

/-- A minimal arrival curve is pointwise below a maximal one for the same `A`:
`A t + αˡ d ≤ A (t+d) ≤ A t + αᵘ d` cancels to `αˡ d ≤ αᵘ d`. -/
theorem isMinimalArrivalCurve_le_isMaximalArrivalCurve {A αu αl : ℝ≥0 → ℝ≥0}
    (hu : IsMaximalArrivalCurve A αu) (hl : IsMinimalArrivalCurve A αl)
    (hAmono : Monotone A) (hlmono : Monotone αl) :
    αl ≤ αu := by
  rw [isMaximalArrivalCurve_iff_increment] at hu
  rw [isMinimalArrivalCurve_iff_increment_of_monotone A αl hAmono hlmono] at hl
  intro d
  have h1 : A 0 + αl d ≤ A (0 + d) := hl 0 d
  have h2 : A (0 + d) ≤ A 0 + αu d := hu 0 d
  exact le_of_add_le_add_left (le_trans h1 h2)

/-- `ηˡ 0 = 0`: each shift term `αˡ v - αᵘ v` vanishes (`αˡ ≤ αᵘ`), so the
supremum defining `ηˡ 0` is `0`. -/
theorem etaMin_zero {A αu αl : ℝ≥0 → ℝ≥0}
    (hu : IsMaximalArrivalCurve A αu) (hl : IsMinimalArrivalCurve A αl)
    (hAmono : Monotone A) (hlmono : Monotone αl) :
    minDeconv αl αu 0 = 0 := by
  have hle := isMinimalArrivalCurve_le_isMaximalArrivalCurve hu hl hAmono hlmono
  show minDeconv αl αu 0 = 0
  unfold minDeconv
  have hz : (fun s : ℝ≥0 => αl (0 + s) - αu s) = fun _ => 0 := by
    funext s; rw [zero_add, tsub_eq_zero_of_le (hle s)]
  rw [hz]; exact ciSup_const

/-- `ηᵘ 0 = 0`: with `αᵘ 0 = αˡ 0 = 0` the `v = 0` term of `ηᵘ 0 = ⨅_v αᵘ v - αˡ v`
is `0`, and every term is `≥ 0` (`αˡ ≤ αᵘ`), so the infimum is `0`. -/
theorem etaMax_zero {A αu αl : ℝ≥0 → ℝ≥0}
    (hu : IsMaximalArrivalCurve A αu) (hl : IsMinimalArrivalCurve A αl)
    (hAmono : Monotone A) (hlmono : Monotone αl)
    (hu0 : αu 0 = 0) (hl0 : αl 0 = 0) :
    maxDeconv αu αl 0 = 0 := by
  have hle := isMinimalArrivalCurve_le_isMaximalArrivalCurve hu hl hAmono hlmono
  show maxDeconv αu αl 0 = 0
  unfold maxDeconv
  apply le_antisymm
  · -- the `v = 0` term is `αᵘ 0 - αˡ 0 = 0`
    refine ciInf_le_of_le (OrderBot.bddBelow _) 0 ?_
    rw [zero_add, hu0, hl0, tsub_zero]
  · -- every term `αᵘ (0+v) - αˡ v ≥ 0`
    exact le_ciInf (fun _ => zero_le')

/-- The easy fixpoint inequality `ηᵘ ⊘̄ ηˡ ≤ ηᵘ`: the `u = 0` term of the
defining infimum is `ηᵘ t - ηˡ 0 = ηᵘ t`. -/
theorem maxDeconv_etaMax_etaMin_le {A αu αl : ℝ≥0 → ℝ≥0}
    (hu : IsMaximalArrivalCurve A αu) (hl : IsMinimalArrivalCurve A αl)
    (hAmono : Monotone A) (hlmono : Monotone αl) :
    maxDeconv (maxDeconv αu αl) (minDeconv αl αu) ≤ maxDeconv αu αl := by
  intro t
  have h0 : minDeconv αl αu 0 = 0 := etaMin_zero hu hl hAmono hlmono
  show maxDeconv (maxDeconv αu αl) (minDeconv αl αu) t ≤ maxDeconv αu αl t
  unfold maxDeconv
  refine ciInf_le_of_le (OrderBot.bddBelow _) 0 ?_
  rw [h0, tsub_zero, add_zero]

/-- Core per-shift bound for the fixpoint: with `αᵘ` sub-additive, `αˡ`
super-additive, `αˡ ≤ αᵘ`, and `αᵘ` monotone, every `ηᵘ`-witness `z`-bound at
`z = u+v+w` (resp. `z = v`) combines with the sub- and super-additivity to
give `ηt + (αˡ (u+w) - αᵘ w) ≤ αᵘ (t+u+v) - αˡ v`. -/
private theorem etaMax_fixpoint_term {au al : ℝ≥0 → ℝ≥0}
    (hsub : IsSubadditive au) (hsup : IsSuperadditive al) (hle : al ≤ au)
    (humono : Monotone au) {ht : ℝ≥0} {t u v w : ℝ≥0}
    (hηt : ∀ z : ℝ≥0, ht ≤ au (t + z) - al z) :
    ht + (al (u + w) - au w) ≤ au (t + u + v) - al v := by
  have ev : al v ≤ au (t + u + v) :=
    le_trans (hle v) (humono (by rw [show t+u+v = v+(t+u) by ring]; exact le_self_add))
  rw [← NNReal.coe_le_coe]; push_cast [NNReal.coe_sub ev]
  rcases le_total (au w) (al (u + w)) with hw | hw
  · have e1 : al (u + v + w) ≤ au (t + (u + v + w)) :=
      le_trans (hle _) (humono le_add_self)
    have hz : (ht : ℝ) ≤ au (t + (u + v + w)) - al (u + v + w) := by
      have := hηt (u + v + w); rw [← NNReal.coe_le_coe] at this
      rwa [NNReal.coe_sub e1] at this
    have htuvw : (au (t + (u + v + w)) : ℝ) = au (t + u + v + w) := by
      norm_num [add_assoc]
    rw [htuvw] at hz
    have hsa : (au (t + u + v + w) : ℝ) ≤ au (t + u + v) + au w := by
      have := hsub (t + u + v) w; rw [← NNReal.coe_le_coe] at this
      push_cast at this; linarith
    have hsp : (al v : ℝ) + al (u + w) ≤ al (u + v + w) := by
      have := hsup v (u + w)
      rw [show v + (u + w) = u + v + w by ring, ← NNReal.coe_le_coe] at this
      push_cast at this; linarith
    rw [NNReal.coe_sub hw]; linarith
  · rw [tsub_eq_zero_of_le hw]; push_cast
    have evt : al v ≤ au (t + v) := le_trans (hle v) (humono le_add_self)
    have hz : (ht : ℝ) ≤ au (t + v) - al v := by
      have := hηt v; rw [← NNReal.coe_le_coe] at this
      rwa [NNReal.coe_sub evt] at this
    have hmono : (au (t + v) : ℝ) ≤ au (t + u + v) := by
      have := humono (show t + v ≤ t + u + v by
        rw [show t + u + v = t + v + u by ring]; exact le_self_add)
      exact_mod_cast this
    linarith

/-- The hard fixpoint inequality `ηᵘ ≤ ηᵘ ⊘̄ ηˡ`: for each outer shift `u`,
`ηᵘ t + ηˡ u ≤ ηᵘ (t+u)`, obtained by pushing `ηˡ u = ⨆_w ⋯` and
`ηᵘ (t+u) = ⨅_v ⋯` into the per-shift bound `etaMax_fixpoint_term`. -/
theorem le_maxDeconv_etaMax_etaMin {A αu αl : ℝ≥0 → ℝ≥0}
    (hu : IsMaximalArrivalCurve A αu) (hl : IsMinimalArrivalCurve A αl)
    (hAmono : Monotone A) (hlmono : Monotone αl) (humono : Monotone αu)
    (hsub : IsSubadditive αu) (hsup : IsSuperadditive αl) :
    maxDeconv αu αl ≤ maxDeconv (maxDeconv αu αl) (minDeconv αl αu) := by
  have hle := isMinimalArrivalCurve_le_isMaximalArrivalCurve hu hl hAmono hlmono
  intro t
  show maxDeconv αu αl t ≤ ⨅ u : ℝ≥0, maxDeconv αu αl (t + u) - minDeconv αl αu u
  refine le_ciInf (fun u => ?_)
  -- `ηᵘ t`-bound at every witness `z`
  have hηt : ∀ z : ℝ≥0, maxDeconv αu αl t ≤ αu (t + z) - αl z := fun z =>
    maxDeconv_le_sub αu αl t z
  -- per-`(v, w)` core bound
  have hterm : ∀ v w : ℝ≥0,
      maxDeconv αu αl t + (αl (u + w) - αu w) ≤ αu (t + u + v) - αl v := fun v w =>
    etaMax_fixpoint_term hsub hsup hle humono hηt
  -- `ηᵘ t + ηˡ u ≤ ηᵘ (t+u)`, hence `ηᵘ t ≤ ηᵘ (t+u) - ηˡ u`
  have hmain : maxDeconv αu αl t + minDeconv αl αu u ≤ maxDeconv αu αl (t + u) := by
    -- push the `⨆` of `ηˡ u` over the `+`, bound each term by the `⨅` of `ηᵘ (t+u)`
    show maxDeconv αu αl t + (⨆ w : ℝ≥0, αl (u + w) - αu w) ≤ maxDeconv αu αl (t + u)
    refine add_ciSup_le _ _ _ (fun w => ?_)
    show maxDeconv αu αl t + (αl (u + w) - αu w) ≤ ⨅ v : ℝ≥0, αu (t + u + v) - αl v
    exact le_ciInf (fun v => hterm v w)
  -- conclude `ηᵘ t ≤ ηᵘ (t+u) - ηˡ u`
  exact le_tsub_of_add_le_right hmain

/-- One-step fixpoint of the maximal refinement: under `αᵘ` sub-additive, `αˡ`
super-additive, `αˡ ≤ αᵘ` (from both being arrival curves) and `αᵘ` monotone,
`ηᵘ = ηᵘ ⊘̄ ηˡ`. Combining the two inequalities, the refinement of the refined
pair returns `ηᵘ` unchanged. -/
theorem etaMax_fixpoint {A αu αl : ℝ≥0 → ℝ≥0}
    (hu : IsMaximalArrivalCurve A αu) (hl : IsMinimalArrivalCurve A αl)
    (hAmono : Monotone A) (hlmono : Monotone αl) (humono : Monotone αu)
    (hsub : IsSubadditive αu) (hsup : IsSuperadditive αl) :
    maxDeconv αu αl = maxDeconv (maxDeconv αu αl) (minDeconv αl αu) :=
  le_antisymm
    (le_maxDeconv_etaMax_etaMin hu hl hAmono hlmono humono hsub hsup)
    (maxDeconv_etaMax_etaMin_le hu hl hAmono hlmono)

/-- Dual core per-shift bound for the minimal fixpoint: with `αᵘ` sub-additive,
`αˡ` super-additive, `αˡ ≤ αᵘ`, `αᵘ` monotone, the `ηˡ`-witness term at
`z = u+v+w` combines with sub- and super-additivity to give
`αˡ (t+u+v) - αᵘ v ≤ ηt + (αᵘ (u+w) - αˡ w)`. -/
private theorem etaMin_fixpoint_term {au al : ℝ≥0 → ℝ≥0}
    (hsub : IsSubadditive au) (hsup : IsSuperadditive al) (hle : al ≤ au)
    (humono : Monotone au) {ht : ℝ≥0} {t u v w : ℝ≥0}
    (hηt : al (t + (u + v + w)) - au (u + v + w) ≤ ht) :
    al (t + u + v) - au v ≤ ht + (au (u + w) - al w) := by
  have hsa : (au (u + v + w) : ℝ) ≤ au v + au (u + w) := by
    have := hsub v (u + w)
    rw [show v + (u + w) = u + v + w by ring, ← NNReal.coe_le_coe] at this
    push_cast at this; linarith
  have hsp : (al (t + u + v) : ℝ) + al w ≤ al (t + (u + v + w)) := by
    have := hsup (t + u + v) w
    rw [show (t + u + v) + w = t + (u + v + w) by ring, ← NNReal.coe_le_coe] at this
    push_cast at this; linarith
  have hzr : (al (t + (u + v + w)) : ℝ) - au (u + v + w) ≤ ht := by
    rcases le_total (au (u + v + w)) (al (t + (u + v + w))) with hz | hz
    · rw [← NNReal.coe_le_coe, NNReal.coe_sub hz] at hηt; exact hηt
    · have : (al (t + (u + v + w)) : ℝ) ≤ au (u + v + w) := by exact_mod_cast hz
      nlinarith [ht.coe_nonneg]
  have hwle : al w ≤ au (u + w) := le_trans (hle w) (humono le_add_self)
  rcases le_total (au v) (al (t + u + v)) with hv | hv
  · rw [← NNReal.coe_le_coe, NNReal.coe_sub hv]
    push_cast [NNReal.coe_sub hwle]; linarith
  · rw [tsub_eq_zero_of_le hv]; exact zero_le'

/-- The supremum defining `ηˡ s = ⨆_z αˡ (s+z) - αᵘ z` is bounded above by
`αᵘ s`: `αˡ (s+z) ≤ αᵘ (s+z) ≤ αᵘ s + αᵘ z` (sub-additivity), so each term is
`≤ αᵘ s`. Hence `ηˡ` is well-defined on `ℝ≥0` with no extra hypothesis. -/
theorem bddAbove_etaMin_sup {αu αl : ℝ≥0 → ℝ≥0}
    (hsub : IsSubadditive αu) (hle : αl ≤ αu) (s : ℝ≥0) :
    BddAbove (Set.range (fun z : ℝ≥0 => αl (s + z) - αu z)) := by
  refine ⟨αu s, ?_⟩
  rintro x ⟨z, rfl⟩
  calc αl (s + z) - αu z ≤ αu (s + z) - αu z := by gcongr; exact hle _
    _ ≤ αu s := tsub_le_iff_right.mpr (hsub s z)

/-- The hard minimal fixpoint inequality `ηˡ ⊘ ηᵘ ≤ ηˡ`: for each outer shift
`u`, `ηˡ (t+u) ≤ ηˡ t + ηᵘ u`, obtained by pushing `ηˡ (t+u) = ⨆_v ⋯` and
`ηᵘ u = ⨅_w ⋯` into the per-shift bound `etaMin_fixpoint_term`. -/
theorem minDeconv_etaMin_etaMax_le {A αu αl : ℝ≥0 → ℝ≥0}
    (hu : IsMaximalArrivalCurve A αu) (hl : IsMinimalArrivalCurve A αl)
    (hAmono : Monotone A) (hlmono : Monotone αl) (humono : Monotone αu)
    (hsub : IsSubadditive αu) (hsup : IsSuperadditive αl) :
    minDeconv (minDeconv αl αu) (maxDeconv αu αl) ≤ minDeconv αl αu := by
  have hle := isMinimalArrivalCurve_le_isMaximalArrivalCurve hu hl hAmono hlmono
  intro t
  show (⨆ u : ℝ≥0, minDeconv αl αu (t + u) - maxDeconv αu αl u) ≤ minDeconv αl αu t
  refine ciSup_le (fun u => ?_)
  -- `ηˡ (t+u) - ηᵘ u ≤ ηˡ t` ⟸ `ηˡ (t+u) ≤ ηˡ t + ηᵘ u`
  refine tsub_le_iff_right.mpr ?_
  -- `ηˡ (t+u) = ⨆_v αˡ (t+u+v) - αᵘ v`; bound each `v`-term
  show (⨆ v : ℝ≥0, αl (t + u + v) - αu v) ≤ minDeconv αl αu t + maxDeconv αu αl u
  refine ciSup_le (fun v => ?_)
  -- `αˡ`-witness term lower-bounds `ηˡ t = ⨆_z αˡ (t+z) - αᵘ z`
  have hηt : ∀ z : ℝ≥0, αl (t + z) - αu z ≤ minDeconv αl αu t := fun z =>
    le_ciSup_of_le (bddAbove_etaMin_sup hsub hle t) z le_rfl
  -- per-`w` core bound, with `ηᵘ u = ⨅_w αᵘ (u+w) - αˡ w` still to push out
  have key : ∀ w : ℝ≥0,
      αl (t + u + v) - αu v ≤ minDeconv αl αu t + (αu (u + w) - αl w) := fun w =>
    etaMin_fixpoint_term hsub hsup hle humono (hηt (u + v + w))
  -- `X ≤ ηˡ t + ⨅_w f w`: shift `ηˡ t` across and use `le_ciInf`
  show αl (t + u + v) - αu v ≤ minDeconv αl αu t + ⨅ w : ℝ≥0, αu (u + w) - αl w
  -- `X ≤ ηˡ t + ⨅_w f w` ⟸ `X - ηˡ t ≤ ⨅_w f w` ⟸ `∀ w, X - ηˡ t ≤ f w`
  refine tsub_le_iff_left.mp (le_ciInf (fun w => ?_))
  exact tsub_le_iff_left.mpr (key w)

/-- The refined minimal curve is below the refined maximal one, `ηˡ ≤ ηᵘ`: for
each `t, z, w`, `αˡ (t+z) - αᵘ z ≤ αᵘ (t+w) - αˡ w` via the chain `αˡ (t+z) + αˡ w
≤ αˡ (t+w+z) ≤ αᵘ (t+w+z) ≤ αᵘ (t+w) + αᵘ z`, so `⨆_z ⋯ ≤ ⨅_w ⋯`. This is the
book's `ηᵘ ≥ ηˡ` hypothesis — automatic once `αᵘ` is sub-additive and `αˡ` is
super-additive with `αˡ ≤ αᵘ`, so it need not be assumed for the fixpoint. -/
theorem etaMin_le_etaMax {A αu αl : ℝ≥0 → ℝ≥0}
    (hu : IsMaximalArrivalCurve A αu) (hl : IsMinimalArrivalCurve A αl)
    (hAmono : Monotone A) (hlmono : Monotone αl) (humono : Monotone αu)
    (hsub : IsSubadditive αu) (hsup : IsSuperadditive αl) :
    minDeconv αl αu ≤ maxDeconv αu αl := by
  have hle := isMinimalArrivalCurve_le_isMaximalArrivalCurve hu hl hAmono hlmono
  intro t
  show (⨆ z : ℝ≥0, αl (t + z) - αu z) ≤ ⨅ w : ℝ≥0, αu (t + w) - αl w
  refine ciSup_le (fun z => ?_)
  refine le_ciInf (fun w => ?_)
  rcases le_total (αu z) (αl (t + z)) with hz | hz
  · rw [← NNReal.coe_le_coe, NNReal.coe_sub hz]
    have hlw : αl w ≤ αu (t + w) := le_trans (hle w) (humono le_add_self)
    push_cast [NNReal.coe_sub hlw]
    have h1 : (αl (t + z) : ℝ) + αl w ≤ αl (t + w + z) := by
      have := hsup (t + z) w
      rw [show (t + z) + w = t + w + z by ring, ← NNReal.coe_le_coe] at this
      push_cast at this; linarith
    have h2 : (αu (t + w + z) : ℝ) ≤ αu (t + w) + αu z := by
      have := hsub (t + w) z; rw [← NNReal.coe_le_coe] at this
      push_cast at this; linarith
    have h3 : (αl (t + w + z) : ℝ) ≤ αu (t + w + z) := by exact_mod_cast hle _
    linarith
  · rw [tsub_eq_zero_of_le hz]; exact zero_le'

/-- `c ≤ ⨅ a, G a + ⨅ b, H b` from a per-pair bound `c ≤ G a + H b`, on `ℝ≥0`
(where `le_ciInf_add_ciInf` does not apply — `ℝ≥0` is not an `AddGroup`). -/
theorem le_ciInf_add_ciInf {c : ℝ≥0} {G H : ℝ≥0 → ℝ≥0}
    (h : ∀ a b, c ≤ G a + H b) : c ≤ (⨅ a, G a) + ⨅ b, H b := by
  have hb : ∀ a : ℝ≥0, c ≤ G a + ⨅ b, H b := fun a =>
    tsub_le_iff_left.mp (le_ciInf (fun b => tsub_le_iff_left.mpr (h a b)))
  have ha : c - (⨅ b, H b) ≤ ⨅ a, G a :=
    le_ciInf (fun a =>
      tsub_le_iff_left.mpr ((hb a).trans_eq (add_comm (G a) (⨅ b, H b))))
  rw [add_comm]; exact tsub_le_iff_left.mp ha

/-- `ηᵘ = αᵘ ⊘̄ αˡ` is sub-additive when `αᵘ` is sub-additive, `αˡ` super-additive,
`αˡ ≤ αᵘ` and `αᵘ` monotone: at the `z = a+b` witness, `αᵘ (u+s+a+b) ≤ αᵘ (u+a)
+ αᵘ (s+b)` and `αˡ a + αˡ b ≤ αˡ (a+b)` combine the two infimum terms. -/
theorem isSubadditive_etaMax {αu αl : ℝ≥0 → ℝ≥0}
    (hsub : IsSubadditive αu) (hsup : IsSuperadditive αl)
    (hle : αl ≤ αu) (humono : Monotone αu) :
    IsSubadditive (maxDeconv αu αl) := by
  intro u s
  show (⨅ z : ℝ≥0, αu (u + s + z) - αl z)
      ≤ (⨅ a : ℝ≥0, αu (u + a) - αl a) + ⨅ b : ℝ≥0, αu (s + b) - αl b
  refine le_ciInf_add_ciInf (fun a b => ?_)
  refine ciInf_le_of_le (OrderBot.bddBelow _) (a + b) ?_
  rw [← NNReal.coe_le_coe]
  have ha' : αl a ≤ αu (u + a) := le_trans (hle a) (humono le_add_self)
  have hb' : αl b ≤ αu (s + b) := le_trans (hle b) (humono le_add_self)
  have hsa : (αu (u + s + (a + b)) : ℝ) ≤ αu (u + a) + αu (s + b) := by
    have := hsub (u + a) (s + b)
    rw [show (u + a) + (s + b) = u + s + (a + b) by ring,
      ← NNReal.coe_le_coe] at this
    push_cast at this; linarith
  have hsp : (αl a : ℝ) + αl b ≤ αl (a + b) := by
    have := hsup a b; rw [← NNReal.coe_le_coe] at this; push_cast at this; linarith
  rcases le_total (αl (a + b)) (αu (u + s + (a + b))) with hz | hz
  · rw [NNReal.coe_sub hz]
    push_cast [NNReal.coe_sub ha', NNReal.coe_sub hb']; linarith
  · rw [tsub_eq_zero_of_le hz]
    push_cast [NNReal.coe_sub ha', NNReal.coe_sub hb']
    nlinarith [NNReal.coe_le_coe.mpr ha', NNReal.coe_le_coe.mpr hb']

/-- The supremum defining `ηˡ ⊘ ηᵘ` at `s` is bounded above by `ηᵘ s` when `ηᵘ`
is sub-additive and `ηˡ ≤ ηᵘ`: `ηˡ (s+u) - ηᵘ u ≤ ηᵘ (s+u) - ηᵘ u ≤ ηᵘ s`. Both
conditions are derivable (`isSubadditive_etaMax`, `etaMin_le_etaMax`), so this
needs no sub-additivity assumption on `ηˡ`. -/
theorem bddAbove_minDeconv_etaMin_etaMax {αu αl : ℝ≥0 → ℝ≥0}
    (hsubU : IsSubadditive (maxDeconv αu αl)) (hETle : minDeconv αl αu ≤ maxDeconv αu αl)
    (s : ℝ≥0) :
    BddAbove (Set.range (fun u : ℝ≥0 =>
      minDeconv αl αu (s + u) - maxDeconv αu αl u)) := by
  refine ⟨maxDeconv αu αl s, ?_⟩
  rintro x ⟨u, rfl⟩
  calc minDeconv αl αu (s + u) - maxDeconv αu αl u
      ≤ maxDeconv αu αl (s + u) - maxDeconv αu αl u := by gcongr; exact hETle _
    _ ≤ maxDeconv αu αl s := tsub_le_iff_right.mpr (hsubU s u)

/-- The easy minimal fixpoint inequality `ηˡ ≤ ηˡ ⊘ ηᵘ`: the `u = 0` term of the
defining supremum is `ηˡ t - ηᵘ 0 = ηˡ t` (using `ηᵘ 0 = 0`). The supremum is
well-defined by `ηᵘ` sub-additive and `ηˡ ≤ ηᵘ`. -/
theorem le_minDeconv_etaMin_etaMax {A αu αl : ℝ≥0 → ℝ≥0}
    (hu : IsMaximalArrivalCurve A αu) (hl : IsMinimalArrivalCurve A αl)
    (hAmono : Monotone A) (hlmono : Monotone αl) (humono : Monotone αu)
    (hsub : IsSubadditive αu) (hsup : IsSuperadditive αl)
    (hu0 : αu 0 = 0) (hl0 : αl 0 = 0)
    (hETle : minDeconv αl αu ≤ maxDeconv αu αl) :
    minDeconv αl αu ≤ minDeconv (minDeconv αl αu) (maxDeconv αu αl) := by
  intro t
  have hle := isMinimalArrivalCurve_le_isMaximalArrivalCurve hu hl hAmono hlmono
  have hsubU : IsSubadditive (maxDeconv αu αl) := isSubadditive_etaMax hsub hsup hle humono
  have h0 : maxDeconv αu αl 0 = 0 := etaMax_zero hu hl hAmono hlmono hu0 hl0
  show minDeconv αl αu t ≤ ⨆ u : ℝ≥0, minDeconv αl αu (t + u) - maxDeconv αu αl u
  refine le_ciSup_of_le (bddAbove_minDeconv_etaMin_etaMax hsubU hETle t) 0 ?_
  rw [h0, tsub_zero, add_zero]

/-- One-step fixpoint of the minimal refinement: under `αᵘ` sub-additive, `αˡ`
super-additive, `αᵘ` monotone and `αᵘ 0 = αˡ 0 = 0`, `ηˡ = ηˡ ⊘ ηᵘ`. The book's
`ηˡ ≤ ηᵘ` condition is derived here (`etaMin_le_etaMax`) and the well-definedness
of the supremum follows from `ηᵘ` being sub-additive (`isSubadditive_etaMax`), so
no condition on `ηˡ` itself need be assumed. -/
theorem etaMin_fixpoint {A αu αl : ℝ≥0 → ℝ≥0}
    (hu : IsMaximalArrivalCurve A αu) (hl : IsMinimalArrivalCurve A αl)
    (hAmono : Monotone A) (hlmono : Monotone αl) (humono : Monotone αu)
    (hsub : IsSubadditive αu) (hsup : IsSuperadditive αl)
    (hu0 : αu 0 = 0) (hl0 : αl 0 = 0) :
    minDeconv αl αu = minDeconv (minDeconv αl αu) (maxDeconv αu αl) :=
  have hETle := etaMin_le_etaMax hu hl hAmono hlmono humono hsub hsup
  le_antisymm
    (le_minDeconv_etaMin_etaMax hu hl hAmono hlmono humono hsub hsup hu0 hl0 hETle)
    (minDeconv_etaMin_etaMax_le hu hl hAmono hlmono humono hsub hsup)

/-! ## The fixpoint is reached by iteration -/

/-- One refinement step on a pair `(ηᵘ, ηˡ)`: the new maximal curve is the
max-plus deconvolution `ηᵘ ⊘̄ ηˡ` and the new minimal curve is the min-plus
deconvolution `ηˡ ⊘ ηᵘ`. -/
noncomputable def refineStep
    (p : (ℝ≥0 → ℝ≥0) × (ℝ≥0 → ℝ≥0)) : (ℝ≥0 → ℝ≥0) × (ℝ≥0 → ℝ≥0) :=
  (maxDeconv p.1 p.2, minDeconv p.2 p.1)

/-- The refinement sequence `(ηᵢᵘ, ηᵢˡ)` from a starting pair `αᵘ, αˡ`:
`(η₀ᵘ, η₀ˡ) = (αᵘ, αˡ)` and `(ηᵢ₊₁ᵘ, ηᵢ₊₁ˡ) = (ηᵢᵘ ⊘̄ ηᵢˡ, ηᵢˡ ⊘ ηᵢᵘ)`. -/
noncomputable def etaSeq (αu αl : ℝ≥0 → ℝ≥0) :
    ℕ → (ℝ≥0 → ℝ≥0) × (ℝ≥0 → ℝ≥0)
  | 0 => (αu, αl)
  | n + 1 => refineStep (etaSeq αu αl n)

/-- The maximal curve of the refinement sequence, `ηᵢᵘ`. -/
noncomputable def etaSeqMax (αu αl : ℝ≥0 → ℝ≥0) (n : ℕ) : ℝ≥0 → ℝ≥0 :=
  (etaSeq αu αl n).1

/-- The minimal curve of the refinement sequence, `ηᵢˡ`. -/
noncomputable def etaSeqMin (αu αl : ℝ≥0 → ℝ≥0) (n : ℕ) : ℝ≥0 → ℝ≥0 :=
  (etaSeq αu αl n).2

/-- The first iterate is the one-step refinement `(ηᵘ, ηˡ)`:
`η₁ᵘ = αᵘ ⊘̄ αˡ` and `η₁ˡ = αˡ ⊘ αᵘ`. -/
theorem etaSeq_one (αu αl : ℝ≥0 → ℝ≥0) :
    etaSeq αu αl 1 = (maxDeconv αu αl, minDeconv αl αu) := rfl

/-- The refined pair `(ηᵘ, ηˡ)` is a fixed point of `refineStep`: combining
the maximal and minimal one-step fixpoints `ηᵘ = ηᵘ ⊘̄ ηˡ` and `ηˡ = ηˡ ⊘ ηᵘ`. -/
theorem refineStep_eta_fixpoint {A αu αl : ℝ≥0 → ℝ≥0}
    (hu : IsMaximalArrivalCurve A αu) (hl : IsMinimalArrivalCurve A αl)
    (hAmono : Monotone A) (hlmono : Monotone αl) (humono : Monotone αu)
    (hsub : IsSubadditive αu) (hsup : IsSuperadditive αl)
    (hu0 : αu 0 = 0) (hl0 : αl 0 = 0) :
    refineStep (maxDeconv αu αl, minDeconv αl αu) = (maxDeconv αu αl, minDeconv αl αu) := by
  unfold refineStep
  refine Prod.ext ?_ ?_
  · exact (etaMax_fixpoint hu hl hAmono hlmono humono hsub hsup).symm
  · exact (etaMin_fixpoint hu hl hAmono hlmono humono hsub hsup hu0 hl0).symm

/-- The refinement sequence stabilizes after one step: for every `i ≥ 1`,
`(ηᵢᵘ, ηᵢˡ) = (maxDeconv αu αl, minDeconv αl αu)`. The first step reaches the refined
pair, which `refineStep_eta_fixpoint` shows is fixed, so the iteration converges
to the fixpoint immediately and stays there. -/
theorem etaSeq_eq_eta_of_one_le {A αu αl : ℝ≥0 → ℝ≥0}
    (hu : IsMaximalArrivalCurve A αu) (hl : IsMinimalArrivalCurve A αl)
    (hAmono : Monotone A) (hlmono : Monotone αl) (humono : Monotone αu)
    (hsub : IsSubadditive αu) (hsup : IsSuperadditive αl)
    (hu0 : αu 0 = 0) (hl0 : αl 0 = 0) :
    ∀ n, 1 ≤ n → etaSeq αu αl n = (maxDeconv αu αl, minDeconv αl αu) := by
  intro n hn
  induction n with
  | zero => exact absurd hn (by norm_num)
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; exact etaSeq_one αu αl
    · show refineStep (etaSeq αu αl k) = _
      rw [ih hk]
      exact refineStep_eta_fixpoint hu hl hAmono hlmono humono hsub hsup hu0 hl0

/-- The maximal iterate converges: `ηᵢᵘ = maxDeconv αu αl` for all `i ≥ 1`. -/
theorem etaSeqMax_eq_etaMax_of_one_le {A αu αl : ℝ≥0 → ℝ≥0}
    (hu : IsMaximalArrivalCurve A αu) (hl : IsMinimalArrivalCurve A αl)
    (hAmono : Monotone A) (hlmono : Monotone αl) (humono : Monotone αu)
    (hsub : IsSubadditive αu) (hsup : IsSuperadditive αl)
    (hu0 : αu 0 = 0) (hl0 : αl 0 = 0) (n : ℕ) (hn : 1 ≤ n) :
    etaSeqMax αu αl n = maxDeconv αu αl :=
  congrArg Prod.fst
    (etaSeq_eq_eta_of_one_le hu hl hAmono hlmono humono hsub hsup hu0 hl0 n hn)

/-- The minimal iterate converges: `ηᵢˡ = minDeconv αl αu` for all `i ≥ 1`. -/
theorem etaSeqMin_eq_etaMin_of_one_le {A αu αl : ℝ≥0 → ℝ≥0}
    (hu : IsMaximalArrivalCurve A αu) (hl : IsMinimalArrivalCurve A αl)
    (hAmono : Monotone A) (hlmono : Monotone αl) (humono : Monotone αu)
    (hsub : IsSubadditive αu) (hsup : IsSuperadditive αl)
    (hu0 : αu 0 = 0) (hl0 : αl 0 = 0) (n : ℕ) (hn : 1 ≤ n) :
    etaSeqMin αu αl n = minDeconv αl αu :=
  congrArg Prod.snd
    (etaSeq_eq_eta_of_one_le hu hl hAmono hlmono humono hsub hsup hu0 hl0 n hn)

/-- A sequence `s : ℕ → X` converges to `L` (in the discrete sense of being
eventually constant): there is an index `N` past which every term equals `L`. -/
def Converges {X : Type*} (s : ℕ → X) (L : X) : Prop :=
  ∃ N, ∀ n, N ≤ n → s n = L

/-- The refinement tuple sequence converges to `(ηᵘ, ηˡ) = (maxDeconv αu αl,
minDeconv αl αu)`: it is constant from index `1` on, so `(ηᵘ, ηˡ)` is its limit.
Both components converge simultaneously, packaged as one statement on the pair. -/
theorem converges_etaSeq {A αu αl : ℝ≥0 → ℝ≥0}
    (hu : IsMaximalArrivalCurve A αu) (hl : IsMinimalArrivalCurve A αl)
    (hAmono : Monotone A) (hlmono : Monotone αl) (humono : Monotone αu)
    (hsub : IsSubadditive αu) (hsup : IsSuperadditive αl)
    (hu0 : αu 0 = 0) (hl0 : αl 0 = 0) :
    Converges (etaSeq αu αl) (maxDeconv αu αl, minDeconv αl αu) :=
  ⟨1, etaSeq_eq_eta_of_one_le hu hl hAmono hlmono humono hsub hsup hu0 hl0⟩

end DeepWiki
