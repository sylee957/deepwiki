import Book.MaximalArrivalCurves
import Book.MinimalArrivalCurves

/-! # Combining minimal and maximal arrival curves
From a maximal arrival curve `αᵘ` and a minimal one `αˡ` for `A`, the
max-plus deconvolution `ηᵘ = αᵘ ⊘̄ αˡ` is a (refined) maximal arrival curve and
the min-plus deconvolution `ηˡ = αˡ ⊘ αᵘ` is a (refined) minimal one. Under
sub- and super-additivity with `αᵘ 0 = αˡ 0 = 0` and `ηᵘ ≥ ηˡ`, the refinement
reaches a fixpoint in one step. -/

namespace DeepWiki

open scoped Classical NNReal

/-- The refined maximal arrival curve `ηᵘ = αᵘ ⊘̄ αˡ` (max-plus deconvolution). -/
noncomputable def etaMax (αu αl : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  maxDeconv αu αl

/-- The refined minimal arrival curve `ηˡ = αˡ ⊘ αᵘ` (min-plus deconvolution). -/
noncomputable def etaMin (αu αl : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  minDeconv αl αu

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
    IsMaximalArrivalCurve A (etaMax αu αl) := by
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
    IsMinimalArrivalCurve A (etaMin αu αl) := by
  rw [isMaximalArrivalCurve_iff_increment] at hu
  rw [isMinimalArrivalCurve_iff_increment_of_monotone A αl hAmono hlmono] at hl
  refine isMinimalArrivalCurve_of_increment A (etaMin αu αl) (fun t d => ?_)
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
    etaMin αu αl 0 = 0 := by
  have hle := isMinimalArrivalCurve_le_isMaximalArrivalCurve hu hl hAmono hlmono
  show minDeconv αl αu 0 = 0
  unfold minDeconv
  have hz : (fun s : ℝ≥0 => αl (0 + s) - αu s) = fun _ => 0 := by
    funext s; rw [zero_add, tsub_eq_zero_of_le (hle s)]
  rw [hz]; exact ciSup_const

end DeepWiki
