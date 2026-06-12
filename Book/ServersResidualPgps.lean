import Book.ServersResidualGps
import Book.RealCurves

/-! # Packetized-GPS residual service
PGPS serves whole packets in the order their bits would complete under
a GPS reference with the same arrivals. The reference's per-packet
completion deadline — every bit cleared by the reference at `u` is
cleared by PGPS by `u + ℓᵘ/R` — is the *horizontal* tracking fact
(`IsPgpsTracking`); it yields the sharp delayed residual
`β(· − ℓᵘ/R)` (`pgpsResidualShifted`) by splitting at the *reference*
start of `t − ℓᵘ/R`, and the book's `[β − ℓᵘ]⁺` (`pgpsResidual`) when
`β` is `R`-Lipschitz. The weaker *vertical* closeness `D − D̂ ≤ ℓᵘ` is
provably insufficient — see the refutation ladder. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **PGPS tracking**: the PGPS departure `Dh` is causal and meets the
GPS reference departure `D`'s per-packet horizontal deadline in
cumulative form — every bit the reference clears at `u` is cleared by
PGPS by `u + ℓᵘ/R`. This is the packet-level deadline `tₖ ≤ uₖ + ℓᵘ/R`
of the book's work-conservation argument, lifted to cumulative
functions and taken as definitional. -/
def IsPgpsTracking (A D Dh : ℝ≥0 → ℝ≥0) (R lu : ℝ≥0) : Prop :=
  Dh ≤ A ∧ ∀ u, D u ≤ Dh (u + lu / R)

/-- The book's PGPS residual `[β − ℓᵘ]⁺`: the reference residual less
one maximal packet. -/
noncomputable def pgpsResidual (β : ℝ≥0 → ℝ≥0) (lu : ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun v => β v - lu

/-- `pgpsResidual β lu v` unfolds to its closed form. -/
@[simp] theorem pgpsResidual_apply (β : ℝ≥0 → ℝ≥0) (lu v : ℝ≥0) :
    pgpsResidual β lu v = β v - lu := rfl

/-- `pgpsResidual β lu 0 = 0` when `β 0 = 0`. -/
theorem pgpsResidual_zero_eq {β : ℝ≥0 → ℝ≥0} (lu : ℝ≥0)
    (hβ0 : β 0 = 0) : pgpsResidual β lu 0 = 0 := by
  rw [pgpsResidual_apply, hβ0, zero_tsub]

/-- The sharp PGPS residual: the reference residual delayed by the
packet horizon, `v ↦ β(v − ℓᵘ/R)`. -/
noncomputable def pgpsResidualShifted (β : ℝ≥0 → ℝ≥0) (R lu : ℝ≥0) :
    ℝ≥0 → ℝ≥0 :=
  fun v => β (v - lu / R)

/-- `pgpsResidualShifted β R lu v` unfolds to its closed form. -/
@[simp] theorem pgpsResidualShifted_apply (β : ℝ≥0 → ℝ≥0)
    (R lu v : ℝ≥0) :
    pgpsResidualShifted β R lu v = β (v - lu / R) := rfl

/-- `pgpsResidualShifted β R lu 0 = 0` when `β 0 = 0`. -/
theorem pgpsResidualShifted_zero_eq {β : ℝ≥0 → ℝ≥0} (R lu : ℝ≥0)
    (hβ0 : β 0 = 0) : pgpsResidualShifted β R lu 0 = 0 := by
  rw [pgpsResidualShifted_apply, zero_tsub, hβ0]

/-- **Sharp PGPS residual service** (latency form): a PGPS departure
tracking a GPS reference that offers the strict `β` satisfies the
min-plus inequality for the delayed residual `β(· − ℓᵘ/R)`. The split
is at the *reference* start of `t − ℓᵘ/R` — where `A = D` genuinely
holds — and the reference increment is carried to PGPS through the
horizontal deadline; the vertical closeness `D − D̂ ≤ ℓᵘ` is never
used. -/
theorem minConv_pgpsResidualShifted_le_of_isPgpsTracking
    {A D Dh : ℝ≥0 → ℝ≥0} {β : ℝ≥0 → ℝ≥0} {R lu : ℝ≥0}
    (hAlc : IsLeftContinuous A) (hDlc : IsLeftContinuous D)
    (h0 : A 0 = D 0) (hA0 : A 0 = 0) (hβ0 : β 0 = 0)
    (hcD : ∀ x, D x ≤ A x)
    (hstrict : ∀ s t, s ≤ t → IsBacklogged A D (Set.Ioc s t) →
      D s + β (t - s) ≤ D t)
    (hp : IsPgpsTracking A D Dh R lu) (t : ℝ≥0) :
    minConv A (pgpsResidualShifted β R lu) t ≤ Dh t := by
  obtain ⟨-, hshift⟩ := hp
  rcases le_total t (lu / R) with htc | hct
  · -- within one packet horizon: the split at the origin vanishes
    refine le_trans (minConv_le_add _ _ (zero_add t)) ?_
    rw [hA0, zero_add, pgpsResidualShifted_apply,
      tsub_eq_zero_of_le htc, hβ0]
    exact zero_le'
  · -- split at the reference start of `t − ℓᵘ/R`
    have hsσ : start A D (t - lu / R) ≤ t - lu / R :=
      start_le A D _
    have hσt : start A D (t - lu / R) ≤ t := hsσ.trans tsub_le_self
    refine le_trans (minConv_le_add _ _
      (add_tsub_cancel_of_le hσt)) ?_
    have heq : A (start A D (t - lu / R))
        = D (start A D (t - lu / R)) :=
      apply_start_eq hAlc hDlc h0 hcD (t - lu / R)
    have hstr := hstrict (start A D (t - lu / R)) (t - lu / R) hsσ
      (isBacklogged_Ioc_start hcD (t - lu / R))
    have hsh := hshift (t - lu / R)
    rw [tsub_add_cancel_of_le hct] at hsh
    rw [pgpsResidualShifted_apply, tsub_right_comm]
    calc A (start A D (t - lu / R))
          + β ((t - lu / R) - start A D (t - lu / R))
        = D (start A D (t - lu / R))
          + β ((t - lu / R) - start A D (t - lu / R)) := by rw [heq]
      _ ≤ D (t - lu / R) := hstr
      _ ≤ Dh t := hsh

/-- An `R`-Lipschitz reference residual turns the packet horizon into
one packet: `[β − ℓᵘ]⁺ ≤ β(· − ℓᵘ/R)` pointwise. -/
theorem pgpsResidual_le_pgpsResidualShifted {β : ℝ≥0 → ℝ≥0}
    {R lu : ℝ≥0}
    (hLip : ∀ v w, w ≤ v → β v ≤ β w + R * (v - w)) (v : ℝ≥0) :
    pgpsResidual β lu v ≤ pgpsResidualShifted β R lu v := by
  rw [pgpsResidual_apply, pgpsResidualShifted_apply]
  refine tsub_le_iff_right.mpr ?_
  refine le_trans (hLip v (v - lu / R) tsub_le_self) ?_
  refine add_le_add le_rfl ?_
  refine le_trans (mul_le_mul' le_rfl tsub_tsub_le) ?_
  rcases eq_zero_or_pos R with rfl | hR
  · rw [zero_mul]
    exact zero_le'
  · rw [mul_comm]
    exact (div_mul_cancel₀ lu hR.ne').le

/-- **PGPS residual service** (the book's curve): under `R`-Lipschitz
`β`, the tracking pair satisfies the min-plus inequality for
`[β − ℓᵘ]⁺`. The book's proof closes by applying the reference's
strict service on the *PGPS* backlogged window, which the vertical
closeness it carries cannot justify (the reference may have caught up
while PGPS still lags within one packet); the repair splits at the
*reference* start of `t − ℓᵘ/R` and routes through the horizontal
deadline. The Lipschitz hypothesis is automatic for the GPS share
`λ_g`, `g ≤ R` (`rate_lipschitz`), and a genuine extra hypothesis for
arbitrary strict `β` — without it only the sharp delayed form holds. -/
theorem minConv_pgpsResidual_le_of_isPgpsTracking
    {A D Dh : ℝ≥0 → ℝ≥0} {β : ℝ≥0 → ℝ≥0} {R lu : ℝ≥0}
    (hAlc : IsLeftContinuous A) (hDlc : IsLeftContinuous D)
    (h0 : A 0 = D 0) (hA0 : A 0 = 0) (hβ0 : β 0 = 0)
    (hcD : ∀ x, D x ≤ A x)
    (hstrict : ∀ s t, s ≤ t → IsBacklogged A D (Set.Ioc s t) →
      D s + β (t - s) ≤ D t)
    (hp : IsPgpsTracking A D Dh R lu)
    (hLip : ∀ v w, w ≤ v → β v ≤ β w + R * (v - w)) (t : ℝ≥0) :
    minConv A (pgpsResidual β lu) t ≤ Dh t := by
  refine le_trans (le_minConv fun u s hus => ?_)
    (minConv_pgpsResidualShifted_le_of_isPgpsTracking hAlc hDlc h0
      hA0 hβ0 hcD hstrict hp t)
  exact le_trans (minConv_le_add _ _ hus)
    (add_le_add le_rfl (pgpsResidual_le_pgpsResidualShifted hLip s))

/-- The rate curve `λ_g` is `R`-Lipschitz once `g ≤ R`. -/
theorem rate_lipschitz {g R : ℝ≥0} (hg : g ≤ R) :
    ∀ v w : ℝ≥0, w ≤ v → rate g v ≤ rate g w + R * (v - w) := by
  intro v w hwv
  have he : rate g v = rate g w + g * (v - w) := by
    rw [rate_apply, rate_apply, ← mul_add, add_tsub_cancel_of_le hwv]
  rw [he]
  exact add_le_add le_rfl (mul_le_mul' hg le_rfl)

/-- **PGPS over a GPS share** (rate form): when the reference offers
the strict rate `λ_g` with `g` at most the line rate `R`, the tracking
pair satisfies the min-plus inequality for `[λ_g − ℓᵘ]⁺` — the
Lipschitz hypothesis discharges automatically. -/
theorem minConv_pgpsResidual_rate_le_of_isPgpsTracking
    {A D Dh : ℝ≥0 → ℝ≥0} {g R lu : ℝ≥0}
    (hAlc : IsLeftContinuous A) (hDlc : IsLeftContinuous D)
    (h0 : A 0 = D 0) (hA0 : A 0 = 0)
    (hcD : ∀ x, D x ≤ A x)
    (hstrict : ∀ s t, s ≤ t → IsBacklogged A D (Set.Ioc s t) →
      D s + rate g (t - s) ≤ D t)
    (hp : IsPgpsTracking A D Dh R lu) (hg : g ≤ R) (t : ℝ≥0) :
    minConv A (pgpsResidual (rate g) lu) t ≤ Dh t :=
  minConv_pgpsResidual_le_of_isPgpsTracking hAlc hDlc h0 hA0
    (by rw [rate_apply, mul_zero]) hcD hstrict hp (rate_lipschitz hg) t

/-! ## Vertical closeness does not suffice -/

/-- The refutation flow: arrivals and reference departures both
`min(·, 1)` — never backlogged, so *any* null-at-origin curve is
vacuously strict for the reference pair. -/
noncomputable def pgpsWitnessFlow : ℝ≥0 → ℝ≥0 := fun x => min x 1

/-- The witness reference pair is strict for every null-at-origin
curve (its backlog is empty). -/
theorem pgpsWitnessFlow_strict {β : ℝ≥0 → ℝ≥0} (hβ0 : β 0 = 0) :
    ∀ s t, s ≤ t →
      IsBacklogged pgpsWitnessFlow pgpsWitnessFlow (Set.Ioc s t) →
      pgpsWitnessFlow s + β (t - s) ≤ pgpsWitnessFlow t := by
  intro s t hst hbl
  rcases eq_or_lt_of_le hst with rfl | hlt
  · rw [tsub_self, hβ0, add_zero]
  · exact absurd (hbl t ⟨hlt, le_rfl⟩) (lt_irrefl _)

/-- The witness convolution stays above `1/2` at `t = 2`: every split
pays either the arrival half or the residual half. -/
theorem le_minConv_pgpsWitnessFlow :
    (2⁻¹ : ℝ≥0) ≤ minConv pgpsWitnessFlow (pgpsResidual (rate 1) 1) 2 := by
  refine le_minConv fun u v huv => ?_
  rw [pgpsResidual_apply, rate_apply, one_mul]
  rcases le_total (2⁻¹ : ℝ≥0) u with hu | hu
  · exact le_trans (le_min hu (by norm_num)) le_self_add
  · have hv : (2 : ℝ≥0) - u = v := by
      rw [← huv, add_tsub_cancel_left]
    have hv32 : (3 / 2 : ℝ≥0) ≤ v := by
      rw [← hv]
      refine le_tsub_of_add_le_right ?_
      calc (3 / 2 : ℝ≥0) + u ≤ 3 / 2 + 2⁻¹ := add_le_add le_rfl hu
        _ = 2 := by norm_num
    refine le_trans ?_ le_add_self
    refine le_tsub_of_add_le_right ?_
    calc (2⁻¹ : ℝ≥0) + 1 = 3 / 2 := by norm_num
      _ ≤ v := hv32

/-- **Vertical closeness is not enough**: replacing the horizontal
deadline by the book's carried bound `D ≤ D̂ + ℓᵘ` (with PGPS
causality) refutes the universally quantified conclusion — the
hypotheses mirror `minConv_pgpsResidual_le_of_isPgpsTracking`
verbatim, with only the tracking field swapped. Witness: the
never-backlogged flow `min(·, 1)` against the zero PGPS departure,
with `β = λ₁`, `R = ℓᵘ = 1`, refuted at `t = 2`. -/
theorem not_forall_minConv_pgpsResidual_le_of_closeness :
    ¬ ∀ (A D Dh : ℝ≥0 → ℝ≥0) (β : ℝ≥0 → ℝ≥0) (R lu : ℝ≥0),
      IsLeftContinuous A → IsLeftContinuous D →
      A 0 = D 0 → A 0 = 0 → β 0 = 0 →
      (∀ x, D x ≤ A x) →
      (∀ s t, s ≤ t → IsBacklogged A D (Set.Ioc s t) →
        D s + β (t - s) ≤ D t) →
      Dh ≤ A → (∀ x, D x ≤ Dh x + lu) →
      (∀ v w, w ≤ v → β v ≤ β w + R * (v - w)) →
      ∀ t, minConv A (pgpsResidual β lu) t ≤ Dh t := by
  intro h
  have hlc : IsLeftContinuous pgpsWitnessFlow :=
    isLeftContinuous_of_continuous _
      (continuous_id.min continuous_const)
  have hβ0 : rate (1 : ℝ≥0) 0 = 0 := by rw [rate_apply, mul_zero]
  have hW := h pgpsWitnessFlow pgpsWitnessFlow (fun _ => 0) (rate 1)
    1 1 hlc hlc rfl (min_eq_left zero_le') hβ0 (fun x => le_rfl)
    (fun s t hst hbl => pgpsWitnessFlow_strict hβ0 s t hst hbl)
    (fun x => zero_le') (fun x => by
      rw [zero_add]
      exact min_le_right x 1)
    (rate_lipschitz le_rfl) 2
  have hcontra := le_trans le_minConv_pgpsWitnessFlow hW
  exact absurd hcontra (by norm_num)

/-! ## Book restatement (PGPS residual service, Theorem 8.4 repaired)
An `n`-server under PGPS at line rate `R` whose GPS reference offers
flow `i` the strict service curve `βᵢᴳᴾˢ`, with packets of length at
most `ℓᵘ`: flow `i` is guaranteed `[βᵢᴳᴾˢ − ℓᵘ]⁺` min-plus. **Book
gap (adjudicated):** the book's final step reads
`D̂ᵢ(t) ≥ Dᵢ(t) − ℓᵘ ≥ Aᵢ(s) + βᵢᴳᴾˢ(t − s)` with
`s = start_{Ŝ,i}(t)` — it applies the *reference*'s strict service on
the *PGPS* pair's backlogged window, which needs the reference pair
backlogged there with `Aᵢ = Dᵢ` at the PGPS start; neither follows
from the vertical closeness `Dᵢ − D̂ᵢ ≤ ℓᵘ` the proof carries (the
printed chain also drops a `− ℓᵘ` after the `β` term). The step is
false as stated — three independent analyses produced runs satisfying
every hypothesis where it fails — but the theorem is true: split at
the *reference* start of `t − ℓᵘ/R` and route through the horizontal
deadline `Dᵢ(u) ≤ D̂ᵢ(u + ℓᵘ/R)` (the book's own per-packet deadline
`tₖ ≤ uₖ + ℓᵘ/R` in cumulative form, `IsPgpsTracking`). The sharp
form is the delayed residual `βᵢᴳᴾˢ(· − ℓᵘ/R)`; the printed
`[βᵢᴳᴾˢ − ℓᵘ]⁺` follows when `βᵢᴳᴾˢ` is `R`-Lipschitz — automatic
for the GPS share `λ_{gᵢ}` of the `λ_R` aggregate
(`ServersResidualGps`), a genuine extra hypothesis in general. -/
example {A D Dh : ℝ≥0 → ℝ≥0} {g R lu : ℝ≥0}
    (hAlc : IsLeftContinuous A) (hDlc : IsLeftContinuous D)
    (h0 : A 0 = D 0) (hA0 : A 0 = 0)
    (hcD : ∀ x, D x ≤ A x)
    (hstrict : ∀ s t, s ≤ t → IsBacklogged A D (Set.Ioc s t) →
      D s + rate g (t - s) ≤ D t)
    (hp : IsPgpsTracking A D Dh R lu) (hg : g ≤ R) :
    (∀ t, minConv A (pgpsResidual (rate g) lu) t ≤ Dh t)
      ∧ ∀ t, minConv A (pgpsResidualShifted (rate g) R lu) t ≤ Dh t :=
  ⟨fun t => minConv_pgpsResidual_rate_le_of_isPgpsTracking hAlc hDlc
      h0 hA0 hcD hstrict hp hg t,
    fun t => minConv_pgpsResidualShifted_le_of_isPgpsTracking hAlc
      hDlc h0 hA0 (by rw [rate_apply, mul_zero]) hcD hstrict hp t⟩

end DeepWiki
