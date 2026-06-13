import Book.ServersResidualGps
import Book.RealCurves

/-! # Packetized-GPS residual service
PGPS serves whole packets in the order their bits would complete under
a GPS reference with the same arrivals. `IsPgpsTracking` is a
*bit-level* horizontal tracking assumption — every bit cleared by the
reference at `u` is cleared by PGPS by `u + ℓᵘ/R` — strictly stronger
than the book's packet-level completion deadline `tₖ ≤ uₖ + ℓᵘ/R`:
fluid GPS partially serves packets whose completion lies far ahead,
and a genuine PGPS run violates the bit-level form (`pgpsRun_*`). The
tracking yields the delayed residual `β(· − ℓᵘ/R)`
(`pgpsResidualShifted`) by splitting at the *reference* start of
`t − ℓᵘ/R`, and the book's `[β − ℓᵘ]⁺` (`pgpsResidual`) when `β` is
`R`-Lipschitz; the packet deadline's faithful cumulative consequence
`D ≤ D̂(· + ℓᵘ/R) + ℓᵘ` gives the same residual with one packet of
slack on the output. The weaker *vertical* closeness `D − D̂ ≤ ℓᵘ` is
provably insufficient — see the refutation ladder. Everything is
pair-level on one flow's `(A, D, D̂)`: the `n`-flow aggregate, the
`φ`-weights, and the `λ_R`-greedy-shaper coupling of the two systems
are not formalized, and no derivation of the tracking from the PGPS
dynamics is attempted. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- **PGPS tracking** (bit-level): the PGPS departure `Dh` is causal
and every bit the reference clears at `u` is cleared by PGPS by
`u + ℓᵘ/R`. This is *strictly stronger* than the book's packet-level
completion deadline `tₖ ≤ uₖ + ℓᵘ/R` — fluid GPS partially serves
packets whose completion lies far ahead, and genuine PGPS runs can
violate the bit-level form (`pgpsRun_not_isPgpsTracking`); the
deadline's faithful cumulative consequence carries one packet of
slack (`minConv_pgpsResidualShifted_le_add_of_close`). -/
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
    (hc : ∀ x, D x ≤ A x)
    (hstrict : ∀ s t, s ≤ t → IsBacklogged A D (Set.Ioc s t) →
      D s + β (t - s) ≤ D t)
    (hpgps : IsPgpsTracking A D Dh R lu) (t : ℝ≥0) :
    minConv A (pgpsResidualShifted β R lu) t ≤ Dh t := by
  obtain ⟨-, hshift⟩ := hpgps
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
      apply_start_eq hAlc hDlc h0 hc (t - lu / R)
    have hstr := hstrict (start A D (t - lu / R)) (t - lu / R) hsσ
      (isBacklogged_Ioc_start hc (t - lu / R))
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
`β` the tracking pair satisfies the min-plus inequality for
`[β − ℓᵘ]⁺`, via `pgpsResidual_le_pgpsResidualShifted`. The Lipschitz
hypothesis is automatic for the GPS share `λ_g`, `g ≤ R`
(`rate_lipschitz`), a genuine extra hypothesis in general. -/
theorem minConv_pgpsResidual_le_of_isPgpsTracking
    {A D Dh : ℝ≥0 → ℝ≥0} {β : ℝ≥0 → ℝ≥0} {R lu : ℝ≥0}
    (hAlc : IsLeftContinuous A) (hDlc : IsLeftContinuous D)
    (h0 : A 0 = D 0) (hA0 : A 0 = 0) (hβ0 : β 0 = 0)
    (hc : ∀ x, D x ≤ A x)
    (hstrict : ∀ s t, s ≤ t → IsBacklogged A D (Set.Ioc s t) →
      D s + β (t - s) ≤ D t)
    (hpgps : IsPgpsTracking A D Dh R lu)
    (hLip : ∀ v w, w ≤ v → β v ≤ β w + R * (v - w)) (t : ℝ≥0) :
    minConv A (pgpsResidual β lu) t ≤ Dh t := by
  refine le_trans (le_minConv fun u s hus => ?_)
    (minConv_pgpsResidualShifted_le_of_isPgpsTracking hAlc hDlc h0
      hA0 hβ0 hc hstrict hpgps t)
  exact le_trans (minConv_le_add _ _ hus)
    (add_le_add le_rfl (pgpsResidual_le_pgpsResidualShifted hLip s))

/-- **PGPS over a GPS share** (rate form): when the reference offers
the strict rate `λ_g` with `g` at most the line rate `R`, the tracking
pair satisfies the min-plus inequality for `[λ_g − ℓᵘ]⁺` — the
Lipschitz hypothesis discharges automatically. -/
theorem minConv_pgpsResidual_rate_le_of_isPgpsTracking
    {A D Dh : ℝ≥0 → ℝ≥0} {g R lu : ℝ≥0}
    (hAlc : IsLeftContinuous A) (hDlc : IsLeftContinuous D)
    (h0 : A 0 = D 0) (hA0 : A 0 = 0)
    (hc : ∀ x, D x ≤ A x)
    (hstrict : ∀ s t, s ≤ t → IsBacklogged A D (Set.Ioc s t) →
      D s + rate g (t - s) ≤ D t)
    (hpgps : IsPgpsTracking A D Dh R lu) (hg : g ≤ R) (t : ℝ≥0) :
    minConv A (pgpsResidual (rate g) lu) t ≤ Dh t :=
  minConv_pgpsResidual_le_of_isPgpsTracking hAlc hDlc h0 hA0
    (rate_zero_eq g) hc hstrict hpgps (rate_lipschitz hg) t

/-- Model witness: the constant-rate triple `A = D = D̂ = λ_r`
satisfies the bit-level tracking for every line rate and packet
bound. -/
theorem isPgpsTracking_rate (r R lu : ℝ≥0) :
    IsPgpsTracking (rate r) (rate r) (rate r) R lu :=
  ⟨le_rfl, fun _ => mul_le_mul' le_rfl le_self_add⟩

/-- **Faithful packet-deadline form**: the book's per-packet
completion deadline only yields the cumulative bound with one packet
of slack, `D ≤ D̂(· + ℓᵘ/R) + ℓᵘ` — fluid GPS may have partially
served one more packet per flow. Under it the same reference-start
split gives the delayed residual with the slack on the output. -/
theorem minConv_pgpsResidualShifted_le_add_of_close
    {A D Dh : ℝ≥0 → ℝ≥0} {β : ℝ≥0 → ℝ≥0} {R lu : ℝ≥0}
    (hAlc : IsLeftContinuous A) (hDlc : IsLeftContinuous D)
    (h0 : A 0 = D 0) (hA0 : A 0 = 0) (hβ0 : β 0 = 0)
    (hc : ∀ x, D x ≤ A x)
    (hstrict : ∀ s t, s ≤ t → IsBacklogged A D (Set.Ioc s t) →
      D s + β (t - s) ≤ D t)
    (hclose : ∀ u, D u ≤ Dh (u + lu / R) + lu) (t : ℝ≥0) :
    minConv A (pgpsResidualShifted β R lu) t ≤ Dh t + lu := by
  rcases le_total t (lu / R) with htc | hct
  · refine le_trans (minConv_le_add _ _ (zero_add t)) ?_
    rw [hA0, zero_add, pgpsResidualShifted_apply,
      tsub_eq_zero_of_le htc, hβ0]
    exact zero_le'
  · have hsσ : start A D (t - lu / R) ≤ t - lu / R :=
      start_le A D _
    have hσt : start A D (t - lu / R) ≤ t := hsσ.trans tsub_le_self
    refine le_trans (minConv_le_add _ _
      (add_tsub_cancel_of_le hσt)) ?_
    have heq : A (start A D (t - lu / R))
        = D (start A D (t - lu / R)) :=
      apply_start_eq hAlc hDlc h0 hc (t - lu / R)
    have hstr := hstrict (start A D (t - lu / R)) (t - lu / R) hsσ
      (isBacklogged_Ioc_start hc (t - lu / R))
    have hsh := hclose (t - lu / R)
    rw [tsub_add_cancel_of_le hct] at hsh
    rw [pgpsResidualShifted_apply, tsub_right_comm]
    calc A (start A D (t - lu / R))
          + β ((t - lu / R) - start A D (t - lu / R))
        = D (start A D (t - lu / R))
          + β ((t - lu / R) - start A D (t - lu / R)) := by rw [heq]
      _ ≤ D (t - lu / R) := hstr
      _ ≤ Dh t + lu := hsh

/-! ## A genuine PGPS run violates the bit-level tracking
Four equal-weight flows, one unit packet each at the origin, line
rate `R = 1`: GPS serves the tagged (last-scheduled) flow at rate
`1/4`, PGPS serves its packet on `[3, 4]`. The packet deadline holds
(`t₄ = 4 ≤ u₄ + 1`), the vertical closeness holds, but at `u = 2` the
reference has cleared half a packet while PGPS has cleared nothing by
`u + ℓᵘ/R = 3` — the bit-level field fails. -/

/-- The counter-run arrivals: one unit packet at the origin. -/
noncomputable def pgpsRunA : ℝ≥0 → ℝ≥0 := fun x => if x = 0 then 0 else 1

/-- The counter-run GPS reference departure: rate `1/4` up to one
packet. -/
noncomputable def pgpsRunD : ℝ≥0 → ℝ≥0 := fun x => min (x / 4) 1

/-- The counter-run PGPS departure: the packet is served on `[3, 4]`. -/
noncomputable def pgpsRunDh : ℝ≥0 → ℝ≥0 := fun x => min (x - 3) 1

/-- The counter-run is causal and vertically close: the reference
never leads PGPS by more than the packet. -/
theorem pgpsRun_close :
    (∀ x, pgpsRunDh x ≤ pgpsRunA x) ∧ ∀ x, pgpsRunD x ≤ pgpsRunDh x + 1 := by
  constructor
  · intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp [pgpsRunDh, pgpsRunA]
    · rw [pgpsRunA, if_neg hx]
      exact min_le_right _ _
  · intro x
    exact le_trans (min_le_right _ _) le_add_self

/-- The counter-run violates the bit-level tracking at `u = 2`:
`D(2) = 1/2` but `D̂(3) = 0`. -/
theorem pgpsRun_not_isPgpsTracking :
    ¬ IsPgpsTracking pgpsRunA pgpsRunD pgpsRunDh 1 1 := by
  rintro ⟨-, hshift⟩
  have h := hshift 2
  rw [show (2 : ℝ≥0) + 1 / 1 = 3 by norm_num] at h
  rw [show pgpsRunDh 3 = 0 by
    simp [pgpsRunDh, tsub_self]] at h
  rw [show pgpsRunD 2 = 2⁻¹ by
    rw [pgpsRunD, min_eq_left (by norm_num)]
    norm_num] at h
  exact absurd h (by norm_num)

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
theorem half_le_minConv_pgpsResidual_pgpsWitnessFlow :
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
  have hβ0 : rate (1 : ℝ≥0) 0 = 0 := rate_zero_eq 1
  have hW := h pgpsWitnessFlow pgpsWitnessFlow (fun _ => 0) (rate 1)
    1 1 hlc hlc rfl (min_eq_left zero_le') hβ0 (fun x => le_rfl)
    (fun s t hst hbl => pgpsWitnessFlow_strict hβ0 s t hst hbl)
    (fun x => zero_le') (fun x => by
      rw [zero_add]
      exact min_le_right x 1)
    (rate_lipschitz le_rfl) 2
  have hcontra := le_trans half_le_minConv_pgpsResidual_pgpsWitnessFlow hW
  exact absurd hcontra (by norm_num)

/-! ## Book restatement (PGPS residual service, Theorem 8.4)
An `n`-server under PGPS at line rate `R` whose GPS reference offers
flow `i` the strict service curve `βᵢᴳᴾˢ`, with packets of length at
most `ℓᵘ`: flow `i` is guaranteed `[βᵢᴳᴾˢ − ℓᵘ]⁺` min-plus. **Book
gap (adjudicated):** the book's final step reads
`D̂ᵢ(t) ≥ Dᵢ(t) − ℓᵘ ≥ Aᵢ(s) + βᵢᴳᴾˢ(t − s)` with
`s = start_{Ŝ,i}(t)` — it applies the *reference*'s strict service on
the *PGPS* pair's backlogged window, which needs the reference pair
backlogged there with `Aᵢ = Dᵢ` at the PGPS start; neither follows
from the vertical closeness `Dᵢ − D̂ᵢ ≤ ℓᵘ` the proof carries. Three
independent analyses produced PGPS runs satisfying every theorem
hypothesis where the step fails; the formal ladder below certifies
the pair-level core — vertical closeness plus causality does not
yield the residual. (The book's printed Step-3 chain is correct as
written — `Dᵢ(t) − ℓᵘ ≥ Aᵢ(s) + βᵢᴳᴾˢ(t − s)`, the `− ℓᵘ` on the
`Dᵢ` side — and the slack-free residual DOES hold for genuine PGPS;
the gap is only the *reference-vs-PGPS start* mismatch, closed by
splitting at the reference clear instant under the packet-deadline
window, not by the bit-level tracking this file uses.) **Scope of the formalization:** the conclusion is
recovered here from the bit-level tracking `Dᵢ(u) ≤ D̂ᵢ(u + ℓᵘ/R)`
(`IsPgpsTracking`), splitting at the *reference* start of `t − ℓᵘ/R`;
that tracking is *strictly stronger* than the book's per-packet
deadline `tₖ ≤ uₖ + ℓᵘ/R` (`pgpsRun_not_isPgpsTracking`), whose
faithful cumulative consequence yields the residual only with one
packet of slack (`minConv_pgpsResidualShifted_le_add_of_close`).
Whether the slack-free conclusion follows from the PGPS dynamics
alone is not settled here: the `n`-flow aggregate, the `φ`-weights,
and the `λ_R`-greedy-shaper coupling are outside the formalization.
The delayed residual `βᵢᴳᴾˢ(· − ℓᵘ/R)` is the stronger conclusion
under the tracking; the printed `[βᵢᴳᴾˢ − ℓᵘ]⁺` follows when
`βᵢᴳᴾˢ` is `R`-Lipschitz — automatic for the GPS share `λ_{gᵢ}` of
the `λ_R` aggregate (`ServersResidualGps`), a genuine extra
hypothesis in general. -/
example {A D Dh : ℝ≥0 → ℝ≥0} {g R lu : ℝ≥0}
    (hAlc : IsLeftContinuous A) (hDlc : IsLeftContinuous D)
    (h0 : A 0 = D 0) (hA0 : A 0 = 0)
    (hc : ∀ x, D x ≤ A x)
    (hstrict : ∀ s t, s ≤ t → IsBacklogged A D (Set.Ioc s t) →
      D s + rate g (t - s) ≤ D t)
    (hpgps : IsPgpsTracking A D Dh R lu) (hg : g ≤ R) :
    (∀ t, minConv A (pgpsResidual (rate g) lu) t ≤ Dh t)
      ∧ ∀ t, minConv A (pgpsResidualShifted (rate g) R lu) t ≤ Dh t :=
  ⟨fun t => minConv_pgpsResidual_rate_le_of_isPgpsTracking hAlc hDlc
      h0 hA0 hc hstrict hpgps hg t,
    fun t => minConv_pgpsResidualShifted_le_of_isPgpsTracking hAlc
      hDlc h0 hA0 (rate_zero_eq g) hc hstrict hpgps t⟩

end DeepWiki
