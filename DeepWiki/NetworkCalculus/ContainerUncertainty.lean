import DeepWiki.NetworkCalculus.ContainerCanonical
import DeepWiki.NetworkCalculus.AlmostConcave
import DeepWiki.NetworkCalculus.Containers
import DeepWiki.NetworkCalculus.Deviations

/-! # Maximal uncertainty of a container (Definition 4.4)
The §4.4.2 measure of how much a container `f = [f̲, f̄]_𝓛` (in canonical form)
can lose in precision: the maximal vertical/horizontal gap between its lower
bound `f̲` and upper bound `f̄`, evaluated at a rank-determined abscissa `t₀`.

A canonical container's bounds are ultimately linear; the **rank** `T_f` of an
ultimately linear `f` is the abscissa of its last semi-infinite segment. The two
maximal uncertainties of `f = [f̲, f̄]_𝓛` are (Definition 4.4, with the upper
bound `f̄` first, matching the book's `hDev(f̄, f̲)` / `vDev(f̄, f̲)`):

* **time domain** — `Dmax = inf_{τ≥0} {τ | f̄(t₀) ≤ f̲(t₀ + τ)}`, the pointwise
  horizontal deviation `hDevAt f̄ f̲ t₀`, where `t₀ = T_f̄` if `f̄(T_f̄) > f̲(T_f̲)`
  and `t₀ = T_f̲` otherwise;
* **data domain** — `Bmax = f̄(t₀) − f̲(t₀)`, the pointwise vertical deviation
  `vDevAt f̄ f̲ t₀`, where `t₀ = max{T_f̲, T_f̄}`.

Both are *pointwise* deviations at the single rank-determined `t₀` (the book
overloads the `hDev`/`vDev` notation for these single-point quantities). The
ranks `T_f̲`, `T_f̄` are the canonical-form data carried alongside the container.
`Dmax` is valued in `ℝ≥0∞` (an unreachable upper bound reads `⊤`); `Bmax` in
`EReal`. Built on the deviation API (`hDevAt`/`vDevAt`,
`DeepWiki.NetworkCalculus.Deviations`). -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

namespace Container

/-! ## The rank-determined abscissa `t₀` -/

/-- The abscissa `t₀` for the **data-domain** maximal uncertainty `Bmax`:
`max{T_f̲, T_f̄}` (Definition 4.4). Here `Tlo`/`Thi` are the ranks of the lower /
upper bounds (abscissae of their last semi-infinite segments). -/
def bmaxAbscissa (Tlo Thi : ℝ≥0) : ℝ≥0 := max Tlo Thi

/-- The abscissa `t₀` for the **time-domain** maximal uncertainty `Dmax`:
`T_f̄` if `f̄(T_f̄) > f̲(T_f̲)`, else `T_f̲` (Definition 4.4). -/
noncomputable def dmaxAbscissa (c : Container) (Tlo Thi : ℝ≥0) : ℝ≥0 :=
  if c.hi Thi > c.lo Tlo then Thi else Tlo

/-- `bmaxAbscissa` is symmetric in its two ranks: `max` is commutative. -/
theorem bmaxAbscissa_comm (Tlo Thi : ℝ≥0) :
    bmaxAbscissa Tlo Thi = bmaxAbscissa Thi Tlo := max_comm _ _

/-! ## Definition 4.4 — the two maximal uncertainties -/

/-- The **time-domain maximal uncertainty** `Dmax = hDev(f̄, f̲)` of a container
(Definition 4.4): the pointwise horizontal deviation of the upper bound `f̄` from
the lower bound `f̲` at the rank abscissa `t₀ = dmaxAbscissa`, namely
`inf_{τ≥0} {τ | f̄(t₀) ≤ f̲(t₀ + τ)}`, valued in `ℝ≥0∞`. -/
noncomputable def maximalUncertaintyTime (c : Container) (Tlo Thi : ℝ≥0) : ℝ≥0∞ :=
  hDevAt c.hi c.lo (c.dmaxAbscissa Tlo Thi)

/-- The **data-domain maximal uncertainty** `Bmax = vDev(f̄, f̲)` of a container
(Definition 4.4): the pointwise vertical deviation `f̄(t₀) − f̲(t₀)` at the rank
abscissa `t₀ = max{T_f̲, T_f̄}`, valued in `EReal`. -/
noncomputable def maximalUncertaintyData (c : Container) (Tlo Thi : ℝ≥0) : EReal :=
  vDevAt c.hi c.lo (bmaxAbscissa Tlo Thi)

/-- `Dmax = hDevAt f̄ f̲ t₀` (unfolds the time-domain maximal uncertainty). -/
theorem maximalUncertaintyTime_eq (c : Container) (Tlo Thi : ℝ≥0) :
    c.maximalUncertaintyTime Tlo Thi
      = hDevAt c.hi c.lo (c.dmaxAbscissa Tlo Thi) := rfl

/-- `Bmax = f̄(t₀) − f̲(t₀)` (unfolds the data-domain maximal uncertainty). -/
theorem maximalUncertaintyData_eq (c : Container) (Tlo Thi : ℝ≥0) :
    c.maximalUncertaintyData Tlo Thi
      = c.hi (bmaxAbscissa Tlo Thi) - c.lo (bmaxAbscissa Tlo Thi) := rfl

/-! ## Nonnegativity (`f̲ ≤ f̄`) -/

/-- The data-domain maximal uncertainty is nonnegative when the lower bound is
finite (`≠ ±∞`) at the rank abscissa: `f̲ ≤ f̄` gives `0 ≤ f̄(t₀) − f̲(t₀)`. -/
theorem zero_le_maximalUncertaintyData (c : Container) (Tlo Thi : ℝ≥0)
    (htop : c.lo (bmaxAbscissa Tlo Thi) ≠ ⊤)
    (hbot : c.lo (bmaxAbscissa Tlo Thi) ≠ ⊥) :
    0 ≤ c.maximalUncertaintyData Tlo Thi := by
  rw [maximalUncertaintyData_eq]
  exact (EReal.sub_nonneg (Or.inr htop) (Or.inr hbot)).2 (c.le _)

/-- The time-domain maximal uncertainty is nonnegative (it is an `ℝ≥0∞`). -/
theorem zero_le_maximalUncertaintyTime (c : Container) (Tlo Thi : ℝ≥0) :
    0 ≤ c.maximalUncertaintyTime Tlo Thi := bot_le

/-! ## The exact (singleton) container has zero uncertainty -/

/-- A singleton (exact) container has zero data-domain uncertainty at a finite
rank value: `Bmax = f(t₀) − f(t₀) = 0`. -/
theorem maximalUncertaintyData_singleton (f : ℝ≥0 → EReal) (Tlo Thi : ℝ≥0)
    (htop : f (bmaxAbscissa Tlo Thi) ≠ ⊤) (hbot : f (bmaxAbscissa Tlo Thi) ≠ ⊥) :
    (singleton f).maximalUncertaintyData Tlo Thi = 0 := by
  rw [maximalUncertaintyData_eq]
  exact EReal.sub_self htop hbot

/-- A singleton (exact) container has zero time-domain uncertainty: `f(t₀) ≤
f(t₀ + 0)` is admissible with shift `0`, so `Dmax = 0`. -/
theorem maximalUncertaintyTime_singleton (f : ℝ≥0 → EReal) (Tlo Thi : ℝ≥0) :
    (singleton f).maximalUncertaintyTime Tlo Thi = 0 := by
  rw [maximalUncertaintyTime_eq]
  refine le_antisymm ?_ bot_le
  have : (hDevAt (singleton f).hi (singleton f).lo
      ((singleton f).dmaxAbscissa Tlo Thi) : ℝ≥0∞) ≤ ((0 : ℝ≥0) : ℝ≥0∞) :=
    hDevAt_le (by simp only [singleton]; exact le_of_eq (by rw [add_zero]))
  simpa using this

/-! ## The full container `[⊥, ⊤]` has total uncertainty -/

/-- The full container `[⊥, ⊤]` has infinite data-domain uncertainty:
`Bmax = ⊤ − ⊥ = ⊤`. -/
@[simp] theorem maximalUncertaintyData_univ (Tlo Thi : ℝ≥0) :
    univ.maximalUncertaintyData Tlo Thi = ⊤ := by
  rw [maximalUncertaintyData_eq, univ_hi, univ_lo]
  rfl

/-- The full container `[⊥, ⊤]` has infinite time-domain uncertainty: the upper
bound is `⊤` everywhere, so `f̄(t₀) ≤ f̲(t₀ + τ)` (`⊤ ≤ ⊥`) is never admissible
and `Dmax = ⊤`. -/
@[simp] theorem maximalUncertaintyTime_univ (Tlo Thi : ℝ≥0) :
    univ.maximalUncertaintyTime Tlo Thi = ⊤ := by
  rw [maximalUncertaintyTime_eq]
  refine hDevAt_eq_top ℝ≥0∞ _ _ _ fun d => ?_
  rw [univ_hi, univ_lo]
  exact fun h => (lt_irrefl (⊥ : EReal)) (lt_of_lt_of_le bot_lt_top h)

/-! ## Inclusion-monotonicity (a wider container is more uncertain)

A container `c` included in a wider `d` (its bounds squeezed inward,
`d.lo ≤ c.lo` and `c.hi ≤ d.hi`) has no larger uncertainty. At **shared ranks**
the data abscissa `bmaxAbscissa Tlo Thi` coincides, so the data-domain
uncertainty is directly monotone; the time-domain version is stated at a fixed
shared abscissa (the time abscissa `dmaxAbscissa` depends on the curves). -/

/-- **Data-domain uncertainty is inclusion-monotone at shared ranks**: squeezing
the bounds inward (`d.lo ≤ c.lo`, `c.hi ≤ d.hi`) shrinks `Bmax`,
`c.Bmax ≤ d.Bmax`. -/
theorem maximalUncertaintyData_mono {c d : Container} (Tlo Thi : ℝ≥0)
    (hlo : d.lo ≤ c.lo) (hhi : c.hi ≤ d.hi) :
    c.maximalUncertaintyData Tlo Thi ≤ d.maximalUncertaintyData Tlo Thi := by
  rw [maximalUncertaintyData_eq, maximalUncertaintyData_eq]
  exact EReal.sub_le_sub (hhi _) (hlo _)

/-- **Time-domain uncertainty is monotone at a fixed abscissa**: squeezing the
bounds inward (`d.lo ≤ c.lo`, `c.hi ≤ d.hi`) shrinks the pointwise `Dmax` at any
shared abscissa `t₀`, `hDevAt c.hi c.lo t₀ ≤ hDevAt d.hi d.lo t₀`. -/
theorem hDevAt_maximalUncertaintyTime_mono {c d : Container}
    (hlo : d.lo ≤ c.lo) (hhi : c.hi ≤ d.hi) (t₀ : ℝ≥0) :
    (hDevAt c.hi c.lo t₀ : ℝ≥0∞) ≤ hDevAt d.hi d.lo t₀ :=
  hDevAt_mono hhi hlo t₀

/-! ## Faithfulness checks (against §4.4, book p. 89) -/

/-- Definition 4.4 (time domain): `Dmax = hDev(f̄, f̲) = inf_{τ≥0} {τ | f̄(t₀) ≤
f̲(t₀ + τ)}`, with the rank-determined `t₀`. -/
example (c : Container) (Tlo Thi : ℝ≥0) :
    c.maximalUncertaintyTime Tlo Thi
      = ⨅ d : {d : ℝ≥0 // c.hi (c.dmaxAbscissa Tlo Thi)
          ≤ c.lo (c.dmaxAbscissa Tlo Thi + d)}, (↑d.1 : ℝ≥0∞) := rfl

/-- Definition 4.4 (data domain): `Bmax = vDev(f̄, f̲) = f̄(t₀) − f̲(t₀)` with
`t₀ = max{T_f̲, T_f̄}`. -/
example (c : Container) (Tlo Thi : ℝ≥0) :
    c.maximalUncertaintyData Tlo Thi
      = c.hi (max Tlo Thi) - c.lo (max Tlo Thi) := rfl

/-- Definition 4.4: the data abscissa is `t₀ = max{T_f̲, T_f̄}`. -/
example (Tlo Thi : ℝ≥0) : bmaxAbscissa Tlo Thi = max Tlo Thi := rfl

/-- Definition 4.4: the time abscissa is `T_f̄` if `f̄(T_f̄) > f̲(T_f̲)`, else
`T_f̲`. -/
example (c : Container) (Tlo Thi : ℝ≥0) :
    c.dmaxAbscissa Tlo Thi = if c.hi Thi > c.lo Tlo then Thi else Tlo := rfl

end Container

end DeepWiki
