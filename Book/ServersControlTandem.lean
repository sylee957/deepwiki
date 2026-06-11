import Book.Deconvolution
import Book.ServersConcatenation
import Book.RealCurvesConv
import Book.DeviationsBounds

/-! # Tandem control
Designing a filter in front of a server: the server offers the min-plus
service curve `β`, and the controlled network `A → [βc] → A' → [β] → D`
must reach a reference behavior `βref`. By the concatenation theorem the
controlled network is guaranteed `βc ∗ β` — at the relation level, any
admissible controller makes `Smp(β) ∘ Smp(βc)` offer `βref` — so the
admissible controllers are `{βc | βref ≤ βc ∗ β}`, and by residuation the
smallest one is the deconvolution `β̂c = βref ⊘ β`. For a delay
requirement `τ`, arrival curves below `(β ⊘ δ_τ)⋆` keep `hDev(α, β) ≤ τ`;
for a backlog requirement `b`, arrival curves below `(β + b)⋆` keep
`vDev(α, β) ≤ b` — each closure being the largest sub-additive curve with
its property. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- The admissible tandem controllers for a server curve `β` and a
reference `βref`: the curves `βc` whose controlled-network guarantee
dominates the reference, `βref ≤ βc ∗ β`. -/
def tandemControlSet (β βref : ℝ≥0 → ℝ≥0∞) : Set (ℝ≥0 → ℝ≥0∞) :=
  {βc | βref ≤ minConv βc β}

/-- `βc` is an admissible tandem controller iff `βref ≤ βc ∗ β`. -/
theorem mem_tandemControlSet_iff {β βref βc : ℝ≥0 → ℝ≥0∞} :
    βc ∈ tandemControlSet β βref ↔ βref ≤ minConv βc β :=
  Iff.rfl

/-- **Tandem control**: the smallest service curve `βc` with
`βc ∗ β ≥ βref` is the deconvolution `βref ⊘ β` — it is itself admissible
and lies below every admissible controller (residuation). -/
theorem isLeast_tandemControlSet (β βref : ℝ≥0 → ℝ≥0∞) :
    IsLeast (tandemControlSet β βref) (minDeconv βref β) :=
  ⟨minDeconv_le_iff_le_minConv.mp le_rfl,
    fun _ hβc => minDeconv_le_iff_le_minConv.mpr hβc⟩

/-- The infimum form of tandem control:
`β̂c = ⋀{βc | βc ∗ β ≥ βref} = βref ⊘ β`. -/
theorem sInf_tandemControlSet (β βref : ℝ≥0 → ℝ≥0∞) :
    sInf (tandemControlSet β βref) = minDeconv βref β :=
  (isLeast_tandemControlSet β βref).csInf_eq

/-- **The controlled network reaches the reference**: a filter curve `βc`
with `βref ≤ βc ∗ β` in front of the server makes the tandem
`Smp(β) ∘ Smp(βc)` offer `βref` (bounded-below curves). -/
theorem comp_minimalServiceRel_le_of_le_minConv
    {β βref βc : ℝ≥0 → EReal}
    (hbc : IsBddBelowReal βc) (hb : IsBddBelowReal β)
    (h : βref ≤ minConv βc β) :
    Relation.Comp (minimalServiceRel βc) (minimalServiceRel β)
      ≤ minimalServiceRel βref :=
  le_trans (comp_minimalServiceRel_le hbc hb) (minimalServiceRel_mono h)

/-! ## Book restatement (tandem control)
Let `βref` be the min-plus service curve the controlled network has to
reach. The smallest service curve `βc`, such that `βc ∗ β ≥ βref`, is
`β̂c = ⋀{βc | βc ∗ β ≥ βref} = βref ⊘ β`. This is a direct application of
the residuation `f ⊘ g ≤ h ↔ f ≤ h ∗ g` (`minDeconv_le_iff_le_minConv`). -/
example (β βref : ℝ≥0 → ℝ≥0∞) :
    sInf {βc : ℝ≥0 → ℝ≥0∞ | βref ≤ minConv βc β} = minDeconv βref β :=
  sInf_tandemControlSet β βref

/-! The infimum is attained: `β̂c` is itself an admissible controller, so
the controlled network designed with `β̂c = βref ⊘ β` reaches `βref`. -/
example (β βref : ℝ≥0 → ℝ≥0∞) :
    βref ≤ minConv (minDeconv βref β) β :=
  (isLeast_tandemControlSet β βref).1

/-! ## Delay requirement -/

/-- **Tandem control with a delay requirement**: an arrival curve below the
delay-`τ` deconvolution meets the requirement — `α ≤ β ⊘ δ_τ` gives
`hDev(α, β) ≤ τ`, each `t` admitting the shift witness `τ` since
`(β ⊘ δ_τ) t = β (t + τ)`. -/
theorem hDev_le_of_le_minDeconv_delayNN {α β : ℝ≥0 → ℝ≥0∞} {τ : ℝ≥0}
    (hβmono : Monotone β) (h : α ≤ minDeconv β (delayNN τ)) :
    (hDev α β : ℝ≥0∞) ≤ τ := by
  refine hDev_le fun t => hDevAt_le ?_
  have ht := h t
  rwa [minDeconv_delayNN β hβmono τ] at ht

/-- The closure form: `α ≤ (β ⊘ δ_τ)⋆` still meets the delay requirement,
the closure lying below the deconvolution. -/
theorem hDev_le_of_le_subadditiveClosureENN_minDeconv
    {α β : ℝ≥0 → ℝ≥0∞} {τ : ℝ≥0} (hβmono : Monotone β)
    (h : α ≤ subadditiveClosureENN (minDeconv β (delayNN τ))) :
    (hDev α β : ℝ≥0∞) ≤ τ :=
  hDev_le_of_le_minDeconv_delayNN hβmono fun t =>
    (h t).trans (subadditiveClosureENN_le _ t)

/-- Exceeding the deconvolution anywhere forfeits the delay requirement:
`β (t + τ) < α t` at some `t` gives `τ ≤ hDev(α, β)`. (The book states the
strict `hDev > τ`; with the infimum-based `hDevAt` only the large
inequality holds — a right-jump of `β` just after `t + τ` keeps
`hDevAt = τ`.) -/
theorem le_hDev_of_apply_add_lt {α β : ℝ≥0 → ℝ≥0∞} {τ : ℝ≥0}
    (hβmono : Monotone β) {t : ℝ≥0} (hlt : β (t + τ) < α t) :
    (τ : ℝ≥0∞) ≤ hDev α β := by
  refine le_trans (le_hDevAt fun d hd => ?_) (hDevAt_le_hDev α β t)
  rcases le_or_gt τ d with hτd | hτd
  · exact ENNReal.coe_le_coe.mpr hτd
  · exact absurd hd (not_le.mpr (lt_of_le_of_lt
      (hβmono (add_le_add_right hτd.le t)) hlt))

/-- **Optimality of the closure**: every sub-additive arrival curve (null
at the origin) below the deconvolution `β ⊘ δ_τ` lies below its
sub-additive closure `(β ⊘ δ_τ)⋆` — the closure is the largest
sub-additive curve meeting the delay requirement through the
deconvolution. -/
theorem le_subadditiveClosureENN_minDeconv_of_isSubadditive
    {α β : ℝ≥0 → ℝ≥0∞} {τ : ℝ≥0} (hsub : IsSubadditive α) (h0 : α 0 = 0)
    (h : α ≤ minDeconv β (delayNN τ)) :
    α ≤ subadditiveClosureENN (minDeconv β (delayNN τ)) :=
  fun t => le_subadditiveClosureENN_of_isSubadditive hsub h0 h t

/-! ## Book restatement (delay requirement)
Let `β ∈ F₀↑` be the service curve of a server and `τ` a fixed maximal
delay. If `α ≤ (β ⊘ δ_τ)⋆`, then `hDev(α, β) ≤ τ`. Moreover `(β ⊘ δ_τ)⋆`
is the largest sub-additive function with this property: it is
sub-additive and dominates every sub-additive `α` below the deconvolution,
while exceeding the deconvolution forfeits the requirement (`τ ≤ hDev`,
the sharp form of the book's strict claim under the infimum-based
deviation). -/
example {β : ℝ≥0 → ℝ≥0∞} (hβmono : Monotone β) (τ : ℝ≥0) :
    (∀ α : ℝ≥0 → ℝ≥0∞,
        α ≤ subadditiveClosureENN (minDeconv β (delayNN τ)) →
          (hDev α β : ℝ≥0∞) ≤ τ)
      ∧ IsSubadditive (subadditiveClosureENN (minDeconv β (delayNN τ)))
      ∧ ∀ α : ℝ≥0 → ℝ≥0∞, IsSubadditive α → α 0 = 0 →
          α ≤ minDeconv β (delayNN τ) →
            α ≤ subadditiveClosureENN (minDeconv β (delayNN τ)) :=
  ⟨fun _ hα => hDev_le_of_le_subadditiveClosureENN_minDeconv hβmono hα,
    subadditiveClosureENN_subadditive _,
    fun _ hsub h0 hα =>
      le_subadditiveClosureENN_minDeconv_of_isSubadditive hsub h0 hα⟩

/-! In other words: through a server pair `(A, D)` offering the service
curve `β`, an `α`-constrained arrival with `α ≤ (β ⊘ δ_τ)⋆` has delay at
most `τ`. -/
example {A D : ℝ≥0 → ℝ≥0} {α β : ℝ≥0 → ℝ≥0∞} {τ : ℝ≥0}
    (hA : Monotone A) (hβmono : Monotone β)
    (harr : IsMaximalArrivalBound (Deviation.liftENN A) α)
    (hserv : ∀ t, minConv (Deviation.liftENN A) β t ≤ (D t : ℝ≥0∞))
    (hα : α ≤ subadditiveClosureENN (minDeconv β (delayNN τ))) :
    Deviation.delay A D ≤ (τ : ℝ≥0∞) :=
  le_trans (Deviation.delay_le_hDev hA hβmono harr hserv)
    (hDev_le_of_le_subadditiveClosureENN_minDeconv hβmono hα)

/-! ## Backlog requirement -/

/-- **Tandem control with a backlog requirement**: an arrival curve below
the raised service curve meets it — `α ≤ β + b` gives `vDev(α, β) ≤ b`. -/
theorem vDev_le_of_le_add {α β : ℝ≥0 → ℝ≥0∞} {b : ℝ≥0∞}
    (h : α ≤ fun t => β t + b) :
    vDev α β ≤ b :=
  vDev_le fun t => tsub_le_iff_left.mpr (h t)

/-- The closure form: `α ≤ (β + b)⋆` still meets the backlog requirement,
the closure lying below the raised curve. -/
theorem vDev_le_of_le_subadditiveClosureENN_add {α β : ℝ≥0 → ℝ≥0∞}
    {b : ℝ≥0∞} (h : α ≤ subadditiveClosureENN fun t => β t + b) :
    vDev α β ≤ b :=
  vDev_le_of_le_add fun t => (h t).trans (subadditiveClosureENN_le _ t)

/-- Exceeding the raised curve anywhere forfeits the backlog requirement:
`β t + b < α t` at some `t` gives the strict `b < vDev(α, β)`. Unlike the
delay requirement, the vertical deviation is a supremum of pointwise
differences, so the book's strict claim is sharp here. -/
theorem lt_vDev_of_apply_add_lt {α β : ℝ≥0 → ℝ≥0∞} {b : ℝ≥0∞}
    {t : ℝ≥0} (hlt : β t + b < α t) :
    b < vDev α β := by
  refine lt_of_lt_of_le ?_ (vDevAt_le_vDev α β t)
  show b < α t - β t
  by_contra hcon
  rw [not_lt] at hcon
  exact absurd (tsub_le_iff_left.mp hcon) (not_le.mpr hlt)

/-- **Optimality of the closure**: every sub-additive arrival curve (null
at the origin) below the raised curve `β + b` lies below its sub-additive
closure `(β + b)⋆` — the closure is the largest sub-additive curve meeting
the backlog requirement through `β + b`. -/
theorem le_subadditiveClosureENN_add_of_isSubadditive
    {α β : ℝ≥0 → ℝ≥0∞} {b : ℝ≥0∞} (hsub : IsSubadditive α) (h0 : α 0 = 0)
    (h : α ≤ fun t => β t + b) :
    α ≤ subadditiveClosureENN fun t => β t + b :=
  fun t => le_subadditiveClosureENN_of_isSubadditive hsub h0 h t

/-! ## Book restatement (backlog requirement)
Let `β ∈ F₀↑` be the service curve of a server and `b` a fixed maximal
backlog. If `α ≤ (β + b)⋆`, then `vDev(α, β) ≤ b`. Moreover `(β + b)⋆` is
the largest sub-additive function with this property: it is sub-additive,
dominates every sub-additive `α` below `β + b`, and exceeding `β + b`
anywhere forces the strict `vDev(α, β) > b`. -/
example {β : ℝ≥0 → ℝ≥0∞} (b : ℝ≥0∞) :
    (∀ α : ℝ≥0 → ℝ≥0∞,
        α ≤ subadditiveClosureENN (fun t => β t + b) → vDev α β ≤ b)
      ∧ IsSubadditive (subadditiveClosureENN fun t => β t + b)
      ∧ ∀ α : ℝ≥0 → ℝ≥0∞, IsSubadditive α → α 0 = 0 →
          (α ≤ fun t => β t + b) →
            α ≤ subadditiveClosureENN fun t => β t + b :=
  ⟨fun _ hα => vDev_le_of_le_subadditiveClosureENN_add hα,
    subadditiveClosureENN_subadditive _,
    fun _ hsub h0 hα =>
      le_subadditiveClosureENN_add_of_isSubadditive hsub h0 hα⟩

/-! In other words: through a server pair `(A, D)` offering the service
curve `β`, an `α`-constrained arrival with `α ≤ (β + b)⋆` has backlog at
most `b`. -/
example {A D : ℝ≥0 → ℝ≥0} {α β : ℝ≥0 → ℝ≥0∞} {b : ℝ≥0∞}
    (harr : IsMaximalArrivalBound (Deviation.liftENN A) α)
    (hserv : ∀ t, minConv (Deviation.liftENN A) β t ≤ (D t : ℝ≥0∞))
    (hα : α ≤ subadditiveClosureENN fun t => β t + b) :
    Deviation.backlog A D ≤ b :=
  le_trans (Deviation.backlog_le_vDev harr hserv)
    (vDev_le_of_le_subadditiveClosureENN_add hα)

end DeepWiki
