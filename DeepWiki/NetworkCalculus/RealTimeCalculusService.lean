import DeepWiki.NetworkCalculus.RealTimeCalculus

/-! # Real-time calculus: the greedy-processor service-curve guarantee
The RTC greedy processor of `RealTimeCalculus` (the bivariate equations
[9.4]–[9.6], `IsRtcGreedy`) **provides a service curve**. Following
Definition 9.1, an RTC server `C` *guarantees* the RTC minimal service
curve `βᵐ` when `βᵐ(t − s) ≤ C[s, t]` for `s ≤ t` — exactly the
capacity-domination hypothesis of a variable-capacity node, read through
the Chasles increment `C[s, t] = Ĉ(t) − Ĉ(s)`. We collect the univariate
readings of the greedy equations (the network-calculus reading `· 0 t`
of output/residual/backlog) and prove the service-curve guarantee
`Â ∗ βᵐ ≤ D̂`: the departure is bounded below by the min-plus convolution
of the arrival with `βᵐ`. The convolution `(f ∗ g)(t) = ⨅_{a+b=t} f a + g b`
is stated over `ℝ` (the carrier of the RTC cumulative functions); the
`Curve`-level transport into `minimalServiceRel`/`IsMinimalServiceCurve`
is recorded in the report (it needs the readings packaged as `Curve`s,
i.e. monotone / left-continuous regularity the bivariate framework does
not carry). -/

namespace DeepWiki

open scoped NNReal

/-! ## Definition 9.1: RTC arrival and service curves -/

/-- **Definition 9.1** (RTC service curve, lower half): the bivariate server `C`
**guarantees** the RTC minimal service curve `βᵐ` when every interval increment
dominates `βᵐ`: `βᵐ(t − s) ≤ C[s, t]` for `s ≤ t`. (`C[s, t] = C s t` is the
amount served over `[s, t]`.) -/
def GuaranteesRtcMinService (C : ℝ≥0 → ℝ≥0 → ℝ) (betaM : ℝ≥0 → ℝ) : Prop :=
  ∀ s t : ℝ≥0, s ≤ t → betaM (t - s) ≤ C s t

/-- **Definition 9.1** (RTC service curve, upper half): the bivariate server `C`
is **bounded by** the RTC maximal service curve `βᴹ` when every interval
increment is dominated by `βᴹ`: `C[s, t] ≤ βᴹ(t − s)` for `s ≤ t`. -/
def BoundedByRtcMaxService (C : ℝ≥0 → ℝ≥0 → ℝ) (betaMaj : ℝ≥0 → ℝ) : Prop :=
  ∀ s t : ℝ≥0, s ≤ t → C s t ≤ betaMaj (t - s)

/-- **Definition 9.1** (RTC arrival curve): the bivariate arrival `A` is
constrained by the RTC arrival curves `(αˡ, αᵘ)` when every increment lies
between them: `αˡ(t − s) ≤ A[s, t] ≤ αᵘ(t − s)` for `s ≤ t`. -/
def IsRtcArrival (A : ℝ≥0 → ℝ≥0 → ℝ) (alphaL alphaU : ℝ≥0 → ℝ) : Prop :=
  ∀ s t : ℝ≥0, s ≤ t → alphaL (t - s) ≤ A s t ∧ A s t ≤ alphaU (t - s)

/-- For a Chasles server, guaranteeing `βᵐ` is the univariate
capacity-domination `βᵐ(t − s) ≤ Ĉ(t) − Ĉ(s)` of a variable-capacity node:
the bivariate increment is the univariate gap, `C[s, t] = Ĉ(t) − Ĉ(s)`. -/
theorem guaranteesRtcMinService_iff_univariate {C : ℝ≥0 → ℝ≥0 → ℝ}
    (hC : IsChasles C) (betaM : ℝ≥0 → ℝ) :
    GuaranteesRtcMinService C betaM ↔
      ∀ s t : ℝ≥0, s ≤ t → betaM (t - s) ≤ C 0 t - C 0 s := by
  constructor
  · intro h s t hst
    rw [← hC.eq_univariate_sub hst]; exact h s t hst
  · intro h s t hst
    rw [hC.eq_univariate_sub hst]; exact h s t hst

/-! ## Univariate readings of the RTC greedy equations [9.4]–[9.6] -/

/-- **[9.4] univariate reading**: the network-calculus output `D̂(t) = D 0 t`
is the served amount minus the residual, `D̂(t) = Ĉ(t) − Ĉ'(t)`, directly from
equation [9.4] at `s = 0`. -/
theorem departure_univariate_of_isRtcGreedy {A C D C' : ℝ≥0 → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} (hg : IsRtcGreedy A C D C' b) (t : ℝ≥0) :
    D 0 t = C 0 t - C' 0 t := hg.1 0 t zero_le

/-- The RTC greedy output is the variable-capacity-node output [9.7]:
`D̂(t) = ⨅_{u ≤ t} (Ĉ(t) − Ĉ(u) + Â(u))`, the network-calculus reading of the
greedy processor (the supremum [9.5] turned into an infimum). -/
theorem departure_eq_varCapacityOutput_of_isRtcGreedy
    {A C D C' : ℝ≥0 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (hA : IsChasles A) (hC : IsChasles C) (hb0 : b 0 = 0)
    (hg : IsRtcGreedy A C D C' b)
    (hbdd : ∀ t : ℝ≥0,
      BddAbove (Set.range fun u : {u : ℝ≥0 // u ≤ t} => C 0 u.1 - A 0 u.1))
    (t : ℝ≥0) :
    D 0 t = ⨅ u : {u : ℝ≥0 // u ≤ t}, (C 0 t - C 0 u.1 + A 0 u.1) :=
  (isVarCapacityEqns_of_isRtcGreedy hA hC hb0 hg hbdd).1 t

/-! ## The RTC greedy processor provides the minimal service curve `βᵐ`

The min-plus convolution `(f ∗ g)(t) = ⨅_{a+b=t} (f a + g b)`, over the real
carrier of the RTC cumulative functions. -/

/-- The min-plus convolution of two real-valued functions of `ℝ≥0` time:
`(f ⊛ g)(t) = ⨅_{a + b = t} (f a + g b)`, the same shape as the generic
`minConv` but stated over `ℝ` (the RTC carrier, which has no `⊥`). -/
noncomputable def minConvReal (f g : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  ⨅ p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t}, (f p.1.1 + g p.1.2)

/-- The split set of `minConvReal` is nonempty (witnessed by `(t, 0)`). -/
instance minConvReal_splitNonempty (t : ℝ≥0) :
    Nonempty {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} :=
  ⟨⟨(t, 0), by simp⟩⟩

/-- Elim: every split bounds `minConvReal` from above,
`minConvReal f g t ≤ f a + g b` when `a + b = t` — provided the split-sum set is
bounded below (so the `⨅` is genuine). -/
theorem minConvReal_le_add {f g : ℝ≥0 → ℝ} {a b t : ℝ≥0} (h : a + b = t)
    (hbdd : BddBelow (Set.range fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
      f p.1.1 + g p.1.2)) :
    minConvReal f g t ≤ f a + g b :=
  ciInf_le_of_le hbdd (⟨(a, b), h⟩ : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t}) le_rfl

/-- For nonnegative `f, g`, the `minConvReal` split-sum set is bounded below
by `0` — the genuineness hypothesis is automatic for cumulative functions. -/
theorem bddBelow_minConvReal_of_nonneg {f g : ℝ≥0 → ℝ}
    (hf : ∀ u, 0 ≤ f u) (hg : ∀ u, 0 ≤ g u) (t : ℝ≥0) :
    BddBelow (Set.range fun p : {p : ℝ≥0 × ℝ≥0 // p.1 + p.2 = t} =>
      f p.1.1 + g p.1.2) :=
  ⟨0, by rintro _ ⟨p, rfl⟩; exact add_nonneg (hf _) (hg _)⟩

/-- **The RTC greedy processor provides the minimal service curve `βᵐ`.**
If `A` and `C` are Chasles, `b 0 = 0`, the residual sets are bounded above, and
the server `C` guarantees `βᵐ` (Definition 9.1, `βᵐ(t − s) ≤ C[s, t]`), then the
network-calculus output is bounded below by the min-plus convolution of the
arrival with `βᵐ`: `Â ∗ βᵐ ≤ D̂` — the service-curve guarantee `D̂(t) ≥ (Â ∗ βᵐ)(t)`.
Each split `u + (t − u) = t` of the convolution dominates the matching term of
the variable-capacity output [9.7] via capacity domination. -/
theorem minConvReal_le_departure_of_isRtcGreedy
    {A C D C' : ℝ≥0 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {betaM : ℝ≥0 → ℝ}
    (hA : IsChasles A) (hC : IsChasles C) (hb0 : b 0 = 0)
    (hg : IsRtcGreedy A C D C' b)
    (hbdd : ∀ t : ℝ≥0,
      BddAbove (Set.range fun u : {u : ℝ≥0 // u ≤ t} => C 0 u.1 - A 0 u.1))
    (hAnn : ∀ u, 0 ≤ A 0 u) (hβnn : ∀ u, 0 ≤ betaM u)
    (hguar : GuaranteesRtcMinService C betaM) (t : ℝ≥0) :
    minConvReal (fun u => A 0 u) betaM t ≤ D 0 t := by
  haveI : Nonempty {u : ℝ≥0 // u ≤ t} := ⟨⟨t, le_rfl⟩⟩
  have hbb := bddBelow_minConvReal_of_nonneg (f := fun u => A 0 u) (g := betaM)
    hAnn hβnn t
  rw [departure_eq_varCapacityOutput_of_isRtcGreedy hA hC hb0 hg hbdd t]
  refine le_ciInf fun u => ?_
  obtain ⟨u, (hu : u ≤ t)⟩ := u
  -- the split `u + (t − u) = t`
  have hsplit : u + (t - u) = t := add_tsub_cancel_of_le hu
  refine le_trans (minConvReal_le_add (f := fun u => A 0 u) (g := betaM)
      hsplit hbb) ?_
  -- capacity domination: βᵐ(t − u) ≤ C[u, t] = Ĉ(t) − Ĉ(u)
  have hcap : betaM (t - u) ≤ C 0 t - C 0 u :=
    (guaranteesRtcMinService_iff_univariate hC betaM).mp hguar u t hu
  -- so A 0 u + βᵐ(t − u) ≤ Ĉ(t) − Ĉ(u) + Â(u)
  have : A 0 u + betaM (t - u) ≤ C 0 t - C 0 u + A 0 u := by linarith
  simpa using this

/-- The variable-capacity output [9.7] is bounded below by `0` for nonnegative
arrival and non-decreasing capacity — the genuineness hypothesis for its
`⨅`. -/
theorem bddBelow_varCapacityOutput {A C : ℝ≥0 → ℝ≥0 → ℝ}
    (hCmono : Monotone (fun u => C 0 u)) (hAnn : ∀ u, 0 ≤ A 0 u) (t : ℝ≥0) :
    BddBelow (Set.range fun u : {u : ℝ≥0 // u ≤ t} =>
      C 0 t - C 0 u.1 + A 0 u.1) :=
  ⟨0, by
    rintro _ ⟨u, rfl⟩
    have : C 0 u.1 ≤ C 0 t := hCmono u.2
    have := hAnn u.1
    dsimp only; linarith⟩

/-- **Causality of the RTC greedy processor**: the network-calculus output never
exceeds the arrival, `D̂(t) ≤ Â(t)` — the `u = t` split of the variable-capacity
output [9.7]. Together with `minConvReal_le_departure_of_isRtcGreedy` this is the
full min-plus service pair `Â ∗ βᵐ ≤ D̂ ≤ Â`. -/
theorem departure_le_arrival_of_isRtcGreedy {A C D C' : ℝ≥0 → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ}
    (hA : IsChasles A) (hC : IsChasles C) (hb0 : b 0 = 0)
    (hg : IsRtcGreedy A C D C' b)
    (hbdd : ∀ t : ℝ≥0,
      BddAbove (Set.range fun u : {u : ℝ≥0 // u ≤ t} => C 0 u.1 - A 0 u.1))
    (hCmono : Monotone (fun u => C 0 u)) (hAnn : ∀ u, 0 ≤ A 0 u) (t : ℝ≥0) :
    D 0 t ≤ A 0 t := by
  haveI : Nonempty {u : ℝ≥0 // u ≤ t} := ⟨⟨t, le_rfl⟩⟩
  rw [departure_eq_varCapacityOutput_of_isRtcGreedy hA hC hb0 hg hbdd t]
  refine le_trans (ciInf_le_of_le (bddBelow_varCapacityOutput hCmono hAnn t)
    (⟨t, le_rfl⟩ : {u : ℝ≥0 // u ≤ t}) le_rfl) ?_
  dsimp only; linarith

end DeepWiki
