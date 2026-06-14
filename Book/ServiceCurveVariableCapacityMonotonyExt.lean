import Book.ServiceCurveMonotonyExt
import Book.ServiceCurveVariableCapacityFamilies

/-! # Refined variable-capacity monotony with extended arrivals (Thm 9.3 item 8)
The variable-capacity (`vcn`) inclusion `S_vcn^ext(β') ⊆ S_vcn^ext(β)` forces the
super-additive closures (of the non-decreasing closures) to be ordered, the book's
`(β↑)^⊛̄ ≤ (β'↑)^⊛̄`. Over finite `Curve` arrivals the forcing fails — the positive-time
capacity terms can undercut the origin term; the instantaneous infinite burst `δ₀`, a
genuine arrival only over the extended carrier, makes it hold. Feeding `δ₀` collapses the
variable-capacity output onto the capacity itself (`vcnOutputExt δ₀ C = C`), so the
super-additive closure `K := (β'↑)^⊛̄` is its own `δ₀`-output: the canonical tight pair
`(δ₀, K)` sits in `S_vcn^ext(β')`. The inclusion carries it into `S_vcn^ext(β)`, producing a
`β`-incrementing capacity equal to `K`, whence `(β↑)^⊛̄ ≤ K = (β'↑)^⊛̄`. This mirrors the
min-plus item-3 forcing `ndClosure_le_of_minimalServiceRelExt_le`, with the super-additive
closure in place of the non-decreasing one and the
`δ₀`-output-of-a-capacity-is-the-capacity collapse in place of `δ₀ ∗ β = β`. The converse is
the easy direction (a capacity carrying `β'`-increments carries `(β'↑)^⊛̄`-increments, hence
`β`-increments once the closures are ordered), so the inclusion is *equivalent* to the
closure ordering. -/

namespace DeepWiki

open Set Topology Filter
open scoped Classical NNReal ENNReal

/-- An extended cumulative process: non-decreasing, `f 0 = 0`, valued in `ℝ≥0∞` (so the
infinite burst `δ₀` is admissible). The `vcn` machinery uses only these two properties. -/
structure ProcessENN where
  /-- The underlying function `ℝ≥0 → ℝ≥0∞`. -/
  toFun : ℝ≥0 → ℝ≥0∞
  /-- Non-decreasing. -/
  mono : Monotone toFun
  /-- Null at the origin: `f 0 = 0`. -/
  zero : toFun 0 = 0

/-- A `ProcessENN` is callable as its underlying function. -/
instance : FunLike ProcessENN ℝ≥0 ℝ≥0∞ where
  coe := ProcessENN.toFun
  coe_injective' f g h := by cases f; cases g; congr

/-- Two extended processes are equal when equal as functions. -/
@[ext] theorem ProcessENN.ext {A B : ProcessENN} (h : ∀ t, A t = B t) : A = B :=
  DFunLike.ext A B h

/-- Pointwise order on extended processes. -/
instance : LE ProcessENN where
  le D A := ∀ t, D t ≤ A t

/-- Every `CurveENN` is an extended cumulative process (forgetting continuity). -/
noncomputable def ProcessENN.ofCurveENN (A : CurveENN) : ProcessENN where
  toFun := A
  mono := A.mono
  zero := A.zero

/-- `ProcessENN.ofCurveENN A t = A t`. -/
@[simp] theorem ProcessENN.ofCurveENN_apply (A : CurveENN) (t : ℝ≥0) :
    ProcessENN.ofCurveENN A t = A t := rfl

/-- The instantaneous infinite burst `δ₀` as an extended cumulative process. -/
noncomputable def delay0Process : ProcessENN := ProcessENN.ofCurveENN delay0ENN

/-- `delay0Process 0 = 0`. -/
@[simp] theorem delay0Process_zero_eq : delay0Process 0 = 0 := delay0ENN_zero_eq

/-- `delay0Process t = ⊤` for positive `t`. -/
theorem delay0Process_apply_pos {t : ℝ≥0} (ht : t ≠ 0) : delay0Process t = ⊤ :=
  delay0ENN_apply_pos ht

/-- `delay0Process` and `delay0ENN` agree as functions. -/
@[simp] theorem delay0Process_coe : (⇑delay0Process : ℝ≥0 → ℝ≥0∞) = ⇑delay0ENN := rfl

/-- Extended variable-capacity output, `ℝ≥0∞`-valued:
`vcnOutputExt A C t = ⨅_{s ≤ t} (A s + (C t − C s))`. The `variableCapacityOutput` of
`ServiceCurveVariableCapacity`, lifted to the complete carrier so `δ₀` is admissible. -/
noncomputable def vcnOutputExt (A C : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) : ℝ≥0∞ :=
  ⨅ s : {s // s ≤ t}, (A s.1 + (C t - C s.1))

/-- Elim: every split bounds the extended output,
`vcnOutputExt A C t ≤ A s + (C t − C s)` for `s ≤ t`. -/
theorem vcnOutputExt_le_add {A C : ℝ≥0 → ℝ≥0∞} {s t : ℝ≥0} (h : s ≤ t) :
    vcnOutputExt A C t ≤ A s + (C t - C s) :=
  iInf_le _ (⟨s, h⟩ : {s // s ≤ t})

/-- **The `δ₀`-collapse**: `vcnOutputExt (⇑delay0ENN) C t = C t` for any null-at-origin
capacity `C`. The origin split gives `C t`; every positive-time split gives `⊤`, so the
infimum is the capacity itself. -/
theorem vcnOutputExt_delay0ENN {C : ℝ≥0 → ℝ≥0∞} (h0 : C 0 = 0) (t : ℝ≥0) :
    vcnOutputExt (⇑delay0ENN) C t = C t := by
  refine le_antisymm ?_ ?_
  · have h := vcnOutputExt_le_add (A := ⇑delay0ENN) (C := C) (s := 0) (t := t) zero_le'
    rwa [delay0ENN_zero_eq, zero_add, h0, tsub_zero] at h
  · refine le_iInf fun s : {s // s ≤ t} => ?_
    rcases eq_or_ne s.1 0 with hs | hs
    · rw [hs, delay0ENN_zero_eq, zero_add, h0, tsub_zero]
    · rw [delay0ENN_apply_pos hs, top_add]
      exact le_top

/-- The extended variable-capacity relation, over `ProcessENN` arrivals/departures: some
monotone null-at-origin extended capacity `C` with `β`-dominating increments drives the
output, `D = vcnOutputExt A C`. Mirrors `minimalServiceRelExt`; the capacity is an extended
cumulative process. -/
def variableCapacityRelExt (beta : ℝ≥0 → ℝ≥0∞) : ProcessENN → ProcessENN → Prop :=
  fun A D => ∃ C : ℝ≥0 → ℝ≥0∞, Monotone C ∧ C 0 = 0 ∧
    (∀ t, (D t : ℝ≥0∞) = vcnOutputExt (⇑A) C t) ∧
    (∀ s t, s ≤ t → beta (t - s) ≤ C t - C s)

/-- `variableCapacityRelExt beta A D` unfolds to the extended capacity witness. -/
theorem mem_variableCapacityRelExt_iff {beta : ℝ≥0 → ℝ≥0∞} {A D : ProcessENN} :
    variableCapacityRelExt beta A D ↔ ∃ C : ℝ≥0 → ℝ≥0∞, Monotone C ∧ C 0 = 0 ∧
      (∀ t, (D t : ℝ≥0∞) = vcnOutputExt (⇑A) C t) ∧
      (∀ s t, s ≤ t → beta (t - s) ≤ C t - C s) :=
  Iff.rfl

/-- Each extended super-additive iterate stays below an affine bound:
`maxConvPow g n t ≤ ρ · t` when `g s ≤ ρ · s`. -/
theorem maxConvPow_le_of_affine_boundNN {g : ℝ≥0 → ℝ≥0∞} {ρ : ℝ≥0∞}
    (hr : ∀ s : ℝ≥0, g s ≤ ρ * s) (n : ℕ) (t : ℝ≥0) :
    maxConvPow g n t ≤ ρ * t := by
  induction n generalizing t with
  | zero => exact hr t
  | succ n ih =>
    show maxConv (maxConvPow g n) (maxConvPow g n) t ≤ ρ * t
    refine maxConv_le fun a b hab => ?_
    calc maxConvPow g n a + maxConvPow g n b
        ≤ ρ * (a : ℝ≥0∞) + ρ * (b : ℝ≥0∞) := add_le_add (ih a) (ih b)
      _ = ρ * ((a : ℝ≥0∞) + b) := (mul_add ρ _ _).symm
      _ = ρ * t := by rw [← hab]; push_cast; ring_nf

/-- The extended super-additive closure stays below an affine bound,
`superadditiveClosureMaxNN g t ≤ ρ · t`. -/
theorem superadditiveClosureMaxNN_le_of_affine_bound {g : ℝ≥0 → ℝ≥0∞} {ρ : ℝ≥0∞}
    (hr : ∀ s : ℝ≥0, g s ≤ ρ * s) (t : ℝ≥0) :
    superadditiveClosureMaxNN g t ≤ ρ * t :=
  iSup_le fun n => maxConvPow_le_of_affine_boundNN hr n t

/-- The extended super-additive iterates vanish at the origin when `g 0 = 0`. -/
theorem maxConvPow_zero_eq {g : ℝ≥0 → ℝ≥0∞} (h0 : g 0 = 0) (n : ℕ) :
    maxConvPow g n 0 = 0 := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    show maxConv (maxConvPow g n) (maxConvPow g n) 0 = 0
    refine le_antisymm (maxConv_le fun u s hus => ?_) zero_le'
    obtain ⟨rfl, rfl⟩ := add_eq_zero.mp hus
    rw [ih, add_zero]

/-- The extended super-additive closure vanishes at the origin when `g 0 = 0`. -/
theorem superadditiveClosureMaxNN_zero_eq {g : ℝ≥0 → ℝ≥0∞} (h0 : g 0 = 0) :
    superadditiveClosureMaxNN g 0 = 0 := by
  refine le_antisymm (iSup_le fun n => ?_) zero_le'
  rw [maxConvPow_zero_eq h0 n]

/-- `f t ≤ ndClosure f t` on the `ℝ≥0∞` carrier (boundedness is automatic). -/
theorem le_ndClosureNN (f : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) : f t ≤ ndClosure f t :=
  le_ndClosure f (fun _ => OrderTop.bddAbove _) t

/-- `ndClosure f` is monotone on the `ℝ≥0∞` carrier. -/
theorem monotone_ndClosureNN (f : ℝ≥0 → ℝ≥0∞) : Monotone (ndClosure f) :=
  fun _ _ hxy => ndClosure_mono f (fun _ => OrderTop.bddAbove _) hxy

/-- The non-decreasing closure of a rate-`ρ` bounded curve's `ℝ≥0∞`-coe is below `ρ · t`. -/
theorem ndClosure_coe_le_affine {β' : Curve} {ρ : ℝ≥0} (hr : ∀ s : ℝ≥0, β' s ≤ ρ * s)
    (t : ℝ≥0) : ndClosure (fun u => (β' u : ℝ≥0∞)) t ≤ (ρ : ℝ≥0∞) * t := by
  refine ndClosure_le (f := fun u => (β' u : ℝ≥0∞)) (g := fun u => (ρ : ℝ≥0∞) * u) ?_ ?_ t
  · intro a b hab; exact mul_le_mul' le_rfl (by exact_mod_cast hab)
  · intro u
    calc (β' u : ℝ≥0∞) ≤ ((ρ * u : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hr u
      _ = (ρ : ℝ≥0∞) * u := by push_cast; rfl

/-- The non-decreasing closure of a rate-bounded curve's `ℝ≥0∞`-coe vanishes at the origin. -/
theorem ndClosure_coe_zero_eq {β' : Curve} {ρ : ℝ≥0} (hr : ∀ s : ℝ≥0, β' s ≤ ρ * s) :
    ndClosure (fun u => (β' u : ℝ≥0∞)) 0 = 0 := by
  refine le_antisymm ?_ zero_le'
  have h := ndClosure_coe_le_affine hr 0
  rwa [show (ρ : ℝ≥0∞) * ((0 : ℝ≥0) : ℝ≥0∞) = 0 by push_cast; ring] at h

/-- The super-additive closure `(β'↑)^⊛̄`, monotone and null at the origin, as an extended
cumulative process — the canonical `vcn` capacity for `β'`. -/
noncomputable def superadditiveNdClosureProcess {β' : Curve} {ρ : ℝ≥0}
    (hr : ∀ s : ℝ≥0, β' s ≤ ρ * s) : ProcessENN where
  toFun := superadditiveClosureMaxNN (ndClosure (fun u => (β' u : ℝ≥0∞)))
  mono := monotone_superadditiveClosureMaxNN (monotone_ndClosureNN _)
  zero := superadditiveClosureMaxNN_zero_eq (ndClosure_coe_zero_eq hr)

/-- `superadditiveNdClosureProcess hr t = (β'↑)^⊛̄ t`. -/
@[simp] theorem superadditiveNdClosureProcess_apply {β' : Curve} {ρ : ℝ≥0}
    (hr : ∀ s : ℝ≥0, β' s ≤ ρ * s) (t : ℝ≥0) :
    (superadditiveNdClosureProcess hr) t
      = superadditiveClosureMaxNN (ndClosure (fun u => (β' u : ℝ≥0∞))) t := rfl

/-- **The closure `(δ₀, (β'↑)^⊛̄)` is variable-capacity served by `β'`** (extended arrivals):
the canonical tight pair with the infinite-burst input. `K := (β'↑)^⊛̄` is monotone, null at
the origin, has `β'`-dominating increments (it is super-additive and dominates `β'`), and is
its own `δ₀`-output. The rate bound on `β'` keeps `K` finite. -/
theorem variableCapacityRelExt_delay0Process_closure {β' : Curve} {ρ : ℝ≥0}
    (hr : ∀ s : ℝ≥0, β' s ≤ ρ * s) :
    variableCapacityRelExt (fun u => (β' u : ℝ≥0∞)) delay0Process
      (superadditiveNdClosureProcess hr) := by
  set g : ℝ≥0 → ℝ≥0∞ := fun u => (β' u : ℝ≥0∞) with hg
  set K : ℝ≥0 → ℝ≥0∞ := superadditiveClosureMaxNN (ndClosure g) with hK
  have hmonoK : Monotone K := monotone_superadditiveClosureMaxNN (monotone_ndClosureNN g)
  have h0K : K 0 = 0 := superadditiveClosureMaxNN_zero_eq (ndClosure_coe_zero_eq hr)
  have hsupK : IsSuperadditive K := isSuperadditive_superadditiveClosureMaxNN _
  have hfin : ∀ s : ℝ≥0, K s ≠ ⊤ := by
    intro s
    have hb : K s ≤ (ρ : ℝ≥0∞) * s :=
      superadditiveClosureMaxNN_le_of_affine_bound (fun u => ndClosure_coe_le_affine hr u) s
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) hb
  refine ⟨K, hmonoK, h0K, fun t => ?_, fun s t hst => ?_⟩
  · rw [superadditiveNdClosureProcess_apply, ← hK, delay0Process_coe]
    exact (vcnOutputExt_delay0ENN h0K t).symm
  · have hβle : g (t - s) ≤ K (t - s) :=
      le_trans (le_ndClosureNN g (t - s))
        (le_superadditiveClosureMaxNN (ndClosure g) (t - s))
    have hincr : K (t - s) ≤ K t - K s := by
      have hsa : K (t - s) + K s ≤ K t := by
        have := hsupK (t - s) s
        rwa [tsub_add_cancel_of_le hst] at this
      exact ENNReal.le_sub_of_add_le_left (hfin s) (by rwa [add_comm] at hsa)
    exact le_trans hβle hincr

/-- Capacity increments dominating `β` dominate the non-decreasing closure of `β`, through
monotonicity of the capacity (the `ℝ≥0∞` analog of `ndClosure_le_capacity`). -/
theorem ndClosure_le_capacityNN {β : Curve} {C : ℝ≥0 → ℝ≥0∞} (hCmono : Monotone C)
    (hcap : ∀ s t, s ≤ t → (β (t - s) : ℝ≥0∞) ≤ C t - C s) :
    ∀ s t, s ≤ t → ndClosure (fun u => (β u : ℝ≥0∞)) (t - s) ≤ C t - C s := by
  intro s t hst
  have hgmono : Monotone (fun w => C (s + w) - C s) :=
    fun a b hab => tsub_le_tsub_right (hCmono (by gcongr)) (C s)
  have hdom : ∀ w, (β w : ℝ≥0∞) ≤ C (s + w) - C s := fun w => by
    have h := hcap s (s + w) le_self_add
    rwa [add_tsub_cancel_left] at h
  have h := ndClosure_le (f := fun u => (β u : ℝ≥0∞)) (g := fun w => C (s + w) - C s)
    hgmono hdom (t - s)
  rwa [add_tsub_cancel_of_le hst] at h

/-- The capacity increments dominate every super-additive iterate of `β↑`: split the
increment window at the iterate's split point (the `ℝ≥0∞` analog of
`maxConvProjPow_le_capacity`). -/
theorem maxConvPow_ndClosure_le_capacityNN {β : Curve} {C : ℝ≥0 → ℝ≥0∞} (hCmono : Monotone C)
    (hcap : ∀ s t, s ≤ t → (β (t - s) : ℝ≥0∞) ≤ C t - C s) (n : ℕ) :
    ∀ s t, s ≤ t → maxConvPow (ndClosure (fun u => (β u : ℝ≥0∞))) n (t - s) ≤ C t - C s := by
  induction n with
  | zero => exact ndClosure_le_capacityNN hCmono hcap
  | succ n ih =>
    intro s t hst
    show maxConv (maxConvPow (ndClosure (fun u => (β u : ℝ≥0∞))) n)
        (maxConvPow (ndClosure (fun u => (β u : ℝ≥0∞))) n) (t - s) ≤ C t - C s
    refine maxConv_le fun a b hab => ?_
    have hT : s + (a + b) = t := by rw [hab, add_tsub_cancel_of_le hst]
    have hmid : s + a ≤ t := by
      calc s + a ≤ s + (a + b) := add_le_add le_rfl le_self_add
        _ = t := hT
    have h1 := ih s (s + a) le_self_add
    have h2 := ih (s + a) t hmid
    rw [add_tsub_cancel_left] at h1
    rw [show t - (s + a) = b from by rw [← hT, ← add_assoc, add_tsub_cancel_left]] at h2
    calc maxConvPow (ndClosure (fun u => (β u : ℝ≥0∞))) n a
            + maxConvPow (ndClosure (fun u => (β u : ℝ≥0∞))) n b
        ≤ (C (s + a) - C s) + (C t - C (s + a)) := add_le_add h1 h2
      _ = C t - C s := by
          rw [add_comm]
          exact tsub_add_tsub_cancel (hCmono hmid) (hCmono le_self_add)

/-- The super-additive closure of `β↑` is dominated by capacity increments:
`(β↑)^⊛̄(t−s) ≤ C(t) − C(s)`. -/
theorem superadditiveClosureMaxNN_ndClosure_le_capacityNN {β : Curve} {C : ℝ≥0 → ℝ≥0∞}
    (hCmono : Monotone C) (hcap : ∀ s t, s ≤ t → (β (t - s) : ℝ≥0∞) ≤ C t - C s)
    {s t : ℝ≥0} (hst : s ≤ t) :
    superadditiveClosureMaxNN (ndClosure (fun u => (β u : ℝ≥0∞))) (t - s) ≤ C t - C s :=
  iSup_le fun n => maxConvPow_ndClosure_le_capacityNN hCmono hcap n s t hst

/-- **Thm 9.3 item 8 (refined variable-capacity monotony, extended arrivals — the forcing)**:
if every extended pair variable-capacity served by `β'` is also served by `β`, the
super-additive closures of the non-decreasing closures are ordered, the book's
`(β↑)^⊛̄ ≤ (β'↑)^⊛̄`. Probing the `β'`-server with the infinite burst `δ₀` recovers
`K := (β'↑)^⊛̄` as the departure (its own `δ₀`-output); the inclusion forces a
`β`-incrementing capacity equal to `K`, so `β(t−s) ≤ K(t) − K(s)`, whence `(β↑)^⊛̄ ≤ K`. A
rate bound on `β'` keeps `K` finite. Over finite `Curve` arrivals the forcing fails; `δ₀`
is what makes it hold. -/
theorem superadditiveClosureMaxNN_ndClosure_le_of_variableCapacityRelExt_le
    {β β' : Curve} {ρ : ℝ≥0} (hr : ∀ s : ℝ≥0, β' s ≤ ρ * s)
    (h : variableCapacityRelExt (fun u => (β' u : ℝ≥0∞))
      ≤ variableCapacityRelExt (fun u => (β u : ℝ≥0∞))) :
    superadditiveClosureMaxNN (ndClosure (fun u => (β u : ℝ≥0∞)))
      ≤ superadditiveClosureMaxNN (ndClosure (fun u => (β' u : ℝ≥0∞))) := by
  have hmem : variableCapacityRelExt (fun u => (β u : ℝ≥0∞)) delay0Process
      (superadditiveNdClosureProcess hr) :=
    h delay0Process (superadditiveNdClosureProcess hr)
      (variableCapacityRelExt_delay0Process_closure hr)
  obtain ⟨C, hCmono, hC0, hDout, hcap⟩ := hmem
  have hKeqC : ∀ t, superadditiveClosureMaxNN (ndClosure (fun u => (β' u : ℝ≥0∞))) t = C t := by
    intro t
    have hd := hDout t
    rw [superadditiveNdClosureProcess_apply] at hd
    rw [hd, delay0Process_coe, vcnOutputExt_delay0ENN hC0 t]
  intro t
  have hb := superadditiveClosureMaxNN_ndClosure_le_capacityNN hCmono hcap (s := 0) (t := t)
    zero_le'
  rw [tsub_zero, hC0, tsub_zero] at hb
  rw [hKeqC t]
  exact hb

/-- **Thm 9.3 item 8 (the converse — closure ordering forces the inclusion)**: if the
super-additive closures are ordered, `(β↑)^⊛̄ ≤ (β'↑)^⊛̄`, then every extended pair
variable-capacity served by `β'` is served by `β` — `S_vcn^ext(β') ⊆ S_vcn^ext(β)`. The same
witness capacity `C` works: its `β'`-increments dominate `(β'↑)^⊛̄`
(`superadditiveClosureMaxNN_ndClosure_le_capacityNN`), hence `(β↑)^⊛̄`, hence `β`. No rate
bound is needed for this direction. -/
theorem variableCapacityRelExt_le_of_superadditiveClosureMaxNN_ndClosure_le {β β' : Curve}
    (h : superadditiveClosureMaxNN (ndClosure (fun u => (β u : ℝ≥0∞)))
      ≤ superadditiveClosureMaxNN (ndClosure (fun u => (β' u : ℝ≥0∞)))) :
    variableCapacityRelExt (fun u => (β' u : ℝ≥0∞))
      ≤ variableCapacityRelExt (fun u => (β u : ℝ≥0∞)) := by
  intro A D hAD
  obtain ⟨C, hCmono, hC0, hDout, hcap⟩ := hAD
  refine ⟨C, hCmono, hC0, hDout, fun s t hst => ?_⟩
  have hβclo : (β (t - s) : ℝ≥0∞)
      ≤ superadditiveClosureMaxNN (ndClosure (fun u => (β u : ℝ≥0∞))) (t - s) :=
    le_trans (le_ndClosureNN (fun u => (β u : ℝ≥0∞)) (t - s))
      (le_superadditiveClosureMaxNN (ndClosure (fun u => (β u : ℝ≥0∞))) (t - s))
  exact le_trans (le_trans hβclo (h (t - s)))
    (superadditiveClosureMaxNN_ndClosure_le_capacityNN hCmono hcap hst)

/-- **Thm 9.3 item 8 (the equivalence)**: for a rate-bounded `β'`, the extended
variable-capacity inclusion `S_vcn^ext(β') ⊆ S_vcn^ext(β)` holds *iff* the super-additive
closures of the non-decreasing closures are ordered, `(β↑)^⊛̄ ≤ (β'↑)^⊛̄`. The forcing
(`⟹`) rides the infinite burst `δ₀`; the converse (`⟸`) is the capacity-domination
argument. -/
theorem variableCapacityRelExt_le_iff_superadditiveClosureMaxNN_ndClosure_le {β β' : Curve}
    {ρ : ℝ≥0} (hr : ∀ s : ℝ≥0, β' s ≤ ρ * s) :
    variableCapacityRelExt (fun u => (β' u : ℝ≥0∞))
        ≤ variableCapacityRelExt (fun u => (β u : ℝ≥0∞))
      ↔ superadditiveClosureMaxNN (ndClosure (fun u => (β u : ℝ≥0∞)))
        ≤ superadditiveClosureMaxNN (ndClosure (fun u => (β' u : ℝ≥0∞))) :=
  ⟨fun h => superadditiveClosureMaxNN_ndClosure_le_of_variableCapacityRelExt_le hr h,
   variableCapacityRelExt_le_of_superadditiveClosureMaxNN_ndClosure_le⟩

/-- Faithfulness restatement of the forcing against the book's wording
`S_vcn^ext(β') ⊆ S_vcn^ext(β) ⟹ (β↑)^⊛̄ ≤ (β'↑)^⊛̄`. -/
example {β β' : Curve} {ρ : ℝ≥0} (hr : ∀ s : ℝ≥0, β' s ≤ ρ * s)
    (h : variableCapacityRelExt (fun u => (β' u : ℝ≥0∞))
      ≤ variableCapacityRelExt (fun u => (β u : ℝ≥0∞))) :
    superadditiveClosureMaxNN (ndClosure (fun u => (β u : ℝ≥0∞)))
      ≤ superadditiveClosureMaxNN (ndClosure (fun u => (β' u : ℝ≥0∞))) :=
  superadditiveClosureMaxNN_ndClosure_le_of_variableCapacityRelExt_le hr h

end DeepWiki
