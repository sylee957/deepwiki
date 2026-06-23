import DeepWiki.NetworkCalculus.WorstCaseBoundX3CReductionNetwork
import Mathlib.Analysis.Convex.Jensen

/-! # Fractional-vs-integral optimality for the X3C worst-case backlog (DNC Theorem 10.2)
The bridge and network files optimize the saturation objective over the *integral*
extremal vertices of the Figure-10.7 rate polytope (the `IsAssignment` routings,
`r ∈ {0,1}`). This file closes the convexity layer above that: the objective is a
**convex** function of the fractional routing, so its maximum over the whole polytope
is attained at a vertex — *no fractional fluid routing beats the integral vertices.*

A fractional routing is `r : α → ι → ℝ`, the served weight of element `e` at subset
`i`; the feasibility polytope is `{r ≥ 0 : Σ_{i ∋ e} r e i = 1}`, a product of
simplices whose vertices are exactly the integral routings. The objective
`fracObjective r = Σᵢ [Σ_{e ∈ cᵢ} r e i − 2]⁺` is convex (each summand is an affine
functional capped below by a constant, `(affine) ⊔ const`), so by Jensen the value at
a convex combination of integral routings is at most the maximum integral value
(`saturatedCount`). The integral routing read off an assignment realizes
`fracObjective = saturatedCount`, so the fractional optimum equals the integral one.

What is **proved**: `convexOn_fracObjective` (convexity of the objective on `univ`);
`fracObjective_integralRouting` (the integral routing's real objective is its
`saturatedCount`); the Jensen consequence `fracObjective_combo_le_q` (any fractional
routing presented as a convex combination of integral routings is dominated by `q`);
and the **whole-polytope closure** `fracObjective_le_q_of_feasible` — *every* feasible
fractional routing (`IsFeasible`) has objective `≤ q`, via `convexHull_pi`
(the polytope is the convex hull of the integral routings) and
`ConvexOn.le_sup_of_mem_convexHull` (a convex function on a hull is maximized at a
vertex). Together these say the worst case over the whole polytope is attained at the
integral vertices, with no "already a convex combination" caveat. -/

namespace DeepWiki

open Finset

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [DecidableEq ι]

/-! ## The fractional routing objective
A fractional routing `r : α → ι → ℝ` assigns to element `e` a served weight `r e i`
at each subset `i`. The load of subset `i` is `Σ_{e ∈ cᵢ} r e i` (the served weight
of `i`'s own elements); the objective contribution of `i` is `[load − 2]⁺`. -/

/-- The **fractional load** of subset `i` under a real routing `r`: `Σ_{e ∈ cᵢ} r e i`,
the served weight of `i`'s own elements (the real-valued analogue of `load`). -/
def X3CInstance.fracLoad (I : X3CInstance ι α) (r : α → ι → ℝ) (i : ι) : ℝ :=
  ∑ e ∈ I.members i, r e i

/-- The **fractional objective** `Σᵢ [Σ_{e ∈ cᵢ} r e i − 2]⁺` of a real routing `r`:
the convex objective the book maximizes over the feasibility polytope (`posPart` is
spelled `· ⊔ 0`). -/
def X3CInstance.fracObjective (I : X3CInstance ι α) (r : α → ι → ℝ) : ℝ :=
  ∑ i, ((I.fracLoad r i - 2) ⊔ 0)

/-- The fractional load `r ↦ Σ_{e ∈ cᵢ} r e i` is a **linear functional** of the
routing `r : α → ι → ℝ`. -/
def X3CInstance.fracLoadHom (I : X3CInstance ι α) (i : ι) : (α → ι → ℝ) →ₗ[ℝ] ℝ where
  toFun r := I.fracLoad r i
  map_add' r r' := by
    simp only [X3CInstance.fracLoad, Pi.add_apply, ← Finset.sum_add_distrib]
  map_smul' c r := by
    simp only [X3CInstance.fracLoad, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      RingHom.id_apply, smul_eq_mul]

omit [DecidableEq ι] in
@[simp] theorem X3CInstance.fracLoadHom_apply (I : X3CInstance ι α) (r : α → ι → ℝ)
    (i : ι) : I.fracLoadHom i r = I.fracLoad r i := rfl

/-! ## Convexity of the objective
Each summand `[load i − 2]⁺ = (fracLoadHom i − 2) ⊔ 0` is convex: an affine functional
of `r` capped below by a constant, the supremum of two convex functions. The objective
is their finite sum, hence convex on `univ`. -/

omit [DecidableEq ι] in
/-- **The `i`-th summand is convex**: `r ↦ [Σ_{e ∈ cᵢ} r e i − 2]⁺` is the supremum of
the affine functional `fracLoadHom i − 2` and the constant `0`, both convex. -/
theorem X3CInstance.convexOn_fracTerm (I : X3CInstance ι α) (i : ι) :
    ConvexOn ℝ Set.univ (fun r : α → ι → ℝ => (I.fracLoad r i - 2) ⊔ 0) := by
  have haff : ConvexOn ℝ Set.univ (fun r : α → ι → ℝ => I.fracLoad r i - 2) := by
    have hlin : ConvexOn ℝ Set.univ (fun r : α → ι → ℝ => I.fracLoadHom i r) :=
      (I.fracLoadHom i).convexOn convex_univ
    have hconst2 : ConvexOn ℝ Set.univ (fun _ : α → ι → ℝ => (-2 : ℝ)) :=
      convexOn_const (-2) convex_univ
    have hadd := hlin.add hconst2
    have heq : (fun r : α → ι → ℝ => I.fracLoadHom i r + (-2 : ℝ))
        = fun r : α → ι → ℝ => I.fracLoad r i - 2 := by
      funext r; simp [X3CInstance.fracLoadHom_apply]; ring
    rw [show ((fun r : α → ι → ℝ => I.fracLoadHom i r) + fun _ => (-2 : ℝ))
        = fun r : α → ι → ℝ => I.fracLoadHom i r + (-2 : ℝ) from rfl, heq] at hadd
    exact hadd
  have hconst : ConvexOn ℝ Set.univ (fun _ : α → ι → ℝ => (0 : ℝ)) :=
    convexOn_const 0 convex_univ
  exact haff.sup hconst

/-- A finite sum of functions convex on `s` is convex on `s`: fold `ConvexOn.add`
over the index finset, starting from the convex constant `0`. -/
theorem convexOn_finsetSum {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {s : Set E} (hs : Convex ℝ s) {κ : Type*} (t : Finset κ) {g : κ → E → ℝ}
    (hg : ∀ k ∈ t, ConvexOn ℝ s (g k)) :
    ConvexOn ℝ s (fun x => ∑ k ∈ t, g k x) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using convexOn_const (0 : ℝ) hs
  | insert k t hkt ih =>
    have hk : ConvexOn ℝ s (g k) := hg k (Finset.mem_insert_self k t)
    have ih' : ConvexOn ℝ s (fun x => ∑ j ∈ t, g j x) :=
      ih fun j hj => hg j (Finset.mem_insert_of_mem hj)
    have hsum : (fun x => ∑ j ∈ insert k t, g j x)
        = (g k) + (fun x => ∑ j ∈ t, g j x) := by
      funext x; simp [Finset.sum_insert hkt]
    rw [hsum]
    exact hk.add ih'

omit [DecidableEq ι] in
/-- **The fractional objective is convex** on the full routing space (so on every
sub-polytope): a finite sum of the convex summands `[load i − 2]⁺`. -/
theorem X3CInstance.convexOn_fracObjective (I : X3CInstance ι α) :
    ConvexOn ℝ Set.univ I.fracObjective := by
  have : I.fracObjective = fun r : α → ι → ℝ => ∑ i, (I.fracLoad r i - 2) ⊔ 0 := rfl
  rw [this]
  exact convexOn_finsetSum convex_univ Finset.univ (fun i _ => I.convexOn_fracTerm i)

/-! ## The integral routing and its real objective
The integral extremal vertex realized by an assignment is `routeRate` cast to `ℝ`. Its
fractional load is the integral `load`, its objective is `saturatedCount` — the bridge
between the real objective and the combinatorial count. -/

/-- The **integral routing** `α → ι → ℝ` realized by `assign`: the extremal vertex
`routeRate` cast to reals (`1` iff `e` is routed to a containing `i`). -/
def X3CInstance.integralRouting (I : X3CInstance ι α) (assign : α → ι) : α → ι → ℝ :=
  fun e i => (I.routeRate assign i e : ℝ)

/-- The fractional load of the integral routing is the integral `load` (cast). -/
theorem X3CInstance.fracLoad_integralRouting (I : X3CInstance ι α) (assign : α → ι)
    (i : ι) : I.fracLoad (I.integralRouting assign) i = (I.load assign i : ℝ) := by
  unfold X3CInstance.fracLoad X3CInstance.integralRouting X3CInstance.load
  push_cast
  rfl

/-- **The integral routing's real objective is the saturated count**: at the integral
vertex `[load i − 2]⁺` is `1` for a saturated subset and `0` otherwise (`load ≤ 3`),
so the real objective `Σᵢ [load i − 2]⁺` equals `saturatedCount`. -/
theorem X3CInstance.fracObjective_integralRouting (I : X3CInstance ι α)
    (assign : α → ι) :
    I.fracObjective (I.integralRouting assign) = (I.saturatedCount assign : ℝ) := by
  unfold X3CInstance.fracObjective
  rw [← I.middleBacklogAt_eq assign]
  unfold X3CInstance.middleBacklogAt
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [I.fracLoad_integralRouting assign i]
  -- `[load − 2]⁺ = load - 2` since `2 ≤ load` for saturated, else both `0`
  have hle := I.load_le_three assign i
  rcases Nat.lt_or_ge (I.load assign i) 2 with hlt | hge
  · -- load < 2 : real `[load − 2]⁺ = 0` and ℕ `load - 2 = 0`
    have h2 : (I.load assign i : ℝ) - 2 ≤ 0 := by
      have : (I.load assign i : ℝ) ≤ 2 := by exact_mod_cast hlt.le
      linarith
    rw [sup_eq_right.mpr h2]
    have : I.load assign i - 2 = 0 := by omega
    rw [this]; norm_num
  · -- 2 ≤ load : real `[load − 2]⁺ = load − 2` and casts agree with ℕ truncated sub
    have h2 : (0 : ℝ) ≤ (I.load assign i : ℝ) - 2 := by
      have : (2 : ℝ) ≤ (I.load assign i : ℝ) := by exact_mod_cast hge
      linarith
    rw [sup_eq_left.mpr h2]
    have hcast : ((I.load assign i - 2 : ℕ) : ℝ) = (I.load assign i : ℝ) - 2 := by
      have : (2 : ℕ) ≤ I.load assign i := hge
      push_cast [Nat.cast_sub this]
      ring
    rw [hcast]

/-! ## The Jensen consequence: no fractional routing beats the integral vertices
A fractional routing that is a convex combination of integral routings has objective
at most the maximum integral `saturatedCount`: convexity (Jensen) bounds the objective
at the center of mass by the objective at *some* constituent vertex, which is that
vertex's `saturatedCount`, in turn `≤ q` and `≤` the integral optimum. -/

/-- **No fractional routing (built as a convex combination of integral routings) beats
the integral vertices**: if `r = Σ_a w a • integralRouting (assign a)` over a finite
family of *valid* assignments with weights `w ≥ 0` summing to `1`, then
`fracObjective r ≤ q`. By Jensen the objective at the center of mass is `≤` the
objective at one constituent integral vertex, whose value is its `saturatedCount ≤ q`.
This is the convex-maximization-attains-a-vertex step: the fractional optimum does not
exceed the integral optimum bound `q`. -/
theorem X3CInstance.fracObjective_combo_le_q (I : X3CInstance ι α)
    {κ : Type*} (t : Finset κ) (w : κ → ℝ) (assign : κ → α → ι)
    (_hassign : ∀ a ∈ t, I.IsAssignment (assign a))
    (hw₀ : ∀ a ∈ t, 0 ≤ w a) (hw₁ : ∑ a ∈ t, w a = 1) :
    I.fracObjective (∑ a ∈ t, w a • I.integralRouting (assign a)) ≤ (I.q : ℝ) := by
  -- Jensen: objective at the center of mass ≤ weighted sum of vertex objectives
  have hjensen :
      I.fracObjective (∑ a ∈ t, w a • I.integralRouting (assign a)) ≤
        ∑ a ∈ t, w a • I.fracObjective (I.integralRouting (assign a)) :=
    I.convexOn_fracObjective.map_sum_le hw₀ hw₁ (fun a _ => Set.mem_univ _)
  refine hjensen.trans ?_
  -- each vertex objective is its `saturatedCount ≤ q`
  have hterm : ∀ a ∈ t, w a • I.fracObjective (I.integralRouting (assign a)) ≤ w a • (I.q : ℝ) := by
    intro a ha
    rw [I.fracObjective_integralRouting (assign a)]
    refine smul_le_smul_of_nonneg_left ?_ (hw₀ a ha)
    exact_mod_cast I.saturatedCount_le_q (assign a)
  calc ∑ a ∈ t, w a • I.fracObjective (I.integralRouting (assign a))
      ≤ ∑ a ∈ t, w a • (I.q : ℝ) := Finset.sum_le_sum hterm
    _ = (∑ a ∈ t, w a) • (I.q : ℝ) := by rw [← Finset.sum_smul]
    _ = (I.q : ℝ) := by rw [hw₁, one_smul]

/-- **The fractional optimum is dominated by the integral optimum** (the `saturatedCount`
supremum over the integral vertices): any fractional routing that is a convex
combination of integral routings has objective at most the maximum integral
`saturatedCount`. Combined with `worstCaseBacklog_eq` this lifts the worst-case
backlog from "sup over integral routings" to "sup over the whole polytope". -/
theorem X3CInstance.fracObjective_combo_le_iSup_saturatedCount (I : X3CInstance ι α)
    (hne : I.HasAssignment)
    {κ : Type*} (t : Finset κ) (w : κ → ℝ) (assign : κ → α → ι)
    (hassign : ∀ a ∈ t, I.IsAssignment (assign a))
    (hw₀ : ∀ a ∈ t, 0 ≤ w a) (hw₁ : ∑ a ∈ t, w a = 1) :
    I.fracObjective (∑ a ∈ t, w a • I.integralRouting (assign a)) ≤
      ((⨆ c : {assign // I.IsAssignment assign}, I.saturatedCount c.1 : ℕ) : ℝ) := by
  obtain ⟨a0, ha0⟩ := hne
  haveI : Nonempty {assign // I.IsAssignment assign} := ⟨⟨a0, ha0⟩⟩
  have hjensen :
      I.fracObjective (∑ a ∈ t, w a • I.integralRouting (assign a)) ≤
        ∑ a ∈ t, w a • I.fracObjective (I.integralRouting (assign a)) :=
    I.convexOn_fracObjective.map_sum_le hw₀ hw₁ (fun a _ => Set.mem_univ _)
  refine hjensen.trans ?_
  set M : ℕ := ⨆ c : {assign // I.IsAssignment assign}, I.saturatedCount c.1 with hM
  have hterm : ∀ a ∈ t, w a • I.fracObjective (I.integralRouting (assign a)) ≤ w a • (M : ℝ) := by
    intro a ha
    rw [I.fracObjective_integralRouting (assign a)]
    refine smul_le_smul_of_nonneg_left ?_ (hw₀ a ha)
    have : I.saturatedCount (assign a) ≤ M :=
      le_ciSup (f := fun c : {assign // I.IsAssignment assign} => I.saturatedCount c.1)
        (Finite.bddAbove_range _) (⟨assign a, hassign a ha⟩ : {assign // I.IsAssignment assign})
    exact_mod_cast this
  calc ∑ a ∈ t, w a • I.fracObjective (I.integralRouting (assign a))
      ≤ ∑ a ∈ t, w a • (M : ℝ) := Finset.sum_le_sum hterm
    _ = (∑ a ∈ t, w a) • (M : ℝ) := by rw [← Finset.sum_smul]
    _ = (M : ℝ) := by rw [hw₁, one_smul]

/-! ## The full polytope closure: every feasible routing lies in the integral hull
The combination bound above takes the fractional routing *already presented* as a convex
combination of integral routings. The polytope-vertex fact removes that caveat: the
feasibility polytope `{r ≥ 0 : r e i = 0 off cᵢ, Σ_i r e i = 1}` is a product of simplex
faces, one per element, whose vertices are the integral routings. By `convexHull_pi` every
feasible routing lies in `convexHull (integral routings)`, so by convexity its objective is
`≤` the maximum integral `saturatedCount` — the *whole-polytope* statement that no
fractional routing beats the integral vertices. -/

/-- A real routing `r` is **feasible** for the Figure-10.7 polytope: nonnegative, supported
on containing subsets (`r e i = 0` when `e ∉ cᵢ`), and each element's served weight sums to
`1` (`Σ_i r e i = 1`). -/
def X3CInstance.IsFeasible (I : X3CInstance ι α) (r : α → ι → ℝ) : Prop :=
  (∀ e i, 0 ≤ r e i) ∧ (∀ e i, e ∉ I.members i → r e i = 0) ∧ (∀ e, ∑ i, r e i = 1)

/-- The **row vertices** for element `e`: the unit routings `Pi.single i 1` over the subsets
`i` containing `e` (the vertices of `e`'s simplex face). -/
noncomputable def X3CInstance.rowVertices (I : X3CInstance ι α) (e : α) : Finset (ι → ℝ) :=
  (Finset.univ.filter (fun i => e ∈ I.members i)).image (fun i => Pi.single i (1 : ℝ))

/-- **Each feasible row lies in the convex hull of its row vertices**: the probability
vector `r e` (supported on subsets containing `e`, summing to `1`) is the center of mass of
the unit routings `Pi.single i 1`, `i ∋ e`. -/
theorem X3CInstance.row_mem_convexHull_rowVertices (I : X3CInstance ι α) {r : α → ι → ℝ}
    (hr : I.IsFeasible r) (e : α) :
    r e ∈ convexHull ℝ (I.rowVertices e : Set (ι → ℝ)) := by
  obtain ⟨hnn, hsupp, hsum⟩ := hr
  set t : Finset ι := Finset.univ.filter (fun i => e ∈ I.members i) with ht
  -- the row is the center of mass of unit vectors at the containing subsets
  have hsum_t : ∑ i ∈ t, r e i = 1 := by
    rw [ht, Finset.sum_filter]
    rw [← hsum e]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : e ∈ I.members i
    · rw [if_pos hi]
    · rw [if_neg hi, hsupp e i hi]
  have hcm : t.centerMass (r e) (fun i => Pi.single i (1 : ℝ)) = r e := by
    rw [Finset.centerMass_eq_of_sum_1 _ _ hsum_t]
    -- `Σ_{i∈t} r e i • Pi.single i 1 = Σ_i Pi.single i (r e i) = r e`
    have hext : ∀ i ∈ t, (r e i) • (Pi.single i (1 : ℝ)) = Pi.single i (r e i) := fun i _ => by
      rw [← Pi.single_smul' i (r e i) (1 : ℝ), smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl hext]
    -- terms off `t` are zero (`r e i = 0`), so the sum extends to `univ`
    have hext_univ : ∑ x ∈ t, Pi.single x (r e x) = ∑ x, Pi.single x (r e x) := by
      refine Finset.sum_subset (Finset.subset_univ t) ?_
      intro i _ hit
      rw [ht, Finset.mem_filter] at hit
      have : e ∉ I.members i := fun hi => hit ⟨Finset.mem_univ i, hi⟩
      rw [hsupp e i this, Pi.single_zero]
    rw [hext_univ, Finset.univ_sum_single (r e)]
  rw [← hcm]
  refine Finset.centerMass_mem_convexHull t (fun i _ => hnn e i) (by rw [hsum_t]; exact one_pos)
    ?_
  intro i hi
  exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hi)

/-- **Every feasible routing lies in the product of the row simplices**: by `convexHull_pi`,
membership of each row in its row-vertex hull lifts to membership of the routing in the
product polytope `∏ₑ convexHull (rowVertices e)`. -/
theorem X3CInstance.mem_pi_convexHull_of_feasible (I : X3CInstance ι α) {r : α → ι → ℝ}
    (hr : I.IsFeasible r) :
    r ∈ (Set.univ : Set α).pi (fun e => convexHull ℝ (I.rowVertices e : Set (ι → ℝ))) := by
  intro e _
  exact I.row_mem_convexHull_rowVertices hr e

/-! ## The whole-polytope objective bound
A feasible routing's objective is `≤ q`. The product polytope is the convex hull of the
integral routings (the products of row vertices), the objective is convex, so its value at a
feasible routing is bounded by its maximum over the integral vertices, each `≤ q`. -/

/-- **No feasible fractional routing beats the bound `q`** (the whole-polytope statement):
every routing in the feasibility polytope has objective `Σᵢ [load i − 2]⁺ ≤ q`. The
objective is convex and the polytope is `∏ₑ (e's simplex face)`, whose vertices are the
integral routings (`saturatedCount ≤ q`); convexity bounds the value at any feasible point
by the vertex maximum. This is the convex-maximization-attains-a-vertex closure with no
"already a convex combination" caveat. -/
theorem X3CInstance.fracObjective_le_q_of_feasible (I : X3CInstance ι α) {r : α → ι → ℝ}
    (hr : I.IsFeasible r) :
    I.fracObjective r ≤ (I.q : ℝ) := by
  classical
  -- the product polytope = convexHull of the (finite) set of integral routings (= ∏ rowVertices)
  set Pset : Set (α → ι → ℝ) :=
    (Set.univ : Set α).pi (fun e => (I.rowVertices e : Set (ι → ℝ))) with hPset
  have hmem_hull : r ∈ convexHull ℝ Pset := by
    rw [hPset, convexHull_pi]
    exact I.mem_pi_convexHull_of_feasible hr
  -- `Pset` is the coe of the finite product finset `T := Fintype.piFinset rowVertices`
  set T : Finset (α → ι → ℝ) := Fintype.piFinset (fun e => I.rowVertices e) with hT
  have hTcoe : (T : Set (α → ι → ℝ)) = Pset := by
    rw [hT, hPset, Fintype.coe_piFinset]
  rw [← hTcoe] at hmem_hull
  -- the objective is convex on `univ ⊇ ↑T`
  have hsub : (T : Set (α → ι → ℝ)) ⊆ Set.univ := fun _ _ => Set.mem_univ _
  have hle := I.convexOn_fracObjective.le_sup_of_mem_convexHull hsub hmem_hull
  refine hle.trans ?_
  -- every vertex of `T` (a product of row vertices) is an integral routing, objective ≤ q
  refine Finset.sup'_le _ _ fun v hv => ?_
  -- read off the assignment `assign e := the index whose unit vector is `v e``
  rw [hT, Fintype.mem_piFinset] at hv
  -- each row `v e ∈ rowVertices e` is `Pi.single (assign e) 1` for some containing `assign e`
  have hchoose : ∀ e, ∃ i, e ∈ I.members i ∧ v e = Pi.single i (1 : ℝ) := by
    intro e
    have := hv e
    rw [X3CInstance.rowVertices, Finset.mem_image] at this
    obtain ⟨i, hi, hvi⟩ := this
    rw [Finset.mem_filter] at hi
    exact ⟨i, hi.2, hvi.symm⟩
  choose assign hassign_mem hassign_eq using hchoose
  -- `v = integralRouting assign`, so `fracObjective v = saturatedCount assign ≤ q`
  have hv_eq : v = I.integralRouting assign := by
    funext e i
    rw [hassign_eq e, X3CInstance.integralRouting, X3CInstance.routeRate]
    by_cases hi : i = assign e
    · subst hi
      rw [Pi.single_eq_same, if_pos ⟨hassign_mem e, rfl⟩]; norm_num
    · rw [Pi.single_eq_of_ne hi]
      rw [if_neg (fun h => hi h.2.symm)]; norm_num
  rw [hv_eq, I.fracObjective_integralRouting assign]
  exact_mod_cast I.saturatedCount_le_q assign

/-! ## Book restatement (Theorem 10.2, fractional-vs-integral optimality)
The objective the book maximizes over the Figure-10.7 rate polytope,
`Σᵢ [Σ_{e ∈ cᵢ} r e i − 2]⁺`, is **convex** in the fractional routing `r`, so its
maximum over the polytope is attained at an extremal vertex. The vertices are the
integral routings (`r ∈ {0,1}`, the valid assignments), where the objective is the
combinatorial `saturatedCount`. Hence *no fractional fluid routing beats the integral
vertices*: every convex combination of integral routings has objective at most the
maximum integral `saturatedCount` (≤ `q`). This closes the convex-maximization layer
above the integral-vertex worst-case backlog. -/
example (I : X3CInstance ι α) :
    -- the objective is convex on the routing space
    ConvexOn ℝ Set.univ I.fracObjective :=
  I.convexOn_fracObjective

example (I : X3CInstance ι α) (assign : α → ι) :
    -- at an integral vertex the real objective is the combinatorial saturated count
    I.fracObjective (I.integralRouting assign) = (I.saturatedCount assign : ℝ) :=
  I.fracObjective_integralRouting assign

example (I : X3CInstance ι α) {κ : Type*} (t : Finset κ) (w : κ → ℝ)
    (assign : κ → α → ι) (hassign : ∀ a ∈ t, I.IsAssignment (assign a))
    (hw₀ : ∀ a ∈ t, 0 ≤ w a) (hw₁ : ∑ a ∈ t, w a = 1) :
    -- no fractional convex combination of integral routings beats the bound `q`
    I.fracObjective (∑ a ∈ t, w a • I.integralRouting (assign a)) ≤ (I.q : ℝ) :=
  I.fracObjective_combo_le_q t w assign hassign hw₀ hw₁

example (I : X3CInstance ι α) {r : α → ι → ℝ} (hr : I.IsFeasible r) :
    -- no feasible fractional routing in the whole polytope beats the bound `q`
    I.fracObjective r ≤ (I.q : ℝ) :=
  I.fracObjective_le_q_of_feasible hr

end DeepWiki
