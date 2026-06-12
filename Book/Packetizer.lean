import Book.Servers
import Book.ArrivalCurvesMaximal
import Book.ArrivalCurvesMinimal

/-! # The packetizer
A packetizer groups a flow into packets: it stores bits until a
packet's last bit arrives, then releases the whole packet. `packetize`
releases, at each time, the largest cumulative packet length fully
arrived strictly before it; it is an idempotent server whose backlog
never exceeds one maximal packet, `A − ℓᵘ ≤ Pᴸ(A) ≤ A`, and which
shifts arrival curves by at most one maximal packet. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Set Topology Filter

/-- Cumulative packet length sequence with packet sizes in `[ll, lu]`:
`L 0 = 0` and every increment lies between the positive minimum and the
maximum packet size. -/
def IsPacketLengthSeq (L : ℕ → ℝ≥0) (ll lu : ℝ≥0) : Prop :=
  L 0 = 0 ∧ 0 < ll ∧ ∀ n, L n + ll ≤ L (n + 1) ∧ L (n + 1) ≤ L n + lu

/-- A packet length sequence is monotone. -/
theorem IsPacketLengthSeq.monotone {L : ℕ → ℝ≥0} {ll lu : ℝ≥0}
    (h : IsPacketLengthSeq L ll lu) : Monotone L :=
  monotone_nat_of_le_succ fun n => le_trans le_self_add (h.2.2 n).1

/-- Packet lengths grow at least linearly: `n • ll ≤ L n` — the
divergence that ensures every bit belongs to a packet. -/
theorem IsPacketLengthSeq.nsmul_le {L : ℕ → ℝ≥0} {ll lu : ℝ≥0}
    (h : IsPacketLengthSeq L ll lu) (n : ℕ) : n • ll ≤ L n := by
  induction n with
  | zero => simp [h.1]
  | succ n ih =>
    rw [succ_nsmul]
    exact le_trans (add_le_add ih le_rfl) (h.2.2 n).1

/-- The candidate indices of the packetizer at `t`: the packets fully
arrived strictly before `t`. -/
def packetizeSet (L : ℕ → ℝ≥0) (A : ℝ≥0 → ℝ≥0) (t : ℝ≥0) : Set ℕ :=
  {n | ∃ u < t, L n ≤ A u}

/-- `n ∈ packetizeSet L A t ↔ ∃ u < t, L n ≤ A u`. -/
theorem mem_packetizeSet_iff {L : ℕ → ℝ≥0} {A : ℝ≥0 → ℝ≥0} {t : ℝ≥0}
    {n : ℕ} : n ∈ packetizeSet L A t ↔ ∃ u < t, L n ≤ A u := Iff.rfl

/-- The packetizer: at `t`, release the largest cumulative packet
length fully arrived strictly before `t`. -/
noncomputable def packetize (L : ℕ → ℝ≥0) (A : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ≥0 :=
  fun t => sSup (L '' packetizeSet L A t)

/-- The packetizer's candidate values are bounded by the current
arrivals. -/
theorem bddAbove_image_packetizeSet {A : ℝ≥0 → ℝ≥0} (hmono : Monotone A)
    (L : ℕ → ℝ≥0) (t : ℝ≥0) :
    BddAbove (L '' packetizeSet L A t) := by
  refine ⟨A t, ?_⟩
  rintro x ⟨n, ⟨u, hu, hLn⟩, rfl⟩
  exact le_trans hLn (hmono hu.le)

/-- Intro: a fully-arrived packet length bounds the packetizer from
below. -/
theorem le_packetize {L : ℕ → ℝ≥0} {A : ℝ≥0 → ℝ≥0} (hmono : Monotone A)
    {n : ℕ} {t : ℝ≥0} (hn : n ∈ packetizeSet L A t) :
    L n ≤ packetize L A t :=
  le_csSup (bddAbove_image_packetizeSet hmono L t) ⟨n, hn, rfl⟩

/-- Elim: a bound on all candidate packet lengths bounds the
packetizer. -/
theorem packetize_le_of_forall {L : ℕ → ℝ≥0} {A : ℝ≥0 → ℝ≥0}
    {x t : ℝ≥0} (h : ∀ n ∈ packetizeSet L A t, L n ≤ x) :
    packetize L A t ≤ x :=
  csSup_le' (by rintro y ⟨n, hn, rfl⟩; exact h n hn)

/-- `packetize L A 0 = 0`: nothing has arrived strictly before `0`. -/
theorem packetize_zero (L : ℕ → ℝ≥0) (A : ℝ≥0 → ℝ≥0) :
    packetize L A 0 = 0 := by
  rw [packetize,
    show packetizeSet L A 0 = ∅ from
      Set.eq_empty_iff_forall_notMem.mpr fun n ⟨u, hu, _⟩ =>
        absurd hu (not_lt.mpr zero_le'),
    Set.image_empty, csSup_empty]
  rfl

/-- Causality: the packetizer never releases more than has arrived,
`packetize L A t ≤ A t`. -/
theorem packetize_le {A : ℝ≥0 → ℝ≥0} (hmono : Monotone A) (L : ℕ → ℝ≥0)
    (t : ℝ≥0) : packetize L A t ≤ A t :=
  packetize_le_of_forall fun _ ⟨_, hu, hLn⟩ =>
    le_trans hLn (hmono hu.le)

/-- `packetize` is monotone in time: the candidate set grows. -/
theorem packetize_mono {A : ℝ≥0 → ℝ≥0} (hmono : Monotone A)
    (L : ℕ → ℝ≥0) : Monotone (packetize L A) := by
  intro a b hab
  refine packetize_le_of_forall ?_
  rintro n ⟨u, hu, hLn⟩
  exact le_packetize hmono ⟨u, lt_of_lt_of_le hu hab, hLn⟩

/-- **Attainment**: for `t > 0` the packetizer value is a cumulative
packet length `L n`, achieved strictly before `t`, with
`L n ≤ A t ≤ L (n + 1)` (the upper bound by left-continuity of `A`). -/
theorem exists_packetize_eq {L : ℕ → ℝ≥0} {ll lu : ℝ≥0}
    (hL : IsPacketLengthSeq L ll lu) {A : ℝ≥0 → ℝ≥0}
    (hmono : Monotone A) (hlc : IsLeftContinuous A) {t : ℝ≥0}
    (ht : 0 < t) :
    ∃ n, packetize L A t = L n ∧ (∃ u < t, L n ≤ A u)
      ∧ L n ≤ A t ∧ A t ≤ L (n + 1) := by
  have hne : (packetizeSet L A t).Nonempty :=
    ⟨0, 0, ht, by rw [hL.1]; exact zero_le'⟩
  have hbdd : BddAbove (packetizeSet L A t) := by
    refine ⟨⌊A t / ll⌋₊, ?_⟩
    rintro n ⟨u, hu, hLn⟩
    refine Nat.le_floor ?_
    rw [le_div_iff₀ hL.2.1]
    calc (n : ℝ≥0) * ll = n • ll := (nsmul_eq_mul n ll).symm
      _ ≤ L n := hL.nsmul_le n
      _ ≤ A u := hLn
      _ ≤ A t := hmono hu.le
  set m := sSup (packetizeSet L A t) with hmdef
  have hmem : m ∈ packetizeSet L A t := Nat.sSup_mem hne hbdd
  refine ⟨m, ?_, hmem, ?_, ?_⟩
  · refine le_antisymm (packetize_le_of_forall fun n hn =>
      hL.monotone (le_csSup hbdd hn)) (le_packetize hmono hmem)
  · obtain ⟨u, hu, hLm⟩ := hmem
    exact le_trans hLm (hmono hu.le)
  · have hub : ∀ u ∈ Set.Iio t, A u ≤ L (m + 1) := by
      intro u hu
      by_contra hgt
      have hmem1 : m + 1 ∈ packetizeSet L A t :=
        ⟨u, hu, (not_le.mp hgt).le⟩
      have := le_csSup hbdd hmem1
      omega
    haveI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
    exact le_of_tendsto (hlc t)
      (Filter.eventually_iff_exists_mem.mpr
        ⟨Set.Iio t, self_mem_nhdsWithin, hub⟩)

/-- **Buffer bound**: arrivals exceed the packetized output by at most
one maximal packet, `A t ≤ packetize L A t + ℓᵘ`. -/
theorem apply_le_packetize_add {L : ℕ → ℝ≥0} {ll lu : ℝ≥0}
    (hL : IsPacketLengthSeq L ll lu) {A : ℝ≥0 → ℝ≥0}
    (hmono : Monotone A) (h0 : A 0 = 0) (hlc : IsLeftContinuous A)
    (t : ℝ≥0) : A t ≤ packetize L A t + lu := by
  rcases eq_zero_or_pos t with rfl | ht
  · rw [h0]
    exact zero_le'
  · obtain ⟨n, hP, _, _, hup⟩ := exists_packetize_eq hL hmono hlc ht
    rw [hP]
    exact le_trans hup (hL.2.2 n).2

/-- The packetized output is left-continuous: it is constant on a left
interval ending at each `t > 0`. -/
theorem packetize_leftCont {L : ℕ → ℝ≥0} {ll lu : ℝ≥0}
    (hL : IsPacketLengthSeq L ll lu) {A : ℝ≥0 → ℝ≥0}
    (hmono : Monotone A) (hlc : IsLeftContinuous A) :
    IsLeftContinuous (packetize L A) := by
  intro t
  rcases eq_zero_or_pos t with rfl | ht
  · exact isLeftContinuousAt_zero _
  · obtain ⟨n, hP, ⟨u₀, hu₀, hLn⟩, _, _⟩ :=
      exists_packetize_eq hL hmono hlc ht
    have hconst : ∀ s ∈ Set.Ioc u₀ t, packetize L A s = L n := by
      intro s hs
      refine le_antisymm ?_ ?_
      · rw [← hP]
        exact packetize_mono hmono L hs.2
      · exact le_packetize hmono ⟨u₀, hs.1, hLn⟩
    have htend : Filter.Tendsto (packetize L A) (𝓝[<] t) (𝓝 (L n)) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Ioo_mem_nhdsLT hu₀] with v hv
      exact (hconst v ⟨hv.1, hv.2.le⟩).symm
    show Filter.Tendsto (packetize L A) (𝓝[<] t)
      (𝓝 (packetize L A t))
    rwa [hP]

/-- The packetized output is piecewise continuous: on `[0, T]` it takes
finitely many of the `L n` values, and each discontinuity is a right
jump. -/
theorem packetize_pwc {L : ℕ → ℝ≥0} {ll lu : ℝ≥0}
    (hL : IsPacketLengthSeq L ll lu) {A : ℝ≥0 → ℝ≥0}
    (hmono : Monotone A) (hlc : IsLeftContinuous A) :
    IsPiecewiseContinuous (packetize L A) := by
  refine isPiecewiseContinuous_of_monotone_of_finite_image
    (packetize_mono hmono L) (packetize_leftCont hL hmono hlc) ?_
  intro T
  refine Set.Finite.subset ((Set.finite_Iic ⌊A T / ll⌋₊).image L) ?_
  rintro x ⟨s, hs, rfl⟩
  rcases eq_zero_or_pos s with rfl | hspos
  · exact ⟨0, Set.mem_Iic.mpr (Nat.zero_le _), by
      rw [packetize_zero, hL.1]⟩
  · obtain ⟨n, hP, _, hle, _⟩ := exists_packetize_eq hL hmono hlc hspos
    refine ⟨n, Set.mem_Iic.mpr (Nat.le_floor ?_), hP.symm⟩
    rw [le_div_iff₀ hL.2.1]
    calc (n : ℝ≥0) * ll = n • ll := (nsmul_eq_mul n ll).symm
      _ ≤ L n := hL.nsmul_le n
      _ ≤ A s := hle
      _ ≤ A T := hmono hs.2

/-- The packetized output as a `Curve`. -/
noncomputable def packetizeCurve {L : ℕ → ℝ≥0} {ll lu : ℝ≥0}
    (hL : IsPacketLengthSeq L ll lu) (A : Curve) : Curve :=
  ⟨packetize L ⇑A, packetize_mono A.mono L, packetize_zero L ⇑A,
    packetize_pwc hL A.mono A.leftCont,
    packetize_leftCont hL A.mono A.leftCont⟩

/-- `packetizeCurve hL A t = packetize L ⇑A t`: the pointwise value. -/
@[simp] theorem packetizeCurve_apply {L : ℕ → ℝ≥0} {ll lu : ℝ≥0}
    (hL : IsPacketLengthSeq L ll lu) (A : Curve) (t : ℝ≥0) :
    packetizeCurve hL A t = packetize L ⇑A t := rfl

/-- Causality at the curve level: `packetizeCurve hL A ≤ A`. -/
theorem packetizeCurve_le {L : ℕ → ℝ≥0} {ll lu : ℝ≥0}
    (hL : IsPacketLengthSeq L ll lu) (A : Curve) :
    packetizeCurve hL A ≤ A :=
  fun t => packetize_le A.mono L t

/-- **Maximum buffer of a packetizer**: the packetizer holds at most
one maximal packet, `A − ℓᵘ ≤ Pᴸ(A) ≤ A`. -/
theorem packetizeCurve_sandwich {L : ℕ → ℝ≥0} {ll lu : ℝ≥0}
    (hL : IsPacketLengthSeq L ll lu) (A : Curve) (t : ℝ≥0) :
    A t - lu ≤ packetizeCurve hL A t ∧ packetizeCurve hL A t ≤ A t :=
  ⟨tsub_le_iff_right.mpr (apply_le_packetize_add hL A.mono
      (A.zero : A 0 = 0) A.leftCont t),
    packetize_le A.mono L t⟩

/-- The packetizer relation: the output is exactly the packetized
input. -/
def packetizerRel (L : ℕ → ℝ≥0) : Curve → Curve → Prop :=
  fun A D => ⇑D = packetize L ⇑A

/-- `packetizerRel L A D` unfolds to `D = Pᴸ(A)` at the function
level. -/
theorem mem_packetizerRel_iff {L : ℕ → ℝ≥0} {A D : Curve} :
    packetizerRel L A D ↔ ⇑D = packetize L ⇑A := Iff.rfl

/-- `packetizerRel L A D` at the `Curve` level: `D = Pᴸ(A)` as curves
(under a packet length sequence witnessing the `Curve` structure). -/
theorem packetizerRel_iff_eq_packetizeCurve {L : ℕ → ℝ≥0}
    {ll lu : ℝ≥0} (hL : IsPacketLengthSeq L ll lu) {A D : Curve} :
    packetizerRel L A D ↔ D = packetizeCurve hL A :=
  ⟨fun hp => Curve.ext fun t => congrFun hp t,
    fun hp => by subst hp; rfl⟩

/-- `S` is an `L`-packetizer: every pair's output is the packetized
input. -/
def IsPacketizer (L : ℕ → ℝ≥0) (S : Curve → Curve → Prop) : Prop :=
  ∀ A D : Curve, S A D → ⇑D = packetize L ⇑A

/-- `IsPacketizer L S` iff `S ≤ packetizerRel L`. -/
theorem isPacketizer_iff_subset {L : ℕ → ℝ≥0}
    {S : Curve → Curve → Prop} :
    IsPacketizer L S ↔ ∀ A D : Curve, S A D → packetizerRel L A D :=
  Iff.rfl

/-- The packetizer relation is an `L`-packetizer. -/
theorem isPacketizer_packetizerRel (L : ℕ → ℝ≥0) :
    IsPacketizer L (packetizerRel L) := fun _ _ hp => hp

/-- **A packetizer is a server**: causal and left-total. -/
theorem isServer_packetizerRel {L : ℕ → ℝ≥0} {ll lu : ℝ≥0}
    (hL : IsPacketLengthSeq L ll lu) : IsServer (packetizerRel L) :=
  ⟨fun A D hp => by
      rw [(packetizerRel_iff_eq_packetizeCurve hL).mp hp]
      exact packetizeCurve_le hL A,
    fun A => ⟨packetizeCurve hL A, rfl⟩⟩

/-! ## Book restatement (a packetizer is a server with unit buffer)
`Pᴸ` maps cumulative functions to cumulative functions with
`A ≥ Pᴸ(A)`, and its backlog is at most the maximum packet size:
`A ≥ Pᴸ(A) ≥ A − ℓᵘ`. -/
example {L : ℕ → ℝ≥0} {ll lu : ℝ≥0} (hL : IsPacketLengthSeq L ll lu) :
    IsServer (packetizerRel L)
      ∧ ∀ A : Curve, ∀ t, A t - lu ≤ packetizeCurve hL A t :=
  ⟨isServer_packetizerRel hL,
    fun A t => (packetizeCurve_sandwich hL A t).1⟩

/-! ## Packetized functions and idempotence -/

/-- `A` is `L`-packetized: the packetizer leaves it unchanged. -/
def IsPacketized (L : ℕ → ℝ≥0) (A : ℝ≥0 → ℝ≥0) : Prop :=
  packetize L A = A

/-- **The packetizer is idempotent**: `Pᴸ(Pᴸ(A)) = Pᴸ(A)` — a
candidate before the inner packetizer is a candidate before the outer
one, by density of the time axis. -/
theorem packetize_packetize {L : ℕ → ℝ≥0} {A : ℝ≥0 → ℝ≥0}
    (hmono : Monotone A) :
    packetize L (packetize L A) = packetize L A := by
  funext t
  refine le_antisymm (packetize_le_of_forall ?_)
    (packetize_le_of_forall ?_)
  · rintro n ⟨u, hu, hLn⟩
    exact le_packetize hmono
      ⟨u, hu, le_trans hLn (packetize_le hmono L u)⟩
  · rintro n ⟨u, hu, hLn⟩
    obtain ⟨v, huv, hvt⟩ := exists_between hu
    exact le_packetize (packetize_mono hmono L)
      ⟨v, hvt, le_packetize hmono ⟨u, huv, hLn⟩⟩

/-- Packetizer outputs are packetized. -/
theorem isPacketized_packetize {L : ℕ → ℝ≥0} {A : ℝ≥0 → ℝ≥0}
    (hmono : Monotone A) : IsPacketized L (packetize L A) :=
  packetize_packetize hmono

/-- Curve form of idempotence. -/
theorem packetizeCurve_packetizeCurve {L : ℕ → ℝ≥0} {ll lu : ℝ≥0}
    (hL : IsPacketLengthSeq L ll lu) (A : Curve) :
    packetizeCurve hL (packetizeCurve hL A) = packetizeCurve hL A :=
  Curve.ext fun t => congrFun (packetize_packetize A.mono) t

/-! ## Arrival curves after a packetizer -/

/-- **Arrival curve after a packetizer** (maximal): the output allows
`αᵘ + ℓᵘ`, through the one-packet sandwich. -/
theorem isMaximalArrivalBound_packetizeCurve {L : ℕ → ℝ≥0}
    {ll lu : ℝ≥0} (hL : IsPacketLengthSeq L ll lu) {A : Curve}
    {α : ℝ≥0 → ℝ≥0} (h : IsMaximalArrivalBound ⇑A α) :
    IsMaximalArrivalBound ⇑(packetizeCurve hL A)
      (fun d => α d + lu) :=
  isMaximalArrivalBound_of_sandwich
    (fun t => packetize_le A.mono L t)
    (fun t => apply_le_packetize_add hL A.mono (A.zero : A 0 = 0)
      A.leftCont t) h

/-- **Arrival curve after a packetizer** (minimal): the output allows
`αˡ − ℓᵘ`, with the hypothesis in increment form. -/
theorem isMinimalArrivalBound_packetizeCurve {L : ℕ → ℝ≥0}
    {ll lu : ℝ≥0} (hL : IsPacketLengthSeq L ll lu) {A : Curve}
    {α : ℝ≥0 → ℝ≥0} (h : ∀ t d, A t + α d ≤ A (t + d)) :
    IsMinimalArrivalBound ⇑(packetizeCurve hL A)
      (fun d => α d - lu) :=
  isMinimalArrivalBound_of_sandwich (packetize_mono A.mono L)
    (fun t => packetize_le A.mono L t)
    (fun t => apply_le_packetize_add hL A.mono (A.zero : A 0 = 0)
      A.leftCont t) h

/-! ## Book restatement (arrival curve after a packetizer)
`(A, D) ∈ Pᴸ` with maximum packet size `ℓᵘ`: if `A` has a maximal
(respectively minimal) arrival curve `αᵘ` (resp. `αˡ`), then `D` has
maximal (resp. minimal) arrival curve `αᵘ + ℓᵘ` (resp. `αˡ − ℓᵘ`). -/
example {L : ℕ → ℝ≥0} {ll lu : ℝ≥0} (hL : IsPacketLengthSeq L ll lu)
    {A D : Curve} (hp : packetizerRel L A D)
    {αu : ℝ≥0 → ℝ≥0} (harr : IsMaximalArrivalCurve ⇑A αu) :
    IsMaximalArrivalCurve ⇑D (fun d => αu d + lu) := by
  rw [show ⇑D = packetize L ⇑A from hp]
  exact ⟨fun a b hab => add_le_add (harr.1 hab) le_rfl,
    isMaximalArrivalBound_packetizeCurve hL harr.2⟩

example {L : ℕ → ℝ≥0} {ll lu : ℝ≥0} (hL : IsPacketLengthSeq L ll lu)
    {A D : Curve} (hp : packetizerRel L A D)
    {αl : ℝ≥0 → ℝ≥0} (harr : IsMinimalArrivalCurve ⇑A αl) :
    IsMinimalArrivalCurve ⇑D (fun d => αl d - lu) := by
  rw [show ⇑D = packetize L ⇑A from hp]
  exact ⟨fun a b hab => tsub_le_tsub_right (harr.1 hab) lu,
    isMinimalArrivalBound_packetizeCurve hL
      ((isMinimalArrivalBound_iff_increment_of_monotone _ _ A.mono
        harr.1).mp harr.2)⟩

end DeepWiki
