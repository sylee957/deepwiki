import Book.Packetizer
import Book.ServersConcatenation
import Book.ArrivalCurvesShaper
import Book.ServiceCurveMaximal
import Book.Deviations

/-! # A server followed by a packetizer
The combined system `S;P`: the packetizer costs one maximal packet on
the minimal service curve (`β − ℓᵘ`), nothing on the maximal one, one
packet on the shaping curve (`σ + ℓᵘ`) and on the backlog; its outputs
are packetized, and on packetized inputs it adds no delay. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal

/-- Lowering the kernel by a real constant lowers the convolution by
the same constant: `f ∗ (g − c) ≤ (f ∗ g) − c` pointwise. -/
theorem minConv_sub_const_le (f g : ℝ≥0 → EReal) (c : ℝ) (t : ℝ≥0) :
    minConv f (fun v => g v - (c : EReal)) t
      ≤ minConv f g t - (c : EReal) := by
  rw [EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot c))
    (Or.inl (EReal.coe_ne_top c))]
  refine le_minConv fun u v huv => ?_
  calc minConv f (fun v => g v - (c : EReal)) t + (c : EReal)
      ≤ (f u + (g v - (c : EReal))) + (c : EReal) :=
        add_le_add (minConv_le_add _ _ huv) le_rfl
    _ = f u + (g v - (c : EReal) + (c : EReal)) := add_assoc _ _ _
    _ = f u + g v := by rw [EReal.sub_add_cancel]

/-- `↑a − ↑b ≤ ↑(a - b)`: the `EReal` difference of coercions is below
the coercion of the truncated `ℝ≥0` difference. -/
theorem coe_sub_le_coe_tsub (a b : ℝ≥0) :
    ((a : ℝ) : EReal) - ((b : ℝ) : EReal)
      ≤ (((a - b : ℝ≥0) : ℝ) : EReal) := by
  rw [← EReal.coe_sub]
  rcases le_total b a with h | h
  · rw [NNReal.coe_sub h]
  · refine EReal.coe_le_coe_iff.mpr ?_
    have h1 : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast h
    have h2 : (0 : ℝ) ≤ ((a - b : ℝ≥0) : ℝ) := (a - b).coe_nonneg
    linarith

/-- **Minimal service through a packetizer**: `S;P` offers `β − ℓᵘ`
when `S` offers the min-plus `β`. -/
theorem IsMinimalServiceCurve.comp_packetizerRel
    {S : Curve → Curve → Prop} {β : ℝ≥0 → EReal}
    (hβ : IsMinimalServiceCurve β S)
    {L : ℕ → ℝ≥0} {ll lu : ℝ≥0} (hL : IsPacketLengthSeq L ll lu) :
    IsMinimalServiceCurve (fun v => β v - ((lu : ℝ) : EReal))
      (Relation.Comp S (packetizerRel L)) := by
  rintro A C ⟨B, hSB, hC⟩
  obtain rfl := (packetizerRel_iff_eq_packetizeCurve hL).mp hC
  intro t
  refine le_trans (minConv_sub_const_le (curveEReal A) β lu t) ?_
  calc minConv (curveEReal A) β t - ((lu : ℝ) : EReal)
      ≤ curveEReal B t - ((lu : ℝ) : EReal) := by
        rw [sub_eq_add_neg, sub_eq_add_neg]
        exact add_le_add (hβ A B hSB t) le_rfl
    _ ≤ (((B t - lu : ℝ≥0) : ℝ) : EReal) := coe_sub_le_coe_tsub _ _
    _ ≤ curveEReal (packetizeCurve hL B) t := by
        rw [curveEReal_apply]
        exact_mod_cast (packetizeCurve_sandwich hL B t).1

/-- **Maximal service through a packetizer**: unchanged, since the
packetizer only removes output. -/
theorem IsMaximalServiceCurve.comp_packetizerRel
    {S : Curve → Curve → Prop} {β : ℝ≥0 → EReal}
    (hβ : IsMaximalServiceCurve β S)
    {L : ℕ → ℝ≥0} {ll lu : ℝ≥0} (hL : IsPacketLengthSeq L ll lu) :
    IsMaximalServiceCurve β (Relation.Comp S (packetizerRel L)) := by
  rintro A C ⟨B, hSB, hC⟩
  obtain rfl := (packetizerRel_iff_eq_packetizeCurve hL).mp hC
  exact le_trans (curveEReal_mono (packetizeCurve_le hL B)) (hβ A B hSB)

/-- **Shaping through a packetizer**: `S;P` is a `(σ + ℓᵘ)`-shaper when
`S` is a `σ`-shaper — the generic sandwich transport at the `curveEReal`
reading. -/
theorem IsShaper.comp_packetizerRel {S : Curve → Curve → Prop}
    {σ : ℝ≥0 → EReal} (hS : IsShaper σ S)
    {L : ℕ → ℝ≥0} {ll lu : ℝ≥0} (hL : IsPacketLengthSeq L ll lu) :
    IsShaper (fun d => σ d + ((lu : ℝ) : EReal))
      (Relation.Comp S (packetizerRel L)) := by
  rintro A C ⟨B, hSB, hC⟩
  obtain rfl := (packetizerRel_iff_eq_packetizeCurve hL).mp hC
  exact isMaximalArrivalBound_of_sandwich
    (fun t => by
      rw [curveEReal_apply, curveEReal_apply]
      exact_mod_cast (packetizeCurve_sandwich hL B t).2)
    (fun t => by
      rw [curveEReal_apply, curveEReal_apply, ← EReal.coe_add]
      exact_mod_cast apply_le_packetize_add hL B.mono
        (B.zero : B 0 = 0) B.leftCont t)
    (hS A B hSB)

/-- **The combined system's outputs are packetized.** -/
theorem isPacketized_of_comp_packetizerRel {S : Curve → Curve → Prop}
    {L : ℕ → ℝ≥0} {A C : Curve}
    (hp : Relation.Comp S (packetizerRel L) A C) :
    IsPacketized L ⇑C := by
  obtain ⟨B, _, hC⟩ := hp
  rw [hC]
  exact isPacketized_packetize B.mono

namespace Deviation

/-- **Backlog through a packetizer** (pair level): the packetizer adds
at most one maximal packet of backlog,
`b(A,B) ≤ b(A, Pᴸ(B)) ≤ b(A,B) + ℓᵘ`. -/
theorem backlog_packetizeCurve_sandwich {L : ℕ → ℝ≥0} {ll lu : ℝ≥0}
    (hL : IsPacketLengthSeq L ll lu) (A : ℝ≥0 → ℝ≥0) (B : Curve) :
    Deviation.backlog A ⇑B
        ≤ Deviation.backlog A ⇑(packetizeCurve hL B)
      ∧ Deviation.backlog A ⇑(packetizeCurve hL B)
        ≤ Deviation.backlog A ⇑B + lu := by
  rw [Deviation.backlog_eq_iSup, Deviation.backlog_eq_iSup]
  constructor
  · refine iSup_mono fun t => ?_
    exact_mod_cast tsub_le_tsub_left (packetize_le B.mono L t) (A t)
  · refine iSup_le fun t => ?_
    have h1 : A t - packetizeCurve hL B t ≤ (A t - B t) + lu := by
      rw [tsub_le_iff_right]
      calc A t ≤ (A t - B t) + B t := le_tsub_add
        _ ≤ (A t - B t) + (packetizeCurve hL B t + lu) :=
            add_le_add le_rfl (apply_le_packetize_add hL B.mono
              (B.zero : B 0 = 0) B.leftCont t)
        _ = (A t - B t) + lu + packetizeCurve hL B t := by ring
    calc ((A t - packetizeCurve hL B t : ℝ≥0) : ℝ≥0∞)
        ≤ (((A t - B t) + lu : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast h1
      _ = ((A t - B t : ℝ≥0) : ℝ≥0∞) + (lu : ℝ≥0∞) := by push_cast; rfl
      _ ≤ (⨆ s : ℝ≥0, ((A s - B s : ℝ≥0) : ℝ≥0∞)) + (lu : ℝ≥0∞) :=
          add_le_add
            (le_iSup (fun s => ((A s - B s : ℝ≥0) : ℝ≥0∞)) t) le_rfl

/-- **A packetizer adds no delay to packetized inputs** (pointwise):
for `L`-packetized `A`, every admissible shift for `B` is a limit of
admissible shifts for `Pᴸ(B)` — the packet `A t` releases as soon as
its last bit is served. -/
theorem delayAt_packetizeCurve_eq {L : ℕ → ℝ≥0} {ll lu : ℝ≥0}
    (hL : IsPacketLengthSeq L ll lu) {A : Curve}
    (hA : IsPacketized L ⇑A) (B : Curve) (t : ℝ≥0) :
    Deviation.delayAt ⇑A ⇑(packetizeCurve hL B) t
      = Deviation.delayAt ⇑A ⇑B t := by
  refine le_antisymm ?_ ?_
  · show Deviation.delayAt ⇑A ⇑(packetizeCurve hL B) t
      ≤ ⨅ d : {d : ℝ≥0 // A t ≤ B (t + d)}, (d.1 : ℝ≥0∞)
    refine le_iInf fun d => ?_
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    rw [show ((d.1 : ℝ≥0∞) + ε) = ((d.1 + ε : ℝ≥0) : ℝ≥0∞) from by
      push_cast; rfl]
    refine hDevAt_le ?_
    rcases eq_zero_or_pos t with rfl | ht
    · exact (A.zero : A 0 = 0).trans_le zero_le'
    · obtain ⟨n, hPn, _, _, _⟩ :=
        exists_packetize_eq hL A.mono A.leftCont ht
      have hAt : A t = L n := by
        rw [← hA]
        exact hPn
      refine le_trans (le_of_eq hAt) ?_
      refine le_packetize B.mono ⟨t + d.1, ?_, ?_⟩
      · rw [← add_assoc]
        exact lt_add_of_pos_right _ hε
      · exact le_trans (le_of_eq hAt.symm) d.2
  · show Deviation.delayAt ⇑A ⇑B t
      ≤ ⨅ d : {d : ℝ≥0 // A t ≤ packetizeCurve hL B (t + d)},
          (d.1 : ℝ≥0∞)
    refine le_iInf fun d => ?_
    exact hDevAt_le (le_trans d.2 (packetize_le B.mono L _))

/-- **A packetizer adds no delay to packetized inputs**:
`d(A, Pᴸ(B)) = d(A, B)` for `L`-packetized `A`. -/
theorem delay_packetizeCurve_eq {L : ℕ → ℝ≥0} {ll lu : ℝ≥0}
    (hL : IsPacketLengthSeq L ll lu) {A : Curve}
    (hA : IsPacketized L ⇑A) (B : Curve) :
    Deviation.delay ⇑A ⇑(packetizeCurve hL B)
      = Deviation.delay ⇑A ⇑B := by
  rw [Deviation.delay_eq_iSup, Deviation.delay_eq_iSup]
  exact iSup_congr fun t => delayAt_packetizeCurve_eq hL hA B t

end Deviation

/-- Pair form: every `S;P` pair with packetized input realizes exactly
the delay of its `S` stage. -/
theorem exists_delay_eq_of_comp_packetizerRel
    {S : Curve → Curve → Prop} {L : ℕ → ℝ≥0} {ll lu : ℝ≥0}
    (hL : IsPacketLengthSeq L ll lu) {A C : Curve}
    (hA : IsPacketized L ⇑A)
    (hp : Relation.Comp S (packetizerRel L) A C) :
    ∃ B, S A B ∧ Deviation.delay ⇑A ⇑C = Deviation.delay ⇑A ⇑B := by
  obtain ⟨B, hSB, hC⟩ := hp
  obtain rfl := (packetizerRel_iff_eq_packetizeCurve hL).mp hC
  exact ⟨B, hSB, Deviation.delay_packetizeCurve_eq hL hA B⟩

/-- Pair form: every `S;P` pair backlogs within one maximal packet of
its `S` stage. -/
theorem exists_backlog_sandwich_of_comp_packetizerRel
    {S : Curve → Curve → Prop} {L : ℕ → ℝ≥0} {ll lu : ℝ≥0}
    (hL : IsPacketLengthSeq L ll lu) {A C : Curve}
    (hp : Relation.Comp S (packetizerRel L) A C) :
    ∃ B, S A B ∧ Deviation.backlog ⇑A ⇑B ≤ Deviation.backlog ⇑A ⇑C
      ∧ Deviation.backlog ⇑A ⇑C ≤ Deviation.backlog ⇑A ⇑B + lu := by
  obtain ⟨B, hSB, hC⟩ := hp
  obtain rfl := (packetizerRel_iff_eq_packetizeCurve hL).mp hC
  exact ⟨B, hSB,
    (Deviation.backlog_packetizeCurve_sandwich hL ⇑A B).1,
    (Deviation.backlog_packetizeCurve_sandwich hL ⇑A B).2⟩

/-! ## Book restatement (the server/packetizer system)
`S` a server, `P` a packetizer with maximum packet size `ℓᵘ`: the
combined system `S;P` is a server; if `S` offers a min-plus minimal
service curve `βᵐ`, a maximal service curve `βᴹ`, and is a `σ`-shaper,
then `S;P` offers `βᵐ − ℓᵘ` and `βᴹ` and is a `(σ + ℓᵘ)`-shaper; its
outputs are packetized; per pair it holds at most one extra maximal
packet of backlog; and on packetized inputs it adds no delay
(`exists_delay_eq_of_comp_packetizerRel`). (The no-strict-counterpart
warning — `β − ℓᵘ` need not be strict for `S;P` — is the remaining
refutation.) -/
example {S : Curve → Curve → Prop} {βm βM σ : ℝ≥0 → EReal}
    {L : ℕ → ℝ≥0} {ll lu : ℝ≥0} (hL : IsPacketLengthSeq L ll lu)
    (hSrv : IsServer S) (hβm : IsMinimalServiceCurve βm S)
    (hβM : IsMaximalServiceCurve βM S) (hsh : IsShaper σ S) :
    IsServer (Relation.Comp S (packetizerRel L))
      ∧ IsMinimalServiceCurve (fun v => βm v - ((lu : ℝ) : EReal))
          (Relation.Comp S (packetizerRel L))
      ∧ IsMaximalServiceCurve βM (Relation.Comp S (packetizerRel L))
      ∧ IsShaper (fun d => σ d + ((lu : ℝ) : EReal))
          (Relation.Comp S (packetizerRel L))
      ∧ (∀ A C, Relation.Comp S (packetizerRel L) A C →
          IsPacketized L ⇑C)
      ∧ (∀ A C : Curve, Relation.Comp S (packetizerRel L) A C →
          ∃ B, S A B
            ∧ Deviation.backlog ⇑A ⇑B ≤ Deviation.backlog ⇑A ⇑C
            ∧ Deviation.backlog ⇑A ⇑C ≤ Deviation.backlog ⇑A ⇑B + lu)
      ∧ (∀ A C : Curve, IsPacketized L ⇑A →
          Relation.Comp S (packetizerRel L) A C →
          ∃ B, S A B
            ∧ Deviation.delay ⇑A ⇑C = Deviation.delay ⇑A ⇑B) :=
  ⟨hSrv.comp (isServer_packetizerRel hL),
    hβm.comp_packetizerRel hL,
    hβM.comp_packetizerRel hL,
    hsh.comp_packetizerRel hL,
    fun _ _ hp => isPacketized_of_comp_packetizerRel hp,
    fun _ _ hp => exists_backlog_sandwich_of_comp_packetizerRel hL hp,
    fun _ _ hA hp => exists_delay_eq_of_comp_packetizerRel hL hA hp⟩

end DeepWiki
