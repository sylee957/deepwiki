import DeepWiki.NetworkCalculus.Packetizer
import DeepWiki.NetworkCalculus.ServiceCurvePackets
import DeepWiki.NetworkCalculus.ServersConcatenation
import DeepWiki.NetworkCalculus.ArrivalCurvesShaper
import DeepWiki.NetworkCalculus.ServiceCurveMaximal
import DeepWiki.NetworkCalculus.Deviations
import DeepWiki.NetworkCalculus.ServersJitter
import DeepWiki.NetworkCalculus.ArrivalCurvesOutput

/-! # A server followed by a packetizer
The combined system `S;P`: the packetizer costs one maximal packet on
the minimal service curve (`β − ℓᵘ`), nothing on the maximal one, one
packet on the shaping curve (`σ + ℓᵘ`) and on the backlog; its outputs
are packetized, and on packetized inputs it adds no delay. The
minimal-service bound has no strict counterpart. -/

namespace DeepWiki

open scoped Classical NNReal ENNReal
open Set Topology Filter

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
    · exact (A.zero : A 0 = 0).trans_le zero_le
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

/-- **Corollary 8.2** (packetizer as a delay): on a `P`-packetized input `A`, the
system `S;P` adds no delay, so it offers the **pure-delay min-plus service curve**
`δ_dM` of its `S` stage — given any finite bound `dM` on the `S`-stage delay
(`∀ B, S A B → delay A B ≤ dM`), the output `C` of `S;P` satisfies
`A (t − dM) ≤ C t` (the `δ_dM` convolution bound). The arrival `A` is
left-continuous as a `Curve`, which the bound at the exact delay requires
(`Deviation.apply_tsub_le_of_delay_le_of_leftCont`; left-continuity is necessary,
`Deviation.not_forall_apply_tsub_le_of_delay_le`). -/
theorem apply_tsub_le_of_isPacketized_comp_packetizerRel
    {S : Curve → Curve → Prop} {L : ℕ → ℝ≥0} {ll lu : ℝ≥0}
    (hL : IsPacketLengthSeq L ll lu) {A C : Curve} {dM : ℝ≥0}
    (hA : IsPacketized L ⇑A)
    (hp : Relation.Comp S (packetizerRel L) A C)
    (hd : ∀ B : Curve, S A B → Deviation.delay ⇑A ⇑B ≤ (dM : ℝ≥0∞))
    (t : ℝ≥0) :
    (⇑A) (t - dM) ≤ (⇑C) t := by
  obtain ⟨B, hSB, hdeq⟩ := exists_delay_eq_of_comp_packetizerRel hL hA hp
  refine Deviation.apply_tsub_le_of_delay_le_of_leftCont
    (A.zero : (⇑A) 0 = 0) A.leftCont C.mono ?_ t
  exact hdeq.le.trans (hd B hSB)

/-- **Corollary 8.3** (combined arrival curve from a packetizer), main bound: the
output `D` of the system `S;P` carries the maximal arrival curve
`((α ∗ βᴹ) ⊘ (βᵐ − ℓᵘ)) ∧ (σ + ℓᵘ)` — the first two of the three book terms, from
the `S;P` service properties (`S;P` offers min-plus `βᵐ − ℓᵘ`, maximal `βᴹ`, and is
a `(σ + ℓᵘ)`-shaper, Theorem 8.2) fed through the output-arrival theorem
`isMaximalArrivalBound_output`. The book's third term `α ⊘ δ_{hDev(α,βᵐ)}` (the
optional delay-based refinement, from Corollary 8.2) sharpens this further. -/
theorem isMaximalArrivalBound_output_comp_packetizerRel
    {S : Curve → Curve → Prop} {βm βM σ : ℝ≥0 → EReal} {αu : ℝ≥0 → ℝ≥0∞}
    {L : ℕ → ℝ≥0} {ll lu : ℝ≥0} (hL : IsPacketLengthSeq L ll lu)
    (hβm : IsMinimalServiceCurve βm S)
    (hnnm' : IsNonneg (fun v => βm v - ((lu : ℝ) : EReal)))
    (hβM : IsMaximalServiceCurve βM S) (hnnM : IsNonneg βM)
    (hsh : IsShaper σ S) (hnnσ : IsNonneg σ)
    {A D : Curve} (hp : Relation.Comp S (packetizerRel L) A D)
    (harru : IsMaximalArrivalBound (Deviation.liftENN ⇑A) αu) :
    IsMaximalArrivalBound (Deviation.liftENN ⇑D)
      (minDeconv (minConv αu (Deviation.toENN βM))
          (Deviation.toENN (fun v => βm v - ((lu : ℝ) : EReal)))
        ⊓ Deviation.toENN (fun d => σ d + ((lu : ℝ) : EReal))) :=
  isMaximalArrivalBound_output (hβm.comp_packetizerRel hL) hnnm'
    (hβM.comp_packetizerRel hL) hnnM (hsh.comp_packetizerRel hL)
    (fun d => add_nonneg (hnnσ d) (by exact_mod_cast lu.coe_nonneg)) hp harru

/-- **Corollary 8.3**, third term (the optional delay-based refinement, via Cor 8.2):
on a `P`-packetized input with the `S`-stage delay bounded by `dM` (and `S` causal),
the output `C` of `S;P` carries the maximal arrival curve `α ⊘ δ_dM` — the
deconvolution of the pure-delay service curve `δ_dM`. With `dM = hDev(α, βᵐ)` this is
the book's third Cor 8.3 term, which `⊓`-refines the main bound
(`isMaximalArrivalBound_output_comp_packetizerRel`). -/
theorem isMaximalArrivalBound_output_delay_comp_packetizerRel
    {S : Curve → Curve → Prop} {αu : ℝ≥0 → ℝ≥0∞} {dM : ℝ≥0}
    {L : ℕ → ℝ≥0} {ll lu : ℝ≥0} (hL : IsPacketLengthSeq L ll lu)
    (hSc : IsCausal S) {A C : Curve} (hA : IsPacketized L ⇑A)
    (hp : Relation.Comp S (packetizerRel L) A C)
    (hd : ∀ B : Curve, S A B → Deviation.delay ⇑A ⇑B ≤ (dM : ℝ≥0∞))
    (harru : IsMaximalArrivalBound (Deviation.liftENN ⇑A) αu) :
    IsMaximalArrivalBound (Deviation.liftENN ⇑C) (minDeconv αu (delayNN dM)) := by
  have hCA : C ≤ A := by
    obtain ⟨B, hSB, hBC⟩ := hp
    rw [(packetizerRel_iff_eq_packetizeCurve hL).mp hBC]
    exact Curve.le_def.mpr fun t =>
      le_trans (Curve.le_def.mp (packetizeCurve_le hL B) t) (Curve.le_def.mp (hSc A B hSB) t)
  set betam : ℝ≥0 → EReal := fun v => ((delayNN dM v : ℝ≥0∞) : EReal) with hbetam
  have hnnm : IsNonneg betam := fun v => EReal.coe_ennreal_nonneg _
  have htoenn : Deviation.toENN betam = delayNN dM := by
    funext v; exact EReal.toENNReal_coe
  set S' : Curve → Curve → Prop := fun A' D' => A = A' ∧ C = D' with hS'
  have hc : IsCausal S' := by rintro A' D' ⟨rfl, rfl⟩; exact hCA
  have hβm : IsMinimalServiceCurve betam S' := by
    rintro A' D' ⟨rfl, rfl⟩ t
    rw [← Deviation.coe_minConv_toENN A hnnm t, htoenn,
      conv_delayNN (Deviation.liftENN ⇑A) (Deviation.monotone_liftENN A.mono) dM]
    calc ((Deviation.liftENN ⇑A (t - dM) : ℝ≥0∞) : EReal)
        ≤ ((C t : ℝ≥0∞) : EReal) := by
          exact_mod_cast apply_tsub_le_of_isPacketized_comp_packetizerRel hL hA hp hd t
      _ = curveEReal C t := by rw [curveEReal]; rfl
  have hout := isMaximalArrivalBound_output_of_isMinimalServiceCurve hc hβm hnnm
    (A := A) (D := C) ⟨rfl, rfl⟩ harru
  rwa [htoenn] at hout

/-- **Corollary 8.3** (combined arrival curve from a packetizer), full three-term
bound: the output `C` of `S;P` (causal `S`, `P`-packetized input, `S`-stage delay
bounded by `dM`) carries the maximal arrival curve
`((α ∗ βᴹ) ⊘ (βᵐ − ℓᵘ)) ∧ (σ + ℓᵘ) ∧ (α ⊘ δ_dM)` — the meet of the main bound
(`isMaximalArrivalBound_output_comp_packetizerRel`) and the delay refinement
(`isMaximalArrivalBound_output_delay_comp_packetizerRel`), with `dM = hDev(α, βᵐ)`. -/
theorem isMaximalArrivalBound_output_full_comp_packetizerRel
    {S : Curve → Curve → Prop} {βm βM σ : ℝ≥0 → EReal} {αu : ℝ≥0 → ℝ≥0∞} {dM : ℝ≥0}
    {L : ℕ → ℝ≥0} {ll lu : ℝ≥0} (hL : IsPacketLengthSeq L ll lu) (hSc : IsCausal S)
    (hβm : IsMinimalServiceCurve βm S)
    (hnnm' : IsNonneg (fun v => βm v - ((lu : ℝ) : EReal)))
    (hβM : IsMaximalServiceCurve βM S) (hnnM : IsNonneg βM)
    (hsh : IsShaper σ S) (hnnσ : IsNonneg σ)
    {A C : Curve} (hA : IsPacketized L ⇑A)
    (hp : Relation.Comp S (packetizerRel L) A C)
    (hd : ∀ B : Curve, S A B → Deviation.delay ⇑A ⇑B ≤ (dM : ℝ≥0∞))
    (harru : IsMaximalArrivalBound (Deviation.liftENN ⇑A) αu) :
    IsMaximalArrivalBound (Deviation.liftENN ⇑C)
      ((minDeconv (minConv αu (Deviation.toENN βM))
            (Deviation.toENN (fun v => βm v - ((lu : ℝ) : EReal)))
          ⊓ Deviation.toENN (fun d => σ d + ((lu : ℝ) : EReal)))
        ⊓ minDeconv αu (delayNN dM)) :=
  (isMaximalArrivalBound_output_comp_packetizerRel hL hβm hnnm' hβM hnnM hsh hnnσ hp harru).inf
    (isMaximalArrivalBound_output_delay_comp_packetizerRel hL hSc hA hp hd harru)

/-! ## Book restatement (the server/packetizer system)
`S` a server, `P` a packetizer with maximum packet size `ℓᵘ`: the
combined system `S;P` is a server; if `S` offers a min-plus minimal
service curve `βᵐ`, a maximal service curve `βᴹ`, and is a `σ`-shaper,
then `S;P` offers `βᵐ − ℓᵘ` and `βᴹ` and is a `(σ + ℓᵘ)`-shaper; its
outputs are packetized; per pair it holds at most one extra maximal
packet of backlog; and on packetized inputs it adds no delay
(`exists_delay_eq_of_comp_packetizerRel`). `β − ℓᵘ` has no strict
counterpart
(`not_forall_isStrictMinimalServiceCurve_comp_packetizerRel` below). -/
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

/-! ## No strict counterpart
The minimal-service property has no strict analogue: `β − ℓᵘ` need not
be a strict service curve for `S;P`. The witness: unit packets, the
shifted staircase arrival `A(t) = ⌈t − 1⌉` served at `B(t) = t − 1` —
admissible for the strict `β = λ₁ ∨ β_{2,1/2}`, since every backlogged
period of `(A, B)` lies strictly between two touch points and so is
shorter than one — while the packetized output starves the combined
pair on `(1, 4]`, where `β − 1` demands four units of service. -/

/-- The unit-packet length sequence `L n = n`. -/
theorem isPacketLengthSeq_natCast :
    IsPacketLengthSeq (fun n => (n : ℝ≥0)) 1 1 :=
  ⟨Nat.cast_zero, one_pos, fun n => by push_cast; exact ⟨le_rfl, le_rfl⟩⟩

/-- The witness strict aggregate curve `λ₁ ∨ β_{2,1/2}`: rate `1` up to
`1`, rate `2` beyond. -/
noncomputable def pkWitnessBeta : ℝ≥0 → ℝ≥0 :=
  fun d => max d (2 * (d - 2⁻¹))

/-- `pkWitnessBeta d = d ⊔ 2(d − 2⁻¹)`: the pointwise reading. -/
theorem pkWitnessBeta_apply (d : ℝ≥0) :
    pkWitnessBeta d = max d (2 * (d - 2⁻¹)) := rfl

/-- `pkWitnessBeta 0 = 0`. -/
theorem pkWitnessBeta_zero_eq : pkWitnessBeta 0 = 0 := by
  rw [pkWitnessBeta_apply, zero_tsub, mul_zero, max_self]

/-- The shifted unit staircase `t ↦ ⌈t − 1⌉` is monotone. -/
theorem pkWitness_stair_mono :
    Monotone (fun t : ℝ≥0 => (⌈(t - 1 : ℝ≥0)⌉₊ : ℝ≥0)) :=
  fun _ _ hab =>
    Nat.cast_le.mpr (Nat.ceil_mono (tsub_le_tsub_right hab 1))

/-- The shifted unit staircase is left-continuous: it is constant on a
left interval ending at each point. -/
theorem pkWitness_stair_leftCont :
    IsLeftContinuous (fun t : ℝ≥0 => (⌈(t - 1 : ℝ≥0)⌉₊ : ℝ≥0)) := by
  intro t
  rcases le_or_gt t 1 with h1 | h1
  · show Filter.Tendsto _ (𝓝[<] t) (𝓝 ((⌈(t - 1 : ℝ≥0)⌉₊ : ℝ≥0)))
    rw [show (⌈(t - 1 : ℝ≥0)⌉₊ : ℝ≥0) = 0 from by
      rw [tsub_eq_zero_of_le h1, Nat.ceil_zero, Nat.cast_zero]]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [tsub_eq_zero_of_le (le_trans (le_of_lt hu) h1), Nat.ceil_zero,
      Nat.cast_zero]
  · have hx : (0 : ℝ≥0) < t - 1 := tsub_pos_of_lt h1
    have hk1 : 1 ≤ ⌈(t - 1 : ℝ≥0)⌉₊ := Nat.one_le_ceil_iff.mpr hx
    have hkt : ((⌈(t - 1 : ℝ≥0)⌉₊ : ℝ≥0)) < t := by
      have h := Nat.ceil_lt_add_one (zero_le : (0 : ℝ≥0) ≤ t - 1)
      rwa [tsub_add_cancel_of_le h1.le] at h
    show Filter.Tendsto _ (𝓝[<] t) (𝓝 ((⌈(t - 1 : ℝ≥0)⌉₊ : ℝ≥0)))
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsLT hkt] with u hu
    have hueq : ⌈(u - 1 : ℝ≥0)⌉₊ = ⌈(t - 1 : ℝ≥0)⌉₊ := by
      rw [Nat.ceil_eq_iff (Nat.one_le_iff_ne_zero.mp hk1)]
      constructor
      · have hcast : ((⌈(t - 1 : ℝ≥0)⌉₊ - 1 : ℕ) : ℝ≥0)
            = (⌈(t - 1 : ℝ≥0)⌉₊ : ℝ≥0) - 1 := by
          rw [Nat.cast_tsub, Nat.cast_one]
        rw [hcast]
        refine lt_of_lt_of_le
          (tsub_lt_tsub_right_of_le ?_ hu.1) le_rfl
        exact_mod_cast hk1
      · exact le_trans (tsub_le_tsub_right hu.2.le 1) (Nat.le_ceil _)
    rw [hueq]

/-- The witness arrival: the shifted unit staircase `t ↦ ⌈t − 1⌉`, one
unit packet just after each integer time `≥ 1`. -/
noncomputable def pkWitnessA : Curve :=
  ⟨fun t => (⌈(t - 1 : ℝ≥0)⌉₊ : ℝ≥0),
    pkWitness_stair_mono,
    by
      show (⌈((0 : ℝ≥0) - 1 : ℝ≥0)⌉₊ : ℝ≥0) = 0
      rw [zero_tsub, Nat.ceil_zero, Nat.cast_zero],
    by
      refine isPiecewiseContinuous_of_monotone_of_finite_image
        pkWitness_stair_mono pkWitness_stair_leftCont fun T => ?_
      refine Set.Finite.subset
        ((Set.finite_Iic ⌈(T - 1 : ℝ≥0)⌉₊).image
          (fun n : ℕ => (n : ℝ≥0))) ?_
      rintro x ⟨s, hs, rfl⟩
      exact ⟨⌈(s - 1 : ℝ≥0)⌉₊, Set.mem_Iic.mpr
        (Nat.ceil_mono (tsub_le_tsub_right hs.2 1)), rfl⟩,
    pkWitness_stair_leftCont⟩

/-- `pkWitnessA t = ⌈t − 1⌉`. -/
theorem pkWitnessA_apply (t : ℝ≥0) :
    pkWitnessA t = (⌈(t - 1 : ℝ≥0)⌉₊ : ℝ≥0) := rfl

/-- The witness service `t ↦ t − 1`: rate `1` after latency `1`. -/
noncomputable def pkWitnessB : Curve :=
  afterCurve 1 (fun w => w - 1)
    (fun _ _ hab => tsub_le_tsub_right hab 1)
    (continuous_sub.comp (continuous_id.prodMk continuous_const))

/-- `pkWitnessB t = t − 1`. -/
theorem pkWitnessB_apply (t : ℝ≥0) : pkWitnessB t = t - 1 := by
  rw [pkWitnessB, afterCurve_apply]
  rcases le_or_gt t 1 with h | h
  · rw [if_neg (not_lt.mpr h), tsub_eq_zero_of_le h]
  · rw [if_pos h]

/-- The witness pair is causal: `t − 1 ≤ ⌈t − 1⌉`. -/
theorem pkWitness_causal : pkWitnessB ≤ pkWitnessA := fun t => by
  rw [pkWitnessB_apply, pkWitnessA_apply]
  exact Nat.le_ceil _

/-- The witness pair obeys the strict `λ₁ ∨ β_{2,1/2}`: a backlogged
period avoids the touch points `t − 1 ∈ ℕ`, so it starts after `1`, is
shorter than one, and the service runs at exact rate `1` through it. -/
theorem pkWitness_strict :
    ∀ s t, s ≤ t →
      IsBacklogged ⇑pkWitnessA ⇑pkWitnessB (Set.Ioc s t) →
      pkWitnessB s + pkWitnessBeta (t - s) ≤ pkWitnessB t := by
  intro s t hst hbl
  rcases eq_or_lt_of_le hst with rfl | hlt
  · rw [tsub_self, pkWitnessBeta_zero_eq, add_zero]
  · have hs1 : (1 : ℝ≥0) ≤ s := by
      by_contra hs
      rw [not_le] at hs
      have hu : min 1 t ∈ Set.Ioc s t :=
        ⟨lt_min hs hlt, min_le_right _ _⟩
      have hb := hbl _ hu
      rw [pkWitnessB_apply, pkWitnessA_apply,
        tsub_eq_zero_of_le (min_le_left _ _)] at hb
      simp at hb
    have hts1 : t ≤ s + 1 := by
      by_contra hts
      rw [not_le] at hts
      set m := ⌊(s - 1 : ℝ≥0)⌋₊ with hm
      have hmem : ((m : ℝ≥0) + 2) ∈ Set.Ioc s t := by
        constructor
        · calc s = (s - 1) + 1 := (tsub_add_cancel_of_le hs1).symm
            _ < ((m : ℝ≥0) + 1) + 1 :=
              add_lt_add_left (Nat.lt_floor_add_one (s - 1 : ℝ≥0)) 1
            _ = (m : ℝ≥0) + 2 := by ring
        · refine le_trans ?_ hts.le
          calc (m : ℝ≥0) + 2 = ((m : ℝ≥0) + 1) + 1 := by ring
            _ ≤ ((s - 1) + 1) + 1 := by
              exact add_le_add (add_le_add
                (Nat.floor_le zero_le) le_rfl) le_rfl
            _ = s + 1 := by rw [tsub_add_cancel_of_le hs1]
      have hb := hbl _ hmem
      rw [pkWitnessB_apply, pkWitnessA_apply,
        show ((m : ℝ≥0) + 2) - 1 = ((m + 1 : ℕ) : ℝ≥0) from by
          push_cast
          rw [show (2 : ℝ≥0) = 1 + 1 from by norm_num, ← add_assoc,
            add_tsub_cancel_right],
        Nat.ceil_natCast] at hb
      exact absurd hb (lt_irrefl _)
    rw [pkWitnessB_apply, pkWitnessB_apply,
      show pkWitnessBeta (t - s) = t - s from by
        rw [pkWitnessBeta_apply]
        refine max_eq_left ?_
        rcases le_total (t - s) 2⁻¹ with hc | hc
        · rw [tsub_eq_zero_of_le hc, mul_zero]
          exact zero_le
        · have hx1 : t - s ≤ 1 := by
            rw [tsub_le_iff_right, add_comm]
            exact hts1
          rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_sub hc]
          have hxc : ((t - s : ℝ≥0) : ℝ) ≤ 1 := by exact_mod_cast hx1
          push_cast
          linarith]
    rw [← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub hs1, NNReal.coe_sub (le_trans hs1 hst),
      NNReal.coe_sub hst]
    linarith

/-- The witness pair sits in the largest strict server of `pkWitnessBeta`. -/
theorem pkWitness_mem_strictServiceRel :
    strictServiceRel pkWitnessBeta pkWitnessA pkWitnessB :=
  ⟨pkWitness_causal, pkWitness_strict⟩

/-- The packetized output stays a full packet below the staircase past
`1`, so the combined system is backlogged from `1` on. (The book states
the gap for all `t > 0`, but arrival and output both vanish on
`(0, 1]`; past `1` is what holds, and all the refutation needs.) -/
theorem pkWitness_packetize_lt {t : ℝ≥0} (ht : 1 < t) :
    packetize (fun n => (n : ℝ≥0)) ⇑pkWitnessB t < pkWitnessA t := by
  have hA1 : (1 : ℝ≥0) ≤ pkWitnessA t := by
    rw [pkWitnessA_apply]
    exact_mod_cast Nat.one_le_ceil_iff.mpr (tsub_pos_of_lt ht)
  refine lt_of_le_of_lt (packetize_le_of_forall ?_)
    (tsub_lt_self (lt_of_lt_of_le one_pos hA1) one_pos)
  rintro n ⟨u, hu, hn⟩
  rw [pkWitnessB_apply] at hn
  have hnlt : n < ⌈(t - 1 : ℝ≥0)⌉₊ := by
    rcases le_or_gt u 1 with h1u | h1u
    · rw [tsub_eq_zero_of_le h1u] at hn
      have hn' : (n : ℝ≥0) ≤ 0 := hn
      have hn0 : n = 0 := by exact_mod_cast le_antisymm hn' zero_le
      rw [hn0]
      exact Nat.one_le_ceil_iff.mpr (tsub_pos_of_lt ht)
    · have hn' : (n : ℝ≥0) ≤ u - 1 := hn
      have hlt : (n : ℝ≥0) < t - 1 :=
        lt_of_le_of_lt hn' (tsub_lt_tsub_right_of_le h1u.le hu)
      exact_mod_cast lt_of_lt_of_le hlt (Nat.le_ceil _)
  rw [pkWitnessA_apply]
  refine le_tsub_of_add_le_right ?_
  exact_mod_cast Nat.succ_le_of_lt hnlt

/-- The packetizer has released nothing by time `1`. -/
theorem pkWitness_packetize_one :
    packetize (fun n => (n : ℝ≥0)) ⇑pkWitnessB 1 = 0 := by
  refine le_antisymm ?_ zero_le
  have h : packetize (fun n => (n : ℝ≥0)) ⇑pkWitnessB 1 ≤ pkWitnessB 1 :=
    packetize_le pkWitnessB.mono _ 1
  rwa [pkWitnessB_apply, tsub_self] at h

/-- The packetizer has released at most two packets by time `4`. -/
theorem pkWitness_packetize_four :
    packetize (fun n => (n : ℝ≥0)) ⇑pkWitnessB 4 ≤ 2 := by
  refine packetize_le_of_forall ?_
  rintro n ⟨u, hu, hn⟩
  rw [pkWitnessB_apply] at hn
  rcases le_or_gt u 1 with h1u | h1u
  · rw [tsub_eq_zero_of_le h1u] at hn
    have hn' : (n : ℝ≥0) ≤ 0 := hn
    exact le_trans hn' (by norm_num)
  · have h3 : u - 1 < 3 := by
      rw [tsub_lt_iff_right h1u.le]
      exact lt_of_lt_of_le hu (by norm_num)
    have hn' : (n : ℝ≥0) ≤ u - 1 := hn
    have hn3 : n < 3 := by exact_mod_cast lt_of_le_of_lt hn' h3
    exact_mod_cast Nat.lt_succ_iff.mp hn3

/-- The combined witness pair is backlogged throughout `(1, 4]`. -/
theorem pkWitness_backlogged :
    IsBacklogged ⇑pkWitnessA
      ⇑(packetizeCurve isPacketLengthSeq_natCast pkWitnessB)
      (Set.Ioc 1 4) :=
  fun _ hu => pkWitness_packetize_lt hu.1

/-- The violation: on `(1, 4]` the strict `pkWitnessBeta − 1` demands four
units while the packetizer releases at most two. -/
theorem not_add_le_pkWitness :
    ¬ (packetizeCurve isPacketLengthSeq_natCast pkWitnessB 1
        + (pkWitnessBeta (4 - 1) - 1)
      ≤ packetizeCurve isPacketLengthSeq_natCast pkWitnessB 4) := by
  intro h
  rw [show (4 : ℝ≥0) - 1 = 3 from tsub_eq_of_eq_add (by norm_num),
    show pkWitnessBeta 3 - 1 = 4 from by
      rw [show pkWitnessBeta 3 = 5 from by
        rw [pkWitnessBeta_apply,
          show (3 : ℝ≥0) - 2⁻¹ = 5 / 2 from
            tsub_eq_of_eq_add (by norm_num),
          show (2 : ℝ≥0) * (5 / 2) = 5 from by norm_num]
        exact max_eq_right (by norm_num)]
      exact tsub_eq_of_eq_add (by norm_num),
    show packetizeCurve isPacketLengthSeq_natCast pkWitnessB 1
        = packetize (fun n => (n : ℝ≥0)) ⇑pkWitnessB 1 from rfl,
    pkWitness_packetize_one, zero_add] at h
  have h2 := le_trans h
    (show packetizeCurve isPacketLengthSeq_natCast pkWitnessB 4
        ≤ 2 from pkWitness_packetize_four)
  norm_num at h2

/-- **`β − ℓᵘ` has no strict counterpart**: the minimal-service
property of the server/packetizer system
(`IsMinimalServiceCurve.comp_packetizerRel`) with "min-plus" upgraded
to "strict" is false. -/
theorem not_forall_isStrictMinimalServiceCurve_comp_packetizerRel :
    ¬ ∀ (S : Curve → Curve → Prop) (β : ℝ≥0 → ℝ≥0) (L : ℕ → ℝ≥0)
      (ll lu : ℝ≥0), IsStrictMinimalServiceCurve β S →
      IsPacketLengthSeq L ll lu →
      IsStrictMinimalServiceCurve (fun v => β v - lu)
        (Relation.Comp S (packetizerRel L)) := by
  intro h
  have hbad := h (strictServiceRel pkWitnessBeta) pkWitnessBeta (fun n => (n : ℝ≥0))
    1 1 (isStrictMinimalServiceCurve_strictServiceRel pkWitnessBeta)
    isPacketLengthSeq_natCast
    pkWitnessA (packetizeCurve isPacketLengthSeq_natCast pkWitnessB)
    ⟨pkWitnessB, pkWitness_mem_strictServiceRel, rfl⟩
    1 4 (by norm_num) pkWitness_backlogged
  exact not_add_le_pkWitness hbad

end DeepWiki
