import Book.Packetizer
import Book.ServersConcatenation
import Book.ArrivalCurvesShaper
import Book.ServiceCurveMaximal
import Book.Deviations

/-! # A server followed by a packetizer
The combined system `S;P`: the packetizer costs one maximal packet on
the minimal service curve (`β − ℓᵘ`), nothing on the maximal one, one
packet on the shaping curve (`σ + ℓᵘ`) and on the backlog, and its
outputs are packetized. -/

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

/-- The real difference is below the truncated difference, read in
`EReal`: `↑a − ↑b ≤ ↑(a ⊖ b)`. -/
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
theorem isMinimalServiceCurve_comp_packetizerRel
    {S : Curve → Curve → Prop} {β : ℝ≥0 → EReal}
    {L : ℕ → ℝ≥0} {ll lu : ℝ≥0} (hL : IsPacketLengthSeq L ll lu)
    (hβ : IsMinimalServiceCurve β S) :
    IsMinimalServiceCurve (fun v => β v - ((lu : ℝ) : EReal))
      (Relation.Comp S (packetizerRel hL)) := by
  rintro A C ⟨B, hSB, rfl⟩
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
theorem isMaximalServiceCurve_comp_packetizerRel
    {S : Curve → Curve → Prop} {β : ℝ≥0 → EReal}
    {L : ℕ → ℝ≥0} {ll lu : ℝ≥0} (hL : IsPacketLengthSeq L ll lu)
    (hβ : IsMaximalServiceCurve β S) :
    IsMaximalServiceCurve β (Relation.Comp S (packetizerRel hL)) := by
  rintro A C ⟨B, hSB, rfl⟩
  exact le_trans (curveEReal_mono (packetizeCurve_le hL B)) (hβ A B hSB)

/-- Sandwich transport at the `EReal` reading: a curve within `c` below
`A` keeps `A`'s maximal arrival bound up to `+ c`. -/
theorem isMaximalArrivalBound_curveEReal_of_sandwich {A D : Curve}
    {σ : ℝ≥0 → EReal} {c : ℝ≥0}
    (hc : ∀ t, D t ≤ A t) (hsand : ∀ t, A t ≤ D t + c)
    (h : IsMaximalArrivalBound (curveEReal A) σ) :
    IsMaximalArrivalBound (curveEReal D)
      (fun d => σ d + ((c : ℝ) : EReal)) := by
  rw [isMaximalArrivalBound_iff_increment] at h ⊢
  intro t d
  calc curveEReal D (t + d) ≤ curveEReal A (t + d) := by
        rw [curveEReal_apply, curveEReal_apply]
        exact_mod_cast hc (t + d)
    _ ≤ curveEReal A t + σ d := h t d
    _ ≤ (curveEReal D t + ((c : ℝ) : EReal)) + σ d := by
        refine add_le_add ?_ le_rfl
        rw [curveEReal_apply, curveEReal_apply, ← EReal.coe_add]
        exact_mod_cast hsand t
    _ = curveEReal D t + (σ d + ((c : ℝ) : EReal)) := by
        rw [add_assoc, add_comm ((c : ℝ) : EReal) (σ d)]

/-- **Shaping through a packetizer**: `S;P` is a `(σ + ℓᵘ)`-shaper when
`S` is a `σ`-shaper. -/
theorem isShaper_comp_packetizerRel {S : Curve → Curve → Prop}
    {σ : ℝ≥0 → EReal} {L : ℕ → ℝ≥0} {ll lu : ℝ≥0}
    (hL : IsPacketLengthSeq L ll lu) (hS : IsShaper σ S) :
    IsShaper (fun d => σ d + ((lu : ℝ) : EReal))
      (Relation.Comp S (packetizerRel hL)) := by
  rintro A C ⟨B, hSB, rfl⟩
  exact isMaximalArrivalBound_curveEReal_of_sandwich
    (fun t => (packetizeCurve_sandwich hL B t).2)
    (fun t => apply_le_packetize_add hL B.mono (B.zero : B 0 = 0)
      B.leftCont t)
    (hS A B hSB)

/-- **The combined system's outputs are packetized.** -/
theorem isPacketized_of_comp_packetizerRel {S : Curve → Curve → Prop}
    {L : ℕ → ℝ≥0} {ll lu : ℝ≥0} (hL : IsPacketLengthSeq L ll lu)
    {A C : Curve} (hp : Relation.Comp S (packetizerRel hL) A C) :
    IsPacketized L ⇑C := by
  obtain ⟨B, _, rfl⟩ := hp
  exact isPacketized_packetize B.mono

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

/-! ## Book restatement (the server/packetizer system)
`S` a server, `P` a packetizer with maximum packet size `ℓᵘ`: the
combined system `S;P` is a server; if `S` offers a min-plus minimal
service curve `βᵐ`, a maximal service curve `βᴹ`, and is a `σ`-shaper,
then `S;P` offers `βᵐ − ℓᵘ` and `βᴹ` and is a `(σ + ℓᵘ)`-shaper; its
outputs are packetized; and per pair it holds at most one extra
maximal packet of backlog. (The delay-preservation property for
packetized inputs is the remaining piece.) -/
example {S : Curve → Curve → Prop} {βm βM σ : ℝ≥0 → EReal}
    {L : ℕ → ℝ≥0} {ll lu : ℝ≥0} (hL : IsPacketLengthSeq L ll lu)
    (hSrv : IsServer S) (hβm : IsMinimalServiceCurve βm S)
    (hβM : IsMaximalServiceCurve βM S) (hsh : IsShaper σ S) :
    IsServer (Relation.Comp S (packetizerRel hL))
      ∧ IsMinimalServiceCurve (fun v => βm v - ((lu : ℝ) : EReal))
          (Relation.Comp S (packetizerRel hL))
      ∧ IsMaximalServiceCurve βM (Relation.Comp S (packetizerRel hL))
      ∧ IsShaper (fun d => σ d + ((lu : ℝ) : EReal))
          (Relation.Comp S (packetizerRel hL))
      ∧ ∀ A C, Relation.Comp S (packetizerRel hL) A C →
          IsPacketized L ⇑C :=
  ⟨hSrv.comp (isServer_packetizerRel hL),
    isMinimalServiceCurve_comp_packetizerRel hL hβm,
    isMaximalServiceCurve_comp_packetizerRel hL hβM,
    isShaper_comp_packetizerRel hL hsh,
    fun _ _ hp => isPacketized_of_comp_packetizerRel hL hp⟩

end DeepWiki
