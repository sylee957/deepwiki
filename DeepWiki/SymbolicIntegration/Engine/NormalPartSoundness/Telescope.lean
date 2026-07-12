import DeepWiki.SymbolicIntegration.Engine.PolynomialBranchSoundness
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded

/-! # Hermite normal-part telescoping

Fraction-accumulator algebra and telescoping soundness for the normal-part Hermite fold.
-/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-! ### The fraction-accumulator reading through `am` -/

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The cross-multiplied fraction-add reads as a field sum through `am`:
`am(gAcc.1·gloc.2 + gloc.1·gAcc.2)/am(gAcc.2·gloc.2) = am gAcc.1/am gAcc.2 + am gloc.1/am gloc.2`. -/
theorem amG_toPolyG_fracAddG (gAcc gloc : DensePoly α × DensePoly α)
    (hAcc : toPoly gAcc.2 ≠ 0) (hloc : toPoly gloc.2 ≠ 0) :
    am α (toPoly (cadd (cmul gAcc.1 gloc.2) (cmul gloc.1 gAcc.2)))
        / am α (toPoly (cmul gAcc.2 gloc.2))
      = am α (toPoly gAcc.1) / am α (toPoly gAcc.2)
        + am α (toPoly gloc.1) / am α (toPoly gloc.2) := by
  simp only [denote, map_add, map_mul]
  rw [div_add_div _ _ (am_ne_zero hAcc) (am_ne_zero hloc)]
  ring

/-! ### `D` distributes over the Hermite `g`-accumulator fold -/

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The Hermite `g`-fold reads as `am s.1/am s.2 + ∑ am glocⱼ.1/am glocⱼ.2` through `am`, with the
running denominator staying nonzero, given a nonzero-denominator seed and contributions. -/
theorem amG_toPolyG_foldl_fracAddG :
    ∀ (glocs : List (DensePoly α × DensePoly α)) (s : DensePoly α × DensePoly α), toPoly s.2 ≠ 0 →
      (∀ g ∈ glocs, toPoly g.2 ≠ 0) →
      let res := glocs.foldl
        (fun (gAcc : DensePoly α × DensePoly α) gloc =>
          (cadd (cmul gAcc.1 gloc.2) (cmul gloc.1 gAcc.2), cmul gAcc.2 gloc.2)) s
      toPoly res.2 ≠ 0 ∧
        am α (toPoly res.1) / am α (toPoly res.2)
          = am α (toPoly s.1) / am α (toPoly s.2)
            + (glocs.map (fun g => am α (toPoly g.1) / am α (toPoly g.2))).sum := by
  intro glocs
  induction glocs with
  | nil => intro s hs _; exact ⟨hs, by simp⟩
  | cons gloc rest ih =>
    intro s hs hmem
    have hgloc : toPoly gloc.2 ≠ 0 := hmem gloc List.mem_cons_self
    set snew : DensePoly α × DensePoly α :=
      (cadd (cmul s.1 gloc.2) (cmul gloc.1 s.2), cmul s.2 gloc.2) with hsnew
    have hsnew_ne : toPoly snew.2 ≠ 0 := by
      rw [hsnew]; show toPoly (cmul s.2 gloc.2) ≠ 0
      simpa only [denote] using mul_ne_zero hs hgloc
    have hrest : ∀ g ∈ rest, toPoly g.2 ≠ 0 := fun g hg => hmem g (List.mem_cons_of_mem _ hg)
    obtain ⟨hden, heq⟩ := ih snew hsnew_ne hrest
    refine ⟨by simpa only [List.foldl_cons] using hden, ?_⟩
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [heq]
    have hstep : am α (toPoly snew.1) / am α (toPoly snew.2)
        = am α (toPoly s.1) / am α (toPoly s.2)
          + am α (toPoly gloc.1) / am α (toPoly gloc.2) := by
      rw [hsnew]; exact amG_toPolyG_fracAddG s gloc hs hgloc
    rw [hstep]; ring

/-- `towerFractionFieldDeriv Dt` distributes over the Hermite `g`-fold:
`D(am(fold).1/am(fold).2) = D(am s.1/am s.2) + ∑ⱼ D(am glocⱼ.1/am glocⱼ.2)`. -/
theorem towerFractionFieldDerivG_amG_fracAccG (Dt : DensePoly α) (s : DensePoly α × DensePoly α)
    (glocs : List (DensePoly α × DensePoly α)) (hs : toPoly s.2 ≠ 0)
    (hmem : ∀ g ∈ glocs, toPoly g.2 ≠ 0) :
    let res := glocs.foldl
      (fun (gAcc : DensePoly α × DensePoly α) gloc =>
        (cadd (cmul gAcc.1 gloc.2) (cmul gloc.1 gAcc.2), cmul gAcc.2 gloc.2)) s
    towerFractionFieldDeriv Dt (am α (toPoly res.1) / am α (toPoly res.2))
      = towerFractionFieldDeriv Dt (am α (toPoly s.1) / am α (toPoly s.2))
        + (glocs.map (fun g =>
            towerFractionFieldDeriv Dt (am α (toPoly g.1) / am α (toPoly g.2)))).sum := by
  intro res
  obtain ⟨_, heq⟩ := amG_toPolyG_foldl_fracAddG glocs s hs hmem
  show towerFractionFieldDeriv Dt (am α (toPoly res.1) / am α (toPoly res.2)) = _
  rw [heq, map_add]
  congr 1
  rw [map_list_sum, List.map_map]
  rfl

/-! ### The per-step contributions telescope -/

/-- The per-step contributions telescope: if each `glocⱼ` satisfies the per-power identity
`D(am g.1/am g.2) = am p.1.1/am p.1.2 − am p.2.1/am p.2.2` against `(L₀ :: rest).zip rest`, then
`∑ⱼ D(am glocⱼ) = am L₀.1/am L₀.2 − am (rest.getLastD L₀).1/am (rest.getLastD L₀).2`. -/
theorem sum_towerFractionFieldDerivG_telescope (Dt : DensePoly α) :
    ∀ (L₀ : DensePoly α × DensePoly α) (rest glocs : List (DensePoly α × DensePoly α)),
      List.Forall₂ (fun g p =>
          towerFractionFieldDeriv Dt (am α (toPoly g.1) / am α (toPoly g.2))
            = am α (toPoly (Prod.fst p).1) / am α (toPoly (Prod.fst p).2)
              - am α (toPoly (Prod.snd p).1) / am α (toPoly (Prod.snd p).2))
          glocs ((L₀ :: rest).zip rest) →
      (glocs.map (fun g =>
          towerFractionFieldDeriv Dt (am α (toPoly g.1) / am α (toPoly g.2)))).sum
        = am α (toPoly L₀.1) / am α (toPoly L₀.2)
          - am α (toPoly (rest.getLastD L₀).1) / am α (toPoly (rest.getLastD L₀).2) := by
  intro L₀ rest
  induction rest generalizing L₀ with
  | nil =>
    intro glocs hforall
    simp only [List.zip_nil_right] at hforall
    rw [List.forall₂_nil_right_iff] at hforall
    subst hforall
    simp
  | cons L₁ rest' ih =>
    intro glocs hforall
    rw [List.zip_cons_cons] at hforall
    rw [List.forall₂_cons_right_iff] at hforall
    obtain ⟨g, glocs', h0, htail, rfl⟩ := hforall
    rw [List.map_cons, List.sum_cons, ih L₁ glocs' htail, h0]
    rw [List.getLastD_cons]
    ring

/-! ### The master Hermite telescoping soundness over the tower -/

/-- Master Hermite telescoping soundness: given a seed `s` with vanishing field derivative, leftover
chain `L₀ :: rest` (`L₀ = a/d`, `rest.getLastD L₀ = h`), and each contribution's per-power identity
`D(am glocⱼ) = am Lⱼ − am Lⱼ₊₁`, the assembled `g = glocs.foldl (fraction-add) s` satisfies
`D(g) + h = a/d`. -/
theorem cHermiteReduceTowerG_telescope (Dt : DensePoly α) (s : DensePoly α × DensePoly α)
    (L₀ : DensePoly α × DensePoly α) (rest glocs : List (DensePoly α × DensePoly α))
    (hs : toPoly s.2 ≠ 0) (hmem : ∀ g ∈ glocs, toPoly g.2 ≠ 0)
    (hseed : towerFractionFieldDeriv Dt (am α (toPoly s.1) / am α (toPoly s.2)) = 0)
    (hstep : List.Forall₂ (fun g p =>
        towerFractionFieldDeriv Dt (am α (toPoly g.1) / am α (toPoly g.2))
          = am α (toPoly (Prod.fst p).1) / am α (toPoly (Prod.fst p).2)
            - am α (toPoly (Prod.snd p).1) / am α (toPoly (Prod.snd p).2))
        glocs ((L₀ :: rest).zip rest)) :
    towerFractionFieldDeriv Dt
        (am α (toPoly (glocs.foldl
            (fun (gAcc : DensePoly α × DensePoly α) gloc =>
              (cadd (cmul gAcc.1 gloc.2) (cmul gloc.1 gAcc.2), cmul gAcc.2 gloc.2)) s).1)
          / am α (toPoly (glocs.foldl
            (fun (gAcc : DensePoly α × DensePoly α) gloc =>
              (cadd (cmul gAcc.1 gloc.2) (cmul gloc.1 gAcc.2), cmul gAcc.2 gloc.2)) s).2))
        + am α (toPoly (rest.getLastD L₀).1) / am α (toPoly (rest.getLastD L₀).2)
      = am α (toPoly L₀.1) / am α (toPoly L₀.2) := by
  have hfold := towerFractionFieldDerivG_amG_fracAccG Dt s glocs hs hmem
  simp only at hfold ⊢
  rw [hfold, hseed, zero_add,
    sum_towerFractionFieldDerivG_telescope Dt L₀ rest glocs hstep]
  ring

/-! ### The seed derivative vanishes (`0/1`) -/

/-- The Hermite seed `([CCommRing.zero], [CCommRing.one])` reads as `0/1 = 0`, so its field derivative
vanishes: `towerFractionFieldDeriv Dt (am 0 / am 1) = 0`. -/
theorem towerFractionFieldDerivG_amG_seed (Dt : DensePoly α) :
    towerFractionFieldDeriv Dt
        (am α (toPoly ([CCommRing.zero] : DensePoly α)) / am α (toPoly ([CCommRing.one] : DensePoly α))) = 0 := by
  have hzero : am α (toPoly ([CCommRing.zero] : DensePoly α)) = 0 := by
    simp only [denote, map_zero, mul_zero, add_zero]
  rw [hzero, zero_div, map_zero]

/-! ### The Hermite telescoping at the engine seed `0/1` -/

/-- The Hermite telescoping at the seed `([CCommRing.zero], [CCommRing.one])`: `D(g) + h = a/d` for the `g`
accumulated by the `g`-fold, given the per-power identities `hstep` and the leftover chain `L₀ :: rest`. -/
theorem cHermiteReduceTowerG_telescope_seed (Dt : DensePoly α)
    (L₀ : DensePoly α × DensePoly α) (rest glocs : List (DensePoly α × DensePoly α))
    (hmem : ∀ g ∈ glocs, toPoly g.2 ≠ 0)
    (hstep : List.Forall₂ (fun g p =>
        towerFractionFieldDeriv Dt (am α (toPoly g.1) / am α (toPoly g.2))
          = am α (toPoly (Prod.fst p).1) / am α (toPoly (Prod.fst p).2)
            - am α (toPoly (Prod.snd p).1) / am α (toPoly (Prod.snd p).2))
        glocs ((L₀ :: rest).zip rest)) :
    towerFractionFieldDeriv Dt
        (am α (toPoly (glocs.foldl
            (fun (gAcc : DensePoly α × DensePoly α) gloc =>
              (cadd (cmul gAcc.1 gloc.2) (cmul gloc.1 gAcc.2), cmul gAcc.2 gloc.2))
            (([CCommRing.zero] : DensePoly α), ([CCommRing.one] : DensePoly α))).1)
          / am α (toPoly (glocs.foldl
            (fun (gAcc : DensePoly α × DensePoly α) gloc =>
              (cadd (cmul gAcc.1 gloc.2) (cmul gloc.1 gAcc.2), cmul gAcc.2 gloc.2))
            (([CCommRing.zero] : DensePoly α), ([CCommRing.one] : DensePoly α))).2))
        + am α (toPoly (rest.getLastD L₀).1) / am α (toPoly (rest.getLastD L₀).2)
      = am α (toPoly L₀.1) / am α (toPoly L₀.2) :=
  cHermiteReduceTowerG_telescope Dt (([CCommRing.zero] : DensePoly α), ([CCommRing.one] : DensePoly α))
    L₀ rest glocs DensePoly.toPolyG_one_singleton_ne_zero hmem (towerFractionFieldDerivG_amG_seed Dt) hstep

end DeepWiki.SymbolicIntegration
