import DeepWiki.SymbolicIntegration.Engine.OneShotSoundness
import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded

/-! # Hermite normal-part telescoping

Fraction-accumulator algebra and telescoping soundness for the normal-part Hermite fold.
-/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-! ### The fraction-accumulator reading through `amG` -/

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The cross-multiplied fraction-add reads as a field sum through `amG`:
`amG(gAcc.1·gloc.2 + gloc.1·gAcc.2)/amG(gAcc.2·gloc.2) = amG gAcc.1/amG gAcc.2 + amG gloc.1/amG gloc.2`. -/
theorem amG_toPolyG_fracAddG (gAcc gloc : CPolyG α × CPolyG α)
    (hAcc : toPolyG gAcc.2 ≠ 0) (hloc : toPolyG gloc.2 ≠ 0) :
    amG α (toPolyG (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2)))
        / amG α (toPolyG (cmulG gAcc.2 gloc.2))
      = amG α (toPolyG gAcc.1) / amG α (toPolyG gAcc.2)
        + amG α (toPolyG gloc.1) / amG α (toPolyG gloc.2) := by
  simp only [denote, map_add, map_mul]
  rw [div_add_div _ _ (amG_toPolyG_ne_zero hAcc) (amG_toPolyG_ne_zero hloc)]
  ring

/-! ### `D` distributes over the Hermite `g`-accumulator fold -/

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The Hermite `g`-fold reads as `amG s.1/amG s.2 + ∑ amG glocⱼ.1/amG glocⱼ.2` through `amG`, with the
running denominator staying nonzero, given a nonzero-denominator seed and contributions. -/
theorem amG_toPolyG_foldl_fracAddG :
    ∀ (glocs : List (CPolyG α × CPolyG α)) (s : CPolyG α × CPolyG α), toPolyG s.2 ≠ 0 →
      (∀ g ∈ glocs, toPolyG g.2 ≠ 0) →
      let res := glocs.foldl
        (fun (gAcc : CPolyG α × CPolyG α) gloc =>
          (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2)) s
      toPolyG res.2 ≠ 0 ∧
        amG α (toPolyG res.1) / amG α (toPolyG res.2)
          = amG α (toPolyG s.1) / amG α (toPolyG s.2)
            + (glocs.map (fun g => amG α (toPolyG g.1) / amG α (toPolyG g.2))).sum := by
  intro glocs
  induction glocs with
  | nil => intro s hs _; exact ⟨hs, by simp⟩
  | cons gloc rest ih =>
    intro s hs hmem
    have hgloc : toPolyG gloc.2 ≠ 0 := hmem gloc List.mem_cons_self
    set snew : CPolyG α × CPolyG α :=
      (caddG (cmulG s.1 gloc.2) (cmulG gloc.1 s.2), cmulG s.2 gloc.2) with hsnew
    have hsnew_ne : toPolyG snew.2 ≠ 0 := by
      rw [hsnew]; show toPolyG (cmulG s.2 gloc.2) ≠ 0
      simpa only [denote] using mul_ne_zero hs hgloc
    have hrest : ∀ g ∈ rest, toPolyG g.2 ≠ 0 := fun g hg => hmem g (List.mem_cons_of_mem _ hg)
    obtain ⟨hden, heq⟩ := ih snew hsnew_ne hrest
    refine ⟨by simpa only [List.foldl_cons] using hden, ?_⟩
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [heq]
    have hstep : amG α (toPolyG snew.1) / amG α (toPolyG snew.2)
        = amG α (toPolyG s.1) / amG α (toPolyG s.2)
          + amG α (toPolyG gloc.1) / amG α (toPolyG gloc.2) := by
      rw [hsnew]; exact amG_toPolyG_fracAddG s gloc hs hgloc
    rw [hstep]; ring

/-- `towerFractionFieldDerivG Dt` distributes over the Hermite `g`-fold:
`D(amG(fold).1/amG(fold).2) = D(amG s.1/amG s.2) + ∑ⱼ D(amG glocⱼ.1/amG glocⱼ.2)`. -/
theorem towerFractionFieldDerivG_amG_fracAccG (Dt : CPolyG α) (s : CPolyG α × CPolyG α)
    (glocs : List (CPolyG α × CPolyG α)) (hs : toPolyG s.2 ≠ 0)
    (hmem : ∀ g ∈ glocs, toPolyG g.2 ≠ 0) :
    let res := glocs.foldl
      (fun (gAcc : CPolyG α × CPolyG α) gloc =>
        (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2)) s
    towerFractionFieldDerivG Dt (amG α (toPolyG res.1) / amG α (toPolyG res.2))
      = towerFractionFieldDerivG Dt (amG α (toPolyG s.1) / amG α (toPolyG s.2))
        + (glocs.map (fun g =>
            towerFractionFieldDerivG Dt (amG α (toPolyG g.1) / amG α (toPolyG g.2)))).sum := by
  intro res
  obtain ⟨_, heq⟩ := amG_toPolyG_foldl_fracAddG glocs s hs hmem
  show towerFractionFieldDerivG Dt (amG α (toPolyG res.1) / amG α (toPolyG res.2)) = _
  rw [heq, map_add]
  congr 1
  rw [map_list_sum, List.map_map]
  rfl

/-! ### The per-step contributions telescope -/

/-- The per-step contributions telescope: if each `glocⱼ` satisfies the per-power identity
`D(amG g.1/amG g.2) = amG p.1.1/amG p.1.2 − amG p.2.1/amG p.2.2` against `(L₀ :: rest).zip rest`, then
`∑ⱼ D(amG glocⱼ) = amG L₀.1/amG L₀.2 − amG (rest.getLastD L₀).1/amG (rest.getLastD L₀).2`. -/
theorem sum_towerFractionFieldDerivG_telescope (Dt : CPolyG α) :
    ∀ (L₀ : CPolyG α × CPolyG α) (rest glocs : List (CPolyG α × CPolyG α)),
      List.Forall₂ (fun g p =>
          towerFractionFieldDerivG Dt (amG α (toPolyG g.1) / amG α (toPolyG g.2))
            = amG α (toPolyG (Prod.fst p).1) / amG α (toPolyG (Prod.fst p).2)
              - amG α (toPolyG (Prod.snd p).1) / amG α (toPolyG (Prod.snd p).2))
          glocs ((L₀ :: rest).zip rest) →
      (glocs.map (fun g =>
          towerFractionFieldDerivG Dt (amG α (toPolyG g.1) / amG α (toPolyG g.2)))).sum
        = amG α (toPolyG L₀.1) / amG α (toPolyG L₀.2)
          - amG α (toPolyG (rest.getLastD L₀).1) / amG α (toPolyG (rest.getLastD L₀).2) := by
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
`D(amG glocⱼ) = amG Lⱼ − amG Lⱼ₊₁`, the assembled `g = glocs.foldl (fraction-add) s` satisfies
`D(g) + h = a/d`. -/
theorem cHermiteReduceTowerG_telescope (Dt : CPolyG α) (s : CPolyG α × CPolyG α)
    (L₀ : CPolyG α × CPolyG α) (rest glocs : List (CPolyG α × CPolyG α))
    (hs : toPolyG s.2 ≠ 0) (hmem : ∀ g ∈ glocs, toPolyG g.2 ≠ 0)
    (hseed : towerFractionFieldDerivG Dt (amG α (toPolyG s.1) / amG α (toPolyG s.2)) = 0)
    (hstep : List.Forall₂ (fun g p =>
        towerFractionFieldDerivG Dt (amG α (toPolyG g.1) / amG α (toPolyG g.2))
          = amG α (toPolyG (Prod.fst p).1) / amG α (toPolyG (Prod.fst p).2)
            - amG α (toPolyG (Prod.snd p).1) / amG α (toPolyG (Prod.snd p).2))
        glocs ((L₀ :: rest).zip rest)) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG (glocs.foldl
            (fun (gAcc : CPolyG α × CPolyG α) gloc =>
              (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2)) s).1)
          / amG α (toPolyG (glocs.foldl
            (fun (gAcc : CPolyG α × CPolyG α) gloc =>
              (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2)) s).2))
        + amG α (toPolyG (rest.getLastD L₀).1) / amG α (toPolyG (rest.getLastD L₀).2)
      = amG α (toPolyG L₀.1) / amG α (toPolyG L₀.2) := by
  have hfold := towerFractionFieldDerivG_amG_fracAccG Dt s glocs hs hmem
  simp only at hfold ⊢
  rw [hfold, hseed, zero_add,
    sum_towerFractionFieldDerivG_telescope Dt L₀ rest glocs hstep]
  ring

/-! ### The seed derivative vanishes (`0/1`) -/

/-- The Hermite seed `([CField.zero], [CField.one])` reads as `0/1 = 0`, so its field derivative
vanishes: `towerFractionFieldDerivG Dt (amG 0 / amG 1) = 0`. -/
theorem towerFractionFieldDerivG_amG_seed (Dt : CPolyG α) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG ([CField.zero] : CPolyG α)) / amG α (toPolyG ([CField.one] : CPolyG α))) = 0 := by
  have hzero : amG α (toPolyG ([CField.zero] : CPolyG α)) = 0 := by
    simp only [denote, map_zero, mul_zero, add_zero]
  rw [hzero, zero_div, map_zero]

/-! ### The Hermite telescoping at the engine seed `0/1` -/

/-- The Hermite telescoping at the seed `([CField.zero], [CField.one])`: `D(g) + h = a/d` for the `g`
accumulated by the `g`-fold, given the per-power identities `hstep` and the leftover chain `L₀ :: rest`. -/
theorem cHermiteReduceTowerG_telescope_seed (Dt : CPolyG α)
    (L₀ : CPolyG α × CPolyG α) (rest glocs : List (CPolyG α × CPolyG α))
    (hmem : ∀ g ∈ glocs, toPolyG g.2 ≠ 0)
    (hstep : List.Forall₂ (fun g p =>
        towerFractionFieldDerivG Dt (amG α (toPolyG g.1) / amG α (toPolyG g.2))
          = amG α (toPolyG (Prod.fst p).1) / amG α (toPolyG (Prod.fst p).2)
            - amG α (toPolyG (Prod.snd p).1) / amG α (toPolyG (Prod.snd p).2))
        glocs ((L₀ :: rest).zip rest)) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG (glocs.foldl
            (fun (gAcc : CPolyG α × CPolyG α) gloc =>
              (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
            (([CField.zero] : CPolyG α), ([CField.one] : CPolyG α))).1)
          / amG α (toPolyG (glocs.foldl
            (fun (gAcc : CPolyG α × CPolyG α) gloc =>
              (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
            (([CField.zero] : CPolyG α), ([CField.one] : CPolyG α))).2))
        + amG α (toPolyG (rest.getLastD L₀).1) / amG α (toPolyG (rest.getLastD L₀).2)
      = amG α (toPolyG L₀.1) / amG α (toPolyG L₀.2) :=
  cHermiteReduceTowerG_telescope Dt (([CField.zero] : CPolyG α), ([CField.one] : CPolyG α))
    L₀ rest glocs CPolyG.toPolyG_one_singleton_ne_zero hmem (towerFractionFieldDerivG_amG_seed Dt) hstep

end DeepWiki.SymbolicIntegration
