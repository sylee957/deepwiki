import DeepWiki.SymbolicIntegration.Engine.NormalPartSoundness

/-! # Normal-part soundness examples

Level-1 specialization and anonymous restatements for the normal-part soundness API.
-/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open CPoly QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-! ### The deliverables at the level-1 carrier `α = QFunNZG ℚ = ℚ(x)` -/

/-- The engine carrier `CFieldSpec.K (QFunNZG ℚ)` is `RatFunc ℚ`, a `ℚ`-algebra. Local instance so the
`QFunNZG ℚ` deliverables synthesize the **same** `Algebra ℚ` the bridge `towerFractionFieldDerivG` uses. -/
noncomputable local instance normalPartSoundnessExamplesAlgebraRatKQFunNZG :
    Algebra ℚ (CFieldSpec.K (QFunNZG ℚ)) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- The Hermite half over `ℚ(x)(t)`: the master Hermite telescoping `D(g) + h = a/d` (seed
`([CField.zero], [CField.one])`) at the carrier `α = QFunNZG ℚ`, over `RatFunc ℚ`. -/
theorem cHermiteReduceTowerG_telescope_seed_qfunNZG (Dt : CPoly (QFunNZG ℚ))
    (L₀ : CPoly (QFunNZG ℚ) × CPoly (QFunNZG ℚ))
    (rest glocs : List (CPoly (QFunNZG ℚ) × CPoly (QFunNZG ℚ)))
    (hmem : ∀ g ∈ glocs, toPolyG g.2 ≠ 0)
    (hstep : List.Forall₂ (fun g p =>
        towerFractionFieldDerivG Dt (amG (QFunNZG ℚ) (toPolyG g.1) / amG (QFunNZG ℚ) (toPolyG g.2))
          = amG (QFunNZG ℚ) (toPolyG (Prod.fst p).1) / amG (QFunNZG ℚ) (toPolyG (Prod.fst p).2)
            - amG (QFunNZG ℚ) (toPolyG (Prod.snd p).1) / amG (QFunNZG ℚ) (toPolyG (Prod.snd p).2))
        glocs ((L₀ :: rest).zip rest)) :
    towerFractionFieldDerivG Dt
        (amG (QFunNZG ℚ) (toPolyG (glocs.foldl
            (fun (gAcc : CPoly (QFunNZG ℚ) × CPoly (QFunNZG ℚ)) gloc =>
              (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
            (([CField.zero] : CPoly (QFunNZG ℚ)), ([CField.one] : CPoly (QFunNZG ℚ)))).1)
          / amG (QFunNZG ℚ) (toPolyG (glocs.foldl
            (fun (gAcc : CPoly (QFunNZG ℚ) × CPoly (QFunNZG ℚ)) gloc =>
              (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
            (([CField.zero] : CPoly (QFunNZG ℚ)), ([CField.one] : CPoly (QFunNZG ℚ)))).2))
        + amG (QFunNZG ℚ) (toPolyG (rest.getLastD L₀).1)
          / amG (QFunNZG ℚ) (toPolyG (rest.getLastD L₀).2)
      = amG (QFunNZG ℚ) (toPolyG L₀.1) / amG (QFunNZG ℚ) (toPolyG L₀.2) :=
  cHermiteReduceTowerG_telescope_seed Dt L₀ rest glocs hmem hstep

/-! ### Restatements against the intended wording (anonymous `example`s) -/

example {K : Type*} [Field K] {H D2 N S : K[X]}
    (hid : H * D2 = N * S) (hND : N.degree < D2.degree) (hS : S ≠ 0) :
    H.degree < S.degree :=
  degree_lt_of_exact_div hid hND hS

example [CFracGcdCoreWf α] (Dt : CPoly α) (a d : CPoly α) (resNum resDen Dstar : CPoly α)
    (hnum : toPolyG (CPoly.cHermiteReduceTowerG Dt a d).2.1
      = toPolyG (cdivWf (cmulG resNum Dstar) resDen))
    (hden : toPolyG (CPoly.cHermiteReduceTowerG Dt a d).2.2 = toPolyG Dstar)
    (hdvd : toPolyG resDen ∣ toPolyG (cmulG resNum Dstar))
    (hresDen : cnormG resDen ≠ []) (hDstar : toPolyG Dstar ≠ 0)
    (hresProper : (toPolyG resNum).degree < (toPolyG resDen).degree) :
    (toPolyG (CPoly.cHermiteReduceTowerG Dt a d).2.1).degree
      < (toPolyG (CPoly.cHermiteReduceTowerG Dt a d).2.2).degree :=
  cHermiteReduceTowerG_leftover_proper_of_residual Dt a d resNum resDen Dstar
    hnum hden hdvd hresDen hDstar hresProper

example {β : Type*} (glocOf : β → CPoly α × CPoly α) (skip : β → Prop) [DecidablePred skip]
    (xs : List β) (s : CPoly α × CPoly α) (hs : (toPolyG s.1).degree < (toPolyG s.2).degree)
    (hmem : ∀ b ∈ xs, ¬ skip b → (toPolyG (glocOf b).1).degree < (toPolyG (glocOf b).2).degree) :
    (toPolyG (xs.foldl
        (fun (gAcc : CPoly α × CPoly α) (b : β) =>
          if skip b then gAcc
          else (caddG (cmulG gAcc.1 (glocOf b).2) (cmulG (glocOf b).1 gAcc.2),
                cmulG gAcc.2 (glocOf b).2)) s).1).degree
      < (toPolyG (xs.foldl
        (fun (gAcc : CPoly α × CPoly α) (b : β) =>
          if skip b then gAcc
          else (caddG (cmulG gAcc.1 (glocOf b).2) (cmulG (glocOf b).1 gAcc.2),
                cmulG gAcc.2 (glocOf b).2)) s).2).degree :=
  foldl_guarded_fracAddG_proper glocOf skip xs s hs hmem

example (Dt : CPoly α) (v u : CPoly α) (hv : toPolyG v ≠ 0)
    (hb : ∀ (rhs : CPoly α),
      (toPolyG (cdiophantineG (cmulG u (cmonomialDeriv Dt v)) v rhs).1).degree
        < (toPolyG v).degree)
    (j : ℕ) (a : CPoly α) (g : CPoly α × CPoly α)
    (hg : (toPolyG g.1).degree < (toPolyG g.2).degree) :
    (toPolyG (cHermiteReduceTowerInnerWf Dt v u j a g).1.1).degree
      < (toPolyG (cHermiteReduceTowerInnerWf Dt v u j a g).1.2).degree :=
  cHermiteReduceTowerInner_g_proper Dt v u ⟨hv, hb⟩ j a g hg

example (Dt : CPoly α) (vi u : CPoly α) (j : ℕ) (a : CPoly α) (hv : toPolyG vi ≠ 0)
    (hb : ∀ (rhs : CPoly α),
      (toPolyG (cdiophantineG (cmulG u (cmonomialDeriv Dt vi)) vi rhs).1).degree
        < (toPolyG vi).degree) :
    (toPolyG (cHermiteReduceTowerInnerWf Dt vi u j a ([CField.zero], [CField.one])).1.1).degree
      < (toPolyG (cHermiteReduceTowerInnerWf Dt vi u j a ([CField.zero], [CField.one])).1.2).degree :=
  cHermiteReduceTowerInner_gloc_proper Dt vi u j a ⟨hv, hb⟩

example (Dt : CPoly α) (a d : CPoly α) (factors : List (CPoly α))
    (hv : ∀ p ∈ factors.zipIdx, ¬ (p.2 + 1 ≤ 1) → toPolyG p.1 ≠ 0)
    (hb : ∀ p ∈ factors.zipIdx, ¬ (p.2 + 1 ≤ 1) → ∀ (rhs : CPoly α),
      (toPolyG (cdiophantineG
          (cmulG (cdivWf d (cpowG p.1 (p.2 + 1))) (cmonomialDeriv Dt p.1)) p.1 rhs).1).degree
        < (toPolyG p.1).degree) :
    (toPolyG (factors.zipIdx.foldl
        (fun (gAcc : CPoly α × CPoly α) (vi, idx) =>
          let i := idx + 1
          if i ≤ 1 then gAcc
          else
            let Vi_pow := cpowG vi i
            let u := cdivWf d Vi_pow
            let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a
              ([CField.zero], [CField.one])).1
            (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
        ([CField.zero], [CField.one])).1).degree
      < (toPolyG (factors.zipIdx.foldl
        (fun (gAcc : CPoly α × CPoly α) (vi, idx) =>
          let i := idx + 1
          if i ≤ 1 then gAcc
          else
            let Vi_pow := cpowG vi i
            let u := cdivWf d Vi_pow
            let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a
              ([CField.zero], [CField.one])).1
            (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
        ([CField.zero], [CField.one])).2).degree :=
  cHermiteReduceTowerG_g_proper Dt a d factors (fun p hp hskip => ⟨hv p hp hskip, hb p hp hskip⟩)

example (Dt : CPoly α) (a d : CPoly α) (factors : List (CPoly α))
    (hDt : (toPolyG Dt).natDegree ≤ 1) (haProper : (toPolyG a).degree < (toPolyG d).degree)
    (hv : ∀ p ∈ factors.zipIdx, ¬ (p.2 + 1 ≤ 1) → toPolyG p.1 ≠ 0)
    (hb : ∀ p ∈ factors.zipIdx, ¬ (p.2 + 1 ≤ 1) → ∀ (rhs : CPoly α),
      (toPolyG (cdiophantineG
          (cmulG (cdivWf d (cpowG p.1 (p.2 + 1))) (cmonomialDeriv Dt p.1)) p.1 rhs).1).degree
        < (toPolyG p.1).degree) :
    let g := factors.zipIdx.foldl
      (fun (gAcc : CPoly α × CPoly α) (vi, idx) =>
        let i := idx + 1
        if i ≤ 1 then gAcc
        else
          let Vi_pow := cpowG vi i
          let u := cdivWf d Vi_pow
          let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a
            ([CField.zero], [CField.one])).1
          (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
      ([CField.zero], [CField.one])
    (toPolyG (csubG (cmulG a (cmulG g.2 g.2))
        (cmulG d (csubG (cmulG (cmonomialDeriv Dt g.1) g.2)
          (cmulG g.1 (cmonomialDeriv Dt g.2)))))).degree
      < (toPolyG (cmulG d (cmulG g.2 g.2))).degree :=
  cHermiteReduceTowerG_residual_proper_of_degree_le_one Dt a d factors hDt haProper
    (fun p hp hskip => ⟨hv p hp hskip, hb p hp hskip⟩)

example (Dt gnum gden : CPoly α) (hM : toPolyG gden ≠ 0) (hDt : (toPolyG Dt).natDegree ≤ 1)
    (hgproper : (toPolyG gnum).degree < (toPolyG gden).degree) :
    (toPolyG (csubG (cmulG (cmonomialDeriv Dt gnum) gden)
        (cmulG gnum (cmonomialDeriv Dt gden)))).degree
      < (toPolyG (cmulG gden gden)).degree :=
  toPolyG_gprimeNum_proper_of_degree_le_one Dt gnum gden hM hDt hgproper

example {K : Type*} [Field K] {p1 q1 p2 q2 : K[X]} (m : ℕ)
    (h1 : p1.degree + (m : ℕ) < q1.degree) (h2 : p2.degree + (m : ℕ) < q2.degree) :
    (p1 * q2 + p2 * q1).degree + (m : ℕ) < (q1 * q2).degree :=
  degree_fracAdd_lt_of_margin m h1 h2

example {β : Type*} (glocOf : β → CPoly α × CPoly α) (skip : β → Prop) [DecidablePred skip] (m : ℕ)
    (xs : List β) (s : CPoly α × CPoly α)
    (hs : (toPolyG s.1).degree + (m : ℕ) < (toPolyG s.2).degree)
    (hmem : ∀ b ∈ xs, ¬ skip b →
      (toPolyG (glocOf b).1).degree + (m : ℕ) < (toPolyG (glocOf b).2).degree) :
    (toPolyG (xs.foldl
        (fun (gAcc : CPoly α × CPoly α) (b : β) =>
          if skip b then gAcc
          else (caddG (cmulG gAcc.1 (glocOf b).2) (cmulG (glocOf b).1 gAcc.2),
                cmulG gAcc.2 (glocOf b).2)) s).1).degree + (m : ℕ)
      < (toPolyG (xs.foldl
        (fun (gAcc : CPoly α × CPoly α) (b : β) =>
          if skip b then gAcc
          else (caddG (cmulG gAcc.1 (glocOf b).2) (cmulG (glocOf b).1 gAcc.2),
                cmulG gAcc.2 (glocOf b).2)) s).2).degree :=
  foldl_guarded_fracAddG_margin glocOf skip m xs s hs hmem

example (Dt a d gnum gden : CPoly α) (hden : toPolyG gden ≠ 0)
    (haProper : (toPolyG a).degree < (toPolyG d).degree)
    (hmargin :
      (toPolyG gnum).degree + (max 0 ((toPolyG Dt).natDegree - 1) : ℕ) < (toPolyG gden).degree) :
    (toPolyG (csubG (cmulG a (cmulG gden gden))
        (cmulG d (csubG (cmulG (cmonomialDeriv Dt gnum) gden)
          (cmulG gnum (cmonomialDeriv Dt gden)))))).degree
      < (toPolyG (cmulG d (cmulG gden gden))).degree :=
  toPolyG_residualFraction_proper_of_margin Dt a d gnum gden hden haProper hmargin

example (Dt a d gnum gden : CPoly α) (hden : toPolyG gden ≠ 0)
    (hDt : (toPolyG Dt).natDegree ≤ 1)
    (haProper : (toPolyG a).degree < (toPolyG d).degree)
    (hgproper : (toPolyG gnum).degree < (toPolyG gden).degree) :
    (toPolyG (csubG (cmulG a (cmulG gden gden))
        (cmulG d (csubG (cmulG (cmonomialDeriv Dt gnum) gden)
          (cmulG gnum (cmonomialDeriv Dt gden)))))).degree
      < (toPolyG (cmulG d (cmulG gden gden))).degree :=
  toPolyG_residualFraction_proper_of_degree_le_one Dt a d gnum gden hden hDt haProper hgproper

example (Dt : CPoly α) (s L₀ : CPoly α × CPoly α) (rest glocs : List (CPoly α × CPoly α))
    (hs : toPolyG s.2 ≠ 0) (hmem : ∀ g ∈ glocs, toPolyG g.2 ≠ 0)
    (hseed : towerFractionFieldDerivG Dt (amG α (toPolyG s.1) / amG α (toPolyG s.2)) = 0)
    (hstep : List.Forall₂ (fun g p =>
        towerFractionFieldDerivG Dt (amG α (toPolyG g.1) / amG α (toPolyG g.2))
          = amG α (toPolyG (Prod.fst p).1) / amG α (toPolyG (Prod.fst p).2)
            - amG α (toPolyG (Prod.snd p).1) / amG α (toPolyG (Prod.snd p).2))
        glocs ((L₀ :: rest).zip rest)) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG (glocs.foldl
            (fun (gAcc : CPoly α × CPoly α) gloc =>
              (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2)) s).1)
          / amG α (toPolyG (glocs.foldl
            (fun (gAcc : CPoly α × CPoly α) gloc =>
              (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2)) s).2))
        + amG α (toPolyG (rest.getLastD L₀).1) / amG α (toPolyG (rest.getLastD L₀).2)
      = amG α (toPolyG L₀.1) / amG α (toPolyG L₀.2) :=
  cHermiteReduceTowerG_telescope Dt s L₀ rest glocs hs hmem hseed hstep

example [CFracGcdCoreWf α] (Dt : CPoly α) (a d : CPoly α) (cands : List α)
    (hgden : toPolyG (CPoly.cIntegrateReducedG Dt a d cands).rational.2 ≠ 0)
    (haden : toPolyG d ≠ 0)
    (hlogs : ∀ cv ∈ (CPoly.cIntegrateReducedG Dt a d cands).logs, toPolyG cv.2 ≠ 0)
    (hcheck : CPoly.checkIdentityG Dt (CPoly.cIntegrateReducedG Dt a d cands) a d = true) :
    towerFractionFieldDerivG Dt
        (amG α (toPolyG (CPoly.cIntegrateReducedG Dt a d cands).rational.1)
          / amG α (toPolyG (CPoly.cIntegrateReducedG Dt a d cands).rational.2))
        + logResidueSumG Dt (CPoly.cIntegrateReducedG Dt a d cands).logs
      = amG α (toPolyG a) / amG α (toPolyG d) :=
  field_identity_of_cIntegrateReducedG_of_checkIdentityG Dt a d cands hgden haden hlogs hcheck

#print axioms cHermiteReduceTowerG_telescope_seed_qfunNZG

end DeepWiki.SymbolicIntegration
