import DeepWiki.SymbolicIntegration.Engine.NormalPartSoundness

/-! # Normal-part soundness examples

Level-1 specialization and anonymous restatements for the normal-part soundness API.
-/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

/-! ### The deliverables at the level-1 carrier `α = DenseFrac ℚ = ℚ(x)` -/

/-- The engine carrier `CFieldSpec.K (DenseFrac ℚ)` is `RatFunc ℚ`, a `ℚ`-algebra. Local instance so the
`DenseFrac ℚ` deliverables synthesize the **same** `Algebra ℚ` the bridge `towerFractionFieldDeriv` uses. -/
noncomputable local instance normalPartSoundnessExamplesAlgebraRatKCFracG :
    Algebra ℚ (CFieldSpec.K (DenseFrac ℚ)) :=
  inferInstanceAs (Algebra ℚ (RatFunc ℚ))

/-- The Hermite half over `ℚ(x)(t)`: the master Hermite telescoping `D(g) + h = a/d` (seed
`([CCommRing.zero], [CCommRing.one])`) at the carrier `α = DenseFrac ℚ`, over `RatFunc ℚ`. -/
theorem cHermiteReduceTowerG_telescope_seed_qfunNZG (Dt : DensePoly (DenseFrac ℚ))
    (L₀ : DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ))
    (rest glocs : List (DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ)))
    (hmem : ∀ g ∈ glocs, toPoly g.2 ≠ 0)
    (hstep : List.Forall₂ (fun g p =>
        towerFractionFieldDeriv Dt (am (DenseFrac ℚ) (toPoly g.1) / am (DenseFrac ℚ) (toPoly g.2))
          = am (DenseFrac ℚ) (toPoly (Prod.fst p).1) / am (DenseFrac ℚ) (toPoly (Prod.fst p).2)
            - am (DenseFrac ℚ) (toPoly (Prod.snd p).1) / am (DenseFrac ℚ) (toPoly (Prod.snd p).2))
        glocs ((L₀ :: rest).zip rest)) :
    towerFractionFieldDeriv Dt
        (am (DenseFrac ℚ) (toPoly (glocs.foldl
            (fun (gAcc : DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ)) gloc =>
              (cadd (cmul gAcc.1 gloc.2) (cmul gloc.1 gAcc.2), cmul gAcc.2 gloc.2))
            (([CCommRing.zero] : DensePoly (DenseFrac ℚ)), ([CCommRing.one] : DensePoly (DenseFrac ℚ)))).1)
          / am (DenseFrac ℚ) (toPoly (glocs.foldl
            (fun (gAcc : DensePoly (DenseFrac ℚ) × DensePoly (DenseFrac ℚ)) gloc =>
              (cadd (cmul gAcc.1 gloc.2) (cmul gloc.1 gAcc.2), cmul gAcc.2 gloc.2))
            (([CCommRing.zero] : DensePoly (DenseFrac ℚ)), ([CCommRing.one] : DensePoly (DenseFrac ℚ)))).2))
        + am (DenseFrac ℚ) (toPoly (rest.getLastD L₀).1)
          / am (DenseFrac ℚ) (toPoly (rest.getLastD L₀).2)
      = am (DenseFrac ℚ) (toPoly L₀.1) / am (DenseFrac ℚ) (toPoly L₀.2) :=
  cHermiteReduceTowerG_telescope_seed Dt L₀ rest glocs hmem hstep

/-! ### Restatements against the intended wording (anonymous `example`s) -/

example {K : Type*} [Field K] {H D2 N S : K[X]}
    (hid : H * D2 = N * S) (hND : N.degree < D2.degree) (hS : S ≠ 0) :
    H.degree < S.degree :=
  degree_lt_of_exact_div hid hND hS

example [CPolySquarefree DensePoly α] (Dt : DensePoly α) (a d : DensePoly α) (resNum resDen Dstar : DensePoly α)
    (hnum : toPoly (DensePoly.cHermiteReduceTower Dt a d).2.1
      = toPoly (CPolyEuclidean.div (cmul resNum Dstar) resDen))
    (hden : toPoly (DensePoly.cHermiteReduceTower Dt a d).2.2 = toPoly Dstar)
    (hdvd : toPoly resDen ∣ toPoly (cmul resNum Dstar))
    (hresDen : cnorm resDen ≠ []) (hDstar : toPoly Dstar ≠ 0)
    (hresProper : (toPoly resNum).degree < (toPoly resDen).degree) :
    (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.1).degree
      < (toPoly (DensePoly.cHermiteReduceTower Dt a d).2.2).degree :=
  cHermiteReduceTowerG_leftover_proper_of_residual Dt a d resNum resDen Dstar
    hnum hden hdvd hresDen hDstar hresProper

example {β : Type*} (glocOf : β → DensePoly α × DensePoly α) (skip : β → Prop) [DecidablePred skip]
    (xs : List β) (s : DensePoly α × DensePoly α) (hs : (toPoly s.1).degree < (toPoly s.2).degree)
    (hmem : ∀ b ∈ xs, ¬ skip b → (toPoly (glocOf b).1).degree < (toPoly (glocOf b).2).degree) :
    (toPoly (xs.foldl
        (fun (gAcc : DensePoly α × DensePoly α) (b : β) =>
          if skip b then gAcc
          else (cadd (cmul gAcc.1 (glocOf b).2) (cmul (glocOf b).1 gAcc.2),
                cmul gAcc.2 (glocOf b).2)) s).1).degree
      < (toPoly (xs.foldl
        (fun (gAcc : DensePoly α × DensePoly α) (b : β) =>
          if skip b then gAcc
          else (cadd (cmul gAcc.1 (glocOf b).2) (cmul (glocOf b).1 gAcc.2),
                cmul gAcc.2 (glocOf b).2)) s).2).degree :=
  foldl_guarded_fracAddG_proper glocOf skip xs s hs hmem

example (Dt : DensePoly α) (v u : DensePoly α) (hv : toPoly v ≠ 0)
    (hb : ∀ (rhs : DensePoly α),
      (toPoly (CPoly.diophantineReduced (cmul u (CPolyEngine.monomialDeriv Dt v)) v rhs).1).degree
        < (toPoly v).degree)
    (j : ℕ) (a : DensePoly α) (g : DensePoly α × DensePoly α)
    (hg : (toPoly g.1).degree < (toPoly g.2).degree) :
    (toPoly (cHermiteReduceTowerInnerWf Dt v u j a g).1.1).degree
      < (toPoly (cHermiteReduceTowerInnerWf Dt v u j a g).1.2).degree :=
  cHermiteReduceTowerInner_g_proper Dt v u ⟨hv, hb⟩ j a g hg

example (Dt : DensePoly α) (vi u : DensePoly α) (j : ℕ) (a : DensePoly α) (hv : toPoly vi ≠ 0)
    (hb : ∀ (rhs : DensePoly α),
      (toPoly (CPoly.diophantineReduced (cmul u (CPolyEngine.monomialDeriv Dt vi)) vi rhs).1).degree
        < (toPoly vi).degree) :
    (toPoly (cHermiteReduceTowerInnerWf Dt vi u j a ([CCommRing.zero], [CCommRing.one])).1.1).degree
      < (toPoly (cHermiteReduceTowerInnerWf Dt vi u j a ([CCommRing.zero], [CCommRing.one])).1.2).degree :=
  cHermiteReduceTowerInner_gloc_proper Dt vi u j a ⟨hv, hb⟩

example (Dt : DensePoly α) (a d : DensePoly α) (factors : List (DensePoly α))
    (hv : ∀ p ∈ factors.zipIdx, ¬ (p.2 + 1 ≤ 1) → toPoly p.1 ≠ 0)
    (hb : ∀ p ∈ factors.zipIdx, ¬ (p.2 + 1 ≤ 1) → ∀ (rhs : DensePoly α),
      (toPoly (CPoly.diophantineReduced
          (cmul (CPolyEuclidean.div d (cpow p.1 (p.2 + 1))) (CPolyEngine.monomialDeriv Dt p.1)) p.1 rhs).1).degree
        < (toPoly p.1).degree) :
    (toPoly (factors.zipIdx.foldl
        (fun (gAcc : DensePoly α × DensePoly α) (vi, idx) =>
          let i := idx + 1
          if i ≤ 1 then gAcc
          else
            let Vi_pow := cpow vi i
            let u := CPolyEuclidean.div d Vi_pow
            let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a
              ([CCommRing.zero], [CCommRing.one])).1
            (cadd (cmul gAcc.1 gloc.2) (cmul gloc.1 gAcc.2), cmul gAcc.2 gloc.2))
        ([CCommRing.zero], [CCommRing.one])).1).degree
      < (toPoly (factors.zipIdx.foldl
        (fun (gAcc : DensePoly α × DensePoly α) (vi, idx) =>
          let i := idx + 1
          if i ≤ 1 then gAcc
          else
            let Vi_pow := cpow vi i
            let u := CPolyEuclidean.div d Vi_pow
            let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a
              ([CCommRing.zero], [CCommRing.one])).1
            (cadd (cmul gAcc.1 gloc.2) (cmul gloc.1 gAcc.2), cmul gAcc.2 gloc.2))
        ([CCommRing.zero], [CCommRing.one])).2).degree :=
  cHermiteReduceTowerG_g_proper Dt a d factors (fun p hp hskip => ⟨hv p hp hskip, hb p hp hskip⟩)

example (Dt : DensePoly α) (a d : DensePoly α) (factors : List (DensePoly α))
    (hDt : (toPoly Dt).natDegree ≤ 1) (haProper : (toPoly a).degree < (toPoly d).degree)
    (hv : ∀ p ∈ factors.zipIdx, ¬ (p.2 + 1 ≤ 1) → toPoly p.1 ≠ 0)
    (hb : ∀ p ∈ factors.zipIdx, ¬ (p.2 + 1 ≤ 1) → ∀ (rhs : DensePoly α),
      (toPoly (CPoly.diophantineReduced
          (cmul (CPolyEuclidean.div d (cpow p.1 (p.2 + 1))) (CPolyEngine.monomialDeriv Dt p.1)) p.1 rhs).1).degree
        < (toPoly p.1).degree) :
    let g := factors.zipIdx.foldl
      (fun (gAcc : DensePoly α × DensePoly α) (vi, idx) =>
        let i := idx + 1
        if i ≤ 1 then gAcc
        else
          let Vi_pow := cpow vi i
          let u := CPolyEuclidean.div d Vi_pow
          let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a
            ([CCommRing.zero], [CCommRing.one])).1
          (cadd (cmul gAcc.1 gloc.2) (cmul gloc.1 gAcc.2), cmul gAcc.2 gloc.2))
      ([CCommRing.zero], [CCommRing.one])
    (toPoly (csub (cmul a (cmul g.2 g.2))
        (cmul d (csub (cmul (CPolyEngine.monomialDeriv Dt g.1) g.2)
          (cmul g.1 (CPolyEngine.monomialDeriv Dt g.2)))))).degree
      < (toPoly (cmul d (cmul g.2 g.2))).degree :=
  cHermiteReduceTowerG_residual_proper_of_degree_le_one Dt a d factors hDt haProper
    (fun p hp hskip => ⟨hv p hp hskip, hb p hp hskip⟩)

example (Dt gnum gden : DensePoly α) (hM : toPoly gden ≠ 0) (hDt : (toPoly Dt).natDegree ≤ 1)
    (hgproper : (toPoly gnum).degree < (toPoly gden).degree) :
    (toPoly (csub (cmul (CPolyEngine.monomialDeriv Dt gnum) gden)
        (cmul gnum (CPolyEngine.monomialDeriv Dt gden)))).degree
      < (toPoly (cmul gden gden)).degree :=
  toPolyG_gprimeNum_proper_of_degree_le_one Dt gnum gden hM hDt hgproper

example {K : Type*} [Field K] {p1 q1 p2 q2 : K[X]} (m : ℕ)
    (h1 : p1.degree + (m : ℕ) < q1.degree) (h2 : p2.degree + (m : ℕ) < q2.degree) :
    (p1 * q2 + p2 * q1).degree + (m : ℕ) < (q1 * q2).degree :=
  degree_fracAdd_lt_of_margin m h1 h2

example {β : Type*} (glocOf : β → DensePoly α × DensePoly α) (skip : β → Prop) [DecidablePred skip] (m : ℕ)
    (xs : List β) (s : DensePoly α × DensePoly α)
    (hs : (toPoly s.1).degree + (m : ℕ) < (toPoly s.2).degree)
    (hmem : ∀ b ∈ xs, ¬ skip b →
      (toPoly (glocOf b).1).degree + (m : ℕ) < (toPoly (glocOf b).2).degree) :
    (toPoly (xs.foldl
        (fun (gAcc : DensePoly α × DensePoly α) (b : β) =>
          if skip b then gAcc
          else (cadd (cmul gAcc.1 (glocOf b).2) (cmul (glocOf b).1 gAcc.2),
                cmul gAcc.2 (glocOf b).2)) s).1).degree + (m : ℕ)
      < (toPoly (xs.foldl
        (fun (gAcc : DensePoly α × DensePoly α) (b : β) =>
          if skip b then gAcc
          else (cadd (cmul gAcc.1 (glocOf b).2) (cmul (glocOf b).1 gAcc.2),
                cmul gAcc.2 (glocOf b).2)) s).2).degree :=
  foldl_guarded_fracAddG_margin glocOf skip m xs s hs hmem

example (Dt a d gnum gden : DensePoly α) (hden : toPoly gden ≠ 0)
    (haProper : (toPoly a).degree < (toPoly d).degree)
    (hmargin :
      (toPoly gnum).degree + (max 0 ((toPoly Dt).natDegree - 1) : ℕ) < (toPoly gden).degree) :
    (toPoly (csub (cmul a (cmul gden gden))
        (cmul d (csub (cmul (CPolyEngine.monomialDeriv Dt gnum) gden)
          (cmul gnum (CPolyEngine.monomialDeriv Dt gden)))))).degree
      < (toPoly (cmul d (cmul gden gden))).degree :=
  toPolyG_residualFraction_proper_of_margin Dt a d gnum gden hden haProper hmargin

example (Dt a d gnum gden : DensePoly α) (hden : toPoly gden ≠ 0)
    (hDt : (toPoly Dt).natDegree ≤ 1)
    (haProper : (toPoly a).degree < (toPoly d).degree)
    (hgproper : (toPoly gnum).degree < (toPoly gden).degree) :
    (toPoly (csub (cmul a (cmul gden gden))
        (cmul d (csub (cmul (CPolyEngine.monomialDeriv Dt gnum) gden)
          (cmul gnum (CPolyEngine.monomialDeriv Dt gden)))))).degree
      < (toPoly (cmul d (cmul gden gden))).degree :=
  toPolyG_residualFraction_proper_of_degree_le_one Dt a d gnum gden hden hDt haProper hgproper

example (Dt : DensePoly α) (s L₀ : DensePoly α × DensePoly α) (rest glocs : List (DensePoly α × DensePoly α))
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
      = am α (toPoly L₀.1) / am α (toPoly L₀.2) :=
  cHermiteReduceTowerG_telescope Dt s L₀ rest glocs hs hmem hseed hstep

example [CPolyGcd DensePoly α] [CPolySquarefree DensePoly α] [CPolyResultant DensePoly]
    (Dt : DensePoly α) (a d : DensePoly α) (cands : List α)
    (hgden : toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2 ≠ 0)
    (haden : toPoly d ≠ 0)
    (hlogs : ∀ cv ∈ (DensePoly.cIntegrateReduced Dt a d cands).logs, toPoly cv.2 ≠ 0)
    (hcheck : DensePoly.checkIdentity Dt (DensePoly.cIntegrateReduced Dt a d cands) a d = true) :
    towerFractionFieldDeriv Dt
        (am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.1)
          / am α (toPoly (DensePoly.cIntegrateReduced Dt a d cands).rational.2))
        + logResidueSum Dt (DensePoly.cIntegrateReduced Dt a d cands).logs
      = am α (toPoly a) / am α (toPoly d) :=
  field_identity_of_cIntegrateReducedG_of_checkIdentityG Dt a d cands hgden haden hlogs hcheck

#print axioms cHermiteReduceTowerG_telescope_seed_qfunNZG

end DeepWiki.SymbolicIntegration
