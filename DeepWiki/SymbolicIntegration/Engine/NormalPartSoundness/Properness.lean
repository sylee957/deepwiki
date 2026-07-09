import DeepWiki.SymbolicIntegration.Engine.NormalPartSoundness.Telescope

/-! # Hermite normal-part properness

Degree and properness bounds for the normal-part Hermite residual and leftover fraction.
-/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [Algebra ℚ (CFieldSpec.K α)]

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- `v` is a nonzero Hermite factor whose Diophantine cofactors are proper. -/
structure IsHermiteInnerFactor (Dt v u : CPolyG α) : Prop where
  /-- The Hermite factor denotes a nonzero polynomial. -/
  nonzero : toPolyG v ≠ 0
  /-- Every Diophantine cofactor against `u * D(v)` is proper modulo `v`. -/
  cofactor_proper : ∀ (rhs : CPolyG α),
    (toPolyG (cdiophantineG (cmulG u (cmonomialDeriv Dt v)) v rhs).1).degree
      < (toPolyG v).degree

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The non-skipped outer Hermite factors carry the inner-factor properness data. -/
abbrev IsHermiteFactorData (Dt d : CPolyG α) (factors : List (CPolyG α)) : Prop :=
  ∀ p ∈ factors.zipIdx, ¬ (p.2 + 1 ≤ 1) →
    IsHermiteInnerFactor Dt p.1 (cdivWf d (cpowG p.1 (p.2 + 1)))

/-! ### The exact-division degree bound -/

/-- Degree cancellation from an exact division: over a field, from `H·D₂ = N·S` with `deg N < deg D₂`
and `S ≠ 0`, the quotient `H` is proper for `S`: `deg H < deg S`. -/
theorem degree_lt_of_exact_div {K : Type*} [Field K] {H D2 N S : K[X]}
    (hid : H * D2 = N * S) (hND : N.degree < D2.degree) (hS : S ≠ 0) :
    H.degree < S.degree := by
  have hD2 : D2 ≠ 0 := by
    rintro rfl; simp only [Polynomial.degree_zero] at hND; exact absurd hND (by simp)
  rcases eq_or_ne H 0 with hH | hH
  · subst hH; rw [Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr (by rwa [Ne, Polynomial.degree_eq_bot])
  · -- `H ≠ 0`, `D₂ ≠ 0` ⟹ `H·D₂ ≠ 0` ⟹ `N·S ≠ 0` ⟹ `N ≠ 0`; all degrees are honest `natDegree`s.
    have hHD2 : H * D2 ≠ 0 := mul_ne_zero hH hD2
    rw [hid] at hHD2
    have hN : N ≠ 0 := fun h => hHD2 (by rw [h, zero_mul])
    have e1 : H.degree = (H.natDegree : WithBot ℕ) := Polynomial.degree_eq_natDegree hH
    have e2 : D2.degree = (D2.natDegree : WithBot ℕ) := Polynomial.degree_eq_natDegree hD2
    have e3 : N.degree = (N.natDegree : WithBot ℕ) := Polynomial.degree_eq_natDegree hN
    have e4 : S.degree = (S.natDegree : WithBot ℕ) := Polynomial.degree_eq_natDegree hS
    have hdeg : H.natDegree + D2.natDegree = N.natDegree + S.natDegree := by
      have hmul : (H * D2).degree = (N * S).degree := by rw [hid]
      rw [Polynomial.degree_mul, Polynomial.degree_mul, e1, e2, e3, e4,
        ← Nat.cast_add, ← Nat.cast_add, Nat.cast_inj] at hmul
      exact hmul
    rw [e1, e4, Nat.cast_lt]
    rw [e2, e3, Nat.cast_lt] at hND
    omega

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The `cHermiteReduceTowerG` leftover is proper (`deg (…).2.1 < deg (…).2.2`) from the leftover
projections `hnum`/`hden`, the exact-division divisibility `resDen ∣ resNum·Dstar`, nonzero radical,
and residual-fraction properness `deg resNum < deg resDen`. -/
theorem cHermiteReduceTowerG_leftover_proper_of_residual [CFracGcdCoreWf α]
    (Dt : CPolyG α) (a d : CPolyG α) (resNum resDen Dstar : CPolyG α)
    (hnum : toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.1
      = toPolyG (cdivWf (cmulG resNum Dstar) resDen))
    (hden : toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.2 = toPolyG Dstar)
    (hdvd : toPolyG resDen ∣ toPolyG (cmulG resNum Dstar))
    (hresDen : cnormG resDen ≠ [])
    (hDstar : toPolyG Dstar ≠ 0)
    (hresProper : (toPolyG resNum).degree < (toPolyG resDen).degree) :
    (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.1).degree
      < (toPolyG (CPolyG.cHermiteReduceTowerG Dt a d).2.2).degree := by
  rw [hnum, hden]
  -- exact division: `h_num · resDen = resNum·Dstar = resNum · Dstar`
  have hexact : toPolyG (cdivWf (cmulG resNum Dstar) resDen) * toPolyG resDen
      = toPolyG resNum * toPolyG Dstar := by
    rw [toPolyG_cdivWf_exact (cmulG resNum Dstar) resDen hresDen hdvd]
    simp only [denote]
  exact degree_lt_of_exact_div hexact hresProper hDstar

/-! ### The residual-fraction properness `deg resNum < deg resDen` for `δ(t) ≤ 1`

The assembled `g = gnum/gden` stays proper by a fold-induction; `D(g)` is proper for `gden²` with the
margin `deg gnum + max(0, deg Dt − 1) < deg gden` (plain properness when `deg Dt ≤ 1`); the difference
`a/d − D(g)` is then proper, giving the residual-fraction properness. -/

/-- Proper-fraction addition is proper: if `deg p₁ < deg q₁` and `deg p₂ < deg q₂` then
`deg(p₁q₂ + p₂q₁) < deg(q₁q₂)`. -/
theorem degree_fracAdd_lt_of_proper {K : Type*} [Field K] {p1 q1 p2 q2 : K[X]}
    (h1 : p1.degree < q1.degree) (h2 : p2.degree < q2.degree) :
    (p1 * q2 + p2 * q1).degree < (q1 * q2).degree := by
  have hq1 : q1 ≠ 0 := by rintro rfl; simp at h1
  have hq2 : q2 ≠ 0 := by rintro rfl; simp at h2
  have e1 : (p1 * q2).degree < (q1 * q2).degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_mul]
    exact WithBot.add_lt_add_right (by rwa [Ne, Polynomial.degree_eq_bot]) h1
  have e2 : (p2 * q1).degree < (q1 * q2).degree := by
    rw [Polynomial.degree_mul, mul_comm q1 q2, Polynomial.degree_mul]
    exact WithBot.add_lt_add_right (by rwa [Ne, Polynomial.degree_eq_bot]) h2
  exact lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt e1 e2)

/-- The residual numerator of a difference of proper fractions is proper: for `A/D − GP/GG` with
`deg A < deg D` and `deg GP < deg GG`, `deg(A·GG − D·GP) < deg(D·GG)`. -/
theorem degree_resNum_lt {K : Type*} [Field K] {A D GG GP : K[X]}
    (haProper : A.degree < D.degree) (hgprime : GP.degree < GG.degree) :
    (A * GG - D * GP).degree < (D * GG).degree := by
  have hGG : GG ≠ 0 := by rintro h; rw [h] at hgprime; simp at hgprime
  have hD : D ≠ 0 := by rintro h; rw [h] at haProper; simp at haProper
  have e1 : (A * GG).degree < (D * GG).degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_mul]
    exact WithBot.add_lt_add_right (by rwa [Ne, Polynomial.degree_eq_bot]) haProper
  have e2 : (D * GP).degree < (D * GG).degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_mul,
      WithBot.add_lt_add_iff_left (by rwa [Ne, Polynomial.degree_eq_bot])]
    exact hgprime
  exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt e1 e2)

/-- The monomial derivation of a proper fraction is proper (margin form): for `M ≠ 0`, the derivative
numerator `implicitDeriv v N · M − N · implicitDeriv v M` is proper for `M²`, given the margin
`deg N + max(0, deg v − 1) < deg M`. -/
theorem degree_implicitDeriv_frac_lt_of_margin {K : Type*} [Field K] [Differential K] {v N M : K[X]}
    (hM : M ≠ 0) (hmargin : N.degree + (max 0 (v.natDegree - 1) : ℕ) < M.degree) :
    (Differential.implicitDeriv v N * M - N * Differential.implicitDeriv v M).degree
      < (M * M).degree := by
  set δ : ℕ := max 0 (v.natDegree - 1) with hδ
  have hMdeg : (M * M).degree = M.degree + M.degree := Polynomial.degree_mul
  have hd1 : (Differential.implicitDeriv v N * M).degree < (M * M).degree := by
    rw [Polynomial.degree_mul, hMdeg]
    have hDN : (Differential.implicitDeriv v N).degree ≤ N.degree + (δ : ℕ) := by
      rcases eq_or_ne (Differential.implicitDeriv v N) 0 with h0 | h0
      · rw [h0, Polynomial.degree_zero]; exact bot_le
      · rw [Polynomial.degree_eq_natDegree h0]
        rcases eq_or_ne N 0 with hN0 | hN0
        · rw [hN0, map_zero] at h0; exact absurd rfl h0
        · rw [Polynomial.degree_eq_natDegree hN0]; exact_mod_cast natDegree_implicitDeriv_le v N
    have hlt : (Differential.implicitDeriv v N).degree < M.degree := lt_of_le_of_lt hDN hmargin
    exact WithBot.add_lt_add_right (by rwa [Ne, Polynomial.degree_eq_bot]) hlt
  have hd2 : (N * Differential.implicitDeriv v M).degree < (M * M).degree := by
    rw [Polynomial.degree_mul, hMdeg]
    have hDM : (Differential.implicitDeriv v M).degree ≤ M.degree + (δ : ℕ) := by
      rcases eq_or_ne (Differential.implicitDeriv v M) 0 with h0 | h0
      · rw [h0, Polynomial.degree_zero]; exact bot_le
      · rw [Polynomial.degree_eq_natDegree h0, Polynomial.degree_eq_natDegree hM]
        exact_mod_cast natDegree_implicitDeriv_le v M
    calc N.degree + (Differential.implicitDeriv v M).degree
        ≤ N.degree + (M.degree + (δ : ℕ)) := by gcongr
      _ = (N.degree + (δ : ℕ)) + M.degree := by ring
      _ < M.degree + M.degree :=
          WithBot.add_lt_add_right (by rwa [Ne, Polynomial.degree_eq_bot]) hmargin
  exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hd1 hd2)

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- One Hermite `g`-fold step preserves properness: the cross-multiplied fraction-add of two proper
fractions `gAcc`, `gloc` is proper (`toPolyG` form of `degree_fracAdd_lt_of_proper`). -/
theorem toPolyG_fracAddG_proper {gAcc gloc : CPolyG α × CPolyG α}
    (h1 : (toPolyG gAcc.1).degree < (toPolyG gAcc.2).degree)
    (h2 : (toPolyG gloc.1).degree < (toPolyG gloc.2).degree) :
    (toPolyG (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2))).degree
      < (toPolyG (cmulG gAcc.2 gloc.2)).degree := by
  simpa using degree_fracAdd_lt_of_proper h1 h2

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The Hermite `g`-fold stays proper: folding the fraction-add combiner from a proper seed over proper
contributions yields a proper running fraction `deg res.1 < deg res.2`. -/
theorem foldl_fracAddG_proper :
    ∀ (glocs : List (CPolyG α × CPolyG α)) (s : CPolyG α × CPolyG α),
      (toPolyG s.1).degree < (toPolyG s.2).degree →
      (∀ g ∈ glocs, (toPolyG g.1).degree < (toPolyG g.2).degree) →
      let res := glocs.foldl
        (fun (gAcc : CPolyG α × CPolyG α) gloc =>
          (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2)) s
      (toPolyG res.1).degree < (toPolyG res.2).degree := by
  intro glocs
  induction glocs with
  | nil => intro s hs _; exact hs
  | cons gloc rest ih =>
    intro s hs hmem
    have hgloc : (toPolyG gloc.1).degree < (toPolyG gloc.2).degree := hmem gloc List.mem_cons_self
    have hrest : ∀ g ∈ rest, (toPolyG g.1).degree < (toPolyG g.2).degree :=
      fun g hg => hmem g (List.mem_cons_of_mem _ hg)
    set snew : CPolyG α × CPolyG α :=
      (caddG (cmulG s.1 gloc.2) (cmulG gloc.1 s.2), cmulG s.2 gloc.2) with hsnew
    have hsnew_proper : (toPolyG snew.1).degree < (toPolyG snew.2).degree := by
      rw [hsnew]; exact toPolyG_fracAddG_proper hs hgloc
    simpa only [List.foldl_cons] using ih snew hsnew_proper hrest

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The guarded Hermite `g`-fold stays proper: for the fold `if skip b then gAcc else gAcc + glocOf b`,
a proper seed and each non-skipped `glocOf b` proper give a proper running fraction. -/
theorem foldl_guarded_fracAddG_proper {β : Type*} (glocOf : β → CPolyG α × CPolyG α)
    (skip : β → Prop) [DecidablePred skip] :
    ∀ (xs : List β) (s : CPolyG α × CPolyG α),
      (toPolyG s.1).degree < (toPolyG s.2).degree →
      (∀ b ∈ xs, ¬ skip b → (toPolyG (glocOf b).1).degree < (toPolyG (glocOf b).2).degree) →
      let res := xs.foldl
        (fun (gAcc : CPolyG α × CPolyG α) (b : β) =>
          if skip b then gAcc
          else (caddG (cmulG gAcc.1 (glocOf b).2) (cmulG (glocOf b).1 gAcc.2),
                cmulG gAcc.2 (glocOf b).2)) s
      (toPolyG res.1).degree < (toPolyG res.2).degree := by
  intro xs
  induction xs with
  | nil => intro s hs _; exact hs
  | cons b rest ih =>
    intro s hs hmem
    have hrest : ∀ b' ∈ rest, ¬ skip b' →
        (toPolyG (glocOf b').1).degree < (toPolyG (glocOf b').2).degree :=
      fun b' hb' => hmem b' (List.mem_cons_of_mem _ hb')
    simp only [List.foldl_cons]
    by_cases hsk : skip b
    · rw [show (if skip b then s
          else (caddG (cmulG s.1 (glocOf b).2) (cmulG (glocOf b).1 s.2),
                cmulG s.2 (glocOf b).2)) = s from if_pos hsk]
      exact ih s hs hrest
    · set snew : CPolyG α × CPolyG α :=
        (caddG (cmulG s.1 (glocOf b).2) (cmulG (glocOf b).1 s.2), cmulG s.2 (glocOf b).2) with hsnew
      rw [show (if skip b then s
          else (caddG (cmulG s.1 (glocOf b).2) (cmulG (glocOf b).1 s.2),
                cmulG s.2 (glocOf b).2)) = snew from if_neg hsk]
      have hgloc : (toPolyG (glocOf b).1).degree < (toPolyG (glocOf b).2).degree :=
        hmem b List.mem_cons_self hsk
      have hsnew_proper : (toPolyG snew.1).degree < (toPolyG snew.2).degree := by
        rw [hsnew]; exact toPolyG_fracAddG_proper hs hgloc
      exact ih snew hsnew_proper hrest

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- `D(g)`'s numerator is proper for `gden²` (margin form): `cmonomialDeriv Dt gnum · gden −
gnum · cmonomialDeriv Dt gden` is proper for `gden·gden`, given `gden ≠ 0` and the margin
`deg gnum + max(0, deg Dt − 1) < deg gden`. -/
theorem toPolyG_gprimeNum_proper_of_margin (Dt gnum gden : CPolyG α) (hM : toPolyG gden ≠ 0)
    (hmargin :
      (toPolyG gnum).degree + (max 0 ((toPolyG Dt).natDegree - 1) : ℕ) < (toPolyG gden).degree) :
    (toPolyG (csubG (cmulG (cmonomialDeriv Dt gnum) gden)
        (cmulG gnum (cmonomialDeriv Dt gden)))).degree
      < (toPolyG (cmulG gden gden)).degree := by
  simpa only [denote] using degree_implicitDeriv_frac_lt_of_margin hM hmargin

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- `D(g)` proper from `g` proper when `deg Dt ≤ 1`: a proper `g = gnum/gden` has proper derivative
numerator `cmonomialDeriv Dt gnum · gden − gnum · cmonomialDeriv Dt gden` for `gden²`, the margin
collapsing to plain properness. -/
theorem toPolyG_gprimeNum_proper_of_degree_le_one (Dt gnum gden : CPolyG α) (hM : toPolyG gden ≠ 0)
    (hDt : (toPolyG Dt).natDegree ≤ 1)
    (hgproper : (toPolyG gnum).degree < (toPolyG gden).degree) :
    (toPolyG (csubG (cmulG (cmonomialDeriv Dt gnum) gden)
        (cmulG gnum (cmonomialDeriv Dt gden)))).degree
      < (toPolyG (cmulG gden gden)).degree := by
  refine toPolyG_gprimeNum_proper_of_margin Dt gnum gden hM ?_
  have hz : max 0 ((toPolyG Dt).natDegree - 1) = 0 := by omega
  rw [hz, Nat.cast_zero, add_zero]
  exact hgproper

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The residual numerator `resNum = a·gden² − d·gprimeNum` is proper for `resDen = d·gden²`, given
`deg a < deg d` and `gprimeNum` proper for `gden²`. -/
theorem toPolyG_resNum_proper (a d gden gprimeNum : CPolyG α)
    (haProper : (toPolyG a).degree < (toPolyG d).degree)
    (hgprime : (toPolyG gprimeNum).degree < (toPolyG (cmulG gden gden)).degree) :
    (toPolyG (csubG (cmulG a (cmulG gden gden)) (cmulG d gprimeNum))).degree
      < (toPolyG (cmulG d (cmulG gden gden))).degree := by
  simp only [denote] at hgprime ⊢
  exact degree_resNum_lt haProper hgprime

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- The residual fraction `a/d − D(g)` is proper for `deg Dt ≤ 1`: for `resNum = a·gden² −
d·(cmonomialDeriv Dt gnum · gden − gnum · cmonomialDeriv Dt gden)`, `resDen = d·gden²`,
`deg resNum < deg resDen`, given `g = gnum/gden` proper, `a/d` proper, and `deg Dt ≤ 1`. -/
theorem toPolyG_residualFraction_proper_of_degree_le_one
    (Dt a d gnum gden : CPolyG α) (hden : toPolyG gden ≠ 0)
    (hDt : (toPolyG Dt).natDegree ≤ 1)
    (haProper : (toPolyG a).degree < (toPolyG d).degree)
    (hgproper : (toPolyG gnum).degree < (toPolyG gden).degree) :
    (toPolyG (csubG (cmulG a (cmulG gden gden))
        (cmulG d (csubG (cmulG (cmonomialDeriv Dt gnum) gden)
          (cmulG gnum (cmonomialDeriv Dt gden)))))).degree
      < (toPolyG (cmulG d (cmulG gden gden))).degree :=
  toPolyG_resNum_proper a d gden _ haProper
    (toPolyG_gprimeNum_proper_of_degree_le_one Dt gnum gden hden hDt hgproper)

/-! ### The `deg Dt ≥ 2` case — the residual is proper iff `g` has the `(deg Dt − 1)` margin

For nonlinear monomials (`deg Dt ≥ 2`) the derivative-degree step needs the strictly-stronger margin
`deg gnum + (deg Dt − 1) < deg gden`, which the generic Hermite output need not satisfy. The lemmas below
carry the margin through the fraction algebra and state the conditional residual properness. -/

/-- Margin-preserving fraction addition: if `deg p₁ + m < deg q₁` and `deg p₂ + m < deg q₂` then
`deg(p₁q₂ + p₂q₁) + m < deg(q₁q₂)`. The `m = 0` case is `degree_fracAdd_lt_of_proper`. -/
theorem degree_fracAdd_lt_of_margin {K : Type*} [Field K] {p1 q1 p2 q2 : K[X]} (m : ℕ)
    (h1 : p1.degree + (m : ℕ) < q1.degree) (h2 : p2.degree + (m : ℕ) < q2.degree) :
    (p1 * q2 + p2 * q1).degree + (m : ℕ) < (q1 * q2).degree := by
  have hq1 : q1 ≠ 0 := by
    rintro rfl; rw [Polynomial.degree_zero] at h1; exact absurd h1 (by simp)
  have hq2 : q2 ≠ 0 := by
    rintro rfl; rw [Polynomial.degree_zero] at h2; exact absurd h2 (by simp)
  have e1 : (p1 * q2).degree + (m : ℕ) < (q1 * q2).degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_mul, add_right_comm]
    exact WithBot.add_lt_add_right (by rwa [Ne, Polynomial.degree_eq_bot]) h1
  have e2 : (p2 * q1).degree + (m : ℕ) < (q1 * q2).degree := by
    rw [Polynomial.degree_mul, mul_comm q1 q2, Polynomial.degree_mul, add_right_comm]
    exact WithBot.add_lt_add_right (by rwa [Ne, Polynomial.degree_eq_bot]) h2
  calc (p1 * q2 + p2 * q1).degree + (m : ℕ)
      ≤ max (p1 * q2).degree (p2 * q1).degree + (m : ℕ) := by
        gcongr; exact Polynomial.degree_add_le _ _
    _ = max ((p1 * q2).degree + (m : ℕ)) ((p2 * q1).degree + (m : ℕ)) :=
        (max_add_add_right _ _ _).symm
    _ < (q1 * q2).degree := max_lt e1 e2

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- One Hermite `g`-fold step preserves the `m`-margin: the cross-multiplied fraction-add of two
margin-proper fractions `gAcc`, `gloc` (each `deg .1 + m < deg .2`) is margin-proper. -/
theorem toPolyG_fracAddG_margin {gAcc gloc : CPolyG α × CPolyG α} (m : ℕ)
    (h1 : (toPolyG gAcc.1).degree + (m : ℕ) < (toPolyG gAcc.2).degree)
    (h2 : (toPolyG gloc.1).degree + (m : ℕ) < (toPolyG gloc.2).degree) :
    (toPolyG (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2))).degree + (m : ℕ)
      < (toPolyG (cmulG gAcc.2 gloc.2)).degree := by
  simpa using degree_fracAdd_lt_of_margin m h1 h2

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The guarded Hermite `g`-fold preserves the `m`-margin: for the fold `if skip b then gAcc else
gAcc + glocOf b`, a margin-proper seed and each non-skipped `glocOf b` margin-proper give a
margin-proper running fraction. The `m = 0` case is `foldl_guarded_fracAddG_proper`. -/
theorem foldl_guarded_fracAddG_margin {β : Type*} (glocOf : β → CPolyG α × CPolyG α)
    (skip : β → Prop) [DecidablePred skip] (m : ℕ) :
    ∀ (xs : List β) (s : CPolyG α × CPolyG α),
      (toPolyG s.1).degree + (m : ℕ) < (toPolyG s.2).degree →
      (∀ b ∈ xs, ¬ skip b →
        (toPolyG (glocOf b).1).degree + (m : ℕ) < (toPolyG (glocOf b).2).degree) →
      let res := xs.foldl
        (fun (gAcc : CPolyG α × CPolyG α) (b : β) =>
          if skip b then gAcc
          else (caddG (cmulG gAcc.1 (glocOf b).2) (cmulG (glocOf b).1 gAcc.2),
                cmulG gAcc.2 (glocOf b).2)) s
      (toPolyG res.1).degree + (m : ℕ) < (toPolyG res.2).degree := by
  intro xs
  induction xs with
  | nil => intro s hs _; exact hs
  | cons b rest ih =>
    intro s hs hmem
    have hrest : ∀ b' ∈ rest, ¬ skip b' →
        (toPolyG (glocOf b').1).degree + (m : ℕ) < (toPolyG (glocOf b').2).degree :=
      fun b' hb' => hmem b' (List.mem_cons_of_mem _ hb')
    simp only [List.foldl_cons]
    by_cases hsk : skip b
    · rw [show (if skip b then s
          else (caddG (cmulG s.1 (glocOf b).2) (cmulG (glocOf b).1 s.2),
                cmulG s.2 (glocOf b).2)) = s from if_pos hsk]
      exact ih s hs hrest
    · set snew : CPolyG α × CPolyG α :=
        (caddG (cmulG s.1 (glocOf b).2) (cmulG (glocOf b).1 s.2), cmulG s.2 (glocOf b).2) with hsnew
      rw [show (if skip b then s
          else (caddG (cmulG s.1 (glocOf b).2) (cmulG (glocOf b).1 s.2),
                cmulG s.2 (glocOf b).2)) = snew from if_neg hsk]
      have hgloc : (toPolyG (glocOf b).1).degree + (m : ℕ) < (toPolyG (glocOf b).2).degree :=
        hmem b List.mem_cons_self hsk
      have hsnew_margin : (toPolyG snew.1).degree + (m : ℕ) < (toPolyG snew.2).degree := by
        rw [hsnew]; exact toPolyG_fracAddG_margin m hs hgloc
      exact ih snew hsnew_margin hrest

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- The residual `a/d − D(g)` is proper for `deg Dt ≥ 2`, conditional on the `(deg Dt − 1)` margin of `g`:
for `resNum = a·gden² − d·(cmonomialDeriv Dt gnum · gden − gnum · cmonomialDeriv Dt gden)`, `resDen =
d·gden²`, `deg resNum < deg resDen`, given `a/d` proper and the margin
`deg gnum + max(0, deg Dt − 1) < deg gden`. -/
theorem toPolyG_residualFraction_proper_of_margin (Dt a d gnum gden : CPolyG α) (hden : toPolyG gden ≠ 0)
    (haProper : (toPolyG a).degree < (toPolyG d).degree)
    (hmargin :
      (toPolyG gnum).degree + (max 0 ((toPolyG Dt).natDegree - 1) : ℕ) < (toPolyG gden).degree) :
    (toPolyG (csubG (cmulG a (cmulG gden gden))
        (cmulG d (csubG (cmulG (cmonomialDeriv Dt gnum) gden)
          (cmulG gnum (cmonomialDeriv Dt gden)))))).degree
      < (toPolyG (cmulG d (cmulG gden gden))).degree :=
  toPolyG_resNum_proper a d gden _ haProper
    (toPolyG_gprimeNum_proper_of_margin Dt gnum gden hden hmargin)

/-! ### The inner-loop `g`-properness — each per-factor `gloc` contribution is proper -/

/-- A reduced cofactor is proper for a positive power of the modulus: from `deg b < deg v` and `v ≠ 0`,
`deg b < deg (v^(n+1))`. -/
theorem degree_lt_pow_succ_of_degree_lt {K : Type*} [Field K] {b v : K[X]} (n : ℕ)
    (hbv : b.degree < v.degree) (hv : v ≠ 0) :
    b.degree < (v ^ (n + 1)).degree := by
  refine lt_of_lt_of_le hbv ?_
  rw [Polynomial.degree_pow]
  calc v.degree = (1 : ℕ) • v.degree := (one_smul _ _).symm
    _ ≤ (n + 1) • v.degree := by
        apply nsmul_le_nsmul_left _ (by omega)
        rw [Polynomial.degree_eq_natDegree hv]; exact_mod_cast Nat.zero_le _

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- One inner-Hermite summand `b/vʲ` is proper: the per-power contribution `(b, cpowG v (j+1))` satisfies
`deg b < deg(v^(j+1))`, given the cofactor bound `deg b < deg v` and `v ≠ 0`. -/
theorem toPolyG_inner_summand_proper (b v : CPolyG α) (j : ℕ)
    (hbv : (toPolyG b).degree < (toPolyG v).degree) (hv : toPolyG v ≠ 0) :
    (toPolyG b).degree < (toPolyG (cpowG v (j + 1))).degree := by
  simpa using degree_lt_pow_succ_of_degree_lt j hbv hv

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The inner Hermite loop's accumulated `g` is proper from inner-factor data. -/
theorem cHermiteReduceTowerInner_g_proper (Dt : CPolyG α) (v u : CPolyG α)
    (hfac : IsHermiteInnerFactor Dt v u) :
    ∀ (j : ℕ) (a : CPolyG α) (g : CPolyG α × CPolyG α),
      (toPolyG g.1).degree < (toPolyG g.2).degree →
      (toPolyG (cHermiteReduceTowerInnerWf Dt v u j a g).1.1).degree
        < (toPolyG (cHermiteReduceTowerInnerWf Dt v u j a g).1.2).degree := by
  intro j
  induction j with
  | zero => intro a g hg; exact hg
  | succ j ih =>
    intro a g hg
    rw [cHermiteReduceTowerInnerWf]
    -- the step's summand `(b, cpowG v (j+1))` is proper, so the `fracAddG` step preserves properness.
    set rhs := cscaleG (CField.neg (CField.inv (cnatCastG (j + 1)))) a with hrhs
    set b := (cdiophantineG (cmulG u (cmonomialDeriv Dt v)) v rhs).1 with hbdef
    have hbproper : (toPolyG b).degree
        < (toPolyG (cpowG v (j + 1))).degree :=
      toPolyG_inner_summand_proper b v j (hfac.cofactor_proper rhs) hfac.nonzero
    have hstep : (toPolyG (caddG (cmulG g.1 (cpowG v (j + 1))) (cmulG b g.2))).degree
        < (toPolyG (cmulG g.2 (cpowG v (j + 1)))).degree :=
      toPolyG_fracAddG_proper (gAcc := g) (gloc := (b, cpowG v (j + 1))) hg hbproper
    exact ih _ _ hstep

omit [CDiffField α] [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The Hermite seed pair `([CField.zero], [CField.one])` is proper under `toPolyG`:
`deg (toPolyG [CField.zero]) < deg (toPolyG [CField.one])` (`⊥ < 0`). -/
theorem toPolyG_seedPair_proper :
    (toPolyG ([CField.zero] : CPolyG α)).degree < (toPolyG ([CField.one] : CPolyG α)).degree := by
  have hzero : toPolyG ([CField.zero] : CPolyG α) = 0 := by
    simp only [denote, map_zero, mul_zero, add_zero]
  have hone : toPolyG ([CField.one] : CPolyG α) = 1 := by
    simp only [denote, map_one, mul_zero, add_zero]
  rw [hzero, hone, Polynomial.degree_zero, Polynomial.degree_one]
  exact bot_lt_iff_ne_bot.mpr (by simp)

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- Each per-factor `gloc` contribution is proper from inner-factor data. -/
theorem cHermiteReduceTowerInner_gloc_proper (Dt : CPolyG α) (vi u : CPolyG α) (j : ℕ)
    (a : CPolyG α) (hfac : IsHermiteInnerFactor Dt vi u) :
    (toPolyG (cHermiteReduceTowerInnerWf Dt vi u j a ([CField.zero], [CField.one])).1.1).degree
      < (toPolyG (cHermiteReduceTowerInnerWf Dt vi u j a ([CField.zero], [CField.one])).1.2).degree :=
  cHermiteReduceTowerInner_g_proper Dt vi u hfac j a ([CField.zero], [CField.one])
    toPolyG_seedPair_proper

/-! ### The assembled `g` is proper — the outer Hermite fold -/

omit [CDiffFieldSpec α] [Algebra ℚ (CFieldSpec.K α)] in
/-- The assembled Hermite rational part `g` is proper from outer factor data. -/
theorem cHermiteReduceTowerG_g_proper (Dt : CPolyG α) (a d : CPolyG α)
    (factors : List (CPolyG α))
    (hfac : IsHermiteFactorData Dt d factors) :
    (toPolyG (factors.zipIdx.foldl
        (fun (gAcc : CPolyG α × CPolyG α) (vi, idx) =>
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
        (fun (gAcc : CPolyG α × CPolyG α) (vi, idx) =>
          let i := idx + 1
          if i ≤ 1 then gAcc
          else
            let Vi_pow := cpowG vi i
            let u := cdivWf d Vi_pow
            let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a
              ([CField.zero], [CField.one])).1
            (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
        ([CField.zero], [CField.one])).2).degree :=
  foldl_guarded_fracAddG_proper
    (glocOf := fun (p : CPolyG α × ℕ) =>
      (cHermiteReduceTowerInnerWf Dt p.1 (cdivWf d (cpowG p.1 (p.2 + 1))) (p.2 + 1 - 1) a
        ([CField.zero], [CField.one])).1)
    (skip := fun (p : CPolyG α × ℕ) => p.2 + 1 ≤ 1)
    factors.zipIdx ([CField.zero], [CField.one]) toPolyG_seedPair_proper
    (fun p hp hskip => cHermiteReduceTowerInner_gloc_proper Dt p.1
      (cdivWf d (cpowG p.1 (p.2 + 1))) (p.2 + 1 - 1) a (hfac p hp hskip))

/-! ### The residual is proper for `deg Dt ≤ 1` from input properness alone -/

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- The residual `a/d − D(g)` is proper for `deg Dt ≤ 1` from outer factor data. -/
theorem cHermiteReduceTowerG_residual_proper_of_degree_le_one (Dt : CPolyG α) (a d : CPolyG α)
    (factors : List (CPolyG α)) (hDt : (toPolyG Dt).natDegree ≤ 1)
    (haProper : (toPolyG a).degree < (toPolyG d).degree)
    (hfac : IsHermiteFactorData Dt d factors) :
    let g := factors.zipIdx.foldl
      (fun (gAcc : CPolyG α × CPolyG α) (vi, idx) =>
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
      < (toPolyG (cmulG d (cmulG g.2 g.2))).degree := by
  intro g
  have hgproper : (toPolyG g.1).degree < (toPolyG g.2).degree :=
    cHermiteReduceTowerG_g_proper Dt a d factors hfac
  exact toPolyG_residualFraction_proper_of_degree_le_one Dt a d g.1 g.2
    (Polynomial.ne_zero_of_degree_gt hgproper) hDt haProper hgproper

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- The residual `a/d − D(g)` is proper for `deg Dt ≥ 2`, gated on the assembled `g` margin. -/
theorem cHermiteReduceTowerG_residual_proper_of_margin_conditional (Dt : CPolyG α) (a d : CPolyG α)
    (factors : List (CPolyG α))
    (haProper : (toPolyG a).degree < (toPolyG d).degree)
    (hfac : IsHermiteFactorData Dt d factors)
    (hmargin :
      (toPolyG (factors.zipIdx.foldl
        (fun (gAcc : CPolyG α × CPolyG α) (vi, idx) =>
          let i := idx + 1
          if i ≤ 1 then gAcc
          else
            let Vi_pow := cpowG vi i
            let u := cdivWf d Vi_pow
            let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a
              ([CField.zero], [CField.one])).1
            (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
        ([CField.zero], [CField.one])).1).degree
          + (max 0 ((toPolyG Dt).natDegree - 1) : ℕ)
        < (toPolyG (factors.zipIdx.foldl
        (fun (gAcc : CPolyG α × CPolyG α) (vi, idx) =>
          let i := idx + 1
          if i ≤ 1 then gAcc
          else
            let Vi_pow := cpowG vi i
            let u := cdivWf d Vi_pow
            let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a
              ([CField.zero], [CField.one])).1
            (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
        ([CField.zero], [CField.one])).2).degree) :
    let g := factors.zipIdx.foldl
      (fun (gAcc : CPolyG α × CPolyG α) (vi, idx) =>
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
      < (toPolyG (cmulG d (cmulG g.2 g.2))).degree := by
  intro g
  have hgproper : (toPolyG g.1).degree < (toPolyG g.2).degree :=
    cHermiteReduceTowerG_g_proper Dt a d factors hfac
  exact toPolyG_residualFraction_proper_of_margin Dt a d g.1 g.2
    (Polynomial.ne_zero_of_degree_gt hgproper) haProper hmargin

omit [Algebra ℚ (CFieldSpec.K α)] in
/-- **The `cHermiteReduceTowerG` leftover is proper for `deg Dt ≤ 1`** (generic, `degree` form, no
splitting): `deg (…).2.1 < deg (…).2.2`. Assembles the residual-fraction properness
(`cHermiteReduceTowerG_residual_proper_of_degree_le_one`, from input properness `deg a < deg d` + `deg Dt ≤ 1`
+ the per-factor nonzero/Bézout hypotheses) with the exact-division degree cancellation
(`cHermiteReduceTowerG_leftover_proper_of_residual`, via the `.2.1`/`.2.2` projections + the residual
divisibility `hdvd`). The generic core of `hAD` (the `QFunNZG ℚ` `_numer_degree_lt` reads off `s.card` from
this by splitting; this stops at the split-free `degree` comparison). -/
theorem cHermiteReduceTowerG_leftover_proper_of_degree_le_one [CFracGcdCoreWf α] (Dt a d : CPolyG α)
    (hDtdeg : (toPolyG Dt).natDegree ≤ 1)
    (haProper : (toPolyG a).degree < (toPolyG d).degree)
    (hfac : IsHermiteFactorData Dt d (cSqfreeYunFFG d))
    (g : CPolyG α × CPolyG α)
    (hgeq : g = (cSqfreeYunFFG d).zipIdx.foldl
      (fun (gAcc : CPolyG α × CPolyG α) (vi, idx) =>
          let i := idx + 1
          if i ≤ 1 then gAcc
          else
            let Vi_pow := cpowG vi i
            let u := cdivWf d Vi_pow
            let gloc := (cHermiteReduceTowerInnerWf Dt vi u (i - 1) a ([CField.zero], [CField.one])).1
            (caddG (cmulG gAcc.1 gloc.2) (cmulG gloc.1 gAcc.2), cmulG gAcc.2 gloc.2))
      ([CField.zero], [CField.one]))
    (hdvd : toPolyG (cmulG d (cmulG g.2 g.2))
      ∣ toPolyG (cmulG (csubG (cmulG a (cmulG g.2 g.2))
          (cmulG d (csubG (cmulG (cmonomialDeriv Dt g.1) g.2) (cmulG g.1 (cmonomialDeriv Dt g.2)))))
        ((cSqfreeYunFFG d).foldl (fun acc vi => cmulG acc vi) [CField.one])))
    (hresDen : cnormG (cmulG d (cmulG g.2 g.2)) ≠ ([] : CPolyG α))
    (hDstar : toPolyG ((cSqfreeYunFFG d).foldl (fun acc vi => cmulG acc vi) [CField.one]) ≠ 0) :
    (toPolyG (cHermiteReduceTowerG Dt a d).2.1).degree
      < (toPolyG (cHermiteReduceTowerG Dt a d).2.2).degree := by
  have hresProper := cHermiteReduceTowerG_residual_proper_of_degree_le_one Dt a d
    (cSqfreeYunFFG d) hDtdeg haProper hfac
  simp only at hresProper
  subst hgeq
  exact cHermiteReduceTowerG_leftover_proper_of_residual Dt a d
    (csubG (cmulG a (cmulG _ _))
      (cmulG d (csubG (cmulG (cmonomialDeriv Dt _) _) (cmulG _ (cmonomialDeriv Dt _)))))
    (cmulG d (cmulG _ _))
    ((cSqfreeYunFFG d).foldl (fun acc vi => cmulG acc vi) [CField.one])
    (by simp only [cHermiteReduceTowerG, denote])
    (by simp only [cHermiteReduceTowerG, denote])
    hdvd hresDen hDstar hresProper

end DeepWiki.SymbolicIntegration
