import DeepWiki.SymbolicIntegration.Engine.Tower.Lvl2
import DeepWiki.SymbolicIntegration.Engine.RischFieldCore
import DeepWiki.SymbolicIntegration.Engine.RischFieldSpec
import DeepWiki.ComputableAlgebra.PolyEngine

/-! # Core hyperexponential Laurent integration helpers

Generic Laurent coefficient integration for a hyperexponential monomial over an abstract `CRischField`.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u v

namespace DensePoly

/-! ### One Laurent coefficient's RDE solve — `Dqⱼ + (jη)qⱼ = aⱼ`

For each Laurent term `qⱼ tʲ`, `D(qⱼ tʲ) = aⱼ tʲ` reduces to the base RDE `Dqⱼ + (j·η)·qⱼ = aⱼ` over `α`. -/

variable {α : Type*} [CField α] [CRischField α]

/-- Signed scalar `cLaurentShift η j = j·η ∈ α`, the base-RDE coefficient of `Dqⱼ + (j·η)·qⱼ = aⱼ`. -/
def cLaurentShift (η : α) (j : ℤ) : α :=
  let n : α := CField.natCast j.natAbs
  let nsigned : α := if j < 0 then CCommRing.neg n else n
  CCommRing.mul nsigned η

/-- One Laurent term's antiderivative coefficient `cLaurentIntCoeff η j aⱼ = some qⱼ` solving
`Dqⱼ + (j·η)·qⱼ = aⱼ` via `CRischField.crischDESolve`, or `none` if non-elementary. -/
def cLaurentIntCoeff (η : α) (j : ℤ) (aj : α) : Option α :=
  CRischField.crischDESolve (cLaurentShift η j) aj

/-- The coefficient RDE for one hyperexponential Laurent term is denotationally solvable. -/
def IsLaurentCoefficientSolvable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α]
    [CDiffFieldSpec α] (η : α) (j : ℤ) (aj : α) : Prop :=
  CFieldRDESolvable (cLaurentShift η j) aj

/-- Field RDE completeness makes a solvable Laurent coefficient executable. -/
theorem cLaurentIntCoeff_exists_of_solvable
    [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    (hcomplete : CRischFieldComplete α) (η : α) (j : ℤ) (aj : α)
    (hsolvable : IsLaurentCoefficientSolvable η j aj) :
    ∃ q, cLaurentIntCoeff η j aj = some q :=
  crischDESolve_exists_of_complete hcomplete (cLaurentShift η j) aj hsolvable

/-- If every indexed Laurent coefficient is executable, the coefficient solve loop succeeds. -/
theorem laurentSolveLoop_exists {α : Type*} [CField α] [CFieldSpec α] [CDiffField α]
    [CDiffFieldSpec α] [CRischField α] (η : α) (shift : ℕ → ℤ) :
    ∀ (coeffs : List α) (start : ℕ),
      (∀ ck ∈ coeffs.zipIdx start,
        ∃ q, cLaurentIntCoeff η (shift ck.2) ck.1 = some q) →
      ∃ solved,
        (coeffs.zipIdx start).foldr (fun ck acc =>
          match acc with
          | none => none
          | some tail =>
            match cLaurentIntCoeff η (shift ck.2) ck.1 with
            | none => none
            | some q => some (q :: tail)) (some []) = some solved := by
  intro coeffs
  induction coeffs with
  | nil =>
      intro start _
      exact ⟨[], by simp⟩
  | cons a rest ih =>
      intro start hall
      have hhead : ∃ q, cLaurentIntCoeff η (shift start) a = some q := by
        apply hall (a, start)
        rw [List.zipIdx_cons]
        exact List.mem_cons_self
      have htail : ∀ ck ∈ rest.zipIdx (start + 1),
          ∃ q, cLaurentIntCoeff η (shift ck.2) ck.1 = some q := by
        intro ck hck
        apply hall ck
        rw [List.zipIdx_cons]
        exact List.mem_cons.mpr (Or.inr hck)
      obtain ⟨tail, htailRun⟩ := ih (start + 1) htail
      obtain ⟨q, hq⟩ := hhead
      refine ⟨q :: tail, ?_⟩
      rw [List.zipIdx_cons, List.foldr_cons, htailRun, hq]

/-! ### The Laurent special-part integrator over the tower

`cIntegrateHyperexpLaurent η pos neg` integrates a Laurent polynomial `∑ⱼ aⱼ tʲ` term by term. -/

/-- Hyperexponential Laurent special-part integrator `cIntegrateHyperexpLaurent η pos neg =
some (num, den)`: integrate `∑ⱼ aⱼ tʲ`, with `pos[k] = a_k` (`k ≥ 0`) and `neg[i] = a_{-(i+1)}`, returning
`num/den` with `den = tᵐ` (`m = neg.length`) and `num[j+m] = qⱼ` from the per-term RDE; `none` if any term
is non-elementary. -/
def cIntegrateHyperexpLaurent {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CRischField α] (η : α) (pos : P α) (neg : List α) :
    Option (P α × P α) :=
  let m : ℕ := (neg : List α).length
  -- the negative tail: index `−(i+1)` solved with shift `−(i+1)`, placed at `num`-index `m−1−i`.
  let negQ : Option (List α) :=
    (neg.zipIdx).foldr (fun (ai, i) acc =>
      match acc with
      | none => none
      | some tail =>
        match cLaurentIntCoeff η (-(i + 1 : ℤ)) ai with
        | none => none
        | some q => some (q :: tail)) (some [])
  -- the non-negative part: index `k` solved with shift `k`, placed at `num`-index `m+k`.
  let posInput : List α := CPolyEngine.coeffList pos
  let posQ : Option (List α) :=
    (posInput.zipIdx).foldr (fun (ak, k) acc =>
      match acc with
      | none => none
      | some tail =>
        match cLaurentIntCoeff η (k : ℤ) ak with
        | none => none
        | some q => some (q :: tail)) (some [])
  match negQ, posQ with
  | some negCoeffs, some posCoeffs =>
    -- `negCoeffs[i] = q_{−(i+1)}`; in `num` (index `j+m`) these go to indices `m-1, m-2, …, 0`,
    -- i.e. the reversed list is `num[0..m-1]`. `posCoeffs[k] = q_k` go to `num[m..]`.
    let num : P α := CPolyEngine.ofCoeffList (negCoeffs.reverse ++ posCoeffs)
    let den : P α := CPolyEngine.monomial (P := P) CCommRing.one m
    some (num, den)
  | _, _ => none

/-- Semantic domain for Laurent integration: every coefficient RDE is solvable in the base field. -/
def HyperexpLaurentDomain {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    (η : α) (pos : P α) (neg : List α) : Prop :=
  (∀ ck ∈ neg.zipIdx,
    IsLaurentCoefficientSolvable η (-(ck.2 + 1 : ℤ)) ck.1) ∧
  ∀ ck ∈ (CPolyEngine.coeffList pos).zipIdx,
    IsLaurentCoefficientSolvable η (ck.2 : ℤ) ck.1

/-- A complete field RDE oracle makes Laurent integration succeed on its semantic domain. -/
theorem cIntegrateHyperexpLaurent_exists_of_domain
    {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CRischField α] (hcomplete : CRischFieldComplete α)
    (η : α) (pos : P α) (neg : List α)
    (hdomain : HyperexpLaurentDomain η pos neg) :
    ∃ num den, cIntegrateHyperexpLaurent η pos neg = some (num, den) := by
  have hnegExec : ∀ ck ∈ neg.zipIdx,
      ∃ q, cLaurentIntCoeff η (-(ck.2 + 1 : ℤ)) ck.1 = some q := by
    intro ck hck
    exact cLaurentIntCoeff_exists_of_solvable hcomplete η (-(ck.2 + 1 : ℤ)) ck.1
      (hdomain.1 ck hck)
  have hposExec : ∀ ck ∈ (CPolyEngine.coeffList pos).zipIdx,
      ∃ q, cLaurentIntCoeff η (ck.2 : ℤ) ck.1 = some q := by
    intro ck hck
    exact cLaurentIntCoeff_exists_of_solvable hcomplete η (ck.2 : ℤ) ck.1
      (hdomain.2 ck hck)
  obtain ⟨negCoeffs, hneg⟩ := laurentSolveLoop_exists η (fun i => -(i + 1 : ℤ)) neg 0 hnegExec
  obtain ⟨posCoeffs, hpos⟩ := laurentSolveLoop_exists η (fun i => (i : ℤ))
    (CPolyEngine.coeffList pos) 0 hposExec
  refine ⟨CPolyEngine.ofCoeffList (negCoeffs.reverse ++ posCoeffs),
    CPolyEngine.monomial CCommRing.one neg.length, ?_⟩
  simp only [cIntegrateHyperexpLaurent, hneg, hpos]

/-- Every successful Laurent integration result has a nonzero monomial denominator. -/
theorem cIntegrateHyperexpLaurent_den_nonzero
    {P : Type u → Type u} [CPoly P] [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CRischField α]
    (η : α) (pos : P α) (neg : List α) (num den : P α)
    (hsome : cIntegrateHyperexpLaurent η pos neg = some (num, den)) :
    CPoly.toPoly den ≠ 0 := by
  rw [cIntegrateHyperexpLaurent] at hsome
  split at hsome
  · rename_i negCoeffs posCoeffs hneg hpos
    simp only [Option.some.injEq, Prod.mk.injEq] at hsome
    obtain ⟨_hnum, hden⟩ := hsome
    subst den
    rw [LawfulCPolyEngine.toPoly_monomial]
    simp only [toR_eq_toK, CFieldSpec.toK_one, map_one, one_mul]
    exact pow_ne_zero _ Polynomial.X_ne_zero
  · simp at hsome

/-- The Laurent integrator executes on sparse polynomials without a separate sparse algorithm. -/
example :
    (match cIntegrateHyperexpLaurent (P := CPoly.SparsePoly) (1 : ℚ)
        (CPoly.SparsePoly.ofList []) [(1 : ℚ)] with
      | some (num, den) =>
          decide (CPoly.coeff num 0 = (-1 : ℚ)) && decide (CPolyEngine.cdeg den = 1)
      | none => false) = true := by
  native_decide

/-! ### Reading the negative Laurent coefficients off the special part `b/dₛ`

For a hyperexponential `t`, `dₛ = c·tᵐ`, so `b/dₛ = ∑_{k=0}^{m-1} (b_k / c) t^{k-m}`. -/

/-- Negative Laurent coefficients `cHyperexpSpecialNeg b ds = [a₋₁, …, a₋ₘ]` of the special part `b/dₛ`
with `dₛ = c·tᵐ` (`m = cdeg ds`, `c = clead ds`): `a_{-(i+1)} = b_{m-1-i} / c`; `[]` if `dₛ` is
constant. -/
def cHyperexpSpecialNeg {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] (b ds : P α) : List α :=
  let m : ℕ := CPolyEngine.cdeg ds
  if CPolyEngine.cisZero ds then []
  else if m = 0 then []
  else
    let c : α := CPolyEngine.clead ds
    let cinv : α := CField.inv c
    -- coefficient of `t^{-(i+1)}` is `b_{m-1-i}/c`, for `i = 0 … m-1`.
    (List.range m).map (fun i =>
      let k : ℕ := m - 1 - i
      CCommRing.mul (CPoly.coeff b k) cinv)

/-- Negative Laurent coefficient extraction executes on sparse numerator and denominator polynomials. -/
example :
    cHyperexpSpecialNeg
      (CPoly.SparsePoly.ofList [(0, (2 : ℚ)), (1, 4)])
      (CPoly.SparsePoly.ofList [(2, (2 : ℚ))]) = [2, 1] := by
  native_decide

end DensePoly

end DeepWiki.SymbolicIntegration
