import DeepWiki.SymbolicIntegration.Engine.Tower.Field
import DeepWiki.SymbolicIntegration.Engine.RischFieldCore

/-! # Core hyperexponential Laurent integration helpers

Generic Laurent coefficient integration for a hyperexponential monomial over an abstract `CRischField`.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

/-! ### One Laurent coefficient's RDE solve — `Dqⱼ + (jη)qⱼ = aⱼ`

For each Laurent term `qⱼ tʲ`, `D(qⱼ tʲ) = aⱼ tʲ` reduces to the base RDE `Dqⱼ + (j·η)·qⱼ = aⱼ` over `α`. -/

variable {α : Type*} [CField α] [CRischField α]

/-- Signed scalar `cLaurentShiftG η j = j·η ∈ α`, the base-RDE coefficient of `Dqⱼ + (j·η)·qⱼ = aⱼ`. -/
def cLaurentShiftG (η : α) (j : ℤ) : α :=
  let n : α := cnatCastG j.natAbs
  let nsigned : α := if j < 0 then CField.neg n else n
  CField.mul nsigned η

/-- One Laurent term's antiderivative coefficient `cLaurentIntCoeffG η j aⱼ = some qⱼ` solving
`Dqⱼ + (j·η)·qⱼ = aⱼ` via `CRischField.crischDESolve`, or `none` if non-elementary. -/
def cLaurentIntCoeffG (η : α) (j : ℤ) (aj : α) : Option α :=
  CRischField.crischDESolve (cLaurentShiftG η j) aj

/-! ### The Laurent special-part integrator over the tower

`cIntegrateHyperexpLaurentG η pos neg` integrates a Laurent polynomial `∑ⱼ aⱼ tʲ` term by term. -/

/-- Hyperexponential Laurent special-part integrator `cIntegrateHyperexpLaurentG η pos neg =
some (num, den)`: integrate `∑ⱼ aⱼ tʲ`, with `pos[k] = a_k` (`k ≥ 0`) and `neg[i] = a_{-(i+1)}`, returning
`num/den` with `den = tᵐ` (`m = neg.length`) and `num[j+m] = qⱼ` from the per-term RDE; `none` if any term
is non-elementary. -/
def cIntegrateHyperexpLaurentG (η : α) (pos : CPolyG α) (neg : List α) :
    Option (CPolyG α × CPolyG α) :=
  let m : ℕ := (neg : List α).length
  -- the negative tail: index `−(i+1)` solved with shift `−(i+1)`, placed at `num`-index `m−1−i`.
  let negQ : Option (List α) :=
    (neg.zipIdx).foldr (fun (ai, i) acc =>
      match acc with
      | none => none
      | some tail =>
        match cLaurentIntCoeffG η (-(i + 1 : ℤ)) ai with
        | none => none
        | some q => some (q :: tail)) (some [])
  -- the non-negative part: index `k` solved with shift `k`, placed at `num`-index `m+k`.
  let posQ : Option (List α) :=
    (pos.zipIdx).foldr (fun (ak, k) acc =>
      match acc with
      | none => none
      | some tail =>
        match cLaurentIntCoeffG η (k : ℤ) ak with
        | none => none
        | some q => some (q :: tail)) (some [])
  match negQ, posQ with
  | some negCoeffs, some posCoeffs =>
    -- `negCoeffs[i] = q_{−(i+1)}`; in `num` (index `j+m`) these go to indices `m-1, m-2, …, 0`,
    -- i.e. the reversed list is `num[0..m-1]`. `posCoeffs[k] = q_k` go to `num[m..]`.
    let num : CPolyG α := negCoeffs.reverse ++ posCoeffs
    let den : CPolyG α := cshiftG m [CField.one]
    some (num, den)
  | _, _ => none

/-! ### Reading the negative Laurent coefficients off the special part `b/dₛ`

For a hyperexponential `t`, `dₛ = c·tᵐ`, so `b/dₛ = ∑_{k=0}^{m-1} (b_k / c) t^{k-m}`. -/

/-- Negative Laurent coefficients `cHyperexpSpecialNegG b ds = [a₋₁, …, a₋ₘ]` of the special part `b/dₛ`
with `dₛ = c·tᵐ` (`m = cdegG ds`, `c = cleadG ds`): `a_{-(i+1)} = b_{m-1-i} / c`; `[]` if `dₛ` is
constant. -/
def cHyperexpSpecialNegG (b ds : CPolyG α) : List α :=
  let m : ℕ := cdegG ds
  if cisZeroG ds then []
  else if m = 0 then []
  else
    let c : α := cleadG ds
    let cinv : α := CField.inv c
    -- coefficient of `t^{-(i+1)}` is `b_{m-1-i}/c`, for `i = 0 … m-1`.
    (List.range m).map (fun i =>
      let k : ℕ := m - 1 - i
      CField.mul ((b : List α).getD k CField.zero) cinv)

end CPolyG

end DeepWiki.SymbolicIntegration
