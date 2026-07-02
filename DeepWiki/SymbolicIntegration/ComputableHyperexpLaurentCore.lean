import DeepWiki.SymbolicIntegration.ComputableTowerField
import DeepWiki.SymbolicIntegration.ComputableRischFieldCore

/-! # Core hyperexponential Laurent integration helpers

Generic §5.10 Laurent coefficient integration over an abstract `CRischField`, separated from the
recursive tower RDE engine and concrete examples.
-/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

namespace CPolyG

/-! ### One Laurent coefficient's RDE solve — `Dqⱼ + (jη)qⱼ = aⱼ`

For a Laurent index `j : ℤ` and coefficient `aⱼ ∈ α`, the antiderivative term `qⱼ tʲ` needs
`D(qⱼ tʲ) = aⱼ tʲ`. Since `D(qⱼ tʲ) = (Dqⱼ + j·η·qⱼ) tʲ` for a hyperexponential `t` (`Dt = η·t`), this is
the base RDE `Dqⱼ + (j·η)·qⱼ = aⱼ` over `α`, solved by `CRischField.crischDESolve`. The coefficient `j·η`
is `cnatCastG |j| · η` with the sign of `j` (so `j = 0` gives coefficient `0` — the pure base integration
`Dq₀ = a₀`). -/

variable {α : Type*} [CField α] [CRischField α]

/-- The signed scalar `cLaurentShiftG η j = j·η ∈ α`: lift the (signed) Laurent index `j : ℤ`
via `cnatCastG |j|`, negate for `j < 0`, and multiply by `η`. The base-RDE coefficient of the
per-term equation `Dqⱼ + (j·η)·qⱼ = aⱼ`; `j = 0` gives `0` (pure integration `Dq₀ = a₀`). -/
def cLaurentShiftG (η : α) (j : ℤ) : α :=
  let n : α := cnatCastG j.natAbs
  let nsigned : α := if j < 0 then CField.neg n else n
  CField.mul nsigned η

/-- One Laurent term's antiderivative coefficient `cLaurentIntCoeffG η j aⱼ = some qⱼ` with
`Dqⱼ + (j·η)·qⱼ = aⱼ` over `α`, or `none` if non-elementary. Routes the base RDE to the oracle
`CRischField.crischDESolve (cLaurentShiftG η j) aⱼ`; for `j = 0` the coefficient is `0`, so this is
the base integration `Dq₀ = a₀`. -/
def cLaurentIntCoeffG (η : α) (j : ℤ) (aj : α) : Option α :=
  CRischField.crischDESolve (cLaurentShiftG η j) aj

/-! ### The §5.10 Laurent special-part integrator over the tower

`cIntegrateHyperexpLaurentG η pos neg` integrates a Laurent polynomial `∑ⱼ aⱼ tʲ` of a
hyperexponential `t` (`Dt = η·t`), given its coefficients as two lists: `pos : CPolyG α` for the
non-negative indices (`pos[k] = a_k`, `k ≥ 0`, the polynomial part `fₚ` together with the constant `a₀`)
and `neg : List α` for the negative indices (`neg[i] = a_{-(i+1)}`, the special tail `fₛ`). It solves each
`qⱼ` by `cLaurentIntCoeffG` and assembles `∑ⱼ qⱼ tʲ = num/tᵐ` (`m = neg.length`, `num[j+m] = qⱼ`). Returns
`none` if any coefficient is non-elementary. -/

/-- Hyperexponential Laurent special-part integrator `cIntegrateHyperexpLaurentG η pos neg =
some (num, den)`: integrate the Laurent polynomial `∑ⱼ aⱼ tʲ` of a hyperexponential `t` (`Dt = η·t`),
with `pos[k] = a_k` (`k ≥ 0`) and `neg[i] = a_{-(i+1)}`, returning `∫ = num/den` with `den = tᵐ`
(`m = neg.length`) and `num[j+m] = qⱼ` (`qⱼ` from the per-term RDE via `cLaurentIntCoeffG`). `none` if
any term is non-elementary. The negatives sit at `num`-indices `0…m−1` (index `−(i+1) ↦ m−1−i`), the
non-negatives at `m…m+n` (index `k ↦ m+k`). Runs at any tower level. -/
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

For a hyperexponential `t`, the canonical-split special part `fₛ = b/dₛ` has `dₛ` a power of `t` (the only
special irreducible), i.e. `dₛ = c·tᵐ` — a single nonzero coefficient `c` at index `m = deg_t dₛ`. Then
`b/dₛ = ∑_{k=0}^{m-1} (b_k / c) t^{k-m}`, so the coefficient of `t^{-(i+1)}` (`i = 0…m−1`) is
`b_{m-1-i} / c`. `cHyperexpSpecialNegG` produces this `neg`-list. -/

/-- Negative Laurent coefficients of the hyperexponential special part `cHyperexpSpecialNegG b ds =
[a₋₁, a₋₂, …, a₋ₘ]` (the `neg`-list for `cIntegrateHyperexpLaurentG`): for `dₛ = c·tᵐ` (a power of `t`,
the hyperexponential special factor; `m = cdegG ds`, `c = cleadG ds`), the special part `b/dₛ =
∑_{k=0}^{m-1} (b_k / c) t^{k-m}`, so `a_{-(i+1)} = b_{m-1-i} / c`. Returns the list indexed by
`i ↦ a_{-(i+1)}`. If `dₛ` is a constant (`m = 0`, no special part), returns `[]`. -/
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
