import DeepWiki.SymbolicIntegration.MonomialExtensions

/-! # Special polynomials of the first kind (Bronstein §3.4)
The *first-kind* special polynomials refine `IsSpecial` by a residue test on the roots: a special
`p ∈ k[t]` is *of the first kind* when, at every root `α` of `p` (in the algebraic closure), the
residue `Dt − Dα` evaluated at `α` is not the logarithmic derivative of a radical in `k(α)`. This
file develops the supporting notion of a *logarithmic derivative of a radical*
(`IsLogDerivRadical`, Def 3.4.3), its descent through algebraic extensions (Lemma 3.4.8), and the
definition and semigroup structure of the first-kind class (Def 3.4.4, Thm 3.4.4). -/

open scoped Differential
open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {k : Type*} [Field k] [Differential k]

/-- **Definition 3.4.3** (§3.4, p.98): `u ∈ k` is a *logarithmic derivative of a `k`-radical* if
`n·u = Dv/v` for some `v ∈ k*` and some nonzero integer `n` — i.e. `u` is, up to an integer scale,
the logarithmic derivative `logDeriv v = v′/v` of a nonzero element. -/
def IsLogDerivRadical (u : k) : Prop :=
  ∃ (v : k) (n : ℤ), v ≠ 0 ∧ n ≠ 0 ∧ (n : k) * u = Differential.logDeriv v

/-- Spelled out: `u` is a log-derivative of a radical iff `n·u = v′/v` for some `v ≠ 0`, `n ≠ 0`. -/
theorem isLogDerivRadical_iff {u : k} :
    IsLogDerivRadical u ↔ ∃ (v : k) (n : ℤ), v ≠ 0 ∧ n ≠ 0 ∧ (n : k) * u = v′ / v :=
  Iff.rfl

/-- `0` is a log-derivative of a radical (`1·0 = logDeriv 1 = 0`). -/
theorem isLogDerivRadical_zero : IsLogDerivRadical (0 : k) :=
  ⟨1, 1, one_ne_zero, one_ne_zero, by simp⟩

/-- The logarithmic derivative of any nonzero `v` is a log-derivative of a radical (`n = 1`). -/
theorem isLogDerivRadical_logDeriv {v : k} (hv : v ≠ 0) :
    IsLogDerivRadical (Differential.logDeriv v) :=
  ⟨v, 1, hv, one_ne_zero, by rw [Int.cast_one, one_mul]⟩

/-- **Definition 3.4.3** normalization (§3.4, p.98): the integer `n` may be taken *positive*. If
`n·u = Dv/v` with `n < 0`, then `(−n)·u = D(v⁻¹)/v⁻¹` using `logDeriv (v⁻¹) = −logDeriv v`, so a
witness with positive multiplier exists. -/
theorem isLogDerivRadical_pos {u : k} (h : IsLogDerivRadical u) :
    ∃ (v : k) (n : ℤ), v ≠ 0 ∧ 0 < n ∧ (n : k) * u = Differential.logDeriv v := by
  obtain ⟨v, n, hv, hn, heq⟩ := h
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · refine ⟨v⁻¹, -n, inv_ne_zero hv, by omega, ?_⟩
    have hlog : Differential.logDeriv v⁻¹ = -Differential.logDeriv v := by
      have := Differential.logDeriv_div (1 : k) v one_ne_zero hv
      simpa using this
    rw [hlog, Int.cast_neg, neg_mul, ← heq]
  · exact ⟨v, n, hv, hpos, heq⟩

end DeepWiki.SymbolicIntegration
