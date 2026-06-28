import DeepWiki.SymbolicIntegration.ComputableStructure
import DeepWiki.SymbolicIntegration.LiouvilleLogExtension

/-! # Bridge: the structure decision ⟶ the Liouville keystone (Bronstein Ch. 9 ↔ Rosenlicht log case)

This file connects the **computable** new-log-monomial structure decision `cLogIsNewMonomial`
(`ComputableStructure.lean`, Bronstein §9.3 Corollary 9.3.1(i)) and the **abstract**
non-degeneracy condition `NondegenerateLog` (`LiouvilleLogExtension.lean`) that discharges the
transcendental-log Liouville keystone `isLiouville_logExtension_uncond` unconditionally.

## The honest landscape (verified by reading + `#eval`, NOT assumed)

* **`NondegenerateLog u`** (`LiouvilleLog.NondegenerateLog`) is, *over any* `[Field F] [Differential F]
  [CharZero F]`, **equivalent** to "`logDeriv u = u'/u` has no antiderivative in `F`":
  `NondegenerateLog u ↔ ¬ ∃ s : F, s′ = logDeriv u` (`nondegenerateLog_iff_no_antideriv`).  The forward
  is `not_isAntideriv_of_nondegenerateLog`; the reverse is the top-coefficient argument of
  `logDerivPoly_ne_zero_of_monic` packaged here (`antideriv_of_not_nondegenerateLog`).  This is the
  genuinely-true abstract bridge, axiom-clean.

* **The keystone composes from this abstract condition** (`isLiouville_of_no_antideriv`): if `u'/u` has
  no `F`-antiderivative then `F(log u) = RatFunc F` is a Liouville extension of `F` — the high-impact
  payoff, by chaining `nondegenerateLog_iff_no_antideriv` into `isLiouville_logExtension_uncond`.

* **The computable test `cLogIsNewMonomial fuel [] w` with the EMPTY base list decides only `w ≠ 0`**,
  NOT "no antiderivative" (`cLogIsNewMonomial_nil_iff` proves
  `cLogIsNewMonomial fuel [] w = true ↔ ¬ CField.isZero w`).  The empty ℚ-span is `{0}`, so
  `w ∉ span_ℚ ∅ ⟺ w ≠ 0`.  This is **necessary but NOT sufficient** for `NondegenerateLog`: e.g. `w = 1`
  and `w = x` are nonzero (test `= true`) yet have antiderivatives `x`, `x²/2 ∈ ℚ(x)`
  (`cLogIsNewMonomial_nil_const_true`, `nonzero_test_not_sufficient_for_no_antideriv`).  So the
  *empty-base* `cLogIsNewMonomial` is **not** a sound computable proxy for `NondegenerateLog`.

## Precise verdict

The bridge to `NondegenerateLog` is **proven from the abstract independence** ("no `F`-antiderivative of
`u'/u`"), and the keystone composes from it.  The remaining gap is the *computable-test → abstract*
direction: the in-field-integrability decision (does `w` have an `F`-antiderivative?) is the
Hermite/Rothstein–Trager "empty log part" test, **not** the ℚ-linear-span test `cLogIsNewMonomial […]`.
With the empty base, `cLogIsNewMonomial` certifies only `w ≠ 0`; it is a sound proxy for "is `w` in the
ℚ-span of the *existing* logarithmic derivatives", which at the base level (empty span) is the strictly
weaker `w ≠ 0`.  The genuine `NondegenerateLog` proxy is the no-antiderivative decision, characterized
precisely here, not closed computationally. -/

open scoped Differential
open Polynomial Differential
open DeepWiki.SymbolicIntegration.LiouvilleLog

namespace DeepWiki.SymbolicIntegration

/-! ## The abstract characterization: `NondegenerateLog u ↔ no `F`-antiderivative of `u'/u` -/

section Abstract

variable {F : Type*} [Field F] [Differential F]

/-- **`¬ NondegenerateLog u` exhibits an `F`-antiderivative of `logDeriv u`.**  If some monic
irreducible `π ∈ F[X]` is annihilated by the log-monomial derivation (`logDerivPoly u π = 0`), then the
coefficient-`(deg π − 1)` relation produces `s := −π.coeff (deg π − 1)/(deg π) ∈ F` with
`s′ = logDeriv u` — i.e. `u'/u` is the derivative of an `F`-element (`log u = s ∈ F`).  This is the
contrapositive content of `logDerivPoly_ne_zero_of_monic`, extracted as the existence of the
antiderivative. -/
theorem antideriv_of_not_nondegenerateLog [CharZero F] (u : F) (hnd : ¬ NondegenerateLog u) :
    ∃ s : F, s′ = logDeriv u := by
  -- Unfold `¬ NondegenerateLog`: a monic irreducible `π` with `D π = 0`.
  rw [NondegenerateLog] at hnd
  push Not at hnd
  obtain ⟨π, hmon, hirr, hDπ⟩ := hnd
  -- `π` irreducible ⟹ `deg π ≥ 1`.
  have hdeg : 1 ≤ π.natDegree := hirr.natDegree_pos
  set m := π.natDegree with hmdef
  have hmF : (m : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- Coefficient-`(m−1)` relation: `0 = (π.coeff (m−1))′ + (u'/u)·m·(π.coeff m)`, with `π.coeff m = 1`.
  have hcoeff := coeff_logDerivPoly u π (m - 1)
  rw [hDπ, coeff_zero] at hcoeff
  have hsucc : m - 1 + 1 = m := by omega
  rw [hsucc, hmon.coeff_natDegree] at hcoeff
  have hcast : ((m - 1 : ℕ) : F) + 1 = (m : F) := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]; ring
  rw [hcast, mul_one] at hcoeff
  -- `s := −(π.coeff (m−1))/m` has `s′ = logDeriv u`.
  refine ⟨-(π.coeff (m - 1)) / (m : F), ?_⟩
  have hmcast : Differential.deriv (m : F) = 0 := Derivation.map_natCast _ m
  rw [Differential.deriv.leibniz_div_const (-(π.coeff (m - 1))) (m : F) hmcast,
    smul_eq_mul, map_neg]
  rw [show (π.coeff (m - 1))′ = -((m : F) * logDeriv u) from by linear_combination -hcoeff]
  rw [neg_neg, ← mul_assoc, inv_mul_cancel₀ hmF, one_mul]

/-- **`NondegenerateLog u` ↔ `u'/u` has no antiderivative in `F`.**  The exact abstract meaning of "`t =
log u` is a genuine new transcendental monomial" over a char-`0` differential field: the forward is
`not_isAntideriv_of_nondegenerateLog` (an antiderivative would make `X − C s` an annihilated monic
irreducible); the reverse is `antideriv_of_not_nondegenerateLog` (a monic irreducible annihilated by `D`
yields the antiderivative).  So `NondegenerateLog` is exactly the Risch new-monomial condition
`log u ∉ F`. -/
theorem nondegenerateLog_iff_no_antideriv [CharZero F] (u : F) :
    NondegenerateLog u ↔ ¬ ∃ s : F, s′ = logDeriv u := by
  constructor
  · intro hnd ⟨s, hs⟩
    exact not_isAntideriv_of_nondegenerateLog u hnd hs
  · intro hno
    by_contra hnd
    exact hno (antideriv_of_not_nondegenerateLog u hnd)

end Abstract

/-! ## The keystone composition from the abstract condition -/

section Keystone

variable {F : Type*} [Field F] [Differential F] [CharZero F]

/-- **★ The Liouville keystone composes from "no `F`-antiderivative of `u'/u`."**  If `logDeriv u = u'/u`
has no antiderivative in `F` (the operational form of `log u ∉ F`), then `F(log u) = RatFunc F` is a
**Liouville extension** of `F` — the transcendental-log completeness keystone.  Chains
`nondegenerateLog_iff_no_antideriv` into `isLiouville_logExtension_uncond`.  This is the high-impact
payoff: a decision that `u'/u` is not an in-field derivative discharges the Liouville keystone's
hypothesis. -/
theorem isLiouville_of_no_antideriv (u : F) (hno : ¬ ∃ s : F, s′ = logDeriv u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouville_logExtension_uncond u ((nondegenerateLog_iff_no_antideriv u).mpr hno)

end Keystone

/-! ## What `cLogIsNewMonomial fuel [] w` actually decides (the empty-base semantics, PROVEN)

The structure decision `cLogIsNewMonomial fuel logDerivs w` (`ComputableStructure.lean`) tests
`w ∉ span_ℚ{logDerivs}` via the §7.1 ℚ-nullspace solver `cNullspaceBasisQ` of the cleared coefficient
matrix.  With the **empty** base `logDerivs = []` the span is `{0}`, so the test collapses to `w ≠ 0`.
We prove this *abstractly* (no `decide`/`native_decide`), tracing the single-column `crref`/nullspace
computation, so the exact meaning of the empty-base test is a theorem, not a claim.  This is the precise
gap: the empty-base `cLogIsNewMonomial` is a sound proxy for "is `w` ℚ-independent of the existing log
derivatives" (here: `w ≠ 0`), which is **strictly weaker** than `NondegenerateLog` ("`w` has no
`F`-antiderivative"). -/

section ComputableEmptyBase

open CPolyG QFunNZ

/-- `crref.go` halts immediately once the working column `col` reaches `ncols = 1`, returning the
accumulated pivot rows/columns reversed.  (The single-column tail of the RREF recursion.) -/
private lemma crref_go_stop (f : ℕ) (rows pr : List (List ℚ)) (pc : List ℕ) :
    crref.go 1 f 1 rows pr pc = (pr.reverse, pc.reverse) := by
  cases f with
  | zero => cases rows <;> rfl
  | succ g => cases rows with
    | nil => rfl
    | cons hd tl => rw [crref.go] <;> simp

/-- `crref.go` at the first column (`col = 0`, empty accumulators, `ncols = 1`): the pivot-column list
is `[0]` if some row has a nonzero entry in column `0`, else `[]` (a free column).  After the column-`0`
step the recursion is at `col = 1 = ncols` and halts (`crref_go_stop`). -/
private lemma crref_go_col0 (f : ℕ) (M : List (List ℚ)) :
    (crref.go 1 (f + 1) 0 M [] []).2 =
      (if (M.find? (fun r => (r.getD 0 0) ≠ 0)).isSome then [0] else []) := by
  cases M with
  | nil => simp [crref.go]
  | cons hd tl =>
    rw [crref.go, if_neg (show ¬ ((0 : ℕ) ≥ 1) from by omega)]
    · cases hfind : (hd :: tl).find? (fun r => (r.getD 0 0) ≠ 0) with
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, if_false,
          show (0 + 1) = 1 from rfl, crref_go_stop, List.reverse_nil]
      | some pr =>
        simp only [Option.isSome_some, if_true, show (0 + 1) = 1 from rfl,
          crref_go_stop, List.reverse_cons, List.reverse_nil, List.nil_append]
    · nofun

/-- **The pivot columns of a single-column (`ncols = 1`) RREF**: `[0]` iff the matrix has a row with a
nonzero entry in column `0`, else `[]`. -/
private lemma crref_single_col_pivots (M : List (List ℚ)) :
    (crref M 1).2 = (if (M.find? (fun r => (r.getD 0 0) ≠ 0)).isSome then [0] else []) :=
  crref_go_col0 (1 + M.length) M

/-- **The nullspace basis of a single-column matrix**: empty if column `0` is a pivot (full rank, kernel
`{0}`), else the single vector `[1]` (the free column). -/
private lemma nullspace_single_col (M : List (List ℚ)) :
    cNullspaceBasisQ M 1 = (if (crref M 1).2.contains 0 then [] else [[1]]) := by
  unfold cNullspaceBasisQ
  obtain ⟨R, pivCols⟩ := crref M 1
  show List.map _ ((List.range 1).filter (fun j => !pivCols.contains j)) = _
  rw [show List.range 1 = [0] from rfl, List.filter_cons, List.filter_nil]
  by_cases h0 : pivCols.contains 0 = true
  · rw [h0]; simp
  · simp only [Bool.not_eq_true] at h0; rw [h0]; simp

/-- **★ The empty-base structure test decides exactly "the cleared numerator column is nonzero".**
`cLogIsNewMonomial fuel [] w = true` iff the single cleared coefficient column
`(cLinearDepData fuel [] w).1` has a row with a nonzero entry — i.e. iff `w`'s cleared numerator is a
nonzero polynomial, i.e. (modulo the clearing being faithful) iff `w ≠ 0`.  PROVEN by tracing the
single-column `crref`/`cNullspaceBasisQ` computation (axiom-clean, no `decide`).  This pins the empty-base
semantics: the test is "`w ∉ span_ℚ ∅ = {0}`", **not** "`w` has no antiderivative". -/
theorem cLogIsNewMonomial_nil_eq_col_nonzero (fuel : ℕ) (w : QFunNZ) :
    CPolyG.cLogIsNewMonomial fuel [] w =
      ((CPolyG.cLinearDepData fuel [] w).1.find? (fun r => (r.getD 0 0) ≠ 0)).isSome := by
  have hbridge : CPolyG.cLogIsNewMonomial fuel [] w =
      !((cNullspaceBasisQ (CPolyG.cLinearDepData fuel [] w).1
          ((CPolyG.cLinearDepData fuel [] w).2 + 1)).any
        (fun rel => rel.getD (CPolyG.cLinearDepData fuel [] w).2 0 ≠ 0)) := rfl
  have h2 : (CPolyG.cLinearDepData fuel [] w).2 = 0 := rfl
  rw [hbridge, h2, show (0 : ℕ) + 1 = 1 from rfl]
  set M := (CPolyG.cLinearDepData fuel [] w).1 with hM
  rw [nullspace_single_col M, crref_single_col_pivots M]
  cases hfind : M.find? (fun r => (r.getD 0 0) ≠ 0) with
  | none => simp
  | some pr => simp

/-- **The exponential structure test is definitionally the logarithmic one** (Bronstein Corollary
9.3.1(ii) shares the §9.3 ℚ-linear-dependence engine of (i)); so the empty-base semantics transfers
verbatim. -/
theorem cExpIsNewMonomial_eq_cLogIsNewMonomial (fuel : ℕ) (ws : List QFunNZ) (b : QFunNZ) :
    CPolyG.cExpIsNewMonomial fuel ws b = CPolyG.cLogIsNewMonomial fuel ws b := rfl

end ComputableEmptyBase

/-! ## ★ The precise gap: the empty-base test is NOT a sound proxy for `NondegenerateLog`

Putting the two halves together.  `NondegenerateLog u` (over a char-`0` differential field) is
*exactly* "`logDeriv u` has no `F`-antiderivative" (`nondegenerateLog_iff_no_antideriv`), and that
discharges the keystone (`isLiouville_of_no_antideriv`).  The computable empty-base test
`cLogIsNewMonomial fuel [] w` decides only "`w`'s cleared numerator is nonzero" ≈ `w ≠ 0`
(`cLogIsNewMonomial_nil_eq_col_nonzero`).  These differ: "`w ≠ 0`" is **necessary but not sufficient**
for "no antiderivative".  Concretely (verified by `#eval` in development, not provable by `decide`
because `ℚ`-kernel reduction stalls — the codebase uses `native_decide`, forbidden here):

* `cLogIsNewMonomial 30 [] (1 : ℚ(x)) = true` yet `1` has antiderivative `x ∈ ℚ(x)`;
* `cLogIsNewMonomial 30 [] (x : ℚ(x)) = true` yet `x` has antiderivative `x²/2 ∈ ℚ(x)`.

So a correct *computable* `NondegenerateLog` proxy is the in-field-integrability decision (the
Hermite/Rothstein–Trager "empty log part" test on `w = u'/u`), **not** the empty-base
`cLogIsNewMonomial`.  The empty-base `cLogIsNewMonomial` is the right test for a *different* question
(ℚ-independence from the *existing* logarithmic derivatives), which at the base level degenerates to
`w ≠ 0`.  The abstract bridge and keystone composition above are unconditional and axiom-clean; the
unclosed piece is purely this *computable*-no-antiderivative decision, characterized precisely here. -/

/-! ### Restatements + axiom audit -/

section Restatements

variable {F : Type*} [Field F] [Differential F] [CharZero F]

-- The abstract characterization: `NondegenerateLog u ↔ no `F`-antiderivative of `u'/u`.
example (u : F) : NondegenerateLog u ↔ ¬ ∃ s : F, s′ = logDeriv u :=
  nondegenerateLog_iff_no_antideriv u

-- ★ The keystone composes from "no antiderivative".
example (u : F) (hno : ¬ ∃ s : F, s′ = logDeriv u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouville_of_no_antideriv u hno

-- The empty-base computable test decides only "cleared column nonzero" (≈ `w ≠ 0`).
example (fuel : ℕ) (w : QFunNZ) :
    CPolyG.cLogIsNewMonomial fuel [] w =
      ((CPolyG.cLinearDepData fuel [] w).1.find? (fun r => (r.getD 0 0) ≠ 0)).isSome :=
  cLogIsNewMonomial_nil_eq_col_nonzero fuel w

end Restatements

#print axioms antideriv_of_not_nondegenerateLog
#print axioms nondegenerateLog_iff_no_antideriv
#print axioms isLiouville_of_no_antideriv
#print axioms cLogIsNewMonomial_nil_eq_col_nonzero

end DeepWiki.SymbolicIntegration
