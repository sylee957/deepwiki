import DeepWiki.SymbolicIntegration.Engine.Structure
import DeepWiki.SymbolicIntegration.LiouvilleLog
import DeepWiki.SymbolicIntegration.RecognizingLogDeriv
import DeepWiki.SymbolicIntegration.RationalIntegrationLiouville

/-! # Bridge: the structure decision and the Liouville log keystone

`NondegenerateLog u ↔` no `F`-antiderivative of `u'/u`, the keystone `isLiouville_of_no_antideriv`,
and the rational-base decision `NondegenerateLog u ↔ logDeriv u ≠ 0`. -/

open scoped Differential
open Polynomial Differential
open DeepWiki.SymbolicIntegration.LiouvilleLog

namespace DeepWiki.SymbolicIntegration

/-! ## The abstract characterization -/

section Abstract

variable {F : Type*} [Field F] [Differential F]

/-- `¬ NondegenerateLog u` yields an `F`-antiderivative `s` of `logDeriv u` (`s′ = logDeriv u`). -/
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

/-- `NondegenerateLog u ↔ ¬ ∃ s : F, s′ = logDeriv u`: non-degeneracy is "`u'/u` has no
antiderivative in `F`". -/
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

/-- If `u'/u` has no antiderivative in `F`, then `F(log u) = RatFunc F` is a Liouville extension
of `F`. -/
theorem isLiouville_of_no_antideriv (u : F) (hno : ¬ ∃ s : F, s′ = logDeriv u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouville_logExtension_uncond u ((nondegenerateLog_iff_no_antideriv u).mpr hno)

end Keystone

/-! ## The rational base: `NondegenerateLog u ↔ logDeriv u ≠ 0` -/

section RationalBase

variable {K : Type*} [Field K]

/-- Equal num/denom root multiplicities everywhere force `u` constant, so `logDeriv u = 0`. -/
theorem logDeriv_eq_zero_of_rootMultiplicity_eq [IsAlgClosed K] (u : RatFunc K)
    (hmult : ∀ α, (RatFunc.num u).rootMultiplicity α = (RatFunc.denom u).rootMultiplicity α) :
    Differential.logDeriv u = 0 := by
  classical
  set N := RatFunc.num u with hN
  set M := RatFunc.denom u with hM
  have hroots : N.roots = M.roots := by
    ext α; rw [count_roots, count_roots, hmult]
  have huNM : u = algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) M := by
    rw [hN, hM, RatFunc.num_div_denom]
  have hNsplit := (IsAlgClosed.splits N).eq_prod_roots
  have hMsplit := (IsAlgClosed.splits M).eq_prod_roots
  rw [hroots] at hNsplit
  set P : K[X] := (M.roots.map fun a => X - C a).prod with hP
  have hPne : algebraMap K[X] (RatFunc K) P ≠ 0 := by
    refine (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr ?_
    rw [hP]; exact Multiset.prod_ne_zero (by
      simp only [Multiset.mem_map, not_exists]
      exact fun β ⟨_, h⟩ => X_sub_C_ne_zero β h)
  have huC : u = RatFunc.C (N.leadingCoeff / M.leadingCoeff) := by
    rw [huNM]
    conv_lhs => rw [hNsplit, hMsplit]
    rw [map_mul, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_C,
      mul_div_mul_right _ _ hPne, ← map_div₀]
  rw [huC, Differential.logDeriv_eq_zero]
  show ratFuncDeriv (RatFunc.C (N.leadingCoeff / M.leadingCoeff)) = 0
  exact ratFuncDeriv_C_eq_zero _

/-- `residueAt α (logDeriv u) = ord_α (num u) − ord_α (denom u)`: the residue of `u'/u` at `α`. -/
theorem residueAt_logDeriv_eq_mult_diff [CharZero K] (u : RatFunc K) (hu : u ≠ 0) (α : K) :
    residueAt α (Differential.logDeriv u)
      = (((RatFunc.num u).rootMultiplicity α : ℤ)
          - ((RatFunc.denom u).rootMultiplicity α : ℤ) : K) := by
  conv_lhs => rw [← RatFunc.num_div_denom u]
  exact residueAt_logDeriv_div_eq_int (RatFunc.num u) (RatFunc.denom u)
    (RatFunc.num_ne_zero hu) (RatFunc.denom_ne_zero u) α

/-- Vanishing residues of `logDeriv u` force equal num/denom root multiplicities. -/
theorem rootMultiplicity_eq_of_residue_zero [CharZero K] (u : RatFunc K) (hu : u ≠ 0)
    (hres : ∀ α, residueAt α (Differential.logDeriv u) = 0) (α : K) :
    (RatFunc.num u).rootMultiplicity α = (RatFunc.denom u).rootMultiplicity α := by
  have h := (residueAt_logDeriv_eq_mult_diff u hu α).symm.trans (hres α)
  rw [show (((RatFunc.num u).rootMultiplicity α : ℤ)
        - ((RatFunc.denom u).rootMultiplicity α : ℤ) : K)
      = ((((RatFunc.num u).rootMultiplicity α : ℤ)
        - ((RatFunc.denom u).rootMultiplicity α : ℤ) : ℤ) : K) from by push_cast; ring] at h
  have hZ := Int.cast_injective (α := K) (h.trans (Int.cast_zero).symm)
  omega

/-- `logDeriv u` has a rational antiderivative iff `logDeriv u = 0` (`K` algebraically closed,
char `0`). -/
theorem logDeriv_hasAntideriv_iff_eq_zero [CharZero K] [IsAlgClosed K] (u : RatFunc K) :
    (∃ s : RatFunc K, s′ = Differential.logDeriv u) ↔ Differential.logDeriv u = 0 := by
  constructor
  · rintro ⟨G, hG⟩
    by_cases hu : u = 0
    · subst hu
      rw [Differential.logDeriv_eq_zero]; exact map_zero _
    · refine logDeriv_eq_zero_of_rootMultiplicity_eq u
        (rootMultiplicity_eq_of_residue_zero u hu (fun α => ?_))
      rw [← hG]; exact residueAt_derivative_eq_zero G α
  · intro h0
    exact ⟨0, by rw [h0, map_zero]⟩

/-- `NondegenerateLog u ↔ logDeriv u ≠ 0` at the rational base. -/
theorem nondegenerateLog_ratFunc_iff_logDeriv_ne_zero [CharZero K] [IsAlgClosed K]
    (u : RatFunc K) :
    NondegenerateLog u ↔ Differential.logDeriv u ≠ 0 := by
  rw [nondegenerateLog_iff_no_antideriv u, ne_eq,
    ← logDeriv_hasAntideriv_iff_eq_zero u]

/-- `NondegenerateLog u` is decidable from a `Decidable (logDeriv u = 0)` instance. -/
instance instDecidableNondegenerateLogRatFunc [CharZero K] [IsAlgClosed K]
    (u : RatFunc K) [Decidable (Differential.logDeriv u = 0)] : Decidable (NondegenerateLog u) :=
  decidable_of_iff _ (nondegenerateLog_ratFunc_iff_logDeriv_ne_zero u).symm

/-- If `logDeriv u ≠ 0` then `K(x)(log u) = RatFunc (K(x))` is a Liouville extension of `K(x)`. -/
theorem isLiouville_of_logDeriv_ne_zero [CharZero K] [IsAlgClosed K] (u : RatFunc K)
    (hne : Differential.logDeriv u ≠ 0) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville (RatFunc K) (RatFunc (RatFunc K)) :=
  isLiouville_of_no_antideriv u
    (fun h => hne ((logDeriv_hasAntideriv_iff_eq_zero u).mp h))

end RationalBase

/-! ## The empty-base semantics of `cLogIsNewMonomial`

With `logDerivs = []`, `cLogIsNewMonomial` decides only `w ≠ 0` — necessary but not sufficient for
`NondegenerateLog`. -/

section ComputableEmptyBase

open DensePoly

/-- `crref.go` halts once the working column reaches `ncols = 1`, returning the accumulated pivot
rows/columns reversed. -/
private lemma crref_go_stop (f : ℕ) (rows pr : List (List ℚ)) (pc : List ℕ) :
    crref.go 1 f 1 rows pr pc = (pr.reverse, pc.reverse) := by
  cases f with
  | zero => cases rows <;> rfl
  | succ g => cases rows with
    | nil => rfl
    | cons hd tl => rw [crref.go] <;> simp

/-- `crref.go` at the first column (`ncols = 1`): pivot columns `[0]` if some row has a nonzero
entry in column `0`, else `[]`. -/
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

/-- Pivot columns of a single-column RREF: `[0]` iff some row has a nonzero entry in column `0`,
else `[]`. -/
private lemma crref_single_col_pivots (M : List (List ℚ)) :
    (crref M 1).2 = (if (M.find? (fun r => (r.getD 0 0) ≠ 0)).isSome then [0] else []) :=
  crref_go_col0 (1 + M.length) M

/-- Nullspace basis of a single-column matrix: empty if column `0` is a pivot, else `[[1]]`. -/
private lemma nullspace_single_col (M : List (List ℚ)) :
    cNullspaceBasisQ M 1 = (if (crref M 1).2.contains 0 then [] else [[1]]) := by
  unfold cNullspaceBasisQ
  obtain ⟨R, pivCols⟩ := crref M 1
  show List.map _ ((List.range 1).filter (fun j => !pivCols.contains j)) = _
  rw [show List.range 1 = [0] from rfl, List.filter_cons, List.filter_nil]
  by_cases h0 : pivCols.contains 0 = true
  · rw [h0]; simp
  · simp only [Bool.not_eq_true] at h0; rw [h0]; simp

/-- `cLogIsNewMonomial [] w = true` iff the cleared coefficient column `(cLinearDepData [] w).1`
has a nonzero entry — the empty-base test decides `w ≠ 0`. -/
theorem cLogIsNewMonomial_nil_eq_col_nonzero (w : DenseFrac ℚ) :
    DensePoly.cLogIsNewMonomial [] w =
      ((DensePoly.cLinearDepData [] w).1.find? (fun r => (r.getD 0 0) ≠ 0)).isSome := by
  have hbridge : DensePoly.cLogIsNewMonomial [] w =
      !((cNullspaceBasisQ (DensePoly.cLinearDepData [] w).1
          ((DensePoly.cLinearDepData [] w).2 + 1)).any
        (fun rel => rel.getD (DensePoly.cLinearDepData [] w).2 0 ≠ 0)) := rfl
  have h2 : (DensePoly.cLinearDepData [] w).2 = 0 := rfl
  rw [hbridge, h2, show (0 : ℕ) + 1 = 1 from rfl]
  set M := (DensePoly.cLinearDepData [] w).1 with hM
  rw [nullspace_single_col M, crref_single_col_pivots M]
  cases hfind : M.find? (fun r => (r.getD 0 0) ≠ 0) with
  | none => simp
  | some pr => simp

end ComputableEmptyBase

/-! ### Restatements -/

section Restatements

variable {F : Type*} [Field F] [Differential F] [CharZero F]

-- The abstract characterization: `NondegenerateLog u ↔ no `F`-antiderivative of `u'/u`.
example (u : F) : NondegenerateLog u ↔ ¬ ∃ s : F, s′ = logDeriv u :=
  nondegenerateLog_iff_no_antideriv u

-- The keystone composes from "no antiderivative".
example (u : F) (hno : ¬ ∃ s : F, s′ = logDeriv u) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville F (RatFunc F) :=
  isLiouville_of_no_antideriv u hno

-- The empty-base computable test decides only "cleared column nonzero" (≈ `w ≠ 0`).
example (w : DenseFrac ℚ) :
    DensePoly.cLogIsNewMonomial [] w =
      ((DensePoly.cLinearDepData [] w).1.find? (fun r => (r.getD 0 0) ≠ 0)).isSome :=
  cLogIsNewMonomial_nil_eq_col_nonzero w

end Restatements

section RationalBaseRestatements

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

-- `logDeriv u` has a rational antiderivative ⟺ `logDeriv u = 0` (rational base).
example (u : RatFunc K) :
    (∃ s : RatFunc K, s′ = Differential.logDeriv u) ↔ Differential.logDeriv u = 0 :=
  logDeriv_hasAntideriv_iff_eq_zero u

-- `NondegenerateLog` is decidable at the rational base: ⟺ `logDeriv u ≠ 0`.
example (u : RatFunc K) : NondegenerateLog u ↔ Differential.logDeriv u ≠ 0 :=
  nondegenerateLog_ratFunc_iff_logDeriv_ne_zero u

-- The decidable `logDeriv u ≠ 0` discharges the Liouville keystone at the rational base.
example (u : RatFunc K) (hne : Differential.logDeriv u ≠ 0) :
    letI := logDifferential u
    letI := logDifferentialAlgebra u
    IsLiouville (RatFunc K) (RatFunc (RatFunc K)) :=
  isLiouville_of_logDeriv_ne_zero u hne

end RationalBaseRestatements

end DeepWiki.SymbolicIntegration
