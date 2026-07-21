import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.RtResultantCorrectness
import DeepWiki.SymbolicIntegration.SubresultantCorrectness
import DeepWiki.ComputableAlgebra.PolyReprDivisionDegree
import DeepWiki.CAlgebra.Integrate.LogPart

/-! # Example 2.4.1 worked example (Bronstein §2.4, p.48): the honest ℚ[t] LRT closure

The native_decide-validated concrete run of the Rothstein–Trager / LRT subresultant machinery
on Example 2.4.1 — the honest resultant 45796·(4t²+1)³, the multiplicity-3 residue regularity,
and the hypothesis-free IsSimilar closure over ℚ[t]/(4t²+1). The general theory and its abstract
correctness live in DeepWiki/SymbolicIntegration/{RtResultantCorrectness,SubresultantCorrectness}. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### Example 2.4.1 concrete data and native_decide validations -/

/-! ### Example 2.4.1 (§2.4, p.48): `A = x⁴−3x²+6`, `D = x⁶−5x⁴+5x²+4`,
`res_x(D, A−t·D') = 45796·(4t²+1)³`, primitive part `R = 4t²+1` -/

/-- **`x⁴ − 3x² + 6`** as a `DensePoly ℚ` (Example 2.4.1's `A`): coefficients `[6, 0, −3, 0, 1]`. -/
def cA241 : DensePoly ℚ := [6, 0, -3, 0, 1]

/-- **`x⁶ − 5x⁴ + 5x² + 4`** as a `DensePoly ℚ` (Example 2.4.1's `D`): coefficients `[4, 0, 5, 0, −5, 0, 1]`. -/
def cD241 : DensePoly ℚ := [4, 0, 5, 0, -5, 0, 1]

-- **Example 2.4.1, `D' = cderiv D`** should be `6x⁵ − 20x³ + 10x` = `[0, 10, 0, −20, 0, 6]`.
#eval cderiv cD241

-- **Example 2.4.1, the computed RT resultant** `R(t) = res_x(D, A − t·D')`. The book (p.48) states
-- this is exactly `45796·(4t²+1)³ = [45796, 0, 549552, 0, 2198208, 0, 2930944]`; its primitive
-- squarefree part is the book's `R = 4t²+1`.
#eval DensePoly.cResidueResultantTower ([1] : DensePoly ℚ) cA241 cD241

-- **Example 2.4.1, the squarefree part** `R / gcd(R, R')`, normalized: the book's `4t²+1` (up to scalar).
#eval cmonic (CPoly.csquarefreePart
  (DensePoly.cResidueResultantTower ([1] : DensePoly ℚ) cA241 cD241))

/-- **Example 2.4.1, the proved RT-resultant computation** (§2.4, p.48): `cResidueResultantTower [1]` on
`A = x⁴−3x²+6`, `D = x⁶−5x⁴+5x²+4` evaluates (by `native_decide`; kernel `decide` stalls on the
GMP-backed `ℚ` arithmetic) to `[45796, 0, 549552, 0, 2198208, 0, 2930944]`, which is **exactly the
book's** `res_x(D, A−t·D') = 45796·(4t²+1)³` (eq 2.7, p.48): `(4t²+1)³ = 64t⁶+48t⁴+12t²+1`, and
`45796·[1,12,48,64] = [45796, 549552, 2198208, 2930944]` in the even-degree slots. This demonstrates
the computable Rothstein–Trager resultant engine actually runs and returns the book's resultant. -/
theorem rtResultant_ex241 :
    DensePoly.cResidueResultantTower ([1] : DensePoly ℚ) cA241 cD241 =
      [45796, 0, 549552, 0, 2198208, 0, 2930944] := by
  native_decide

/-- **Example 2.4.1, the primitive part is the book's `R = 4t²+1`** (§2.4, p.48): the squarefree
(monic radical) part of the resultant `45796·(4t²+1)³` is `t² + 1/4` = `[1/4, 0, 1]` (monic `4t²+1`),
exactly the book's `R(t) = 4t²+1` up to the leading-coefficient scalar. Proved by `native_decide`. -/
theorem rtResultant_ex241_sqfree :
    cmonic (CPoly.csquarefreePart
      (DensePoly.cResidueResultantTower ([1] : DensePoly ℚ) cA241 cD241)) = [1/4, 0, 1] := by
  native_decide

/-! ### Example 2.4.1 (§2.4/§2.6, p.48/54): `A = x⁴−3x²+6`, `D = x⁶−5x⁴+5x²+4`,
LRT log argument `S(t,x) = x³ + 2t·x² − 3x − 4t` (Czichowski/Gröbner `B = {4t²+1, x³+2tx²−3x−4t}`). -/

/-- **The Rothstein–Trager resultant factor `R(t) = 4t²+1`** of Example 2.4.1 as a `DensePoly ℚ`
(`[1, 0, 4]` = `1 + 4t²`); the residues are its roots, and `ℚ[t]/(R)` is the residue ring the LRT log
argument is normalized over. Up to the leading scalar this is the normalized
`CPoly.csquarefreePart` of the full resultant `45796·(4t²+1)³`. -/
def cR241 : DensePoly ℚ := [1, 0, 4]

-- **Example 2.4.1, the lifted `A − t·D'`** (sanity print): `A − t·(6x⁵−20x³+10x)`.
#eval bArgAmtD' cA241 cD241

-- **Example 2.4.1, the subresultant PRS `x`-degrees** `[6,5,4,3,2,1,0]` (the degree-0 tail is the
-- resultant `45796·(4t²+1)³`, matching `rtResultant_ex241`).
#eval (subresPRS 30 (liftCtoBPoly cD241) (bArgAmtD' cA241 cD241)).map DensePoly.cdeg

-- **Example 2.4.1, the degree-3 subresultant** `S₃`, `ℚ[t]`-primitive in `x`: the LRT log argument up
-- to a `ℚ[t]` cofactor. Its raw (pre-primitive) form `[[-16,0,792],[0,32,0,-2440],[7,0,-400],
-- [0,-14,0,800]]` satisfies `S₃ ≡ −214t·(x³+2tx²−3x−4t) mod 4t²+1`; `GBPolyCore.gbprimitivePartCore CPolyGcd.compute` strips a constant.
#eval lrtSubresultantCompute 30 3 cA241 cD241

-- **Example 2.4.1, the normalized LRT log argument** `S(t,x)` = `S₃` mod `4t²+1`, monic in `x`:
-- the book's `x³ + 2t·x² − 3x − 4t = [[0,-4], [-3], [0,2], [1]]`.
#eval lrtGcdCompute 30 3 cR241 cA241 cD241

/-- **Example 2.4.1, the proved LRT log-argument computation** (§2.4/§2.6, p.48/54): the degree-3
bivariate subresultant `S₃(D, A − t·D')` of `D = x⁶−5x⁴+5x²+4` and `A − t·D'` (`A = x⁴−3x²+6`), reduced
modulo the resultant factor `R(t) = 4t²+1` and made monic in `x` over `ℚ[t]/(R)`, evaluates (by
`native_decide`) to `[[0, -4], [-3], [0, 2], [1]]` = `x³ + 2t·x² − 3x − 4t`. This is **exactly** the
book's LRT log argument — the Czichowski/Gröbner basis element `x³+2tx²−3x−4t` of Example 2.6.1
(`B = {4t²+1, x³+2tx²−3x−4t}`), with `4t²+1` the RT resultant `R(t)` of `rtResultant_ex241_sqfree`. The
raw subresultant `S₃` carries the `ℚ[t]` cofactor `−214t` (`S₃ ≡ −214t·(x³+2tx²−3x−4t) mod R`), stripped
by the Exercise 2.7 monic-in-`x` normalization (`bmonicXmodR`). This demonstrates the computable
bivariate LRT log-argument engine actually runs and returns the book's `S(t,x)`. -/
theorem lrtGcd_ex241 :
    lrtGcdCompute 30 3 cR241 cA241 cD241 = [[0, -4], [-3], [0, 2], [1]] := by
  native_decide

/-! ### Example 2.4.1: the honest `ℚ[t]` Rothstein–Trager resultant `= 45796·(4t²+1)³` -/

open Polynomial in
/-- **`toPoly cD241` is monic** (`D = x⁶−5x⁴+5x²+4` has leading coefficient 1). -/
theorem monic_toPoly_cD241 : (toPoly cD241 : ℚ[X]).Monic := by
  rw [Monic, ← DensePoly.toK_cleadG_eq_leadingCoeff]
  change clead cD241 = (1 : ℚ)
  native_decide

open Polynomial in
/-- **`deg A < deg D` for Example 2.4.1** (`deg A = 4 < 6 = deg D`). -/
theorem natDegree_cA241_lt_cD241 :
    (toPoly cA241 : ℚ[X]).natDegree < (toPoly cD241 : ℚ[X]).natDegree := by
  rw [← DensePoly.cdegG_eq_natDegree, ← DensePoly.cdegG_eq_natDegree]; decide

open Polynomial in
/-- **The dense `DensePoly ℚ` `[45796,0,549552,0,2198208,0,2930944]` reads as `45796·(4t²+1)³`** in `ℚ[t]`. -/
theorem toPoly_ex241_value :
    toPoly ([45796, 0, 549552, 0, 2198208, 0, 2930944] : DensePoly ℚ)
      = Polynomial.C 45796 * (Polynomial.C 4 * Polynomial.X ^ 2 + Polynomial.C 1) ^ 3 := by
  simp only [DensePoly.toPolyG_cons, DensePoly.toPolyG_nil,
    toR_eq_toK, CFieldSpec.toK_rat, map_ofNat, map_one, map_zero]
  ring

open Polynomial in
/-- **Example 2.4.1, the honest `ℚ[t]` Rothstein–Trager resultant** (§2.4, p.48, eq 2.7): the
*noncomputable* `rtResultant (toPoly cA241) (toPoly cD241)` equals `45796·(4t²+1)³` as an honest
polynomial in `ℚ[t]`. Routes the `native_decide`-validated computation (`rtResultant_ex241`) through the
proven agreement `toPolyG_cResidueResultantTower_one_eq_rtResultant` (monic `D`, `deg A < deg D`) and the
closed-form read `toPoly_ex241_value`. This is the honest equation behind the residue multiplicities. -/
theorem rtResultant_ex241_eq :
    rtResultant (toPoly cA241) (toPoly cD241)
      = Polynomial.C 45796 * (Polynomial.C 4 * Polynomial.X ^ 2 + Polynomial.C 1) ^ 3 := by
  have hresult := toPolyG_cResidueResultantTower_one_eq_rtResultant cA241 cD241
    (by exact monic_toPoly_cD241)
    (by exact natDegree_cA241_lt_cD241)
  rw [← show toPoly (DensePoly.cResidueResultantTower ([1] : DensePoly ℚ) cA241 cD241)
      = rtResultant (toPoly cA241) (toPoly cD241) from by
        exact hresult,
    rtResultant_ex241, toPoly_ex241_value]

/-! ### Closing Example 2.4.1: the residue ring `ℚ[t]/(4t²+1)` and `IsDomain`
The concrete agreement `lrtGcdCompute_isSimilar_lrtSubresultant_concrete` needs a residue map
`φ : ℚ[X] →+* S` killing `toPoly R` with `S` a domain. For Example 2.4.1 the modulus is `R = 4t²+1`
(`cR241`); since `4X²+1` is **irreducible over ℚ** (degree 2, no rational root: `4x²+1 ≥ 1 > 0`),
`S = AdjoinRoot (toPoly cR241) ≅ ℚ(i/2)` is a **field**, hence a domain. The quotient map
`φ = AdjoinRoot.mk (toPoly cR241)` kills `toPoly cR241` by `AdjoinRoot.mk_self`. -/

/-- **`toPoly cR241 = 1 + 4·X²`**: the Rothstein–Trager modulus `R = 4t²+1` read into `ℚ[X]`
(here `X` is the `t`-indeterminate). -/
theorem toPoly_cR241 : (toPoly cR241 : ℚ[X]) = 1 + 4 * X ^ 2 := by
  show toPoly [(1 : ℚ), 0, 4] = _
  simp only [DensePoly.toPolyG_cons, DensePoly.toPolyG_nil,
    toR_eq_toK, CFieldSpec.toK_rat, map_zero, map_one, mul_zero, add_zero, map_ofNat]
  ring

/-- **`toPoly cR241` has degree 2**: `(toPoly cR241).natDegree = 2`. -/
theorem natDegree_toPoly_cR241 : (toPoly cR241 : ℚ[X]).natDegree = 2 := by
  rw [← DensePoly.cdegG_eq_natDegree]
  native_decide

/-- **`4X²+1` has no rational root**: `4x²+1 ≥ 1 > 0` for every `x : ℚ`, so it is never zero. -/
theorem toPoly_cR241_not_isRoot (x : ℚ) : ¬ (toPoly cR241 : ℚ[X]).IsRoot x := by
  rw [Polynomial.IsRoot.def, toPoly_cR241]
  simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_X]
  change ¬ (1 + 4 * x ^ 2 : ℚ) = 0
  nlinarith [sq_nonneg x]

/-- **`4X²+1` (i.e. `toPoly cR241`) is irreducible over `ℚ`**: degree 2 with no rational root
(`irreducible_of_degree_le_three_of_not_isRoot`). -/
theorem irreducible_toPoly_cR241 : Irreducible (toPoly cR241 : ℚ[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_toPoly_cR241]; decide
  · exact toPoly_cR241_not_isRoot

/-- **`ℚ[t]/(4t²+1)` is a field** (`Fact (Irreducible (toPoly cR241))` ⟹ `AdjoinRoot.instField`). -/
noncomputable instance : Fact (Irreducible (toPoly cR241)) := ⟨irreducible_toPoly_cR241⟩

/-- **The residue ring** `R241 := AdjoinRoot (toPoly cR241) = ℚ[t]/(4t²+1)` of Example 2.4.1 — a field
(hence a domain), over which the LRT log argument is normalized. -/
noncomputable abbrev R241 : Type := AdjoinRoot (toPoly cR241)

/-- **The residue map** `φ241 := AdjoinRoot.mk (toPoly cR241) : ℚ[X] →+* R241` (the quotient map). -/
noncomputable abbrev φ241 : ℚ[X] →+* R241 := AdjoinRoot.mk (toPoly cR241)

/-- **`φ241` kills `toPoly cR241`**: `φ241 (toPoly cR241) = 0` (`AdjoinRoot.mk_self`). -/
theorem φ241_toPoly_cR241 : φ241 (toPoly cR241) = 0 := AdjoinRoot.mk_self

/-- **`φ241 x = 0 ↔ (4t²+1) ∣ x`**: the kernel of the quotient map `φ241 = AdjoinRoot.mk (toPoly cR241)`
is exactly the multiples of `toPoly cR241` (`AdjoinRoot.mk_eq_zero`). -/
theorem φ241_eq_zero_iff (x : ℚ[X]) : φ241 x = 0 ↔ toPoly cR241 ∣ x := AdjoinRoot.mk_eq_zero

/-! ### The decidable chain regularity for Example 2.4.1 (`native_decide`)
The concrete chain `subresPRS 30 (liftCtoBPoly cD241) (bArgAmtD' cA241 cD241)` has `x`-degrees
`[6,5,4,3,2,1,0]` (indices 0..6), then index 7 is zero. The book's LRT log argument is the **degree-3**
element `x³+2tx²−3x−4t` (index 3), so the regular index is `m + 2 = 3`, i.e. `m = 1`. We instantiate the
headline `lrtGcdCompute_isSimilar_lrtSubresultant` directly at this `m` (the `_concrete` wrapper's
`chain_hfilt` only extracts the *terminal* chain element, so it would force `j = 0`; instead we discharge
the singleton-filter `hfilt` at the degree-3 index by `native_decide`, since the `[6,5,4,3,2,1,0]` degrees
are all distinct ⟹ the degree-3 element is unique). Every `DensePoly.cdeg`/`DensePoly.cisZero`/`cnorm`/`cmod`/`cisZero` fact
on the chain is a decidable `ℚ`-fact, pinned by `native_decide` (the established `lrtGcd_ex241` pattern;
`decide` stalls on the GMP-backed `ℚ` arithmetic). `chain`/`chainBt` unfold to the computable
`goState`/`goBeta`. Throughout, `fuel = 30`, `P = liftCtoBPoly cD241`, `Q = bArgAmtD' cA241 cD241`. The two
facts mentioning the `Classical.choose` witnesses `chainC`/`chainS` (the content nonzero `hc0` and
quotient-degree bound `hQ`) are derived separately (below). -/

/-- The Example 2.4.1 chain abbreviation: `gP = liftCtoBPoly cD241`, `gQ = bArgAmtD' cA241 cD241`. -/
private abbrev gP : GBPolyCore ℚ := liftCtoBPoly cD241
private abbrev gQ : GBPolyCore ℚ := bArgAmtD' cA241 cD241

/-- **The degree-3 element's `x`-degree is 3**: `(DensePoly.toPoly (chain 30 gP gQ 3)).natDegree = 3` (the regular
LRT index `j = m+2 = 3`). Via `DensePoly.cdegG_eq_natDegree` and `native_decide` on `DensePoly.cdeg (chain … 3)`. -/
theorem natDegree_toBPoly_chainG3_ex241 :
    (DensePoly.toPoly (chain 30 gP gQ 3)).natDegree = 3 := by
  rw [← DensePoly.cdegG_eq_natDegree]
  show DensePoly.cdeg (goState 30 (gP, gQ, [-1], 1) 3).1 = 3
  native_decide

/-- `(toPoly cD241).natDegree = 6`: `D = x⁶−5x⁴+5x²+4` has degree 6 (via `DensePoly.cdegG_eq_natDegree`). -/
theorem natDegree_toPoly_cD241 : (toPoly cD241).natDegree = 6 := by
  rw [← DensePoly.cdegG_eq_natDegree]; native_decide

/-- **`hd0` for Ex 2.4.1**: `(DensePoly.toPoly (chain 30 gP gQ 0)).natDegree = (toPoly cD241).natDegree` (both 6). -/
theorem hd0_ex241 :
    (DensePoly.toPoly (chain 30 gP gQ 0)).natDegree = (toPoly cD241).natDegree := by
  rw [← DensePoly.cdegG_eq_natDegree, natDegree_toPoly_cD241]
  show DensePoly.cdeg (goState 30 (gP, gQ, [-1], 1) 0).1 = 6
  native_decide

/-- **`hd1` for Ex 2.4.1**: `(DensePoly.toPoly (chain 30 gP gQ 1)).natDegree = (toPoly cD241).natDegree − 1`
(5 = 6−1). -/
theorem hd1_ex241 :
    (DensePoly.toPoly (chain 30 gP gQ 1)).natDegree = (toPoly cD241).natDegree - 1 := by
  rw [← DensePoly.cdegG_eq_natDegree, natDegree_toPoly_cD241]
  show DensePoly.cdeg (goState 30 (gP, gQ, [-1], 1) 1).1 = 6 - 1
  native_decide

/-- **Chain nonzero through index 3**: `chain 0 … chain 3` are all nonzero (degrees `6,5,4,3`). -/
theorem chainG_ne_zero_ex241 :
    ∀ i ≤ 3, ¬ DensePoly.cisZero (chain 30 gP gQ i) = true := by
  simp only [chain]; native_decide

/-- **`hβcn` for Ex 2.4.1**: the β-divisors `chainBt 0`, `chainBt 1` are nonzero `ℚ[t]` lists
(`[1]`, `[0,0,36]`). -/
theorem hβcn_ex241 :
    ∀ l ≤ 1, cnorm (chainBt 30 gP gQ l) ≠ [] := by
  intro l hl; interval_cases l <;>
    · simp only [chainBt]; native_decide

/-- **`hβ0` for Ex 2.4.1**: the β-divisors `chainBt 0`, `chainBt 1` read to nonzero `ℚ[t]` polynomials
(`toPoly ≠ 0`), via `DensePoly.cnormG_eq_nil_iff`. -/
theorem hβ0_ex241 :
    ∀ l ≤ 1, toPoly (chainBt 30 gP gQ l) ≠ 0 := by
  intro l hl h
  exact hβcn_ex241 l hl ((DensePoly.cnormG_eq_nil_iff _).mpr h)

/-- **`hdiv` for Ex 2.4.1** (Collins β-divisibility, concrete): `chainBt l` divides every `x`-coefficient
of the pseudo-remainder `prem (chain l) (chain (l+1))` exactly (`cmod` reads to 0), via
`DensePoly.cnormG_eq_nil_iff`. The decidable per-coefficient `cmod`-zero certificate, `native_decide`'d. -/
theorem hdiv_ex241 :
    ∀ l ≤ 1, ∀ a ∈ GBPolyCore.gbpsremainderCore 30 (chain 30 gP gQ l) (chain 30 gP gQ (l + 1)),
      toPoly (CPolyEuclidean.mod a (chainBt 30 gP gQ l)) = 0 := by
  intro l hl a ha
  rw [← DensePoly.cnormG_eq_nil_iff]
  revert a ha
  interval_cases l <;>
    · simp only [chainBt, chain]; native_decide

/-- **`hlc` for Ex 2.4.1**: the leading `x`-coefficient of `chain (l+1)` (`l ≤ 1`) is nonzero. -/
theorem hlc_ex241 :
    ∀ l ≤ 1, (DensePoly.toPoly (chain 30 gP gQ (l + 1))).coeff
      (DensePoly.toPoly (chain 30 gP gQ (l + 1))).natDegree ≠ 0 := by
  intro l hl
  rw [← DensePoly.cdegG_eq_natDegree, ← GBPolyCore.toPolyG_gblcCore_eq_coeff]
  exact toPolyG_gblcCore_ne_zero
    (Bool.eq_false_iff.mpr (chainG_ne_zero_ex241 (l + 1) (by omega)))

/-- **`hcb` for Ex 2.4.1**: the `x`-degrees strictly decrease (`chain (l+2)` below `chain (l+1)`,
`l ≤ 1`: `4<5`, `3<4`), via `DensePoly.cdegG_eq_natDegree`. -/
theorem hcb_ex241 :
    ∀ l ≤ 1, (DensePoly.toPoly (chain 30 gP gQ (l + 2))).natDegree
      < (DensePoly.toPoly (chain 30 gP gQ (l + 1))).natDegree := by
  intro l hl
  rw [← DensePoly.cdegG_eq_natDegree, ← DensePoly.cdegG_eq_natDegree]
  interval_cases l <;>
    · simp only [chain]; native_decide

/-- **`hjlt` for Ex 2.4.1**: the degree-3 element `chain 3` is strictly below `chain (l+2)` for `l<1`
(only `l=0`: `3<4`), via `DensePoly.cdegG_eq_natDegree`. -/
theorem hjlt_ex241 :
    ∀ l < 1, (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree
      < (DensePoly.toPoly (chain 30 gP gQ (l + 2))).natDegree := by
  intro l hl
  rw [← DensePoly.cdegG_eq_natDegree, ← DensePoly.cdegG_eq_natDegree]
  interval_cases l
  simp only [chain]; native_decide

/-- **`hCne` for Ex 2.4.1**: the degree-3 chain element `chain 3` is nonzero (`DensePoly.toPoly ≠ 0`), via
`DensePoly.cisZeroG_iff`. -/
theorem hCne_ex241 : DensePoly.toPoly (chain 30 gP gQ (1 + 2)) ≠ 0 := by
  rw [Ne, ← DensePoly.cisZeroG_iff]
  exact chainG_ne_zero_ex241 3 (by omega)

/-- **The degree-3 filter of `subresPRS` is `[chain 3]`** (the singleton-filter `hfil`, by
`native_decide`): the `[6,5,4,3,2,1,0]` chain degrees are all distinct, so the degree-3 nonzero filter of
`subresPRS 30 gP gQ` is exactly the single element `chain 3`. Direct `native_decide` (no abstract
`unique_of_strictAnti` argument needed — both sides are computable). -/
theorem subresPRS_filter_singleton_ex241 :
    (subresPRS 30 gP gQ).filter
        (fun R => decide (DensePoly.cdeg R = (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree ∧ ¬ DensePoly.cisZero R))
      = [chain 30 gP gQ (1 + 2)] := by
  rw [natDegree_toBPoly_chainG3_ex241]
  show (subresPRS 30 gP gQ).filter (fun R => decide (DensePoly.cdeg R = 3 ∧ ¬ DensePoly.cisZero R))
      = [(goState 30 (gP, gQ, [-1], 1) (1 + 2)).1]
  native_decide

/-- **`hfilt` for Ex 2.4.1**: the degree-3 filter of `bsubresultantGcd 30 3 gP gQ` returns `chain 3`
(under `DensePoly.toPoly`). From the singleton filter `subresPRS_filter_singleton_ex241` via
`toBPoly_bsubresultantGcd_eq_of_filter_singleton`. -/
theorem hfilt_ex241 :
    DensePoly.toPoly (bsubresultantGcd 30 (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree gP gQ)
      = DensePoly.toPoly (chain 30 gP gQ (1 + 2)) :=
  toBPoly_bsubresultantGcd_eq_of_filter_singleton 30 gP gQ (chain 30 gP gQ) 1
    subresPRS_filter_singleton_ex241

/-! ### `GBPolyCore.gbprimitivePartCore CPolyGcd.compute` content-exactness on the degree-3 element (Ex 2.4.1, `native_decide`)
The raw degree-3 subresultant `bsubresultantGcd 30 3 gP gQ = S₃ = [[-16,0,792],[0,32,0,-2440],[7,0,-400],
[0,-14,0,800]]` carries a `ℚ[t]`-content; `GBPolyCore.gbprimitivePartCore CPolyGcd.compute` strips it. The content `GBPolyCore.gbcontentCore CPolyGcd.compute` is a
nonzero `ℚ[t]` polynomial dividing every `x`-coefficient exactly — all decidable `cisZero`/`cmod`-zero
facts, `native_decide`'d. -/

/-- **`hg` for Ex 2.4.1**: the `ℚ[t]`-content of the degree-3 raw subresultant is nonzero
(`¬ cisZero (GBPolyCore.gbcontentCore CPolyGcd.compute (bsubresultantGcd 30 3 gP gQ))`). -/
theorem hg_ex241 :
    ¬ cisZero (GBPolyCore.gbcontentCore CPolyGcd.compute (bsubresultantGcd 30
      (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree gP gQ)) = true := by
  rw [natDegree_toBPoly_chainG3_ex241]; native_decide

/-- **`hgcn` for Ex 2.4.1**: the `ℚ[t]`-content of the degree-3 raw subresultant has nonempty `cnorm`. -/
theorem hgcn_ex241 :
    cnorm (GBPolyCore.gbcontentCore CPolyGcd.compute (bsubresultantGcd 30
      (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree gP gQ)) ≠ [] := by
  rw [natDegree_toBPoly_chainG3_ex241]; native_decide

/-- **`hg0` for Ex 2.4.1**: the `ℚ[t]`-content reads to a nonzero `ℚ[t]` polynomial (`toPoly ≠ 0`), via
`DensePoly.cnormG_eq_nil_iff`. -/
theorem hg0_ex241 :
    toPoly (GBPolyCore.gbcontentCore CPolyGcd.compute (bsubresultantGcd 30
      (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree gP gQ)) ≠ 0 := by
  intro h; exact hgcn_ex241 ((DensePoly.cnormG_eq_nil_iff _).mpr h)

/-- **`hrem` for Ex 2.4.1**: the `ℚ[t]`-content divides every `x`-coefficient of the degree-3 raw
subresultant exactly (`cmod` reads to 0), via `DensePoly.cnormG_eq_nil_iff`. -/
theorem hrem_ex241 :
    ∀ a ∈ GBPolyCore.gbnormCore (bsubresultantGcd 30
        (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree gP gQ),
      toPoly (CPolyEuclidean.mod a (GBPolyCore.gbcontentCore CPolyGcd.compute (bsubresultantGcd 30
        (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree gP gQ))) = 0 := by
  intro a ha
  rw [← DensePoly.cnormG_eq_nil_iff]
  revert a ha
  rw [natDegree_toBPoly_chainG3_ex241]
  native_decide

/-- **`hpz` for Ex 2.4.1**: the mod-`R` reduction of the primitive degree-3 subresultant is nonzero
(`¬ DensePoly.cisZero (bredR cR241 (lrtSubresultantCompute 30 3 cA241 cD241))`). -/
theorem hpz_ex241 :
    ¬ DensePoly.cisZero (bredR cR241 (lrtSubresultantCompute 30
      (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree cA241 cD241)) = true := by
  rw [natDegree_toBPoly_chainG3_ex241]; native_decide

/-! ### The Exercise 2.7 residue-ring unit regularity (Ex 2.4.1, `native_decide`)
The `bmonicXmodR` monic-in-`x` normalization needs the leading `x`-coefficient of the mod-`R`-reduced
primitive subresultant to be a **unit mod `R = 4t²+1`**. Concretely its leading coefficient is `(107/8)·t`,
whose extended-Euclidean gcd with `4t²+1` reduces to the constant `1` — so it is a unit, with `u = 1`. The
gcd `.1` literally evaluates to `[1]` (`native_decide`), and `toPoly [1] = C 1`. -/

/-- **The leading-`x`-coefficient mod-`R` gcd is `[1]`** (Ex 2.4.1): the extended-Euclidean gcd of the
reduced primitive subresultant's leading `x`-coefficient (`(107/8)·t`) with `R = 4t²+1` is the constant
`1` (the leading coefficient is a unit mod `R`). `native_decide`. -/
theorem cgcdWf_blc_bredR_ex241 :
    (CPolyEuclidean.gcdExt (GBPolyCore.gblcCore (bredR cR241 (lrtSubresultantCompute 30
      (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree cA241 cD241))) cR241).1 = [1] := by
  rw [natDegree_toBPoly_chainG3_ex241]; native_decide

/-- **`hgu` for Ex 2.4.1** (Exercise 2.7 regularity, `u = 1`): the leading-`x`-coefficient mod-`R` gcd
reduces to the nonzero constant `C 1` — so the leading coefficient is a unit mod `R = 4t²+1`. From
`cgcdWf_blc_bredR_ex241` (`gcd = [1]`) and `toPoly [1] = C 1`. -/
theorem hgu_ex241 :
    toPoly (CPolyEuclidean.gcdExt (GBPolyCore.gblcCore (bredR cR241 (lrtSubresultantCompute 30
      (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree cA241 cD241))) cR241).1
      = Polynomial.C (1 : ℚ) := by
  rw [cgcdWf_blc_bredR_ex241]
  show toPoly [(1 : ℚ)] = _
  simp [DensePoly.toPolyG_cons, DensePoly.toPolyG_nil]

/-! ### The content nonzero `hc0` and quotient-degree bound `hQ`, derived from `chain_hsc`
The two hypotheses of `_concrete` mentioning the `Classical.choose` witnesses `chainC`/`chainS` are *not*
directly `native_decide`'able (the choose is noncomputable). But they follow from the pseudo-division
identity `chain_hsc` by a **degree argument** over the domain `(ℚ[X])[X]`, using only computable chain
facts: the chain elements `chain (l+1)`, `chain (l+2)` are nonzero with known `x`-degrees, and the
β-divisor exactly divides the pseudo-remainder (`hdiv_ex241`), so the pseudo-remainder has `x`-degree
`deg (chain (l+2)) < deg (chain (l+1))`. -/

/-- The chain elements `chain 1 … chain 3` are nonzero under `DensePoly.toPoly` (`l ≤ 1` ⟹ `l+1, l+2 ∈ {1,2,3}`),
via `DensePoly.cisZeroG_iff` and `chainG_ne_zero_ex241`. -/
theorem toBPoly_chainG_ne_zero_ex241 (i : ℕ) (hi : i ≤ 3) : DensePoly.toPoly (chain 30 gP gQ i) ≠ 0 := by
  rw [Ne, ← DensePoly.cisZeroG_iff]
  exact chainG_ne_zero_ex241 i hi

/-- **The pseudo-remainder is `C(toPoly βₗ)` times the next chain element** (Ex 2.4.1, `l ≤ 1`):
`DensePoly.toPoly (prem (chain l) (chain (l+1))) = C(toPoly (chainBt l)) · DensePoly.toPoly (chain (l+2))`. From
`chain_hG2` (the divided-step recurrence) and the β-divisor exact division `toBPoly_bdivC_exact`
(`hdiv_ex241`). -/
theorem toBPoly_prem_ex241 (l : ℕ) (hl : l ≤ 1) :
    DensePoly.toPoly (GBPolyCore.gbpsremainderCore 30 (chain 30 gP gQ l) (chain 30 gP gQ (l + 1)))
      = Polynomial.C (toPoly (chainBt 30 gP gQ l)) * DensePoly.toPoly (chain 30 gP gQ (l + 2)) := by
  have hexact := toBPoly_bdivC_exact
    (GBPolyCore.gbpsremainderCore 30 (chain 30 gP gQ l) (chain 30 gP gQ (l + 1))) (chainBt 30 gP gQ l)
    (hβcn_ex241 l hl) (fun a ha => hdiv_ex241 l hl a ha)
  rw [chain_hG2]
  exact hexact.symm

/-- The `x`-degree of the pseudo-remainder `prem (chain l) (chain (l+1))` equals
`deg (chain (l+2))` (`l ≤ 1`): the `C(toPoly βₗ)` constant factor does not change the `x`-degree
(`toPoly βₗ ≠ 0`), via `toBPoly_prem_ex241` and `natDegree_C_mul`. -/
theorem natDegree_toBPoly_prem_ex241 (l : ℕ) (hl : l ≤ 1) :
    (DensePoly.toPoly (GBPolyCore.gbpsremainderCore 30 (chain 30 gP gQ l) (chain 30 gP gQ (l + 1)))).natDegree
      = (DensePoly.toPoly (chain 30 gP gQ (l + 2))).natDegree := by
  rw [toBPoly_prem_ex241 l hl, Polynomial.natDegree_C_mul (hβ0_ex241 l hl)]

/-- **`hc0` for Ex 2.4.1**: the pseudo-division content `chainC l` (`l ≤ 1`) reads to a nonzero `ℚ[t]`
polynomial (`toPoly (chainC l) ≠ 0`). Degree argument over the domain `(ℚ[X])[X]`: if `toPoly (chainC l) =
0`, then `chain_hsc` gives `DensePoly.toPoly (chainS l) · DensePoly.toPoly (chain (l+1)) = − DensePoly.toPoly (prem)`; the RHS has
`x`-degree `deg (chain (l+2)) < deg (chain (l+1))` (`natDegree_toBPoly_prem_ex241` + `hcb_ex241`), while
the LHS has `x`-degree `≥ deg (chain (l+1))` (if `chainS l ≠ 0`) or is `0` forcing `chain (l+2) = 0`
(if `chainS l = 0`) — both contradictions. -/
theorem hc0_ex241 : ∀ l ≤ 1, toPoly (chainC 30 gP gQ l) ≠ 0 := by
  intro l hl hc0
  have hsc := chain_hsc 30 gP gQ l
  rw [hc0, map_zero, zero_mul] at hsc
  -- 0 = DensePoly.toPoly(chainS l) · DensePoly.toPoly(G(l+1)) + DensePoly.toPoly(prem)
  have hprem := toBPoly_prem_ex241 l hl
  have hG1ne := toBPoly_chainG_ne_zero_ex241 (l + 1) (by omega)
  have hG2ne := toBPoly_chainG_ne_zero_ex241 (l + 2) (by omega)
  have hβne := hβ0_ex241 l hl
  -- rearrange: DensePoly.toPoly(chainS l)·DensePoly.toPoly(G(l+1)) = - DensePoly.toPoly(prem)
  have heq : DensePoly.toPoly (chainS 30 gP gQ l) * DensePoly.toPoly (chain 30 gP gQ (l + 1))
      = - DensePoly.toPoly (GBPolyCore.gbpsremainderCore 30 (chain 30 gP gQ l) (chain 30 gP gQ (l + 1))) := by
    linear_combination -hsc
  -- degree of the RHS
  have hpremne : DensePoly.toPoly (GBPolyCore.gbpsremainderCore 30 (chain 30 gP gQ l) (chain 30 gP gQ (l + 1))) ≠ 0 := by
    rw [hprem]
    have hβdense : DensePoly.toPoly (chainBt 30 gP gQ l) ≠ 0 := by
      exact hβne
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hβdense) hG2ne
  by_cases hSne : DensePoly.toPoly (chainS 30 gP gQ l) = 0
  · rw [hSne, zero_mul, eq_comm, neg_eq_zero] at heq
    exact hpremne heq
  · -- both sides nonzero; compare degrees
    have hdRHS : (- DensePoly.toPoly (GBPolyCore.gbpsremainderCore 30 (chain 30 gP gQ l) (chain 30 gP gQ (l + 1)))).natDegree
        = (DensePoly.toPoly (chain 30 gP gQ (l + 2))).natDegree := by
      rw [Polynomial.natDegree_neg, natDegree_toBPoly_prem_ex241 l hl]
    have hdLHS : (DensePoly.toPoly (chainS 30 gP gQ l) * DensePoly.toPoly (chain 30 gP gQ (l + 1))).natDegree
        = (DensePoly.toPoly (chainS 30 gP gQ l)).natDegree + (DensePoly.toPoly (chain 30 gP gQ (l + 1))).natDegree :=
      Polynomial.natDegree_mul hSne hG1ne
    have hdeg := congrArg Polynomial.natDegree heq
    rw [hdLHS, hdRHS] at hdeg
    have hcb := hcb_ex241 l hl
    omega

/-- **The `x`-degree of `chain (l+1)` is strictly below that of `chain l`** (Ex 2.4.1, `l ≤ 1`):
`deg (chain (l+1)) < deg (chain l)` (`5<6`, `4<5`), via `DensePoly.cdegG_eq_natDegree`. -/
theorem natDegree_toBPoly_chainG_strictAnti_ex241 (l : ℕ) (hl : l ≤ 1) :
    (DensePoly.toPoly (chain 30 gP gQ (l + 1))).natDegree < (DensePoly.toPoly (chain 30 gP gQ l)).natDegree := by
  rw [← DensePoly.cdegG_eq_natDegree, ← DensePoly.cdegG_eq_natDegree]
  interval_cases l <;>
    · simp only [chain]; native_decide

/-- **`hQ` for Ex 2.4.1**: the pseudo-division quotient degree bound
`deg (chainS l) + deg (chain (l+1)) ≤ deg (chain l)` (`l ≤ 1`). Degree argument over `(ℚ[X])[X]` on
`chain_hsc` (now with `hc0_ex241` giving the content nonzero): `C(toPoly cl)·DensePoly.toPoly(Gl)` has `x`-degree
`deg (Gl)`; the RHS `DensePoly.toPoly(sl)·DensePoly.toPoly(G(l+1)) + DensePoly.toPoly(prem)` has `x`-degree `deg(sl)+deg(G(l+1))` when
`sl ≠ 0` (the `prem` term has the strictly-smaller degree `deg (G(l+2))`,
`natDegree_add_eq_left_of_natDegree_lt`), so `deg(sl)+deg(G(l+1)) = deg(Gl)`; when `sl = 0` it is
`deg(G(l+1)) < deg(Gl)` (`natDegree_toBPoly_chainG_strictAnti_ex241`). -/
theorem hQ_ex241 : ∀ l ≤ 1,
    (DensePoly.toPoly (chainS 30 gP gQ l)).natDegree + (DensePoly.toPoly (chain 30 gP gQ (l + 1))).natDegree
      ≤ (DensePoly.toPoly (chain 30 gP gQ l)).natDegree := by
  intro l hl
  have hsc := chain_hsc 30 gP gQ l
  have hGlne := toBPoly_chainG_ne_zero_ex241 l (by omega)
  have hG1ne := toBPoly_chainG_ne_zero_ex241 (l + 1) (by omega)
  have hcl := hc0_ex241 l hl
  have hpremdeg := natDegree_toBPoly_prem_ex241 l hl
  have hcb := hcb_ex241 l hl
  have hstrict := natDegree_toBPoly_chainG_strictAnti_ex241 l hl
  -- LHS degree = deg(Gl)
  have hdLHS : (Polynomial.C (toPoly (chainC 30 gP gQ l)) * DensePoly.toPoly (chain 30 gP gQ l)).natDegree
      = (DensePoly.toPoly (chain 30 gP gQ l)).natDegree :=
    Polynomial.natDegree_C_mul hcl
  by_cases hSne : DensePoly.toPoly (chainS 30 gP gQ l) = 0
  · -- chainS l = 0: bound is deg(G(l+1)) < deg(Gl)
    rw [hSne, Polynomial.natDegree_zero]
    omega
  · -- chainS l ≠ 0: RHS top term is sl·G(l+1), degree deg(sl)+deg(G(l+1)) = deg(Gl)
    have hmuldeg : (DensePoly.toPoly (chainS 30 gP gQ l) * DensePoly.toPoly (chain 30 gP gQ (l + 1))).natDegree
        = (DensePoly.toPoly (chainS 30 gP gQ l)).natDegree + (DensePoly.toPoly (chain 30 gP gQ (l + 1))).natDegree :=
      Polynomial.natDegree_mul hSne hG1ne
    have hpremlt : (DensePoly.toPoly (GBPolyCore.gbpsremainderCore 30 (chain 30 gP gQ l) (chain 30 gP gQ (l + 1)))).natDegree
        < (DensePoly.toPoly (chainS 30 gP gQ l) * DensePoly.toPoly (chain 30 gP gQ (l + 1))).natDegree := by
      rw [hmuldeg, hpremdeg]; omega
    have hRHSdeg : (DensePoly.toPoly (chainS 30 gP gQ l) * DensePoly.toPoly (chain 30 gP gQ (l + 1))
          + DensePoly.toPoly (GBPolyCore.gbpsremainderCore 30 (chain 30 gP gQ l) (chain 30 gP gQ (l + 1)))).natDegree
        = (DensePoly.toPoly (chainS 30 gP gQ l) * DensePoly.toPoly (chain 30 gP gQ (l + 1))).natDegree :=
      Polynomial.natDegree_add_eq_left_of_natDegree_lt hpremlt
    have hdeg := congrArg Polynomial.natDegree hsc
    rw [hdLHS, hRHSdeg, hmuldeg] at hdeg
    omega

/-! ### The nonzero `φ`-images `Φ M_gcd ≠ 0`, `Φ M ≠ 0` (Ex 2.4.1)
The correct bridge `isSimilar_mapRingHom_of_irreducible` needs the `φ`-images nonzero. The computable LRT
output `lrtGcdCompute 30 3 cR241 cA241 cD241 = [[0,-4],[-3],[0,2],[1]]` (`lrtGcd_ex241`) is monic in `x`
(leading coefficient `[1]`), so its `φ`-image's degree-3 `x`-coefficient is `φ 1 = 1 ≠ 0`. From the unit
relation `Φ M_gcd = C(unit)·Φ M` this also gives `Φ M ≠ 0`. -/

/-- **`Φ (DensePoly.toPoly (lrtGcdCompute …)) ≠ 0`** (Ex 2.4.1): the `φ`-image of the computable LRT log argument is
nonzero — its degree-3 `x`-coefficient is `φ241 (toPoly [1]) = φ241 1 = 1 ≠ 0` (using `lrtGcd_ex241`,
`[[0,-4],[-3],[0,2],[1]]`, leading coefficient `[1]`). -/
theorem mapRingHom_φ241_toBPoly_lrtGcdCompute_ne_zero :
    (Polynomial.mapRingHom φ241) (DensePoly.toPoly
      (lrtGcdCompute 30 (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree cR241 cA241 cD241)) ≠ 0 := by
  rw [natDegree_toBPoly_chainG3_ex241]
  intro h
  have hcoeff : ((Polynomial.mapRingHom φ241) (DensePoly.toPoly
      (lrtGcdCompute 30 3 cR241 cA241 cD241))).coeff 3 = 0 := by rw [h]; simp
  rw [Polynomial.coe_mapRingHom, Polynomial.coeff_map, lrtGcd_ex241, DensePoly.toPolyG_coeff_dense] at hcoeff
  -- (DensePoly.toPoly [[0,-4],[-3],[0,2],[1]]).coeff 3 = toPoly [1] = 1, φ241 1 = 1 ≠ 0
  rw [show ([[0, -4], [-3], [0, 2], [1]] : GBPolyCore ℚ).getD 3 [] = [1] from rfl] at hcoeff
  rw [show toPoly ([1] : DensePoly ℚ) = 1 by
    simp [DensePoly.toPolyG_cons, DensePoly.toPolyG_nil], map_one] at hcoeff
  exact one_ne_zero hcoeff

/-! ### The ℚ[t]-similarity `lrtSubresultant ∼ lrtSubresultantCompute` for Ex 2.4.1 (all chain hyps discharged)
Plugging every discharged chain regularity lemma into `isSimilar_lrtSubresultant_lrtSubresultantCompute`
(at `m = 1`, the degree-3 index) gives the abstract `ℚ[t]`-similarity
`lrtSubresultant A D 3 ∼ DensePoly.toPoly (lrtSubresultantCompute 30 3 A D)` with **no** remaining chain hypotheses
— `hc0`/`hQ` are the derived `hc0_ex241`/`hQ_ex241`, the rest are `native_decide` facts. -/

/-- **`lrtSubresultant ∼ lrtSubresultantCompute` for Ex 2.4.1** (`ℚ[t]`-similarity, all chain hypotheses
discharged): the abstract LRT subresultant `lrtSubresultant (toPoly cA241) (toPoly cD241) 3` is `ℚ[t]`-similar
to the computable primitive LRT subresultant `DensePoly.toPoly (lrtSubresultantCompute 30 3 cA241 cD241)`. The full
chain agreement `isSimilar_lrtSubresultant_lrtSubresultantCompute` with every regularity hypothesis
discharged for the real `subresPRS` chain of Example 2.4.1. -/
theorem isSimilar_lrtSubresultant_lrtSubresultantCompute_ex241 :
    IsSimilar (lrtSubresultant (toPoly cA241) (toPoly cD241)
        (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree)
      (DensePoly.toPoly (lrtSubresultantCompute 30
        (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree cA241 cD241)) := by
  let hchain : IsSubresPRSChainInput 30 (chain 30 gP gQ) (chainBt 30 gP gQ)
      (chainS 30 gP gQ) (chainC 30 gP gQ) 1 := {
    exact_step := fun l hl => ⟨chain_hsc 30 gP gQ l, hβcn_ex241 l hl, hdiv_ex241 l hl⟩
    next_eq := fun l _ => chain_hG2 30 gP gQ l
    scale_toPoly_ne := hc0_ex241
    beta_toPoly_ne := hβ0_ex241
    leading_coeff_ne := hlc_ex241
    degree_drop := hcb_ex241
    endpoint_degree_lt := hjlt_ex241
    quotient_degree_le := hQ_ex241
    endpoint_ne_zero := hCne_ex241 }
  let hprim : IsPrimitivePartXInput
      (bsubresultantGcd 30 (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree gP gQ) := {
    content_not_zero := hg_ex241
    content_cnorm_ne := hgcn_ex241
    content_toPoly_ne := hg0_ex241
    exact_division := hrem_ex241 }
  exact isSimilar_lrtSubresultant_lrtSubresultantCompute 30 cA241 cD241 (chain 30 gP gQ)
    (chainBt 30 gP gQ) (chainS 30 gP gQ) (chainC 30 gP gQ) 1
    (chainG_zero 30 gP gQ) (chainG_one 30 gP gQ) hd0_ex241 hd1_ex241 hchain
    hfilt_ex241 hprim

/-! ### The headline closure: `Φ (lrtSubresultant) ∼ Φ (DensePoly.toPoly lrtGcdCompute)` over `ℚ[t]/(4t²+1)`
Pushing the `ℚ[t]`-similarity `isSimilar_lrtSubresultant_lrtSubresultantCompute_ex241` through the residue
map `φ241` via the *correct* bridge `isSimilar_mapRingHom_of_irreducible` (`4t²+1` irreducible), and chaining
the `bmonicXmodR` unit bridge (`mapRingHom_toPolyG_bmonicXmodR`, `u = 1`), lands the residue-ring similarity
between the abstract `lrtSubresultant` and the computable `lrtGcdCompute` for Example 2.4.1.

The **only** remaining hypothesis is `Φ (lrtSubresultant …) ≠ 0` — the nonvanishing of the residue
specialization of the (noncomputable) subresultant. It is genuinely mathematics-grade: it equals
`(4t²+1) ∤ content(lrtSubresultant A D 3)`, a fact about the `ℚ[t]`-content of the noncomputable subresultant
that cannot be reduced to `native_decide` (the abstract `subresultant` determinant is noncomputable in Lean).
Every *other* hypothesis — including the over-strong universal `hne` of the original
`lrtGcdCompute_isSimilar_lrtSubresultant`, which is **unsatisfiable** (it demands `φ a ≠ 0` for witness pairs
scalable by `4t²+1` ∈ ker φ) — is **discharged**: the correct bridge replaces `hne` entirely, `hc0`/`hQ` are
the derived `hc0_ex241`/`hQ_ex241`, and the residue-ring/content/monic facts are `native_decide`. -/

/-- **`Φ (lrtSubresultantCompute) ≠ 0`** (Ex 2.4.1): the `φ241`-image of the computable *primitive* LRT
subresultant is nonzero. From `Φ (DensePoly.toPoly lrtGcdCompute) ≠ 0` and the `bmonicXmodR` unit relation
`Φ (DensePoly.toPoly lrtGcdCompute) = C(φ inv)·Φ (DensePoly.toPoly lrtSubrCompute)`. -/
theorem mapRingHom_φ241_toBPoly_lrtSubresultantCompute_ne_zero :
    (Polynomial.mapRingHom φ241) (DensePoly.toPoly
      (lrtSubresultantCompute 30 (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree cA241 cD241)) ≠ 0 := by
  obtain ⟨hbridge, _⟩ := mapRingHom_toPolyG_bmonicXmodR φ241 cR241
    (lrtSubresultantCompute 30 (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree cA241 cD241)
    (by decide) φ241_toPoly_cR241 (u := 1) one_ne_zero hgu_ex241 hpz_ex241
  intro h
  apply mapRingHom_φ241_toBPoly_lrtGcdCompute_ne_zero
  rw [lrtGcdCompute, hbridge, h, mul_zero]

/-! ### The `hLne` residue non-vanishing, reduced to the `eval-at-root` form (Ex 2.4.1)
The single remaining hypothesis `hLne : Φ (lrtSubresultant A D 3) ≠ 0` is, via the `mk ↔ eval-at-root`
bridge `mapRingHom_mk_lrtSubresultant`, exactly the statement that the *base-changed* LRT subresultant over
`R241 = ℚ(i/2)`, specialized at the root `α = root(4t²+1)`, is nonzero:
`(lrtSubresultant (A.map σ) (D.map σ) 3).map (evalRingHom α) ≠ 0` (`σ = of (4t²+1)` the base change). This
is the residue specialization of the abstract LRT subresultant at the residue `α = i/2` — exactly the object
the proven LRT regularity `leadingCoeff_lrtSubresultant_eval_ne_zero` controls, *provided* the index `3`
matches the residue multiplicity `rootMultiplicity α (rtResultant (A.map σ) (D.map σ))`. The bridge below
records the reduction; discharging it needs the multiplicity-`3` fact over an algebraically closed extension
(see the closing note: `α = i/2` is a residue of multiplicity exactly `3 = deg gcd(D, A − (i/2)·D')`). -/

/-- **`hLne` ⟺ residue specialization of the base-changed subresultant is nonzero** (Ex 2.4.1): the residue
non-vanishing `Φ (lrtSubresultant A D 3) ≠ 0` (where `Φ = mapRingHom φ241`, `φ241 = mk (4t²+1)`) is, by the
`mk ↔ eval-at-root` bridge `mapRingHom_mk_lrtSubresultant`, *defeq-after-rewrite* equal to the non-vanishing
of the base-changed LRT subresultant `lrtSubresultant (A.map σ) (D.map σ) 3` (over `R241 = ℚ(i/2)`,
`σ = of (4t²+1)`) specialized at the root `α = root (4t²+1)`. This identifies `hLne` with the abstract
`lrtSubresultant_eval`-style object at the residue `α`, the entry point for the LRT regularity transfer. -/
theorem mapRingHom_φ241_lrtSubresultant_ex241_eq_eval :
    (Polynomial.mapRingHom φ241) (lrtSubresultant (toPoly cA241) (toPoly cD241) 3)
      = (lrtSubresultant ((toPoly cA241).map (AdjoinRoot.of (toPoly cR241)))
            ((toPoly cD241).map (AdjoinRoot.of (toPoly cR241))) 3).map
          (Polynomial.evalRingHom (AdjoinRoot.root (toPoly cR241))) :=
  mapRingHom_mk_lrtSubresultant (toPoly cR241) (toPoly cA241) (toPoly cD241) 3

/-- **The closed residue-ring agreement for Example 2.4.1**: over the residue field
`R241 = ℚ[t]/(4t²+1) = AdjoinRoot (toPoly cR241)`, the `φ241`-image of the abstract LRT subresultant
`lrtSubresultant (toPoly cA241) (toPoly cD241) 3` is `IsSimilar` to the `φ241`-image of the computable LRT
log argument `DensePoly.toPoly (lrtGcdCompute 30 3 cR241 cA241 cD241)` — i.e. the engine's degree-3 output **is** the
honest LRT subresultant of Example 2.4.1, up to a residue-ring unit. Everything is discharged except the
single hypothesis `hLne` that the residue specialization of the (noncomputable) subresultant is nonzero
(`(4t²+1) ∤ content(lrtSubresultant)`, mathematics-grade). The `ℚ[t]`-similarity
(`isSimilar_lrtSubresultant_lrtSubresultantCompute_ex241`, hypothesis-free) is pushed through `φ241` by the
*correct* bridge `isSimilar_mapRingHom_of_irreducible` (replacing the unsatisfiable universal `hne`), then
chained with the `bmonicXmodR` unit bridge. -/
theorem lrtGcdCompute_ex241_isSimilar_lrtSubresultant
    (hLne : (Polynomial.mapRingHom φ241)
      (lrtSubresultant (toPoly cA241) (toPoly cD241)
        (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree) ≠ 0) :
    IsSimilar ((Polynomial.mapRingHom φ241)
        (lrtSubresultant (toPoly cA241) (toPoly cD241)
          (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree))
      ((Polynomial.mapRingHom φ241) (DensePoly.toPoly
        (lrtGcdCompute 30 (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree cR241 cA241 cD241))) := by
  -- Φ L ∼ Φ M via the correct bridge (4t²+1 irreducible)
  have hLM : IsSimilar
      ((Polynomial.mapRingHom φ241) (lrtSubresultant (toPoly cA241) (toPoly cD241)
        (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree))
      ((Polynomial.mapRingHom φ241) (DensePoly.toPoly (lrtSubresultantCompute 30
        (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree cA241 cD241))) :=
    isSimilar_mapRingHom_of_irreducible (toPoly cR241) irreducible_toPoly_cR241 φ241
      φ241_eq_zero_iff isSimilar_lrtSubresultant_lrtSubresultantCompute_ex241
      hLne mapRingHom_φ241_toBPoly_lrtSubresultantCompute_ne_zero
  -- Φ M ∼ Φ M_gcd via the bmonicXmodR unit bridge
  obtain ⟨hbridge, hunit⟩ := mapRingHom_toPolyG_bmonicXmodR φ241 cR241
    (lrtSubresultantCompute 30 (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree cA241 cD241)
    (by decide) φ241_toPoly_cR241 (u := 1) one_ne_zero hgu_ex241 hpz_ex241
  have hMMgcd : IsSimilar
      ((Polynomial.mapRingHom φ241) (DensePoly.toPoly (lrtSubresultantCompute 30
        (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree cA241 cD241)))
      ((Polynomial.mapRingHom φ241) (DensePoly.toPoly
        (lrtGcdCompute 30 (DensePoly.toPoly (chain 30 gP gQ (1 + 2))).natDegree cR241 cA241 cD241))) :=
    isSimilar_of_unit_mul hunit (by rw [lrtGcdCompute]; exact hbridge)
  exact hLM.trans hMMgcd

/-- **The engine's output is the honest LRT subresultant of Example 2.4.1**: the `φ241`-image of the
computed log argument `x³ + 2t·x² − 3x − 4t` (`= lrtGcdCompute 30 3 cR241 cA241 cD241`, by `lrtGcd_ex241`)
is `IsSimilar` over `ℚ[t]/(4t²+1)` to the `φ241`-image of the abstract `lrtSubresultant`. Restates
`lrtGcdCompute_ex241_isSimilar_lrtSubresultant` with the computed value `[[0,-4],[-3],[0,2],[1]]` substituted
(via `lrtGcd_ex241`) — the book's `S(t,x) = x³+2tx²−3x−4t`. The single hypothesis is the residue
nonvanishing of the noncomputable subresultant. -/
example
    (hLne : (Polynomial.mapRingHom φ241)
      (lrtSubresultant (toPoly cA241) (toPoly cD241) 3) ≠ 0) :
    IsSimilar ((Polynomial.mapRingHom φ241)
        (lrtSubresultant (toPoly cA241) (toPoly cD241) 3))
      ((Polynomial.mapRingHom φ241) (DensePoly.toPoly
        ([[0, -4], [-3], [0, 2], [1]] : GBPolyCore ℚ))) := by
  have h := lrtGcdCompute_ex241_isSimilar_lrtSubresultant
    (by rw [natDegree_toBPoly_chainG3_ex241]; exact hLne)
  rw [natDegree_toBPoly_chainG3_ex241, lrtGcd_ex241] at h
  exact h


end DeepWiki.SymbolicIntegration.Compute

namespace DeepWiki.SymbolicIntegration

open Polynomial

open scoped Classical in
/-- **`cD241` is separable** (`x⁶−5x⁴+5x²+4` is squarefree): the computable extended gcd of `D` and
`D'` is the constant `[4]` (`native_decide`), so the Bézout cofactors scaled by `1/4` witness
`a·D + b·D' = 1` (`separable_def'`). -/
theorem separable_toPoly_cD241 : (Compute.toPoly Compute.cD241 : ℚ[X]).Separable := by
  rw [separable_def']
  have hbez :
      Compute.toPoly (CPolyEuclidean.gcdExt Compute.cD241 (Compute.cderiv Compute.cD241)).2.1
          * Compute.toPoly Compute.cD241
        + Compute.toPoly (CPolyEuclidean.gcdExt Compute.cD241 (Compute.cderiv Compute.cD241)).2.2
          * Compute.toPoly (Compute.cderiv Compute.cD241)
      = Compute.toPoly (CPolyEuclidean.gcdExt Compute.cD241 (Compute.cderiv Compute.cD241)).1 := by
    exact
      DensePoly.toPolyG_cgcdWf Compute.cD241 (Compute.cderiv Compute.cD241)
  have hderiv : Compute.toPoly (Compute.cderiv Compute.cD241) =
      derivative (Compute.toPoly Compute.cD241) := by
    exact
      DensePoly.toPolyG_cderivG Compute.cD241
  rw [hderiv] at hbez
  have hg : Compute.toPoly (CPolyEuclidean.gcdExt Compute.cD241 (Compute.cderiv Compute.cD241)).1
      = C 4 := by
    have : (CPolyEuclidean.gcdExt Compute.cD241 (Compute.cderiv Compute.cD241)).1 = [4] := by
      native_decide
    rw [this]
    simp [DensePoly.toPolyG_cons, DensePoly.toPolyG_nil]
  rw [hg] at hbez
  refine ⟨C (4:ℚ)⁻¹ * Compute.toPoly (CPolyEuclidean.gcdExt Compute.cD241
            (Compute.cderiv Compute.cD241)).2.1,
          C (4:ℚ)⁻¹ * Compute.toPoly (CPolyEuclidean.gcdExt Compute.cD241
            (Compute.cderiv Compute.cD241)).2.2, ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add, hbez, ← C_mul]
  norm_num

/-- **`toPoly cR241 = 4t²+1` is separable** over `ℚ` (degree-2, distinct roots `±i/2`): it is
irreducible over `ℚ` (`irreducible_toPoly_cR241`) and `ℚ` has characteristic zero
(`Irreducible.separable`). -/
theorem separable_toPoly_cR241 : (Compute.toPoly Compute.cR241 : ℚ[X]).Separable :=
  by
    have h : Irreducible ((1 : ℚ[X]) + 4 * X ^ 2) := by
      rw [← Compute.toPoly_cR241]
      exact Compute.irreducible_toPoly_cR241
    rw [Compute.toPoly_cR241]
    exact h.separable

/-! ### The multiplicity-3 nonvanishing of the LRT subresultant at the residue `α = i/2` -/

open scoped Classical in
/-- **The residue `β` is a multiplicity-3 root of the base-changed `rtResultant`** (Ex 2.4.1): over a
field `L` with an injective `τ : ℚ →+* L` and `β` a root of `(4t²+1).map τ`, the multiplicity of `β` in
`rtResultant (cA241.map τ) (cD241.map τ)` is exactly 3. From `rtResultant_map_of_injective` and the honest
equation `rtResultant_ex241_eq`, `rtResultant (…τ) = C(τ 45796)·((4t²+1).map τ)³`, and `(4t²+1).map τ` is
separable (so `β` is a simple root), so `rootMultiplicity_C_mul_pow_of_separable` gives `3`. -/
theorem rootMultiplicity_rtResultant_map_ex241 {L : Type*} [Field L] (τ : ℚ →+* L)
    (hτ : Function.Injective τ) {β : L}
    (hβ : ((Compute.toPoly Compute.cR241).map τ).IsRoot β) :
    Polynomial.rootMultiplicity β
        (rtResultant ((Compute.toPoly Compute.cA241).map τ) ((Compute.toPoly Compute.cD241).map τ))
      = 3 := by
  rw [rtResultant_map_of_injective τ hτ, Compute.rtResultant_ex241_eq]
  -- `(C 45796·(C4·X²+C1)³).map τ = C (τ 45796) · ((C4·X²+C1).map τ)³`
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow]
  set p := (Polynomial.C (4:ℚ) * Polynomial.X ^ 2 + Polynomial.C 1).map τ with hp
  -- `p = (toPoly cR241).map τ` (both `4t²+1`), so `p` is separable and `β` is a root
  have hpeq : p = (Compute.toPoly Compute.cR241).map τ := by
    rw [hp, Compute.toPoly_cR241]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_ofNat, map_ofNat, map_one]
    ring
  have hpsep : p.Separable := by rw [hpeq]; exact separable_toPoly_cR241.map
  have hpβ : p.IsRoot β := by rw [hpeq]; exact hβ
  have hc : τ 45796 ≠ 0 := by
    simpa using (map_ne_zero_iff τ hτ).mpr (by norm_num : (45796 : ℚ) ≠ 0)
  exact rootMultiplicity_C_mul_pow_of_separable hc hpsep hpβ 3

/-! ### Discharging `hLne` for Example 2.4.1 (the residue non-vanishing) -/

open Compute in
/-- **`(toPoly cD241).natDegree = 6`** (`D = x⁶−5x⁴+5x²+4`). -/
theorem natDegree_toPoly_cD241 : (toPoly cD241).natDegree = 6 := by
  rw [← DensePoly.cdegG_eq_natDegree]; decide

set_option maxHeartbeats 800000 in
open Compute in
open scoped Classical in
/-- **The residue specialization of the base-changed LRT subresultant is nonzero** (Ex 2.4.1): over
`R241 = ℚ[t]/(4t²+1)`, the degree-3 LRT subresultant of `(A.map σ, D.map σ)` specialized at the root
`α = i/2` is nonzero, `(lrtSubresultant (cA241.map σ) (cD241.map σ) 3).map (evalRingHom α) ≠ 0`. Proved by
base-changing to the algebraic closure `K̄ = AlgebraicClosure R241` (`ι` injective), where the LRT
regularity core `leadingCoeff_lrtSubresultant_eval_ne_zero` fires: the residue `β = ι α` is a root of the
base-changed `rtResultant` of *multiplicity exactly 3* (`rootMultiplicity_rtResultant_map_ex241`, from the
honest equation `rtResultant = 45796·(4t²+1)³`), so the index-3 specialized subresultant has degree 3 and
nonzero leading coefficient. The `ι`-image being nonzero reflects back through injectivity. -/
theorem lrtSubresultant_map_eval_ex241_ne_zero :
    (lrtSubresultant ((toPoly cA241).map (AdjoinRoot.of (toPoly cR241)))
        ((toPoly cD241).map (AdjoinRoot.of (toPoly cR241))) 3).map
      (Polynomial.evalRingHom (AdjoinRoot.root (toPoly cR241))) ≠ 0 := by
  classical
  set R241 := AdjoinRoot (toPoly cR241) with hR
  set σ : ℚ →+* R241 := AdjoinRoot.of (toPoly cR241) with hσ
  set α : R241 := AdjoinRoot.root (toPoly cR241) with hα
  set Kbar := AlgebraicClosure R241 with hK
  set ι : R241 →+* Kbar := algebraMap R241 Kbar with hι
  have hιinj : Function.Injective ι := FaithfulSMul.algebraMap_injective R241 Kbar
  set τ : ℚ →+* Kbar := ι.comp σ with hτ
  have hτinj : Function.Injective τ := hιinj.comp (AdjoinRoot.of (toPoly cR241)).injective
  set β : Kbar := ι α with hβdef
  -- `β` is a root of `(toPoly cR241).map τ`
  have hβroot : ((toPoly cR241).map τ).IsRoot β := by
    have hαroot : ((toPoly cR241).map σ).IsRoot α := AdjoinRoot.isRoot_root (toPoly cR241)
    rw [hτ, ← Polynomial.map_map, hβdef]
    simpa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.eval₂_hom]
      using congrArg ι hαroot
  -- separability and degree facts over `Kbar`
  have hDsep : ((toPoly cD241).map τ).Separable := separable_toPoly_cD241.map
  have hAD : ((toPoly cA241).map τ).natDegree < ((toPoly cD241).map τ).natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective hτinj,
      Polynomial.natDegree_map_eq_of_injective hτinj]
    exact natDegree_cA241_lt_cD241
  -- the multiplicity-3 fact
  have hmult : Polynomial.rootMultiplicity β
      (rtResultant ((toPoly cA241).map τ) ((toPoly cD241).map τ)) = 3 :=
    rootMultiplicity_rtResultant_map_ex241 τ hτinj hβroot
  -- `β` is a root of `rtResultant (A.map τ)(D.map τ)`
  have hRne : rtResultant ((toPoly cA241).map τ) ((toPoly cD241).map τ) ≠ 0 := by
    intro h0; rw [h0, Polynomial.rootMultiplicity_zero] at hmult; exact absurd hmult (by norm_num)
  have hβR : (rtResultant ((toPoly cA241).map τ) ((toPoly cD241).map τ)).IsRoot β :=
    (Polynomial.rootMultiplicity_pos hRne).mp (by rw [hmult]; norm_num)
  -- the regularity core over the algebraically closed `Kbar` at multiplicity `3 < deg D = 6`
  have hdegD6 : ((toPoly cD241).map τ).natDegree = 6 := by
    rw [Polynomial.natDegree_map_eq_of_injective hτinj]; exact natDegree_toPoly_cD241
  have hcore := leadingCoeff_lrtSubresultant_eval_ne_zero
    ((toPoly cA241).map τ) ((toPoly cD241).map τ) hDsep hAD β hβR (by rw [hmult, hdegD6]; norm_num)
  rw [hmult] at hcore
  -- so the specialized subresultant over `Kbar` is nonzero
  have hKbarne : ((lrtSubresultant ((toPoly cA241).map τ) ((toPoly cD241).map τ) 3).map
      (Polynomial.evalRingHom β)) ≠ 0 := fun h => hcore (by rw [h, Polynomial.coeff_zero])
  -- this `Kbar` object is the `ι`-image of the `R241` object; reflect nonzero back
  intro hzero
  apply hKbarne
  -- `map_eval` commute (over `R241 → Kbar`), then `A.map σ.map ι = A.map τ`, `ι α = β`
  have hmapτ : ∀ p : ℚ[X], p.map τ = (p.map σ).map ι := fun p => by rw [hτ, Polynomial.map_map]
  have hcommute := map_eval_lrtSubresultant_map ι hιinj
    ((toPoly cA241).map σ) ((toPoly cD241).map σ) 3 α
  rw [← hmapτ, ← hmapτ] at hcommute
  rw [show β = ι α from hβdef, ← hcommute, hzero, Polynomial.map_zero]

open Compute in
/-- **Example 2.4.1's `hLne` is a theorem**: `Φ (lrtSubresultant (toPoly cA241) (toPoly cD241) 3) ≠ 0`
(with `Φ = mapRingHom φ241`, `φ241 = mk (4t²+1)`). Routes the residue-specialization form
(`mapRingHom_φ241_lrtSubresultant_ex241_eq_eval`) to the proven base-changed non-vanishing
`lrtSubresultant_map_eval_ex241_ne_zero`. -/
theorem mapRingHom_φ241_lrtSubresultant_ex241_ne_zero :
    (Polynomial.mapRingHom φ241) (lrtSubresultant (toPoly cA241) (toPoly cD241) 3) ≠ 0 := by
  rw [mapRingHom_φ241_lrtSubresultant_ex241_eq_eval]
  exact lrtSubresultant_map_eval_ex241_ne_zero

open Compute in
/-- **Example 2.4.1's LRT closure, hypothesis-free** (§2.4, p.48): over the residue ring
`ℚ[t]/(4t²+1)`, the `φ241`-image of the abstract LRT subresultant `lrtSubresultant (toPoly cA241)
(toPoly cD241) 3` is `IsSimilar` to the `φ241`-image of the computable LRT log argument
`x³ + 2t·x² − 3x − 4t` (`= DensePoly.toPoly [[0,−4],[−3],[0,2],[1]]`, the book's `S(t,x)`). The single hypothesis
`hLne` of `lrtGcdCompute_ex241_isSimilar_lrtSubresultant` is now discharged by the proven residue
non-vanishing `mapRingHom_φ241_lrtSubresultant_ex241_ne_zero` (the multiplicity-3 regularity of the LRT
subresultant at the residue `α = i/2`). So the computable engine's degree-3 output **is** the honest LRT
subresultant of Example 2.4.1, up to a residue-ring unit — unconditionally. -/
theorem lrtGcdCompute_ex241_isSimilar_lrtSubresultant_closed :
    IsSimilar ((Polynomial.mapRingHom φ241)
        (lrtSubresultant (toPoly cA241) (toPoly cD241) 3))
      ((Polynomial.mapRingHom φ241) (DensePoly.toPoly
        ([[0, -4], [-3], [0, 2], [1]] : GBPolyCore ℚ))) := by
  have h := lrtGcdCompute_ex241_isSimilar_lrtSubresultant
    (by rw [natDegree_toBPoly_chainG3_ex241]; exact mapRingHom_φ241_lrtSubresultant_ex241_ne_zero)
  rw [natDegree_toBPoly_chainG3_ex241, lrtGcd_ex241] at h
  exact h

open Compute in
-- The Example 2.4.1 LRT log argument is the honest subresultant, unconditionally (book's `x³+2tx²−3x−4t`).
example :
    IsSimilar ((Polynomial.mapRingHom φ241)
        (lrtSubresultant (toPoly cA241) (toPoly cD241) 3))
      ((Polynomial.mapRingHom φ241) (DensePoly.toPoly
        ([[0, -4], [-3], [0, 2], [1]] : GBPolyCore ℚ))) :=
  lrtGcdCompute_ex241_isSimilar_lrtSubresultant_closed

/-! ### Example 2.4.1 through the hex-style engine (`DeepWiki/CAlgebra`) -/

/-- **Example 2.4.1, the new engine's Rothstein–Trager resultant** (§2.4, p.48): the
class-dispatched `rtResultant` (primitive-PRS backend) reproduces the book's
`45796·(4t²+1)³` exactly — cross-engine agreement with `cResidueResultantTower` above. -/
theorem rtResultant_ex241_hex_engine :
    (DeepWiki.CAlgebra.DensePoly.rtResultant
        (DeepWiki.CAlgebra.DensePoly.ofList ([6, 0, -3, 0, 1] : List ℚ))
        (DeepWiki.CAlgebra.DensePoly.ofList ([4, 0, 5, 0, -5, 0, 1] : List ℚ))).coeffs
      = [45796, 0, 549552, 0, 2198208, 0, 2930944] := by
  native_decide

/-- **Example 2.4.1, the new engine's LRT coefficient polynomial** (§2.4, p.48): the single
log-term factor is the book's `R = 4t²+1` (at multiplicity 3), exactly. -/
theorem lrtLogTerms_ex241_hex_engine :
    (DeepWiki.CAlgebra.DensePoly.lrtLogTerms
        (DeepWiki.CAlgebra.DensePoly.ofList ([6, 0, -3, 0, 1] : List ℚ))
        (DeepWiki.CAlgebra.DensePoly.ofList ([4, 0, 5, 0, -5, 0, 1] : List ℚ))).map
      (fun t => t.1.coeffs)
      = [[1, 0, 4]] := by
  native_decide

end DeepWiki.SymbolicIntegration
