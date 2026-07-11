import DeepWiki.SymbolicIntegration.Engine.Tower.WellFounded
import DeepWiki.SymbolicIntegration.Engine.PolySplitFactor
import DeepWiki.SymbolicIntegration.Engine.Tower.RischDE
import DeepWiki.ComputableAlgebra.PolyAntiderivative

/-! # Well-founded generic tower Risch-DE oracle `cRischDE`

The generic Risch-DE pipeline, by well-founded recursion: the recursive bottoms
`cPolyRischDECancelPrim` (primitive cancellation), `cPolyRischDECancelExp` (hyperexponential
cancellation), and `cValuation` (the `p`-adic valuation), plus a flat composition over them for the
weak normalizer, normal/special denominators, degree bound, and the headline `cRischDE`. `[CField α]`-only
on the runtime fragment (plus selected gcd/split capabilities, `[CDiffField α]`, and `[CRischField α]` where needed), so it
`native_decide`s over the noncomputable tower. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u

/-! ## The three remaining recursive bottoms

`cPolyRischDECancelPrim` / `cPolyRischDECancelExp` (degree-by-degree own-loops on
`(cnorm c).length`, carrying `[CRischField α]`) and `cValuation` (trial-division own-loop on
`(cnorm x).length`), each well-founded with a structural runtime guard. -/

namespace DensePoly

variable {α : Type*} [CField α] [CDiffField α] [CRischField α]

/-- Generic primitive cancellation Poly-Risch-DE `cPolyRischDECancelPrim Dt b c n`: given the primitive
monomial derivation `D` (`Dt ∈ α`), scalar `b ∈ α*` (`b₀ = lc(b)`) and `c ∈ α[t]` with degree bound `n : ℤ`,
solves `Dq + b·q = c` degree-by-degree, recursing at degree `m = deg(c)` into the base RDE
`CRischField.crischDESolve b₀ (lc c)`, leading monomial `s·tᵐ`, remainder `c' = c − b·(s·tᵐ) − D(s·tᵐ)`.
Returns `none` or `some q`. Well-founded on `(cnorm c).length`. `[CRischField α]`-generic. -/
def cPolyRischDECancelPrim (Dt : DensePoly α) (b c : DensePoly α) (n : ℤ) :
    Option (DensePoly α) :=
  let b0 : α := clead b
  if cisZero c then some []
  else if n < (cdeg c : ℤ) then none
  else
    let m : ℕ := cdeg c
    match CRischField.crischDESolve b0 (clead c) with
    | none => none
    | some s =>
      let stm : DensePoly α := cshift m [s]               -- `s·tᵐ`
      let c' := csub (csub c (cmul b stm)) (CPolyEngine.monomialDeriv Dt stm)
      if (cnorm c' : List α).length < (cnorm c : List α).length then
        match cPolyRischDECancelPrim Dt b c' ((m : ℤ) - 1) with
        | none => none
        | some q => some (cadd stm q)
      else none   -- unreachable on a real run (the leading monomial cancels, degree drops)
termination_by (cnorm c).length
decreasing_by assumption

/-- Generic hyperexponential cancellation Poly-Risch-DE `cPolyRischDECancelExp Dt b c n`: given the
hyperexponential monomial derivation `D` (`η = Dt/t ∈ α`, `δ = 1`), scalar `b ∈ α*` (`b₀ = lc(b)`) and
`c ∈ α[t]` with degree bound `n : ℤ`, solves `Dq + b·q = c` degree-by-degree, recursing at degree
`m = deg(c)` into the base RDE `crischDESolve (b₀ + m·η) (lc c)` (`η = cExpEta Dt`), leading monomial
`s·tᵐ`, remainder `c' = c − b·(s·tᵐ) − D(s·tᵐ)`. Returns `none` or `some q`. Well-founded on
`(cnorm c).length`. `[CRischField α]`-generic. -/
def cPolyRischDECancelExp (Dt : DensePoly α) (b c : DensePoly α) (n : ℤ) :
    Option (DensePoly α) :=
  let b0 : α := clead b
  let η : α := cExpEta Dt
  if cisZero c then some []
  else if n < (cdeg c : ℤ) then none
  else
    let m : ℕ := cdeg c
    -- eq. 6.24 base RDE `Ds + (b₀ + m·η)·s = lc(c)` over `α`.
    let coeff : α := CCommRing.add b0 (CCommRing.mul (CField.natCast m) η)
    match CRischField.crischDESolve coeff (clead c) with
    | none => none
    | some s =>
      let stm : DensePoly α := cshift m [s]               -- `s·tᵐ`
      let c' := csub (csub c (cmul b stm)) (CPolyEngine.monomialDeriv Dt stm)
      if (cnorm c' : List α).length < (cnorm c : List α).length then
        match cPolyRischDECancelExp Dt b c' ((m : ℤ) - 1) with
        | none => none
        | some q => some (cadd stm q)
      else none   -- unreachable on a real run (the leading monomial cancels, degree drops)
termination_by (cnorm c).length
decreasing_by assumption

end DensePoly

namespace DensePoly

variable {α : Type*} [CField α]

/-- Generic `p`-adic valuation `cValuation p x = ν_p(x)`: the multiplicity of the monic irreducible `p`
dividing `x` (largest `k` with `pᵏ ∣ x`), by trial division. Stops at the zero polynomial, a constant/unit
`p` (`cdeg p = 0`), or a non-dividing step, else recurses on `x/p` (`CPolyEuclidean.div`) and adds one. Well-founded on
`(cnorm x).length`. `[CField α]`-generic. -/
def cValuation (p x : DensePoly α) : ℕ :=
  if cisZero x then 0
  else if cdeg p = 0 then 0
  else if CPolyEuclidean.dvd p x then
    let xq := CPolyEuclidean.div x p
    if (cnorm xq : List α).length < (cnorm x : List α).length then
      1 + cValuation p xq
    else 0   -- unreachable on a real run (non-constant `p ∣ x` drops the degree)
  else 0
termination_by (cnorm x).length
decreasing_by assumption

variable [CFieldSpec α]

/-- `cValuation` divides: `toPoly p ^ cValuation p x ∣ toPoly x`. Each recursive step peels one
exact `p` factor using the exact-division theorem; terminal branches return the unit power. -/
theorem toPolyG_pow_cValuationG_dvd (p x : DensePoly α) :
    toPoly p ^ cValuation p x ∣ toPoly x := by
  induction x using cValuation.induct p with
  | case1 x hx =>
      rw [cValuation.eq_def, if_pos hx, pow_zero]
      exact one_dvd _
  | case2 x hx hp =>
      rw [cValuation.eq_def, if_neg hx, if_pos hp, pow_zero]
      exact one_dvd _
  | case3 x hx hp hdvd _xq hguard ih =>
      rw [cValuation.eq_def, if_neg hx, if_neg hp, if_pos hdvd, if_pos hguard]
      have hpne : cnorm p ≠ [] := fun hpe => hp (by rw [cdeg, hpe]; rfl)
      have hp0 : toPoly p ≠ 0 := fun h => hpne ((cnormG_eq_nil_iff _).mpr h)
      have hp0G : CPoly.toPoly p ≠ 0 := by rwa [toPoly_list_eq]
      have hpx : toPoly p ∣ toPoly x := by
        simpa only [toPoly_list_eq] using
          CPolyEuclidean.toPoly_dvd_of_dvd_eq_true p x hp0G hdvd
      have hid : toPoly x = toPoly (CPolyEuclidean.div x p) * toPoly p :=
        (toPolyG_div_exact x p hpne hpx).symm
      rw [add_comm, pow_add, pow_one, hid]
      exact mul_dvd_mul ih dvd_rfl
  | case4 x hx hp hdvd _xq hguard =>
      rw [cValuation.eq_def, if_neg hx, if_neg hp, if_pos hdvd, if_neg hguard, pow_zero]
      exact one_dvd _
  | case5 x hx hp hdvd =>
      rw [cValuation.eq_def, if_neg hx, if_neg hp, if_neg hdvd, pow_zero]
      exact one_dvd _

/-- `cValuation` is sharp: for nonconstant `p` and nonzero `x`, one more `p` factor than
`cValuation p x` does not divide `x`. Uses `CPolyEuclidean.dvd`'s false-case converse at the terminal
non-dividing branch. -/
theorem cValuationG_sharp (p x : DensePoly α)
    (hp : cdeg p ≠ 0) (hx0 : toPoly x ≠ 0) :
    ¬ toPoly p ^ (cValuation p x + 1) ∣ toPoly x := by
  have hpne : cnorm p ≠ [] := fun hpe => hp (by rw [cdeg, hpe]; rfl)
  have hp0 : toPoly p ≠ 0 := fun h => hpne (by rw [cnormG_eq_nil_iff]; exact h)
  have hpdeg : 0 < (toPoly p).natDegree := by
    rw [← cdegG_eq_natDegree]
    omega
  revert hx0
  induction x using cValuation.induct p with
  | case1 x hx =>
      intro hx0
      exact False.elim (hx0 ((cisZeroG_iff x).mp hx))
  | case2 x hx hdeg =>
      intro _hx0
      exact False.elim (hp hdeg)
  | case3 x hx hdeg hdvd _xq hguard ih =>
      intro hx0
      rw [cValuation.eq_def, if_neg hx, if_neg hdeg, if_pos hdvd, if_pos hguard]
      have hp0G : CPoly.toPoly p ≠ 0 := by rwa [toPoly_list_eq]
      have hpx : toPoly p ∣ toPoly x := by
        simpa only [toPoly_list_eq] using
          CPolyEuclidean.toPoly_dvd_of_dvd_eq_true p x hp0G hdvd
      have hid : toPoly x = toPoly (CPolyEuclidean.div x p) * toPoly p :=
        (toPolyG_div_exact x p hpne hpx).symm
      have hq0 : toPoly (CPolyEuclidean.div x p) ≠ 0 := by
        intro h
        apply hx0
        rw [hid, h, zero_mul]
      have hihq := ih hq0
      intro hcontra
      apply hihq
      rw [hid, show 1 + cValuation p (CPolyEuclidean.div x p) + 1 =
          (cValuation p (CPolyEuclidean.div x p) + 1) + 1 by ring, pow_succ] at hcontra
      exact (mul_dvd_mul_iff_right hp0).mp hcontra
  | case4 x hx hdeg hdvd _xq hguard =>
      intro hx0
      have hp0G : CPoly.toPoly p ≠ 0 := by rwa [toPoly_list_eq]
      have hpx : toPoly p ∣ toPoly x := by
        simpa only [toPoly_list_eq] using
          CPolyEuclidean.toPoly_dvd_of_dvd_eq_true p x hp0G hdvd
      have hid : toPoly x = toPoly (CPolyEuclidean.div x p) * toPoly p :=
        (toPolyG_div_exact x p hpne hpx).symm
      have hq0 : toPoly (CPolyEuclidean.div x p) ≠ 0 := by
        intro h
        apply hx0
        rw [hid, h, zero_mul]
      have hxne : cnorm x ≠ [] := fun he => hx0 ((cnormG_eq_nil_iff _).mp he)
      have hqne : cnorm (CPolyEuclidean.div x p) ≠ [] := fun he =>
        hq0 (by rw [cnormG_eq_nil_iff] at he; exact he)
      have hdegdrop : (toPoly (CPolyEuclidean.div x p)).natDegree < (toPoly x).natDegree := by
        rw [hid, Polynomial.natDegree_mul hq0 hp0]
        omega
      have hlen : (cnorm (CPolyEuclidean.div x p) : List α).length < (cnorm x : List α).length := by
        rw [length_cnormG_of_ne _ hqne, length_cnormG_of_ne _ hxne]
        omega
      exact False.elim (hguard hlen)
  | case5 x hx hdeg hdvd =>
      intro _hx0
      have hfalse : CPolyEuclidean.dvd p x = false := Bool.eq_false_iff.mpr hdvd
      rw [cValuation.eq_def, if_neg hx, if_neg hdeg, if_neg hdvd, zero_add, pow_one]
      have hp0G : CPoly.toPoly p ≠ 0 := by rwa [toPoly_list_eq]
      simpa only [toPoly_list_eq] using
        CPolyEuclidean.not_toPoly_dvd_of_dvd_eq_false p x hp0G hfalse

end DensePoly

/-! ## The flat-composition §6 pipeline

Everything past the five recursive bottoms is a flat composition over the leaves above plus the generic
`CPolyEuclidean.divmod`/`gcdExt`, `CPoly.diophantineReduced`, `CPolyEuclidean.dvd`, and the §5.6
`cResidueResultantTower`/`cinterpolate`/`ceval`. -/

namespace DensePoly

variable {α : Type*} [CField α] [CDiffField α] [CPolyGcd DensePoly α]
  [CPolySplitFactor DensePoly α]

/-- Generic weak normalizer `cWeakNormalizer Dt fnum fden = q ∈ α[t]`: split the denominator into its
normal part `dₙ` (`CPoly.splitFactor`), form `d₁ = (dₙ/g)/gcd(dₙ/g, g)` with `g = gcd(dₙ, dₙ')`, solve the
residue numerator `a` via `CPoly.diophantineReduced`, build the residue resultant `r = res_t(a − z·Dd₁, d₁)`
(`cResidueResultantTower`), and return `∏ᵢ gcd(a − nᵢ·Dd₁, d₁)^{nᵢ}` over the positive integer roots `nᵢ`
of `r`. For an already-weakly-normalized `f`, `q = 1`; gcd and differential splitting are selected
through `CPolyGcd` and `CPolySplitFactor`. -/
def cWeakNormalizer (Dt : DensePoly α) (fnum fden : DensePoly α) (boundRoots : ℕ := 16) : DensePoly α :=
  let dn := (CPoly.splitFactor Dt fden).1
  let g := CPolyGcd.compute dn (cderiv dn)
  let dstar := CPolyEuclidean.div dn g
  let d1 := CPolyEuclidean.div dstar (CPolyGcd.compute dstar g)
  let fdenOverD1 := CPolyEuclidean.div fden d1
  let a := (CPoly.diophantineReduced fdenOverD1 d1 fnum).1
  let Dd1 := CPolyEngine.monomialDeriv Dt d1
  let r := cResidueResultantTower Dt a d1
  let roots := cPosIntRoots r boundRoots
  roots.foldl (fun (acc : DensePoly α) (n : ℕ) =>
    let gi := CPolyGcd.compute (csub a (cscale (CField.natCast n) Dd1)) d1
    cmul acc (cpow gi n)) [CCommRing.one]

/-- Generic normal-denominator reduction `cRdeNormalDenominator Dt fnum fden gnum gden` for weakly
normalized `f = fnum/fden`, `g = gnum/gden`. Returns `none` or `some (a, b, c, h)` reducing `Dy + fy = g` to
`a·Dq + b·q = c` with `q = y·h`. Split the denominators into normal parts `dₙ, eₙ`; `p = gcd(dₙ, eₙ)`,
`h = gcd(eₙ, eₙ')/gcd(p, p')`; if `eₙ ∤ dₙh²` then `none`; else `a = dₙh`, `b = (dₙh·fnum − dₙ·Dh·fden)/fden`,
`c = dₙh²·gnum/gden`. -/
def cRdeNormalDenominator (Dt : DensePoly α) (fnum fden gnum gden : DensePoly α) :
    Option (DensePoly α × DensePoly α × DensePoly α × DensePoly α) :=
  let dn := (CPoly.splitFactor Dt fden).1
  let en := (CPoly.splitFactor Dt gden).1
  let p := CPolyGcd.compute dn en
  let h := CPolyEuclidean.div (CPolyGcd.compute en (cderiv en))
    (CPolyGcd.compute p (cderiv p))
  let dnh2 := cmul (cmul dn h) h
  if CPolyEuclidean.dvd en dnh2 then
    let a := cmul dn h
    let Dh := CPolyEngine.monomialDeriv Dt h
    let b := CPolyEuclidean.div (csub (cmul a fnum) (cmul (cmul dn Dh) fden)) fden
    let c := CPolyEuclidean.div (cmul dnh2 gnum) gden
    some (a, b, c, h)
  else none

end DensePoly

namespace DensePoly

variable {α : Type*} [CField α] [CDiffField α] [CPolySplitFactor DensePoly α]

/-- Generic special monic irreducible of the monomial `cSpecialPoly Dt = p`: the monic special part of
the monomial derivative `Dt` (`t²+1` hypertangent, `t` hyperexponential, `1` primitive) via the
selected splitting-factorization `CPoly.splitFactor`. -/
def cSpecialPoly (Dt : DensePoly α) : DensePoly α :=
  cmonic (CPoly.splitFactor Dt Dt).2

/-- Generic special-denominator reduction `cRdeSpecialDenominator Dt a b c`. Given `a·Dq + b·q = c` with
`a` free of special factors, returns the special-cleared quadruplet `(ā, b̄, c̄, h)` (`h = p^{−n}`) so
`r = q·h ∈ α[t]` solves `ā·Dr + b̄·r = c̄`. Steps: `p ← cSpecialPoly Dt` (constant ⇒ trivial);
`n_b = ν_p(b)`, `n_c = ν_p(c)`, `n = min(0, n_c − min(0, n_b))`, `N = max(0, −n_b, n − n_c)`; return
`(a·pᴺ, (b + n·a·Dp/p)·pᴺ, c·p^{N−n}, p^{−n})`. -/
def cRdeSpecialDenominator (Dt : DensePoly α) (a b c : DensePoly α) :
    DensePoly α × DensePoly α × DensePoly α × DensePoly α :=
  let p := cSpecialPoly Dt
  if cdeg p = 0 then (a, b, c, [CCommRing.one])
  else
    let nb : ℤ := (cValuation p b : ℤ)
    let nc : ℤ := (cValuation p c : ℤ)
    let n : ℤ := min 0 (nc - min 0 nb)
    let N : ℤ := max (max 0 (-nb)) (n - nc)
    let Nnat : ℕ := N.toNat
    let negn : ℕ := (-n).toNat
    let Nminusn : ℕ := (N - n).toNat
    let pN := cpow p Nnat
    let abar := cmul a pN
    let DpOverp := CPolyEuclidean.div (CPolyEngine.monomialDeriv Dt p) p
    let bterm := cscale (CCommRing.neg (CField.natCast negn)) (cmul a DpOverp)
    let bbar := cmul (cadd b bterm) pN
    let cbar := cmul c (cpow p Nminusn)
    let h := cpow p negn
    (abar, bbar, cbar, h)

/-- The special-denominator stage is the identity in the primitive regime: when the special polynomial is
constant, `cRdeSpecialDenominator Dt a b c = (a, b, c, [1])`. -/
theorem cRdeSpecialDenominatorG_primitive_eq (Dt : DensePoly α) (a b c : DensePoly α)
    (hp : cdeg (cSpecialPoly Dt) = 0) :
    cRdeSpecialDenominator Dt a b c = (a, b, c, [CCommRing.one]) := by
  rw [cRdeSpecialDenominator]
  simp only [hp, if_pos]

/-- Special-denominator no-clear predicate: the special-denominator shift
`n = min(0, ν_p(c) - min(0, ν_p(b)))` is zero, equivalently the reconstruction power `p^{-n}` is
trivial. -/
def CSpecialDenomNoClear (Dt : DensePoly α) (b c : DensePoly α) : Prop :=
  let p := cSpecialPoly Dt
  min (0 : ℤ) ((cValuation p c : ℤ) - min 0 (cValuation p b : ℤ)) = 0

/-- The special-denominator no-clear predicate holds for all inputs: `cValuation` is natural-valued,
so both valuations are nonnegative after casting to `ℤ`. -/
theorem cSpecialDenomNoClearG_always (Dt : DensePoly α) (b c : DensePoly α) :
    CSpecialDenomNoClear Dt b c := by
  rw [CSpecialDenomNoClear]
  have hnb : (0 : ℤ) ≤ (cValuation (cSpecialPoly Dt) b : ℤ) := Int.natCast_nonneg _
  have hnc : (0 : ℤ) ≤ (cValuation (cSpecialPoly Dt) c : ℤ) := Int.natCast_nonneg _
  omega

/-- The special-denominator reconstruction power is trivial under no-clear: if
`CSpecialDenomNoClear Dt b c` and the special polynomial is nonconstant, then
`cRdeSpecialDenominator` returns `h = [1]`. -/
theorem cRdeSpecialDenominatorG_h1_eq_one_of_noClear (Dt : DensePoly α) (a b c : DensePoly α)
    (hp : cdeg (cSpecialPoly Dt) ≠ 0) (hn : CSpecialDenomNoClear Dt b c) :
    (cRdeSpecialDenominator Dt a b c).2.2.2 = [CCommRing.one] := by
  rw [cRdeSpecialDenominator]
  simp only [if_neg hp]
  rw [CSpecialDenomNoClear] at hn
  show cpow (cSpecialPoly Dt) (-(min 0
    ((cValuation (cSpecialPoly Dt) c : ℤ)
      - min 0 (cValuation (cSpecialPoly Dt) b : ℤ)))).toNat = [CCommRing.one]
  rw [hn]
  rfl

/-- The special-denominator reconstruction power is always trivial in the nonconstant special-polynomial
regime. -/
theorem cRdeSpecialDenominatorG_h1_eq_one_always (Dt : DensePoly α) (a b c : DensePoly α)
    (hp : cdeg (cSpecialPoly Dt) ≠ 0) :
    (cRdeSpecialDenominator Dt a b c).2.2.2 = [CCommRing.one] :=
  cRdeSpecialDenominatorG_h1_eq_one_of_noClear Dt a b c hp
    (cSpecialDenomNoClearG_always Dt b c)

/-- The special-denominator coefficients factor as `(·)·pᴺ` in the no-clear regime: under
`CSpecialDenomNoClear`, the cleared coefficients are `a·pᴺ`, `b·pᴺ`, and `c·pᴺ` through `toPoly`. -/
theorem toPolyG_cRdeSpecialDenominatorG_coeffs_of_noClear [CFieldSpec α] (Dt : DensePoly α)
    (a b c : DensePoly α) (hp : cdeg (cSpecialPoly Dt) ≠ 0)
    (hn : CSpecialDenomNoClear Dt b c) :
    let pN : DensePoly α := cpow (cSpecialPoly Dt)
      (max (max 0 (-(cValuation (cSpecialPoly Dt) b : ℤ)))
        (-(cValuation (cSpecialPoly Dt) c : ℤ))).toNat
    toPoly (cRdeSpecialDenominator Dt a b c).1 = toPoly a * toPoly pN
    ∧ toPoly (cRdeSpecialDenominator Dt a b c).2.1 = toPoly b * toPoly pN
    ∧ toPoly (cRdeSpecialDenominator Dt a b c).2.2.1 = toPoly c * toPoly pN := by
  intro pN
  rw [CSpecialDenomNoClear] at hn
  have hbterm0 : CFieldSpec.toK (CCommRing.neg (CCommRing.zero : α)) = 0 := by
    rw [CFieldSpec.toK_neg, CFieldSpec.toK_zero, neg_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [cRdeSpecialDenominator]
    simp only [if_neg hp, hn, denote, zero_sub]
    dsimp only [pN]
    simp only [denote]
  · rw [cRdeSpecialDenominator]
    simp only [if_neg hp, hn, neg_zero, Int.toNat_zero, CField.natCast, denote, hbterm0, map_zero, zero_mul,
      add_zero, zero_sub]
    dsimp only [pN]
    simp only [denote]
  · rw [cRdeSpecialDenominator]
    simp only [if_neg hp, hn, sub_zero, denote, zero_sub]
    dsimp only [pN]
    simp only [denote]

end DensePoly

namespace DensePoly

variable {α : Type*} [CField α] [CDiffField α]

variable {α : Type*} [CField α] [CDiffField α] [CRischField α]

/-- Generic Poly-Risch-DE dispatcher `cPolyRischDE Dt b c n`: solves `Dq + b·q = c` for `q ∈ α[t]`,
`deg(q) ≤ n`, routing by monomial type and `deg(b)`: `b = 0` ⇒ pure integration (`CPoly.antiderivative`, with
the `deg(c)+1 ≤ n` check); `deg(b) > max(0, δ−1)` ⇒ non-cancellation (`cPolyRischDENoCancel`);
`δ = 0, deg(b) = 0` ⇒ primitive cancellation (`cPolyRischDECancelPrim`); `δ = 1, deg(b) = 0` ⇒
hyperexponential cancellation (`cPolyRischDECancelExp`); else (`δ ≥ 2`) ⇒ non-cancellation.
`[CRischField α]`-generic. -/
def cPolyRischDE (Dt : DensePoly α) (b c : DensePoly α) (n : ℤ) : Option (DensePoly α) :=
  let δ : ℤ := (cdeg Dt : ℤ)
  let db : ℤ := (cdeg b : ℤ)
  if cisZero b then
    if cisZero c then some []
    else if (cdeg c : ℤ) + 1 > n then none
    else some (CPoly.antiderivative c)
  else if db > max 0 (δ - 1) then
    cPolyRischDENoCancel Dt b c n
  else if δ = 0 ∧ db = 0 then
    cPolyRischDECancelPrim Dt b c n
  else if δ = 1 ∧ db = 0 then
    cPolyRischDECancelExp Dt b c n
  else
    cPolyRischDENoCancel Dt b c n

end DensePoly

/-! ## The generic Risch-DE oracle `cRischDE`

For `f = fnum/fden`, `g = gnum/gden ∈ α(t)`, `cRischDE` returns `some (ynum, yden)` with `y = ynum/yden`
solving `Dy + f·y = g`, or `none`. The base solve inside the cancellation cases is `crischDESolve`, so a
level-`n+1` call recurses into the level-`n` `crischDESolve`. -/

namespace DensePoly

variable {α : Type*} [CField α] [CDiffField α] [CPolyGcd DensePoly α]
  [CPolySplitFactor DensePoly α] [CRischField α]

/-- The generic Risch differential equation solver `cRischDE Dt fnum fden gnum gden`. For
`f = fnum/fden`, `g = gnum/gden ∈ α(t)` and the monomial derivation `D = CPolyEngine.monomialDeriv Dt`, returns
`some (ynum, yden)` with `y = ynum/yden ∈ α(t)` solving `Dy + f·y = g`, or `none`. Stages: normal denominator
(`cRdeNormalDenominator`) → special denominator (`cRdeSpecialDenominator`) → degree bound
(`cRdeBoundDegree`) → SPDE (`cSPDE`) → PolyRischDE dispatch (`cPolyRischDE`), with the polynomial
unknown `Q = α'·v + β` reassembled to `y = Q·h₁ / h₀`. The cancellation cases recurse into
`CRischField.crischDESolve` over `α`; gcd and differential splitting are selected through
`CPolyGcd` and `CPolySplitFactor`.
`f` is assumed weakly normalized. -/
def cRischDE (Dt : DensePoly α) (fnum fden gnum gden : DensePoly α) :
    Option (DensePoly α × DensePoly α) :=
  match cRdeNormalDenominator Dt fnum fden gnum gden with
  | none => none
  | some (a0, b0, c0, h0) =>
    let (a, b, c, h1) := cRdeSpecialDenominator Dt a0 b0 c0
    let N := cRdeBoundDegree Dt a b c
    match cSPDE Dt a b c (N : ℤ) with
    | none => none
    | some (bbar, cbar, _m, α', β) =>
      match cPolyRischDE Dt bbar cbar _m with
      | none => none
      | some v =>
        let Q := cadd (cmul α' v) β
        some (cmul Q h1, h0)

/-- `cRischDE = some _` structurally forces the stage `some`-results: a successful §6 RDE run exposes
the normal-denominator output, the SPDE output on the special-cleared coefficients, the Poly-Risch-DE
dispatcher output, and the final numerator/denominator reassembly. -/
theorem cRischDEG_some_imp_stages (Dt : DensePoly α) (fnum fden gnum gden ynum yden : DensePoly α)
    (hsucc : cRischDE Dt fnum fden gnum gden = some (ynum, yden)) :
    ∃ (a0 b0 c0 h0 bbar cbar : DensePoly α) (m : ℤ) (α' β v : DensePoly α),
      cRdeNormalDenominator Dt fnum fden gnum gden = some (a0, b0, c0, h0)
      ∧ cSPDE Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1
          (cRdeBoundDegree Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
            (cRdeSpecialDenominator Dt a0 b0 c0).2.1
            (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α', β)
      ∧ cPolyRischDE Dt bbar cbar m = some v
      ∧ ynum = cmul (cadd (cmul α' v) β) (cRdeSpecialDenominator Dt a0 b0 c0).2.2.2
      ∧ yden = h0 := by
  rw [cRischDE] at hsucc
  rcases hnorm : cRdeNormalDenominator Dt fnum fden gnum gden with _ | ⟨a0, b0, c0, h0⟩ <;>
    rw [hnorm] at hsucc
  · exact absurd hsucc (by simp)
  · simp only at hsucc
    rcases hspecial : cRdeSpecialDenominator Dt a0 b0 c0 with ⟨a, b, c, h1⟩
    rw [hspecial] at hsucc
    rcases hspde : cSPDE Dt a b c (cRdeBoundDegree Dt a b c : ℤ) with _ | ⟨bbar, cbar, m, α', β⟩ <;>
      rw [hspde] at hsucc
    · exact absurd hsucc (by simp)
    · simp only at hsucc
      rcases hpoly : cPolyRischDE Dt bbar cbar m with _ | v <;> rw [hpoly] at hsucc
      · exact absurd hsucc (by simp)
      · rw [Option.some.injEq, Prod.mk.injEq] at hsucc
        obtain ⟨hynum, hyden⟩ := hsucc
        refine ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, rfl, ?_, hpoly, ?_, hyden.symm⟩
        · rw [hspecial]
          exact hspde
        · rw [hspecial]
          exact hynum.symm

end DensePoly

namespace CFrac

/-- Test whether a represented fraction denominator equals its selected differential normal part. -/
def denomNormalGate {F : (α : Type u) → [CField α] → Type u} {P : Type u → Type u}
    [CPoly P] [CPolyEngine P] [CPolyEuclidean P] [CFrac F P]
    {β : Type u} [CField β] [CPolyGcd P β] [CDiffField β] [CPolySplitFactor P β]
    (a : F β) : Bool :=
  CPolyEngine.cisZero (CPolyEngine.sub
    (CPoly.splitFactor (CPoly.one : P β) (CFrac.den a)).1 (CFrac.den a))

/-- Sparse polynomial denominators execute through the generic normality gate. -/
example :
    let den : CPoly.SparsePoly ℚ := CPoly.SparsePoly.ofList [(0, 1), (1, 1)]
    let a : SparseFrac ℚ := CFrac.ofFraction CPoly.one den (by cfrac_nonzero)
    CFrac.denomNormalGate a = true := by
  ccompute

end CFrac

/-! The validations of `cRischDE` at `DenseFrac ℚ` live in `Tower/RischDEInstance.lean`, which supplies
the `CRischField (DenseFrac ℚ)` instance. -/

end DeepWiki.SymbolicIntegration
