import DeepWiki.SymbolicIntegration.Computable.Tower.WellFounded
import DeepWiki.SymbolicIntegration.Computable.Tower.RischDE

/-! # Well-founded generic tower Risch-DE oracle `cRischDEGWf`

The generic Risch-DE pipeline, by well-founded recursion: the recursive bottoms
`cPolyRischDECancelPrimGWf` (primitive cancellation), `cPolyRischDECancelExpGWf` (hyperexponential
cancellation), and `cValuationGWf` (the `p`-adic valuation), plus a flat composition over them for the
weak normalizer, normal/special denominators, degree bound, and the headline `cRischDEGWf`. `[CField α]`-only
on the runtime fragment (plus `[CDiffField α]`/`[CFracGcdCoreWf α]`/`[CRischField α]` where needed), so it
`native_decide`s over the noncomputable tower. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

/-! ## The three remaining recursive bottoms

`cPolyRischDECancelPrimGWf` / `cPolyRischDECancelExpGWf` (degree-by-degree own-loops on
`(cnormG c).length`, carrying `[CRischField α]`) and `cValuationGWf` (trial-division own-loop on
`(cnormG x).length`), each well-founded with a structural runtime guard. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CRischField α]

/-- Generic primitive cancellation Poly-Risch-DE `cPolyRischDECancelPrimGWf Dt b c n`: given the primitive
monomial derivation `D` (`Dt ∈ α`), scalar `b ∈ α*` (`b₀ = lc(b)`) and `c ∈ α[t]` with degree bound `n : ℤ`,
solves `Dq + b·q = c` degree-by-degree, recursing at degree `m = deg(c)` into the base RDE
`CRischField.crischDESolve b₀ (lc c)`, leading monomial `s·tᵐ`, remainder `c' = c − b·(s·tᵐ) − D(s·tᵐ)`.
Returns `none` or `some q`. Well-founded on `(cnormG c).length`. `[CRischField α]`-generic. -/
def cPolyRischDECancelPrimGWf (Dt : CPolyG α) (b c : CPolyG α) (n : ℤ) :
    Option (CPolyG α) :=
  let b0 : α := cleadG b
  if cisZeroG c then some []
  else if n < (cdegG c : ℤ) then none
  else
    let m : ℕ := cdegG c
    match CRischField.crischDESolve b0 (cleadG c) with
    | none => none
    | some s =>
      let stm : CPolyG α := cshiftG m [s]               -- `s·tᵐ`
      let c' := csubG (csubG c (cmulG b stm)) (cmonomialDeriv Dt stm)
      if (cnormG c' : List α).length < (cnormG c : List α).length then
        match cPolyRischDECancelPrimGWf Dt b c' ((m : ℤ) - 1) with
        | none => none
        | some q => some (caddG stm q)
      else none   -- unreachable on a real run (the leading monomial cancels, degree drops)
termination_by (cnormG c).length
decreasing_by assumption

/-- Generic hyperexponential cancellation Poly-Risch-DE `cPolyRischDECancelExpGWf Dt b c n`: given the
hyperexponential monomial derivation `D` (`η = Dt/t ∈ α`, `δ = 1`), scalar `b ∈ α*` (`b₀ = lc(b)`) and
`c ∈ α[t]` with degree bound `n : ℤ`, solves `Dq + b·q = c` degree-by-degree, recursing at degree
`m = deg(c)` into the base RDE `crischDESolve (b₀ + m·η) (lc c)` (`η = cExpEtaG Dt`), leading monomial
`s·tᵐ`, remainder `c' = c − b·(s·tᵐ) − D(s·tᵐ)`. Returns `none` or `some q`. Well-founded on
`(cnormG c).length`. `[CRischField α]`-generic. -/
def cPolyRischDECancelExpGWf (Dt : CPolyG α) (b c : CPolyG α) (n : ℤ) :
    Option (CPolyG α) :=
  let b0 : α := cleadG b
  let η : α := cExpEtaG Dt
  if cisZeroG c then some []
  else if n < (cdegG c : ℤ) then none
  else
    let m : ℕ := cdegG c
    -- eq. 6.24 base RDE `Ds + (b₀ + m·η)·s = lc(c)` over `α`.
    let coeff : α := CField.add b0 (CField.mul (cnatCastG m) η)
    match CRischField.crischDESolve coeff (cleadG c) with
    | none => none
    | some s =>
      let stm : CPolyG α := cshiftG m [s]               -- `s·tᵐ`
      let c' := csubG (csubG c (cmulG b stm)) (cmonomialDeriv Dt stm)
      if (cnormG c' : List α).length < (cnormG c : List α).length then
        match cPolyRischDECancelExpGWf Dt b c' ((m : ℤ) - 1) with
        | none => none
        | some q => some (caddG stm q)
      else none   -- unreachable on a real run (the leading monomial cancels, degree drops)
termination_by (cnormG c).length
decreasing_by assumption

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α]

/-- Generic `p`-adic valuation `cValuationGWf p x = ν_p(x)`: the multiplicity of the monic irreducible `p`
dividing `x` (largest `k` with `pᵏ ∣ x`), by trial division. Stops at the zero polynomial, a constant/unit
`p` (`cdegG p = 0`), or a non-dividing step, else recurses on `x/p` (`cdivWf`) and adds one. Well-founded on
`(cnormG x).length`. `[CField α]`-generic. -/
def cValuationGWf (p x : CPolyG α) : ℕ :=
  if cisZeroG x then 0
  else if cdegG p = 0 then 0
  else if cdvdGWf p x then
    let xq := cdivWf x p
    if (cnormG xq : List α).length < (cnormG x : List α).length then
      1 + cValuationGWf p xq
    else 0   -- unreachable on a real run (non-constant `p ∣ x` drops the degree)
  else 0
termination_by (cnormG x).length
decreasing_by assumption

variable [CFieldSpec α]

/-- `cValuationGWf` divides: `toPolyG p ^ cValuationGWf p x ∣ toPolyG x`. Each recursive step peels one
exact `p` factor using the exact-division theorem; terminal branches return the unit power. -/
theorem toPolyG_pow_cValuationGWf_dvd (p x : CPolyG α) :
    toPolyG p ^ cValuationGWf p x ∣ toPolyG x := by
  induction x using cValuationGWf.induct p with
  | case1 x hx =>
      rw [cValuationGWf.eq_def, if_pos hx, pow_zero]
      exact one_dvd _
  | case2 x hx hp =>
      rw [cValuationGWf.eq_def, if_neg hx, if_pos hp, pow_zero]
      exact one_dvd _
  | case3 x hx hp hdvd _xq hguard ih =>
      rw [cValuationGWf.eq_def, if_neg hx, if_neg hp, if_pos hdvd, if_pos hguard]
      have hpne : cnormG p ≠ [] := fun hpe => hp (by rw [cdegG, hpe]; rfl)
      have hpx : toPolyG p ∣ toPolyG x := dvd_of_cdvdGWf p x hpne hdvd
      have hid : toPolyG x = toPolyG (cdivWf x p) * toPolyG p :=
        (toPolyG_cdivWf_exact x p hpne hpx).symm
      rw [add_comm, pow_add, pow_one, hid]
      exact mul_dvd_mul ih dvd_rfl
  | case4 x hx hp hdvd _xq hguard =>
      rw [cValuationGWf.eq_def, if_neg hx, if_neg hp, if_pos hdvd, if_neg hguard, pow_zero]
      exact one_dvd _
  | case5 x hx hp hdvd =>
      rw [cValuationGWf.eq_def, if_neg hx, if_neg hp, if_neg hdvd, pow_zero]
      exact one_dvd _

/-- `cValuationGWf` is sharp: for nonconstant `p` and nonzero `x`, one more `p` factor than
`cValuationGWf p x` does not divide `x`. Uses `cdvdGWf`'s false-case converse at the terminal
non-dividing branch. -/
theorem cValuationGWf_sharp (p x : CPolyG α)
    (hp : cdegG p ≠ 0) (hx0 : toPolyG x ≠ 0) :
    ¬ toPolyG p ^ (cValuationGWf p x + 1) ∣ toPolyG x := by
  have hpne : cnormG p ≠ [] := fun hpe => hp (by rw [cdegG, hpe]; rfl)
  have hp0 : toPolyG p ≠ 0 := fun h => hpne (by rw [cnormG_eq_nil_iff]; exact h)
  have hpdeg : 0 < (toPolyG p).natDegree := by
    rw [← cdegG_eq_natDegree]
    omega
  revert hx0
  induction x using cValuationGWf.induct p with
  | case1 x hx =>
      intro hx0
      exact False.elim (hx0 ((cisZeroG_iff x).mp hx))
  | case2 x hx hdeg =>
      intro _hx0
      exact False.elim (hp hdeg)
  | case3 x hx hdeg hdvd _xq hguard ih =>
      intro hx0
      rw [cValuationGWf.eq_def, if_neg hx, if_neg hdeg, if_pos hdvd, if_pos hguard]
      have hpx : toPolyG p ∣ toPolyG x := dvd_of_cdvdGWf p x hpne hdvd
      have hid : toPolyG x = toPolyG (cdivWf x p) * toPolyG p :=
        (toPolyG_cdivWf_exact x p hpne hpx).symm
      have hq0 : toPolyG (cdivWf x p) ≠ 0 := by
        intro h
        apply hx0
        rw [hid, h, zero_mul]
      have hihq := ih hq0
      intro hcontra
      apply hihq
      rw [hid, show 1 + cValuationGWf p (cdivWf x p) + 1 =
          (cValuationGWf p (cdivWf x p) + 1) + 1 by ring, pow_succ] at hcontra
      exact (mul_dvd_mul_iff_right hp0).mp hcontra
  | case4 x hx hdeg hdvd _xq hguard =>
      intro hx0
      have hpx : toPolyG p ∣ toPolyG x := dvd_of_cdvdGWf p x hpne hdvd
      have hid : toPolyG x = toPolyG (cdivWf x p) * toPolyG p :=
        (toPolyG_cdivWf_exact x p hpne hpx).symm
      have hq0 : toPolyG (cdivWf x p) ≠ 0 := by
        intro h
        apply hx0
        rw [hid, h, zero_mul]
      have hxne : cnormG x ≠ [] := fun he => hx0 (by rw [← toPolyG_cnormG, he, toPolyG_nil])
      have hqne : cnormG (cdivWf x p) ≠ [] := fun he =>
        hq0 (by rw [cnormG_eq_nil_iff] at he; exact he)
      have hdegdrop : (toPolyG (cdivWf x p)).natDegree < (toPolyG x).natDegree := by
        rw [hid, Polynomial.natDegree_mul hq0 hp0]
        omega
      have hlen : (cnormG (cdivWf x p) : List α).length < (cnormG x : List α).length := by
        rw [length_cnormG_of_ne _ hqne, length_cnormG_of_ne _ hxne]
        omega
      exact False.elim (hguard hlen)
  | case5 x hx hdeg hdvd =>
      intro _hx0
      have hfalse : cdvdGWf p x = false := Bool.eq_false_iff.mpr hdvd
      rw [cValuationGWf.eq_def, if_neg hx, if_neg hdeg, if_neg hdvd, zero_add, pow_one]
      exact not_dvd_of_cdvdGWf_false p x hpne hfalse

end CPolyG

/-! ## The flat-composition §6 pipeline

Everything past the five recursive bottoms is a flat composition over the leaves above plus the generic
`cdivWf`, `cdivmodWf`, `cdiophantineGWf`, `cdvdGWf`, `cgcdWf`, and the §5.6
`cResidueResultantTowerGWf`/`cinterpolateG`/`cHornerG`. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α]

/-- Generic weak normalizer `cWeakNormalizerGWf Dt fnum fden = q ∈ α[t]`: split the denominator into its
normal part `dₙ` (`cSplitFactorFastGWf`), form `d₁ = (dₙ/g)/gcd(dₙ/g, g)` with `g = gcd(dₙ, dₙ')`, solve the
residue numerator `a` via `cdiophantineGWf`, build the residue resultant `r = res_t(a − z·Dd₁, d₁)`
(`cResidueResultantTowerGWf`), and return `∏ᵢ gcd(a − nᵢ·Dd₁, d₁)^{nᵢ}` over the positive integer roots `nᵢ`
of `r`. For an already-weakly-normalized `f`, `q = 1`. `[CField α] [CDiffField α] [CFracGcdCoreWf α]`-generic. -/
def cWeakNormalizerGWf (Dt : CPolyG α) (fnum fden : CPolyG α) (boundRoots : ℕ := 16) : CPolyG α :=
  let dn := (cSplitFactorFastGWf Dt fden).1
  let g := CFracGcdCoreWf.cgcdFFCoreWf dn (cderivG dn)
  let dstar := cdivWf dn g
  let d1 := cdivWf dstar (CFracGcdCoreWf.cgcdFFCoreWf dstar g)
  let fdenOverD1 := cdivWf fden d1
  let a := (cdiophantineGWf fdenOverD1 d1 fnum).1
  let Dd1 := cmonomialDeriv Dt d1
  let r := cResidueResultantTowerGWf Dt a d1
  let roots := cPosIntRootsG r boundRoots
  roots.foldl (fun (acc : CPolyG α) (n : ℕ) =>
    let gi := CFracGcdCoreWf.cgcdFFCoreWf (csubG a (cscaleG (cnatCastG n) Dd1)) d1
    cmulG acc (cpowG gi n)) [CField.one]

/-- Generic normal-denominator reduction `cRdeNormalDenominatorGWf Dt fnum fden gnum gden` for weakly
normalized `f = fnum/fden`, `g = gnum/gden`. Returns `none` or `some (a, b, c, h)` reducing `Dy + fy = g` to
`a·Dq + b·q = c` with `q = y·h`. Split the denominators into normal parts `dₙ, eₙ`; `p = gcd(dₙ, eₙ)`,
`h = gcd(eₙ, eₙ')/gcd(p, p')`; if `eₙ ∤ dₙh²` then `none`; else `a = dₙh`, `b = (dₙh·fnum − dₙ·Dh·fden)/fden`,
`c = dₙh²·gnum/gden`. -/
def cRdeNormalDenominatorGWf (Dt : CPolyG α) (fnum fden gnum gden : CPolyG α) :
    Option (CPolyG α × CPolyG α × CPolyG α × CPolyG α) :=
  let dn := (cSplitFactorFastGWf Dt fden).1
  let en := (cSplitFactorFastGWf Dt gden).1
  let p := CFracGcdCoreWf.cgcdFFCoreWf dn en
  let h := cdivWf (CFracGcdCoreWf.cgcdFFCoreWf en (cderivG en))
    (CFracGcdCoreWf.cgcdFFCoreWf p (cderivG p))
  let dnh2 := cmulG (cmulG dn h) h
  if cdvdGWf en dnh2 then
    let a := cmulG dn h
    let Dh := cmonomialDeriv Dt h
    let b := cdivWf (csubG (cmulG a fnum) (cmulG (cmulG dn Dh) fden)) fden
    let c := cdivWf (cmulG dnh2 gnum) gden
    some (a, b, c, h)
  else none

/-- Generic special monic irreducible of the monomial `cSpecialPolyGWf Dt = p`: the monic special part of
the monomial derivative `Dt` (`t²+1` hypertangent, `t` hyperexponential, `1` primitive) via the
splitting-factorization `cSplitFactorFastGWf`. -/
def cSpecialPolyGWf (Dt : CPolyG α) : CPolyG α :=
  cmonicG (cSplitFactorFastGWf Dt Dt).2

/-- Generic special-denominator reduction `cRdeSpecialDenominatorGWf Dt a b c`. Given `a·Dq + b·q = c` with
`a` free of special factors, returns the special-cleared quadruplet `(ā, b̄, c̄, h)` (`h = p^{−n}`) so
`r = q·h ∈ α[t]` solves `ā·Dr + b̄·r = c̄`. Steps: `p ← cSpecialPolyGWf Dt` (constant ⇒ trivial);
`n_b = ν_p(b)`, `n_c = ν_p(c)`, `n = min(0, n_c − min(0, n_b))`, `N = max(0, −n_b, n − n_c)`; return
`(a·pᴺ, (b + n·a·Dp/p)·pᴺ, c·p^{N−n}, p^{−n})`. -/
def cRdeSpecialDenominatorGWf (Dt : CPolyG α) (a b c : CPolyG α) :
    CPolyG α × CPolyG α × CPolyG α × CPolyG α :=
  let p := cSpecialPolyGWf Dt
  if cdegG p = 0 then (a, b, c, [CField.one])
  else
    let nb : ℤ := (cValuationGWf p b : ℤ)
    let nc : ℤ := (cValuationGWf p c : ℤ)
    let n : ℤ := min 0 (nc - min 0 nb)
    let N : ℤ := max (max 0 (-nb)) (n - nc)
    let Nnat : ℕ := N.toNat
    let negn : ℕ := (-n).toNat
    let Nminusn : ℕ := (N - n).toNat
    let pN := cpowG p Nnat
    let abar := cmulG a pN
    let DpOverp := cdivWf (cmonomialDeriv Dt p) p
    let bterm := cscaleG (CField.neg (cnatCastG negn)) (cmulG a DpOverp)
    let bbar := cmulG (caddG b bterm) pN
    let cbar := cmulG c (cpowG p Nminusn)
    let h := cpowG p negn
    (abar, bbar, cbar, h)

/-- The special-denominator stage is the identity in the primitive regime: when the special polynomial is
constant, `cRdeSpecialDenominatorGWf Dt a b c = (a, b, c, [1])`. -/
theorem cRdeSpecialDenominatorGWf_primitive_eq (Dt : CPolyG α) (a b c : CPolyG α)
    (hp : cdegG (cSpecialPolyGWf Dt) = 0) :
    cRdeSpecialDenominatorGWf Dt a b c = (a, b, c, [CField.one]) := by
  rw [cRdeSpecialDenominatorGWf]
  simp only [hp, if_pos]

/-- Special-denominator no-clear predicate: the special-denominator shift
`n = min(0, ν_p(c) - min(0, ν_p(b)))` is zero, equivalently the reconstruction power `p^{-n}` is
trivial. -/
def CSpecialDenomNoClearGWf (Dt : CPolyG α) (b c : CPolyG α) : Prop :=
  let p := cSpecialPolyGWf Dt
  min (0 : ℤ) ((cValuationGWf p c : ℤ) - min 0 (cValuationGWf p b : ℤ)) = 0

/-- The special-denominator no-clear predicate holds for all inputs: `cValuationGWf` is natural-valued,
so both valuations are nonnegative after casting to `ℤ`. -/
theorem cSpecialDenomNoClearGWf_always (Dt : CPolyG α) (b c : CPolyG α) :
    CSpecialDenomNoClearGWf Dt b c := by
  rw [CSpecialDenomNoClearGWf]
  have hnb : (0 : ℤ) ≤ (cValuationGWf (cSpecialPolyGWf Dt) b : ℤ) := Int.natCast_nonneg _
  have hnc : (0 : ℤ) ≤ (cValuationGWf (cSpecialPolyGWf Dt) c : ℤ) := Int.natCast_nonneg _
  omega

/-- The special-denominator reconstruction power is trivial under no-clear: if
`CSpecialDenomNoClearGWf Dt b c` and the special polynomial is nonconstant, then
`cRdeSpecialDenominatorGWf` returns `h = [1]`. -/
theorem cRdeSpecialDenominatorGWf_h1_eq_one_of_noClear (Dt : CPolyG α) (a b c : CPolyG α)
    (hp : cdegG (cSpecialPolyGWf Dt) ≠ 0) (hn : CSpecialDenomNoClearGWf Dt b c) :
    (cRdeSpecialDenominatorGWf Dt a b c).2.2.2 = [CField.one] := by
  rw [cRdeSpecialDenominatorGWf]
  simp only [if_neg hp]
  rw [CSpecialDenomNoClearGWf] at hn
  show cpowG (cSpecialPolyGWf Dt) (-(min 0
    ((cValuationGWf (cSpecialPolyGWf Dt) c : ℤ)
      - min 0 (cValuationGWf (cSpecialPolyGWf Dt) b : ℤ)))).toNat = [CField.one]
  rw [hn]
  rfl

/-- The special-denominator reconstruction power is always trivial in the nonconstant special-polynomial
regime. -/
theorem cRdeSpecialDenominatorGWf_h1_eq_one_always (Dt : CPolyG α) (a b c : CPolyG α)
    (hp : cdegG (cSpecialPolyGWf Dt) ≠ 0) :
    (cRdeSpecialDenominatorGWf Dt a b c).2.2.2 = [CField.one] :=
  cRdeSpecialDenominatorGWf_h1_eq_one_of_noClear Dt a b c hp
    (cSpecialDenomNoClearGWf_always Dt b c)

/-- The special-denominator coefficients factor as `(·)·pᴺ` in the no-clear regime: under
`CSpecialDenomNoClearGWf`, the cleared coefficients are `a·pᴺ`, `b·pᴺ`, and `c·pᴺ` through `toPolyG`. -/
theorem toPolyG_cRdeSpecialDenominatorGWf_coeffs_of_noClear [CFieldSpec α] (Dt : CPolyG α)
    (a b c : CPolyG α) (hp : cdegG (cSpecialPolyGWf Dt) ≠ 0)
    (hn : CSpecialDenomNoClearGWf Dt b c) :
    let pN : CPolyG α := cpowG (cSpecialPolyGWf Dt)
      (max (max 0 (-(cValuationGWf (cSpecialPolyGWf Dt) b : ℤ)))
        (-(cValuationGWf (cSpecialPolyGWf Dt) c : ℤ))).toNat
    toPolyG (cRdeSpecialDenominatorGWf Dt a b c).1 = toPolyG a * toPolyG pN
    ∧ toPolyG (cRdeSpecialDenominatorGWf Dt a b c).2.1 = toPolyG b * toPolyG pN
    ∧ toPolyG (cRdeSpecialDenominatorGWf Dt a b c).2.2.1 = toPolyG c * toPolyG pN := by
  intro pN
  rw [CSpecialDenomNoClearGWf] at hn
  have hbterm0 : CFieldSpec.toK (CField.neg (CField.zero : α)) = 0 := by
    rw [CFieldSpec.toK_neg, CFieldSpec.toK_zero, neg_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [cRdeSpecialDenominatorGWf]
    simp only [if_neg hp, hn, denote, zero_sub]
    dsimp only [pN]
    simp only [denote]
  · rw [cRdeSpecialDenominatorGWf]
    simp only [if_neg hp, hn, neg_zero, Int.toNat_zero, cnatCastG, denote, hbterm0, map_zero, zero_mul,
      add_zero, zero_sub]
    dsimp only [pN]
    simp only [denote]
  · rw [cRdeSpecialDenominatorGWf]
    simp only [if_neg hp, hn, sub_zero, denote, zero_sub]
    dsimp only [pN]
    simp only [denote]

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

/-- Generic polynomial antiderivative `cIntegratePolyGWf c = q` with `Dq = c` and `q(0) = 0`, for the
canonical primitive monomial (`Dt = 1`) and constant coefficients: termwise
`∫ Σ cᵢtⁱ = Σ (cᵢ/(i+1)) t^{i+1}` (`cᵢ/(i+1) = CField.div cᵢ (cnatCastG (i+1))`). -/
def cIntegratePolyGWf (c : CPolyG α) : CPolyG α :=
  CField.zero :: ((c : List α).zipIdx.map (fun (a, i) => CField.div a (cnatCastG (i + 1))))

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CRischField α]

/-- Generic Poly-Risch-DE dispatcher `cPolyRischDEGWf Dt b c n`: solves `Dq + b·q = c` for `q ∈ α[t]`,
`deg(q) ≤ n`, routing by monomial type and `deg(b)`: `b = 0` ⇒ pure integration (`cIntegratePolyGWf`, with
the `deg(c)+1 ≤ n` check); `deg(b) > max(0, δ−1)` ⇒ non-cancellation (`cPolyRischDENoCancelGWf`);
`δ = 0, deg(b) = 0` ⇒ primitive cancellation (`cPolyRischDECancelPrimGWf`); `δ = 1, deg(b) = 0` ⇒
hyperexponential cancellation (`cPolyRischDECancelExpGWf`); else (`δ ≥ 2`) ⇒ non-cancellation.
`[CRischField α]`-generic. -/
def cPolyRischDEGWf (Dt : CPolyG α) (b c : CPolyG α) (n : ℤ) : Option (CPolyG α) :=
  let δ : ℤ := (cdegG Dt : ℤ)
  let db : ℤ := (cdegG b : ℤ)
  if cisZeroG b then
    if cisZeroG c then some []
    else if (cdegG c : ℤ) + 1 > n then none
    else some (cIntegratePolyGWf c)
  else if db > max 0 (δ - 1) then
    cPolyRischDENoCancelGWf Dt b c n
  else if δ = 0 ∧ db = 0 then
    cPolyRischDECancelPrimGWf Dt b c n
  else if δ = 1 ∧ db = 0 then
    cPolyRischDECancelExpGWf Dt b c n
  else
    cPolyRischDENoCancelGWf Dt b c n

end CPolyG

/-! ## The generic Risch-DE oracle `cRischDEGWf`

For `f = fnum/fden`, `g = gnum/gden ∈ α(t)`, `cRischDEGWf` returns `some (ynum, yden)` with `y = ynum/yden`
solving `Dy + f·y = g`, or `none`. The base solve inside the cancellation cases is `crischDESolve`, so a
level-`n+1` call recurses into the level-`n` `crischDESolve`. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α] [CRischField α]

/-- The generic Risch differential equation solver `cRischDEGWf Dt fnum fden gnum gden`. For
`f = fnum/fden`, `g = gnum/gden ∈ α(t)` and the monomial derivation `D = cmonomialDeriv Dt`, returns
`some (ynum, yden)` with `y = ynum/yden ∈ α(t)` solving `Dy + f·y = g`, or `none`. Stages: normal denominator
(`cRdeNormalDenominatorGWf`) → special denominator (`cRdeSpecialDenominatorGWf`) → degree bound
(`cRdeBoundDegreeG`) → SPDE (`cSPDEGWf`) → PolyRischDE dispatch (`cPolyRischDEGWf`), with the polynomial
unknown `Q = α'·v + β` reassembled to `y = Q·h₁ / h₀`. The cancellation cases recurse into
`CRischField.crischDESolve` over `α`. `[CField α] [CDiffField α] [CFracGcdCoreWf α] [CRischField α]`-generic;
`f` is assumed weakly normalized. -/
def cRischDEGWf (Dt : CPolyG α) (fnum fden gnum gden : CPolyG α) :
    Option (CPolyG α × CPolyG α) :=
  match cRdeNormalDenominatorGWf Dt fnum fden gnum gden with
  | none => none
  | some (a0, b0, c0, h0) =>
    let (a, b, c, h1) := cRdeSpecialDenominatorGWf Dt a0 b0 c0
    let N := cRdeBoundDegreeG Dt a b c
    match cSPDEGWf Dt a b c (N : ℤ) with
    | none => none
    | some (bbar, cbar, _m, α', β) =>
      match cPolyRischDEGWf Dt bbar cbar _m with
      | none => none
      | some v =>
        let Q := caddG (cmulG α' v) β
        some (cmulG Q h1, h0)

/-- `cRischDEGWf = some _` structurally forces the stage `some`-results: a successful §6 RDE run exposes
the normal-denominator output, the SPDE output on the special-cleared coefficients, the Poly-Risch-DE
dispatcher output, and the final numerator/denominator reassembly. -/
theorem cRischDEGWf_some_imp_stages (Dt : CPolyG α) (fnum fden gnum gden ynum yden : CPolyG α)
    (hsucc : cRischDEGWf Dt fnum fden gnum gden = some (ynum, yden)) :
    ∃ (a0 b0 c0 h0 bbar cbar : CPolyG α) (m : ℤ) (α' β v : CPolyG α),
      cRdeNormalDenominatorGWf Dt fnum fden gnum gden = some (a0, b0, c0, h0)
      ∧ cSPDEGWf Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1
          (cRdeBoundDegreeG Dt (cRdeSpecialDenominatorGWf Dt a0 b0 c0).1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.1
            (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.1 : ℤ)
        = some (bbar, cbar, m, α', β)
      ∧ cPolyRischDEGWf Dt bbar cbar m = some v
      ∧ ynum = cmulG (caddG (cmulG α' v) β) (cRdeSpecialDenominatorGWf Dt a0 b0 c0).2.2.2
      ∧ yden = h0 := by
  rw [cRischDEGWf] at hsucc
  rcases hnorm : cRdeNormalDenominatorGWf Dt fnum fden gnum gden with _ | ⟨a0, b0, c0, h0⟩ <;>
    rw [hnorm] at hsucc
  · exact absurd hsucc (by simp)
  · simp only at hsucc
    rcases hspecial : cRdeSpecialDenominatorGWf Dt a0 b0 c0 with ⟨a, b, c, h1⟩
    rw [hspecial] at hsucc
    rcases hspde : cSPDEGWf Dt a b c (cRdeBoundDegreeG Dt a b c : ℤ) with _ | ⟨bbar, cbar, m, α', β⟩ <;>
      rw [hspde] at hsucc
    · exact absurd hsucc (by simp)
    · simp only at hsucc
      rcases hpoly : cPolyRischDEGWf Dt bbar cbar m with _ | v <;> rw [hpoly] at hsucc
      · exact absurd hsucc (by simp)
      · rw [Option.some.injEq, Prod.mk.injEq] at hsucc
        obtain ⟨hynum, hyden⟩ := hsucc
        refine ⟨a0, b0, c0, h0, bbar, cbar, m, α', β, v, rfl, ?_, hpoly, ?_, hyden.symm⟩
        · rw [hspecial]
          exact hspde
        · rw [hspecial]
          exact hynum.symm

end CPolyG

section Gate

variable {β : Type*} [CField β] [CDiffField β] [CFracGcdCoreWf β]

/-- The denominator-direct normality gate for tower RDE inputs. -/
def cdenomNormalGateGWf (a : QFunNZG β) : Bool :=
  CPolyG.cisZeroG (CPolyG.csubG
    (CPolyG.cSplitFactorFastGWf ([CField.one] : CPolyG β) a.1.2).1
    a.1.2)

end Gate

/-! The validations of `cRischDEGWf` at `QFunNZG ℚ` live in `Tower/RischDEInstance.lean`, which supplies
the `CRischField (QFunNZG ℚ)` instance. -/

end DeepWiki.SymbolicIntegration
