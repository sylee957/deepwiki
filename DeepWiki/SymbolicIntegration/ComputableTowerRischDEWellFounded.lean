import DeepWiki.SymbolicIntegration.ComputableTowerWellFounded
import DeepWiki.SymbolicIntegration.ComputableTowerRischDE

/-! # Fuel-free (well-founded) GENERIC tower §6 Risch-DE oracle `cRischDEGWf`

The generic §6 RDE pipeline (`ComputableTowerRischDE`) — `cRischDEG` and its stages — is
`[CField α] [CDiffField α] [CFracGcdCore α] [CRischField α]`-generic and gate-clean, but every op carries an
explicit `fuel : ℕ`. This file builds the **fuel-free** companions `…GWf`, completing the generic fuel-free
engine: the reduced-case driver `cIntegrateReducedGWf` (`ComputableTowerWellFounded`) is already fuel-free, and TWO
of the RDE recursive bottoms landed there (`cPolyRischDENoCancelGWf` §6.5, `cSPDEGWf` §6.4). Here we finish
the §6 oracle — the headline `cRischDEGWf`.

The §6 pipeline bottoms out at FIVE fuel-recursive ops; two are done in `ComputableTowerWellFounded`
(`cPolyRischDENoCancelGWf`, `cSPDEGWf`), and the remaining THREE are built here:

* **`cPolyRischDECancelPrimGWf`** — §6.6 primitive cancellation, recursing degree-by-degree into the base
  RDE `CRischField.crischDESolve b₀ (lc c)` (eq. 6.23). The leading monomial `s·tᵐ` cancels `c`'s top, so
  `(cnormG c).length` strictly drops; well-founded recursion on it, structural runtime guard.
* **`cPolyRischDECancelExpGWf`** — §6.6 hyperexponential cancellation, recursing into the eq. 6.24 base RDE
  `crischDESolve (b₀ + m·η) (lc c)` (`η = cExpEtaG Dt`). Same own-loop on `(cnormG c).length`.
* **`cValuationGWf`** — the `ν_p` `p`-adic valuation (used by the special-denominator stage), recursing on
  `(cnormG x).length` by trial division.

The rest is a flat composition over fuel-free leaves: the generic §6.1 weak normalizer, the §6.2
normal/special denominators, the §6.3 degree bound, the §6.4 SPDE, the §6.5/§6.6 dispatcher, and the
headline `cRischDEGWf`. Each substitutes the fuel-free leaves — the generic ones reused verbatim
(`cdivWf`, `cdivmodWf`, `cdiophantineGWf`, `cdvdGWf`, `cgcdWf`) and the new ones (`cgcdFFCoreWf`, the two
done RDE bottoms, and the three above). The public surface is the fuel-free engine; compatibility
scaffolding with the old fueled `…G` pipeline is kept out of this module's API.

Every `…GWf` def is **`[CField α]`-only on the fuel-free fragment** (plus `[CDiffField α]`/`[CFracGcdCoreWf α]`/
`[CRischField α]` where the pipeline needs the derivation / the fraction-free gcd / the base solve) — never
`[CFieldSpec α]`, which would break `native_decide` over the noncomputable tower (the keystone lesson). The
runtime ops carry no fuel. The §6.6 hypertangent cancellation falls back to non-cancellation as in
`cRischDEG` (not handled here). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute

/-! ## Part 1 — the three remaining fuel-recursive bottoms

`cPolyRischDECancelPrimGWf` / `cPolyRischDECancelExpGWf` (degree-by-degree own-loops on `(cnormG c).length`,
carrying `[CRischField α]`) and `cValuationGWf` (trial-division own-loop on `(cnormG x).length`). Each is a
true well-founded recursion with a structural runtime guard (`decreasing_by := assumption`) — the generic
primitive-cancellation, hyperexponential-cancellation, and valuation own-loops. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CRischField α]

/-- **Generic fuel-free primitive cancellation Poly-Risch-DE** (Bronstein §6.6, book p.212)
`cPolyRischDECancelPrimGWf Dt b c n`: the generic, fuel-free companion of `cPolyRischDECancelPrimG`. Given the
primitive monomial derivation `D` (`Dt ∈ α`), `b ∈ α*` (a degree-0 `t`-polynomial, scalar `b₀ = lc(b)`) and
`c ∈ α[t]`, with degree bound `n : ℤ`, solves `Dq + b·q = c` degree-by-degree, recursing at degree
`m = deg(c)` into the base RDE `CRischField.crischDESolve b₀ (lc c)` (eq. 6.23) over `α`, leading monomial
`s·tᵐ`, remainder `c' = c − b·(s·tᵐ) − D(s·tᵐ)` (`D = cmonomialDeriv Dt`). Returns `none` ("no solution of
degree `≤ n`") or `some q`. True well-founded recursion on `(cnormG c).length` — **no fuel at runtime**; the
recursion is taken only under the structural guard `(cnormG c').length < (cnormG c).length` (the leading
monomial cancels `c`'s top), so `decreasing_by` is `assumption`. `[CRischField α]`-generic — runs at any
tower level. -/
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

/-- **Generic fuel-free hyperexponential cancellation Poly-Risch-DE** (Bronstein §6.6, book p.213)
`cPolyRischDECancelExpGWf Dt b c n`: the generic, fuel-free companion of `cPolyRischDECancelExpG`. Given the
hyperexponential monomial derivation `D` (`η = Dt/t ∈ α`, `δ = 1`), `b ∈ α*` (scalar `b₀ = lc(b)`) and
`c ∈ α[t]`, with degree bound `n : ℤ`, solves `Dq + b·q = c` degree-by-degree, recursing at degree
`m = deg(c)` into the eq. 6.24 base RDE `crischDESolve (b₀ + m·η) (lc c)` over `α` (the `m·η` shift makes the
coefficient genuinely non-constant, `η = cExpEtaG Dt`), leading monomial `s·tᵐ`, remainder
`c' = c − b·(s·tᵐ) − D(s·tᵐ)`. Returns `none` or `some q`. True well-founded recursion on `(cnormG c).length`
— **no fuel at runtime**; the structural guard `(cnormG c').length < (cnormG c).length` is `decreasing_by :=
assumption`. `[CRischField α]`-generic — runs at any tower level. -/
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

/-- **Generic fuel-free `p`-adic valuation** `cValuationGWf p x = ν_p(x)`: the generic, fuel-free companion of
`cValuationG`, the multiplicity of the monic irreducible `p` dividing `x` (largest `k` with `pᵏ ∣ x`), by
trial division. Stops at the zero polynomial, a constant/unit `p` (`cdegG p = 0`), or a non-dividing step,
else recurses on `x/p` (the **fuel-free** `cdivWf`) and adds one. True well-founded recursion on
`(cnormG x).length` — **no fuel at runtime**; the recursion is taken only under the structural guard
`(cnormG (x/p)).length < (cnormG x).length`, so `decreasing_by` is `assumption`. The exact division `p ∣ x`
with non-constant `p` drops the `t`-degree on a real run, so the guard never fails and it agrees with
`cValuationG`. `[CField α]`-generic — runs at any tower level. -/
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

/-- **`cValuationGWf` divides**: `toPolyG p ^ cValuationGWf p x ∣ toPolyG x`. Each recursive Wf
step peels one exact `p` factor using the fuel-free exact-division theorem; terminal branches return the
unit power. -/
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

/-- **`cValuationGWf` is sharp**: for nonconstant `p` and nonzero `x`, one more `p` factor than
`cValuationGWf p x` does not divide `x`. The proof is Wf-native and uses `cdvdGWf`'s false-case
converse at the terminal non-dividing branch. -/
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

/-! ## Part 2 — the flat-composition §6 pipeline (fuel-free leaf substitution)

Everything past the five recursive bottoms is a flat composition over fuel-free leaves. The fuel-free companions
substitute the fuel-free leaves — the generic ones reused verbatim (`cdivWf`, `cdivmodWf`, `cdiophantineGWf`,
`cdvdGWf`, `cgcdWf`, the §5.6 `cResidueResultantTowerGWf`/`cinterpolateG`/`cHornerG`) and the new ones from
Part 1 plus the integration fuel-free file (`cgcdFFCoreWf`, `cSplitFactorFastGWf`, the two done RDE
bottoms `cPolyRischDENoCancelGWf`/`cSPDEGWf`, and the three Part-1 bottoms). Each `…GWf` mirrors its `…G`
original op-for-op with the fuel dropped — a pure composition, no new recursion. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α]

/-- **Generic fuel-free weak normalizer** `cWeakNormalizerGWf Dt fnum fden = q ∈ α[t]` (Bronstein §6.1, book
p.183): the generic, fuel-free companion of `cWeakNormalizerG`. Split the denominator into its normal part
`dₙ` (`cSplitFactorFastGWf`), form `d₁ = (dₙ/g)/gcd(dₙ/g, g)` with `g = gcd(dₙ, dₙ')`, solve the residue
numerator `a` via `cdiophantineGWf`, build the residue resultant `r = res_t(a − z·Dd₁, d₁)`
(`cResidueResultantTowerGWf`), and return `∏ᵢ gcd(a − nᵢ·Dd₁, d₁)^{nᵢ}` over the positive integer roots `nᵢ`
of `r` (`cPosIntRootsG`, nodes lifted by `cnatCastG`). Every gcd is the fuel-free `cgcdFFCoreWf`, every
division the fuel-free `cdivWf` — **no fuel at runtime**. For an already-weakly-normalized `f`, `q = 1`.
`[CField α] [CDiffField α] [CFracGcdCoreWf α]`-generic — runs at any tower level. -/
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

/-- **Generic fuel-free normal-denominator reduction** `cRdeNormalDenominatorGWf Dt fnum fden gnum gden`
(Bronstein §6.2, book p.185): the generic, fuel-free companion of `cRdeNormalDenominatorG`, for weakly
normalized `f = fnum/fden`, `g = gnum/gden`. Returns `none` ("no solution") or `some (a, b, c, h)` reducing
`Dy + fy = g` to `a·Dq + b·q = c` with `q = y·h`. Split the denominators into normal parts `dₙ, eₙ`
(`cSplitFactorFastGWf`); `p = gcd(dₙ, eₙ)`, `h = gcd(eₙ, eₙ')/gcd(p, p')`; if `eₙ ∤ dₙh²` then `none`; else
`a = dₙh`, `b = (dₙh·fnum − dₙ·Dh·fden)/fden`, `c = dₙh²·gnum/gden`. Every gcd/division/divisibility is the
fuel-free `cgcdFFCoreWf`/`cdivWf`/`cdvdGWf` — **no fuel at runtime**. -/
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

/-- **Generic fuel-free special monic irreducible of the monomial** `cSpecialPolyGWf Dt = p`: the generic,
fuel-free companion of `cSpecialPolyG`, the monic special part of the monomial derivative `Dt` (`t²+1`
hypertangent, `t` hyperexponential, `1` primitive) via the fuel-free splitting-factorization
`cSplitFactorFastGWf` — **no fuel at runtime**. -/
def cSpecialPolyGWf (Dt : CPolyG α) : CPolyG α :=
  cmonicG (cSplitFactorFastGWf Dt Dt).2

/-- **Generic fuel-free special-denominator reduction** `cRdeSpecialDenominatorGWf Dt a b c` (Bronstein §6.2,
book p.190/192): the generic, fuel-free companion of `cRdeSpecialDenominatorG`. Given `a·Dq + b·q = c` with
`a` free of special factors, returns the special-cleared quadruplet `(ā, b̄, c̄, h)` (`h = p^{−n}`) so
`r = q·h ∈ α[t]` solves `ā·Dr + b̄·r = c̄`. Steps: `p ← cSpecialPolyGWf Dt` (constant ⇒ trivial, returns
`(a,b,c,1)`); `n_b = ν_p(b)`, `n_c = ν_p(c)` (fuel-free `cValuationGWf`), `n = min(0, n_c − min(0, n_b))`,
`N = max(0, −n_b, n − n_c)`; return `(a·pᴺ, (b + n·a·Dp/p)·pᴺ, c·p^{N−n}, p^{−n})`, the `Dp/p` division the
fuel-free `cdivWf`. The cancellation refinement (`n_b = 0` branch) is the documented continuation. The
scalar `−negn` is lifted by `cnatCastG` (negated). **No fuel at runtime**. -/
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

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

/-- **Generic fuel-free polynomial antiderivative** `cIntegratePolyGWf c = q` with `Dq = c` and `q(0) = 0`,
for the canonical primitive monomial (`Dt = 1`) and constant coefficients: termwise
`∫ Σ cᵢtⁱ = Σ (cᵢ/(i+1)) t^{i+1}` (`cᵢ/(i+1) = CField.div cᵢ (cnatCastG (i+1))`). The fuel-free companion of
`cIntegratePolyG` (which already carries no fuel) — **no fuel at runtime**. -/
def cIntegratePolyGWf (c : CPolyG α) : CPolyG α :=
  CField.zero :: ((c : List α).zipIdx.map (fun (a, i) => CField.div a (cnatCastG (i + 1))))

end CPolyG

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CRischField α]

/-- **Generic fuel-free Poly-Risch-DE dispatcher** `cPolyRischDEGWf Dt b c n` (Bronstein §6.5 + §6.6): the
generic, fuel-free companion of `cPolyRischDEG`. Solves `Dq + b·q = c` for `q ∈ α[t]`, `deg(q) ≤ n`, routing
by monomial type and `deg(b)` (Lemma 6.5.1): `b = 0` ⇒ pure integration (`cIntegratePolyGWf`, with the
`deg(c)+1 ≤ n` check — the primitive base branch); `deg(b) > max(0, δ−1)` ⇒ non-cancellation
(`cPolyRischDENoCancelGWf`); `δ = 0, deg(b) = 0` ⇒ primitive cancellation (`cPolyRischDECancelPrimGWf`);
`δ = 1, deg(b) = 0` ⇒ hyperexponential cancellation (`cPolyRischDECancelExpGWf`); else (hypertangent
`δ ≥ 2`) ⇒ falls back to the non-cancellation loop. Every branch runs fuel-free — **no fuel at runtime**.
`[CRischField α]`-generic — runs at any tower level. -/
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

/-! ## Part 3 — ★ THE HEADLINE: the generic fuel-free Risch-DE oracle `cRischDEGWf`

`cRischDEGWf` threads the fuel-free §6 stages, the fuel-free companion of `cRischDEG`. For `f = fnum/fden`,
`g = gnum/gden ∈ α(t)` it returns `some (ynum, yden)` with `y = ynum/yden` solving `Dy + f·y = g`, or `none`.
The base solve inside the cancellation cases is the typeclass `crischDESolve` (through the Part-1 own-loops),
so a *level-`n+1`* call recurses into the *level-`n`* `crischDESolve`. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α] [CFracGcdCoreWf α] [CRischField α]

/-- **★ THE HEADLINE — the generic fuel-free Risch differential equation solver** `cRischDEGWf Dt fnum fden
gnum gden` (Bronstein Ch. 6, assembled): the generic, fuel-free companion of `cRischDEG`. For `f = fnum/fden`,
`g = gnum/gden ∈ α(t)` and the monomial derivation `D = cmonomialDeriv Dt`, returns `some (ynum, yden)` with
`y = ynum/yden ∈ α(t)` solving `Dy + f·y = g`, or `none`. Stages: §6.2 normal denominator
(`cRdeNormalDenominatorGWf`) → §6.2 special denominator (`cRdeSpecialDenominatorGWf`) → §6.3 degree bound
(`cRdeBoundDegreeG`) → §6.4 SPDE (`cSPDEGWf`) → §6.5/§6.6 PolyRischDE dispatch (`cPolyRischDEGWf`), with the
polynomial unknown `Q = α'·v + β` reassembled to `y = Q·h₁ / h₀`. The cancellation cases recurse into
`CRischField.crischDESolve` over `α` — at level `n+1` this is the level-`n` oracle. **No fuel at runtime in
any regime**; `native_decide`-able over the noncomputable tower. `[CField α] [CDiffField α]
[CFracGcdCoreWf α] [CRischField α]`-generic — runs at any tower level. (`f` is assumed weakly normalized —
the post-Hermite RDE input; `cWeakNormalizerGWf` returns `q = 1` on such `f`.) -/
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

end CPolyG

/-! ## Part 4 — ★ `native_decide` smoke test: the headline `cRischDEGWf` computes fuel-free

The deliverable: the generic fuel-free RDE oracle `cRischDEGWf` *runs in native code* over the tower. We solve
a small Risch differential equation over `CPolyG (QFunNZG ℚ) = ℚ(x)[t₁]` with the primitive monomial `t₁`
(`Dt₁ = [1]`, `D(t₁) = 1`): `Dy + 0·y = 1` (`f = 0/1`, `g = 1/1`), whose solution is `y = t₁`. The fuel-free
oracle — normal denominator → special denominator → degree bound → SPDE → the §6.5/§6.6 dispatch (here the
`b = 0` primitive-integration branch) — returns `some (ynum, yden)` with **no fuel at runtime**, and the
returned `y = ynum/yden` is verified to **actually solve** the equation by the cleared polynomial identity
`gden·fden·(D(ynum)·yden − ynum·D(yden)) + gden·fnum·ynum·yden = gnum·fden·yden²` reading to `0`
(`cisZeroG`, the generic analogue of `rdeClearedCheck`, not merely pinning the output). Everything stays
`[CField …]`/`[CDiffField …]`/`[CFracGcdCoreWf …]`/`[CRischField …]`-computable with `Prop`-erased subtype
proofs, so nothing noncomputable reaches the native compiler — `native_decide` reduces, the oracle genuinely
running the fuel-free §6 pipeline over ℚ(x)[t₁]. -/

open CPolyG in
/-- The level-1 monomial derivative `Dt₁ = 1` over `CPolyG (QFunNZG ℚ) = ℚ(x)[t₁]` (`t₁` primitive). -/
def towerRdeGWfDt : CPolyG (QFunNZG ℚ) := [CField.one]

open CPolyG in
/-- **★ The generic fuel-free RDE oracle `cRischDEGWf` solves `Dy = 1` over ℚ(x)(t₁), fuel-free**
(`native_decide`, the smoke-test deliverable). `cRischDEGWf [1] 0 1 1 1` over `CPolyG (QFunNZG ℚ) = ℚ(x)[t₁]`
(monomial `t₁`, `Dt₁ = 1`, primitive) returns `some (ynum, yden)` with **no fuel at runtime**, and the
returned `y = ynum/yden` is verified to **actually solve** `Dy + 0·y = 1` by the cleared polynomial identity
(`= 0` via `cisZeroG`) — the solution `y = t₁`. This certifies the headline generic fuel-free oracle computes
end-to-end over the tower: the §6 pipeline (down to the `b = 0` integration branch of `cPolyRischDEGWf`) runs
fuel-free over ℚ(x)[t₁]. -/
theorem towerRdeGWf_solves_Dy_eq_one :
    (match cRischDEGWf towerRdeGWfDt ([] : CPolyG (QFunNZG ℚ)) [CField.one] [CField.one] [CField.one] with
      | some (ynum, yden) =>
          let Dyn := cmonomialDeriv towerRdeGWfDt ynum
          let Dyd := cmonomialDeriv towerRdeGWfDt yden
          let fnum : CPolyG (QFunNZG ℚ) := []
          let fden : CPolyG (QFunNZG ℚ) := [CField.one]
          let gnum : CPolyG (QFunNZG ℚ) := [CField.one]
          let gden : CPolyG (QFunNZG ℚ) := [CField.one]
          let lhs := caddG
            (cmulG (cmulG gden fden) (csubG (cmulG Dyn yden) (cmulG ynum Dyd)))
            (cmulG (cmulG (cmulG gden fnum) ynum) yden)
          let rhs := cmulG (cmulG gnum fden) (cmulG yden yden)
          cisZeroG (csubG lhs rhs)
      | none => false) = true := by native_decide

open CPolyG in
/-- **The generic fuel-free RDE oracle solves `Dy + y = t₁ + 1` over ℚ(x)(t₁), fuel-free**
(`native_decide`): this exercises the primitive-cancellation branch of `cRischDEGWf` with nonzero
coefficient `f = 1`, returning a solution whose cleared RDE identity holds. -/
theorem towerRdeGWf_solves_Dy_plus_y_eq_t1_plus_one :
    (match cRischDEGWf towerRdeGWfDt [CField.one] [CField.one]
        [CField.one, CField.one] [CField.one] with
      | some (ynum, yden) =>
          let Dyn := cmonomialDeriv towerRdeGWfDt ynum
          let Dyd := cmonomialDeriv towerRdeGWfDt yden
          let fnum : CPolyG (QFunNZG ℚ) := [CField.one]
          let fden : CPolyG (QFunNZG ℚ) := [CField.one]
          let gnum : CPolyG (QFunNZG ℚ) := [CField.one, CField.one]
          let gden : CPolyG (QFunNZG ℚ) := [CField.one]
          let lhs := caddG
            (cmulG (cmulG gden fden) (csubG (cmulG Dyn yden) (cmulG ynum Dyd)))
            (cmulG (cmulG (cmulG gden fnum) ynum) yden)
          let rhs := cmulG (cmulG gnum fden) (cmulG yden yden)
          cisZeroG (csubG lhs rhs)
      | none => false) = true := by native_decide

-- The `native_decide` smoke tests carry `Lean.ofReduceBool` separately.
#print axioms towerRdeGWf_solves_Dy_eq_one
#print axioms towerRdeGWf_solves_Dy_plus_y_eq_t1_plus_one

end DeepWiki.SymbolicIntegration
