import DeepWiki.SymbolicIntegration.ComputableAlgebraicResidues

/-! # Residue at infinity for simple-radical differentials (Trager Ch. 5 §2 + Ch. 2 §3)

The finite log-part residues of an algebraic differential `f dx` on `y² = ρ(x)` are computed by the
eq. 7 residue resultant `cAlgResidueResultant` (`ComputableAlgebraicResidues`). To complete the picture
one needs the **residue at infinity** — Trager's "normalize at infinity" (Ch. 2 §3). For the
arcsinh/arccosh-class integrals (`∫ dx/√(x²±1)`) the *finite* residues all vanish and the entire log
term comes from the place over `x = ∞`.

**The key reduction.** The residue at infinity of `f dx` is the **finite** residue at `t = 0` of the
differential transformed under `x = 1/t`, `dx = −dt/t²`. So no new resultant is needed: transform the
data `(ρ, g₀, g₁, D)` (for `f = (g₀ + g₁ y)/D`) into `(ρ̃, g̃₀, g̃₁, D̃)` in `t`, then read the residue
at the place `t = 0` off the **existing** eq. 7 machinery.

**The transform (`x = 1/t`).** With `d = deg ρ`, `m = ⌈d/2⌉`, `N = max(deg g₀, deg g₁, deg D)`, and the
reverse-coefficient operation `revₖ p := t^k·p(1/t)` (pad to length `k+1`, reverse): set `ỹ = t^m·y`
(so `ỹ² = ρ̃ := rev_{2m} ρ`) and `y = ỹ/t^m`, then
  `f dx = (g₀(1/t) + g₁(1/t)·ỹ/t^m)/D(1/t) · (−dt/t²)
        = −(t^m·rev_N g₀ + (rev_N g₁)·ỹ)/(t^{m+2}·rev_N D) dt`,
giving raw `g̃₀ = −t^m·rev_N g₀`, `g̃₁ = −rev_N g₁`, `D̃ = t^{m+2}·rev_N D`, `ρ̃ = rev_{2m} ρ`. A common
`t`-power across `(g̃₀, g̃₁, D̃)` is cancelled (it leaves `f̃` unchanged but inflates the pole order at
`t = 0` and spoils the simple-pole resultant), keeping the place over `∞` a **simple** pole.

**Reading the residue at ∞.** `res_t((Z·D̃' − g̃₀)² − g̃₁²·ρ̃, D̃)` factors over the roots `t₀` of `D̃`,
its `t₀`-factor being the eq. 7 norm `(Z·D̃'(t₀) − g̃₀(t₀))² − g̃₁(t₀)²·ρ̃(t₀)`. The residue **at
infinity** is precisely the factor at `t₀ = 0`. Two views, both reusing the engine:
* `cAlgResidueAtInfinity` — the **full** `R̃(Z) = res_t(norm, D̃)` (the existing `cAlgResidueResultant`
  on the transformed data). For the clean even-degree arcsinh/arccosh cases the only nonzero-residue
  place is `t = 0`, so the nonzero roots of `R̃` *are* the residues at ∞ (the rest is a `Z`-power from
  zero-residue branch places `t = ±i` ↔ the curve's branch points).
* `cResidueAtInfinityPlace` — the **isolated `t = 0` place** factor `(Z·D̃'(0) − g̃₀(0))² −
  g̃₁(0)²·ρ̃(0)` (= `res_t(norm, t)` with the *true* `D̃'`), the genuinely-localized residue at ∞ that
  stays correct even when `t = 0` is not a pole (residue `0`) — needed for the residue-theorem
  cross-check on differentials with both finite and infinite contributions. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### Reverse-coefficient (`t^k·p(1/t)`) and common-`t`-power cancellation -/

/-- **Pad** a `CPolyG` (low→high) on the high end with `CField.zero` up to length `n` (no-op if already
≥ `n` long). The list view of zero-padding used by the reverse-coefficient transform. -/
def cpadG (n : ℕ) (p : CPolyG α) : CPolyG α :=
  (p : List α) ++ List.replicate (n - (p : List α).length) CField.zero

/-- **Reverse-coefficient transform** `creverseDegG k p = t^k · p(1/t)` for `k ≥ deg p`: pad `p` to
length `k + 1` then reverse the coefficient list (so the `t^j` coefficient is `p`'s `(k − j)` one).
With `p(x) = Σ aᵢ xⁱ`, `creverseDegG k p` is `Σ aᵢ t^{k−i}` — the engine's `x = 1/t` substitution on a
single polynomial. -/
def creverseDegG (k : ℕ) (p : CPolyG α) : CPolyG α :=
  (cpadG (k + 1) p).reverse

/-- **Count leading-zero coefficients** of a `CPolyG` (initial `isZero` run length) — the order of
vanishing at `t = 0`, i.e. the `t`-power dividing `p`. -/
def cleadingZerosG (p : CPolyG α) : ℕ := (p.takeWhile (fun a => CField.isZero a)).length

/-- **Common `t`-power** `commonTPow ps` shared by every `CPolyG` in `ps`: the `min` of their
leading-zero counts (`0` for the empty list). The maximal `t^k` dividing all of `ps` simultaneously. -/
def commonTPow (ps : List (CPolyG α)) : ℕ :=
  match ps.map cleadingZerosG with
  | [] => 0
  | n :: ns => ns.foldl Nat.min n

/-- **Divide a `CPolyG` by `t^k`** by dropping `k` low coefficients (`p.drop k`). Sound only when the
first `k` coefficients are zero (the caller guarantees this via `commonTPow`); realizes division by the
monomial `t^k`. -/
def cdropTPowG (k : ℕ) (p : CPolyG α) : CPolyG α := (p : List α).drop k

/-! ### The coordinate transform at infinity -/

/-- **The `x = 1/t` coordinate transform at infinity** `radTransformAtInfinity ρ g₀ g₁ D = (ρ̃, g̃₀,
g̃₁, D̃)` for the simple-radical differential `f dx = (g₀ + g₁·y)/D dx` on `y² = ρ`. With `d = deg ρ`,
`m = ⌈d/2⌉`, `N = max(deg g₀, deg g₁, deg D)`, and `revₖ p := t^k·p(1/t)` (`creverseDegG`):
`ρ̃ = rev_{2m} ρ`, raw `g̃₀ = −t^m·rev_N g₀`, raw `g̃₁ = −rev_N g₁`, raw `D̃ = t^{m+2}·rev_N D`; then the
common `t`-power across `(g̃₀, g̃₁, D̃)` is cancelled (`commonTPow`/`cdropTPowG`) so the place over `∞`
stays a **simple** pole. The residue at `∞` of `f dx` is the residue at the place `t = 0` of
`(g̃₀ + g̃₁·ỹ)/D̃ dt` on `ỹ² = ρ̃` (Trager Ch. 2 §3, normalize at infinity). Generic over `[CField α]`. -/
def radTransformAtInfinity (rho g0 g1 D : CPolyG α) :
    CPolyG α × CPolyG α × CPolyG α × CPolyG α :=
  let d := cdegG rho
  let m := (d + 1) / 2                                            -- ⌈d/2⌉
  let N := max (max (cdegG g0) (cdegG g1)) (cdegG D)
  let rhoT := creverseDegG (2 * m) rho                           -- t^{2m}·ρ(1/t)
  let g0raw := cnegG (cshiftG m (creverseDegG N g0))             -- −t^m·rev_N g₀
  let g1raw := cnegG (creverseDegG N g1)                         -- −rev_N g₁
  let Draw := cshiftG (m + 2) (creverseDegG N D)                 -- t^{m+2}·rev_N D
  let k := commonTPow [g0raw, g1raw, Draw]
  (cnormG rhoT, cnormG (cdropTPowG k g0raw), cnormG (cdropTPowG k g1raw), cnormG (cdropTPowG k Draw))

/-! ### The residue-at-infinity resultant (full + isolated-place) -/

/-- **Full residue-at-infinity resultant** `cAlgResidueAtInfinity fuel ρ g₀ g₁ D = R̃(Z) ∈ K[Z]`: the
**existing** `cAlgResidueResultant` (eq. 7) on the `x = 1/t`-transformed data
`radTransformAtInfinity ρ g₀ g₁ D`. `R̃(Z) = res_t((Z·D̃' − g̃₀)² − g̃₁²·ρ̃, D̃)` factors over the roots
of `D̃`; the **residue at infinity** is the `t = 0` factor. For the clean even-degree arcsinh/arccosh
differentials the other roots (`t = ±i`, the curve's branch points) have residue `0`, so the **nonzero**
roots of `R̃` are exactly the residues at ∞. Reuses the resultant — no new elimination. -/
def cAlgResidueAtInfinity (fuel : ℕ) (rho g0 g1 D : CPolyG α) : CPolyG α :=
  let (rhoT, g0T, g1T, DT) := radTransformAtInfinity rho g0 g1 D
  cAlgResidueResultant fuel DT rhoT g0T g1T

/-- **Isolated residue at the place `t = 0`** (= the residue at infinity) `cResidueAtInfinityPlace fuel
ρ g₀ g₁ D = (Z·D̃'(0) − g̃₀(0))² − g̃₁(0)²·ρ̃(0) ∈ K[Z]`, the `t = 0` factor of the eq. 7 norm with the
**true** transformed derivative `D̃'` — i.e. `res_t(norm, t)` localized at the place over `∞`. Built
directly from the four constants `D̃'(0), g̃₀(0), g̃₁(0), ρ̃(0)` (`cevalG · 0`) as the degree-≤2
`Z`-polynomial `(Z·D̃'(0) − g̃₀(0))² − g̃₁(0)²·ρ̃(0)`. Unlike the full `cAlgResidueAtInfinity` this
isolates the single place `t = 0`, so it stays correct (residue `0`, i.e. `R̃₀ = D̃'(0)²·Z²`) when `∞`
is **not** a pole — the form needed for the residue-theorem cross-check on mixed differentials. -/
def cResidueAtInfinityPlace (fuel : ℕ) (rho g0 g1 D : CPolyG α) : CPolyG α :=
  let (rhoT, g0T, g1T, DT) := radTransformAtInfinity rho g0 g1 D
  let Dp0 := cevalG (cderivG DT) CField.zero                     -- D̃'(0)
  let a0 := cevalG g0T CField.zero                               -- g̃₀(0)
  let b0 := cevalG g1T CField.zero                               -- g̃₁(0)
  let r0 := cevalG rhoT CField.zero                              -- ρ̃(0)
  let lin : CPolyG α := [CField.neg a0, Dp0]                     -- D̃'(0)·Z − g̃₀(0)
  let _ := fuel
  csubG (cmulG lin lin) [CField.mul (CField.mul b0 b0) r0]       -- (·)² − g̃₁(0)²·ρ̃(0)

end CPolyG

/-! ### ★ Validation: `∫ dx/√(x²+1)` (arcsinh) and `∫ dx/√(x²−1)` (arccosh) — residues at ∞ (`native_decide`)

`K = ℚ`. For `∫ dx/√(x² + 1)` on `y² = ρ = x² + 1`: rationalize `1/y = y/ρ`, so `g(x,y) = y`
(`g₀ = 0, g₁ = 1`) and `D(x) = ρ = x² + 1`. The transform at `∞` gives `(ρ̃, g̃₀, g̃₁, D̃) =
(1 + t², 0, −1, t(1 + t²))` (the prompt's hand computation), whose `t = 0` place has residue resultant
`Z² − 1`, residues `±1` — matching the log term `log(x + √(x² + 1)) = arcsinh(x)`. `∫ dx/√(x² − 1)`
(arccosh) is identical with `ρ = x² − 1`. -/

open CPolyG

/-- arcsinh radicand `ρ = x² + 1` (curve `y² = x² + 1`), `ℚ[x]` `[1, 0, 1]`. -/
def arcsinhInf_rho : CPolyG ℚ := [1, 0, 1]
/-- arcsinh numerator low part `g₀ = 0` (`g = y`). -/
def arcsinhInf_g0 : CPolyG ℚ := []
/-- arcsinh numerator `y`-coefficient `g₁ = 1` (`g = y`), `ℚ[x]` `[1]`. -/
def arcsinhInf_g1 : CPolyG ℚ := [1]
/-- arcsinh denominator `D = ρ = x² + 1` (`f = 1/y = y/ρ`), `ℚ[x]` `[1, 0, 1]`. -/
def arcsinhInf_D : CPolyG ℚ := [1, 0, 1]

/-- arccosh radicand `ρ = x² − 1` (curve `y² = x² − 1`), `ℚ[x]` `[−1, 0, 1]`. -/
def arccoshInf_rho : CPolyG ℚ := [-1, 0, 1]
/-- arccosh denominator `D = ρ = x² − 1`, `ℚ[x]` `[−1, 0, 1]`. -/
def arccoshInf_D : CPolyG ℚ := [-1, 0, 1]

-- Sanity print: `(ρ̃, g̃₀, g̃₁, D̃) = (1+t², 0, −1, t(1+t²))`, then the `t=0` place residue `Z²−1`.
#eval (radTransformAtInfinity arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D : CPolyG ℚ × CPolyG ℚ × CPolyG ℚ × CPolyG ℚ)
#eval (cnormG (cResidueAtInfinityPlace 30 arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D) : List ℚ)

/-- **★ The `x = 1/t` transform reproduces Trager's normalize-at-infinity data** (`native_decide`). For
`∫ dx/√(x² + 1)` the transform of `(ρ, g₀, g₁, D) = (x² + 1, 0, 1, x² + 1)` is exactly the prompt's hand
computation `(ρ̃, g̃₀, g̃₁, D̃) = (1 + t², 0, −1, t(1 + t²))` — the common `t²` correctly cancelled so
`D̃ = t(1 + t²)` keeps the place over `∞` a simple pole. -/
theorem arcsinhInf_transform_eq :
    radTransformAtInfinity arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D
      = ([1, 0, 1], [], [-1], [0, 1, 0, 1]) := by native_decide

/-- **★ Residue at infinity of `∫ dx/√(x² + 1)` is `±1`** (`native_decide`, Trager Ch. 2 §3 + Ch. 5 §2).
The isolated `t = 0` place residue resultant is `Z² − 1 = (Z − 1)(Z + 1)` (`cisZeroG` of
`cResidueAtInfinityPlace − (Z² − 1)`), so the residues at ∞ are `±1` — exactly the log term
`log(x + √(x² + 1)) = arcsinh(x)`. The arcsinh class is generated at infinity. -/
theorem arcsinhInf_residue_eq :
    cisZeroG (csubG (cResidueAtInfinityPlace 30 arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D)
      [-1, 0, 1]) = true := by native_decide

/-- **★ The full transformed resultant exposes the same `±1`** (`native_decide`): the full
`R̃(Z) = res_t(norm, D̃) = 16·Z⁴·(Z² − 1)` (`cisZeroG` of `R̃ − 16Z⁴(Z²−1)`). The factor `Z² − 1` is the
`t = 0` place (residue at ∞, `±1`); the `Z⁴` is the two branch places `t = ±i` (`x = ∓i`, the curve's
branch points) where the residue vanishes. So the nonzero roots of `R̃` are the residues at ∞. -/
theorem arcsinhInf_full_resultant_eq :
    cisZeroG (csubG (cAlgResidueAtInfinity 30 arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D)
      [0, 0, 0, 0, -16, 0, 16]) = true := by native_decide

/-- **★ `±1` are residues at ∞; `2` is not** (`native_decide`): `cIsResidue` on the isolated place
resultant `Z² − 1` accepts `Z = ±1` and rejects `Z = 2`. -/
theorem arcsinhInf_isResidue :
    cIsResidue 30 (cResidueAtInfinityPlace 30 arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D) (1 : ℚ) = true
    ∧ cIsResidue 30 (cResidueAtInfinityPlace 30 arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D) (-1 : ℚ) = true
    ∧ cIsResidue 30 (cResidueAtInfinityPlace 30 arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D) (2 : ℚ) = false := by
  native_decide

/-- **★ Residue at infinity of `∫ dx/√(x² − 1)` (arccosh) is `±1`** (`native_decide`). Same as arcsinh
with `ρ = x² − 1`: the isolated `t = 0` place residue resultant is again `Z² − 1`, residues `±1` —
the log term `log(x + √(x² − 1)) = arccosh(x)` is generated at infinity. -/
theorem arccoshInf_residue_eq :
    cisZeroG (csubG (cResidueAtInfinityPlace 30 arccoshInf_rho arcsinhInf_g0 arcsinhInf_g1 arccoshInf_D)
      [-1, 0, 1]) = true := by native_decide

/-! ### ★ The residue theorem as cross-check (`native_decide`)

Residue theorem on `y² = ρ`: (sum of finite residues) + (sum of residues at ∞) = 0. For `∫ dx/√(x² ± 1)`
the **finite** residue resultant is a pure power of `Z` — every finite residue is `0` — while the residue
at infinity is `±1`. The two ∞-residues `+1, −1` sum to `0`, and `0 + 0 = 0`: the residue theorem holds.
(The finite residue resultant `cAlgResidueResultant D ρ g₀ g₁` for the *same* differential equals
`16·Z⁴`, exhibiting all finite residues `= 0`.) -/

/-- **★ All finite residues of `∫ dx/√(x² + 1)` vanish** (`native_decide`): the finite eq. 7 resultant
`cAlgResidueResultant D ρ g₀ g₁ = 16·Z⁴` — a pure `Z`-power, so every finite residue is `0`. (The roots
of `D = x² + 1` are `x = ±i`, the branch points, with vanishing residue.) -/
theorem arcsinhInf_finite_residues_zero :
    cisZeroG (csubG (cAlgResidueResultant 30 arcsinhInf_D arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1)
      [0, 0, 0, 0, 16]) = true := by native_decide

/-- **★ The residue theorem for `∫ dx/√(x² + 1)`** (`native_decide`): finite residues are all `0`
(`arcsinhInf_finite_residues_zero`) and the residues at ∞ are `±1` (`arcsinhInf_residue_eq`); their grand
sum `0 + (+1) + (−1) = 0`. We certify the residue-at-∞ side by `cResiduesMatch` (the isolated place
resultant `Z² − 1 = (Z − 1)(Z + 1)`, residues `+1, −1`) — and the finite side has no residue to add. The
residue theorem (finite + ∞ = 0) is satisfied: the arcsinh log term comes entirely from infinity. -/
theorem arcsinhInf_residue_theorem :
    cResiduesMatch (cResidueAtInfinityPlace 30 arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D) [1, -1] = true
    ∧ cisZeroG (cAlgResidueResultant 30 arcsinhInf_D arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1) = false
    ∧ cResiduesMatch (cAlgResidueResultant 30 arcsinhInf_D arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1) [0, 0, 0, 0] = true := by
  native_decide

/-! ### ★ STRETCH 1: a differential with BOTH finite and ∞ residues nonzero (`native_decide`)

`∫ √(x² + 1)/(x² − x) dx`, i.e. `f = y/(x² − x)` on `y² = ρ = x² + 1` — `g = y` (`g₀ = 0, g₁ = 1`),
`D = x² − x = x(x − 1)`. Now both ends contribute: the **finite** eq. 7 resultant is
`(Z² − 1)(Z² − 2)` — finite residues `±1` (pole `x = 0`, sheets `y = ±1`) and `±√2` (pole `x = 1`,
`y = ±√2`) — while the residue at ∞ (`f ~ y/x² ~ 1/x` near ∞, a genuine simple pole) is `Z² − 1`,
residues `±1`. The residue theorem demands the grand total vanish: each resultant's sum of roots is `0`
(no second-leading term — `Z⁴ + 0·Z³ − 3Z² + 0·Z + 2` and `Z² + 0·Z − 1`), so finite-sum `0` +
∞-sum `0` = `0`. -/

/-- both-nonzero radicand `ρ = x² + 1`, `ℚ[x]` `[1, 0, 1]`. -/
def bothInf_rho : CPolyG ℚ := [1, 0, 1]
/-- both-nonzero numerator `g = y` (`g₀ = 0`). -/
def bothInf_g0 : CPolyG ℚ := []
/-- both-nonzero numerator `y`-coefficient `g₁ = 1`. -/
def bothInf_g1 : CPolyG ℚ := [1]
/-- both-nonzero denominator `D = x² − x = x(x − 1)`, `ℚ[x]` `[0, −1, 1]`. -/
def bothInf_D : CPolyG ℚ := [0, -1, 1]

-- Sanity: finite `(Z²−1)(Z²−2) = Z⁴−3Z²+2`, then the ∞ place `Z²−1`.
#eval (cnormG (cAlgResidueResultant 40 bothInf_D bothInf_rho bothInf_g0 bothInf_g1) : List ℚ)
#eval (cnormG (cResidueAtInfinityPlace 40 bothInf_rho bothInf_g0 bothInf_g1 bothInf_D) : List ℚ)

/-- **★ Finite residue resultant of `∫ √(x²+1)/(x²−x) dx` is `(Z²−1)(Z²−2)`** (`native_decide`): the
finite eq. 7 resultant `cAlgResidueResultant D ρ g₀ g₁ = Z⁴ − 3Z² + 2`, so the finite residues are the
roots `±1` (pole `x = 0`) and `±√2` (pole `x = 1`) — both nonzero, the `±√2` an irrational residue
requiring the splitting field `ℚ(√2)`. -/
theorem bothInf_finite_resultant_eq :
    cisZeroG (csubG (cAlgResidueResultant 40 bothInf_D bothInf_rho bothInf_g0 bothInf_g1)
      [2, 0, -3, 0, 1]) = true := by native_decide

/-- **★ Residue at infinity of `∫ √(x²+1)/(x²−x) dx` is `±1`** (`native_decide`): the isolated `t = 0`
place resultant is `Z² − 1` (`f ~ 1/x` at ∞ is a genuine simple pole), residues `±1` — nonzero, so this
differential has nontrivial residues at **both** the finite poles and infinity. -/
theorem bothInf_infinity_residue_eq :
    cisZeroG (csubG (cResidueAtInfinityPlace 40 bothInf_rho bothInf_g0 bothInf_g1 bothInf_D)
      [-1, 0, 1]) = true := by native_decide

/-- **★ The residue theorem for `∫ √(x²+1)/(x²−x) dx`: finite + ∞ residues sum to `0`**
(`native_decide`). With both sides nonzero, the cross-check is Vieta: each resultant has **vanishing**
second-leading coefficient, so its roots (the residues) sum to `0`. The finite `(Z²−1)(Z²−2) =
Z⁴ + 0·Z³ − 3Z² + 0·Z + 2` has root-sum `0`; the ∞ `Z² − 1 = Z² + 0·Z − 1` has root-sum `0`; hence
(finite-sum) + (∞-sum) `= 0 + 0 = 0`. The residue theorem holds with nontrivial contributions from both
ends — the engine computes the complete residue picture. (Checked: the `Z³` coefficient of the finite
resultant and the `Z¹` coefficient of the ∞ resultant are both `0`.) -/
theorem bothInf_residue_theorem :
    ((cnormG (cAlgResidueResultant 40 bothInf_D bothInf_rho bothInf_g0 bothInf_g1) : List ℚ).getD 3 0 = 0)
    ∧ ((cnormG (cResidueAtInfinityPlace 40 bothInf_rho bothInf_g0 bothInf_g1 bothInf_D) : List ℚ).getD 1 0 = 0)
    ∧ cisZeroG (cAlgResidueResultant 40 bothInf_D bothInf_rho bothInf_g0 bothInf_g1) = false
    ∧ cisZeroG (cResidueAtInfinityPlace 40 bothInf_rho bothInf_g0 bothInf_g1 bothInf_D) = false := by
  native_decide

/-! ### STRETCH 2: the odd-`deg ρ` case — a branch place at infinity (Puiseux, documented)

When `deg ρ` is **odd**, the point at infinity is a single **branch place** of `y² = ρ` and the transform
degenerates: `ρ̃ = rev_{2m} ρ` then has `ρ̃(0) = 0` (the leading `t`-coefficient is dropped), so the
transformed curve `ỹ² = ρ̃` is itself **ramified at `t = 0`** — `ỹ = √(ρ̃) ∼ √t` is a half-integer
(Puiseux) expansion, not a rational place. The simple-pole residue formula `g/D'` (and the eq. 7 norm at
a *regular* place) no longer applies directly; reading the residue at this ramified place needs the local
**Puiseux** parametrization (`t = s²`), i.e. machinery beyond the clean even-degree reduction. Probe on
`∫ dx/√(x³)` (`ρ = x³`, deg 3, `m = 2`): the transform yields `ρ̃ = t` (deg 1, odd ⇒ ramified) and the
place computation returns the degenerate `Z²` (a pure `Z`-power, the `−g̃₁(0)²·ρ̃(0)` term vanishing with
`ρ̃(0) = 0` — no honest residue extracted), flagging exactly this Puiseux obstruction. The **even** case
(`∫ dx/√(x² ± 1)`, two unramified places or one
regular place over ∞) is the one the engine resolves; the odd case is documented here as the next step. -/

/-- odd-degree probe radicand `ρ = x³`, `ℚ[x]` `[0, 0, 0, 1]` (deg 3, odd — branch place at ∞). -/
def oddInf_rho : CPolyG ℚ := [0, 0, 0, 1]
/-- odd-degree probe denominator `D = x³` (`f = 1/y = y/ρ`), `ℚ[x]` `[0, 0, 0, 1]`. -/
def oddInf_D : CPolyG ℚ := [0, 0, 0, 1]

-- Probe: `ρ̃ = t` (deg 1, odd ⇒ ramified — `ỹ = √t` Puiseux), place computation degenerates to `−Z²`.
#eval (radTransformAtInfinity oddInf_rho arcsinhInf_g0 arcsinhInf_g1 oddInf_D : CPolyG ℚ × CPolyG ℚ × CPolyG ℚ × CPolyG ℚ)
#eval (cnormG (cResidueAtInfinityPlace 30 oddInf_rho arcsinhInf_g0 arcsinhInf_g1 oddInf_D) : List ℚ)

/-- **The odd-degree transform leaves a ramified radicand** (`native_decide`): `∫ dx/√(x³)` transforms to
`ρ̃ = t` (the `t = 0` coefficient `ρ̃(0) = 0`), so `ỹ² = ρ̃` is ramified at `t = 0` — `ỹ = √t`, a Puiseux
(half-integer) place over ∞. This is the documented obstruction: the simple-pole residue resultant does
not extract an honest residue at a ramified place (the `even`-degree arcsinh/arccosh case is the resolved
one). The transformed radicand is exactly `[0, 1] = t`. -/
theorem oddInf_radicand_ramified :
    (radTransformAtInfinity oddInf_rho arcsinhInf_g0 arcsinhInf_g1 oddInf_D).1 = [0, 1] := by
  native_decide

/-! ### Restatement and axioms -/

/-- Restatement (the deliverable): the engine computes the **residue at infinity** of `∫ dx/√(x² + 1)`
— via the `x = 1/t` transform `radTransformAtInfinity` plus the **reused** eq. 7 norm localized at the
place `t = 0` — as `Z² − 1`, residues `±1`, the arcsinh log term. -/
example : cisZeroG (csubG
    (cResidueAtInfinityPlace 30 arcsinhInf_rho arcsinhInf_g0 arcsinhInf_g1 arcsinhInf_D) [-1, 0, 1])
    = true := by native_decide

#print axioms arcsinhInf_transform_eq
#print axioms arcsinhInf_residue_eq
#print axioms arcsinhInf_residue_theorem

end DeepWiki.SymbolicIntegration
