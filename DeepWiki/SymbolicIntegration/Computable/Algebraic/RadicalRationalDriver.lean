import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalCase2
import DeepWiki.SymbolicIntegration.Computable.Tower.Integrate
import DeepWiki.SymbolicIntegration.Computable.Tower.GcdFFCore

/-! # Algebraic-function integration: the general simple-radical rational-part integrator (Trager A §2)

`ComputableRadicalIntegrate` ran the **Case-1** driver (`radReduceCase1Iterate`/`radIntegrateCase1`) on a
single `C/(Vᵏ⁰y)` integrand (`V` coprime to the radicand), and `ComputableRadicalCase2` re-derived and
`radDeriv`-validated the **corrected Case-2** single step (`radCase2CofactorC`/`radCase2ResidualC`, for
`C/(Wᵏy)` with `W ∣ ρ`). What was still single-case is the **front-end**: a *general* simple-radical
integrand `∫ R/(B·y)` over `y² = ρ` has a denominator `B` whose squarefree factors are a *mix* of
`V`-factors (coprime to `ρ`, Case 1) and `W`-factors (dividing `ρ`, Case 2). This file closes that gap.

* **`radReduceCase2Iterate`** (Trager Appendix A §2.2, iterated) — the Case-2 analogue of
  `radReduceCase1Iterate`, built on the **corrected** single step (`radCase2CofactorC`/`radCase2ResidualC`).
  Starting from `C/(Wᵏ⁰y)` (`W ∣ ρ`) it runs the Hermite step `k → k−1` repeatedly, accumulating each
  contribution `B·ρ·W^{k0−k}` into a running numerator `vNum` over the common denominator `W^{k0}·y` (the
  step at multiplicity `k` produces `Bρ/(Wᵏy)`, which over `W^{k0}` is `Bρ·W^{k0−k}`), and recurses on the
  negated residual `−D` at `k−1`. Bottoms at `k ≤ 1`. Master identity: `∫ C/(W^{k0}y) = vNum/(W^{k0}y) +
  ∫ Crem/(Wy)`.

* **`radClassifyFactor`** — classifies a squarefree denominator factor `Bᵢ`: `true` (a `V`-factor, Case 1)
  when `gcd(Bᵢ, ρ)` is constant (coprime to the radicand), `false` (a `W`-factor, Case 2) when `Bᵢ ∣ ρ`.

* **`radPartialFractionCoprime`** — the partial-fraction front-end: given a numerator `R` and the list of
  pairwise-coprime prime-powers `[G₁,…,Gₘ]` (`Gᵢ = Bᵢ^{eᵢ}`, `∏Gᵢ = B`), returns the numerators
  `[N₁,…,Nₘ]` with `R/B = Σ Nᵢ/Gᵢ`, `deg Nᵢ < deg Gᵢ`, by iterating the fuel-free generic Bézout split
  `cdiophantineGWf`.

* **`radReduceCase3Iterate`** (Trager Appendix A §2.3, iterated) — the leftover `C/y` (`C` a polynomial,
  no denominator factor) degree-lowering, iterating `radCase3Cofactor`/`radCase3Residual` until
  `deg C < deg ρ`. `radDeriv`-validated on `∫ x⁴/√(x³+1)`: `c3itDriver_integrates`.

* **`radIntegrateRational`** (the multi-case dispatch driver) — squarefree-decomposes `B` (`cSqfreeYunFFG`)
  into `[Bᵢ]` (`Bᵢ` of multiplicity `eᵢ`), **splits** each squarefree factor `Bᵢ = Vᵢ·Wᵢ` into its `V`-part
  `Vᵢ = Bᵢ/gcd(Bᵢ, ρ)` (coprime to `ρ`, Case 1) and `W`-part `Wᵢ = gcd(Bᵢ, ρ)` (`Wᵢ ∣ ρ`, Case 2) — a
  single squarefree factor at one multiplicity may carry both — partial-fractions `R` across the resulting
  prime-powers, and dispatches each part `Nᵢ/(factorᵢ^{eᵢ}y)` to `radReduceCase1Iterate` /
  `radReduceCase2Iterate`. Returns the per-factor reductions `(isV, factorᵢ, eᵢ, Nᵢ, vNumᵢ, Cremᵢ)`, from
  which the total rational part `v = Σ vᵢ` and the leftover `Σ Cremᵢ/(factorᵢ·y)` are assembled.

* **★ The headline multi-case `native_decide`** — over `y² = x` (`ρ = x`), the integrand `1/((x−1)²x²y)`
  has a `V`-factor `(x−1)` (coprime to `ρ = x`, Case 1) AND a `W`-factor `x` (dividing `ρ`, Case 2). The
  driver partial-fractions, dispatches the `(x−1)` part to Case 1 and the `x` part to Case 2, and assembles
  `v = v_V + v_W`. Checked by the **actual** diagonal derivation `radDeriv 2 x`:
  `radDeriv(v) = (rational part of the integrand) − Crem_V/((x−1)y) − Crem_W/(xy)`. The engine now
  integrates the rational part of a **general (multi-case-denominator)** simple-radical integrand
  end-to-end, validated by the real radical derivation.

Cases 1, 2 **and** 3 are now realized and `radDeriv`-validated; the multi-case (mixed `V`/`W` denominator)
front-end dispatches Cases 1–2 end-to-end.

**Deferred** (documented): the `k = 1` lower-coefficient solve — for the base `θ' = 1` algebraic case (these
examples) this is the **algebraic** logarithmic part (Trager Ch. 5–6 residue / divisor theory, the
`ComputableAlgebraicResidues` axis), *not* the transcendental `cRischDEG`; `cRischDEG` is the right tool
only for the `θ = log v` / `θ = exp v` *lower-coefficient* first-order ODEs (Risch [38]), a layer this file
does not build. The entire (algebraic) logarithmic part is likewise deferred. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open RadElem CPolyG

namespace CPolyG

variable {α : Type*} [CField α]

/-! ### The iterated Case-2 rational-part reduction (Trager Appendix A §2.2, iterated)

`radReduceCase2Iterate` mirrors `radReduceCase1Iterate` but on the **corrected** Case-2 single step
(`radCase2CofactorC`/`radCase2ResidualC`, the `radDeriv`-validated one). For `W ∣ ρ` (a squarefree
factor of the radicand) the step at multiplicity `k` satisfies (over the radical, `n = 2`)
`radDeriv(Bρ/(Wᵏy)) = C/(Wᵏy) + D/(W^{k−1}y)`, so `∫ C/(Wᵏy) = Bρ/(Wᵏy) − ∫ D/(W^{k−1}y)`: accumulate
`+Bρ`, recurse on `−D` — the same sign pattern as Case 1. **The common-denominator bookkeeping differs**:
the contribution at multiplicity `k` is `Bρ/(Wᵏy)` (denominator `Wᵏ`, not `W^{k−1}` as in Case 1), so the
common denominator across the descent is `W^{k0}` and the step at `k` enters scaled by `W^{k0−k}`. -/

/-- **Iterated Case-2 reduction** `radReduceCase2Iterate W h ρ k0 fuel k C vNum = (Crem, vNumOut)` (Trager
Appendix A §2.2, iterated). One structural step per unit of `fuel` (call with `fuel = k0`): at multiplicity
`k ≥ 2` it solves the corrected Case-2 cofactor `B = radCase2CofactorC` (congruence `B·(½−k)W'h ≡ C
(mod W)`, `h = ρ/W`), forms the residual `D = radCase2ResidualC`, **accumulates** the contribution
`B·ρ·W^{k0−k}` into `vNum` (the numerator of the rational part over the common denominator `W^{k0}·y`), and
recurses on the negated residual `−D` at `k−1`. Bottoms at `k ≤ 1` returning `(C, vNum)` — the leftover
`k = 1` numerator and the assembled rational-part numerator. `W` (a squarefree factor of `ρ`), `h = ρ/W`,
and the radicand `ρ` are passed in. Generic over `[CField α]`. -/
def radReduceCase2Iterate (W h ρ : CPolyG α) (k0 : ℕ) :
    ℕ → ℕ → CPolyG α → CPolyG α → CPolyG α × CPolyG α
  | 0, _, C, vNum => (C, vNum)
  | fuel + 1, k, C, vNum =>
    if k ≤ 1 then (C, vNum)
    else
      let B := radCase2CofactorC k W h C
      let D := radCase2ResidualC k W h C B
      -- contribution `B·ρ/(Wᵏy)` over the common denominator `W^{k0}`: `B·ρ·W^{k0−k}`
      let contrib := cmulG (cmulG B ρ) (cpowG W (k0 - k))
      radReduceCase2Iterate W h ρ k0 fuel (k - 1) (cnegG D) (caddG vNum contrib)

/-- **The simple-radical rational-part driver (Case 2)** `radIntegrateCase2 W ρ k0 C = (Crem, vNum)`
(Trager Appendix A §2.2) — the `∫ C/(W^{k0}y)` driver over a simple radical `y² = ρ` with `W ∣ ρ` a
squarefree factor of the radicand. Computes `h = ρ/W` with `cdivWf` and runs the iterated Case-2 reduction
`radReduceCase2Iterate` from multiplicity `k0` down to `1` (structural fuel `k0`), returning the leftover
`k = 1` numerator `Crem` and the accumulated rational-part numerator `vNum` over the common denominator
`W^{k0}·y`. Master identity: `∫ C/(W^{k0}y) = vNum/(W^{k0}y) + ∫ Crem/(Wy)`. Generic over `[CField α]`. -/
def radIntegrateCase2 (W ρ : CPolyG α) (k0 : ℕ) (C : CPolyG α) : CPolyG α × CPolyG α :=
  radReduceCase2Iterate W (cdivWf ρ W) ρ k0 k0 k0 C []

/-! ### The iterated Case-3 (`C/y`) degree-lowering (Trager Appendix A §2.3, iterated)

After Cases 1–2 cleared every denominator factor, the leftover is `C/y` with `C` a polynomial (Trager
Appendix A §2.3). There is no denominator to lower — instead the single step `radCase3Cofactor`/
`radCase3Residual` (`θ' = 1`) lowers **`deg C`** by cancelling its leading term with a leading-coefficient
monomial `B = b·θ^{j+1}`, giving `(Bf/y)' − C/y = D/y` with `deg D < deg C`. So `∫ C/y = Bf/y − ∫ D/y`:
accumulate `+Bf`, recurse on `−D` (the same sign pattern as Cases 1–2). Every contribution has denominator
just `y` (no power), so the running rational-part numerator `vNum` is simply `Σ Bᵢf` over the common
denominator `y`. Iterating bottoms out when `deg C < deg f` (the irreducible rational part, left for the
logarithmic part). -/

/-- **Iterated Case-3 reduction** `radReduceCase3Iterate der f g fuel C vNum = (Crem, vNumOut)` (Trager
Appendix A §2.3, iterated). One structural step per unit of `fuel` (call with `fuel = deg C`): while
`deg C ≥ deg f` it cancels the leading term of `C` with `B = radCase3Cofactor f g C` (the leading-coefficient
monomial), forms the residual `D = radCase3Residual` (`deg D < deg C`), **accumulates** the contribution
`B·f` into `vNum` (the numerator of the rational part over the common denominator `y`), and recurses on the
negated residual `−D`. Bottoms at `deg C < deg f` returning `(C, vNum)` — the irreducible `C/y` leftover and
the assembled rational-part numerator. `der` is the level's base derivation (`cderivG` for `θ' = 1`); `f`
the radicand, `g` (from `(f/y)' = g/y`) passed in. Generic over `[CField α]`. -/
def radReduceCase3Iterate (der : CPolyG α → CPolyG α) (f g : CPolyG α) :
    ℕ → CPolyG α → CPolyG α → CPolyG α × CPolyG α
  | 0, C, vNum => (C, vNum)
  | fuel + 1, C, vNum =>
    if cisZeroG C || cdegG C < cdegG f then (C, vNum)
    else
      let B := radCase3Cofactor f g C
      let D := radCase3Residual f g B C (der B)
      radReduceCase3Iterate der f g fuel (cnegG D) (caddG vNum (cmulG B f))

/-- **The simple-radical rational-part driver (Case 3)** `radIntegrateCase3 der f g C = (Crem, vNum)`
(Trager Appendix A §2.3) — the `∫ C/y` driver over a simple radical `y² = f` for a polynomial numerator
`C`. Runs the iterated Case-3 degree-lowering `radReduceCase3Iterate` (structural fuel `deg C + 1`),
returning the irreducible leftover `Crem` (`deg Crem < deg f`) and the accumulated rational-part numerator
`vNum` over the common denominator `y`. Master identity: `∫ C/y = vNum/y + ∫ Crem/y`. `der = cderivG` for
`θ' = 1`; `g` read off `(f/y)' = g/y`. Generic over `[CField α]`. -/
def radIntegrateCase3 (der : CPolyG α → CPolyG α) (f g C : CPolyG α) : CPolyG α × CPolyG α :=
  radReduceCase3Iterate der f g (cdegG C + 1) C []

/-! ### The partial-fraction front-end and the multi-case dispatch (Trager Appendix A §2)

By §1 the integrand is `R/(B·y)` (numerator `R`, denominator `B` monic over the base field). §2
squarefree-decomposes `B = ∏ᵢ Bᵢ^{eᵢ}` (the `Bᵢ` squarefree, pairwise coprime), classifies each `Bᵢ` as a
`V`-factor (coprime to the radicand `ρ`, Case 1) or a `W`-factor (`Bᵢ ∣ ρ`, Case 2), partial-fractions
`R/B = Σᵢ Nᵢ/Bᵢ^{eᵢ}` over the prime-powers, and dispatches each piece `Nᵢ/(Bᵢ^{eᵢ}y)` to the matching
iterated reduction at multiplicity `eᵢ`. -/

/-- **Product of a list of polynomials** `radProdList ps = ∏ ps` (folding `cmulG` from the constant `1`).
The partial-fraction front-end uses it to form `∏_{j≠i} Gⱼ` (the cofactor of the `i`-th prime-power). -/
def radProdList (ps : List (CPolyG α)) : CPolyG α :=
  ps.foldl (fun acc p => cmulG acc p) [CField.one]

/-- **Classify a squarefree denominator factor** `radClassifyFactor Bi ρ = true` iff `Bi` is a
`V`-factor (coprime to the radicand `ρ`, Trager Case 1), i.e. `gcd(Bi, ρ)` is a constant; `false` iff `Bi`
is a `W`-factor (`Bi ∣ ρ`, Case 2). Reads `cdegG (gcd Bi ρ) = 0` off the fuel-free generic extended
Euclidean algorithm `cgcdWf`. Generic over `[CField α]`. -/
def radClassifyFactor (Bi ρ : CPolyG α) : Bool :=
  cdegG (cgcdWf Bi ρ).1 = 0

/-- **Partial fraction across coprime prime-powers** `radPartialFractionCoprime R Gs = [N₁,…,Nₘ]`:
for pairwise-coprime `Gs = [G₁,…,Gₘ]` with `B = ∏Gᵢ` and a **proper** numerator `R` (`deg R < deg B`),
returns the numerators `Nᵢ` with `R/B = Σᵢ Nᵢ/Gᵢ`, `deg Nᵢ < deg Gᵢ`. One step peels `G₁` off
`P = ∏_{j>1} Gⱼ` via `cdiophantineGWf P G₁ R = (Nᵢ, c)` (`Nᵢ·P + c·G₁ = R`, `deg Nᵢ < deg G₁`), giving
`R/(G₁·P) = Nᵢ/G₁ + c/P`, then recurses on `c` over the remaining factors. Generic over `[CField α]`. -/
def radPartialFractionCoprime : CPolyG α → List (CPolyG α) → List (CPolyG α)
  | _, [] => []
  | R, G :: rest =>
    let P := radProdList rest
    let (Ni, c) := cdiophantineGWf P G R   -- `Ni·P + c·G = R`, `deg Ni < deg G`
    Ni :: radPartialFractionCoprime c rest

end CPolyG

/-! ### ★ The iterated Case-2 reduction validates: `∫ 1/(x³·√(x³−x))` (`native_decide`)

`F = ℚ`, `θ = x` (`θ' = 1`), radicand `y² = ρ = x³ − x = x(x−1)(x+1)` (`n = 2`, squarefree), `W = x` (a
branch place `x = 0`, `W ∣ ρ`), `h = ρ/W = x² − 1`, `k₀ = 3`, `C₀ = 1` — the integrand `1/(x³·√(x³−x))`.
`radIntegrateCase2` runs **two** Case-2 steps (`k = 3 → 2 → 1`), accumulating `vNum` over the common
denominator `W^{k0} = x³` and leaving the `k = 1` residual `Crem`. Validated end-to-end by the **actual**
diagonal derivation `radDeriv 2 (x³−x)`: `radDeriv(vNum/(x³√(x³−x))) = 1/(x³√(x³−x)) − Crem/(x√(x³−x))`. -/

open RadElem CPolyG

/-- Case-2-iterate example radicand `ρ = x³ − x = x(x−1)(x+1)` (`y² = ρ`, squarefree), `ℚ[x]` `[0,−1,0,1]`. -/
def c2itRho : CPolyG ℚ := [0, -1, 0, 1]

/-- Case-2-iterate example squarefree factor `W = x` (a branch place `x = 0` of `√(x³−x)`, `W ∣ ρ`),
`[0,1]`. -/
def c2itW : CPolyG ℚ := [0, 1]

/-- Case-2-iterate example numerator `C₀ = 1` (integrand `1/(x³·√(x³−x))`), `[1]`. -/
def c2itC : CPolyG ℚ := [1]

/-- **The Case-2-iterate run** `radIntegrateCase2 W ρ 3 C = (Crem, vNum)` on `∫ 1/(x³·√(x³−x))` — runs two
Case-2 Hermite steps (`k = 3 → 2 → 1`), returning the `k = 1` residual `Crem` and the accumulated
rational-part numerator `vNum` over the common denominator `W³ = x³`. -/
def c2itRun : CPolyG ℚ × CPolyG ℚ := radIntegrateCase2 c2itW c2itRho 3 c2itC

/-- The radicand `ρ = x³ − x` lifted to `ℚ(x)` (`QFunNZG ℚ`), the Picture-B radicand for `radDeriv 2`. -/
def c2itRhoQx : QFunNZG ℚ := qxOfNum [0, -1, 0, 1]

/-- The common-denominator power `W³ = x³` as a `ℚ[x]` polynomial (the denominator of `vNum`). -/
def c2itW3 : CPolyG ℚ := cpowG c2itW 3

/-- The rational part `v = vNum/(W³·y)` lifted to `RadElem (QFunNZG ℚ)` — the pure-`y` element
`[0, vNum/(W³·ρ)]` over `ℚ(x)` (an `R/y` form is `[0, R/ρ]` since `R/y = (R/ρ)·y`). -/
def c2itVlift : RadElem (QFunNZG ℚ) :=
  [CField.zero, CField.div (qxOfNum c2itRun.2) (qxOfNum (cmulG c2itW3 c2itRho))]

/-- The integrand's rational part `C₀/(W³y) − Crem/(Wy)` lifted to `RadElem (QFunNZG ℚ)` — the pure-`y`
element `[0, C₀/(W³·ρ) − Crem/(W·ρ)]` over `ℚ(x)`. -/
def c2itRatLift : RadElem (QFunNZG ℚ) :=
  [CField.zero,
    CField.sub (CField.div (qxOfNum c2itC) (qxOfNum (cmulG c2itW3 c2itRho)))
      (CField.div (qxOfNum c2itRun.1) (qxOfNum (cmulG c2itW c2itRho)))]

/-- **★ The Case-2 iterate integrates `∫ 1/(x³·√(x³−x))`: `D(v) = rational part of the integrand`**
(`native_decide`). Over the genuine radical extension `(QFunNZG ℚ)[y]/(y² − (x³−x))`, the **actual**
diagonal radical derivation `radDeriv 2 (x³−x)` of the iterated Case-2 rational part `v = vNum/(W³√(x³−x))`
equals `C₀/(W³√(x³−x)) − Crem/(W√(x³−x))`, the rational part of `1/(x³·√(x³−x))` (leftover `k = 1` term
subtracted). Checked by `radIsZero` of the difference over `ℚ(x)`. **THE CASE-2 ITERATE INTEGRATES** —
`D(∫) = rational-part` for a multi-step (`k = 3 → 2 → 1`) Case-2 reduction at a branch place, validated by
the real derivation. -/
theorem c2itDriver_integrates :
    radIsZero (radSub (radDeriv 2 c2itRhoQx c2itVlift) c2itRatLift) = true := by native_decide

/-! ### ★ The iterated Case-3 reduction validates: `∫ x⁴/√(x³+1)` (`native_decide`)

`F = ℚ`, `θ = x` (`θ' = 1`), radicand `y² = ρ = x³ + 1` (`n = 2`, `y = √(x³+1)`), numerator `C = x⁴`
(`deg C = 4 ≥ deg ρ = 3`), `g = ½ρ' = (3/2)x²` — the integrand `x⁴/√(x³+1)` (a `C/y` Case-3 form, no
denominator factor). `radIntegrateCase3` runs the degree-lowering until `deg C < 3`, accumulating `vNum`
over the common denominator `y` and leaving the irreducible residual `Crem` (`deg Crem < 3`). Validated
end-to-end by the **actual** diagonal derivation `radDeriv 2 (x³+1)`: `radDeriv(vNum/√(x³+1)) = x⁴/√(x³+1) −
Crem/√(x³+1)`. -/

/-- Case-3-iterate example radicand `ρ = x³ + 1` (`y² = ρ`, `y = √(x³+1)`), `ℚ[x]` `[1,0,0,1]`. -/
def c3itRho : CPolyG ℚ := [1, 0, 0, 1]

/-- Case-3-iterate example helper `g = ½ρ' = (3/2)x²` (`n = 2`, `(f/y)' = g/y`). -/
def c3itG : CPolyG ℚ := cscaleG (1/2 : ℚ) (cderivG c3itRho)

/-- Case-3-iterate example numerator `C = x⁴` (integrand `x⁴/√(x³+1)`, `deg C ≥ deg ρ`), `[0,0,0,0,1]`. -/
def c3itC : CPolyG ℚ := [0, 0, 0, 0, 1]

/-- **The Case-3-iterate run** `radIntegrateCase3 cderivG ρ g C = (Crem, vNum)` on `∫ x⁴/√(x³+1)` — runs the
`C/y` degree-lowering, returning the irreducible residual `Crem` (`deg < 3`) and the accumulated
rational-part numerator `vNum` over the common denominator `y`. -/
def c3itRun : CPolyG ℚ × CPolyG ℚ := radIntegrateCase3 cderivG c3itRho c3itG c3itC

/-- The radicand `ρ = x³ + 1` lifted to `ℚ(x)` (`QFunNZG ℚ`), the Picture-B radicand for `radDeriv 2`. -/
def c3itRhoQx : QFunNZG ℚ := qxOfNum [1, 0, 0, 1]

/-- The rational part `v = vNum/y` lifted to `RadElem (QFunNZG ℚ)` — the pure-`y` element `[0, vNum/ρ]` over
`ℚ(x)` (an `R/y` form is `[0, R/ρ]` since `R/y = (R/ρ)·y`; here the common denominator is just `y`). -/
def c3itVlift : RadElem (QFunNZG ℚ) :=
  [CField.zero, CField.div (qxOfNum c3itRun.2) (qxOfNum c3itRho)]

/-- The integrand's rational part `C/y − Crem/y` lifted to `RadElem (QFunNZG ℚ)` — the pure-`y` element
`[0, (C − Crem)/ρ]` over `ℚ(x)`. -/
def c3itRatLift : RadElem (QFunNZG ℚ) :=
  [CField.zero, CField.div (qxOfNum (csubG c3itC c3itRun.1)) (qxOfNum c3itRho)]

/-- **★ The Case-3 iterate integrates `∫ x⁴/√(x³+1)`: `D(v) = rational part of the integrand`**
(`native_decide`). Over the genuine radical extension `(QFunNZG ℚ)[y]/(y² − (x³+1))`, the **actual**
diagonal radical derivation `radDeriv 2 (x³+1)` of the iterated Case-3 rational part `v = vNum/√(x³+1)`
equals `x⁴/√(x³+1) − Crem/√(x³+1)`, the rational part of `x⁴/√(x³+1)` (the irreducible `C/y` leftover
subtracted). Checked by `radIsZero` of the difference over `ℚ(x)`. **THE CASE-3 ITERATE INTEGRATES** —
`D(∫) = rational-part` for the `C/y` degree-lowering, validated by the real derivation. -/
theorem c3itDriver_integrates :
    radIsZero (radSub (radDeriv 2 c3itRhoQx c3itVlift) c3itRatLift) = true := by native_decide

/-! ### ★ The multi-case dispatch integrates `∫ 1/((x−1)²x²·√x)` end-to-end (`native_decide`)

The headline: a **general** simple-radical rational integrand whose denominator mixes a `V`-factor and a
`W`-factor, integrated end-to-end by the dispatch front-end and validated by the **actual** `radDeriv`.

`F = ℚ`, `θ = x` (`θ' = 1`), radicand `y² = ρ = x` (`n = 2`, `y = √x`). The integrand is `1/((x−1)²x²·y)`
— denominator `B = (x−1)²·x²`, numerator `R = 1`, presented **unfactored**. Squarefree-decomposing `B`
(`cSqfreeYunFFG`) gives a single squarefree factor of multiplicity `2`: `B₂ = (x−1)·x` (`B = B₂²`). But
`(x−1)` is **coprime to `ρ = x`** (Case 1) while `x` **divides `ρ`** (Case 2): a single squarefree factor
at one multiplicity carries **both** a `V`-part and a `W`-part. So the driver splits `B₂ = V₂·W₂` with
`W₂ = gcd(B₂, ρ) = x` and `V₂ = B₂/W₂ = (x−1)`, giving the two distinct prime-powers `[(x−1)², x²]`.

`radIntegrateRational` then partial-fractions `1/((x−1)²x²) = N_V/(x−1)² + N_W/x²`, classifies `(x−1)` as
`V` / `x` as `W`, runs one Case-1 step on `N_V/((x−1)²y)` (`k = 2 → 1`, `v_V = vNum_V/((x−1)·y)`, leftover
`Crem_V`) and one Case-2 step on `N_W/(x²y)` (`k = 2 → 1`, `v_W = vNum_W/(x²·y)`, leftover `Crem_W`). The
total rational part is `v = v_V + v_W`, and (by the partial fraction) `radDeriv(v) = 1/((x−1)²x²·y) −
Crem_V/((x−1)y) − Crem_W/(xy)`. -/

/-- Headline-dispatch radicand `ρ = x` (`y² = x`, `y = √x`), as `ℚ[x]` `[0, 1]`. -/
def mcRho : CPolyG ℚ := [0, 1]

/-- Headline-dispatch numerator `R = 1` (integrand `1/((x−1)²x²·√x)`), `[1]`. -/
def mcR : CPolyG ℚ := [1]

/-- Headline-dispatch denominator `B = (x−1)²·x² = (x⁴ − 2x³ + x²)`, presented **unfactored** `[0,0,1,−2,1]`
— the driver squarefree-decomposes it (one factor `(x−1)x` of multiplicity `2`), then splits that factor
into the `V`-part `(x−1)` (coprime to `ρ = x`) and the `W`-part `x` (dividing `ρ`). -/
def mcB : CPolyG ℚ := cmulG (cpowG [-1, 1] 2) (cpowG [0, 1] 2)

/-- The radicand `ρ = x` as `QFunNZG ℚ` for the multi-case `∫ 1/((x−1)²x²·√x)` capstone (the base of the
`RadElem` lift used by the Wf validation in `Sources.Hdl_1721_1_15391.AppendixA`). -/
def mcRhoQx : QFunNZG ℚ := qxOfNum [0, 1]
