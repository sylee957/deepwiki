import DeepWiki.SymbolicIntegration.Engine.Algebraic.DivisorOrder

/-! # A lightweight general-torsion ceiling by point counting over `𝔽_p`

The good-reduction torsion ceiling for an arbitrary plane curve via direct point counting over `𝔽_p`, a
lightweight alternative to the fractional-ideal order machinery (which is too heavy to
`native_decide`-compile). The `ℚ`-torsion of `Pic⁰(C)` injects into `Pic⁰(C)(𝔽_p)` at every good prime,
whose order for genus 1 is the point count `N_p = #C(𝔽_p)`, so the torsion order divides `gcd_p N_p`. The
count scans the affine `𝔽_p²` grid testing `f(x, y) = 0` (pure `ZMod p` ring arithmetic) and adds the
points at infinity; `torsionCeiling` is the `gcd` over good primes. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace CPolyG

/-! ## Bivariate evaluation over `𝔽_p` (`ZMod p` ring arithmetic)

A plane curve `f(x, y) = Σᵢ fᵢ(x)·yⁱ` is a list of univariate coefficient-polynomials; evaluating at
`(x₀, y₀)` is two nested Horner folds over `[CommRing R]`, so `ZMod p` works for every `p`. -/

variable {R : Type*} [CommRing R]

/-- Univariate Horner evaluation `evalUniR p c = p(c)` of a `List R` (dense, low→high) at `c ∈ R`, via
`R`'s `+`/`*` only. -/
def evalUniR (p : List R) (c : R) : R :=
  p.foldr (fun coeff acc => coeff + c * acc) 0

/-- Bivariate Horner evaluation `curveEval2 f x₀ y₀ = f(x₀, y₀)` of `f = Σᵢ fᵢ(x)·yⁱ`: evaluate each
`fᵢ(x₀)` (`evalUniR`), then Horner-fold in `y₀`. -/
def curveEval2 (f : List (List R)) (x0 y0 : R) : R :=
  (f.map (fun fi => evalUniR fi x0)).foldr (fun coeff acc => coeff + y0 * acc) 0

/-- On-curve test `onCurve2 f x₀ y₀`: `true` iff `f(x₀, y₀) = 0`. -/
def onCurve2 [DecidableEq R] (f : List (List R)) (x0 y0 : R) : Bool :=
  decide (curveEval2 f x0 y0 = 0)

end CPolyG

/-! ## Affine point counting over `𝔽_p`

`countAffinePoints p f = #{(x, y) ∈ 𝔽_p² : f(x, y) = 0}`, by scanning the `p × p` grid of `𝔽_p`-points
and counting the on-curve ones. -/

open CPolyG

/-- The `𝔽_p` grid `zmodGrid p = [0, 1, …, p−1] : List (ZMod p)`, the scan domain for the point count. -/
def zmodGrid (p : ℕ) : List (ZMod p) := (List.range p).map (fun k => (k : ZMod p))

/-- Affine point count `countAffinePoints p f = #{(x, y) ∈ 𝔽_p² : f(x, y) = 0}` of the plane curve
`f = Σᵢ fᵢ(x)·yⁱ`, by a double scan over `zmodGrid p` testing `onCurve2`. -/
def countAffinePoints (p : ℕ) (f : List (List (ZMod p))) : ℕ :=
  ((zmodGrid p).foldl (fun accx x =>
    accx + (zmodGrid p).foldl (fun accy y =>
      accy + (if onCurve2 f x y then 1 else 0)) 0) 0)

/-! ## Points at infinity, and `N_p = |Pic⁰(C)(𝔽_p)|` (genus 1)

The number of points at infinity is read from the curve's leading form: a smooth plane cubic (e.g. Fermat
`x³ + y³ = 1`) has the cube roots of `−1` at infinity; a hyperelliptic `y² = ρ(x)` with `deg ρ` odd has
exactly one. `N_p` is the affine count plus these. -/

/-- Points at infinity of a Fermat-type cubic `countInfCubeRootsNegOne p = #{ t ∈ 𝔽_p : t³ + 1 = 0 }`,
the cube roots of `−1` in `𝔽_p` (the points `[1 : t : 0]` where the leading form `X³ + Y³` vanishes). -/
def countInfCubeRootsNegOne (p : ℕ) : ℕ :=
  (zmodGrid p).foldl (fun acc t => acc + (if t ^ 3 + 1 = 0 then 1 else 0)) 0

/-- `N_p` of a Fermat-type cubic `npFermatCubic p f = (affine count) + (#points at ∞)` =
`|Pic⁰(C)(𝔽_p)|` for the genus-1 cubic `f`. -/
def npFermatCubic (p : ℕ) (f : List (List (ZMod p))) : ℕ :=
  countAffinePoints p f + countInfCubeRootsNegOne p

/-- `N_p` of a hyperelliptic curve with one point at infinity `npHypOddDeg p f = (affine count) + 1` =
`|Jac(C)(𝔽_p)|` for the genus-1 curve `y² = ρ(x)`, `deg ρ` odd. -/
def npHypOddDeg (p : ℕ) (f : List (List (ZMod p))) : ℕ :=
  countAffinePoints p f + 1

/-! ## The good-reduction torsion ceiling `gcd_p N_p`

The `ℚ`-torsion order divides `|Pic⁰(C)(𝔽_p)|` at every good prime, so its exponent divides `gcd_p N_p`,
read straight off the point counts. -/

/-- The good-reduction torsion ceiling `torsionCeiling nps = gcd_p N_p` over a list `nps` of good-prime
point counts. (`gcd` of the empty list is `0`; supply at least two good primes.) -/
def torsionCeiling (nps : List ℕ) : ℕ := nps.foldr Nat.gcd 0

end DeepWiki.SymbolicIntegration

/-! ## The non-hyperelliptic Fermat cubic `x³ + y³ = 1`

The Fermat cubic is a smooth genus-1 plane curve, not a hyperelliptic model, with rational torsion `ℤ/3`.
Its point counts over `p = 5, 7, 11, 13` are `6, 9, 12, 9`, with `gcd = 3` pinning the `ℚ`-torsion order
to `3` in pure `ZMod p` arithmetic. -/

namespace DeepWiki.SymbolicIntegration

open CPolyG

/-- The non-hyperelliptic Fermat cubic `f(x, y) = x³ + y³ − 1` over `𝔽_p`, as the `y`-coefficient list
`[x³ − 1, 0, 0, 1]`. Genus 1, rational torsion `ℤ/3`. -/
def fermatCubic (p : ℕ) : List (List (ZMod p)) := [[-1, 0, 0, 1], [], [], [1]]

/-- The Fermat-cubic point counts `N_p = 6, 9, 12, 9` over `p = 5, 7, 11, 13`:
`npFermatCubic p (fermatCubic p) = |Pic⁰(C)(𝔽_p)|` for `x³ + y³ = 1`. -/
theorem fermatCubic_Np :
    (npFermatCubic 5 (fermatCubic 5), npFermatCubic 7 (fermatCubic 7),
      npFermatCubic 11 (fermatCubic 11), npFermatCubic 13 (fermatCubic 13)) = (6, 9, 12, 9) := by
  native_decide

/-- The Fermat-cubic torsion ceiling is `3`: `torsionCeiling [N₅, N₇, N₁₁, N₁₃] = gcd(6, 9, 12, 9) = 3`,
pinning the `ℚ`-torsion order of `x³ + y³ = 1` to its rational `ℤ/3`. -/
theorem fermatCubic_torsionCeiling_eq3 :
    torsionCeiling [npFermatCubic 5 (fermatCubic 5), npFermatCubic 7 (fermatCubic 7),
      npFermatCubic 11 (fermatCubic 11), npFermatCubic 13 (fermatCubic 13)] = 3 := by
  native_decide

/-- Every good prime forces `3 ∣ N_p` for the Fermat cubic: over `p = 5, 7, 11, 13, 17, 19, 31` each
`N_p mod 3` is `0`, the fingerprint of the persistent rational `ℤ/3` torsion. -/
theorem fermatCubic_three_divides_Np :
    (npFermatCubic 5 (fermatCubic 5) % 3, npFermatCubic 7 (fermatCubic 7) % 3,
      npFermatCubic 11 (fermatCubic 11) % 3, npFermatCubic 13 (fermatCubic 13) % 3,
      npFermatCubic 17 (fermatCubic 17) % 3, npFermatCubic 19 (fermatCubic 19) % 3,
      npFermatCubic 31 (fermatCubic 31) % 3) = (0, 0, 0, 0, 0, 0, 0) := by
  native_decide

/-! ## Hyperelliptic conservativity: the ceiling reproduces the Cantor torsion data

The same point count, on the hyperelliptic curves the Mumford/Cantor engine handles, recovers their
torsion orders: `y² = x³ + 1` (torsion `ℤ/6`) gives `gcd_p N_p = 6`, and `y² = x³ − 2` (trivial torsion)
gives `1`. -/

/-- The hyperelliptic curve `y² = x³ + 1` over `𝔽_p` as the `y`-coefficient list `[x³ + 1, 0, −1]`;
torsion `ℤ/6`. -/
def hypCurveX3p1 (p : ℕ) : List (List (ZMod p)) := [[1, 0, 0, 1], [], [-1]]

/-- The hyperelliptic curve `y² = x³ − 2` over `𝔽_p` as `[x³ − 2, 0, −1]`; trivial torsion. -/
def hypCurveX3m2 (p : ℕ) : List (List (ZMod p)) := [[-2, 0, 0, 1], [], [-1]]

/-- Hyperelliptic conservativity, `ℤ/6` case: `gcd_p N_p = 6` for `y² = x³ + 1`, from
`N_p = 6, 12, 12, 12, 18` over `p = 5, 7, 11, 13, 17`. -/
theorem hypCurveX3p1_torsionCeiling_eq6 :
    torsionCeiling [npHypOddDeg 5 (hypCurveX3p1 5), npHypOddDeg 7 (hypCurveX3p1 7),
      npHypOddDeg 11 (hypCurveX3p1 11), npHypOddDeg 13 (hypCurveX3p1 13),
      npHypOddDeg 17 (hypCurveX3p1 17)] = 6 := by
  native_decide

/-- Hyperelliptic conservativity, trivial-torsion case: `gcd_p N_p = 1` for `y² = x³ − 2`, from
`N_p = 6, 7, 12, 19` over `p = 5, 7, 11, 13` — no rational torsion. -/
theorem hypCurveX3m2_torsionCeiling_eq1 :
    torsionCeiling [npHypOddDeg 5 (hypCurveX3m2 5), npHypOddDeg 7 (hypCurveX3m2 7),
      npHypOddDeg 11 (hypCurveX3m2 11), npHypOddDeg 13 (hypCurveX3m2 13)] = 1 := by
  native_decide

/-- The `𝔽_p` point-count torsion ceiling computes the Fermat and hyperelliptic sample ceilings. -/
theorem lightweight_general_torsion_validates :
    -- the non-hyperelliptic Fermat cubic: torsion ceiling 3
    (npFermatCubic 5 (fermatCubic 5), npFermatCubic 7 (fermatCubic 7),
        npFermatCubic 11 (fermatCubic 11), npFermatCubic 13 (fermatCubic 13)) = (6, 9, 12, 9)
    ∧ torsionCeiling [npFermatCubic 5 (fermatCubic 5), npFermatCubic 7 (fermatCubic 7),
        npFermatCubic 11 (fermatCubic 11), npFermatCubic 13 (fermatCubic 13)] = 3
    -- hyperelliptic conservativity: ℤ/6 and trivial torsion
    ∧ torsionCeiling [npHypOddDeg 5 (hypCurveX3p1 5), npHypOddDeg 7 (hypCurveX3p1 7),
        npHypOddDeg 11 (hypCurveX3p1 11), npHypOddDeg 13 (hypCurveX3p1 13),
        npHypOddDeg 17 (hypCurveX3p1 17)] = 6
    ∧ torsionCeiling [npHypOddDeg 5 (hypCurveX3m2 5), npHypOddDeg 7 (hypCurveX3m2 7),
        npHypOddDeg 11 (hypCurveX3m2 11), npHypOddDeg 13 (hypCurveX3m2 13)] = 1 := by
  native_decide

end DeepWiki.SymbolicIntegration
