import DeepWiki.SymbolicIntegration.Compute.LogToAtan
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms.RothsteinTrager.RtResultant

/-! # Computable Rothstein–Trager resultant over `ℚ`
A `#eval`-able rendering of the resultant `R(t) = res_x(D, A − t·D')` on the carrier
`CPoly := List ℚ`: a univariate `cresultant` via the Euclidean polynomial-remainder-sequence, then
`R(t)` recovered by evaluation and Lagrange interpolation (`cinterpolate`). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace Compute

/-! ### Computable derivative on `CPoly` -/

/-- Coefficient-shift derivative `cderiv [a₀,a₁,a₂,…] = [a₁, 2a₂, 3a₃, …]`. -/
def cderiv : CPoly → CPoly
  | [] => []
  | _ :: as => go 1 as
where
  /-- From degree `k`, emit `k·a` for each coefficient `a` (the derivative tail). -/
  go : ℕ → CPoly → CPoly
  | _, [] => []
  | k, a :: as => ((k : ℚ) * a) :: go (k + 1) as

/-- `toPoly (cderiv p) = derivative (toPoly p)`: `cderiv` realizes the `ℚ[X]` derivative. -/
theorem toPoly_cderiv (p : CPoly) : toPoly (cderiv p) = derivative (toPoly p) := by
  -- Generalize the starting degree: `toPoly (cderiv.go k as) = derivative (X * toPoly_at_degree)`…
  -- A direct two-list induction with the index threaded through is cleanest.
  suffices h : ∀ (as : CPoly) (k : ℕ),
      toPoly (cderiv.go k as) = (k : ℚ[X]) * toPoly as + X * derivative (toPoly as) by
    cases p with
    | nil => simp [cderiv]
    | cons a as =>
      show toPoly (cderiv.go 1 as) = derivative (toPoly (a :: as))
      rw [h as 1, toPoly_cons, derivative_add, derivative_C, derivative_mul, derivative_X]
      push_cast; ring
  intro as
  induction as with
  | nil => intro k; simp [cderiv.go]
  | cons b bs ih =>
    intro k
    show toPoly (((k : ℚ) * b) :: cderiv.go (k + 1) bs) = _
    rw [toPoly_cons, ih (k + 1), toPoly_cons, derivative_add, derivative_C, derivative_mul,
      derivative_X, map_mul, map_natCast]
    push_cast; ring

/-! ### Computable univariate resultant on `CPoly` (Euclidean-PRS route) -/

/-- Degree of a `CPoly` as a `ℕ`: `cdeg p = (length of normalized p) − 1`, with `cdeg 0 = 0`. -/
def cdeg (p : CPoly) : ℕ := (cnorm p).length - 1

/-- Power of a rational `c^n`, by `ℕ`-recursion. -/
def cpow (c : ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => c * cpow c n

/-- Computable univariate resultant `cresultant fuel p q = res_x(p, q) ∈ ℚ`, fuel-bounded, via the
Euclidean polynomial-remainder-sequence identity
`res(p,q) = (−1)^(deg p·deg q)·lc(q)^(deg p − deg r)·res(q, r)` with `r = p mod q`. -/
def cresultant : ℕ → CPoly → CPoly → ℚ
  | 0, _, _ => 0
  | fuel + 1, p, q =>
    let p := cnorm p
    let q := cnorm q
    if cisZero q then
      -- `res(p, 0)`: `1` if `p` is also constant (degree 0), else `0`.
      if p.length ≤ 1 then 1 else 0
    else if q.length ≤ 1 then
      -- `q = c` constant: `res(p, c) = c^(deg p)`.
      cpow (clead q) (cdeg p)
    else if p.length < q.length then
      -- `deg p < deg q`: swap, picking up the sign `(−1)^(deg p · deg q)`.
      let s := cpow (-1) (cdeg p * cdeg q)
      s * cresultant fuel q p
    else
      let r := cnorm (cmod (fuel + 1) p q)
      let sign := cpow (-1) (cdeg p * cdeg q)
      let lcpow := cpow (clead q) (cdeg p - cdeg r)
      sign * lcpow * cresultant fuel q r

/-! ### Computable Lagrange interpolation on `CPoly` -/

/-- Constant `CPoly` `cC c = [c]`, normalized to `[]` when `c = 0`. -/
def cC (c : ℚ) : CPoly := cnorm [c]

/-- Lagrange basis numerator `∏_{j} (x − xⱼ)` over the sample abscissas `xs`. -/
def clagNum : List ℚ → CPoly
  | [] => [1]
  | x :: xs => cmul [(-x), 1] (clagNum xs)

/-- Lagrange interpolation `cinterpolate pts = R(t)` with `R(xₖ) = yₖ` for each `(xₖ, yₖ) ∈ pts`
(distinct abscissas over `ℚ`): `∑ₖ yₖ · ∏_{j≠k}(t − xⱼ)/(xₖ − xⱼ)`. -/
def cinterpolate (pts : List (ℚ × ℚ)) : CPoly :=
  let xs := pts.map Prod.fst
  let term : ℚ × ℚ → CPoly := fun (xk, yk) =>
    let others := xs.filter (· != xk)
    let num := clagNum others
    let denom := others.foldl (fun acc xj => acc * (xk - xj)) 1
    cscale (yk / denom) num
  cnorm (pts.foldl (fun acc p => cadd acc (term p)) [])

/-! ### The Rothstein–Trager resultant `R(t) = res_x(D, A − t·D')` -/

/-- Computable Rothstein–Trager resultant `rtResultantCompute fuel A D = R(t) = res_x(D, A − t·D')`,
returned as a `CPoly` in `t`, computed by sampling and Lagrange interpolation. -/
def rtResultantCompute (fuel : ℕ) (A D : CPoly) : CPoly :=
  let D' := cderiv D
  let n := cdeg D  -- `deg_t R ≤ deg_x D = n`, so `n + 1` sample points determine `R`.
  let pts : List (ℚ × ℚ) := (List.range (n + 1)).map (fun k =>
    let a : ℚ := (k : ℚ)
    let Aa := csub A (cscale a D')
    (a, cresultant fuel D Aa))
  cinterpolate pts

/-! ### Squarefree (primitive) part -/

/-- Make a `CPoly` monic (lead coefficient `1`) by dividing through by its leading coefficient; the
zero polynomial stays `[]`. -/
def cmonic (p : CPoly) : CPoly :=
  let p := cnorm p
  if cisZero p then [] else cscale (clead p)⁻¹ p

/-- Squarefree part of a `CPoly` over `ℚ`, made monic: `csqfreePart fuel p = monic(p / gcd(p, p'))`,
the radical of `p`. -/
def csqfreePart (fuel : ℕ) (p : CPoly) : CPoly :=
  let p := cnorm p
  let (g, _, _) := cgcdExt fuel p (cderiv p)
  cmonic (cdiv fuel p g)

/-! ### Bridge back to `ℚ[X]` and agreement
`toPoly (cresultant …)` agrees with Mathlib's `Polynomial.resultant` and
`toPoly (rtResultantCompute …)` with the noncomputable `rtResultant`, proven in `Correctness` and
`RtResultantCorrectness`. -/

/-- Agreement `Prop`: up to a nonzero scalar, `toPoly (rtResultantCompute fuel A D)` equals
`rtResultant (toPoly A) (toPoly D)`. -/
def rtResultantCompute_agrees_statement : Prop :=
  ∀ (A D : CPoly) (fuel : ℕ), ∃ c : ℚ, c ≠ 0 ∧
    toPoly (rtResultantCompute fuel A D)
      = Polynomial.C c * rtResultant (toPoly A) (toPoly D)

end Compute

end DeepWiki.SymbolicIntegration
