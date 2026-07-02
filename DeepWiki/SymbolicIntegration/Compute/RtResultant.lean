import DeepWiki.SymbolicIntegration.Compute.LogToAtan
import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms

/-! # Computable Rothstein–Trager resultant over `ℚ` (Bronstein §2.4, Example 2.4.1, p.47–48)
The noncomputable `rtResultant A D = res_x(D, A − t·D') ∈ ℚ[t]` (in
`DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms`) is the heart of the Rothstein–Trager /
LRT logarithmic part — its roots are the residues. Mathlib's `ℚ[X]` resultant is **noncomputable**
(`Polynomial.resultant` over the noncomputable `ℚ[X]` arithmetic), so it cannot `#eval`. Here we give a
genuinely **computable**, `#eval`-able rendering on the dense coefficient carrier `CPoly := List ℚ`
(from `LogToAtanCompute`): a univariate `cresultant` via the **Euclidean polynomial-remainder-sequence**
identity `res(p,q) = (−1)^(deg p·deg q)·lc(q)^(deg p − deg r)·res(q, r)` with `r = p mod q`, bottoming
out at `res(p, c) = c^(deg p)` for constant `c`. The bivariate Rothstein–Trager resultant `R(t) =
res_x(D, A − t·D')` is recovered, staying in univariate `CPoly`, by **evaluation + Lagrange
interpolation**: sample `R(aₖ) = cresultant D (A − aₖ·D')` at `aₖ = k` for `k = 0,…,deg D` and
interpolate (`cinterpolate`). We `#eval`/`native_decide` it on **Example 2.4.1**
`A = x⁴−3x²+6, D = x⁶−5x⁴+5x²+4`, recovering the book's `R(t) = 4t²+1` up to a nonzero rational scalar.
`cderiv` is the computable coefficient-shift derivative; everything reuses `LogToAtanCompute`'s `CPoly`
algebra and the `toPoly : CPoly → ℚ[X]` bridge. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace Compute

/-! ### Computable derivative on `CPoly` -/

/-- **Coefficient-shift derivative** `cderiv [a₀,a₁,a₂,…] = [a₁, 2a₂, 3a₃, …]`: differentiates a
`CPoly` by multiplying each coefficient by its degree and dropping the constant term. -/
def cderiv : CPoly → CPoly
  | [] => []
  | _ :: as => go 1 as
where
  /-- Auxiliary: from degree `k`, emit `k·a` for each coefficient `a` (the derivative tail). -/
  go : ℕ → CPoly → CPoly
  | _, [] => []
  | k, a :: as => ((k : ℚ) * a) :: go (k + 1) as

/-- `toPoly (cderiv p) = derivative (toPoly p)`: `cderiv` realizes the `ℚ[X]` derivative under the
Horner bridge. -/
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

/-- **Degree** of a `CPoly` as a `ℕ`: `cdeg p = (length of normalized p) − 1`, with `cdeg 0 = 0`
(treated together with `cisZero` at the call sites). -/
def cdeg (p : CPoly) : ℕ := (cnorm p).length - 1

/-- **Power** of a rational `c^n` (computable, by `ℕ`-recursion). -/
def cpow (c : ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => c * cpow c n

/-- **Computable univariate resultant** `cresultant fuel p q = res_x(p, q) ∈ ℚ`, fuel-bounded, via the
Euclidean polynomial-remainder-sequence identity. With `r = p mod q`, `dp = deg p`, `dq = deg q`,
`dr = deg r`: `res(p,q) = (−1)^(dp·dq) · lc(q)^(dp − dr) · res(q, r)`, bottoming out at `res(p, c) =
c^(deg p)` for a *constant* `q = c` and `res(p, 0) = 0` when `deg p > 0` (`= 1` when `p` is also
constant). One step suffices per degree drop, so `fuel ≥ deg p + deg q` is safe. -/
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

/-- **Constant `CPoly`** `cC c = [c]` (degree-0 polynomial), normalized to `[]` when `c = 0`. -/
def cC (c : ℚ) : CPoly := cnorm [c]

/-- **Lagrange basis numerator** `∏_{j≠i} (x − xⱼ)` over the sample abscissas `xs`, skipping index `i`'s
abscissa value `xi` once (so it must be called with the `i`-th abscissa removed, or guarded by `xi`). -/
def clagNum : List ℚ → CPoly
  | [] => [1]
  | x :: xs => cmul [(-x), 1] (clagNum xs)

/-- **Lagrange interpolation** `cinterpolate pts = R(t)` with `R(xₖ) = yₖ` for each `(xₖ, yₖ) ∈ pts`
(distinct abscissas, over the field `ℚ`): `∑ₖ yₖ · ∏_{j≠k}(t − xⱼ)/(xₖ − xⱼ)`, built in `CPoly` via
`cmul`/`cadd`/`cscale` (the scalar `1/∏(xₖ − xⱼ)` is a `ℚ` inverse — `ℚ` is a field). -/
def cinterpolate (pts : List (ℚ × ℚ)) : CPoly :=
  let xs := pts.map Prod.fst
  let term : ℚ × ℚ → CPoly := fun (xk, yk) =>
    let others := xs.filter (· != xk)
    let num := clagNum others
    let denom := others.foldl (fun acc xj => acc * (xk - xj)) 1
    cscale (yk / denom) num
  cnorm (pts.foldl (fun acc p => cadd acc (term p)) [])

/-! ### The Rothstein–Trager resultant `R(t) = res_x(D, A − t·D')` -/

/-- **Computable Rothstein–Trager resultant** `rtResultantCompute fuel A D = R(t) = res_x(D, A − t·D')
∈ ℚ[t]`, returned as a `CPoly` in `t`. Since `deg_t R ≤ deg D`, it is computed by **evaluation +
Lagrange interpolation**: for `aₖ = k`, `k = 0,…,deg D`, sample `R(aₖ) = cresultant fuel D (A − aₖ·D')`
(with `D' = cderiv D`, `A − aₖ·D'` a `CPoly` via `csub`/`cscale`), then interpolate the points
`(aₖ, R(aₖ))`. This stays entirely in univariate `CPoly`. -/
def rtResultantCompute (fuel : ℕ) (A D : CPoly) : CPoly :=
  let D' := cderiv D
  let n := cdeg D  -- `deg_t R ≤ deg_x D = n`, so `n + 1` sample points determine `R`.
  let pts : List (ℚ × ℚ) := (List.range (n + 1)).map (fun k =>
    let a : ℚ := (k : ℚ)
    let Aa := csub A (cscale a D')
    (a, cresultant fuel D Aa))
  cinterpolate pts

/-! ### Squarefree (primitive) part — recovers the book's `R = 4t²+1` -/

/-- **Make a `CPoly` monic** (lead coefficient `1`) by dividing through by its leading coefficient;
the zero polynomial stays `[]`. -/
def cmonic (p : CPoly) : CPoly :=
  let p := cnorm p
  if cisZero p then [] else cscale (clead p)⁻¹ p

/-- **Squarefree part** of a `CPoly` over `ℚ`, made monic: `csqfreePart fuel p = monic(p / gcd(p, p'))`,
the radical of `p` (each irreducible factor with multiplicity 1). For the Example 2.4.1 resultant
`45796·(4t²+1)³` this returns `t² + 1/4` = monic `4t²+1`. -/
def csqfreePart (fuel : ℕ) (p : CPoly) : CPoly :=
  let p := cnorm p
  let (g, _, _) := cgcdExt fuel p (cderiv p)
  cmonic (cdiv fuel p g)

/-! ### Bridge back to `ℚ[X]` and agreement — PROVEN in `ComputeCorrectness`/`RtResultantCorrectness`
`toPoly (cresultant …)` agrees with Mathlib's `Polynomial.resultant` on all inputs
(`ComputeCorrectness.cresultant_eq`, via the Euclidean-PRS toolkit `resultant_comm`/
`resultant_add_mul_right`/`resultant_add_right_deg` with the §2.4 formal-vs-actual degree
reconciliation), and `toPoly (rtResultantCompute …)` equals the noncomputable bivariate resultant
`rtResultant` (`RtResultantCorrectness.toPoly_rtResultantCompute_eq_rtResultant`, for monic `D` and
`deg A < deg D`): both have degree `< deg D + 1` and agree at the `deg D + 1` integer nodes
(`cinterpolate` correctness `toPoly_cinterpolate_eval` + the column-degree bound
`natDegree_rtResultant_le`), hence are equal by `Lagrange.eq_of_degrees_lt_of_eval_index_eq`. The
`native_decide` computation on Example 2.4.1 (`rtResultant_ex241`, `rtResultant_ex241_normalized`)
remains as a concrete witness. -/

/-- **Agreement with the noncomputable `rtResultant` — PROVEN.** Under the `toPoly` bridge, the
computable `rtResultantCompute` equals the noncomputable `DeepWiki.SymbolicIntegration.rtResultant`
(exactly, for monic `D` and `deg A < deg D`): see
`RtResultantCorrectness.toPoly_rtResultantCompute_eq_rtResultant`. This `Prop` records the general
up-to-scalar form; the exact equality under the natural hypotheses is the stronger proven statement. -/
def rtResultantCompute_agrees_statement : Prop :=
  ∀ (A D : CPoly) (fuel : ℕ), ∃ c : ℚ, c ≠ 0 ∧
    toPoly (rtResultantCompute fuel A D)
      = Polynomial.C c * rtResultant (toPoly A) (toPoly D)

end Compute

end DeepWiki.SymbolicIntegration
