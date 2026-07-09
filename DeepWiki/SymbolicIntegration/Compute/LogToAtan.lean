import DeepWiki.SymbolicIntegration.RiobooLogToAtan
import DeepWiki.ComputableAlgebra.GenericPolyEngine

/-! # Computable `LogToAtan` over `ℚ`
An executable rendering of the `LogToAtan` algorithm on the dense coefficient carrier
`CPolyQ := List ℚ`, with a `toPoly : CPolyQ → ℚ[X]` bridge back to the `ℚ[X]`-level theory. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace Compute

/-- Dense coefficient list over `ℚ` (index = degree, low to high): `CPolyQ := CPolyG ℚ`, the
computable polynomial carrier (defeq to `List ℚ`). -/
abbrev CPolyQ := CPolyG ℚ

/-- Normalize a `CPolyQ` by stripping trailing (high-degree) zero coefficients (zero polynomial
becomes `[]`). -/
def cnorm : CPolyQ → CPolyQ := CPolyG.cnormG

/-- Coefficientwise addition of two `CPolyQ`s (the shorter is zero-extended implicitly). -/
def cadd : CPolyQ → CPolyQ → CPolyQ := CPolyG.caddG

/-- Negation of a `CPolyQ`, coefficientwise. -/
def cneg (p : CPolyQ) : CPolyQ := CPolyG.cnegG p

/-- Subtraction of `CPolyQ`s, `p − q := p + (−q)`. -/
def csub (p q : CPolyQ) : CPolyQ := cadd p (cneg q)

/-- Scalar multiplication of a `CPolyQ` by `c : ℚ`, coefficientwise. -/
def cscale (c : ℚ) (p : CPolyQ) : CPolyQ := CPolyG.cscaleG c p

/-- Degree shift `cshift k p = x^k · p`: prepend `k` zero coefficients. -/
def cshift : ℕ → CPolyQ → CPolyQ := CPolyG.cshiftG

/-- Polynomial multiplication of `CPolyQ`s (schoolbook convolution via `cshift`/`cscale`). -/
def cmul : CPolyQ → CPolyQ → CPolyQ := CPolyG.cmulG

/-- Leading coefficient of a `CPolyQ` (top nonzero coefficient; `0` for the zero polynomial). -/
def clead (p : CPolyQ) : ℚ := CPolyG.cleadG p

/-- Zero test for a `CPolyQ`: `true` iff it normalizes to `[]`. -/
def cisZero (p : CPolyQ) : Bool := cnorm p == []

/-- Euclidean division of `CPolyQ`s, fuel-bounded: `cdivmod fuel p q = (quotient, remainder)` with
`p = quotient · q + remainder`, `deg remainder < deg q`. -/
def cdivmod : ℕ → CPolyQ → CPolyQ → CPolyQ × CPolyQ
  | 0, p, _ => ([], cnorm p)
  | fuel + 1, p, q =>
    let p := cnorm p
    let q := cnorm q
    if cisZero q then ([], [])
    else if p.length < q.length then ([], p)
    else
      let c := clead p / clead q
      let k := p.length - q.length
      let term := cshift k [c]
      let p' := cnorm (csub p (cmul term q))
      let (quo, rem) := cdivmod fuel p' q
      (cadd term quo, rem)

/-- Quotient of `CPolyQ` Euclidean division (`cdivmod`'s first component). -/
def cdiv (fuel : ℕ) (p q : CPolyQ) : CPolyQ := (cdivmod fuel p q).1

/-- Remainder of `CPolyQ` Euclidean division (`cdivmod`'s second component). -/
def cmod (fuel : ℕ) (p q : CPolyQ) : CPolyQ := (cdivmod fuel p q).2

/-- Divisibility test `cdvd fuel q p`: `true` iff `q ∣ p` (remainder of `p` by `q` is zero). -/
def cdvd (fuel : ℕ) (q p : CPolyQ) : Bool := cisZero (cmod fuel p q)

/-- Extended Euclidean algorithm on `CPolyQ`s, fuel-bounded: `cgcdExt fuel a b = (g, s, t)` with
`s · a + t · b = g` and `g = gcd(a, b)`. -/
def cgcdExt : ℕ → CPolyQ → CPolyQ → CPolyQ × CPolyQ × CPolyQ
  | 0, a, _ => (cnorm a, [1], [])
  | fuel + 1, a, b =>
    if cisZero b then (cnorm a, [1], [])
    else
      let (q, r) := cdivmod (fuel + 1) a b
      let (g, s, t) := cgcdExt fuel b r
      -- `s·b + t·r = g`, `r = a − q·b` ⇒ `t·a + (s − t·q)·b = g`
      (g, t, csub s (cmul t q))

/-- Computable `LogToAtan` over `CPolyQ`, fuel-bounded: `logToAtanCompute fuel A B` returns the
arctangent arguments as `(numerator, denominator)` pairs. -/
def logToAtanCompute : ℕ → CPolyQ → CPolyQ → List (CPolyQ × CPolyQ)
  | 0, _, _ => []
  | fuel + 1, A, B =>
    let A := cnorm A
    let B := cnorm B
    if cdvd (fuel + 1) B A then
      [(cdiv (fuel + 1) A B, [1])]
    else if A.length < B.length then
      logToAtanCompute fuel (cneg B) A
    else
      -- `cgcdExt B (−A) = (G, D, C)` gives `D·B + C·(−A) = G`, i.e. `B·D − A·C = G`.
      let (g, s, t) := cgcdExt (fuel + 1) B (cneg A)
      let D := s
      let C := t
      let G := g
      (cadd (cmul A D) (cmul B C), G) :: logToAtanCompute fuel D C

/-- `x³ − 3x` as a `CPolyQ`: coefficients `[0, −3, 0, 1]`. -/
def cX3m3X : CPolyQ := [0, -3, 0, 1]

/-- `x² − 2` as a `CPolyQ`: coefficients `[-2, 0, 1]`. -/
def cX2m2 : CPolyQ := [-2, 0, 1]

/-- `logToAtanCompute` on `(x³−3x, x²−2)` evaluates to the three `(numerator, denominator)` arctan
arguments `[((−x+3x³−x⁵), −2), ((−x³), −1), ((x), 1)]`. -/
theorem logToAtanCompute_ex281 :
    logToAtanCompute 20 cX3m3X cX2m2
      = [([0, -1, 0, 3, 0, -1], [-2]), ([0, 0, 0, -1], [-1]), ([0, 1], [1])] := by
  native_decide

/-! ### Bridge back to `ℚ[X]`
`toPoly` reads a `CPolyQ` as a `Polynomial ℚ`; the homomorphism lemmas show the `CPolyQ` operations
realize the `ℚ[X]` operations. -/

/-- Bridge `toPoly p` reading a `CPolyQ` coefficient list (index = degree, low to high) as a
`Polynomial ℚ` in Horner form `p₀ + x·(p₁ + x·(p₂ + …))`. -/
noncomputable def toPoly : CPolyQ → ℚ[X]
  | [] => 0
  | a :: p => Polynomial.C a + X * toPoly p

/-- `toPoly [] = 0`: the empty coefficient list is the zero polynomial. -/
@[simp] theorem toPoly_nil : toPoly ([] : CPolyQ) = 0 := rfl

/-- `toPoly (a :: p) = C a + X · toPoly p` (Horner recursion). -/
@[simp] theorem toPoly_cons (a : ℚ) (p : CPolyQ) :
    toPoly (a :: p) = Polynomial.C a + X * toPoly p := rfl

/-- `toPoly` is additive: `toPoly (cadd p q) = toPoly p + toPoly q`. -/
theorem toPoly_cadd (p q : CPolyQ) : toPoly (cadd p q) = toPoly p + toPoly q := by
  induction p generalizing q with
  | nil => simp [cadd, CPolyG.caddG]
  | cons a as ih =>
    cases q with
    | nil => simp [cadd, CPolyG.caddG]
    | cons b bs =>
      show toPoly (CField.add a b :: cadd as bs) = _
      rw [toPoly_cons, ih bs, toPoly_cons, toPoly_cons]
      show C (a + b) + _ = _
      rw [map_add]; ring

/-- `toPoly` commutes with negation: `toPoly (cneg p) = − toPoly p`. -/
theorem toPoly_cneg (p : CPolyQ) : toPoly (cneg p) = - toPoly p := by
  induction p with
  | nil => simp [cneg, CPolyG.cnegG]
  | cons a as ih =>
    show toPoly (-a :: cneg as) = -toPoly (a :: as)
    rw [toPoly_cons, toPoly_cons, ih, map_neg]; ring

/-- `toPoly` realizes subtraction: `toPoly (csub p q) = toPoly p − toPoly q`. -/
theorem toPoly_csub (p q : CPolyQ) : toPoly (csub p q) = toPoly p - toPoly q := by
  rw [csub, toPoly_cadd, toPoly_cneg, sub_eq_add_neg]

/-- `toPoly` realizes scalar multiplication: `toPoly (cscale c p) = C c · toPoly p`. -/
theorem toPoly_cscale (c : ℚ) (p : CPolyQ) : toPoly (cscale c p) = Polynomial.C c * toPoly p := by
  induction p with
  | nil => simp [cscale, CPolyG.cscaleG]
  | cons a as ih =>
    show toPoly (c * a :: cscale c as) = Polynomial.C c * toPoly (a :: as)
    rw [toPoly_cons, toPoly_cons, ih, map_mul]; ring

/-- `toPoly` realizes the degree shift: `toPoly (cshift k p) = X^k · toPoly p`. -/
theorem toPoly_cshift (k : ℕ) (p : CPolyQ) : toPoly (cshift k p) = X ^ k * toPoly p := by
  induction k with
  | zero => simp [cshift, CPolyG.cshiftG]
  | succ n ih =>
    show toPoly (0 :: cshift n p) = X ^ (n + 1) * toPoly p
    rw [toPoly_cons, ih, map_zero]; ring

/-- `toPoly` is multiplicative: `toPoly (cmul p q) = toPoly p · toPoly q`. -/
theorem toPoly_cmul (p q : CPolyQ) : toPoly (cmul p q) = toPoly p * toPoly q := by
  induction p with
  | nil => simp [cmul, CPolyG.cmulG]
  | cons a as ih =>
    show toPoly (cadd (cscale a q) (0 :: cmul as q)) = toPoly (a :: as) * toPoly q
    rw [toPoly_cadd, toPoly_cscale, toPoly_cons, toPoly_cons, ih, map_zero]; ring

/-- `foldl (·* V) init` over `range n` realizes `init · V^n` under `toPoly`. -/
theorem toPoly_foldl_cmul (V : CPolyQ) (n : ℕ) (init : CPolyQ) :
    toPoly ((List.range n).foldl (fun acc _ => cmul acc V) init)
      = toPoly init * toPoly V ^ n := by
  induction n generalizing init with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_concat, toPoly_cmul, ih, pow_succ]
    ring

/-! ### Agreement with the `ℚ[X]`-level `logToAtanAux`
The cofactor Bézout identity `B·D − A·C = G` under `toPoly` is proven in `logToAtan_cofactor_bezout`
(`Correctness`), so the arctan argument fractions `(A·D + B·C)/G` are well-defined. -/

end Compute

end DeepWiki.SymbolicIntegration
