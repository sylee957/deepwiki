import DeepWiki.SymbolicIntegration.RiobooLogToAtan
import DeepWiki.SymbolicIntegration.GenericPolyEngine

/-! # Computable `LogToAtan` over `ℚ` (Bronstein §2.8, Example 2.8.1, p.63–64)
Mathlib's `ℚ[X]` arithmetic is **noncomputable** (`Polynomial` wraps `Finsupp`/`AddMonoidAlgebra`,
whose `+`/`*`/`-` have no kernel reduction), so the abstract `logToAtanAux` cannot `#eval`. Here we
give a genuinely **computable**, `#eval`-able rendering of Rioboo's `LogToAtan` on a dense coefficient
representation `CPoly := List ℚ` (index = degree, low to high): `cadd`/`cneg`/`cmul`/`cdivmod`/`cgcdExt`
are ordinary computable list functions, and `logToAtanCompute` mirrors the three branches of
`logToAtanAux` (base `B ∣ A`, swap `deg A < deg B`, step with the extended-Euclidean cofactors
`B·D − A·C = G`) with a `ℕ` fuel parameter. We `#eval` it on **Example 2.8.1** `(x³−3x, x²−2)` and pin
the result with `native_decide` (kernel `decide` stalls on GMP-backed `ℚ` arithmetic), recovering the
book's arctan arguments `(x⁵−3x³+x)/2, x³, x`. A `toPoly : CPoly → ℚ[X]` bridge connects this back to
the `ℚ[X]`-level theory; the cofactor Bézout invariant is **proven** (`logToAtan_cofactor_bezout`,
`ComputeCorrectness`), the full entry-by-entry correspondence to `logToAtanAux` still open. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

namespace Compute

/-- **Dense coefficient list** over `ℚ` (index = degree, low to high): `CPoly := CPolyG ℚ` is the
computable polynomial carrier the `LogToAtan` recursion runs on — the generic `CPolyG` engine
(`GenericPolyEngine`) specialized at the computable field `ℚ` (defeq to `List ℚ`). -/
abbrev CPoly := CPolyG ℚ

/-- **Normalize** a `CPoly` by stripping trailing (high-degree) zero coefficients, so `cnorm` is a
canonical form (the zero polynomial becomes `[]`). -/
def cnorm : CPoly → CPoly
  | [] => []
  | a :: as => match cnorm as with
    | [] => if a = 0 then [] else [a]
    | r => a :: r

/-- **Coefficientwise addition** of two `CPoly`s (the shorter is zero-extended implicitly). -/
def cadd : CPoly → CPoly → CPoly
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => (a + b) :: cadd as bs

/-- **Negation** of a `CPoly`, coefficientwise. -/
def cneg (p : CPoly) : CPoly := p.map (- ·)

/-- **Subtraction** of `CPoly`s, `p − q := p + (−q)`. -/
def csub (p q : CPoly) : CPoly := cadd p (cneg q)

/-- **Scalar multiplication** of a `CPoly` by `c : ℚ`, coefficientwise. -/
def cscale (c : ℚ) (p : CPoly) : CPoly := p.map (c * ·)

/-- **Degree shift** `cshift k p = x^k · p`: prepend `k` zero coefficients. -/
def cshift : ℕ → CPoly → CPoly
  | 0, p => p
  | n + 1, p => 0 :: cshift n p

/-- **Polynomial multiplication** of `CPoly`s (schoolbook convolution via `cshift`/`cscale`). -/
def cmul : CPoly → CPoly → CPoly
  | [], _ => []
  | a :: as, q => cadd (cscale a q) (0 :: cmul as q)

/-- **Leading coefficient** of a `CPoly` (the top nonzero coefficient; `0` for the zero polynomial). -/
def clead (p : CPoly) : ℚ := (cnorm p).getLast?.getD 0

/-- **Zero test** for a `CPoly`: `true` iff it normalizes to `[]`. -/
def cisZero (p : CPoly) : Bool := cnorm p == []

/-- **Euclidean division** of `CPoly`s, fuel-bounded: `cdivmod fuel p q = (quotient, remainder)` with
`p = quotient · q + remainder` and `deg remainder < deg q` (long division over the field `ℚ`; `q ≠ 0`).
The `ℕ` fuel makes it structurally recursive hence computable; one step suffices per degree drop. -/
def cdivmod : ℕ → CPoly → CPoly → CPoly × CPoly
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

/-- **Quotient** of `CPoly` Euclidean division (`cdivmod`'s first component). -/
def cdiv (fuel : ℕ) (p q : CPoly) : CPoly := (cdivmod fuel p q).1

/-- **Remainder** of `CPoly` Euclidean division (`cdivmod`'s second component). -/
def cmod (fuel : ℕ) (p q : CPoly) : CPoly := (cdivmod fuel p q).2

/-- **Divisibility test** `cdvd fuel q p`: `true` iff `q ∣ p` (remainder of `p` by `q` is zero). -/
def cdvd (fuel : ℕ) (q p : CPoly) : Bool := cisZero (cmod fuel p q)

/-- **Extended Euclidean algorithm** on `CPoly`s, fuel-bounded: `cgcdExt fuel a b = (g, s, t)` with the
Bézout relation `s · a + t · b = g` and `g = gcd(a, b)`. Mirrors `EuclideanDomain.gcd`/`gcdA`/`gcdB`. -/
def cgcdExt : ℕ → CPoly → CPoly → CPoly × CPoly × CPoly
  | 0, a, _ => (cnorm a, [1], [])
  | fuel + 1, a, b =>
    if cisZero b then (cnorm a, [1], [])
    else
      let (q, r) := cdivmod (fuel + 1) a b
      let (g, s, t) := cgcdExt fuel b r
      -- `s·b + t·r = g`, `r = a − q·b` ⇒ `t·a + (s − t·q)·b = g`
      (g, t, csub s (cmul t q))

/-- **Computable `LogToAtan`** (Rioboo, §2.8 p.63) over `CPoly`, fuel-bounded: `logToAtanCompute fuel
A B` returns the list of arctangent arguments as `(numerator, denominator)` pairs. Branches mirror
`logToAtanAux`: `B ∣ A → [(A/B, 1)]`; `deg A < deg B → LogToAtan(−B, A)`; else with the extended-
Euclidean cofactors `(g, D, C) = cgcdExt B (−A)` (so `B·D − A·C = G`), prepend `((A·D + B·C), G)` and
recurse on `(D, C)`. Genuinely **computable** (no `noncomputable`, no `Classical`) — it `#eval`s. -/
def logToAtanCompute : ℕ → CPoly → CPoly → List (CPoly × CPoly)
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

/-- **`x³ − 3x`** as a `CPoly` (Example 2.8.1's `A`): coefficients `[0, −3, 0, 1]`. -/
def cX3m3X : CPoly := [0, -3, 0, 1]

/-- **`x² − 2`** as a `CPoly` (Example 2.8.1's `B`): coefficients `[-2, 0, 1]`. -/
def cX2m2 : CPoly := [-2, 0, 1]

-- **Example 2.8.1, the computed `LogToAtan` run** (printed at build): with `A = x³−3x`, `B = x²−2`,
-- this prints `[([0, -1, 0, 3, 0, -1], [-2]), ([0, 0, 0, -1], [-1]), ([0, 1], [1])]`, i.e. the
-- `(num, den)` pairs `((−x + 3x³ − x⁵), −2)`, `((−x³), −1)`, `((x), 1)` = the book's
-- `(x⁵−3x³+x)/2, x³, x`.
#eval logToAtanCompute 20 cX3m3X cX2m2

/-- **Example 2.8.1, the proved computation** (§2.8, p.63–64): `logToAtanCompute` on `(x³−3x, x²−2)`
evaluates to the three `(numerator, denominator)` arctan arguments
`[((−x+3x³−x⁵), −2), ((−x³), −1), ((x), 1)]` — equal as fractions to the book table's
`(x⁵−3x³+x)/2, x³, x` (eq 2.20). Proved by `native_decide` (kernel `decide` stalls on the GMP-backed
`ℚ` arithmetic); this pins the printed `#eval` as a *theorem*, demonstrating the algorithm actually
runs and returns the book's answer. -/
theorem logToAtanCompute_ex281 :
    logToAtanCompute 20 cX3m3X cX2m2
      = [([0, -1, 0, 3, 0, -1], [-2]), ([0, 0, 0, -1], [-1]), ([0, 1], [1])] := by
  native_decide

/-! ### Bridge back to `ℚ[X]`
`toPoly` reads a `CPoly` coefficient list as an honest (noncomputable) `Polynomial ℚ`; the homomorphism
lemmas (`cadd`/`cneg`/`csub`/`cscale`/`cshift`/`cmul` realize the `ℚ[X]` operations) let the computable
algorithm's outputs be compared with the `ℚ[X]`-level `logToAtanAux`/`IsLogToAtanRun` theory. -/

/-- **Bridge to `ℚ[X]`**: `toPoly p` reads a `CPoly` coefficient list (index = degree, low to high)
back as an honest (noncomputable) `Polynomial ℚ` in **Horner form** `p₀ + x·(p₁ + x·(p₂ + …))`. The
Horner shape makes `toPoly_nil`/`toPoly_cons` definitional. -/
noncomputable def toPoly : CPoly → ℚ[X]
  | [] => 0
  | a :: p => Polynomial.C a + X * toPoly p

/-- `toPoly [] = 0`: the empty coefficient list is the zero polynomial. -/
@[simp] theorem toPoly_nil : toPoly ([] : CPoly) = 0 := rfl

/-- `toPoly`'s leading recursion (Horner): `toPoly (a :: p) = C a + X · toPoly p`. -/
@[simp] theorem toPoly_cons (a : ℚ) (p : CPoly) :
    toPoly (a :: p) = Polynomial.C a + X * toPoly p := rfl

/-- `toPoly` is **additive**: `toPoly (cadd p q) = toPoly p + toPoly q` — the list addition `cadd`
realizes `ℚ[X]` addition under the Horner bridge. -/
theorem toPoly_cadd (p q : CPoly) : toPoly (cadd p q) = toPoly p + toPoly q := by
  induction p generalizing q with
  | nil => simp [cadd]
  | cons a as ih =>
    cases q with
    | nil => simp [cadd]
    | cons b bs =>
      simp only [cadd, toPoly_cons, ih bs, map_add]
      ring

/-- `toPoly` commutes with **negation**: `toPoly (cneg p) = − toPoly p`. -/
theorem toPoly_cneg (p : CPoly) : toPoly (cneg p) = - toPoly p := by
  induction p with
  | nil => simp [cneg]
  | cons a as ih =>
    show toPoly (-a :: cneg as) = -toPoly (a :: as)
    rw [toPoly_cons, toPoly_cons, ih, map_neg]; ring

/-- `toPoly` realizes **subtraction**: `toPoly (csub p q) = toPoly p − toPoly q`. -/
theorem toPoly_csub (p q : CPoly) : toPoly (csub p q) = toPoly p - toPoly q := by
  rw [csub, toPoly_cadd, toPoly_cneg, sub_eq_add_neg]

/-- `toPoly` realizes **scalar multiplication**: `toPoly (cscale c p) = C c · toPoly p`. -/
theorem toPoly_cscale (c : ℚ) (p : CPoly) : toPoly (cscale c p) = Polynomial.C c * toPoly p := by
  induction p with
  | nil => simp [cscale]
  | cons a as ih =>
    show toPoly (c * a :: cscale c as) = Polynomial.C c * toPoly (a :: as)
    rw [toPoly_cons, toPoly_cons, ih, map_mul]; ring

/-- `toPoly` realizes the **degree shift**: `toPoly (cshift k p) = X^k · toPoly p`. -/
theorem toPoly_cshift (k : ℕ) (p : CPoly) : toPoly (cshift k p) = X ^ k * toPoly p := by
  induction k with
  | zero => simp [cshift]
  | succ n ih =>
    show toPoly (0 :: cshift n p) = X ^ (n + 1) * toPoly p
    rw [toPoly_cons, ih, map_zero]; ring

/-- `toPoly` is **multiplicative**: `toPoly (cmul p q) = toPoly p · toPoly q` — `cmul` realizes `ℚ[X]`
multiplication under the Horner bridge. -/
theorem toPoly_cmul (p q : CPoly) : toPoly (cmul p q) = toPoly p * toPoly q := by
  induction p with
  | nil => simp [cmul]
  | cons a as ih =>
    show toPoly (cadd (cscale a q) (0 :: cmul as q)) = toPoly (a :: as) * toPoly q
    rw [toPoly_cadd, toPoly_cscale, toPoly_cons, toPoly_cons, ih, map_zero]; ring

/-! ### Agreement with the `ℚ[X]`-level `logToAtanAux` — PARTIAL (cofactor Bézout invariant proven)
The single new mathematical fact behind the entry-by-entry correspondence is **proven**:
`logToAtan_cofactor_bezout` (`ComputeCorrectness`) certifies the `cgcdExt` Bézout identity
`B·D − A·C = G` under `toPoly`, so the arctan *argument fractions* `(A·D + B·C)/G` are well-defined and
the `cgcdExt` cofactors `(D, C, G)` agree with `EuclideanDomain.gcdA/gcdB/gcd (toPoly B) (toPoly (cneg A))`
up to the `gcd`-normalizing unit (which cancels between numerator and denominator). What remains for the
*full* list-level `logToAtanCompute fuel A B ↦ logToAtanAux φ fuel' (toPoly A) (toPoly B)` is the
non-mathematical plumbing: matching the branch tests (`cdvd` vs `∣`, `length` vs `degree`) and
reconciling the two fuel budgets. The correctness of the fractions (`atanDerivSum … = i · logDeriv …`)
transfers through `isLogToAtanRun_correct`; the `native_decide` computation on Example 2.8.1
(`logToAtanCompute_ex281`) is the concrete witness. -/

end Compute

end DeepWiki.SymbolicIntegration
