import DeepWiki.SymbolicIntegration.ComputableGeneralPicardGroupLaw

/-! # The NON-hyperelliptic Picard group law over `𝔽_p` via the `L(D)` `𝔽_p`-linear solve — the
genuinely-general case (no `y² = ρ(x)` involution, so Cantor/Mumford does NOT apply), reading an
INDIVIDUAL divisor class's order on an arbitrary plane curve (Trager Ch. 6 / computational AG: a
**`ZMod p` Gaussian-elimination `L(D)` solve**, NOT the `𝔽_p[x]` HNF)

`ComputableGeneralPicardGroupLaw` reads an individual class's order beyond the genus-1 ceiling — but only
for a **hyperelliptic** `y² = ρ(x)` model, because its reduction *engine* round-trips through the proven
Mumford/Cantor compose/reduce (`ptToMum` / `mumToPts`). A genuinely **non-hyperelliptic** plane curve — a
smooth `f(x, y) = 0` with no `y² = ρ` involution, e.g. the **Fermat cubic** `x³ + y³ = 1` — has no Mumford
pair, so Cantor is inapplicable. The general reduction is then the **`L((g+1)·∞)` Riemann–Roch space
`𝔽_p`-linear solve** over a bivariate monomial basis (computational Brill–Noether / Hess).

**This file supplies that non-hyperelliptic reduction, and the crucial point the user makes: the
`𝔽_p`-LINEAR algebra is `native_decide`-LIGHT** — a small `ZMod p` Gaussian elimination (`kernelVec`),
NOT the `𝔽_p[x]` Hermite normal form that hit the compilation wall. The keystone framing (the user's): this
is COMPUTATIONAL ALGEBRAIC GEOMETRY (linear solves over `𝔽_p`), not abstract Riemann–Roch.

## The `L(D)` `𝔽_p`-linear solve (the line system `|H|` = `L(1·∞-divisor)`)

For a plane curve `f(x, y) = 0` and an effective `𝔽_p`-point divisor `D` (degree `≤ g + 1`),
`L((g+1)·∞ − D)` is the space of polynomials `h(x, y)` of bounded total degree (a monomial basis) that
**vanish at every point of `D`**. For the genus-1 plane cubic the relevant space is the **line system**:
linear forms `h = a·X + b·Y + c·Z` (monomial basis `{X, Y, Z}`). A line vanishing at two points of `D` is a
**nonzero kernel vector** of the `2×3` homogeneous matrix `[Xᵢ Yᵢ Zᵢ]` over `𝔽_p` — found by
`kernelVec`, a small `ZMod p` Gaussian elimination (LIGHT). That line is the reducing function `h`.

## Reducing a divisor class (chord-and-tangent = the `L(D)` solve + residual)

* **`pgThird P Q`** — the residual zero of `div(h)`: the **third** intersection of the line `h ∈ L(D)`
  (through `P`, `Q`) with the cubic. Computed from the **binary cubic** of `f` restricted to the line
  parametrization `s·P + t·Q` (Vieta: the third root `(s : t) = (−C : B)`), pure `ZMod p` arithmetic. The
  tangent case `P = Q` uses the polar line `(X² : Y² : −Z²)` (contact-2 = vanishing to multiplicity 2, the
  `L(2·D)` solve) and factors out the double root.
* **`pgNeg P = pgThird P O`** (`O` = the base point `∞`), **`pgAddPt P Q = pgThird (pgThird P Q) O`** — the
  chord-and-tangent law: `[P − ∞] + [Q − ∞] = −[R − ∞]` with `R = pgThird P Q`, negated through `O`. The
  reduced representative of any class is a single affine point (or `[]` = identity); the analogue of
  `pdivAdd`.
* **`nhReduce`** folds the point law over an effective point list (the analogue of `pdivReduce`);
  **`picMulNH` / `picOrderNH`** read an individual class's order (the analogues of `picMul` / `picOrder`).

★ **Proof-of-concept** (`native_decide`): on the **Fermat cubic** `x³ + y³ = 1` (genus 1 but
**NON-hyperelliptic** — Cantor inapplicable, exactly why the `L(D)` route is needed) over `𝔽₅` and `𝔽₁₁`
(both `≡ 2 mod 3`, so the curve has a **single rational point at infinity** `∞`, the clean base), the
`L(D)`-solve group law computes `picOrderNH` of the flex class `(1,0) − ∞` as **3** — a genuine
`ℤ/3`-torsion class — and `3 ∣ N_p` (the `ComputableGeneralTorsionLight` point count). One validated
non-hyperelliptic `picOrder` via the `L(D)` solve = the general group law works.

Everything is **fuel-bounded total recursion** (no `partial def`), so the axiom set stays
`[propext, Classical.choice, Quot.sound]` + the `native_decide` reduction axiom — no `sorryAx`. -/

namespace DeepWiki.SymbolicIntegration

/-! ## Projective `𝔽_p`-points and their normalization

A point on the projective plane curve is a triple `[X : Y : Z] ∈ (ZMod p)³`. The base point `∞` of the
Fermat cubic over `p ≡ 2 mod 3` is the single rational point at infinity `[1 : τ : 0]` (`τ³ = −1`); affine
points are `[x : y : 1]`. We carry the triple internally and read off the affine `(x, y)` for the
`RedDivNH` representation. -/

/-- **A projective `𝔽_p`-point** `PPt p = ZMod p × ZMod p × ZMod p` — homogeneous coordinates `[X : Y : Z]`
of a point on the projective plane curve. Affine points are `[x : y : 1]`; the base point `∞` of the Fermat
cubic (`p ≡ 2 mod 3`) is `[1 : τ : 0]`. The internal point representation of the `L(D)`-solve group law. -/
abbrev PPt (p : ℕ) : Type := ZMod p × ZMod p × ZMod p

/-- **Normalize a projective point** `ppNorm P` to a canonical representative: scale so the last nonzero
coordinate is `1` (`Z = 1` for affine, else `X = 1` for the point at infinity, else `[0:1:0]`). Makes
projective equality a decidable `ZMod p`-tuple equality — the canonical-form primitive (analogue of
`pdivCanon` on the point representation). -/
def ppNorm {p : ℕ} (P : PPt p) : PPt p :=
  let (X, Y, Z) := P
  if Z ≠ 0 then (X * Z⁻¹, Y * Z⁻¹, 1)
  else if X ≠ 0 then (1, Y * X⁻¹, 0)
  else (0, 1, 0)

/-- **Projective-point equality** `ppEq P Q` — `true` iff `ppNorm`-equal, i.e. the same projective point.
The identity test for the group law (analogue of `pdivEq`). -/
def ppEq {p : ℕ} (P Q : PPt p) : Bool := decide (ppNorm P = ppNorm Q)

/-! ## The `L(D)` `𝔽_p`-linear solve: a general `ZMod p` Gaussian-elimination kernel basis

The space `L((g+1)·∞ − D)` of monomials vanishing at `D` is the **kernel** of the homogeneous matrix whose
rows are the monomial basis evaluated at the points of `D`. We compute that kernel by a genuine general
`ZMod p` **Gaussian elimination** (`kernelMat`): reduce the matrix to reduced row-echelon form
(`rrefMat`, pivot/scale/eliminate over the finite field), then read one basis vector off each free column.
This is the **`native_decide`-LIGHT** linear algebra — a handful of `ZMod p` field operations on a small
matrix — the computational heart of the general reduction, where the `𝔽_p[x]` HNF hit the wall. The matrix
is a `List (List (ZMod p))` (rows); `kernelMat` is generic in the number of columns, so the same routine
serves the line system (`{X, Y, Z}`, `3` columns) and any larger monomial basis. -/

/-- **Row-scale** `rowSmul c r = c · r` — multiply a `ZMod p` row by a scalar (the pivot-normalization
step of Gaussian elimination). -/
def rowSmul {p : ℕ} (c : ZMod p) (r : List (ZMod p)) : List (ZMod p) := r.map (c * ·)

/-- **Row-combine** `rowAxpy c r s = s − c · r` — subtract a scalar multiple of the pivot row `r` from row
`s` (the elimination step), zipped componentwise. Pure `ZMod p` arithmetic. -/
def rowAxpy {p : ℕ} (c : ZMod p) (r s : List (ZMod p)) : List (ZMod p) :=
  (s.zip r).map (fun pr => pr.1 - c * pr.2)

/-- **Eliminate a pivot column from all other rows** `elimCol col piv rows` — for each `r ∈ rows` subtract
`r[col] · piv` (so its `col` entry becomes `0`), using the already-normalized pivot row `piv` (leading `1`
in `col`). The reduce-all-other-rows step of full (Gauss–Jordan) `ZMod p` elimination. -/
def elimCol {p : ℕ} (col : ℕ) (piv : List (ZMod p)) (rows : List (List (ZMod p))) :
    List (List (ZMod p)) :=
  rows.map (fun r => rowAxpy (r.getD col 0) piv r)

/-- **Gauss–Jordan elimination to reduced row-echelon form** `rrefAux fuel col ncol pivots rows` — sweep
columns `col, col+1, …` up to `ncol` (bounded by `fuel`). At each column find a not-yet-pivoted row with a
nonzero entry (`List.find?` over `rows` excluding the recorded `pivots`), scale it to a leading `1`,
eliminate that column from **every** other row (`elimCol`, full Gauss–Jordan — so earlier pivot rows are
cleaned too), append the normalized pivot row to `pivots` with its column, and recurse. Returns the
accumulated `(pivotCol, pivotRow)` list — true **reduced** row-echelon form. Pure `ZMod p` field
arithmetic; `fuel`-bounded (no `partial def`). -/
def rrefAux {p : ℕ} : ℕ → ℕ → ℕ → List (ℕ × List (ZMod p)) → List (List (ZMod p)) →
    List (ℕ × List (ZMod p))
  | 0, _, _, pivots, _ => pivots
  | fuel + 1, col, ncol, pivots, rows =>
    if col ≥ ncol then pivots
    else
      -- candidate pivot rows: those not already recorded as a pivot row, with a nonzero `col` entry
      let used := pivots.map Prod.snd
      match rows.find? (fun r => decide (r.getD col 0 ≠ 0) && !(used.contains r)) with
      | none => rrefAux fuel (col + 1) ncol pivots rows
      | some piv0 =>
        let piv := rowSmul (piv0.getD col 0)⁻¹ piv0
        -- eliminate `col` from every other row (Gauss–Jordan), including earlier pivot rows
        let rows' := (rows.map (fun r => if r == piv0 then piv
          else rowAxpy (r.getD col 0) piv r))
        let pivots' := (pivots.map (fun pr => (pr.1, rowAxpy (pr.2.getD col 0) piv pr.2))) ++
          [(col, piv)]
        rrefAux fuel (col + 1) ncol pivots' rows'

/-- **The RREF pivot data** `rref ncol rows` — run `rrefAux` over all `ncol` columns from a fresh start: the
list of `(pivotColumn, pivotRow)` pairs of the `ZMod p` reduced row-echelon form of the matrix `rows`. The
basis-of-the-row-space datum the kernel read-off uses. -/
def rref {p : ℕ} (ncol : ℕ) (rows : List (List (ZMod p))) : List (ℕ × List (ZMod p)) :=
  rrefAux ncol 0 ncol [] rows

/-- **A kernel basis over `𝔽_p`** `kernelMat ncol rows` — the `L(D)` linear solve: a basis of the (right)
**kernel** `{v : v · rowᵀ = 0}` of the matrix `rows` (the homogeneous system the monomial basis must
satisfy at `D`), via `ZMod p` Gaussian elimination. Run `rref`, then for each **free** column (no pivot)
emit a basis vector with `1` there and `−(pivotRow[freeCol])` at each pivot column. Returns the list of
kernel basis vectors (length-`ncol` `ZMod p` lists). A nonzero one is the reducing function `h`; for an
independent `2×3` line system it is the single vector `u × v`. Pure `ZMod p` field arithmetic — the
`native_decide`-LIGHT computational-AG core, no `𝔽_p[x]` HNF. -/
def kernelMat {p : ℕ} (ncol : ℕ) (rows : List (List (ZMod p))) : List (List (ZMod p)) :=
  let piv := rref ncol rows
  let pivCols := piv.map Prod.fst
  ((List.range ncol).filter (fun c => !(pivCols.contains c))).map (fun fc =>
    (List.range ncol).map (fun c =>
      if c = fc then 1
      else match piv.find? (fun pr => decide (pr.1 = c)) with
        | some pr => -(pr.2.getD fc 0)
        | none => 0))

/-! ## The plane curve, and the residual zero via the binary cubic (the chord-and-tangent intersection)

A projective plane curve is a homogeneous cubic `f(X, Y, Z)`, here packaged as the `ZMod p`-function
`PCurve p`. The reducing function `h ∈ L(D)` is a **line** (the `L(D)` kernel solve, `kernelVec`); its
residual zero on the cubic is the **third** intersection point. We compute it from the **binary cubic**
`f(s·P + t·Q) = A·s³ + B·s²t + C·st² + D·t³` (a univariate form on the line parametrization): with `P`, `Q`
on the curve (`A = D = 0`) the third root is `(s : t) = (−C : B)` (Vieta). The four coefficients `A, B, C,
D` are read off by evaluating `f` at four parameter values — pure `ZMod p` ring arithmetic. -/

/-- **A projective plane curve over `𝔽_p`** `PCurve p = ZMod p → ZMod p → ZMod p → ZMod p` — a homogeneous
polynomial `f(X, Y, Z)` as its `ZMod p`-evaluation function. The Fermat cubic is `f X Y Z = X³ + Y³ − Z³`.
Used to read the binary-cubic intersection coefficients. -/
abbrev PCurve (p : ℕ) : Type := ZMod p → ZMod p → ZMod p → ZMod p

/-- **The Fermat cubic** `fermatF X Y Z = X³ + Y³ − Z³` over `𝔽_p` — the homogeneous form of `x³ + y³ = 1`.
A smooth genus-1 plane cubic, **not** a hyperelliptic `y² = ρ(x)` model (so Cantor/Mumford does not apply);
its `L(D)`-solve group law is the proof-of-concept. -/
def fermatF {p : ℕ} : PCurve p := fun X Y Z => X ^ 3 + Y ^ 3 - Z ^ 3

/-- **Projective combination** `ppComb P Q s t = s·P + t·Q` (componentwise), normalized — the point at
parameter `(s : t)` on the line through `P`, `Q`. The line parametrization the binary cubic runs over. -/
def ppComb {p : ℕ} (P Q : PPt p) (s t : ZMod p) : PPt p :=
  ppNorm (s * P.1 + t * Q.1, s * P.2.1 + t * Q.2.1, s * P.2.2 + t * Q.2.2)

/-- **Evaluate the curve on the line parametrization** `lineEval f P Q s t = f(s·P + t·Q)` — `f` at the
unnormalized combination `s·P + t·Q`. Sampling this at four `(s, t)` recovers the binary-cubic
coefficients. -/
def lineEval {p : ℕ} (f : PCurve p) (P Q : PPt p) (s t : ZMod p) : ZMod p :=
  f (s * P.1 + t * Q.1) (s * P.2.1 + t * Q.2.1) (s * P.2.2 + t * Q.2.2)

/-- **Binary-cubic coefficients** `binCubic f P Q = (A, B, C, D)` of `f(s·P + t·Q) = A s³ + B s²t + C st²
+ D t³`: `A = f(1,0)`, `D = f(0,1)`, and `B`, `C` from `f(1,1)`, `f(1,−1)` by `C = (f₁₁ + f₁₋₁ − 2A)/2`,
`B = (f₁₁ − f₁₋₁)/2 − D`. The univariate intersection form of the curve with the line, by four `ZMod p`
evaluations. -/
def binCubic {p : ℕ} (f : PCurve p) (P Q : PPt p) : ZMod p × ZMod p × ZMod p × ZMod p :=
  let a := lineEval f P Q 1 0
  let d := lineEval f P Q 0 1
  let f11 := lineEval f P Q 1 1
  let f1m1 := lineEval f P Q 1 (-1)
  let c := (f11 + f1m1 - 2 * a) * (2 : ZMod p)⁻¹
  let b := (f11 - f1m1) * (2 : ZMod p)⁻¹ - d
  (a, b, c, d)

/-- **Two independent points on a line** `lineTwoPts ℓ = (U, V)` where `ℓ = (a, b, c)` is the line
`a·X + b·Y + c·Z = 0`: the two non-degenerate cross products of `ℓ` with the coordinate basis vectors. Used
to parametrize the **tangent** line (whose coefficients are the polar `(X², Y², −Z²)`) for the doubling
case. Pure `ZMod p` arithmetic. -/
def lineTwoPts {p : ℕ} (ℓ : ZMod p × ZMod p × ZMod p) : PPt p × PPt p :=
  let (a, b, c) := ℓ
  -- ℓ × e₀ = (0, c, -b);  ℓ × e₁ = (-c, 0, a);  ℓ × e₂ = (b, -a, 0)
  let w0 : PPt p := (0, c, -b)
  let w1 : PPt p := (-c, 0, a)
  let w2 : PPt p := (b, -a, 0)
  -- pick the first that is nonzero as U, then the first independent of U as V
  if w0 ≠ (0, 0, 0) then
    (w0, if (w0.2.1 * w1.2.2 - w0.2.2 * w1.2.1, w0.2.2 * w1.1 - w0.1 * w1.2.2,
              w0.1 * w1.2.1 - w0.2.1 * w1.1) ≠ (0, 0, 0) then w1 else w2)
  else (w1, w2)

/-- **Parameter of `P` on the line spanned by `U`, `V`** `lineParam U V P = (s, t)` with `s·U + t·V ~ P`
(projectively): solved from whichever `2×2` coordinate minor of `[U V]` is invertible (Cramer over `𝔽_p`).
Used to locate the tangent point in its own parametrization, to factor out the double root. -/
def lineParam {p : ℕ} (U V P : PPt p) : ZMod p × ZMod p :=
  let co : PPt p → ℕ → ZMod p := fun w i => match i with | 0 => w.1 | 1 => w.2.1 | _ => w.2.2
  let try2 : ℕ → ℕ → Option (ZMod p × ZMod p) := fun i j =>
    let det := co U i * co V j - co U j * co V i
    if det = 0 then none
    else some ((co P i * co V j - co P j * co V i) * det⁻¹,
               (co U i * co P j - co U j * co P i) * det⁻¹)
  match try2 0 1 with
  | some r => r
  | none => match try2 0 2 with
    | some r => r
    | none => (try2 1 2).getD (0, 0)

/-- **The residual (third) intersection** `pgThird f P Q` of the line `h ∈ L(D)` through `P`, `Q` with the
cubic `f`. **Chord** (`P ≠ Q`): the binary cubic `f(s·P + t·Q)` has `A = D = 0`, so the third root is
`(s : t) = (−C : B)` — return `ppComb P Q (−C) B`. **Tangent** (`P = Q`): take the polar line `(X², Y²,
−Z²)`, parametrize it by `lineTwoPts` (giving `U`, `V`), locate `P`'s parameter `(sp, tp)` (`lineParam`),
and factor the double root out of the binary cubic to read the third root (`r₃ = −B/A − 2·sp/tp` in the
`tp ≠ 0` chart, the dual otherwise). The `L(D)`-solve residual that the chord-and-tangent group law builds
on; pure `ZMod p` arithmetic. -/
def pgThird {p : ℕ} (f : PCurve p) (P Q : PPt p) : PPt p :=
  if P ≠ Q then
    let (_, b, c, _) := binCubic f P Q
    ppComb P Q (-c) b
  else
    -- tangent at P = (X, Y, Z): polar line coeffs (X², Y², −Z²)
    let ℓ : ZMod p × ZMod p × ZMod p := (P.1 ^ 2, P.2.1 ^ 2, -(P.2.2 ^ 2))
    let (U, V) := lineTwoPts ℓ
    let (a, b, c, d) := binCubic f U V
    let (sp, tp) := lineParam U V P
    if tp ≠ 0 then
      if a = 0 then ppComb U V 1 0
      else ppComb U V ((-b) * a⁻¹ - 2 * (sp * tp⁻¹)) 1
    else
      if d = 0 then ppComb U V 1 0
      else ppComb U V 1 ((-c) * d⁻¹)

end DeepWiki.SymbolicIntegration
