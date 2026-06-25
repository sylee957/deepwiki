import DeepWiki.SymbolicIntegration.ComputableRischDE
import DeepWiki.SymbolicIntegration.ComputableHermiteTowerCorrect
import DeepWiki.SymbolicIntegration.ComputablePolyPartTowerCorrect

/-! # Abstract correctness of the §6 Risch-DE pipeline `cRischDE` (Bronstein Chapter 6)

The computable Risch differential equation oracle `cRischDE` (`ComputableRischDE`) solves
`D(y) + f·y = g` over the monomial tower ℚ(x)[t] through a five-stage pipeline (§6.2 normal denominator →
§6.2 special denominator → §6.3 degree bound → §6.4 `cSPDE` → §6.5/§6.6 `cPolyRischDE`). The end-to-end
output is validated *pointwise* by `native_decide` (`rischDE_solve_example`, the cleared identity
`rdeClearedCheck`: `D(y)+f·y = g` after multiplying out denominators). This file proves the **abstract**
correctness — for ALL inputs, axiom-clean (no `native_decide`) — of the *polynomial-stage* identities that
those checks rest on, working **leaf-first** up the pipeline.

The route is the **cleared-polynomial identity** technique of `ComputablePolyPartTowerCorrect` /
`ComputableHermiteTowerCorrect`: state identities over `(RatFunc ℚ)[X]` with `D = cmonomialDeriv Dt =
Differential.implicitDeriv (toPolyG Dt)` (`toPolyG_cmonomialDeriv`), a `Derivation`, so `map_add`/Leibniz
hold, proven by clean fuel induction.

## What this file delivers

* **§6.5 `cPolyRischDENoCancel` cleared identity** (`cPolyRischDENoCancel_cleared_identity`): when the
  non-cancellation solve **succeeds** (`= some q`), the output `q` satisfies the polynomial RDE
  `D(q) + b·q = c` over `(RatFunc ℚ)[X]`. The all-inputs generalization of the leading-coefficient
  degree-by-degree solve's `native_decide` validation. Proved by induction on fuel through the additivity
  of the `implicitDeriv` derivation: each pass peels `p = (lc(c)/lc(b))·tᵐ`, recurses on
  `c' = c − D(p) − b·p`, and glues `D(p+q) + b·(p+q) = D(p) + b·p + (D(q) + b·q) = D(p)+b·p+c' = c`.

* **§6.4 `cSPDE` cleared reduction** (`cSPDE_cleared_reduction`): the Rothstein `gcd(a,b)`-peel reduces
  `a·D(q) + b·q = c` to a smaller `D(h) + b̄·h = c̄`. We prove the **lifting** direction the pipeline
  uses: from the returned `(b̄, c̄, m, α, β)`, *any* `h` solving the reduced `D(h) + b̄·h = c̄` yields
  `q = α·h + β` solving the **original `a/g`-divided** equation `ā·D(q) + b̄'·q = c̄'`, where
  `(ā, b̄', c̄') = (a/g, b/g, c/g)` for `g = gcd(a,b)` — the cleared identity at each peel level, threaded
  by fuel induction. (The cleared statement is for the gcd-divided equation; the original
  `a·D(q)+b·q = c` follows by multiplying through by `g` when `g ∣ c`, the box's `cdvdG g c` test.)

## The remaining gap (honestly documented)

The §6.3 degree bound is a *bound* (an `ℕ`), not an identity — it constrains *which* `q` can solve, not
the cleared form, so it enters only as a hypothesis at the §6.4/§6.5 boundary (the degree-`≤ n`
short-circuits), never as an algebraic identity to discharge. The §6.2 special-denominator and
normal-denominator transforms replace the unknown by `q = h/denom` (eq. 6.7 substitution `q = h·pⁿ`), so
they change the equation **by the denominator** `p^N`: their cleared form is `(a·pᴺ)·D(r) + (…)·r =
c·p^{…}` reading the *cleared* numerator equation, which the engine produces as genuine `CPolyG QFunNZ`
polynomials. Stating those two reductions' cleared identities is **algebraically** within the
cleared-polynomial technique (no fraction-field derivation needed: `Dp/p` is exact-divided since `p ∣ Dp`
for a special `p`, exactly as Hermite's residual `hNum` is exact-divided), but the §6.2 `b`-component
`dₙh·f − dₙ·Dh` mixes the *rational* `f = fnum/fden` with the polynomial `Dh`, so its cleared identity is a
**fraction-cleared** identity over `fden` (the `cdivFF … fden` exact division), needing the same
exact-division-certificate hypothesis shape as `cHermiteReduceTower_cleared_identity`. The genuinely
*missing* infrastructure for an unconditional full-pipeline `cRischDE_cleared` is a
`Differential (RatFunc (RatFunc ℚ))` realizing `implicitDeriv` on the fraction field (the repo's
`ratFuncDeriv` is `d/dx` only) — needed only where a stage's invariant is naturally stated on the
*fraction field* `k(t)` rather than the cleared *polynomial* numerator equation, i.e. the §6.1 weak
normalizer's residue argument and the rational `b`-component. The two polynomial-stage leaves (§6.5, §6.4)
delivered here sidestep that entirely. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### §6.5 — the cleared non-cancellation identity `D(q) + b·q = c` for ALL inputs (when it succeeds)

`cPolyRischDENoCancel Dt fuel b c n` solves `D(q) + b·q = c` (eq. 6.19) degree-by-degree: peel
`p = (lc(c)/lc(b))·tᵐ`, recurse on `c' = c − D(p) − b·p`, glue `q ← p + (recursive q)`. When it returns
`some q`, the cleared identity `D(q) + b·q = c` holds over `(RatFunc ℚ)[X]`,
`D = implicitDeriv (toPolyG Dt)` — proved by induction on `fuel`, the additivity of `implicitDeriv`
gluing the peeled `p` to the recursive solution. -/

/-- **`cPolyRischDENoCancel` satisfies the cleared RDE identity `D(q) + b·q = c`** (abstract, ALL inputs)
over the field ℚ(x), whenever the solve **succeeds**. If `cPolyRischDENoCancel Dt fuel b c n = some q`
then, with `D = cmonomialDeriv Dt` the monomial derivation (`= Differential.implicitDeriv (toPolyG Dt)`
through `toPolyG`), the degree-by-degree non-cancellation solve reconstructs the polynomial RDE exactly:
`implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG b * toPolyG q = toPolyG c` in `(RatFunc ℚ)[X]`. The
all-inputs, axiom-clean (no `native_decide`) generalization of the §6.5 `rdeClearedCheck` validation,
gated on no preconditions beyond success (the degree bound `n` only governs *whether* it succeeds, not the
identity). Proved by induction on `fuel`: each pass peels `p = (lc(c)/lc(b))·tᵐ`, recurses on
`c' = c − D(p) − b·p`, and the additivity of `implicitDeriv` glues `D(p+q) + b·(p+q) =
D(p) + b·p + (D(q) + b·q) = D(p) + b·p + c' = c`. -/
theorem cPolyRischDENoCancel_cleared_identity (Dt b : CPolyG QFunNZ) :
    ∀ (fuel : ℕ) (c : CPolyG QFunNZ) (n : ℤ) (q : CPolyG QFunNZ),
      cPolyRischDENoCancel Dt fuel b c n = some q →
        Differential.implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG b * toPolyG q = toPolyG c := by
  intro fuel
  induction fuel with
  | zero =>
    intro c n q hq
    -- `cPolyRischDENoCancel Dt 0 _ _ _ = none`, contradiction
    rw [cPolyRischDENoCancel] at hq
    exact absurd hq (by simp)
  | succ fuel ih =>
    intro c n q hq
    rw [cPolyRischDENoCancel] at hq
    by_cases hc : cisZeroG c = true
    · -- base case: `c = 0`, returns `[]`, so `D(0) + b·0 = 0 = c`
      rw [if_pos hc, Option.some.injEq] at hq
      subst hq
      have hc0 : toPolyG c = 0 := (cisZeroG_iff c).mp hc
      rw [toPolyG_nil, map_zero, mul_zero, add_zero, hc0]
    · -- recursion branch
      rw [if_neg hc] at hq
      set m : ℤ := (cdegG c : ℤ) - (cdegG b : ℤ) with hm
      by_cases hguard : n < 0 ∨ m < 0 ∨ m > n
      · rw [if_pos hguard] at hq
        exact absurd hq (by simp)
      · rw [if_neg hguard] at hq
        simp only at hq
        set coeff := CField.div (cleadG c) (cleadG b) with hcoeff
        set p := cshiftG m.toNat [coeff] with hp
        set c' := csubG (csubG c (cmonomialDeriv Dt p)) (cmulG b p) with hc'
        -- destructure the recursive call
        rcases hrec : cPolyRischDENoCancel Dt fuel b c' (m - 1) with _ | qrec
        · rw [hrec] at hq; exact absurd hq (by simp)
        · rw [hrec, Option.some.injEq] at hq
          -- the recursive identity on `c'`
          have ihrec := ih c' (m - 1) qrec hrec
          -- `q = p + qrec`
          subst hq
          rw [toPolyG_caddG, map_add, mul_add]
          -- expand `c' = c − D(p) − b·p` through `toPolyG`
          have hc'eq : toPolyG c' = toPolyG c
              - Differential.implicitDeriv (toPolyG Dt) (toPolyG p) - toPolyG b * toPolyG p := by
            rw [hc', toPolyG_csubG, toPolyG_csubG, toPolyG_cmonomialDeriv, toPolyG_cmulG]
          rw [hc'eq] at ihrec
          -- glue: `D(p) + D(qrec) + (b·p + b·qrec) = D(p) + b·p + (D(qrec) + b·qrec) = c`
          linear_combination ihrec

/-- The §6.5 non-cancellation cleared identity, restated. When `cPolyRischDENoCancel Dt fuel b c n =
some q`, the output `q` solves `D(q) + b·q = c` over ℚ(x)[t]. -/
example (Dt b c : CPolyG QFunNZ) (fuel : ℕ) (n : ℤ) (q : CPolyG QFunNZ)
    (hq : cPolyRischDENoCancel Dt fuel b c n = some q) :
    Differential.implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG b * toPolyG q = toPolyG c :=
  cPolyRischDENoCancel_cleared_identity Dt b fuel c n q hq

/-! ### The `cisZeroG`-Boolean form — directly bridging the §6.5 `native_decide` validation
The §6.5 leg of `rischDE_solve_example` ultimately checks a cleared polynomial difference is `0`. The
abstract identity makes the exact Boolean check `cisZeroG (D(q) + b·q − c) = true` provably `true` for ALL
successful runs, through `cisZeroG_iff` and the `toPolyG` homomorphism lemmas. -/

/-- **The §6.5 cleared check holds for ALL successful runs**: when `cPolyRischDENoCancel Dt fuel b c n =
some q`, the Boolean cleared check `cisZeroG ((D(q) + b·q) − c) = true` (`D = cmonomialDeriv Dt`) is a
theorem, the all-inputs axiom-clean (no `native_decide`) generalization of the §6.5 pointwise validation. -/
theorem cPolyRischDENoCancel_cisZeroG_cleared (Dt b c : CPolyG QFunNZ) (fuel : ℕ) (n : ℤ)
    (q : CPolyG QFunNZ) (hq : cPolyRischDENoCancel Dt fuel b c n = some q) :
    cisZeroG (csubG (caddG (cmonomialDeriv Dt q) (cmulG b q)) c) = true := by
  rw [cisZeroG_iff, toPolyG_csubG, toPolyG_caddG, toPolyG_cmonomialDeriv, toPolyG_cmulG, sub_eq_zero]
  exact cPolyRischDENoCancel_cleared_identity Dt b fuel c n q hq

#print axioms cPolyRischDENoCancel_cleared_identity
#print axioms cPolyRischDENoCancel_cisZeroG_cleared

/-! ### §6.4 — the Rothstein `SPDE` step gluing (Bronstein Theorem 6.4.1, the algebraic core)

`cSPDE` reduces `a·D(q) + b·q = c` (with `a ⊥ b` after the `gcd`-peel) by solving the Bézout
`b·r + a·z = c` (`deg(r) < deg(a)`) and recursing on `a·D(h) + (b + D(a))·h = z − D(r)`, reconstructing
`q = a·h + r`. The gluing identity — that this reconstruction *solves* the original divided equation —
is pure `Derivation`-algebra: `D(a·h + r) = D(a)·h + a·D(h) + D(r)` (Leibniz), so
`a·D(a·h + r) + b·(a·h + r) = a·(a·D(h) + (b+D(a))·h) + a·D(r) + b·r = a·(z − D(r)) + a·D(r) + b·r =
a·z + b·r = c`. Stated abstractly for any `Derivation` over a commutative ring, so it applies verbatim to
`implicitDeriv (toPolyG Dt)` on `(RatFunc ℚ)[X]`. This is the §6.4 analogue of `hermiteTower_cleared_of_exact`:
the algebraic heart, gated on the two certificates (Bézout + the reduced solution) the `native_decide`
validation produces along the recursion. -/

/-- **The Rothstein `SPDE`-step gluing identity** (commutative-ring `Derivation` algebra): with `D` a
derivation, divided coefficients `a, b, c`, a Bézout witness `b·r + a·z = c`, and a solution `h` of the
*reduced* equation `a·D(h) + (b + D(a))·h = z − D(r)`, the reconstruction `q = a·h + r` solves the
original divided equation `a·D(q) + b·q = c`. Pure `Derivation.leibniz` + `ring`; the algebraic core of
one `cSPDE` peel (Bronstein Theorem 6.4.1). -/
theorem spde_step_glue {R : Type*} [CommRing R] (D : Derivation ℤ R R)
    (a b c r z h : R)
    (hbez : b * r + a * z = c)
    (hred : a * D h + (b + D a) * h = z - D r) :
    a * D (a * h + r) + b * (a * h + r) = c := by
  have hD : D (a * h + r) = a * D h + D a * h + D r := by
    rw [map_add, Derivation.leibniz]; simp only [smul_eq_mul]; ring
  rw [hD]
  -- `a·(a·Dh + Da·h + Dr) + b·(a·h + r) = a·(a·Dh + (b+Da)·h) + a·Dr + b·r`
  have : a * (a * D h + D a * h + D r) + b * (a * h + r)
      = a * (a * D h + (b + D a) * h) + (a * D r + b * r) := by ring
  rw [this, hred]
  linear_combination hbez

-- The `SPDE`-step reconstruction `q = a·h + r` solves `a·D(q) + b·q = c` given the Bézout + reduced witness.
example {R : Type*} [CommRing R] (D : Derivation ℤ R R) (a b c r z h : R)
    (hbez : b * r + a * z = c) (hred : a * D h + (b + D a) * h = z - D r) :
    a * D (a * h + r) + b * (a * h + r) = c :=
  spde_step_glue D a b c r z h hbez hred

/-! ### §6.4 — the constant-`a` base-case lifting (unconditional)

When `cSPDE` reaches `deg(a) = 0` (`a ∈ k*`) it returns `(b/lc(a), c/lc(a), n, [1], [])`: the reduced
equation is `D(h) + (b/lc(a))·h = c/lc(a)` and the reconstruction is `q = α·h + β = 1·h + 0 = h`. So a
solution `h` of the reduced equation, scaled back by `lc(a)` (a nonzero constant since `a ∈ k*`), solves
`a·D(h) + b·h = c` directly — `lc(a)·D(h) + lc(a)·(b/lc(a))·h = lc(a)·(c/lc(a))`. The lifting is the
trivial scaling identity, stated abstractly. -/

/-- **The constant-`a` base-case scaling identity** (commutative-ring): if `a₀ ≠ 0` is a nonzero scalar
and `h` solves the reduced `D(h) + (a₀⁻¹·b)·h = a₀⁻¹·c`, then `h` solves `a₀·D(h) + b·h = c` (multiply
through by `a₀`). The `deg(a) = 0` base case of `cSPDE`, where `α = 1`, `β = 0` (`q = h`). -/
theorem spde_const_base {K : Type*} [Field K] (D : Derivation ℤ K[X] K[X])
    (a0 : K) (b c h : K[X]) (ha0 : a0 ≠ 0)
    (hred : D h + (Polynomial.C a0⁻¹ * b) * h = Polynomial.C a0⁻¹ * c) :
    Polynomial.C a0 * D h + b * h = c := by
  have key : Polynomial.C a0 * (D h + (Polynomial.C a0⁻¹ * b) * h)
      = Polynomial.C a0 * (Polynomial.C a0⁻¹ * c) := by rw [hred]
  have hinv : Polynomial.C a0 * Polynomial.C a0⁻¹ = 1 := by
    rw [← Polynomial.C_mul, mul_inv_cancel₀ ha0, Polynomial.C_1]
  calc Polynomial.C a0 * D h + b * h
      = Polynomial.C a0 * (D h + (Polynomial.C a0⁻¹ * b) * h)
          - (Polynomial.C a0 * Polynomial.C a0⁻¹ - 1) * (b * h) := by ring
    _ = Polynomial.C a0 * (Polynomial.C a0⁻¹ * c) - (1 - 1) * (b * h) := by rw [key, hinv]
    _ = (Polynomial.C a0 * Polynomial.C a0⁻¹) * c := by ring
    _ = c := by rw [hinv, one_mul]

/-! ### §6.4 — the one-peel `cSPDE` cleared lifting through `toPolyG` (engine-level)

The abstract `spde_step_glue` instantiated at `D = implicitDeriv (toPolyG Dt)` over `(RatFunc ℚ)[X]`,
with the engine's concrete reduction quantities read through `toPolyG`. One `cSPDE` recursion peel takes
the divided `(ad, bd, cd) = (a/g, b/g, c/g)` (`g = gcd(a,b)`), solves the Bézout `bd·r + ad·z = cd` by
`cdiophantineG bd ad cd = (r, z)`, and recurses on `(ad, bd + D(ad), z − D(r))`. Given the **Bézout
certificate** (`toPolyG bd · toPolyG r + toPolyG ad · toPolyG z = toPolyG cd`, discharged from
`toPolyG_cdiophantineG` exactly as the Hermite inner loop) and a solution `h` of the reduced equation,
the reconstruction `q = ad·h + r` solves `ad·D(q) + bd·q = cd`. This is the `cSPDE` peel's cleared
identity, gated only on the Bézout certificate the validation pins — the §6.4 analogue of the Hermite
`cHermiteReduceTower_cleared_identity`. -/

/-- **One `cSPDE` peel's cleared lifting** through `toPolyG`, at `D = cmonomialDeriv Dt =
implicitDeriv (toPolyG Dt)`. Write `Dpoly = implicitDeriv (toPolyG Dt)`. Given the divided coefficients
`ad, bd, cd : CPolyG QFunNZ`, the Bézout cofactors `r, z` with the **certificate**
`toPolyG bd · toPolyG r + toPolyG ad · toPolyG z = toPolyG cd` (the `cdiophantineG bd ad cd` output
relation), and any `h` solving the **reduced** equation
`toPolyG ad · Dpoly(toPolyG h) + (toPolyG bd + Dpoly(toPolyG ad))·toPolyG h = toPolyG z − Dpoly(toPolyG r)`,
the reconstruction `q = cmulG ad h + r` (`= ad·h + r`) solves the divided equation
`toPolyG ad · Dpoly(toPolyG q) + toPolyG bd · toPolyG q = toPolyG cd` over `(RatFunc ℚ)[X]`. The engine
instance of `spde_step_glue`; the `cmonomialDeriv`/`caddG`/`cmulG` outputs read through the `toPolyG`
homomorphism. -/
theorem cSPDE_peel_cleared (Dt ad bd cd r z h : CPolyG QFunNZ)
    (hbez : toPolyG bd * toPolyG r + toPolyG ad * toPolyG z = toPolyG cd)
    (hred : toPolyG ad * Differential.implicitDeriv (toPolyG Dt) (toPolyG h)
        + (toPolyG bd + Differential.implicitDeriv (toPolyG Dt) (toPolyG ad)) * toPolyG h
      = toPolyG z - Differential.implicitDeriv (toPolyG Dt) (toPolyG r)) :
    toPolyG ad * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG ad h) r))
        + toPolyG bd * toPolyG (caddG (cmulG ad h) r)
      = toPolyG cd := by
  rw [toPolyG_caddG, toPolyG_cmulG]
  exact spde_step_glue (Differential.implicitDeriv (toPolyG Dt))
    (toPolyG ad) (toPolyG bd) (toPolyG cd) (toPolyG r) (toPolyG z) (toPolyG h) hbez hred

-- One `cSPDE` peel: `q = ad·h + r` solves `ad·D(q) + bd·q = cd` given the Bézout + reduced-solution witnesses.
example (Dt ad bd cd r z h : CPolyG QFunNZ)
    (hbez : toPolyG bd * toPolyG r + toPolyG ad * toPolyG z = toPolyG cd)
    (hred : toPolyG ad * Differential.implicitDeriv (toPolyG Dt) (toPolyG h)
        + (toPolyG bd + Differential.implicitDeriv (toPolyG Dt) (toPolyG ad)) * toPolyG h
      = toPolyG z - Differential.implicitDeriv (toPolyG Dt) (toPolyG r)) :
    toPolyG ad * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG ad h) r))
        + toPolyG bd * toPolyG (caddG (cmulG ad h) r)
      = toPolyG cd :=
  cSPDE_peel_cleared Dt ad bd cd r z h hbez hred

/-! ### §6.4 — the FULL recursive `cSPDE` cleared lifting (the whole `gcd`-peel chain)

The capstone of §6.4: thread `cSPDE_peel_cleared` / `spde_const_base` through the entire `gcd`-peel
recursion. The recursion's per-level certificates — that `g = gcd(a,b)` exact-divides `a, b, c` (so the
divided `ad, bd, cd` recover `a, b, c`) and that `cdiophantineG bd ad cd = (r, z)` solves the Bézout
`bd·r + ad·z = cd` — are bundled into a recursively-defined predicate `cSPDECleared` mirroring `cSPDE`'s
own `match` structure, so the lifting is a clean fuel induction. With `cSPDECleared` in force,
`cSPDE Dt fuel a b c n = some (b̄, c̄, m, α, β)` guarantees: **any** `h` solving the reduced
`D(h) + b̄·h = c̄` makes `q = α·h + β` solve the divided equation `ad·D(q) + bd·q = cd` (top-level
`ad = a/g`, `bd = b/g`, `cd = c/g`), hence — multiplying by `g`, since `g ∣ c` — the original
`a·D(q) + b·q = c`. -/

/-- **Per-level certificate predicate for `cSPDE`** `cSPDECleared Dt fuel a b c n`: the recursively
bundled `toPolyG`-level facts that the `gcd`-peel divisions are exact and the Bézout solve is correct,
matching `cSPDE`'s own recursion. At each non-base level (`n ≥ 0`, `g ∣ c`, `deg(a/g) > 0`) it asserts
`toPolyG (a/g)·toPolyG g = toPolyG a` (and `b`, `c`), and the Bézout
`toPolyG bd·toPolyG r + toPolyG ad·toPolyG z = toPolyG cd`, then recurses on the reduced equation. The
base cases (`n < 0`, or `deg(a/g) = 0`) need only the `a/b/c`-division witnesses. Designed so that
`cSPDE = some (...)` together with `cSPDECleared` discharges the full lifting by induction. -/
def cSPDECleared (Dt : CPolyG QFunNZ) : ℕ → (a b c : CPolyG QFunNZ) → (n : ℤ) → Prop
  | 0, _, _, _, _ => True
  | fuel + 1, a, b, c, n =>
    if n < 0 then True
    else
      let g := cgcdFF fuel a b
      if cdvdG fuel g c then
        let ad := cdivFF fuel a g
        let bd := cdivFF fuel b g
        let cd := cdivFF fuel c g
        -- the three exact-division witnesses (so `toPolyG` of divided · gcd = original)
        (toPolyG ad * toPolyG g = toPolyG a) ∧ (toPolyG bd * toPolyG g = toPolyG b)
          ∧ (toPolyG cd * toPolyG g = toPolyG c)
          -- `a` (hence the divided `ad`) is nonzero (the SPDE input invariant `a ≠ 0`)
          ∧ (toPolyG ad ≠ 0)
          ∧ (if cdegG ad = 0 then True
             else
               let rz := cdiophantineG fuel bd ad cd
               -- the Bézout certificate `bd·r + ad·z = cd`
               (toPolyG bd * toPolyG rz.1 + toPolyG ad * toPolyG rz.2 = toPolyG cd)
                 ∧ cSPDECleared Dt fuel ad (caddG bd (cmonomialDeriv Dt ad))
                     (csubG rz.2 (cmonomialDeriv Dt rz.1)) (n - (cdegG ad : ℤ)))
      else True

/-- **The full recursive `cSPDE` cleared lifting**: under the certificate predicate `cSPDECleared`, if
`cSPDE Dt fuel a b c n = some (b̄, c̄, m, α, β)` then for every `h` solving the reduced
`D(h) + b̄·h = c̄` (`D = implicitDeriv (toPolyG Dt)`), the reconstruction `q = α·h + β` solves the
**original** equation `a·D(q) + b·q = c` over `(RatFunc ℚ)[X]`. The §6.4 capstone — `spde_step_glue`
threaded through the whole `gcd`-peel by induction on `fuel`. Each level's certificate (`cSPDECleared`)
supplies the exact-division witnesses `(a/g)·g = a`, …, the nonzero-leading `a/g ≠ 0`, and the Bézout
`bd·r + ad·z = cd`, so the constant base case multiplies the divided identity back by `toPolyG g`
(recovering `a·D(q)+b·q=c` since `g ∣ a,b,c`) and the recursion peel applies `spde_step_glue` to the IH's
reduced solution. The all-inputs, axiom-clean (no `native_decide`) §6.4 reduction correctness. -/
theorem cSPDE_cleared_lifting (Dt : CPolyG QFunNZ) :
    ∀ (fuel : ℕ) (a b c : CPolyG QFunNZ) (n : ℤ) (bbar cbar : CPolyG QFunNZ) (m : ℤ)
      (α β : CPolyG QFunNZ),
      cSPDE Dt fuel a b c n = some (bbar, cbar, m, α, β) →
      cSPDECleared Dt fuel a b c n →
      ∀ h : CPolyG QFunNZ,
        Differential.implicitDeriv (toPolyG Dt) (toPolyG h) + toPolyG bbar * toPolyG h = toPolyG cbar →
        toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α h) β))
            + toPolyG b * toPolyG (caddG (cmulG α h) β)
          = toPolyG c := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b c n bbar cbar m α β hspde _ h _
    rw [cSPDE] at hspde
    exact absurd hspde (by simp)
  | succ fuel ih =>
    intro a b c n bbar cbar m α β hspde hcert h hh
    rw [cSPDE] at hspde
    by_cases hn : n < 0
    · -- base case `n < 0`: `c = 0` ⇒ `(b̄,c̄,m,α,β) = ([],[],0,[],[])`, `q = 0`, divided = original
      rw [if_pos hn] at hspde
      by_cases hc0 : cisZeroG c = true
      · rw [if_pos hc0, Option.some.injEq] at hspde
        simp only [Prod.mk.injEq] at hspde
        obtain ⟨_hbbar, _hcbar, _, hα, hβ⟩ := hspde
        -- `q = α·h + β = 0·h + 0 = 0`, and `c = 0`
        subst hα; subst hβ
        have hcc : toPolyG c = 0 := (cisZeroG_iff c).mp hc0
        rw [toPolyG_caddG, toPolyG_cmulG, toPolyG_nil, zero_mul, add_zero, map_zero, mul_zero,
          mul_zero, add_zero, hcc]
      · rw [if_neg hc0] at hspde
        exact absurd hspde (by simp)
    · -- recursion / constant-base
      rw [if_neg hn] at hspde
      -- unfold the certificate
      rw [cSPDECleared] at hcert
      simp only [if_neg hn] at hcert
      set g := cgcdFF fuel a b with hg
      by_cases hdvd : cdvdG fuel g c = true
      · rw [if_pos hdvd] at hspde hcert
        set ad := cdivFF fuel a g with had
        set bd := cdivFF fuel b g with hbd
        set cd := cdivFF fuel c g with hcd
        obtain ⟨hdiva, hdivb, hdivc, hadne, hcertrest⟩ := hcert
        by_cases hdeg : cdegG ad = 0
        · -- constant-`a` base case: `cSPDE` returns `(ainv·bd, ainv·cd, n, [1], [])`, `q = h`
          rw [if_pos hdeg, Option.some.injEq] at hspde
          simp only [Prod.mk.injEq] at hspde
          obtain ⟨hbbar, hcbar, _, hα, hβ⟩ := hspde
          -- `α = [1]`, `β = []`, so `q = 1·h + 0 = h`
          subst hα; subst hβ
          rw [toPolyG_caddG, toPolyG_cmulG, toPolyG_nil, add_zero]
          have hone : toPolyG ([CField.one] : CPolyG QFunNZ) = 1 := by
            rw [toPolyG_cons, toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]
          rw [hone, one_mul]
          -- the constant scalar `a0 = lc(ad) = leadingCoeff(toPolyG ad) ≠ 0`
          set a0 : RatFunc ℚ := CFieldSpec.toK (cleadG ad) with ha0def
          have ha0ne : a0 ≠ 0 := by
            rw [ha0def, toK_cleadG_eq_leadingCoeff]
            exact Polynomial.leadingCoeff_ne_zero.mpr hadne
          -- `toPolyG ad = C a0` (degree 0 ⇒ constant polynomial)
          have hadC : toPolyG ad = Polynomial.C a0 := by
            have hnd : (toPolyG ad).natDegree = 0 := by rw [← cdegG_eq_natDegree, hdeg]
            rw [ha0def, toK_cleadG_eq_leadingCoeff, Polynomial.leadingCoeff, hnd]
            conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hnd]
          -- read `hh` as the reduced equation `D(h) + (C a0⁻¹·bd)·h = C a0⁻¹·cd`
          rw [← hbbar, ← hcbar, toPolyG_cscaleG, toPolyG_cscaleG, CFieldSpec.toK_inv,
            ← ha0def] at hh
          -- the divided identity `ad·D(h) + bd·h = cd` from `spde_const_base`
          have hdivided : toPolyG ad * Differential.implicitDeriv (toPolyG Dt) (toPolyG h)
              + toPolyG bd * toPolyG h = toPolyG cd := by
            rw [hadC]
            exact spde_const_base (Differential.implicitDeriv (toPolyG Dt)) a0 (toPolyG bd) (toPolyG cd)
              (toPolyG h) ha0ne hh
          -- multiply by `toPolyG g`: `a·D(h) + b·h = g·(ad·D(h) + bd·h) = g·cd = c`
          rw [← hdiva, ← hdivb, ← hdivc]
          linear_combination toPolyG g * hdivided
        · -- recursion peel: `q = ad·h' + r`, `h'` from the recursive solve
          rw [if_neg hdeg] at hspde
          rw [if_neg hdeg] at hcertrest
          -- destructure the Bézout cofactors `(r, z) = cdiophantineG bd ad cd`
          rcases hrz : cdiophantineG fuel bd ad cd with ⟨r, z⟩
          rw [hrz] at hspde hcertrest
          simp only at hspde hcertrest
          obtain ⟨hbez', hcertrec⟩ := hcertrest
          rcases hrec : cSPDE Dt fuel ad (caddG bd (cmonomialDeriv Dt ad))
            (csubG z (cmonomialDeriv Dt r)) (n - (cdegG ad : ℤ))
            with _ | ⟨bbar', cbar', m', α', β'⟩
          · rw [hrec] at hspde; exact absurd hspde (by simp)
          · rw [hrec, Option.some.injEq] at hspde
            simp only [Prod.mk.injEq] at hspde
            obtain ⟨hbbar, hcbar, _hm, hα, hβ⟩ := hspde
            -- `α = ad·α'`, `β = ad·β' + r`, `bbar = bbar'`, `cbar = cbar'`
            rw [← hbbar] at hh; rw [← hcbar] at hh
            -- IH gives the recursive call's ORIGINAL equation
            --   `ad·D(h') + (bd + D(ad))·h' = z − D(r)`,  `h' = α'·h + β'`
            have hihrec := ih ad (caddG bd (cmonomialDeriv Dt ad))
              (csubG z (cmonomialDeriv Dt r)) (n - (cdegG ad : ℤ))
              bbar' cbar' m' α' β' hrec hcertrec h hh
            -- expand `hihrec` into the `cSPDE_peel_cleared`-`hred` shape, with `h' = α'·h + β'`
            have hred : toPolyG ad
                  * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α' h) β'))
                + (toPolyG bd + Differential.implicitDeriv (toPolyG Dt) (toPolyG ad))
                    * toPolyG (caddG (cmulG α' h) β')
                = toPolyG z - Differential.implicitDeriv (toPolyG Dt) (toPolyG r) := by
              simp only [toPolyG_caddG, toPolyG_cmonomialDeriv, toPolyG_csubG] at hihrec ⊢
              linear_combination hihrec
            subst hα; subst hβ
            -- divided peel identity from `cSPDE_peel_cleared` (reconstruction `ad·(α'·h + β') + r`)
            have hpeel := cSPDE_peel_cleared Dt ad bd cd r z (caddG (cmulG α' h) β') hbez' hred
            -- the goal's `q = (ad·α')·h + (ad·β' + r)` equals `ad·(α'·h+β') + r` as a polynomial
            have hqeq : toPolyG (caddG (cmulG (cmulG ad α') h) (caddG (cmulG ad β') r))
                = toPolyG (caddG (cmulG ad (caddG (cmulG α' h) β')) r) := by
              simp only [toPolyG_caddG, toPolyG_cmulG]; ring
            -- rewrite the goal's `q`-image to the peel shape, then multiply the peel by `g`
            rw [hqeq, ← hdiva, ← hdivb, ← hdivc]
            linear_combination toPolyG g * hpeel
      · rw [if_neg hdvd] at hspde
        exact absurd hspde (by simp)

-- Full recursive `cSPDE` lifting: under `cSPDECleared`, a reduced solution lifts to the original eqn.
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (a b c : CPolyG QFunNZ) (n : ℤ)
    (bbar cbar : CPolyG QFunNZ) (m : ℤ) (α β : CPolyG QFunNZ)
    (hspde : cSPDE Dt fuel a b c n = some (bbar, cbar, m, α, β))
    (hcert : cSPDECleared Dt fuel a b c n) (h : CPolyG QFunNZ)
    (hh : Differential.implicitDeriv (toPolyG Dt) (toPolyG h) + toPolyG bbar * toPolyG h
      = toPolyG cbar) :
    toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG (caddG (cmulG α h) β))
        + toPolyG b * toPolyG (caddG (cmulG α h) β)
      = toPolyG c :=
  cSPDE_cleared_lifting Dt fuel a b c n bbar cbar m α β hspde hcert h hh

#print axioms spde_step_glue
#print axioms spde_const_base
#print axioms cSPDE_peel_cleared
#print axioms cSPDE_cleared_lifting

end DeepWiki.SymbolicIntegration
