import DeepWiki.SymbolicIntegration.ComputableHermiteTowerCorrect
import DeepWiki.SymbolicIntegration.ComputablePolyPartTowerCorrect

/-! # Abstract §6.4 `cSPDE`-step algebra and the `cSPDECleared` certificate (Bronstein Chapter 6)

The §6 Risch differential equation pipeline reduces `D(y) + f·y = g` over the monomial tower ℚ(x)[t]
through normal/special denominator → degree bound → §6.4 `cSPDE` (Rothstein peel) → §6.5/§6.6
`cPolyRischDE`. This file proves the **abstract**, axiom-clean (no `native_decide`) algebraic core of the
§6.4 Rothstein-`SPDE` peel and packages the per-level certificate the lifting needs. The generic engine's
abstract correctness (`ComputableRischDETowerCorrect`) transports these §6.4 facts to `cSPDEG`.

The route is the **cleared-polynomial identity** technique of `ComputablePolyPartTowerCorrect` /
`ComputableHermiteTowerCorrect`: state identities over `(RatFunc ℚ)[X]` with `D = cmonomialDeriv Dt =
Differential.implicitDeriv (toPolyG Dt)` (`toPolyG_cmonomialDeriv`), a `Derivation`, so `map_add`/Leibniz
hold.

## What this file delivers

* **§6.4 `cSPDE` step algebra** (`spde_step_glue`, `spde_const_base`, `cSPDE_peel_cleared`): the
  Rothstein peel's correctness core as pure `Derivation` algebra — given the Bézout `b·r + a·z = c` and a
  solution `h` of the reduced `a·D(h) + (b + D(a))·h = z − D(r)`, the reconstruction `q = a·h + r` solves
  `a·D(q) + b·q = c` (Leibniz + `ring`), plus the `deg(a) = 0` scaling base case; `cSPDE_peel_cleared`
  instantiates this at `implicitDeriv (toPolyG Dt)` over `(RatFunc ℚ)[X]`.

* **The per-level certificate predicate `cSPDECleared`**: the recursively-bundled exact-division witnesses
  `(a/g)·g = a` …, `a/g ≠ 0`, and the Bézout `bd·r + ad·z = cd` at every `gcd`-peel level. It mirrors the
  Rothstein recursion's own `match` structure so a lifting is a clean fuel induction; `cSPDECleared_of_inputs`
  (`ComputableRischDESPDECorrect`) discharges it from a transparent input predicate. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

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

#print axioms spde_step_glue
#print axioms spde_const_base
#print axioms cSPDE_peel_cleared

end DeepWiki.SymbolicIntegration
