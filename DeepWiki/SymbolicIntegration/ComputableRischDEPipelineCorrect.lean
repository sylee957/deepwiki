import DeepWiki.SymbolicIntegration.ComputableRischDESPDECorrect
import DeepWiki.SymbolicIntegration.ComputableFractionFieldDeriv

/-! # The §6.2 normal-denominator cleared-lifting glue (Bronstein Chapter 6)

The §6.2 normal-denominator stage `cRdeNormalDenominator` reduces `D(y) + f·y = g`
(`f = fnum/fden`, `g = gnum/gden`) to a polynomial RDE `a·D(q) + b·q = c` with `q = y·h`, returning
`(a, b, c, h)` with `a = dₙ·h`, `b·fden = a·fnum − dₙ·Dh·fden`, `c·gden = dₙ·h²·gnum` (the
exact-division certificates the `cdivFF` clearings carry). The **converse** the solver needs — that a
polynomial `Q` solving the reduced equation makes `y = Q/h` solve `D(y) + f·y = g` — is the pure
commutative-ring `Derivation` lemma `rdeNormalDenominator_glue`: multiply the reduced identity by
`fden·gden`, substitute the three certificates, and the whole cleared form
`gden·fden·(D(Q)·h − Q·Dh) + gden·fnum·Q·h = gnum·fden·h²` is `dₙ` times the goal, so cancelling the
nonzero normal part `dₙ` gives it (no fraction-field derivation; stays polynomial, exactly the shape
`rdeClearedCheck` decides). Stated abstractly over any `Derivation` on a `CommRing` with
`NoZeroDivisors`, so it applies verbatim at `implicitDeriv (toPolyG Dt)` over `(RatFunc ℚ)[X]`. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### §6.2 normal denominator — the cleared lifting `y = Q/h` solves `D(y) + f·y = g`

`cRdeNormalDenominator Dt fuel fnum fden gnum gden` (Bronstein §6.2 / Corollary 6.1.1) reduces
`D(y) + f·y = g` (`f = fnum/fden`, `g = gnum/gden`) to a polynomial equation `a·D(q) + b·q = c` with
`q = y·h`, returning `(a, b, c, h)` where (the `cdvdG`-branch outputs)

```
  a = dₙ·h,   b·fden = a·fnum − dₙ·Dh·fden,   c·gden = dₙ·h²·gnum,   Dh = D(h)
```

(`dₙ` the normal part of `fden`; `b, c` are the `cdivFF`-cleared numerators over `fden`, `gden`). The
**converse** the solver needs: a polynomial `Q` solving the reduced `a·D(Q) + b·Q = c` makes
`y = Q/h` solve `D(y) + f·y = g`. In the cleared polynomial form (the shape `rdeClearedCheck` decides,
`ynum = Q`, `yden = h`):

```
  gden·fden·(D(Q)·h − Q·Dh) + gden·fnum·Q·h = gnum·fden·h²
```

This is **purely polynomial** (no fraction-field derivation): multiply the reduced equation by
`fden·gden`, substitute the three exact-division/factorization certificates, and the whole identity is
`dₙ` times the goal — so cancelling the nonzero normal part `dₙ` gives it. The three certificates are
the `cdivFF`-clearing facts (dischargeable from `toPolyG_cdivFF_exact` as in §6.4), supplied here as
hypotheses on the `toPolyG` images. -/

/-- **The §6.2 normal-denominator cleared lifting** (commutative-ring `Derivation` core): with `D` a
derivation, the normal part `DN ≠ 0`, the factorization `A = DN·H` and the two exact-division
certificates `B·FDEN = A·FNUM − DN·(D H)·FDEN`, `C·GDEN = DN·H²·GNUM`, a solution `Q` of the reduced
equation `A·D(Q) + B·Q = C` makes `y = Q/H` solve `D(y) + f·y = g` in the cleared form
`GDEN·FDEN·(D(Q)·H − Q·(D H)) + GDEN·FNUM·Q·H = GNUM·FDEN·H²`. Pure algebra: multiply the reduced
equation by `FDEN·GDEN`, the whole identity is `DN` times the goal, cancel the nonzero `DN`. -/
theorem rdeNormalDenominator_glue {R : Type*} [CommRing R] [NoZeroDivisors R]
    (D : Derivation ℤ R R) (DN H FNUM FDEN GNUM GDEN A B C Q : R)
    (hDN : DN ≠ 0)
    (hA : A = DN * H)
    (hB : B * FDEN = A * FNUM - DN * D H * FDEN)
    (hC : C * GDEN = DN * H ^ 2 * GNUM)
    (hred : A * D Q + B * Q = C) :
    GDEN * FDEN * (D Q * H - Q * D H) + GDEN * FNUM * Q * H = GNUM * FDEN * H ^ 2 := by
  -- multiply the reduced equation by `FDEN·GDEN` and substitute the certificates
  have hmul : FDEN * GDEN * (A * D Q + B * Q) = FDEN * GDEN * C := by rw [hred]
  -- the whole cleared identity is `DN` times the goal
  have hkey : DN * (GDEN * FDEN * (D Q * H - Q * D H) + GDEN * FNUM * Q * H)
      = DN * (GNUM * FDEN * H ^ 2) := by
    have e1 : FDEN * GDEN * (A * D Q + B * Q)
        = GDEN * (A * D Q * FDEN) + GDEN * Q * (B * FDEN) := by ring
    have e2 : FDEN * GDEN * C = FDEN * (C * GDEN) := by ring
    rw [e1, e2, hB, hC, hA] at hmul
    linear_combination hmul
  exact mul_left_cancel₀ hDN hkey

-- The §6.2 normal-denominator glue: a reduced solution `Q` makes `y = Q/H` solve `D(y)+f·y=g` (cleared).
example {R : Type*} [CommRing R] [NoZeroDivisors R] (D : Derivation ℤ R R)
    (DN H FNUM FDEN GNUM GDEN A B C Q : R)
    (hDN : DN ≠ 0) (hA : A = DN * H) (hB : B * FDEN = A * FNUM - DN * D H * FDEN)
    (hC : C * GDEN = DN * H ^ 2 * GNUM) (hred : A * D Q + B * Q = C) :
    GDEN * FDEN * (D Q * H - Q * D H) + GDEN * FNUM * Q * H = GNUM * FDEN * H ^ 2 :=
  rdeNormalDenominator_glue D DN H FNUM FDEN GNUM GDEN A B C Q hDN hA hB hC hred

#print axioms rdeNormalDenominator_glue

end DeepWiki.SymbolicIntegration
