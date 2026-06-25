import DeepWiki.SymbolicIntegration.ComputableHermiteTower
import DeepWiki.SymbolicIntegration.ComputableGcdCorrect
import DeepWiki.SymbolicIntegration.ComputableSplitFactorCorrect

/-! # Abstract correctness of the transcendental Hermite reduction `cHermiteReduceTower` (Bronstein §5.3)
The computable transcendental Hermite reduction `cHermiteReduceTower Dt fuel a d`
(`ComputableHermiteTower`) rewrites `f = a/d` over the monomial extension ℚ(x)[t] as `D(g) + h` with `D`
the **monomial derivation** `D = cmonomialDeriv Dt = implicitDeriv (toPolyG Dt)`, returning the rational
part `g = gnum/gden` (already integrated) and a residual `h = hNum/Dstar` with `Dstar` squarefree. It is
validated *pointwise* by `native_decide` (`hermiteTower_example`, the cleared identity `D(g) + h = f`).
This file proves the **abstract** correctness — for ALL inputs, axiom-clean (no `native_decide`) — the
cleared-denominator identity that `hermiteTower_example` checks.

The deliverable is the all-inputs generalization of the exact `native_decide` check. `hermiteTower_example`
verifies, over ℚ(x)[t] = `CPolyG QFunNZ`, the cleared form of `D(gnum/gden) + hNum/Dstar = a/d`:
```
(gprimeNum · Dstar + hNum · gden²) · d  =  a · (gden² · Dstar)
```
where `gprimeNum = D(gnum)·gden − gnum·D(gden)` is the quotient-rule numerator of `D(g)` (`D` the
monomial derivation). Reading both sides through `toPolyG` into `(RatFunc ℚ)[X]`, `D` becomes
`implicitDeriv (toPolyG Dt)` (`toPolyG_cmonomialDeriv`), and the identity is a **polynomial** identity
over the field ℚ(x) — no `RatFunc (RatFunc ℚ)` fraction-field derivation is constructed.

**Route — the cleared polynomial identity from the exact-division certificate.** The residual numerator
is recovered by an *exact division* `hNum = (resNum · Dstar) / resDen` with `resNum = a·gden² −
d·gprimeNum`, `resDen = d·gden²` (the residual `a/d − D(g) = resNum/resDen`, cleared). The exact-division
certificate (the remainder `cmodG fuel (resNum·Dstar) resDen` reads to `0`) gives, through
`toPolyG_cdivFF_exact`, the polynomial witness `hNum · resDen = resNum · Dstar`, and the cleared identity
follows by `ring`. This mirrors §2's `hermiteReduce_residual_correct` (the rational Hermite residual,
recovered by exact division) and §3.5's `toPolyG_cdivFF_exact` step style: the identity is gated only on
the exact-division certificate of the single `cdivG` call, exactly the polynomial cleared identity
`resNum·Dstar = hNum·resDen` that the `native_decide` evidence pins. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### The cleared residual identity over `(RatFunc ℚ)[X]`
The pure-polynomial algebra: from the exact-division witness `hNum · resDen = resNum · Dstar` (with
`resNum = a·gden² − d·gprimeNum`, `resDen = d·gden²`), the Hermite cleared identity
`(gprimeNum·Dstar + hNum·gden²)·d = a·(gden²·Dstar)` follows by `ring`. Stated abstractly in a commutative
ring so it applies verbatim to the `toPolyG`-images of the engine's outputs. -/

/-- **The cleared Hermite residual identity** (commutative-ring algebra): if `hNum · (d·gden²) =
(a·gden² − d·gprimeNum) · Dstar` (the exact-division witness recovering the residual numerator `hNum` over
the squarefree radical `Dstar`), then the Hermite cleared identity `(gprimeNum·Dstar + hNum·gden²)·d =
a·(gden²·Dstar)` holds. Pure `ring` from the witness; the algebraic core of `D(g) + h = f` once the
fractions are cleared. -/
theorem hermiteTower_cleared_of_exact {R : Type*} [CommRing R]
    (a d gprimeNum gden hNum Dstar : R)
    (hwit : hNum * (d * (gden * gden)) = (a * (gden * gden) - d * gprimeNum) * Dstar) :
    (gprimeNum * Dstar + hNum * (gden * gden)) * d = a * ((gden * gden) * Dstar) := by
  linear_combination hwit

/-! ### The exact-division witness through `toPolyG`
The engine's residual numerator is `hNum = cdivG fuel (cmulG resNum Dstar) resDen`. Under the
exact-division precondition (`cmodG fuel (resNum·Dstar) resDen` reads to `0` over ℚ(x)[t]) and a nonzero
divisor `resDen`, `toPolyG_cdivFF_exact` gives the polynomial witness
`toPolyG (resNum·Dstar) = toPolyG hNum · toPolyG resDen` over `(RatFunc ℚ)[X]`. -/

/-- **Exact-division witness over ℚ(x)[t]**: if the divisor `q` is nonzero (`cnormG q ≠ []`), fuel bounds
the dividend length, and `toPolyG q ∣ toPolyG p`, then `toPolyG (cdivG fuel p q) · toPolyG q = toPolyG p`
— the `cdivG`/`cdivFF` exact-division factorization with the factors in the order the cleared identity
consumes. The thin reorientation of `toPolyG_cdivFF_exact`. -/
theorem toPolyG_cdivG_exact_mul (fuel : ℕ) (p q : CPolyG QFunNZ)
    (hq0 : cnormG q ≠ []) (hfuel : (cnormG p : List QFunNZ).length ≤ fuel)
    (hQdvd : toPolyG q ∣ toPolyG p) :
    toPolyG (cdivG fuel p q) * toPolyG q = toPolyG p := by
  rw [show cdivG fuel p q = CPolyG.cdivFF fuel p q from rfl]
  exact (toPolyG_cdivFF_exact fuel p q hq0 hfuel hQdvd).symm

/-! ### The headline — the cleared Hermite identity for ALL inputs
Combining the exact-division witness with the cleared-identity algebra. The output of
`cHermiteReduceTower` is `((gnum, gden), (hNum, Dstar))`; with `D = cmonomialDeriv Dt`,
`gprimeNum = D(gnum)·gden − gnum·D(gden)`, the Hermite cleared identity
`(gprimeNum·Dstar + hNum·gden²)·d = a·(gden²·Dstar)` is the all-inputs generalization of
`hermiteTower_example`'s `cisZeroG`-check. We state it through `toPolyG` over the field ℚ(x), where the
monomial derivation `D` is `implicitDeriv (toPolyG Dt)` (`toPolyG_cmonomialDeriv`). -/

/-- **`cHermiteReduceTower` satisfies the cleared Hermite identity** (abstract, all inputs) over the field
ℚ(x). Write `((gnum, gden), (hNum, Dstar)) = cHermiteReduceTower Dt fuel a d` and let `D = cmonomialDeriv
Dt` be the monomial derivation, `gprimeNum = D(gnum)·gden − gnum·D(gden)` the quotient-rule numerator of
`D(gnum/gden)`. Under the **exact-division certificate** — the residual numerator
`hNum = cdivG fuel (resNum·Dstar) resDen` divides exactly (`cmodG fuel (resNum·Dstar) resDen` reads to
`0`), with `resNum = a·gden² − d·gprimeNum`, `resDen = d·gden²` *as the raw (pre-`cnormG`) reduction
quantities* — and a nonzero divisor `resDen` with sufficient fuel, the cleared identity
`(gprimeNum·Dstar + hNum·gden²)·d = a·(gden²·Dstar)` holds in `(RatFunc ℚ)[X]`. This is `D(gnum/gden) +
hNum/Dstar = a/d` cleared over the common denominator `gden²·Dstar·d` (the monomial-derivation analogue of
`hermiteReduce_residual_correct`). The single hypothesis is precisely the polynomial cleared identity
`resNum·Dstar = hNum·resDen` the `native_decide` evidence (`hermiteTower_example`) pins. -/
theorem cHermiteReduceTower_cleared_identity (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ)
    -- the raw (pre-`cnormG`) reduction quantities the engine computes internally
    (gnumR gdenR DstarR gprimeNum resNum resDen hNumR : CPolyG QFunNZ)
    (_hgnum : gnumR = (cHermiteReduceTower Dt fuel a d).1.1)
    (_hgden : gdenR = (cHermiteReduceTower Dt fuel a d).1.2)
    (_hDstar : DstarR = (cHermiteReduceTower Dt fuel a d).2.2)
    -- the residual quotient-rule numerator and the exact-division divisor / dividend / quotient
    (hgprime : gprimeNum
      = csubG (cmulG (cmonomialDeriv Dt gnumR) gdenR) (cmulG gnumR (cmonomialDeriv Dt gdenR)))
    (hresNum : resNum = csubG (cmulG a (cmulG gdenR gdenR)) (cmulG d gprimeNum))
    (hresDen : resDen = cmulG d (cmulG gdenR gdenR))
    (hhNum : hNumR = cdivG fuel (cmulG resNum DstarR) resDen)
    -- the exact-division certificate + nonzero divisor + fuel bound
    (hq0 : cnormG resDen ≠ [])
    (hfuel : (cnormG (cmulG resNum DstarR) : List QFunNZ).length ≤ fuel)
    (hdvd : toPolyG resDen ∣ toPolyG (cmulG resNum DstarR)) :
    ((toPolyG (cmonomialDeriv Dt gnumR) * toPolyG gdenR
        - toPolyG gnumR * toPolyG (cmonomialDeriv Dt gdenR)) * toPolyG DstarR
        + toPolyG hNumR * (toPolyG gdenR * toPolyG gdenR)) * toPolyG d
      = toPolyG a * ((toPolyG gdenR * toPolyG gdenR) * toPolyG DstarR) := by
  -- the exact-division witness: `toPolyG hNumR · toPolyG resDen = toPolyG (resNum · Dstar)`
  have hwit0 : toPolyG hNumR * toPolyG resDen = toPolyG (cmulG resNum DstarR) := by
    rw [hhNum]; exact toPolyG_cdivG_exact_mul fuel (cmulG resNum DstarR) resDen hq0 hfuel hdvd
  -- read both sides through the `toPolyG` ring homomorphisms
  have hgp : toPolyG gprimeNum
      = toPolyG (cmonomialDeriv Dt gnumR) * toPolyG gdenR
          - toPolyG gnumR * toPolyG (cmonomialDeriv Dt gdenR) := by
    rw [hgprime, toPolyG_csubG, toPolyG_cmulG, toPolyG_cmulG]
  have hwit : toPolyG hNumR * (toPolyG d * (toPolyG gdenR * toPolyG gdenR))
      = (toPolyG a * (toPolyG gdenR * toPolyG gdenR)
          - toPolyG d * toPolyG gprimeNum) * toPolyG DstarR := by
    have hlhs : toPolyG resDen = toPolyG d * (toPolyG gdenR * toPolyG gdenR) := by
      rw [hresDen, toPolyG_cmulG, toPolyG_cmulG]
    have hrhs : toPolyG (cmulG resNum DstarR)
        = (toPolyG a * (toPolyG gdenR * toPolyG gdenR) - toPolyG d * toPolyG gprimeNum)
            * toPolyG DstarR := by
      rw [hresNum, toPolyG_cmulG, toPolyG_csubG, toPolyG_cmulG, toPolyG_cmulG, toPolyG_cmulG]
    rw [← hlhs, hwit0, hrhs]
  -- the cleared identity, by the ring algebra of `hermiteTower_cleared_of_exact`
  rw [hgp] at hwit
  linear_combination hwit

/-- The abstract cleared Hermite identity is the all-inputs (non-`native_decide`) generalization of the
`hermiteTower_example` check: under the exact-division certificate, the computed reduction satisfies
`(D(gnum)·gden − gnum·D(gden))·Dstar + hNum·gden²) · d = a · (gden²·Dstar)` — i.e. `D(g) + h = f`
cleared over ℚ(x)[t]. -/
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d gnumR gdenR DstarR gprimeNum resNum resDen hNumR :
      CPolyG QFunNZ)
    (hgnum : gnumR = (cHermiteReduceTower Dt fuel a d).1.1)
    (hgden : gdenR = (cHermiteReduceTower Dt fuel a d).1.2)
    (hDstar : DstarR = (cHermiteReduceTower Dt fuel a d).2.2)
    (hgprime : gprimeNum
      = csubG (cmulG (cmonomialDeriv Dt gnumR) gdenR) (cmulG gnumR (cmonomialDeriv Dt gdenR)))
    (hresNum : resNum = csubG (cmulG a (cmulG gdenR gdenR)) (cmulG d gprimeNum))
    (hresDen : resDen = cmulG d (cmulG gdenR gdenR))
    (hhNum : hNumR = cdivG fuel (cmulG resNum DstarR) resDen)
    (hq0 : cnormG resDen ≠ [])
    (hfuel : (cnormG (cmulG resNum DstarR) : List QFunNZ).length ≤ fuel)
    (hdvd : toPolyG resDen ∣ toPolyG (cmulG resNum DstarR)) :
    ((toPolyG (cmonomialDeriv Dt gnumR) * toPolyG gdenR
        - toPolyG gnumR * toPolyG (cmonomialDeriv Dt gdenR)) * toPolyG DstarR
        + toPolyG hNumR * (toPolyG gdenR * toPolyG gdenR)) * toPolyG d
      = toPolyG a * ((toPolyG gdenR * toPolyG gdenR) * toPolyG DstarR) :=
  cHermiteReduceTower_cleared_identity Dt fuel a d gnumR gdenR DstarR gprimeNum resNum resDen hNumR
    hgnum hgden hDstar hgprime hresNum hresDen hhNum hq0 hfuel hdvd

#print axioms cHermiteReduceTower_cleared_identity
