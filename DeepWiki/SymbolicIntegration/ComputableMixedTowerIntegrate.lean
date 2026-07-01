import DeepWiki.SymbolicIntegration.ComputableTranscendentalOverAlgebraic
import DeepWiki.SymbolicIntegration.ComputableTowerRischDE
import DeepWiki.SymbolicIntegration.ComputableHyperexpSpecial

/-! # The first transcendental INTEGRAL over an algebraic base (Bronstein 1990, mixed tower)
`ComputableTranscendentalOverAlgebraic` made the radical field `RadX3 = ℚ(x)[√(x³+1)]` a full
`CField`+`CDiffField`+`CFieldDomain` Risch base, **unconditionally** — so a transcendental monomial `t`
stacks on top of the algebraic `√(x³+1)` and its derivation runs (`radX3_monomialDeriv_t2sq_eq_two_t2sq`,
`radX3_monomialDeriv_genT_eq`). That gave the **derivative** at transcendental-over-algebraic level. This
file takes the next step: the **integral**. The full poly/special tower integrator
`CPolyG.cIntegrateGFull` (`ComputableTowerRischDE`) is `[CField α] [CDiffField α] [CFracGcdCore α]
[CRischField α]`-generic; with the radical base supplying the first two (built in the enabler), we equip
`RadX3` with the remaining two and run `cIntegrateGFull` at `α = RadX3` — integrating a transcendental
monomial `t` **over** the algebraic `√(x³+1)`, the first transcendental-on-algebraic `∫` in DeepWiki.

* **`CFracGcdCore RadX3`** — `RadX3` is a genuine field (`y² − (x³+1)` is irreducible over ℚ(x),
  `irreducible_radX3`), so its polynomial ring `RadX3[t]` has the ordinary Euclidean gcd; the raw
  fraction-free gcd is `(cgcdExtG _).1` over `RadX3[t]`, **exactly** the `ℚ`-base recipe `instCFracGcdCoreQ`
  (a field's content is a unit). This is what `canonicalRepresentationFastG` / the Hermite reduction and
  the residue log part dispatch through.
* **`CRischField RadX3`** — the base RDE-over-the-field solver, now supplied by the **generic**
  `instCRischFieldRadExt` (`ComputableTranscendentalOverAlgebraic`, imported here) via
  `RadX3 = RadExt (QFunNZG ℚ) 2 (x³+1)`: scalar-`B` decoupling of `Dz + B·z = C` into the per-`y`-power
  base RDEs over ℚ(x) (the coupled-system case, non-scalar `B`, deferred). It replaces the earlier per-base
  conservative `f = 0 ∧ g = 0 ↦ 0` stub. The integrals below run the **`b = 0` primitive branch** of
  `cPolyRischDEG` (`cIntegratePolyG`, the term-by-term antiderivative), which **never** invokes
  `crischDESolve`, so they are unchanged by the swap; the generic instance is the better base solve now in
  scope for any deeper dispatch.

* **★ The headline** (`native_decide`): over `RadX3[t] = ℚ(x)[√(x³+1)][t]` with `t` primitive (`Dt = 1`),
  `cIntegrateGFull` integrates polynomial parts by the §5.4 primitive-base RDE branch and a normal part by
  Rothstein–Trager, **over the algebraic base** — the whole pipeline (canonical split, gcd over `RadX3[t]`,
  Hermite, residue logs) runs with `α = RadX3`:
  - `∫ t dt = t²/2` — the cleanest, the poly-part driver over the algebraic base, validated `D(∫f) = f`.
  - `∫ t² dt = t³/3` and `∫ (2t+1) dt = t²+t` — higher / mixed degree poly parts, validated `D(∫f) = f`.
  - `∫ dt/t = log t` — the **normal-part / Rothstein–Trager log** route over the algebraic base (a
    different driver path than the poly part), validated `D(log t) = 1/t`.

* **★ The algebraic-coefficient boundary** (an honest non-theorem, `native_decide`): `∫ y dt` does **not**
  validate `D(∫f) = f` through the primitive driver — because `y = √(x³+1)` is **not** a `D`-constant
  (`D(y) = ℓ·y ≠ 0`, `ℓ = f'/(2f)`), so the would-be antiderivative `y·t` has full-tower derivative
  `D(y·t) = ℓ·y·t + y ≠ y`. The `b = 0` poly driver is correct only on `D`-constant (here: ℚ) coefficients;
  the only `D`-constants of `RadX3` are ℚ. This is recorded as `mixedY_not_validated` — the genuine reason
  a transcendental-over-algebraic *polynomial* integral keeps ℚ coefficients in the part the primitive
  driver disposes (the algebraic coefficient enters through the **log argument**, not the poly part).

Each integral is validated by `checkIdentityG` (the cleared antiderivative identity `D(∫f) = f` over the
`RadX3` `CDiffField`), the same diagonal-radical derivation the enabler validated `D(y·t)` with.
Everything reduces in the native compiler: `RadX3` is the computable radical carrier (`CFieldDomain`
`Prop`-erased), `cIntegrateGFull` is list/field arithmetic, the gcd `cgcdExtG` is Euclid over `RadX3[t]`.
The instantiation is **pure reuse** — the integrator is taken verbatim; only the two missing base
typeclasses (`CFracGcdCore`/`CRischField`) are supplied for `RadX3`.

* **★★★ A top-level ∫ whose integration step DESCENDS through the algebraic RDE** (`native_decide`, the
  airtight end-to-end claim). The poly-driver integrals above never reach `crischDESolve` (their `b = 0`
  branch is pure term-by-term antidifferentiation); `mixedRde_radx3_descends` showed the *RDE solver*
  descend through `instCRischFieldRadExt`, but not an *integral*. The **hyperexponential special part**
  (Bronstein §5.10, `cIntegrateHyperexpLaurentG`, generic) closes this: for `t = exp` over the radical base
  (`Dt = η·t`, `η = 1`), the Laurent term `∫ a₋₁ t⁻¹` solves its base RDE
  `crischDESolve ((−1)·η) a₋₁` over `RadX3` with a **nonzero scalar** `(−1)·η = −1`, exactly the slice
  `instCRischFieldRadExt` scalar-decouples to the two per-`y`-power base RDEs over ℚ(x). So
  `∫ t⁻¹ = −t⁻¹` (`mixedHyperexpRecip_integral_descends`) and `∫ (t + t⁻¹) = t − t⁻¹`
  (`mixedHyperexpPolySpec_integral_descends`, a polynomial part *plus* the descending special part) are
  validated `D(∫f) = f` over the `RadX3` derivation — **an actual integral over the mixed tower whose
  special-part step recurses `RadX3[t] → crischDESolve over RadX3 → ℚ(x)`**. The descent is fed canonical
  Laurent coefficients; the full driver `cIntegrateHyperexpG`'s top entry now validates the same mixed-tower
  integral (`mixedHyperexpG_topEntry_validates`), so the earlier canonicalization-gap smoke test is gone. -/

namespace DeepWiki.SymbolicIntegration

open CPolyG

/-! ### The remaining base typeclass for the radical field `RadX3`

`cIntegrateGFull` needs `[CFracGcdCore α] [CRischField α]` beyond the `[CField α] [CDiffField α]` the
enabler built. We supply `CFracGcdCore RadX3` here; `CRischField RadX3` is now supplied by the **generic**
`instCRischFieldRadExt` (`ComputableTranscendentalOverAlgebraic`, imported), so the earlier per-base
conservative stub is retired — the scalar-decoupling solver resolves automatically via
`RadX3 = RadExt (QFunNZG ℚ) 2 (x³+1)`. -/

/-- **`CFracGcdCore RadX3`** — the raw fraction-free gcd over `RadX3[t]`. `RadX3` is a genuine field
(`y² − (x³+1)` is irreducible over ℚ(x), `irreducible_radX3`), so — exactly as for the constant base
`instCFracGcdCoreQ` — its content is a unit and the raw gcd is the **raw** Euclidean gcd
`(cgcdExtG _).1` over `RadX3[t]` (not monic; the public `cgcdFFCore` monic-normalizes at the top). The
Euclidean work is `[CField RadX3]`-only, so it reduces in the native compiler. This is what
`canonicalRepresentationFastG`, the Hermite reduction, and the residue log part dispatch through. -/
instance instCFracGcdCoreRadX3 : CFracGcdCore RadX3 where
  cgcdFFRawCore fuel p q := (CPolyG.cgcdExtG fuel p q).1

/-! ### Shared integrand data over `RadX3[t]`

The primitive monomial `t` (`Dt = 1`), the trivial denominator `d = 1`, and the residue candidate set. -/

/-- The primitive monomial derivative `Dt = 1` over `CPolyG RadX3 = ℚ(x)[√(x³+1)][t]` (`t` independent,
`t' = 1` — the primitive case). -/
def mixedDt : CPolyG RadX3 := [CField.one]

/-- The integrand denominator `d = 1` over `CPolyG RadX3` (for the pure polynomial parts). -/
def mixedD : CPolyG RadX3 := [CField.one]

/-- The residue candidate set over `RadX3` (`0`, `1` — the log integrand `1/t` has residue `1`). -/
def mixedCands : List RadX3 := [CField.zero, CField.one]

/-! ### ★ `∫ t dt = t²/2` over `RadX3[t] = ℚ(x)[√(x³+1)][t]` (`native_decide`)

The cleanest transcendental-over-algebraic integral: a **pure polynomial part** `f = t` over the radical
base, `t` primitive (`Dt = 1`). `cIntegrateGFull` splits `f = t` (polynomial part `fₚ = t`, no normal or
special part), solves `Dqₚ = t` by the §5.4 primitive-base branch (`b = 0`, so `cPolyRischDEG` hits
`cIntegratePolyG t = [0, 0, 1/2] = (1/2)t²`), and returns `(1/2)t²` with no logs. The poly-part driver
runs over the ALGEBRAIC base ℚ(x)[√(x³+1)], and the result differentiates back to `f`. -/

/-- The integrand `f = t` over `CPolyG RadX3` (numerator `t = [0, 1]`, denominator `1`): a pure polynomial
part that the reduced-case capstone leaves undisposed (handled by the full driver `cIntegrateGFull`). -/
def mixedTa : CPolyG RadX3 := [CField.zero, CField.one]

/-- **★ `∫ t dt = t²/2` over `RadX3[t] = ℚ(x)[√(x³+1)][t]`, and `D(∫f) = f`** (`native_decide`, the
milestone). The full driver `cIntegrateGFull` (canonical split + the §5.4 `b = 0` primitive-base RDE solve
`Dqₚ = t` + recombination) integrates the pure polynomial part `f = t` over the ALGEBRAIC base
ℚ(x)[√(x³+1)], returning `some res` whose rational part is `(1/2)t²`, and `res` satisfies the
antiderivative identity `D(res) = f` (`checkIdentityG`, cleared of denominators, with the `RadX3`
diagonal-radical `CDiffField` derivation). THE FIRST TRANSCENDENTAL INTEGRAL OVER AN ALGEBRAIC BASE —
`cIntegrateGFull` instantiated at `α = RadExt`. -/
theorem mixedT_integral_eq :
    (match CPolyG.cIntegrateGFull mixedDt 20 mixedTa mixedD mixedCands with
      | some res => CPolyG.checkIdentityG mixedDt res mixedTa mixedD
      | none => false) = true := by native_decide

/-! ### ★ `∫ t² dt = t³/3` and `∫ (2t+1) dt = t²+t` over `RadX3[t]` (`native_decide`)

Higher- and mixed-degree polynomial parts over the algebraic base, to show the primitive poly-part driver
disposes a genuine `RadX3[t]` polynomial term-by-term: `cIntegratePolyG [0,0,1] = [0,0,0,1/3] = t³/3`,
`cIntegratePolyG [1,2] = [0,1,1] = t²+t` (`∫(2t+1) = t²+t`). Both validated `D(∫f) = f`. -/

/-- The integrand `f = t²` over `CPolyG RadX3` (numerator `[0,0,1]`, a pure degree-`2` polynomial part). -/
def mixedT2a : CPolyG RadX3 := [CField.zero, CField.zero, CField.one]

/-- **★ `∫ t² dt = t³/3` over `RadX3[t]`, and `D(∫f) = f`** (`native_decide`): the full driver integrates
the degree-`2` polynomial part `f = t²` over the algebraic base to `t³/3` (`cIntegratePolyG [0,0,1] =
[0,0,0,1/3]`), and the result differentiates back to `f`. -/
theorem mixedT2_integral_eq :
    (match CPolyG.cIntegrateGFull mixedDt 20 mixedT2a mixedD mixedCands with
      | some res => CPolyG.checkIdentityG mixedDt res mixedT2a mixedD
      | none => false) = true := by native_decide

/-- The integrand `f = 2t + 1` over `CPolyG RadX3` (numerator `[1,2]`, a mixed-degree polynomial part). -/
def mixedLina : CPolyG RadX3 := [CField.one, CField.add CField.one CField.one]

/-- **★ `∫ (2t+1) dt = t²+t` over `RadX3[t]`, and `D(∫f) = f`** (`native_decide`): the full driver
integrates the mixed-degree polynomial part `f = 2t+1` over the algebraic base to `t²+t`
(`cIntegratePolyG [1,2] = [0,1,1]`), and the result differentiates back to `f`. -/
theorem mixedLin_integral_eq :
    (match CPolyG.cIntegrateGFull mixedDt 20 mixedLina mixedD mixedCands with
      | some res => CPolyG.checkIdentityG mixedDt res mixedLina mixedD
      | none => false) = true := by native_decide

/-! ### ★ `∫ dt/t = log t` over `RadX3[t]` — the normal-part / Rothstein–Trager log route (`native_decide`)

A different driver path than the poly part: the integrand `f = 1/t` is a pure **normal part**
(`dₙ = t` squarefree, no polynomial or special part), integrated by `cIntegrateReducedG` (Hermite — trivial
here — then the Rothstein–Trager residue log part `cLogPartG`), producing `log t` (residue `1` at the
argument `t`). The whole normal-part pipeline — the gcd over `RadX3[t]`, the residue resultant — runs
**over the algebraic base** `RadX3`. Validated `D(log t) = 1/t` (`checkIdentityG`, the log term
`c·D(v)/v = 1·(1)/t`). -/

/-- The integrand `f = 1/t` over `RadX3[t]` as `a/d` with `a = 1`, `d = t` (a pure normal part,
squarefree denominator `t`). -/
def mixedRecipNum : CPolyG RadX3 := [CField.one]

/-- The denominator `d = t = [0,1]` over `CPolyG RadX3` for `f = 1/t`. -/
def mixedRecipDen : CPolyG RadX3 := [CField.zero, CField.one]

/-- **★ `∫ dt/t = log t` over `RadX3[t]`, and `D(log t) = 1/t`** (`native_decide`): the full driver routes
`f = 1/t` (a pure normal part over the algebraic base, `dₙ = t` squarefree) through
`cIntegrateReducedG` — Hermite (trivial) then the Rothstein–Trager residue log part `cLogPartG` — producing
`log t` (residue `1` at argument `t`), and the result satisfies the antiderivative identity `D(∫f) = f`
(`checkIdentityG`, the log term `1·D(t)/t = 1/t`). THE NORMAL-PART / RESIDUE-LOG PIPELINE RUNS OVER THE
ALGEBRAIC BASE — a transcendental-over-algebraic integral producing a logarithm. -/
theorem mixedRecip_integral_eq :
    (match CPolyG.cIntegrateGFull mixedDt 20 mixedRecipNum mixedRecipDen mixedCands with
      | some res => CPolyG.checkIdentityG mixedDt res mixedRecipNum mixedRecipDen
      | none => false) = true := by native_decide

/-! ### ★ The algebraic-coefficient boundary: `∫ y dt` does NOT validate (`native_decide`, honest)

A genuine finding, not a bug. The poly-part primitive driver `cIntegratePolyG` is correct **only** when the
coefficients are `D`-constant. The only `D`-constants of `RadX3 = ℚ(x)[√(x³+1)]` are ℚ: for `a + b·y` to be
`D`-killed needs `D(a) = 0` (so `a ∈ ℚ`) and `D(b) + b·ℓ = 0` (so `b'/b = −ℓ = −f'/(2f)`, i.e. `b ∝ 1/√f ∉
ℚ(x)`). In particular `y = √(x³+1)` has `D(y) = ℓ·y ≠ 0`. So the would-be antiderivative `y·t` of `f = y`
has **full-tower** derivative `D(y·t) = D(y)·t + y·Dt = ℓ·y·t + y ≠ y`: the driver's `y·t` is *not* a
genuine antiderivative of `y`. We pin this: `cIntegrateGFull` returns a result on `f = y` (the poly driver
runs), but `checkIdentityG` is **false** — the `D(∫f) = f` identity fails. Hence a transcendental-over-
algebraic *polynomial* integral keeps ℚ coefficients in the primitive-driver part; the algebraic `y` enters
validated integrals only through the **log argument** (above), not as a poly coefficient. -/

/-- The integrand `f = y = √(x³+1)` over `CPolyG RadX3` — a degree-`0` `t`-polynomial whose single
coefficient is the radical generator `y = radX3Gen` (which is **not** a `D`-constant). -/
def mixedYa : CPolyG RadX3 := [radX3Gen]

/-- **★ `∫ y dt` does NOT satisfy `D(∫f) = f`** (`native_decide`, the honest boundary): on `f = y =
√(x³+1)` the full driver runs the `b = 0` poly branch and returns `some (y·t)`, but `checkIdentityG` is
**false** — because `y` is **not** a `D`-constant (`D(y) = ℓ·y ≠ 0`), the full-tower derivative of `y·t` is
`ℓ·y·t + y ≠ y`. The primitive poly driver is correct only on `D`-constant (ℚ) coefficients; an algebraic
coefficient `y` breaks the antiderivative identity. This is why validated transcendental-over-algebraic
*polynomial* integrals (above) keep ℚ poly coefficients, and the algebraic `y` enters a validated integral
only through the log argument. -/
theorem mixedY_not_validated :
    (match CPolyG.cIntegrateGFull mixedDt 20 mixedYa mixedD mixedCands with
      | some res => CPolyG.checkIdentityG mixedDt res mixedYa mixedD
      | none => false) = false := by native_decide

/-! ### ★★ STRETCH: a MULTI-LEVEL descent — an RDE over `RadX3[t]` that recurses into `crischDESolve`
over the algebraic `RadX3`, which itself decouples to ℚ(x) (`native_decide`)

The headline multi-level descent. `cIntegrateGFull`'s *polynomial part* runs `cPolyRischDEG Dt fuel [] fp …`
with `b = 0` — the pure-integration branch `cIntegratePolyG`, which **never** calls `crischDESolve`. So an
*integral* over `RadX3[t]` cannot, by construction, descend into the algebraic RDE. The genuine descent is
the full **RDE solver** `cRischDEG` over `RadX3[t]` with a **nonzero** coefficient `f`: then the §6.6
**primitive-cancellation** branch `cPolyRischDECancelPrimG` fires and recurses into
`CRischField.crischDESolve b₀ (lc c)` over `RadX3` (eq. 6.23) — and `b₀ = 1 : RadX3` is a nonzero **scalar**,
so the new `instCRischFieldRadExt` **decouples** it into the per-`y`-power base RDEs over ℚ(x). A genuine
THREE-level recursion: `RadX3[t]` →(§6.6 cancellation)→ `crischDESolve` over `RadX3` →(scalar decoupling)→
base RDEs over `ℚ(x)`.

We solve `Dy + 1·y = t + 1` over `RadX3[t]` (`t` primitive, `Dt = 1`), whose solution is `y = t`
(`D(t) + t = 1 + t`). `f = 1 ≠ 0` routes through cancellation, calling `crischDESolve (1 : RadX3) (lc c)`
on the new instance. -/

/-- The RDE coefficient `f = 1 ∈ RadX3[t]` (a **nonzero** degree-0 `t`-polynomial), forcing `cRischDEG`'s
§6.6 primitive-cancellation branch — the path that recurses into `crischDESolve` over `RadX3`. -/
def mixedRdeF : CPolyG RadX3 := [CField.one]

/-- The RDE coefficient denominator `fden = 1 ∈ RadX3[t]`. -/
def mixedRdeFden : CPolyG RadX3 := [CField.one]

/-- The RDE right-hand side `g = t + 1 ∈ RadX3[t]` for `Dy + 1·y = t + 1` (solution `y = t`). -/
def mixedRdeG : CPolyG RadX3 := [CField.one, CField.one]

/-- The RDE right-hand side denominator `gden = 1 ∈ RadX3[t]`. -/
def mixedRdeGden : CPolyG RadX3 := [CField.one]

/-- **The RDE over `RadX3[t]` is solved (returns `some`)** (`native_decide`): `cRischDEG` over
`RadX3[t] = ℚ(x)[√(x³+1)][t]` solves `Dy + 1·y = t + 1`, descending through the §6.6 primitive-cancellation
branch into `crischDESolve (1 : RadX3) (lc c)` over the algebraic base — the new `instCRischFieldRadExt`. -/
theorem mixedRde_radx3_isSome :
    (CPolyG.cRischDEG ([CField.one] : CPolyG RadX3) 60
      mixedRdeF mixedRdeFden mixedRdeG mixedRdeGden).isSome = true := by native_decide

/-- **★★ A MULTI-LEVEL RDE descent: `Dy + 1·y = t + 1` solved over `RadX3[t]`, recursing into the
algebraic `crischDESolve`** (`native_decide`, the stretch deliverable). `cRischDEG` over `RadX3[t]` returns
`some (ynum, yden)` with `y = ynum/yden = t`, and the RDE identity `D(ynum) + 1·ynum = (t+1)·yden` holds —
checked by `cisZeroG` of the cleared form over `RadX3[t]` (the tower derivation `cmonomialDeriv [1]`, `Dt =
1`, on the `RadX3` coefficients). The nonzero `f = 1` forced the §6.6 **primitive-cancellation** branch
`cPolyRischDECancelPrimG`, which recursed into `CRischField.crischDESolve (1 : RadX3) (lc c)` over the
algebraic base `RadX3 = ℚ(x)[√(x³+1)]` — the **generic** `instCRischFieldRadExt`, scalar-decoupling that
RDE into per-`y`-power base RDEs over ℚ(x). THE RISCH PIPELINE RECURSES THROUGH THE ALGEBRAIC LEVEL:
`RadX3[t] → crischDESolve over RadX3 → ℚ(x)`. -/
theorem mixedRde_radx3_descends :
    (match CPolyG.cRischDEG ([CField.one] : CPolyG RadX3) 60
        mixedRdeF mixedRdeFden mixedRdeG mixedRdeGden with
      | some (ynum, yden) =>
          CPolyG.cisZeroG (CPolyG.csubG
            (CPolyG.caddG (CPolyG.cmonomialDeriv ([CField.one] : CPolyG RadX3) ynum)
              (CPolyG.cmulG mixedRdeF ynum))
            (CPolyG.cmulG mixedRdeG yden))
      | none => false) = true := by native_decide

/-! ### ★★★ A genuine top-level ∫ over `RadX3[t]` that DESCENDS through `instCRischFieldRadExt` — the §5.10
hyperexponential Laurent integral over the algebraic base (`native_decide`)

The headline this file was reaching for: an actual **integral** (an `∫`-symbol call) over the *mixed* tower
`RadX3[t] = ℚ(x)[√(x³+1)][t]` whose **integration step descends through the algebraic RDE instance**
`instCRischFieldRadExt` — making "an actual integral descends through an algebraic level" airtight,
end-to-end, `D(∫f) = f`.

`mixedRde_radx3_descends` above showed the *RDE solver* `cRischDEG` descend; but an **integral** through the
poly driver (`cIntegrateGFull`/`cIntegratePolyG`, the `b = 0` branch) never calls `crischDESolve`, so it
cannot reach the algebraic level. The route that *does* is the **hyperexponential special part** (Bronstein
§5.10): for a hyperexponential `t` (`Dt = η·t`), the Laurent special integrator
`cIntegrateHyperexpLaurentG` (`ComputableHyperexpSpecial`, imported) integrates `∫ ∑ⱼ aⱼ tʲ` **term by
term**, each `∫ aⱼ tʲ` solved as the base RDE `Dqⱼ + (j·η)·qⱼ = aⱼ` via
`CRischField.crischDESolve (j·η) aⱼ`. That class method is `[CField α] [CDiffField α] [CFracGcdCore α]
[CRischField α]`-generic, so at **`α = RadX3`** the negative-index term `∫ a₋₁ t⁻¹` calls
`crischDESolve (−1·η) a₋₁` over `RadX3` with a **nonzero scalar** coefficient `−1·η = −1 : RadX3` — exactly
the slice the **generic** `instCRischFieldRadExt` decouples (`radExtRischDESolve`) into the two per-`y`-power
base RDEs over ℚ(x): `Dz₀ − z₀ = (a₋₁)₀` and `Dz₁ + (−1 + ℓ)·z₁ = (a₋₁)₁` (`ℓ = f'/(2f)`), each run by the
level-1 `CRischField (QFunNZG ℚ)`. THE INTEGRAL'S SPECIAL-PART STEP RECURSES `RadX3[t] →
crischDESolve over RadX3 → ℚ(x)` — the same descent as `mixedRde_radx3_descends`, but now fired *by an
integral*.

We integrate `t = exp` over the radical base (`Dt = η·t`, `η = 1`, `Dt = [0, 1]`), feeding the §5.10 Laurent
integrator the **canonical** Laurent coefficients directly (the clean entry, sidestepping the
canonical-split bloat noted at the end). Both `∫ t⁻¹ = −t⁻¹` (pure special, the single descending term) and
`∫ (t + t⁻¹) = t − t⁻¹` (a polynomial part `∫ t` *plus* the descending special part `∫ t⁻¹`) are validated
`D(∫f) = f` over the `RadX3` diagonal-radical `CDiffField` derivation (`checkIdentityG`). -/

/-- The hyperexponential monomial derivative `Dt = η·t = [0, 1]` over `RadX3[t] = ℚ(x)[√(x³+1)][t]`
(`t = exp`, `η = 1`): the transcendental-over-algebraic hyperexponential analogue of the primitive
`mixedDt = [1]`. The §5.10 Laurent integrator reads `η = cExpEtaG Dt = 1` off it. -/
def mixedHyperexpDt : CPolyG RadX3 := [CField.zero, CField.one]

/-- **`η = Dt/t = 1` over `RadX3`** (`native_decide`): `cExpEtaG` reads the hyperexponential coefficient
`η = 1 ∈ RadX3` off `Dt = [0, 1]`, so the §5.10 per-term shift `j·η` is just `j` — confirming `t = exp` over
the algebraic base. -/
theorem mixedHyperexp_eta_eq_one :
    CField.isZero (CField.sub (cExpEtaG 12 mixedHyperexpDt) (CField.one : RadX3)) = true := by
  native_decide

/-- The §5.10 per-term coefficient `(−1)·η = −1 ∈ RadX3` for the `t⁻¹` Laurent term (`j = −1`,
`cLaurentShiftG η (−1)`): a **nonzero scalar** over the radical base, exactly the coefficient
`crischDESolve` is handed when the special part descends. -/
def mixedLaurentShiftNeg1 : RadX3 := CPolyG.cLaurentShiftG (CField.one : RadX3) (-1)

/-- **The descending per-term coefficient `(−1)·η` is a NONZERO SCALAR over `RadX3`** (`native_decide`):
`RadExt.isScalar ((−1)·η) = true` (no `y`-component, so `radExtRischDESolve` takes the decoupling branch)
*and* `(−1)·η ≠ 0` (so the solve is genuine algebraic-RDE work, not the retired `f = 0 ∧ g = 0 ↦ 0` stub).
This is the coefficient the §5.10 `∫ t⁻¹` term forces into `crischDESolve` over the algebraic base. -/
theorem mixedLaurentShiftNeg1_nonzero_scalar :
    RadExt.isScalar mixedLaurentShiftNeg1 = true ∧
    CField.isZero mixedLaurentShiftNeg1 = false := by
  constructor <;> native_decide

/-- **★ The §5.10 `∫ t⁻¹` term DESCENDS through `instCRischFieldRadExt`** (`native_decide`): the per-term
base RDE `Dq₋₁ + (−1·η)·q₋₁ = 1` of `∫ 1·t⁻¹` — i.e. `CRischField.crischDESolve ((−1)·η) (1 : RadX3)` over
`RadX3 = ℚ(x)[√(x³+1)]` — returns `some` via the **generic** `instCRischFieldRadExt`, which (the coefficient
`(−1)·η = −1` being a nonzero scalar, `mixedLaurentShiftNeg1_nonzero_scalar`) **scalar-decouples** it into
the two base RDEs over ℚ(x) and dispatches each to the level-1 `CRischField (QFunNZG ℚ)`. THIS IS THE
ALGEBRAIC DESCENT FIRED BY AN INTEGRAL'S SPECIAL-PART STEP. -/
theorem mixedLaurentTerm_descends :
    (CRischField.crischDESolve mixedLaurentShiftNeg1 (CField.one : RadX3)).isSome = true := by
  native_decide

/-- **★★★ `∫ t⁻¹ = −t⁻¹` over `RadX3[t]` via the §5.10 Laurent integrator, descending through the algebraic
RDE, and `D(∫f) = f`** (`native_decide`, the headline). The §5.10 hyperexponential Laurent integrator
`cIntegrateHyperexpLaurentG (η = 1) [] [a₋₁ = 1]` over `RadX3 = ℚ(x)[√(x³+1)]` integrates the single special
term `∫ 1·t⁻¹` by solving its base RDE `Dq₋₁ − q₋₁ = 1` through `crischDESolve ((−1)·η) 1` — which
**descends through `instCRischFieldRadExt`** (`mixedLaurentTerm_descends`), decoupling to ℚ(x) — returning
`q₋₁ = −1`, so `∫ t⁻¹ = −t⁻¹` (rational part `−1/t`). Wrapped as an `IntegralResultG` (no logs) and validated
`D(−1/t) = 1/t` over the `RadX3` diagonal-radical `CDiffField` derivation (`checkIdentityG`, `f = 1/t`).
**AN ACTUAL INTEGRAL OVER THE MIXED TOWER, WHOSE INTEGRATION STEP DESCENDS THROUGH THE ALGEBRAIC LEVEL.** -/
theorem mixedHyperexpRecip_integral_descends :
    (match CPolyG.cIntegrateHyperexpLaurentG (CField.one : RadX3) [] [CField.one] with
      | some (num, den) =>
          CPolyG.checkIdentityG mixedHyperexpDt ⟨(num, den), []⟩ [CField.one] [CField.zero, CField.one]
      | none => false) = true := by native_decide

/-- **★★★ `∫ (t + t⁻¹) = t − t⁻¹` over `RadX3[t]` via the §5.10 Laurent integrator, the special part
descending through the algebraic RDE, and `D(∫f) = f`** (`native_decide`, the headline+). A Laurent
polynomial with a **polynomial part `t`** (positive index `a₁ = 1`) *and* a **special part `t⁻¹`** (negative
index `a₋₁ = 1`) over the algebraic base. `cIntegrateHyperexpLaurentG (η = 1) [0, 1] [1]` integrates each
term through its own base RDE over `RadX3`: `∫ t` solves `Dq₁ + (1·η)·q₁ = 1` (`q₁ = 1`), and the
**descending** `∫ t⁻¹` solves `Dq₋₁ + (−1·η)·q₋₁ = 1` (`crischDESolve` through `instCRischFieldRadExt`,
decoupling to ℚ(x), `q₋₁ = −1`); recombining gives `t − t⁻¹` (rational part `(t² − 1)/t`). Validated
`D(t − t⁻¹) = t + t⁻¹` over the `RadX3` `CDiffField` derivation (`checkIdentityG`, `f = (t²+1)/t`). THE
INTEGRAL OF A POLY-PLUS-SPECIAL LAURENT FORM OVER THE MIXED TOWER, WHOSE SPECIAL-PART STEP DESCENDS THROUGH
THE ALGEBRAIC LEVEL. -/
theorem mixedHyperexpPolySpec_integral_descends :
    (match CPolyG.cIntegrateHyperexpLaurentG (CField.one : RadX3) [CField.zero, CField.one]
        [CField.one] with
      | some (num, den) =>
          CPolyG.checkIdentityG mixedHyperexpDt ⟨(num, den), []⟩
            [CField.one, CField.zero, CField.one] [CField.zero, CField.one]
      | none => false) = true := by native_decide

/-! ### ★ The full `cIntegrateHyperexpG` top entry now routes over `RadX3` (`native_decide`)

The §5.10 Laurent integrator above is the clean, canonical-coefficient entry point for watching the descent
step directly. The full hyperexponential driver now succeeds on the same `f = (t²+1)/t = t + t⁻¹` input too:
`canonicalRepresentationFastG` feeds the special part into `cIntegrateHyperexpG`, the base RDE over `RadX3`
descends through `instCRischFieldRadExt`, and the returned `IntegralResultG` validates the cleared identity
`D(∫f) = f`. This removes the old representation-sensitive top-entry gap from this example. -/

/-- **`cIntegrateHyperexpG`'s top entry validates over `RadX3`** (`native_decide`): on `f = (t²+1)/t =
t + t⁻¹` over `RadX3[t]`, the full hyperexponential driver returns `some res` and `checkIdentityG` confirms
`D(res) = f`. -/
theorem mixedHyperexpG_topEntry_validates :
    (match CPolyG.cIntegrateHyperexpG mixedHyperexpDt 20 [CField.one, CField.zero, CField.one]
        [CField.zero, CField.one] [CField.zero, CField.one] with
      | some res =>
          CPolyG.checkIdentityG mixedHyperexpDt res [CField.one, CField.zero, CField.one]
            [CField.zero, CField.one]
      | none => false) = true := by native_decide

/-! ### `#print axioms` — the transcendental-over-algebraic integrals

Each result carries the standard `[propext, Classical.choice, Quot.sound]` plus the `native_decide`
compiler axiom (`native`) — no `sorry`, no extra axiom. `cIntegrateGFull` (canonical split + §5.4 primitive
poly-part RDE solve + Rothstein–Trager residue logs + recombination) computes over `RadX3[t] =
ℚ(x)[√(x³+1)][t]`, and each validated result differentiates back to `f` through the `RadX3`
diagonal-radical `CDiffField` derivation — the first transcendental integrals over an algebraic base, with
the algebraic-coefficient boundary recorded honestly. -/

-- ★ `∫ t dt = t²/2` over ℚ(x)[√(x³+1)][t] (the milestone):
#print axioms mixedT_integral_eq
-- ★ `∫ t² dt = t³/3`, `∫ (2t+1) dt = t²+t` (higher / mixed degree poly parts):
#print axioms mixedT2_integral_eq
#print axioms mixedLin_integral_eq
-- ★ `∫ dt/t = log t` (normal-part / residue-log route over the algebraic base):
#print axioms mixedRecip_integral_eq
-- ★ The honest boundary: `∫ y dt` does not validate (y is not a D-constant):
#print axioms mixedY_not_validated
-- ★★ The multi-level descent: an RDE over RadX3[t] recursing into crischDESolve over RadX3 → ℚ(x):
#print axioms mixedRde_radx3_descends
-- ★★★ A top-level ∫ (§5.10 Laurent) over RadX3[t] whose integration step DESCENDS through the
-- algebraic RDE instCRischFieldRadExt, validated D(∫f) = f:
#print axioms mixedHyperexpRecip_integral_descends
#print axioms mixedHyperexpPolySpec_integral_descends
-- ★ The full cIntegrateHyperexpG top entry now validates over RadX3:
#print axioms mixedHyperexpG_topEntry_validates

end DeepWiki.SymbolicIntegration
