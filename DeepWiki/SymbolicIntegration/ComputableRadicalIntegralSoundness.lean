import DeepWiki.SymbolicIntegration.ComputableRadicalDerivationInvariant
import DeepWiki.SymbolicIntegration.ComputableSplitFactorTowerCorrectG

/-! # The first abstractly-verified algebraic (radical) integral — `D(v) = g` via `radDeriv`
`ComputableRadicalExtension` / `ComputableRadicalRationalDriver` *compute* simple-radical antiderivatives
(`∫ R/(B√ρ)`) and validate `D(v) = g` for concrete integrands by `native_decide`;
`ComputableRadicalDerivationInvariant` proves the keystone **`toPolyG_radDeriv`** — through the Horner
bridge `toPolyG : RadElem α → K[X]` (with `X` the radical generator `y`, `K = CFieldSpec.K α`), the
diagonal derivation `radDeriv n f` *is* Mathlib's `Differential.implicitDeriv (C (toK ℓ) · X)` for the
rule `y' = ℓ·y`, `ℓ = logDerRadicand n f = f'/(nf)`.

This file takes the first step from "`radDeriv` is a derivation" to "**the integrator is sound**": it
proves a concrete algebraic integral *correct as a general theorem* — `radDeriv n f v = g` in the genuine
field `K[X]`, via the keystone + `implicitDeriv_X` + `ring`, with **no `native_decide`** (axiom-clean
`[propext, Classical.choice, Quot.sound]`). The seed of the soundness capstone `D(∫f) = f`.

* **`IsRadicalRationalIntegral n f g v`** — the soundness predicate (rational part, no log term):
  `radDeriv n f v = g` read in `K[X]` (`toPolyG (radDeriv n f v) = toPolyG g`). The named target the
  capstone grows into.

* **`isRadicalRationalIntegral_radGen`** — the abstractly-verified integral
  **`∫ (f'/(nf))·√f dx = √f`**, i.e. `D(√f) = (f'/(nf))·√f` (`radDeriv n f radGen = [zero, logDerRadicand
  n f]`). The antiderivative `v = radGen = y = √f` is the polynomial-in-`y` element `[0,1]` (no
  denominator), so the proof stays in the ring `RadElem α` and routes entirely through `toPolyG_radDeriv`
  + `implicitDeriv_X` (`toPolyG radGen = X`, `implicitDeriv v X = v`). General in `n`, the radicand `f`,
  and the base `α` — needs **no** `n·toK f ≠ 0` hypothesis (the generator identity `y' = ℓ·y` holds
  unconditionally). Over `α = ℚ(x)`, `n = 2`, `f = x³+1` this is the `native_decide` fact
  `radDeriv_radGen_eq`, here proven abstractly.

* **`isRadicalRationalIntegral_linear`** — the same for a *general* degree-`< n` antiderivative
  `v = a₀ + a₁·y` (`[a₀, a₁]`): `D(a₀ + a₁y) = D(a₀) + (D(a₁) + a₁ℓ)·y`, the diagonal derivation made an
  honest `K[X]` identity. Shows the soundness holds for any two-term radical antiderivative, not only the
  bare generator.

What the **general** rational-part soundness `radDeriv n f (radIntegrateRational … g) = g` additionally
needs is recorded in the closing module docstring: the *algorithm-correctness* invariant of the Hermite /
undetermined-coefficient reductions (each `radReduceCaseᵢIterate` step lowers a denominator multiplicity /
`deg C` while preserving `radDeriv(running v) + leftover = integrand`), reduced to the cleared single-step
identities already validated. This file supplies the derivation half abstractly; the reduction-invariant
half is the scoped follow-up. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace RadElem

variable {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]

/-! ### The Horner readings `toPolyG radGen = X` and `toPolyG [0, c] = C(toK c)·X`

The radical antiderivatives in play are pure-`y` (and, more generally, degree-`< n`) elements; their
`toPolyG` images are the corresponding low-degree polynomials in `X`. These two readings are all the
`toPolyG`-side computation the concrete soundness proofs need (`radGen = [0,1]`, the integrand `[0, ℓ]`). -/

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **`toPolyG radGen = X`** — the radical generator `y = √f` (`radGen = [0, 1]`) reads as the formal
variable `X` under the Horner bridge (`toK 0 = 0`, `toK 1 = 1`). The single fact that turns
`implicitDeriv … X = …` into a statement about `radDeriv radGen`. -/
theorem toPolyG_radGen : CPolyG.toPolyG (radGen : RadElem α) = X := by
  show CPolyG.toPolyG [CField.zero, CField.one] = X
  rw [CPolyG.toPolyG_cons, CPolyG.toPolyG_cons, CPolyG.toPolyG_nil, mul_zero, add_zero,
    CFieldSpec.toK_zero, CFieldSpec.toK_one, map_zero, map_one, zero_add, mul_one]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **`toPolyG [zero, c] = C (toK c) · X`** — the pure-`y` element `c·y` (`[0, c]`) reads as `C(toK c)·X`
(its only nonzero coefficient is at degree `1`). The reading of an `R/y`-form radical antiderivative
(`c·y`) and of a diagonal-derivation `y`-component. -/
theorem toPolyG_zero_cons (c : α) :
    CPolyG.toPolyG ([CField.zero, c] : RadElem α) = Polynomial.C (CFieldSpec.toK c) * X := by
  rw [CPolyG.toPolyG_cons, CPolyG.toPolyG_cons, CPolyG.toPolyG_nil, mul_zero, add_zero,
    CFieldSpec.toK_zero, map_zero, zero_add]
  ring

/-! ### The soundness predicate and the first abstractly-verified algebraic integral

`IsRadicalRationalIntegral n f g v` says the radical element `v` is an antiderivative of the integrand `g`
in `F(y) = α[y]/(yⁿ − f)`, *rational part only* (no `Σ cᵢ log uᵢ` term): the genuine-field reading of
`radDeriv n f v = g`. The concrete witness is `v = √f` against `g = (f'/(nf))·√f`. -/

/-- **The radical rational-integral soundness predicate** `IsRadicalRationalIntegral n f g v` — the radical
element `v` integrates `g` over `α[y]/(yⁿ − f)`, *rational part* (no logarithmic term): the genuine-field
identity `toPolyG (radDeriv n f v) = toPolyG g` in `K[X]` (`K = CFieldSpec.K α`, `X` the generator `y`).
The named soundness target the capstone `D(∫g) = g` grows into; an instance is a concrete algebraic
integral proven correct **abstractly** (not by `native_decide`). -/
def IsRadicalRationalIntegral (n : ℕ) (f g v : RadElem α) : Prop :=
  CPolyG.toPolyG (radDeriv n (f.headD CField.zero) v) = CPolyG.toPolyG g

/-- **★ The abstractly-verified algebraic integral `∫ (f'/(nf))·√f dx = √f`** — `D(√f) = (f'/(nf))·√f`
in the genuine field `K[X]`: `toPolyG (radDeriv n f radGen) = toPolyG [zero, logDerRadicand n f]`. The
antiderivative `v = radGen = y = √f` is `[0,1]` (a polynomial in `y`, no denominator), so the whole proof
is the keystone `toPolyG_radDeriv` + `toPolyG_radGen` (`toPolyG radGen = X`) + Mathlib's `implicitDeriv_X`
(`implicitDeriv v X = v`): `toPolyG (radDeriv n f radGen) = implicitDeriv (C(toK ℓ)·X) X = C(toK ℓ)·X =
toPolyG [0, ℓ]`. General in `n`, the radicand `f`, and `α`; needs **no** `n·toK f ≠ 0` (the generator
identity `y' = ℓ·y` is unconditional). This is the `native_decide` fact `radDeriv_radGen_eq` proven as a
general theorem — the first abstractly-verified simple-radical integral. -/
theorem toPolyG_radDeriv_radGen (n : ℕ) (f : α) :
    CPolyG.toPolyG (radDeriv n f (radGen : RadElem α))
      = CPolyG.toPolyG ([CField.zero, logDerRadicand n f] : RadElem α) := by
  rw [toPolyG_radDeriv, toPolyG_radGen, Differential.implicitDeriv_X,
    toPolyG_zero_cons (logDerRadicand n f)]

/-- **★ The radical integral `∫ (f'/(nf))·√f = √f` as a soundness instance** —
`IsRadicalRationalIntegral n [f] g radGen` with the integrand `g = [zero, logDerRadicand n f] =
(f'/(nf))·y`. The first concrete algebraic integral packaged as the named soundness predicate, proven
abstractly via `toPolyG_radDeriv_radGen` (`[f].headD = f` exposes the radicand to `radDeriv`). -/
theorem isRadicalRationalIntegral_radGen (n : ℕ) (f : α) :
    IsRadicalRationalIntegral n [f] ([CField.zero, logDerRadicand n f]) (radGen : RadElem α) := by
  show CPolyG.toPolyG (radDeriv n (([f] : RadElem α).headD CField.zero) radGen) = _
  rw [List.headD_cons, toPolyG_radDeriv_radGen]

/-! ### A general degree-`< n` antiderivative: `D(a₀ + a₁y) = D(a₀) + (D(a₁) + a₁ℓ)·y`

Beyond the bare generator, the soundness holds for any two-term radical element `v = a₀ + a₁y` — the
diagonal derivation `radDeriv` reads, through `toPolyG`, as the honest `K[X]` derivation
`implicitDeriv (C(toK ℓ)·X)`, so `D(a₀ + a₁y)` is `D(a₀) + (D(a₁) + a₁·ℓ)·y` exactly (no `y`-power
mixing, no quotient reduction — `v` has degree `< n` for `n ≥ 2`). The integrand it integrates is read
off the diagonal formula. -/

/-- **★ The diagonal-derivation identity for a two-term radical antiderivative** —
`toPolyG (radDeriv n f [a₀, a₁]) = toPolyG [D(a₀), D(a₁) + a₁·ℓ]` with `ℓ = logDerRadicand n f`: the
genuine-field reading of `D(a₀ + a₁y) = D(a₀) + (D(a₁) + a₁·ℓ)·y`, the diagonal derivation made an honest
`K[X]` identity (keystone + `implicitDeriv` on `C(toK a₀) + C(toK a₁)·X`, `ring`). Shows the radical
integrator's `D(v) = g` is sound for *any* degree-`< n` antiderivative `v = a₀ + a₁y`, not only the
generator. -/
theorem toPolyG_radDeriv_linear (n : ℕ) (f a₀ a₁ : α) :
    CPolyG.toPolyG (radDeriv n f ([a₀, a₁] : RadElem α))
      = CPolyG.toPolyG ([CDiffField.cderiv a₀,
          CField.add (CDiffField.cderiv a₁) (CField.mul a₁ (logDerRadicand n f))] : RadElem α) := by
  rw [toPolyG_radDeriv]
  -- read `toPolyG [a₀, a₁] = C(toK a₀) + C(toK a₁)·X` and the target coefficients through `toK`
  have hv : CPolyG.toPolyG ([a₀, a₁] : RadElem α)
      = Polynomial.C (CFieldSpec.toK a₀) + Polynomial.C (CFieldSpec.toK a₁) * X := by
    rw [CPolyG.toPolyG_cons, CPolyG.toPolyG_cons, CPolyG.toPolyG_nil, mul_zero, add_zero]; ring
  -- `implicitDeriv` is a `Derivation`: `D(C a₀ + C a₁·X) = D(C a₀) + (C a₁·D X + X·D(C a₁))` (Leibniz on
  -- the product, additive on the sum); `D(C b) = C b'`, `D X = C(toK ℓ)·X`.
  rw [hv, map_add, Derivation.leibniz, Differential.implicitDeriv_C, Differential.implicitDeriv_C,
    Differential.implicitDeriv_X, smul_eq_mul, smul_eq_mul]
  -- the RHS coefficients, expanded through the `toK` homomorphism laws and `toK_cderiv`
  rw [CPolyG.toPolyG_cons, CPolyG.toPolyG_cons, CPolyG.toPolyG_nil, mul_zero, add_zero,
    CFieldSpec.toK_add, CFieldSpec.toK_mul, CDiffFieldSpec.toK_cderiv, CDiffFieldSpec.toK_cderiv,
    map_add, map_mul]
  ring

/-- **★ The two-term radical integral as a soundness instance** —
`IsRadicalRationalIntegral n [f] g [a₀, a₁]` with the integrand `g = [D(a₀), D(a₁) + a₁·ℓ]`
(`ℓ = logDerRadicand n f`): the antiderivative `v = a₀ + a₁y` integrates `D(a₀) + (D(a₁) + a₁ℓ)·y`,
packaged as the named predicate and proven abstractly via `toPolyG_radDeriv_linear`. -/
theorem isRadicalRationalIntegral_linear (n : ℕ) (f a₀ a₁ : α) :
    IsRadicalRationalIntegral n [f]
      ([CDiffField.cderiv a₀,
        CField.add (CDiffField.cderiv a₁) (CField.mul a₁ (logDerRadicand n f))])
      ([a₀, a₁] : RadElem α) := by
  show CPolyG.toPolyG (radDeriv n (([f] : RadElem α).headD CField.zero) [a₀, a₁]) = _
  rw [List.headD_cons, toPolyG_radDeriv_linear]

end RadElem

/-! ### ★ The concrete `√(x³+1)` integral, abstractly: `∫ (3x²/(2(x³+1)))·√(x³+1) dx = √(x³+1)`

The engine's `native_decide` fact `radDeriv_radGen_eq` (`ComputableRadicalExtension`) — `D(√(x³+1)) =
(3x²/(2(x³+1)))·√(x³+1)` over `α = QFunNZG ℚ ≅ ℚ(x)`, `n = 2`, `f = x³+1` — now follows from the **general
theorem** `RadElem.toPolyG_radDeriv_radGen` specialized to that base, *without* `native_decide`. The
abstract `toPolyG`-equality in `K[X]` (`K = CFieldSpec.K (QFunNZG ℚ)`) is the faithful field-level
statement; `radIsZero (radSub …) = true` is its `cisZeroG`-test form, here a corollary of the abstract
identity rather than a separate kernel computation. -/

open RadElem

/-- **★ `∫ (3x²/(2(x³+1)))·√(x³+1) dx = √(x³+1)` over `ℚ(x)`, abstractly** — `D(√(x³+1)) =
(3x²/(2(x³+1)))·√(x³+1)` as the genuine-field identity `toPolyG (radDeriv 2 (x³+1) radGen) = toPolyG [0,
3x²/(2(x³+1))]` in `K[X]`, `K = CFieldSpec.K (QFunNZG ℚ)`. The engine's `native_decide` carrier check
`radDeriv_radGen_eq` proven as a corollary of the general `toPolyG_radDeriv_radGen` — the first concrete
**algebraic** integral verified abstractly (`[propext, Classical.choice, Quot.sound]`, no
`native_decide`). The radicand `radicandX3p1 = x³+1` and the integrand coefficient `logDerRadicand 2
radicandX3p1 = radicandLogDer = 3x²/(2(x³+1))` are the engine's own definitions. -/
theorem radDeriv_radGen_sound_qx :
    CPolyG.toPolyG (radDeriv 2 radicandX3p1 (radGen : RadElem (QFunNZG ℚ)))
      = CPolyG.toPolyG ([CField.zero, radicandLogDer] : RadElem (QFunNZG ℚ)) := by
  rw [toPolyG_radDeriv_radGen]
  rfl

/-- **The `radIsZero` test form of the `√(x³+1)` integral**, abstractly — `radIsZero (radDeriv 2 (x³+1)
radGen − [0, 3x²/(2(x³+1))]) = true`: the engine's `native_decide` statement `radDeriv_radGen_eq`, but
derived from the abstract `K[X]` identity `radDeriv_radGen_sound_qx` through `cisZeroG_iff` /
`toPolyG_csubG` (so it carries **no** `native_decide` axiom). The same proposition the kernel checks
numerically, here a theorem of the abstract derivation. -/
theorem radIsZero_radDeriv_radGen_qx :
    radIsZero (radSub (radDeriv 2 radicandX3p1 (radGen : RadElem (QFunNZG ℚ)))
        [CField.zero, radicandLogDer]) = true := by
  rw [radIsZero, radSub, CPolyG.cisZeroG_iff, CPolyG.toPolyG_csubG, sub_eq_zero,
    radDeriv_radGen_sound_qx]

/-! ### `#print axioms` — the algebraic integral is abstractly verified (no `native_decide`)

Each concrete soundness theorem carries **only** the standard `[propext, Classical.choice, Quot.sound]` —
no `native_decide` compiler axiom, no `sorry`. The simple-radical integral `∫ (f'/(nf))·√f = √f` (and its
two-term generalization) is `D(v) = g` proven as a general theorem and specialized to the concrete
elliptic radicand `x³+1` over `ℚ(x)`. The first abstractly-verified algebraic (radical) integral — the
seed of the soundness capstone `D(∫f) = f`. -/

-- The general algebraic integral `∫ (f'/(nf))·√f = √f` and its soundness-predicate packaging:
#print axioms RadElem.toPolyG_radDeriv_radGen
#print axioms RadElem.isRadicalRationalIntegral_radGen

-- The general two-term antiderivative `D(a₀ + a₁y) = D(a₀) + (D(a₁) + a₁ℓ)y`:
#print axioms RadElem.isRadicalRationalIntegral_linear

-- ★ The concrete elliptic-radicand integral over ℚ(x), abstractly (the engine's native_decide fact):
#print axioms radDeriv_radGen_sound_qx
#print axioms radIsZero_radDeriv_radGen_qx

end DeepWiki.SymbolicIntegration
