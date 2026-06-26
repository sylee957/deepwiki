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

/-! ### The fuel-recursion TELESCOPING invariant (the genuinely new lemma)

The multi-case driver's `radReduceCaseᵢIterate` is a fuel recursion with an **accumulator** `vNum`: each
step appends one contribution (`radAdd vNum contrib`) and replaces the leftover integrand by the negated
residual. Soundness of the assembled `v` rests on the loop invariant
`radDeriv(vNum) + leftover = original integrand` being preserved across the descent.

Stripped to its mathematical core — which is what makes it provable *generally and abstractly* — the
invariant is a **telescoping of `radDeriv` over a list of contributions**. Two ingredients:

* **`toPolyG_radDeriv_foldlRadAdd`** — `radDeriv` distributes over the accumulator `foldl radAdd`:
  `toPolyG (radDeriv n f (cs.foldl radAdd acc)) = toPolyG (radDeriv n f acc) + Σ_{c∈cs} toPolyG (radDeriv
  n f c)`. The accumulator structure of every `radReduceCaseᵢIterate` is exactly this fold; additivity
  (`toPolyG_radDeriv_radAdd`) pushed through it.

* **`sum_radDeriv_telescope`** — if each contribution's derivative is the *difference of consecutive
  leftovers* (`toPolyG (radDeriv n f (cs.get i)) = toPolyG (Ls.get i) − toPolyG (Ls.get (i+1))`, the
  per-step cleared identity (1) read through `radDeriv`), the sum telescopes to
  `toPolyG (Ls.head) − toPolyG (Ls.getLast)`.

Composing, the accumulated `v = foldl radAdd radZero cs` satisfies the master soundness
`toPolyG (radDeriv n f v) + toPolyG (final leftover) = toPolyG (initial integrand)`
(`radReduceRationalTelescope`): the **general rational-part soundness, as an abstract `K[X]` identity**,
reduced to the per-step `radDeriv` identity (1) over the engine's already-cleared single steps. -/

variable {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]

/-- **`radDeriv` distributes over the accumulator fold** — `toPolyG (radDeriv n f (cs.foldl radAdd acc))
= toPolyG (radDeriv n f acc) + (cs.map (fun c => toPolyG (radDeriv n f c))).sum`. The exact accumulator
structure of every `radReduceCaseᵢIterate` (`vNum ↦ radAdd vNum contrib`), so its accumulated `radDeriv`
is the sum of the per-step `radDeriv` contributions plus the seed. Proven by list induction on `cs`,
generalizing the accumulator, with the single step `toPolyG_radDeriv_radAdd`. -/
theorem toPolyG_radDeriv_foldlRadAdd (n : ℕ) (f : α) (acc : RadElem α) (cs : List (RadElem α)) :
    CPolyG.toPolyG (radDeriv n f (cs.foldl radAdd acc))
      = CPolyG.toPolyG (radDeriv n f acc)
        + (cs.map (fun c => CPolyG.toPolyG (radDeriv n f c))).sum := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, ih (radAdd acc c), toPolyG_radDeriv_radAdd, List.map_cons, List.sum_cons]
    ring

omit [CDiffFieldSpec α] in
/-- **The per-step contributions telescope (head/last form)** — for a head leftover `L₀`, a tail list of
leftovers `rest`, and contributions `cs` of the same length as `rest`, if each contribution's
`radDeriv`-image is the difference of consecutive leftovers — phrased as: `cs` zipped against the
consecutive pairs of `L₀ :: rest` (i.e. `(L₀ :: rest).zip rest`) satisfies, head-to-head,
`toPolyG (radDeriv n f c) = toPolyG p.1 − toPolyG p.2` (the per-step cleared identity (1)) — then the sum
of the contributions' `radDeriv`-images is `toPolyG L₀ − toPolyG (rest.getLastD L₀)`. The clean
telescoping over the fuel descent: each step "moves one piece" from the leftover into the accumulator, the
sum collapsing to the endpoints. Stated via a parallel `List.Forall₂` recursion to keep the endpoints free
of index/non-emptiness proof obligations. -/
theorem sum_radDeriv_telescope (n : ℕ) (f : α) :
    ∀ (L₀ : RadElem α) (rest : List (RadElem α)) (cs : List (RadElem α)),
      List.Forall₂ (fun c p => CPolyG.toPolyG (radDeriv n f c)
            = CPolyG.toPolyG p.1 - CPolyG.toPolyG p.2)
          cs ((L₀ :: rest).zip rest) →
      (cs.map (fun c => CPolyG.toPolyG (radDeriv n f c))).sum
        = CPolyG.toPolyG L₀ - CPolyG.toPolyG (rest.getLastD L₀) := by
  intro L₀ rest
  induction rest generalizing L₀ with
  | nil =>
    intro cs hforall
    -- `(L₀ :: []).zip [] = []`, so `cs = []`; sum = 0 and `getLastD L₀ [] = L₀`
    simp only [List.zip_nil_right] at hforall
    rw [List.forall₂_nil_right_iff] at hforall
    subst hforall
    simp
  | cons L₁ rest' ih =>
    intro cs hforall
    -- `(L₀ :: L₁ :: rest').zip (L₁ :: rest') = (L₀, L₁) :: (L₁ :: rest').zip rest'`
    rw [List.zip_cons_cons] at hforall
    -- so `cs = c :: cs'` with the head step `radDeriv c = toPolyG L₀ − toPolyG L₁` + the tail
    rw [List.forall₂_cons_right_iff] at hforall
    obtain ⟨c, cs', h0, htail, rfl⟩ := hforall
    rw [List.map_cons, List.sum_cons, ih L₁ cs' htail, h0]
    -- `getLastD L₀ (L₁ :: rest') = getLastD L₁ rest'`
    rw [List.getLastD_cons]
    ring

/-- **★ The master rational-part telescoping soundness (abstract, general)** — let `cs` be the list of
per-step contributions a `radReduceCaseᵢIterate` accumulates (each `radAdd`-ed into the running `vNum`,
from the seed `radZero`), and let `L₀ :: rest` be the chain of leftover integrands it passes through (`L₀`
the *original* integrand, `rest.getLastD L₀` the *final* leftover). If each contribution's `radDeriv`-image
is the difference of the consecutive leftovers it sits between (the per-step cleared identity (1), read
through `radDeriv` and zipped as `(L₀ :: rest).zip rest`), then the accumulated antiderivative
`v = cs.foldl radAdd radZero` satisfies the master soundness in `K[X]`:
`toPolyG (radDeriv n f v) + toPolyG (final leftover) = toPolyG (original integrand)`.
The general rational-part soundness as an abstract `K[X]` identity, reduced exactly to the per-step
`radDeriv` identity — `radDeriv` distributes over the accumulator fold (`toPolyG_radDeriv_foldlRadAdd`,
seed `radDeriv radZero = 0`) and the contributions telescope (`sum_radDeriv_telescope`). This is the
genuinely-new accumulation-invariant lemma; instantiating the hypothesis with the per-case lift gives the
soundness of `radIntegrateRational`'s assembled `v`. -/
theorem radReduceRationalTelescope (n : ℕ) (f : α) (L₀ : RadElem α) (rest cs : List (RadElem α))
    (hstep : List.Forall₂ (fun c p => CPolyG.toPolyG (radDeriv n f c)
          = CPolyG.toPolyG p.1 - CPolyG.toPolyG p.2)
        cs ((L₀ :: rest).zip rest)) :
    CPolyG.toPolyG (radDeriv n f (cs.foldl radAdd radZero))
        + CPolyG.toPolyG (rest.getLastD L₀)
      = CPolyG.toPolyG L₀ := by
  rw [toPolyG_radDeriv_foldlRadAdd, toPolyG_radDeriv_radZero, zero_add,
    sum_radDeriv_telescope n f L₀ rest cs hstep]
  ring

/-! ### Toward the general rational-part soundness: the `C/y`-form single step (capstone reduction)

The multi-case driver `radIntegrateRational` (`ComputableRadicalRationalDriver`) assembles the rational
part of `∫ R/(B√ρ)` as a sum of `R/y`-form pieces, each lifted to the pure-`y` radical element `[0, c]`
(`c·y`, with `c = vNum/(denom·ρ)` a base-field element — the `native_decide` `*_integrates` theorems use
exactly this `[0, R/ρ]` lift, since `R/y = (R/ρ)·y` in `α[y]/(y² − ρ)`). The driver's soundness
`radDeriv(v) = integrand` therefore rests, piece by piece, on the **`C/y`-form single-step identity**: for
`v = c·y` and integrand `g = γ·y`, `radDeriv n f v = g` is the *single base-field equation*
`D(c) + c·ℓ = γ` (`ℓ = logDerRadicand n f`). The next two lemmas make that reduction abstract: the
`C/y`-form soundness is **equivalent** to that one equation in `K`, and the equation is what each cleared
Case identity (`case3_cleared_identity` & co., currently `native_decide`) certifies after dividing by the
common denominator. -/

/-- **The `y`-component reading of a `C/y`-form antiderivative's derivative** —
`toPolyG (radDeriv n f [zero, c]) = C (toK (D(c) + c·ℓ)) · X` with `ℓ = logDerRadicand n f`: the diagonal
derivation of `c·y` (`[0, c]`) is `(D(c) + c·ℓ)·y`, a pure `y`-component (`D(c·y) = D(c)·y + c·D(y) =
D(c)·y + c·ℓ·y`). Specializes `toPolyG_radDeriv_linear` at `a₀ = 0` (the constant component vanishes:
`D(0) = 0`). The building block of the `C/y`-form soundness. -/
theorem toPolyG_radDeriv_zero_cons (n : ℕ) (f c : α) :
    CPolyG.toPolyG (radDeriv n f ([CField.zero, c] : RadElem α))
      = Polynomial.C (CFieldSpec.toK
          (CField.add (CDiffField.cderiv c) (CField.mul c (logDerRadicand n f)))) * X := by
  rw [toPolyG_radDeriv_linear, CPolyG.toPolyG_cons, CPolyG.toPolyG_cons, CPolyG.toPolyG_nil,
    mul_zero, add_zero, CDiffFieldSpec.toK_cderiv, CFieldSpec.toK_zero]
  -- the constant component is `D(0) = 0`, leaving only the `y`-component `C (toK (D c + c·ℓ))·X`
  rw [map_zero, map_zero, zero_add]
  ring

/-- **★ The `C/y`-form soundness reduces to one base-field equation** — for a base-field witness `c` and
integrand coefficient `γ`, the radical antiderivative `c·y` integrates `γ·y` (i.e.
`IsRadicalRationalIntegral n [f] [zero, γ] [zero, c]`) **iff** `D(c) + c·ℓ = γ` in `K`
(`ℓ = logDerRadicand n f`, read through `toK`). This is the abstract reduction the capstone chains: every
`R/y`-form piece of the rational-part driver is a `C/y`-form, and its soundness is exactly this single `K`
equation (the cleared single-step Case identities certify it after clearing the common denominator).
Proven from `toPolyG_radDeriv_zero_cons` + the injectivity of `C(·)·X ↦ ·` (`C` injective, `X` a
nonzerodivisor). -/
theorem isRadicalRationalIntegral_zero_cons_iff (n : ℕ) (f c γ : α) :
    IsRadicalRationalIntegral n [f] ([CField.zero, γ]) ([CField.zero, c] : RadElem α)
      ↔ CFieldSpec.toK (CField.add (CDiffField.cderiv c) (CField.mul c (logDerRadicand n f)))
          = CFieldSpec.toK γ := by
  unfold IsRadicalRationalIntegral
  rw [List.headD_cons, toPolyG_radDeriv_zero_cons, toPolyG_zero_cons]
  constructor
  · intro h
    -- `C a · X = C b · X` with `X` a nonzerodivisor ⟹ `C a = C b` ⟹ `a = b` (`C` injective)
    have hX : Polynomial.C (CFieldSpec.toK
          (CField.add (CDiffField.cderiv c) (CField.mul c (logDerRadicand n f))))
        = Polynomial.C (CFieldSpec.toK γ) :=
      mul_right_cancel₀ X_ne_zero h
    exact Polynomial.C_injective hX
  · intro h; rw [h]

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

/-! ### What the GENERAL rational-part soundness `radDeriv(radIntegrateRational … g) = g` still needs

This file proves the *derivation half* abstractly: `radDeriv` is a genuine derivation (imported keystone),
and a `C/y`-form antiderivative's soundness collapses to one base-field equation
(`isRadicalRationalIntegral_zero_cons_iff`). The **general** statement
`radDeriv n ρ (lift (radIntegrateRational fuel ρ R B)) = lift (R/(B·y))` (rational part, leftover
subtracted) additionally needs the **algorithm-correctness invariant** of the iterated Hermite /
undetermined-coefficient reductions — none of which is `radDeriv`-specific arithmetic; all of it is
*loop-invariant bookkeeping* over the engine's already-cleared single steps:

1. **Single-step cleared-identity ⟹ `radDeriv` step** (per case). Each `radReduceCaseᵢIterate` step has a
   *cleared polynomial identity* already validated (`case1_cleared_identity`, `case2_cleared_identity`,
   `case3_cleared_identity`, currently `native_decide`): e.g. Case 3's `B'f + Bg − C = D`. The abstract
   bridge is: *that polynomial identity, divided by the common denominator, is exactly the `K` equation
   `isRadicalRationalIntegral_zero_cons_iff` reduces to* — i.e. `radDeriv(Bf/(…y)) = C/(…y) + D/(…y)` as a
   `radDeriv` statement. Promoting each cleared identity from `native_decide` to an abstract `cisZeroG_iff`
   (the `D(g)+h = f` pattern is already done abstractly elsewhere in the engine, e.g.
   `checkIdentityG`/`ComputableIntegrateTowerCorrectG`) is mechanical but per-case.

2. **The fuel-recursion accumulation invariant**. `radReduceCaseᵢIterate … k C vNum` maintains
   `radDeriv(vNum-lift) + (C-leftover-lift) = (original integrand)` across the descent `k → k−1` (resp.
   `deg C → deg C − 1`): an induction on the structural `fuel`, with the base case the bottoming `k ≤ 1`
   (resp. `deg C < deg ρ`) returning the leftover unchanged, and the step case chaining (1) with the
   inductive hypothesis on the negated residual `−D`. This is the genuine new lemma — a `radDeriv`-level
   telescoping over the accumulator, reduced to the per-step identity of (1).

3. **The partial-fraction / dispatch front-end**. `radIntegrateRational` squarefree-decomposes `B`, splits
   each factor into its `V`/`W` parts, partial-fractions `R/B = Σ Nᵢ/Gᵢ`, and sums the per-piece rational
   parts. Soundness needs `R/B = Σ Nᵢ/Gᵢ` as a `K`-identity (the `cdiophantineG` Bézout-split correctness,
   already available as `toPolyG_cdiophantineG`-style lemmas) plus additivity of `radDeriv` over the sum
   (the imported `toPolyG_radDeriv_radAdd`). Then `radDeriv(Σ vᵢ) = Σ radDeriv(vᵢ) = Σ (piece integrand) =
   integrand − Σ leftover`.

So the capstone reduces to: **(1) per-case abstract cleared identity + (2) one telescoping fuel-induction +
(3) partial-fraction `K`-identity** — every piece either already abstract in the engine or a mechanical
lift, with the genuinely new content the accumulation invariant (2). This file is the `k = 0`/base layer:
the derivation is a derivation, and `D(v) = g` holds abstractly for the generator and every `C/y`-form
witness. -/

/-! ### `#print axioms` — the algebraic integral is abstractly verified (no `native_decide`)

Each concrete soundness theorem carries **only** the standard `[propext, Classical.choice, Quot.sound]` —
no `native_decide` compiler axiom, no `sorry`. The simple-radical integral `∫ (f'/(nf))·√f = √f` (and its
two-term generalization, and the `C/y`-form reduction) is `D(v) = g` proven as a general theorem and
specialized to the concrete elliptic radicand `x³+1` over `ℚ(x)`. The first abstractly-verified algebraic
(radical) integral — the seed of the soundness capstone `D(∫f) = f`. -/

-- The general algebraic integral `∫ (f'/(nf))·√f = √f` and its soundness-predicate packaging:
#print axioms RadElem.toPolyG_radDeriv_radGen
#print axioms RadElem.isRadicalRationalIntegral_radGen

-- The general two-term antiderivative `D(a₀ + a₁y) = D(a₀) + (D(a₁) + a₁ℓ)y`:
#print axioms RadElem.isRadicalRationalIntegral_linear

-- The capstone reduction: the `C/y`-form soundness ⟺ one base-field equation `D(c) + c·ℓ = γ`:
#print axioms RadElem.isRadicalRationalIntegral_zero_cons_iff

-- ★ The concrete elliptic-radicand integral over ℚ(x), abstractly (the engine's native_decide fact):
#print axioms radDeriv_radGen_sound_qx
#print axioms radIsZero_radDeriv_radGen_qx

end DeepWiki.SymbolicIntegration
