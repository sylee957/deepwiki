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

The **general** rational-part soundness is then assembled (abstract `K[X]`, general in `n`/`f`/`α`):

* **`radReduceRationalTelescope`** — the fuel-recursion **telescoping invariant** (the genuinely-new
  accumulation lemma): `radDeriv` distributes over the integrator's accumulator `foldl radAdd`
  (`toPolyG_radDeriv_foldlRadAdd`) and the per-step contributions telescope to the endpoints
  (`sum_radDeriv_telescope`), giving `radDeriv(accumulated v) + final-leftover = original integrand`.

* **`radDeriv_foldlRadAdd_zero_cons_telescope`** — the **general rational-part soundness**: for the
  pure-`y` lifts (`R/y ↦ (R/ρ)·y`, the form every `radReduceCaseᵢIterate` piece takes), *given* each
  step's base-field equation `D(cBᵢ) + cBᵢ·ℓ = cCᵢ − cCᵢ₊₁` (the cleared single-step Case identity read in
  `K`, via the per-step lift `toPolyG_radDeriv_zero_cons_sub_iff`), the assembled antiderivative
  `v = foldl radAdd radZero [0,cBᵢ]` satisfies `radDeriv(v) = integrand − final-leftover` in `K[X]`.

So the soundness capstone is a theorem under the precondition "each cleared step's `K`-equation holds";
the remaining scoped follow-up is discharging that precondition for the *literal* `radIntegrateRational`
over `QFunNZG ℚ` (the noncomputable `qxOfNum`/`RatFunc` lift bridges — `cderiv∘qxOfNum = qxOfNum∘cderivG`,
`g = ℓ·f`), recorded in the closing module docstring. -/

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

/-! ### The per-case `radDeriv`-step lift (piece 1): pure-`y` contributions, difference of leftovers

The telescoping invariant (`radReduceRationalTelescope`) consumes, per step, a `radDeriv` identity of the
shape `toPolyG (radDeriv n f contribᵢ) = toPolyG leftoverᵢ − toPolyG leftoverᵢ₊₁`. In the rational-part
driver every `contrib`, `leftover` lifts to a **pure-`y`** radical element `[0, ·]` (an `R/y`-form is
`(R/ρ)·y = [0, R/ρ]`). For pure-`y` elements the per-step `radDeriv` identity collapses to a single
base-field equation, exactly mirroring `isRadicalRationalIntegral_zero_cons_iff` but in
difference-of-leftovers form — the bridge that turns each cleared single-step `K`-equation into a `Forall₂`
entry the telescoping accepts. -/

/-- **★ The per-step `radDeriv` lift for pure-`y` contributions** — for base-field coefficients `cB` (the
lifted step contribution `cB·y`) and `cC`, `cD` (the lifted consecutive leftovers `cC·y`, `cD·y`),
`toPolyG (radDeriv n f [zero, cB]) = toPolyG [zero, cC] − toPolyG [zero, cD]` **iff** the single base-field
equation `D(cB) + cB·ℓ = cC − cD` holds in `K` (`ℓ = logDerRadicand n f`). This is piece (1) of the
capstone in its telescoping shape: each cleared single-step Case identity, lifted to the genuine field,
*is* this `K`-equation, and this lemma packages it as the difference-of-leftovers `radDeriv` statement the
fuel-telescoping `radReduceRationalTelescope` consumes. Proven from `toPolyG_radDeriv_zero_cons` +
`toPolyG_zero_cons` + `C(·)·X` injectivity (`C` injective, `X` a nonzerodivisor). -/
theorem toPolyG_radDeriv_zero_cons_sub_iff (n : ℕ) (f cB cC cD : α) :
    CPolyG.toPolyG (radDeriv n f ([CField.zero, cB] : RadElem α))
        = CPolyG.toPolyG ([CField.zero, cC] : RadElem α)
          - CPolyG.toPolyG ([CField.zero, cD] : RadElem α)
      ↔ CFieldSpec.toK (CField.add (CDiffField.cderiv cB) (CField.mul cB (logDerRadicand n f)))
          = CFieldSpec.toK cC - CFieldSpec.toK cD := by
  rw [toPolyG_radDeriv_zero_cons, toPolyG_zero_cons, toPolyG_zero_cons, ← sub_mul, ← map_sub]
  constructor
  · intro h
    have hX := mul_right_cancel₀ X_ne_zero h
    have := Polynomial.C_injective hX
    rw [this]
  · intro h; rw [h]

/-! ### ★ The general rational-part soundness for an assembled pure-`y` antiderivative (compose 1+2)

Composing the telescoping invariant (piece 2) with the per-step lift (piece 1): the rational-part driver
accumulates its antiderivative `v` as the `radAdd`-fold of pure-`y` step contributions `[0, cBᵢ]`, while
the integrand and the running residuals are the pure-`y` leftovers `[0, cCᵢ]`. Given the per-step `K`-
equations `D(cBᵢ) + cBᵢ·ℓ = cCᵢ − cCᵢ₊₁` — exactly the cleared single-step Case identities read in the
genuine field (piece 1) — the assembled `v` is a correct antiderivative of the original integrand modulo
the final leftover: `radDeriv n f v + [0, finalLeftover] = [0, originalIntegrand]` in `K[X]`. This is the
**general rational-part soundness**, abstract over arbitrary `α`, its precondition the list of cleared-step
`K`-equations the engine validates one step at a time. -/

/-- **★ The general rational-part soundness, assembled-`v` form** — for a list of step-contribution
coefficients `cBs = [cB₀,…,cB_{m−1}]` and a one-longer list of leftover coefficients `cCs = [cC₀,…,cC_m]`
(`cC₀` the original integrand's `y`-coefficient, `cC_m` the final leftover's), if every step satisfies the
base-field equation `D(cBᵢ) + cBᵢ·ℓ = cCᵢ − cCᵢ₊₁` in `K` (`ℓ = logDerRadicand n f`; the cleared
single-step Case identity in the genuine field), then the antiderivative `v` assembled as the `radAdd`-fold
of the pure-`y` contributions `[0, cBᵢ]` integrates the original integrand modulo the final leftover:
`toPolyG (radDeriv n f v) + toPolyG [0, cC_m] = toPolyG [0, cC₀]` in `K[X]`. The capstone composition:
`radReduceRationalTelescope` (telescoping, piece 2) fed by `toPolyG_radDeriv_zero_cons_sub_iff` (per-step
lift, piece 1) on each cleared-step `K`-equation. General in `n`, `f`, `α` — the residual to a *specific*
driver run is supplying its per-step `K`-equations (the lifted cleared identities). -/
theorem radDeriv_foldlRadAdd_zero_cons_telescope (n : ℕ) (f : α)
    (cBs : List α) (cCs : List α) (hlen : cBs.length + 1 = cCs.length)
    (hstep : ∀ i : ℕ, (hi : i < cBs.length) →
      CFieldSpec.toK (CField.add (CDiffField.cderiv (cBs.get ⟨i, hi⟩))
            (CField.mul (cBs.get ⟨i, hi⟩) (logDerRadicand n f)))
        = CFieldSpec.toK (cCs.get ⟨i, by omega⟩) - CFieldSpec.toK (cCs.get ⟨i + 1, by omega⟩)) :
    CPolyG.toPolyG (radDeriv n f
          ((cBs.map (fun cB => ([CField.zero, cB] : RadElem α))).foldl radAdd radZero))
        + CPolyG.toPolyG ([CField.zero, cCs.getLastD CField.zero] : RadElem α)
      = CPolyG.toPolyG ([CField.zero, cCs.headD CField.zero] : RadElem α) := by
  -- peel `cCs = cC₀ :: rest`; the contributions are `cs = cBs.map (fun cB => [0, cB])`
  match cCs, hlen with
  | cC₀ :: rest, hlen =>
    have hlen' : cBs.length = rest.length := by simpa using hlen
    -- assemble the `Forall₂` per-step hypothesis from the `K`-equations, via the per-step lift
    have hforall : List.Forall₂
        (fun c p => CPolyG.toPolyG (radDeriv n f c)
            = CPolyG.toPolyG p.1 - CPolyG.toPolyG p.2)
        (cBs.map (fun cB => ([CField.zero, cB] : RadElem α)))
        (((cC₀ :: rest).map (fun cC => ([CField.zero, cC] : RadElem α))).zip
          (rest.map (fun cC => ([CField.zero, cC] : RadElem α)))) := by
      rw [List.forall₂_iff_get]
      have hleneq : (cBs.map (fun cB => ([CField.zero, cB] : RadElem α))).length
          = (((cC₀ :: rest).map (fun cC => ([CField.zero, cC] : RadElem α))).zip
              (rest.map (fun cC => ([CField.zero, cC] : RadElem α)))).length := by
        rw [List.length_map, List.length_zip, List.length_map, List.length_map]
        simp only [List.length_cons]; omega
      refine ⟨hleneq, ?_⟩
      -- index-wise: each pair `(cBᵢ, (cCᵢ, cCᵢ₊₁))` satisfies the per-step lift from the `K`-equation
      intro i hi hi2
      have hik : i < cBs.length := by simpa using hi
      simp only [List.get_eq_getElem, List.getElem_map, List.getElem_zip]
      rw [toPolyG_radDeriv_zero_cons_sub_iff]
      have := hstep i hik
      simpa only [List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero] using this
    -- the telescoping invariant closes it; `getLastD`/`headD` bookkeeping on `cC₀ :: rest`
    have hkey := radReduceRationalTelescope n f ([CField.zero, cC₀] : RadElem α)
      (rest.map (fun cC => ([CField.zero, cC] : RadElem α)))
      (cBs.map (fun cB => ([CField.zero, cB] : RadElem α))) hforall
    rw [List.headD_cons]
    -- `(map g rest).getLastD (g cC₀) = g (rest.getLastD cC₀)`
    rw [show ([CField.zero, cC₀] : RadElem α) = (fun cC => ([CField.zero, cC] : RadElem α)) cC₀ from rfl,
      List.getLastD_map] at hkey
    -- align the goal's `(cC₀ :: rest).getLastD 0` with `rest.getLastD cC₀`
    rw [List.getLastD_cons]
    exact hkey

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

/-! ### The GENERAL rational-part soundness: what is now a theorem, and the precise residual

This file proves the **general rational-part soundness as an abstract `K[X]` theorem** —
`radDeriv_foldlRadAdd_zero_cons_telescope`:

> For a list of step-contribution coefficients `cBs` and a one-longer list of leftover coefficients
> `cCs` (head = the original integrand's `y`-coefficient, last = the final leftover's), **if** every step
> satisfies the base-field equation `D(cBᵢ) + cBᵢ·ℓ = cCᵢ − cCᵢ₊₁` in `K`, **then** the assembled
> antiderivative `v = (cBs.map (·↦[0,·])).foldl radAdd radZero` satisfies
> `toPolyG (radDeriv n f v) + toPolyG [0, cC_last] = toPolyG [0, cC_head]`,

i.e. `radDeriv(v) = integrand − final-leftover`, **general in `n`, the radicand `f`, and the base `α`**.
It composes the two pieces named in the prior plan, both now landed and axiom-clean:

1. **Per-case `radDeriv`-step lift** — `toPolyG_radDeriv_zero_cons_sub_iff`: for pure-`y` contributions the
   per-step `radDeriv` identity `radDeriv [0, cB] = [0, cC] − [0, cD]` collapses to the single base-field
   equation `D(cB) + cB·ℓ = cC − cD` in `K`. Every cleared single-step Case identity
   (`case1/2/3_cleared_identity`, `B'f + Bg − C = D` & co.), divided by the common denominator and read in
   the genuine field, *is* exactly this `K`-equation. (Done here.)

2. **★ The fuel-recursion telescoping invariant** — `radReduceRationalTelescope` (built from
   `toPolyG_radDeriv_foldlRadAdd` + `sum_radDeriv_telescope`): `radDeriv` distributes over the accumulator
   `foldl radAdd` and the per-step contributions telescope to the endpoints. This is the genuinely-new
   accumulation invariant; with the seed `radDeriv radZero = 0` it gives
   `radDeriv(accumulated v) + final-leftover = original integrand`. (Done here — the hard new lemma.)

**The precise residual.** What `radDeriv_foldlRadAdd_zero_cons_telescope` takes as its **precondition** —
the list of per-step `K`-equations `D(cBᵢ) + cBᵢ·ℓ = cCᵢ − cCᵢ₊₁` — is, for the literal
`radIntegrateRational` over the concrete base `α = QFunNZG ℚ`, the statement that each iterate step's
*polynomial* cleared identity `B'f + Bg − C = D` lifts to the field equation on the `R/y ↦ (R/ρ)·y`
coefficients. Discharging that precondition for a *specific* driver run requires three `QFunNZG ℚ`-specific
bridges, none of them `radDeriv`-arithmetic: (i) the `qxOfNum : CPolyG ℚ → QFunNZG ℚ` lift is a ring
homomorphism commuting with the derivation (`cderiv (qxOfNum P) = qxOfNum (cderivG P)`); (ii) the radical's
helper satisfies `g = ℓ·f` in `K` (`toK g = toK ℓ · toK f`, since `g = (1/n)f'` and `ℓ = f'/(nf)` —
clean once `toK(nf) ≠ 0`); (iii) the per-step polynomial identity itself (already `rfl` for `radCase3Residual`,
which is *defined* as `B'f + Bg − C`). The `toK`-into-`RatFunc ℚ` bridge is **noncomputable**, so these are
genuine `RatFunc`-arithmetic lemmas, not `decide`/`rfl` — that is the scoped follow-up. The abstract
soundness theorem above is complete and general; only the `QFunNZG ℚ`-specific *discharge of its
precondition for a concrete run* (re-deriving e.g. `c3itDriver_integrates` without `native_decide`)
remains. -/

/-! ### `#print axioms` — the general rational-part soundness is abstractly verified (no `native_decide`)

Each soundness theorem carries **only** the standard `[propext, Classical.choice, Quot.sound]` — no
`native_decide` compiler axiom, no `sorry`. The simple-radical integral `∫ (f'/(nf))·√f = √f`, its two-term
generalization, the `C/y`-form reduction, the **telescoping invariant**, and the **general rational-part
soundness** `radDeriv(assembled v) = integrand − final-leftover` are all general theorems (specialized to
the concrete elliptic radicand `x³+1` over `ℚ(x)` for the headline). The seed-plus-engine of the soundness
capstone `D(∫f) = f`. -/

-- The general algebraic integral `∫ (f'/(nf))·√f = √f` and its soundness-predicate packaging:
#print axioms RadElem.toPolyG_radDeriv_radGen
#print axioms RadElem.isRadicalRationalIntegral_radGen

-- The general two-term antiderivative `D(a₀ + a₁y) = D(a₀) + (D(a₁) + a₁ℓ)y`:
#print axioms RadElem.isRadicalRationalIntegral_linear

-- The capstone reduction: the `C/y`-form soundness ⟺ one base-field equation `D(c) + c·ℓ = γ`:
#print axioms RadElem.isRadicalRationalIntegral_zero_cons_iff

-- ★ The fuel-recursion telescoping invariant (the genuinely-new accumulation lemma):
#print axioms RadElem.radReduceRationalTelescope

-- ★ The general rational-part soundness: assembled `v` integrates the integrand modulo the final leftover:
#print axioms RadElem.radDeriv_foldlRadAdd_zero_cons_telescope

-- ★ The concrete elliptic-radicand integral over ℚ(x), abstractly (the engine's native_decide fact):
#print axioms radDeriv_radGen_sound_qx
#print axioms radIsZero_radDeriv_radGen_qx

end DeepWiki.SymbolicIntegration
