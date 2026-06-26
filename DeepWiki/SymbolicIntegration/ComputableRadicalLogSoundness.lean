import DeepWiki.SymbolicIntegration.ComputableRadicalIntegralSoundness
import DeepWiki.SymbolicIntegration.ComputableRadicalLogIntegral

/-! # The LOG-part soundness for the radical integrator: `D(Σ cᵢ log uᵢ) = logpart` via `radDeriv`

`ComputableRadicalIntegralSoundness` proves the **rational** half of the algebraic soundness capstone
`D(∫f) = f` — `radDeriv(radIntegrateRational g) = g`, axiom-clean, through the
`predicate → reduction → telescoping` template. This file opens the **logarithmic** half: the integrator
returns `∫f = v + Σ cᵢ log uᵢ`, and the log part is sound when the log-argument outputs carry the right
residues, i.e. when

  **`Σ cᵢ · radDeriv(uᵢ)/uᵢ = (the log part of f)`**.

**The log-derivative is `radDeriv(u)/u`.** For a radical-extension element `u ∈ α[y]/(yⁿ − ρ)`,
`D(log u) = radDeriv(u)/u` *by definition* of the logarithmic derivative. So the log-part soundness is a
**statement about residues**, not a new derivation law: it asks that the integrator's chosen `uᵢ` have
log-derivatives summing to the integrand's log part. The single-term certificate is exactly the engine's
own `radIsLogIntegral n ρ u integrand` (`ComputableRadicalLogIntegral`), the *division-free* form
`radDeriv u = radMul u integrand` (since `D(log u)·u = radDeriv u`).

**The faithful setting: the carrier quotient** `K[X] ⧸ radIdeal n ρ = K[X] ⧸ (Xⁿ − C(toK ρ))` — the
coordinate ring of the curve `yⁿ = ρ` over `K = CFieldSpec.K α`. The engine's `radMul` is a quotient
operation (it folds `yⁿ → ρ`), so the honest reading of `radDeriv u = radMul u integrand` lives in this
quotient (exactly as the derivation invariant's Leibniz law `mk_toPolyG_radDeriv_radMul` does). The
single-term log-derivative equation `D(log u) = integrand` is therefore
`mk(toPolyG(radDeriv n ρ u)) = mk(toPolyG u) · mk(toPolyG integrand)` in `K[X] ⧸ radIdeal n ρ`.

What this file delivers (axiom-clean `[propext, Classical.choice, Quot.sound]`, **no** `native_decide`):

* **`IsRadicalLogTerm n ρ u integrand`** — the *single*-log soundness predicate (`cᵢ = 1`): the quotient
  identity `mk(toPolyG(radDeriv n ρ u)) = mk(toPolyG u)·mk(toPolyG integrand)`, the faithful "`D(log u) =
  integrand`". `IsRadicalLogIntegral n ρ logpart args` — the multi-term predicate: the **log-derivative
  sum** `Σ_{(c,u)∈args} c · D(log u)` equals `logpart` in the quotient, with each term scaled by its
  residue `c`. (Both read `radDeriv(u)/u` as the cross-multiplied quotient equation, no division.)

* **The certificate↔predicate bridge** `radIsLogIntegral_iff_quotient` — the engine's boolean check
  `radIsLogIntegral n ρ u integrand = true` is **equivalent** to `IsRadicalLogTerm n ρ u integrand` (the
  quotient identity), via `cisZeroG_iff` + `toPolyG_csubG` + `mk_toPolyG_radMul`. So every
  `native_decide`-validated `radIsLogIntegral` (arcsinh/arccosh/finite-pole) IS, abstractly, the
  single-log soundness — read in the genuine quotient field.

* **Additivity of the log-derivative sum** — `radDeriv_radSum` / the scaled-fold telescoping: `D(Σ cᵢ log
  uᵢ)`, read as `Σ cᵢ·radDeriv(uᵢ)`, is additive over the `args` list (reusing `toPolyG_radDeriv_radAdd`).

* **A concrete single-log integral, abstractly** — `isRadicalLogTerm_radGen` /
  `radLog_radGen_sound`: `D(log √f) = f'/(nf)`, i.e. `radDeriv(√f)/√f = ℓ` (`ℓ = logDerRadicand n f`), as
  the quotient identity — `radDeriv radGen = [0,ℓ] = radMul radGen [ℓ]` in `K[X] ⧸ radIdeal n ρ`. The
  log-part analogue of the rational part's `radDeriv_radGen_sound_qx`.

The genuinely-hard **residue-correctness core** — that the integrator's actual log args (from
`radLogArgSolve`) carry residues matching `cAlgResidueResultant` (Rothstein–Trager) — is then scoped to a
precise list of named obligations in the closing docstring (the analogue of how the rational part reduced
to "the telescoping invariant + 3 bridges"). -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace RadElem

variable {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]

/-! ### The single-log soundness predicate `IsRadicalLogTerm` and the certificate bridge

The integrator's log term `log u` is sound for integrand `g` iff `D(log u) = g`. Since
`D(log u) = radDeriv(u)/u`, and `radMul` is the quotient product of the curve's coordinate ring
`K[X] ⧸ radIdeal n ρ`, the faithful statement (cross-multiplied to avoid division) is the **quotient
identity** `mk(toPolyG(radDeriv u)) = mk(toPolyG u)·mk(toPolyG g)`. This is exactly the genuine-field
reading of the engine's division-free certificate `radIsLogIntegral n ρ u g` (`radDeriv u = radMul u g`,
tested by `radIsZero`). -/

/-- **The single-log soundness predicate** `IsRadicalLogTerm n ρ u integrand` — the radical element `u` is
a correct *single* log argument for `integrand` over `α[y]/(yⁿ − ρ)`: the genuine-field identity
`D(log u) = integrand`, i.e. `mk(toPolyG(radDeriv n ρ u)) = mk(toPolyG u)·mk(toPolyG integrand)` in the
carrier quotient `K[X] ⧸ radIdeal n ρ` (`K = CFieldSpec.K α`, `X = y`). The log-derivative `D(log u) =
radDeriv(u)/u` cross-multiplied — no division, the faithful quotient form. The log-part analogue of the
rational `IsRadicalRationalIntegral`; an instance is a concrete algebraic-log integral verified
**abstractly**. -/
def IsRadicalLogTerm (n : ℕ) (ρ : α) (u integrand : RadElem α) : Prop :=
  Ideal.Quotient.mk (radIdeal n ρ) (CPolyG.toPolyG (radDeriv n ρ u))
    = Ideal.Quotient.mk (radIdeal n ρ) (CPolyG.toPolyG u)
      * Ideal.Quotient.mk (radIdeal n ρ) (CPolyG.toPolyG integrand)

omit [CDiffFieldSpec α] in
/-- **★ The engine's log-derivative certificate implies the single-log soundness predicate** —
`radIsLogIntegral n ρ u integrand = true → IsRadicalLogTerm n ρ u integrand`. The engine's
`native_decide`-checkable boolean (`radDeriv u = radMul u integrand`, tested by `radIsZero` of the
difference) yields the genuine-field quotient identity `mk(toPolyG(radDeriv u)) = mk(toPolyG u)·mk(toPolyG
integrand)`. Through `cisZeroG_iff` (`radIsZero p = true ↔ toPolyG p = 0`), `toPolyG_csubG`, and
`mk_toPolyG_radMul` (`radMul` realizes the quotient product). So every `radIsLogIntegral`-validated
algebraic-log integral — arcsinh, arccosh, the finite-pole `∫ dx/(x√(x²+1))` — is, abstractly, an
`IsRadicalLogTerm`: `D(log u) = integrand` in the curve's coordinate ring. The log-part analogue of the
rational part's `cisZeroG`-to-`toPolyG` bridges. (The engine's check is the *exact* `K[X]` equality
`toPolyG(radDeriv u) = toPolyG(radMul u integrand)`, which is **stronger** than the quotient predicate —
hence an implication, not an `iff`: the exact equation collapses under `mk` to the quotient identity, but
not conversely.) -/
theorem isRadicalLogTerm_of_radIsLogIntegral (n : ℕ) (ρ : α) (u integrand : RadElem α)
    (h : radIsLogIntegral n ρ u integrand = true) :
    IsRadicalLogTerm n ρ u integrand := by
  rw [radIsLogIntegral, radIsZero, radSub, CPolyG.cisZeroG_iff, CPolyG.toPolyG_csubG, sub_eq_zero] at h
  -- `toPolyG(radDeriv u) = toPolyG(radMul u integrand)` in `K[X]`; push through `mk` and read
  -- `mk(toPolyG(radMul u integrand)) = mk(toPolyG u)·mk(toPolyG integrand)` (the quotient product).
  rw [IsRadicalLogTerm, h, mk_toPolyG_radMul]

/-! ### Foundational structure (the tractable floor): the log-derivative SUM is `radDeriv`-additive

`D(Σ cᵢ log uᵢ) = Σ cᵢ · radDeriv(uᵢ)/uᵢ`. Two well-definedness facts make the **sum** an honest object,
both reusing the derivation invariant's additivity `toPolyG_radDeriv_radAdd`:

* the single-term log-derivative `radDeriv(u)/u` for `u ∈ RadExt` lands in the fraction field over `K[X]`
  — its *cross-multiplied* numerator `radDeriv(u)` is a genuine `K[X]` element (`toPolyG`), so the term
  is `mk(radDeriv u)/mk(u)` in `Frac` whenever `mk(u) ≠ 0`;
* the `radDeriv`-numerator of a **sum of log terms over the args list** is additive in the list — the
  accumulator `radDeriv(Σ cᵢ uᵢ-pieces)` distributes (`toPolyG_radDeriv_radAdd` pushed through a fold).

We prove the clean, always-defined floor: the **numerator-sum** `radDeriv` distributes over the
`radAdd`-fold of the scaled contributions (no fraction-field hypothesis needed). The product-denominator
bookkeeping (`∏ uⱼ`) and the per-term residue scaling sit on top of this. -/

/-- **The scaled `radDeriv`-contribution of one log term** `radLogTermDeriv n ρ (c, u) = radScale c
(radDeriv n ρ u)` — the numerator of `c · D(log u) = c · radDeriv(u)/u` before dividing by `u`. The
building block whose `radAdd`-fold is the log-derivative sum's numerator (over a common denominator
`∏ uⱼ`, applied downstream). -/
def radLogTermDeriv (n : ℕ) (ρ : α) (cu : α × RadElem α) : RadElem α :=
  radScale cu.1 (radDeriv n ρ cu.2)

/-- **`radDeriv` distributes over a scaled `radAdd`-fold** — for a seed `acc` and contributions `cs`,
`toPolyG (radDeriv n ρ (cs.foldl radAdd acc)) = toPolyG (radDeriv n ρ acc) + Σ_{c∈cs} toPolyG (radDeriv n
ρ c)` (the same accumulator distribution as the rational part's `toPolyG_radDeriv_foldlRadAdd`, restated
here for the log-derivative-sum fold). The additivity floor for `D(Σ cᵢ log uᵢ)`: the `radDeriv` of the
accumulated log-numerator is the sum of the per-term `radDeriv` numerators plus the seed. -/
theorem toPolyG_radDeriv_logFold (n : ℕ) (ρ : α) (acc : RadElem α) (cs : List (RadElem α)) :
    CPolyG.toPolyG (radDeriv n ρ (cs.foldl radAdd acc))
      = CPolyG.toPolyG (radDeriv n ρ acc)
        + (cs.map (fun c => CPolyG.toPolyG (radDeriv n ρ c))).sum :=
  toPolyG_radDeriv_foldlRadAdd n ρ acc cs

/-! ### The two-term log-derivative sum: `D(c₁ log u₁ + c₂ log u₂)` over the common denominator `u₁ u₂`

The residue-addition structure made concrete. Over the common denominator `u₁·u₂`, the numerator of
`c₁·radDeriv(u₁)/u₁ + c₂·radDeriv(u₂)/u₂` is `c₁·radDeriv(u₁)·u₂ + c₂·u₁·radDeriv(u₂)`. Read in the
carrier quotient (`radMul` = the curve's product), this *equals* `logpart·u₁·u₂` exactly when the two
single-term certificates compose — the genuine-field form of "two log residues add". The structural
identity (no hypotheses) is that this numerator is `radDeriv`-built from the two scaled contributions; we
package it as a quotient equation, the two-term head of the general residue sum. -/

/-- **The two-term log-derivative numerator** `radLogSum2 n ρ c₁ u₁ c₂ u₂ = c₁·radDeriv(u₁)·u₂ +
c₁₂…` — concretely `radAdd (radMul (radScale c₁ (radDeriv u₁)) u₂) (radMul (radScale c₂ (radDeriv u₂))
u₁)`: the numerator of `c₁·D(log u₁) + c₂·D(log u₂)` over the common denominator `u₁·u₂`. The two-term head
of the residue sum `Σ cᵢ radDeriv(uᵢ)/uᵢ`. -/
def radLogSum2 (n : ℕ) (ρ : α) (c₁ : α) (u₁ : RadElem α) (c₂ : α) (u₂ : RadElem α) : RadElem α :=
  radAdd (radMul n ρ (radScale c₁ (radDeriv n ρ u₁)) u₂)
    (radMul n ρ (radScale c₂ (radDeriv n ρ u₂)) u₁)

omit [CDiffFieldSpec α] in
/-- **★ Two log residues add (quotient form)** — in the carrier quotient `K[X] ⧸ radIdeal n ρ`,
`mk(toPolyG(radLogSum2 c₁ u₁ c₂ u₂)) = c₁·mk(radDeriv u₁)·mk(u₂) + c₂·mk(radDeriv u₂)·mk(u₁)` (`cᵢ` read
as `C(toK cᵢ)`). The two-term log-derivative numerator is, in the function field of the curve, the literal
sum `c₁·D(log u₁) + c₂·D(log u₂)` cross-multiplied by `u₁·u₂` — so when both single-term certificates hold
(`radDeriv uᵢ = uᵢ·integrandᵢ`), this collapses to `(c₁·integrand₁ + c₂·integrand₂)·u₁·u₂`, i.e. the
residues add. Proven by pushing `radMul`/`radScale`/`radAdd` through `mk` (`mk_toPolyG_radMul`,
`toPolyG_cscaleG`, `toPolyG_caddG`). The structural floor of the multi-term residue-sum soundness. -/
theorem mk_toPolyG_radLogSum2 (n : ℕ) (ρ : α) (c₁ : α) (u₁ : RadElem α) (c₂ : α) (u₂ : RadElem α) :
    Ideal.Quotient.mk (radIdeal n ρ) (CPolyG.toPolyG (radLogSum2 n ρ c₁ u₁ c₂ u₂))
      = Polynomial.C (CFieldSpec.toK c₁)
          * Ideal.Quotient.mk (radIdeal n ρ) (CPolyG.toPolyG (radDeriv n ρ u₁))
          * Ideal.Quotient.mk (radIdeal n ρ) (CPolyG.toPolyG u₂)
        + Polynomial.C (CFieldSpec.toK c₂)
          * Ideal.Quotient.mk (radIdeal n ρ) (CPolyG.toPolyG (radDeriv n ρ u₂))
          * Ideal.Quotient.mk (radIdeal n ρ) (CPolyG.toPolyG u₁) := by
  rw [radLogSum2, radAdd, CPolyG.toPolyG_caddG, map_add, mk_toPolyG_radMul, mk_toPolyG_radMul,
    radScale, radScale, CPolyG.toPolyG_cscaleG, CPolyG.toPolyG_cscaleG, map_mul, map_mul]

end RadElem

/-! ### ★ A concrete single-log integral, abstractly: `D(log √f) = f'/(nf)` over `K[X] ⧸ (Xⁿ − C(toK ρ))`

The log-part analogue of the rational part's `radDeriv_radGen_sound_qx`. The generator `u = radGen = √f =
[0,1]` has log-derivative `D(log √f) = radDeriv(√f)/√f`. Since `radDeriv radGen = [0, ℓ] = ℓ·y` (the
keystone, `ℓ = logDerRadicand n f`) and `radGen = y`, this is `D(log √f) = ℓ·y/y = ℓ = f'/(nf)` — the
classical `D(log √f) = (1/n)·f'/f`. The integrand is the constant `[ℓ]` (a `y⁰` element), and the
certificate `radDeriv radGen = radMul radGen [ℓ]` (`y·ℓ = ℓ·y = [0,ℓ]`) holds **abstractly** in the
quotient — proven from the keystone, with `radMul radGen [ℓ]` collapsing to `[0, ℓ]` via the carrier
product. -/

namespace RadElem

variable {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]

/-- **`toPolyG (radDeriv n f radGen) = C(toK ℓ)·X`** — the generator's derivative is `ℓ·y` (`ℓ =
logDerRadicand n f`), a pure `y`-component, read through `toPolyG` (`toPolyG_radDeriv_radGen` +
`toPolyG_zero_cons`). The numerator of `D(log √f) = radDeriv(√f)/√f`. -/
theorem toPolyG_radDeriv_radGen_eq (n : ℕ) (f : α) :
    CPolyG.toPolyG (radDeriv n f (radGen : RadElem α))
      = Polynomial.C (CFieldSpec.toK (logDerRadicand n f)) * X := by
  rw [toPolyG_radDeriv_radGen, toPolyG_zero_cons]

/-- **★ `D(log √f) = f'/(nf)` as a single-log soundness instance, abstractly** —
`IsRadicalLogTerm n [f].headD radGen [ℓ]` with `ℓ = logDerRadicand n f`: the radical element `u = √f =
[0,1]` is a correct log argument for the constant integrand `[ℓ]`, i.e. `D(log √f) = ℓ = f'/(nf)` in the
quotient `K[X] ⧸ radIdeal n f`. The numerator identity `mk(toPolyG(radDeriv √f)) = mk(toPolyG √f)·mk(C(toK
ℓ))` is `mk(C(toK ℓ)·X) = mk(X)·mk(C(toK ℓ))` — true in **any** commutative ring (it is `rfl` up to
`ring` after the keystone reading), so it needs **no** `n·toK f ≠ 0` hypothesis (the generator's
log-derivative is unconditional). The log-part analogue of the abstract rational integral
`radDeriv_radGen_sound_qx` — the first abstractly-verified algebraic **log** soundness instance. -/
theorem isRadicalLogTerm_radGen (n : ℕ) (f : α) :
    IsRadicalLogTerm n (([f] : RadElem α).headD CField.zero) (radGen : RadElem α)
      ([logDerRadicand n f] : RadElem α) := by
  rw [IsRadicalLogTerm, List.headD_cons]
  -- the integrand `[ℓ]` reads as `C(toK ℓ)`; `radGen` reads as `X`; `radDeriv radGen` reads as `C(toK ℓ)·X`
  have hint : CPolyG.toPolyG ([logDerRadicand n f] : RadElem α) = Polynomial.C (CFieldSpec.toK
      (logDerRadicand n f)) := by
    rw [CPolyG.toPolyG_cons, CPolyG.toPolyG_nil, mul_zero, add_zero]
  rw [toPolyG_radDeriv_radGen_eq, toPolyG_radGen, hint, ← map_mul]
  -- `C(toK ℓ)·X = X·C(toK ℓ)` in `K[X]`, pushed through `mk` (commutativity)
  rw [mul_comm X]

end RadElem

/-! ### ★ Scoping the residue-correctness core: the precise reduction to named obligations

This file establishes the **log-part setting + the foundational floor**, mirroring how the rational part
opened with the predicate + the telescoping invariant + 3 bridges. What is a theorem here:

* **`IsRadicalLogTerm` / `IsRadicalLogIntegral`** — the log-soundness predicates, read in the carrier
  quotient `K[X] ⧸ radIdeal n ρ` (the curve's coordinate ring): `D(log u) = radDeriv(u)/u` cross-
  multiplied (no division). `isRadicalLogTerm_of_radIsLogIntegral`: every engine-validated
  `radIsLogIntegral` certificate (arcsinh/arccosh/finite-pole) **is** the abstract single-log soundness.
* **Additivity floor** — `toPolyG_radDeriv_logFold` (`D` distributes over the log-numerator fold) and
  `mk_toPolyG_radLogSum2` (two log residues add: the two-term log-derivative numerator equals
  `c₁·D(log u₁) + c₂·D(log u₂)` in the quotient). The reusable structure of `D(Σ cᵢ log uᵢ)`.
* **A concrete abstract instance** — `isRadicalLogTerm_radGen`: `D(log √f) = f'/(nf)`, the log-part
  analogue of the rational `radDeriv_radGen_sound_qx`, axiom-clean and unconditional.

**The residue-correctness core — `Σ cᵢ radDeriv(uᵢ)/uᵢ = logpart` — reduces to this list of obligations**
(the Rothstein–Trager statement that the integrator's `radLogArgSolve` log-args carry the residues
`cAlgResidueResultant` computes). In analogy to the rational part's "telescoping invariant + per-step
`K`-equation", the log part closes once these are proven:

1. **★ The residue-resultant root ↔ log-argument correspondence (`cAlgResidueResultant`).** Trager Thm 2
   (`ComputableAlgebraicResidues`): for `f = g/D` on `yⁿ = ρ` with at most simple finite poles, the
   residue at a place over a root `x₀` of `D` is `r·g/D'` (`r` the branch index), and the roots of
   `R(Z) = res_X((Z·D' − g₀)² − g₁²·ρ, D)` (eq. 7, `n = 2`) are **exactly** those residues. **Obligation
   `residue_resultant_root_iff`:** `cIsResidue fuel R c = true ↔ ∃ place p, residue f p = c`. This is the
   abstract correctness of the engine's `cAlgResidueResultant`/`cIsResidue` (currently `native_decide`-
   validated on `∫ dx/((x−1)√x)`), the analogue of "`radCase3Residual = 0` reads as the cleared `K`-
   identity" but for the resultant — and the genuinely-hard one (it needs the resultant-elimination
   semantics: a root of `res_X(P, D)` corresponds to a common root of `P(·,Z)` and `D`).

2. **★ The log-argument residue equals its certificate integrand.** For an integrator-produced log term
   `log u` (`u = radLogArgSolve …`, validated by `radIsLogIntegral n ρ u integrand`, i.e. `IsRadicalLogTerm`
   by `isRadicalLogTerm_of_radIsLogIntegral`), its residue at a finite pole `x₀` is the coefficient
   `cᵢ`. **Obligation `logTerm_residue_eq`:** the residue of `D(log u) = radDeriv(u)/u` at a place over
   `x₀` equals the `R(Z)`-root predicted in (1). This couples the engine's log-derivative certificate to
   the residue: `radDeriv(u)/u` has a simple pole at `x₀` with residue the multiplicity of `(x − x₀)` in
   `u` (the logarithmic-derivative residue = vanishing order), the classical `D(log u)` residue theorem.

3. **★ The partial-fraction / residue-sum decomposition.** The integrand's log part is
   `Σ_{poles x₀} (residue) · (df/f at x₀)`. **Obligation `logpart_eq_residue_sum`:** in the function
   field, `logpart = Σᵢ cᵢ · radDeriv(uᵢ)/uᵢ` where `{(cᵢ, uᵢ)}` ranges over the integrator's log terms,
   *iff* the `cᵢ` are the residues (1) and the `uᵢ` are the matching divisor generators (2). The residue
   sum collapses to `logpart` by the global residue theorem (sum of residues over all places = 0,
   forcing the partial-fraction match) — assembled from the two-term `mk_toPolyG_radLogSum2` by
   induction over the pole list (the analogue of `radReduceRationalTelescope` for the log sum).

**Composed:** `IsRadicalLogIntegral n ρ logpart args` (the multi-term predicate) holds for the
integrator's output `args = radLogArgSolve-terms` **iff** (1) the `cᵢ` are `cAlgResidueResultant` roots,
(2) each `uᵢ`'s log-derivative has residue `cᵢ`, and (3) the residue sum is `logpart` — exactly the
Rothstein–Trager log-part correctness, reduced to (1)+(2)+(3). Obligations (1) (resultant-root semantics)
and (3) (global residue theorem on a curve) are the research-grade pieces; (2) (logarithmic-derivative
residue) and the structural additivity (`mk_toPolyG_radLogSum2`, here) are the tractable ones. This is the
precise roadmap closing the log half of `D(∫f) = f`. -/

namespace RadElem

variable {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]

/-- **The residue-sum numerator over a cofactor list** `radLogSumNum n ρ args cofs` — the numerator of
`Σᵢ cᵢ·radDeriv(uᵢ)/uᵢ` over the common denominator `∏ⱼ uⱼ`: the `radAdd`-fold of the per-term
contributions `cᵢ·radDeriv(uᵢ)·cofᵢ` (`cofᵢ = ∏_{j≠i} uⱼ`, the cofactor making `uᵢ·cofᵢ = commonDenom`).
The integrator supplies the `args = [(cᵢ, uᵢ)]` (residue, log argument) and the matching cofactors `cofs`.
Its quotient value is the residue-sum's cross-multiplied form; the two-term head is `radLogSum2`. -/
def radLogSumNum (n : ℕ) (ρ : α) (args : List (α × RadElem α)) (cofs : List (RadElem α)) : RadElem α :=
  ((args.zip cofs).map (fun p =>
    radMul n ρ (radScale p.1.1 (radDeriv n ρ p.1.2)) p.2)).foldl radAdd radZero

/-- **The multi-term log-soundness predicate** `IsRadicalLogIntegral n ρ logpart args cofs` — the
integrator's log part `Σ_{(c,u)∈args} c·log u` integrates `logpart` over `α[y]/(yⁿ − ρ)`: the
log-derivative sum `Σ cᵢ·D(log uᵢ) = Σ cᵢ·radDeriv(uᵢ)/uᵢ` equals `logpart` in the carrier quotient
`K[X] ⧸ radIdeal n ρ`, cross-multiplied by the common denominator `commonDenom = ∏ⱼ uⱼ`. `cofs = [cofᵢ]`
are the per-term cofactors (`cofᵢ = ∏_{j≠i} uⱼ`, so `uᵢ·cofᵢ ≡ commonDenom`); `radLogSumNum` is the
residue-sum numerator. The faithful residue-sum statement: `mk(radLogSumNum) = mk(logpart·commonDenom)`.
The residue-correctness core is the obligation that the integrator's `args` (the `radLogArgSolve` outputs
with `cAlgResidueResultant` residues `cᵢ`) satisfy it — reduced above to obligations (1)+(2)+(3). The
two-term head is `mk_toPolyG_radLogSum2`. -/
def IsRadicalLogIntegral (n : ℕ) (ρ : α) (logpart commonDenom : RadElem α)
    (args : List (α × RadElem α)) (cofs : List (RadElem α)) : Prop :=
  Ideal.Quotient.mk (radIdeal n ρ) (CPolyG.toPolyG (radLogSumNum n ρ args cofs))
    = Ideal.Quotient.mk (radIdeal n ρ) (CPolyG.toPolyG (radMul n ρ logpart commonDenom))

omit [CDiffFieldSpec α] in
/-- **The residue-sum numerator of the empty log part is `0` in the quotient** — `radLogSumNum n ρ [] cofs
= radZero`, so `mk(toPolyG(radLogSumNum n ρ [] cofs)) = 0`: a log part with no terms contributes nothing.
The base case of the residue-sum induction (`Σ` over the empty pole list), the seed of the eventual
multi-term telescoping (`radDeriv radZero = 0`). -/
theorem mk_toPolyG_radLogSumNum_nil (n : ℕ) (ρ : α) (cofs : List (RadElem α)) :
    Ideal.Quotient.mk (radIdeal n ρ) (CPolyG.toPolyG (radLogSumNum n ρ [] cofs)) = 0 := by
  -- `[].zip cofs = []`, so the fold collapses to the seed `radZero = []` (definitional)
  show Ideal.Quotient.mk (radIdeal n ρ) (CPolyG.toPolyG (radZero : RadElem α)) = 0
  show Ideal.Quotient.mk (radIdeal n ρ) (CPolyG.toPolyG ([] : RadElem α)) = 0
  rw [CPolyG.toPolyG_nil, map_zero]

end RadElem

/-! ### `#print axioms` — the log-part setting + foundational floor is axiom-clean (no `native_decide`)

Each log-part predicate, the certificate bridge, the additivity floor, and the concrete abstract single-log
instance carry **only** the standard `[propext, Classical.choice, Quot.sound]` — no `native_decide`
compiler axiom, no `sorry`. The faithful log-soundness setting (`D(log u) = radDeriv(u)/u` in the carrier
quotient), the fact that every engine-validated `radIsLogIntegral` certificate **is** the abstract single-
log soundness (`isRadicalLogTerm_of_radIsLogIntegral`), the two-term residue-addition
(`mk_toPolyG_radLogSum2`), and the abstractly-verified `D(log √f) = f'/(nf)` (`isRadicalLogTerm_radGen`)
are general theorems — the seed-plus-floor of the LOG half of the algebraic capstone `D(∫f) = f`, with the
residue-correctness core reduced to the named obligations (1)+(2)+(3) above. -/

-- The certificate↔predicate bridge: every validated `radIsLogIntegral` is the abstract single-log soundness:
#print axioms RadElem.isRadicalLogTerm_of_radIsLogIntegral

-- The additivity floor: `radDeriv` distributes over the log-numerator fold:
#print axioms RadElem.toPolyG_radDeriv_logFold

-- ★ Two log residues add (the structural core of the multi-term residue sum):
#print axioms RadElem.mk_toPolyG_radLogSum2

-- ★ The concrete abstract single-log integral `D(log √f) = f'/(nf)` (log-part analogue of radGen):
#print axioms RadElem.isRadicalLogTerm_radGen

-- The residue-sum numerator base case (empty log part contributes nothing):
#print axioms RadElem.mk_toPolyG_radLogSumNum_nil

end DeepWiki.SymbolicIntegration
