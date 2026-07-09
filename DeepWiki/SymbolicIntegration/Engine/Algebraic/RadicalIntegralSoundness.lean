import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalDerivationInvariant
import DeepWiki.SymbolicIntegration.Engine.CFracGDiffSpec
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalRationalDriver

/-! # Abstract soundness of the radical rational-part integrator: `radDeriv v = g` in `K[X]`

Through the Horner bridge `toPoly : RadElem α → K[X]` (with `X` the generator `y`, `K = CFieldSpec.K α`),
the diagonal derivation `radDeriv n f` is `Differential.implicitDeriv (C (toK ℓ) · X)` for the rule
`y' = ℓ·y`, `ℓ = logDerRadicand n f = f'/(nf)`. Using this keystone, the rational-part integrator's
`radDeriv v = g` is proven as a genuine-field `K[X]` identity, with no `native_decide`.

The predicate is `IsRadicalRationalIntegral n f g v` (`toPoly (radDeriv n f v) = toPoly g`); concrete
instances are `isRadicalRationalIntegral_radGen` (`∫ (f'/(nf))·√f = √f`) and
`isRadicalRationalIntegral_linear` (two-term antiderivatives). The general soundness is the telescoping
invariant `radReduceRationalTelescope` and `radDeriv_foldlRadAdd_zero_cons_telescope`, whose per-step
`K`-equation precondition is discharged for the literal `qxOfNum`-coefficient lifts via three
`CFrac ℚ`-specific bridges (`toCFracG_cderiv_qxOfNum`, `toK_logDerRadicand_mul_radicand`,
`radCase3Residual_eq`), composed by `toK_step_qxOfNum_iff` and `radDeriv_foldlRadAdd_qxOfNum_telescope`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace RadElem

variable {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]

/-! ### The soundness predicate and the concrete algebraic integrals -/

/-- The radical rational-integral soundness predicate `IsRadicalRationalIntegral n f g v`: the radical
element `v` integrates `g` over `α[y]/(yⁿ − f)` (rational part), i.e. the genuine-field identity
`toPoly (radDeriv n f v) = toPoly g` in `K[X]`. -/
def IsRadicalRationalIntegral (n : ℕ) (f g v : RadElem α) : Prop :=
  CPoly.toPoly (radDeriv n (f.headD CField.zero) v) = CPoly.toPoly g

/-- `radGen` is a radical rational integral for its logarithmic-derivative integrand. -/
theorem isRadicalRationalIntegral_radGen (n : ℕ) (f : α) :
    IsRadicalRationalIntegral n [f] ([CField.zero, logDerRadicand n f]) (radGen : RadElem α) := by
  show CPoly.toPoly (radDeriv n (([f] : RadElem α).headD CField.zero) radGen) = _
  rw [List.headD_cons, toPolyG_radDeriv_radGen]

/-- A two-term radical element integrates its computed diagonal derivative. -/
theorem isRadicalRationalIntegral_linear (n : ℕ) (f a₀ a₁ : α) :
    IsRadicalRationalIntegral n [f]
      ([CDiffField.cderiv a₀,
        CField.add (CDiffField.cderiv a₁) (CField.mul a₁ (logDerRadicand n f))])
      ([a₀, a₁] : RadElem α) := by
  show CPoly.toPoly (radDeriv n (([f] : RadElem α).headD CField.zero) [a₀, a₁]) = _
  rw [List.headD_cons, toPolyG_radDeriv_linear]

/-! ### The fuel-recursion telescoping invariant

The driver's accumulator `radDeriv(vNum) + leftover = original integrand` is a telescoping of `radDeriv`
over the contribution list: `radDeriv` distributes over `foldl radAdd` (`toPolyG_radDeriv_foldlRadAdd`)
and the per-step contributions telescope to the endpoints (`sum_radDeriv_telescope`), giving
`radReduceRationalTelescope`. -/

variable {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]

omit [CDiffFieldSpec α] in
/-- Contributions whose derivatives are consecutive leftover differences telescope. -/
theorem sum_radDeriv_telescope (n : ℕ) (f : α) :
    ∀ (L₀ : RadElem α) (rest : List (RadElem α)) (cs : List (RadElem α)),
      List.Forall₂ (fun c p => CPoly.toPoly (radDeriv n f c)
            = CPoly.toPoly p.1 - CPoly.toPoly p.2)
          cs ((L₀ :: rest).zip rest) →
      (cs.map (fun c => CPoly.toPoly (radDeriv n f c))).sum
        = CPoly.toPoly L₀ - CPoly.toPoly (rest.getLastD L₀) := by
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
    -- so `cs = c :: cs'` with the head step `radDeriv c = toPoly L₀ − toPoly L₁` + the tail
    rw [List.forall₂_cons_right_iff] at hforall
    obtain ⟨c, cs', h0, htail, rfl⟩ := hforall
    rw [List.map_cons, List.sum_cons, ih L₁ cs' htail, h0]
    -- `getLastD L₀ (L₁ :: rest') = getLastD L₁ rest'`
    rw [List.getLastD_cons]
    ring

/-- The master rational-part telescoping soundness: for contributions `cs` (accumulated from `radZero`)
and leftovers `L₀ :: rest`, if each contribution's `radDeriv`-image is the difference of consecutive
leftovers, then `v = cs.foldl radAdd radZero` satisfies
`toPoly (radDeriv n f v) + toPoly (final leftover) = toPoly (original integrand)` in `K[X]`. Composes
`toPolyG_radDeriv_foldlRadAdd` and `sum_radDeriv_telescope`. -/
theorem radReduceRationalTelescope (n : ℕ) (f : α) (L₀ : RadElem α) (rest cs : List (RadElem α))
    (hstep : List.Forall₂ (fun c p => CPoly.toPoly (radDeriv n f c)
          = CPoly.toPoly p.1 - CPoly.toPoly p.2)
        cs ((L₀ :: rest).zip rest)) :
    CPoly.toPoly (radDeriv n f (cs.foldl radAdd radZero))
        + CPoly.toPoly (rest.getLastD L₀)
      = CPoly.toPoly L₀ := by
  rw [toPolyG_radDeriv_foldlRadAdd, toPolyG_radDeriv_radZero, zero_add,
    sum_radDeriv_telescope n f L₀ rest cs hstep]
  ring

/-! ### The `C/y`-form single step: reduction to one base-field equation

Every `R/y`-form piece of the rational-part driver lifts to a pure-`y` element `[0, c]` (`c·y`); for such
`v = c·y` and integrand `g = γ·y`, `radDeriv n f v = g` collapses to the single base-field equation
`D(c) + c·ℓ = γ` (`ℓ = logDerRadicand n f`). -/

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
shape `toPoly (radDeriv n f contribᵢ) = toPoly leftoverᵢ − toPoly leftoverᵢ₊₁`. In the rational-part
driver every `contrib`, `leftover` lifts to a **pure-`y`** radical element `[0, ·]` (an `R/y`-form is
`(R/ρ)·y = [0, R/ρ]`). For pure-`y` elements the per-step `radDeriv` identity collapses to a single
base-field equation, exactly mirroring `isRadicalRationalIntegral_zero_cons_iff` but in
difference-of-leftovers form — the bridge that turns each cleared single-step `K`-equation into a `Forall₂`
entry the telescoping accepts. -/

/-- **★ The per-step `radDeriv` lift for pure-`y` contributions** — for base-field coefficients `cB` (the
lifted step contribution `cB·y`) and `cC`, `cD` (the lifted consecutive leftovers `cC·y`, `cD·y`),
`toPoly (radDeriv n f [zero, cB]) = toPoly [zero, cC] − toPoly [zero, cD]` **iff** the single base-field
equation `D(cB) + cB·ℓ = cC − cD` holds in `K` (`ℓ = logDerRadicand n f`). This is piece (1) of the
capstone in its telescoping shape: each cleared single-step Case identity, lifted to the genuine field,
*is* this `K`-equation, and this lemma packages it as the difference-of-leftovers `radDeriv` statement the
fuel-telescoping `radReduceRationalTelescope` consumes. Proven from `toPolyG_radDeriv_zero_cons` +
`toPolyG_zero_cons` + `C(·)·X` injectivity (`C` injective, `X` a nonzerodivisor). -/
theorem toPolyG_radDeriv_zero_cons_sub_iff (n : ℕ) (f cB cC cD : α) :
    CPoly.toPoly (radDeriv n f ([CField.zero, cB] : RadElem α))
        = CPoly.toPoly ([CField.zero, cC] : RadElem α)
          - CPoly.toPoly ([CField.zero, cD] : RadElem α)
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
`toPoly (radDeriv n f v) + toPoly [0, cC_m] = toPoly [0, cC₀]` in `K[X]`. The capstone composition:
`radReduceRationalTelescope` (telescoping, piece 2) fed by `toPolyG_radDeriv_zero_cons_sub_iff` (per-step
lift, piece 1) on each cleared-step `K`-equation. General in `n`, `f`, `α` — the residual to a *specific*
driver run is supplying its per-step `K`-equations (the lifted cleared identities). -/
theorem radDeriv_foldlRadAdd_zero_cons_telescope (n : ℕ) (f : α)
    (cBs : List α) (cCs : List α) (hlen : cBs.length + 1 = cCs.length)
    (hstep : ∀ i : ℕ, (hi : i < cBs.length) →
      CFieldSpec.toK (CField.add (CDiffField.cderiv (cBs.get ⟨i, hi⟩))
            (CField.mul (cBs.get ⟨i, hi⟩) (logDerRadicand n f)))
        = CFieldSpec.toK (cCs.get ⟨i, by omega⟩) - CFieldSpec.toK (cCs.get ⟨i + 1, by omega⟩)) :
    CPoly.toPoly (radDeriv n f
          ((cBs.map (fun cB => ([CField.zero, cB] : RadElem α))).foldl radAdd radZero))
        + CPoly.toPoly ([CField.zero, cCs.getLastD CField.zero] : RadElem α)
      = CPoly.toPoly ([CField.zero, cCs.headD CField.zero] : RadElem α) := by
  -- peel `cCs = cC₀ :: rest`; the contributions are `cs = cBs.map (fun cB => [0, cB])`
  match cCs, hlen with
  | cC₀ :: rest, hlen =>
    have hlen' : cBs.length = rest.length := by simpa using hlen
    -- assemble the `Forall₂` per-step hypothesis from the `K`-equations, via the per-step lift
    have hforall : List.Forall₂
        (fun c p => CPoly.toPoly (radDeriv n f c)
            = CPoly.toPoly p.1 - CPoly.toPoly p.2)
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
(3x²/(2(x³+1)))·√(x³+1)` over `α = CFrac ℚ ≅ ℚ(x)`, `n = 2`, `f = x³+1` — now follows from the **general
theorem** `RadElem.toPolyG_radDeriv_radGen` specialized to that base, *without* `native_decide`. The
abstract `toPoly`-equality in `K[X]` (`K = CFieldSpec.K (CFrac ℚ)`) is the faithful field-level
statement; `radIsZero (radSub …) = true` is its `cisZero`-test form, here a corollary of the abstract
identity rather than a separate kernel computation. -/

open RadElem

/-- **★ `∫ (3x²/(2(x³+1)))·√(x³+1) dx = √(x³+1)` over `ℚ(x)`, abstractly** — `D(√(x³+1)) =
(3x²/(2(x³+1)))·√(x³+1)` as the genuine-field identity `toPoly (radDeriv 2 (x³+1) radGen) = toPoly [0,
3x²/(2(x³+1))]` in `K[X]`, `K = CFieldSpec.K (CFrac ℚ)`. The engine's `native_decide` carrier check
`radDeriv_radGen_eq` proven as a corollary of the general `toPolyG_radDeriv_radGen` — the first concrete
**algebraic** integral verified abstractly (`[propext, Classical.choice, Quot.sound]`, no
`native_decide`). The radicand `radicandX3p1 = x³+1` and the integrand coefficient `logDerRadicand 2
radicandX3p1 = radicandLogDer = 3x²/(2(x³+1))` are the engine's own definitions. -/
theorem radDeriv_radGen_sound_qx :
    CPoly.toPoly (radDeriv 2 radicandX3p1 (radGen : RadElem (CFrac ℚ)))
      = CPoly.toPoly ([CField.zero, radicandLogDer] : RadElem (CFrac ℚ)) := by
  rw [toPolyG_radDeriv_radGen]
  rfl

/-- The abstract zero-test form of the `√(x³+1)` radical-generator derivative. -/
theorem radIsZero_radDeriv_radGen_qx :
    radIsZero (radSub (radDeriv 2 radicandX3p1 (radGen : RadElem (CFrac ℚ)))
        [CField.zero, radicandLogDer]) = true := by
  rw [radIsZero, radSub, CPoly.cisZeroG_iff]
  simp only [denote, radDeriv_radGen_sound_qx]
  ring

/-! ### Bridge (i): the `qxOfNum : CPoly ℚ → CFrac ℚ` lift commutes with the derivation

The literal `radIntegrateRational` over `α = CFrac ℚ` builds its base-field coefficients by
`qxOfNum : CPoly ℚ → CFrac ℚ` (`p ↦ ⟨(p, [1]), _⟩`, a polynomial over denominator `1`). Discharging
the per-step `K`-equation `D(cBᵢ) + cBᵢ·ℓ = cCᵢ − cCᵢ₊₁` for a *concrete* driver run needs to push the
engine's polynomial derivative `cderiv : CPoly ℚ → CPoly ℚ` (formal `d/dX` on coefficient lists)
through `qxOfNum` and `cderiv` (the tower derivation `towerDerivCFrac [1]`). This is the substantive
noncomputable bridge — it lives in the genuine field `RatFunc ℚ` (`= CFieldSpec.K (CFrac ℚ)`), read
through `toCFrac = CFieldSpec.toK`.

The chain: `qxOfNum p` reads as the algebra-map image `am (toPoly p) = algebraMap ℚ[X] (RatFunc ℚ)
(toPoly p)` (denominator `1`); the tower derivation `towerDerivCFrac [1]` realizes Mathlib's
`extendDeriv (implicitDeriv (toPoly [1]))` (`toCFracG_towerDerivCFracG`), which on an algebra-map image
is `algebraMap (baseDerivQ (toPoly p))` (`extendDeriv_algebraMap`); and `baseDerivQ = implicitDeriv
(toPoly [1]) = implicitDeriv 1` is the plain polynomial `derivative` over `ℚ` (the base `Differential ℚ`
is `⟨0⟩`, so `mapCoeffs = 0`), which matches `toPoly (cderiv p)` (`toPolyG_cderivG`). -/

/-- **`qxOfNum p` reads as `algebraMap ℚ[X] (RatFunc ℚ) (toPoly p)`** — the genuine-field image of the
polynomial-over-`1` element `qxOfNum p = ⟨(p, [1]), _⟩` is `am (toPoly p)` (denominator `[1]` reads as
`1`, so the quotient `am (toPoly p) / 1` collapses). The reading that turns the derivation-commutation
bridge into an `extendDeriv ∘ algebraMap` computation. -/
theorem toCFracG_qxOfNum (p : CPoly ℚ) :
    CFrac.toCFrac (qxOfNum p) = CFrac.am ℚ (CPoly.toPoly p) := by
  show CFrac.am ℚ (CPoly.toPoly p) / CFrac.am ℚ (CPoly.toPoly ([CField.one] : CPoly ℚ)) = _
  have h1 : CPoly.toPoly ([CField.one] : CPoly ℚ) = 1 := by
    simp only [denote]
    simp
  rw [h1, map_one, div_one]

/-- **`baseDerivQ` is the plain polynomial derivative over `ℚ`** — `baseDerivQ q = Polynomial.derivative
q` in `ℚ[X]`. `baseDerivQ = implicitDeriv (toPoly [1]) = implicitDeriv 1 = mapCoeffs + 1 · derivative'`,
and over `ℚ` the base `Differential ℚ` is the zero derivation (`instDifferentialQ = ⟨0⟩`), so `mapCoeffs =
0` and only `derivative'` survives. The base-derivation half of bridge (i). -/
theorem baseDerivQ_apply (q : (CFieldSpec.K ℚ)[X]) :
    baseDerivQ q = Polynomial.derivative q := by
  have h1 : CPoly.toPoly ([CField.one] : CPoly ℚ) = 1 := by
    simp only [denote]
    simp
  rw [baseDerivQ, h1, Differential.implicitDeriv]
  -- `mapCoeffs q = 0` (base deriv on ℚ is `0`), leaving `1 • derivative' q = derivative q`
  have hmc : Differential.mapCoeffs q = 0 := by
    ext i
    rw [Differential.coeff_mapCoeffs, Polynomial.coeff_zero]
    show @Differential.deriv ℚ _ _ (q.coeff i) = 0
    rfl
  simp only [Derivation.add_apply, hmc, Derivation.restrictScalars_apply, one_smul, zero_add]
  rfl

/-- **★ Bridge (i) — the derivation commutes with `qxOfNum`** — `toCFrac (cderiv (qxOfNum p)) =
toCFrac (qxOfNum (cderiv p))` in `RatFunc ℚ` (`= CFieldSpec.K (CFrac ℚ)`): the polynomial-into-ℚ(x)
embedding `qxOfNum : CPoly ℚ → CFrac ℚ` is a derivation morphism, i.e. `cderiv ∘ qxOfNum = qxOfNum ∘
cderiv` read through the genuine field. The substantive noncomputable bridge of the literal-radical
soundness: `cderiv = towerDerivCFrac [1]` realizes `extendDeriv (implicitDeriv (toPoly [1]))`
(`toCFracG_towerDerivCFracG`); on the algebra-map image `qxOfNum p ↦ am (toPoly p)`
(`toCFracG_qxOfNum`) this is `algebraMap (baseDerivQ (toPoly p))` (`extendDeriv_algebraMap`); and
`baseDerivQ` is the plain `derivative` (`baseDerivQ_apply`), matching `toPoly (cderiv p)`
(`toPolyG_cderivG`). -/
theorem toCFracG_cderiv_qxOfNum (p : CPoly ℚ) :
    CFrac.toCFrac (CDiffField.cderiv (qxOfNum p))
      = CFrac.toCFrac (qxOfNum (CPoly.cderiv p)) := by
  -- `cderiv = towerDerivCFrac [1]`; realize it as `extendDeriv (implicitDeriv (toPoly [1]))`
  show CFrac.toCFrac (CFrac.towerDerivCFrac [CField.one] (qxOfNum p)) = _
  rw [CFrac.toCFracG_towerDerivCFracG, toCFracG_qxOfNum, toCFracG_qxOfNum, CFrac.am]
  -- `extendDeriv (implicitDeriv (toPoly [1])) (algebraMap (toPoly p)) = algebraMap (baseDerivQ (toPoly p))`
  rw [show Differential.implicitDeriv (CPoly.toPoly ([CField.one] : CPoly ℚ)) = baseDerivQ from rfl,
    extendDeriv_algebraMap, baseDerivQ_apply, CPoly.toPolyG_cderivG]

/-! ### Bridge (ii): `g = ℓ·f` in `K` — the integrand IS the diagonal multiplier times the radicand

The rational-part driver's integrand-helper is `g = (1/n)·f'` (the `(f/y)' = g/y` numerator), while the
diagonal radical derivation `radDeriv n f` carries `ℓ = logDerRadicand n f = f'/(nf)` (`y' = ℓ·y`). These
two are linked in `K` by `ℓ·f = (1/n)·f' = g`: the same content as the crux scalar identity
`toK_logDerRadicand_mul` (`n·toK ℓ·toK f = toK f'`), rearranged. So the integrand `g`'s `y`-coefficient
and the derivation multiplier `ℓ` agree after multiplying by `f` — exactly what makes a `[0, c]`-form
antiderivative's derivative `(D(c) + c·ℓ)·y` reproduce the integrand `g·y` of the cleared step. -/

namespace RadElem

variable {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]

omit [CDiffFieldSpec α] in
/-- **★ Bridge (ii) — `ℓ·f = (1/n)·f'` in `K`** — `toK (logDerRadicand n f · f) = (n : K)⁻¹ · toK f'`
(`ℓ = logDerRadicand n f = f'/(nf)`), valid when `n·toK f ≠ 0`. The integrand-helper `g = (1/n)f'` of the
rational-part driver IS the diagonal multiplier `ℓ` times the radicand `f`, read in the genuine field.
Rearranged from the crux scalar identity `toK_logDerRadicand_mul` (`n·toK ℓ·toK f = toK f'`) by dividing
through by `n`. The denominator-clearing half of the literal-soundness composition. -/
theorem toK_logDerRadicand_mul_radicand (n : ℕ) (f : α)
    (hnf : (n : CFieldSpec.K α) * CFieldSpec.toK f ≠ 0) :
    CFieldSpec.toK (CField.mul (logDerRadicand n f) f)
      = (n : CFieldSpec.K α)⁻¹ * CFieldSpec.toK (CDiffField.cderiv f) := by
  have hn : (n : CFieldSpec.K α) ≠ 0 := by
    intro h; rw [h, zero_mul] at hnf; exact hnf rfl
  rw [CFieldSpec.toK_mul, ← toK_logDerRadicand_mul n f hnf]
  field_simp

end RadElem

/-! ### Bridge (iii): the per-step polynomial cleared identity is definitional

The Case-3 single-step residual `radCase3Residual f g B C Bder = B'f + Bg − C` is the *defining*
expression `csub (cadd (cmul Bder f) (cmul B g)) C`. The engine's per-step cleared identity is
`radCase3Residual f g B C (cderiv B) = D` (the next leftover), and reading it through `toPoly` is the
polynomial equation `B'·f + B·g − C = D` in `K[X]` — a `rfl`/`cisZero` fact, no `radDeriv` reasoning.
This is the trivial bridge: it just unfolds the definition. -/

namespace CPoly

variable {α : Type*} [CField α] [CDiffField α]

omit [CDiffField α] in
/-- **Bridge (iii) — `radCase3Residual` is definitionally `B'f + Bg − C`** — `radCase3Residual f g B C
Bder = csub (cadd (cmul Bder f) (cmul B g)) C`. The per-step polynomial cleared identity is `rfl`: the
residual the Case-3 iterate negates and recurses on is literally `B'·f + B·g − C` (with `Bder = B'`
supplied by the caller). No content beyond unfolding — the bridge is definitional. -/
theorem radCase3Residual_eq (f g B C Bder : CPoly α) :
    radCase3Residual f g B C Bder
      = csub (cadd (cmul Bder f) (cmul B g)) C :=
  rfl

end CPoly

/-! ### ★ Composition (i)+(ii)+(iii): the literal `radDeriv(assembled v) = integrand − leftover` over `ℚ(x)`

With the three `CFrac ℚ` bridges in hand, the per-step `K`-equation precondition of
`radDeriv_foldlRadAdd_zero_cons_telescope` is discharged for the **literal** `radIntegrateRational`
coefficients — pure-`y` lifts of `qxOfNum`-of-polynomials over the radicand `qxOfNum ρ`. The genuine-field
`K`-equation `D(cBᵢ) + cBᵢ·ℓ = cCᵢ − cCᵢ₊₁` (with `cBᵢ = qxOfNum Bᵢ`, `cCᵢ = qxOfNum Cᵢ`, `ℓ =
logDerRadicand n (qxOfNum ρ) = ρ'/(nρ)`) clears, via bridges (i) (`cderiv∘qxOfNum = qxOfNum∘cderiv`) and
(ii) (`ℓ·ρ = (1/n)ρ'`), to the polynomial cleared identity `n·ρ·Bᵢ' + Bᵢ·ρ' = n·ρ·(Cᵢ − Cᵢ₊₁)` in
`K[X]` — the genuine-field reading of each engine step's `radCase3Residual = 0` (bridge (iii)). Feeding
the polynomial identities into the telescope yields the literal rational-part soundness over `ℚ(x)`. -/

namespace RadElem

open scoped Polynomial

/-- **`toK (qxOfNum p) = am (toPoly p)`** (`CFieldSpec.toK`-flavoured) — the same content as
`toCFracG_qxOfNum`, restated against `CFieldSpec.toK` (definitionally `CFrac.toCFrac` for `CFrac ℚ`)
so it `rw`s directly in `toK`-expressed goals. -/
theorem toK_qxOfNum (p : CPoly ℚ) :
    CFieldSpec.toK (qxOfNum p) = CFrac.am ℚ (CPoly.toPoly p) :=
  toCFracG_qxOfNum p

/-- **`toK (cderiv (qxOfNum p)) = am (derivative (toPoly p))`** (`CFieldSpec.toK`-flavoured bridge (i)) —
the genuine-field reading of `cderiv ∘ qxOfNum`: bridge (i) (`toCFracG_cderiv_qxOfNum`) composed with the
`qxOfNum`-reading and `toPolyG_cderivG`. The `toK`-side form used in the per-step composition. -/
theorem toK_cderiv_qxOfNum (p : CPoly ℚ) :
    CFieldSpec.toK (CDiffField.cderiv (qxOfNum p))
      = CFrac.am ℚ (derivative (CPoly.toPoly p)) := by
  rw [show CFieldSpec.toK (CDiffField.cderiv (qxOfNum p))
        = CFrac.toCFrac (CDiffField.cderiv (qxOfNum p)) from rfl,
    toCFracG_cderiv_qxOfNum, toCFracG_qxOfNum, CPoly.toPolyG_cderivG]

/-- **`toK (logDerRadicand n (qxOfNum ρ)) = am(ρ') / ((n:K)·am(ρ))`** — the diagonal multiplier of the
literal radical derivation, read in `RatFunc ℚ`: `ℓ = ρ'/(nρ)` reads as `am(derivative ρ̄)/((n:K)·am ρ̄)`
(`ρ̄ = toPoly ρ`). Routes `logDerRadicand`'s `div`/`mul`/`cnatCast` through the `toK` homomorphism laws
and the bridge-(i) reading `toK_cderiv_qxOfNum`. -/
theorem toK_logDerRadicand_qxOfNum (n : ℕ) (ρ : CPoly ℚ) :
    CFieldSpec.toK (logDerRadicand n (qxOfNum ρ))
      = CFrac.am ℚ (derivative (CPoly.toPoly ρ))
        / ((n : RatFunc (CFieldSpec.K ℚ)) * CFrac.am ℚ (CPoly.toPoly ρ)) := by
  rw [logDerRadicand, CFieldSpec.toK_div, CFieldSpec.toK_mul, CPoly.toK_cnatCastG, toK_cderiv_qxOfNum,
    toK_qxOfNum]

/-- **★ The literal per-step `K`-equation reduces to the cleared polynomial identity** — for `qxOfNum`-of-
polynomial step coefficient `B` and consecutive leftovers `C`, `C'` over the radicand `ρ` (all `CPoly ℚ`),
the telescope's per-step base-field equation
`toK (cderiv (qxOfNum B) + qxOfNum B · logDerRadicand n (qxOfNum ρ)) = toK (qxOfNum C) − toK (qxOfNum C')`
holds in `RatFunc ℚ` **iff** the cleared polynomial identity
`(n:K[X])·ρ̄·B̄' + B̄·ρ̄' = (n:K[X])·ρ̄·(C̄ − C̄')` holds in `K[X]` (`ρ̄ = toPoly ρ` etc.), provided `n ≠ 0`
and `ρ̄ ≠ 0`. This is the (i)+(ii)+(iii) composition at one step: bridge (i) reads `cderiv∘qxOfNum`, bridge
(ii) clears `ℓ = ρ'/(nρ)`, and `am` injectivity descends the `RatFunc` equation to the `K[X]` identity.
The genuine-field form of `radCase3Residual = 0`. -/
theorem toK_step_qxOfNum_iff (n : ℕ) (ρ B C C' : CPoly ℚ)
    (hn : (n : RatFunc (CFieldSpec.K ℚ)) ≠ 0) (hρ : CPoly.toPoly ρ ≠ 0) :
    CFieldSpec.toK (CField.add (CDiffField.cderiv (qxOfNum B))
          (CField.mul (qxOfNum B) (logDerRadicand n (qxOfNum ρ))))
        = CFieldSpec.toK (qxOfNum C) - CFieldSpec.toK (qxOfNum C')
      ↔ (n : (CFieldSpec.K ℚ)[X]) * CPoly.toPoly ρ * derivative (CPoly.toPoly B)
            + CPoly.toPoly B * derivative (CPoly.toPoly ρ)
          = (n : (CFieldSpec.K ℚ)[X]) * CPoly.toPoly ρ
              * (CPoly.toPoly C - CPoly.toPoly C') := by
  -- read every `toK` through `am` (bridge (i) for `cderiv`, the `ℓ` reading for the multiplier)
  rw [CFieldSpec.toK_add, CFieldSpec.toK_mul, toK_cderiv_qxOfNum, toK_qxOfNum, toK_qxOfNum,
    toK_qxOfNum, toK_logDerRadicand_qxOfNum]
  have hρK : CFrac.am ℚ (CPoly.toPoly ρ) ≠ 0 := CFrac.amG_toPolyG_ne_zero hρ
  have hinj := RatFunc.algebraMap_injective (CFieldSpec.K ℚ)
  -- the `K[X]` identity, pushed through the ring hom `am`, with the denominator `(n:K)·am ρ̄ ≠ 0`
  -- cleared, is exactly the `RatFunc` equation; `am` injectivity gives the converse.
  constructor
  · intro h
    apply hinj
    rw [map_add, map_mul, map_mul, map_mul, map_mul, map_mul, map_sub, map_natCast]
    field_simp [CFrac.am] at h
    linear_combination h
  · intro h
    have h' := congrArg (CFrac.am ℚ) h
    rw [map_add, map_mul, map_mul, map_mul, map_mul, map_mul, map_sub, map_natCast] at h'
    field_simp [CFrac.am]
    linear_combination h'

/-- **★ The LITERAL rational-part soundness over `ℚ(x)`** — for a radicand `ρ`, a list of step-contribution
polynomials `Bpolys` and a one-longer list of leftover polynomials `Cpolys` (all `CPoly ℚ`), **if** every
step's cleared polynomial identity `(n:K[X])·ρ̄·Bᵢ' + Bᵢ·ρ̄' = (n:K[X])·ρ̄·(Cᵢ − Cᵢ₊₁)` holds in `K[X]`
(`ρ̄ = toPoly ρ` etc. — the genuine-field reading of each engine step's `radCase3Residual = 0`, bridge
(iii)), **then** the assembled pure-`y` antiderivative `v = (Bpolys.map (qxOfNum · ↦ [0, ·])).foldl radAdd
radZero` satisfies the soundness identity `radDeriv n (qxOfNum ρ) v + [0, qxOfNum Cpolys.last] = [0,
qxOfNum Cpolys.head]` in `K[X]` (`radDeriv(v) = integrand − final-leftover`). The (i)+(ii)+(iii) composition
for the LITERAL `qxOfNum`-coefficient lifts the `radIntegrateRational` driver produces: `toK_step_qxOfNum_iff`
turns each cleared polynomial identity into the telescope's per-step `K`-equation, then
`radDeriv_foldlRadAdd_zero_cons_telescope` assembles. Precondition: `n ≠ 0` (in `RatFunc ℚ`), `ρ ≠ 0`
(`toPoly ρ ≠ 0`), and the per-step polynomial identities. -/
theorem radDeriv_foldlRadAdd_qxOfNum_telescope (n : ℕ) (ρ : CPoly ℚ) (Bpolys Cpolys : List (CPoly ℚ))
    (hlen : Bpolys.length + 1 = Cpolys.length)
    (hn : (n : RatFunc (CFieldSpec.K ℚ)) ≠ 0) (hρ : CPoly.toPoly ρ ≠ 0)
    (hpoly : ∀ i : ℕ, (hi : i < Bpolys.length) →
      (n : (CFieldSpec.K ℚ)[X]) * CPoly.toPoly ρ * derivative (CPoly.toPoly (Bpolys.get ⟨i, hi⟩))
          + CPoly.toPoly (Bpolys.get ⟨i, hi⟩) * derivative (CPoly.toPoly ρ)
        = (n : (CFieldSpec.K ℚ)[X]) * CPoly.toPoly ρ
            * (CPoly.toPoly (Cpolys.get ⟨i, by omega⟩)
              - CPoly.toPoly (Cpolys.get ⟨i + 1, by omega⟩))) :
    CPoly.toPoly (radDeriv n (qxOfNum ρ)
          (((Bpolys.map qxOfNum).map (fun cB => ([CField.zero, cB] : RadElem (CFrac ℚ)))).foldl
            radAdd radZero))
        + CPoly.toPoly
            ([CField.zero, (Cpolys.map qxOfNum).getLastD CField.zero] : RadElem (CFrac ℚ))
      = CPoly.toPoly ([CField.zero, (Cpolys.map qxOfNum).headD CField.zero] : RadElem (CFrac ℚ)) := by
  -- the radicand exposed to `radDeriv` is `(qxOfNum ρ).headD = qxOfNum ρ`? no — `radDeriv` takes the
  -- radicand directly here. Apply the abstract telescope at the `qxOfNum`-lifted coefficient lists.
  have hlen' : (Bpolys.map qxOfNum).length + 1 = (Cpolys.map qxOfNum).length := by
    rw [List.length_map, List.length_map]; omega
  have hkey := radDeriv_foldlRadAdd_zero_cons_telescope (α := CFrac ℚ) n (qxOfNum ρ)
    (Bpolys.map qxOfNum) (Cpolys.map qxOfNum) hlen' ?_
  · simpa using hkey
  · -- each step's `K`-equation from the cleared polynomial identity, via `toK_step_qxOfNum_iff`
    intro i hi
    have hiB : i < Bpolys.length := by simpa using hi
    have hiC : i < Cpolys.length := by omega
    have hiC1 : i + 1 < Cpolys.length := by omega
    -- rewrite the lifted `get`s back to `qxOfNum` of the polynomial `get`s
    rw [show (Bpolys.map qxOfNum).get ⟨i, hi⟩ = qxOfNum (Bpolys.get ⟨i, hiB⟩) from by
        simp [List.get_eq_getElem, List.getElem_map],
      show (Cpolys.map qxOfNum).get ⟨i, by omega⟩ = qxOfNum (Cpolys.get ⟨i, hiC⟩) from by
        simp [List.get_eq_getElem, List.getElem_map],
      show (Cpolys.map qxOfNum).get ⟨i + 1, by omega⟩ = qxOfNum (Cpolys.get ⟨i + 1, hiC1⟩) from by
        simp [List.get_eq_getElem, List.getElem_map]]
    exact (toK_step_qxOfNum_iff n ρ (Bpolys.get ⟨i, hiB⟩) (Cpolys.get ⟨i, hiC⟩)
      (Cpolys.get ⟨i + 1, hiC1⟩) hn hρ).mpr (hpoly i hiB)

/-! ### ★ The FRACTION-coefficient single-step iff: the named-run lift `[0, qxOfNum N / qxOfNum ρ]`

The `radIntegrateRational` *named runs* (`c3itRun`/`gcuspYRun`/`mcRun`, `ComputableRadicalRationalDriver`)
do not lift their accumulated antiderivative as a `radAdd`-fold of pure-`y` step contributions `[0, qxOfNum
Bᵢ]`; they lift the **whole accumulator** `vNum` over the common denominator `ρ` as the *single* fraction
element `c3itVlift = [0, qxOfNum vNum / qxOfNum ρ]` (`= vNum/ρ·y`, the `R/y ↦ (R/ρ)·y` reading), and the
integrand-minus-leftover as `[0, qxOfNum (C − Crem) / qxOfNum ρ]`. So the `qxOfNum`-coefficient telescope
above (whose contributions carry *no* division) does not directly apply to a named run.

The bridge is a **fraction-coefficient** variant of `toK_step_qxOfNum_iff`: for a single `C/y`-form with
coefficient `c = qxOfNum N / qxOfNum ρ` and integrand coefficient `γ = qxOfNum M / qxOfNum ρ` (the same
denominator `ρ`), `radDeriv n (qxOfNum ρ) [0, c] = [0, γ]` (read in `K[X]`) collapses — clearing the common
denominator `ρ̄` and the power index `n` — to one cleared **polynomial** identity in `K[X] = ℚ[X]`. This is
the literal shape of the engine's whole-accumulator check `radDeriv(vNum/ρ·y) = (C−Crem)/ρ·y`, and turns it
into a single `K[X]` equation between `toPoly`s. -/

/-- **`deriv (am p) = am (derivative p)`** in `RatFunc ℚ` — the Mathlib field derivation `Differential.deriv`
on the algebra-map image of a `K[X]`-polynomial is the algebra-map of its `derivative` (bridge (i) read in
the `deriv`/`am` direction): `toK (cderiv (qxOfNum N)) = deriv (toK (qxOfNum N)) = deriv (am (toPoly N))`
(`toK_cderiv`) and `= am (derivative (toPoly N))` (`toK_cderiv_qxOfNum`), so the two readings agree on every
`toPoly`. The `deriv`-side restatement of bridge (i), used to expand the quotient rule on `c = N̄/ρ̄`. -/
theorem deriv_amG_toPolyG (N : CPoly ℚ) :
    @Differential.deriv _ _ (CDiffFieldSpec.diffK (α := CFrac ℚ))
        (CFrac.am ℚ (CPoly.toPoly N))
      = CFrac.am ℚ (derivative (CPoly.toPoly N)) := by
  rw [show CFrac.am ℚ (CPoly.toPoly N) = CFieldSpec.toK (qxOfNum N) from (toK_qxOfNum N).symm,
    ← CDiffFieldSpec.toK_cderiv, toK_cderiv_qxOfNum]

/-- **★ The FRACTION-coefficient single-step iff** — for `qxOfNum`-of-polynomial numerator `N`, integrand
numerator `M`, and the common denominator `ρ` (all `CPoly ℚ`), the `C/y`-form soundness with the fraction
coefficient `c = qxOfNum N / qxOfNum ρ` and integrand `γ = qxOfNum M / qxOfNum ρ`,
`IsRadicalRationalIntegral n [qxOfNum ρ] [0, γ] [0, c]` (i.e. `radDeriv n (qxOfNum ρ) [0, c] = [0, γ]` in
`K[X]`), holds **iff** the single cleared **polynomial** identity
`(n:K[X])·(ρ̄·N̄' − N̄·ρ̄') + N̄·ρ̄' = (n:K[X])·ρ̄·M̄` holds in `K[X] = ℚ[X]` (`N̄ = toPoly N`, `ρ̄ = toPoly ρ`,
`M̄ = toPoly M`), provided `n ≠ 0` and `ρ̄ ≠ 0`. The denominator `ρ` and the index `n` are cleared through
the quotient rule (`Derivation.leibniz_div`) and `am` injectivity; the constant `½ρ' = g` integrand-helper
of the driver is the `n = 2` case `M = C − Crem`. This is the named-run lift's reduction (the whole
accumulator `vNum/ρ·y` is a *single* `C/y` fraction, not a fold), composing `isRadicalRationalIntegral_
zero_cons_iff` (the `C/y`-form `K`-equation), bridge (i) (`deriv_amG_toPolyG`), and the `logDerRadicand`
reading. -/
theorem isRadicalRationalIntegral_div_qxOfNum_iff (n : ℕ) (N M ρ : CPoly ℚ)
    (hn : (n : RatFunc (CFieldSpec.K ℚ)) ≠ 0) (hρ : CPoly.toPoly ρ ≠ 0) :
    IsRadicalRationalIntegral n [qxOfNum ρ]
        ([CField.zero, CField.div (qxOfNum M) (qxOfNum ρ)])
        ([CField.zero, CField.div (qxOfNum N) (qxOfNum ρ)] : RadElem (CFrac ℚ))
      ↔ (n : (CFieldSpec.K ℚ)[X]) * (CPoly.toPoly ρ * derivative (CPoly.toPoly N)
              - CPoly.toPoly N * derivative (CPoly.toPoly ρ))
            + CPoly.toPoly N * derivative (CPoly.toPoly ρ)
          = (n : (CFieldSpec.K ℚ)[X]) * CPoly.toPoly ρ * CPoly.toPoly M := by
  rw [isRadicalRationalIntegral_zero_cons_iff]
  -- abbreviations for the `am`-images and the denominator nonzero facts
  have hρK : CFrac.am ℚ (CPoly.toPoly ρ) ≠ 0 := CFrac.amG_toPolyG_ne_zero hρ
  have hinj := RatFunc.algebraMap_injective (CFieldSpec.K ℚ)
  -- expand the `K`-equation `toK(cderiv c + c·ℓ) = toK γ` through `toK_div`, bridge (i), and `ℓ = ρ'/(nρ)`
  rw [CFieldSpec.toK_add, CFieldSpec.toK_mul, CFieldSpec.toK_div, CFieldSpec.toK_div, toK_qxOfNum,
    toK_qxOfNum, toK_qxOfNum, toK_logDerRadicand_qxOfNum]
  -- `toK (cderiv (div (qxOfNum N) (qxOfNum ρ))) = deriv (am N̄ / am ρ̄)` (the quotient rule)
  rw [show CFieldSpec.toK (CDiffField.cderiv (CField.div (qxOfNum N) (qxOfNum ρ)))
        = @Differential.deriv _ _ (CDiffFieldSpec.diffK (α := CFrac ℚ))
            (CFrac.am ℚ (CPoly.toPoly N) / CFrac.am ℚ (CPoly.toPoly ρ)) by
      rw [CDiffFieldSpec.toK_cderiv, CFieldSpec.toK_div, toK_qxOfNum, toK_qxOfNum]]
  rw [Derivation.leibniz_div, smul_eq_mul, smul_eq_mul, smul_eq_mul, deriv_amG_toPolyG,
    deriv_amG_toPolyG]
  -- now a pure `RatFunc` equation in `am`-images; clear denominators and descend by `am` injectivity
  -- the cleared `K[X]` identity, transported through the ring hom `am` (`map_*` + `map_natCast`),
  -- is exactly the `RatFunc` equation after clearing the denominator `(n:K)·am ρ̄ ≠ 0`.
  have hden : (n : RatFunc (CFieldSpec.K ℚ)) * CFrac.am ℚ (CPoly.toPoly ρ) ≠ 0 :=
    mul_ne_zero hn hρK
  constructor
  · intro h
    apply hinj
    rw [map_add, map_mul, map_mul, map_sub, map_mul, map_mul, map_mul, map_natCast]
    field_simp at h ⊢
    simp only [map_mul, map_natCast]
    linear_combination h
  · intro h
    have h' := congrArg (CFrac.am ℚ) h
    rw [map_add, map_mul, map_mul, map_sub, map_mul, map_mul, map_mul, map_natCast] at h'
    field_simp
    simp only [map_mul, map_natCast] at h' ⊢
    linear_combination h'

/-- **★ Reading the engine's cleared `cisZero` check into the fraction-iff `K[X]` identity** (the `n = 2`
named-run form) — given the engine-side polynomial check `cisZero (2·ρ·N' − N·ρ' − 2·ρ·M) = true` (the
whole-accumulator cleared identity over `CPoly ℚ`, `2·_ = cscale 2`, `_' = cderiv`), reading it abstractly
through `cisZeroG_iff` + `toPolyG_csubG` (+ `toPolyG_cmulG`/`toPolyG_cscaleG`/`toPolyG_cderivG`) yields the
`K[X] = ℚ[X]` identity `(2:K[X])·(ρ̄·N̄' − N̄·ρ̄') + N̄·ρ̄' = (2:K[X])·ρ̄·M̄` — exactly the hypothesis of
`isRadicalRationalIntegral_div_qxOfNum_iff` at `n = 2` (`2(ρ̄N̄' − N̄ρ̄') + N̄ρ̄' = 2ρ̄N̄' − N̄ρ̄'`). The bridge
that turns a named driver run's own `cisZero` check (its cleared polynomial identity) into the fraction
iff's precondition, with no `radDeriv`/`RatFunc` reasoning — only the `toPoly` polynomial readings. -/
theorem clearedKX2_of_cisZeroG (N M ρ : CPoly ℚ)
    (hcheck : CPoly.cisZero
        (CPoly.csub (CPoly.csub (CPoly.cmul (CPoly.cscale (2 : ℚ) ρ) (CPoly.cderiv N))
          (CPoly.cmul N (CPoly.cderiv ρ)))
          (CPoly.cmul (CPoly.cscale (2 : ℚ) ρ) M)) = true) :
    (2 : (CFieldSpec.K ℚ)[X]) * (CPoly.toPoly ρ * derivative (CPoly.toPoly N)
            - CPoly.toPoly N * derivative (CPoly.toPoly ρ))
          + CPoly.toPoly N * derivative (CPoly.toPoly ρ)
      = (2 : (CFieldSpec.K ℚ)[X]) * CPoly.toPoly ρ * CPoly.toPoly M := by
  rw [CPoly.cisZeroG_iff] at hcheck
  simp only [denote] at hcheck
  rw [sub_eq_zero] at hcheck
  -- `C (toK (2:ℚ)) = (2 : K[X])` (the scalar `2`)
  rw [show Polynomial.C (CFieldSpec.toK (2 : ℚ)) = (2 : (CFieldSpec.K ℚ)[X]) from by
    show Polynomial.C ((2 : ℚ) : ℚ) = (2 : ℚ[X]); rw [map_ofNat]] at hcheck
  linear_combination hcheck

end RadElem

/-! ### ★ The NAMED driver run `c3itRun` (`∫ x⁴/√(x³+1)`), abstractly: `radDeriv(c3itVlift) = c3itRatLift`

The `radIntegrateCase3` named run `c3itRun = (Crem, vNum)` on `∫ x⁴/√(x³+1)`
(`ComputableRadicalRationalDriver`, `c3itRho = x³+1`, `c3itC = x⁴`, `n = 2`) lifts its accumulated rational
part as the single fraction element `c3itVlift = [0, qxOfNum vNum / qxOfNum ρ]` and the integrand-minus-
leftover as `c3itRatLift = [0, qxOfNum (C − Crem) / qxOfNum ρ]` (`R/y = (R/ρ)·y`). The engine validates
`radDeriv 2 ρ c3itVlift = c3itRatLift` by `native_decide` (`c3itDriver_integrates`). Here that soundness is
proven **abstractly** (`[propext, Classical.choice, Quot.sound]`, no `native_decide`) **from the engine's own
cleared `cisZero` check** of the whole-accumulator polynomial identity `2·ρ·vNum' − vNum·ρ' = 2·ρ·(C − Crem)`
(supplied as the explicit hypothesis `hcheck` — the genuine-field reading of the run's `radCase3Residual`
sum, which the kernel cannot reduce for `ℚ`, hence stated rather than discharged): the fraction iff
`isRadicalRationalIntegral_div_qxOfNum_iff` collapses the radical derivation to that one `K[X]` identity, and
`clearedKX2_of_cisZeroG` reads the engine check into it. The remaining precondition is exactly `hcheck` — the
engine's own polynomial cleared identity for the run. -/

open RadElem CPoly

/-- **`toPoly c3itRho ≠ 0`** — the named run's radicand `ρ = x³+1` (`c3itRho = [1,0,0,1]`) has nonzero
`K[X]`-image: its constant coefficient is `toK 1 = 1 ≠ 0`. The `ρ̄ ≠ 0` side-condition of the fraction iff
for the `c3itRun` instantiation. -/
theorem toPolyG_c3itRho_ne_zero : CPoly.toPoly (c3itRho : CPoly ℚ) ≠ 0 := by
  intro h
  have hc : (CPoly.toPoly (c3itRho : CPoly ℚ)).coeff 0 = 0 := by rw [h, Polynomial.coeff_zero]
  rw [show (c3itRho : CPoly ℚ) = [1, 0, 0, 1] from rfl] at hc
  simp only [CPoly.toPolyG_cons, CPoly.toPolyG_nil, Polynomial.coeff_add, Polynomial.coeff_C_zero,
    Polynomial.coeff_X_mul_zero, add_zero] at hc
  exact one_ne_zero hc

/-- **`(2 : RatFunc (CFieldSpec.K ℚ)) ≠ 0`** — the power index `n = 2` is nonzero in the genuine field
`RatFunc ℚ`: `2 = am 2` and `am` is injective with `(2 : ℚ[X]) ≠ 0`. The `n ≠ 0` side-condition of the
fraction iff for `n = 2`. -/
theorem two_ne_zero_ratFunc : (2 : RatFunc (CFieldSpec.K ℚ)) ≠ 0 := by
  rw [show (2 : RatFunc (CFieldSpec.K ℚ)) = CFrac.am ℚ (2 : (CFieldSpec.K ℚ)[X]) from
    (map_ofNat _ 2).symm]
  exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective (CFieldSpec.K ℚ))).mpr
    (by show (2 : ℚ[X]) ≠ 0; exact two_ne_zero)

/-- **★ The named run `c3itRun` is sound, abstractly** — `IsRadicalRationalIntegral 2 [qxOfNum c3itRho]
c3itRatLift c3itVlift`, i.e. `toPoly (radDeriv 2 (qxOfNum c3itRho) c3itVlift) = toPoly c3itRatLift` in
`K[X]`: the actual diagonal radical derivation of the run's lifted rational part `c3itVlift = [0, qxOfNum
vNum / qxOfNum ρ]` equals the integrand-minus-leftover `c3itRatLift = [0, qxOfNum (C − Crem) / qxOfNum ρ]`.
Proven abstractly (no `native_decide`) **from the engine's own cleared `cisZero` check** `hcheck` (the
whole-accumulator polynomial identity `2·ρ·vNum' − vNum·ρ' = 2·ρ·(C − Crem)`): `clearedKX2_of_cisZeroG`
reads it into the fraction iff's `K[X]` identity, then `isRadicalRationalIntegral_div_qxOfNum_iff` (at
`n = 2`, `ρ̄ ≠ 0` by `toPolyG_c3itRho_ne_zero`, `2 ≠ 0` by `two_ne_zero_ratFunc`) closes it. The engine's
`native_decide` fact `c3itDriver_integrates`, here a corollary of the abstract derivation **modulo the one
polynomial check** `hcheck`. -/
theorem isRadicalRationalIntegral_c3itRun
    (hcheck : CPoly.cisZero
        (CPoly.csub (CPoly.csub (CPoly.cmul (CPoly.cscale (2 : ℚ) c3itRho) (CPoly.cderiv c3itRun.2))
          (CPoly.cmul c3itRun.2 (CPoly.cderiv c3itRho)))
          (CPoly.cmul (CPoly.cscale (2 : ℚ) c3itRho) (CPoly.csub c3itC c3itRun.1))) = true) :
    IsRadicalRationalIntegral 2 [qxOfNum c3itRho] c3itRatLift c3itVlift :=
  (isRadicalRationalIntegral_div_qxOfNum_iff 2 c3itRun.2 (csub c3itC c3itRun.1) c3itRho
    two_ne_zero_ratFunc toPolyG_c3itRho_ne_zero).mpr
    (clearedKX2_of_cisZeroG c3itRun.2 (csub c3itC c3itRun.1) c3itRho hcheck)

/-- **★ The `radIsZero` engine-test form of the named run's soundness**, abstractly — `radIsZero (radSub
(radDeriv 2 c3itRhoQx c3itVlift) c3itRatLift) = true`: the engine's `native_decide` statement
`c3itDriver_integrates`, here derived from the abstract `K[X]` identity `isRadicalRationalIntegral_c3itRun`
through `cisZeroG_iff` / `toPolyG_csubG` (so it carries **no** `native_decide` axiom — only the engine's
polynomial cleared check `hcheck`). The same proposition the kernel checks numerically, here a theorem of the
abstract derivation. `c3itRhoQx = qxOfNum c3itRho` is the run's radicand. -/
theorem radIsZero_radDeriv_c3itVlift
    (hcheck : CPoly.cisZero
        (CPoly.csub (CPoly.csub (CPoly.cmul (CPoly.cscale (2 : ℚ) c3itRho) (CPoly.cderiv c3itRun.2))
          (CPoly.cmul c3itRun.2 (CPoly.cderiv c3itRho)))
          (CPoly.cmul (CPoly.cscale (2 : ℚ) c3itRho) (CPoly.csub c3itC c3itRun.1))) = true) :
    radIsZero (radSub (radDeriv 2 c3itRhoQx c3itVlift) c3itRatLift) = true := by
  rw [radIsZero, radSub, CPoly.cisZeroG_iff]
  simp only [denote]
  rw [sub_eq_zero]
  simpa only [IsRadicalRationalIntegral, c3itRhoQx, c3itRho, List.headD_cons, denote]
    using isRadicalRationalIntegral_c3itRun hcheck

/-! ### The GENERAL rational-part soundness: what is now a theorem, and the precise residual

This file proves the **general rational-part soundness as an abstract `K[X]` theorem** —
`radDeriv_foldlRadAdd_zero_cons_telescope`:

> For a list of step-contribution coefficients `cBs` and a one-longer list of leftover coefficients
> `cCs` (head = the original integrand's `y`-coefficient, last = the final leftover's), **if** every step
> satisfies the base-field equation `D(cBᵢ) + cBᵢ·ℓ = cCᵢ − cCᵢ₊₁` in `K`, **then** the assembled
> antiderivative `v = (cBs.map (·↦[0,·])).foldl radAdd radZero` satisfies
> `toPoly (radDeriv n f v) + toPoly [0, cC_last] = toPoly [0, cC_head]`,

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

**★ The precondition is now discharged for the LITERAL `qxOfNum`-coefficient lifts** — what
`radDeriv_foldlRadAdd_zero_cons_telescope` takes as its **precondition**, the list of per-step `K`-equations
`D(cBᵢ) + cBᵢ·ℓ = cCᵢ − cCᵢ₊₁`, is, for the literal `radIntegrateRational` over `α = CFrac ℚ`, each
iterate step's *polynomial* cleared identity `B'f + Bg − C = D` lifted to the field equation on the `R/y ↦
(R/ρ)·y` coefficients. That lift is now a theorem via three `CFrac ℚ`-specific bridges, **all landed and
axiom-clean** (none of them `radDeriv`-arithmetic):

* (i) **`toCFracG_cderiv_qxOfNum`** — `cderiv (qxOfNum P) = qxOfNum (cderiv P)` read in `RatFunc ℚ`: the
  polynomial embedding `qxOfNum : CPoly ℚ → CFrac ℚ` commutes with the derivation. The substantive
  bridge: `cderiv = towerDerivCFrac [1]` realizes `extendDeriv (implicitDeriv (toPoly [1]))`, which on
  the algebra-map image `qxOfNum P ↦ am (toPoly P)` is `algebraMap (baseDerivQ (toPoly P))`, and
  `baseDerivQ` is the plain `derivative` over `ℚ` (`baseDerivQ_apply`).
* (ii) **`toK_logDerRadicand_mul_radicand`** — `ℓ·f = (1/n)·f'` in `K` (`toK (logDerRadicand n f · f) =
  n⁻¹·toK f'`): the integrand-helper `g = (1/n)f'` IS the diagonal multiplier `ℓ = f'/(nf)` times the
  radicand `f`, rearranged from the crux `toK_logDerRadicand_mul`.
* (iii) **`radCase3Residual_eq`** — the per-step polynomial cleared identity `B'f + Bg − C` is definitional
  (`rfl`).

Composed: **`toK_step_qxOfNum_iff`** turns each step's cleared polynomial identity
`(n:K[X])·ρ̄·Bᵢ' + Bᵢ·ρ̄' = (n:K[X])·ρ̄·(Cᵢ − Cᵢ₊₁)` into the telescope's per-step `K`-equation (bridges (i)
+(ii) read the `toK`s through `am`, `am`-injectivity descends the cleared `RatFunc` equation), and
**`radDeriv_foldlRadAdd_qxOfNum_telescope`** assembles them into the **LITERAL** rational-part soundness over
`ℚ(x)`: for `qxOfNum`-of-polynomial step/leftover lists, `radDeriv n (qxOfNum ρ) (assembled v) + [0,
qxOfNum Cpolys.last] = [0, qxOfNum Cpolys.head]` in `K[X]`, under `n ≠ 0`, `ρ ≠ 0`, and the per-step
polynomial cleared identities.

**★ The NAMED-run gap is now closed (via the whole-accumulator FRACTION route).** The named runs
(`c3itRun`/`gcuspYRun`/`mcRun`) do *not* lift their antiderivative as the telescope's `radAdd`-fold of pure-`y`
contributions `[0, qxOfNum Bᵢ]` — they lift the **whole accumulator** `vNum` over the common denominator `ρ`
as the *single* fraction element `[0, qxOfNum vNum / qxOfNum ρ]`. So rather than extract the per-step
`Bpolys`/`Cpolys` (the fuel recursion's accumulator chain, genuinely fiddly), the named run is handled as one
`C/y` *fraction*: **`isRadicalRationalIntegral_div_qxOfNum_iff`** (the fraction-coefficient variant of
`toK_step_qxOfNum_iff`) collapses `radDeriv n (qxOfNum ρ) [0, qxOfNum N / qxOfNum ρ] = [0, qxOfNum M / qxOfNum
ρ]` — clearing the denominator `ρ` (quotient rule `Derivation.leibniz_div` + `deriv_amG_toPolyG`) and the index
`n` — to the single cleared `K[X]` identity `(n:K[X])·(ρ̄·N̄' − N̄·ρ̄') + N̄·ρ̄' = (n:K[X])·ρ̄·M̄`. At `n = 2`
(every named run is `radDeriv 2`) this is `2·ρ̄·N̄' − N̄·ρ̄' = 2·ρ̄·M̄`, and **`clearedKX2_of_cisZeroG`** reads it
*off the engine's own polynomial `cisZero` check* through `cisZeroG_iff` + `toPolyG_csubG` (no `radDeriv`/
`RatFunc` reasoning). Composed: **`isRadicalRationalIntegral_c3itRun`** / **`radIsZero_radDeriv_c3itVlift`**
prove the literal `∫ x⁴/√(x³+1)` run `radDeriv 2 c3itRhoQx c3itVlift = c3itRatLift` — the engine's
`native_decide` fact `c3itDriver_integrates`, here a **theorem of the abstract derivation**
(`[propext, Classical.choice, Quot.sound]`, no `native_decide`).

**The one precondition that genuinely remains** is the run's whole-accumulator cleared identity itself, supplied
as the explicit hypothesis `hcheck : cisZero (2·ρ·vNum' − vNum·ρ' − 2·ρ·(C − Crem)) = true`. This is the
engine's *own* polynomial check over the named run's `vNum`/`Crem`, but it is **not** dischargeable abstractly:
the kernel cannot reduce `c3itRun` (the fuel recursion over `ℚ` — `decide`/`rfl` both get stuck on `ℚ`
arithmetic; only `native_decide`'s compiler evaluates it), so the run's output and its cleared check are
accessible *only* through the forbidden `native_decide`. Hence `radDeriv(radIntegrateRational g) = g` is now
self-contained **modulo exactly this one polynomial check** — the radical-derivation soundness fully reduced
to a single `cisZero`-shaped `ℚ[X]` identity over the run, the irreducible `native_decide`-only kernel
residue. -/

/-! ### `#print axioms` — the bridges and the literal soundness are abstractly verified (no `native_decide`)

Each soundness theorem and each of the three literal-radical bridges carries **only** the standard
`[propext, Classical.choice, Quot.sound]` (or, for the definitional bridge (iii), *no* axioms) — no
`native_decide` compiler axiom, no `sorry`. The simple-radical integral `∫ (f'/(nf))·√f = √f`, its two-term
generalization, the `C/y`-form reduction, the **telescoping invariant**, the **general rational-part
soundness** `radDeriv(assembled v) = integrand − final-leftover`, the three `CFrac ℚ` bridges
(i)/(ii)/(iii), and the **LITERAL `qxOfNum`-coefficient soundness** `radDeriv_foldlRadAdd_qxOfNum_telescope`
are all general theorems (specialized to the concrete elliptic radicand `x³+1` over `ℚ(x)` for the
headline). The seed-plus-engine of the soundness capstone `D(∫f) = f`. -/

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

-- ★ Bridge (i): the derivation commutes with `qxOfNum` (the substantive `RatFunc ℚ` bridge):
#print axioms toCFracG_cderiv_qxOfNum

-- ★ Bridge (ii): `g = ℓ·f` in `K` (the diagonal multiplier times the radicand is `(1/n)f'`):
#print axioms RadElem.toK_logDerRadicand_mul_radicand

-- ★ Bridge (iii): the per-step polynomial cleared identity `B'f + Bg − C` is definitional:
#print axioms CPoly.radCase3Residual_eq

-- ★ The LITERAL per-step `K`-equation ⟺ cleared polynomial identity (i+ii+iii composed at one step):
#print axioms RadElem.toK_step_qxOfNum_iff

-- ★★ The LITERAL rational-part soundness over ℚ(x): `radDeriv(assembled qxOfNum-v) = integrand − leftover`:
#print axioms RadElem.radDeriv_foldlRadAdd_qxOfNum_telescope

-- ★ The concrete elliptic-radicand integral over ℚ(x), abstractly (the engine's native_decide fact):
#print axioms radDeriv_radGen_sound_qx
#print axioms radIsZero_radDeriv_radGen_qx

-- ★ The FRACTION-coefficient single-step iff (the named-run lift `[0, qxOfNum N / qxOfNum ρ]`):
#print axioms RadElem.isRadicalRationalIntegral_div_qxOfNum_iff

-- ★ Reading the engine's cleared `cisZero` check into the fraction-iff `K[X]` identity (n = 2):
#print axioms RadElem.clearedKX2_of_cisZeroG

-- ★ The NAMED driver run `c3itRun` (`∫ x⁴/√(x³+1)`) is sound, abstractly, from the engine's own check:
#print axioms isRadicalRationalIntegral_c3itRun
#print axioms radIsZero_radDeriv_c3itVlift

end DeepWiki.SymbolicIntegration
