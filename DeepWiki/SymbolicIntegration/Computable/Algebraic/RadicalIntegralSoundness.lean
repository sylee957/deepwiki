import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalDerivationInvariant
import DeepWiki.SymbolicIntegration.Computable.SplitFactorTowerCorrectG
import DeepWiki.SymbolicIntegration.Computable.Algebraic.RadicalRationalDriver

/-! # Abstract soundness of the radical rational-part integrator: `radDeriv v = g` in `K[X]`

Through the Horner bridge `toPolyG : RadElem α → K[X]` (with `X` the generator `y`, `K = CFieldSpec.K α`),
the diagonal derivation `radDeriv n f` is `Differential.implicitDeriv (C (toK ℓ) · X)` for the rule
`y' = ℓ·y`, `ℓ = logDerRadicand n f = f'/(nf)`. Using this keystone, the rational-part integrator's
`radDeriv v = g` is proven as a genuine-field `K[X]` identity, with no `native_decide`.

The predicate is `IsRadicalRationalIntegral n f g v` (`toPolyG (radDeriv n f v) = toPolyG g`); concrete
instances are `isRadicalRationalIntegral_radGen` (`∫ (f'/(nf))·√f = √f`) and
`isRadicalRationalIntegral_linear` (two-term antiderivatives). The general soundness is the telescoping
invariant `radReduceRationalTelescope` and `radDeriv_foldlRadAdd_zero_cons_telescope`, whose per-step
`K`-equation precondition is discharged for the literal `qxOfNum`-coefficient lifts via three
`QFunNZG ℚ`-specific bridges (`toQFunNZG_cderiv_qxOfNum`, `toK_logDerRadicand_mul_radicand`,
`radCase3Residual_eq`), composed by `toK_step_qxOfNum_iff` and `radDeriv_foldlRadAdd_qxOfNum_telescope`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace RadElem

variable {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]

/-! ### The Horner readings `toPolyG radGen = X` and `toPolyG [0, c] = C(toK c)·X` -/

omit [CDiffField α] [CDiffFieldSpec α] in
/-- `toPolyG radGen = X`: the generator `y = √f` (`radGen = [0, 1]`) reads as `X` under the Horner
bridge. -/
@[denote] theorem toPolyG_radGen : CPolyG.toPolyG (radGen : RadElem α) = X := by
  show CPolyG.toPolyG [CField.zero, CField.one] = X
  rw [CPolyG.toPolyG_cons, CPolyG.toPolyG_cons, CPolyG.toPolyG_nil, mul_zero, add_zero,
    CFieldSpec.toK_zero, CFieldSpec.toK_one, map_zero, map_one, zero_add, mul_one]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- `toPolyG [zero, c] = C (toK c) · X`: the pure-`y` element `c·y` reads as `C(toK c)·X`. -/
theorem toPolyG_zero_cons (c : α) :
    CPolyG.toPolyG ([CField.zero, c] : RadElem α) = Polynomial.C (CFieldSpec.toK c) * X := by
  rw [CPolyG.toPolyG_cons, CPolyG.toPolyG_cons, CPolyG.toPolyG_nil, mul_zero, add_zero,
    CFieldSpec.toK_zero, map_zero, zero_add]
  ring

/-! ### The soundness predicate and the concrete algebraic integrals -/

/-- The radical rational-integral soundness predicate `IsRadicalRationalIntegral n f g v`: the radical
element `v` integrates `g` over `α[y]/(yⁿ − f)` (rational part), i.e. the genuine-field identity
`toPolyG (radDeriv n f v) = toPolyG g` in `K[X]`. -/
def IsRadicalRationalIntegral (n : ℕ) (f g v : RadElem α) : Prop :=
  CPolyG.toPolyG (radDeriv n (f.headD CField.zero) v) = CPolyG.toPolyG g

/-- The algebraic integral `∫ (f'/(nf))·√f dx = √f`: `toPolyG (radDeriv n f radGen) =
toPolyG [zero, logDerRadicand n f]` in `K[X]`, via the keystone + `toPolyG_radGen` + `implicitDeriv_X`.
General in `n`, `f`, `α`; no `n·toK f ≠ 0` needed. -/
theorem toPolyG_radDeriv_radGen (n : ℕ) (f : α) :
    CPolyG.toPolyG (radDeriv n f (radGen : RadElem α))
      = CPolyG.toPolyG ([CField.zero, logDerRadicand n f] : RadElem α) := by
  rw [toPolyG_radDeriv, toPolyG_radGen, Differential.implicitDeriv_X,
    toPolyG_zero_cons (logDerRadicand n f)]

/-- The radical integral `∫ (f'/(nf))·√f = √f` as a soundness instance:
`IsRadicalRationalIntegral n [f] [zero, logDerRadicand n f] radGen`, via `toPolyG_radDeriv_radGen`. -/
theorem isRadicalRationalIntegral_radGen (n : ℕ) (f : α) :
    IsRadicalRationalIntegral n [f] ([CField.zero, logDerRadicand n f]) (radGen : RadElem α) := by
  show CPolyG.toPolyG (radDeriv n (([f] : RadElem α).headD CField.zero) radGen) = _
  rw [List.headD_cons, toPolyG_radDeriv_radGen]

/-! ### A general degree-`< n` antiderivative: `D(a₀ + a₁y) = D(a₀) + (D(a₁) + a₁ℓ)·y` -/

/-- The diagonal-derivation identity for a two-term antiderivative:
`toPolyG (radDeriv n f [a₀, a₁]) = toPolyG [D(a₀), D(a₁) + a₁·ℓ]` with `ℓ = logDerRadicand n f`, i.e.
`D(a₀ + a₁y) = D(a₀) + (D(a₁) + a₁·ℓ)·y` in `K[X]`. -/
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

/-- The two-term radical integral as a soundness instance:
`IsRadicalRationalIntegral n [f] [D(a₀), D(a₁) + a₁·ℓ] [a₀, a₁]`, via `toPolyG_radDeriv_linear`. -/
theorem isRadicalRationalIntegral_linear (n : ℕ) (f a₀ a₁ : α) :
    IsRadicalRationalIntegral n [f]
      ([CDiffField.cderiv a₀,
        CField.add (CDiffField.cderiv a₁) (CField.mul a₁ (logDerRadicand n f))])
      ([a₀, a₁] : RadElem α) := by
  show CPolyG.toPolyG (radDeriv n (([f] : RadElem α).headD CField.zero) [a₀, a₁]) = _
  rw [List.headD_cons, toPolyG_radDeriv_linear]

/-! ### The fuel-recursion telescoping invariant

The driver's accumulator `radDeriv(vNum) + leftover = original integrand` is a telescoping of `radDeriv`
over the contribution list: `radDeriv` distributes over `foldl radAdd` (`toPolyG_radDeriv_foldlRadAdd`)
and the per-step contributions telescope to the endpoints (`sum_radDeriv_telescope`), giving
`radReduceRationalTelescope`. -/

variable {α : Type*} [CField α] [CDiffField α] [CFieldSpec α] [CDiffFieldSpec α]

/-- `radDeriv` distributes over the accumulator fold: `toPolyG (radDeriv n f (cs.foldl radAdd acc)) =
toPolyG (radDeriv n f acc) + (cs.map (fun c => toPolyG (radDeriv n f c))).sum`. -/
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
/-- The per-step contributions telescope (head/last form): if each contribution's `radDeriv`-image is
the difference of consecutive leftovers (zipped as `(L₀ :: rest).zip rest`), the sum is
`toPolyG L₀ − toPolyG (rest.getLastD L₀)`. Stated via `List.Forall₂` to keep the endpoints free of
index obligations. -/
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

/-- The master rational-part telescoping soundness: for contributions `cs` (accumulated from `radZero`)
and leftovers `L₀ :: rest`, if each contribution's `radDeriv`-image is the difference of consecutive
leftovers, then `v = cs.foldl radAdd radZero` satisfies
`toPolyG (radDeriv n f v) + toPolyG (final leftover) = toPolyG (original integrand)` in `K[X]`. Composes
`toPolyG_radDeriv_foldlRadAdd` and `sum_radDeriv_telescope`. -/
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

/-! ### The `C/y`-form single step: reduction to one base-field equation

Every `R/y`-form piece of the rational-part driver lifts to a pure-`y` element `[0, c]` (`c·y`); for such
`v = c·y` and integrand `g = γ·y`, `radDeriv n f v = g` collapses to the single base-field equation
`D(c) + c·ℓ = γ` (`ℓ = logDerRadicand n f`). -/

/-- The `y`-component reading of a `C/y`-form antiderivative's derivative:
`toPolyG (radDeriv n f [zero, c]) = C (toK (D(c) + c·ℓ)) · X` with `ℓ = logDerRadicand n f`. Specializes
`toPolyG_radDeriv_linear` at `a₀ = 0`. -/
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
  rw [radIsZero, radSub, CPolyG.cisZeroG_iff]
  simp only [denote]
  rw [radDeriv_radGen_sound_qx]
  simp only [denote]
  ring

/-! ### Bridge (i): the `qxOfNum : CPolyG ℚ → QFunNZG ℚ` lift commutes with the derivation

The literal `radIntegrateRational` over `α = QFunNZG ℚ` builds its base-field coefficients by
`qxOfNum : CPolyG ℚ → QFunNZG ℚ` (`p ↦ ⟨(p, [1]), _⟩`, a polynomial over denominator `1`). Discharging
the per-step `K`-equation `D(cBᵢ) + cBᵢ·ℓ = cCᵢ − cCᵢ₊₁` for a *concrete* driver run needs to push the
engine's polynomial derivative `cderivG : CPolyG ℚ → CPolyG ℚ` (formal `d/dX` on coefficient lists)
through `qxOfNum` and `cderiv` (the tower derivation `towerDerivQFunNZG [1]`). This is the substantive
noncomputable bridge — it lives in the genuine field `RatFunc ℚ` (`= CFieldSpec.K (QFunNZG ℚ)`), read
through `toQFunNZG = CFieldSpec.toK`.

The chain: `qxOfNum p` reads as the algebra-map image `amG (toPolyG p) = algebraMap ℚ[X] (RatFunc ℚ)
(toPolyG p)` (denominator `1`); the tower derivation `towerDerivQFunNZG [1]` realizes Mathlib's
`extendDeriv (implicitDeriv (toPolyG [1]))` (`toQFunNZG_towerDerivQFunNZG`), which on an algebra-map image
is `algebraMap (baseDerivQ (toPolyG p))` (`extendDeriv_algebraMap`); and `baseDerivQ = implicitDeriv
(toPolyG [1]) = implicitDeriv 1` is the plain polynomial `derivative` over `ℚ` (the base `Differential ℚ`
is `⟨0⟩`, so `mapCoeffs = 0`), which matches `toPolyG (cderivG p)` (`toPolyG_cderivG`). -/

/-- **`qxOfNum p` reads as `algebraMap ℚ[X] (RatFunc ℚ) (toPolyG p)`** — the genuine-field image of the
polynomial-over-`1` element `qxOfNum p = ⟨(p, [1]), _⟩` is `amG (toPolyG p)` (denominator `[1]` reads as
`1`, so the quotient `amG (toPolyG p) / 1` collapses). The reading that turns the derivation-commutation
bridge into an `extendDeriv ∘ algebraMap` computation. -/
theorem toQFunNZG_qxOfNum (p : CPolyG ℚ) :
    QFunNZG.toQFunNZG (qxOfNum p) = QFunNZG.amG ℚ (CPolyG.toPolyG p) := by
  show QFunNZG.amG ℚ (CPolyG.toPolyG p) / QFunNZG.amG ℚ (CPolyG.toPolyG ([CField.one] : CPolyG ℚ)) = _
  have h1 : CPolyG.toPolyG ([CField.one] : CPolyG ℚ) = 1 := by
    rw [CPolyG.toPolyG_cons, CPolyG.toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]
  rw [h1, map_one, div_one]

/-- **`baseDerivQ` is the plain polynomial derivative over `ℚ`** — `baseDerivQ q = Polynomial.derivative
q` in `ℚ[X]`. `baseDerivQ = implicitDeriv (toPolyG [1]) = implicitDeriv 1 = mapCoeffs + 1 · derivative'`,
and over `ℚ` the base `Differential ℚ` is the zero derivation (`instDifferentialQ = ⟨0⟩`), so `mapCoeffs =
0` and only `derivative'` survives. The base-derivation half of bridge (i). -/
theorem baseDerivQ_apply (q : (CFieldSpec.K ℚ)[X]) :
    baseDerivQ q = Polynomial.derivative q := by
  have h1 : CPolyG.toPolyG ([CField.one] : CPolyG ℚ) = 1 := by
    rw [CPolyG.toPolyG_cons, CPolyG.toPolyG_nil, CFieldSpec.toK_one, mul_zero, add_zero, map_one]
  rw [baseDerivQ, h1, Differential.implicitDeriv]
  -- `mapCoeffs q = 0` (base deriv on ℚ is `0`), leaving `1 • derivative' q = derivative q`
  have hmc : Differential.mapCoeffs q = 0 := by
    ext i
    rw [Differential.coeff_mapCoeffs, Polynomial.coeff_zero]
    show @Differential.deriv ℚ _ _ (q.coeff i) = 0
    rfl
  simp only [Derivation.add_apply, hmc, Derivation.restrictScalars_apply, one_smul, zero_add]
  rfl

/-- **★ Bridge (i) — the derivation commutes with `qxOfNum`** — `toQFunNZG (cderiv (qxOfNum p)) =
toQFunNZG (qxOfNum (cderivG p))` in `RatFunc ℚ` (`= CFieldSpec.K (QFunNZG ℚ)`): the polynomial-into-ℚ(x)
embedding `qxOfNum : CPolyG ℚ → QFunNZG ℚ` is a derivation morphism, i.e. `cderiv ∘ qxOfNum = qxOfNum ∘
cderivG` read through the genuine field. The substantive noncomputable bridge of the literal-radical
soundness: `cderiv = towerDerivQFunNZG [1]` realizes `extendDeriv (implicitDeriv (toPolyG [1]))`
(`toQFunNZG_towerDerivQFunNZG`); on the algebra-map image `qxOfNum p ↦ amG (toPolyG p)`
(`toQFunNZG_qxOfNum`) this is `algebraMap (baseDerivQ (toPolyG p))` (`extendDeriv_algebraMap`); and
`baseDerivQ` is the plain `derivative` (`baseDerivQ_apply`), matching `toPolyG (cderivG p)`
(`toPolyG_cderivG`). -/
theorem toQFunNZG_cderiv_qxOfNum (p : CPolyG ℚ) :
    QFunNZG.toQFunNZG (CDiffField.cderiv (qxOfNum p))
      = QFunNZG.toQFunNZG (qxOfNum (CPolyG.cderivG p)) := by
  -- `cderiv = towerDerivQFunNZG [1]`; realize it as `extendDeriv (implicitDeriv (toPolyG [1]))`
  show QFunNZG.toQFunNZG (QFunNZG.towerDerivQFunNZG [CField.one] (qxOfNum p)) = _
  rw [QFunNZG.toQFunNZG_towerDerivQFunNZG, toQFunNZG_qxOfNum, toQFunNZG_qxOfNum, QFunNZG.amG]
  -- `extendDeriv (implicitDeriv (toPolyG [1])) (algebraMap (toPolyG p)) = algebraMap (baseDerivQ (toPolyG p))`
  rw [show Differential.implicitDeriv (CPolyG.toPolyG ([CField.one] : CPolyG ℚ)) = baseDerivQ from rfl,
    extendDeriv_algebraMap, baseDerivQ_apply, CPolyG.toPolyG_cderivG]

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
expression `csubG (caddG (cmulG Bder f) (cmulG B g)) C`. The engine's per-step cleared identity is
`radCase3Residual f g B C (cderivG B) = D` (the next leftover), and reading it through `toPolyG` is the
polynomial equation `B'·f + B·g − C = D` in `K[X]` — a `rfl`/`cisZeroG` fact, no `radDeriv` reasoning.
This is the trivial bridge: it just unfolds the definition. -/

namespace CPolyG

variable {α : Type*} [CField α] [CDiffField α]

omit [CDiffField α] in
/-- **Bridge (iii) — `radCase3Residual` is definitionally `B'f + Bg − C`** — `radCase3Residual f g B C
Bder = csubG (caddG (cmulG Bder f) (cmulG B g)) C`. The per-step polynomial cleared identity is `rfl`: the
residual the Case-3 iterate negates and recurses on is literally `B'·f + B·g − C` (with `Bder = B'`
supplied by the caller). No content beyond unfolding — the bridge is definitional. -/
theorem radCase3Residual_eq (f g B C Bder : CPolyG α) :
    radCase3Residual f g B C Bder
      = csubG (caddG (cmulG Bder f) (cmulG B g)) C :=
  rfl

end CPolyG

/-! ### ★ Composition (i)+(ii)+(iii): the literal `radDeriv(assembled v) = integrand − leftover` over `ℚ(x)`

With the three `QFunNZG ℚ` bridges in hand, the per-step `K`-equation precondition of
`radDeriv_foldlRadAdd_zero_cons_telescope` is discharged for the **literal** `radIntegrateRational`
coefficients — pure-`y` lifts of `qxOfNum`-of-polynomials over the radicand `qxOfNum ρ`. The genuine-field
`K`-equation `D(cBᵢ) + cBᵢ·ℓ = cCᵢ − cCᵢ₊₁` (with `cBᵢ = qxOfNum Bᵢ`, `cCᵢ = qxOfNum Cᵢ`, `ℓ =
logDerRadicand n (qxOfNum ρ) = ρ'/(nρ)`) clears, via bridges (i) (`cderiv∘qxOfNum = qxOfNum∘cderivG`) and
(ii) (`ℓ·ρ = (1/n)ρ'`), to the polynomial cleared identity `n·ρ·Bᵢ' + Bᵢ·ρ' = n·ρ·(Cᵢ − Cᵢ₊₁)` in
`K[X]` — the genuine-field reading of each engine step's `radCase3Residual = 0` (bridge (iii)). Feeding
the polynomial identities into the telescope yields the literal rational-part soundness over `ℚ(x)`. -/

namespace RadElem

open scoped Polynomial

/-- **`toK (qxOfNum p) = amG (toPolyG p)`** (`CFieldSpec.toK`-flavoured) — the same content as
`toQFunNZG_qxOfNum`, restated against `CFieldSpec.toK` (definitionally `QFunNZG.toQFunNZG` for `QFunNZG ℚ`)
so it `rw`s directly in `toK`-expressed goals. -/
theorem toK_qxOfNum (p : CPolyG ℚ) :
    CFieldSpec.toK (qxOfNum p) = QFunNZG.amG ℚ (CPolyG.toPolyG p) :=
  toQFunNZG_qxOfNum p

/-- **`toK (cderiv (qxOfNum p)) = amG (derivative (toPolyG p))`** (`CFieldSpec.toK`-flavoured bridge (i)) —
the genuine-field reading of `cderiv ∘ qxOfNum`: bridge (i) (`toQFunNZG_cderiv_qxOfNum`) composed with the
`qxOfNum`-reading and `toPolyG_cderivG`. The `toK`-side form used in the per-step composition. -/
theorem toK_cderiv_qxOfNum (p : CPolyG ℚ) :
    CFieldSpec.toK (CDiffField.cderiv (qxOfNum p))
      = QFunNZG.amG ℚ (derivative (CPolyG.toPolyG p)) := by
  rw [show CFieldSpec.toK (CDiffField.cderiv (qxOfNum p))
        = QFunNZG.toQFunNZG (CDiffField.cderiv (qxOfNum p)) from rfl,
    toQFunNZG_cderiv_qxOfNum, toQFunNZG_qxOfNum, CPolyG.toPolyG_cderivG]

/-- **`toK (logDerRadicand n (qxOfNum ρ)) = amG(ρ') / ((n:K)·amG(ρ))`** — the diagonal multiplier of the
literal radical derivation, read in `RatFunc ℚ`: `ℓ = ρ'/(nρ)` reads as `amG(derivative ρ̄)/((n:K)·amG ρ̄)`
(`ρ̄ = toPolyG ρ`). Routes `logDerRadicand`'s `div`/`mul`/`cnatCastG` through the `toK` homomorphism laws
and the bridge-(i) reading `toK_cderiv_qxOfNum`. -/
theorem toK_logDerRadicand_qxOfNum (n : ℕ) (ρ : CPolyG ℚ) :
    CFieldSpec.toK (logDerRadicand n (qxOfNum ρ))
      = QFunNZG.amG ℚ (derivative (CPolyG.toPolyG ρ))
        / ((n : RatFunc (CFieldSpec.K ℚ)) * QFunNZG.amG ℚ (CPolyG.toPolyG ρ)) := by
  rw [logDerRadicand, CFieldSpec.toK_div, CFieldSpec.toK_mul, CPolyG.toK_cnatCastG, toK_cderiv_qxOfNum,
    toK_qxOfNum]

/-- **★ The literal per-step `K`-equation reduces to the cleared polynomial identity** — for `qxOfNum`-of-
polynomial step coefficient `B` and consecutive leftovers `C`, `C'` over the radicand `ρ` (all `CPolyG ℚ`),
the telescope's per-step base-field equation
`toK (cderiv (qxOfNum B) + qxOfNum B · logDerRadicand n (qxOfNum ρ)) = toK (qxOfNum C) − toK (qxOfNum C')`
holds in `RatFunc ℚ` **iff** the cleared polynomial identity
`(n:K[X])·ρ̄·B̄' + B̄·ρ̄' = (n:K[X])·ρ̄·(C̄ − C̄')` holds in `K[X]` (`ρ̄ = toPolyG ρ` etc.), provided `n ≠ 0`
and `ρ̄ ≠ 0`. This is the (i)+(ii)+(iii) composition at one step: bridge (i) reads `cderiv∘qxOfNum`, bridge
(ii) clears `ℓ = ρ'/(nρ)`, and `amG` injectivity descends the `RatFunc` equation to the `K[X]` identity.
The genuine-field form of `radCase3Residual = 0`. -/
theorem toK_step_qxOfNum_iff (n : ℕ) (ρ B C C' : CPolyG ℚ)
    (hn : (n : RatFunc (CFieldSpec.K ℚ)) ≠ 0) (hρ : CPolyG.toPolyG ρ ≠ 0) :
    CFieldSpec.toK (CField.add (CDiffField.cderiv (qxOfNum B))
          (CField.mul (qxOfNum B) (logDerRadicand n (qxOfNum ρ))))
        = CFieldSpec.toK (qxOfNum C) - CFieldSpec.toK (qxOfNum C')
      ↔ (n : (CFieldSpec.K ℚ)[X]) * CPolyG.toPolyG ρ * derivative (CPolyG.toPolyG B)
            + CPolyG.toPolyG B * derivative (CPolyG.toPolyG ρ)
          = (n : (CFieldSpec.K ℚ)[X]) * CPolyG.toPolyG ρ
              * (CPolyG.toPolyG C - CPolyG.toPolyG C') := by
  -- read every `toK` through `amG` (bridge (i) for `cderiv`, the `ℓ` reading for the multiplier)
  rw [CFieldSpec.toK_add, CFieldSpec.toK_mul, toK_cderiv_qxOfNum, toK_qxOfNum, toK_qxOfNum,
    toK_qxOfNum, toK_logDerRadicand_qxOfNum]
  have hρK : QFunNZG.amG ℚ (CPolyG.toPolyG ρ) ≠ 0 := QFunNZG.amG_toPolyG_ne_zero hρ
  have hinj := RatFunc.algebraMap_injective (CFieldSpec.K ℚ)
  -- the `K[X]` identity, pushed through the ring hom `amG`, with the denominator `(n:K)·amG ρ̄ ≠ 0`
  -- cleared, is exactly the `RatFunc` equation; `amG` injectivity gives the converse.
  constructor
  · intro h
    apply hinj
    rw [map_add, map_mul, map_mul, map_mul, map_mul, map_mul, map_sub, map_natCast]
    field_simp [QFunNZG.amG] at h
    linear_combination h
  · intro h
    have h' := congrArg (QFunNZG.amG ℚ) h
    rw [map_add, map_mul, map_mul, map_mul, map_mul, map_mul, map_sub, map_natCast] at h'
    field_simp [QFunNZG.amG]
    linear_combination h'

/-- **★ The LITERAL rational-part soundness over `ℚ(x)`** — for a radicand `ρ`, a list of step-contribution
polynomials `Bpolys` and a one-longer list of leftover polynomials `Cpolys` (all `CPolyG ℚ`), **if** every
step's cleared polynomial identity `(n:K[X])·ρ̄·Bᵢ' + Bᵢ·ρ̄' = (n:K[X])·ρ̄·(Cᵢ − Cᵢ₊₁)` holds in `K[X]`
(`ρ̄ = toPolyG ρ` etc. — the genuine-field reading of each engine step's `radCase3Residual = 0`, bridge
(iii)), **then** the assembled pure-`y` antiderivative `v = (Bpolys.map (qxOfNum · ↦ [0, ·])).foldl radAdd
radZero` satisfies the soundness identity `radDeriv n (qxOfNum ρ) v + [0, qxOfNum Cpolys.last] = [0,
qxOfNum Cpolys.head]` in `K[X]` (`radDeriv(v) = integrand − final-leftover`). The (i)+(ii)+(iii) composition
for the LITERAL `qxOfNum`-coefficient lifts the `radIntegrateRational` driver produces: `toK_step_qxOfNum_iff`
turns each cleared polynomial identity into the telescope's per-step `K`-equation, then
`radDeriv_foldlRadAdd_zero_cons_telescope` assembles. Precondition: `n ≠ 0` (in `RatFunc ℚ`), `ρ ≠ 0`
(`toPolyG ρ ≠ 0`), and the per-step polynomial identities. -/
theorem radDeriv_foldlRadAdd_qxOfNum_telescope (n : ℕ) (ρ : CPolyG ℚ) (Bpolys Cpolys : List (CPolyG ℚ))
    (hlen : Bpolys.length + 1 = Cpolys.length)
    (hn : (n : RatFunc (CFieldSpec.K ℚ)) ≠ 0) (hρ : CPolyG.toPolyG ρ ≠ 0)
    (hpoly : ∀ i : ℕ, (hi : i < Bpolys.length) →
      (n : (CFieldSpec.K ℚ)[X]) * CPolyG.toPolyG ρ * derivative (CPolyG.toPolyG (Bpolys.get ⟨i, hi⟩))
          + CPolyG.toPolyG (Bpolys.get ⟨i, hi⟩) * derivative (CPolyG.toPolyG ρ)
        = (n : (CFieldSpec.K ℚ)[X]) * CPolyG.toPolyG ρ
            * (CPolyG.toPolyG (Cpolys.get ⟨i, by omega⟩)
              - CPolyG.toPolyG (Cpolys.get ⟨i + 1, by omega⟩))) :
    CPolyG.toPolyG (radDeriv n (qxOfNum ρ)
          (((Bpolys.map qxOfNum).map (fun cB => ([CField.zero, cB] : RadElem (QFunNZG ℚ)))).foldl
            radAdd radZero))
        + CPolyG.toPolyG
            ([CField.zero, (Cpolys.map qxOfNum).getLastD CField.zero] : RadElem (QFunNZG ℚ))
      = CPolyG.toPolyG ([CField.zero, (Cpolys.map qxOfNum).headD CField.zero] : RadElem (QFunNZG ℚ)) := by
  -- the radicand exposed to `radDeriv` is `(qxOfNum ρ).headD = qxOfNum ρ`? no — `radDeriv` takes the
  -- radicand directly here. Apply the abstract telescope at the `qxOfNum`-lifted coefficient lists.
  have hlen' : (Bpolys.map qxOfNum).length + 1 = (Cpolys.map qxOfNum).length := by
    rw [List.length_map, List.length_map]; omega
  have hkey := radDeriv_foldlRadAdd_zero_cons_telescope (α := QFunNZG ℚ) n (qxOfNum ρ)
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
into a single `K[X]` equation between `toPolyG`s. -/

/-- **`deriv (amG p) = amG (derivative p)`** in `RatFunc ℚ` — the Mathlib field derivation `Differential.deriv`
on the algebra-map image of a `K[X]`-polynomial is the algebra-map of its `derivative` (bridge (i) read in
the `deriv`/`amG` direction): `toK (cderiv (qxOfNum N)) = deriv (toK (qxOfNum N)) = deriv (amG (toPolyG N))`
(`toK_cderiv`) and `= amG (derivative (toPolyG N))` (`toK_cderiv_qxOfNum`), so the two readings agree on every
`toPolyG`. The `deriv`-side restatement of bridge (i), used to expand the quotient rule on `c = N̄/ρ̄`. -/
theorem deriv_amG_toPolyG (N : CPolyG ℚ) :
    @Differential.deriv _ _ (CDiffFieldSpec.diffK (α := QFunNZG ℚ))
        (QFunNZG.amG ℚ (CPolyG.toPolyG N))
      = QFunNZG.amG ℚ (derivative (CPolyG.toPolyG N)) := by
  rw [show QFunNZG.amG ℚ (CPolyG.toPolyG N) = CFieldSpec.toK (qxOfNum N) from (toK_qxOfNum N).symm,
    ← CDiffFieldSpec.toK_cderiv, toK_cderiv_qxOfNum]

/-- **★ The FRACTION-coefficient single-step iff** — for `qxOfNum`-of-polynomial numerator `N`, integrand
numerator `M`, and the common denominator `ρ` (all `CPolyG ℚ`), the `C/y`-form soundness with the fraction
coefficient `c = qxOfNum N / qxOfNum ρ` and integrand `γ = qxOfNum M / qxOfNum ρ`,
`IsRadicalRationalIntegral n [qxOfNum ρ] [0, γ] [0, c]` (i.e. `radDeriv n (qxOfNum ρ) [0, c] = [0, γ]` in
`K[X]`), holds **iff** the single cleared **polynomial** identity
`(n:K[X])·(ρ̄·N̄' − N̄·ρ̄') + N̄·ρ̄' = (n:K[X])·ρ̄·M̄` holds in `K[X] = ℚ[X]` (`N̄ = toPolyG N`, `ρ̄ = toPolyG ρ`,
`M̄ = toPolyG M`), provided `n ≠ 0` and `ρ̄ ≠ 0`. The denominator `ρ` and the index `n` are cleared through
the quotient rule (`Derivation.leibniz_div`) and `amG` injectivity; the constant `½ρ' = g` integrand-helper
of the driver is the `n = 2` case `M = C − Crem`. This is the named-run lift's reduction (the whole
accumulator `vNum/ρ·y` is a *single* `C/y` fraction, not a fold), composing `isRadicalRationalIntegral_
zero_cons_iff` (the `C/y`-form `K`-equation), bridge (i) (`deriv_amG_toPolyG`), and the `logDerRadicand`
reading. -/
theorem isRadicalRationalIntegral_div_qxOfNum_iff (n : ℕ) (N M ρ : CPolyG ℚ)
    (hn : (n : RatFunc (CFieldSpec.K ℚ)) ≠ 0) (hρ : CPolyG.toPolyG ρ ≠ 0) :
    IsRadicalRationalIntegral n [qxOfNum ρ]
        ([CField.zero, CField.div (qxOfNum M) (qxOfNum ρ)])
        ([CField.zero, CField.div (qxOfNum N) (qxOfNum ρ)] : RadElem (QFunNZG ℚ))
      ↔ (n : (CFieldSpec.K ℚ)[X]) * (CPolyG.toPolyG ρ * derivative (CPolyG.toPolyG N)
              - CPolyG.toPolyG N * derivative (CPolyG.toPolyG ρ))
            + CPolyG.toPolyG N * derivative (CPolyG.toPolyG ρ)
          = (n : (CFieldSpec.K ℚ)[X]) * CPolyG.toPolyG ρ * CPolyG.toPolyG M := by
  rw [isRadicalRationalIntegral_zero_cons_iff]
  -- abbreviations for the `amG`-images and the denominator nonzero facts
  have hρK : QFunNZG.amG ℚ (CPolyG.toPolyG ρ) ≠ 0 := QFunNZG.amG_toPolyG_ne_zero hρ
  have hinj := RatFunc.algebraMap_injective (CFieldSpec.K ℚ)
  -- expand the `K`-equation `toK(cderiv c + c·ℓ) = toK γ` through `toK_div`, bridge (i), and `ℓ = ρ'/(nρ)`
  rw [CFieldSpec.toK_add, CFieldSpec.toK_mul, CFieldSpec.toK_div, CFieldSpec.toK_div, toK_qxOfNum,
    toK_qxOfNum, toK_qxOfNum, toK_logDerRadicand_qxOfNum]
  -- `toK (cderiv (div (qxOfNum N) (qxOfNum ρ))) = deriv (amG N̄ / amG ρ̄)` (the quotient rule)
  rw [show CFieldSpec.toK (CDiffField.cderiv (CField.div (qxOfNum N) (qxOfNum ρ)))
        = @Differential.deriv _ _ (CDiffFieldSpec.diffK (α := QFunNZG ℚ))
            (QFunNZG.amG ℚ (CPolyG.toPolyG N) / QFunNZG.amG ℚ (CPolyG.toPolyG ρ)) by
      rw [CDiffFieldSpec.toK_cderiv, CFieldSpec.toK_div, toK_qxOfNum, toK_qxOfNum]]
  rw [Derivation.leibniz_div, smul_eq_mul, smul_eq_mul, smul_eq_mul, deriv_amG_toPolyG,
    deriv_amG_toPolyG]
  -- now a pure `RatFunc` equation in `amG`-images; clear denominators and descend by `amG` injectivity
  -- the cleared `K[X]` identity, transported through the ring hom `amG` (`map_*` + `map_natCast`),
  -- is exactly the `RatFunc` equation after clearing the denominator `(n:K)·amG ρ̄ ≠ 0`.
  have hden : (n : RatFunc (CFieldSpec.K ℚ)) * QFunNZG.amG ℚ (CPolyG.toPolyG ρ) ≠ 0 :=
    mul_ne_zero hn hρK
  constructor
  · intro h
    apply hinj
    rw [map_add, map_mul, map_mul, map_sub, map_mul, map_mul, map_mul, map_natCast]
    field_simp at h ⊢
    simp only [map_mul, map_natCast]
    linear_combination h
  · intro h
    have h' := congrArg (QFunNZG.amG ℚ) h
    rw [map_add, map_mul, map_mul, map_sub, map_mul, map_mul, map_mul, map_natCast] at h'
    field_simp
    simp only [map_mul, map_natCast] at h' ⊢
    linear_combination h'

/-- **★ Reading the engine's cleared `cisZeroG` check into the fraction-iff `K[X]` identity** (the `n = 2`
named-run form) — given the engine-side polynomial check `cisZeroG (2·ρ·N' − N·ρ' − 2·ρ·M) = true` (the
whole-accumulator cleared identity over `CPolyG ℚ`, `2·_ = cscaleG 2`, `_' = cderivG`), reading it abstractly
through `cisZeroG_iff` + `toPolyG_csubG` (+ `toPolyG_cmulG`/`toPolyG_cscaleG`/`toPolyG_cderivG`) yields the
`K[X] = ℚ[X]` identity `(2:K[X])·(ρ̄·N̄' − N̄·ρ̄') + N̄·ρ̄' = (2:K[X])·ρ̄·M̄` — exactly the hypothesis of
`isRadicalRationalIntegral_div_qxOfNum_iff` at `n = 2` (`2(ρ̄N̄' − N̄ρ̄') + N̄ρ̄' = 2ρ̄N̄' − N̄ρ̄'`). The bridge
that turns a named driver run's own `cisZeroG` check (its cleared polynomial identity) into the fraction
iff's precondition, with no `radDeriv`/`RatFunc` reasoning — only the `toPolyG` polynomial readings. -/
theorem clearedKX2_of_cisZeroG (N M ρ : CPolyG ℚ)
    (hcheck : CPolyG.cisZeroG
        (CPolyG.csubG (CPolyG.csubG (CPolyG.cmulG (CPolyG.cscaleG (2 : ℚ) ρ) (CPolyG.cderivG N))
          (CPolyG.cmulG N (CPolyG.cderivG ρ)))
          (CPolyG.cmulG (CPolyG.cscaleG (2 : ℚ) ρ) M)) = true) :
    (2 : (CFieldSpec.K ℚ)[X]) * (CPolyG.toPolyG ρ * derivative (CPolyG.toPolyG N)
            - CPolyG.toPolyG N * derivative (CPolyG.toPolyG ρ))
          + CPolyG.toPolyG N * derivative (CPolyG.toPolyG ρ)
      = (2 : (CFieldSpec.K ℚ)[X]) * CPolyG.toPolyG ρ * CPolyG.toPolyG M := by
  rw [CPolyG.cisZeroG_iff, CPolyG.toPolyG_csubG, sub_eq_zero, CPolyG.toPolyG_csubG,
    CPolyG.toPolyG_cmulG, CPolyG.toPolyG_cmulG, CPolyG.toPolyG_cscaleG, CPolyG.toPolyG_cmulG,
    CPolyG.toPolyG_cscaleG, CPolyG.toPolyG_cderivG, CPolyG.toPolyG_cderivG] at hcheck
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
cleared `cisZeroG` check** of the whole-accumulator polynomial identity `2·ρ·vNum' − vNum·ρ' = 2·ρ·(C − Crem)`
(supplied as the explicit hypothesis `hcheck` — the genuine-field reading of the run's `radCase3Residual`
sum, which the kernel cannot reduce for `ℚ`, hence stated rather than discharged): the fraction iff
`isRadicalRationalIntegral_div_qxOfNum_iff` collapses the radical derivation to that one `K[X]` identity, and
`clearedKX2_of_cisZeroG` reads the engine check into it. The remaining precondition is exactly `hcheck` — the
engine's own polynomial cleared identity for the run. -/

open RadElem CPolyG

/-- **`toPolyG c3itRho ≠ 0`** — the named run's radicand `ρ = x³+1` (`c3itRho = [1,0,0,1]`) has nonzero
`K[X]`-image: its constant coefficient is `toK 1 = 1 ≠ 0`. The `ρ̄ ≠ 0` side-condition of the fraction iff
for the `c3itRun` instantiation. -/
theorem toPolyG_c3itRho_ne_zero : CPolyG.toPolyG (c3itRho : CPolyG ℚ) ≠ 0 := by
  intro h
  have hc : (CPolyG.toPolyG (c3itRho : CPolyG ℚ)).coeff 0 = 0 := by rw [h, Polynomial.coeff_zero]
  rw [show (c3itRho : CPolyG ℚ) = [1, 0, 0, 1] from rfl] at hc
  simp only [CPolyG.toPolyG_cons, CPolyG.toPolyG_nil, Polynomial.coeff_add, Polynomial.coeff_C_zero,
    Polynomial.coeff_X_mul_zero, add_zero] at hc
  exact one_ne_zero hc

/-- **`(2 : RatFunc (CFieldSpec.K ℚ)) ≠ 0`** — the power index `n = 2` is nonzero in the genuine field
`RatFunc ℚ`: `2 = amG 2` and `amG` is injective with `(2 : ℚ[X]) ≠ 0`. The `n ≠ 0` side-condition of the
fraction iff for `n = 2`. -/
theorem two_ne_zero_ratFunc : (2 : RatFunc (CFieldSpec.K ℚ)) ≠ 0 := by
  rw [show (2 : RatFunc (CFieldSpec.K ℚ)) = QFunNZG.amG ℚ (2 : (CFieldSpec.K ℚ)[X]) from
    (map_ofNat _ 2).symm]
  exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective (CFieldSpec.K ℚ))).mpr
    (by show (2 : ℚ[X]) ≠ 0; exact two_ne_zero)

/-- **★ The named run `c3itRun` is sound, abstractly** — `IsRadicalRationalIntegral 2 [qxOfNum c3itRho]
c3itRatLift c3itVlift`, i.e. `toPolyG (radDeriv 2 (qxOfNum c3itRho) c3itVlift) = toPolyG c3itRatLift` in
`K[X]`: the actual diagonal radical derivation of the run's lifted rational part `c3itVlift = [0, qxOfNum
vNum / qxOfNum ρ]` equals the integrand-minus-leftover `c3itRatLift = [0, qxOfNum (C − Crem) / qxOfNum ρ]`.
Proven abstractly (no `native_decide`) **from the engine's own cleared `cisZeroG` check** `hcheck` (the
whole-accumulator polynomial identity `2·ρ·vNum' − vNum·ρ' = 2·ρ·(C − Crem)`): `clearedKX2_of_cisZeroG`
reads it into the fraction iff's `K[X]` identity, then `isRadicalRationalIntegral_div_qxOfNum_iff` (at
`n = 2`, `ρ̄ ≠ 0` by `toPolyG_c3itRho_ne_zero`, `2 ≠ 0` by `two_ne_zero_ratFunc`) closes it. The engine's
`native_decide` fact `c3itDriver_integrates`, here a corollary of the abstract derivation **modulo the one
polynomial check** `hcheck`. -/
theorem isRadicalRationalIntegral_c3itRun
    (hcheck : CPolyG.cisZeroG
        (CPolyG.csubG (CPolyG.csubG (CPolyG.cmulG (CPolyG.cscaleG (2 : ℚ) c3itRho) (CPolyG.cderivG c3itRun.2))
          (CPolyG.cmulG c3itRun.2 (CPolyG.cderivG c3itRho)))
          (CPolyG.cmulG (CPolyG.cscaleG (2 : ℚ) c3itRho) (CPolyG.csubG c3itC c3itRun.1))) = true) :
    IsRadicalRationalIntegral 2 [qxOfNum c3itRho] c3itRatLift c3itVlift :=
  (isRadicalRationalIntegral_div_qxOfNum_iff 2 c3itRun.2 (csubG c3itC c3itRun.1) c3itRho
    two_ne_zero_ratFunc toPolyG_c3itRho_ne_zero).mpr
    (clearedKX2_of_cisZeroG c3itRun.2 (csubG c3itC c3itRun.1) c3itRho hcheck)

/-- **★ The `radIsZero` engine-test form of the named run's soundness**, abstractly — `radIsZero (radSub
(radDeriv 2 c3itRhoQx c3itVlift) c3itRatLift) = true`: the engine's `native_decide` statement
`c3itDriver_integrates`, here derived from the abstract `K[X]` identity `isRadicalRationalIntegral_c3itRun`
through `cisZeroG_iff` / `toPolyG_csubG` (so it carries **no** `native_decide` axiom — only the engine's
polynomial cleared check `hcheck`). The same proposition the kernel checks numerically, here a theorem of the
abstract derivation. `c3itRhoQx = qxOfNum c3itRho` is the run's radicand. -/
theorem radIsZero_radDeriv_c3itVlift
    (hcheck : CPolyG.cisZeroG
        (CPolyG.csubG (CPolyG.csubG (CPolyG.cmulG (CPolyG.cscaleG (2 : ℚ) c3itRho) (CPolyG.cderivG c3itRun.2))
          (CPolyG.cmulG c3itRun.2 (CPolyG.cderivG c3itRho)))
          (CPolyG.cmulG (CPolyG.cscaleG (2 : ℚ) c3itRho) (CPolyG.csubG c3itC c3itRun.1))) = true) :
    radIsZero (radSub (radDeriv 2 c3itRhoQx c3itVlift) c3itRatLift) = true := by
  rw [radIsZero, radSub, CPolyG.cisZeroG_iff, CPolyG.toPolyG_csubG, sub_eq_zero]
  exact isRadicalRationalIntegral_c3itRun hcheck

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

**★ The precondition is now discharged for the LITERAL `qxOfNum`-coefficient lifts** — what
`radDeriv_foldlRadAdd_zero_cons_telescope` takes as its **precondition**, the list of per-step `K`-equations
`D(cBᵢ) + cBᵢ·ℓ = cCᵢ − cCᵢ₊₁`, is, for the literal `radIntegrateRational` over `α = QFunNZG ℚ`, each
iterate step's *polynomial* cleared identity `B'f + Bg − C = D` lifted to the field equation on the `R/y ↦
(R/ρ)·y` coefficients. That lift is now a theorem via three `QFunNZG ℚ`-specific bridges, **all landed and
axiom-clean** (none of them `radDeriv`-arithmetic):

* (i) **`toQFunNZG_cderiv_qxOfNum`** — `cderiv (qxOfNum P) = qxOfNum (cderivG P)` read in `RatFunc ℚ`: the
  polynomial embedding `qxOfNum : CPolyG ℚ → QFunNZG ℚ` commutes with the derivation. The substantive
  bridge: `cderiv = towerDerivQFunNZG [1]` realizes `extendDeriv (implicitDeriv (toPolyG [1]))`, which on
  the algebra-map image `qxOfNum P ↦ amG (toPolyG P)` is `algebraMap (baseDerivQ (toPolyG P))`, and
  `baseDerivQ` is the plain `derivative` over `ℚ` (`baseDerivQ_apply`).
* (ii) **`toK_logDerRadicand_mul_radicand`** — `ℓ·f = (1/n)·f'` in `K` (`toK (logDerRadicand n f · f) =
  n⁻¹·toK f'`): the integrand-helper `g = (1/n)f'` IS the diagonal multiplier `ℓ = f'/(nf)` times the
  radicand `f`, rearranged from the crux `toK_logDerRadicand_mul`.
* (iii) **`radCase3Residual_eq`** — the per-step polynomial cleared identity `B'f + Bg − C` is definitional
  (`rfl`).

Composed: **`toK_step_qxOfNum_iff`** turns each step's cleared polynomial identity
`(n:K[X])·ρ̄·Bᵢ' + Bᵢ·ρ̄' = (n:K[X])·ρ̄·(Cᵢ − Cᵢ₊₁)` into the telescope's per-step `K`-equation (bridges (i)
+(ii) read the `toK`s through `amG`, `amG`-injectivity descends the cleared `RatFunc` equation), and
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
*off the engine's own polynomial `cisZeroG` check* through `cisZeroG_iff` + `toPolyG_csubG` (no `radDeriv`/
`RatFunc` reasoning). Composed: **`isRadicalRationalIntegral_c3itRun`** / **`radIsZero_radDeriv_c3itVlift`**
prove the literal `∫ x⁴/√(x³+1)` run `radDeriv 2 c3itRhoQx c3itVlift = c3itRatLift` — the engine's
`native_decide` fact `c3itDriver_integrates`, here a **theorem of the abstract derivation**
(`[propext, Classical.choice, Quot.sound]`, no `native_decide`).

**The one precondition that genuinely remains** is the run's whole-accumulator cleared identity itself, supplied
as the explicit hypothesis `hcheck : cisZeroG (2·ρ·vNum' − vNum·ρ' − 2·ρ·(C − Crem)) = true`. This is the
engine's *own* polynomial check over the named run's `vNum`/`Crem`, but it is **not** dischargeable abstractly:
the kernel cannot reduce `c3itRun` (the fuel recursion over `ℚ` — `decide`/`rfl` both get stuck on `ℚ`
arithmetic; only `native_decide`'s compiler evaluates it), so the run's output and its cleared check are
accessible *only* through the forbidden `native_decide`. Hence `radDeriv(radIntegrateRational g) = g` is now
self-contained **modulo exactly this one polynomial check** — the radical-derivation soundness fully reduced
to a single `cisZeroG`-shaped `ℚ[X]` identity over the run, the irreducible `native_decide`-only kernel
residue. -/

/-! ### `#print axioms` — the bridges and the literal soundness are abstractly verified (no `native_decide`)

Each soundness theorem and each of the three literal-radical bridges carries **only** the standard
`[propext, Classical.choice, Quot.sound]` (or, for the definitional bridge (iii), *no* axioms) — no
`native_decide` compiler axiom, no `sorry`. The simple-radical integral `∫ (f'/(nf))·√f = √f`, its two-term
generalization, the `C/y`-form reduction, the **telescoping invariant**, the **general rational-part
soundness** `radDeriv(assembled v) = integrand − final-leftover`, the three `QFunNZG ℚ` bridges
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
#print axioms toQFunNZG_cderiv_qxOfNum

-- ★ Bridge (ii): `g = ℓ·f` in `K` (the diagonal multiplier times the radicand is `(1/n)f'`):
#print axioms RadElem.toK_logDerRadicand_mul_radicand

-- ★ Bridge (iii): the per-step polynomial cleared identity `B'f + Bg − C` is definitional:
#print axioms CPolyG.radCase3Residual_eq

-- ★ The LITERAL per-step `K`-equation ⟺ cleared polynomial identity (i+ii+iii composed at one step):
#print axioms RadElem.toK_step_qxOfNum_iff

-- ★★ The LITERAL rational-part soundness over ℚ(x): `radDeriv(assembled qxOfNum-v) = integrand − leftover`:
#print axioms RadElem.radDeriv_foldlRadAdd_qxOfNum_telescope

-- ★ The concrete elliptic-radicand integral over ℚ(x), abstractly (the engine's native_decide fact):
#print axioms radDeriv_radGen_sound_qx
#print axioms radIsZero_radDeriv_radGen_qx

-- ★ The FRACTION-coefficient single-step iff (the named-run lift `[0, qxOfNum N / qxOfNum ρ]`):
#print axioms RadElem.isRadicalRationalIntegral_div_qxOfNum_iff

-- ★ Reading the engine's cleared `cisZeroG` check into the fraction-iff `K[X]` identity (n = 2):
#print axioms RadElem.clearedKX2_of_cisZeroG

-- ★ The NAMED driver run `c3itRun` (`∫ x⁴/√(x³+1)`) is sound, abstractly, from the engine's own check:
#print axioms isRadicalRationalIntegral_c3itRun
#print axioms radIsZero_radDeriv_c3itVlift

end DeepWiki.SymbolicIntegration
