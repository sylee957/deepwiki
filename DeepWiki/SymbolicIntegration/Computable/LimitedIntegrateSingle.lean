import DeepWiki.SymbolicIntegration.Computable.Parametric
import DeepWiki.SymbolicIntegration.Computable.Tower.CarrierRec

/-! # Base single-`w` limited integration (Phase 1 of `docs/tower-limited-integration.md`)

The operation the recursive primitive-polynomial case needs but currently lacks: **`LimitedIntegrate(a, η)`**
(Bronstein §5.8/§5.12) — find `b ∈ k` and a constant `c` with

```
a = D(b) + c·η
```

for a **raw** generator `η = Dt` (the primitive's derivative — the `c·t` degree-raiser), over the base field
`k = ℚ(x)`. This is `cParamRischDE`'s two-generator kernel `{(c₀,c₁) : c₀·a + c₁·η = Dp}`: take the `c₀ ≠ 0`
vector, normalize `c₀ = 1` (so `a = Dp + (−c₁)·η`), and recover `b = p` by integrating the (polynomial) cleared
residual. Scope = the **polynomial-`b`** regime (matches `cParamRischDE`); rational `b` (a Hermite pre-pass) is
Phase 1b. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG Polynomial

namespace CPolyG

/-- **Base polynomial antiderivative over ℚ** `cAntiderivBaseQ p = ∫ p dt`: for `p = Σ aᵢ tⁱ`, returns
`Σ aᵢ/(i+1)·t^(i+1)` (constant of integration `0`). The `D = d/dt` inverse on `ℚ[t]`. -/
def cAntiderivBaseQ (p : CPolyG ℚ) : CPolyG ℚ :=
  (0 : ℚ) :: ((p : List ℚ).zipIdx.map (fun ai => ai.1 / (ai.2 + 1)))

/-- **Base single-`w` limited integration** `cLimitedIntegrateSingleBase a η` (Bronstein §5.8's
`LimitedIntegrate(a, Dt)`, `k = ℚ(x)`, polynomial-`b` regime): returns `some (b, c)` with `a = D(b) + c·η`
(`b ∈ ℚ[x] ⊂ ℚ(x)`, `c ∈ ℚ`), or `none` if no such pair exists in this regime. Builds the two-generator
constraint system `[a, η]` (`cLinearConstraintsQ`), takes the `c₀ ≠ 0` kernel vector (`cNullspaceBasisQ`),
normalizes `c₀ = 1`, and recovers `b` by antidifferentiating the cleared polynomial residual `q₀ + c₁·q₁`. -/
def cLimitedIntegrateSingleBase (a η : QFunNZG ℚ) : Option (QFunNZG ℚ × ℚ) :=
  let gnums := [a.1.1, η.1.1]
  let gdens := [a.1.2, η.1.2]
  let (qs, M) := cLinearConstraintsQ gnums gdens
  let kernel := cNullspaceBasisQ M 2
  match kernel.find? (fun v => v.getD 0 0 ≠ 0) with
  | none => none
  | some v =>
    let c0 := v.getD 0 0
    let c1 := (v.getD 1 0) / c0                                   -- normalized `c₁` (`c₀ = 1`)
    let integrand := caddG (qs.getD 0 []) (cscaleG c1 (qs.getD 1 []))
    let bpoly := cAntiderivBaseQ integrand
    some (⟨(bpoly, [(1 : ℚ)]), QFunNZG.cisZeroG_one_singleton⟩, -c1)

/-- `c · tⁿ` as a `CPolyG α` (`n` zeros then `c`). -/
def cMonomialG {α : Type*} [CField α] (c : α) (n : ℕ) : CPolyG α :=
  (List.replicate n (CField.zero) ++ [c] : List α)

/-- **Degree-raising primitive-polynomial integration** `cIntegratePrimPolyDegRaiseG η limInt fuel p`
(Bronstein `IntegratePrimitivePolynomial`, Thm 5.8.1): given the primitive derivation `Dt = η ∈ α`, a
single-`w` limited integrator `limInt : a ↦ (b, c)` with `a = D(b) + c·η` (`c` the constant embedded in `α`),
and `p ∈ α[t]`, returns `q` with `D_tower(q) = p` and `deg q ≤ deg p + 1`. Peels the leading term
`a·tᵐ`: `LimitedIntegrate(a, η) = (b, c)` gives `q₀ = c/(m+1)·t^(m+1) + b·tᵐ` (the **degree-raising** term),
whose derivative matches `a·tᵐ`, then recurses on `p − D_tower(q₀)` (degree `< m`). -/
def cIntegratePrimPolyDegRaiseG {α : Type*} [CField α] [CDiffField α]
    (η : α) (limInt : α → Option (α × α)) : ℕ → CPolyG α → Option (CPolyG α)
  | 0, p => if cisZeroG p then some [] else none
  | fuel + 1, p =>
    if cisZeroG p then some []
    else
      (limInt (cleadG p)).bind fun bc =>
        let q0 := caddG (cMonomialG (CField.div bc.2 (cnatCastG (cdegG p + 1))) (cdegG p + 1))
          (cMonomialG bc.1 (cdegG p))
        (cIntegratePrimPolyDegRaiseG η limInt fuel (csubG p (cmonomialDeriv [η] q0))).map fun qr =>
          caddG qr q0

/-- **Soundness of the degree-raising primitive-polynomial integrator** — `D_tower(q) = p`. Denotationally,
`implicitDeriv (C ⟦η⟧) (toPolyG q) = toPolyG p`. The identity **telescopes**: each step forms `q₀`, recurses on
`p − D_tower(q₀)`, and adds `q₀` back, so `D_tower(q) = D_tower(q_rec) + D_tower(q₀) = (p − D_tower(q₀)) +
D_tower(q₀) = p` — holding for **any** `limInt` (no correctness hypothesis on it), the same exact-subtraction
insight as the cancellation-case poly-RDE soundness. -/
theorem cIntegratePrimPolyDegRaiseG_sound {α : Type*} [CField α] [CFieldSpec α] [CDiffField α]
    [CDiffFieldSpec α] (η : α) (limInt : α → Option (α × α)) :
    ∀ (fuel : ℕ) (p q : CPolyG α), cIntegratePrimPolyDegRaiseG η limInt fuel p = some q →
      Differential.implicitDeriv (Polynomial.C (CFieldSpec.toK η)) (toPolyG q) = toPolyG p := by
  have hη : toPolyG ([η] : CPolyG α) = Polynomial.C (CFieldSpec.toK η) := by
    rw [toPolyG_cons, toPolyG_nil, mul_zero, add_zero]
  intro fuel
  induction fuel with
  | zero =>
    intro p q h
    simp only [cIntegratePrimPolyDegRaiseG] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h; subst h
      rw [toPolyG_nil, map_zero, (cisZeroG_iff p).mp hc]
    · simp at h
  | succ fuel ih =>
    intro p q h
    simp only [cIntegratePrimPolyDegRaiseG] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h; subst h
      rw [toPolyG_nil, map_zero, (cisZeroG_iff p).mp hc]
    · rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨b, c⟩, _hlim, hmap⟩ := h
      rw [Option.map_eq_some_iff] at hmap
      obtain ⟨qr, hrec, rfl⟩ := hmap
      rw [toPolyG_caddG, map_add, ih _ _ hrec, toPolyG_csubG, toPolyG_cmonomialDeriv, hη]
      ring

end CPolyG

/-! ### Validation — the degree-raising example

`a = 1 + 1/x`, `η = 1/x` (so `t` is the primitive with `Dt = 1/x`, i.e. `t = log x`): the antiderivative
`∫(1 + 1/x) dx = x + log x = x + t`, i.e. `a = D(x) + 1·η`. So `LimitedIntegrate(a, η) = (x, 1)` — the constant
`c = 1` is exactly the degree-raiser the current log-free discharge cannot produce. -/

open CPolyG

/-- `a = 1 + 1/x = (x+1)/x ∈ ℚ(x)`. -/
def limIntSingleExampleA : QFunNZG ℚ := ⟨([1, 1], [0, 1]), by decide⟩
/-- `η = 1/x ∈ ℚ(x)` (the primitive derivative `Dt = 1/x`). -/
def limIntSingleExampleEta : QFunNZG ℚ := ⟨([1], [0, 1]), by decide⟩

-- **Sanity print.** `cLimitedIntegrateSingleBase (1+1/x) (1/x)` should give `(b, c)` with `b = x`, `c = 1`.
#eval (cLimitedIntegrateSingleBase limIntSingleExampleA limIntSingleExampleEta).map
  (fun bc => (CPolyG.qnormPairG bc.1.1.1 bc.1.1.2, bc.2))

/-- **The base single-`w` limited integration finds the degree-raising constant.** For `a = 1 + 1/x`,
`η = 1/x`, `cLimitedIntegrateSingleBase` returns `(b, c)` satisfying the defining identity `a = D(b) + c·η`
(with `D` the base derivation on `ℚ(x)`), i.e. `a − D(b) − c·η = 0`. The witness has `c = 1` (nonzero — the
degree-raiser). -/
theorem cLimitedIntegrateSingleBase_example :
    (match cLimitedIntegrateSingleBase limIntSingleExampleA limIntSingleExampleEta with
      | some (b, c) =>
          CField.isZero (CField.sub limIntSingleExampleA
            (CField.add (CDiffField.cderiv b)
              (CField.mul (CPolyG.qConstParamG c) limIntSingleExampleEta)))
            && decide (c ≠ 0)
      | none => false) = true := by native_decide

/-! ### 2-level end-to-end — the degree-raising primitive polynomial integral

`k = ℚ(x)(t)`, `Dt = 1/x` (`t = log x`). Integrate `p = (1 + 1/x)·t + 1 ∈ ℚ(x)[t]`. The leading coefficient
`1 + 1/x` has `LimitedIntegrate(1+1/x, 1/x) = (x, 1)` with `c = 1 ≠ 0`, so the antiderivative gains a degree:
`∫p = t²/2 + x·t = (log x)²/2 + x·log x`. This is exactly the case the current log-free coefficient discharge
declines. -/

/-- The base single-`w` limited integrator wrapped to `α × α` (embedding the constant `c ∈ ℚ` as `qConstParamG c`),
the `intR` the degree-raising recursion consumes at the base level. -/
def limIntBaseWrap (η a : QFunNZG ℚ) : Option (QFunNZG ℚ × QFunNZG ℚ) :=
  (cLimitedIntegrateSingleBase a η).map (fun bc => (bc.1, CPolyG.qConstParamG bc.2))

/-- `p = 1 + (1 + 1/x)·t ∈ ℚ(x)[t]`. -/
def prim2ExampleP : CPolyG (QFunNZG ℚ) := [qConstParamG 1, limIntSingleExampleA]

-- **Sanity print.** `∫p` should be `[0, x, 1/2]` = `x·t + (1/2)·t²` = `x·log x + (log x)²/2`.
#eval (cIntegratePrimPolyDegRaiseG limIntSingleExampleEta (limIntBaseWrap limIntSingleExampleEta) 3
    prim2ExampleP).map (fun q => q.map (fun c => CPolyG.qnormPairG c.1.1 c.1.2))

/-- **The degree-raising primitive-polynomial integrator is correct on the 2-level example.** With the Phase-1
base `LimitedIntegrate` as `intR`, `cIntegratePrimPolyDegRaiseG` computes `q` with `D_tower(q) = p` for
`p = (1+1/x)·t + 1` over `ℚ(x)(t)` (`Dt = 1/x`), and the antiderivative has **degree 2 = deg p + 1** — the
degree-raising the log-free discharge cannot produce. -/
theorem cIntegratePrimPolyDegRaiseG_example :
    (match cIntegratePrimPolyDegRaiseG limIntSingleExampleEta (limIntBaseWrap limIntSingleExampleEta) 3
        prim2ExampleP with
      | some q =>
          cisZeroG (csubG (cmonomialDeriv [limIntSingleExampleEta] q) prim2ExampleP)
            && decide (cdegG q = 2)
      | none => false) = true := by native_decide

end DeepWiki.SymbolicIntegration
