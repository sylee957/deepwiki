import DeepWiki.SymbolicIntegration.Engine.Parametric
import DeepWiki.SymbolicIntegration.Engine.Tower.CarrierRec

/-! # Base single-`w` limited integration

Limited integration solves `a = D(b) + c·η` for a primitive generator derivative `η = Dt`, with
`b` in the polynomial base regime over `ℚ(x)`. -/

namespace DeepWiki.SymbolicIntegration

open CPolyG Polynomial

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

/-- **`cLimitedIntegrateSingleBase` in the num/den signature** of `LawfulRischLevelLrt.limitedIntegrateSingle`
(`anum aden ηnum ηden ↦ ((bnum, bden), c)`) — the base ℚ instance's field for Phase 3-wire-2. Guards the
denominators nonzero (`QFunNZG` needs `cisZeroG den = false`), then wraps `cLimitedIntegrateSingleBase`. -/
def limitedIntegrateSingleBaseNumDen (anum aden ηnum ηden : CPolyG ℚ) :
    Option ((CPolyG ℚ × CPolyG ℚ) × ℚ) :=
  if hA : CPolyG.cisZeroG aden = false then
    if hη : CPolyG.cisZeroG ηden = false then
      (cLimitedIntegrateSingleBase ⟨(anum, aden), hA⟩ ⟨(ηnum, ηden), hη⟩).map
        fun bc => ((bc.1.1.1, bc.1.1.2), bc.2)
    else none
  else none

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
    simp only [denote, mul_zero, add_zero]
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
      simp only [denote, map_add, ih _ _ hrec, hη]
      ring

end CPolyG

end DeepWiki.SymbolicIntegration
