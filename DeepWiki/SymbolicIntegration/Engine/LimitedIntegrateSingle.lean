import DeepWiki.SymbolicIntegration.Engine.Parametric
import DeepWiki.SymbolicIntegration.Engine.Tower.CarrierRec

/-! # Base single-`w` limited integration

Limited integration solves `a = D(b) + c·η` for a primitive generator derivative `η = Dt`, with
`b` in the polynomial base regime over `ℚ(x)`. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly Polynomial

namespace DensePoly

/-- **Base polynomial antiderivative over ℚ** `cAntiderivBaseQ p = ∫ p dt`: for `p = Σ aᵢ tⁱ`, returns
`Σ aᵢ/(i+1)·t^(i+1)` (constant of integration `0`). The `D = d/dt` inverse on `ℚ[t]`. -/
def cAntiderivBaseQ (p : DensePoly ℚ) : DensePoly ℚ :=
  (0 : ℚ) :: ((p : List ℚ).zipIdx.map (fun ai => ai.1 / (ai.2 + 1)))

/-- **Base single-`w` limited integration** `cLimitedIntegrateSingleBase a η` (Bronstein §5.8's
`LimitedIntegrate(a, Dt)`, `k = ℚ(x)`, polynomial-`b` regime): returns `some (b, c)` with `a = D(b) + c·η`
(`b ∈ ℚ[x] ⊂ ℚ(x)`, `c ∈ ℚ`), or `none` if no such pair exists in this regime. Builds the two-generator
constraint system `[a, η]` (`cLinearConstraintsQ`), takes the `c₀ ≠ 0` kernel vector (`cNullspaceBasisQ`),
normalizes `c₀ = 1`, and recovers `b` by antidifferentiating the cleared polynomial residual `q₀ + c₁·q₁`. -/
def cLimitedIntegrateSingleBase (a η : CFrac ℚ) : Option (CFrac ℚ × ℚ) :=
  let gnums := [a.num, η.num]
  let gdens := [a.den, η.den]
  let (qs, M) := cLinearConstraintsQ gnums gdens
  let kernel := cNullspaceBasisQ M 2
  match kernel.find? (fun v => v.getD 0 0 ≠ 0) with
  | none => none
  | some v =>
    let c0 := v.getD 0 0
    let c1 := (v.getD 1 0) / c0                                   -- normalized `c₁` (`c₀ = 1`)
    let integrand := cadd (qs.getD 0 []) (cscale c1 (qs.getD 1 []))
    let bpoly := cAntiderivBaseQ integrand
    some (CFrac.ofPoly bpoly, -c1)

/-- **`cLimitedIntegrateSingleBase` in the num/den signature** of `LawfulRischLevelLrt.limitedIntegrateSingle`
(`anum aden ηnum ηden ↦ ((bnum, bden), c)`) — the base ℚ instance's field for Phase 3-wire-2. Guards the
denominators nonzero (`CFrac` needs `cisZero den = false`), then wraps `cLimitedIntegrateSingleBase`. -/
def limitedIntegrateSingleBaseNumDen (anum aden ηnum ηden : DensePoly ℚ) :
    Option ((DensePoly ℚ × DensePoly ℚ) × ℚ) :=
  if hA : DensePoly.cisZero aden = false then
    if hη : DensePoly.cisZero ηden = false then
      (cLimitedIntegrateSingleBase (CFrac.ofFraction anum aden hA)
        (CFrac.ofFraction ηnum ηden hη)).map
        fun bc => ((bc.1.num, bc.1.den), bc.2)
    else none
  else none

/-- **Degree-raising primitive-polynomial integration** `cIntegratePrimPolyDegRaise η limInt fuel p`
(Bronstein `IntegratePrimitivePolynomial`, Thm 5.8.1): given the primitive derivation `Dt = η ∈ α`, a
single-`w` limited integrator `limInt : a ↦ (b, c)` with `a = D(b) + c·η` (`c` the constant embedded in `α`),
and `p ∈ α[t]`, returns `q` with `D_tower(q) = p` and `deg q ≤ deg p + 1`. Peels the leading term
`a·tᵐ`: `LimitedIntegrate(a, η) = (b, c)` gives `q₀ = c/(m+1)·t^(m+1) + b·tᵐ` (the **degree-raising** term),
whose derivative matches `a·tᵐ`, then recurses on `p − D_tower(q₀)` (degree `< m`). -/
def cIntegratePrimPolyDegRaise {α : Type*} [CField α] [CDiffField α]
    (η : α) (limInt : α → Option (α × α)) : ℕ → DensePoly α → Option (DensePoly α)
  | 0, p => if cisZero p then some [] else none
  | fuel + 1, p =>
    if cisZero p then some []
    else
      (limInt (clead p)).bind fun bc =>
        let q0 := cadd (cMonomial (CField.div bc.2 (cnatCast (cdeg p + 1))) (cdeg p + 1))
          (cMonomial bc.1 (cdeg p))
        (cIntegratePrimPolyDegRaise η limInt fuel (csub p (cmonomialDeriv [η] q0))).map fun qr =>
          cadd qr q0

/-- **Soundness of the degree-raising primitive-polynomial integrator** — `D_tower(q) = p`. Denotationally,
`implicitDeriv (C ⟦η⟧) (toPoly q) = toPoly p`. The identity **telescopes**: each step forms `q₀`, recurses on
`p − D_tower(q₀)`, and adds `q₀` back, so `D_tower(q) = D_tower(q_rec) + D_tower(q₀) = (p − D_tower(q₀)) +
D_tower(q₀) = p` — holding for **any** `limInt` (no correctness hypothesis on it), the same exact-subtraction
insight as the cancellation-case poly-RDE soundness. -/
theorem cIntegratePrimPolyDegRaiseG_sound {α : Type*} [CField α] [CFieldSpec α] [CDiffField α]
    [CDiffFieldSpec α] (η : α) (limInt : α → Option (α × α)) :
    ∀ (fuel : ℕ) (p q : DensePoly α), cIntegratePrimPolyDegRaise η limInt fuel p = some q →
      Differential.implicitDeriv (Polynomial.C (CFieldSpec.toK η)) (toPoly q) = toPoly p := by
  have hη : toPoly ([η] : DensePoly α) = Polynomial.C (CFieldSpec.toK η) := by
    simp only [denote, mul_zero, add_zero]
  intro fuel
  induction fuel with
  | zero =>
    intro p q h
    simp only [cIntegratePrimPolyDegRaise] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h; subst h
      rw [toPolyG_nil, map_zero, (cisZeroG_iff p).mp hc]
    · simp at h
  | succ fuel ih =>
    intro p q h
    simp only [cIntegratePrimPolyDegRaise] at h
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

end DensePoly

end DeepWiki.SymbolicIntegration
