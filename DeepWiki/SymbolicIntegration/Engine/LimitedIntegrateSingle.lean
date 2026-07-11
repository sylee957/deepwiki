import DeepWiki.SymbolicIntegration.Engine.Parametric
import DeepWiki.SymbolicIntegration.Engine.Tower.CarrierRec
import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv
import DeepWiki.ComputableAlgebra.PolyAntiderivative

/-! # Base single-`w` limited integration

Limited integration solves `a = D(b) + c·η` for a primitive generator derivative `η = Dt`, with
`b` in the polynomial base regime over `ℚ(x)`. -/

namespace DeepWiki.SymbolicIntegration

open DensePoly Polynomial

universe u v

namespace CFrac

/-- **Base single-`w` limited integration** `limitedIntegrateSingleBase a η` (Bronstein §5.8's
`LimitedIntegrate(a, Dt)`, `k = ℚ(x)`, polynomial-`b` regime): returns `some (b, c)` with `a = D(b) + c·η`
(`b ∈ ℚ[x] ⊂ ℚ(x)`, `c ∈ ℚ`), or `none` if no such pair exists in this regime. Builds the two-generator
constraint system `[a, η]` (`CPoly.linearConstraintsQ`), takes a selected `c₀ ≠ 0` kernel vector,
normalizes `c₀ = 1`, and recovers `b` by antidifferentiating the cleared polynomial residual `q₀ + c₁·q₁`. -/
def limitedIntegrateSingleBase
    {F : (α : Type) → [CField α] → Type} {P : Type → Type}
    [CPoly P] [CPolyEngine P] [CPolyGcd P ℚ] [CPolyEuclidean P]
    [CFrac F P] [LawfulCFrac F P] [CFieldDomain ℚ P] [CLinearSolve ℚ]
    (a η : F ℚ) : Option (F ℚ × ℚ) :=
  let gnums := [CFrac.num a, CFrac.num η]
  let gdens := [CFrac.den a, CFrac.den η]
  let (qs, M) := CPoly.linearConstraintsQ gnums gdens
  let kernel := CLinearSolve.nullspaceBasis M 2
  match kernel.find? (fun v => v.getD 0 0 ≠ 0) with
  | none => none
  | some v =>
    let c0 := v.getD 0 0
    let c1 := (v.getD 1 0) / c0                                   -- normalized `c₁` (`c₀ = 1`)
    let integrand := CPolyEngine.add (qs.getD 0 CPoly.czero)
      (CPolyEngine.scale c1 (qs.getD 1 CPoly.czero))
    let bpoly := CPoly.antiderivative integrand
    some (CFrac.ofPoly bpoly, -c1)

end CFrac

/-! ### Representation-independence validation -/

/-- The base limited integrator runs unchanged on certified sparse fractions. -/
example :
    let ofList : List ℚ → CPoly.SparsePoly ℚ := CPolyEngine.ofCoeffList
    let a : SparseFrac ℚ := CFrac.ofFraction (ofList [1, 1]) (ofList [0, 1]) (by cfrac_nonzero)
    let η : SparseFrac ℚ := CFrac.ofFraction (ofList [1]) (ofList [0, 1]) (by cfrac_nonzero)
    (match CFrac.limitedIntegrateSingleBase (F := SparseFrac) (P := CPoly.SparsePoly) a η with
      | some (b, c) =>
          CPoly.coeff (CFrac.num b) 0 == 0 && CPoly.coeff (CFrac.num b) 1 == 1 &&
            CPoly.coeff (CFrac.den b) 0 == 1 && c == 1
      | none => false) = true := by
  ccompute

namespace DensePoly

/-- **`CFrac.limitedIntegrateSingleBase` in the num/den signature** of
`CRischLevelLrt.limitedIntegrateSingle`
(`anum aden ηnum ηden ↦ ((bnum, bden), c)`) — the base ℚ instance's field for Phase 3-wire-2. Guards the
denominators nonzero (`CFrac` needs `cisZero den = false`), then wraps the generic integrator. -/
def limitedIntegrateSingleBaseNumDen (anum aden ηnum ηden : DensePoly ℚ) :
    Option ((DensePoly ℚ × DensePoly ℚ) × ℚ) :=
  if hA : DensePoly.cisZero aden = false then
    if hη : DensePoly.cisZero ηden = false then
      (CFrac.limitedIntegrateSingleBase (F := DenseFrac) (P := DensePoly)
        (CFrac.ofFraction anum aden hA)
        (CFrac.ofFraction ηnum ηden hη)).map
        fun bc => ((CFrac.num bc.1, CFrac.den bc.1), bc.2)
    else none
  else none

/-- **Degree-raising primitive-polynomial integration** `cIntegratePrimPolyDegRaise η limInt fuel p`
(Bronstein `IntegratePrimitivePolynomial`, Thm 5.8.1): given the primitive derivation `Dt = η ∈ α`, a
single-`w` limited integrator `limInt : a ↦ (b, c)` with `a = D(b) + c·η` (`c` the constant embedded in `α`),
and `p ∈ α[t]`, returns `q` with `D_tower(q) = p` and `deg q ≤ deg p + 1`. Peels the leading term
`a·tᵐ`: `LimitedIntegrate(a, η) = (b, c)` gives `q₀ = c/(m+1)·t^(m+1) + b·tᵐ` (the **degree-raising** term),
whose derivative matches `a·tᵐ`, then recurses on `p − D_tower(q₀)` (degree `< m`). -/
def cIntegratePrimPolyDegRaise {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CDiffField α]
    (η : α) (limInt : α → Option (α × α)) : ℕ → P α → Option (P α)
  | 0, p => if CPolyEngine.cisZero p then some CPoly.czero else none
  | fuel + 1, p =>
    if CPolyEngine.cisZero p then some CPoly.czero
    else
      (limInt (CPolyEngine.clead p)).bind fun bc =>
        let q0 := CPolyEngine.add
          (CPolyEngine.monomial (P := P)
            (CField.div bc.2 (CField.natCast (CPolyEngine.cdeg p + 1))) (CPolyEngine.cdeg p + 1))
          (CPolyEngine.monomial (P := P) bc.1 (CPolyEngine.cdeg p))
        (cIntegratePrimPolyDegRaise η limInt fuel
          (CPolyEngine.sub p
            (CPolyEngine.monomialDeriv (CPolyEngine.monomial (P := P) η 0) q0))).map fun qr =>
          CPolyEngine.add qr q0

/-- **Soundness of the degree-raising primitive-polynomial integrator** — `D_tower(q) = p`. Denotationally,
`implicitDeriv (C ⟦η⟧) (toPoly q) = toPoly p`. The identity **telescopes**: each step forms `q₀`, recurses on
`p − D_tower(q₀)`, and adds `q₀` back, so `D_tower(q) = D_tower(q_rec) + D_tower(q₀) = (p − D_tower(q₀)) +
D_tower(q₀) = p` — holding for **any** `limInt` (no correctness hypothesis on it), the same exact-subtraction
insight as the cancellation-case poly-RDE soundness. -/
theorem cIntegratePrimPolyDegRaiseG_sound {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    [LawfulCPolyEngine.{u,v} P] {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CDiffField α]
    [CDiffFieldSpec.{u,v} α] (η : α) (limInt : α → Option (α × α)) :
    ∀ (fuel : ℕ) (p q : P α), cIntegratePrimPolyDegRaise η limInt fuel p = some q →
      Differential.implicitDeriv (Polynomial.C (CFieldSpec.toK η)) (CPoly.toPoly q) =
        CPoly.toPoly p := by
  have hη : CPoly.toPoly (CPolyEngine.monomial (P := P) η 0) =
      Polynomial.C (CFieldSpec.toK η) := by
    rw [LawfulCPolyEngine.toPoly_monomial (P := P)]
    simp only [toR_eq_toK, pow_zero, mul_one]
  intro fuel
  induction fuel with
  | zero =>
    intro p q h
    simp only [cIntegratePrimPolyDegRaise] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst q
      rw [CPoly.toPoly_czero, map_zero,
        (LawfulCPolyEngine.cisZero_iff (P := P) p).mp hc]
    · simp at h
  | succ fuel ih =>
    intro p q h
    simp only [cIntegratePrimPolyDegRaise] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst q
      rw [CPoly.toPoly_czero, map_zero,
        (LawfulCPolyEngine.cisZero_iff (P := P) p).mp hc]
    · rw [Option.bind_eq_some_iff] at h
      obtain ⟨⟨b, c⟩, _hlim, hmap⟩ := h
      rw [Option.map_eq_some_iff] at hmap
      obtain ⟨qr, hrec, rfl⟩ := hmap
      rw [LawfulCPolyEngine.toPoly_add (P := P), map_add, ih _ _ hrec,
        CPolyEngine.toPoly_sub (P := P), CPolyEngine.toPoly_monomialDeriv (P := P), hη]
      ring

/-! ### Representation-independence validation -/

/-- The degree-raising primitive-polynomial recursion executes unchanged on sparse polynomials. -/
example :
    (match cIntegratePrimPolyDegRaise (P := CPoly.SparsePoly) (1 : ℚ)
        (fun a => some ((0 : ℚ), a)) 3 (CPoly.SparsePoly.ofList [(0, 1), (1, 2)]) with
      | some q =>
          CPolyEngine.cisZero
              (CPolyEngine.sub
                (CPolyEngine.monomialDeriv
                  (CPolyEngine.monomial (P := CPoly.SparsePoly) (1 : ℚ) 0) q)
                (CPoly.SparsePoly.ofList [(0, 1), (1, 2)]))
            && decide (CPolyEngine.cdeg q = 2)
      | none => false) = true := by
  ccompute

end DensePoly

end DeepWiki.SymbolicIntegration
