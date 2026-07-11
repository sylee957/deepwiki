import DeepWiki.SymbolicIntegration.Engine.RischDE.SolveSoundWf

/-! # RDE decision-procedure completeness — `solvable ⟹ some`

The completeness direction of the RDE solver `crischDESolveSoundWf`: modulo the residual
`RischDECompletenessResidualWf`, `FieldRDESolvable f g ⟹ ∃ y, crischDESolveSoundWf f g = some y`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open DensePoly CFrac

universe u v

/-! ## The field-level RDE solvability predicate `FieldRDESolvable` -/

section Solvable

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β DensePoly]
  [Algebra ℚ (CFieldSpec.K β)]

/-- `FieldRDESolvable f g`: some `y : DenseFrac β` solves the field-level Risch DE `D(Y) + F·Y = G`
over `RatFunc (CFieldSpec.K β)`, read through `am ∘ toPoly`. -/
def FieldRDESolvable (f g : DenseFrac β) : Prop :=
  ∃ y : DenseFrac β,
    towerFractionFieldDeriv ([CCommRing.one] : DensePoly β)
          (am β (toPoly y.num) / am β (toPoly y.den))
        + am β (toPoly f.num) / am β (toPoly f.den)
          * (am β (toPoly y.num) / am β (toPoly y.den))
      = am β (toPoly g.num) / am β (toPoly g.den)

end Solvable

/-! ## Structural `some`/`none`-characterization -/

section StructuralWf

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β DensePoly]
  [CPolyGcd DensePoly β] [CPolySplitFactor DensePoly β] [CRischField β]

omit [CFieldSpec β] in
/-- `crischDESolveSoundWf f g = some y` iff the weak normalizer is nonzero, the canon-normality gate
passes on the weak-normalized input, and `crischDERawSolveWf` succeeds on the reduced pair (returned value
transformed back by `q⁻¹`). -/
theorem crischDESolveSoundWf_some_iff (f g y : DenseFrac β) :
    crischDESolveSoundWf f g = some y ↔
      (DensePoly.cisZero (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den)
          = false
        ∧ CFrac.canonNormalizedGate (weakNormalizedF f
            (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den)))
          = true
        ∧ ∃ ytilde : DenseFrac β,
            crischDERawSolveWf
                (CFrac.reduce (weakNormalizedF f
                  (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den))))
                (mul (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den)) g)
              = some ytilde
              ∧ y = mul ytilde (inv (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β)
                  f.num f.den)))) := by
  set q : DensePoly β := cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den with hq
  set q' : DenseFrac β := CFrac.ofPoly q with hq'
  set ftilde : DenseFrac β := weakNormalizedF f q' with hft
  rw [show crischDESolveSoundWf f g
      = (if DensePoly.cisZero q then none
         else if CFrac.canonNormalizedGate ftilde then
                match crischDERawSolveWf (CFrac.reduce ftilde) (mul q' g) with
                | none => none
                | some ytilde => some (mul ytilde (inv q'))
              else none) from rfl]
  by_cases hqz : DensePoly.cisZero q = true
  · rw [if_pos hqz]
    simp only [hqz, Bool.true_eq_false, false_and, iff_false]
    intro h; exact absurd h (by simp)
  · rw [if_neg hqz]
    rw [Bool.not_eq_true] at hqz
    by_cases hck : CFrac.canonNormalizedGate ftilde = true
    · rw [if_pos hck]
      rcases _hinner : crischDERawSolveWf (CFrac.reduce ftilde) (mul q' g) with _ | ytilde
      · simp only [hqz, hck, true_and]
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨yt, hyt, _⟩; exact absurd hyt (by simp)
      · simp only [hqz, hck, true_and, Option.some.injEq]
        constructor
        · intro h; exact ⟨ytilde, rfl, h.symm⟩
        · rintro ⟨yt, hyt, hy⟩; rw [hy, hyt]
    · rw [if_neg hck]
      rw [Bool.not_eq_true] at hck
      simp only [hck, Bool.false_eq_true, and_false, false_and, iff_false]
      intro h; exact absurd h (by simp)

omit [CFieldSpec β] in
/-- If the weak normalizer is nonzero, the canon-normality gate passes, and `crischDERawSolveWf` returns
`some ỹ`, then `crischDESolveSoundWf f g = some (ỹ/q')`. -/
theorem crischDESolveSoundWf_some_of_stages (f g ytilde : DenseFrac β)
    (hq : DensePoly.cisZero (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den)
        = false)
    (hck : CFrac.canonNormalizedGate (weakNormalizedF f
        (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den)))
        = true)
    (hinner : crischDERawSolveWf
        (CFrac.reduce (weakNormalizedF f
          (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den))))
        (mul (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den)) g)
        = some ytilde) :
    crischDESolveSoundWf f g
      = some (mul ytilde (inv (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β)
          f.num f.den)))) :=
  (crischDESolveSoundWf_some_iff f g _).mpr ⟨hq, hck, ytilde, hinner, rfl⟩

/-! ### Restatement against the intended wording (anonymous `example`) -/

example (f g ytilde : DenseFrac β)
    (hq : DensePoly.cisZero (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den)
        = false)
    (hck : CFrac.canonNormalizedGate (weakNormalizedF f
        (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den)))
        = true)
    (hinner : crischDERawSolveWf
        (CFrac.reduce (weakNormalizedF f
          (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den))))
        (mul (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den)) g)
        = some ytilde) :
    crischDESolveSoundWf f g
      = some (mul ytilde (inv (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β)
          f.num f.den)))) :=
  crischDESolveSoundWf_some_of_stages f g ytilde hq hck hinner

end StructuralWf

/-! ## Base-field completeness over the constants `ℚ` -/

section BaseField

/-- The constant-field RDE `b·y = g` (`D = 0`) is solvable in `ℚ` iff the base oracle returns `some` —
`(∃ y : ℚ, b·y = g) ↔ ∃ y, CRischField.crischDESolve b g = some y`. -/
theorem rischDE_complete_base (b g : ℚ) :
    (∃ y : ℚ, b * y = g) ↔ ∃ y, CRischField.crischDESolve b g = some y := by
  simp only [CRischField.crischDESolve]
  constructor
  · rintro ⟨y, hy⟩
    by_cases hb : b = 0
    · -- `b = 0` ⟹ `g = 0`, oracle is `some 0`
      have hg : g = 0 := by rw [← hy, hb, zero_mul]
      exact ⟨0, by rw [if_pos hb, if_pos hg]⟩
    · -- `b ≠ 0` ⟹ oracle is `some (g/b)`
      exact ⟨g / b, by rw [if_neg hb]⟩
  · rintro ⟨y, hy⟩
    by_cases hb : b = 0
    · -- `b = 0`: oracle `some` forces `g = 0`, then `b·0 = 0 = g`
      rw [if_pos hb] at hy
      by_cases hg : g = 0
      · exact ⟨0, by rw [hb, zero_mul, hg]⟩
      · rw [if_neg hg] at hy; exact absurd hy (by simp)
    · -- `b ≠ 0`: `y = g/b` solves `b·(g/b) = g`
      rw [if_neg hb, Option.some.injEq] at hy
      exact ⟨g / b, mul_div_cancel₀ g hb⟩

/-- A solvable constant-field RDE `b·y = g` makes the base oracle return `some` —
`(∃ y : ℚ, b·y = g) → ∃ y, CRischField.crischDESolve b g = some y`. -/
theorem rischDE_complete_base_some (b g : ℚ) (hsol : ∃ y : ℚ, b * y = g) :
    ∃ y, CRischField.crischDESolve b g = some y :=
  (rischDE_complete_base b g).mp hsol

end BaseField

/-! ## The `cRischDE`-level polynomial-solution predicates -/

section InnerSubResidual

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CRischField α]

/-- `IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden`: the cleared polynomial identity
`gden·fden·(D(ynum)·yden − ynum·D(yden)) + gden·fnum·ynum·yden = gnum·fden·yden²` over `(CFieldSpec.K α)[X]`
— `(ynum/yden)` solves the RDE for `(fnum/fden, gnum/gden)`. -/
def IsCRischDEGPolySol (Dt fnum fden gnum gden ynum yden : DensePoly α) : Prop :=
  toPoly gden * toPoly fden
      * (Differential.implicitDeriv (toPoly Dt) (toPoly ynum) * toPoly yden
          - toPoly ynum * Differential.implicitDeriv (toPoly Dt) (toPoly yden))
      + toPoly gden * toPoly fnum * toPoly ynum * toPoly yden
    = toPoly gnum * toPoly fden * toPoly yden ^ 2

/-- `IsReducedRdeSol Dt a b c q`: `q` solves the reduced linear ODE `a·D(q) + b·q = c` over
`(CFieldSpec.K α)[X]` (`D = implicitDeriv (toPoly Dt)`). -/
def IsReducedRdeSol (Dt a b c q : DensePoly α) : Prop :=
  toPoly a * Differential.implicitDeriv (toPoly Dt) (toPoly q) + toPoly b * toPoly q
    = toPoly c

end InnerSubResidual

/-! ## Inner sub-residual -/

section InnerSubResidualWf

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CPolyGcd DensePoly α] [CPolySplitFactor DensePoly α] [CRischField α]

/-- `RischDEInnerCompletenessWf Dt fnum fden gnum gden`: the inner-stage completeness sub-residuals —
`hnorm` (normal-denominator stage succeeds), `hbound` (degree-upper-bound), `hsolve` (inner solver succeeds)
on polynomial-solvable inputs. -/
structure RischDEInnerCompletenessWf (Dt fnum fden gnum gden : DensePoly α) : Prop where
  /-- A polynomial-solvable RDE's normal-denominator reduction succeeds. -/
  hnorm : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    (cRdeNormalDenominator Dt fnum fden gnum gden).isSome = true
  /-- Any reduced polynomial solution has degree at most `cRdeBoundDegree`. -/
  hbound : ∀ a0 b0 c0 h0 : DensePoly α,
    cRdeNormalDenominator Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
    ∀ q : DensePoly α,
      IsReducedRdeSol Dt (cRdeSpecialDenominator Dt a0 b0 c0).1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.1
          (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1 q →
      cdeg q ≤ cRdeBoundDegree Dt
        (cRdeSpecialDenominator Dt a0 b0 c0).1
        (cRdeSpecialDenominator Dt a0 b0 c0).2.1
        (cRdeSpecialDenominator Dt a0 b0 c0).2.2.1
  /-- A polynomial-solvable RDE makes the inner solver succeed. -/
  hsolve : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    (cRischDE Dt fnum fden gnum gden).isSome = true

/-- `RischDEInnerCompletenessWf` yields `cRischDE = some _` on a polynomial-solvable input. -/
theorem cRischDEG_isSome_of_innerCompletenessWf (Dt fnum fden gnum gden : DensePoly α)
    (hinner : RischDEInnerCompletenessWf Dt fnum fden gnum gden)
    (hsol : ∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) :
    (cRischDE Dt fnum fden gnum gden).isSome = true :=
  hinner.hsolve hsol

end InnerSubResidualWf

/-! ## Raw inner-solver bridge

Move the inner-completeness result across the `CFrac` denominator guard from `cRischDE` to the wrapper's
`crischDERawSolveWf`. -/

section RawInnerWf

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β DensePoly]
  [CPolyGcd DensePoly β] [CPolySplitFactor DensePoly β] [CRischField β]

omit [CFieldSpec β] [CDiffFieldSpec β] [CFieldDomain β DensePoly] in
/-- If `cRischDE [1]` succeeds and every returned denominator is nonzero, then `crischDERawSolveWf`
returns `some`. -/
theorem crischDERawSolveWf_isSome_of_cRischDEG_some_den (ftilde gtilde : DenseFrac β)
    (hsome : (cRischDE ([CCommRing.one] : DensePoly β) ftilde.num ftilde.den gtilde.num gtilde.den).isSome = true)
    (hden : ∀ ynum yden : DensePoly β,
      cRischDE ([CCommRing.one] : DensePoly β) ftilde.num ftilde.den gtilde.num gtilde.den = some (ynum, yden) →
      DensePoly.cisZero yden = false) :
    ∃ ytilde, crischDERawSolveWf ftilde gtilde = some ytilde := by
  obtain ⟨⟨ynum, yden⟩, hp⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨CFrac.ofFraction ynum yden (hden ynum yden hp), ?_⟩
  exact (crischDERawSolveWf_some_iff ftilde gtilde _).mpr
    ⟨ynum, yden, hden ynum yden hp, hp, rfl⟩

omit [CFieldSpec β] [CDiffFieldSpec β] [CFieldDomain β DensePoly] in
/-- Inner stage successes plus the returned-denominator guard imply `crischDERawSolveWf` succeeds. -/
theorem crischDERawSolveWf_isSome_of_cRischDEG_stages_den (ftilde gtilde : DenseFrac β)
    (a0 b0 c0 h0 bbar cbar : DensePoly β) (m : ℤ) (α' β' v : DensePoly β)
    (hnorm : cRdeNormalDenominator ([CCommRing.one] : DensePoly β)
      ftilde.num ftilde.den gtilde.num gtilde.den = some (a0, b0, c0, h0))
    (hspde : cSPDE ([CCommRing.one] : DensePoly β) (cRdeSpecialDenominator ([CCommRing.one] : DensePoly β)
        a0 b0 c0).1
        (cRdeSpecialDenominator ([CCommRing.one] : DensePoly β) a0 b0 c0).2.1
        (cRdeSpecialDenominator ([CCommRing.one] : DensePoly β) a0 b0 c0).2.2.1
        (cRdeBoundDegree ([CCommRing.one] : DensePoly β) (cRdeSpecialDenominator ([CCommRing.one] : DensePoly β)
          a0 b0 c0).1
          (cRdeSpecialDenominator ([CCommRing.one] : DensePoly β) a0 b0 c0).2.1
          (cRdeSpecialDenominator ([CCommRing.one] : DensePoly β) a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β'))
    (hpoly : cPolyRischDE ([CCommRing.one] : DensePoly β) bbar cbar m = some v)
    (hden : ∀ ynum yden : DensePoly β,
      cRischDE ([CCommRing.one] : DensePoly β) ftilde.num ftilde.den gtilde.num gtilde.den = some (ynum, yden) →
      DensePoly.cisZero yden = false) :
    ∃ ytilde, crischDERawSolveWf ftilde gtilde = some ytilde := by
  have hsome : (cRischDE ([CCommRing.one] : DensePoly β)
      ftilde.num ftilde.den gtilde.num gtilde.den).isSome = true := by
    rw [cRischDE, hnorm]
    simp only [hspde, hpoly, Option.isSome_some]
  exact crischDERawSolveWf_isSome_of_cRischDEG_some_den ftilde gtilde hsome hden

omit [CFieldDomain β DensePoly] in
/-- An inner-completeness residual, a polynomial solution, and the denominator guard imply
`crischDERawSolveWf` succeeds. -/
theorem crischDERawSolveWf_isSome_of_innerCompletenessWf (ftilde gtilde : DenseFrac β)
    (hinner : RischDEInnerCompletenessWf ([CCommRing.one] : DensePoly β)
      ftilde.num ftilde.den gtilde.num gtilde.den)
    (hsol : ∃ ynum yden,
      IsCRischDEGPolySol ([CCommRing.one] : DensePoly β) ftilde.num ftilde.den gtilde.num gtilde.den ynum yden)
    (hden : ∀ ynum yden : DensePoly β,
      cRischDE ([CCommRing.one] : DensePoly β) ftilde.num ftilde.den gtilde.num gtilde.den = some (ynum, yden) →
      DensePoly.cisZero yden = false) :
    ∃ ytilde, crischDERawSolveWf ftilde gtilde = some ytilde :=
  crischDERawSolveWf_isSome_of_cRischDEG_some_den ftilde gtilde
    (cRischDEG_isSome_of_innerCompletenessWf ([CCommRing.one] : DensePoly β)
      ftilde.num ftilde.den gtilde.num gtilde.den hinner hsol)
    hden

/-! ### Restatement against the intended wording (anonymous `example`) -/

example (ftilde gtilde : DenseFrac β)
    (hinner : RischDEInnerCompletenessWf ([CCommRing.one] : DensePoly β)
      ftilde.num ftilde.den gtilde.num gtilde.den)
    (hsol : ∃ ynum yden,
      IsCRischDEGPolySol ([CCommRing.one] : DensePoly β) ftilde.num ftilde.den gtilde.num gtilde.den ynum yden)
    (hden : ∀ ynum yden : DensePoly β,
      cRischDE ([CCommRing.one] : DensePoly β) ftilde.num ftilde.den gtilde.num gtilde.den = some (ynum, yden) →
      DensePoly.cisZero yden = false) :
    ∃ ytilde, crischDERawSolveWf ftilde gtilde = some ytilde :=
  crischDERawSolveWf_isSome_of_innerCompletenessWf ftilde gtilde hinner hsol hden

end RawInnerWf

/-! ## Completeness wrapper -/

section CompleteWf

variable {β : Type u} [CField β] [CFieldSpec.{u,v} β] [CDiffField β] [CDiffFieldSpec β]
  [CFieldDomain β DensePoly]
  [CPolyGcd DensePoly β] [CPolySplitFactor DensePoly β]
  [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

/-- A successful `crischDESolveSoundWf` run (with soundness certificate `RischDESoundnessWf`) witnesses
`FieldRDESolvable`. -/
theorem crischDESolveSoundWf_imp_solvable (f g y : DenseFrac β)
    (hsolve : crischDESolveSoundWf f g = some y)
    (hsound : RischDESoundnessWf f g) :
    FieldRDESolvable f g :=
  ⟨y, crischDESolveSoundWf_field f g y hsolve hsound⟩

/-! ### Completeness residual -/

/-- `RischDECompletenessResidualWf f g`: the three stage-completeness facts consumed by
`crischDESolveSoundWf_some_of_stages` — nonzero weak normalizer (`hwn`), canonical-normality (`hck`),
inner solver success (`hinner`) on a solvable RDE. -/
structure RischDECompletenessResidualWf (f g : DenseFrac β) : Prop where
  /-- A solvable RDE has a nonzero weak normalizer. -/
  hwn : FieldRDESolvable f g →
    DensePoly.cisZero (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den) = false
  /-- A solvable RDE satisfies the canonical-normality guarantee. -/
  hck : FieldRDESolvable f g →
    IsCanonNormalized f
      (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den))
  /-- A solvable RDE makes the inner solve succeed on the reduced pair. -/
  hinner : FieldRDESolvable f g →
    ∃ ytilde : DenseFrac β,
      crischDERawSolveWf
          (CFrac.reduce (weakNormalizedF f
            (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den))))
          (mul (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den)) g)
        = some ytilde

/-- If the RDE is solvable and `RischDECompletenessResidualWf` holds, then `crischDESolveSoundWf`
returns `some`. -/
theorem crischDESolveSoundWf_complete_of_residualWf (f g : DenseFrac β)
    [LawfulCPolyGcd.{u,v} DensePoly β]
    (hsol : FieldRDESolvable f g) (hres : RischDECompletenessResidualWf f g) :
    ∃ y, crischDESolveSoundWf f g = some y := by
  obtain ⟨ytilde, hinner⟩ := hres.hinner hsol
  have hck : CFrac.canonNormalizedGate (weakNormalizedF f
      (CFrac.ofPoly (cWeakNormalizer ([CCommRing.one] : DensePoly β) f.num f.den))) = true :=
    (canonNormalizedGate_iff f _).mpr (hres.hck hsol)
  exact ⟨_, crischDESolveSoundWf_some_of_stages f g ytilde (hres.hwn hsol) hck hinner⟩

/-- Modulo `RischDECompletenessResidualWf` and `RischDESoundnessWf`, `crischDESolveSoundWf f g` returns
`some` iff the field-level RDE is solvable. -/
theorem crischDESolveSoundWf_decides_of_residualWf (f g : DenseFrac β)
    [LawfulCPolyGcd.{u,v} DensePoly β]
    (hres : RischDECompletenessResidualWf f g)
    (hsound : RischDESoundnessWf f g) :
    (∃ y, crischDESolveSoundWf f g = some y) ↔ FieldRDESolvable f g := by
  constructor
  · rintro ⟨y, hy⟩
    exact crischDESolveSoundWf_imp_solvable f g y hy hsound
  · intro hsol
    exact crischDESolveSoundWf_complete_of_residualWf f g hsol hres

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- The Wf-native residual gives the same decision statement with a fuel-free completeness direction.
example (f g : DenseFrac β) [LawfulCPolyGcd.{u,v} DensePoly β]
    (hres : RischDECompletenessResidualWf f g)
    (hsound : RischDESoundnessWf f g) :
    (∃ y, crischDESolveSoundWf f g = some y) ↔ FieldRDESolvable f g :=
  crischDESolveSoundWf_decides_of_residualWf f g hres hsound

end CompleteWf

/-! ### Axiom audit -/

#print axioms crischDESolveSoundWf_some_iff
#print axioms crischDESolveSoundWf_some_of_stages
#print axioms rischDE_complete_base
#print axioms crischDERawSolveWf_isSome_of_cRischDEG_stages_den
#print axioms crischDESolveSoundWf_complete_of_residualWf
#print axioms crischDESolveSoundWf_decides_of_residualWf

end DeepWiki.SymbolicIntegration
