import DeepWiki.SymbolicIntegration.Engine.RischDE.SolveSoundWf

/-! # RDE decision-procedure completeness — `solvable ⟹ some`

The completeness direction of the RDE solver `crischDESolveSoundWf`: modulo the residual
`RischDECompletenessResidualWf`, `FieldRDESolvable f g ⟹ ∃ y, crischDESolveSoundWf f g = some y`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open CPoly QFunNZG

/-! ## The field-level RDE solvability predicate `FieldRDESolvable` -/

section Solvable

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [Algebra ℚ (CFieldSpec.K β)]

/-- `FieldRDESolvable f g`: some `y : QFunNZG β` solves the field-level Risch DE `D(Y) + F·Y = G`
over `RatFunc (CFieldSpec.K β)`, read through `amG ∘ toPolyG`. -/
def FieldRDESolvable (f g : QFunNZG β) : Prop :=
  ∃ y : QFunNZG β,
    towerFractionFieldDerivG ([CField.one] : CPoly β)
          (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
        + amG β (toPolyG f.1.1) / amG β (toPolyG f.1.2)
          * (amG β (toPolyG y.1.1) / amG β (toPolyG y.1.2))
      = amG β (toPolyG g.1.1) / amG β (toPolyG g.1.2)

end Solvable

/-! ## Structural `some`/`none`-characterization -/

section StructuralWf

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CFieldDomain β]
  [CFracGcdCoreWf β] [CRischField β]

/-- `crischDESolveSoundWf f g = some y` iff the weak normalizer is nonzero, the canon-normality gate
passes on the weak-normalized input, and `crischDERawSolveWf` succeeds on the reduced pair (returned value
transformed back by `q⁻¹`). -/
theorem crischDESolveSoundWf_some_iff (f g y : QFunNZG β) :
    crischDESolveSoundWf f g = some y ↔
      (CPoly.cisZeroG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2)
          = false
        ∧ cisCanonNormalizedG (weakNormalizedF f
            (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2)))
          = true
        ∧ ∃ ytilde : QFunNZG β,
            crischDERawSolveWf
                (qReduce (weakNormalizedF f
                  (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2))))
                (qmulNZG (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2)) g)
              = some ytilde
              ∧ y = qmulNZG ytilde (qinvNZG (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β)
                  f.1.1 f.1.2)))) := by
  set q : CPoly β := cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2 with hq
  set q' : QFunNZG β := qOfPolyNZG q with hq'
  set ftilde : QFunNZG β := weakNormalizedF f q' with hft
  rw [show crischDESolveSoundWf f g
      = (if CPoly.cisZeroG q then none
         else if cisCanonNormalizedG ftilde then
                match reduceSoundOpt ftilde with
                | none => none
                | some ftildeR =>
                  match crischDERawSolveWf ftildeR (qmulNZG q' g) with
                  | none => none
                  | some ytilde => some (qmulNZG ytilde (qinvNZG q'))
              else none) from rfl]
  by_cases hqz : CPoly.cisZeroG q = true
  · rw [if_pos hqz]
    simp only [hqz, Bool.true_eq_false, false_and, iff_false]
    intro h; exact absurd h (by simp)
  · rw [if_neg hqz]
    rw [Bool.not_eq_true] at hqz
    by_cases hck : cisCanonNormalizedG ftilde = true
    · rw [if_pos hck, reduceSoundOpt_eq]
      rcases hinner : crischDERawSolveWf (qReduce ftilde) (qmulNZG q' g) with _ | ytilde
      · simp only [hinner, hqz, hck, true_and]
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨yt, hyt, _⟩; exact absurd hyt (by simp)
      · simp only [hinner, hqz, hck, true_and, Option.some.injEq]
        constructor
        · intro h; exact ⟨ytilde, rfl, h.symm⟩
        · rintro ⟨yt, hyt, hy⟩; rw [hy, hyt]
    · rw [if_neg hck]
      rw [Bool.not_eq_true] at hck
      simp only [hck, Bool.false_eq_true, and_false, false_and, iff_false]
      intro h; exact absurd h (by simp)

/-- If the weak normalizer is nonzero, the canon-normality gate passes, and `crischDERawSolveWf` returns
`some ỹ`, then `crischDESolveSoundWf f g = some (ỹ/q')`. -/
theorem crischDESolveSoundWf_some_of_stages (f g ytilde : QFunNZG β)
    (hq : CPoly.cisZeroG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2)
        = false)
    (hck : cisCanonNormalizedG (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2)))
        = true)
    (hinner : crischDERawSolveWf
        (qReduce (weakNormalizedF f
          (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2))))
        (qmulNZG (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2)) g)
        = some ytilde) :
    crischDESolveSoundWf f g
      = some (qmulNZG ytilde (qinvNZG (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β)
          f.1.1 f.1.2)))) :=
  (crischDESolveSoundWf_some_iff f g _).mpr ⟨hq, hck, ytilde, hinner, rfl⟩

/-! ### Restatement against the intended wording (anonymous `example`) -/

example (f g ytilde : QFunNZG β)
    (hq : CPoly.cisZeroG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2)
        = false)
    (hck : cisCanonNormalizedG (weakNormalizedF f
        (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2)))
        = true)
    (hinner : crischDERawSolveWf
        (qReduce (weakNormalizedF f
          (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2))))
        (qmulNZG (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2)) g)
        = some ytilde) :
    crischDESolveSoundWf f g
      = some (qmulNZG ytilde (qinvNZG (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β)
          f.1.1 f.1.2)))) :=
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

/-! ## The `cRischDEG`-level polynomial-solution predicates -/

section InnerSubResidual

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CRischField α]

/-- `IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden`: the cleared polynomial identity
`gden·fden·(D(ynum)·yden − ynum·D(yden)) + gden·fnum·ynum·yden = gnum·fden·yden²` over `(CFieldSpec.K α)[X]`
— `(ynum/yden)` solves the RDE for `(fnum/fden, gnum/gden)`. -/
def IsCRischDEGPolySol (Dt fnum fden gnum gden ynum yden : CPoly α) : Prop :=
  toPolyG gden * toPolyG fden
      * (Differential.implicitDeriv (toPolyG Dt) (toPolyG ynum) * toPolyG yden
          - toPolyG ynum * Differential.implicitDeriv (toPolyG Dt) (toPolyG yden))
      + toPolyG gden * toPolyG fnum * toPolyG ynum * toPolyG yden
    = toPolyG gnum * toPolyG fden * toPolyG yden ^ 2

/-- `IsReducedRdeSol Dt a b c q`: `q` solves the reduced linear ODE `a·D(q) + b·q = c` over
`(CFieldSpec.K α)[X]` (`D = implicitDeriv (toPolyG Dt)`). -/
def IsReducedRdeSol (Dt a b c q : CPoly α) : Prop :=
  toPolyG a * Differential.implicitDeriv (toPolyG Dt) (toPolyG q) + toPolyG b * toPolyG q
    = toPolyG c

end InnerSubResidual

/-! ## Inner sub-residual -/

section InnerSubResidualWf

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α] [CFracGcdCoreWf α]
  [CRischField α]

/-- `RischDEInnerCompletenessWf Dt fnum fden gnum gden`: the inner-stage completeness sub-residuals —
`hnorm` (normal-denominator stage succeeds), `hbound` (degree-upper-bound), `hsolve` (inner solver succeeds)
on polynomial-solvable inputs. -/
structure RischDEInnerCompletenessWf (Dt fnum fden gnum gden : CPoly α) : Prop where
  /-- A polynomial-solvable RDE's normal-denominator reduction succeeds. -/
  hnorm : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    (cRdeNormalDenominatorG Dt fnum fden gnum gden).isSome = true
  /-- Any reduced polynomial solution has degree at most `cRdeBoundDegreeG`. -/
  hbound : ∀ a0 b0 c0 h0 : CPoly α,
    cRdeNormalDenominatorG Dt fnum fden gnum gden = some (a0, b0, c0, h0) →
    ∀ q : CPoly α,
      IsReducedRdeSol Dt (cRdeSpecialDenominatorG Dt a0 b0 c0).1
          (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
          (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1 q →
      cdegG q ≤ cRdeBoundDegreeG Dt
        (cRdeSpecialDenominatorG Dt a0 b0 c0).1
        (cRdeSpecialDenominatorG Dt a0 b0 c0).2.1
        (cRdeSpecialDenominatorG Dt a0 b0 c0).2.2.1
  /-- A polynomial-solvable RDE makes the inner solver succeed. -/
  hsolve : (∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) →
    (cRischDEG Dt fnum fden gnum gden).isSome = true

/-- `RischDEInnerCompletenessWf` yields `cRischDEG = some _` on a polynomial-solvable input. -/
theorem cRischDEG_isSome_of_innerCompletenessWf (Dt fnum fden gnum gden : CPoly α)
    (hinner : RischDEInnerCompletenessWf Dt fnum fden gnum gden)
    (hsol : ∃ ynum yden, IsCRischDEGPolySol Dt fnum fden gnum gden ynum yden) :
    (cRischDEG Dt fnum fden gnum gden).isSome = true :=
  hinner.hsolve hsol

end InnerSubResidualWf

/-! ## Raw inner-solver bridge

Move the inner-completeness result across the `QFunNZG` denominator guard from `cRischDEG` to the wrapper's
`crischDERawSolveWf`. -/

section RawInnerWf

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCoreWf β] [CRischField β]

omit [CFieldSpec β] [CDiffFieldSpec β] [CFieldDomain β] in
/-- If `cRischDEG [1]` succeeds and every returned denominator is nonzero, then `crischDERawSolveWf`
returns `some`. -/
theorem crischDERawSolveWf_isSome_of_cRischDEG_some_den (ftilde gtilde : QFunNZG β)
    (hsome : (cRischDEG ([CField.one] : CPoly β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2).isSome = true)
    (hden : ∀ ynum yden : CPoly β,
      cRischDEG ([CField.one] : CPoly β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 = some (ynum, yden) →
      CPoly.cisZeroG yden = false) :
    ∃ ytilde, crischDERawSolveWf ftilde gtilde = some ytilde := by
  obtain ⟨⟨ynum, yden⟩, hp⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨⟨(ynum, yden), hden ynum yden hp⟩, ?_⟩
  exact (crischDERawSolveWf_some_iff ftilde gtilde _).mpr
    ⟨ynum, yden, hden ynum yden hp, hp, rfl⟩

omit [CFieldSpec β] [CDiffFieldSpec β] [CFieldDomain β] in
/-- Inner stage successes plus the returned-denominator guard imply `crischDERawSolveWf` succeeds. -/
theorem crischDERawSolveWf_isSome_of_cRischDEG_stages_den (ftilde gtilde : QFunNZG β)
    (a0 b0 c0 h0 bbar cbar : CPoly β) (m : ℤ) (α' β' v : CPoly β)
    (hnorm : cRdeNormalDenominatorG ([CField.one] : CPoly β)
      ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 = some (a0, b0, c0, h0))
    (hspde : cSPDEG ([CField.one] : CPoly β) (cRdeSpecialDenominatorG ([CField.one] : CPoly β)
        a0 b0 c0).1
        (cRdeSpecialDenominatorG ([CField.one] : CPoly β) a0 b0 c0).2.1
        (cRdeSpecialDenominatorG ([CField.one] : CPoly β) a0 b0 c0).2.2.1
        (cRdeBoundDegreeG ([CField.one] : CPoly β) (cRdeSpecialDenominatorG ([CField.one] : CPoly β)
          a0 b0 c0).1
          (cRdeSpecialDenominatorG ([CField.one] : CPoly β) a0 b0 c0).2.1
          (cRdeSpecialDenominatorG ([CField.one] : CPoly β) a0 b0 c0).2.2.1 : ℤ)
      = some (bbar, cbar, m, α', β'))
    (hpoly : cPolyRischDEG ([CField.one] : CPoly β) bbar cbar m = some v)
    (hden : ∀ ynum yden : CPoly β,
      cRischDEG ([CField.one] : CPoly β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 = some (ynum, yden) →
      CPoly.cisZeroG yden = false) :
    ∃ ytilde, crischDERawSolveWf ftilde gtilde = some ytilde := by
  have hsome : (cRischDEG ([CField.one] : CPoly β)
      ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2).isSome = true := by
    rw [cRischDEG, hnorm]
    simp only [hspde, hpoly, Option.isSome_some]
  exact crischDERawSolveWf_isSome_of_cRischDEG_some_den ftilde gtilde hsome hden

omit [CFieldDomain β] in
/-- An inner-completeness residual, a polynomial solution, and the denominator guard imply
`crischDERawSolveWf` succeeds. -/
theorem crischDERawSolveWf_isSome_of_innerCompletenessWf (ftilde gtilde : QFunNZG β)
    (hinner : RischDEInnerCompletenessWf ([CField.one] : CPoly β)
      ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2)
    (hsol : ∃ ynum yden,
      IsCRischDEGPolySol ([CField.one] : CPoly β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 ynum yden)
    (hden : ∀ ynum yden : CPoly β,
      cRischDEG ([CField.one] : CPoly β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 = some (ynum, yden) →
      CPoly.cisZeroG yden = false) :
    ∃ ytilde, crischDERawSolveWf ftilde gtilde = some ytilde :=
  crischDERawSolveWf_isSome_of_cRischDEG_some_den ftilde gtilde
    (cRischDEG_isSome_of_innerCompletenessWf ([CField.one] : CPoly β)
      ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 hinner hsol)
    hden

/-! ### Restatement against the intended wording (anonymous `example`) -/

example (ftilde gtilde : QFunNZG β)
    (hinner : RischDEInnerCompletenessWf ([CField.one] : CPoly β)
      ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2)
    (hsol : ∃ ynum yden,
      IsCRischDEGPolySol ([CField.one] : CPoly β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 ynum yden)
    (hden : ∀ ynum yden : CPoly β,
      cRischDEG ([CField.one] : CPoly β) ftilde.1.1 ftilde.1.2 gtilde.1.1 gtilde.1.2 = some (ynum, yden) →
      CPoly.cisZeroG yden = false) :
    ∃ ytilde, crischDERawSolveWf ftilde gtilde = some ytilde :=
  crischDERawSolveWf_isSome_of_innerCompletenessWf ftilde gtilde hinner hsol hden

end RawInnerWf

/-! ## Completeness wrapper -/

section CompleteWf

variable {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β] [CFieldDomain β]
  [CFracGcdCoreWf β] [CRischField β] [Algebra ℚ (CFieldSpec.K β)]

/-- A successful `crischDESolveSoundWf` run (with soundness certificate `RischDESoundnessWf`) witnesses
`FieldRDESolvable`. -/
theorem crischDESolveSoundWf_imp_solvable (f g y : QFunNZG β)
    (hsolve : crischDESolveSoundWf f g = some y)
    (hsound : RischDESoundnessWf f g) :
    FieldRDESolvable f g :=
  ⟨y, crischDESolveSoundWf_field f g y hsolve hsound⟩

/-! ### Completeness residual -/

/-- `RischDECompletenessResidualWf f g`: the three stage-completeness facts consumed by
`crischDESolveSoundWf_some_of_stages` — nonzero weak normalizer (`hwn`), canonical-normality (`hck`),
inner solver success (`hinner`) on a solvable RDE. -/
structure RischDECompletenessResidualWf (f g : QFunNZG β) : Prop where
  /-- A solvable RDE has a nonzero weak normalizer. -/
  hwn : FieldRDESolvable f g →
    CPoly.cisZeroG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2) = false
  /-- A solvable RDE satisfies the canonical-normality guarantee. -/
  hck : FieldRDESolvable f g →
    IsCanonNormalizedWf f
      (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2))
  /-- A solvable RDE makes the inner solve succeed on the reduced pair. -/
  hinner : FieldRDESolvable f g →
    ∃ ytilde : QFunNZG β,
      crischDERawSolveWf
          (qReduce (weakNormalizedF f
            (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2))))
          (qmulNZG (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2)) g)
        = some ytilde

/-- If the RDE is solvable and `RischDECompletenessResidualWf` holds, then `crischDESolveSoundWf`
returns `some`. -/
theorem crischDESolveSoundWf_complete_of_residualWf (f g : QFunNZG β)
    (hsol : FieldRDESolvable f g) (hres : RischDECompletenessResidualWf f g) :
    ∃ y, crischDESolveSoundWf f g = some y := by
  obtain ⟨ytilde, hinner⟩ := hres.hinner hsol
  have hck : cisCanonNormalizedG (weakNormalizedF f
      (qOfPolyNZG (cWeakNormalizerG ([CField.one] : CPoly β) f.1.1 f.1.2))) = true :=
    (cisCanonNormalizedG_iff f _).mpr (hres.hck hsol)
  exact ⟨_, crischDESolveSoundWf_some_of_stages f g ytilde (hres.hwn hsol) hck hinner⟩

/-- Modulo `RischDECompletenessResidualWf` and `RischDESoundnessWf`, `crischDESolveSoundWf f g` returns
`some` iff the field-level RDE is solvable. -/
theorem crischDESolveSoundWf_decides_of_residualWf (f g : QFunNZG β)
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
example (f g : QFunNZG β) (hres : RischDECompletenessResidualWf f g)
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
