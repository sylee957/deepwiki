import DeepWiki.CAlgebra.IntegrateRisch.DiffRing
import DeepWiki.CAlgebra.IntegrateRisch.Results
import DeepWiki.CAlgebra.Integrate.LogPart
import DeepWiki.CAlgebra.Integrate.DerivDataSpec

/-! # The log part at a tower level: Rothstein–Trager with the field derivation

The Lazard–Rioboo–Trager construction generalized from the base's formal derivative to a
tower level's field derivation `D = extendDeriv d Dt`: the residues (roots of the
Rothstein–Trager resultant) are the log coefficients, and the **residue-constancy test**
(`mapCoeffs d Q = 0` — decidable) is the elementarity criterion. At the base data
`(d = 0, Dt = 1)` the construction is exactly the rational `rtResultant`/`lrtLogTerms`,
so the base level inherits the fully-proven rational LRT soundness; the tower levels'
residue-criterion soundness is the remaining arc (see `docs/integrate-risch-calgebra.md`).

The field's `d′` is the formal derivative only because at the base it *equals* the field
derivation; here we replace it with `extendDeriv d Dt` (the genuine field derivation), the
form the old engine's `rtResultantGen … (implicitDeriv-based B)` confirms. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {K : Type u} [Field K] [DecidableEq K] [DensePolyGcd K]

open scoped Differential FormalDiff

/-- **Derivation-generic Rothstein–Trager resultant** `R(z) = res_x(dp, b − z·(D dp))`
for the level derivation `D = extendDeriv d Dt`. Its roots are the log coefficients of
`∫ b/dp`. -/
def rtResultantD (d : K → K) (Dt b dp : DensePoly K) : DensePoly K :=
  DensePolyResultant.resultant (liftX dp) (liftX b - zC * liftX (extendDeriv d Dt dp))

omit [DensePolyGcd K] in
/-- At the base data `(d = 0, Dt = 1)` the field derivation is the formal derivative, so
the generic resultant is the rational one. -/
theorem rtResultantD_zero_one (b dp : DensePoly K) :
    rtResultantD (fun _ => 0) 1 b dp = rtResultant b dp := by
  rw [rtResultantD, rtResultant, extendDeriv_zero_one]

variable [DensePolySquarefree K]

/-- **Derivation-generic Lazard–Rioboo–Trager log terms** for `b/dp` at the level
derivation `D = extendDeriv d Dt`: for each nonconstant squarefree factor `Qᵢ` of the
Rothstein–Trager resultant at exponent `i`, the log argument `Sᵢ(z,x)` is the
`x`-degree-`i` element of the remainder sequence (or `dp` itself at the top index). -/
def lrtLogTermsD (d : K → K) (Dt b dp : DensePoly K) :
    List (DensePoly K × DensePoly (DensePoly K)) :=
  let prs := DensePolyPRS.prs (liftX dp) (liftX b - zC * liftX (extendDeriv d Dt dp))
  (DensePolySquarefree.sqfDecomp (rtResultantD d Dt b dp)).zipIdx.filterMap fun Qi =>
    if Qi.1.size ≤ 1 then none
    else some (Qi.1,
      if Qi.2 + 2 = dp.size then liftX dp
      else match prs.find? (fun S => S.size = Qi.2 + 2) with
        | some S => S
        | none => liftX dp)

/-- At the base data the generic log terms coincide with the rational `lrtLogTerms`, so
the base level inherits the fully-proven rational LRT soundness. -/
theorem lrtLogTermsD_zero_one (b dp : DensePoly K) :
    lrtLogTermsD (fun _ => 0) 1 b dp = lrtLogTerms b dp := by
  unfold lrtLogTermsD lrtLogTerms
  rw [rtResultantD_zero_one, extendDeriv_zero_one]
  rfl

/-- **Structural soundness**: every produced factor `Qᵢ` is squarefree and nonconstant. -/
theorem lrtLogTermsD_fst_squarefree (d : K → K) (Dt b dp : DensePoly K) :
    ∀ t ∈ lrtLogTermsD d Dt b dp, Squarefree t.1 ∧ 1 < t.1.size := by
  have hmem : ∀ (L : List (DensePoly K)) (n : ℕ), ∀ x ∈ L.zipIdx n, x.1 ∈ L := by
    intro L
    induction L with
    | nil => intro n x hx; simp [List.zipIdx] at hx
    | cons a T ih =>
        intro n x hx
        rw [List.zipIdx_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih (n + 1) x hx)
  intro t ht
  simp only [lrtLogTermsD, List.mem_filterMap] at ht
  obtain ⟨Qi, hQi, hsome⟩ := ht
  have hsz : ¬ Qi.1.size ≤ 1 := by
    intro hsz
    rw [if_pos hsz] at hsome
    simp at hsome
  rw [if_neg hsz] at hsome
  have ht1 : t.1 = Qi.1 := by
    have h := Option.some.inj hsome
    rw [← h]
  rw [ht1]
  exact ⟨DensePolySquarefree.squarefree_of_mem (hmem _ 0 Qi hQi), by omega⟩

/-! ### The residue-constancy test -/

/-- **Residue constancy** for a produced factor `Q`: its coefficients are `d`-constants,
so its roots — the residues, i.e. the log coefficients — are constants of the field.
This is Bronstein's elementarity criterion, decidable through `mapCoeffs d Q = 0`. -/
def IsResidueConstant (d : K → K) (Q : DensePoly K) : Prop := mapCoeffs d Q = 0

instance (d : K → K) (Q : DensePoly K) : Decidable (IsResidueConstant d Q) :=
  decEq (mapCoeffs d Q) 0

/-- The residue-constancy test over all produced factors — exactly the `ResultRisch`
`fst_constant` invariant, tying the log-part stage to the result record. -/
def AllResiduesConstant (d : K → K)
    (terms : List (DensePoly K × DensePoly (DensePoly K))) : Prop :=
  ∀ t ∈ terms, IsResidueConstant d t.1

instance (d : K → K) (terms : List (DensePoly K × DensePoly (DensePoly K))) :
    Decidable (AllResiduesConstant d terms) :=
  List.decidableBAll _ _

omit [DensePolyGcd K] in
/-- The all-constant test unfolds to the `ResultRisch.fst_constant` shape. -/
theorem allResiduesConstant_iff (d : K → K)
    (terms : List (DensePoly K × DensePoly (DensePoly K))) :
    AllResiduesConstant d terms ↔ ∀ t ∈ terms, mapCoeffs d t.1 = 0 :=
  Iff.rfl

/-! ### The residue criterion (the sound direction)

The log-part stage's soundness — that the field derivative of the produced logarithms is
the integrand — is Bronstein's residue criterion (§5.6). We name it as a genuine
mathematical frontier (`ResidueCriterion`), discharge it unconditionally at the base
level, and leave the tower discharge to P4b (bridge to the old engine's general-derivation
LRT soundness). This is the frontier-as-hypothesis pattern: the criterion is real content,
not bookkeeping. -/

/-- **The residue criterion** at level data `(d, Dt)`: for every valid simple part `g`
(proper, squarefree denominator), the field derivative `∑ᵢ ∑_{Qᵢ(α)=0} α·D(log Sᵢ)` of the
produced logarithms equals `g`. This is the log-part stage's soundness — a decidable log
list whose derivative recovers the integrand. -/
def ResidueCriterion (d : K → K) (Dt : DensePoly K) : Prop :=
  ∀ g : DenseFrac K, Squarefree g.den.toPoly → RatFunc.IsProper (DenseFrac.toRatFunc g) →
    ((lrtLogTermsD d Dt g.num g.den.toPoly).map
      (fun QS => rootSumDerivD d Dt QS.1 QS.2)).sum = g

section BaseSound

variable [CharZero K] [IsAlgClosed K]

/-- **Base-level log-part soundness**: at base data `(d = 0, Dt = 1)`, the field
derivative of the produced logarithms is the integrand — `D(∑ᵢ ∑_{Qᵢ(α)=0} α·log Sᵢ) = g`
for a proper `g` with squarefree denominator. Proven by reduction (`lrtLogTermsD_zero_one`,
`rootSumDerivD_zero_one`) to the rational `lrtIntegrate_sound`. -/
theorem lrtLogTermsD_baseSound (g : DenseFrac K) (hsf : Squarefree g.den.toPoly)
    (hprop : RatFunc.IsProper (DenseFrac.toRatFunc g)) :
    ((lrtLogTermsD (fun _ => 0) 1 g.num g.den.toPoly).map
      (fun QS => rootSumDerivD (fun _ => 0) 1 QS.1 QS.2)).sum = g := by
  rw [lrtLogTermsD_zero_one]
  have hmap : (lrtLogTerms g.num g.den.toPoly).map
        (fun QS => rootSumDerivD (fun _ => 0) 1 QS.1 QS.2)
      = (lrtLogTerms g.num g.den.toPoly).map (fun QS => rootSumDeriv QS.1 QS.2) :=
    List.map_congr_left (fun QS _ => rootSumDerivD_zero_one QS.1 QS.2)
  rw [hmap]
  exact lrtIntegrate_sound g hsf hprop

/-- **The residue criterion holds at the base level** — the sound direction, discharged
unconditionally for `R(x)` with `d/dx`. -/
theorem residueCriterion_zero_one : ResidueCriterion (fun _ : K => 0) 1 :=
  fun g hsf hprop => lrtLogTermsD_baseSound g hsf hprop

end BaseSound

end DensePoly

end DeepWiki.CAlgebra
