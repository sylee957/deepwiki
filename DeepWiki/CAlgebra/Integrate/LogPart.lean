import DeepWiki.CAlgebra.Integrate.Hermite
import DeepWiki.CAlgebra.Resultant

/-! # The logarithmic part: Lazard–Rioboo–Trager

For a Hermite log part `b/d` (proper, coprime, squarefree monic denominator), the
Rothstein–Trager resultant `R(z) = res_x(d, b − z·d′)` has as roots exactly the coefficients
of the logarithms of `∫ b/d`, and by Lazard–Rioboo–Trager the argument of the logarithm for
a root `c` of the multiplicity-`i` part of `R` is the degree-`i` element of the polynomial
remainder sequence of `(d, b − z·d′)`, specialized at `z = c` — no gcd over an algebraic
extension is ever computed. This module computes that data: pairs `(Qᵢ(z), Sᵢ(z,x))` with
`Qᵢ` squarefree (its roots are the log coefficients) and `Sᵢ` the bivariate log argument.
`∫ b/d = Σᵢ Σ_{Qᵢ(c)=0} c · log Sᵢ(c, x)`. The bivariate machinery (lifts, contents, the
primitive remainder sequence) lives in `Resultant/Primitive`.

The resultant is the Mathlib-bridged Sylvester determinant (`toPolynomial_resultant` gives
the certificate hook); the remainder sequence is the primitive pseudo-remainder sequence —
its elements differ from the subresultants only by `z`-contents, which specialize to
constants and vanish under the logarithmic derivative. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R] [DensePolyGcd R]

open scoped Differential FormalDiff

/-! ### The Rothstein–Trager data -/

/-- The Rothstein–Trager resultant `R(z) = res_x(d, b − z·d′)`: its roots are the
coefficients of the logarithms of `∫ b/d` (algorithm dispatched by `DensePolyResultant` —
the pseudo-remainder sequence over `K[z]`). -/
def rtResultant (b d : DensePoly R) : DensePoly R :=
  DensePolyResultant.resultant (liftX d) (liftX b - zC * liftX (d′))

variable [DensePolySquarefree R]

/-- **Lazard–Rioboo–Trager log terms** for `b/d`: for each squarefree factor `Qᵢ` of the
Rothstein–Trager resultant at exponent `i` (constant factors dropped — they carry no roots),
the log argument `Sᵢ(z,x)` is the `x`-degree-`i` element of the remainder sequence — or `d`
itself when `i = deg d`. -/
def lrtLogTerms (b d : DensePoly R) : List (DensePoly R × DensePoly (DensePoly R)) :=
  let prs := DensePolyPRS.prs (liftX d) (liftX b - zC * liftX (d′))
  (DensePolySquarefree.sqfDecomp (rtResultant b d)).zipIdx.filterMap fun Qi =>
    if Qi.1.size ≤ 1 then none
    else some (Qi.1,
      if Qi.2 + 2 = d.size then liftX d
      else match prs.find? (fun S => S.size = Qi.2 + 2) with
        | some S => S
        | none => liftX d)

/-- The logarithmic-part data of a canonical fraction (intended: a Hermite `logPart`):
`∫ f = Σᵢ Σ_{Qᵢ(c)=0} c · log Sᵢ(c, x)`. -/
def lrtLogPart (h : DenseFrac R) : List (DensePoly R × DensePoly (DensePoly R)) :=
  lrtLogTerms h.num h.den.toPoly

/-- Members of `zipIdx` project to members of the list. -/
private theorem fst_mem_of_mem_zipIdx {α : Type u} :
    ∀ {l : List α} {n : ℕ} {x : α × ℕ}, x ∈ l.zipIdx n → x.1 ∈ l := by
  intro l
  induction l with
  | nil => intro n x h; simp [List.zipIdx] at h
  | cons a t ih =>
      intro n x h
      rw [List.zipIdx_cons] at h
      rcases List.mem_cons.mp h with rfl | h
      · simp
      · exact List.mem_cons_of_mem a (ih h)

/-- Every coefficient polynomial of the log terms is squarefree and nonconstant. -/
theorem lrtLogTerms_fst_squarefree (b d : DensePoly R) :
    ∀ t ∈ lrtLogTerms b d, Squarefree t.1 ∧ 1 < t.1.size := by
  intro t ht
  simp only [lrtLogTerms, List.mem_filterMap] at ht
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
  exact ⟨DensePolySquarefree.squarefree_of_mem (fst_mem_of_mem_zipIdx hQi), by omega⟩


/-- Bundled Lazard–Rioboo–Trager output for a canonical fraction: the computable
`RootSum` data of the logarithmic integral — pairs `(Qᵢ, Sᵢ)` meaning
`∫ = ∑ᵢ ∑_{Qᵢ(α)=0} α · log Sᵢ(α, x)` — with the factor contract carried as an
invariant. -/
structure LrtResult (R : Type u) [Field R] [DecidableEq R] where
  /-- The log-term pairs `(Qᵢ, Sᵢ)`. -/
  terms : List (DensePoly R × DensePoly (DensePoly R))
  /-- Every `Qᵢ` is squarefree and nonconstant. -/
  fst_squarefree : ∀ t ∈ terms, Squarefree t.1 ∧ 1 < t.1.size

/-- **The LRT stage, bundled**: the log-part data of a canonical fraction, with its
contract. -/
def lrtIntegrate (h : DenseFrac R) : LrtResult R where
  terms := lrtLogPart h
  fst_squarefree := lrtLogTerms_fst_squarefree h.num h.den.toPoly

/-- The bundled terms are the log-part data. -/
theorem lrtIntegrate_terms (h : DenseFrac R) : (lrtIntegrate h).terms = lrtLogPart h := rfl

/-- A member of `lrtLogTerms` is the image of a decomposition index. -/
theorem exists_index_of_mem_lrtLogTerms {b d : DensePoly R}
    {QS : DensePoly R × DensePoly (DensePoly R)} (h : QS ∈ lrtLogTerms b d) :
    ∃ j, ∃ hj : j < (DensePolySquarefree.sqfDecomp (rtResultant b d)).length,
      QS.1 = (DensePolySquarefree.sqfDecomp (rtResultant b d))[j] := by
  rw [lrtLogTerms, List.mem_filterMap] at h
  obtain ⟨Qi, hQi, hf⟩ := h
  obtain ⟨j, hjlen, hgot⟩ := List.mem_iff_getElem.mp hQi
  have hj : j < (DensePolySquarefree.sqfDecomp (rtResultant b d)).length := by
    simpa using hjlen
  have hQi_eq : Qi = ((DensePolySquarefree.sqfDecomp (rtResultant b d))[j], j) := by
    rw [← hgot, List.getElem_zipIdx]
    simp
  subst hQi_eq
  dsimp only at hf
  by_cases hsz : ((DensePolySquarefree.sqfDecomp (rtResultant b d))[j]).size ≤ 1
  · rw [if_pos hsz] at hf
    simp at hf
  · rw [if_neg hsz, Option.some_inj] at hf
    exact ⟨j, hj, by rw [← hf]⟩

/-- **Covering uniqueness**: two produced pairs sharing a root coincide. -/
theorem lrt_covering_unique [CharZero R] {b d : DensePoly R}
    (hrt : rtResultant b d ≠ 0) {QS QS' : DensePoly R × DensePoly (DensePoly R)}
    (h1 : QS ∈ lrtLogTerms b d) (h2 : QS' ∈ lrtLogTerms b d) {α : R}
    (hr1 : (toPolynomial QS.1).IsRoot α) (hr2 : (toPolynomial QS'.1).IsRoot α) :
    QS = QS' := by
  rw [lrtLogTerms, List.mem_filterMap] at h1 h2
  obtain ⟨Qi, hQi, hf1⟩ := h1
  obtain ⟨Qi', hQi', hf2⟩ := h2
  obtain ⟨j, hjlen, hgot⟩ := List.mem_iff_getElem.mp hQi
  obtain ⟨k, hklen, hgot'⟩ := List.mem_iff_getElem.mp hQi'
  have hj : j < (DensePolySquarefree.sqfDecomp (rtResultant b d)).length := by
    simpa using hjlen
  have hk : k < (DensePolySquarefree.sqfDecomp (rtResultant b d)).length := by
    simpa using hklen
  have hQi_eq : Qi = ((DensePolySquarefree.sqfDecomp (rtResultant b d))[j], j) := by
    rw [← hgot, List.getElem_zipIdx]; simp
  have hQi'_eq : Qi' = ((DensePolySquarefree.sqfDecomp (rtResultant b d))[k], k) := by
    rw [← hgot', List.getElem_zipIdx]; simp
  subst hQi_eq
  subst hQi'_eq
  dsimp only at hf1 hf2
  by_cases hsz1 : ((DensePolySquarefree.sqfDecomp (rtResultant b d))[j]).size ≤ 1
  · rw [if_pos hsz1] at hf1
    simp at hf1
  by_cases hsz2 : ((DensePolySquarefree.sqfDecomp (rtResultant b d))[k]).size ≤ 1
  · rw [if_pos hsz2] at hf2
    simp at hf2
  rw [if_neg hsz1, Option.some_inj] at hf1
  rw [if_neg hsz2, Option.some_inj] at hf2
  rcases eq_or_ne j k with rfl | hne
  · rw [← hf1, ← hf2]
  · rw [← hf1] at hr1
    rw [← hf2] at hr2
    exact absurd (sqfDecomp_no_common_root hrt hj hk hne hr1 hr2) not_false

/-- The `j`-th nonconstant decomposition factor yields a produced pair. -/
theorem mem_lrtLogTerms_of_index {b d : DensePoly R} {j : ℕ}
    (hj : j < (DensePolySquarefree.sqfDecomp (rtResultant b d)).length)
    (hsz : ¬ ((DensePolySquarefree.sqfDecomp (rtResultant b d))[j]).size ≤ 1) :
    ((DensePolySquarefree.sqfDecomp (rtResultant b d))[j],
      if j + 2 = d.size then liftX d
      else match (DensePolyPRS.prs (liftX d)
          (liftX b - zC * liftX (d′))).find? (fun S => S.size = j + 2) with
        | some S => S
        | none => liftX d) ∈ lrtLogTerms b d := by
  rw [lrtLogTerms, List.mem_filterMap]
  refine ⟨((DensePolySquarefree.sqfDecomp (rtResultant b d))[j], j), ?_, ?_⟩
  · have hlen : j < (DensePolySquarefree.sqfDecomp (rtResultant b d)).zipIdx.length := by
      simpa using hj
    have hget : (DensePolySquarefree.sqfDecomp (rtResultant b d)).zipIdx[j]
        = ((DensePolySquarefree.sqfDecomp (rtResultant b d))[j], j) := by
      rw [List.getElem_zipIdx]
      simp
    rw [← hget]
    exact List.getElem_mem hlen
  · dsimp only
    rw [if_neg hsz]

end DensePoly

end DeepWiki.CAlgebra
