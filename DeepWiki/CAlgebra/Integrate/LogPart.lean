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
`∫ b/d = Σᵢ Σ_{Qᵢ(c)=0} c · log Sᵢ(c, x)`.

The resultant is the Mathlib-bridged Sylvester determinant (`toPolynomial_resultant` gives
the certificate hook); the remainder sequence is the primitive pseudo-remainder sequence —
its elements differ from the subresultants only by `z`-contents, which specialize to
constants and vanish under the logarithmic derivative. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R] [DensePolyGcd R]

open scoped Differential FormalDiff

/-! ### Bivariate helpers: `K[z][x]`, `x` outermost -/

/-- Lift an `x`-polynomial into `K[z][x]`: coefficients become `z`-constants. -/
def liftX (p : DensePoly R) : DensePoly (DensePoly R) := ofList (p.coeffs.map C)

/-- The indeterminate `z`, as a constant of `K[z][x]`. -/
def zC : DensePoly (DensePoly R) := C (ofList [0, 1])

/-- The `z`-content: the gcd of the `x`-coefficients. -/
def zContent (p : DensePoly (DensePoly R)) : DensePoly R :=
  p.coeffs.foldr (fun c acc => DensePolyGcd.gcd c acc) 0

/-- The `z`-primitive part: divide each `x`-coefficient by the content. -/
def zPrimitive (p : DensePoly (DensePoly R)) : DensePoly (DensePoly R) :=
  ofList (p.coeffs.map fun c => div c (zContent p))

/-- The primitive pseudo-remainder sequence in `x` over `K[z]`, starting from the second
input: pseudo-divide, take the `z`-primitive part, recurse. -/
def primPRS : ℕ → DensePoly (DensePoly R) → DensePoly (DensePoly R) →
    List (DensePoly (DensePoly R))
  | 0, _, _ => []
  | fuel + 1, A, B =>
      if B = 0 then []
      else B :: primPRS fuel B (zPrimitive (pseudoMod A B))

/-! ### The Rothstein–Trager data -/

/-- The Rothstein–Trager resultant `R(z) = res_x(d, b − z·d′)`: its roots are the
coefficients of the logarithms of `∫ b/d` (algorithm dispatched by `DensePolyResultant` —
the pseudo-remainder sequence over `K[z]`). -/
def rtResultant (b d : DensePoly R) : DensePoly R :=
  DensePolyResultant.resultant (liftX d) (liftX b - zC * liftX (d′))
    (d.size - 1) (d.size - 2)

variable [DensePolySquarefree R]

/-- **Lazard–Rioboo–Trager log terms** for `b/d`: for each squarefree factor `Qᵢ` of the
Rothstein–Trager resultant at exponent `i` (constant factors dropped — they carry no roots),
the log argument `Sᵢ(z,x)` is the `x`-degree-`i` element of the remainder sequence — or `d`
itself when `i = deg d`. -/
def lrtLogTerms (b d : DensePoly R) : List (DensePoly R × DensePoly (DensePoly R)) :=
  let prs := primPRS d.size (liftX d) (liftX b - zC * liftX (d′))
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

end DensePoly

end DeepWiki.CAlgebra
