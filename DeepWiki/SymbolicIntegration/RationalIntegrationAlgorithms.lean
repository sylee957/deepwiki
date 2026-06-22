import DeepWiki.SymbolicIntegration.RationalIntegration
import DeepWiki.SymbolicIntegration.Residues
import DeepWiki.SymbolicIntegration.SquarefreeFactorization
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Radical.Basic
import Mathlib.Algebra.Polynomial.Degree.Units

/-! # Rational-function integration algorithms — functional form (Bronstein §2.1–§2.2)
The book's integration *algorithms* (Bernoulli, Hermite, Horowitz–Ostrogradsky, Rothstein–Trager,
Lazard–Rioboo–Trager) are formalized as ordinary functional Lean `def`s over `K[X]` paired with a
correctness theorem, rather than via an operational-semantics interpreter. This file starts the
shared kernel: the extended-Euclidean **Diophantine solver** `aB + bC = c` for coprime `a, b`, the
inner step of partial-fraction (§2.1) and Hermite (§2.2) reduction. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

open Classical in
/-- **Diophantine solver** (the extended-Euclidean inner step of §2.1/§2.2): for `a, b ∈ K[X]`,
return `(B, C)` with `a·B + b·C = c` whenever `a, b` are coprime, computed from the Bézout
coefficients `gcdA/gcdB` scaled by the inverse of the (constant, unit) `gcd a b`. -/
noncomputable def diophantineSolve (a b c : K[X]) : K[X] × K[X] :=
  (c * EuclideanDomain.gcdA a b * C ((EuclideanDomain.gcd a b).coeff 0)⁻¹,
   c * EuclideanDomain.gcdB a b * C ((EuclideanDomain.gcd a b).coeff 0)⁻¹)

open Classical in
/-- **Correctness of `diophantineSolve`**: for coprime `a, b`, the returned pair `(B, C)` solves the
Bézout/Diophantine equation `a·B + b·C = c`. -/
theorem diophantineSolve_spec {a b : K[X]} (hab : IsCoprime a b) (c : K[X]) :
    a * (diophantineSolve a b c).1 + b * (diophantineSolve a b c).2 = c := by
  have hg : IsUnit (EuclideanDomain.gcd a b) := EuclideanDomain.gcd_isUnit_iff.mpr hab
  have hdeg : (EuclideanDomain.gcd a b).natDegree = 0 := natDegree_eq_zero_of_isUnit hg
  have hgC : EuclideanDomain.gcd a b = C ((EuclideanDomain.gcd a b).coeff 0) :=
    eq_C_of_natDegree_eq_zero hdeg
  have hr0 : (EuclideanDomain.gcd a b).coeff 0 ≠ 0 := fun h =>
    hg.ne_zero (by rw [hgC, h, map_zero])
  simp only [diophantineSolve]
  have step : a * (c * EuclideanDomain.gcdA a b * C ((EuclideanDomain.gcd a b).coeff 0)⁻¹)
        + b * (c * EuclideanDomain.gcdB a b * C ((EuclideanDomain.gcd a b).coeff 0)⁻¹)
      = c * C ((EuclideanDomain.gcd a b).coeff 0)⁻¹
        * (a * EuclideanDomain.gcdA a b + b * EuclideanDomain.gcdB a b) := by ring
  rw [step, ← EuclideanDomain.gcd_eq_gcd_ab, mul_assoc]
  nth_rewrite 2 [hgC]
  rw [← map_mul, inv_mul_cancel₀ hr0, map_one, mul_one]

/-! ## §2.4 The Rothstein–Trager algorithm (functional core)
The algorithm computes the logarithmic part `∫ A/D = Σ a·log(Gₐ)` for squarefree `D` from two
primitives: the resultant `R(t) = resultant_x(D, A − t·D')` (whose roots are the residues) and the
gcd `Gₐ = gcd(D, A − a·D')` (whose roots are the `D`-roots with residue `a`). Both are functional
`def`s; correctness reuses the §4.4 residue theory. -/

/-- **Rothstein–Trager resultant** `R(t) = resultant_x(D, A − t·D') ∈ K[t]`: `D, A, D'` are lifted to
`(K[t])[x]` (coefficients embedded by `C : K → K[t]`) and `t` becomes the constant `C X`; the
resultant eliminates `x`. Formal `x`-degrees `deg D` and `deg D − 1` (the book's layout). -/
noncomputable def rtResultant (A D : K[X]) : K[X] :=
  Polynomial.resultant (D.map (C : K →+* K[X]))
    (A.map (C : K →+* K[X]) - C Polynomial.X * (derivative D).map (C : K →+* K[X]))
    D.natDegree (D.natDegree - 1)

/-- **Specialization of `rtResultant`**: evaluating `R(t)` at `t = a` recovers the parameter
resultant `resultant_x(D, A − a·D')` (same formal degrees) — `resultant_map_map` for the coefficient
evaluation `K[t] → K`, since `(C·)` then `eval a` is the identity on `K`. -/
theorem rtResultant_eval (A D : K[X]) (a : K) :
    (rtResultant A D).eval a
      = Polynomial.resultant D (A - C a * derivative D) D.natDegree (D.natDegree - 1) := by
  have hcomp : (Polynomial.evalRingHom a).comp (C : K →+* K[X]) = RingHom.id K := by
    ext k; simp
  show Polynomial.evalRingHom a (rtResultant A D) = _
  rw [rtResultant, ← Polynomial.resultant_map_map]
  congr 1
  · rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  · simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_C, hcomp,
      Polynomial.map_id]
    simp

open Classical in
/-- **Rothstein–Trager `Gₐ`** `= gcd(D, A − a·D')`, the gcd whose roots are exactly the roots of `D`
at which the residue of `A/D` equals `a` (its correctness is `isRoot_gcd_iff_residue`). -/
noncomputable def rtLogGcd (A D : K[X]) (a : K) : K[X] :=
  gcd D (A - C a * derivative D)

open Classical in
/-- **Correctness of `rtLogGcd`** (Rothstein–Trager (ii)): at a point `α` with `D'(α) ≠ 0`, `α` is a
root of `Gₐ` iff `α` is a root of `D` with residue `a`. -/
theorem rtLogGcd_isRoot_iff (A D : K[X]) (a α : K) (hα : (derivative D).eval α ≠ 0) :
    (rtLogGcd A D a).IsRoot α ↔ (D.IsRoot α ∧ A.eval α / (derivative D).eval α = a) :=
  isRoot_gcd_iff_residue A D a α hα

/-- **Rothstein–Trager correctness, residues = roots of `R`** (combining the resultant primitive with
Thm 2.4.1(i)): over an algebraically closed field, for squarefree `D`, if the parameter resultant has
the book's `x`-degree `deg D − 1` (e.g. `a ≠ 0`), then `R(a) = 0` iff `a` is a residue of `A/D`. -/
theorem rtResultant_eval_eq_zero_iff [IsAlgClosed K] (A D : K[X]) (hD : D.Separable) (a : K)
    (hdeg : (A - C a * derivative D).natDegree = D.natDegree - 1) :
    (rtResultant A D).eval a = 0 ↔ ∃ α, D.IsRoot α ∧ A.eval α / (derivative D).eval α = a := by
  rw [rtResultant_eval, ← hdeg, ← residue_iff_resultant_eq_zero A D hD a]

/-! ## §2.3 The Horowitz–Ostrogradsky algorithm (denominator split)
The algorithm writes `∫ A/D = B/D⁻ + ∫ C/D*` with `D⁻ = gcd(D, D')` and `D* = D/D⁻` the squarefree
part (radical) of `D`; `B, C` then come from a linear system. Here is the functional denominator
split with its two structural correctness facts: `D⁻·D* = D` and `D*` squarefree. -/

open Classical in
/-- **Horowitz–Ostrogradsky denominator split** (§2.3): `(D⁻, D*) = (gcd(D, D'), D/gcd(D, D'))`. -/
noncomputable def hoSplit (D : K[X]) : K[X] × K[X] :=
  (gcd D (derivative D), D / gcd D (derivative D))

open Classical in
/-- `gcd(D, D') ≠ 0` for `D ≠ 0`. -/
private theorem gcd_derivative_ne_zero {D : K[X]} (hD : D ≠ 0) : gcd D (derivative D) ≠ 0 :=
  fun h => hD (zero_dvd_iff.mp (h ▸ gcd_dvd_left D (derivative D)))

open Classical in
/-- **`D⁻·D* = D`**: the Horowitz–Ostrogradsky split factors `D` (since `gcd(D, D') ∣ D`). -/
theorem hoSplit_mul (D : K[X]) (hD : D ≠ 0) : (hoSplit D).1 * (hoSplit D).2 = D :=
  EuclideanDomain.mul_div_cancel' (gcd_derivative_ne_zero hD) (gcd_dvd_left _ _)

open Classical in
/-- **`D*` is squarefree** (§2.3): over a characteristic-`0` field, `D* = D/gcd(D, D')` is the radical
of `D`. Via the §1.6 deflation theory (`squarefreePart_mul_deflation`, `deflation_one_eq_gcd`) it is
associated to `squarefreePart D = radical D`, which is squarefree (`squarefree_radical`). -/
theorem hoSplit_snd_squarefree [CharZero K] (D : K[X]) (hD : D ≠ 0) :
    Squarefree (hoSplit D).2 := by
  have hprim : D.IsPrimitive := (isPrimitive_iff_ne_zero D).mpr hD
  have hpp : D.primPart = D := by
    have h := eq_C_content_mul_primPart D
    rw [hprim.content_eq_one, map_one, one_mul] at h; exact h.symm
  have hppne : D.primPart ≠ 0 := by rw [hpp]; exact hD
  have hmul : gcd D (derivative D) * (hoSplit D).2 = D := hoSplit_mul D hD
  have h1 : Associated (squarefreePart D * deflation D 1) D := by
    have := squarefreePart_mul_deflation D hppne; rwa [hpp] at this
  have h2 : Associated (gcd D (derivative D)) (deflation D 1) := by
    have := deflation_one_eq_gcd D hppne; rwa [hpp] at this
  -- cancel the common factor gcd ~ deflation to get D* ~ squarefreePart
  have hcomb : Associated (gcd D (derivative D) * (hoSplit D).2)
      (deflation D 1 * squarefreePart D) := by
    rw [hmul, mul_comm (deflation D 1) (squarefreePart D)]; exact h1.symm
  have hAD : Associated (hoSplit D).2 (squarefreePart D) :=
    Associated.of_mul_left hcomb h2 (gcd_derivative_ne_zero hD)
  have hsqfp : squarefreePart D = UniqueFactorizationMonoid.radical D := by
    unfold squarefreePart UniqueFactorizationMonoid.radical UniqueFactorizationMonoid.primeFactors
    rw [hpp]; congr!
  rw [hAD.squarefree_iff, hsqfp]
  exact UniqueFactorizationMonoid.squarefree_radical

end DeepWiki.SymbolicIntegration
