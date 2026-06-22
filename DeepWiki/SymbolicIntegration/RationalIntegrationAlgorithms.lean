import DeepWiki.SymbolicIntegration.RationalIntegration
import DeepWiki.SymbolicIntegration.RationalFunctionDerivative
import DeepWiki.SymbolicIntegration.Residues
import DeepWiki.SymbolicIntegration.SquarefreeFactorization
import DeepWiki.SymbolicIntegration.Subresultants
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

/-- **Rothstein–Trager resultant as a product over the roots of `D`** (Bronstein §1.4, Thm 1.4.1
specialized at `t = a`): over an algebraically closed field, for `deg A < deg D`,
`R(a) = lc(D)^{deg D − 1} · ∏_{α : D(α)=0} (A(α) − a·D'(α))`. This is `rtResultant_eval` composed with
Mathlib's `resultant_eq_prod_eval` (the resultant of a split polynomial as a product of the other's
evaluations at the roots); the degree bound `deg(A − a·D') ≤ deg D − 1` holds since `deg A < deg D` and
`deg D' ≤ deg D − 1`. This is the formula whose root `a` of multiplicity `i` matches `deg gcd(D, A−aD') = i`
(the residue-multiplicity count behind Theorem 2.5.1). -/
theorem rtResultant_eval_eq_prod_roots [IsAlgClosed K] (A D : K[X]) (a : K)
    (hA : A.natDegree < D.natDegree) :
    (rtResultant A D).eval a
      = D.leadingCoeff ^ (D.natDegree - 1) *
        (D.roots.map (fun α => A.eval α - a * (derivative D).eval α)).prod := by
  have hg : (A - C a * derivative D).natDegree ≤ D.natDegree - 1 :=
    (natDegree_sub_le _ _).trans
      (max_le (by omega) ((natDegree_C_mul_le _ _).trans (natDegree_derivative_le D)))
  rw [rtResultant_eval, Polynomial.resultant_eq_prod_eval D (A - C a * derivative D)
    (D.natDegree - 1) hg (IsAlgClosed.splits D)]
  exact congrArg (D.leadingCoeff ^ (D.natDegree - 1) * ·)
    (congrArg Multiset.prod (Multiset.map_congr rfl (fun α _ => by simp [eval_sub, eval_mul, eval_C])))

/-! ## §2.5 The Lazard–Rioboo–Trager algorithm (subresultant primitive)
LRT replaces the per-residue gcd computations of Rothstein–Trager with the *subresultant PRS* of `D` and
`A − t·D'` (in `x`), computed once over `K[t]`. The `j`-th subresultant `Sⱼ(D, A−tD')`, specialized at a
root `a` of `R`, yields `Gₐ = gcd(D, A−aD')` (Theorem 2.5.1, which rests on the §1.4/§1.5 subresultant-PRS
theory). Here is the functional primitive `Sⱼ` and its specialization, the subresultant analog of
`rtResultant`/`rtResultant_eval`. -/

/-- **Lazard–Rioboo–Trager subresultant** `Sⱼ(D, A − t·D') ∈ K[t][x]`: `D, A, D'` lifted to `(K[t])[x]`
(coefficients embedded by `C : K → K[t]`), `t = C X`, and the `j`-th subresultant taken w.r.t. `x` with the
book's formal degrees `deg D` and `deg D − 1`. The remainders of this one PRS replace the Rothstein–Trager
gcds. -/
noncomputable def lrtSubresultant (A D : K[X]) (j : ℕ) : (K[X])[X] :=
  subresultant (D.map (C : K →+* K[X]))
    (A.map (C : K →+* K[X]) - C Polynomial.X * (derivative D).map (C : K →+* K[X]))
    D.natDegree (D.natDegree - 1) j

/-- **Specialization of `lrtSubresultant`**: mapping the `K[t]`-coefficients by `t ↦ a` recovers the
parameter subresultant `Sⱼ(D, A − a·D')` over `K` — `subresultant_map` for the coefficient evaluation
`K[t] → K`, since `(C·)` then `eval a` is the identity on `K`. By Theorem 2.5.1 this equals `gcd(D, A−aD')`
up to its leading coefficient. -/
theorem lrtSubresultant_eval (A D : K[X]) (a : K) (j : ℕ) :
    (lrtSubresultant A D j).map (Polynomial.evalRingHom a)
      = subresultant D (A - C a * derivative D) D.natDegree (D.natDegree - 1) j := by
  have hcomp : (Polynomial.evalRingHom a).comp (C : K →+* K[X]) = RingHom.id K := by ext k; simp
  rw [lrtSubresultant, ← subresultant_map]
  congr 1
  · rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  · simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_C, hcomp,
      Polynomial.map_id]
    simp

open Classical in
/-- **Lazard–Rioboo–Trager algorithm** (§2.5, p.51, `IntRationalLogPart`): the functional log-part
computation, returning the list of pairs `(Qᵢ, Sᵢ)` whose meaning is the logarithmic part
`∫ A/D = ∑ᵢ ∑_{a : Qᵢ(a)=0} a·log(Sᵢ(a,x))`. The `Qᵢ` are the squarefree-factorization parts of the
Rothstein–Trager resultant `R = resultant_x(D, A−tD')` (so `Qᵢ` collects the residues of multiplicity `i`
in `R`); for each `i` with `deg Qᵢ > 0`, `Sᵢ = D` if `i = deg D`, else the `i`-th subresultant
`lrtSubresultant A D i` (of `x`-degree `i`). The book's optional `lcₓ`-normalization (making the
logarithms monic) is omitted — the un-normalized output is equally a valid antiderivative. -/
noncomputable def lazardRiobooTrager (A D : K[X]) : List (K[X] × (K[X])[X]) :=
  (squarefreeFactorization (rtResultant A D)).zipIdx.filterMap fun p =>
    let i := p.2 + 1
    if p.1.natDegree = 0 then none
    else some (p.1, if i = D.natDegree then D.map (C : K →+* K[X]) else lrtSubresultant A D i)

open scoped Differential in
/-- **Hermite reduction step in `K(x)`** (§2.2): the integral-lowering identity for a rational
function, now a theorem *about rational functions* (using `K(x) = RatFunc K`'s differential structure).
If `B·V' + Cc·V = A` (the Bézout data the algorithm finds, e.g. from `diophantineSolve`), then writing
`k = m+2`, `∫ (1−k)A/Vᵏ = B/Vᵏ⁻¹ + ∫ ((1−k)Cc − B')/Vᵏ⁻¹` — the integrand's denominator power drops by
one. Obtained by applying the abstract `hermite_reduction_step` to the `algebraMap` images in `RatFunc K`
(`d/dx` on the images is `Polynomial.derivative` by `ratFuncDeriv_algebraMap`). -/
theorem hermiteReduce_step_ratFunc {A B Cc V : K[X]} (hV : V ≠ 0) (m : ℕ)
    (hrel : B * derivative V + Cc * V = A) :
    (-((m : RatFunc K) + 1) * algebraMap K[X] (RatFunc K) A)
        / algebraMap K[X] (RatFunc K) V ^ (m + 2)
      = (algebraMap K[X] (RatFunc K) B / algebraMap K[X] (RatFunc K) V ^ (m + 1))′
        + (-((m : RatFunc K) + 1) * algebraMap K[X] (RatFunc K) Cc
            - algebraMap K[X] (RatFunc K) (derivative B))
          / algebraMap K[X] (RatFunc K) V ^ (m + 1) := by
  have hv : algebraMap K[X] (RatFunc K) V ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hV
  have key := hermite_reduction_step (algebraMap K[X] (RatFunc K) B)
    (algebraMap K[X] (RatFunc K) Cc) (algebraMap K[X] (RatFunc K) V) hv m
  rw [show (algebraMap K[X] (RatFunc K) V)′ = algebraMap K[X] (RatFunc K) (derivative V) from
        ratFuncDeriv_algebraMap V,
      show (algebraMap K[X] (RatFunc K) B)′ = algebraMap K[X] (RatFunc K) (derivative B) from
        ratFuncDeriv_algebraMap B,
      ← map_mul, ← map_mul, ← map_add, hrel] at key
  exact key

open Classical in
/-- **Hermite reduction — the prime-power inner loop** (§2.2): iterate `hermiteReduce_step_ratFunc`
to reduce an integrand `A/Vᵏ` (with `V` squarefree) to `g + r/V`, lowering the denominator power one
step at a time. Returns `(g, r)` with `g ∈ K(x)` the accumulated rational part and `r ∈ K[X]` the
final numerator over the squarefree `V`. At power `k = m+2` it solves `B·V' + Cc·V = -A/(m+1)` (Bézout,
`diophantineSolve`, since `V ⊥ V'`), emits `B/Vᵐ⁺¹` into `g`, and recurses on `-(m+1)·Cc − B'` over
`Vᵐ⁺¹`. -/
noncomputable def hermiteReducePower (V : K[X]) : ℕ → K[X] → RatFunc K × K[X]
  | 0,     A => (0, A)
  | 1,     A => (0, A)
  | (m+2), A =>
      let c : K[X] := -A * Polynomial.C (((m : K) + 1)⁻¹)
      let B : K[X] := (diophantineSolve (derivative V) V c).1
      let Cc : K[X] := (diophantineSolve (derivative V) V c).2
      let r : K[X] := -(Polynomial.C ((m : K) + 1)) * Cc - derivative B
      (algebraMap K[X] (RatFunc K) B / algebraMap K[X] (RatFunc K) V ^ (m + 1)
          + (hermiteReducePower V (m + 1) r).1,
       (hermiteReducePower V (m + 1) r).2)

open scoped Differential in
open Classical in
/-- **Correctness of `hermiteReducePower`** (§2.2): for squarefree `V` over a characteristic-`0` field
and any power `k ≥ 1`, the integrand splits as `A/Vᵏ = g' + r/V` where `(g, r) = hermiteReducePower V k A`
— i.e. `∫ A/Vᵏ = g + ∫ r/V`, the rational part `g` extracted and the remaining integral having the
squarefree denominator `V`. Proven by induction on `k`, each step the `hermiteReduce_step_ratFunc`
identity glued to the recursive tail. -/
theorem hermiteReducePower_spec [CharZero K] (V : K[X]) (hV : Squarefree V) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (A : K[X]),
      algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) V ^ k
        = ((hermiteReducePower V k A).1)′
          + algebraMap K[X] (RatFunc K) (hermiteReducePower V k A).2
            / algebraMap K[X] (RatFunc K) V := by
  have hV0 : V ≠ 0 := hV.ne_zero
  have hcop : IsCoprime (derivative V) V := (squarefree_iff_isCoprime_derivative.mp hV).symm
  have e1 : ∀ k : K, algebraMap K[X] (RatFunc K) (Polynomial.C k) = algebraMap K (RatFunc K) k := by
    intro k
    rw [← Polynomial.algebraMap_eq]
    exact (IsScalarTower.algebraMap_apply K K[X] (RatFunc K) k).symm
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro hk A
    obtain _ | _ | m := k
    · exact absurd hk (by norm_num)
    · simp only [hermiteReducePower, pow_one, map_zero, zero_add]
    · have hm1 : ((m : K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
      have hc1 : algebraMap K (RatFunc K) ((m : K) + 1) = (m : RatFunc K) + 1 := by
        rw [map_add, map_natCast, map_one]
      simp only [hermiteReducePower]
      set c : K[X] := -A * Polynomial.C (((m : K) + 1)⁻¹) with hc
      set B : K[X] := (diophantineSolve (derivative V) V c).1 with hB
      set Cc : K[X] := (diophantineSolve (derivative V) V c).2 with hCc
      set r : K[X] := -(Polynomial.C ((m : K) + 1)) * Cc - derivative B with hr
      have hrel : B * derivative V + Cc * V = c := by
        have h := diophantineSolve_spec hcop c
        rw [hB, hCc]; linear_combination h
      have hkey : algebraMap K (RatFunc K) ((m : K) + 1)
          * algebraMap K (RatFunc K) (((m : K) + 1)⁻¹) = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hm1, map_one]
      have hcoef : -((m : RatFunc K) + 1) * algebraMap K[X] (RatFunc K) c
          = algebraMap K[X] (RatFunc K) A := by
        rw [hc, map_mul, map_neg, e1, ← hc1]
        linear_combination (algebraMap K[X] (RatFunc K) A) * hkey
      have hnum : -((m : RatFunc K) + 1) * algebraMap K[X] (RatFunc K) Cc
            - algebraMap K[X] (RatFunc K) (derivative B)
          = algebraMap K[X] (RatFunc K) r := by
        rw [hr]; simp only [map_sub, map_mul, map_neg, e1, hc1]
      have key := hermiteReduce_step_ratFunc hV0 m hrel
      rw [hcoef, hnum] at key
      have IHr := IH (m + 1) (by omega) (by omega) r
      rw [map_add,
        add_assoc (algebraMap K[X] (RatFunc K) B / algebraMap K[X] (RatFunc K) V ^ (m + 1))′,
        ← IHr]
      exact key

open Classical in
/-- **Two-factor partial fraction in `K(x)`** (§2.2/§2.5, the coprime split): for coprime `P, Q` (both
nonzero) and any numerator `A`, `A/(P·Q) = B/Q + C/P` where `(B, C) = diophantineSolve P Q A` solves the
Bézout relation `P·B + Q·C = A`. This is the inductive building block of the multi-factor partial-fraction
decomposition across a squarefree factorization `D = ∏ᵢ Dᵢ^i` (each `Dᵢ^i` pairwise coprime), which feeds
the prime-power Hermite loop `hermiteReducePower` on each factor. -/
theorem ratFunc_partialFraction_coprime {P Q A : K[X]} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hPQ : IsCoprime P Q) :
    algebraMap K[X] (RatFunc K) A
        / (algebraMap K[X] (RatFunc K) P * algebraMap K[X] (RatFunc K) Q)
      = algebraMap K[X] (RatFunc K) (diophantineSolve P Q A).1 / algebraMap K[X] (RatFunc K) Q
        + algebraMap K[X] (RatFunc K) (diophantineSolve P Q A).2 / algebraMap K[X] (RatFunc K) P := by
  have hp : algebraMap K[X] (RatFunc K) P ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hP
  have hq : algebraMap K[X] (RatFunc K) Q ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hQ
  have hspec : algebraMap K[X] (RatFunc K) A
      = algebraMap K[X] (RatFunc K) P * algebraMap K[X] (RatFunc K) (diophantineSolve P Q A).1
        + algebraMap K[X] (RatFunc K) Q * algebraMap K[X] (RatFunc K) (diophantineSolve P Q A).2 := by
    rw [← map_mul, ← map_mul, ← map_add, diophantineSolve_spec hPQ A]
  rw [hspec]; field_simp

open Classical in
/-- **Multi-factor partial fraction in `K(x)`** (§2.2, the full coprime decomposition): for a nonempty
finite family of pairwise-coprime nonzero factors `P i` (`i ∈ s`), `A/∏ᵢ Pᵢ = ∑ᵢ Bᵢ/Pᵢ` for some
numerators `B i` — obtained by iterating the two-factor split `ratFunc_partialFraction_coprime` down the
family. Specializing `s` to the prime powers `Dᵢ^i` of a squarefree factorization `D = ∏ Dᵢ^i` (pairwise
coprime) decomposes `A/D` into per-prime-power pieces, each then reduced by `hermiteReducePower`. -/
theorem ratFunc_partialFraction_prod {ι : Type*} (P : ι → K[X]) :
    ∀ (s : Finset ι), s.Nonempty → (∀ i ∈ s, P i ≠ 0) →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (P i) (P j)) → ∀ (A : K[X]),
      ∃ B : ι → K[X],
        algebraMap K[X] (RatFunc K) A / ∏ i ∈ s, algebraMap K[X] (RatFunc K) (P i)
          = ∑ i ∈ s, algebraMap K[X] (RatFunc K) (B i) / algebraMap K[X] (RatFunc K) (P i) := by
  intro s hs
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => exact fun _ _ A => ⟨fun _ => A, by simp⟩
  | cons a s ha hs ih =>
      intro hP hcop A
      have hmem : ∀ i ∈ s, i ∈ Finset.cons a s ha := fun i hi => Finset.mem_cons.mpr (Or.inr hi)
      have hPa : P a ≠ 0 := hP a (Finset.mem_cons_self a s)
      have hP' : ∀ i ∈ s, P i ≠ 0 := fun i hi => hP i (hmem i hi)
      have hcop' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (P i) (P j) :=
        fun i hi j hj hij => hcop i (hmem i hi) j (hmem j hj) hij
      have hQ0 : (∏ i ∈ s, P i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hP'
      have hcopaQ : IsCoprime (P a) (∏ i ∈ s, P i) :=
        IsCoprime.prod_right fun i hi =>
          hcop a (Finset.mem_cons_self a s) i (hmem i hi) (by rintro rfl; exact ha hi)
      obtain ⟨B', hB'⟩ := ih hP' hcop' (diophantineSolve (P a) (∏ i ∈ s, P i) A).1
      refine ⟨fun i => if i = a then (diophantineSolve (P a) (∏ i ∈ s, P i) A).2 else B' i, ?_⟩
      have hsplit := ratFunc_partialFraction_coprime (A := A) hPa hQ0 hcopaQ
      rw [map_prod] at hsplit
      have hsumeq : (∑ i ∈ s, algebraMap K[X] (RatFunc K)
            (if i = a then (diophantineSolve (P a) (∏ i ∈ s, P i) A).2 else B' i)
            / algebraMap K[X] (RatFunc K) (P i))
          = ∑ i ∈ s, algebraMap K[X] (RatFunc K) (B' i) / algebraMap K[X] (RatFunc K) (P i) :=
        Finset.sum_congr rfl fun i hi => by
          rw [if_neg (fun (h : i = a) => ha (h ▸ hi))]
      rw [Finset.prod_cons, Finset.sum_cons]
      dsimp only
      rw [hsumeq, if_pos rfl, hsplit, hB', add_comm]

open scoped Differential in
open Classical in
/-- **Hermite reduction of a full partial-fraction sum** (§2.2, the outer reduction): for a family of
squarefree factors `D i` with multiplicities `e i ≥ 1` (char 0), the sum of prime-power fractions reduces
as `∑ᵢ Aᵢ/Dᵢ^{eᵢ} = (∑ᵢ gᵢ)′ + ∑ᵢ rᵢ/Dᵢ` where `(gᵢ, rᵢ) = hermiteReducePower Dᵢ eᵢ Aᵢ` — i.e.
`∫ ∑ᵢ Aᵢ/Dᵢ^{eᵢ} = ∑ᵢ gᵢ + ∫ ∑ᵢ rᵢ/Dᵢ`, the rational part collected and the remaining integrand having
squarefree denominators. Composing with `ratFunc_partialFraction_prod` (which produces the `Aᵢ` from a
single `A/D`, `D = ∏ Dᵢ^{eᵢ}`) is the complete Hermite reduction. -/
theorem hermiteReduce_sum_spec [CharZero K] {ι : Type*} (s : Finset ι) (D : ι → K[X])
    (e : ι → ℕ) (A : ι → K[X]) (hD : ∀ i ∈ s, Squarefree (D i)) (he : ∀ i ∈ s, 1 ≤ e i) :
    ∑ i ∈ s, algebraMap K[X] (RatFunc K) (A i) / algebraMap K[X] (RatFunc K) (D i) ^ e i
      = (∑ i ∈ s, (hermiteReducePower (D i) (e i) (A i)).1)′
        + ∑ i ∈ s, algebraMap K[X] (RatFunc K) (hermiteReducePower (D i) (e i) (A i)).2
            / algebraMap K[X] (RatFunc K) (D i) := by
  rw [map_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i hi =>
    hermiteReducePower_spec (D i) (hD i hi) (e i) (he i hi) (A i)

open scoped Differential in
open Classical in
/-- **Hermite reduction — complete outer algorithm** (§2.2): for a single proper fraction `A/D` whose
denominator has squarefree factorization `D = ∏ᵢ Dᵢ^{eᵢ}` (the `Dᵢ` squarefree, pairwise coprime,
`eᵢ ≥ 1`, char 0), there is a rational part `g` and numerators `rᵢ` with
`A/D = g′ + ∑ᵢ rᵢ/Dᵢ` — i.e. `∫ A/D = g + ∫ ∑ᵢ rᵢ/Dᵢ`, the remaining integrand having squarefree
denominators. Composes `ratFunc_partialFraction_prod` (decompose `A/D` into `∑ Bᵢ/Dᵢ^{eᵢ}`) with
`hermiteReduce_sum_spec` (reduce each prime power). -/
theorem hermiteReduce_full [CharZero K] {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (D : ι → K[X]) (e : ι → ℕ) (hD : ∀ i ∈ s, Squarefree (D i)) (he : ∀ i ∈ s, 1 ≤ e i)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (D i) (D j)) (A : K[X]) :
    ∃ (g : RatFunc K) (r : ι → K[X]),
      algebraMap K[X] (RatFunc K) A / ∏ i ∈ s, algebraMap K[X] (RatFunc K) (D i) ^ e i
        = g′ + ∑ i ∈ s, algebraMap K[X] (RatFunc K) (r i) / algebraMap K[X] (RatFunc K) (D i) := by
  obtain ⟨B, hB⟩ := ratFunc_partialFraction_prod (fun i => D i ^ e i) s hs
    (fun i hi => pow_ne_zero _ (hD i hi).ne_zero)
    (fun i hi j hj hij => (hcop i hi j hj hij).pow) A
  simp only [map_pow] at hB
  exact ⟨_, _, hB.trans (hermiteReduce_sum_spec s D e B hD he)⟩

/-! ## §2.5 The polynomial part of `IntegrateRationalFunction` (`∫ Q dx`)
The top-level algorithm splits `∫ A/D` into a rational part (Hermite), a polynomial part `∫ Q dx`
(`Q` from polynomial division), and a logarithmic part (LRT). Here is the polynomial antiderivative
`∫ Q dx` — missing from Mathlib — with its correctness `derivative (polyIntegral Q) = Q`. -/

/-- **Polynomial antiderivative** (§2.5, the `∫ Q dx` piece of `IntegrateRationalFunction`):
`∫ (∑ₙ aₙ xⁿ) dx = ∑ₙ (aₙ/(n+1))·xⁿ⁺¹`, the term-by-term antiderivative of a polynomial. -/
noncomputable def polyIntegral (Q : K[X]) : K[X] :=
  Q.sum fun n a => C (a / ((n : K) + 1)) * X ^ (n + 1)

/-- **Correctness of `polyIntegral`** (§2.5): over a characteristic-`0` field,
`d/dx (∫ Q dx) = Q` — `polyIntegral` is a genuine antiderivative of `Q`. Each term's derivative is
`C ((a/(n+1))·(n+1)) · Xⁿ = C a · Xⁿ` (`(n+1 : K) ≠ 0` in char `0`); summing reassembles `Q` via
`sum_C_mul_X_pow_eq`. -/
theorem polyIntegral_derivative [CharZero K] (Q : K[X]) : derivative (polyIntegral Q) = Q := by
  rw [polyIntegral, Polynomial.sum_def, derivative_sum]
  rw [show (∑ n ∈ Q.support, derivative (C (Q.coeff n / ((n : K) + 1)) * X ^ (n + 1)))
        = ∑ n ∈ Q.support, C (Q.coeff n) * X ^ n from Finset.sum_congr rfl fun n _ => ?_]
  · conv_rhs => rw [← Polynomial.sum_C_mul_X_pow_eq Q, Polynomial.sum_def]
  · rw [derivative_C_mul_X_pow, Nat.add_sub_cancel]
    have hn1 : ((n + 1 : ℕ) : K) = (n : K) + 1 := by push_cast; ring
    rw [hn1, div_mul_cancel₀ _ (by exact_mod_cast Nat.succ_ne_zero n)]

-- `∫ Q dx` is a genuine antiderivative of `Q`.
example [CharZero K] (Q : K[X]) : derivative (polyIntegral Q) = Q := polyIntegral_derivative Q

/-- **Polynomial-division split in `K(x)`** (§2.5, the `PolyDivide` step of `IntegrateRationalFunction`):
for `Den ≠ 0`, `A/Den = (A / Den) + (A % Den)/Den` in `K(x)` — the improper fraction `A/Den` splits into
its polynomial quotient `Q = A / Den` and the proper remainder fraction `(A % Den)/Den`
(Euclidean `div_add_mod`). -/
theorem ratFunc_polyDivide_split (A Den : K[X]) (hDen : Den ≠ 0) :
    algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) Den
      = algebraMap K[X] (RatFunc K) (A / Den)
        + algebraMap K[X] (RatFunc K) (A % Den) / algebraMap K[X] (RatFunc K) Den := by
  have hd : algebraMap K[X] (RatFunc K) Den ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hDen
  have hAeq : algebraMap K[X] (RatFunc K) A
      = algebraMap K[X] (RatFunc K) Den * algebraMap K[X] (RatFunc K) (A / Den)
        + algebraMap K[X] (RatFunc K) (A % Den) := by
    rw [← map_mul, ← map_add, EuclideanDomain.div_add_mod]
  rw [hAeq]; field_simp

open scoped Differential in
open Classical in
/-- **`IntegrateRationalFunction` reduction** (§2.5, p.52): for a numerator `A` and a denominator given
in squarefree-factored form `Den = ∏ᵢ Dᵢ^{eᵢ}` (`Dᵢ` squarefree, pairwise coprime, `eᵢ ≥ 1`, char `0`),
the integrand `A/Den` reduces to a rational derivative `g′`, the derivative of a polynomial integral
`(∫ p dx)′ = (polyIntegral p)′`, and a sum of proper fractions with squarefree denominators `∑ᵢ rᵢ/Dᵢ`:
`A/Den = g′ + (polyIntegral p)′ + ∑ᵢ rᵢ/Dᵢ`, i.e. `∫ A/Den = g + ∫ p dx + ∫ ∑ᵢ rᵢ/Dᵢ`. Assembles
`ratFunc_polyDivide_split` (PolyDivide → polynomial part `p = (A % Den)/Den` quotient + proper remainder),
`polyIntegral`/`polyIntegral_derivative` (`∫ p dx`), and `hermiteReduce_full` (the proper remainder's
rational + squarefree-denominator split). The residual `∑ᵢ rᵢ/Dᵢ` is the `IntRationalLogPart` input. -/
theorem integrateRationalFunction_reduction [CharZero K] {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (D : ι → K[X]) (e : ι → ℕ) (hD : ∀ i ∈ s, Squarefree (D i)) (he : ∀ i ∈ s, 1 ≤ e i)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (D i) (D j)) (A : K[X]) :
    ∃ (g : RatFunc K) (p : K[X]) (r : ι → K[X]),
      algebraMap K[X] (RatFunc K) A / ∏ i ∈ s, algebraMap K[X] (RatFunc K) (D i) ^ e i
        = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
          + ∑ i ∈ s, algebraMap K[X] (RatFunc K) (r i) / algebraMap K[X] (RatFunc K) (D i) := by
  set Den : K[X] := ∏ i ∈ s, D i ^ e i with hDen
  have hDenne : Den ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hD i hi).ne_zero
  have hDenmap : (∏ i ∈ s, algebraMap K[X] (RatFunc K) (D i) ^ e i)
      = algebraMap K[X] (RatFunc K) Den := by
    rw [hDen, map_prod]; exact Finset.prod_congr rfl fun i _ => (map_pow _ _ _).symm
  -- PolyDivide: split off the polynomial quotient `A / Den`.
  rw [hDenmap, ratFunc_polyDivide_split A Den hDenne]
  -- Hermite-reduce the proper remainder `(A % Den) / Den`.
  obtain ⟨g, r, hg⟩ := hermiteReduce_full s hs D e hD he hcop (A % Den)
  rw [← hDenmap, hg]
  -- The polynomial quotient integrates to `polyIntegral (A / Den)`.
  refine ⟨g, A / Den, r, ?_⟩
  have hpi : (algebraMap K[X] (RatFunc K) (polyIntegral (A / Den)))′
      = algebraMap K[X] (RatFunc K) (A / Den) := by
    show ratFuncDeriv _ = _
    rw [ratFuncDeriv_algebraMap (polyIntegral (A / Den)), polyIntegral_derivative]
  rw [hpi]; ring

open scoped Differential in
open Classical in
-- `∫ A/Den` reduces to a rational part, a polynomial-integral part, and a squarefree-denominator sum.
example [CharZero K] {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (D : ι → K[X]) (e : ι → ℕ)
    (hD : ∀ i ∈ s, Squarefree (D i)) (he : ∀ i ∈ s, 1 ≤ e i)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (D i) (D j)) (A : K[X]) :
    ∃ (g : RatFunc K) (p : K[X]) (r : ι → K[X]),
      algebraMap K[X] (RatFunc K) A / ∏ i ∈ s, algebraMap K[X] (RatFunc K) (D i) ^ e i
        = g′ + (algebraMap K[X] (RatFunc K) (polyIntegral p))′
          + ∑ i ∈ s, algebraMap K[X] (RatFunc K) (r i) / algebraMap K[X] (RatFunc K) (D i) :=
  integrateRationalFunction_reduction s hs D e hD he hcop A

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

open Classical in
/-- **Key divisibility for Horowitz–Ostrogradsky** (§2.3): `D⁻ = gcd(D, D')` divides `D⁻′·D*` where
`D* = D/D⁻`. (From `D' = D⁻′·D* + D⁻·D*'` and `D⁻ ∣ D'`, so `D⁻ ∣ D' − D⁻·D*' = D⁻′·D*`.) This is what
makes the Horowitz polynomial `E := D⁻′·D*/D⁻` exist, so the reduction stays inside `K[X]`. -/
theorem hoSplit_fst_dvd_deriv_mul_snd (D : K[X]) (hD : D ≠ 0) :
    (hoSplit D).1 ∣ derivative (hoSplit D).1 * (hoSplit D).2 := by
  have hmul : (hoSplit D).1 * (hoSplit D).2 = D := hoSplit_mul D hD
  have hderiv : derivative D
      = derivative (hoSplit D).1 * (hoSplit D).2 + (hoSplit D).1 * derivative (hoSplit D).2 := by
    conv_lhs => rw [← hmul]
    rw [derivative_mul]
  have hdvdD' : (hoSplit D).1 ∣ derivative D := gcd_dvd_right D (derivative D)
  have key : (hoSplit D).1 ∣ derivative D - (hoSplit D).1 * derivative (hoSplit D).2 :=
    dvd_sub hdvdD' (dvd_mul_right _ _)
  rwa [hderiv, add_sub_cancel_right] at key

open scoped Differential in
/-- **Horowitz–Ostrogradsky reduction step in `K(x)`** (§2.3): the polynomial-level integral identity.
For a split `D = D⁻·D*` with the Horowitz polynomial `E` (`E·D⁻ = D⁻′·D*`) and numerator data
`B′·D* − B·E + C·D⁻ = A`, `A/(D⁻·D*) = (B/D⁻)′ + C/D*` in `K(x)`, so `∫ A/D = B/D⁻ + ∫ C/D*`. Obtained
from the abstract `horowitz_reduction_step` on the `algebraMap` images (`d/dx` on them is
`Polynomial.derivative`). The algorithm finds `B, C` (degree-bounded) by a linear system. -/
theorem horowitzReduce_step_ratFunc {A B C Dminus Dstar E : K[X]} (hDm : Dminus ≠ 0) (hDs : Dstar ≠ 0)
    (hE : E * Dminus = derivative Dminus * Dstar)
    (hA : derivative B * Dstar - B * E + C * Dminus = A) :
    algebraMap K[X] (RatFunc K) A
        / (algebraMap K[X] (RatFunc K) Dminus * algebraMap K[X] (RatFunc K) Dstar)
      = (algebraMap K[X] (RatFunc K) B / algebraMap K[X] (RatFunc K) Dminus)′
        + algebraMap K[X] (RatFunc K) C / algebraMap K[X] (RatFunc K) Dstar := by
  have hm : algebraMap K[X] (RatFunc K) Dminus ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hDm
  have hs : algebraMap K[X] (RatFunc K) Dstar ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hDs
  have hE' : algebraMap K[X] (RatFunc K) E * algebraMap K[X] (RatFunc K) Dminus
      = (algebraMap K[X] (RatFunc K) Dminus)′ * algebraMap K[X] (RatFunc K) Dstar := by
    rw [show (algebraMap K[X] (RatFunc K) Dminus)′
          = algebraMap K[X] (RatFunc K) (derivative Dminus) from ratFuncDeriv_algebraMap Dminus,
        ← map_mul, ← map_mul, hE]
  have key := horowitz_reduction_step (algebraMap K[X] (RatFunc K) B) (algebraMap K[X] (RatFunc K) C)
    (algebraMap K[X] (RatFunc K) Dminus) (algebraMap K[X] (RatFunc K) Dstar)
    (algebraMap K[X] (RatFunc K) E) hm hs hE'
  have hnum : (algebraMap K[X] (RatFunc K) B)′ * algebraMap K[X] (RatFunc K) Dstar
        - algebraMap K[X] (RatFunc K) B * algebraMap K[X] (RatFunc K) E
        + algebraMap K[X] (RatFunc K) C * algebraMap K[X] (RatFunc K) Dminus
      = algebraMap K[X] (RatFunc K) A := by
    rw [show (algebraMap K[X] (RatFunc K) B)′
          = algebraMap K[X] (RatFunc K) (derivative B) from ratFuncDeriv_algebraMap B,
        ← map_mul, ← map_mul, ← map_mul, ← map_sub, ← map_add, hA]
  rw [hnum] at key
  exact key

end DeepWiki.SymbolicIntegration
