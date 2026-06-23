import DeepWiki.SymbolicIntegration.PartialFraction
import DeepWiki.SymbolicIntegration.Residues
import DeepWiki.SymbolicIntegration.ResidueMultiplicity

/-! # Recognizing logarithmic derivatives (Bronstein §2.9)
For `f = A/D ∈ K(x)` with `D` squarefree, `deg A < deg D`, `gcd(A, D) = 1`, the criterion of §2.9
(Mařík): `f` is the logarithmic derivative of a rational function — `∃ u ∈ K(x)*, f = logDeriv u` —
**iff** all the residues `A(α)/D'(α)` (the roots of the Rothstein–Trager resultant, by
`roots_rtResultant`) are integers (lie in the image of `ℤ → K`). The reachable substance is the
`⟸` direction: grouping the simple-root residue decomposition `ratFunc_eq_sum_residue_grouped` by
residue value, each integer residue `nₐ` turns the grouped factor `Gₐ = ∏_{res α = a}(X−α)` into a
power `Gₐ^{nₐ}`, so `A/D = logDeriv(∏ₐ Gₐ^{nₐ}) = logDeriv u` with `u` the explicit `zpow`-product. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

variable {K : Type*} [Field K]

open scoped Classical in
open scoped Differential in
/-- The constant residue `C a` as a rational function equals the integer scalar `(n : K(x))` when
`a = (n : K)`: `algebraMap K[X] (RatFunc K) (C (n : K)) = (n : RatFunc K)`. -/
theorem algebraMap_C_intCast (n : ℤ) :
    algebraMap K[X] (RatFunc K) (C (n : K)) = (n : RatFunc K) := by
  rw [show (C (n : K)) = ((n : K[X])) from by simp, map_intCast]

open scoped Classical in
open scoped Differential in
/-- The explicit logarithmic-derivative witness `u = ∏ₐ Gₐ^{nₐ}` for the §2.9 criterion: the product,
over the distinct residue values `a` of `A/D`, of the Rothstein–Trager factor
`Ḡₐ = algebraMap(∏_{res α = a}(X − α))` raised to the integer `nₐ` chosen for that residue. Nonzero
(a `zpow`-product of nonzero polynomials), it satisfies `A/D = logDeriv u` (`logDeriv_intResidues_witness`). -/
noncomputable def intResiduesWitness (s : Finset K) (A : K[X]) (n : K → ℤ) : RatFunc K :=
  ∏ a ∈ s.image (fun α => A.eval α / eval α (derivative (Lagrange.nodal s id))),
    (algebraMap K[X] (RatFunc K)
        (∏ α ∈ s.filter (fun α => A.eval α / eval α (derivative (Lagrange.nodal s id)) = a),
          (X - C α))) ^ n a

open scoped Classical in
/-- The witness `intResiduesWitness s A n` is nonzero — a `zpow`-product of nonzero `Ḡₐ`. -/
theorem intResiduesWitness_ne_zero (s : Finset K) (A : K[X]) (n : K → ℤ) :
    intResiduesWitness s A n ≠ 0 := by
  rw [intResiduesWitness]
  refine Finset.prod_ne_zero_iff.mpr fun a _ => zpow_ne_zero _ ?_
  refine (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr ?_
  exact Finset.prod_ne_zero_iff.mpr fun α _ => X_sub_C_ne_zero α

open scoped Classical in
open scoped Differential in
/-- **Recognizing logarithmic derivatives, `⟸` direction** (Bronstein §2.9, p.72): if every residue
`a = A(α)/D'(α)` of `A/D` is an integer in `K` (witnessed by `n a : ℤ` with `(n a : K) = a`), then
`A/D = logDeriv u` with `u = ∏ₐ Gₐ^{nₐ}` the explicit `intResiduesWitness`. Grouping
`ratFunc_eq_sum_residue_grouped` by residue value, each term `C a · logDeriv(Ḡₐ)` becomes
`(nₐ : K(x)) · logDeriv(Ḡₐ) = logDeriv(Ḡₐ^{nₐ})`; summing is `logDeriv(∏ₐ Ḡₐ^{nₐ})` by
`logDeriv_prod_zpow`. (For `D = ∏_{α∈s}(X−α)` squarefree with roots `s`, `deg A < #s`.) -/
theorem logDeriv_intResiduesWitness (s : Finset K) (A : K[X]) (hA : A.degree < s.card)
    (n : K → ℤ)
    (hn : ∀ α ∈ s, ((n (A.eval α / eval α (derivative (Lagrange.nodal s id))) : K))
      = A.eval α / eval α (derivative (Lagrange.nodal s id))) :
    algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
      = Differential.logDeriv (intResiduesWitness s A n) := by
  set res : K → K := fun α => A.eval α / eval α (derivative (Lagrange.nodal s id)) with hres
  -- nonzero of each grouped factor `Ḡₐ`
  have hGne : ∀ a ∈ s.image res, algebraMap K[X] (RatFunc K)
      (∏ α ∈ s.filter (fun α => res α = a), (X - C α)) ≠ 0 := fun a _ =>
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr
      (Finset.prod_ne_zero_iff.mpr fun α _ => X_sub_C_ne_zero α)
  -- residue values in the image are integers
  have hint : ∀ a ∈ s.image res, ((n a : K)) = a := by
    intro a ha
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp ha
    exact hn α hα
  rw [ratFunc_eq_sum_residue_grouped s A hA, intResiduesWitness, ← hres,
    logDeriv_prod_zpow _ _ _ hGne]
  refine Finset.sum_congr rfl fun a ha => ?_
  congr 1
  rw [← algebraMap_C_intCast (n a), hint a ha]

open scoped Classical in
open scoped Differential in
/-- **Recognizing logarithmic derivatives, `⟸`** (Bronstein §2.9, p.72), existential form: if every
residue `A(α)/D'(α)` of `A/D` is an integer in `K`, then `A/D` is the logarithmic derivative of a
*nonzero* rational function — `∃ u ≠ 0, A/D = logDeriv u`. The witness is `intResiduesWitness`. -/
theorem isLogDeriv_of_integer_residues (s : Finset K) (A : K[X]) (hA : A.degree < s.card)
    (hint : ∀ α ∈ s, ∃ m : ℤ, ((m : K)) = A.eval α / eval α (derivative (Lagrange.nodal s id))) :
    ∃ u : RatFunc K, u ≠ 0 ∧
      algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
        = Differential.logDeriv u := by
  classical
  -- choose an integer exponent for each residue value
  set res : K → K := fun α => A.eval α / eval α (derivative (Lagrange.nodal s id)) with hres
  have hex : ∀ a : K, (∃ α ∈ s, res α = a) → ∃ m : ℤ, ((m : K)) = a := by
    rintro a ⟨α, hα, rfl⟩; exact hint α hα
  let n : K → ℤ := fun a => if h : ∃ α ∈ s, res α = a then (hex a h).choose else 0
  have hn : ∀ α ∈ s, ((n (res α) : K)) = res α := by
    intro α hα
    have h : ∃ β ∈ s, res β = res α := ⟨α, hα, rfl⟩
    simp only [n, dif_pos h]
    exact (hex (res α) h).choose_spec
  refine ⟨intResiduesWitness s A n, intResiduesWitness_ne_zero s A n,
    logDeriv_intResiduesWitness s A hA n hn⟩

open scoped Classical in
open scoped Differential in
-- The `⟸` direction: integer residues give a logarithmic-derivative witness for `A/D`.
example (s : Finset K) (A : K[X]) (hA : A.degree < s.card)
    (hint : ∀ α ∈ s, ∃ m : ℤ, ((m : K)) = A.eval α / eval α (derivative (Lagrange.nodal s id))) :
    ∃ u : RatFunc K, u ≠ 0 ∧
      algebraMap K[X] (RatFunc K) A / algebraMap K[X] (RatFunc K) (Lagrange.nodal s id)
        = Differential.logDeriv u :=
  isLogDeriv_of_integer_residues s A hA hint

end DeepWiki.SymbolicIntegration
