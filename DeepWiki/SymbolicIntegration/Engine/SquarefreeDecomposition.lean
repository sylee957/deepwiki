import DeepWiki.Algebra.ListProducts
import DeepWiki.ComputableAlgebra.PolySquarefree
import DeepWiki.SymbolicIntegration.SquarefreeFactorization

/-! # Interface: `LawfulSquarefreeDecomposition`

The squarefree-decomposition stage of the Risch reduced case, stated purely against the polynomial
denotation `toPoly` — no concrete algorithm. A list `decomp = [v₁, …, vₘ]` (the multiplicity-`i` factor at
index `i-1`) is a *lawful* squarefree decomposition of `d` when its factors denote a monic, squarefree,
pairwise-coprime family whose powered product `∏ᵢ vᵢ^i` reconstructs `d` up to associates. Algorithmic
realizations live with the squarefree decomposition engines. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

universe u v

/-- **The product of pairwise-coprime squarefree polynomials is squarefree** (list form). -/
theorem squarefree_list_prod {K : Type*} [Field K] (L : List K[X])
    (hpw : L.Pairwise IsRelPrime) (hsf : ∀ a ∈ L, Squarefree a) : Squarefree L.prod := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.pairwise_cons] at hpw
    rw [List.prod_cons, squarefree_mul_iff]
    exact ⟨isRelPrime_list_prod_right a t (fun b hb => hpw.1 b hb),
      hsf a (List.mem_cons_self ..),
      ih hpw.2 (fun x hx => hsf x (List.mem_cons_of_mem a hx))⟩

/-- The product of monic polynomials is monic (list form). -/
theorem monic_list_prod {K : Type*} [Field K] (L : List K[X]) (h : ∀ p ∈ L, p.Monic) :
    L.prod.Monic := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons]
    exact (h a (List.mem_cons_self ..)).mul (ih (fun p hp => h p (List.mem_cons_of_mem a hp)))

variable {P : Type u → Type u} [CPoly P]
variable {α : Type u} [CField α] [CFieldSpec.{u,v} α]

/-- File-local bridge from a selected lawful gcd to the mathematical polynomial gcd. -/
private theorem selectedGcd_associated [CPolyEngine P] [CPolyGcd P α]
    [LawfulCPolyGcd.{u,v} P α] (p q : P α) :
    Associated (CPoly.toPoly (CPolyGcd.compute p q)) (gcd (CPoly.toPoly p) (CPoly.toPoly q)) := by
  obtain ⟨hleft, hright, hgreatest⟩ := LawfulCPolyGcd.compute_isGCD' p q
  apply associated_of_dvd_dvd (dvd_gcd hleft hright)
  exact hgreatest _ (gcd_dvd_left _ _) (gcd_dvd_right _ _)

/-- File-local bridge showing engine monic normalization preserves association. -/
private theorem cmonic_associated [CPolyEngine P] [LawfulCPolyEngine.{u,v} P]
    (p : P α) (hp : CPoly.toPoly p ≠ 0) :
    Associated (CPoly.toPoly (CPolyEngine.cmonic p)) (CPoly.toPoly p) := by
  have hlead : (CPoly.toPoly p).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  rw [CPolyEngine.toPoly_cmonic_of_ne_zero p hp]
  refine ⟨(isUnit_C.mpr (isUnit_iff_ne_zero.mpr hlead)).unit, ?_⟩
  rw [IsUnit.unit_spec]
  calc
    Polynomial.C (CPoly.toPoly p).leadingCoeff⁻¹ * CPoly.toPoly p *
        Polynomial.C (CPoly.toPoly p).leadingCoeff =
      (Polynomial.C (CPoly.toPoly p).leadingCoeff⁻¹ *
        Polynomial.C (CPoly.toPoly p).leadingCoeff) * CPoly.toPoly p := by ring
    _ = CPoly.toPoly p := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hlead, Polynomial.C_1, one_mul]

/-- **Interface law: `decomp` is a squarefree decomposition of `d`.** Through `toPoly`, the factors are
monic, squarefree, and pairwise coprime, and the powered product `prodPow 1 (map toPoly decomp) = ∏ᵢ vᵢ^i`
is associated to `d`. Abstract: the assembler and the Hermite stage consume *this*, never a concrete loop. -/
structure LawfulSquarefreeDecomposition (d : P α) (decomp : List (P α)) : Prop where
  /-- The powered product `∏ᵢ vᵢ^i` reconstructs `d` up to associates. -/
  reconstruct : Associated (CPoly.toPoly d) (prodPow 1 (decomp.map CPoly.toPoly))
  /-- Each factor is monic. -/
  monic : ∀ p ∈ decomp, (CPoly.toPoly p).Monic
  /-- Each factor is squarefree. -/
  squarefree : ∀ p ∈ decomp, Squarefree (CPoly.toPoly p)
  /-- Distinct factors are relatively prime. -/
  coprime : decomp.Pairwise (fun p q => IsRelPrime (CPoly.toPoly p) (CPoly.toPoly q))

/-- Denotation law for a representation-selected squarefree decomposition. The selected output is
lawful whenever its input denotes a nonzero polynomial with nonzero primitive part. -/
class LawfulCPolySquarefree (P : Type u → Type u) [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
    (α : Type u) [CField α] [CPolyGcd P α] [CFieldSpec.{u,v} α] [CharZero (CFieldSpec.K α)]
    [CPolySquarefree P α] : Prop where
  /-- The selected squarefree decomposition satisfies the semantic factorization contract. -/
  compute_lawful : ∀ (d : P α), CPoly.toPoly d ≠ 0 → (CPoly.toPoly d).primPart ≠ 0 →
      LawfulSquarefreeDecomposition d (CPoly.squarefreeYun d)

namespace LawfulCPolySquarefree

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
variable {α : Type u} [CField α] [CFieldSpec.{u,v} α] [CharZero (CFieldSpec.K α)]
  [CPolyGcd P α] [CPolySquarefree P α] [LawfulCPolySquarefree.{u,v} P α]

/-- The selected squarefree decomposition satisfies its semantic contract. -/
theorem compute_lawful' (d : P α) (hd0 : CPoly.toPoly d ≠ 0)
    (hpp : (CPoly.toPoly d).primPart ≠ 0) :
    LawfulSquarefreeDecomposition d (CPoly.squarefreeYun d) :=
  LawfulCPolySquarefree.compute_lawful d hd0 hpp

end LawfulCPolySquarefree

namespace LawfulSquarefreeDecomposition

/-- The radical `∏ᵢ vᵢ` (the plain product of the factors) is squarefree — the property the Hermite stage
consumes abstractly (not from the concrete Yun loop). -/
theorem prod_squarefree {d : P α} {decomp : List (P α)}
    (h : LawfulSquarefreeDecomposition d decomp) :
    Squarefree ((decomp.map CPoly.toPoly).prod) := by
  refine squarefree_list_prod _ ?_ ?_
  · rw [List.pairwise_map]; exact h.coprime
  · intro p hp; rw [List.mem_map] at hp; obtain ⟨q, hq, rfl⟩ := hp; exact h.squarefree q hq

/-- The radical `∏ᵢ vᵢ` is monic. -/
theorem prod_monic {d : P α} {decomp : List (P α)}
    (h : LawfulSquarefreeDecomposition d decomp) :
    ((decomp.map CPoly.toPoly).prod).Monic := by
  refine monic_list_prod _ ?_
  intro p hp; rw [List.mem_map] at hp; obtain ⟨q, hq, rfl⟩ := hp; exact h.monic q hq

end LawfulSquarefreeDecomposition

end DeepWiki.SymbolicIntegration
