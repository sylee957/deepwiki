import DeepWiki.Algebra.ListProducts
import DeepWiki.SymbolicIntegration.Computable.GenericPolyEngine
import DeepWiki.SymbolicIntegration.HermiteCorrectness

/-! # Interface: `LawfulSquarefreeDecomposition`

The squarefree-decomposition stage of the Risch reduced case, stated purely against the polynomial
denotation `toPolyG` — no concrete algorithm. A list `decomp = [v₁, …, vₘ]` (the multiplicity-`i` factor at
index `i-1`) is a *lawful* squarefree decomposition of `d` when its factors denote a monic, squarefree,
pairwise-coprime family whose powered product `∏ᵢ vᵢ^i` reconstructs `d` up to associates. Algorithmic
realizations live with the squarefree decomposition engines. -/

open Polynomial Classical

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

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

open Compute CPolyG

variable {α : Type*} [CField α] [CFieldSpec α]

/-- **Interface law: `decomp` is a squarefree decomposition of `d`.** Through `toPolyG`, the factors are
monic, squarefree, and pairwise coprime, and the powered product `prodPow 1 (map toPolyG decomp) = ∏ᵢ vᵢ^i`
is associated to `d`. Abstract: the assembler and the Hermite stage consume *this*, never a concrete loop. -/
structure LawfulSquarefreeDecomposition (d : CPolyG α) (decomp : List (CPolyG α)) : Prop where
  /-- The powered product `∏ᵢ vᵢ^i` reconstructs `d` up to associates. -/
  reconstruct : Associated (toPolyG d) (prodPow 1 (decomp.map toPolyG))
  /-- Each factor is monic. -/
  monic : ∀ p ∈ decomp, (toPolyG p).Monic
  /-- Each factor is squarefree. -/
  squarefree : ∀ p ∈ decomp, Squarefree (toPolyG p)
  /-- Distinct factors are relatively prime. -/
  coprime : decomp.Pairwise (fun p q => IsRelPrime (toPolyG p) (toPolyG q))

namespace LawfulSquarefreeDecomposition

/-- The radical `∏ᵢ vᵢ` (the plain product of the factors) is squarefree — the property the Hermite stage
consumes abstractly (not from the concrete Yun loop). -/
theorem prod_squarefree {d : CPolyG α} {decomp : List (CPolyG α)}
    (h : LawfulSquarefreeDecomposition d decomp) :
    Squarefree ((decomp.map toPolyG).prod) := by
  refine squarefree_list_prod _ ?_ ?_
  · rw [List.pairwise_map]; exact h.coprime
  · intro p hp; rw [List.mem_map] at hp; obtain ⟨q, hq, rfl⟩ := hp; exact h.squarefree q hq

/-- The radical `∏ᵢ vᵢ` is monic. -/
theorem prod_monic {d : CPolyG α} {decomp : List (CPolyG α)}
    (h : LawfulSquarefreeDecomposition d decomp) :
    ((decomp.map toPolyG).prod).Monic := by
  refine monic_list_prod _ ?_
  intro p hp; rw [List.mem_map] at hp; obtain ⟨q, hq, rfl⟩ := hp; exact h.monic q hq

end LawfulSquarefreeDecomposition

end DeepWiki.SymbolicIntegration
