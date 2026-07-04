import DeepWiki.SymbolicIntegration.Computable.GenericPolyEngine
import DeepWiki.SymbolicIntegration.HermiteCorrectness

/-! # Interface: `LawfulSquarefreeDecomposition` (Stage-1 abstract)

The squarefree-decomposition stage of the Risch reduced case, stated purely against the polynomial
denotation `toPolyG` — no concrete algorithm. A list `decomp = [v₁, …, vₘ]` (the multiplicity-`i` factor at
index `i-1`) is a *lawful* squarefree decomposition of `d` when its factors denote a monic, squarefree,
pairwise-coprime family whose powered product `∏ᵢ vᵢ^i` reconstructs `d` up to associates.

See `docs/risch-two-stage-discipline.md`. The realization `cSqfreeYunFFGWf_lawfulSquarefreeDecomposition`
lives with the algorithm (`YunTowerCorrect`), not here. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

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

end DeepWiki.SymbolicIntegration
