import DeepWiki.CAlgebra.Squarefree.Musser
import DeepWiki.CAlgebra.Squarefree.Yun

/-! # Switchable squarefree decomposition for `DensePoly`

`DensePolySquarefree` packages a squarefree-decomposition algorithm with its full contract —
squarefree factors, exponent-exact staircase reconstruction, radical product — so consumers
depend only on the spec while the algorithm is chosen per carrier by instance priority
(Yun's sweep by default, Musser's recursion available). -/

namespace DeepWiki.CAlgebra

universe u

open scoped Differential FormalDiff

open DensePoly

/-- A squarefree-decomposition algorithm for `DensePoly R` together with its contract: every
factor is squarefree, `p` reconstructs as the staircase product `∏ᵢ pᵢ^i` up to a constant,
and the plain factor product is the squarefree part. Consumers use only these fields; instance
priority selects the algorithm per carrier. -/
class DensePolySquarefree (R : Type u) [Field R] [DecidableEq R] [DensePolyGcd R] where
  /-- The decomposition: `p ~ ∏ᵢ pᵢ^i` with staircase exponents starting at `1`. -/
  sqfDecomp : DensePoly R → List (DensePoly R)
  /-- Every factor produced is squarefree. -/
  squarefree_of_mem : ∀ {p f : DensePoly R}, f ∈ sqfDecomp p → Squarefree f
  /-- Exponent-exact reconstruction up to a nonzero constant. -/
  associated_powProd : ∀ {p : DensePoly R}, p ≠ 0 → Associated p (powProd (sqfDecomp p) 1)
  /-- The plain product of the factors is the squarefree part (the radical). -/
  associated_prod : ∀ {p : DensePoly R}, p ≠ 0 → Associated (sqfreePart p) (sqfDecomp p).prod

variable {R : Type u} [Field R] [DecidableEq R] [DensePolyGcd R]

/-- Musser's recursion on `gcd(p, p′)`, registered below the Yun default. -/
instance (priority := 90) musserDensePolySquarefree [CharZero R] : DensePolySquarefree R where
  sqfDecomp := sqfDecompMusser
  squarefree_of_mem := squarefree_of_mem_sqfDecompMusser
  associated_powProd hp := (sqfDecompMusser_spec hp).1
  associated_prod hp := (sqfDecompMusser_spec hp).2

/-- Default algorithm: Yun's sweep — same proven contract as Musser's, fewer large gcds
(benchmarked 1.4–1.7× faster over `ℚ`). -/
instance (priority := 100) yunDensePolySquarefree [CharZero R] : DensePolySquarefree R where
  sqfDecomp := sqfDecompYun
  squarefree_of_mem := squarefree_of_mem_sqfDecompYun
  associated_powProd hp := (sqfDecompYun_spec hp).1
  associated_prod hp := (sqfDecompYun_spec hp).2

end DeepWiki.CAlgebra
