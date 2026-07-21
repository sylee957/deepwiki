import DeepWiki.CAlgebra.Squarefree.Musser

/-! # Yun's squarefree decomposition — checker-validated

Yun's algorithm computes the same staircase factors as Musser's from one initial
`gcd(p, deriv p)` plus gcds of the much smaller factor pairs `(cᵢ, dᵢ)`. Its loop has no
structural termination measure (constant factors stall the state), so the sweep runs on an
iteration bound and the output is validated by the **decidable contract check** — squarefree
factors, staircase reconstruction, radical product — falling back to Musser's decomposition
when the check fails. Soundness therefore needs no Yun invariant theory. -/

namespace DeepWiki.CAlgebra

universe u

namespace DensePoly

variable {R : Type u} [Field R] [DecidableEq R] [DensePolyGcd R]

/-- One Yun sweep: emit `gcd(c, d)`, divide it out, and update the derivative accumulator.
The fuel only bounds iterations (the max multiplicity, `≤ p.size`); short-fuel junk is caught
by the contract check in `sqfDecompYun`. -/
private def yunAux : ℕ → DensePoly R → DensePoly R → List (DensePoly R)
  | 0, _, _ => []
  | fuel + 1, c, d =>
    if c.size ≤ 1 then []
    else
      let P := DensePolyGcd.gcd c d
      P :: yunAux fuel (div c P) (div d P - deriv (div c P))

/-- The unvalidated Yun sweep: `c₁ = sqfreePart p`, `d₁ = p′/gcd(p,p′) − c₁′`. -/
def sqfDecompYunRaw [CharZero R] (p : DensePoly R) : List (DensePoly R) :=
  yunAux p.size (sqfreePart p)
    (div (deriv p) (DensePolyGcd.gcd p (deriv p)) - deriv (sqfreePart p))

/-- Yun's decomposition, validated by the decidable contract check (squarefree factors,
staircase reconstruction certificate, radical-product certificate); falls back to
`sqfDecompMusser` if the sweep's output fails the check. -/
def sqfDecompYun [CharZero R] (p : DensePoly R) : List (DensePoly R) :=
  if (∀ f ∈ sqfDecompYunRaw p, Squarefree f) ∧
      powProd (sqfDecompYunRaw p) 1 ≠ 0 ∧
      p * C (powProd (sqfDecompYunRaw p) 1).leadingCoeff
        = powProd (sqfDecompYunRaw p) 1 * C p.leadingCoeff ∧
      (sqfDecompYunRaw p).prod ≠ 0 ∧
      sqfreePart p * C (sqfDecompYunRaw p).prod.leadingCoeff
        = (sqfDecompYunRaw p).prod * C (sqfreePart p).leadingCoeff
  then sqfDecompYunRaw p else sqfDecompMusser p

/-- Every factor produced by the validated Yun decomposition is squarefree. -/
theorem squarefree_of_mem_sqfDecompYun [CharZero R] {p f : DensePoly R}
    (hf : f ∈ sqfDecompYun p) : Squarefree f := by
  rw [sqfDecompYun] at hf
  split_ifs at hf with h
  · exact h.1 f hf
  · exact squarefree_of_mem_sqfDecompMusser hf

/-- **Exponent-exact reconstruction for validated Yun**: identical contract to
`sqfDecompMusser_spec`, from the certificates in the passing branch and Musser's theorem in
the fallback. -/
theorem sqfDecompYun_spec [CharZero R] {p : DensePoly R} (hp : p ≠ 0) :
    Associated p (powProd (sqfDecompYun p) 1) ∧
      Associated (sqfreePart p) (sqfDecompYun p).prod := by
  rw [sqfDecompYun]
  split_ifs with h
  · obtain ⟨-, hq0, hcross, hpr0, hcross'⟩ := h
    exact ⟨associated_of_cross_mul_C hp hq0 hcross,
      associated_of_cross_mul_C (sqfreePart_ne_zero hp) hpr0 hcross'⟩
  · exact sqfDecompMusser_spec hp

end DensePoly

end DeepWiki.CAlgebra
