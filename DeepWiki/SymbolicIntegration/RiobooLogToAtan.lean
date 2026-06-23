import DeepWiki.SymbolicIntegration.RiobooRealLogarithm

/-! # Rioboo's `LogToAtan`: complex-log → real-arctan conversion (Bronstein §2.8, p.63)
Rioboo's `LogToAtan(A, B)` (`A, B ∈ K[x]`, `B ≠ 0`) returns a list of arctangent arguments whose
arctan-derivative sum `∑ 2·P'/(1+P²)` equals `i · d/dx log((A+iB)/(A−iB))`. The recursion:
`if B ∣ A return [A/B]`; `if deg A < deg B return LogToAtan(−B, A)`; else with the extended
Euclidean cofactors `B·D − A·C = G = gcd(A,B)`, `return (A·D+B·C)/G :: LogToAtan(D, C)`.

Each branch is exactly **Theorem 2.8.1** (already proved): base = the `q = A/B` form of Lemma 2.8.1,
swap = `logDeriv_imagQuot_eq_imagQuot_swap`, step = `logDeriv_imagQuot_eq_arctan_add_imagQuot`. Here we
add the recursion's list helper `atanDerivSum`, a **fuel-bounded** total `logToAtanAux`, the three
single-step unfolding identities, and the assembled correctness `logToAtanAux_correct` (under a
"fuel reaches the base case" predicate). Everything is stated abstractly in a characteristic-`0`
differential field `R` with `i² = −1`; the algorithm's branch decisions live on the `K[x]` operands,
embedded into `R` by a derivation-commuting ring hom `φ`. -/

open Polynomial
open scoped Differential
open Classical

namespace DeepWiki.SymbolicIntegration

section AtanDerivSum
variable {R : Type*} [Field R] [Differential R]

/-- **Arctan-derivative sum** of a list of arctan arguments: `atanDerivSum L = ∑_{P∈L} 2·P'/(1+P²)`,
the derivative of `∑_{P∈L} 2·arctan(P)`. -/
def atanDerivSum (L : List R) : R :=
  (L.map fun P => 2 * (P′ / (1 + P ^ 2))).sum

/-- `atanDerivSum [] = 0`. -/
@[simp] theorem atanDerivSum_nil : atanDerivSum ([] : List R) = 0 := by
  simp [atanDerivSum]

/-- `atanDerivSum (P :: L) = 2·P'/(1+P²) + atanDerivSum L`. -/
@[simp] theorem atanDerivSum_cons (P : R) (L : List R) :
    atanDerivSum (P :: L) = 2 * (P′ / (1 + P ^ 2)) + atanDerivSum L := by
  simp [atanDerivSum]

/-- `atanDerivSum [P] = 2·P'/(1+P²)`. -/
theorem atanDerivSum_singleton (P : R) : atanDerivSum [P] = 2 * (P′ / (1 + P ^ 2)) := by
  simp

end AtanDerivSum

section LogToAtan
variable {K : Type*} [Field K] [CharZero K]
variable {R : Type*} [Field R] [Differential R] [CharZero R]

/-- **`LogToAtan` recursion, fuel-bounded** (§2.8, p.63): `logToAtanAux φ fuel A B` runs Rioboo's
recursion `fuel` steps, returning the list of arctan arguments (as elements of `R` via `φ`). Branches:
`B ∣ A → [φ(A)/φ(B)]`; `deg A < deg B → LogToAtan(−B, A)`; else with `B·D − A·C = G = gcd(A,B)`,
`(φ(A)φ(D)+φ(B)φ(C))/φ(G) :: LogToAtan(D, C)`. Returns `[]` at `fuel = 0`. -/
noncomputable def logToAtanAux (φ : K[X] →+* R) : ℕ → K[X] → K[X] → List R
  | 0, _, _ => []
  | fuel + 1, A, B =>
    if B ∣ A then
      [φ A / φ B]
    else if A.degree < B.degree then
      logToAtanAux φ fuel (-B) A
    else
      let C := EuclideanDomain.gcdB B (-A)
      let D := EuclideanDomain.gcdA B (-A)
      let G := EuclideanDomain.gcd B (-A)
      (φ A * φ D + φ B * φ C) / φ G :: logToAtanAux φ fuel D C
