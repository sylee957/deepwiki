import DeepWiki.SymbolicIntegration.RationalIntegrationAlgorithms
import DeepWiki.SymbolicIntegration.PseudoRemainderSequence

/-! # Lazard–Rioboo–Trager correctness (Bronstein Theorem 2.5.1, part (ii))
The LRT log-part algorithm replaces the Rothstein–Trager per-residue gcds `gcd(D, A − a·D')` by the
specializations `Sᵢ(a, x)` of one subresultant PRS. Theorem 2.5.1(ii) is the correctness statement
`ppₓ(Sₘ)(a, x) ~ gcd(D, A − a·D')`. This file connects the *concrete* subresultant ↔ gcd engine
(`subresultant_euclideanPRS_isSimilar_gcd`) to the algorithm's primitive `lrtSubresultant` via the
specialization `lrtSubresultant_eval` (`t ↦ a`). The bridge is the non-degeneracy
`deg(A − a·D') = deg D − 1`, which matches `lrtSubresultant`'s formal degree `deg D − 1` to the *actual*
degree of `A − a·D'` driving the Euclidean p.r.s. (Over a field `ppₓ(Sₘ) ~ Sₘ`, so the similarity below is
the part-(ii) conclusion with the primitive part absorbed by `~`.) -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

/-- **Theorem 2.5.1, part (ii)** (the LRT subresultant correctness, non-degenerate case): for `D ≠ 0` and a
value `a` with `deg(A − a·D') = deg D − 1`, the LRT subresultant `lrtSubresultant A D` at the index
`i = deg R_k` (`R_k` the last nonzero element of the Euclidean p.r.s. of `D, A − a·D'`), specialized by
`t ↦ a`, is *similar* to `gcd(D, A − a·D')`. Combines `lrtSubresultant_eval` (the `t ↦ a` specialization,
which lands on `subresultant D (A − a·D') (deg D) (deg D − 1) i`) with the concrete subresultant ↔ gcd
connection `subresultant_euclideanPRS_isSimilar_gcd`, the degree hypothesis bridging the formal degree
`deg D − 1` to the actual `deg(A − a·D')`. -/
theorem isSimilar_lrtSubresultant_eval_gcd {K : Type*} [Field K] [GCDMonoid K[X]]
    (A D : K[X]) (a : K) (hD : D ≠ 0)
    (hdeg : (A - C a * derivative D).natDegree = D.natDegree - 1)
    {k : ℕ} (hk2 : 2 ≤ k) (hk0 : euclideanPRS D (A - C a * derivative D) (k + 1) = 0)
    (hknz : ∀ j, 1 ≤ j → j ≤ k → euclideanPRS D (A - C a * derivative D) j ≠ 0) :
    IsSimilar
      ((lrtSubresultant A D (euclideanPRS D (A - C a * derivative D) k).natDegree).map
        (Polynomial.evalRingHom a))
      (gcd D (A - C a * derivative D)) := by
  rw [lrtSubresultant_eval, ← hdeg]
  exact subresultant_euclideanPRS_isSimilar_gcd D (A - C a * derivative D) hD
    (by rw [hdeg]; exact Nat.sub_le _ _) hk2 hk0 hknz

end DeepWiki.SymbolicIntegration
