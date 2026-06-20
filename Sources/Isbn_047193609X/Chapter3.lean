import DeepWiki.NetworkCalculus.MinPlusMatrix
import Sources.Isbn_047193609X.Source

/-! # Synchronization and Linearity catalog — Chapter 3 (dioid matrix theory)
The (min,plus) dual of BCOQ Chapter 3. BCOQ works in `(max,plus)` (maximum cycle mean, circuits of
positive weight); the `DeepWiki.MinPlusMatrix` library is the order-dual `(min,plus)` (minimum cycle
mean, circuits of nonnegative weight). The three results below are formalized in full; the asymptotic
cyclicity (Thm 3.112) is formalized in part — the periodic recurrence at a critical vertex — its
extension to all entries past a finite rank resting on the §3.7.1–3.7.3 critical-graph and
spectral-projector theory, which is not formalized. -/

namespace DeepWiki.Bcoq

open DeepWiki.MinPlusMatrix

/-- **Theorem 3.20** (§3.2): if `G(A)` has no circuit of positive weight then the Kleene star
`A⁺ = A ⊕ ⋯ ⊕ Aⁿ` is reached by finite powers. Dual form (nonnegative circuits): for every power `k`
some power below `n` is entrywise at least as good, so `⨁ₖ Aᵏ = ⨁_{k<n} Aᵏ` — the library's
`exists_lt_untrop_pow_le` (the sub-additive closure stabilizes at rank `n`). -/
alias thm_3_20 := exists_lt_untrop_pow_le

/-- **Theorem 3.23** (§3.2.4, Spectral Theory of Matrices): an irreducible matrix has a unique
eigenvalue, equal to the maximum cycle mean. Dual form: the eigenvalue is the **minimum mean cycle**
`minMeanCycle A`, and it is *attained* by an explicit short circuit — the library's `minMeanCycle_eq`
(with `minMeanCycle_le`: it lower-bounds every circuit mean). -/
alias thm_3_23 := minMeanCycle_eq

/-- **Theorem 3.112** (§3.7.4, Asymptotic Behavior of `Aᵏ`): every matrix is asymptotically cyclic —
`Aᵏ⁺ᵈ = Aᵏ ⊗ λᵈ` past a finite rank, with cyclicity `d`. Formalized **in part**: the recurrence
`(A^((k+1)p₀))ᵥ₀ᵥ₀ = (A^(kp₀))ᵥ₀ᵥ₀ ⊗ trop(c·λ)` is realized exactly at a critical vertex `v₀` for any
matrix with a circuit — the library's `exists_critical_cyclicity`. The full theorem (all entries, the
minimal cyclicity `d`) additionally needs the critical-graph and spectral-projector theory of
§3.7.1–3.7.3. -/
alias thm_3_112 := exists_critical_cyclicity

end DeepWiki.Bcoq
