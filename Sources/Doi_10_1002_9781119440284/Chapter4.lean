import DeepWiki.NetworkCalculus.ConcaveDioid
import DeepWiki.NetworkCalculus.ConcaveProps
import DeepWiki.NetworkCalculus.ClosuresEReal
import DeepWiki.NetworkCalculus.FunctionDioids
import DeepWiki.NetworkCalculus.UltimatelyPseudoPeriodic
import DeepWiki.NetworkCalculus.UppSequence
import Sources.Doi_10_1002_9781119440284.Source

/-! # DNC catalog — Chapter 4: Efficient Computations for (min,plus) Operators
Book-numbered catalog entries for this chapter, each linked to the
`DeepWiki` library declaration that formalizes it (`alias`/`abbrev`),
or recorded as a note / unformalized item. -/

namespace DeepWiki.Dnc

open DeepWiki
open scoped NNReal ENNReal

/-! **Definition 4.1** (§4.2.1, p.63): Concave piecewise-linear normal form: f = ⋀_{i=1}^n γ_{r_i,b_i} with strictly decreasing slopes r_i and no removable redundant segment; defines the breakpoint sequence (t_i) of consecutive intersections. Not formalized in the library. -/

/-! **Proposition 4.1** (§4.2.1, p.63): A concave PWL function in normal form satisfies: (1) f is concave; (2) the b_i are increasing; (3) the breakpoints t_i are increasing; (4) f is piecewise linear, equal to γ_{r_i,b_i} on each [t_i,t_{i+1}]. Not formalized in the library. -/

/-! **Theorem 4.1** (§4.2.2.1, p.65): Convolution of two convex PWL functions f,g: f ∗ g concatenates all the segments of f and g in increasing order of slope, starting from f(0)+g(0) (including the semi-infinite segment). Not formalized in the library. -/

/-! **Lemma 4.1** (§4.2.2.2, p.68): For consecutive concave segments g_{j-1},g_j of g convolved with a convex f, with thresholds u_j,u_{j-1}: for t ≤ c_j+u_j, f∗g_j ≥ f∗g_{j-1}, and for t ≥ c_j+u_{j-1}, f∗g_{j-1} ≥ f∗g_j (segment placement of the min). Not formalized in the library. -/

/-! **Theorem 4.2** (§4.2.2.2, p.70): Convolution of a convex by a concave PWL function: the convolution of a convex function with a concave function can be computed segment-wise (the concave g splits the time axis into intervals; the result picks the right segment combination). Mathematical core (convolution of two concave functions = their min up to a constant) is IsConcaveEReal.minConv. Library: IsConcaveEReal.minConv, IsConcaveEReal.inf. -/

/-- **Definition** (§4.3.2, p.74): the class of **ultimately pseudo-periodic** functions — beyond a
rank `T`, advancing time by a period `d` raises the value by an increment `c`. The library's
`DeepWiki.IsUPP` (`IsUPPWith` carries the explicit `(T, d, c)`). The basis of finite representation
and the algorithmic (min,plus) calculus. -/
abbrev def_4_upp := @IsUPP

/-- **Theorem 4.3** (§4.3.2.2, p.74): the class of plain ultimately pseudo-periodic functions of
`F[ℚ,ℚ]` is stable under min, max, +, −, convolution, deconvolution and sub-additive closure. The
library formalizes the UPP class (`def_4_upp`) and its stability under `+`/`⊓`/`⊔`
(`lemma_4_2`/`lemma_4_3_min`/`lemma_4_3_max` below, common-period forms); the convolution,
deconvolution and sub-additive-closure parts are not yet formalized. -/
theorem thm_4_3_add {V : Type*} [AddCommMonoid V] {f g : ℝ≥0 → V} {T₁ T₂ d c₁ c₂}
    (hf : IsUPPWith f T₁ d c₁) (hg : IsUPPWith g T₂ d c₂) :
    IsUPPWith (fun t => f t + g t) (max T₁ T₂) d (c₁ + c₂) := hf.add hg

/-- **Lemma 4.2** (§4.3.2.2, p.75): the sum of two ultimately pseudo-periodic functions is
ultimately pseudo-periodic from `max(T_f,T_g)` with period `lcm(d_f,d_g)` and increment
`(d_g c_f + d_f c_g)/gcd(d_f,d_g)`. The library's `DeepWiki.IsUPPWith.add_of_commonPeriod` (general
commensurable-period form — a common multiple `m•d₁ = n•d₂` with increment `m•c₁ + n•c₂`; the `lcm`
cofactors give exactly the book's formula). The shared-period special case is `IsUPPWith.add`. -/
alias lemma_4_2 := IsUPPWith.add_of_commonPeriod

/-- **Lemma 4.3** (§4.3.2.2, p.75), minimum, balanced case `d_g c_f = d_f c_g`: the minimum of two
ultimately pseudo-periodic functions with a common period and equal scaled increments is ultimately
pseudo-periodic. The library's `DeepWiki.IsUPPWith.min_of_commonPeriod` (shared-period special case
`IsUPPWith.min`). The dominant-slope cases reduce to the faster function and need an Archimedean
argument; not yet formalized. -/
alias lemma_4_3_min := IsUPPWith.min_of_commonPeriod

/-- **Lemma 4.3** (§4.3.2.2, p.75), maximum, balanced case. The library's
`DeepWiki.IsUPPWith.max_of_commonPeriod`. -/
alias lemma_4_3_max := IsUPPWith.max_of_commonPeriod

/-- **Lemma 4.3** (§4.3.2.2, p.75), minimum — **general case** (all slope relations): the pointwise
minimum of two UPP sequences is ultimately pseudo-periodic, `min(f,g)(n+d) = min(f,g)(n) + min(c_f',c_g')`
with `d = lcm` and the increment the smaller per-`d` slope. The library's
`DeepWiki.UppSeq.min_evalNat_add_lcm` — covering the dominant-slope cases via the Archimedean crossover
`evalNat_eventually_le` (the slower function is the min past the crossover). Requires `V` an
Archimedean ordered group. -/
alias lemma_4_3 := UppSeq.min_evalNat_add_lcm

/-- **Lemma 4.4** (§4.3.2.2, p.76): `f ∗ g` is ultimately pseudo-periodic with period `d = lcm(d_f,d_g)`
from rank `T_f + T_g + d`. The library's `DeepWiki.UppSeq.convNat_add_lcm_of_balanced` proves the
pseudo-period step `(f⊗g)(n+d) = (f⊗g)(n) + c` in the **balanced case** — equal asymptotic slopes
`(d/d_f)c_f = (d/d_g)c_g` — matching the book's rank and increment (both bounds via the convolution
minimizer `convNat_eq`). The non-balanced case (increment = the smaller slope) needs the dominant-slope
crossover / general min-of-UPP and is deferred. The pointwise convolution is `DeepWiki.UppSeq.convNat`
(`convNat_le`/`convNat_eq`); the `minplus` CLI's `conv` samples it. -/
alias lemma_4_4 := UppSeq.convNat_add_lcm_of_balanced

/-! **Lemma 4.5** (§4.3.2.2, p.77): If f,g are ultimately pseudo-periodic, then the deconvolution f ⊘ g is ultimately pseudo-periodic from T_f with period d_f and increment c_f. Not formalized in the library. -/

/-! **Lemma 4.6** (§4.3.2.2, p.78): Deconvolution of two segments f (on [I,J]) and g (on interval): f ⊘ g is computed in closed form over three subcases according to the relative endpoints and slopes (default −∞ outside the interval). Not formalized in the library. -/

/-! **Lemma 4.7** (§4.3.2.2, p.78): Sub-additive closure factorization: for f,g,h ∈ F, (f ∗ g ∗ h*)* = f* ∗ (δ₀ ∧ g ∗ h*), reducing the closure of a sum to a finite number of convolutions. Not formalized in the library. -/

/-! **Lemma 4.8** (§4.3.2.2, p.79): Closure of a spot: if f is defined on {d} with f(d)=c then f* is the function defined on ℕd by f*(nd)=nc. Not formalized in the library. -/

/-! **Lemma 4.9** (§4.3.2.2, p.79): If f is a segment defined on an open interval, then f* is ultimately pseudo-periodic. Not formalized in the library. -/

/-! **Remark** (§4.3.3, p.80): On the discrete domain ℕ, (F_ℕ, ∧, ∗_ℕ) is a dioid; the library's function complete-dioid (FPlus over the ℝ≥0 domain) carries the same (min,conv) dioid algebra. Library: FPlus, isSubCompleteDioid_FPlus. -/

/-! **Definition 4.2** (§4.4.2, p.84): Set F of containers: F = {[f̲,f̄]_L | f̲ ∈ F_acx, f̄ ∈ F_acv, ρ_f̲ = ρ_f̄}, the interval of functions between a convex lower bound and concave upper bound sharing an asymptotic slope, modulo the Legendre–Fenchel transform. Not formalized in the library. -/

/-! **Proposition 4.2** (§4.4.2, p.84): Functions f,g ∈ F^⊤_≥0 have the same Legendre–Fenchel transform iff they have the same convex hull: L(f)=L(g) ⇔ C_cv(f)=C_cv(g); and [C_cv f]_L = [f]_L with ∀f'∈[f]_L, C_cv(f) ≤ f'. Not formalized in the library. -/

/-! **Proposition 4.3** (§4.4.2, p.85): The quotient of the dioid F^⊤_≥0 by congruence modulo the Legendre–Fenchel transform is another dioid F^⊤_{≥0}/L; minimum and convolution between containers descend as [f]_L ∧ [g]_L := [f ∧ g]_L, [f]_L ∗ [g]_L := [f ∗ g]_L, [f]*_L := [f*]_L. Not formalized in the library. -/

/-! **Lemma 4.10** (§4.4.2, p.86): Computing with equivalence classes modulo L equals computing with convex hulls: [f]_L ∧ [g]_L ⇔ C_cv(C_cv f ∧ C_cv g), [f]_L ∗ [g]_L ⇔ C_cv(C_cv f ∗ C_cv g), [f]*_L ⇔ C_cv((C_cv f)*). Not formalized in the library. -/

/-! **Proposition 4.4** (§4.4.2, p.87): Canonical upper bound of an equivalence class: for f the canonical lower bound of [f̲,f̄]_L, the canonical upper bound Ω_f̲ is the piecewise-constant function = +∞ on non-differentiable points of f̲ and = f̄ elsewhere; [f̲,f̄]_L = [f̲, C_cv(f̄ ∧ Ω_f̲)]_L. Not formalized in the library. -/

/-! **Definition 4.3** (§4.4.2, p.87): Canonical representation of a container F = [f̲,f̄]_L: the pair [f̲, C_cv(f̄ ∧ Ω_f̲)]_L (canonical lower bound paired with the canonical upper bound), removing representation ambiguities. Not formalized in the library. -/

/-! **Definition 4.4** (§4.4.2, p.89): Maximal uncertainty of a container F = [f̲,f̄]_L: horizontal hDev(f̄,f̲) = inf{τ≥0 | f̄(t₀) ≤ f̲(t₀+τ)} and vertical vDev(f̄,f̲) = f̄(t₀)−f̲(t₀), with t₀ given by the semi-infinite linear part of f̄. Not formalized in the library. -/

/-! **Definition 4.5** (§4.4.3, p.90): Inclusion functions for containers: F[∧]G := [f̲∧g̲, C_cv(f̄∧ḡ)]_L (minimum) and F[∗]G := [f̲∗g̲, f̄∗ḡ]_L (convolution); and the sub-additive-closure inclusion function F[*] := [f̲*, ⟨f̄*⟩] with f̲*=C_cv(f̲*) and ⟨f̄*⟩ = ⋀_{i≥0} C_cv(C_cv(Θ^{f̲*}_{t_i}) ∧ (e ∧ Θ^{f̲*}_{f̄} ∗ ... ∧ g)). Not formalized in the library. -/

/-! **Theorem 4.4** (§4.4.3, p.91): Inclusion functions are stable: for containers f∈F, g∈G of F, f∈F[∧]G ⇒ f∧g ∈ F[∧]G, f∗g∈F[∗]G, f*∈F[*]; the entire proof is given (general case). Not formalized in the library. -/

/-! **Remark 4.1** (§4.4.1, p.82): The container theory connects to the dual algebraic structure: ⊕ is the terms-sum (less ton- and term-wise minimum), and ⊗ is the natural-order multiplication; all notations are inverted between this section and the chapter. Not formalized in the library. -/

end DeepWiki.Dnc
