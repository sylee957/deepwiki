import DeepWiki.NetworkCalculus.ContainerInternalF
import Sources.Doi_10_1007_s10626_012_0148_9.Source

/-! # Le Corronc–Cottenceau–Hardouin — container internality (F-closure) — catalog
Paper-side ("double reference") pointers to the `DeepWiki.NetworkCalculus` theorems formalizing this
paper's internality results, complementing the DNC book catalog's `Chapter4` (Thm 4.4 / Def 4.5, whose
full F-closure the book defers here). Convention bridge: the paper's order `≼` is the REVERSE of the
numeric order (Remark 1), so paper-`f̄` (convex) = DeepWiki container `lo` and paper-`f̲` (concave) =
DeepWiki `hi`; `DeepWiki.IsCanonicalContainer` (`lo_acx`/`hi_acv`) is the faithful reading. The full
internality of `[*]`/`[⋆]` (Props 6/7/9) + the rank-renormalized canonical reassembly (Prop 3) remain
`[infra]`, scoped in the library file. -/

namespace DeepWiki.Lcch

open DeepWiki DeepWiki.Container

/-- **Theorem 3 / eq. (8)** (Le Boudec–Thiran, restated p.18): for concave functions null at origin,
convolution is the meet — `Γ₁ ∗ Γ₂ = Γ₁ ⊓ Γ₂`. The library's
`DeepWiki.Container.concave_minConv_eq_inf`. -/
alias thm_3_conv := Container.concave_minConv_eq_inf

/-- **Theorem 3 / eq. (9)** (p.18): a concave function null at origin is its own sub-additive closure,
`Γ⋆ = Γ`. The library's `DeepWiki.Container.concave_subadditiveClosure_eq_self`. -/
alias thm_3_closure := Container.concave_subadditiveClosure_eq_self

/-- **Proposition 3 (slope), provable half** (p.19): `ρ_{f⊓g} ≤ min(ρ_f, ρ_g)` — the meet's asymptotic
slope is at most the min (the reverse inequality is the geometric extremal-point half, carried as a
hypothesis). The library's `DeepWiki.Container.rho_inf_le_min`. -/
alias prop_3_slope_le := Container.rho_inf_le_min

/-- **Definition 17 / eq. (10)** (p.17): the convex hull `C_vx = biconj` (the Legendre biconjugate) is
convex whenever `f 0 ≠ ⊤` — the lower-bound internality engine. The library's
`DeepWiki.Container.isConvexEReal_biconj_of_zero_ne_top`. -/
alias def_17_convex_hull := Container.isConvexEReal_biconj_of_zero_ne_top

/-- **Definition 23 internality of `[⊕]`** (eq. 14, p.20), the headline: the canonicalized lifted meet
`[C_vx(f̲⊓g̲), f̄⊓ḡ]` IS a canonical container of `F` (convex lower bound + almost-concave upper bound at
a shared rank + asymptotic typing) — so the inclusion function `[⊕]` is internal to `F`. The library's
`DeepWiki.Container.isCanonicalContainer_canonicalizedInf`. -/
alias def_23_internal_inf := Container.isCanonicalContainer_canonicalizedInf

end DeepWiki.Lcch
