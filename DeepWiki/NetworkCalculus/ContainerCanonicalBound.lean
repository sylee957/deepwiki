import DeepWiki.NetworkCalculus.Containers
import DeepWiki.NetworkCalculus.ContainerQuotient
import DeepWiki.NetworkCalculus.ContainerCanonical

/-! # Canonical bound and computing on canonical representatives (Prop 4.4, Lemma 4.10)

The convex hull `Cvx f = 𝓛(𝓛 f) = biconj f` is the **least element** of the
Legendre–Fenchel class `[f]_𝓛 = legendreClass f` (Proposition 4.4's
foundation, book p. 85: "`𝒞_vx(f)` is the least representative"). Lemma 4.10
restates the quotient operations of `ℱ↑/𝓛` as biconditionals on the convex
hulls: computing `⊓`/`∗`/`⋆` in `ℱ↑/𝓛` agrees with computing on the canonical
representatives. The explicit elementary-function *upper* bound `Θ_f̲` of
Proposition 4.4 [4.13] (a meet of `Θ^κ_τ` over the non-differentiable points)
needs the non-differentiable-point enumeration layer and is research-grade. -/

namespace DeepWiki

namespace Container

open scoped Classical NNReal ENNReal

/-! ## Proposition 4.4 — `Cvx f` is the least element of `[f]_𝓛`

The book (p. 85) records that `𝒞_vx(f)` is the *least representative* of the
equivalence class `[f]_𝓛`; Proposition 4.4 then builds an explicit *upper*
bound `Θ_f̲` of the class. The least-element fact is the foundation: the convex
hull `Cvx f = biconj f` is both a member of `[f]_𝓛` (`legendre_biconj`) and a
lower bound for it (`biconj_le_of_sameLegendre`), i.e. its minimum. -/

/-- **`Cvx f` is a lower bound of `[f]_𝓛`**: `biconj f ≤ g` pointwise for every
`g ∈ [f]_𝓛` (`biconj_le_of_sameLegendre`). -/
theorem biconj_mem_lowerBounds (f : ℝ≥0 → EReal) :
    biconj f ∈ lowerBounds (legendreClass f) :=
  fun _g hg u => biconj_le_of_sameLegendre hg u

/-- **Proposition 4.4 (foundation), p. 85: `𝒞_vx(f)` is the least element of
`[f]_𝓛`.** The convex hull `Cvx f = biconj f` is a member of the class
(`biconj_mem_legendreClass`) and a lower bound of it
(`biconj_mem_lowerBounds`), hence the minimum (`IsLeast`). -/
theorem isLeast_legendreClass_biconj (f : ℝ≥0 → EReal) :
    IsLeast (legendreClass f) (biconj f) :=
  ⟨biconj_mem_legendreClass f, biconj_mem_lowerBounds f⟩

/-- **Uniqueness of the canonical (least) representative.** Any least element
of `[f]_𝓛` equals the convex hull `Cvx f`; so `biconj f` is *the* canonical
representative. -/
theorem eq_biconj_of_isLeast {f g : ℝ≥0 → EReal} (h : IsLeast (legendreClass f) g) :
    g = biconj f :=
  IsLeast.unique h (isLeast_legendreClass_biconj f)

/-- **`Cvx` is idempotent on the class**: the convex hull of any member of
`[f]_𝓛` is the convex hull of `f`. (`Cvx (Cvx f) = Cvx f` is the `g = biconj f`
special case.) -/
theorem biconj_eq_of_mem_legendreClass {f g : ℝ≥0 → EReal}
    (h : g ∈ legendreClass f) : biconj g = biconj f :=
  ((sameLegendre_iff_biconj_eq f g).mp h).symm

/-- `Cvx` is idempotent: `Cvx (Cvx f) = Cvx f`. -/
theorem biconj_biconj (f : ℝ≥0 → EReal) : biconj (biconj f) = biconj f :=
  biconj_eq_of_mem_legendreClass (biconj_mem_legendreClass f)

/-! ## Lemma 4.10 — computing in `ℱ↑/𝓛` ≡ computing on canonical representatives

The quotient `mk`-equality `[a]_𝓛 = [b]_𝓛` is exactly `Cvx a = Cvx b`
(`mk_eq_mk` ∘ `sameLegendre_iff_biconj_eq`). Lemma 4.10 [4.10]–[4.12] are the
instances of this for `⊓`, `∗`, `⋆`: the quotient operation computed on
representatives equals the class of the operation iff the convex hulls agree. -/

/-- **`[a]_𝓛 = [b]_𝓛 ↔ Cvx a = Cvx b`.** The quotient-class equality is the
equality of convex hulls (`mk_eq_mk` composed with
`sameLegendre_iff_biconj_eq`); the engine of Lemma 4.10's biconditionals. -/
theorem mk_eq_mk_iff_biconj_eq (f g : ℝ≥0 → EReal) :
    FmodL.mk f = FmodL.mk g ↔ biconj f = biconj g :=
  (FmodL.mk_eq_mk).trans (sameLegendre_iff_biconj_eq f g)

/-- **Lemma 4.10 [4.10], p. 86 — the meet.** `[f]_𝓛 ⊓ [g]_𝓛 = [f ⊓ g]_𝓛`
iff `Cvx (Cvx f ⊓ Cvx g) = Cvx (f ⊓ g)`. The left side is the descended meet
on representatives (`FmodL.inf_mk`); the biconditional is `mk_eq_mk_iff_biconj_eq`
after rewriting `Cvx f ⊓ Cvx g` for the left operand via idempotence of `Cvx`. -/
theorem inf_mk_eq_iff_biconj (f g : ℝ≥0 → EReal) :
    FmodL.inf (FmodL.mk f) (FmodL.mk g) = FmodL.mk (f ⊓ g) ↔
      biconj (biconj f ⊓ biconj g) = biconj (f ⊓ g) := by
  rw [FmodL.inf_mk, mk_eq_mk_iff_biconj_eq]
  constructor
  · intro h
    -- `Cvx (f ⊓ g) = Cvx (Cvx f ⊓ Cvx g)`: rewrite each operand of `⊓` by `Cvx`-idempotence
    refine Eq.trans ?_ h.symm
    refine biconj_eq_of_mem_legendreClass ?_
    -- `Cvx f ⊓ Cvx g ∈ [f ⊓ g]_𝓛`, i.e. `𝓛(f ⊓ g) = 𝓛(Cvx f ⊓ Cvx g)`
    show legendre (f ⊓ g) = legendre (biconj f ⊓ biconj g)
    rw [legendre_inf, legendre_inf, legendre_biconj, legendre_biconj]
  · intro h
    refine Eq.trans ?_ h
    refine (biconj_eq_of_mem_legendreClass ?_).symm
    show legendre (f ⊓ g) = legendre (biconj f ⊓ biconj g)
    rw [legendre_inf, legendre_inf, legendre_biconj, legendre_biconj]

/-- **Lemma 4.10 [4.10] always holds (the meet case is unconditional).** Because
`𝓛` is a `⊓`-homomorphism (`legendre_inf`) and `Cvx` shares transforms
(`legendre_biconj`), `Cvx (Cvx f ⊓ Cvx g) = Cvx (f ⊓ g)` is a *theorem*; so the
quotient meet always computes on canonical representatives. -/
theorem biconj_inf_biconj (f g : ℝ≥0 → EReal) :
    biconj (biconj f ⊓ biconj g) = biconj (f ⊓ g) := by
  refine biconj_eq_of_mem_legendreClass ?_
  show legendre (f ⊓ g) = legendre (biconj f ⊓ biconj g)
  rw [legendre_inf, legendre_inf, legendre_biconj, legendre_biconj]

/-- **Lemma 4.10's meet section property.** The quotient meet of two classes is
the class of the meet of their canonical representatives: computing `⊓` in
`ℱ↑/𝓛` agrees with computing on convex hulls. -/
theorem inf_mk_biconj (f g : ℝ≥0 → EReal) :
    FmodL.inf (FmodL.mk (biconj f)) (FmodL.mk (biconj g)) = FmodL.mk (f ⊓ g) := by
  rw [FmodL.inf_mk, mk_eq_mk_iff_biconj_eq]
  exact biconj_inf_biconj f g

/-- **Lemma 4.10 [4.11], p. 86 — the convolution.** For proper curves with
proper convex hulls the quotient product `[f]_𝓛 ∗ [g]_𝓛 = [f ∗ g]_𝓛` iff
`Cvx (Cvx f ∗ Cvx g) = Cvx (f ∗ g)` (with `∗ = legendreConv` the
inf-convolution). Like the meet, this is *unconditional*: `𝓛(f ∗ g) = 𝓛 f + 𝓛 g`
(`legendre_legendreConv`) is a homomorphism, so the convex hulls always agree.
The biconjugate-properness hypotheses are what `legendre_legendreConv` consumes
to read the transform of `Cvx f ∗ Cvx g` as a sum. -/
theorem biconj_legendreConv_biconj {f g : ℝ≥0 → EReal}
    (hf₀ : ∀ u, f u ≠ ⊥) (hg₀ : ∀ v, g v ≠ ⊥)
    (hbf₀ : ∀ u, biconj f u ≠ ⊥) (hbg₀ : ∀ v, biconj g v ≠ ⊥) :
    biconj (legendreConv (biconj f) (biconj g)) = biconj (legendreConv f g) := by
  refine biconj_eq_of_mem_legendreClass ?_
  show legendre (legendreConv f g) = legendre (legendreConv (biconj f) (biconj g))
  rw [legendre_legendreConv hf₀ hg₀, legendre_legendreConv hbf₀ hbg₀,
    legendre_biconj, legendre_biconj]

/-- **Lemma 4.10's convolution section property** (proper curves with proper
convex hulls). The quotient product of two proper classes is the class of the
convolution of their canonical representatives: computing `∗` in `ℱ↑/𝓛` agrees
with computing on convex hulls. -/
theorem mk_legendreConv_biconj {f g : ℝ≥0 → EReal}
    (hf₀ : ∀ u, f u ≠ ⊥) (hg₀ : ∀ v, g v ≠ ⊥)
    (hbf₀ : ∀ u, biconj f u ≠ ⊥) (hbg₀ : ∀ v, biconj g v ≠ ⊥) :
    FmodL.mk (legendreConv (biconj f) (biconj g)) = FmodL.mk (legendreConv f g) :=
  (mk_eq_mk_iff_biconj_eq _ _).mpr (biconj_legendreConv_biconj hf₀ hg₀ hbf₀ hbg₀)

/-! ## Faithfulness checks (anonymous restatements vs the book) -/

-- Proposition 4.4 (p. 85): `Cvx f` is the least element of `[f]_𝓛`.
example (f : ℝ≥0 → EReal) :
    biconj f ∈ legendreClass f ∧ ∀ g ∈ legendreClass f, biconj f ≤ g :=
  ⟨(isLeast_legendreClass_biconj f).1, (isLeast_legendreClass_biconj f).2⟩

-- Lemma 4.10 [4.10] (p. 86): `[f]_𝓛 ⊓ [g]_𝓛 = [f ⊓ g]_𝓛 ⟺ Cvx(Cvx f ⊓ Cvx g) = Cvx(f ⊓ g)`.
example (f g : ℝ≥0 → EReal) :
    FmodL.inf (FmodL.mk f) (FmodL.mk g) = FmodL.mk (f ⊓ g) ↔
      biconj (biconj f ⊓ biconj g) = biconj (f ⊓ g) :=
  inf_mk_eq_iff_biconj f g

-- Lemma 4.10 [4.11] (p. 86): `Cvx(Cvx f ∗ Cvx g) = Cvx(f ∗ g)` (proper curves).
example {f g : ℝ≥0 → EReal} (hf₀ : ∀ u, f u ≠ ⊥) (hg₀ : ∀ v, g v ≠ ⊥)
    (hbf₀ : ∀ u, biconj f u ≠ ⊥) (hbg₀ : ∀ v, biconj g v ≠ ⊥) :
    biconj (legendreConv (biconj f) (biconj g)) = biconj (legendreConv f g) :=
  biconj_legendreConv_biconj hf₀ hg₀ hbf₀ hbg₀

end Container

end DeepWiki
