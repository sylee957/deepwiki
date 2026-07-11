import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralWellFounded
import DeepWiki.SymbolicIntegration.Engine.Algebraic.GeneralResidues
import DeepWiki.SymbolicIntegration.Engine.Algebraic.RadicalLogSoundness

/-! # General-curve log-part soundness

Log-part soundness `D(Σ cᵢ log uᵢ) = logpart` for the general-curve integrator, via `afDerivWf` in the
carrier quotient `K[X] ⧸ afIdeal f`: the single- and multi-term predicates, the engine certificate bridge,
the residue-correctness core (`genNormFactor`, `roots_genResidueResultant_eq_residues`, the interpolation
compute-bridge), and the composition with the rational part into the full `D(∫f) = f` predicate. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open scoped Differential

namespace DensePoly

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-! ### The log-soundness predicates and residue-sum skeleton

For a carrier element `u ∈ K(x)[y]/(f)`, `D(log u) = afDerivWf(u)/u`; the predicates read this as the
cross-multiplied (division-free) quotient equation in `K[X] ⧸ afIdeal f`. -/

/-- Single-log soundness predicate: `D(log u) = integrand`, read as
`mk(toPoly(afDerivWf f u)) = mk(toPoly u)·mk(toPoly integrand)` in the quotient. -/
def IsGeneralLogTermWf (f u integrand : DensePoly α) : Prop :=
  Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f u))
    = Ideal.Quotient.mk (afIdeal f) (toPoly u)
      * Ideal.Quotient.mk (afIdeal f) (toPoly integrand)

omit [CDiffFieldSpec α] in
/-- The engine log-derivative certificate as a `K[X]` equality. -/
theorem toPolyG_afDerivWf_eq_of_logCert (f u integrand : DensePoly α)
    (h : cisZero (csub (afDerivWf f u) (CPoly.mulMod f u integrand)) = true) :
    toPoly (afDerivWf f u) = toPoly (CPoly.mulMod f u integrand) := by
  simpa [cisZeroG_iff, sub_eq_zero] using h

omit [CDiffFieldSpec α] in
/-- An engine log-derivative certificate implies the single-log predicate. -/
theorem isGeneralLogTermWf_of_logCert (f u integrand : DensePoly α) (hf : cnorm f ≠ [])
    (h : cisZero (csub (afDerivWf f u) (CPoly.mulMod f u integrand)) = true) :
    IsGeneralLogTermWf f u integrand := by
  rw [IsGeneralLogTermWf, toPolyG_afDerivWf_eq_of_logCert f u integrand h,
    mk_toPoly_mulMod f u integrand hf]

/-- The two-term log-derivative numerator `c₁·D(u₁)·u₂ + c₂·D(u₂)·u₁`. -/
def afLogSum2Wf (f : DensePoly α) (c₁ : α) (u₁ : DensePoly α) (c₂ : α) (u₂ : DensePoly α) :
    DensePoly α :=
  cadd (CPoly.mulMod f (cscale c₁ (afDerivWf f u₁)) u₂)
    (CPoly.mulMod f (cscale c₂ (afDerivWf f u₂)) u₁)

omit [CDiffFieldSpec α] in
/-- Two log-derivative terms add in quotient form. -/
theorem mk_toPolyG_afLogSum2Wf (f : DensePoly α) (c₁ : α) (u₁ : DensePoly α) (c₂ : α)
    (u₂ : DensePoly α) (hf : cnorm f ≠ []) :
    Ideal.Quotient.mk (afIdeal f) (toPoly (afLogSum2Wf f c₁ u₁ c₂ u₂))
      = Polynomial.C (CFieldSpec.toK c₁)
          * Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f u₁))
          * Ideal.Quotient.mk (afIdeal f) (toPoly u₂)
        + Polynomial.C (CFieldSpec.toK c₂)
      * Ideal.Quotient.mk (afIdeal f) (toPoly (afDerivWf f u₂))
      * Ideal.Quotient.mk (afIdeal f) (toPoly u₁) := by
  rw [afLogSum2Wf]
  simp only [denote, map_add, map_mul, mk_toPoly_mulMod _ _ _ hf]

/-- The residue-sum numerator `Σ cᵢ·afDerivWf(uᵢ)·cofᵢ` over a cofactor list. -/
def afLogSumNumWf (f : DensePoly α) (args : List (α × DensePoly α)) (cofs : List (DensePoly α)) :
    DensePoly α :=
  ((args.zip cofs).map (fun p =>
    CPoly.mulMod f (cscale p.1.1 (afDerivWf f p.1.2)) p.2)).foldl cadd ([] : DensePoly α)

/-- Multi-term log-soundness predicate: `Σ cᵢ·afDerivWf(uᵢ)/uᵢ = logpart` in the quotient,
cross-multiplied by the common denominator. -/
def IsGeneralLogIntegralWf (f logpart commonDenomQ : DensePoly α)
    (args : List (α × DensePoly α)) (cofs : List (DensePoly α)) : Prop :=
  Ideal.Quotient.mk (afIdeal f) (toPoly (afLogSumNumWf f args cofs))
    = Ideal.Quotient.mk (afIdeal f) (toPoly (CPoly.mulMod f logpart commonDenomQ))

omit [CDiffFieldSpec α] in
/-- The residue-sum numerator of the empty log part is zero in the quotient. -/
theorem mk_toPolyG_afLogSumNumWf_nil (f : DensePoly α) (cofs : List (DensePoly α)) :
    Ideal.Quotient.mk (afIdeal f) (toPoly (afLogSumNumWf f [] cofs)) = 0 := by
  show Ideal.Quotient.mk (afIdeal f) (toPoly ([] : DensePoly α)) = 0
  rw [toPolyG_nil, map_zero]

omit [CDiffFieldSpec α] in
/-- The residue-sum numerator distributes over the args list. -/
theorem mk_toPolyG_afLogSumNumWf_eq_sum (f : DensePoly α) (args : List (α × DensePoly α))
    (cofs : List (DensePoly α)) :
    Ideal.Quotient.mk (afIdeal f) (toPoly (afLogSumNumWf f args cofs))
      = ((args.zip cofs).map (fun p =>
          Ideal.Quotient.mk (afIdeal f)
            (toPoly (CPoly.mulMod f (cscale p.1.1 (afDerivWf f p.1.2)) p.2)))).sum := by
  rw [afLogSumNumWf]
  set terms := (args.zip cofs).map (fun p =>
    CPoly.mulMod f (cscale p.1.1 (afDerivWf f p.1.2)) p.2) with hterms
  have hfold : ∀ (ts : List (DensePoly α)) (acc : DensePoly α),
      Ideal.Quotient.mk (afIdeal f) (toPoly (ts.foldl cadd acc))
        = Ideal.Quotient.mk (afIdeal f) (toPoly acc)
          + (ts.map (fun t => Ideal.Quotient.mk (afIdeal f) (toPoly t))).sum := by
    intro ts
    induction ts with
    | nil => intro acc; simp
    | cons t ts ih =>
      intro acc
      rw [List.foldl_cons, ih (cadd acc t)]
      simp only [denote, map_add, List.map_cons, List.sum_cons]
      ring
  rw [hfold terms ([] : DensePoly α)]
  rw [toPolyG_nil, map_zero, zero_add, hterms, List.map_map]
  rfl

omit [CDiffFieldSpec α] in
/-- The log part composes from the per-term residue match. -/
theorem isGeneralLogIntegralWf_of_residue_match (f logpart commonDenomQ : DensePoly α)
    (args : List (α × DensePoly α)) (cofs : List (DensePoly α))
    (hmatch : ((args.zip cofs).map (fun p =>
          Ideal.Quotient.mk (afIdeal f)
            (toPoly (CPoly.mulMod f (cscale p.1.1 (afDerivWf f p.1.2)) p.2)))).sum
        = Ideal.Quotient.mk (afIdeal f) (toPoly (CPoly.mulMod f logpart commonDenomQ))) :
    IsGeneralLogIntegralWf f logpart commonDenomQ args cofs := by
  rw [IsGeneralLogIntegralWf, mk_toPolyG_afLogSumNumWf_eq_sum, hmatch]

omit [CDiffFieldSpec α] in
/-- A one-term log part composes to `IsGeneralLogIntegralWf`. -/
theorem isGeneralLogIntegralWf_singleton (f logpart commonDenomQ : DensePoly α)
    (c : α) (u cof : DensePoly α)
    (hmatch : Ideal.Quotient.mk (afIdeal f)
          (toPoly (CPoly.mulMod f (cscale c (afDerivWf f u)) cof))
        = Ideal.Quotient.mk (afIdeal f) (toPoly (CPoly.mulMod f logpart commonDenomQ))) :
    IsGeneralLogIntegralWf f logpart commonDenomQ [(c, u)] [cof] := by
  apply isGeneralLogIntegralWf_of_residue_match
  simpa using hmatch

end DensePoly

/-! ### The logarithmic-derivative residue, general-carrier framing

The residue of `D(log u) = afDerivWf(u)/u` at a place over `x₀` equals the vanishing order of `u` there:
in the general setting `afDerivWf(u)/u` localizes (through `toPoly`) to the base-field log-derivative on
the place's uniformizer, so the base-field `logDeriv_residue_eq_multiplicity` carries the content. -/

namespace LogResidue

variable {K : Type*} [Field K]

/-! ### The residue-norm factoring: `genResidueResultant` roots = residues -/

/-- The residue-norm factors into the per-place residues: for `c ≠ 0` and a fiber multiset `fiber` with
per-place numerators `gval β`, `∏_{β ∈ fiber}(Z·c − gval β) = C(c)^{|fiber|}·∏_{β ∈ fiber}(Z − gval β /
c)`, exhibiting the residues `gval β / c`. -/
theorem genNormFactor (c : K) (fiber : Multiset K) (gval : K → K) (hc : c ≠ 0) :
    (fiber.map (fun β => Polynomial.X * Polynomial.C c - Polynomial.C (gval β))).prod
      = Polynomial.C c ^ Multiset.card fiber
        * (fiber.map (fun β => Polynomial.X - Polynomial.C (gval β / c))).prod := by
  -- each linear factor `Z·c − gval β = C c·(Z − gval β/c)`
  have hfac : ∀ β, Polynomial.X * Polynomial.C c - Polynomial.C (gval β)
      = Polynomial.C c * (Polynomial.X - Polynomial.C (gval β / c)) := by
    intro β
    have hcr : Polynomial.C c * Polynomial.C (gval β / c) = Polynomial.C (gval β) := by
      rw [← map_mul, mul_div_cancel₀ _ hc]
    rw [mul_sub, hcr, mul_comm (Polynomial.C c) Polynomial.X]
  rw [Multiset.map_congr rfl (fun β _ => hfac β)]
  -- `∏_β (C c · (Z − r β)) = (∏_β C c)·(∏_β (Z − r β))` (`prod_map_mul`), and `∏_β C c = C c^card`
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate]

/-- The residue-norm's root multiset is the per-place residues: for `c ≠ 0`, the roots of
`∏_{β ∈ fiber}(Z·c − gval β)` are `fiber.map (fun β => gval β / c)`. -/
theorem roots_genNorm (c : K) (fiber : Multiset K) (gval : K → K) (hc : c ≠ 0) :
    ((fiber.map (fun β => Polynomial.X * Polynomial.C c - Polynomial.C (gval β))).prod).roots
      = fiber.map (fun β => gval β / c) := by
  rw [genNormFactor c fiber gval hc]
  -- drop the nonzero leading scalar `C c^card = C (c^card)`
  rw [show (Polynomial.C c : K[X]) ^ Multiset.card fiber = Polynomial.C (c ^ Multiset.card fiber) from
      (map_pow _ _ _).symm,
    Polynomial.roots_C_mul _ (pow_ne_zero _ hc)]
  -- the product of monic linear factors `∏_β (Z − r β)` has roots `{r β}`
  rw [show (fiber.map (fun β => Polynomial.X - Polynomial.C (gval β / c)))
      = (fiber.map (fun β => gval β / c)).map (fun a => Polynomial.X - Polynomial.C a) by
      rw [Multiset.map_map]; rfl,
    Polynomial.roots_multiset_prod_X_sub_C]

/-- The residue resultant's roots are the per-place residues: given the product form
`R = C(lc)^N · ∏_{α₀ ∈ Droots} genNorm(α₀, Z)` with `Dprime α₀ ≠ 0` on `Droots`, `R.roots =
Droots.bind (fun α₀ => (fiber α₀).map (fun β => g α₀ β / Dprime α₀))`. -/
theorem roots_genResidueResultant_eq_residues (lc : K) (N : ℕ) (Droots : Multiset K)
    (Dprime : K → K) (fiber : K → Multiset K) (g : K → K → K)
    (hlc : lc ≠ 0)
    (hDp : ∀ α₀ ∈ Droots, Dprime α₀ ≠ 0)
    (R : K[X])
    (hR : R = Polynomial.C lc ^ N
      * (Droots.map (fun α₀ =>
          ((fiber α₀).map (fun β =>
            Polynomial.X * Polynomial.C (Dprime α₀) - Polynomial.C (g α₀ β))).prod)).prod) :
    R.roots = Droots.bind (fun α₀ => (fiber α₀).map (fun β => g α₀ β / Dprime α₀)) := by
  subst hR
  -- drop the nonzero leading scalar `C lc^N` (`lc ≠ 0`)
  rw [show (Polynomial.C lc : K[X]) ^ N = Polynomial.C (lc ^ N) from (map_pow _ _ _).symm,
    Polynomial.roots_C_mul _ (pow_ne_zero N hlc)]
  -- the product's roots are the `bind` of the per-root norm's roots (no factor is `0`)
  rw [Polynomial.roots_multiset_prod _ (by
    -- `0 ∉ map (genNorm ·) Droots`: each per-root norm is nonzero (its roots are the residues)
    rw [Multiset.mem_map]
    rintro ⟨α₀, hα, hα0⟩
    -- if the norm were `0` its root multiset would be `0`, but `roots_genNorm` gives the residues
    have hroots := roots_genNorm (Dprime α₀) (fiber α₀) (g α₀) (hDp α₀ hα)
    rw [hα0, Polynomial.roots_zero] at hroots
    -- `roots_genNorm` then asserts `0 = (fiber α₀).map (residue ·)`, so `card (fiber α₀) = 0`
    have hcard : Multiset.card (fiber α₀) = 0 := by
      have := congrArg Multiset.card hroots
      simpa [Multiset.card_map] using this.symm
    -- `card (fiber α₀) = 0` ⟹ `fiber α₀ = 0`, so the norm-product is the empty product `1 ≠ 0`
    rw [Multiset.card_eq_zero] at hcard
    rw [hcard] at hα0
    simp only [Multiset.map_zero, Multiset.prod_zero] at hα0
    exact one_ne_zero hα0)]
  -- per-root: `roots(genNorm α₀) = (fiber α₀).map (residue ·)`
  rw [Multiset.bind_map]
  refine Multiset.bind_congr (fun α₀ hα => ?_)
  exact roots_genNorm (Dprime α₀) (fiber α₀) (g α₀) (hDp α₀ hα)

end LogResidue

/-! ### The compute-bridge: `genResidueResultant`'s interpolation-uniqueness characterization -/

namespace DensePoly

/-- The interpolation-uniqueness characterization of `genResidueResultant`: if `R : ℚ[X]` has
`degree < cdeg f * cdeg D + 2` and agrees with the selected resultant at each node `k`, then
`toPoly (genResidueResultant f g Dder D) = R`. -/
theorem toPolyG_genResidueResultant_eq_of_eval [CPolyResultant DensePoly]
    (f g : DensePoly (DenseFrac ℚ)) (Dder : DenseFrac ℚ) (D : DensePoly ℚ)
    (R : ℚ[X])
    (hRdeg : R.degree < (cdeg f * cdeg D + 2 : ℕ))
    (hnode : ∀ k ∈ Finset.range (cdeg f * cdeg D + 1 + 1),
      R.eval ((k : ℚ))
        = CPolyResultant.compute (resYAtNode f g Dder ((k : ℚ))) D) :
    toPoly (genResidueResultant f g Dder D) = R := by
  classical
  -- Lean elaborates the engine's `(range n).map (fun k:ℕ => ((k:ℚ), …))` by lifting the tuple coercion to a
  -- DOUBLE map `((range n).map Nat.cast).map (fun z:ℚ => (z, …))`. We pin `pts` in exactly that doubly-mapped
  -- form (so `hpts` is `rfl` against the engine), and the list-shape lemmas compose over the two `List.map`s.
  -- `zs` = the `ℚ`-node abscissae. Build it via `List.range'` reused through `CField.natCast`-free `map`; pin it
  -- with `List.Nodup`/`length`/`mem` facts proven by the dedicated `range_map` lemmas (the coercion makes the
  -- literal `(range).map (↑·)` re-display as a `flatMap`/`do`-block, so we keep the facts, not the syntax).
  -- `zs` = the `ℚ`-node abscissae, kept as the EXPLICIT cast-map of `range` (`List.map_coe_range`) so the
  -- coercion does not re-lift into a `flatMap`. Facts proven by the `range`/`map` lemmas via `simp`.
  set zs : List ℚ := (List.range (cdeg f * cdeg D + 1 + 1)).map (Nat.cast) with hzs
  have hzs_len : zs.length = cdeg f * cdeg D + 1 + 1 := by
    rw [hzs, List.length_map, List.length_range]
  have hzs_nodup : zs.Nodup :=
    hzs ▸ List.Nodup.map (fun a b hab => Nat.cast_injective hab) List.nodup_range
  have hzs_mem : ∀ k, k ∈ List.range (cdeg f * cdeg D + 1 + 1) → ((k : ℚ)) ∈ zs := by
    intro k hk; rw [hzs, List.mem_map]; exact ⟨k, hk, rfl⟩
  set pts : List (ℚ × ℚ) :=
    zs.map (fun z => (z, CPolyResultant.compute (resYAtNode f g Dder z) D))
    with hpts
  -- bridge the engine's node list to `pts` STRUCTURALLY (no resultant evaluation): the engine's
  -- `(range).map (fun k:ℕ => let z:=↑k; (z, …))` and `pts = ((range).map ↑).map (fun z:ℚ => (z, …))` are the
  -- SAME up to `flatMap_pure_eq_map` (the lifted coercion) + `map_map`.
  have hcompute : genResidueResultant f g Dder D = cinterpolate pts := by
    rw [genResidueResultant, genResidueResultantWith, CPoly.interpolate_dense_eq, hpts, hzs]
    congr 1
    rw [List.map_map]
    -- the engine's inner `do let a ← range; pure ↑a` IS `range.map Nat.cast` (`flatMap_pure_eq_map`),
    -- then `map_map` collapses both sides to `range.map ((z,…) ∘ ↑)`
    rw [show (do let a ← List.range (cdeg f * cdeg D + 1 + 1); pure (↑a : ℚ))
        = (List.range (cdeg f * cdeg D + 1 + 1)).map (Nat.cast) from
      List.flatMap_pure_eq_map _ _, List.map_map]
  have htoK : ∀ q : ℚ, CFieldSpec.toK q = q := fun _ => rfl
  -- node-abscissa images = `zs`; reusable membership/length/nodup facts over the double map
  have hmempts : ∀ z, z ∈ zs →
      (z, CPolyResultant.compute (resYAtNode f g Dder z) D) ∈ pts := by
    intro z hz; rw [hpts, List.mem_map]; exact ⟨z, hz, rfl⟩
  have hfst : pts.map (fun p => CFieldSpec.toK p.1) = zs := by
    rw [hpts, List.map_map]
    simp only [htoK]
    rw [show (fun p : ℚ × ℚ => p.1) ∘ (fun z => (z, CPolyResultant.compute
        (resYAtNode f g Dder z) D)) = id from rfl, List.map_id]
  have hnodup : (pts.map (fun p => CFieldSpec.toK p.1)).Nodup := by rw [hfst]; exact hzs_nodup
  have hne : pts ≠ [] := by
    rw [hpts, Ne, List.map_eq_nil_iff]
    intro hzsnil; rw [hzsnil] at hzs_len; simp at hzs_len
  have hlen : pts.length = cdeg f * cdeg D + 1 + 1 := by
    rw [hpts, List.length_map, hzs_len]
  rw [hcompute]
  -- Lagrange uniqueness: degree `< #nodes` both sides, agreeing at the nodes
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (R := ℚ) (ι := ℕ)
    (s := Finset.range (cdeg f * cdeg D + 1 + 1))
    (v := fun k => (k : ℚ))
    (f := toPoly (cinterpolate pts)) (g := R)
    (fun a _ b _ hab => Nat.cast_injective hab) ?_ ?_ ?_
  · -- `degree (toPoly (cinterpolate pts)) < #nodes`
    rw [Finset.card_range, Nat.cast_withBot]
    have := degree_toPolyG_cinterpolateG_lt pts hne
    rw [hlen] at this
    simpa [Nat.cast_withBot] using this
  · -- `degree R < #nodes`: `cdeg f · cdeg D + 2 = #nodes`
    rw [Finset.card_range, Nat.cast_withBot]
    have hcard : (cdeg f * cdeg D + 1 + 1 : ℕ) = (cdeg f * cdeg D + 2 : ℕ) := by ring
    rw [hcard]
    exact hRdeg
  · -- agree at the nodes: `toPoly(cinterpolate pts)((k:ℚ)) = node value = R((k:ℚ))`
    intro k hk
    -- `(k:ℚ) ∈ zs` since `zs = (range n).map (↑·)` and `k ∈ range n`
    have hzmem : ((k : ℚ)) ∈ zs := by
      rw [hzs, List.mem_map]; exact ⟨k, by simpa using hk, rfl⟩
    have heval := eval_toPolyG_cinterpolateG pts hnodup (hmempts ((k : ℚ)) hzmem)
    rw [htoK, htoK] at heval
    rw [heval]
    exact (hnode k hk).symm

end DensePoly

/-! ### Composing rational + log into the full algebraic integral soundness `D(∫f) = f`

The full soundness `D(v + Σ cᵢ log uᵢ) = f` splits into the rational part `afDerivWf(v) = ratPart` and the
log part `IsGeneralLogIntegralWf`. Cross-multiplied by `commonDenomQ = ∏ uⱼ`, the composed predicate
`IsGeneralAlgebraicIntegralWf` follows from the two halves plus the split `f = ratPart + logPart`. -/

namespace DensePoly

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

/-- The fuel-free full general algebraic-integral soundness predicate. -/
def IsGeneralAlgebraicIntegralWf (f g v commonDenomQ : DensePoly α)
    (args : List (α × DensePoly α)) (cofs : List (DensePoly α)) : Prop :=
  Ideal.Quotient.mk (afIdeal f) (toPoly (CPoly.mulMod f (afDerivWf f v) commonDenomQ))
    + Ideal.Quotient.mk (afIdeal f) (toPoly (afLogSumNumWf f args cofs))
  = Ideal.Quotient.mk (afIdeal f) (toPoly (CPoly.mulMod f g commonDenomQ))

omit [CDiffFieldSpec α] in
/-- The fuel-free full general algebraic integral composes from Wf rational and log soundness. -/
theorem isGeneralAlgebraicIntegralWf_of_parts (f g v ratPart logPart commonDenomQ : DensePoly α)
    (args : List (α × DensePoly α)) (cofs : List (DensePoly α))
    (hrat : Ideal.Quotient.mk (afIdeal f)
          (toPoly (CPoly.mulMod f (afDerivWf f v) commonDenomQ))
        = Ideal.Quotient.mk (afIdeal f) (toPoly (CPoly.mulMod f ratPart commonDenomQ)))
    (hlog : IsGeneralLogIntegralWf f logPart commonDenomQ args cofs)
    (hsplit : Ideal.Quotient.mk (afIdeal f) (toPoly (CPoly.mulMod f ratPart commonDenomQ))
        + Ideal.Quotient.mk (afIdeal f) (toPoly (CPoly.mulMod f logPart commonDenomQ))
      = Ideal.Quotient.mk (afIdeal f) (toPoly (CPoly.mulMod f g commonDenomQ))) :
    IsGeneralAlgebraicIntegralWf f g v commonDenomQ args cofs := by
  rw [IsGeneralAlgebraicIntegralWf, hrat, hlog, hsplit]

end DensePoly

/-! ### Axiom audit (`#print axioms`)

The log-part predicates, the certificate bridge, the residue-norm factoring and root↔residue theorem, the
partial fraction, the compute-bridge, and the full composition carry only `[propext, Classical.choice,
Quot.sound]` — no `sorry`. -/

-- ★ Obligation 1's general ingredient: the general residue-norm factors into the per-place residues:
#print axioms LogResidue.genNormFactor

-- ★★ Obligation 1 MILESTONE (abstract): the general residue resultant's roots ARE the per-place residues:
#print axioms LogResidue.roots_genResidueResultant_eq_residues

-- ★★ The compute-bridge CLOSED: the interpolation-uniqueness characterization of the engine's `genResidueResultant`:
#print axioms DensePoly.toPolyG_genResidueResultant_eq_of_eval

-- The fuel-free log/capstone API, using `afDerivWf` and `afLogSumNumWf`:
#print axioms DensePoly.isGeneralLogTermWf_of_logCert
#print axioms DensePoly.mk_toPolyG_afLogSum2Wf
#print axioms DensePoly.mk_toPolyG_afLogSumNumWf_eq_sum
#print axioms DensePoly.isGeneralLogIntegralWf_of_residue_match
#print axioms DensePoly.isGeneralAlgebraicIntegralWf_of_parts

end DeepWiki.SymbolicIntegration
