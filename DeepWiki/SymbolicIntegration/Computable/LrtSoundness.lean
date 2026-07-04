import DeepWiki.SymbolicIntegration.Computable.LrtIntegrate
import DeepWiki.SymbolicIntegration.Computable.IntegrateTowerCorrectG

/-! # Symbolic-log soundness for the root-free LRT reduced integrator (G5, pass P1)

`IsIntegralResultLrtG` — the soundness contract for `cIntegrateReducedLrtG`'s **symbolic** log part
`[(Rᵢ, Sᵢ)]`, denoting `Σᵢ Σ_{Rᵢ(c)=0} c·(Δ Sᵢ(c,t))/Sᵢ(c,t)`. To handle **algebraic** residues without
building a `Differential (AlgebraicClosure K)` instance, it is stated over an arbitrary differential
extension `E` of `K = CFieldSpec.K α` in which every `Rᵢ` splits (the descent vehicle): `extendDeriv` /
`Differential.implicitDeriv` are already generic over any such `E`. See `docs/g5-lrt-soundness.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]

section Ext

variable {E : Type*} [Field E] [Algebra (CFieldSpec.K α) E]

/-- Base-change of a `K`-polynomial to `RatFunc E` (`K = CFieldSpec.K α`). -/
noncomputable def amGExt (p : (CFieldSpec.K α)[X]) : RatFunc E :=
  algebraMap E[X] (RatFunc E) (p.map (algebraMap (CFieldSpec.K α) E))

/-- The symbolic log argument `Sᵢ` (a list of `z`-polynomials, one per `t`-power) evaluated at a residue
`c ∈ E` and **monic-normalized in `t`**: the raw `E[t]` polynomial `Σₖ (Sᵢ[k] at z=c)·tᵏ` divided by its
leading `t`-coefficient. The monic normalization (Bronstein §2 Ex 2.7, `LrtMonicLogs.monicLrtLog`) is
**required for tower soundness** — the raw subresultant `Sᵢ(c) = sᵢ(c)·(monic gcd)` carries a
leading-coefficient unit `sᵢ(c)` whose *tower* log-derivative `D_base(sᵢ(c))/sᵢ(c)` does **not** vanish
(unlike the formal `d/dx` case), so the raw argument gives a spurious extra term. Dividing by the leading
coefficient turns `Sᵢ(c)` into the **monic gcd**, whose log-derivative is exactly the RT residue term. -/
noncomputable def evalLrtArg (Si : List (CPolyG α)) (c : E) : E[X] :=
  let raw : E[X] := (Si.zipIdx.map (fun p =>
    C ((toPolyG p.1).eval₂ (algebraMap (CFieldSpec.K α) E) c) * X ^ p.2)).sum
  raw * C raw.leadingCoeff⁻¹

variable [Differential E] [Algebra ℚ E]

/-- The `E`-tower derivation on `RatFunc E`: `extendDeriv` of `implicitDeriv (Dt base-changed to E)`. The
generic (any differential extension `E`) analogue of `towerFractionFieldDerivG`. -/
noncomputable def towerDerivExt (Dt : CPolyG α) : Derivation ℤ (RatFunc E) (RatFunc E) :=
  extendDeriv (Differential.implicitDeriv ((toPolyG Dt).map (algebraMap (CFieldSpec.K α) E)))

/-- The **algebraic residue sum** over `E`: `Σᵢ Σ_{c ∈ roots(Rᵢ in E)} c·(Δ Sᵢ(c,t))/Sᵢ(c,t)` — the honest
denotation of the symbolic LRT log part, summing over the residues (roots of each `Rᵢ`) in `E`. -/
noncomputable def logResidueSumLrtG (Dt : CPolyG α)
    (logs : List (CPolyG α × List (CPolyG α))) : RatFunc E :=
  (logs.map (fun p =>
    (((toPolyG p.1).map (algebraMap (CFieldSpec.K α) E)).roots.map (fun c =>
      algebraMap E (RatFunc E) c
        * (towerDerivExt Dt (algebraMap E[X] (RatFunc E) (evalLrtArg p.2 c))
            / algebraMap E[X] (RatFunc E) (evalLrtArg p.2 c)))).sum)).sum

/-- The per-pole logarithmic term `(Δ (t−β))/(t−β)` for a pole `β ∈ E`. -/
noncomputable def poleTerm (Dt : CPolyG α) (β : E) : RatFunc E :=
  towerDerivExt Dt (algebraMap E[X] (RatFunc E) (X - C β))
    / algebraMap E[X] (RatFunc E) (X - C β)

/-- The single-`(Rᵢ, Sᵢ)` residue term: `Σ_{c ∈ roots(Rᵢ in E)} c·(Δ Sᵢ(c,t))/Sᵢ(c,t)`. -/
noncomputable def logResidueTermLrtG (Dt : CPolyG α) (p : CPolyG α × List (CPolyG α)) : RatFunc E :=
  (((toPolyG p.1).map (algebraMap (CFieldSpec.K α) E)).roots.map (fun c =>
    algebraMap E (RatFunc E) c
      * (towerDerivExt Dt (algebraMap E[X] (RatFunc E) (evalLrtArg p.2 c))
          / algebraMap E[X] (RatFunc E) (evalLrtArg p.2 c)))).sum

omit [CDiffField α] [CDiffFieldSpec α] in
/-- `logResidueSumLrtG` is the sum of the per-`(Rᵢ, Sᵢ)` terms. -/
theorem logResidueSumLrtG_eq_sum (Dt : CPolyG α) (logs : List (CPolyG α × List (CPolyG α))) :
    logResidueSumLrtG (E := E) Dt logs = (logs.map (logResidueTermLrtG (E := E) Dt)).sum := rfl

omit [CDiffField α] [CDiffFieldSpec α] in
/-- `logResidueSumLrtG` of the empty log list is `0`. -/
@[simp] theorem logResidueSumLrtG_nil (Dt : CPolyG α) :
    logResidueSumLrtG (E := E) Dt ([] : List (CPolyG α × List (CPolyG α))) = 0 := rfl

omit [CDiffField α] [CDiffFieldSpec α] in
/-- `logResidueSumLrtG` peels the head. -/
theorem logResidueSumLrtG_cons (Dt : CPolyG α) (p : CPolyG α × List (CPolyG α))
    (rest : List (CPolyG α × List (CPolyG α))) :
    logResidueSumLrtG (E := E) Dt (p :: rest)
      = logResidueTermLrtG (E := E) Dt p + logResidueSumLrtG (E := E) Dt rest := by
  rw [logResidueSumLrtG_eq_sum, logResidueSumLrtG_eq_sum, List.map_cons, List.sum_cons]

/-! ### Log-derivative additivity (the residue↔pole reindexing core) -/

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Log-derivative additivity for the `E`-tower derivation.** `D(a·b)/(a·b) = D(a)/a + D(b)/b`. -/
theorem towerDerivExt_div_mul (Dt : CPolyG α) (a b : RatFunc E) (ha : a ≠ 0) (hb : b ≠ 0) :
    towerDerivExt Dt (a * b) / (a * b)
      = towerDerivExt Dt a / a + towerDerivExt Dt b / b := by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  field_simp
  ring

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Log-derivative of a product is the sum of log-derivatives**: `D(∏ xᵢ)/∏ xᵢ = Σ D(xᵢ)/xᵢ` (for nonzero
factors). This is the algebraic core of the residue↔pole reindexing — it splits the log-derivative of a
`gcd = ∏(t−β)` into the per-pole terms `monomial_residue_match_of_cancel` sums over. -/
theorem towerDerivExt_div_prod (Dt : CPolyG α) (l : Multiset (RatFunc E)) (hl : ∀ x ∈ l, x ≠ 0) :
    towerDerivExt Dt l.prod / l.prod = (l.map (fun x => towerDerivExt Dt x / x)).sum := by
  induction l using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have ha : a ≠ 0 := hl a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, x ≠ 0 := fun x hx => hl x (Multiset.mem_cons_of_mem hx)
    have hsp : s.prod ≠ 0 := Multiset.prod_ne_zero (fun h => (hs 0 h) rfl)
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      towerDerivExt_div_mul Dt a s.prod ha hsp, ih hs]

omit [CDiffField α] [CDiffFieldSpec α] in
/-- Log-derivative of a product of **polynomial** factors through `algebraMap`:
`D(⟦∏ pᵢ⟧)/⟦∏ pᵢ⟧ = Σ D(⟦pᵢ⟧)/⟦pᵢ⟧` (`⟦·⟧ = algebraMap E[X] (RatFunc E)`, nonzero factors). This is the
form applied to a `gcd = ∏(t−β)` — it produces the per-pole terms directly. -/
theorem towerDerivExt_div_algebraMap_prod (Dt : CPolyG α) (l : Multiset E[X]) (hl : ∀ p ∈ l, p ≠ 0) :
    towerDerivExt Dt (algebraMap E[X] (RatFunc E) l.prod) / algebraMap E[X] (RatFunc E) l.prod
      = (l.map (fun p => towerDerivExt Dt (algebraMap E[X] (RatFunc E) p)
          / algebraMap E[X] (RatFunc E) p)).sum := by
  rw [map_multiset_prod, towerDerivExt_div_prod Dt (l.map (algebraMap E[X] (RatFunc E))) (by
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact fun h => hl p hp (IsFractionRing.injective E[X] (RatFunc E) (by rw [h, map_zero])) ),
    Multiset.map_map]
  rfl

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Term-level assembly: the residue term is the residue-weighted per-pole sum.** Given that each
monic log argument `evalLrtArg Sᵢ c` factors as `∏_{β ∈ fac c}(t−β)` (the gcd as linear factors, P3), the
per-`Rᵢ` residue term becomes `Σ_{c ∈ roots Rᵢ} c·(Σ_{β ∈ fac c} poleTerm β)` — via the log-derivative
product split. Combined with `residue_pole_regroup` this collapses to the pole sum. -/
theorem logResidueTermLrtG_eq_pole_sum (Dt : CPolyG α) (p : CPolyG α × List (CPolyG α))
    (fac : E → Multiset E)
    (hfac : ∀ c ∈ ((toPolyG p.1).map (algebraMap (CFieldSpec.K α) E)).roots,
      evalLrtArg p.2 c = ((fac c).map (fun β => X - C β)).prod) :
    logResidueTermLrtG Dt p
      = (((toPolyG p.1).map (algebraMap (CFieldSpec.K α) E)).roots.map (fun c =>
          algebraMap E (RatFunc E) c * ((fac c).map (poleTerm Dt)).sum)).sum := by
  rw [logResidueTermLrtG]
  refine congrArg Multiset.sum (Multiset.map_congr rfl (fun c hc => ?_))
  rw [hfac c hc, towerDerivExt_div_algebraMap_prod Dt ((fac c).map (fun β => X - C β)) (by
    intro q hq
    rw [Multiset.mem_map] at hq
    obtain ⟨β, _, rfl⟩ := hq
    exact X_sub_C_ne_zero β), Multiset.map_map]
  rfl

end Ext

open scoped Classical in
/-- **Residue↔pole regrouping.** Grouping poles `β` by residue value `res β = c`, the *residue*-indexed sum
`Σ_c c·(Σ_{res β = c} term β)` equals the *pole*-indexed sum `Σ_β res(β)·term β`. This is the combinatorial
core connecting `logResidueSumLrtG` (residue-indexed, via the `Rᵢ` roots) to the pole sum that
`monomial_residue_match_of_cancel` proves equals `hNum/Dstar`. -/
theorem residue_pole_regroup {E : Type*} [Field E] (poles : Finset E) (res : E → E)
    (term : E → RatFunc E) :
    (∑ c ∈ poles.image res, algebraMap E (RatFunc E) c
        * (∑ β ∈ poles.filter (fun β => res β = c), term β))
      = ∑ β ∈ poles, algebraMap E (RatFunc E) (res β) * term β := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := poles) (t := poles.image res)
    (g := res) (fun β hβ => Finset.mem_image_of_mem res hβ)
    (fun β => algebraMap E (RatFunc E) (res β) * term β)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun β hβ => ?_)
  rw [Finset.mem_filter] at hβ
  rw [hβ.2]

/-- **Symbolic-log soundness for the LRT reduced result.** Over **any** differential extension `E` of `K =
CFieldSpec.K α` in which every residue polynomial `Rᵢ` splits, the `E`-tower derivative of the rational part
plus the algebraic residue sum equals `anum/aden` (base-changed to `E`). The `E`-quantification + splitting
hypothesis is the descent vehicle (instantiate `E` at a splitting field to prove; injectivity of the base
change gives the `K`-level statement). This is the root-free analogue of `IsIntegralResultG` handling
algebraic residues. -/
def IsIntegralResultLrtG (Dt anum aden : CPolyG α) (res : LrtResultG α) : Prop :=
  ∀ (E : Type*) [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E]
    [DifferentialAlgebra (CFieldSpec.K α) E],
    (∀ p ∈ res.logs,
      Polynomial.Splits ((toPolyG p.1).map (algebraMap (CFieldSpec.K α) E))) →
    (towerDerivExt Dt (amGExt (toPolyG res.rational.1) / amGExt (toPolyG res.rational.2))
          + logResidueSumLrtG Dt res.logs : RatFunc E)
      = amGExt (toPolyG anum) / amGExt (toPolyG aden)

end DeepWiki.SymbolicIntegration
