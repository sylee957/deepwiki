import DeepWiki.SymbolicIntegration.Computable.LrtIntegrate
import DeepWiki.SymbolicIntegration.Computable.IntegrateTowerCorrectG
import DeepWiki.SymbolicIntegration.Computable.SubresultantTowerSpec
import DeepWiki.SymbolicIntegration.LrtGeneralDerivation
import DeepWiki.SymbolicIntegration.Computable.ResidueMatchSoundness

/-! # Symbolic-log soundness for the root-free LRT reduced integrator (G5, pass P1)

`IsIntegralResultLrtG` — the soundness contract for `cIntegrateReducedLrtG`'s **symbolic** log part
`[(Rᵢ, Sᵢ)]`, denoting `Σᵢ Σ_{Rᵢ(c)=0} c·(Δ Sᵢ(c,t))/Sᵢ(c,t)`. To handle **algebraic** residues without
building a `Differential (AlgebraicClosure K)` instance, it is stated over an arbitrary differential
extension `E` of `K = CFieldSpec.K α` in which every `Rᵢ` splits (the descent vehicle): `extendDeriv` /
`Differential.implicitDeriv` are already generic over any such `E`. See `docs/g5-lrt-soundness.md`. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-- The coefficient-list polynomial `Σ_{(a,k) ∈ l.zipIdx s} C a · Xᵏ = Σ_{i<len} C(l[i])·X^{s+i}`. -/
theorem zipIdx_C_mul_X_pow_sum_eq {R : Type*} [Semiring R] (l : List R) (s : ℕ) :
    ((l.zipIdx s).map (fun p : R × ℕ => Polynomial.C p.1 * Polynomial.X ^ p.2)).sum
      = ∑ i ∈ Finset.range l.length, Polynomial.C (l.getD i 0) * Polynomial.X ^ (s + i) := by
  induction l generalizing s with
  | nil => simp
  | cons a t ih =>
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, ih (s + 1), List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
    rw [add_comm (Polynomial.C a * Polynomial.X ^ s)]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show s + 1 + i = s + (i + 1) from by omega]

/-- The `n`-th coefficient of the coefficient-list polynomial is `l.getD n 0`. -/
theorem zipIdx_C_mul_X_pow_sum_coeff {R : Type*} [Semiring R] (l : List R) (n : ℕ) :
    (((l.zipIdx).map (fun p : R × ℕ => Polynomial.C p.1 * Polynomial.X ^ p.2)).sum).coeff n
      = l.getD n 0 := by
  rw [zipIdx_C_mul_X_pow_sum_eq l 0]
  simp only [Nat.zero_add, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
  by_cases hn : n < l.length
  · rw [if_pos hn]
  · rw [if_neg hn, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

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

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **`evalLrtArg`'s raw sum is the base-changed abstract polynomial.** Given the G4c coefficient identity
`toPolyG (Sᵢ.getD n []) = P.coeff n` (P the abstract `lrtSubresultantGen`), the computable raw sum equals
`P.map (eval₂RingHom (algebraMap K E) c)` (`= S`, the base-changed subresultant at `z = c`). -/
theorem raw_eq_map (Si : List (CPolyG α)) (c : E) (P : ((CFieldSpec.K α)[X])[X])
    (hg4c : ∀ n, toPolyG (Si.getD n []) = P.coeff n) :
    (Si.zipIdx.map (fun p => Polynomial.C ((toPolyG p.1).eval₂ (algebraMap (CFieldSpec.K α) E) c)
        * Polynomial.X ^ p.2)).sum
      = P.map (Polynomial.eval₂RingHom (algebraMap (CFieldSpec.K α) E) c) := by
  have hcommute : (Si.zipIdx.map (fun p => Polynomial.C ((toPolyG p.1).eval₂
        (algebraMap (CFieldSpec.K α) E) c) * Polynomial.X ^ p.2))
      = (Si.map (fun sk => (toPolyG sk).eval₂ (algebraMap (CFieldSpec.K α) E) c)).zipIdx.map
        (fun p : E × ℕ => Polynomial.C p.1 * Polynomial.X ^ p.2) := by
    rw [List.zipIdx_map, List.map_map]; rfl
  rw [hcommute]
  ext n
  rw [zipIdx_C_mul_X_pow_sum_coeff, Polynomial.coeff_map, Polynomial.coe_eval₂RingHom, ← hg4c n,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases Si[n]? with
  | none => simp [toPolyG_nil]
  | some sk => simp

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **P3: the monic log argument is the residue-pole product.** Given the G4c coefficient identity and that
the base-changed subresultant `S` is similar to `∏_{β}(t−β)` (G3 `~gcd` + G2 `gcd=∏`), `evalLrtArg Sᵢ c =
∏_{β}(t−β)`. Composes `raw_eq_map` (`raw = S`) with `monicNormalize_eq_of_isSimilar_prod` (`monic(S) = ∏`). -/
theorem evalLrtArg_eq_prod (Si : List (CPolyG α)) (c : E) (A D B : (CFieldSpec.K α)[X]) (j : ℕ)
    (poles : Multiset E) (hφ : Function.Injective (algebraMap (CFieldSpec.K α) E))
    (hg4c : ∀ n, toPolyG (Si.getD n []) = (lrtSubresultantGen A D B j).coeff n)
    (hsim : IsSimilar (subresultant (D.map (algebraMap (CFieldSpec.K α) E))
        (A.map (algebraMap (CFieldSpec.K α) E)
          - Polynomial.C c * B.map (algebraMap (CFieldSpec.K α) E)) D.natDegree (D.natDegree - 1) j)
      (poles.map (fun β => Polynomial.X - Polynomial.C β)).prod) :
    evalLrtArg Si c = (poles.map (fun β => Polynomial.X - Polynomial.C β)).prod := by
  have hraw : (Si.zipIdx.map (fun p => Polynomial.C
        ((toPolyG p.1).eval₂ (algebraMap (CFieldSpec.K α) E) c) * Polynomial.X ^ p.2)).sum
      = subresultant (D.map (algebraMap (CFieldSpec.K α) E))
        (A.map (algebraMap (CFieldSpec.K α) E)
          - Polynomial.C c * B.map (algebraMap (CFieldSpec.K α) E)) D.natDegree (D.natDegree - 1) j := by
    rw [raw_eq_map Si c (lrtSubresultantGen A D B j) hg4c,
      lrtSubresultantGen_map_eval₂ _ A D B c j hφ]
  simp only [evalLrtArg]
  rw [hraw]
  exact monicNormalize_eq_of_isSimilar_prod poles hsim

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **P3 for the engine's parametric subresultant.** `hg4c` discharged by G4c
(`toPolyG_cSubresultantParam_getD`): `evalLrtArg (cSubresultantParam Dstar hNum Dd (cdegG Dstar)(cdegG Dd) j) c
= ∏_{β}(t−β)`, given `deg Dd = deg Dstar − 1` and `IsSimilar S (∏)`. -/
theorem evalLrtArg_cSubresultantParam_eq_prod [CharZero (CFieldSpec.K α)]
    (Dstar hNum Dd : CPolyG α) (c : E) (j : ℕ) (poles : Multiset E)
    (hm : cdegG Dd = cdegG Dstar - 1)
    (hφ : Function.Injective (algebraMap (CFieldSpec.K α) E))
    (hsim : IsSimilar (subresultant ((toPolyG Dstar).map (algebraMap (CFieldSpec.K α) E))
        ((toPolyG hNum).map (algebraMap (CFieldSpec.K α) E)
          - Polynomial.C c * (toPolyG Dd).map (algebraMap (CFieldSpec.K α) E))
        (toPolyG Dstar).natDegree ((toPolyG Dstar).natDegree - 1) j)
      (poles.map (fun β => Polynomial.X - Polynomial.C β)).prod) :
    evalLrtArg (cSubresultantParam Dstar hNum Dd (cdegG Dstar) (cdegG Dd) j) c
      = (poles.map (fun β => Polynomial.X - Polynomial.C β)).prod :=
  evalLrtArg_eq_prod _ c (toPolyG hNum) (toPolyG Dstar) (toPolyG Dd) j poles hφ
    (fun n => toPolyG_cSubresultantParam_getD Dstar hNum Dd j n hm) hsim

variable [Differential E] [Algebra ℚ E]

/-- The `E`-tower derivation on `RatFunc E`: `extendDeriv` of `implicitDeriv (Dt base-changed to E)`. The
generic (any differential extension `E`) analogue of `towerFractionFieldDerivG`. -/
noncomputable def towerDerivExt (Dt : CPolyG α) : Derivation ℤ (RatFunc E) (RatFunc E) :=
  extendDeriv (Differential.implicitDeriv ((toPolyG Dt).map (algebraMap (CFieldSpec.K α) E)))

omit [CDiffField α] [CDiffFieldSpec α] in
/-- **Quotient rule for `towerDerivExt`** (the `E`-analogue of `towerFractionFieldDerivG_div`): for `E`-polys
`P, Q`, `Δ(P/Q) = (Δ'P·Q − P·Δ'Q)/Q²` in `RatFunc E`, where `Δ' = implicitDeriv (Dt base-changed to E)`. -/
theorem towerDerivExt_div (Dt : CPolyG α) (P Q : E[X]) :
    towerDerivExt Dt (algebraMap E[X] (RatFunc E) P / algebraMap E[X] (RatFunc E) Q)
      = (algebraMap E[X] (RatFunc E)
            (Differential.implicitDeriv ((toPolyG Dt).map (algebraMap (CFieldSpec.K α) E)) P)
          * algebraMap E[X] (RatFunc E) Q
          - algebraMap E[X] (RatFunc E) P
            * algebraMap E[X] (RatFunc E)
                (Differential.implicitDeriv ((toPolyG Dt).map (algebraMap (CFieldSpec.K α) E)) Q))
        / (algebraMap E[X] (RatFunc E) Q) ^ 2 := by
  rw [towerDerivExt, ← RatFunc.mk_eq_div, extendDeriv_mk, RatFunc.mk_eq_div, map_sub, map_mul,
    map_mul, map_pow]

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
/-- Rewrite the residue sum termwise: if each `(Rᵢ, Sᵢ)` term equals `f p`, then `logResidueSumLrtG = Σ f`. -/
theorem logResidueSumLrtG_eq_termwise (Dt : CPolyG α) (logs : List (CPolyG α × List (CPolyG α)))
    (f : CPolyG α × List (CPolyG α) → RatFunc E)
    (hterm : ∀ p ∈ logs, logResidueTermLrtG Dt p = f p) :
    logResidueSumLrtG (E := E) Dt logs = (logs.map f).sum := by
  rw [logResidueSumLrtG_eq_sum]
  exact congrArg List.sum (List.map_congr_left hterm)

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

open scoped Differential Classical in
omit [CDiffField α] [CDiffFieldSpec α] in
/-- **The residue-weighted pole sum is the normal part** (P5 endpoint, over `E`). Instantiating the
tower residue-match identity `monomial_residue_match_of_cancel` at `K := E` with derivation data
`v = (toPolyG Dt).map φ` (so `poleTerm Dt β` is literally its `extendDeriv(implicitDeriv v)(t−β)/(t−β)`
summand): the residue-weighted pole sum `Σ_β res(β)·poleTerm β` equals `a/∏_{β∈s}(t−β)`, where the RT
residue `res β = a(β)/D(∏)(β)` and `hcancel` is the (automatically-true for a primitive `Dt`)
polynomial-part cancellation. -/
theorem pole_sum_eq_normalPart (Dt : CPolyG α) (a : E[X]) (s : Finset E)
    (hA : a.degree < s.card)
    (hnorm : ∀ β ∈ s, ((toPolyG Dt).map (algebraMap (CFieldSpec.K α) E)).eval β ≠ β′)
    (hcancel : ∑ β ∈ s, algebraMap E[X] (RatFunc E)
        (C (a.eval β / (Differential.implicitDeriv ((toPolyG Dt).map (algebraMap (CFieldSpec.K α) E))
              (Lagrange.nodal s id)).eval β)
          * ((((toPolyG Dt).map (algebraMap (CFieldSpec.K α) E)) - C (β′)) /ₘ (X - C β))) = 0) :
    ∑ β ∈ s, algebraMap E (RatFunc E)
          (a.eval β / (Differential.implicitDeriv ((toPolyG Dt).map (algebraMap (CFieldSpec.K α) E))
              (Lagrange.nodal s id)).eval β)
        * poleTerm Dt β
      = algebraMap E[X] (RatFunc E) a / algebraMap E[X] (RatFunc E) (Lagrange.nodal s id) := by
  rw [← ResidueMatchTower.monomial_residue_match_of_cancel s a
        ((toPolyG Dt).map (algebraMap (CFieldSpec.K α) E)) hA hnorm hcancel]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  congr 1

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

open scoped Classical in
/-- **Per-`Rᵢ` residue term = finset pole sum.** When `Rᵢ`'s roots (in `E`) are exactly the residue values
of a pole set `polesᵢ` and each monic log argument factors over the residue-`c` poles
(`fac c = polesᵢ.filter (res · = c)`), the residue term collapses to the pole sum
`Σ_{β ∈ polesᵢ} res(β)·poleTerm β`. Chains `logResidueTermLrtG_eq_pole_sum` (product split) with
`residue_pole_regroup` (residue↔pole). -/
theorem logResidueTermLrtG_eq_finset_pole_sum {α : Type*} [CField α] [CFieldSpec α] {E : Type*}
    [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E]
    (Dt : CPolyG α) (p : CPolyG α × List (CPolyG α)) (polesᵢ : Finset E) (res : E → E)
    (hroots : ((toPolyG p.1).map (algebraMap (CFieldSpec.K α) E)).roots = (polesᵢ.image res).val)
    (hfac : ∀ c ∈ ((toPolyG p.1).map (algebraMap (CFieldSpec.K α) E)).roots,
      evalLrtArg p.2 c = ((polesᵢ.filter (fun β => res β = c)).val.map (fun β => X - C β)).prod) :
    logResidueTermLrtG Dt p = ∑ β ∈ polesᵢ, algebraMap E (RatFunc E) (res β) * poleTerm Dt β := by
  rw [logResidueTermLrtG_eq_pole_sum Dt p
    (fun c => (polesᵢ.filter (fun β => res β = c)).val) hfac, hroots]
  exact residue_pole_regroup polesᵢ res (poleTerm Dt)

/-- **A list-indexed disjoint partition splits a `Finset` sum.** For pairwise-disjoint per-index pole sets
`polesOf`, the list-sum of per-index `Finset` sums equals the `Finset` sum over their union — the pure
combinatorial fact behind `hpart`. -/
theorem sum_over_list_partition {ι : Type*} {γ : Type*} [DecidableEq γ] {M : Type*} [AddCommMonoid M]
    (l : List ι) (polesOf : ι → Finset γ) (g : γ → M)
    (hdisj : l.Pairwise (fun p q => Disjoint (polesOf p) (polesOf q))) :
    (l.map (fun p => ∑ β ∈ polesOf p, g β)).sum
      = ∑ β ∈ (l.map polesOf).foldr (· ∪ ·) ∅, g β := by
  have hmemfold : ∀ (L : List (Finset γ)) (β : γ), β ∈ L.foldr (· ∪ ·) ∅ → ∃ s ∈ L, β ∈ s := by
    intro L β hβ
    induction L with
    | nil => simp at hβ
    | cons hd u ih =>
      rw [List.foldr_cons, Finset.mem_union] at hβ
      rcases hβ with h | h
      · exact ⟨hd, List.mem_cons_self, h⟩
      · obtain ⟨s', hs', hβ'⟩ := ih h
        exact ⟨s', List.mem_cons_of_mem hd hs', hβ'⟩
  induction l with
  | nil => simp
  | cons p t ih =>
    rw [List.pairwise_cons] at hdisj
    have hpt : Disjoint (polesOf p) ((t.map polesOf).foldr (· ∪ ·) ∅) := by
      rw [Finset.disjoint_right]
      intro β hβ hβp
      obtain ⟨s, hs, hβs⟩ := hmemfold (t.map polesOf) β hβ
      rw [List.mem_map] at hs
      obtain ⟨q, hqt, rfl⟩ := hs
      exact (Finset.disjoint_left.mp (hdisj.1 q hqt) hβp) hβs
    rw [List.map_cons, List.sum_cons, List.map_cons, List.foldr_cons,
      Finset.sum_union hpt, ih hdisj.2]

open scoped Classical in
/-- **Log-part sum in pole form (partition assembly).** Summing the per-`Rᵢ` pole sums over a per-entry
pole set `polesOf` that tiles the full pole set: `logResidueSumLrtG = Σ_{β ∈ allpoles} res(β)·poleTerm β`.
Chains `logResidueSumLrtG_eq_termwise` (sum over entries) with `logResidueTermLrtG_eq_finset_pole_sum`
(each entry ↦ its pole sum). `hpart` is the structural fact that the entries' pole sets partition
`allpoles` (the LRT/Yun fiber-size decomposition). -/
theorem logResidueSumLrtG_eq_poleSum {α : Type*} [CField α] [CFieldSpec α] {E : Type*}
    [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E]
    (Dt : CPolyG α) (logs : List (CPolyG α × List (CPolyG α))) (allpoles : Finset E) (res : E → E)
    (polesOf : CPolyG α × List (CPolyG α) → Finset E)
    (hroots : ∀ p ∈ logs, ((toPolyG p.1).map (algebraMap (CFieldSpec.K α) E)).roots
      = ((polesOf p).image res).val)
    (hfac : ∀ p ∈ logs, ∀ c ∈ ((toPolyG p.1).map (algebraMap (CFieldSpec.K α) E)).roots,
      evalLrtArg p.2 c = (((polesOf p).filter (fun β => res β = c)).val.map (fun β => X - C β)).prod)
    (hpart : (logs.map (fun p => ∑ β ∈ polesOf p,
        algebraMap E (RatFunc E) (res β) * poleTerm Dt β)).sum
      = ∑ β ∈ allpoles, algebraMap E (RatFunc E) (res β) * poleTerm Dt β) :
    logResidueSumLrtG Dt logs = ∑ β ∈ allpoles, algebraMap E (RatFunc E) (res β) * poleTerm Dt β := by
  rw [logResidueSumLrtG_eq_termwise Dt logs
      (fun p => ∑ β ∈ polesOf p, algebraMap E (RatFunc E) (res β) * poleTerm Dt β)
      (fun p hp => logResidueTermLrtG_eq_finset_pole_sum Dt p (polesOf p) res (hroots p hp) (hfac p hp))]
  exact hpart

open scoped Differential Classical in
/-- **LRT log-part soundness (the named theorem).** The tower derivative of the LRT symbolic log part
denotes the normal integrand: `logResidueSumLrtG Dt logs = hNum/Dstar` over `E`, where `Dstar` splits as
`∏_{β ∈ allpoles}(t−β)`. Composes `logResidueSumLrtG_eq_poleSum` (log sum ↦ residue-weighted pole sum,
over a pole partition `polesOf`) with `pole_sum_eq_normalPart` (the Rothstein–Trager residue match
`Σ_β res(β)·poleTerm β = hNum/Dstar`). The residue is fixed to the RT form
`res β = hNum(β)/D(∏)(β)`. -/
theorem logResidueSumLrtG_eq_normalPart {α : Type*} [CField α] [CFieldSpec α] {E : Type*}
    [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E]
    (Dt hNum : CPolyG α) (logs : List (CPolyG α × List (CPolyG α))) (allpoles : Finset E)
    (polesOf : CPolyG α × List (CPolyG α) → Finset E)
    (hroots : ∀ p ∈ logs, ((toPolyG p.1).map (algebraMap (CFieldSpec.K α) E)).roots
      = ((polesOf p).image (fun β => ((toPolyG hNum).map (algebraMap (CFieldSpec.K α) E)).eval β
          / (Differential.implicitDeriv ((toPolyG Dt).map (algebraMap (CFieldSpec.K α) E))
              (Lagrange.nodal allpoles id)).eval β)).val)
    (hfac : ∀ p ∈ logs, ∀ c ∈ ((toPolyG p.1).map (algebraMap (CFieldSpec.K α) E)).roots,
      evalLrtArg p.2 c = (((polesOf p).filter (fun β =>
          ((toPolyG hNum).map (algebraMap (CFieldSpec.K α) E)).eval β
            / (Differential.implicitDeriv ((toPolyG Dt).map (algebraMap (CFieldSpec.K α) E))
                (Lagrange.nodal allpoles id)).eval β = c)).val.map (fun β => X - C β)).prod)
    (hpart : (logs.map (fun p => ∑ β ∈ polesOf p,
        algebraMap E (RatFunc E) (((toPolyG hNum).map (algebraMap (CFieldSpec.K α) E)).eval β
            / (Differential.implicitDeriv ((toPolyG Dt).map (algebraMap (CFieldSpec.K α) E))
                (Lagrange.nodal allpoles id)).eval β) * poleTerm Dt β)).sum
      = ∑ β ∈ allpoles, algebraMap E (RatFunc E)
          (((toPolyG hNum).map (algebraMap (CFieldSpec.K α) E)).eval β
            / (Differential.implicitDeriv ((toPolyG Dt).map (algebraMap (CFieldSpec.K α) E))
                (Lagrange.nodal allpoles id)).eval β) * poleTerm Dt β)
    (hA : ((toPolyG hNum).map (algebraMap (CFieldSpec.K α) E)).degree < allpoles.card)
    (hnorm : ∀ β ∈ allpoles, ((toPolyG Dt).map (algebraMap (CFieldSpec.K α) E)).eval β ≠ β′)
    (hcancel : ∑ β ∈ allpoles, algebraMap E[X] (RatFunc E)
        (C (((toPolyG hNum).map (algebraMap (CFieldSpec.K α) E)).eval β
              / (Differential.implicitDeriv ((toPolyG Dt).map (algebraMap (CFieldSpec.K α) E))
                  (Lagrange.nodal allpoles id)).eval β)
          * ((((toPolyG Dt).map (algebraMap (CFieldSpec.K α) E)) - C (β′)) /ₘ (X - C β))) = 0) :
    logResidueSumLrtG Dt logs
      = algebraMap E[X] (RatFunc E) ((toPolyG hNum).map (algebraMap (CFieldSpec.K α) E))
        / algebraMap E[X] (RatFunc E) (Lagrange.nodal allpoles id) := by
  rw [logResidueSumLrtG_eq_poleSum Dt logs allpoles _ polesOf hroots hfac hpart]
  exact pole_sum_eq_normalPart Dt ((toPolyG hNum).map (algebraMap (CFieldSpec.K α) E)) allpoles
    hA hnorm hcancel

/-- **LRT field-identity assembler** (the analogue of `field_identity_of_reducedG_of_residueMatch`, over
`E`). Given the log-part match `hlog` (`logResidueSumLrtG = hNum/Dstar`, from
`logResidueSumLrtG_eq_normalPart`) and the Hermite half `hherm` (`D(g) + hNum/Dstar = a/d`), the full
reduced field identity `D(g) + logResidueSumLrtG = a/d` holds. -/
theorem field_identity_lrt_of_hherm_of_logMatch {α : Type*} [CField α] [CFieldSpec α] {E : Type*}
    [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E]
    (Dt gnum gden hNum hDen anum aden : CPolyG α) (logs : List (CPolyG α × List (CPolyG α)))
    (hlog : (logResidueSumLrtG Dt logs : RatFunc E) = amGExt (toPolyG hNum) / amGExt (toPolyG hDen))
    (hherm : (towerDerivExt Dt (amGExt (toPolyG gnum) / amGExt (toPolyG gden))
          + amGExt (toPolyG hNum) / amGExt (toPolyG hDen) : RatFunc E)
        = amGExt (toPolyG anum) / amGExt (toPolyG aden)) :
    (towerDerivExt Dt (amGExt (toPolyG gnum) / amGExt (toPolyG gden)) + logResidueSumLrtG Dt logs
        : RatFunc E)
      = amGExt (toPolyG anum) / amGExt (toPolyG aden) := by
  rw [hlog]; exact hherm

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

/-- **`IsIntegralResultLrtG` from the log match + Hermite half.** Packages `field_identity_lrt_of_hherm_of_
logMatch` under the `E`-quantifier: given, over every splitting extension `E`, the log-part match `hlog`
(`logResidueSumLrtG res.logs = hNum/Dstar`) and the Hermite half `hherm` (`D(g) + hNum/Dstar = a/d`), the
soundness predicate `IsIntegralResultLrtG` holds. This is the final-assembly skeleton: what remains is
discharging `hlog` (via `logResidueSumLrtG_eq_normalPart` + the Yun partition) and `hherm` (base-change of
the Hermite tower soundness) for `res = cIntegrateReducedLrtG`. -/
theorem isIntegralResultLrtG_of_hherm_of_logMatch.{u} (Dt anum aden : CPolyG α) (res : LrtResultG α)
    (hNum hDen : CPolyG α)
    (hlog : ∀ (E : Type u) [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E]
        [DifferentialAlgebra (CFieldSpec.K α) E],
        (∀ p ∈ res.logs, Polynomial.Splits ((toPolyG p.1).map (algebraMap (CFieldSpec.K α) E))) →
        (logResidueSumLrtG Dt res.logs : RatFunc E) = amGExt (toPolyG hNum) / amGExt (toPolyG hDen))
    (hherm : ∀ (E : Type u) [Field E] [Algebra (CFieldSpec.K α) E] [Differential E] [Algebra ℚ E]
        [DifferentialAlgebra (CFieldSpec.K α) E],
        (towerDerivExt Dt (amGExt (toPolyG res.rational.1) / amGExt (toPolyG res.rational.2))
            + amGExt (toPolyG hNum) / amGExt (toPolyG hDen) : RatFunc E)
          = amGExt (toPolyG anum) / amGExt (toPolyG aden)) :
    IsIntegralResultLrtG.{_, u} Dt anum aden res := by
  intro E _ _ _ _ _ hsplits
  exact field_identity_lrt_of_hherm_of_logMatch Dt res.rational.1 res.rational.2 hNum hDen anum aden
    res.logs (hlog E hsplits) (hherm E)

end DeepWiki.SymbolicIntegration
