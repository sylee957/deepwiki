import DeepWiki.ComputableAlgebra.PolyEngineLawful
import DeepWiki.Algebra.PolynomialMatrixDegree

/-! # Representation-selected polynomial interpolation

`CPolyInterpolate` selects an executable interpolation algorithm for a polynomial representation.
`LawfulCPolyInterpolate` characterizes the selected interpolant by evaluation at distinct nodes and
the usual strict degree bound. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration

universe u v

/-- Executable interpolation selected by a computable polynomial representation. -/
class CPolyInterpolate (P : Type u → Type u) [CPoly P] [CPolyEngine P] where
  /-- Interpolate a polynomial through the supplied coefficient-field points. -/
  compute : {α : Type u} → [CField α] → List (α × α) → P α

/-- Laws characterizing a representation-selected interpolation algorithm. -/
class LawfulCPolyInterpolate (P : Type u → Type u) [CPoly P] [CPolyEngine P]
    [CPolyInterpolate P] : Prop where
  /-- The selected interpolant evaluates to every sampled value when the denoted nodes are distinct. -/
  eval_compute : ∀ {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (pts : List (α × α)),
    (pts.map (fun p => (CFieldSpec.toK p.1 : CFieldSpec.K α))).Nodup →
    ∀ {zk yk : α}, (zk, yk) ∈ pts →
      (CPoly.toPoly (CPolyInterpolate.compute (P := P) pts)).eval (CFieldSpec.toK zk) =
        CFieldSpec.toK yk
  /-- A nonempty selected interpolant has degree strictly below the number of samples. -/
  degree_compute_lt : ∀ {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (pts : List (α × α)), pts ≠ [] →
      (CPoly.toPoly (CPolyInterpolate.compute (P := P) pts)).degree < (pts.length : WithBot ℕ)

namespace CPolyInterpolate

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P]
variable {α : Type u} [CField α]

/-- Representation-generic numerator of a Lagrange basis polynomial. -/
private def defaultLagNum : List α → P α
  | [] => CPoly.one
  | z :: zs => CPolyEngine.mul (CPolyEngine.ofCoeffList [CCommRing.neg z, CCommRing.one])
      (defaultLagNum zs)

/-- Representation-generic Lagrange interpolation built only from selected engine operations. -/
def default (pts : List (α × α)) : P α :=
  let zs := pts.map Prod.fst
  let term : α × α → P α := fun (zk, yk) =>
    let others := zs.filter (fun zj => CCommRing.isZero (CField.sub zj zk) = false)
    let num := defaultLagNum others
    let denom := others.foldl (fun acc zj => CCommRing.mul acc (CField.sub zk zj)) CCommRing.one
    CPolyEngine.scale (CField.div yk denom) num
  CPolyEngine.cnorm (pts.foldl (fun acc p => CPolyEngine.add acc (term p)) CPoly.czero)

/-- One term of the representation-generic Lagrange interpolation algorithm. -/
private def defaultTerm (zs : List α) (p : α × α) : P α :=
  CPolyEngine.scale
    (CField.div p.2 ((zs.filter (fun zj => CCommRing.isZero (CField.sub zj p.1) = false)).foldl
      (fun acc zj => CCommRing.mul acc (CField.sub p.1 zj)) CCommRing.one))
    (defaultLagNum (zs.filter (fun zj => CCommRing.isZero (CField.sub zj p.1) = false)))

variable [CFieldSpec.{u,v} α] [LawfulCPolyEngine.{u,v} P]

/-- A selected coefficient-list linear factor denotes `X - C z`. -/
private theorem toPoly_ofCoeffList_linear (z : α) :
    CPoly.toPoly
      (CPolyEngine.ofCoeffList (P := P) [CCommRing.neg z, CCommRing.one]) =
        Polynomial.X - Polynomial.C (CFieldSpec.toK z) := by
  rw [LawfulCPolyEngine.toPoly_ofCoeffList]
  apply Polynomial.ext
  intro i
  rw [CPoly.coeff_toPoly, CPoly.coeff_ofList]
  rcases i with _ | i
  · simp [toR_eq_toK, CFieldSpec.toK_neg]
  rcases i with _ | i
  · simp [toR_eq_toK, CFieldSpec.toK_one]
  · simp [List.getD_eq_getElem?_getD, Polynomial.coeff_X, CFieldSpec.toK_zero]

/-- The selected denominator fold denotes the corresponding product of node differences. -/
private theorem toK_foldl_sub_mul (zk : α) (others : List α) (init : α) :
    CFieldSpec.toK
      (others.foldl (fun acc zj => CCommRing.mul acc (CField.sub zk zj)) init) =
      CFieldSpec.toK init *
        (others.map (fun zj => CFieldSpec.toK zk - CFieldSpec.toK zj)).prod := by
  induction others generalizing init with
  | nil => simp
  | cons z zs ih =>
    rw [List.foldl_cons, ih, CFieldSpec.toK_mul, CFieldSpec.toK_sub,
      List.map_cons, List.prod_cons]
    ring

/-- The selected denominator product is nonzero when every node differs from the base node. -/
private theorem prod_sub_ne_zero {zk : α} {others : List α}
    (hne : ∀ zj ∈ others, CFieldSpec.toK zj ≠ CFieldSpec.toK zk) :
    (others.map (fun zj => CFieldSpec.toK zk - CFieldSpec.toK zj)).prod ≠ 0 := by
  rw [Ne, List.prod_eq_zero_iff]
  intro hy
  rw [List.mem_map] at hy
  obtain ⟨zj, hzj, hzeq⟩ := hy
  exact hne zj hzj (sub_eq_zero.mp hzeq).symm

/-- The generic Lagrange numerator denotes the product of its linear factors. -/
@[denote] private theorem toPoly_defaultLagNum (zs : List α) :
    CPoly.toPoly (defaultLagNum (P := P) zs) =
      (zs.map (fun z => Polynomial.X - Polynomial.C (CFieldSpec.toK z))).prod := by
  induction zs with
  | nil => simp [defaultLagNum, CPoly.toPoly_one]
  | cons z zs ih =>
    rw [defaultLagNum, LawfulCPolyEngine.toPoly_mul, toPoly_ofCoeffList_linear, ih,
      List.map_cons, List.prod_cons]

/-- Denotation of one term of the generic Lagrange interpolation algorithm. -/
private theorem toPoly_defaultTerm (zk yk : α) (others : List α) :
    CPoly.toPoly
        (CPolyEngine.scale (P := P)
          (CField.div yk
            (others.foldl (fun acc zj => CCommRing.mul acc (CField.sub zk zj)) CCommRing.one))
          (defaultLagNum (P := P) others)) =
      Polynomial.C (CFieldSpec.toK yk /
        (others.map (fun zj => CFieldSpec.toK zk - CFieldSpec.toK zj)).prod) *
        (others.map (fun z => Polynomial.X - Polynomial.C (CFieldSpec.toK z))).prod := by
  rw [LawfulCPolyEngine.toPoly_scale, toPoly_defaultLagNum]
  simp only [toR_eq_toK, CFieldSpec.toK_div, toK_foldl_sub_mul,
    CFieldSpec.toK_one, one_mul]

/-- Evaluation of one generic Lagrange term at a denoted coefficient. -/
private theorem eval_toPoly_defaultTerm (zk yk : α) (others : List α)
    (x : CFieldSpec.K α) :
    (CPoly.toPoly
      (CPolyEngine.scale (P := P)
        (CField.div yk
          (others.foldl (fun acc zj => CCommRing.mul acc (CField.sub zk zj)) CCommRing.one))
        (defaultLagNum (P := P) others))).eval x =
      (CFieldSpec.toK yk /
        (others.map (fun zj => CFieldSpec.toK zk - CFieldSpec.toK zj)).prod) *
        (others.map (fun zj => x - CFieldSpec.toK zj)).prod := by
  rw [toPoly_defaultTerm, eval_mul, eval_C]
  congr 1
  rw [eval_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro zj _
  simp [Function.comp, eval_sub, eval_X, eval_C]

/-- A generic Lagrange term evaluates to its sampled value at its own node. -/
private theorem eval_toPoly_defaultTerm_at_self (zk yk : α) (others : List α)
    (hne : ∀ zj ∈ others, CFieldSpec.toK zj ≠ CFieldSpec.toK zk) :
    (CPoly.toPoly
      (CPolyEngine.scale (P := P)
        (CField.div yk
          (others.foldl (fun acc zj => CCommRing.mul acc (CField.sub zk zj)) CCommRing.one))
        (defaultLagNum (P := P) others))).eval (CFieldSpec.toK zk) = CFieldSpec.toK yk := by
  rw [eval_toPoly_defaultTerm, div_mul_cancel₀]
  exact prod_sub_ne_zero hne

/-- A generic Lagrange term vanishes at every other sampled node. -/
private theorem eval_toPoly_defaultTerm_at_other (zk yk x : α) (others : List α)
    (hx : x ∈ others) :
    (CPoly.toPoly
      (CPolyEngine.scale (P := P)
        (CField.div yk
          (others.foldl (fun acc zj => CCommRing.mul acc (CField.sub zk zj)) CCommRing.one))
        (defaultLagNum (P := P) others))).eval (CFieldSpec.toK x) = 0 := by
  rw [eval_toPoly_defaultTerm]
  have hz : (others.map (fun zj => CFieldSpec.toK x - CFieldSpec.toK zj)).prod = 0 := by
    rw [List.prod_eq_zero_iff, List.mem_map]
    exact ⟨x, hx, sub_self _⟩
  rw [hz, mul_zero]

/-- Reading a selected-addition fold gives the initial value plus the sum of all term denotations. -/
private theorem toPoly_foldl_defaultTerm (zs : List α) (pts : List (α × α)) (acc : P α) :
    CPoly.toPoly (pts.foldl
      (fun acc p => CPolyEngine.add acc (defaultTerm (P := P) zs p)) acc) =
      CPoly.toPoly acc +
        (pts.map (fun p => CPoly.toPoly (defaultTerm (P := P) zs p))).sum := by
  induction pts generalizing acc with
  | nil => simp
  | cons p pts ih =>
    rw [List.foldl_cons, ih, LawfulCPolyEngine.toPoly_add, List.map_cons, List.sum_cons]
    ring

/-- The generic interpolant denotes the sum of its Lagrange terms. -/
@[denote] theorem toPoly_default (pts : List (α × α)) :
    CPoly.toPoly (default (P := P) pts) =
      (pts.map (fun p => CPoly.toPoly (defaultTerm (P := P) (pts.map Prod.fst) p))).sum := by
  rw [default, LawfulCPolyEngine.toPoly_cnorm]
  change CPoly.toPoly (pts.foldl
    (fun acc p => CPolyEngine.add acc (defaultTerm (P := P) (pts.map Prod.fst) p))
    CPoly.czero) = _
  rw [toPoly_foldl_defaultTerm, CPoly.toPoly_czero, zero_add]

open scoped Classical in
/-- A nodup node list selects the unique sampled value from the interpolation-term sum. -/
private theorem sum_ite_eq_of_nodup_toK_fst (pts : List (α × α))
    (hnodup : (pts.map (fun p => CFieldSpec.toK p.1)).Nodup)
    {zk yk : α} (hmem : (zk, yk) ∈ pts) :
    (pts.map (fun p => if CFieldSpec.toK p.1 = CFieldSpec.toK zk
      then CFieldSpec.toK p.2 else 0)).sum = CFieldSpec.toK yk := by
  induction pts with
  | nil => simp at hmem
  | cons p ps ih =>
    rw [List.map_cons, List.sum_cons]
    rw [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hpnotin, hpsnodup⟩ := hnodup
    rcases List.mem_cons.mp hmem with hpeq | hpps
    · obtain rfl := hpeq
      rw [if_pos rfl]
      have hzero : (ps.map (fun q => if CFieldSpec.toK q.1 = CFieldSpec.toK zk
          then CFieldSpec.toK q.2 else 0)).sum = 0 := by
        apply List.sum_eq_zero
        intro w hw
        rw [List.mem_map] at hw
        obtain ⟨q, hq, rfl⟩ := hw
        rw [if_neg]
        intro hqzk
        exact hpnotin (by rw [List.mem_map]; exact ⟨q, hq, hqzk⟩)
      rw [hzero, add_zero]
    · have hp1 : CFieldSpec.toK p.1 ≠ CFieldSpec.toK zk := by
        intro h
        exact hpnotin (by rw [h, List.mem_map]; exact ⟨(zk, yk), hpps, rfl⟩)
      rw [if_neg hp1, zero_add]
      exact ih hpsnodup hpps

open scoped Classical in
/-- The generic default interpolant evaluates to every sampled value at distinct denoted nodes. -/
theorem eval_toPoly_default (pts : List (α × α))
    (hnodup : (pts.map (fun p => CFieldSpec.toK p.1)).Nodup)
    {zk yk : α} (hmem : (zk, yk) ∈ pts) :
    (CPoly.toPoly (default (P := P) pts)).eval (CFieldSpec.toK zk) = CFieldSpec.toK yk := by
  rw [toPoly_default]
  rw [show (List.map (fun p => CPoly.toPoly (defaultTerm (P := P) (pts.map Prod.fst) p)) pts).sum.eval
        (CFieldSpec.toK zk) =
      (Polynomial.evalRingHom (CFieldSpec.toK zk))
        (List.map (fun p => CPoly.toPoly (defaultTerm (P := P) (pts.map Prod.fst) p)) pts).sum from rfl,
    map_list_sum, List.map_map]
  set zs := pts.map Prod.fst with hzs
  have key : ∀ p ∈ pts,
      ((Polynomial.evalRingHom (CFieldSpec.toK zk)) ∘
          fun p => CPoly.toPoly (defaultTerm (P := P) zs p)) p =
        if CFieldSpec.toK p.1 = CFieldSpec.toK zk then CFieldSpec.toK p.2 else 0 := by
    rintro ⟨a, b⟩ hp
    simp only [Function.comp_apply, Polynomial.coe_evalRingHom, defaultTerm]
    by_cases hak : CFieldSpec.toK a = CFieldSpec.toK zk
    · rw [if_pos hak, ← hak]
      apply eval_toPoly_defaultTerm_at_self
      intro zj hzj
      rw [List.mem_filter] at hzj
      have hzj2 : CCommRing.isZero (CField.sub zj a) = false := by simpa using hzj.2
      rw [Bool.eq_false_iff, Ne, CFieldSpec.isZero_iff, CFieldSpec.toK_sub, sub_eq_zero] at hzj2
      exact hzj2
    · rw [if_neg hak]
      apply eval_toPoly_defaultTerm_at_other
      rw [List.mem_filter]
      refine ⟨by rw [hzs, List.mem_map]; exact ⟨(zk, yk), hmem, rfl⟩, ?_⟩
      have hgoal : CCommRing.isZero (CField.sub zk a) = false := by
        rw [Bool.eq_false_iff, Ne, CFieldSpec.isZero_iff, CFieldSpec.toK_sub, sub_eq_zero]
        exact fun h => hak h.symm
      simpa using hgoal
  rw [List.map_congr_left key]
  exact sum_ite_eq_of_nodup_toK_fst pts hnodup hmem

/-- Each generic interpolation term has degree at most its number of linear factors. -/
private theorem natDegree_toPoly_defaultTerm_le (zs : List α) (p : α × α) :
    (CPoly.toPoly (defaultTerm (P := P) zs p)).natDegree ≤
      (zs.filter (fun zj => CCommRing.isZero (CField.sub zj p.1) = false)).length := by
  obtain ⟨a, b⟩ := p
  rw [defaultTerm, toPoly_defaultTerm]
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_list_prod_le _).trans ?_
  rw [List.map_map]
  refine (List.sum_le_card_nsmul _ 1 ?_).trans ?_
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨zj, _, rfl⟩ := hx
    simp only [Function.comp_apply]
    exact natDegree_X_sub_C_le _
  · simp

/-- A nonempty generic default interpolant has degree below its number of samples. -/
theorem degree_toPoly_default_lt (pts : List (α × α)) (hne : pts ≠ []) :
    (CPoly.toPoly (default (P := P) pts)).degree < (pts.length : WithBot ℕ) := by
  rw [toPoly_default]
  have hlen : 1 ≤ pts.length := List.length_pos_iff.mpr hne
  refine lt_of_le_of_lt
    (degree_list_sum_le_of_forall_degree_le _ ((pts.length : ℕ) - 1 : ℕ) ?_) ?_
  · intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    apply Polynomial.degree_le_of_natDegree_le
    refine le_trans (natDegree_toPoly_defaultTerm_le (P := P) (pts.map Prod.fst) q) ?_
    have hq1 : q.1 ∈ pts.map Prod.fst := List.mem_map.mpr ⟨q, hq, rfl⟩
    have hfilt : ((pts.map Prod.fst).filter
        (fun zj => CCommRing.isZero (CField.sub zj q.1) = false)).length <
        (pts.map Prod.fst).length := by
      apply List.length_filter_lt_length_iff_exists.mpr
      refine ⟨q.1, hq1, ?_⟩
      have hz : CCommRing.isZero (CField.sub q.1 q.1) = true := by
        rw [CFieldSpec.isZero_iff, CFieldSpec.toK_sub, sub_self]
      simp [hz]
    rw [List.length_map] at hfilt
    omega
  · rw [Nat.cast_lt]
    omega

end CPolyInterpolate


namespace CPoly

variable {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyInterpolate P]

/-- Interpolate using the algorithm selected by polynomial representation `P`. -/
def interpolate {α : Type u} [CField α] (pts : List (α × α)) : P α :=
  CPolyInterpolate.compute pts

variable [LawfulCPolyInterpolate.{u,v} P]

/-- Selected interpolation evaluates to the sampled value at each distinct node. -/
theorem eval_toPoly_interpolate {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (pts : List (α × α))
    (hnodup : (pts.map (fun p => (CFieldSpec.toK p.1 : CFieldSpec.K α))).Nodup)
    {zk yk : α} (hmem : (zk, yk) ∈ pts) :
    (toPoly (interpolate (P := P) pts)).eval (CFieldSpec.toK zk) = CFieldSpec.toK yk := by
  exact LawfulCPolyInterpolate.eval_compute pts hnodup hmem

/-- A nonempty selected interpolant has degree strictly below the number of samples. -/
theorem degree_toPoly_interpolate_lt {α : Type u} [CField α] [CFieldSpec.{u,v} α]
    (pts : List (α × α)) (hne : pts ≠ []) :
    (toPoly (interpolate (P := P) pts)).degree < (pts.length : WithBot ℕ) := by
  exact LawfulCPolyInterpolate.degree_compute_lt pts hne

end CPoly

end DeepWiki.SymbolicIntegration
