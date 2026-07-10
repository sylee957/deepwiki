import DeepWiki.SymbolicIntegration.Engine.FuelFreeGcd
import DeepWiki.ComputableAlgebra.GenericBezout
import DeepWiki.ComputableAlgebra.PolyGcdAlgorithms
import DeepWiki.SymbolicIntegration.Engine.MonomialDeriv

/-! # Generic Bézout/Diophantine helpers

Bézout cofactors, the extended-Euclidean split, and reduced Diophantine solving are selected through the
representation-independent `CPoly` capability layer. The dense inner Hermite loop over one squarefree
factor (`cHermiteReduceTowerInnerWf`) uses those algorithms. The defs are `[CField α]`-only (plus
`[CDiffField α]` for the Hermite loop), so they `native_decide` over noncomputable-`CFieldSpec`
carriers; correctness is proved through `toPoly` over `K[X]`. -/

namespace DeepWiki.SymbolicIntegration

namespace DensePoly

variable {α : Type*} [CField α]

variable [CFieldSpec α]

/-! ### Correctness of the Bézout/Diophantine leaves -/

/-- `CPoly.bezoutOne` solves the normalized Bézout identity over `K[X]` in the coprime case. -/
theorem toPolyG_bezoutOne (a b : DensePoly α)
    (hgdeg : (toPoly (cgcdWf a b).1).natDegree = 0)
    (hgne : toPoly (cgcdWf a b).1 ≠ 0) :
    toPoly (CPoly.bezoutOne a b).1 * toPoly a
        + toPoly (CPoly.bezoutOne a b).2 * toPoly b = 1 := by
  have hgdeg' : (CPoly.toPoly (CPolyEuclidean.gcdExt a b).1).natDegree = 0 := by
    simpa only [CPolyEuclidean.gcdExt_dense_eq, toPoly_list_eq] using hgdeg
  have hgne' : CPoly.toPoly (CPolyEuclidean.gcdExt a b).1 ≠ 0 := by
    simpa only [CPolyEuclidean.gcdExt_dense_eq, toPoly_list_eq] using hgne
  simpa only [CPolyEuclidean.gcdExt_dense_eq, toPoly_list_eq] using
    CPoly.toPoly_bezoutOne (P := DensePoly) a b hgdeg' hgne'

/-- `CPoly.extendedEuclideanSplit` solves the split Bézout equation over `K[X]`. -/
theorem toPolyG_extendedEuclideanSplit (dn ds r u w : DensePoly α)
    (hds0 : cnorm ds ≠ [])
    (hbez : toPoly u * toPoly dn + toPoly w * toPoly ds = 1) :
    toPoly (CPoly.extendedEuclideanSplit dn ds r u w).1 * toPoly dn
        + toPoly (CPoly.extendedEuclideanSplit dn ds r u w).2 * toPoly ds
      = toPoly r := by
  have hdsDense : toPoly ds ≠ 0 := fun h => hds0 ((cnormG_eq_nil_iff ds).mpr h)
  have hds : CPoly.toPoly ds ≠ 0 := by simpa only [toPoly_list_eq] using hdsDense
  have hbez' : CPoly.toPoly u * CPoly.toPoly dn + CPoly.toPoly w * CPoly.toPoly ds = 1 := by
    simpa only [toPoly_list_eq] using hbez
  simpa only [toPoly_list_eq] using
    CPoly.toPoly_extendedEuclideanSplit (P := DensePoly) dn ds r u w hds hbez'

/-- `CPoly.extendedEuclideanSplit`'s first cofactor is proper: `deg b < deg dₛ`. -/
theorem extendedEuclideanSplit_fst_degree_lt (dn ds r u w : DensePoly α)
    (hds : cnorm ds ≠ []) :
    (toPoly (CPoly.extendedEuclideanSplit dn ds r u w).1).degree < (toPoly ds).degree := by
  have hfst : (CPoly.extendedEuclideanSplit dn ds r u w).1 = cmodWf (cmul u r) ds := by
    change CPolyEuclidean.mod (CPolyEngine.mul u r) ds = _
    rw [CPolyEuclidean.mod_dense_eq, CPolyEngine.mul_dense_eq]
  rw [hfst]
  refine toPolyG_degree_lt_of_length_lt _ _ hds ?_
  show (cnorm (cmodWf (cmul u r) ds) : List α).length < _
  exact cmodWf_length_lt (cmul u r) ds hds

/-- `CPoly.extendedEuclideanSplit`'s second cofactor is proper: `deg c < deg dₙ`. -/
theorem extendedEuclideanSplit_snd_degree_lt (dn ds r u w d : DensePoly α)
    (hds : cnorm ds ≠ []) (hdn : cnorm dn ≠ [])
    (hsplit : toPoly d = toPoly ds * toPoly dn)
    (hbez : toPoly u * toPoly dn + toPoly w * toPoly ds = 1)
    (hr : (toPoly r).degree < (toPoly d).degree) :
    (toPoly (CPoly.extendedEuclideanSplit dn ds r u w).2).degree < (toPoly dn).degree := by
  set b := toPoly (CPoly.extendedEuclideanSplit dn ds r u w).1 with hbdef
  set c := toPoly (CPoly.extendedEuclideanSplit dn ds r u w).2 with hcdef
  have hds0 : toPoly ds ≠ 0 := fun h => hds ((cnormG_eq_nil_iff ds).mpr h)
  have hdn0 : toPoly dn ≠ 0 := fun h => hdn ((cnormG_eq_nil_iff dn).mpr h)
  have hspec : b * toPoly dn + c * toPoly ds = toPoly r :=
    toPolyG_extendedEuclideanSplit dn ds r u w hds hbez
  have hbdeg : b.degree < (toPoly ds).degree :=
    extendedEuclideanSplit_fst_degree_lt dn ds r u w hds
  have hbdn : (b * toPoly dn).degree < (toPoly d).degree := by
    rw [hsplit, Polynomial.degree_mul, Polynomial.degree_mul]
    exact WithBot.add_lt_add_right (by rwa [Ne, Polynomial.degree_eq_bot]) hbdeg
  have hcds : c * toPoly ds = toPoly r - b * toPoly dn := by linear_combination hspec
  have hcdsdeg : (c * toPoly ds).degree < (toPoly d).degree := by
    rw [hcds]
    calc (toPoly r - b * toPoly dn).degree
        ≤ max (toPoly r).degree (b * toPoly dn).degree := Polynomial.degree_sub_le _ _
      _ < (toPoly d).degree := max_lt hr hbdn
  rw [Polynomial.degree_mul, hsplit, Polynomial.degree_mul] at hcdsdeg
  have hdsdeg : (toPoly ds).degree ≠ ⊥ := by rwa [Ne, Polynomial.degree_eq_bot]
  rw [add_comm (toPoly ds).degree (toPoly dn).degree] at hcdsdeg
  exact (WithBot.add_lt_add_iff_right hdsdeg).mp hcdsdeg

/-- `CPoly.diophantineReduced` solves the Diophantine equation over `K[X]` for coprime inputs. -/
theorem toPolyG_diophantineReduced (p q rhs : DensePoly α)
    (hq0 : cnorm q ≠ [])
    (hgdeg : (toPoly (cgcdWf p q).1).natDegree = 0)
    (hgne : toPoly (cgcdWf p q).1 ≠ 0) :
    toPoly (CPoly.diophantineReduced p q rhs).1 * toPoly p
        + toPoly (CPoly.diophantineReduced p q rhs).2 * toPoly q = toPoly rhs := by
  have hqDense : toPoly q ≠ 0 := fun h => hq0 ((cnormG_eq_nil_iff q).mpr h)
  have hq : CPoly.toPoly q ≠ 0 := by simpa only [toPoly_list_eq] using hqDense
  have hgdeg' : (CPoly.toPoly (CPolyEuclidean.gcdExt p q).1).natDegree = 0 := by
    simpa only [CPolyEuclidean.gcdExt_dense_eq, toPoly_list_eq] using hgdeg
  have hgne' : CPoly.toPoly (CPolyEuclidean.gcdExt p q).1 ≠ 0 := by
    simpa only [CPolyEuclidean.gcdExt_dense_eq, toPoly_list_eq] using hgne
  simpa only [toPoly_list_eq] using
    CPoly.toPoly_diophantineReduced (P := DensePoly) p q rhs hq hgdeg' hgne'

/-- `CPoly.diophantineReduced`'s first cofactor is proper for nonzero `q`. -/
theorem diophantineReduced_fst_degree_lt (p q rhs : DensePoly α) (hq : cnorm q ≠ []) :
    (toPoly (CPoly.diophantineReduced p q rhs).1).degree < (toPoly q).degree := by
  set g := (cgcdWf p q).1 with hg
  set s := (cgcdWf p q).2.1 with hs
  set S := cmul (cscale (CField.inv (clead g)) s) rhs with hS
  have hfst : (CPoly.diophantineReduced p q rhs).1 = cnorm (cmodWf S q) := by
    rw [CPoly.diophantineReduced, CPoly.bezoutOne, CPoly.extendedEuclideanSplit]
    simp only [CPolyEuclidean.gcdExt_dense_eq, CPolyEuclidean.mod_dense_eq,
      CPolyEngine.mul_dense_eq, CPolyEngine.scale_dense_eq, CPolyEngine.cnorm_dense_eq,
      CPolyEngine.clead_dense_eq,
      ← hg, ← hs, ← hS]
  rw [hfst]
  refine toPolyG_degree_lt_of_length_lt _ _ hq ?_
  rw [cnormG_idem]
  exact cmodWf_length_lt S q hq

end DensePoly

namespace DensePoly

variable {α : Type*} [CField α] [CDiffField α]

/-- Inner Hermite loop over a squarefree factor `v`, driven by a downward multiplicity counter. -/
def cHermiteReduceTowerInnerWf (Dt : DensePoly α) (v u : DensePoly α) :
    ℕ → DensePoly α → DensePoly α × DensePoly α → (DensePoly α × DensePoly α) × DensePoly α
  | 0, a, g => (g, a)
  | j + 1, a, g =>
    let jval : α := cnatCast (j + 1)                                 -- `j` as a field element
    let Dv := cmonomialDeriv Dt v
    let p := cmul u Dv
    let rhs := cscale (CCommRing.neg (CField.inv jval)) a               -- `−a/j`
    let (b, c) := CPoly.diophantineReduced p v rhs
    let Vpow := cpow v (j + 1)
    let g' := (cadd (cmul g.1 Vpow) (cmul b g.2), cmul g.2 Vpow)  -- `g + b/Vʲ` (cross-multiplied)
    let a' := csub (cscale (CCommRing.neg jval) c) (cmul u (cmonomialDeriv Dt b))  -- `−j·c − u·Db`
    cHermiteReduceTowerInnerWf Dt v u j a' g'

end DensePoly

end DeepWiki.SymbolicIntegration
