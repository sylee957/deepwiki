import DeepWiki.ComputableAlgebra.PolyEuclidean
import DeepWiki.ComputableAlgebra.PolyEngine
import DeepWiki.ComputableAlgebra.PolyReprGcd

/-! # Representation-independent gcd-derived polynomial algorithms

Fraction-pair normalization, polynomial lcm, and normalized Bezout splitting select gcd and division
through capability classes. -/

namespace DeepWiki.SymbolicIntegration

universe u v

namespace CPoly

/-- Test whether a coefficient is a root using the selected Euclidean remainder. -/
def isRoot {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
    {α : Type u} [CField α] (p : P α) (a : α) : Bool :=
  CPolyEngine.cisZero
    (CPolyEuclidean.mod p (CPolyEngine.ofCoeffList [CCommRing.neg a, CCommRing.one]))

/-- Test whether a polynomial has exactly the supplied linear factors up to scalar. -/
def matchesLinearFactors {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] (p : P α) (roots : List α) : Bool :=
  let product := roots.foldl (fun acc a =>
    CPolyEngine.mul acc (CPolyEngine.ofCoeffList [CCommRing.neg a, CCommRing.one]))
    (CPoly.one : P α)
  CPolyEngine.cisZero
    (CPolyEngine.sub (CPolyEngine.cmonic p) (CPolyEngine.cmonic product))

/-- Normalize selected extended-gcd cofactors so their Bezout combination is `1`. -/
def bezoutOne {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
    {α : Type u} [CField α] (a b : P α) : P α × P α :=
  let (g, s, t) := CPolyEuclidean.gcdExt a b
  let ginv := CField.inv (CPolyEngine.clead g)
  (CPolyEngine.scale ginv s, CPolyEngine.scale ginv t)

/-- Split `r` into proper cofactors along `dn` and `ds` using a supplied Bezout pair. -/
def extendedEuclideanSplit {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
    {α : Type u} [CField α] (dn ds r u w : P α) : P α × P α :=
  let ur := CPolyEngine.mul u r
  let quo := CPolyEuclidean.div ur ds
  let rem := CPolyEuclidean.mod ur ds
  (rem, CPolyEngine.add (CPolyEngine.mul w r) (CPolyEngine.mul quo dn))

/-- Solve `b * p + c * q = rhs` with the first cofactor reduced modulo `q`. -/
def diophantineReduced {P : Type u → Type u} [CPoly P] [CPolyEngine P] [CPolyEuclidean P]
    {α : Type u} [CField α] (p q rhs : P α) : P α × P α :=
  let uw := bezoutOne p q
  let bc := extendedEuclideanSplit p q rhs uw.1 uw.2
  (CPolyEngine.cnorm bc.1, CPolyEngine.cnorm bc.2)

/-- `bezoutOne` denotes a normalized Bezout identity when the selected gcd is a nonzero constant. -/
theorem toPoly_bezoutOne {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    [LawfulCPolyEngine.{u,v} P] [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] (a b : P α)
    (hgdeg : (CPoly.toPoly (CPolyEuclidean.gcdExt a b).1).natDegree = 0)
    (hgne : CPoly.toPoly (CPolyEuclidean.gcdExt a b).1 ≠ 0) :
    CPoly.toPoly (bezoutOne a b).1 * CPoly.toPoly a
        + CPoly.toPoly (bezoutOne a b).2 * CPoly.toPoly b = 1 := by
  set g := (CPolyEuclidean.gcdExt a b).1 with hg
  set s := (CPolyEuclidean.gcdExt a b).2.1 with hs
  set t := (CPolyEuclidean.gcdExt a b).2.2 with ht
  have hbez : CPoly.toPoly s * CPoly.toPoly a + CPoly.toPoly t * CPoly.toPoly b =
      CPoly.toPoly g := by
    simpa only [hg, hs, ht] using LawfulCPolyEuclidean.gcdExt_bezout (P := P) a b
  set c := (CPoly.toPoly g).leadingCoeff with hc
  have hlead_ne : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hgne
  have hgC : CPoly.toPoly g = Polynomial.C c := by
    conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hgdeg]
    rw [hc, Polynomial.leadingCoeff, hgdeg]
  have hu : CPoly.toPoly (bezoutOne a b).1 = Polynomial.C c⁻¹ * CPoly.toPoly s := by
    rw [bezoutOne]
    change CPoly.toPoly (CPolyEngine.scale (CField.inv (CPolyEngine.clead g)) s) = _
    rw [LawfulCPolyEngine.toPoly_scale]
    congr 2
    change CFieldSpec.toK (CField.inv (CPolyEngine.clead g)) = _
    rw [CFieldSpec.toK_inv]
    change (CRingSpec.toR (CPolyEngine.clead g))⁻¹ = _
    rw [LawfulCPolyEngine.toR_clead_eq_leadingCoeff, ← hc]
  have hw : CPoly.toPoly (bezoutOne a b).2 = Polynomial.C c⁻¹ * CPoly.toPoly t := by
    rw [bezoutOne]
    change CPoly.toPoly (CPolyEngine.scale (CField.inv (CPolyEngine.clead g)) t) = _
    rw [LawfulCPolyEngine.toPoly_scale]
    congr 2
    change CFieldSpec.toK (CField.inv (CPolyEngine.clead g)) = _
    rw [CFieldSpec.toK_inv]
    change (CRingSpec.toR (CPolyEngine.clead g))⁻¹ = _
    rw [LawfulCPolyEngine.toR_clead_eq_leadingCoeff, ← hc]
  rw [hu, hw]
  calc
    Polynomial.C c⁻¹ * CPoly.toPoly s * CPoly.toPoly a
          + Polynomial.C c⁻¹ * CPoly.toPoly t * CPoly.toPoly b =
        Polynomial.C c⁻¹ * CPoly.toPoly g := by rw [← hbez]; ring
    _ = Polynomial.C c⁻¹ * Polynomial.C c := by rw [hgC]
    _ = 1 := by rw [← Polynomial.C_mul, inv_mul_cancel₀ hlead_ne, Polynomial.C_1]

/-- `extendedEuclideanSplit` denotes the requested split identity for a nonzero `ds`. -/
theorem toPoly_extendedEuclideanSplit {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    [LawfulCPolyEngine.{u,v} P] [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] (dn ds r u w : P α)
    (hds : CPoly.toPoly ds ≠ 0)
    (hbez : CPoly.toPoly u * CPoly.toPoly dn + CPoly.toPoly w * CPoly.toPoly ds = 1) :
    CPoly.toPoly (extendedEuclideanSplit dn ds r u w).1 * CPoly.toPoly dn
        + CPoly.toPoly (extendedEuclideanSplit dn ds r u w).2 * CPoly.toPoly ds =
      CPoly.toPoly r := by
  set ur := CPolyEngine.mul u r with hur
  have hdivmod := LawfulCPolyEuclidean.divmod_spec (P := P) ur ds hds
  have hb : (extendedEuclideanSplit dn ds r u w).1 = CPolyEuclidean.mod ur ds := by
    simp [extendedEuclideanSplit, hur]
  have hc : (extendedEuclideanSplit dn ds r u w).2 =
      CPolyEngine.add (CPolyEngine.mul w r) (CPolyEngine.mul (CPolyEuclidean.div ur ds) dn) := by
    simp [extendedEuclideanSplit, hur]
  rw [hb, hc, LawfulCPolyEngine.toPoly_add, LawfulCPolyEngine.toPoly_mul,
    LawfulCPolyEngine.toPoly_mul]
  have hrem : CPoly.toPoly (CPolyEuclidean.mod ur ds) = CPoly.toPoly ur -
      CPoly.toPoly (CPolyEuclidean.div ur ds) * CPoly.toPoly ds := by
    rw [hdivmod]
    ring
  rw [hrem, hur, LawfulCPolyEngine.toPoly_mul]
  calc
    (CPoly.toPoly u * CPoly.toPoly r -
          CPoly.toPoly (CPolyEuclidean.div ur ds) * CPoly.toPoly ds) * CPoly.toPoly dn
        + (CPoly.toPoly w * CPoly.toPoly r +
          CPoly.toPoly (CPolyEuclidean.div ur ds) * CPoly.toPoly dn) * CPoly.toPoly ds =
      (CPoly.toPoly u * CPoly.toPoly dn + CPoly.toPoly w * CPoly.toPoly ds) *
        CPoly.toPoly r := by ring
    _ = CPoly.toPoly r := by rw [hbez, one_mul]

/-- The first split cofactor has degree below the selected nonzero modulus. -/
theorem toPoly_extendedEuclideanSplit_fst_degree_lt
    {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    [LawfulCPolyEngine.{u,v} P] [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] (dn ds r u w : P α)
    (hds : CPoly.toPoly ds ≠ 0) :
    (CPoly.toPoly (extendedEuclideanSplit dn ds r u w).1).degree <
      (CPoly.toPoly ds).degree := by
  change (CPoly.toPoly (CPolyEuclidean.mod (CPolyEngine.mul u r) ds)).degree <
    (CPoly.toPoly ds).degree
  exact LawfulCPolyEuclidean.mod_degree_lt (P := P) _ _ hds

/-- `diophantineReduced` denotes a solution when the selected gcd is a nonzero constant. -/
theorem toPoly_diophantineReduced {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    [LawfulCPolyEngine.{u,v} P] [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] (p q rhs : P α)
    (hq : CPoly.toPoly q ≠ 0)
    (hgdeg : (CPoly.toPoly (CPolyEuclidean.gcdExt p q).1).natDegree = 0)
    (hgne : CPoly.toPoly (CPolyEuclidean.gcdExt p q).1 ≠ 0) :
    CPoly.toPoly (diophantineReduced p q rhs).1 * CPoly.toPoly p
        + CPoly.toPoly (diophantineReduced p q rhs).2 * CPoly.toPoly q =
      CPoly.toPoly rhs := by
  let uw := bezoutOne p q
  have hbez : CPoly.toPoly uw.1 * CPoly.toPoly p + CPoly.toPoly uw.2 * CPoly.toPoly q = 1 := by
    simpa only [uw] using toPoly_bezoutOne (P := P) p q hgdeg hgne
  have hsplit := toPoly_extendedEuclideanSplit (P := P) p q rhs uw.1 uw.2 hq hbez
  simpa only [diophantineReduced, uw, LawfulCPolyEngine.toPoly_cnorm] using hsplit

/-- The reduced Diophantine solution's first cofactor has degree below a nonzero second input. -/
theorem toPoly_diophantineReduced_fst_degree_lt
    {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    [LawfulCPolyEngine.{u,v} P] [CPolyEuclidean P] [LawfulCPolyEuclidean.{u,v} P]
    {α : Type u} [CField α] [CFieldSpec.{u,v} α] (p q rhs : P α)
    (hq : CPoly.toPoly q ≠ 0) :
    (CPoly.toPoly (diophantineReduced p q rhs).1).degree < (CPoly.toPoly q).degree := by
  let uw := bezoutOne p q
  have hproper := toPoly_extendedEuclideanSplit_fst_degree_lt
    (P := P) p q rhs uw.1 uw.2 hq
  simpa only [diophantineReduced, uw, LawfulCPolyEngine.toPoly_cnorm] using hproper

/-- Reduce a represented fraction pair to a monic-denominator form through selected gcd and division. -/
def normalizeFracPair {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CPolyGcd P α] [CPolyEuclidean P]
    (num den : P α) : P α × P α :=
  if CPolyEngine.cisZero num then (CPoly.czero, CPoly.one)
  else
    let g := CPolyGcd.compute num den
    let num' := CPolyEuclidean.div num g
    let den' := CPolyEuclidean.div den g
    let s := CField.inv (CPolyEngine.clead den')
    (CPolyEngine.scale s num', CPolyEngine.scale s den')

/-- A zero numerator normalizes to the represented fraction `0/1`. -/
@[simp] theorem normalizeFracPair_of_cisZero {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CPolyGcd P α] [CPolyEuclidean P] (num den : P α)
    (h : CPolyEngine.cisZero num = true) :
    normalizeFracPair num den = (CPoly.czero, CPoly.one) := by
  simp [normalizeFracPair, h]

/-- Compute a monic polynomial lcm through the selected gcd and Euclidean-division capabilities. -/
def lcm {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CPolyGcd P α] [CPolyEuclidean P] (p q : P α) : P α :=
  if CPolyEngine.cisZero p || CPolyEngine.cisZero q then CPoly.czero
  else CPolyEngine.cmonic
    (CPolyEuclidean.div (CPolyEngine.mul p q) (CPolyGcd.compute p q))

/-- The selected polynomial lcm is zero when its left input is zero. -/
@[simp] theorem lcm_eq_zero_of_left {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CPolyGcd P α] [CPolyEuclidean P] (p q : P α)
    (h : CPolyEngine.cisZero p = true) : lcm p q = CPoly.czero := by
  simp [lcm, h]

/-- The selected polynomial lcm is zero when its right input is zero. -/
@[simp] theorem lcm_eq_zero_of_right {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CPolyGcd P α] [CPolyEuclidean P] (p q : P α)
    (h : CPolyEngine.cisZero q = true) : lcm p q = CPoly.czero := by
  simp [lcm, h]

/-- A left input recognized as zero makes the selected lcm zero. -/
@[simp] theorem lcm_of_left_isZero {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CPolyGcd P α] [CPolyEuclidean P] (p q : P α)
    (h : CPolyEngine.cisZero p = true) : lcm p q = CPoly.czero := by
  simp [lcm, h]

/-- A right input recognized as zero makes the selected lcm zero. -/
@[simp] theorem lcm_of_right_isZero {P : Type u → Type u} [CPoly P] [CPolyEngine P]
    {α : Type u} [CField α] [CPolyGcd P α] [CPolyEuclidean P] (p q : P α)
    (h : CPolyEngine.cisZero q = true) : lcm p q = CPoly.czero := by
  simp [lcm, h]

end CPoly

end DeepWiki.SymbolicIntegration
