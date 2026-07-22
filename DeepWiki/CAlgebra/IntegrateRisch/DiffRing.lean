import DeepWiki.CAlgebra.IntegrateRisch.DerivationExtend

/-! # Computable differential rings

`DenseDiffRing K` bundles a carrier's computable derivation `d : K → K` with the proof
it is one — the differential-structure core threaded through the tower's stages (it is
what Hermite reduction and the log part consume). The constraint is `[CommRing K]` (in
the tower `K` is always a field, but the bundle needs no more than a ring). The monomial
choice `Dt` is **not** part of it: a differential ring is `(K, d)`, whereas `Dt` is the
parameter of the extension step `extend`, which climbs one level to the differential ring
on `K(t) = DenseFrac K`. `toDifferential` is the bridge into Mathlib's `Differential`
class (a conversion, deliberately **not** an instance — the derivation is per-value data
chosen by the monomial, not a canonical per-type structure). -/

namespace DeepWiki.CAlgebra

universe u

/-- A computable differential ring: a carrier `K` with a computable derivation `d` and
the proof it is a derivation. -/
structure DenseDiffRing (K : Type u) [CommRing K] where
  /-- The computable derivation. -/
  d : K → K
  /-- `d` is a derivation. -/
  isDerivation : IsDerivation d

namespace DenseDiffRing

variable {K : Type u} [CommRing K]

/-- **Bridge to Mathlib**: the computable derivation as a `Differential` structure
(a conversion used inside proofs, not a global instance). -/
@[reducible] noncomputable def toDifferential (F : DenseDiffRing K) : Differential K :=
  F.isDerivation.toDifferential

/-- The bridged derivation applies as `F.d`. -/
theorem toDifferential_deriv (F : DenseDiffRing K) :
    ⇑(@Differential.deriv K _ F.toDifferential) = F.d := rfl

/-- The constant differential ring: the zero derivation (the tower base). -/
def base : DenseDiffRing K :=
  ⟨fun _ => 0, isDerivation_zero⟩

@[simp] theorem base_d : (base : DenseDiffRing K).d = fun _ => 0 := rfl

/-- **The monomial extension step**: extend `(K, d)` by a transcendental `t` with
prescribed derivative `Dt`, producing the differential ring on `K(t) = DenseFrac K`
with the quotient-rule extension derivation. -/
def extend {K : Type u} [Field K] [DecidableEq K] [DensePolyGcd K]
    (F : DenseDiffRing K) (Dt : DensePoly K) : DenseDiffRing (DenseFrac K) :=
  ⟨DenseFrac.extendDeriv F.d Dt, DenseFrac.isDerivation_extendDeriv F.isDerivation Dt⟩

@[simp] theorem extend_d {K : Type u} [Field K] [DecidableEq K] [DensePolyGcd K]
    (F : DenseDiffRing K) (Dt : DensePoly K) :
    (F.extend Dt).d = DenseFrac.extendDeriv F.d Dt := rfl

end DenseDiffRing

end DeepWiki.CAlgebra
