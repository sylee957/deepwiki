import DeepWiki.SymbolicIntegration.ComputableSplitFactorCorrect
import DeepWiki.SymbolicIntegration.ComputableSplitSquarefree
import DeepWiki.SymbolicIntegration.ComputableCanonicalRep

/-! # Abstract correctness of the §3.5 `SplitSquarefreeFactor`/`CanonicalRepresentation` over ℚ(x)[t]
The two remaining §3.5 algorithms of the computable engine — the squarefree split
`cSplitSquarefreeFactorFast` (`ComputableSplitSquarefree`) and the canonical-representation capstone
`canonicalRepresentationFast` (`ComputableCanonicalRep`) — get their **abstract** correctness here,
axiom-clean (no `native_decide`), reading the computable output through `toPolyG` over the field
ℚ(x) = `RatFunc ℚ` with the monomial derivation `D = implicitDeriv (toPolyG Dt)`.

* **`cSplitSquarefreeFactorFast` (per Yun factor)** — for one **squarefree** factor `pᵢ` the computed
  `(Nᵢ, Sᵢ)` is a book-faithful splitting factorization `IsSplittingFactorizationGen (toPolyG pᵢ)
  (toPolyG Sᵢ) (toPolyG Nᵢ)`: `Sᵢ = cgcdFF pᵢ (cmonomialDeriv Dt pᵢ) ~ gcd(pᵢ, Dpᵢ)` (the special
  part, via `cgcdFF` correctness + `toPolyG_cmonomialDeriv`) and `Nᵢ = pᵢ/Sᵢ` exactly. For a
  squarefree `pᵢ`, `gcd(pᵢ, dpᵢ/dt) = 1`, so `gcd(pᵢ, Dpᵢ) = splitFactorStep`, which the abstract
  theory shows is special with normal-sqfree quotient.

* **`cextendedEuclideanSplit`/`cbezoutOne`** — the Bézout split solves `b·dₙ + c·dₛ = r` with
  `deg b < deg dₛ`, mirroring the abstract `extendedEuclideanSplit`/`bezoutOne`, via the generic
  extended-Euclid Bézout identity `toPolyG_cgcdExtG` (`ComputableFieldGcd`) rescaled by `g⁻¹`.

* **`canonicalRepresentationFast` (the capstone)** — its output `(q, (b, dₛ), (c, dₙ))` reconstructs
  `f = a/d`: `(q : ℚ(x)(t)) + b/dₛ + c/dₙ = f`, via the denominator split (`cSplitFactorFast`
  correctness), the Bézout split, and the abstract `canonicalRepresentation_add_eq`. -/

open Polynomial Classical
open scoped Differential

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG

/-! ### Target 1 — `cSplitSquarefreeFactorFast`: the per-Yun-factor squarefree split

For a squarefree factor `pᵢ`, the computable special factor is `Sᵢ = cgcdFF pᵢ (cmonomialDeriv Dt
pᵢ)` and the normal factor `Nᵢ = cdivG pᵢ Sᵢ`. We mirror the abstract `splitSquarefreeFactor`: `Sᵢ`
read through `toPolyG` is associated to the abstract special part `gcd(toPolyG pᵢ, D(toPolyG pᵢ))`,
and the pair is a book-faithful splitting factorization. -/

/-- The computable special factor of one Yun factor: `cgcdFF p (cmonomialDeriv Dt p)`. -/
abbrev csqfreeSpecial (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ) : CPolyG QFunNZ :=
  CPolyG.cgcdFF fuel p (cmonomialDeriv Dt p)

/-- The computable normal factor of one Yun factor: `cdivG p (cgcdFF p (cmonomialDeriv Dt p))`. -/
abbrev csqfreeNormal (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ) : CPolyG QFunNZ :=
  CPolyG.cdivG fuel p (csqfreeSpecial Dt fuel p)

/-- **For a squarefree `p`, the special part `gcd(p, Dp)` is the `SplitFactor` step** (up to
associates): `Associated (squarefreeSpecialPart v p) (splitFactorStep v p)`. Since `p` is squarefree
(char `0`), `gcd(p, dp/dt)` is a unit, so the step `gcd(p, Dp)/gcd(p, dp/dt)` is associated to its
numerator `gcd(p, Dp) = squarefreeSpecialPart v p`. -/
theorem associated_squarefreeSpecialPart_splitFactorStep {K : Type*} [Field K] [CharZero K]
    [Differential K] (v : K[X]) {p : K[X]} (hsf : Squarefree p) :
    Associated (squarefreeSpecialPart v p) (splitFactorStep v p) := by
  have hden_unit : IsUnit (gcd p (derivative p)) :=
    (gcd_isUnit_iff p (derivative p)).mpr
      (squarefree_iff_isCoprime_derivative.mp hsf)
  have hden_ne : gcd p (derivative p) ≠ 0 := hden_unit.ne_zero
  have hdvd : gcd p (derivative p) ∣ gcd p (Differential.implicitDeriv v p) :=
    hden_unit.dvd
  unfold squarefreeSpecialPart splitFactorStep
  refine ((associated_div_iff hden_ne hdvd).mpr ?_).symm
  exact (associated_unit_mul_left _ _ hden_unit).symm

/-- **The computable special part is associated to `gcd(p, Dp)`** (the abstract special part): for
`toPolyG p ≠ 0` and a node-regular `cgcdFF` call, `toPolyG (csqfreeSpecial Dt fuel p)` is
`Associated` to `squarefreeSpecialPart (toPolyG Dt) (toPolyG p)` in `(RatFunc ℚ)[X]`. The `cgcdFF`
correctness with the second argument identified by `toPolyG_cmonomialDeriv`. -/
theorem associated_toPolyG_csqfreeSpecial (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ)
    (hreg : CgcdFFNodeReg fuel p (cmonomialDeriv Dt p)) :
    Associated (toPolyG (csqfreeSpecial Dt fuel p))
      (squarefreeSpecialPart (toPolyG Dt) (toPolyG p)) := by
  have h := associated_toPolyG_cgcdFF_node fuel p (cmonomialDeriv Dt p) hreg
  rw [toPolyG_cmonomialDeriv] at h
  unfold squarefreeSpecialPart
  exact h

/-- **Per-factor regularity bundle** `CSqfreeFactorRegular Dt fuel p`: the transparent preconditions for
the squarefree split of one Yun factor `p` to match the abstract `splitSquarefreeFactor` — the special
`cgcdFF p (cmonomialDeriv Dt p)` call is node-regular (`CgcdFFNodeReg`) and the dividend list is short
enough that the exact division `cdivG p (cgcdFF …)` is fully reduced (`(cnormG p).length ≤ fuel`). -/
def CSqfreeFactorRegular (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ) : Prop :=
  CgcdFFNodeReg fuel p (cmonomialDeriv Dt p) ∧
  (cnormG p : List QFunNZ).length ≤ fuel

/-- **The special part divides its Yun factor exactly** (over ℚ(x)): `toPolyG p = toPolyG (csqfreeNormal
Dt fuel p) · toPolyG (csqfreeSpecial Dt fuel p)` — the gcd `gcd(p, Dp)` divides `p` (`gcd_dvd_left`),
transported across the association, so exact division `cdivG` has zero remainder. -/
theorem toPolyG_csqfree_factorization (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ)
    (hp : toPolyG p ≠ 0) (hreg : CSqfreeFactorRegular Dt fuel p) :
    toPolyG p = toPolyG (csqfreeNormal Dt fuel p) * toPolyG (csqfreeSpecial Dt fuel p) := by
  obtain ⟨hgcdreg, hfuel⟩ := hreg
  set S := csqfreeSpecial Dt fuel p with hSdef
  have haS : Associated (toPolyG S) (squarefreeSpecialPart (toPolyG Dt) (toPolyG p)) :=
    associated_toPolyG_csqfreeSpecial Dt fuel p hgcdreg
  have hSdvd : toPolyG S ∣ toPolyG p :=
    haS.dvd.trans (by unfold squarefreeSpecialPart; exact gcd_dvd_left _ _)
  have hSne : toPolyG S ≠ 0 := by
    intro h0
    have hz : (squarefreeSpecialPart (toPolyG Dt) (toPolyG p)) = 0 := haS.eq_zero_iff.mp h0
    unfold squarefreeSpecialPart at hz
    exact hp (eq_zero_of_zero_dvd (hz ▸ gcd_dvd_left _ _))
  have hScn : cnormG S ≠ [] := fun h => hSne ((cnormG_eq_nil_iff S).mp h)
  have hexact : toPolyG p = toPolyG (CPolyG.cdivFF fuel p S) * toPolyG S :=
    toPolyG_cdivFF_exact fuel p S hScn hfuel hSdvd
  show toPolyG p = toPolyG (CPolyG.cdivG fuel p S) * toPolyG S
  rw [hSdef] at hexact ⊢
  exact hexact

/-- **Per squarefree Yun factor — the computable split is a book-faithful splitting factorization** over
ℚ(x): for a **squarefree** `toPolyG p ≠ 0` and a regular split (`CSqfreeFactorRegular`), the computed
`(Nᵢ, Sᵢ)` satisfies `IsSplittingFactorizationGen (toPolyG p) (toPolyG Sᵢ) (toPolyG Nᵢ)` w.r.t. the
monomial derivation `D` (`Dt = toPolyG Dt`) — `p = Sᵢ·Nᵢ`, `Sᵢ` special, every squarefree factor of
`Nᵢ` normal. The special part `Sᵢ ~ gcd(p, Dp) = splitFactorStep` (squarefree, so the `dp/dt` gcd is a
unit), special by `isSpecial_splitFactorStep`; the abstract `splitFactorAux` correctness supplies the
normal-sqfree part. -/
theorem cSqfreeFactor_isSplittingFactorizationGen (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ)
    (hp : toPolyG p ≠ 0) (hsf : Squarefree (toPolyG p)) (hreg : CSqfreeFactorRegular Dt fuel p) :
    @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (toPolyG Dt)⟩
      (toPolyG p)
      (toPolyG (csqfreeSpecial Dt fuel p))
      (toPolyG (csqfreeNormal Dt fuel p)) := by
  haveI : CharZero (CFieldSpec.K QFunNZ) := inferInstanceAs (CharZero (RatFunc ℚ))
  letI : Differential (CFieldSpec.K QFunNZ)[X] := ⟨Differential.implicitDeriv (toPolyG Dt)⟩
  obtain ⟨hgcdreg, hfuel⟩ := hreg
  set v := toPolyG Dt with hv
  set P := toPolyG p with hP
  set S := csqfreeSpecial Dt fuel p with hSdef
  set N := csqfreeNormal Dt fuel p with hNdef
  -- the special part `S ~ gcd(P, DP) ~ splitFactorStep` (squarefree).
  have haS : Associated (toPolyG S) (squarefreeSpecialPart v P) :=
    associated_toPolyG_csqfreeSpecial Dt fuel p hgcdreg
  have hStep : Associated (toPolyG S) (splitFactorStep v P) :=
    haS.trans (associated_squarefreeSpecialPart_splitFactorStep v hsf)
  -- `S` is special.
  have hSspec : @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ (toPolyG S) :=
    IsSpecial.of_associated hStep.symm (isSpecial_splitFactorStep v hp)
  -- product invariant `P = N · S`.
  have hfact : toPolyG p = toPolyG N * toPolyG S :=
    toPolyG_csqfree_factorization Dt fuel p hp ⟨hgcdreg, hfuel⟩
  -- `N` and `S` are coprime: `P = N·S` is squarefree.
  have hPsf : Squarefree (toPolyG N * toPolyG S) := hfact ▸ hsf
  have hNScop : IsCoprime (toPolyG N) (toPolyG S) :=
    ((squarefree_mul_iff.mp hPsf).1).isCoprime
  -- `N` is normal-sqfree: every prime factor `π ∣ N` is normal (non-special).
  have hNnorm : @IsNormalSqfree _ _ ⟨Differential.implicitDeriv v⟩ (toPolyG N) := by
    refine isNormalSqfree_of_forall_prime_normal v (fun π hprime hπN => ?_)
    -- `IsNormal π ⟺ ¬ IsSpecial π` for an irreducible `π` (`isUnit_gcd_iff`).
    have hπnospec : ¬ @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ π := by
      intro hπspec
      -- a special prime factor of `P` divides the special part `S ~ ∏_{special}π`.
      have hπP : π ∣ toPolyG p := by rw [hfact]; exact hπN.trans (dvd_mul_right _ _)
      -- find a normalized associate `ρ ∈ primeFactors P`; `ρ` is special (associate-invariant).
      obtain ⟨ρ, hρmem, hρassoc⟩ :=
        UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hp hprime.irreducible hπP
      have hρpf : ρ ∈ UniqueFactorizationMonoid.primeFactors (toPolyG p) :=
        UniqueFactorizationMonoid.mem_primeFactors.mpr hρmem
      have hρspec : @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ ρ :=
        IsSpecial.of_associated hρassoc hπspec
      have hρmemf : ρ ∈ (UniqueFactorizationMonoid.primeFactors (toPolyG p)).filter
          (fun ρ => @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ ρ) :=
        Finset.mem_filter.mpr ⟨hρpf, hρspec⟩
      have hρdvdProd : ρ ∣ ∏ σ ∈ (UniqueFactorizationMonoid.primeFactors (toPolyG p)).filter
          (fun σ => @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ σ), σ :=
        Finset.dvd_prod_of_mem _ hρmemf
      have hρS : ρ ∣ toPolyG S :=
        (hρdvdProd.trans (splitFactorStep_associated_prod_special v hp).symm.dvd).trans hStep.symm.dvd
      have hπS : π ∣ toPolyG S := hρassoc.dvd.trans hρS
      -- but `π ∣ N` and `π ∣ S` contradicts `IsCoprime N S`.
      exact hprime.not_unit (hNScop.isUnit_of_dvd' hπN hπS)
    -- non-special irreducible ⇒ `gcd(π, π′)` a unit ⇒ `IsNormal π`.
    have hgcdu : IsUnit (gcd π (@Differential.deriv _ _ ⟨Differential.implicitDeriv v⟩ π)) :=
      hprime.irreducible.isUnit_gcd_iff.mpr
        (fun hd => hπnospec (hd : @IsSpecial _ _ ⟨Differential.implicitDeriv v⟩ π))
    exact (gcd_isUnit_iff_isRelPrime.mp hgcdu).isCoprime
  exact ⟨by rw [hP, hfact, mul_comm], hSspec, hNnorm⟩

/-! ### Restatement against the intended wording (anonymous `example`) -/

-- The headline (target 1): for one **squarefree** Yun factor `pᵢ`, the fraction-free squarefree split
-- `(Nᵢ, Sᵢ) = (cdivG pᵢ Sᵢ, cgcdFF pᵢ (cmonomialDeriv Dt pᵢ))`, read over ℚ(x) = `RatFunc ℚ`, returns
-- a book-faithful splitting factorization of `toPolyG pᵢ` w.r.t. the monomial derivation `Dt = toPolyG
-- Dt` — `pᵢ = Sᵢ·Nᵢ`, `Sᵢ` special, every squarefree factor of `Nᵢ` normal — under the transparent
-- per-node degree/fuel preconditions a real run satisfies. Mirrors the abstract `splitSquarefreeFactor`.
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (p : CPolyG QFunNZ) (hp : toPolyG p ≠ 0)
    (hsf : Squarefree (toPolyG p)) (hreg : CSqfreeFactorRegular Dt fuel p) :
    @IsSplittingFactorizationGen _ _ ⟨Differential.implicitDeriv (toPolyG Dt)⟩
      (toPolyG p)
      (toPolyG (csqfreeSpecial Dt fuel p))
      (toPolyG (csqfreeNormal Dt fuel p)) :=
  cSqfreeFactor_isSplittingFactorizationGen Dt fuel p hp hsf hreg

/-! ### Target 2 (Bézout pieces) — `cbezoutOne` and `cextendedEuclideanSplit` correctness

`cbezoutOne fuel a b = (cscaleG (inv (cleadG g)) s, cscaleG (inv (cleadG g)) t)` for `(g, s, t) =
cgcdExtG fuel a b`, rescaling the raw cofactors by the inverse leading coefficient of `g`. When `a, b`
are coprime over ℚ(x) their gcd `g` is a nonzero **constant**, so `toPolyG g = C(lead g)` and the
rescaled cofactors solve `u·a + w·b = 1` (`toPolyG_cgcdExtG` divided by the constant `g`). The Bézout
split `cextendedEuclideanSplit` then solves `b·dₙ + c·dₛ = r`, mirroring the abstract
`extendedEuclideanSplit_spec`. -/

variable {α : Type*} [CField α] [CFieldSpec α]

/-- **`cbezoutOne` solves the Bézout identity** `u·a + w·b = 1` over `K[X]`: with `(g, s, t) = cgcdExtG
fuel a b` and `g` a nonzero **constant** (`natDegree (toPolyG g) = 0`, `toPolyG g ≠ 0` — the coprime
case), the rescaled cofactors `(u, w) = cbezoutOne fuel a b` (each scaled by `(lead g)⁻¹`) satisfy
`toPolyG u · toPolyG a + toPolyG w · toPolyG b = 1`. From the raw Bézout `toPolyG_cgcdExtG` divided by
the constant `g`. -/
theorem toPolyG_cbezoutOne (fuel : ℕ) (a b : CPolyG α)
    (hgdeg : (toPolyG (cgcdExtG fuel a b).1).natDegree = 0)
    (hgne : toPolyG (cgcdExtG fuel a b).1 ≠ 0) :
    toPolyG (CPolyG.cbezoutOne fuel a b).1 * toPolyG a
        + toPolyG (CPolyG.cbezoutOne fuel a b).2 * toPolyG b = 1 := by
  set g := (cgcdExtG fuel a b).1 with hg
  set s := (cgcdExtG fuel a b).2.1 with hs
  set t := (cgcdExtG fuel a b).2.2 with ht
  -- the raw Bézout identity from `cgcdExtG`.
  have hbez : toPolyG s * toPolyG a + toPolyG t * toPolyG b = toPolyG g :=
    toPolyG_cgcdExtG fuel a b
  -- freeze the leading coefficient `c = lead g`, a nonzero scalar.
  set c := (toPolyG g).leadingCoeff with hc
  have hlead_ne : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hgne
  -- `toPolyG g = C c`, a nonzero constant.
  have hgC : toPolyG g = Polynomial.C c := by
    conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hgdeg]
    rw [hc, Polynomial.leadingCoeff, hgdeg]
  -- `cbezoutOne` rescales `(s, t)` by `(toK (cleadG g))⁻¹ = c⁻¹`.
  have hu : toPolyG (CPolyG.cbezoutOne fuel a b).1 = Polynomial.C c⁻¹ * toPolyG s := by
    rw [CPolyG.cbezoutOne]
    show toPolyG (cscaleG (CField.inv (cleadG g)) s) = _
    rw [toPolyG_cscaleG, CFieldSpec.toK_inv, toK_cleadG_eq_leadingCoeff, ← hc]
  have hw : toPolyG (CPolyG.cbezoutOne fuel a b).2 = Polynomial.C c⁻¹ * toPolyG t := by
    rw [CPolyG.cbezoutOne]
    show toPolyG (cscaleG (CField.inv (cleadG g)) t) = _
    rw [toPolyG_cscaleG, CFieldSpec.toK_inv, toK_cleadG_eq_leadingCoeff, ← hc]
  rw [hu, hw]
  -- `C(c⁻¹)·s·a + C(c⁻¹)·t·b = C(c⁻¹)·(s·a + t·b) = C(c⁻¹)·C(c) = 1`.
  have hcombine : Polynomial.C c⁻¹ * toPolyG s * toPolyG a
      + Polynomial.C c⁻¹ * toPolyG t * toPolyG b = Polynomial.C c⁻¹ * toPolyG g := by
    rw [← hbez]; ring
  rw [hcombine, hgC, ← Polynomial.C_mul, inv_mul_cancel₀ hlead_ne, Polynomial.C_1]

/-- **`cextendedEuclideanSplit` solves `b·dₙ + c·dₛ = r`** over `K[X]`: with a Bézout pair `u·dₙ + w·dₛ
= 1` (read through `toPolyG`), `cextendedEuclideanSplit fuel dn ds r u w = (b, c)` gives `toPolyG b ·
toPolyG dn + toPolyG c · toPolyG ds = toPolyG r`. Mirrors `extendedEuclideanSplit_spec`. Requires `dₛ`
nonzero (`cnormG ds ≠ []`). -/
theorem toPolyG_cextendedEuclideanSplit (fuel : ℕ) (dn ds r u w : CPolyG α)
    (hds0 : cnormG ds ≠ [])
    (hbez : toPolyG u * toPolyG dn + toPolyG w * toPolyG ds = 1) :
    toPolyG (CPolyG.cextendedEuclideanSplit fuel dn ds r u w).1 * toPolyG dn
        + toPolyG (CPolyG.cextendedEuclideanSplit fuel dn ds r u w).2 * toPolyG ds
      = toPolyG r := by
  -- `b = (u·r) mod ds`, `c = w·r + (u·r div ds)·dn`.
  set ur := cmulG u r with hur
  -- Euclidean identity `u·r = (u·r div ds)·ds + (u·r mod ds)`.
  have hdivmod : toPolyG ur
      = toPolyG (cdivG fuel ur ds) * toPolyG ds + toPolyG (cmodG fuel ur ds) :=
    toPolyG_cdivmodG' fuel ur ds hds0
  -- the components of `cextendedEuclideanSplit`.
  have hb : (CPolyG.cextendedEuclideanSplit fuel dn ds r u w).1 = cmodG fuel ur ds := by
    rw [CPolyG.cextendedEuclideanSplit]; simp only [cmodG, hur]
  have hc : (CPolyG.cextendedEuclideanSplit fuel dn ds r u w).2
      = caddG (cmulG w r) (cmulG (cdivG fuel ur ds) dn) := by
    rw [CPolyG.cextendedEuclideanSplit]; simp only [cdivG, hur]
  rw [hb, hc, toPolyG_caddG, toPolyG_cmulG, toPolyG_cmulG]
  -- substitute the Euclidean remainder `(u·r mod ds) = u·r − (u·r div ds)·ds`.
  have hrem : toPolyG (cmodG fuel ur ds)
      = toPolyG ur - toPolyG (cdivG fuel ur ds) * toPolyG ds := by
    rw [hdivmod]; ring
  rw [hrem, hur, toPolyG_cmulG]
  -- `(u·r − Q·ds)·dn + (w·r + Q·dn)·ds = (u·dn + w·ds)·r = r`.
  have hkey : (toPolyG u * toPolyG r - toPolyG (cdivG fuel (cmulG u r) ds) * toPolyG ds) * toPolyG dn
      + (toPolyG w * toPolyG r + toPolyG (cdivG fuel (cmulG u r) ds) * toPolyG dn) * toPolyG ds
      = (toPolyG u * toPolyG dn + toPolyG w * toPolyG ds) * toPolyG r := by ring
  rw [show cmulG u r = ur from rfl] at hkey ⊢
  rw [hkey, hbez, one_mul]

/-! ### Target 2 (the capstone) — `canonicalRepresentationFast` reconstructs `f`

`canonicalRepresentationFast Dt fuel a d = (q, (b, dₛ), (c, dₙ))` with `(q, r) = cdivmodG a d`,
`(dₙ, dₛ) = cSplitFactorFast Dt fuel d`, `(u, w) = cbezoutOne dₙ dₛ`, `(b, c) =
cextendedEuclideanSplit dₙ dₛ r u w`. We prove the abstract reconstruction over `RatFunc ℚ`:
`(q : ℚ(x)(t)) + b/dₛ + c/dₙ = a/d`, mirroring `canonicalRepresentation_add_eq`. -/

/-- **The abstract canonical field identity** over ℚ(x)(t): from the division `a = q·d + r`, the
denominator split `d = dₛ·dₙ`, and the Bézout split `b·dₙ + c·dₛ = r`, the three pieces recombine to
`a/d` — `q + b/dₛ + c/dₙ = a/d`. The field-arithmetic core, independent of the computable engine. -/
theorem canonicalRepFast_field_identity {K : Type*} [Field K] (a d q r dn ds b c : K[X])
    (hd : d ≠ 0) (hdn : dn ≠ 0) (hds : ds ≠ 0)
    (hadiv : a = q * d + r) (hsplit : d = ds * dn) (hbcr : b * dn + c * ds = r) :
    (algebraMap K[X] (RatFunc K) q)
        + algebraMap K[X] (RatFunc K) b / algebraMap K[X] (RatFunc K) ds
        + algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) dn
      = algebraMap K[X] (RatFunc K) a / algebraMap K[X] (RatFunc K) d := by
  set A := algebraMap K[X] (RatFunc K) with hA
  have hAd : A d ≠ 0 := RatFunc.algebraMap_ne_zero hd
  have hAdn : A dn ≠ 0 := RatFunc.algebraMap_ne_zero hdn
  have hAds : A ds ≠ 0 := RatFunc.algebraMap_ne_zero hds
  have hAa : A a = A q * (A ds * A dn) + (A b * A dn + A c * A ds) := by
    rw [hadiv, hsplit, ← hbcr]; push_cast [hA]; ring
  rw [show A d = A ds * A dn by rw [hsplit, map_mul]]
  rw [eq_div_iff (mul_ne_zero hAds hAdn), hAa]
  field_simp
  ring

/-- **Per-run regularity bundle** `CCanonicalRepFastRegular Dt fuel a d`: the transparent per-node
preconditions for `canonicalRepresentationFast` to reconstruct `f = a/d` — the denominator split
`cSplitFactorFast Dt fuel d` is a regular run (`CSplitFactorFastRegular`), fuel exceeds the
denominator `t`-degree, and the Bézout gcd of the split parts is a nonzero constant (the coprime
case). The dividend `d` and both split parts are taken nonzero. -/
structure CCanonicalRepFastRegular (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ) : Prop where
  /-- `d` is nonzero. -/
  hd : toPolyG d ≠ 0
  /-- fuel exceeds the denominator `t`-degree (so `cSplitFactorFast`/`cdivmodG` are reduced). -/
  hdeg : (toPolyG d).natDegree ≤ fuel
  /-- the denominator split is a regular `cSplitFactorFast` run. -/
  hsplitreg : CSplitFactorFastRegular Dt fuel d
  /-- the Bézout gcd of the split parts `(dₙ, dₛ)` is a **constant** (coprime case). -/
  hgdeg : (toPolyG (cgcdExtG fuel (cSplitFactorFast Dt fuel d).1
    (cSplitFactorFast Dt fuel d).2).1).natDegree = 0
  /-- the Bézout gcd is nonzero. -/
  hgne : toPolyG (cgcdExtG fuel (cSplitFactorFast Dt fuel d).1
    (cSplitFactorFast Dt fuel d).2).1 ≠ 0

open RatFunc in
/-- **`canonicalRepresentationFast` reconstructs `f`** (the §3.5 capstone), abstract correctness over
ℚ(x)(t): with the output `(q, (b, dₛ), (c, dₙ)) = canonicalRepresentationFast Dt fuel a d`, the three
pieces recombine to `f = a/d` — `(q : ℚ(x)(t)) + b/dₛ + c/dₙ = a/d`. Via the denominator split
(`cSplitFactorFast` correctness, `d = dₛ·dₙ`), the Euclidean division (`a = q·d + r`), the Bézout
cofactors (`cbezoutOne`, `u·dₙ + w·dₛ = 1`), and the Bézout split (`cextendedEuclideanSplit`,
`b·dₙ + c·dₛ = r`), assembled by `canonicalRepFast_field_identity`. Mirrors the abstract
`canonicalRepresentation_add_eq`. -/
theorem canonicalRepFast_reconstructs (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ)
    (hreg : CCanonicalRepFastRegular Dt fuel a d) :
    (let res := CPolyG.canonicalRepresentationFast Dt fuel a d
      let q := res.1
      let b := res.2.1.1
      let ds := res.2.1.2
      let c := res.2.2.1
      let dn := res.2.2.2
      (algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG q))
          + algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG b)
              / algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG ds)
          + algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG c)
              / algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG dn)
        = algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG a)
            / algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG d)) := by
  haveI : CharZero (CFieldSpec.K QFunNZ) := inferInstanceAs (CharZero (RatFunc ℚ))
  obtain ⟨hd, hdeg, hsplitreg, hgdeg, hgne⟩ := hreg
  -- names matching the `let`-bindings of `canonicalRepresentationFast`.
  set qr := cdivmodG fuel a d with hqr
  set dnds := cSplitFactorFast Dt fuel d with hdnds
  set dn := dnds.1 with hdn
  set ds := dnds.2 with hds
  set q := qr.1 with hq
  set r := qr.2 with hr
  set uw := CPolyG.cbezoutOne fuel dn ds with huw
  set u := uw.1 with hu
  set w := uw.2 with hw
  set bc := CPolyG.cextendedEuclideanSplit fuel dn ds r u w with hbc
  set b := bc.1 with hb
  set c := bc.2 with hc
  -- 1. the denominator split `toPolyG d = toPolyG ds · toPolyG dn`.
  have hsplit := cSplitFactorFast_isSplittingFactorizationGen Dt fuel d hd hdeg hsplitreg
  have hsplit_eq : toPolyG d = toPolyG ds * toPolyG dn := hsplit.1
  -- both split parts nonzero.
  have hdn_ne : toPolyG dn ≠ 0 := by
    intro h0; exact hd (by rw [hsplit_eq, h0, mul_zero])
  have hds_ne : toPolyG ds ≠ 0 := by
    intro h0; exact hd (by rw [hsplit_eq, h0, zero_mul])
  -- 2. the Euclidean division `toPolyG a = toPolyG q · toPolyG d + toPolyG r`.
  have hdcn : cnormG d ≠ [] := fun h => hd ((cnormG_eq_nil_iff d).mp h)
  have hadiv : toPolyG a = toPolyG q * toPolyG d + toPolyG r :=
    toPolyG_cdivmodG' fuel a d hdcn
  -- 3. the Bézout cofactors `u·dn + w·ds = 1` (gcd of `(dn, ds)` a nonzero constant).
  have hbez : toPolyG u * toPolyG dn + toPolyG w * toPolyG ds = 1 := by
    have := toPolyG_cbezoutOne fuel dn ds hgdeg hgne
    rw [← hu, ← hw] at this; exact this
  -- 4. the Bézout split `b·dn + c·ds = r`.
  have hds0 : cnormG ds ≠ [] := fun h => hds_ne ((cnormG_eq_nil_iff ds).mp h)
  have hbcr : toPolyG b * toPolyG dn + toPolyG c * toPolyG ds = toPolyG r := by
    have := toPolyG_cextendedEuclideanSplit fuel dn ds r u w hds0 hbez
    rw [← hb, ← hc] at this; exact this
  -- assemble the field identity.
  show (algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG q))
      + algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG b)
          / algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG ds)
      + algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG c)
          / algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG dn)
    = algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG a)
        / algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG d)
  exact canonicalRepFast_field_identity (toPolyG a) (toPolyG d) (toPolyG q) (toPolyG r)
    (toPolyG dn) (toPolyG ds) (toPolyG b) (toPolyG c) hd hdn_ne hds_ne hadiv hsplit_eq hbcr

/-! ### Restatements against the intended wording (anonymous `example`s) -/

-- The Bézout cofactors solve `u·a + w·b = 1` (coprime case: gcd `g` a nonzero constant).
example {α : Type*} [CField α] [CFieldSpec α] (fuel : ℕ) (a b : CPolyG α)
    (hgdeg : (toPolyG (cgcdExtG fuel a b).1).natDegree = 0)
    (hgne : toPolyG (cgcdExtG fuel a b).1 ≠ 0) :
    toPolyG (CPolyG.cbezoutOne fuel a b).1 * toPolyG a
        + toPolyG (CPolyG.cbezoutOne fuel a b).2 * toPolyG b = 1 :=
  toPolyG_cbezoutOne fuel a b hgdeg hgne

-- The Bézout split solves `b·dₙ + c·dₛ = r` given a Bézout pair `u·dₙ + w·dₛ = 1`.
example {α : Type*} [CField α] [CFieldSpec α] (fuel : ℕ) (dn ds r u w : CPolyG α)
    (hds0 : cnormG ds ≠ [])
    (hbez : toPolyG u * toPolyG dn + toPolyG w * toPolyG ds = 1) :
    toPolyG (CPolyG.cextendedEuclideanSplit fuel dn ds r u w).1 * toPolyG dn
        + toPolyG (CPolyG.cextendedEuclideanSplit fuel dn ds r u w).2 * toPolyG ds
      = toPolyG r :=
  toPolyG_cextendedEuclideanSplit fuel dn ds r u w hds0 hbez

-- The headline (target 2 capstone): `canonicalRepresentationFast Dt fuel a d = (q, (b, dₛ), (c, dₙ))`,
-- read over ℚ(x)(t) = `RatFunc (RatFunc ℚ)`, reconstructs `f = a/d` — `q + b/dₛ + c/dₙ = a/d` — under
-- the transparent per-node regularity preconditions a real run satisfies.
example (Dt : CPolyG QFunNZ) (fuel : ℕ) (a d : CPolyG QFunNZ)
    (hreg : CCanonicalRepFastRegular Dt fuel a d) :
    (algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
          (toPolyG (CPolyG.canonicalRepresentationFast Dt fuel a d).1))
        + algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
              (toPolyG (CPolyG.canonicalRepresentationFast Dt fuel a d).2.1.1)
            / algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
              (toPolyG (CPolyG.canonicalRepresentationFast Dt fuel a d).2.1.2)
        + algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
              (toPolyG (CPolyG.canonicalRepresentationFast Dt fuel a d).2.2.1)
            / algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
              (toPolyG (CPolyG.canonicalRepresentationFast Dt fuel a d).2.2.2)
      = algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG a)
          / algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) (toPolyG d) :=
  canonicalRepFast_reconstructs Dt fuel a d hreg

end DeepWiki.SymbolicIntegration
