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

end DeepWiki.SymbolicIntegration
