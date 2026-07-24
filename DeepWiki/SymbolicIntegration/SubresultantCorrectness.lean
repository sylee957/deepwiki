import DeepWiki.ComputableAlgebra.Fraction
import DeepWiki.SymbolicIntegration.SubresultantCorrectness.ChainEndpoint
import DeepWiki.SymbolicIntegration.SubresultantCorrectness.DividedStep
import DeepWiki.SymbolicIntegration.SubresultantCorrectness.FilterPrimitive
import DeepWiki.SymbolicIntegration.SubresultantCorrectness.LrtOperands
import DeepWiki.SymbolicIntegration.SubresultantCorrectness.PseudoRemainderStep
import DeepWiki.SymbolicIntegration.Engine.PrimPRSRegular.Degree
import DeepWiki.Algebra.SubresultantPRS
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree

/-! # Bridging the computable subresultant PRS to the abstract subresultant
Connects the computable bivariate PRS engine (`GBPolyCore ℚ = ℚ[t][x]`, `GBPolyCore.gbpsremainderCore`, `subresPRS`) to the
abstract Sylvester-submatrix `subresultant` through the `DensePoly.toPoly : GBPolyCore ℚ → (ℚ[X])[X]` homomorphism, up to
the full `lrtGcdCompute ↔ lrtSubresultant` agreement over a residue ring. -/

open Polynomial

namespace DeepWiki.SymbolicIntegration.Compute

/-! ### The `bmonicXmodR` mod-`R` unit bridge (`lrtSubresultantCompute → lrtGcdCompute`)
Modeling the residue ring `ℚ[t]/(R)` by an arbitrary ring hom `φ : ℚ[X] →+* S` killing `toPoly R`, the
monic-in-`x` normalization `bmonicXmodR` is multiplication by a residue-ring unit. -/

/-- For `φ` killing `toPoly R`, reducing `c` modulo `R` does not change its image under `φ`. -/
theorem map_toPoly_cmodWf {S : Type*} [CommRing S] (φ : ℚ[X] →+* S) (c R : DensePoly ℚ)
    (hR : cnorm R ≠ []) (hφR : φ (toPoly R) = 0) :
    φ (toPoly (CPolyEuclidean.mod c R)) = φ (toPoly c) := by
  have hdiv : toPoly c = toPoly (CPolyEuclidean.div c R) * toPoly R
      + toPoly (CPolyEuclidean.mod c R) := by
    exact DensePoly.toPolyG_cmodWf c R hR
  rw [hdiv, map_add, map_mul, hφR, mul_zero, zero_add]

/-- With `Φ = mapRingHom φ` and `φ` killing `toPoly R`,
mapping coefficientwise remainder modulo `R` does not change `Φ (DensePoly.toPoly p)`. -/
theorem mapRingHom_toPolyG_map_cmodWf {S : Type*} [CommRing S]
    (φ : ℚ[X] →+* S) (R : DensePoly ℚ)
    (p : GBPolyCore ℚ) (hR : cnorm R ≠ []) (hφR : φ (toPoly R) = 0) :
    (Polynomial.mapRingHom φ)
        (DensePoly.toPoly (p.map (fun c => CPolyEuclidean.mod c R)))
      = (Polynomial.mapRingHom φ) (DensePoly.toPoly p) := by
  induction p with
  | nil => simp
  | cons a as ih =>
    rw [List.map_cons, DensePoly.toPolyG_cons_dense, DensePoly.toPolyG_cons_dense, map_add, map_add, map_mul, map_mul, ih]
    congr 1
    rw [Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.map_C]
    change Polynomial.C (φ (toPoly (CPolyEuclidean.mod a R))) = Polynomial.C (φ (toPoly a))
    rw [map_toPoly_cmodWf φ a R hR hφR]

/-- With `Φ = mapRingHom φ` and `φ` killing `toPoly R`, `Φ (DensePoly.toPoly (bredR R p)) = Φ (DensePoly.toPoly p)`. -/
theorem mapRingHom_toPolyG_bredR {S : Type*} [CommRing S] (φ : ℚ[X] →+* S) (R : DensePoly ℚ)
    (p : GBPolyCore ℚ) (hR : cnorm R ≠ []) (hφR : φ (toPoly R) = 0) :
    (Polynomial.mapRingHom φ) (DensePoly.toPoly (bredR R p)) = (Polynomial.mapRingHom φ) (DensePoly.toPoly p) := by
  rw [bredR, GBPolyCore.toPolyG_gbnormCore,
    mapRingHom_toPolyG_map_cmodWf φ R p hR hφR]

/-- `cinvMod` is the mod-`R` inverse: for `φ` killing `toPoly R`, when the extended-Euclidean gcd of `c, R`
reduces to a nonzero constant `C u`, `φ (toPoly (cinvMod R c)) · φ (toPoly c) = 1`. -/
theorem map_toPoly_cinvMod_mul {S : Type*} [CommRing S] (φ : ℚ[X] →+* S) (R c : DensePoly ℚ)
    (hR : cnorm R ≠ []) (hφR : φ (toPoly R) = 0) {u : ℚ} (hu : u ≠ 0)
    (hg : toPoly (CPolyEuclidean.gcdExt c R).1 = Polynomial.C u) :
    φ (toPoly (cinvMod R c)) * φ (toPoly c) = 1 := by
  -- Bézout: toPoly s · toPoly c + toPoly t · toPoly R = toPoly g = C u
  have hbez : toPoly (CPolyEuclidean.gcdExt c R).2.1 * toPoly c
      + toPoly (CPolyEuclidean.gcdExt c R).2.2 * toPoly R
      = toPoly (CPolyEuclidean.gcdExt c R).1 := by
    simpa only [CPolyEuclidean.gcdExt_dense_eq, CFieldSpec.toK_rat] using
      DensePoly.toPolyG_cgcdWf c R
  -- clead g = u (leading coeff of the constant C u)
  have hlead : clead (CPolyEuclidean.gcdExt c R).1 = u := by
    change CRingSpec.toR (clead (CPolyEuclidean.gcdExt c R).1) = u
    rw [DensePoly.toR_cleadG_eq_leadingCoeff, hg, Polynomial.leadingCoeff_C]
  -- φ image of the inverse: drop the remainder, expand the cscale
  rw [cinvMod]
  -- cinvMod R c = cmodWf (cscale (clead g)⁻¹ s) R, with s from `cgcdWf c R`.
  rw [map_toPoly_cmodWf φ _ R hR hφR, DensePoly.toPolyG_cscaleG, toR_eq_toK, CFieldSpec.toK_rat,
    map_mul, hlead]
  -- now: φ (C u⁻¹) * φ (toPoly s) * φ (toPoly c) = 1
  -- from Bézout image: φ(toPoly s)·φ(toPoly c) = φ (C u)
  have himg : φ (toPoly (CPolyEuclidean.gcdExt c R).2.1) * φ (toPoly c)
      = φ (Polynomial.C u) := by
    have := congrArg φ hbez
    rw [map_add, map_mul, map_mul, hφR, mul_zero, add_zero, hg] at this
    exact this
  rw [mul_assoc, himg, ← map_mul, ← Polynomial.C_mul, inv_mul_cancel₀ hu, Polynomial.C_1, map_one]

/-- With `Φ = mapRingHom φ` and `φ` killing `toPoly R`,
mapping `c * inv` coefficientwise modulo `R` scales `Φ (DensePoly.toPoly q)` by `φ (toPoly inv)`. -/
theorem mapRingHom_toPolyG_map_cmodWf_cmul {S : Type*} [CommRing S]
    (φ : ℚ[X] →+* S)
    (R inv : DensePoly ℚ) (q : GBPolyCore ℚ) (hR : cnorm R ≠ []) (hφR : φ (toPoly R) = 0) :
    (Polynomial.mapRingHom φ)
        (DensePoly.toPoly (q.map (fun c => CPolyEuclidean.mod (cmul c inv) R)))
      = Polynomial.C (φ (toPoly inv)) * (Polynomial.mapRingHom φ) (DensePoly.toPoly q) := by
  induction q with
  | nil => simp
  | cons a as ih =>
    rw [List.map_cons, DensePoly.toPolyG_cons_dense, DensePoly.toPolyG_cons_dense, map_add, map_add, map_mul, map_mul, ih, mul_add]
    congr 1
    · rw [Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.map_C]
      change Polynomial.C (φ (toPoly (CPolyEuclidean.mod (cmul a inv) R)))
          = Polynomial.C (φ (toPoly inv)) * Polynomial.C (φ (toPoly a))
      rw [map_toPoly_cmodWf φ _ R hR hφR]
      rw [DensePoly.toPolyG_cmulG, map_mul, Polynomial.C_mul, mul_comm]
    · rw [Polynomial.coe_mapRingHom (f := φ), Polynomial.map_X]; ring

/-- With `Φ = mapRingHom φ` and `φ` killing `toPoly R`, when the leading coefficient's mod-`R` gcd reduces
to a nonzero constant `C u`, `Φ (DensePoly.toPoly (bmonicXmodR R p)) = C (φ (toPoly inv)) · Φ (DensePoly.toPoly p)` with
`φ (toPoly inv)` a unit in `S`. -/
theorem mapRingHom_toPolyG_bmonicXmodR {S : Type*} [CommRing S]
    (φ : ℚ[X] →+* S) (R : DensePoly ℚ)
    (p : GBPolyCore ℚ) (hR : cnorm R ≠ []) (hφR : φ (toPoly R) = 0) {u : ℚ} (hu : u ≠ 0)
    (hg : toPoly (CPolyEuclidean.gcdExt (GBPolyCore.gblcCore (bredR R p)) R).1 = Polynomial.C u)
    (hpz : ¬ DensePoly.cisZero (bredR R p) = true) :
    (Polynomial.mapRingHom φ) (DensePoly.toPoly (bmonicXmodR R p))
        = Polynomial.C (φ (toPoly (cinvMod R (GBPolyCore.gblcCore (bredR R p)))))
          * (Polynomial.mapRingHom φ) (DensePoly.toPoly p)
      ∧ φ (toPoly (cinvMod R (GBPolyCore.gblcCore (bredR R p))))
          * φ (toPoly (GBPolyCore.gblcCore (bredR R p))) = 1 := by
  refine ⟨?_, map_toPoly_cinvMod_mul φ R (GBPolyCore.gblcCore (bredR R p)) hR hφR hu hg⟩
  rw [bmonicXmodR]
  simp only [hpz, Bool.false_eq_true, if_false]
  rw [GBPolyCore.toPolyG_gbnormCore,
    mapRingHom_toPolyG_map_cmodWf_cmul φ R
      (cinvMod R (GBPolyCore.gblcCore (bredR R p)))
      (bredR R p) hR hφR,
    mapRingHom_toPolyG_bredR φ R p hR hφR]

/-! ### The full `lrtGcdCompute ↔ lrtSubresultant` agreement over the residue ring `ℚ[t]/(R)` -/

/-- The full `lrtGcdCompute ↔ lrtSubresultant` agreement over `S = ℚ[t]/(R)`: for a residue map
`φ : ℚ[X] →+* S` killing `toPoly R`, under the whole-chain and regularity hypotheses,
`IsSimilar (Φ (lrtSubresultant A D j)) (Φ (DensePoly.toPoly (lrtGcdCompute fuel j R A D)))`. -/
theorem lrtGcdCompute_isSimilar_lrtSubresultant {S : Type*} [CommRing S] [IsDomain S] (φ : ℚ[X] →+* S)
    (fuel : ℕ) (R A D : DensePoly ℚ) (G : ℕ → GBPolyCore ℚ) (bt : ℕ → DensePoly ℚ) (s : ℕ → GBPolyCore ℚ) (c : ℕ → DensePoly ℚ) (m : ℕ)
    (hRcn : cnorm R ≠ []) (hφR : φ (toPoly R) = 0)
    (hG0 : G 0 = liftCtoBPoly D) (hG1 : G 1 = bArgAmtD' A D)
    (hd0 : (DensePoly.toPoly (G 0)).natDegree = (toPoly D).natDegree)
    (hd1 : (DensePoly.toPoly (G 1)).natDegree = (toPoly D).natDegree - 1)
    (hchain : IsSubresPRSChainInput fuel G bt s c m)
    (hfilt : DensePoly.toPoly (bsubresultantGcd fuel (DensePoly.toPoly (G (m + 2))).natDegree (G 0) (G 1))
      = DensePoly.toPoly (G (m + 2)))
    (hprim : IsPrimitivePartXInput
      (bsubresultantGcd fuel (DensePoly.toPoly (G (m + 2))).natDegree (G 0) (G 1)))
    (hne : ∀ a b : ℚ[X], a ≠ 0 → b ≠ 0 →
        Polynomial.C a * lrtSubresultant (toPoly A) (toPoly D) (DensePoly.toPoly (G (m + 2))).natDegree
          = Polynomial.C b * DensePoly.toPoly (lrtSubresultantCompute fuel (DensePoly.toPoly (G (m + 2))).natDegree A D)
        → φ a ≠ 0 ∧ φ b ≠ 0)
    {u : ℚ} (hu : u ≠ 0)
    (hgu : toPoly (CPolyEuclidean.gcdExt
        (GBPolyCore.gblcCore (bredR R (lrtSubresultantCompute fuel (DensePoly.toPoly (G (m + 2))).natDegree A D))) R).1
      = Polynomial.C u)
    (hpz : ¬ DensePoly.cisZero (bredR R
        (lrtSubresultantCompute fuel (DensePoly.toPoly (G (m + 2))).natDegree A D)) = true) :
    IsSimilar ((Polynomial.mapRingHom φ)
        (lrtSubresultant (toPoly A) (toPoly D) (DensePoly.toPoly (G (m + 2))).natDegree))
      ((Polynomial.mapRingHom φ) (DensePoly.toPoly
        (lrtGcdCompute fuel (DensePoly.toPoly (G (m + 2))).natDegree R A D))) := by
  -- abstract ℚ[t]-similarity, mapped through φ to the residue ring
  have habs := isSimilar_lrtSubresultant_lrtSubresultantCompute fuel A D G bt s c m hG0 hG1 hd0 hd1
    hchain hfilt hprim
  have hmap := isSimilar_mapRingHom φ habs hne
  -- the bmonicXmodR unit bridge: lrtGcdCompute = bmonicXmodR R lrtSubresultantCompute
  obtain ⟨hbridge, hunit⟩ := mapRingHom_toPolyG_bmonicXmodR φ R
    (lrtSubresultantCompute fuel (DensePoly.toPoly (G (m + 2))).natDegree A D) hRcn hφR hu hgu hpz
  have hsimUnit := isSimilar_of_unit_mul
    (A := (Polynomial.mapRingHom φ) (DensePoly.toPoly
      (lrtSubresultantCompute fuel (DensePoly.toPoly (G (m + 2))).natDegree A D)))
    (B := (Polynomial.mapRingHom φ) (DensePoly.toPoly
      (lrtGcdCompute fuel (DensePoly.toPoly (G (m + 2))).natDegree R A D)))
    hunit (by rw [lrtGcdCompute]; exact hbridge)
  exact hmap.trans hsimUnit

/-! ### From the chain agreement to `lrtGcdCompute`
The pieces above assemble the full multi-step subresultant-PRS chain agreement into the headline
`lrtGcdCompute_isSimilar_lrtSubresultant`, with the degree-`j` filter identity and the `bmonicXmodR` unit
bridge both discharged structurally, and the concrete `subresPRS` data supplied by the `goState` section
below. -/

/-! ### Instantiating the abstract chain from the concrete `subresPRS.go`
Mirrors the internal `subresPRS.go` recurrence as a top-level state machine `goState`, so the abstract
chain data `G`/`bt`/`s`/`c` and its side-conditions can be supplied from the real `subresPRS fuel P Q`. -/

/-- ψ-update of one `subresPRS.go` step (Brown–Traub (41)): `ψ' = (−lc Ri)^δ / ψ^(δ−1)`
with the **right** element's leading coefficient (`ψ' = ψ` when `δ = 0`). -/
def goPsi' (Ri : GBPolyCore ℚ) (psi : DensePoly ℚ) (δ : ℕ) : DensePoly ℚ :=
  if δ = 0 then psi else CPolyEuclidean.div (DensePoly.cpow (cneg (GBPolyCore.gblcCore Ri)) δ)
    (DensePoly.cpow psi (δ - 1))

/-- β-divisor of one `subresPRS.go` step (Brown–Traub (38)/(39)): `(−1)^{δ+1}` on the first
step, else `−lc(Ri₋₁)·ψ^δ` with the **un-updated** `ψ`. -/
def goBeta (Ri_1 : GBPolyCore ℚ) (psi : DensePoly ℚ) (δ first : ℕ) : DensePoly ℚ :=
  if first = 1 then DensePoly.cpow (cneg (cnorm [1])) (δ + 1)
  else cmul (cneg (GBPolyCore.gblcCore Ri_1)) (DensePoly.cpow psi δ)

/-- One `subresPRS.go` step on the state `(Ri₋₁, Ri, ψ, first) ↦ (Ri, Ri₊₁, ψ', 0)` with
`δ = cdeg Ri₋₁ − cdeg Ri`, `Ri₊₁ = bdivC (prem Ri₋₁ Ri) β`, `β = goBeta`, `ψ' = goPsi'`. -/
def goStep (fuel : ℕ) : GBPolyCore ℚ × GBPolyCore ℚ × DensePoly ℚ × ℕ → GBPolyCore ℚ × GBPolyCore ℚ × DensePoly ℚ × ℕ
  | (Ri_1, Ri, psi, first) =>
    let δ := DensePoly.cdeg Ri_1 - DensePoly.cdeg Ri
    let beta := goBeta Ri_1 psi δ first
    let Ri1 := bdivC (GBPolyCore.gbpsremainderCore fuel Ri_1 Ri) beta
    (Ri, Ri1, goPsi' Ri psi δ, 0)

/-- The `subresPRS.go` state at index `i`: `goState fuel s₀ i = goStepⁱ s₀`. -/
def goState (fuel : ℕ) (s0 : GBPolyCore ℚ × GBPolyCore ℚ × DensePoly ℚ × ℕ) : ℕ → GBPolyCore ℚ × GBPolyCore ℚ × DensePoly ℚ × ℕ
  | 0 => s0
  | i + 1 => goStep fuel (goState fuel s0 i)

/-- `goState fuel (goStep fuel s₀) k = goState fuel s₀ (k+1)`. -/
theorem goState_goStep (fuel : ℕ) (s0 : GBPolyCore ℚ × GBPolyCore ℚ × DensePoly ℚ × ℕ) (k : ℕ) :
    goState fuel (goStep fuel s0) k = goState fuel s0 (k + 1) := by
  induction k generalizing s0 with
  | zero => rfl
  | succ n ih => rw [goState, goState, ih]

/-- `(goState fuel s₀ (l+1)).1 = (goState fuel s₀ l).2.1`. -/
theorem goState_succ_fst (fuel : ℕ) (s0 : GBPolyCore ℚ × GBPolyCore ℚ × DensePoly ℚ × ℕ) (l : ℕ) :
    (goState fuel s0 (l + 1)).1 = (goState fuel s0 l).2.1 := by
  show (goStep fuel (goState fuel s0 l)).1 = _
  rw [goStep]

/-- The divided-PRS recurrence for `goState`: `(goState fuel s₀ (l+2)).1 = bdivC (prem …)
(goBeta …)`, holding definitionally. -/
theorem goState_fst_add_two (fuel : ℕ) (s0 : GBPolyCore ℚ × GBPolyCore ℚ × DensePoly ℚ × ℕ) (l : ℕ) :
    (goState fuel s0 (l + 2)).1
      = bdivC (GBPolyCore.gbpsremainderCore fuel (goState fuel s0 l).1 (goState fuel s0 (l + 1)).1)
          (goBeta (goState fuel s0 l).1 (goState fuel s0 l).2.2.1
            (DensePoly.cdeg (goState fuel s0 l).1 - DensePoly.cdeg (goState fuel s0 l).2.1)
            (goState fuel s0 l).2.2.2) := by
  rw [goState_succ_fst fuel s0 (l + 1)]
  show (goStep fuel (goState fuel s0 l)).2.1 = _
  rw [goStep]
  rw [goState_succ_fst fuel s0 l]

/-! #### The `go`-list ↔ `goState` bridge -/

/-- While `s.2.1` is nonzero, `go fuel (fo+1) …` emits it and recurses on the `goStep`-advanced state. -/
theorem go_step_state (fuel fo : ℕ) (s : GBPolyCore ℚ × GBPolyCore ℚ × DensePoly ℚ × ℕ) (hz : ¬ DensePoly.cisZero s.2.1 = true) :
    subresPRS.go fuel (fo + 1) s.1 s.2.1 s.2.2.1 s.2.2.2
      = s.2.1 :: subresPRS.go fuel fo (goStep fuel s).1 (goStep fuel s).2.1
          (goStep fuel s).2.2.1 (goStep fuel s).2.2.2 := by
  obtain ⟨Ri_1, Ri, psi, dp⟩ := s
  rw [subresPRS.go.eq_2]
  simp only at hz
  simp only [hz, Bool.false_eq_true, if_false]
  rfl

/-- While the chain stays nonzero through index `k` and `k < fo`, the `k`-th element of `go fuel fo …` is
`(goState fuel s k).2.1`. -/
theorem go_getD (fuel : ℕ) (s : GBPolyCore ℚ × GBPolyCore ℚ × DensePoly ℚ × ℕ) (k fo : ℕ) (hfo : k < fo)
    (hnz : ∀ i ≤ k, ¬ DensePoly.cisZero (goState fuel s i).2.1 = true) :
    (subresPRS.go fuel fo s.1 s.2.1 s.2.2.1 s.2.2.2).getD k [] = (goState fuel s k).2.1 := by
  induction k generalizing s fo with
  | zero =>
    obtain ⟨f', rfl⟩ : ∃ f', fo = f' + 1 := ⟨fo - 1, by omega⟩
    rw [go_step_state fuel f' s (hnz 0 (by omega))]
    rfl
  | succ n ih =>
    obtain ⟨f', rfl⟩ : ∃ f', fo = f' + 1 := ⟨fo - 1, by omega⟩
    rw [go_step_state fuel f' s (hnz 0 (by omega)), List.getD_cons_succ,
      ih (goStep fuel s) f' (by omega)
        (fun i hi => by rw [goState_goStep]; exact hnz (i + 1) (by omega)),
      goState_goStep]

/-- The `i`-th element of `subresPRS fuel P Q` is `(goState fuel (P,Q,[-1],…) i).1`, while the chain stays
nonzero through `i−1` and `i ≤ fuel`. -/
theorem subresPRS_getD (fuel : ℕ) (P Q : GBPolyCore ℚ) (i : ℕ) (hfo : i ≤ fuel)
    (hnz : ∀ k < i, ¬ DensePoly.cisZero (goState fuel (P, Q, [-1], 1) k).2.1 = true) :
    (subresPRS fuel P Q).getD i [] = (goState fuel (P, Q, [-1], 1) i).1 := by
  rw [subresPRS.eq_def]
  cases i with
  | zero => rfl
  | succ n =>
    rw [List.getD_cons_succ]
    have h := go_getD fuel (P, Q, [-1], 1) n fuel (by omega)
      (fun k hk => hnz k (by omega))
    simp only at h
    rw [h, goState_succ_fst]

/-- If `s.2.1` is zero, `go fuel fo … = []`. -/
theorem go_zero (fuel fo : ℕ) (s : GBPolyCore ℚ × GBPolyCore ℚ × DensePoly ℚ × ℕ) (hz : DensePoly.cisZero s.2.1 = true) :
    subresPRS.go fuel fo s.1 s.2.1 s.2.2.1 s.2.2.2 = [] := by
  cases fo with
  | zero => rw [subresPRS.go.eq_1]
  | succ f' =>
    obtain ⟨Ri_1, Ri, psi, dp⟩ := s
    rw [subresPRS.go.eq_2]
    simp only at hz
    simp only [hz, if_true]

/-- When the chain is nonzero through `k`, zero at `k+1`, and fuel suffices,
`go fuel fo … = (List.range (k+1)).map (fun i => (goState fuel s i).2.1)`. -/
theorem go_eq_range (fuel : ℕ) (s : GBPolyCore ℚ × GBPolyCore ℚ × DensePoly ℚ × ℕ) (k fo : ℕ) (hfo : k + 1 < fo)
    (hnz : ∀ i ≤ k, ¬ DensePoly.cisZero (goState fuel s i).2.1 = true)
    (hz : DensePoly.cisZero (goState fuel s (k + 1)).2.1 = true) :
    subresPRS.go fuel fo s.1 s.2.1 s.2.2.1 s.2.2.2
      = (List.range (k + 1)).map (fun i => (goState fuel s i).2.1) := by
  induction k generalizing s fo with
  | zero =>
    obtain ⟨f', rfl⟩ : ∃ f', fo = f' + 1 := ⟨fo - 1, by omega⟩
    rw [go_step_state fuel f' s (hnz 0 (by omega)),
      go_zero fuel f' (goStep fuel s) hz]
    rfl
  | succ n ih =>
    obtain ⟨f', rfl⟩ : ∃ f', fo = f' + 1 := ⟨fo - 1, by omega⟩
    rw [go_step_state fuel f' s (hnz 0 (by omega)),
      ih (goStep fuel s) f' (by omega)
        (fun i hi => by rw [goState_goStep]; exact hnz (i + 1) (by omega))
        (by rw [goState_goStep]; exact hz)]
    conv_rhs => rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    rw [goState_goStep]

/-- If `N` is the unique index below `n` with `q N = true`, then `(List.range n).filter q = [N]`. -/
theorem filter_range_unique {n N : ℕ} (q : ℕ → Bool) (hN : N < n) (hqN : q N = true)
    (huniq : ∀ i, i < n → q i = true → i = N) :
    (List.range n).filter q = [N] := by
  have hnodup : (List.range n).Nodup := List.nodup_range
  have hfnodup : ((List.range n).filter q).Nodup := hnodup.filter q
  have hmem : N ∈ (List.range n).filter q := by
    rw [List.mem_filter, List.mem_range]; exact ⟨hN, hqN⟩
  have hall : ∀ x ∈ (List.range n).filter q, x = N := by
    intro x hx
    rw [List.mem_filter, List.mem_range] at hx
    exact huniq x hx.1 hx.2
  cases hl : (List.range n).filter q with
  | nil => rw [hl] at hmem; simp at hmem
  | cons a as =>
    rw [hl] at hall hmem hfnodup
    have ha : a = N := hall a (by simp)
    have has : as = [] := by
      cases as with
      | nil => rfl
      | cons b bs =>
        exfalso
        have hb : b = N := hall b (by simp)
        rw [ha, hb] at hfnodup
        simp at hfnodup
    rw [ha, has]

/-- When the chain `G i := (goState fuel (P,Q,[-1],…) i).1` is nonzero through `N`, zero at `N+1`, and
`N+1 < fuel`, `subresPRS fuel P Q = (List.range (N+1)).map G`. -/
theorem subresPRS_eq_range (fuel : ℕ) (P Q : GBPolyCore ℚ) (N : ℕ) (hfo : N + 1 < fuel)
    (hnz : ∀ i ≤ N, ¬ DensePoly.cisZero (goState fuel (P, Q, [-1], 1) i).1 = true)
    (hzN : DensePoly.cisZero (goState fuel (P, Q, [-1], 1) (N + 1)).1 = true) :
    subresPRS fuel P Q
      = (List.range (N + 1)).map (fun i => (goState fuel (P, Q, [-1], 1) i).1) := by
  set s0 : GBPolyCore ℚ × GBPolyCore ℚ × DensePoly ℚ × ℕ := (P, Q, [-1], 1) with hs0
  rw [subresPRS.eq_def]
  cases N with
  | zero =>
    have hQz : DensePoly.cisZero s0.2.1 = true := by
      have := hzN; rw [goState_succ_fst] at this; exact this
    rw [go_zero fuel fuel s0 hQz]
    show [P] = [(goState fuel s0 0).1]
    rfl
  | succ n =>
    rw [go_eq_range fuel s0 n fuel (by omega)
      (fun i hi => by rw [← goState_succ_fst]; exact hnz (i + 1) (by omega))
      (by rw [← goState_succ_fst]; exact hzN)]
    conv_rhs => rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    refine congrArg (P :: ·) (List.map_congr_left ?_)
    intro i _
    simp only [Function.comp_apply, goState_succ_fst]

/-- If `f (i+1) < f i` for all `i < N`, then `N` is the only index `i ≤ N` with `f i = f N`. -/
theorem unique_of_strictAnti (f : ℕ → ℕ) (N : ℕ) (hstrict : ∀ i < N, f (i + 1) < f i) :
    ∀ i ≤ N, f i = f N → i = N := by
  have mono : ∀ j ≤ N, ∀ i < j, f j < f i := by
    intro j hj
    induction j with
    | zero => intro i hi; omega
    | succ n ih =>
      intro i hi
      have hstep : f (n + 1) < f n := hstrict n (by omega)
      rcases Nat.lt_or_ge i n with hlt | hge
      · have := ih (by omega) i hlt; omega
      · have : i = n := by omega
        subst this; omega
  intro i hi heq
  by_contra hne
  have hiN : i < N := lt_of_le_of_ne hi hne
  have := mono N (le_refl N) i hiN
  omega

/-- The degree-`DensePoly.cdeg (G N)` nonzero filter of `subresPRS fuel P Q` is `[G N]`, under nonzero-through-`N`,
zero-at-`N+1`, strict `DensePoly.cdeg` decrease, and `N+1 < fuel`. -/
theorem subresPRS_filter_singleton (fuel : ℕ) (P Q : GBPolyCore ℚ) (N : ℕ) (hfo : N + 1 < fuel)
    (hnz : ∀ i ≤ N, ¬ DensePoly.cisZero (goState fuel (P, Q, [-1], 1) i).1 = true)
    (hzN : DensePoly.cisZero (goState fuel (P, Q, [-1], 1) (N + 1)).1 = true)
    (hstrict : ∀ i < N, DensePoly.cdeg (goState fuel (P, Q, [-1], 1) (i + 1)).1
        < DensePoly.cdeg (goState fuel (P, Q, [-1], 1) i).1) :
    (subresPRS fuel P Q).filter
        (fun R => decide (DensePoly.cdeg R = DensePoly.cdeg (goState fuel (P, Q, [-1], 1) N).1
          ∧ ¬ DensePoly.cisZero R))
      = [(goState fuel (P, Q, [-1], 1) N).1] := by
  set s0 : GBPolyCore ℚ × GBPolyCore ℚ × DensePoly ℚ × ℕ := (P, Q, [-1], 1) with hs0
  set G := fun i => (goState fuel s0 i).1 with hG
  rw [subresPRS_eq_range fuel P Q N hfo hnz hzN, List.filter_map]
  have hfilt : (List.range (N + 1)).filter
      ((fun R => decide (DensePoly.cdeg R = DensePoly.cdeg (G N) ∧ ¬ DensePoly.cisZero R)) ∘ G) = [N] := by
    apply filter_range_unique
    · omega
    · simp only [Function.comp_apply, decide_eq_true_eq, true_and]
      exact hnz N (le_refl N)
    · intro i hi hqi
      simp only [Function.comp_apply, decide_eq_true_eq] at hqi
      exact unique_of_strictAnti (fun i => DensePoly.cdeg (G i)) N hstrict i (by omega) hqi.1
  rw [hfilt, List.map_singleton]

/-! #### Concrete chain data from `subresPRS` -/

/-- The concrete `subresPRS` chain element `chain fuel P Q i := (goState fuel (P,Q,[-1],…) i).1`. -/
noncomputable def chain (fuel : ℕ) (P Q : GBPolyCore ℚ) (i : ℕ) : GBPolyCore ℚ :=
  (goState fuel (P, Q, [-1], 1) i).1

/-- The concrete `subresPRS` β-divisor `chainBt fuel P Q l := goBeta …` at the `l`-th state. -/
noncomputable def chainBt (fuel : ℕ) (P Q : GBPolyCore ℚ) (l : ℕ) : DensePoly ℚ :=
  goBeta (goState fuel (P, Q, [-1], 1) l).1
    (goState fuel (P, Q, [-1], 1) l).2.2.1
    (DensePoly.cdeg (goState fuel (P, Q, [-1], 1) l).1
      - DensePoly.cdeg (goState fuel (P, Q, [-1], 1) l).2.1)
    (goState fuel (P, Q, [-1], 1) l).2.2.2

/-- The concrete pseudo-division quotient `chainS fuel P Q l` for the chain pair `(chain l, chain (l+1))`. -/
noncomputable def chainS (fuel : ℕ) (P Q : GBPolyCore ℚ) (l : ℕ) : GBPolyCore ℚ :=
  (GBPolyCore.toPolyG_gbpsremainderCore fuel (chain fuel P Q l) (chain fuel P Q (l + 1))).choose

/-- The concrete pseudo-division content `chainC fuel P Q l` for the chain pair `(chain l, chain (l+1))`. -/
noncomputable def chainC (fuel : ℕ) (P Q : GBPolyCore ℚ) (l : ℕ) : DensePoly ℚ :=
  (GBPolyCore.toPolyG_gbpsremainderCore fuel (chain fuel P Q l) (chain fuel P Q (l + 1))).choose_spec.choose

/-- `chain fuel P Q 0 = P`. -/
@[simp] theorem chainG_zero (fuel : ℕ) (P Q : GBPolyCore ℚ) : chain fuel P Q 0 = P := rfl

/-- `chain fuel P Q 1 = Q`. -/
@[simp] theorem chainG_one (fuel : ℕ) (P Q : GBPolyCore ℚ) : chain fuel P Q 1 = Q := by
  rw [chain, goState_succ_fst]; rfl

/-- The pseudo-division identity holds for the concrete `chainS`/`chainC`. -/
theorem chain_hsc (fuel : ℕ) (P Q : GBPolyCore ℚ) (l : ℕ) :
    Polynomial.C (toPoly (chainC fuel P Q l)) * DensePoly.toPoly (chain fuel P Q l)
      = DensePoly.toPoly (chainS fuel P Q l) * DensePoly.toPoly (chain fuel P Q (l + 1))
        + DensePoly.toPoly (GBPolyCore.gbpsremainderCore fuel (chain fuel P Q l) (chain fuel P Q (l + 1))) :=
  (GBPolyCore.toPolyG_gbpsremainderCore fuel (chain fuel P Q l) (chain fuel P Q (l + 1))).choose_spec.choose_spec

/-- The divided-PRS recurrence `chain (l+2) = bdivC (prem (chain l) (chain (l+1))) (chainBt l)`. -/
theorem chain_hG2 (fuel : ℕ) (P Q : GBPolyCore ℚ) (l : ℕ) :
    chain fuel P Q (l + 2)
      = bdivC (GBPolyCore.gbpsremainderCore fuel (chain fuel P Q l) (chain fuel P Q (l + 1)))
          (chainBt fuel P Q l) := by
  rw [chain, goState_fst_add_two, chainBt]
  rfl

/-- The filter identity for the concrete chain:
`DensePoly.toPoly (bsubresultantGcd fuel (deg (chain (m+2))) P Q) = DensePoly.toPoly (chain (m+2))`. -/
theorem chain_hfilt (fuel : ℕ) (P Q : GBPolyCore ℚ) (m : ℕ) (hfo : m + 2 + 1 < fuel)
    (hnz : ∀ i ≤ m + 2, ¬ DensePoly.cisZero (chain fuel P Q i) = true)
    (hzN : DensePoly.cisZero (chain fuel P Q (m + 2 + 1)) = true)
    (hstrict : ∀ i < m + 2, DensePoly.cdeg (chain fuel P Q (i + 1)) < DensePoly.cdeg (chain fuel P Q i)) :
    DensePoly.toPoly (bsubresultantGcd fuel (DensePoly.toPoly (chain fuel P Q (m + 2))).natDegree P Q)
      = DensePoly.toPoly (chain fuel P Q (m + 2)) := by
  have hfil := subresPRS_filter_singleton fuel P Q (m + 2) hfo hnz hzN hstrict
  rw [DensePoly.cdegG_eq_natDegree] at hfil
  exact toBPoly_bsubresultantGcd_eq_of_filter_singleton fuel P Q (chain fuel P Q) m hfil

/-! ### The clean concrete agreement: `lrtGcdCompute ↔ lrtSubresultant` for the real `subresPRS` -/

/-- The clean concrete `lrtGcdCompute ↔ lrtSubresultant` agreement for the real
`subresPRS fuel (liftCtoBPoly D) (bArgAmtD' A D)` chain: for a residue map `φ` killing `toPoly R`, under
the regularity inputs, `IsSimilar (Φ (lrtSubresultant A D j)) (Φ (DensePoly.toPoly (lrtGcdCompute fuel j R A D)))`
over `S = ℚ[t]/(R)` at `j = (DensePoly.toPoly (chain (m+2))).natDegree`. -/
theorem lrtGcdCompute_isSimilar_lrtSubresultant_concrete {S : Type*} [CommRing S] [IsDomain S]
    (φ : ℚ[X] →+* S) (fuel : ℕ) (R A D : DensePoly ℚ) (m : ℕ)
    (hRcn : cnorm R ≠ []) (hφR : φ (toPoly R) = 0)
    (hd0 : (DensePoly.toPoly (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) 0)).natDegree
      = (toPoly D).natDegree)
    (hd1 : (DensePoly.toPoly (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) 1)).natDegree
      = (toPoly D).natDegree - 1)
    -- singleton-filter inputs (chain nonzero through m+2, zero after, strict DensePoly.cdeg decrease, fuel)
    (hfoF : m + 2 + 1 < fuel)
    (hnzF : ∀ i ≤ m + 2, ¬ DensePoly.cisZero (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) i) = true)
    (hzNF : DensePoly.cisZero (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2 + 1)) = true)
    (hstrictF : ∀ i < m + 2,
      DensePoly.cdeg (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) (i + 1))
        < DensePoly.cdeg (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) i))
    -- Collins β-divisibility + chain degree/nonzero regularity
    (hβcn : ∀ l ≤ m, cnorm (chainBt fuel (liftCtoBPoly D) (bArgAmtD' A D) l) ≠ [])
    (hdiv : ∀ l ≤ m, ∀ a ∈ GBPolyCore.gbpsremainderCore fuel (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) l)
        (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) (l + 1)),
      toPoly (CPolyEuclidean.mod a (chainBt fuel (liftCtoBPoly D) (bArgAmtD' A D) l)) = 0)
    (hc0 : ∀ l ≤ m, toPoly (chainC fuel (liftCtoBPoly D) (bArgAmtD' A D) l) ≠ 0)
    (hβ0 : ∀ l ≤ m, toPoly (chainBt fuel (liftCtoBPoly D) (bArgAmtD' A D) l) ≠ 0)
    (hlc : ∀ l ≤ m, (DensePoly.toPoly (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) (l + 1))).coeff
      (DensePoly.toPoly (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) (l + 1))).natDegree ≠ 0)
    (hcb : ∀ l ≤ m, (DensePoly.toPoly (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) (l + 2))).natDegree
      < (DensePoly.toPoly (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) (l + 1))).natDegree)
    (hjlt : ∀ l < m, (DensePoly.toPoly (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree
      < (DensePoly.toPoly (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) (l + 2))).natDegree)
    (hQ : ∀ l ≤ m, (DensePoly.toPoly (chainS fuel (liftCtoBPoly D) (bArgAmtD' A D) l)).natDegree
        + (DensePoly.toPoly (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) (l + 1))).natDegree
      ≤ (DensePoly.toPoly (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) l)).natDegree)
    (hCne : DensePoly.toPoly (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2)) ≠ 0)
    -- GBPolyCore.gbprimitivePartCore CPolyGcd.computeFn content-exactness on the degree-j element
    (hprim : IsPrimitivePartXInput
      (bsubresultantGcd fuel
        (DensePoly.toPoly (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree
        (liftCtoBPoly D) (bArgAmtD' A D)))
    (hne : ∀ a b : ℚ[X], a ≠ 0 → b ≠ 0 →
        Polynomial.C a * lrtSubresultant (toPoly A) (toPoly D)
            (DensePoly.toPoly (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree
          = Polynomial.C b * DensePoly.toPoly (lrtSubresultantCompute fuel
            (DensePoly.toPoly (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree A D)
        → φ a ≠ 0 ∧ φ b ≠ 0)
    {u : ℚ} (hu : u ≠ 0)
    (hgu : toPoly (CPolyEuclidean.gcdExt
        (GBPolyCore.gblcCore (bredR R (lrtSubresultantCompute fuel
          (DensePoly.toPoly (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree A D))) R).1
      = Polynomial.C u)
    (hpz : ¬ DensePoly.cisZero (bredR R
        (lrtSubresultantCompute fuel
          (DensePoly.toPoly (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree A D)) = true) :
    IsSimilar ((Polynomial.mapRingHom φ)
        (lrtSubresultant (toPoly A) (toPoly D)
          (DensePoly.toPoly (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree))
      ((Polynomial.mapRingHom φ) (DensePoly.toPoly
        (lrtGcdCompute fuel
          (DensePoly.toPoly (chain fuel (liftCtoBPoly D) (bArgAmtD' A D) (m + 2))).natDegree R A D))) := by
  have hfilt := chain_hfilt fuel (liftCtoBPoly D) (bArgAmtD' A D) m hfoF hnzF hzNF hstrictF
  have hchain : IsSubresPRSChainInput fuel
      (chain fuel (liftCtoBPoly D) (bArgAmtD' A D))
      (chainBt fuel (liftCtoBPoly D) (bArgAmtD' A D))
      (chainS fuel (liftCtoBPoly D) (bArgAmtD' A D))
      (chainC fuel (liftCtoBPoly D) (bArgAmtD' A D)) m := {
    exact_step := fun l hl => ⟨chain_hsc fuel (liftCtoBPoly D) (bArgAmtD' A D) l,
      hβcn l hl, hdiv l hl⟩
    next_eq := fun l _ => chain_hG2 fuel (liftCtoBPoly D) (bArgAmtD' A D) l
    scale_toPoly_ne := hc0
    beta_toPoly_ne := hβ0
    leading_coeff_ne := hlc
    degree_drop := hcb
    endpoint_degree_lt := hjlt
    quotient_degree_le := hQ
    endpoint_ne_zero := hCne }
  exact lrtGcdCompute_isSimilar_lrtSubresultant φ fuel R A D
    (chain fuel (liftCtoBPoly D) (bArgAmtD' A D))
    (chainBt fuel (liftCtoBPoly D) (bArgAmtD' A D))
    (chainS fuel (liftCtoBPoly D) (bArgAmtD' A D))
    (chainC fuel (liftCtoBPoly D) (bArgAmtD' A D)) m
    hRcn hφR (chainG_zero fuel (liftCtoBPoly D) (bArgAmtD' A D))
    (chainG_one fuel (liftCtoBPoly D) (bArgAmtD' A D)) hd0 hd1
    hchain hfilt hprim hne hu hgu hpz

/-! ### The `AdjoinRoot.mk ↔ eval-at-root` bridge for `lrtSubresultant` -/

/-- For a field `K`, `f : K[X]`, `S = AdjoinRoot f`, `σ = of f`, `α = root f`, the lifted residue map
`Φ = mapRingHom (mk f)` sends `lrtSubresultant A D j` to
`(lrtSubresultant (A.map σ) (D.map σ) j).map (evalRingHom α)`. -/
theorem mapRingHom_mk_lrtSubresultant {K : Type*} [Field K] (f : K[X]) [Fact (Irreducible f)]
    (A D : K[X]) (j : ℕ) :
    (Polynomial.mapRingHom (AdjoinRoot.mk f)) (lrtSubresultant A D j)
      = (lrtSubresultant (A.map (AdjoinRoot.of f)) (D.map (AdjoinRoot.of f)) j).map
          (Polynomial.evalRingHom (AdjoinRoot.root f)) := by
  set σ : K →+* AdjoinRoot f := AdjoinRoot.of f with hσ
  set α : AdjoinRoot f := AdjoinRoot.root f with hα
  -- `mk f ∘ C = of f = σ` (the base-change embedding of constants).
  have hmkC : (AdjoinRoot.mk f).comp (C : K →+* K[X]) = σ := by
    rw [hσ, AdjoinRoot.of]
  -- the base change `σ = of f` is injective (field hom), so it preserves the `x`-degree parameters.
  have hσinj : Function.Injective σ := (AdjoinRoot.of f).injective
  have hdeg : (D.map σ).natDegree = D.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hσinj D
  -- LHS: push `mk f` through the subresultant determinant (`subresultant_map`), then through the operands.
  rw [Polynomial.coe_mapRingHom, lrtSubresultant, ← subresultant_map]
  -- RHS: specialize the base-changed `lrtSubresultant` at `α` (`lrtSubresultant_eval` shape).
  rw [lrtSubresultant_eval, hdeg]
  congr 1
  · -- `(D.map C).map (mk f) = (D.map σ).map (evalRingHom α … )`-side: both equal `D.map σ`.
    rw [Polynomial.map_map, hmkC]
  · -- the second LRT operand matches: `(A.map C − C X·D'.map C).map (mk f) = A.map σ − C α·(D.map σ)'`.
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_map, Polynomial.map_map, hmkC,
      Polynomial.map_C, AdjoinRoot.mk_X, derivative_map]

end DeepWiki.SymbolicIntegration.Compute
