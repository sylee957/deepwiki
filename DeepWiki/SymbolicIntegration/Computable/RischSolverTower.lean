import DeepWiki.SymbolicIntegration.Computable.LrtAssembly
import DeepWiki.SymbolicIntegration.Computable.LrtGuarded
import DeepWiki.SymbolicIntegration.Computable.RischTower
import DeepWiki.SymbolicIntegration.Computable.RischTowerPrimitive
import DeepWiki.SymbolicIntegration.Computable.RischTowerPrimitiveLrt
import DeepWiki.SymbolicIntegration.Computable.Tower.CarrierRec

/-! # `RischSolver` — the recursive Risch tower solver (base + step)

The genuine, root-free Risch integrator, structured **recursively** over the monomial tower — **the one
solver**. Integrating `a/d ∈ α(t)` decomposes into the polynomial part, the reduced part (root-free LRT),
and the special part, and the **polynomial part's coefficient integration recurses into `RischSolver` for
the coefficient field**. That coefficient recursion is the heart of the transcendental algorithm (Bronstein
§5.3–5.9) — and is exactly what a one-level solver misses: its special-part hook fires only when the
polynomial part has constant coefficients (`D(fp) = 0`).

- **`integrate`** — integrate `a/d ∈ α(t)` (monomial derivative `Dt`) to a root-free `LrtResultG`, or `none`.
- **`sound`** — a successful run is a **genuine** antiderivative (`IsGenuineIntegralResultLrtG`: the LRT
  identity + all residues constant).

The **base** instance (`instRischSolverPrimitive`, from `[PrimitiveFrontierLrt α]`) is the genuine one-level
LRT integrator inlined here — canonical split → special hook → root-free `cIntegrateReducedLrtG` →
`combineSNLrt`, then the residue-constancy guard — correct for the constant-coefficient regime (`ℚ(x)` and any
level whose polynomial part is constant). It supersedes the retired `LawfulRischLevelLrt`. The **step** adds
the coefficient recursion `[RischSolver β] → RischSolver (QFunNZG β)` via the generic-tower limited
integration. See `docs/recursive-risch-tower.md`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial
open scoped Differential

variable {α : Type*} [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
  [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]

/-- **The recursive Risch tower solver, as a class.** `integrate Dt a d` integrates `a/d ∈ α(t)` (with
monomial derivative `Dt`) to a root-free `LrtResultG α`, or declines; `sound` certifies a successful run is a
*genuine* antiderivative (`IsGenuineIntegralResultLrtG`). One instance at each tower level (base + step)
assembles a solver at every depth by resolution. -/
class RischSolver (α : Type*) [CField α] [CFieldSpec α] [CDiffField α] [CDiffFieldSpec α]
    [CFracGcdCoreWf α] [Algebra ℚ (CFieldSpec.K α)] [CharZero (CFieldSpec.K α)]
    [Fact (GcdFFCorrect (α := α))] where
  /-- Integrate `a/d ∈ α(t)` (monomial derivative `Dt`) to a root-free LRT result, or `none`. -/
  integrate : CPolyG α → CPolyG α → CPolyG α → Option (LrtResultG α)
  /-- **Genuine soundness**: a successful run is a true antiderivative of `a/d` with constant residues. -/
  sound : ∀ (Dt a d : CPolyG α) (r : LrtResultG α), toPolyG d ≠ 0 →
    integrate Dt a d = some r → IsGenuineIntegralResultLrtG Dt a d r

/-- **The base integrator** — the genuine one-level LRT primitive integrator: `d ≠ 0` guard, the primitive
case integrator `cIntegrateCaseLrt primitiveGuardedCase` (canonical split → special hook → root-free
`cIntegrateReducedLrtG` → `combineSNLrt`), then the residue-constancy guard `allResiduesConstantLrtG`. -/
def rischIntegratePrimitive [CRischField α] [Fact (GcdFFCorrect (α := α))] [PrimitiveFrontierLrt α]
    (Dt a d : CPolyG α) : Option (LrtResultG α) :=
  if cisZeroG d then none else
    (cIntegrateCaseLrt primitiveGuardedCase Dt a d).bind fun res =>
      if allResiduesConstantLrtG res then some res else none

/-- **Base soundness** — a successful `rischIntegratePrimitive` run is a genuine antiderivative: the LRT
identity (via `cIntegrateCaseLrt_sound` from `primitiveGuardedCase_specialSound` + `PrimitiveFrontierLrt.hreducedLrt`)
plus residue-constancy (the guard). -/
theorem rischSoundPrimitive [CRischField α] [Fact (GcdFFCorrect (α := α))] [PrimitiveFrontierLrt α]
    (Dt a d : CPolyG α) (r : LrtResultG α) (h : rischIntegratePrimitive Dt a d = some r) :
    IsGenuineIntegralResultLrtG Dt a d r := by
  rw [rischIntegratePrimitive] at h
  by_cases hdz : cisZeroG d = true
  · rw [if_pos hdz] at h; simp at h
  · rw [if_neg hdz, Option.bind_eq_some_iff] at h
    obtain ⟨res', hcase, hguard⟩ := h
    have hd0 : toPolyG d ≠ 0 := fun hh => hdz ((cisZeroG_iff d).mpr hh)
    split at hguard
    · rename_i hg
      obtain rfl : res' = r := (Option.some.injEq _ _).mp hguard
      refine ⟨?_, hg⟩
      have h0 : cIntegrateCaseLrt primitiveGuardedCase Dt a d = some res' := hcase
      rw [cIntegrateCaseLrt] at hcase
      rcases hcrep : canonicalRepresentationFastGWf Dt a d with ⟨fp, ⟨b, ds⟩, ⟨cn, dn⟩⟩
      rw [hcrep] at hcase
      dsimp only at hcase
      rcases hspec : primitiveGuardedCase.integrateSpecial Dt fp b ds with _ | ⟨snum, sden⟩
      · rw [hspec] at hcase; simp at hcase
      · rw [hspec] at hcase
        have hSpec : primitiveGuardedCase.integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d)
            (crSpecDen Dt a d) = some (snum, sden) := by
          simp only [crPoly, crSpecNum, crSpecDen, hcrep]; exact hspec
        obtain ⟨hsden, v, hSpecField, hrecon⟩ := primitiveGuardedCase_specialSound Dt a d snum sden hd0 hSpec
        exact cIntegrateCaseLrt_sound (Fact.out (p := GcdFFCorrect (α := α))) primitiveGuardedCase Dt a d res'
          snum sden v hd0 hSpec h0 hsden hSpecField (PrimitiveFrontierLrt.hreducedLrt Dt a d hd0) hrecon
    · simp at hguard

/-- **The base Risch solver** (`ℚ(x)` and any constant-coefficient level) — `rischIntegratePrimitive` +
`rischSoundPrimitive`, resolved from `[PrimitiveFrontierLrt α]`. Supersedes the retired `LawfulRischLevelLrt`.
Low priority so the recursive step wins at `QFunNZG` levels. -/
instance (priority := 100) instRischSolverPrimitive [CRischField α] [Fact (GcdFFCorrect (α := α))]
    [PrimitiveFrontierLrt α] : RischSolver α where
  integrate := rischIntegratePrimitive
  sound Dt a d r _ h := rischSoundPrimitive Dt a d r h

/-! ## Limited integration — the primitive the coefficient recursion calls

The polynomial-part recursion needs, at each degree, a **rational** antiderivative of a coefficient
(an element of the coefficient field itself — introducing a logarithm there would leave the field).
`integrateRational` is `integrate` restricted to log-free results. -/

/-- **Limited integration**: integrate `a/d ∈ α(t)` demanding a **rational** antiderivative (no new
logarithms) — `some (num, den)` with `D(num/den) = a/d`, or `none`. This is the primitive the
polynomial-part coefficient recursion calls: each polynomial coefficient must integrate to an element of
the coefficient field, not introduce a log. -/
def RischSolver.integrateRational [Fact (GcdFFCorrect (α := α))] [RischSolver α]
    (Dt a d : CPolyG α) : Option (CPolyG α × CPolyG α) :=
  (RischSolver.integrate Dt a d).bind fun r => if r.logs.isEmpty then some r.rational else none

/-- **Limited-integration soundness.** A successful `integrateRational` is a genuine *rational*
antiderivative: the log-free `LrtResultG ⟨(num, den), []⟩` satisfies the LRT identity, i.e. over every
splitting extension the tower derivative of `⟦num/den⟧` equals `a/d`. -/
theorem RischSolver.integrateRational_sound [Fact (GcdFFCorrect (α := α))] [RischSolver α]
    (Dt a d num den : CPolyG α) (hd0 : toPolyG d ≠ 0)
    (h : RischSolver.integrateRational Dt a d = some (num, den)) :
    IsIntegralResultLrtG Dt a d ⟨(num, den), []⟩ := by
  unfold RischSolver.integrateRational at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨r, hint, hguard⟩ := h
  split at hguard
  · rename_i hemp
    have hrat : r.rational = (num, den) := (Option.some.injEq _ _).mp hguard
    have hlogs : r.logs = [] := List.isEmpty_iff.mp hemp
    have hgen := (RischSolver.sound Dt a d r hd0 hint).1
    obtain ⟨rr, rl⟩ := r
    simp only at hrat hlogs
    subst hrat; subst hlogs
    exact hgen
  · exact absurd hguard (by simp)

/-! ## The coefficient recursion — generic-tower polynomial-part limited integration

The polynomial part `p = Σ aᵢ tⁱ ∈ α(t)` (primitive case `Dθ = η ∈ α`) integrates to `q = Σ bᵢ tⁱ` with
`D_tower(q) = p`, where `D_tower(q) = Σᵢ (D(bᵢ) + (i+1)·η·bᵢ₊₁) tⁱ`. Matching coefficients gives the
**top-down** system `D(bᵢ) = aᵢ − (i+1)·η·bᵢ₊₁`, each a limited integration of an `α`-coefficient — the
recursion into the coefficient field's solver. This is what the one-level solver skipped (it fires only for
`D(fp) = 0`). -/

/-- Top-first coefficient recursion: process `[(aₖ,k), …, (a₀,0)]` (reversed `zipIdx`), threading the
already-computed higher coefficients `acc = [bₖ₊₁, …, bₙ]`. Each step computes `bᵢ = intR(aᵢ − (i+1)·η·bᵢ₊₁)`
(`bᵢ₊₁ = acc.headD`) and prepends it. Structural recursion — induction-friendly. -/
def limIntTopFirst {α : Type*} [CField α] (η : α) (intR : α → Option α) :
    List (α × ℕ) → List α → Option (List α)
  | [], acc => some acc
  | (a, i) :: rest, acc =>
    (intR (CField.sub a (CField.mul (CField.mul (cnatCastG (i + 1)) η) (acc.headD CField.zero)))).bind
      fun bi => limIntTopFirst η intR rest (bi :: acc)

/-- **Generic-tower polynomial-part limited integration** (primitive case, `Dθ = η ∈ α`). Solves the
coefficient system `D(bᵢ) = aᵢ − (i+1)·η·bᵢ₊₁` top-down (from the leading coefficient down), each step a
limited integration `intR` of an `α`-coefficient — the recursion into the coefficient field. Returns the
antiderivative's coefficient list `[b₀, …, bₙ]`, or `none` if any coefficient fails to integrate rationally.
Parameterized by `intR : α → Option α` so the tower step plugs in `RischSolver β.integrateRational`. -/
def cLimitedIntegratePolyRatG {α : Type*} [CField α] (η : α) (intR : α → Option α)
    (p : List α) : Option (List α) :=
  limIntTopFirst η intR p.zipIdx.reverse []

/-- **The result's top part is the accumulator, and its length is `|L| + |acc|`.** Each successful step
prepends exactly one coefficient, so `q = [new…] ++ acc` — `q.drop |L| = acc`. The structural invariant the
coefficient equations rest on. -/
theorem limIntTopFirst_drop {α : Type*} [CField α] (η : α) (intR : α → Option α) :
    ∀ (L : List (α × ℕ)) (acc q : List α),
      limIntTopFirst η intR L acc = some q → q.drop L.length = acc ∧ q.length = L.length + acc.length := by
  intro L
  induction L with
  | nil => intro acc q h; simp only [limIntTopFirst, Option.some.injEq] at h; subst h; simp
  | cons hd tl ih =>
    intro acc q h
    obtain ⟨a, i⟩ := hd
    simp only [limIntTopFirst] at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨bi, _, hrec⟩ := h
    obtain ⟨hdrop, hlen⟩ := ih (bi :: acc) q hrec
    refine ⟨?_, ?_⟩
    · rw [List.length_cons, ← List.drop_drop, hdrop, List.drop_succ_cons, List.drop_zero]
    · rw [hlen, List.length_cons, List.length_cons]; omega

/-- `l.getD (n + j) = r.getD j` when `l.drop n = r`. -/
private theorem getD_of_drop {α : Type*} (l : List α) (n j : ℕ) (x : α) (r : List α)
    (h : l.drop n = r) : l.getD (n + j) x = r.getD j x := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, ← List.getElem?_drop, h]

/-- **The coefficient equations** (bridge 1). With a sound `intR` (`intR c = some b ⟹ D(b) = c`), every
accepted coefficient of `limIntTopFirst` satisfies the top-down system: at each position `m < |L|`,
`D(q[m]) = aₘ − (m+1)·η·q[m+1]`, where `(aₘ, jₘ) = L.reverse[m]` (the coefficient/index processed there).
The algorithmic heart of the polynomial-part soundness. -/
theorem limIntTopFirst_eq {α : Type*} [CField α] [CFieldSpec α] (D : α → α) (η : α) (intR : α → Option α)
    (hintR : ∀ c b, intR c = some b → CFieldSpec.toK (D b) = CFieldSpec.toK c) :
    ∀ (L : List (α × ℕ)) (acc q : List α), limIntTopFirst η intR L acc = some q →
      ∀ m, m < L.length →
        CFieldSpec.toK (D (q.getD m CField.zero))
        = CFieldSpec.toK (CField.sub (L.reverse.getD m (CField.zero, 0)).1
            (CField.mul (CField.mul (cnatCastG ((L.reverse.getD m (CField.zero, 0)).2 + 1)) η)
              (q.getD (m + 1) CField.zero))) := by
  intro L
  induction L with
  | nil => intro acc q _ m hm; simp at hm
  | cons hd tl ih =>
    intro acc q h m hm
    obtain ⟨a, i⟩ := hd
    simp only [limIntTopFirst] at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨bi, hbi, hrec⟩ := h
    obtain ⟨hdrop, _⟩ := limIntTopFirst_drop η intR tl (bi :: acc) q hrec
    rw [List.length_cons] at hm
    rcases Nat.lt_or_ge m tl.length with hm2 | hm2
    · have hrev : ((a, i) :: tl).reverse.getD m (CField.zero, 0) = tl.reverse.getD m (CField.zero, 0) := by
        rw [List.reverse_cons, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by rw [List.length_reverse]; exact hm2)]
      rw [hrev]; exact ih (bi :: acc) q hrec m hm2
    · have hmeq : m = tl.length := by omega
      subst hmeq
      have hq0 : q.getD tl.length CField.zero = bi := by
        have h0 := getD_of_drop q tl.length 0 CField.zero (bi :: acc) hdrop; simpa using h0
      have hq1 : q.getD (tl.length + 1) CField.zero = acc.headD CField.zero := by
        have h1 := getD_of_drop q tl.length 1 CField.zero (bi :: acc) hdrop
        rw [List.getD_cons_succ] at h1
        rw [h1]; cases acc <;> rfl
      have hrev : ((a, i) :: tl).reverse.getD tl.length (CField.zero, 0) = (a, i) := by
        rw [List.reverse_cons, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by rw [List.length_reverse]), List.length_reverse, Nat.sub_self]
        rfl
      rw [hq0, hq1, hrev]
      exact hintR _ _ hbi

/-- **The coefficient equations, indexed by degree** — the usable form. With `intR` sound, the antiderivative
`q` of the polynomial part `p` satisfies `D(q[m]) = p[m] − (m+1)·η·q[m+1]` for every `m < deg p`. Specializes
`limIntTopFirst_eq` to `p.zipIdx.reverse` (where the processing position equals the polynomial index). This is
the coefficient-level statement of `D_tower(q) = p`; the remaining bridges (`toK` transport +
`coeff (implicitDeriv (C η) Q) = D(coeff) + η·(i+1)·coeff(i+1)` + `Polynomial.ext`) assemble the polynomial
identity. -/
theorem cLimitedIntegratePolyRatG_eq {α : Type*} [CField α] [CFieldSpec α] (D : α → α) (η : α)
    (intR : α → Option α)
    (hintR : ∀ c b, intR c = some b → CFieldSpec.toK (D b) = CFieldSpec.toK c)
    (p q : List α) (h : cLimitedIntegratePolyRatG η intR p = some q) :
    ∀ m, m < p.length →
      CFieldSpec.toK (D (q.getD m CField.zero))
      = CFieldSpec.toK (CField.sub (p.getD m CField.zero)
          (CField.mul (CField.mul (cnatCastG (m + 1)) η) (q.getD (m + 1) CField.zero))) := by
  intro m hm
  have hlen : p.zipIdx.reverse.length = p.length := by rw [List.length_reverse, List.length_zipIdx]
  have heq := limIntTopFirst_eq D η intR hintR p.zipIdx.reverse [] q h m (by rw [hlen]; exact hm)
  rw [List.reverse_reverse] at heq
  have hpm : p[m]? = some p[m] := List.getElem?_eq_getElem hm
  have hget : p.zipIdx.getD m (CField.zero, 0) = (p.getD m CField.zero, m) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_zipIdx, hpm]
    simp [List.getD_eq_getElem?_getD, hpm]
  rw [hget] at heq
  exact heq

/-- **★ Polynomial-part soundness** (bridges 2–4). With a sound `intR` (`intR c = some b ⟹ cderiv b = c`),
the antiderivative `q` of the polynomial part `p` (primitive case, `Dθ = η`) satisfies the tower-derivative
identity `implicitDeriv (C ⟦η⟧) (toPolyG q) = toPolyG p` — i.e. `D_tower(q) = p`. Assembled coefficient-wise
(`Polynomial.ext`): `coeff m (implicitDeriv (C η) Q) = D(coeff m Q) + η·(m+1)·coeff (m+1) Q`
(`coeff_mapCoeffs` + `coeff_C_mul` + `coeff_derivative`), matched to the indexed coefficient equations
(`cLimitedIntegratePolyRatG_eq`) transported through `toK` (`toK_cderiv`, `toK_sub`, `toK_mul`,
`toK_cnatCastG`); off-degree both sides vanish. This is the primitive polynomial integration the one-level
solver skipped — now sound for **any** polynomial part whose coefficients integrate in the coefficient field. -/
theorem cLimitedIntegratePolyRatG_poly_sound {α : Type*} [CField α] [CFieldSpec α] [CDiffField α]
    [CDiffFieldSpec α] (η : α) (intR : α → Option α)
    (hintR : ∀ c b, intR c = some b → CFieldSpec.toK (CDiffField.cderiv b) = CFieldSpec.toK c)
    (p q : List α) (h : cLimitedIntegratePolyRatG η intR p = some q) :
    Differential.implicitDeriv (Polynomial.C (CFieldSpec.toK η)) (toPolyG q) = toPolyG p := by
  have hlen : q.length = p.length := by
    have hd := (limIntTopFirst_drop η intR p.zipIdx.reverse [] q h).2
    simpa [List.length_reverse, List.length_zipIdx] using hd
  have heq := cLimitedIntegratePolyRatG_eq CDiffField.cderiv η intR hintR p q h
  have htoKnat : ∀ k : ℕ, CFieldSpec.toK (cnatCastG k : α) = (k : CFieldSpec.K α) := by
    intro k
    induction k with
    | zero => rw [cnatCastG, CFieldSpec.toK_zero]; simp
    | succ n ih => rw [cnatCastG, CFieldSpec.toK_add, CFieldSpec.toK_one, ih]; push_cast; ring
  have himpl : Differential.implicitDeriv (Polynomial.C (CFieldSpec.toK η)) (toPolyG q)
      = Differential.mapCoeffs (toPolyG q) + Polynomial.C (CFieldSpec.toK η) * derivative (toPolyG q) := by
    simp [Differential.implicitDeriv, derivative']
  apply Polynomial.ext
  intro m
  rw [himpl, coeff_add, Differential.coeff_mapCoeffs, coeff_C_mul, Polynomial.coeff_derivative,
    toPolyG_coeff, toPolyG_coeff, toPolyG_coeff]
  rcases Nat.lt_or_ge m p.length with hm | hm
  · rw [← CDiffFieldSpec.toK_cderiv, heq m hm, CFieldSpec.toK_sub, CFieldSpec.toK_mul,
      CFieldSpec.toK_mul, htoKnat]
    push_cast; ring
  · have hpm : p.getD m CField.zero = CField.zero := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have hqm : q.getD m CField.zero = CField.zero := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have hqm1 : q.getD (m + 1) CField.zero = CField.zero := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [hpm, hqm, hqm1]
    simp [CFieldSpec.toK_zero]

/-! ## The tower step's recursion connector

Integrating `a/d ∈ (QFunNZG β)(t)`, the polynomial part's coefficients live in `QFunNZG β = β(s)`. Each is
integrated by recursing into `RischSolver β` — this is `intR` for `cLimitedIntegratePolyRatG`. The derivation
used is the **carrier** one (`Ds = [1]`, `s` an independent variable), which is exactly the `cderiv` that
`cLimitedIntegratePolyRatG_poly_sound` is stated against — so the recursion is consistent and sound. -/

/-- Embed a polynomial as a fraction `num/1 ∈ QFunNZG β`. -/
def qEmbedNumG {β : Type*} [CField β] [CFieldDomain β] (num : CPolyG β) : QFunNZG β :=
  ⟨(num, [CField.one]), QFunNZG.cisZeroG_one_singleton⟩

/-- **The coefficient-recursion bridge** — integrate a coefficient `c ∈ QFunNZG β = β(s)`: decompose to
`num/den ∈ CPolyG β`, recurse into `LawfulRischLevel β.integrateRational` (the **rational, base-level**
integrator — its soundness is descent-free `K`-level, exactly what the coefficient recursion needs) with the
carrier derivation `Ds = [1]`, and reassemble via `QFunNZG β`'s field division (`CField.div`, total). The
`intR` the tower step feeds to `cLimitedIntegratePolyRatG` — the recursion into the coefficient field, once. -/
def towerCoeffIntegrate {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β]
    [CFieldDomain β] [CRischField β] [CFracGcdCoreWf β] [Algebra ℚ (CFieldSpec.K β)] [LawfulRischLevel β]
    (c : QFunNZG β) : Option (QFunNZG β) :=
  (LawfulRischLevel.integrateRational [CField.one] (qnumCoeffG c) (qdenCoeffG c)).map fun bd =>
    CField.div (qEmbedNumG bd.1) (qEmbedNumG bd.2)

/-- **The tower step's polynomial-part integrator** — the proven coefficient recursion
`cLimitedIntegratePolyRatG` with the coefficient bridge `towerCoeffIntegrate` plugged in as `intR`: the
polynomial part `Σ aᵢ tⁱ` of a `(QFunNZG β)(t)` element integrates by recursing into `LawfulRischLevel β` for
each coefficient. This is the recursion the whole rebuild was for, written once — its soundness
`D_tower(q) = p` is `cLimitedIntegratePolyRatG_poly_sound` once `towerCoeffIntegrate` is shown sound
(`intR c = some b ⟹ cderiv b = c`, now on descent-free `K`-level ground). -/
def towerPolyIntegrate {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β]
    [CFieldDomain β] [CRischField β] [CFracGcdCoreWf β] [Algebra ℚ (CFieldSpec.K β)] [LawfulRischLevel β]
    (η : QFunNZG β) (p : CPolyG (QFunNZG β)) : Option (CPolyG (QFunNZG β)) :=
  cLimitedIntegratePolyRatG η towerCoeffIntegrate p

/-- **★ Coefficient-recursion soundness.** A successful `towerCoeffIntegrate c = some b` gives the
**denotational** derivative identity `toK (cderiv b) = toK c` in `RatFunc (CFieldSpec.K β)`. This is the
correct form (a *carrier* equality `cderiv b = c` is unavailable — `toK` is deliberately non-injective on
unreduced fractions) and exactly the `intR`-soundness `cLimitedIntegratePolyRatG_poly_sound` consumes.
Proof: `integrateRational` returns `(bn, bd)` with the base-level `K`-identity
`D_tower(amG bn / amG bd) = amG (qnum c) / amG (qden c)` (`integrateRational_sound`, no algebraic-closure
descent); `toK (cderiv b)` rewrites to `towerFractionFieldDerivG [1] (toK b)` (carrier
`cderiv = towerDerivQFunNZG [1]`, intertwined by `toK_cderiv`), `toK b` to `amG bn / amG bd`
(`toK_div`, `qEmbedNumG` embeds `num/1`), and `toK c` to `amG (qnum c) / amG (qden c)` (`toQFunNZG`). -/
theorem towerCoeffIntegrate_sound {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β]
    [CFieldDomain β] [CRischField β] [CFracGcdCoreWf β] [Algebra ℚ (CFieldSpec.K β)] [LawfulRischLevel β]
    (c b : QFunNZG β) (h : towerCoeffIntegrate c = some b) :
    CFieldSpec.toK (CDiffField.cderiv b) = CFieldSpec.toK c := by
  unfold towerCoeffIntegrate at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨bn, bd⟩, hint, rfl⟩ := h
  -- Base-level rational-antiderivative identity from `integrateRational_sound` (descent-free `K`-level).
  have hsound := LawfulRischLevel.integrateRational_sound [CField.one]
    (qnumCoeffG c) (qdenCoeffG c) bn bd hint
  -- `toK (cderiv X) = towerFractionFieldDerivG [1] (toK X)`: `toK_cderiv` + the carrier derivation is
  -- `towerDerivQFunNZG [1]`, whose abstract realization `deriv diffK` *is* `towerFractionFieldDerivG [1]`.
  have hcd : CFieldSpec.toK (CDiffField.cderiv (CField.div (qEmbedNumG bn) (qEmbedNumG bd)))
      = towerFractionFieldDerivG [CField.one]
          (CFieldSpec.toK (CField.div (qEmbedNumG bn) (qEmbedNumG bd))) := by
    rw [CDiffFieldSpec.toK_cderiv]
    rfl
  -- `toK (qEmbedNumG num) = amG (toPolyG num)` (the `num/1` embed).
  have htoK_embed : ∀ num : CPolyG β, CFieldSpec.toK (qEmbedNumG num) = QFunNZG.amG β (toPolyG num) := by
    intro num
    show QFunNZG.amG β (toPolyG num) / QFunNZG.amG β (toPolyG ([CField.one] : CPolyG β))
      = QFunNZG.amG β (toPolyG num)
    rw [toPolyG_one_singleton, map_one, div_one]
  -- `toK c = amG (qnum c) / amG (qden c)` (`toQFunNZG`, `qnumCoeffG`/`qdenCoeffG` are `c.1.1`/`c.1.2`).
  have htoK_c : CFieldSpec.toK c
      = QFunNZG.amG β (toPolyG (qnumCoeffG c)) / QFunNZG.amG β (toPolyG (qdenCoeffG c)) := rfl
  rw [hcd, CFieldSpec.toK_div, htoK_embed bn, htoK_embed bd, htoK_c]
  exact hsound

/-- **★ The tower step's polynomial-part soundness** — `D_tower(q) = p` for the recursion assembled from
`towerCoeffIntegrate`. The proven generic `cLimitedIntegratePolyRatG_poly_sound` fed the coefficient bridge
`towerCoeffIntegrate` (sound by `towerCoeffIntegrate_sound`): a successful `towerPolyIntegrate η p = some q`
gives the tower-derivative identity `implicitDeriv (C ⟦η⟧) (toPolyG q) = toPolyG p` over
`(RatFunc (CFieldSpec.K β))[X]` — the polynomial part `Σ aᵢ tⁱ` integrates by recursing into
`LawfulRischLevel β` for each coefficient. This is the recursion a one-level solver skips, now sound at the
next tower level, base-level-descent-free. -/
theorem towerPolyIntegrate_sound {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β]
    [CFieldDomain β] [CRischField β] [CFracGcdCoreWf β] [Algebra ℚ (CFieldSpec.K β)] [LawfulRischLevel β]
    (η : QFunNZG β) (p q : CPolyG (QFunNZG β)) (h : towerPolyIntegrate η p = some q) :
    Differential.implicitDeriv (Polynomial.C (CFieldSpec.toK η)) (toPolyG q) = toPolyG p :=
  cLimitedIntegratePolyRatG_poly_sound η towerCoeffIntegrate
    (fun c b hcb => towerCoeffIntegrate_sound c b hcb) p q h

/-- **★ The tower step's special-part field identity** (`Dθ = 1`, the `D(t)=1` log-tower case). From
`towerPolyIntegrate_sound`, the polynomial antiderivative `qp` of the poly part `fp` gives the field-level
`D_tower(⟦qp/1⟧) = ⟦fp/1⟧`: `towerFractionFieldDerivG Dt (fieldFrac qp [1]) = fieldFrac fp [1]` under
`toPolyG Dt = 1`. This is the `integrateSpecial`-soundness the tower primitive `MonomialCase` needs —
mirroring `primitive_special_identity` (same `Dt` + `toPolyG Dt = 1` shape) but for GENERAL coefficients (the
recursion), not constant ones. The bridge: `towerFractionFieldDerivG` on a poly image `amG P` is `amG (Δ P)`
(quotient rule with denominator `1`, `Δ 1 = 0`); then `Δ = implicitDeriv 1` matches `towerPolyIntegrate_sound`. -/
theorem tower_special_identity {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β]
    [CFieldDomain β] [CRischField β] [CFracGcdCoreWf β] [Algebra ℚ (CFieldSpec.K β)] [LawfulRischLevel β]
    (Dt fp qp : CPolyG (QFunNZG β)) (hDt : toPolyG Dt = 1)
    (h : towerPolyIntegrate CField.one fp = some qp) :
    towerFractionFieldDerivG Dt (fieldFrac qp [CField.one]) = fieldFrac fp [CField.one] := by
  have hpoly := towerPolyIntegrate_sound CField.one fp qp h
  rw [CFieldSpec.toK_one, Polynomial.C_1] at hpoly
  have hone : toPolyG ([CField.one] : CPolyG (QFunNZG β)) = 1 := toPolyG_one_singleton
  -- `towerFractionFieldDerivG Dt (amG (toPolyG qp)) = amG (implicitDeriv (toPolyG Dt) (toPolyG qp))`.
  have hbridge : towerFractionFieldDerivG Dt (QFunNZG.amG (QFunNZG β) (toPolyG qp))
      = QFunNZG.amG (QFunNZG β) (Differential.implicitDeriv (toPolyG Dt) (toPolyG qp)) := by
    have hd := towerFractionFieldDerivG_div Dt (toPolyG qp) 1
    simp only [map_one, div_one, one_pow, Derivation.map_one_eq_zero, map_zero, mul_zero, sub_zero,
      mul_one] at hd
    exact hd
  simp only [fieldFrac, hone, map_one, div_one]
  rw [hbridge, hDt, hpoly]

/-- **The tower primitive monomial case** — the `Dθ = 1` log-tower case with the polynomial part integrated
by the coefficient RECURSION `towerPolyIntegrate` (not the constant-coefficient `cPolyRischDEGWf` of the
one-level `primitiveGuardedCase`). Guard: `b = 0` (no special denominator) and `Dt = [1]`; the constant-`fp`
requirement is DROPPED — the recursion handles general coefficients. The reduced-part hook is the shared
residue guard (`primitiveGuardedCase.reducedCorrect`). This is the extension point: hyperexp/hypertangent
cases supply a different `integrateSpecial`. -/
def towerPrimitiveCase {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β]
    [CFieldDomain β] [CRischField β] [CFracGcdCoreWf β] [Algebra ℚ (CFieldSpec.K β)] [LawfulRischLevel β] :
    MonomialCase (QFunNZG β) where
  integrateSpecial Dt fp b _ds :=
    if cisZeroG b && cisZeroG (csubG Dt [CField.one]) then
      match towerPolyIntegrate CField.one fp with
      | none => none
      | some qp => some (qp, [CField.one])
    else none
  reducedCorrect := (primitiveGuardedCase (α := QFunNZG β)).reducedCorrect

/-- **Tower primitive special-part soundness** — the tower analogue of `primitiveGuardedCase_specialSound`.
Under the guard (`b = 0`, `Dθ = 1`) the polynomial RECURSION `towerPolyIntegrate` yields `qp` with
`D_tower(⟦qp⟧) = ⟦fp⟧` (`tower_special_identity`, GENERAL coefficients), and the reconstruction
(`canonicalReconstruction_of_charZero`, special term vanishing since `b = 0`) closes; off the guard the hook
returns `none`. -/
theorem towerPrimitiveCase_specialSound {β : Type*} [CField β] [CFieldSpec β] [CDiffField β]
    [CDiffFieldSpec β] [CFieldDomain β] [CRischField β] [CFracGcdCoreWf β] [Algebra ℚ (CFieldSpec.K β)]
    [CharZero (CFieldSpec.K β)] [LawfulRischLevel β] [Fact (GcdFFCorrect (α := QFunNZG β))]
    (Dt a d snum sden : CPolyG (QFunNZG β)) (hd0 : toPolyG d ≠ 0)
    (hhook : (towerPrimitiveCase (β := β)).integrateSpecial Dt (crPoly Dt a d) (crSpecNum Dt a d)
      (crSpecDen Dt a d) = some (snum, sden)) :
    toPolyG sden ≠ 0 ∧ ∃ v : RatFunc (CFieldSpec.K (QFunNZG β)),
      towerFractionFieldDerivG Dt (fieldFrac snum sden) = v ∧
      v + fieldFrac (crNormNum Dt a d) (crNormDen Dt a d) = fieldFrac a d := by
  simp only [towerPrimitiveCase] at hhook
  by_cases hguard : (cisZeroG (crSpecNum Dt a d) && cisZeroG (csubG Dt [CField.one])) = true
  · rw [if_pos hguard] at hhook
    rw [Bool.and_eq_true] at hguard
    obtain ⟨hb, hDt1g⟩ := hguard
    rcases hqp : towerPolyIntegrate CField.one (crPoly Dt a d) with _ | qp
    · rw [hqp] at hhook; simp at hhook
    · rw [hqp] at hhook
      simp only [Option.some.injEq, Prod.mk.injEq] at hhook
      obtain ⟨rfl, rfl⟩ := hhook
      have hDt1 : toPolyG Dt = 1 := by
        have hh := (cisZeroG_iff (csubG Dt [CField.one])).mp hDt1g
        rw [toPolyG_csubG, toPolyG_one_singleton, sub_eq_zero] at hh; exact hh
      refine ⟨?_, fieldFrac (crPoly Dt a d) [CField.one], ?_, ?_⟩
      · rw [toPolyG_one_singleton]; exact one_ne_zero
      · exact tower_special_identity Dt (crPoly Dt a d) qp hDt1 hqp
      · have hvan : fieldFrac (crSpecNum Dt a d) (crSpecDen Dt a d) = 0 := by
          simp only [fieldFrac, (cisZeroG_iff (crSpecNum Dt a d)).mp hb, map_zero, zero_div]
        have hrec := canonicalReconstruction_of_charZero
          (Fact.out (p := GcdFFCorrect (α := QFunNZG β))) Dt a d hd0
        rw [hvan, add_zero] at hrec
        exact hrec
  · rw [if_neg hguard] at hhook; simp at hhook

open Classical in
/-- **★★ The tower STEP instance** — `LawfulRischLevel (QFunNZG β)` from a below-level solver
`[LawfulRischLevel β]` and this level's reduced frontier `[PrimitiveFrontier (QFunNZG β)]`. Together with the
base (`instLawfulRischLevelPrimitive : PrimitiveFrontier ℚ ⇒ LawfulRischLevel ℚ`) this makes the Risch solver
resolve at EVERY tower depth by recursion — the whole point of the rebuild. `specialSound` is the coefficient
RECURSION (`towerPrimitiveCase_specialSound`, general polynomial parts, not just constant ones);
`reducedSound`/`caseGuardsResidues` reuse the shared guarded reduced hook (`primitiveGuardedCase.reducedCorrect`,
so the reduced frontier is exactly the base one lifted a level). -/
instance instLawfulRischLevelTower {β : Type*} [CField β] [CFieldSpec β] [CDiffField β] [CDiffFieldSpec β]
    [CFieldDomain β] [CRischField β] [CFracGcdCoreWf β] [Algebra ℚ (CFieldSpec.K β)]
    [CharZero (CFieldSpec.K β)] [LawfulRischLevel β] [Fact (GcdFFCorrect (α := QFunNZG β))]
    [PrimitiveFrontier (QFunNZG β)] : LawfulRischLevel (QFunNZG β) where
  case := towerPrimitiveCase
  candidates := fun _ _ d => defaultResidueCandidates (cdegG d + 3)
  specialSound := fun Dt a d snum sden hd0 hhook =>
    towerPrimitiveCase_specialSound Dt a d snum sden hd0 hhook
  reducedSound := by
    intro Dt a d cands nrm hd0 hcorr
    have hcn : toPolyG (crNormDen Dt a d) ≠ 0 :=
      crNormDen_ne_zero_of_charZero (Fact.out (p := GcdFFCorrect (α := QFunNZG β))) Dt a d hd0
    have hpp : (toPolyG (crNormDen Dt a d)).primPart ≠ 0 := Polynomial.primPart_ne_zero _
    refine ⟨?_, PrimitiveFrontier.hreduced Dt a d cands nrm hd0 hcorr⟩
    simp only [towerPrimitiveCase, primitiveGuardedCase] at hcorr
    split at hcorr
    · obtain rfl : nrm = redNorm Dt a d cands := (Option.some.injEq _ _).mp hcorr.symm
      exact toPolyG_cHermiteReduceTowerGWf_den_ne_zero (Fact.out (p := GcdFFCorrect (α := QFunNZG β)))
        Dt (crNormNum Dt a d) (crNormDen Dt a d) hcn hpp
    · exact absurd hcorr (by simp)
  caseGuardsResidues := primitiveGuardedCase_guardsResidues

end DeepWiki.SymbolicIntegration
