import DeepWiki.SymbolicIntegration.Computable.RischTowerPrimitive
import DeepWiki.SymbolicIntegration.Computable.Tower.CarrierRec

/-! # The generic polynomial-part coefficient recursion (the reusable tower-step core)

The **coefficient recursion** shared by every tower step: integrating `a/d ∈ (QFunNZG β)(t)`, the polynomial
part's coefficients live in `QFunNZG β = β(s)`, and each is integrated by recursing into the coefficient field's
solver — the heart of the transcendental algorithm (Bronstein §5.3–5.9), and exactly what a one-level solver
misses (its special-part hook fires only when the polynomial part has constant coefficients, `D(fp) = 0`).

- **`cLimitedIntegratePolyRatG`** — the generic top-down coefficient recursion `D(bᵢ) = aᵢ − (i+1)·η·bᵢ₊₁`,
  with soundness `cLimitedIntegratePolyRatG_poly_sound` (`D_tower(q) = p`, denotational form) for **any** sound
  coefficient integrator `intR`. Result-type-agnostic, so both the rational- and LRT-residue tower steps reuse
  it — each plugs in its own `intR` (`towerCoeffIntegrateLrt` in `RischSolverTowerLrt.lean`).
- **`qEmbedNumG`** — the `num/1 ∈ QFunNZG β` embedding used to reassemble a recursed coefficient.

The recursive tower solver is `LawfulRischLevelLrt` (`RischTowerLrt.lean` / `RischSolverTowerLrt.lean`). See
`docs/recursive-lrt-typeclass.md`. -/

namespace DeepWiki.SymbolicIntegration

open Compute CPolyG QFunNZG Polynomial
open scoped Differential

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
Parameterized by `intR : α → Option α` so each tower step plugs in its coefficient-field integrator (the LRT
step's `towerCoeffIntegrateLrt`). -/
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

/-! ## The recursion connector

The `num/1` embedding used to reassemble a coefficient after recursing into the coefficient field's solver
(the carrier derivation `Ds = [1]`, `s` an independent variable, is the `cderiv` that
`cLimitedIntegratePolyRatG_poly_sound` is stated against, so the recursion is consistent and sound). -/

/-- Embed a polynomial as a fraction `num/1 ∈ QFunNZG β`. -/
def qEmbedNumG {β : Type*} [CField β] [CFieldDomain β] (num : CPolyG β) : QFunNZG β :=
  ⟨(num, [CField.one]), QFunNZG.cisZeroG_one_singleton⟩

end DeepWiki.SymbolicIntegration
