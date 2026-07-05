import DeepWiki.SymbolicIntegration.Computable.RischTowerLrt

/-! # `RischSolver` — the recursive Risch tower solver (base + step)

The genuine, root-free Risch integrator, structured **recursively** over the monomial tower. Where
`LawfulRischLevelLrt` is a *one-level* solver (it handles the reduced part via LRT and the special part
only in the constant-coefficient regime), `RischSolver` is the recursion: integrating `a/d ∈ α(t)`
decomposes into the polynomial part, the reduced part (root-free LRT — reused verbatim), and the special
part, and the **polynomial part's coefficient integration recurses into `RischSolver` for the coefficient
field**. That coefficient recursion is the heart of the transcendental algorithm (Bronstein §5.3–5.9) and
is exactly what the one-level solver was missing — its `integrateSpecial` fires only when the polynomial
part has constant coefficients (`D(fp) = 0`).

- **`integrate`** — integrate `a/d ∈ α(t)` (monomial derivative `Dt`) to a root-free `LrtResultG`, or `none`.
- **`sound`** — a successful run is a **genuine** antiderivative (`IsGenuineIntegralResultLrtG`: the LRT
  identity + all residues constant).

The **base** instance reuses the genuine one-level LRT solver (`integrateLrt`/`soundLrt`) — correct for the
constant-coefficient regime (`ℚ(x)` and any level whose polynomial part is constant). The **step**
(`RischSolverStep.lean`) adds the coefficient recursion `[RischSolver β] → RischSolver (QFunNZG β)` via the
generic-tower limited integration. See `docs/recursive-risch-tower.md`. -/

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

/-- **The base Risch solver** — the genuine one-level LRT solver *is* a Risch solver: it handles the reduced
part (root-free LRT) and the special part in the constant-coefficient regime, which is complete at the tower
base (`ℚ(x)`, where the polynomial-part coefficients are constants). Reuses `integrateLrt` / `soundLrt`
verbatim; the coefficient recursion is added by the step instance. Low priority so the step wins at
`QFunNZG` levels. -/
instance (priority := 100) instRischSolverOfLawfulLrt [Fact (GcdFFCorrect (α := α))]
    [LawfulRischLevelLrt α] : RischSolver α where
  integrate := LawfulRischLevelLrt.integrateLrt
  sound Dt a d r _ h := LawfulRischLevelLrt.soundLrt Dt a d r h

/-- The base solver's `integrate` is exactly `integrateLrt` (the reduced part is genuine LRT, so this
transports the guard + soundness of the one-level solver). -/
theorem RischSolver.integrate_base_eq [Fact (GcdFFCorrect (α := α))] [LawfulRischLevelLrt α]
    (Dt a d : CPolyG α) :
    (instRischSolverOfLawfulLrt).integrate Dt a d = LawfulRischLevelLrt.integrateLrt Dt a d := rfl

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
theorem limIntTopFirst_eq {α : Type*} [CField α] (D : α → α) (η : α) (intR : α → Option α)
    (hintR : ∀ c b, intR c = some b → D b = c) :
    ∀ (L : List (α × ℕ)) (acc q : List α), limIntTopFirst η intR L acc = some q →
      ∀ m, m < L.length →
        D (q.getD m CField.zero)
        = CField.sub (L.reverse.getD m (CField.zero, 0)).1
            (CField.mul (CField.mul (cnatCastG ((L.reverse.getD m (CField.zero, 0)).2 + 1)) η)
              (q.getD (m + 1) CField.zero)) := by
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
theorem cLimitedIntegratePolyRatG_eq {α : Type*} [CField α] (D : α → α) (η : α) (intR : α → Option α)
    (hintR : ∀ c b, intR c = some b → D b = c)
    (p q : List α) (h : cLimitedIntegratePolyRatG η intR p = some q) :
    ∀ m, m < p.length →
      D (q.getD m CField.zero)
      = CField.sub (p.getD m CField.zero)
          (CField.mul (CField.mul (cnatCastG (m + 1)) η) (q.getD (m + 1) CField.zero)) := by
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

end DeepWiki.SymbolicIntegration
