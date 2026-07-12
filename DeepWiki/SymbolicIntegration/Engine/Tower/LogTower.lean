import DeepWiki.SymbolicIntegration.Engine.Tower.CarrierRec
import DeepWiki.SymbolicIntegration.Engine.LrtGuarded
import DeepWiki.SymbolicIntegration.Engine.Tower.TranscendentalResult

/-! # Recursive transcendental log syntax

`TowerLog` preserves the field level of every Liouville logarithm in a finite dense fraction tower. A
successor can add local ordinary or root-free LRT logs while retaining all lower evidence as inherited syntax. -/

namespace DeepWiki.SymbolicIntegration

/-- A Liouville logarithm living in the denotation field at a finite dense-tower depth. -/
inductive TowerLog : (n : ℕ) → Type
  /-- An ordinary logarithm created by the extension from depth `n` to depth `n + 1`. -/
  | ordinary (derivative : DensePoly (DenseFracTower n))
      (coefficient : DenseFracTower n) (argument : DensePoly (DenseFracTower n)) :
      TowerLog (n + 1)
  /-- A root-free LRT family created by the extension from depth `n` to depth `n + 1`. -/
  | lrt (derivative : DensePoly (DenseFracTower n)) (residue : DensePoly (DenseFracTower n))
      (argument : List (DensePoly (DenseFracTower n))) : TowerLog (n + 1)
  /-- A logarithm inherited unchanged from the preceding tower depth. -/
  | inherited : TowerLog n → TowerLog (n + 1)

/-- The syntactic genuine-log condition appropriate to a recursive tower log. -/
def TowerLog.IsGenuine : ∀ {n : ℕ}, TowerLog n → Prop
  | _, .ordinary _ coefficient argument =>
      CFieldSpec.toK (CDiffField.cderiv coefficient) = 0 ∧ CPoly.toPoly argument ≠ 0
  | _, .lrt _ residue _ =>
      CPolyEngine.cisZero (CPolyEngine.mapDeriv (CPolyEngine.cmonic residue)) = true
  | _, .inherited log => log.IsGenuine

/-- A finite tower result has a rational part at the new depth and logs at their original depths. -/
structure TowerIntegralResult (n : ℕ) where
  /-- Rational antiderivative part in the successor fraction field. -/
  rational : DenseFrac (DenseFracTower n)
  /-- Local and inherited logarithms, each retaining its source depth. -/
  logs : List (TowerLog (n + 1))

/-- All recursive logs recorded by a tower result are genuine. -/
def TowerIntegralResult.LogsGenuine {n : ℕ} (res : TowerIntegralResult n) : Prop :=
  ∀ log ∈ res.logs, log.IsGenuine

/-- Embed an ordinary result as local logs at the successor tower depth. -/
noncomputable def TowerIntegralResult.ofIntegralResult {n : ℕ} (derivative : DensePoly (DenseFracTower n))
    (res : IntegralResult (DenseFracTower n)) :
    TowerIntegralResult n where
  rational := CField.div (CFrac.ofPoly res.rational.1) (CFrac.ofPoly res.rational.2)
  logs := res.logs.map fun log => .ordinary derivative log.1 log.2

/-- Embed a root-free result as local LRT logs at the successor tower depth. -/
noncomputable def TowerIntegralResult.ofLrtResult {n : ℕ} (derivative : DensePoly (DenseFracTower n))
    (res : LrtResult (DenseFracTower n)) :
    TowerIntegralResult n where
  rational := CField.div (CFrac.ofPoly res.rational.1) (CFrac.ofPoly res.rational.2)
  logs := res.logs.map fun log => .lrt derivative log.1 log.2

/-- Lift a log list unchanged through one new tower extension. -/
def TowerLog.inheritAll {n : ℕ} (logs : List (TowerLog n)) : List (TowerLog (n + 1)) :=
  logs.map .inherited

/-- Explicit embeddings of every field through depth `N` into one final evaluation field. -/
structure TowerLog.EvaluationMaps (N : ℕ) (E : Type*) [Field E] where
  /-- Embed the denotation field at a selected depth into `E`. -/
  map : ∀ n, n ≤ N → CFieldSpec.K (DenseFracTower n) →+* E

/-- Evaluate logs created by the extension over `Kₙ` in a target field with maps through `Kₙ`. -/
noncomputable def TowerLog.denote {n N : ℕ} {E : Type*} [Field E] [Differential E] [Algebra ℚ E]
    (maps : TowerLog.EvaluationMaps N E) (hn : n ≤ N) : TowerLog (n + 1) → RatFunc E := by
  intro log
  letI : Algebra (CFieldSpec.K (DenseFracTower n)) E :=
    RingHom.toAlgebra (maps.map n hn)
  cases log with
  | ordinary derivative coefficient argument =>
    exact localLogTerm (E := E) derivative (coefficient, argument)
  | lrt derivative residue argument =>
    exact logResidueTermLrt (E := E) derivative (residue, argument)
  | inherited log =>
    cases n with
    | zero => exact nomatch log
    | succ n =>
      exact TowerLog.denote maps (Nat.le_trans (Nat.le_succ n) hn) log

/-- Sum recursive-log denotations in a final evaluation field. -/
noncomputable def TowerLog.denoteSum {n N : ℕ} {E : Type*} [Field E] [Differential E] [Algebra ℚ E]
    (maps : TowerLog.EvaluationMaps N E) (hn : n ≤ N) (logs : List (TowerLog (n + 1))) : RatFunc E :=
  (logs.map (TowerLog.denote maps hn)).sum

/-- Genuine ordinary one-level logs remain genuine in the recursive syntax. -/
theorem TowerIntegralResult.logsGenuine_ofIntegralResult {n : ℕ}
    (derivative : DensePoly (DenseFracTower n)) (res : IntegralResult (DenseFracTower n))
    (hconstants : ∀ log ∈ res.logs,
      CFieldSpec.toK (CDiffField.cderiv log.1) = 0)
    (hargs : ∀ log ∈ res.logs, CPoly.toPoly log.2 ≠ 0) :
    (TowerIntegralResult.ofIntegralResult derivative res).LogsGenuine := by
  intro log hlog
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hlog
  exact ⟨hconstants source hsource, hargs source hsource⟩

/-- Genuine root-free one-level logs remain genuine in the recursive syntax. -/
theorem TowerIntegralResult.logsGenuine_ofLrtResult {n : ℕ}
    (derivative : DensePoly (DenseFracTower n)) (res : LrtResult (DenseFracTower n))
    (hres : AllResiduesConstantLrt res) :
    (TowerIntegralResult.ofLrtResult derivative res).LogsGenuine := by
  intro log hlog
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hlog
  exact (List.all_eq_true.mp hres) source hsource

/-- Inheriting a genuine log list preserves its genuine-log condition. -/
theorem towerLog_inheritAll_genuine {n : ℕ} (logs : List (TowerLog n))
    (hlogs : ∀ log ∈ logs, log.IsGenuine) :
    ∀ log ∈ TowerLog.inheritAll logs, log.IsGenuine := by
  intro log hlog
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hlog
  exact hlogs source hsource

end DeepWiki.SymbolicIntegration
