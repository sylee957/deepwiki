import DeepWiki.SymbolicIntegration.Engine.Tower.CarrierRec
import DeepWiki.SymbolicIntegration.Engine.LrtGuarded

/-! # Recursive transcendental log syntax

`TowerLog` preserves the field level of every Liouville logarithm in a finite dense fraction tower. A
successor can add local ordinary or root-free LRT logs while retaining all lower evidence as inherited syntax. -/

namespace DeepWiki.SymbolicIntegration

/-- A Liouville logarithm living in the denotation field at a finite dense-tower depth. -/
inductive TowerLog : (n : ℕ) → Type
  /-- An ordinary logarithm created by the extension from depth `n` to depth `n + 1`. -/
  | ordinary (coefficient : DenseFracTower n) (argument : DensePoly (DenseFracTower n)) :
      TowerLog (n + 1)
  /-- A root-free LRT family created by the extension from depth `n` to depth `n + 1`. -/
  | lrt (residue : DensePoly (DenseFracTower n))
      (argument : List (DensePoly (DenseFracTower n))) : TowerLog (n + 1)
  /-- A logarithm inherited unchanged from the preceding tower depth. -/
  | inherited : TowerLog n → TowerLog (n + 1)

/-- The syntactic genuine-log condition appropriate to a recursive tower log. -/
def TowerLog.IsGenuine : ∀ {n : ℕ}, TowerLog n → Prop
  | _, .ordinary coefficient argument =>
      CFieldSpec.toK (CDiffField.cderiv coefficient) = 0 ∧ CPoly.toPoly argument ≠ 0
  | _, .lrt residue _ =>
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
noncomputable def TowerIntegralResult.ofIntegralResult {n : ℕ} (res : IntegralResult (DenseFracTower n)) :
    TowerIntegralResult n where
  rational := CField.div (CFrac.ofPoly res.rational.1) (CFrac.ofPoly res.rational.2)
  logs := res.logs.map fun log => .ordinary log.1 log.2

/-- Embed a root-free result as local LRT logs at the successor tower depth. -/
noncomputable def TowerIntegralResult.ofLrtResult {n : ℕ} (res : LrtResult (DenseFracTower n)) :
    TowerIntegralResult n where
  rational := CField.div (CFrac.ofPoly res.rational.1) (CFrac.ofPoly res.rational.2)
  logs := res.logs.map fun log => .lrt log.1 log.2

/-- Lift a log list unchanged through one new tower extension. -/
def TowerLog.inheritAll {n : ℕ} (logs : List (TowerLog n)) : List (TowerLog (n + 1)) :=
  logs.map .inherited

/-- Genuine ordinary one-level logs remain genuine in the recursive syntax. -/
theorem TowerIntegralResult.logsGenuine_ofIntegralResult {n : ℕ}
    (res : IntegralResult (DenseFracTower n))
    (hconstants : ∀ log ∈ res.logs,
      CFieldSpec.toK (CDiffField.cderiv log.1) = 0)
    (hargs : ∀ log ∈ res.logs, CPoly.toPoly log.2 ≠ 0) :
    (TowerIntegralResult.ofIntegralResult res).LogsGenuine := by
  intro log hlog
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hlog
  exact ⟨hconstants source hsource, hargs source hsource⟩

/-- Genuine root-free one-level logs remain genuine in the recursive syntax. -/
theorem TowerIntegralResult.logsGenuine_ofLrtResult {n : ℕ}
    (res : LrtResult (DenseFracTower n)) (hres : AllResiduesConstantLrt res) :
    (TowerIntegralResult.ofLrtResult res).LogsGenuine := by
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
