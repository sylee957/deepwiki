import DeepWiki.SymbolicIntegration.Engine.Tower.CarrierRec
import DeepWiki.SymbolicIntegration.Engine.LrtGuarded
import DeepWiki.SymbolicIntegration.Engine.Tower.RecursiveElementary

/-! # Recursive transcendental log syntax

`TowerLog` preserves the field level of every Liouville logarithm in a finite dense fraction tower. A
successor can add local ordinary or root-free LRT logs while retaining all lower evidence as inherited syntax. -/

namespace DeepWiki.SymbolicIntegration

universe u

variable {β : Type u} [CField β] [CFieldSpec.{u,u} β] [CDiffField β]

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

/-- Derivative contribution of a current-extension logarithm in an evaluation field. -/
noncomputable def localLogTerm {E : Type*} [Field E]
    [Algebra (CFieldSpec.K β) E] [Differential E] [Algebra ℚ E]
    (Dt : DensePoly β) (log : β × DensePoly β) : RatFunc E :=
  algebraMap E (RatFunc E) (algebraMap (CFieldSpec.K β) E (CFieldSpec.toK log.1)) *
    (towerDerivExt Dt (amGExt (E := E) (CPoly.toPoly log.2)) /
      amGExt (E := E) (CPoly.toPoly log.2))

/-- Derivative contribution of all current-extension logarithms. -/
noncomputable def localLogSum {E : Type*} [Field E]
    [Algebra (CFieldSpec.K β) E] [Differential E] [Algebra ℚ E]
    (Dt : DensePoly β) (logs : List (β × DensePoly β)) : RatFunc E :=
  (logs.map (localLogTerm (E := E) Dt)).sum

/-- The current-extension derivation of a represented polynomial is its base-changed monomial derivative. -/
theorem towerDerivExt_amGExt (Dt p : DensePoly β) {E : Type*} [Field E]
    [Algebra (CFieldSpec.K β) E] [Differential E] [Algebra ℚ E]
    [CDiffFieldSpec β] [DifferentialAlgebra (CFieldSpec.K β) E] :
    towerDerivExt Dt (amGExt (E := E) (CPoly.toPoly p)) =
      amGExt (E := E) (CPoly.toPoly (CPolyEngine.monomialDeriv Dt p)) := by
  unfold towerDerivExt amGExt
  rw [extendDeriv_algebraMap, CPolyEngine.toPoly_monomialDeriv, ← implicitDeriv_map]
  simp only [toPoly_list_eq]

/-- A current-extension logarithmic term is the base change of its represented logarithmic derivative. -/
theorem localLogTerm_eq_baseChange (Dt : DensePoly β) (log : β × DensePoly β)
    {E : Type*} [Field E] [Algebra (CFieldSpec.K β) E] [Differential E] [Algebra ℚ E]
    [CDiffFieldSpec β] [DifferentialAlgebra (CFieldSpec.K β) E] :
    localLogTerm (E := E) Dt log =
      ratFuncBaseChange E
        (CFrac.am β (Polynomial.C (CFieldSpec.toK log.1)) *
          (CFrac.am β (CPoly.toPoly (CPolyEngine.monomialDeriv Dt log.2)) /
            CFrac.am β (CPoly.toPoly log.2))) := by
  unfold localLogTerm
  rw [map_mul, ratFuncBaseChange_amG, ratFuncBaseChange_amG_div,
    ← towerDerivExt_amGExt]
  simp [amGExt]

/-- The current-extension log sum is the base change of the ordinary represented log sum. -/
theorem localLogSum_eq_baseChange (Dt : DensePoly β) (logs : List (β × DensePoly β))
    {E : Type*} [Field E] [Algebra (CFieldSpec.K β) E] [Differential E] [Algebra ℚ E]
    [CDiffFieldSpec β] [DifferentialAlgebra (CFieldSpec.K β) E] :
    localLogSum (E := E) Dt logs = ratFuncBaseChange E (logResidueSumP Dt logs) := by
  induction logs with
  | nil => simp [localLogSum, logResidueSumP]
  | cons log logs ih =>
    simp only [localLogSum, logResidueSumP, List.map_cons, List.sum_cons, map_add]
    rw [localLogTerm_eq_baseChange]
    have htail : (logs.map (localLogTerm (E := E) Dt)).sum =
        ratFuncBaseChange E
          (logs.map fun cv =>
            CFrac.am β (Polynomial.C (CFieldSpec.toK cv.1)) *
              (CFrac.am β (CPoly.toPoly (CPolyEngine.monomialDeriv Dt cv.2)) /
                CFrac.am β (CPoly.toPoly cv.2))).sum := by
      simpa [localLogSum, logResidueSumP] using ih
    rw [htail]

/-- Coherent differential embeddings of every field through depth `N` into one final evaluation field. -/
structure TowerLog.EvaluationMaps (N : ℕ) (E : Type*) [Field E] [Differential E] where
  /-- The selected algebra structure at each tower depth. -/
  algebra : ∀ n, n ≤ N → Algebra (CFieldSpec.K (DenseFracTower n)) E
  /-- Each selected algebra embedding commutes with the selected derivations. -/
  differentialAlgebra : ∀ n (hn : n ≤ N),
    letI : Algebra (CFieldSpec.K (DenseFracTower n)) E := algebra n hn
    DifferentialAlgebra (CFieldSpec.K (DenseFracTower n)) E
  /-- Consecutive embeddings agree with the canonical rational-function inclusion. -/
  coherent : ∀ n (hn : n + 1 ≤ N),
    letI : Algebra (CFieldSpec.K (DenseFracTower n)) E := algebra n (Nat.le_trans (Nat.le_succ n) hn)
    letI : Algebra (CFieldSpec.K (DenseFracTower (n + 1))) E := algebra (n + 1) hn
    (algebraMap (CFieldSpec.K (DenseFracTower (n + 1))) E).comp (denseFracTowerKStep n) =
      algebraMap (CFieldSpec.K (DenseFracTower n)) E

/-- The ring homomorphism induced by a coherent evaluation algebra at a selected depth. -/
noncomputable def TowerLog.EvaluationMaps.map {N : ℕ} {E : Type*} [Field E] [Differential E]
    (maps : TowerLog.EvaluationMaps N E) (n : ℕ) (hn : n ≤ N) :
    CFieldSpec.K (DenseFracTower n) →+* E :=
  @algebraMap (CFieldSpec.K (DenseFracTower n)) E _ _ (maps.algebra n hn)

/-- Evaluate logs created by the extension over `Kₙ` in a target field with maps through `Kₙ`. -/
noncomputable def TowerLog.denote {n N : ℕ} {E : Type*} [Field E] [Differential E] [Algebra ℚ E]
    (maps : TowerLog.EvaluationMaps N E) (hn : n ≤ N) : TowerLog (n + 1) → RatFunc E := by
  intro log
  letI : Algebra (CFieldSpec.K (DenseFracTower n)) E :=
    maps.algebra n hn
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

/-- A recursive tower result differentiates to its input after all local and inherited logs are evaluated. -/
def IsTowerIntegralResult {n : ℕ} (Dt anum aden : DensePoly (DenseFracTower n))
    (res : TowerIntegralResult n) : Prop :=
  ∀ (E : Type) [Field E] [Differential E] [Algebra ℚ E] [IsAlgClosed E]
    (maps : TowerLog.EvaluationMaps n E),
    letI : Algebra (CFieldSpec.K (DenseFracTower n)) E := maps.algebra n (Nat.le_refl n)
    letI : DifferentialAlgebra (CFieldSpec.K (DenseFracTower n)) E :=
      maps.differentialAlgebra n (Nat.le_refl n)
    towerDerivExt Dt
        (amGExt (E := E) (CPoly.toPoly (CFrac.num res.rational)) /
          amGExt (E := E) (CPoly.toPoly (CFrac.den res.rational))) +
      TowerLog.denoteSum maps (Nat.le_refl n) res.logs =
      amGExt (E := E) (CPoly.toPoly anum) /
        amGExt (E := E) (CPoly.toPoly aden)

/-- Recursive ordinary logs evaluate to the corresponding current-level log sum. -/
theorem towerLog_denoteSum_ordinary {n N : ℕ} {E : Type*}
    [Field E] [Differential E] [Algebra ℚ E] (maps : TowerLog.EvaluationMaps N E)
    (hn : n ≤ N) (derivative : DensePoly (DenseFracTower n))
    (logs : List (DenseFracTower n × DensePoly (DenseFracTower n))) :
    TowerLog.denoteSum maps hn (logs.map fun log => TowerLog.ordinary derivative log.1 log.2) =
      letI : Algebra (CFieldSpec.K (DenseFracTower n)) E := maps.algebra n hn
      localLogSum (E := E) derivative logs := by
  letI : Algebra (CFieldSpec.K (DenseFracTower n)) E := maps.algebra n hn
  induction logs with
  | nil => rfl
  | cons log logs ih =>
    simp only [TowerLog.denoteSum, localLogSum,
      List.map_cons, List.sum_cons]
    change TowerLog.denote maps hn (TowerLog.ordinary derivative log.1 log.2) +
        TowerLog.denoteSum maps hn (logs.map fun log => TowerLog.ordinary derivative log.1 log.2) =
      localLogTerm (E := E) derivative log + localLogSum (E := E) derivative logs
    rw [ih]
    have hhead : TowerLog.denote maps hn (TowerLog.ordinary derivative log.1 log.2) =
        localLogTerm (E := E) derivative log := by
      unfold TowerLog.denote
      cases n <;> rfl
    rw [hhead]

/-- The recursive evaluation of an ordinary one-level result is its ordinary local log sum. -/
theorem TowerIntegralResult.denoteSum_ofIntegralResult {n N : ℕ} {E : Type*}
    [Field E] [Differential E] [Algebra ℚ E] (maps : TowerLog.EvaluationMaps N E)
    (hn : n ≤ N) (derivative : DensePoly (DenseFracTower n))
    (res : IntegralResult (DenseFracTower n)) :
    TowerLog.denoteSum maps hn (TowerIntegralResult.ofIntegralResult derivative res).logs =
      letI : Algebra (CFieldSpec.K (DenseFracTower n)) E := maps.algebra n hn
      localLogSum (E := E) derivative res.logs := by
  exact towerLog_denoteSum_ordinary maps hn derivative res.logs

/-- Recursive root-free logs evaluate to the corresponding current-level LRT sum. -/
theorem towerLog_denoteSum_lrt {n N : ℕ} {E : Type*}
    [Field E] [Differential E] [Algebra ℚ E] (maps : TowerLog.EvaluationMaps N E)
    (hn : n ≤ N) (derivative : DensePoly (DenseFracTower n))
    (logs : List (DensePoly (DenseFracTower n) × List (DensePoly (DenseFracTower n)))) :
    TowerLog.denoteSum maps hn (logs.map fun log => TowerLog.lrt derivative log.1 log.2) =
      letI : Algebra (CFieldSpec.K (DenseFracTower n)) E := maps.algebra n hn
      logResidueSumLrt (E := E) derivative logs := by
  letI : Algebra (CFieldSpec.K (DenseFracTower n)) E := maps.algebra n hn
  induction logs with
  | nil => rfl
  | cons log logs ih =>
    simp only [TowerLog.denoteSum, logResidueSumLrtG_cons, List.map_cons, List.sum_cons]
    change TowerLog.denote maps hn (TowerLog.lrt derivative log.1 log.2) +
        TowerLog.denoteSum maps hn (logs.map fun log => TowerLog.lrt derivative log.1 log.2) =
      logResidueTermLrt (E := E) derivative log + logResidueSumLrt (E := E) derivative logs
    rw [ih]
    have hhead : TowerLog.denote maps hn (TowerLog.lrt derivative log.1 log.2) =
        logResidueTermLrt (E := E) derivative log := by
      unfold TowerLog.denote
      cases n <;> rfl
    rw [hhead]

/-- The recursive evaluation of a root-free one-level result is its LRT log sum. -/
theorem TowerIntegralResult.denoteSum_ofLrtResult {n N : ℕ} {E : Type*}
    [Field E] [Differential E] [Algebra ℚ E] (maps : TowerLog.EvaluationMaps N E)
    (hn : n ≤ N) (derivative : DensePoly (DenseFracTower n))
    (res : LrtResult (DenseFracTower n)) :
    TowerLog.denoteSum maps hn (TowerIntegralResult.ofLrtResult derivative res).logs =
      letI : Algebra (CFieldSpec.K (DenseFracTower n)) E := maps.algebra n hn
      logResidueSumLrt (E := E) derivative res.logs := by
  exact towerLog_denoteSum_lrt maps hn derivative res.logs

/-- An ordinary one-level certificate transports to the recursive tower-result invariant. -/
theorem isTowerIntegralResult_ofIntegralResult {n : ℕ}
    [CFieldDomain (DenseFracTower n) DensePoly]
    (Dt anum aden : DensePoly (DenseFracTower n)) (res : IntegralResult (DenseFracTower n))
    (hres : IsIntegralResultP Dt anum aden res) :
    IsTowerIntegralResult Dt anum aden (TowerIntegralResult.ofIntegralResult Dt res) := by
  intro E _ _ _ _ maps
  letI : Algebra (CFieldSpec.K (DenseFracTower n)) E := maps.algebra n (Nat.le_refl n)
  letI : DifferentialAlgebra (CFieldSpec.K (DenseFracTower n)) E :=
    maps.differentialAlgebra n (Nat.le_refl n)
  have hderiv :
      ratFuncBaseChange E
          (towerFractionFieldDerivP Dt (fieldFracP res.rational.1 res.rational.2)) =
        towerDerivExt Dt
          (amGExt (E := E) (CPoly.toPoly res.rational.1) /
            amGExt (E := E) (CPoly.toPoly res.rational.2)) := by
    simpa only [towerFractionFieldDerivP, towerFractionFieldDeriv, fieldFracP, toPoly_list_eq] using
      (ratFuncBaseChange_towerFractionFieldDerivG (E := E) Dt
        (CPoly.toPoly res.rational.1) (CPoly.toPoly res.rational.2))
  have hrational :
      amGExt (E := E)
          (CPoly.toPoly (CFrac.num (TowerIntegralResult.ofIntegralResult Dt res).rational)) /
        amGExt (E := E)
          (CPoly.toPoly (CFrac.den (TowerIntegralResult.ofIntegralResult Dt res).rational)) =
        amGExt (E := E) (CPoly.toPoly res.rational.1) /
          amGExt (E := E) (CPoly.toPoly res.rational.2) := by
    calc
      _ = ratFuncBaseChange E
          (CFieldSpec.toK (TowerIntegralResult.ofIntegralResult Dt res).rational) := by
        symm
        rw [toK_denseFrac_eq_fieldFrac, fieldFracP, ratFuncBaseChange_amG_div]
      _ = ratFuncBaseChange E (fieldFracP res.rational.1 res.rational.2) := by
        simp [TowerIntegralResult.ofIntegralResult, fieldFracP, CFieldSpec.toK_div,
          CFrac.toK_ofPoly]
      _ = _ := by
        rw [fieldFracP, ratFuncBaseChange_amG_div]
  have hbase := congrArg (ratFuncBaseChange E) hres
  rw [map_add, hderiv, ← localLogSum_eq_baseChange,
    ratFuncBaseChange_amG_div] at hbase
  rw [hrational, TowerIntegralResult.denoteSum_ofIntegralResult maps (Nat.le_refl n) Dt res]
  exact hbase

/-- A root-free one-level certificate transports to the recursive tower-result invariant. -/
theorem isTowerIntegralResult_ofLrtResult {n : ℕ}
    [CFieldDomain (DenseFracTower n) DensePoly]
    (Dt anum aden : DensePoly (DenseFracTower n)) (res : LrtResult (DenseFracTower n))
    (hres : IsIntegralResultLrt Dt anum aden res) :
    IsTowerIntegralResult Dt anum aden (TowerIntegralResult.ofLrtResult Dt res) := by
  intro E _ _ _ _ maps
  letI : Algebra (CFieldSpec.K (DenseFracTower n)) E := maps.algebra n (Nat.le_refl n)
  letI : DifferentialAlgebra (CFieldSpec.K (DenseFracTower n)) E :=
    maps.differentialAlgebra n (Nat.le_refl n)
  have hrational :
      amGExt (E := E)
          (CPoly.toPoly (CFrac.num (TowerIntegralResult.ofLrtResult Dt res).rational)) /
        amGExt (E := E)
          (CPoly.toPoly (CFrac.den (TowerIntegralResult.ofLrtResult Dt res).rational)) =
        amGExt (E := E) (CPoly.toPoly res.rational.1) /
          amGExt (E := E) (CPoly.toPoly res.rational.2) := by
    calc
      _ = ratFuncBaseChange E
          (CFieldSpec.toK (TowerIntegralResult.ofLrtResult Dt res).rational) := by
        symm
        rw [toK_denseFrac_eq_fieldFrac, fieldFracP, ratFuncBaseChange_amG_div]
      _ = ratFuncBaseChange E (fieldFracP res.rational.1 res.rational.2) := by
        simp [TowerIntegralResult.ofLrtResult, fieldFracP, CFieldSpec.toK_div,
          CFrac.toK_ofPoly]
      _ = _ := by
        rw [fieldFracP, ratFuncBaseChange_amG_div]
  rw [hrational, TowerIntegralResult.denoteSum_ofLrtResult maps (Nat.le_refl n) Dt res]
  simpa only [toPoly_list_eq] using hres E

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
