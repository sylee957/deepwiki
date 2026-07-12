import DeepWiki.SymbolicIntegration.Engine.Tower.CarrierRec
import DeepWiki.SymbolicIntegration.Engine.LrtGuarded
import DeepWiki.SymbolicIntegration.Engine.Tower.RecursiveElementary
import DeepWiki.SymbolicIntegration.Engine.Tower.Realization
import DeepWiki.SymbolicIntegration.Engine.Tower.Stage

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

/-- Retain all lower-depth logs while adding a successor's local rational and logarithmic result. -/
def TowerIntegralResult.appendInherited {n : ℕ}
    (localResult : TowerIntegralResult (n + 1)) (lower : TowerIntegralResult n) :
    TowerIntegralResult (n + 1) where
  rational := localResult.rational
  logs := localResult.logs ++ TowerLog.inheritAll lower.logs

/-- Add two tower antiderivative pieces at the same extension depth. -/
noncomputable def TowerIntegralResult.add {n : ℕ} (left right : TowerIntegralResult n) :
    TowerIntegralResult n where
  rational := CCommRing.add left.rational right.rational
  logs := left.logs ++ right.logs

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

/-- Restrict coherent evaluation maps to an initial finite prefix of the tower. -/
noncomputable def TowerLog.EvaluationMaps.restrict {M N : ℕ} {E : Type*}
    [Field E] [Differential E] (maps : TowerLog.EvaluationMaps N E) (hMN : M ≤ N) :
    TowerLog.EvaluationMaps M E where
  algebra n hn := maps.algebra n (Nat.le_trans hn hMN)
  differentialAlgebra n hn := maps.differentialAlgebra n (Nat.le_trans hn hMN)
  coherent n hn := maps.coherent n (Nat.le_trans hn hMN)

/-- Evaluate the rational part of a tower result in a selected final evaluation field. -/
noncomputable def TowerIntegralResult.rationalDenote {n N : ℕ} {E : Type*}
    [Field E] [Differential E] [Algebra ℚ E] (maps : TowerLog.EvaluationMaps N E)
    (hn : n ≤ N) (res : TowerIntegralResult n) : RatFunc E := by
  letI : Algebra (CFieldSpec.K (DenseFracTower n)) E := maps.algebra n hn
  exact amGExt (E := E) (CPoly.toPoly (CFrac.num res.rational)) /
    amGExt (E := E) (CPoly.toPoly (CFrac.den res.rational))

/-- The rational evaluation is the base change of the represented fraction's denotation. -/
theorem TowerIntegralResult.rationalDenote_eq_baseChange {n N : ℕ} {E : Type*}
    [Field E] [Differential E] [Algebra ℚ E] (maps : TowerLog.EvaluationMaps N E)
    (hn : n ≤ N) (res : TowerIntegralResult n) :
    res.rationalDenote maps hn =
      letI : Algebra (CFieldSpec.K (DenseFracTower n)) E := maps.algebra n hn
      ratFuncBaseChange E (CFieldSpec.toK res.rational) := by
  letI : Algebra (CFieldSpec.K (DenseFracTower n)) E := maps.algebra n hn
  unfold TowerIntegralResult.rationalDenote
  symm
  rw [toK_denseFrac_eq_fieldFrac, fieldFracP, ratFuncBaseChange_amG_div]

/-- Restricting maps does not change the rational denotation of a tower result. -/
theorem TowerIntegralResult.rationalDenote_restrict {n M N : ℕ} {E : Type*}
    [Field E] [Differential E] [Algebra ℚ E] (maps : TowerLog.EvaluationMaps N E)
    (hMN : M ≤ N) (hn : n ≤ M) (res : TowerIntegralResult n) :
    res.rationalDenote (maps.restrict hMN) hn =
      res.rationalDenote maps (Nat.le_trans hn hMN) := by
  unfold TowerIntegralResult.rationalDenote TowerLog.EvaluationMaps.restrict
  rfl

/-- Rational evaluation distributes over composition of tower antiderivative pieces. -/
theorem TowerIntegralResult.rationalDenote_add {n N : ℕ} {E : Type*}
    [Field E] [Differential E] [Algebra ℚ E] (maps : TowerLog.EvaluationMaps N E)
    (hn : n ≤ N) (left right : TowerIntegralResult n) :
    (left.add right).rationalDenote maps hn =
      left.rationalDenote maps hn + right.rationalDenote maps hn := by
  letI : Algebra (CFieldSpec.K (DenseFracTower n)) E := maps.algebra n hn
  rw [TowerIntegralResult.rationalDenote_eq_baseChange,
    TowerIntegralResult.rationalDenote_eq_baseChange,
    TowerIntegralResult.rationalDenote_eq_baseChange]
  change ratFuncBaseChange E
      (CFieldSpec.toK (CCommRing.add left.rational right.rational)) = _
  rw [CFieldSpec.toK_add, map_add]

/-- Evaluate logs created by the extension over `Kₙ` in a target field with maps through `Kₙ`. -/
noncomputable def TowerLog.denote {n N : ℕ} {E : Type*} [Field E] [Differential E] [Algebra ℚ E]
    (maps : TowerLog.EvaluationMaps N E) (hn : n ≤ N) : TowerLog (n + 1) → RatFunc E :=
  match n with
  | 0 => fun log =>
    letI : Algebra (CFieldSpec.K (DenseFracTower 0)) E := maps.algebra 0 hn
    match log with
    | .ordinary derivative coefficient argument =>
      localLogTerm (E := E) derivative (coefficient, argument)
    | .lrt derivative residue argument =>
      logResidueTermLrt (E := E) derivative (residue, argument)
  | n + 1 => fun log =>
    letI : Algebra (CFieldSpec.K (DenseFracTower (n + 1))) E := maps.algebra (n + 1) hn
    match log with
    | .ordinary derivative coefficient argument =>
      localLogTerm (E := E) derivative (coefficient, argument)
    | .lrt derivative residue argument =>
      logResidueTermLrt (E := E) derivative (residue, argument)
    | .inherited log =>
      TowerLog.denote maps (Nat.le_trans (Nat.le_succ n) hn) log
termination_by n

/-- Evaluate a recursive log in the field layer where it is differentiated.

Unlike `TowerLog.denote`, inherited logs are transported through the recursive realization's
function-field lift before they are included as successor coefficients. -/
noncomputable def TowerLog.realize {N : ℕ} (R : TowerRealization N) :
    ∀ n (hn : n ≤ N),
      letI : Field (R.Carrier n hn) := R.field (TowerRealization.index hn)
      TowerLog (n + 1) → RatFunc (R.Carrier n hn)
  | 0, hn, log => by
    letI : Field (R.Carrier 0 hn) := R.field (TowerRealization.index hn)
    letI : Differential (R.Carrier 0 hn) := R.differential (TowerRealization.index hn)
    letI : Algebra ℚ (R.Carrier 0 hn) := R.algebraQ (TowerRealization.index hn)
    letI : Algebra (CFieldSpec.K (DenseFracTower 0)) (R.Carrier 0 hn) := R.algebra 0 hn
    exact match log with
    | .ordinary derivative coefficient argument =>
      localLogTerm (E := R.Carrier 0 hn) derivative (coefficient, argument)
    | .lrt derivative residue argument =>
      logResidueTermLrt (E := R.Carrier 0 hn) derivative (residue, argument)
    | .inherited lower => nomatch lower
  | n + 1, hn, log => by
    let hprev : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
    letI : Field (R.Carrier (n + 1) hn) := R.field (TowerRealization.index hn)
    letI : Differential (R.Carrier (n + 1) hn) := R.differential (TowerRealization.index hn)
    letI : Algebra ℚ (R.Carrier (n + 1) hn) := R.algebraQ (TowerRealization.index hn)
    letI : Algebra (CFieldSpec.K (DenseFracTower (n + 1))) (R.Carrier (n + 1) hn) :=
      R.algebra (n + 1) hn
    exact match log with
    | .ordinary derivative coefficient argument =>
      localLogTerm (E := R.Carrier (n + 1) hn) derivative (coefficient, argument)
    | .lrt derivative residue argument =>
      logResidueTermLrt (E := R.Carrier (n + 1) hn) derivative (residue, argument)
    | .inherited lower =>
      letI : Field (R.Carrier n hprev) := R.field (TowerRealization.index hprev)
      letI : Algebra (RatFunc (R.Carrier n hprev)) (R.Carrier (n + 1) hn) :=
        R.stepAlgebra n hn
      algebraMap (R.Carrier (n + 1) hn) (RatFunc (R.Carrier (n + 1) hn))
        (R.lift n hn (TowerLog.realize R n hprev lower))

/-- Sum the realization-indexed derivative contributions of a recursive log list. -/
noncomputable def TowerLog.realizeSum {N n : ℕ} (R : TowerRealization N) (hn : n ≤ N)
    (logs : List (TowerLog (n + 1))) :
    letI : Field (R.Carrier n hn) := R.field (TowerRealization.index hn)
    RatFunc (R.Carrier n hn) := by
  letI : Field (R.Carrier n hn) := R.field (TowerRealization.index hn)
  exact (logs.map (TowerLog.realize R n hn)).sum

/-- The realization of an inherited log is the coefficient lift of its preceding derivative term. -/
theorem TowerLog.realize_inherited {N n : ℕ} (R : TowerRealization N) (hn : n + 1 ≤ N)
    (log : TowerLog (n + 1)) :
    let hprev : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
    letI : Field (R.Carrier n hprev) := R.field (TowerRealization.index hprev)
    letI : Field (R.Carrier (n + 1) hn) := R.field (TowerRealization.index hn)
    letI : Algebra (RatFunc (R.Carrier n hprev)) (R.Carrier (n + 1) hn) :=
      R.stepAlgebra n hn
    TowerLog.realize R (n + 1) hn (TowerLog.inherited log) =
      algebraMap (R.Carrier (n + 1) hn) (RatFunc (R.Carrier (n + 1) hn))
        (R.lift n hn (TowerLog.realize R n hprev log)) := by
  rfl

/-- Realizing an inherited log list applies the successor coefficient lift to its preceding sum. -/
theorem towerLog_realizeSum_inheritAll {N n : ℕ} (R : TowerRealization N) (hn : n + 1 ≤ N)
    (logs : List (TowerLog (n + 1))) :
    let hprev : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
    letI : Field (R.Carrier n hprev) := R.field (TowerRealization.index hprev)
    letI : Field (R.Carrier (n + 1) hn) := R.field (TowerRealization.index hn)
    letI : Algebra (RatFunc (R.Carrier n hprev)) (R.Carrier (n + 1) hn) :=
      R.stepAlgebra n hn
    TowerLog.realizeSum R hn (TowerLog.inheritAll logs) =
      algebraMap (R.Carrier (n + 1) hn) (RatFunc (R.Carrier (n + 1) hn))
        (R.lift n hn (TowerLog.realizeSum R hprev logs)) := by
  let hprev : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
  letI : Field (R.Carrier n hprev) := R.field (TowerRealization.index hprev)
  letI : Field (R.Carrier (n + 1) hn) := R.field (TowerRealization.index hn)
  letI : Algebra (RatFunc (R.Carrier n hprev)) (R.Carrier (n + 1) hn) :=
    R.stepAlgebra n hn
  induction logs with
  | nil => simp [TowerLog.inheritAll, TowerLog.realizeSum]
  | cons log logs ih =>
    have htail :
        (List.map (TowerLog.realize R (n + 1) hn)
          (List.map TowerLog.inherited logs)).sum =
          algebraMap (R.Carrier (n + 1) hn) (RatFunc (R.Carrier (n + 1) hn))
            (R.lift n hn ((List.map (TowerLog.realize R n
              (Nat.le_trans (Nat.le_succ n) hn)) logs).sum)) := by
      simpa [TowerLog.inheritAll, TowerLog.realizeSum] using ih
    simp only [TowerLog.inheritAll, TowerLog.realizeSum, List.map_cons, List.sum_cons]
    rw [TowerLog.realize_inherited, htail]
    simp only [map_add]

/-- Realize the rational part of a tower result at its own recursive coefficient field. -/
noncomputable def TowerIntegralResult.rationalRealize {N n : ℕ} (R : TowerRealization N)
    (hn : n ≤ N) (res : TowerIntegralResult n) :
    letI : Field (R.Carrier n hn) := R.field (TowerRealization.index hn)
    letI : Algebra (CFieldSpec.K (DenseFracTower n)) (R.Carrier n hn) := R.algebra n hn
    RatFunc (R.Carrier n hn) := by
  letI : Field (R.Carrier n hn) := R.field (TowerRealization.index hn)
  letI : Algebra (CFieldSpec.K (DenseFracTower n)) (R.Carrier n hn) := R.algebra n hn
  exact amGExt (E := R.Carrier n hn) (CPoly.toPoly (CFrac.num res.rational)) /
    amGExt (E := R.Carrier n hn) (CPoly.toPoly (CFrac.den res.rational))

/-- Differentiate a tower result in the realization layer for its monomial extension. -/
noncomputable def TowerIntegralResult.derivRealize {N n : ℕ} (R : TowerRealization N)
    (hn : n ≤ N) (Dt : DensePoly (DenseFracTower n)) (res : TowerIntegralResult n) :
    letI : Field (R.Carrier n hn) := R.field (TowerRealization.index hn)
    letI : Differential (R.Carrier n hn) := R.differential (TowerRealization.index hn)
    letI : Algebra ℚ (R.Carrier n hn) := R.algebraQ (TowerRealization.index hn)
    letI : Algebra (CFieldSpec.K (DenseFracTower n)) (R.Carrier n hn) := R.algebra n hn
    RatFunc (R.Carrier n hn) := by
  letI : Field (R.Carrier n hn) := R.field (TowerRealization.index hn)
  letI : Differential (R.Carrier n hn) := R.differential (TowerRealization.index hn)
  letI : Algebra ℚ (R.Carrier n hn) := R.algebraQ (TowerRealization.index hn)
  letI : Algebra (CFieldSpec.K (DenseFracTower n)) (R.Carrier n hn) := R.algebra n hn
  exact towerDerivExt Dt (res.rationalRealize R hn) + TowerLog.realizeSum R hn res.logs

/-- A result differentiates to its input fraction in a fixed recursive tower realization. -/
def IsRealizedTowerIntegralResult {N n : ℕ} (R : TowerRealization N) (hn : n ≤ N)
    (Dt anum aden : DensePoly (DenseFracTower n)) (res : TowerIntegralResult n) : Prop :=
  letI : Field (R.Carrier n hn) := R.field (TowerRealization.index hn)
  letI : Differential (R.Carrier n hn) := R.differential (TowerRealization.index hn)
  letI : Algebra ℚ (R.Carrier n hn) := R.algebraQ (TowerRealization.index hn)
  letI : Algebra (CFieldSpec.K (DenseFracTower n)) (R.Carrier n hn) := R.algebra n hn
  res.derivRealize R hn Dt =
    amGExt (E := R.Carrier n hn) (CPoly.toPoly anum) /
      amGExt (E := R.Carrier n hn) (CPoly.toPoly aden)

/-- A realized lower coefficient identity lifts to its successor represented-field value. -/
theorem lift_isRealizedCoefficient {N n : ℕ} (R : TowerRealization N) (hn : n + 1 ≤ N)
    (Dt : DensePoly (DenseFracTower n)) (c : DenseFracTower (n + 1))
    (res : TowerIntegralResult n)
    (hres : IsRealizedTowerIntegralResult R (Nat.le_trans (Nat.le_succ n) hn)
      Dt (CFrac.num c) (CFrac.den c) res) :
    let hprev : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
    letI : Field (R.Carrier n hprev) := R.field (TowerRealization.index hprev)
    letI : Differential (R.Carrier n hprev) := R.differential (TowerRealization.index hprev)
    letI : Algebra ℚ (R.Carrier n hprev) := R.algebraQ (TowerRealization.index hprev)
    letI : Algebra (CFieldSpec.K (DenseFracTower n)) (R.Carrier n hprev) := R.algebra n hprev
    letI : Field (R.Carrier (n + 1) hn) := R.field (TowerRealization.index hn)
    letI : Algebra (RatFunc (R.Carrier n hprev)) (R.Carrier (n + 1) hn) := R.stepAlgebra n hn
    letI : Algebra (CFieldSpec.K (DenseFracTower (n + 1))) (R.Carrier (n + 1) hn) :=
      R.algebra (n + 1) hn
    R.lift n hn (res.derivRealize R hprev Dt) =
      algebraMap (CFieldSpec.K (DenseFracTower (n + 1))) (R.Carrier (n + 1) hn)
        (CFieldSpec.toK c) := by
  let hprev : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
  letI : Field (R.Carrier n hprev) := R.field (TowerRealization.index hprev)
  letI : Differential (R.Carrier n hprev) := R.differential (TowerRealization.index hprev)
  letI : Algebra ℚ (R.Carrier n hprev) := R.algebraQ (TowerRealization.index hprev)
  letI : Algebra (CFieldSpec.K (DenseFracTower n)) (R.Carrier n hprev) := R.algebra n hprev
  letI : Field (R.Carrier (n + 1) hn) := R.field (TowerRealization.index hn)
  letI : Algebra (RatFunc (R.Carrier n hprev)) (R.Carrier (n + 1) hn) := R.stepAlgebra n hn
  letI : Algebra (CFieldSpec.K (DenseFracTower (n + 1))) (R.Carrier (n + 1) hn) :=
    R.algebra (n + 1) hn
  dsimp
  unfold IsRealizedTowerIntegralResult at hres
  rw [hres]
  change R.lift n hn (R.coefficientRealize n hprev c) = _
  exact R.lift_coefficientRealize n hn c

/-- Appending lower logs realizes as the local sum plus the lifted preceding log contribution. -/
theorem TowerIntegralResult.realizeSum_appendInherited {N n : ℕ} (R : TowerRealization N)
    (hn : n + 1 ≤ N) (localResult : TowerIntegralResult (n + 1))
    (lower : TowerIntegralResult n) :
    let hprev : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
    letI : Field (R.Carrier n hprev) := R.field (TowerRealization.index hprev)
    letI : Field (R.Carrier (n + 1) hn) := R.field (TowerRealization.index hn)
    letI : Algebra (RatFunc (R.Carrier n hprev)) (R.Carrier (n + 1) hn) :=
      R.stepAlgebra n hn
    TowerLog.realizeSum R hn (localResult.appendInherited lower).logs =
      TowerLog.realizeSum R hn localResult.logs +
        algebraMap (R.Carrier (n + 1) hn) (RatFunc (R.Carrier (n + 1) hn))
          (R.lift n hn (TowerLog.realizeSum R hprev lower.logs)) := by
  let hprev : n ≤ N := Nat.le_trans (Nat.le_succ n) hn
  letI : Field (R.Carrier n hprev) := R.field (TowerRealization.index hprev)
  letI : Field (R.Carrier (n + 1) hn) := R.field (TowerRealization.index hn)
  letI : Algebra (RatFunc (R.Carrier n hprev)) (R.Carrier (n + 1) hn) :=
    R.stepAlgebra n hn
  unfold TowerIntegralResult.appendInherited
  have hinherit := towerLog_realizeSum_inheritAll R hn lower.logs
  have hinherit' :
      (List.map (TowerLog.realize R (n + 1) hn)
        (TowerLog.inheritAll lower.logs)).sum =
        algebraMap (R.Carrier (n + 1) hn) (RatFunc (R.Carrier (n + 1) hn))
          (R.lift n hn ((List.map (TowerLog.realize R n hprev) lower.logs).sum)) := by
    simpa [TowerLog.realizeSum] using hinherit
  simp only [TowerLog.realizeSum, List.map_append, List.sum_append]
  rw [hinherit']

/-- Realization-indexed ordinary logs sum to the corresponding one-level log contribution. -/
theorem towerLog_realizeSum_ordinary {N n : ℕ} (R : TowerRealization N) (hn : n ≤ N)
    (derivative : DensePoly (DenseFracTower n))
    (logs : List (DenseFracTower n × DensePoly (DenseFracTower n))) :
    letI : Field (R.Carrier n hn) := R.field (TowerRealization.index hn)
    letI : Differential (R.Carrier n hn) := R.differential (TowerRealization.index hn)
    letI : Algebra ℚ (R.Carrier n hn) := R.algebraQ (TowerRealization.index hn)
    letI : Algebra (CFieldSpec.K (DenseFracTower n)) (R.Carrier n hn) := R.algebra n hn
    TowerLog.realizeSum R hn (logs.map fun log => TowerLog.ordinary derivative log.1 log.2) =
      localLogSum (E := R.Carrier n hn) derivative logs := by
  letI : Field (R.Carrier n hn) := R.field (TowerRealization.index hn)
  letI : Differential (R.Carrier n hn) := R.differential (TowerRealization.index hn)
  letI : Algebra ℚ (R.Carrier n hn) := R.algebraQ (TowerRealization.index hn)
  letI : Algebra (CFieldSpec.K (DenseFracTower n)) (R.Carrier n hn) := R.algebra n hn
  induction logs with
  | nil => rfl
  | cons log logs ih =>
    have ih' :
        (List.map (TowerLog.realize R n hn)
          (logs.map fun log => TowerLog.ordinary derivative log.1 log.2)).sum =
          localLogSum (E := R.Carrier n hn) derivative logs := by
      simpa [TowerLog.realizeSum] using ih
    simp only [TowerLog.realizeSum, localLogSum, List.map_cons, List.sum_cons]
    rw [ih']
    unfold TowerLog.realize
    cases n <;> rfl

/-- Realization-indexed LRT logs sum to the corresponding one-level residue contribution. -/
theorem towerLog_realizeSum_lrt {N n : ℕ} (R : TowerRealization N) (hn : n ≤ N)
    (derivative : DensePoly (DenseFracTower n))
    (logs : List (DensePoly (DenseFracTower n) × List (DensePoly (DenseFracTower n)))) :
    letI : Field (R.Carrier n hn) := R.field (TowerRealization.index hn)
    letI : Differential (R.Carrier n hn) := R.differential (TowerRealization.index hn)
    letI : Algebra ℚ (R.Carrier n hn) := R.algebraQ (TowerRealization.index hn)
    letI : Algebra (CFieldSpec.K (DenseFracTower n)) (R.Carrier n hn) := R.algebra n hn
    TowerLog.realizeSum R hn (logs.map fun log => TowerLog.lrt derivative log.1 log.2) =
      logResidueSumLrt (E := R.Carrier n hn) derivative logs := by
  letI : Field (R.Carrier n hn) := R.field (TowerRealization.index hn)
  letI : Differential (R.Carrier n hn) := R.differential (TowerRealization.index hn)
  letI : Algebra ℚ (R.Carrier n hn) := R.algebraQ (TowerRealization.index hn)
  letI : Algebra (CFieldSpec.K (DenseFracTower n)) (R.Carrier n hn) := R.algebra n hn
  induction logs with
  | nil => rfl
  | cons log logs ih =>
    have ih' :
        (List.map (TowerLog.realize R n hn)
          (logs.map fun log => TowerLog.lrt derivative log.1 log.2)).sum =
          logResidueSumLrt (E := R.Carrier n hn) derivative logs := by
      simpa [TowerLog.realizeSum] using ih
    simp only [TowerLog.realizeSum, logResidueSumLrtG_cons, List.map_cons, List.sum_cons]
    rw [ih']
    unfold TowerLog.realize
    cases n <;> rfl

/-- Restricting evaluation maps does not change a source-level log's denotation. -/
theorem TowerLog.denote_restrict {n M N : ℕ} {E : Type*}
    [Field E] [Differential E] [Algebra ℚ E] (maps : TowerLog.EvaluationMaps N E)
    (hMN : M ≤ N) (hn : n ≤ M) (log : TowerLog (n + 1)) :
    TowerLog.denote (maps.restrict hMN) hn log =
      TowerLog.denote maps (Nat.le_trans hn hMN) log := by
  induction n generalizing M N with
  | zero =>
    cases log <;> simp only [TowerLog.denote, TowerLog.EvaluationMaps.restrict]
  | succ n ih =>
    cases log with
    | ordinary derivative coefficient argument =>
      simp only [TowerLog.denote, TowerLog.EvaluationMaps.restrict]
    | lrt derivative residue argument =>
      simp only [TowerLog.denote, TowerLog.EvaluationMaps.restrict]
    | inherited log =>
      simp only [TowerLog.denote, TowerLog.EvaluationMaps.restrict]
      exact ih maps hMN (Nat.le_trans (Nat.le_succ n) hn) log

/-- Sum recursive-log denotations in a final evaluation field. -/
noncomputable def TowerLog.denoteSum {n N : ℕ} {E : Type*} [Field E] [Differential E] [Algebra ℚ E]
    (maps : TowerLog.EvaluationMaps N E) (hn : n ≤ N) (logs : List (TowerLog (n + 1))) : RatFunc E :=
  (logs.map (TowerLog.denote maps hn)).sum

/-- Restricting maps preserves the denotation of an entire source-level log list. -/
theorem TowerLog.denoteSum_restrict {n M N : ℕ} {E : Type*}
    [Field E] [Differential E] [Algebra ℚ E] (maps : TowerLog.EvaluationMaps N E)
    (hMN : M ≤ N) (hn : n ≤ M) (logs : List (TowerLog (n + 1))) :
    TowerLog.denoteSum (maps.restrict hMN) hn logs =
      TowerLog.denoteSum maps (Nat.le_trans hn hMN) logs := by
  induction logs with
  | nil => rfl
  | cons log logs ih =>
    simp only [TowerLog.denoteSum, List.map_cons, List.sum_cons]
    change TowerLog.denote (maps.restrict hMN) hn log +
        TowerLog.denoteSum (maps.restrict hMN) hn logs =
      TowerLog.denote maps (Nat.le_trans hn hMN) log +
        TowerLog.denoteSum maps (Nat.le_trans hn hMN) logs
    rw [TowerLog.denote_restrict, ih]

/-- Log evaluation distributes over composition of tower antiderivative pieces. -/
theorem TowerIntegralResult.denoteSum_add {n N : ℕ} {E : Type*}
    [Field E] [Differential E] [Algebra ℚ E] (maps : TowerLog.EvaluationMaps N E)
    (hn : n ≤ N) (left right : TowerIntegralResult n) :
    TowerLog.denoteSum maps hn (left.add right).logs =
      TowerLog.denoteSum maps hn left.logs + TowerLog.denoteSum maps hn right.logs := by
  simp only [TowerIntegralResult.add, TowerLog.denoteSum, List.map_append, List.sum_append]

/-- The complete differentiated denotation of one tower antiderivative piece. -/
noncomputable def TowerIntegralResult.derivDenote {n N : ℕ} {E : Type*}
    [Field E] [Differential E] [Algebra ℚ E] (Dt : DensePoly (DenseFracTower n))
    (maps : TowerLog.EvaluationMaps N E) (hn : n ≤ N) (res : TowerIntegralResult n) : RatFunc E := by
  letI : Algebra (CFieldSpec.K (DenseFracTower n)) E := maps.algebra n hn
  exact towerDerivExt Dt (res.rationalDenote maps hn) + TowerLog.denoteSum maps hn res.logs

/-- Differentiated tower-result denotation distributes over reconstruction by addition. -/
theorem TowerIntegralResult.derivDenote_add {n N : ℕ} {E : Type*}
    [Field E] [Differential E] [Algebra ℚ E] (Dt : DensePoly (DenseFracTower n))
    (maps : TowerLog.EvaluationMaps N E) (hn : n ≤ N)
    (left right : TowerIntegralResult n) :
    (left.add right).derivDenote Dt maps hn =
      left.derivDenote Dt maps hn + right.derivDenote Dt maps hn := by
  letI : Algebra (CFieldSpec.K (DenseFracTower n)) E := maps.algebra n hn
  unfold TowerIntegralResult.derivDenote
  rw [TowerIntegralResult.rationalDenote_add, map_add,
    TowerIntegralResult.denoteSum_add]
  ring

/-- Restricting maps preserves a complete differentiated tower-result denotation. -/
theorem TowerIntegralResult.derivDenote_restrict {n M N : ℕ} {E : Type*}
    [Field E] [Differential E] [Algebra ℚ E] (Dt : DensePoly (DenseFracTower n))
    (maps : TowerLog.EvaluationMaps N E) (hMN : M ≤ N) (hn : n ≤ M)
    (res : TowerIntegralResult n) :
    res.derivDenote Dt (maps.restrict hMN) hn =
      res.derivDenote Dt maps (Nat.le_trans hn hMN) := by
  letI : Algebra (CFieldSpec.K (DenseFracTower n)) E :=
    maps.algebra n (Nat.le_trans hn hMN)
  unfold TowerIntegralResult.derivDenote
  rw [TowerIntegralResult.rationalDenote_restrict,
    TowerLog.denoteSum_restrict]
  rfl

/-- Evaluating an inherited log agrees with evaluating its source-level syntax. -/
theorem TowerLog.denote_inherited {n N : ℕ} {E : Type*}
    [Field E] [Differential E] [Algebra ℚ E] (maps : TowerLog.EvaluationMaps N E)
    (hn : n + 1 ≤ N) (log : TowerLog (n + 1)) :
    TowerLog.denote maps hn (TowerLog.inherited log) =
      TowerLog.denote maps (Nat.le_trans (Nat.le_succ n) hn) log := by
  cases n <;> cases log <;> simp only [TowerLog.denote]

/-- Evaluating a lifted log list agrees with evaluating the original list at its source depth. -/
theorem towerLog_denoteSum_inheritAll {n N : ℕ} {E : Type*}
    [Field E] [Differential E] [Algebra ℚ E] (maps : TowerLog.EvaluationMaps N E)
    (hn : n + 1 ≤ N) (logs : List (TowerLog (n + 1))) :
    TowerLog.denoteSum maps hn (TowerLog.inheritAll logs) =
      TowerLog.denoteSum maps (Nat.le_trans (Nat.le_succ n) hn) logs := by
  induction logs with
  | nil => rfl
  | cons log logs ih =>
    simp only [TowerLog.inheritAll, TowerLog.denoteSum, List.map_cons, List.sum_cons]
    change TowerLog.denote maps hn (TowerLog.inherited log) +
        TowerLog.denoteSum maps hn (TowerLog.inheritAll logs) =
      TowerLog.denote maps (Nat.le_trans (Nat.le_succ n) hn) log +
        TowerLog.denoteSum maps (Nat.le_trans (Nat.le_succ n) hn) logs
    rw [TowerLog.denote_inherited, ih]

/-- Appending lower logs evaluates as the sum of local and lower-depth contributions. -/
theorem TowerIntegralResult.denoteSum_appendInherited {n N : ℕ} {E : Type*}
    [Field E] [Differential E] [Algebra ℚ E] (maps : TowerLog.EvaluationMaps N E)
    (hn : n + 1 ≤ N) (localResult : TowerIntegralResult (n + 1))
    (lower : TowerIntegralResult n) :
    TowerLog.denoteSum maps hn (localResult.appendInherited lower).logs =
      TowerLog.denoteSum maps hn localResult.logs +
        TowerLog.denoteSum maps (Nat.le_trans (Nat.le_succ n) hn) lower.logs := by
  simp only [TowerIntegralResult.appendInherited, TowerLog.denoteSum,
    List.map_append, List.sum_append]
  change TowerLog.denoteSum maps hn localResult.logs +
      TowerLog.denoteSum maps hn (TowerLog.inheritAll lower.logs) =
    TowerLog.denoteSum maps hn localResult.logs +
      TowerLog.denoteSum maps (Nat.le_trans (Nat.le_succ n) hn) lower.logs
  rw [towerLog_denoteSum_inheritAll]

/-- A semantic remainder in every algebraically closed evaluation field at one tower depth. -/
abbrev TowerRemainder (n : ℕ) : Type 1 :=
  ∀ (E : Type) [Field E] [Differential E] [Algebra ℚ E] [IsAlgClosed E],
    TowerLog.EvaluationMaps n E → RatFunc E

/-- The semantic remainder denoted by a represented input fraction. -/
noncomputable def towerInputRemainder {n : ℕ}
    (anum aden : DensePoly (DenseFracTower n)) : TowerRemainder n :=
  fun E _ _ _ _ maps => by
    letI : Algebra (CFieldSpec.K (DenseFracTower n)) E :=
      maps.algebra n (Nat.le_refl n)
    exact amGExt (E := E) (CPoly.toPoly anum) /
      amGExt (E := E) (CPoly.toPoly aden)

/-- A tower result has the specified semantic derivative remainder. -/
def IsTowerAntiderivative {n : ℕ} (Dt : DensePoly (DenseFracTower n))
    (res : TowerIntegralResult n) (remainder : TowerRemainder n) : Prop :=
  ∀ (E : Type) [Field E] [Differential E] [Algebra ℚ E] [IsAlgClosed E]
    (maps : TowerLog.EvaluationMaps n E),
    res.derivDenote Dt maps (Nat.le_refl n) = remainder E maps

/-- Semantic tower antiderivative certificates compose by addition of their remainders. -/
theorem isTowerAntiderivative_add {n : ℕ} (Dt : DensePoly (DenseFracTower n))
    (left right : TowerIntegralResult n) (leftRemainder rightRemainder : TowerRemainder n)
    (hleft : IsTowerAntiderivative Dt left leftRemainder)
    (hright : IsTowerAntiderivative Dt right rightRemainder) :
    IsTowerAntiderivative Dt (left.add right)
      (fun E _ _ _ _ maps => leftRemainder E maps + rightRemainder E maps) := by
  intro E _ _ _ _ maps
  rw [TowerIntegralResult.derivDenote_add, hleft E maps, hright E maps]

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

/-- The concrete input-fraction invariant is the general tower-remainder contract specialized to that input. -/
theorem isTowerIntegralResult_iff {n : ℕ} (Dt anum aden : DensePoly (DenseFracTower n))
    (res : TowerIntegralResult n) :
    IsTowerIntegralResult Dt anum aden res ↔
      IsTowerAntiderivative Dt res (towerInputRemainder anum aden) := by
  rfl

/-- A certified tower result evaluates correctly in any coherent extension of its source depth. -/
theorem isTowerIntegralResult_evaluate {n N : ℕ} {E : Type}
    [Field E] [Differential E] [Algebra ℚ E] [IsAlgClosed E]
    (Dt anum aden : DensePoly (DenseFracTower n)) (res : TowerIntegralResult n)
    (hres : IsTowerIntegralResult Dt anum aden res)
    (maps : TowerLog.EvaluationMaps N E) (hn : n ≤ N) :
    res.derivDenote Dt maps hn =
      letI : Algebra (CFieldSpec.K (DenseFracTower n)) E := maps.algebra n hn
      amGExt (E := E) (CPoly.toPoly anum) /
        amGExt (E := E) (CPoly.toPoly aden) := by
  have hsource := (isTowerIntegralResult_iff Dt anum aden res).mp hres E
    (maps.restrict hn)
  rw [TowerIntegralResult.derivDenote_restrict Dt maps hn (Nat.le_refl n)] at hsource
  exact hsource

/-- The common recursive-output contract for a coefficient under the preceding monomial derivative. -/
def TowerCoefficientStage.Correct {n : ℕ} (derivative : DensePoly (DenseFracTower n))
    (c : DenseFracTower (n + 1))
    (res : TowerIntegralResult n) : Prop :=
  IsTowerIntegralResult derivative
    (CFrac.num c) (CFrac.den c) res ∧ res.LogsGenuine

/-- A certified lower coefficient stage with a recursive tower-result output. -/
structure TowerCoefficientStage (n : ℕ) where
  /-- Monomial derivative of the field in which coefficient fractions are integrated. -/
  derivative : DensePoly (DenseFracTower n)
  /-- Semantic integrability predicate supported by the selected lower stage. -/
  Integrable : DenseFracTower (n + 1) → Prop
  /-- Executable, domain-certified lower coefficient stage. -/
  stage : IntegrationStage (DenseFracTower (n + 1)) (TowerIntegralResult n)
    Integrable (TowerCoefficientStage.Correct derivative)

/-- A coefficient stage is semantically aligned with one step of a recursive realization. -/
def TowerCoefficientStage.IsRealized {N n : ℕ} (C : TowerCoefficientStage n)
    (R : TowerRealization N) (hn : n + 1 ≤ N) : Prop :=
  C.derivative = R.monomialDerivative n hn ∧
    ∀ fuel c result, C.stage.domain c → C.stage.run fuel c = some result →
      IsRealizedTowerIntegralResult R (Nat.le_trans (Nat.le_succ n) hn)
        C.derivative (CFrac.num c) (CFrac.den c) result ∧ result.LogsGenuine

/-- A successor-local result is correct relative to the logarithms retained from the preceding level. -/
def IsTowerIntegralResultWithLowerLogs {n : ℕ}
    (Dt anum aden : DensePoly (DenseFracTower (n + 1)))
    (localResult : TowerIntegralResult (n + 1)) (lower : TowerIntegralResult n) : Prop :=
  ∀ (E : Type) [Field E] [Differential E] [Algebra ℚ E] [IsAlgClosed E]
    (maps : TowerLog.EvaluationMaps (n + 1) E),
    letI : Algebra (CFieldSpec.K (DenseFracTower (n + 1))) E :=
      maps.algebra (n + 1) (Nat.le_refl (n + 1))
    letI : DifferentialAlgebra (CFieldSpec.K (DenseFracTower (n + 1))) E :=
      maps.differentialAlgebra (n + 1) (Nat.le_refl (n + 1))
    towerDerivExt Dt
        (amGExt (E := E) (CPoly.toPoly (CFrac.num localResult.rational)) /
          amGExt (E := E) (CPoly.toPoly (CFrac.den localResult.rational))) +
      (TowerLog.denoteSum maps (Nat.le_refl (n + 1)) localResult.logs +
        TowerLog.denoteSum maps
          (Nat.le_trans (Nat.le_succ n) (Nat.le_refl (n + 1))) lower.logs) =
      amGExt (E := E) (CPoly.toPoly anum) /
        amGExt (E := E) (CPoly.toPoly aden)

/-- A relative successor certificate becomes an ordinary result certificate after inherited logs are appended. -/
theorem isTowerIntegralResult_appendInherited {n : ℕ}
    (Dt anum aden : DensePoly (DenseFracTower (n + 1)))
    (localResult : TowerIntegralResult (n + 1)) (lower : TowerIntegralResult n)
    (hresult : IsTowerIntegralResultWithLowerLogs Dt anum aden localResult lower) :
    IsTowerIntegralResult Dt anum aden (localResult.appendInherited lower) := by
  intro E _ _ _ _ maps
  letI : Algebra (CFieldSpec.K (DenseFracTower (n + 1))) E :=
    maps.algebra (n + 1) (Nat.le_refl (n + 1))
  letI : DifferentialAlgebra (CFieldSpec.K (DenseFracTower (n + 1))) E :=
    maps.differentialAlgebra (n + 1) (Nat.le_refl (n + 1))
  rw [TowerIntegralResult.denoteSum_appendInherited maps (Nat.le_refl (n + 1))]
  exact hresult E maps

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

/-- An ordinary one-level certificate transports to the realization-indexed tower invariant. -/
theorem isRealizedTowerIntegralResult_ofIntegralResult {N n : ℕ} (R : TowerRealization N)
    (hn : n ≤ N) [CFieldDomain (DenseFracTower n) DensePoly]
    (Dt anum aden : DensePoly (DenseFracTower n)) (res : IntegralResult (DenseFracTower n))
    (hres : IsIntegralResultP Dt anum aden res) :
    IsRealizedTowerIntegralResult R hn Dt anum aden
      (TowerIntegralResult.ofIntegralResult Dt res) := by
  letI : Field (R.Carrier n hn) := R.field (TowerRealization.index hn)
  letI : Differential (R.Carrier n hn) := R.differential (TowerRealization.index hn)
  letI : Algebra ℚ (R.Carrier n hn) := R.algebraQ (TowerRealization.index hn)
  letI : Algebra (CFieldSpec.K (DenseFracTower n)) (R.Carrier n hn) := R.algebra n hn
  letI : DifferentialAlgebra (CFieldSpec.K (DenseFracTower n)) (R.Carrier n hn) :=
    R.differentialAlgebra n hn
  have hderiv :
      ratFuncBaseChange (R.Carrier n hn)
          (towerFractionFieldDerivP Dt (fieldFracP res.rational.1 res.rational.2)) =
        towerDerivExt Dt
          (amGExt (E := R.Carrier n hn) (CPoly.toPoly res.rational.1) /
            amGExt (E := R.Carrier n hn) (CPoly.toPoly res.rational.2)) := by
    simpa only [towerFractionFieldDerivP, towerFractionFieldDeriv, fieldFracP, toPoly_list_eq] using
      (ratFuncBaseChange_towerFractionFieldDerivG (E := R.Carrier n hn) Dt
        (CPoly.toPoly res.rational.1) (CPoly.toPoly res.rational.2))
  have hrational :
      amGExt (E := R.Carrier n hn)
          (CPoly.toPoly (CFrac.num (TowerIntegralResult.ofIntegralResult Dt res).rational)) /
        amGExt (E := R.Carrier n hn)
          (CPoly.toPoly (CFrac.den (TowerIntegralResult.ofIntegralResult Dt res).rational)) =
        amGExt (E := R.Carrier n hn) (CPoly.toPoly res.rational.1) /
          amGExt (E := R.Carrier n hn) (CPoly.toPoly res.rational.2) := by
    calc
      _ = ratFuncBaseChange (R.Carrier n hn)
          (CFieldSpec.toK (TowerIntegralResult.ofIntegralResult Dt res).rational) := by
        symm
        rw [toK_denseFrac_eq_fieldFrac, fieldFracP, ratFuncBaseChange_amG_div]
      _ = ratFuncBaseChange (R.Carrier n hn) (fieldFracP res.rational.1 res.rational.2) := by
        simp [TowerIntegralResult.ofIntegralResult, fieldFracP, CFieldSpec.toK_div,
          CFrac.toK_ofPoly]
      _ = _ := by
        rw [fieldFracP, ratFuncBaseChange_amG_div]
  have hbase := congrArg (ratFuncBaseChange (R.Carrier n hn)) hres
  rw [map_add, hderiv, ← localLogSum_eq_baseChange,
    ratFuncBaseChange_amG_div] at hbase
  unfold IsRealizedTowerIntegralResult TowerIntegralResult.derivRealize
    TowerIntegralResult.rationalRealize
  have hlogs :
      TowerLog.realizeSum R hn (TowerIntegralResult.ofIntegralResult Dt res).logs =
        localLogSum (E := R.Carrier n hn) Dt res.logs := by
    simpa [TowerIntegralResult.ofIntegralResult] using
      (towerLog_realizeSum_ordinary R hn Dt res.logs)
  rw [hrational, hlogs]
  exact hbase

/-- A root-free one-level certificate transports to the realization-indexed tower invariant. -/
theorem isRealizedTowerIntegralResult_ofLrtResult {N n : ℕ} (R : TowerRealization N)
    (hn : n ≤ N) [CFieldDomain (DenseFracTower n) DensePoly]
    (Dt anum aden : DensePoly (DenseFracTower n)) (res : LrtResult (DenseFracTower n))
    (hres : IsIntegralResultLrt Dt anum aden res) :
    IsRealizedTowerIntegralResult R hn Dt anum aden
      (TowerIntegralResult.ofLrtResult Dt res) := by
  letI : Field (R.Carrier n hn) := R.field (TowerRealization.index hn)
  letI : Differential (R.Carrier n hn) := R.differential (TowerRealization.index hn)
  letI : Algebra ℚ (R.Carrier n hn) := R.algebraQ (TowerRealization.index hn)
  letI : IsAlgClosed (R.Carrier n hn) := R.isAlgClosed (TowerRealization.index hn)
  letI : Algebra (CFieldSpec.K (DenseFracTower n)) (R.Carrier n hn) := R.algebra n hn
  letI : DifferentialAlgebra (CFieldSpec.K (DenseFracTower n)) (R.Carrier n hn) :=
    R.differentialAlgebra n hn
  have hrational :
      amGExt (E := R.Carrier n hn)
          (CPoly.toPoly (CFrac.num (TowerIntegralResult.ofLrtResult Dt res).rational)) /
        amGExt (E := R.Carrier n hn)
          (CPoly.toPoly (CFrac.den (TowerIntegralResult.ofLrtResult Dt res).rational)) =
        amGExt (E := R.Carrier n hn) (CPoly.toPoly res.rational.1) /
          amGExt (E := R.Carrier n hn) (CPoly.toPoly res.rational.2) := by
    calc
      _ = ratFuncBaseChange (R.Carrier n hn)
          (CFieldSpec.toK (TowerIntegralResult.ofLrtResult Dt res).rational) := by
        symm
        rw [toK_denseFrac_eq_fieldFrac, fieldFracP, ratFuncBaseChange_amG_div]
      _ = ratFuncBaseChange (R.Carrier n hn) (fieldFracP res.rational.1 res.rational.2) := by
        simp [TowerIntegralResult.ofLrtResult, fieldFracP, CFieldSpec.toK_div,
          CFrac.toK_ofPoly]
      _ = _ := by
        rw [fieldFracP, ratFuncBaseChange_amG_div]
  unfold IsRealizedTowerIntegralResult TowerIntegralResult.derivRealize
    TowerIntegralResult.rationalRealize
  have hlogs :
      TowerLog.realizeSum R hn (TowerIntegralResult.ofLrtResult Dt res).logs =
        logResidueSumLrt (E := R.Carrier n hn) Dt res.logs := by
    simpa [TowerIntegralResult.ofLrtResult] using
      (towerLog_realizeSum_lrt R hn Dt res.logs)
  rw [hrational, hlogs]
  simpa only [toPoly_list_eq] using hres (R.Carrier n hn)

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

/-- Composing two genuine tower antiderivative pieces preserves genuine-log validity. -/
theorem TowerIntegralResult.logsGenuine_add {n : ℕ}
    (left right : TowerIntegralResult n)
    (hleft : left.LogsGenuine) (hright : right.LogsGenuine) :
    (left.add right).LogsGenuine := by
  intro log hlog
  rcases List.mem_append.mp hlog with hlog | hlog
  · exact hleft log hlog
  · exact hright log hlog

/-- Inheriting a genuine log list preserves its genuine-log condition. -/
theorem towerLog_inheritAll_genuine {n : ℕ} (logs : List (TowerLog n))
    (hlogs : ∀ log ∈ logs, log.IsGenuine) :
    ∀ log ∈ TowerLog.inheritAll logs, log.IsGenuine := by
  intro log hlog
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hlog
  exact hlogs source hsource

/-- Appending inherited lower logs preserves genuine-log validity. -/
theorem TowerIntegralResult.logsGenuine_appendInherited {n : ℕ}
    (localResult : TowerIntegralResult (n + 1)) (lower : TowerIntegralResult n)
    (hlocal : localResult.LogsGenuine) (hlower : lower.LogsGenuine) :
    (localResult.appendInherited lower).LogsGenuine := by
  intro log hlog
  rcases List.mem_append.mp hlog with hlocalLog | hinherited
  · exact hlocal log hlocalLog
  · exact towerLog_inheritAll_genuine lower.logs hlower log hinherited

end DeepWiki.SymbolicIntegration
