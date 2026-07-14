import DeepWiki.Refine.AnnotationConstraintSolver
import DeepWiki.Refine.RegisteredConstantSyntax

/-! # Output-indexed registered-constant rows

Registered translations retain their source, annotated type, target, witness, and annotation
dependencies. Output weakening generates one payload-preserving row at every strict lower annotation.
-/

namespace DeepWiki.Refine.RegisteredConstantRows

open RegisteredConstantSyntax

/-- A registered-constant row with both its annotation signature and translation payload. -/
structure Row (Constant : Type u) where
  /-- The source global constant. -/
  source : Constant
  /-- The annotated closed type selected for the source constant. -/
  sourceType : Term Constant 0
  /-- The annotation carried by the row's result relation. -/
  output : Annotation
  /-- The annotations occurring in the selected source type. -/
  inputs : List Annotation
  /-- The translated target term. -/
  target : Term Constant 0
  /-- The relation-witness term. -/
  witness : Term Constant 0
  deriving DecidableEq, Repr

/-- Forget a payload row to the annotation signature consumed by constraint solving. -/
def Row.annotationSignature (row : Row Constant) : Annotation × List Annotation :=
  (row.output, row.inputs)

/-- Forget a payload table to its annotation-only constraint rows. -/
def annotationRows (rows : List (Row Constant)) : List (Annotation × List Annotation) :=
  rows.map Row.annotationSignature

/-- Output weakening transforms a witness whenever the requested annotation is lower. -/
structure WitnessWeakening (Constant : Type u) where
  /-- Weaken a closed witness from `available` structure to `required` structure. -/
  weaken : {available required : Annotation} → required ≤ available →
    Term Constant 0 → Term Constant 0

/-- Replace a row's output annotation and witness while preserving its remaining payload. -/
def Row.weakenOutput (weakening : WitnessWeakening Constant) (row : Row Constant)
    (required : Annotation) (lower : required ≤ row.output) : Row Constant where
  source := row.source
  sourceType := row.sourceType
  output := required
  inputs := row.inputs
  target := row.target
  witness := weakening.weaken lower row.witness

/-- Output weakening preserves the source constant. -/
@[simp] theorem Row.weakenOutput_source (weakening : WitnessWeakening Constant)
    (row : Row Constant) (required : Annotation) (lower : required ≤ row.output) :
    (row.weakenOutput weakening required lower).source = row.source :=
  rfl

/-- Output weakening preserves the selected annotated source type. -/
@[simp] theorem Row.weakenOutput_sourceType (weakening : WitnessWeakening Constant)
    (row : Row Constant) (required : Annotation) (lower : required ≤ row.output) :
    (row.weakenOutput weakening required lower).sourceType = row.sourceType :=
  rfl

/-- Output weakening installs the requested output annotation. -/
@[simp] theorem Row.weakenOutput_output (weakening : WitnessWeakening Constant)
    (row : Row Constant) (required : Annotation) (lower : required ≤ row.output) :
    (row.weakenOutput weakening required lower).output = required :=
  rfl

/-- Output weakening preserves the source-type annotation dependencies. -/
@[simp] theorem Row.weakenOutput_inputs (weakening : WitnessWeakening Constant)
    (row : Row Constant) (required : Annotation) (lower : required ≤ row.output) :
    (row.weakenOutput weakening required lower).inputs = row.inputs :=
  rfl

/-- Output weakening preserves the translated target term. -/
@[simp] theorem Row.weakenOutput_target (weakening : WitnessWeakening Constant)
    (row : Row Constant) (required : Annotation) (lower : required ≤ row.output) :
    (row.weakenOutput weakening required lower).target = row.target :=
  rfl

/-- Output weakening replaces the witness by the selected weakening operation. -/
@[simp] theorem Row.weakenOutput_witness (weakening : WitnessWeakening Constant)
    (row : Row Constant) (required : Annotation) (lower : required ≤ row.output) :
    (row.weakenOutput weakening required lower).witness =
      weakening.weaken lower row.witness :=
  rfl

/-- A strict lower output is an annotation properly below the registered output. -/
abbrev StrictLowerOutput (output : Annotation) := {required : Annotation // required < output}

/-- Strict lower outputs inherit finiteness from the annotation lattice. -/
noncomputable instance (output : Annotation) : Fintype (StrictLowerOutput output) :=
  Fintype.ofFinite _

/-- The base row followed by its witness-weakened row at every strict lower output annotation. -/
noncomputable def generatedRows (weakening : WitnessWeakening Constant) (row : Row Constant) :
    List (Row Constant) :=
  row :: (Finset.univ : Finset (StrictLowerOutput row.output)).toList.map
    fun required : StrictLowerOutput row.output =>
      row.weakenOutput weakening required.1 (le_of_lt required.2)

/-- Membership in the generated family is exactly the base row or one strict output weakening. -/
theorem mem_generatedRows_iff (weakening : WitnessWeakening Constant) (row candidate : Row Constant) :
    candidate ∈ generatedRows weakening row ↔
      candidate = row ∨
        ∃ required : Annotation, ∃ lower : required < row.output,
          row.weakenOutput weakening required (le_of_lt lower) = candidate := by
  simp [generatedRows]

/-- The registered base row belongs to its generated downward family. -/
theorem mem_generatedRows_self (weakening : WitnessWeakening Constant) (row : Row Constant) :
    row ∈ generatedRows weakening row := by
  simp [generatedRows]

/-- Every strict lower output contributes its witness-weakened row to the generated family. -/
theorem mem_generatedRows_weakenOutput (weakening : WitnessWeakening Constant)
    (row : Row Constant) (required : Annotation) (lower : required < row.output) :
    row.weakenOutput weakening required (le_of_lt lower) ∈ generatedRows weakening row := by
  rw [mem_generatedRows_iff]
  exact Or.inr ⟨required, lower, rfl⟩

/-- Every generated row has an output annotation below the base row's output. -/
theorem output_le_of_mem_generatedRows (weakening : WitnessWeakening Constant)
    (row candidate : Row Constant) (member : candidate ∈ generatedRows weakening row) :
    candidate.output ≤ row.output := by
  rw [mem_generatedRows_iff] at member
  rcases member with rfl | ⟨required, lower, rfl⟩
  · exact le_rfl
  · exact le_of_lt lower

/-- Payload-backed rows induce the same registered-constant constraint as their signatures. -/
theorem holds_registeredConstant_annotationRows_iff {arity : Nat}
    (assignment : AnnotationAssignment arity) (output : AnnotationNode arity)
    (inputs : List (AnnotationNode arity)) (rows : List (Row Constant)) :
    (AnnotationConstraint.registeredConstant output inputs (annotationRows rows)).Holds assignment ↔
      ∃ row ∈ rows,
        output.evaluate assignment = row.output ∧
          inputs.map (fun input => input.evaluate assignment) = row.inputs := by
  rw [AnnotationConstraint.holds_registeredConstant_iff]
  simp [annotationRows, Row.annotationSignature]

/-- A row is realized by the recursive environment when its source/type lookup returns its payload. -/
def Row.RealizedBy (row : Row Constant) (environment : Environment Constant) : Prop :=
  environment.translation row.source row.sourceType = some (row.target, row.witness)

/-- A source/type-keyed lookup can realize at most one target-and-witness payload. -/
theorem realizedBy_payload_unique {environment : Environment Constant}
    {first second : Row Constant}
    (sameSource : first.source = second.source)
    (sameType : first.sourceType = second.sourceType)
    (firstRealized : first.RealizedBy environment)
    (secondRealized : second.RealizedBy environment) :
    first.target = second.target ∧ first.witness = second.witness := by
  have sameLookup :
      environment.translation first.source first.sourceType =
        environment.translation second.source second.sourceType := by
    rw [sameSource, sameType]
  have pairEqual :
      (first.target, first.witness) = (second.target, second.witness) := by
    exact Option.some.inj (firstRealized.symm.trans (sameLookup.trans secondRealized))
  exact Prod.mk.inj pairEqual

/-- Distinct weakened witnesses cannot both inhabit one unindexed source/type lookup. -/
theorem not_both_realizedBy_of_weakened_witness_ne
    {environment : Environment Constant} (weakening : WitnessWeakening Constant)
    (row : Row Constant) (required : Annotation) (lower : required ≤ row.output)
    (different : row.witness ≠ weakening.weaken lower row.witness) :
    ¬ (row.RealizedBy environment ∧
      (row.weakenOutput weakening required lower).RealizedBy environment) := by
  intro realized
  have payloadEqual := realizedBy_payload_unique
    (environment := environment) (first := row)
    (second := row.weakenOutput weakening required lower)
    rfl rfl realized.1 realized.2
  exact different payloadEqual.2

/-- A base lookup realizes its weakened row exactly when weakening leaves the witness unchanged. -/
theorem weakenOutput_realizedBy_iff_of_realizedBy
    {environment : Environment Constant} (weakening : WitnessWeakening Constant)
    (row : Row Constant) (required : Annotation) (lower : required ≤ row.output)
    (realized : row.RealizedBy environment) :
    (row.weakenOutput weakening required lower).RealizedBy environment ↔
      weakening.weaken lower row.witness = row.witness := by
  constructor
  · intro weakenedRealized
    exact (realizedBy_payload_unique
      (environment := environment) (first := row.weakenOutput weakening required lower)
      (second := row) rfl rfl weakenedRealized realized).2
  · intro fixed
    rw [Row.RealizedBy, Row.weakenOutput_source, Row.weakenOutput_sourceType,
      Row.weakenOutput_target, Row.weakenOutput_witness, fixed]
    exact realized

example (weakening : WitnessWeakening Constant) (row : Row Constant)
    (required : Annotation) (lower : required < row.output) :
    row.weakenOutput weakening required (le_of_lt lower) ∈ generatedRows weakening row :=
  mem_generatedRows_weakenOutput weakening row required lower

example {arity : Nat} (assignment : AnnotationAssignment arity)
    (output : AnnotationNode arity) (inputs : List (AnnotationNode arity))
    (rows : List (Row Constant)) :
    (AnnotationConstraint.registeredConstant output inputs (annotationRows rows)).Holds assignment ↔
      ∃ row ∈ rows,
        output.evaluate assignment = row.output ∧
          inputs.map (fun input => input.evaluate assignment) = row.inputs :=
  holds_registeredConstant_annotationRows_iff assignment output inputs rows

example {environment : Environment Constant} (weakening : WitnessWeakening Constant)
    (row : Row Constant) (required : Annotation) (lower : required ≤ row.output)
    (different : row.witness ≠ weakening.weaken lower row.witness) :
    ¬ (row.RealizedBy environment ∧
      (row.weakenOutput weakening required lower).RealizedBy environment) :=
  not_both_realizedBy_of_weakened_witness_ne weakening row required lower different

example {environment : Environment Constant} (weakening : WitnessWeakening Constant)
    (row : Row Constant) (required : Annotation) (lower : required ≤ row.output)
    (realized : row.RealizedBy environment) :
    (row.weakenOutput weakening required lower).RealizedBy environment ↔
      weakening.weaken lower row.witness = row.witness :=
  weakenOutput_realizedBy_iff_of_realizedBy weakening row required lower realized

end DeepWiki.Refine.RegisteredConstantRows
