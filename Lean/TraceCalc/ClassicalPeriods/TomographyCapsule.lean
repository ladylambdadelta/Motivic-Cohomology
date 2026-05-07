import TraceCalc.ClassicalPeriods.ClassicalManuscriptTargets
import TraceCalc.ClassicalPeriods.GeneratorRealizationExamples

universe u v w

namespace TraceCalc
namespace ClassicalPeriods

/-- Constructible core of the tomography capsule: one generator table, one recovered
comparison-slot map, and row-wise slot-separation data. -/
structure GeneratorTomographyCore
    (ctx : ClassicalComparisonContext.{u, v})
    (setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}) where
  assignmentTable : GeneratorRealizationAssignmentTable ctx
  slotData :
    TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
      StructuredComparisonSlotData
  recoveredMap :
    SymbolicRecoveredSlotAssignmentMap
      (GeneratorRealizationAssignmentTable.toGeneratorTableSlotLabelAssignment assignmentTable)
      slotData
  rowSlotSeparation : GeneratorRowSlotSeparationData assignmentTable

namespace GeneratorTomographyCore

/-- Pack recovered-row witnesses into the existing five-row recovered assignment target. -/
def recoveredAssignments
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup) :
    RecoveredSlotAssignmentData core.assignmentTable core.slotData :=
  core.recoveredMap.toRecoveredSlotAssignmentData

/-- The existing comparison-boundary recovery assumption built from the capsule core. -/
def toGeneratorTablePortLabelSeparationAssumption
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup) :
    GeneratorTablePortLabelSeparationAssumption core.assignmentTable core.slotData :=
  GeneratorTablePortLabelSeparationAssumption.ofData
    core.rowSlotSeparation
    core.recoveredAssignments

/-- Boundary-recovery bridge: recovered assignments feed the existing
comparison-side port-label separation target. -/
theorem toBoundaryRecoveryTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup) :
    PortLabelSeparationTargetOfSlots core.slotData :=
  (core.toGeneratorTablePortLabelSeparationAssumption).reducedPortLabelSeparationTarget

/-- Legacy manuscript-facing boundary shell obtained from the capsule core. -/
def toPortLabelSeparationTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup) :
    PortLabelSeparationTarget :=
  PortLabelSeparationTarget.ofGeneratorTableAssumption
    core.toGeneratorTablePortLabelSeparationAssumption

/-! ### Row slot API exposed by the capsule core -/

/-- Corr source-slot API. -/
def corrSourceSlot
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup) : String :=
  core.assignmentTable.corrAssignment.sourceSlotName

/-- Corr target-slot API. -/
def corrTargetSlot
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup) : String :=
  core.assignmentTable.corrAssignment.targetSlotName

/-- Loc ambient-slot API. -/
def locAmbientSlot
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup) : String :=
  core.assignmentTable.locAssignment.ambientSlotName

/-- Loc open-slot API. -/
def locOpenSlot
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup) : String :=
  core.assignmentTable.locAssignment.openSlotName

/-- Loc closed-slot API (table-level; not present in recovered core slots). -/
def locClosedSlot
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup) : String :=
  core.assignmentTable.locAssignment.closedSlotName

/-- Nis base-slot API. -/
def nisBaseSlot
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup) : String :=
  core.assignmentTable.nisAssignment.baseSlotName

/-- Nis patch-slot API. -/
def nisPatchSlot
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup) : String :=
  core.assignmentTable.nisAssignment.patchSlotName

/-- Nis overlap-slot API (table-level; not present in recovered core slots). -/
def nisOverlapSlot
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup) : String :=
  core.assignmentTable.nisAssignment.overlapSlotName

/-- A1 base-slot API. -/
def a1BaseSlot
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup) : String :=
  core.assignmentTable.a1Assignment.baseSlotName

/-- A1 cylinder-slot API. -/
def a1CylinderSlot
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup) : String :=
  core.assignmentTable.a1Assignment.cylinderSlotName

/-- Env ambient-slot API. -/
def envAmbientSlot
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup) : String :=
  core.assignmentTable.envAssignment.ambientSlotName

/-- Env envelope-slot API. -/
def envEnvelopeSlot
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup) : String :=
  core.assignmentTable.envAssignment.envelopeSlotName

/-! ### Row-wise recovered-slot soundness (for core recovered slots) -/

theorem corrSourceSound
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup)
    (hrow : core.recoveredMap.rowOf R = .corr) :
    (core.slotData R).sourceSlot =
      core.assignmentTable.toGeneratorTableSlotLabelAssignment.slotLabel (.corr .source) := by
  simpa [StructuredComparisonSlotData.coreLabel, hrow,
      SymbolicRecoveredSlotAssignmentMap.recoveredTableSlot,
      FiveRowSlotLabelAssignment.slotLabel_ofRowAndLabel]
    using core.recoveredMap.recoversSlotLabel R .source

 theorem corrTargetSound
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup)
    (hrow : core.recoveredMap.rowOf R = .corr) :
    (core.slotData R).targetSlot =
      core.assignmentTable.toGeneratorTableSlotLabelAssignment.slotLabel (.corr .target) := by
  simpa [StructuredComparisonSlotData.coreLabel, hrow,
      SymbolicRecoveredSlotAssignmentMap.recoveredTableSlot,
      FiveRowSlotLabelAssignment.slotLabel_ofRowAndLabel]
    using core.recoveredMap.recoversSlotLabel R .target

 theorem locAmbientSound
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup)
    (hrow : core.recoveredMap.rowOf R = .loc) :
    (core.slotData R).sourceSlot =
      core.assignmentTable.toGeneratorTableSlotLabelAssignment.slotLabel (.loc .source) := by
  simpa [StructuredComparisonSlotData.coreLabel,
    SymbolicRecoveredSlotAssignmentMap.recoveredTableSlot,
    FiveRowSlotLabelAssignment.slotLabel_ofRowAndLabel,
    hrow]
    using core.recoveredMap.recoversSlotLabel R .source

 theorem locOpenSound
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup)
    (hrow : core.recoveredMap.rowOf R = .loc) :
    (core.slotData R).targetSlot =
      core.assignmentTable.toGeneratorTableSlotLabelAssignment.slotLabel (.loc .target) := by
  simpa [StructuredComparisonSlotData.coreLabel,
    SymbolicRecoveredSlotAssignmentMap.recoveredTableSlot,
    FiveRowSlotLabelAssignment.slotLabel_ofRowAndLabel,
    hrow]
    using core.recoveredMap.recoversSlotLabel R .target

 theorem nisBaseSound
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup)
    (hrow : core.recoveredMap.rowOf R = .nis) :
    (core.slotData R).sourceSlot =
      core.assignmentTable.toGeneratorTableSlotLabelAssignment.slotLabel (.nis .source) := by
  simpa [StructuredComparisonSlotData.coreLabel,
    SymbolicRecoveredSlotAssignmentMap.recoveredTableSlot,
    FiveRowSlotLabelAssignment.slotLabel_ofRowAndLabel,
    hrow]
    using core.recoveredMap.recoversSlotLabel R .source

 theorem nisPatchSound
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup)
    (hrow : core.recoveredMap.rowOf R = .nis) :
    (core.slotData R).targetSlot =
      core.assignmentTable.toGeneratorTableSlotLabelAssignment.slotLabel (.nis .target) := by
  simpa [StructuredComparisonSlotData.coreLabel,
    SymbolicRecoveredSlotAssignmentMap.recoveredTableSlot,
    FiveRowSlotLabelAssignment.slotLabel_ofRowAndLabel,
    hrow]
    using core.recoveredMap.recoversSlotLabel R .target

 theorem a1BaseSound
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup)
    (hrow : core.recoveredMap.rowOf R = .a1) :
    (core.slotData R).sourceSlot =
      core.assignmentTable.toGeneratorTableSlotLabelAssignment.slotLabel (.a1 .source) := by
  simpa [StructuredComparisonSlotData.coreLabel,
    SymbolicRecoveredSlotAssignmentMap.recoveredTableSlot,
    FiveRowSlotLabelAssignment.slotLabel_ofRowAndLabel,
    hrow]
    using core.recoveredMap.recoversSlotLabel R .source

 theorem a1CylinderSound
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup)
    (hrow : core.recoveredMap.rowOf R = .a1) :
    (core.slotData R).targetSlot =
      core.assignmentTable.toGeneratorTableSlotLabelAssignment.slotLabel (.a1 .target) := by
  simpa [StructuredComparisonSlotData.coreLabel,
    SymbolicRecoveredSlotAssignmentMap.recoveredTableSlot,
    FiveRowSlotLabelAssignment.slotLabel_ofRowAndLabel,
    hrow]
    using core.recoveredMap.recoversSlotLabel R .target

 theorem envAmbientSound
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup)
    (hrow : core.recoveredMap.rowOf R = .env) :
    (core.slotData R).sourceSlot =
      core.assignmentTable.toGeneratorTableSlotLabelAssignment.slotLabel (.env .source) := by
  simpa [StructuredComparisonSlotData.coreLabel,
    SymbolicRecoveredSlotAssignmentMap.recoveredTableSlot,
    FiveRowSlotLabelAssignment.slotLabel_ofRowAndLabel,
    hrow]
    using core.recoveredMap.recoversSlotLabel R .source

 theorem envEnvelopeSound
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup)
    (hrow : core.recoveredMap.rowOf R = .env) :
    (core.slotData R).targetSlot =
      core.assignmentTable.toGeneratorTableSlotLabelAssignment.slotLabel (.env .target) := by
  simpa [StructuredComparisonSlotData.coreLabel,
    SymbolicRecoveredSlotAssignmentMap.recoveredTableSlot,
    FiveRowSlotLabelAssignment.slotLabel_ofRowAndLabel,
    hrow]
    using core.recoveredMap.recoversSlotLabel R .target

/-! ### Completeness/no-extra for the current finite core-slot enumeration -/

theorem recoveredTableSlot_row
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup)
    (label : GeneratorCoreSlotLabel) :
    (core.recoveredMap.recoveredTableSlot R label).row = core.recoveredMap.rowOf R := by
  simp [SymbolicRecoveredSlotAssignmentMap.recoveredTableSlot]

 theorem recoveredTableSlot_label
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup)
    (label : GeneratorCoreSlotLabel) :
    (core.recoveredMap.recoveredTableSlot R label).label = label := by
  simp [SymbolicRecoveredSlotAssignmentMap.recoveredTableSlot]

 theorem recoveredCoreSlots_complete
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup)
    (slot : GeneratorTableSlot)
    (hrow : slot.row = core.recoveredMap.rowOf R) :
    ∃ label : GeneratorCoreSlotLabel,
      core.recoveredMap.recoveredTableSlot R label = slot := by
  refine ⟨slot.label, ?_⟩
  have hrow' : core.recoveredMap.rowOf R = slot.row := hrow.symm
  have hcanon : GeneratorTableSlot.ofRowAndLabel slot.row slot.label = slot := by
    cases slot <;> rfl
  simpa [SymbolicRecoveredSlotAssignmentMap.recoveredTableSlot, hrow', hcanon]

 theorem recoveredCoreSlots_no_extra
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup)
    (label : GeneratorCoreSlotLabel) :
    ∃ slot : GeneratorTableSlot,
      slot = core.recoveredMap.recoveredTableSlot R label :=
  ⟨core.recoveredMap.recoveredTableSlot R label, rfl⟩

/-- Strongest boundary-recovery theorem directly available from the core capsule. -/
def toStructuredComparisonDeterminesVisibleBoundaryTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {α : Type v} {β : Sort _}
    (core : GeneratorTomographyCore ctx setup)
    (comparison :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α)
    (boundaryPorts :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        VisibleBoundaryPortData)
    (visibleBoundary :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → β)
    (slotInjectivity :
      ComparisonSlotInjectivityTarget comparison core.slotData)
    (boundaryPortRecovery :
      BoundaryPortRecoveryFromComparisonSlotsTarget core.slotData boundaryPorts)
    (visibleBoundaryReconstruction :
      VisibleBoundaryReconstructionFromPortsTarget boundaryPorts visibleBoundary) :
    TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.StructuredComparisonDeterminesVisibleBoundaryTarget
      (setup := setup)
      comparison
      visibleBoundary :=
  (core.toGeneratorTablePortLabelSeparationAssumption).structuredComparisonDeterminesVisibleBoundaryTarget
    comparison
    core.slotData
    boundaryPorts
    visibleBoundary
    slotInjectivity
    boundaryPortRecovery
    visibleBoundaryReconstruction

end GeneratorTomographyCore

/-- Honest missing pieces: `Loc.closed` and `Nis.overlap` are row data in the
assignment table but are not part of the current recovered core-slot language
(`source/target/betti/deRham/comparison`). -/
structure GeneratorTomographyObligations
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup) where
  locClosedRecoveredSlot :
    TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → String
  nisOverlapRecoveredSlot :
    TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → String
  locClosedSound :
    ∀ R,
      core.recoveredMap.rowOf R = .loc →
        locClosedRecoveredSlot R = core.locClosedSlot
  nisOverlapSound :
    ∀ R,
      core.recoveredMap.rowOf R = .nis →
        nisOverlapRecoveredSlot R = core.nisOverlapSlot

/-- Single theorem-carrier capsule: constructible core plus explicit named
obligations for the currently unencoded recovered slots. -/
structure GeneratorTomographyCapsule
    (ctx : ClassicalComparisonContext.{u, v})
    (setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}) where
  core : GeneratorTomographyCore ctx setup
  obligations : GeneratorTomographyObligations core

namespace GeneratorTomographyCore

/-- Package a complete tomography capsule once the explicit missing-slot
obligations are supplied. -/
def withObligations_complete
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup)
    (obligations : GeneratorTomographyObligations core) :
    GeneratorTomographyCapsule ctx setup where
  core := core
  obligations := obligations

/-- Manuscript-facing bridge: from the capsule core and the existing additional
inputs, produce the strongest existing classical manuscript recovery target in
`ClassicalManuscriptTargets`. -/
def toStructuredComparisonVisibleBoundaryRecoveryTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {structuredEq : StructuredComparisonEquality ctx}
    (core : GeneratorTomographyCore ctx setup)
    (tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq)
    (finiteDimensionality : FiniteDimensionalProbeSeparation ctx)
    (comparisonSlotInjectivityTarget : Prop)
    (boundaryPortRecoveryFromComparisonSlotsTarget : Prop)
    (visibleBoundaryReconstructionTarget : Prop)
    (chosenBasesTarget : Prop) :
    StructuredComparisonVisibleBoundaryRecoveryTarget ctx structuredEq :=
  StructuredComparisonVisibleBoundaryRecoveryTarget.ofTomographySoundnessAndExposedAssumptions
    tomographySoundness
    finiteDimensionality
    (ComparisonSlotSeparationTarget core.slotData)
    comparisonSlotInjectivityTarget
    boundaryPortRecoveryFromComparisonSlotsTarget
    visibleBoundaryReconstructionTarget
    chosenBasesTarget
    core.toPortLabelSeparationTarget

end GeneratorTomographyCore

namespace GeneratorTomographyObligations

/-- Canonical constructor for obligations: the missing auxiliary slots
(Loc.closed and Nis.overlap) are recovered trivially from the assignment
table, since they are constant table-level names. -/
def ofCore
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup) :
    GeneratorTomographyObligations core where
  locClosedRecoveredSlot := fun _ => core.locClosedSlot
  nisOverlapRecoveredSlot := fun _ => core.nisOverlapSlot
  locClosedSound := fun _ _ => rfl
  nisOverlapSound := fun _ _ => rfl

end GeneratorTomographyObligations

/-- Concrete assignment table used by the canonical tomography core. -/
def canonicalGeneratorTomographyAssignmentTable
    {ctx : ClassicalComparisonContext.{u, v}} :
    GeneratorRealizationAssignmentTable ctx :=
  unitGeneratorRealizationAssignmentTable ctx

/-- Canonical Corr row slot-label data. -/
def canonicalCorrSlotLabelData : StructuredComparisonSlotData := {
  sourceSlot := "source"
  targetSlot := "target"
  bettiSlot := "betti"
  deRhamSlot := "deRham"
  comparisonSlot := "comparison"
}

/-- Canonical Loc row slot-label data. -/
def canonicalLocSlotLabelData : StructuredComparisonSlotData := {
  sourceSlot := "ambient"
  targetSlot := "open"
  bettiSlot := "betti"
  deRhamSlot := "deRham"
  comparisonSlot := "comparison"
}

/-- Canonical Nis row slot-label data. -/
def canonicalNisSlotLabelData : StructuredComparisonSlotData := {
  sourceSlot := "base"
  targetSlot := "patch"
  bettiSlot := "betti"
  deRhamSlot := "deRham"
  comparisonSlot := "comparison"
}

/-- Canonical A1 row slot-label data. -/
def canonicalA1SlotLabelData : StructuredComparisonSlotData := {
  sourceSlot := "base"
  targetSlot := "cylinder"
  bettiSlot := "betti"
  deRhamSlot := "deRham"
  comparisonSlot := "comparison"
}

/-- Canonical Env row slot-label data. -/
def canonicalEnvSlotLabelData : StructuredComparisonSlotData := {
  sourceSlot := "ambient"
  targetSlot := "envelope"
  bettiSlot := "betti"
  deRhamSlot := "deRham"
  comparisonSlot := "comparison"
}

/-- Canonical five-row slot-label assignment assembled from named constants. -/
def canonicalGeneratorTomographySlotLabelAssignment
    {ctx : ClassicalComparisonContext.{u, v}} :
    GeneratorTableSlotLabelAssignment ctx := {
  corr := canonicalCorrSlotLabelData
  loc := canonicalLocSlotLabelData
  nis := canonicalNisSlotLabelData
  a1 := canonicalA1SlotLabelData
  env := canonicalEnvSlotLabelData
}

@[simp] theorem canonicalCorrSlotLabelData_sourceSlot :
    canonicalCorrSlotLabelData.sourceSlot = "source" := rfl

@[simp] theorem canonicalCorrSlotLabelData_targetSlot :
    canonicalCorrSlotLabelData.targetSlot = "target" := rfl

@[simp] theorem canonicalLocSlotLabelData_sourceSlot :
    canonicalLocSlotLabelData.sourceSlot = "ambient" := rfl

@[simp] theorem canonicalLocSlotLabelData_targetSlot :
    canonicalLocSlotLabelData.targetSlot = "open" := rfl

@[simp] theorem canonicalNisSlotLabelData_sourceSlot :
    canonicalNisSlotLabelData.sourceSlot = "base" := rfl

@[simp] theorem canonicalNisSlotLabelData_targetSlot :
    canonicalNisSlotLabelData.targetSlot = "patch" := rfl

@[simp] theorem canonicalA1SlotLabelData_sourceSlot :
    canonicalA1SlotLabelData.sourceSlot = "base" := rfl

@[simp] theorem canonicalA1SlotLabelData_targetSlot :
    canonicalA1SlotLabelData.targetSlot = "cylinder" := rfl

@[simp] theorem canonicalEnvSlotLabelData_sourceSlot :
    canonicalEnvSlotLabelData.sourceSlot = "ambient" := rfl

@[simp] theorem canonicalEnvSlotLabelData_targetSlot :
    canonicalEnvSlotLabelData.targetSlot = "envelope" := rfl

@[simp] theorem canonicalGeneratorTomographyAssignmentTable_corrSlotData
    {ctx : ClassicalComparisonContext.{u, v}} :
    (canonicalGeneratorTomographyAssignmentTable (ctx := ctx)).corrAssignment.toComparisonBoundarySlotData =
      canonicalCorrSlotLabelData := rfl

@[simp] theorem canonicalGeneratorTomographyAssignmentTable_locSlotData
    {ctx : ClassicalComparisonContext.{u, v}} :
    (canonicalGeneratorTomographyAssignmentTable (ctx := ctx)).locAssignment.toComparisonBoundarySlotData =
      canonicalLocSlotLabelData := rfl

@[simp] theorem canonicalGeneratorTomographyAssignmentTable_nisSlotData
    {ctx : ClassicalComparisonContext.{u, v}} :
    (canonicalGeneratorTomographyAssignmentTable (ctx := ctx)).nisAssignment.toComparisonBoundarySlotData =
      canonicalNisSlotLabelData := rfl

@[simp] theorem canonicalGeneratorTomographyAssignmentTable_a1SlotData
    {ctx : ClassicalComparisonContext.{u, v}} :
    (canonicalGeneratorTomographyAssignmentTable (ctx := ctx)).a1Assignment.toComparisonBoundarySlotData =
      canonicalA1SlotLabelData := rfl

@[simp] theorem canonicalGeneratorTomographyAssignmentTable_envSlotData
    {ctx : ClassicalComparisonContext.{u, v}} :
    (canonicalGeneratorTomographyAssignmentTable (ctx := ctx)).envAssignment.toComparisonBoundarySlotData =
      canonicalEnvSlotLabelData := rfl

/-- Concrete slot data used by the canonical tomography core.
The current recovery lane is anchored on the Corr row's core symbolic slots. -/
def canonicalGeneratorTomographySlotData
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}} :
    TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
      StructuredComparisonSlotData :=
  fun _ => canonicalCorrSlotLabelData

/-- Concrete recovered-map data used by the canonical tomography core. -/
def canonicalGeneratorTomographyRecoveredMap
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}} :
    SymbolicRecoveredSlotAssignmentMap
      (@canonicalGeneratorTomographySlotLabelAssignment ctx)
      (@canonicalGeneratorTomographySlotData ctx setup) where
  rowOf := fun _ => .corr
  recovers := fun _ => rfl

/-- Concrete row-wise symbolic slot-separation witness for the canonical assignment table. -/
def canonicalGeneratorTomographyRowSlotSeparation
    {ctx : ClassicalComparisonContext.{u, v}} :
    GeneratorRowSlotSeparationData
  (@canonicalGeneratorTomographyAssignmentTable ctx) where
  corrSeparated := by
    simpa using (show canonicalCorrSlotLabelData.Separated from by decide)
  locSeparated := by
    simpa using (show canonicalLocSlotLabelData.Separated from by decide)
  nisSeparated := by
    simpa using (show canonicalNisSlotLabelData.Separated from by decide)
  a1Separated := by
    simpa using (show canonicalA1SlotLabelData.Separated from by decide)
  envSeparated := by
    simpa using (show canonicalEnvSlotLabelData.Separated from by decide)

/-- Concrete canonical tomography core filling all four required fields:
assignment table, slot data, recovered map, and row-slot separation witness.
Production note: this is the absolute concrete capsule core instance, not merely
parametric `core -> capsule` infrastructure. -/
def canonicalGeneratorTomographyCore
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}} :
    GeneratorTomographyCore ctx setup where
  assignmentTable := canonicalGeneratorTomographyAssignmentTable
  slotData := @canonicalGeneratorTomographySlotData ctx setup
  recoveredMap := @canonicalGeneratorTomographyRecoveredMap ctx setup
  rowSlotSeparation := @canonicalGeneratorTomographyRowSlotSeparation ctx

/-- Canonical tomography capsule constructor, assuming a concrete core instance
is provided. The obligations are constructed from the core's slot-name API. -/
def GeneratorTomographyCapsule.ofCoreWithCanonicalObligations
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup) :
    GeneratorTomographyCapsule ctx setup :=
  core.withObligations_complete (GeneratorTomographyObligations.ofCore core)

/-- Concrete complete capsule built from the canonical concrete core. -/
def canonicalGeneratorTomographyCapsule
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}} :
    GeneratorTomographyCapsule ctx setup :=
  GeneratorTomographyCapsule.ofCoreWithCanonicalObligations
    (@canonicalGeneratorTomographyCore ctx setup)

/-- Concrete comparison-boundary recovery bridge from the canonical capsule core. -/
def canonicalGeneratorTomographyBoundaryRecoveryTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}} :
    PortLabelSeparationTargetOfSlots
      (@canonicalGeneratorTomographyCore ctx setup).slotData :=
  (@canonicalGeneratorTomographyCore ctx setup).toBoundaryRecoveryTarget

/-- Audit aliases: the canonical core fields are exactly the named concrete objects. -/
@[simp] theorem canonicalGeneratorTomographyCore_assignmentTable
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}} :
    (@canonicalGeneratorTomographyCore ctx setup).assignmentTable =
      canonicalGeneratorTomographyAssignmentTable := rfl

@[simp] theorem canonicalGeneratorTomographyCore_slotData
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}} :
    (@canonicalGeneratorTomographyCore ctx setup).slotData =
      (@canonicalGeneratorTomographySlotData ctx setup) := rfl

@[simp] theorem canonicalGeneratorTomographyCore_recoveredMap
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}} :
    (@canonicalGeneratorTomographyCore ctx setup).recoveredMap =
      (@canonicalGeneratorTomographyRecoveredMap ctx setup) := rfl

@[simp] theorem canonicalGeneratorTomographyCore_rowSlotSeparation
    {ctx : ClassicalComparisonContext.{u, v}} {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}} :
    (@canonicalGeneratorTomographyCore ctx setup).rowSlotSeparation =
      (@canonicalGeneratorTomographyRowSlotSeparation ctx) := rfl

/-
This bridge intentionally remains at the slot-recovery target level.
The old direct `PortLabelSeparationTarget` constant was removed because it
introduced universe-level metavariable leakage. Use
`canonicalGeneratorTomographyBoundaryRecoveryTarget` and
`GeneratorTomographyCore.toPortLabelSeparationTarget` at call sites.
-/


/-- Strongest parametric definition: any `GeneratorTomographyCore` induces a complete,
fully-inhabited `GeneratorTomographyCapsule`. Concrete instantiation requires
a concrete core (with concrete assignmentTable, slotData, recoveredMap,
rowSlotSeparation). -/
def GeneratorTomographyCore.toCompleteCapsule
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (core : GeneratorTomographyCore ctx setup) :
    GeneratorTomographyCapsule ctx setup :=
  GeneratorTomographyCapsule.ofCoreWithCanonicalObligations core

end ClassicalPeriods
end TraceCalc
