import TraceCalc.ClassicalPeriods.ComparisonBoundaryRecovery
import TraceCalc.ClassicalPeriods.ManuscriptTargetSupport
import TraceCalc.ClassicalPeriods.PeriodConjectureTarget

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

/-- Decomposition target for the "same generator families" slice of
`thm:core-presentation-equivalence`. This sits directly on top of the existing
named generator-family package. -/
structure CommonGeneratorFamilyTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  generatorPackage : GeometricGeneratorFamilyPackage ctx
  sameGeneratorFamiliesTarget : Prop
  corrFamilyAgreementTarget : Prop
  locFamilyAgreementTarget : Prop
  nisFamilyAgreementTarget : Prop
  a1FamilyAgreementTarget : Prop
  envFamilyAgreementTarget : Prop

namespace CommonGeneratorFamilyTarget

def ofGeneratorPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (generatorPackage : GeometricGeneratorFamilyPackage ctx)
    (sameGeneratorFamiliesTarget corrFamilyAgreementTarget locFamilyAgreementTarget
      nisFamilyAgreementTarget a1FamilyAgreementTarget envFamilyAgreementTarget : Prop) :
    CommonGeneratorFamilyTarget ctx where
  generatorPackage := generatorPackage
  sameGeneratorFamiliesTarget := sameGeneratorFamiliesTarget
  corrFamilyAgreementTarget := corrFamilyAgreementTarget
  locFamilyAgreementTarget := locFamilyAgreementTarget
  nisFamilyAgreementTarget := nisFamilyAgreementTarget
  a1FamilyAgreementTarget := a1FamilyAgreementTarget
  envFamilyAgreementTarget := envFamilyAgreementTarget

def ofAssignmentTable
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx)
    (sameGeneratorFamiliesTarget corrFamilyAgreementTarget locFamilyAgreementTarget
      nisFamilyAgreementTarget a1FamilyAgreementTarget envFamilyAgreementTarget : Prop) :
    CommonGeneratorFamilyTarget ctx :=
  ofGeneratorPackage assignmentTable.toGeometricGeneratorFamilyPackage
    sameGeneratorFamiliesTarget corrFamilyAgreementTarget locFamilyAgreementTarget
    nisFamilyAgreementTarget a1FamilyAgreementTarget envFamilyAgreementTarget

@[simp] theorem ofAssignmentTable_generatorPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx)
    (sameGeneratorFamiliesTarget corrFamilyAgreementTarget locFamilyAgreementTarget
      nisFamilyAgreementTarget a1FamilyAgreementTarget envFamilyAgreementTarget : Prop) :
    (ofAssignmentTable assignmentTable sameGeneratorFamiliesTarget corrFamilyAgreementTarget
      locFamilyAgreementTarget nisFamilyAgreementTarget a1FamilyAgreementTarget
      envFamilyAgreementTarget).generatorPackage =
        assignmentTable.toGeometricGeneratorFamilyPackage :=
  rfl

end CommonGeneratorFamilyTarget

/-- Decomposition target for the "same relation families" slice of
`thm:core-presentation-equivalence`. This is intentionally stated at the
localization-package level. -/
structure CommonRelationFamilyTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  localizationPackage : GeometricLocalizationPackage ctx
  sameRelationFamiliesTarget : Prop
  corrRelationAgreementTarget : Prop
  locRelationAgreementTarget : Prop
  nisRelationAgreementTarget : Prop
  a1RelationAgreementTarget : Prop
  envRelationAgreementTarget : Prop

namespace CommonRelationFamilyTarget

def ofLocalizationPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (localizationPackage : GeometricLocalizationPackage ctx)
    (sameRelationFamiliesTarget corrRelationAgreementTarget locRelationAgreementTarget
      nisRelationAgreementTarget a1RelationAgreementTarget envRelationAgreementTarget : Prop) :
    CommonRelationFamilyTarget ctx where
  localizationPackage := localizationPackage
  sameRelationFamiliesTarget := sameRelationFamiliesTarget
  corrRelationAgreementTarget := corrRelationAgreementTarget
  locRelationAgreementTarget := locRelationAgreementTarget
  nisRelationAgreementTarget := nisRelationAgreementTarget
  a1RelationAgreementTarget := a1RelationAgreementTarget
  envRelationAgreementTarget := envRelationAgreementTarget

def ofAssignmentTable
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx)
    (sameRelationFamiliesTarget corrRelationAgreementTarget locRelationAgreementTarget
      nisRelationAgreementTarget a1RelationAgreementTarget envRelationAgreementTarget : Prop) :
    CommonRelationFamilyTarget ctx :=
  ofLocalizationPackage assignmentTable.toGeometricLocalizationPackage
    sameRelationFamiliesTarget corrRelationAgreementTarget locRelationAgreementTarget
    nisRelationAgreementTarget a1RelationAgreementTarget envRelationAgreementTarget

@[simp] theorem ofAssignmentTable_localizationPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx)
    (sameRelationFamiliesTarget corrRelationAgreementTarget locRelationAgreementTarget
      nisRelationAgreementTarget a1RelationAgreementTarget envRelationAgreementTarget : Prop) :
    (ofAssignmentTable assignmentTable sameRelationFamiliesTarget corrRelationAgreementTarget
      locRelationAgreementTarget nisRelationAgreementTarget a1RelationAgreementTarget
      envRelationAgreementTarget).localizationPackage =
        assignmentTable.toGeometricLocalizationPackage :=
  rfl

end CommonRelationFamilyTarget

/-- Decomposition target for the soundness direction of the trace-to-geometric
packet interpretation. The existing packet-equivalence target is kept as the
carrier so downstream code does not need a second realization interface. -/
structure PrimitiveGeometricPacketFamilySoundnessTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  tracePacketEquivalence : TraceToGeometricPacketEquivalenceTarget ctx
  traceToGeometricPacketSoundnessTarget : Prop
  corrPacketSoundnessTarget : Prop
  locPacketSoundnessTarget : Prop
  nisPacketSoundnessTarget : Prop
  a1PacketSoundnessTarget : Prop
  envPacketSoundnessTarget : Prop
  assignmentTableCompatibilityTarget : Prop

/-- Narrow Corr-row soundness target already backed by concrete generator
realization data. This states only the row-wise packet facts presently exposed
by `GeneratorRealizationAssignmentTable`, without claiming the other four
families are closed. -/
def CorrPacketSoundnessFromGeneratorRealizationTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) : Prop :=
  ∀ gen : assignmentTable.corrAssignment.family.GeneratorIndex,
    (assignmentTable.corrAssignment.family.generatorCorrespondence gen).correspondenceTarget ∧
      (assignmentTable.corrAssignment.sourceComparisonDatum gen).grothendieckComparisonTarget ∧
      (assignmentTable.corrAssignment.targetComparisonDatum gen).grothendieckComparisonTarget

theorem corrPacketSoundnessFromGeneratorRealization
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    CorrPacketSoundnessFromGeneratorRealizationTarget assignmentTable := by
  intro gen
  exact
    ⟨assignmentTable.corrAssignment.family.correspondenceTarget gen,
      assignmentTable.corrAssignment.sourceGrothendieckComparisonTarget gen,
      assignmentTable.corrAssignment.targetGrothendieckComparisonTarget gen⟩

/-- Narrow proof-backed Loc-row target extracted from concrete generator
realization data. The per-generator ambient/open/closed period-compatibility is
available now, but the remaining lower-level triangle blocker should
ultimately be discharged by trace-native sink-peel / replay data
(`CertifiedLocPacketReplayData`) rather than by a standalone cone API. -/
def LocPacketPeriodCompatibilityFromGeneratorRealizationTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) : Prop :=
  ∀ gen : assignmentTable.locAssignment.family.GeneratorIndex,
    (assignmentTable.locAssignment.ambientComparisonDatum gen).periodCompatibilityTarget ∧
      (assignmentTable.locAssignment.openComparisonDatum gen).periodCompatibilityTarget ∧
      (assignmentTable.locAssignment.closedComparisonDatum gen).periodCompatibilityTarget

theorem locPacketPeriodCompatibilityFromGeneratorRealization
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    LocPacketPeriodCompatibilityFromGeneratorRealizationTarget assignmentTable := by
  intro gen
  exact
    ⟨assignmentTable.locAssignment.ambientPeriodCompatibilityTarget gen,
      assignmentTable.locAssignment.openPeriodCompatibilityTarget gen,
      assignmentTable.locAssignment.closedPeriodCompatibilityTarget gen⟩

theorem locTriangleCompatibilityFromGeneratorRealization
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    assignmentTable.locAssignment.triangleCompatibilityTarget :=
  assignmentTable.locAssignment.triangleCompatibilityFromCertifiedReplay

theorem locConnectingPacket_comparison_naturality_from_replay
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    assignmentTable.locAssignment.coneNaturalityData.connectingMorphismCompatibilityTarget :=
  assignmentTable.locAssignment.locConnectingPacket_comparison_naturality_from_replay

theorem locTriangleCompatibility_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    assignmentTable.locAssignment.triangleCompatibilityTarget :=
  assignmentTable.locAssignment.triangleCompatibilityFromCertifiedReplay

theorem locPacketSoundness_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    LocPacketPeriodCompatibilityFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.locAssignment.triangleCompatibilityTarget := by
  exact ⟨locPacketPeriodCompatibilityFromGeneratorRealization assignmentTable,
    locTriangleCompatibility_from_certifiedReplay assignmentTable⟩

theorem locPacketSoundnessFromGeneratorRealization
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    LocPacketPeriodCompatibilityFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.locAssignment.triangleCompatibilityTarget := by
  exact locPacketSoundness_from_certifiedReplay assignmentTable

/-- Replay-native Nis-row target extracted from concrete generator realization data. -/
def NisPacketComparisonFromGeneratorRealizationTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) : Prop :=
  ∀ gen : assignmentTable.nisAssignment.family.GeneratorIndex,
    (assignmentTable.nisAssignment.baseComparisonDatum gen).grothendieckComparisonTarget ∧
      (assignmentTable.nisAssignment.patchComparisonDatum gen).grothendieckComparisonTarget ∧
      (assignmentTable.nisAssignment.overlapComparisonDatum gen).grothendieckComparisonTarget

theorem nisPacketComparisonFromGeneratorRealization
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    NisPacketComparisonFromGeneratorRealizationTarget assignmentTable :=
  assignmentTable.nisAssignment.nisOverlapAgreement_from_certifiedReplay

theorem nisOverlapAgreement_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    NisPacketComparisonFromGeneratorRealizationTarget assignmentTable :=
  assignmentTable.nisAssignment.nisOverlapAgreement_from_certifiedReplay

theorem nisDescentSquareCompatibility_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    assignmentTable.nisAssignment.descentSquareCompatibilityTarget :=
  assignmentTable.nisAssignment.nisDescentSquareCompatibility_from_certifiedReplay

theorem nisPacketSoundness_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    NisPacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.nisAssignment.descentSquareCompatibilityTarget := by
  exact ⟨nisPacketComparisonFromGeneratorRealization assignmentTable,
    nisDescentSquareCompatibility_from_certifiedReplay assignmentTable⟩

theorem nisPacketSoundnessFromGeneratorRealization
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    NisPacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.nisAssignment.descentSquareCompatibilityTarget := by
  exact nisPacketSoundness_from_certifiedReplay assignmentTable

/-- Replay-native A1-row target extracted from concrete generator realization data. -/
def A1PacketComparisonFromGeneratorRealizationTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) : Prop :=
  ∀ gen : assignmentTable.a1Assignment.family.GeneratorIndex,
    (assignmentTable.a1Assignment.baseComparisonDatum gen).grothendieckComparisonTarget ∧
      (assignmentTable.a1Assignment.cylinderComparisonDatum gen).grothendieckComparisonTarget ∧
      (assignmentTable.a1Assignment.baseComparisonDatum gen).periodCompatibilityTarget ∧
      (assignmentTable.a1Assignment.cylinderComparisonDatum gen).periodCompatibilityTarget

theorem a1EndpointAgreement_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    A1PacketComparisonFromGeneratorRealizationTarget assignmentTable :=
  assignmentTable.a1Assignment.a1EndpointAgreement_from_certifiedReplay

theorem a1HomotopyInvariance_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    assignmentTable.a1Assignment.framedExtractionTarget :=
  assignmentTable.a1Assignment.a1HomotopyInvariance_from_certifiedReplay

theorem a1PacketSoundness_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    A1PacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.a1Assignment.framedExtractionTarget := by
  exact ⟨a1EndpointAgreement_from_certifiedReplay assignmentTable,
    a1HomotopyInvariance_from_certifiedReplay assignmentTable⟩

theorem a1PacketSoundnessFromGeneratorRealization
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    A1PacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.a1Assignment.framedExtractionTarget := by
  exact a1PacketSoundness_from_certifiedReplay assignmentTable

/-- Replay-native Env-row target extracted from concrete generator realization data. -/
def EnvPacketComparisonFromGeneratorRealizationTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) : Prop :=
  ∀ gen : assignmentTable.envAssignment.family.GeneratorIndex,
    (assignmentTable.envAssignment.ambientComparisonDatum gen).grothendieckComparisonTarget ∧
      (assignmentTable.envAssignment.envelopeComparisonDatum gen).grothendieckComparisonTarget ∧
      (assignmentTable.envAssignment.ambientComparisonDatum gen).periodCompatibilityTarget ∧
      (assignmentTable.envAssignment.envelopeComparisonDatum gen).periodCompatibilityTarget

theorem envComparisonAgreement_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    EnvPacketComparisonFromGeneratorRealizationTarget assignmentTable :=
  assignmentTable.envAssignment.envComparisonAgreement_from_certifiedReplay

theorem envFormalClosureSoundness_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    assignmentTable.envAssignment.exactCompletionTarget :=
  assignmentTable.envAssignment.envFormalClosureSoundness_from_certifiedReplay

theorem envPacketSoundness_from_certifiedReplay
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    EnvPacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.envAssignment.exactCompletionTarget := by
  exact ⟨envComparisonAgreement_from_certifiedReplay assignmentTable,
    envFormalClosureSoundness_from_certifiedReplay assignmentTable⟩

theorem envPacketSoundnessFromGeneratorRealization
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    EnvPacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.envAssignment.exactCompletionTarget := by
  exact envPacketSoundness_from_certifiedReplay assignmentTable

namespace PrimitiveGeometricPacketFamilySoundnessTarget

def ofPacketEquivalence
    {ctx : ClassicalComparisonContext.{u, v}}
    (tracePacketEquivalence : TraceToGeometricPacketEquivalenceTarget ctx)
    (traceToGeometricPacketSoundnessTarget corrPacketSoundnessTarget
      locPacketSoundnessTarget nisPacketSoundnessTarget a1PacketSoundnessTarget
      envPacketSoundnessTarget assignmentTableCompatibilityTarget : Prop) :
    PrimitiveGeometricPacketFamilySoundnessTarget ctx where
  tracePacketEquivalence := tracePacketEquivalence
  traceToGeometricPacketSoundnessTarget := traceToGeometricPacketSoundnessTarget
  corrPacketSoundnessTarget := corrPacketSoundnessTarget
  locPacketSoundnessTarget := locPacketSoundnessTarget
  nisPacketSoundnessTarget := nisPacketSoundnessTarget
  a1PacketSoundnessTarget := a1PacketSoundnessTarget
  envPacketSoundnessTarget := envPacketSoundnessTarget
  assignmentTableCompatibilityTarget := assignmentTableCompatibilityTarget

@[simp] theorem ofPacketEquivalence_corrPacketSoundnessTarget_fromGeneratorRealization
    {ctx : ClassicalComparisonContext.{u, v}}
    (tracePacketEquivalence : TraceToGeometricPacketEquivalenceTarget ctx)
    (assignmentTable : GeneratorRealizationAssignmentTable ctx)
    (traceToGeometricPacketSoundnessTarget locPacketSoundnessTarget
      nisPacketSoundnessTarget a1PacketSoundnessTarget envPacketSoundnessTarget
      assignmentTableCompatibilityTarget : Prop) :
    (ofPacketEquivalence
      tracePacketEquivalence
      traceToGeometricPacketSoundnessTarget
      (CorrPacketSoundnessFromGeneratorRealizationTarget assignmentTable)
      locPacketSoundnessTarget
      nisPacketSoundnessTarget
      a1PacketSoundnessTarget
      envPacketSoundnessTarget
      assignmentTableCompatibilityTarget).corrPacketSoundnessTarget =
        CorrPacketSoundnessFromGeneratorRealizationTarget assignmentTable := by
  rfl

@[simp] theorem ofPacketEquivalence_locPacketSoundnessTarget_fromGeneratorRealizationPeriodCompatibility
    {ctx : ClassicalComparisonContext.{u, v}}
    (tracePacketEquivalence : TraceToGeometricPacketEquivalenceTarget ctx)
    (assignmentTable : GeneratorRealizationAssignmentTable ctx)
    (traceToGeometricPacketSoundnessTarget corrPacketSoundnessTarget
      nisPacketSoundnessTarget a1PacketSoundnessTarget envPacketSoundnessTarget
      assignmentTableCompatibilityTarget : Prop) :
    (ofPacketEquivalence
      tracePacketEquivalence
      traceToGeometricPacketSoundnessTarget
      corrPacketSoundnessTarget
      (LocPacketPeriodCompatibilityFromGeneratorRealizationTarget assignmentTable)
      nisPacketSoundnessTarget
      a1PacketSoundnessTarget
      envPacketSoundnessTarget
      assignmentTableCompatibilityTarget).locPacketSoundnessTarget =
        LocPacketPeriodCompatibilityFromGeneratorRealizationTarget assignmentTable := by
  rfl

@[simp] theorem ofPacketEquivalence_locPacketSoundnessTarget_fromGeneratorRealization
    {ctx : ClassicalComparisonContext.{u, v}}
    (tracePacketEquivalence : TraceToGeometricPacketEquivalenceTarget ctx)
    (assignmentTable : GeneratorRealizationAssignmentTable ctx)
    (traceToGeometricPacketSoundnessTarget corrPacketSoundnessTarget
      nisPacketSoundnessTarget a1PacketSoundnessTarget envPacketSoundnessTarget
      assignmentTableCompatibilityTarget : Prop) :
    (ofPacketEquivalence
      tracePacketEquivalence
      traceToGeometricPacketSoundnessTarget
      corrPacketSoundnessTarget
      (LocPacketPeriodCompatibilityFromGeneratorRealizationTarget assignmentTable ∧
        assignmentTable.locAssignment.triangleCompatibilityTarget)
      nisPacketSoundnessTarget
      a1PacketSoundnessTarget
      envPacketSoundnessTarget
      assignmentTableCompatibilityTarget).locPacketSoundnessTarget =
        (LocPacketPeriodCompatibilityFromGeneratorRealizationTarget assignmentTable ∧
          assignmentTable.locAssignment.triangleCompatibilityTarget) := by
  rfl

end PrimitiveGeometricPacketFamilySoundnessTarget

/-- Decomposition target for the soundness direction of the trace-to-geometric
packet interpretation. The existing packet-equivalence target is kept as the
carrier so downstream code does not need a second realization interface. -/
structure TraceToGeometricSoundnessTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  tracePacketEquivalence : TraceToGeometricPacketEquivalenceTarget ctx
  traceToGeometricPacketSoundnessTarget : Prop
  corrPacketSoundnessTarget : Prop
  locPacketSoundnessTarget : Prop
  nisPacketSoundnessTarget : Prop
  a1PacketSoundnessTarget : Prop
  envPacketSoundnessTarget : Prop
  assignmentTableCompatibilityTarget : Prop

namespace TraceToGeometricSoundnessTarget

def ofPacketEquivalence
    {ctx : ClassicalComparisonContext.{u, v}}
    (tracePacketEquivalence : TraceToGeometricPacketEquivalenceTarget ctx)
    (traceToGeometricPacketSoundnessTarget corrPacketSoundnessTarget
      locPacketSoundnessTarget nisPacketSoundnessTarget a1PacketSoundnessTarget
      envPacketSoundnessTarget assignmentTableCompatibilityTarget : Prop) :
    TraceToGeometricSoundnessTarget ctx where
  tracePacketEquivalence := tracePacketEquivalence
  traceToGeometricPacketSoundnessTarget := traceToGeometricPacketSoundnessTarget
  corrPacketSoundnessTarget := corrPacketSoundnessTarget
  locPacketSoundnessTarget := locPacketSoundnessTarget
  nisPacketSoundnessTarget := nisPacketSoundnessTarget
  a1PacketSoundnessTarget := a1PacketSoundnessTarget
  envPacketSoundnessTarget := envPacketSoundnessTarget
  assignmentTableCompatibilityTarget := assignmentTableCompatibilityTarget

def ofPrimitivePacketFamilySoundness
    {ctx : ClassicalComparisonContext.{u, v}}
    (packetFamilySoundness : PrimitiveGeometricPacketFamilySoundnessTarget ctx) :
    TraceToGeometricSoundnessTarget ctx :=
  ofPacketEquivalence
    packetFamilySoundness.tracePacketEquivalence
    packetFamilySoundness.traceToGeometricPacketSoundnessTarget
    packetFamilySoundness.corrPacketSoundnessTarget
    packetFamilySoundness.locPacketSoundnessTarget
    packetFamilySoundness.nisPacketSoundnessTarget
    packetFamilySoundness.a1PacketSoundnessTarget
    packetFamilySoundness.envPacketSoundnessTarget
    packetFamilySoundness.assignmentTableCompatibilityTarget

def primitivePacketFamilySoundness
    {ctx : ClassicalComparisonContext.{u, v}}
    (soundness : TraceToGeometricSoundnessTarget ctx) :
    PrimitiveGeometricPacketFamilySoundnessTarget ctx :=
  PrimitiveGeometricPacketFamilySoundnessTarget.ofPacketEquivalence
    soundness.tracePacketEquivalence
    soundness.traceToGeometricPacketSoundnessTarget
    soundness.corrPacketSoundnessTarget
    soundness.locPacketSoundnessTarget
    soundness.nisPacketSoundnessTarget
    soundness.a1PacketSoundnessTarget
    soundness.envPacketSoundnessTarget
    soundness.assignmentTableCompatibilityTarget

@[simp] theorem ofPrimitivePacketFamilySoundness_tracePacketEquivalence
    {ctx : ClassicalComparisonContext.{u, v}}
    (packetFamilySoundness : PrimitiveGeometricPacketFamilySoundnessTarget ctx) :
    (ofPrimitivePacketFamilySoundness packetFamilySoundness).tracePacketEquivalence =
      packetFamilySoundness.tracePacketEquivalence :=
  rfl

@[simp] theorem primitivePacketFamilySoundness_tracePacketEquivalence
    {ctx : ClassicalComparisonContext.{u, v}}
    (soundness : TraceToGeometricSoundnessTarget ctx) :
    soundness.primitivePacketFamilySoundness.tracePacketEquivalence =
      soundness.tracePacketEquivalence :=
  rfl

end TraceToGeometricSoundnessTarget

/-- Decomposition target for completeness / essential surjectivity of the
geometric packet presentation. -/
structure GeometricPresentationCompletenessTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  operationalPresentation : OperationalGeometricPresentationTarget ctx
  geometricPresentationCompletenessTarget : Prop
  essentialSurjectivityTarget : Prop
  relationGenerationTarget : Prop
  assignmentTableCompatibilityTarget : Prop

namespace GeometricPresentationCompletenessTarget

def ofOperationalPresentation
    {ctx : ClassicalComparisonContext.{u, v}}
    (operationalPresentation : OperationalGeometricPresentationTarget ctx)
    (geometricPresentationCompletenessTarget essentialSurjectivityTarget
      relationGenerationTarget assignmentTableCompatibilityTarget : Prop) :
    GeometricPresentationCompletenessTarget ctx where
  operationalPresentation := operationalPresentation
  geometricPresentationCompletenessTarget := geometricPresentationCompletenessTarget
  essentialSurjectivityTarget := essentialSurjectivityTarget
  relationGenerationTarget := relationGenerationTarget
  assignmentTableCompatibilityTarget := assignmentTableCompatibilityTarget

end GeometricPresentationCompletenessTarget

/-- Combined decomposition record for `thm:core-presentation-equivalence`. This
is the proof-discharge surface immediately below the existing coarse theorem
targets. -/
structure CorePresentationEquivalenceDecompositionTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  commonGenerators : CommonGeneratorFamilyTarget ctx
  commonRelations : CommonRelationFamilyTarget ctx
  traceToGeometricSoundness : TraceToGeometricSoundnessTarget ctx
  presentationCompleteness : GeometricPresentationCompletenessTarget ctx
  corrLocNisA1EnvAssignmentTableCompatibilityTarget : Prop

namespace CorePresentationEquivalenceDecompositionTarget

def toGeometricPresentationTheoremTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (decomposition : CorePresentationEquivalenceDecompositionTarget ctx) :
    GeometricPresentationTheoremTarget ctx where
  operationalPresentation := decomposition.presentationCompleteness.operationalPresentation
  tracePacketEquivalence := decomposition.traceToGeometricSoundness.tracePacketEquivalence
  presentationCompletenessTarget :=
    decomposition.presentationCompleteness.geometricPresentationCompletenessTarget

def commonPresentationTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (decomposition : CorePresentationEquivalenceDecompositionTarget ctx) : Prop :=
  decomposition.commonGenerators.sameGeneratorFamiliesTarget ∧
    decomposition.commonRelations.sameRelationFamiliesTarget ∧
    decomposition.traceToGeometricSoundness.traceToGeometricPacketSoundnessTarget ∧
    decomposition.presentationCompleteness.geometricPresentationCompletenessTarget

@[simp] theorem toGeometricPresentationTheoremTarget_operationalPresentation
    {ctx : ClassicalComparisonContext.{u, v}}
    (decomposition : CorePresentationEquivalenceDecompositionTarget ctx) :
    decomposition.toGeometricPresentationTheoremTarget.operationalPresentation =
      decomposition.presentationCompleteness.operationalPresentation :=
  rfl

@[simp] theorem toGeometricPresentationTheoremTarget_tracePacketEquivalence
    {ctx : ClassicalComparisonContext.{u, v}}
    (decomposition : CorePresentationEquivalenceDecompositionTarget ctx) :
    decomposition.toGeometricPresentationTheoremTarget.tracePacketEquivalence =
      decomposition.traceToGeometricSoundness.tracePacketEquivalence :=
  rfl

end CorePresentationEquivalenceDecompositionTarget

structure FullGeometricComparisonTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  localizationPackage : GeometricLocalizationPackage ctx
  fullComparisonTarget : Prop
  classicalSoundnessTarget : Prop

namespace FullGeometricComparisonTarget

def ofLocalizationPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (localizationPackage : GeometricLocalizationPackage ctx)
    (fullComparisonTarget classicalSoundnessTarget : Prop) :
    FullGeometricComparisonTarget ctx where
  localizationPackage := localizationPackage
  fullComparisonTarget := fullComparisonTarget
  classicalSoundnessTarget := classicalSoundnessTarget

end FullGeometricComparisonTarget

structure MotIncPresentationRealizationEquivalenceTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  localizationPackage : GeometricLocalizationPackage ctx
  commonPresentationTarget : Prop
  realizationEquivalenceTarget : Prop

namespace MotIncPresentationRealizationEquivalenceTarget

def ofLocalizationPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (localizationPackage : GeometricLocalizationPackage ctx)
    (commonPresentationTarget realizationEquivalenceTarget : Prop) :
    MotIncPresentationRealizationEquivalenceTarget ctx where
  localizationPackage := localizationPackage
  commonPresentationTarget := commonPresentationTarget
  realizationEquivalenceTarget := realizationEquivalenceTarget

def ofCorePresentationDecomposition
    {ctx : ClassicalComparisonContext.{u, v}}
    (decomposition : CorePresentationEquivalenceDecompositionTarget ctx)
    (localizationPackage : GeometricLocalizationPackage ctx)
    (_hLocalization : localizationPackage = decomposition.commonRelations.localizationPackage)
    (realizationEquivalenceTarget : Prop) :
    MotIncPresentationRealizationEquivalenceTarget ctx where
  localizationPackage := localizationPackage
  commonPresentationTarget := decomposition.commonPresentationTarget
  realizationEquivalenceTarget := realizationEquivalenceTarget

end MotIncPresentationRealizationEquivalenceTarget

structure AdmissibleSixFunctorGeometryTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  localizationPackage : GeometricLocalizationPackage ctx
  admissibleSixFunctorGeometryTarget : Prop
  envelopeClosureTarget : Prop

namespace AdmissibleSixFunctorGeometryTarget

def ofLocalizationPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (localizationPackage : GeometricLocalizationPackage ctx)
    (admissibleSixFunctorGeometryTarget envelopeClosureTarget : Prop) :
    AdmissibleSixFunctorGeometryTarget ctx where
  localizationPackage := localizationPackage
  admissibleSixFunctorGeometryTarget := admissibleSixFunctorGeometryTarget
  envelopeClosureTarget := envelopeClosureTarget

end AdmissibleSixFunctorGeometryTarget

structure SmoothProjectiveGeneratorTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  generatorPackage : GeometricGeneratorFamilyPackage ctx
  smoothProjectiveGenerationTarget : Prop
  fiveFamilyCoverageTarget : Prop

namespace SmoothProjectiveGeneratorTarget

def ofGeneratorPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (generatorPackage : GeometricGeneratorFamilyPackage ctx)
    (smoothProjectiveGenerationTarget fiveFamilyCoverageTarget : Prop) :
    SmoothProjectiveGeneratorTarget ctx where
  generatorPackage := generatorPackage
  smoothProjectiveGenerationTarget := smoothProjectiveGenerationTarget
  fiveFamilyCoverageTarget := fiveFamilyCoverageTarget

end SmoothProjectiveGeneratorTarget

structure CompatibleRealizationUniversalityTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  assignmentTable : GeneratorRealizationAssignmentTable ctx
  compatibleRealizationUniversalityTarget : Prop
  rowCompatibilityTarget : Prop

namespace CompatibleRealizationUniversalityTarget

def ofAssignmentTable
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx)
    (compatibleRealizationUniversalityTarget rowCompatibilityTarget : Prop) :
    CompatibleRealizationUniversalityTarget ctx where
  assignmentTable := assignmentTable
  compatibleRealizationUniversalityTarget := compatibleRealizationUniversalityTarget
  rowCompatibilityTarget := rowCompatibilityTarget

end CompatibleRealizationUniversalityTarget

structure ScalarFramedExtractionFromGeometryTarget
    (ctx : ClassicalComparisonContext.{u, v})
    (structuredEq : StructuredComparisonEquality ctx) where
  tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq
  scalarExtractionTarget : Prop
  framedExtractionTarget : Prop
  coarseScalarCompatibilityTarget : Prop

namespace ScalarFramedExtractionFromGeometryTarget

def ofTomographySoundness
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq)
    (scalarExtractionTarget framedExtractionTarget coarseScalarCompatibilityTarget : Prop) :
    ScalarFramedExtractionFromGeometryTarget ctx structuredEq where
  tomographySoundness := tomographySoundness
  scalarExtractionTarget := scalarExtractionTarget
  framedExtractionTarget := framedExtractionTarget
  coarseScalarCompatibilityTarget := coarseScalarCompatibilityTarget

@[simp] theorem ofTomographySoundness_tomographySoundness
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq)
    (scalarExtractionTarget framedExtractionTarget coarseScalarCompatibilityTarget : Prop) :
    (ofTomographySoundness tomographySoundness scalarExtractionTarget framedExtractionTarget
      coarseScalarCompatibilityTarget).tomographySoundness = tomographySoundness := rfl

end ScalarFramedExtractionFromGeometryTarget

/-- Smallest manuscript-facing port-label assumption on the comparison side:
the recovered slot data admit a symbolic separation witness. -/
def GeometricPortLabelSeparationAssumption
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        TraceCalc.ClassicalPeriods.StructuredComparisonSlotData) : Prop :=
  Nonempty (TraceCalc.ClassicalPeriods.SymbolicPortLabelSeparationTarget slotData)

namespace GeometricPortLabelSeparationAssumption

theorem ofGeneratorTableAssumption
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {assignmentTable : GeneratorRealizationAssignmentTable ctx}
    {slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        TraceCalc.ClassicalPeriods.StructuredComparisonSlotData}
    (assumption : GeneratorTablePortLabelSeparationAssumption assignmentTable slotData) :
    GeometricPortLabelSeparationAssumption slotData := by
  rcases assumption with ⟨hWitness, hAssignment⟩
  refine ⟨?_⟩
  exact
    TraceCalc.ClassicalPeriods.GeometricBoundaryPortLabelAssignmentTarget.toSymbolicPortLabelSeparationTarget
      (Classical.choice hWitness)
      hAssignment

def reducedPortLabelSeparationTarget
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        TraceCalc.ClassicalPeriods.StructuredComparisonSlotData) : Prop :=
  TraceCalc.ClassicalPeriods.PortLabelSeparationTargetOfSlots slotData

theorem reducedPortLabelSeparationTarget_of_assumption
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        TraceCalc.ClassicalPeriods.StructuredComparisonSlotData}
    (assumption : GeometricPortLabelSeparationAssumption slotData) :
    reducedPortLabelSeparationTarget slotData :=
  TraceCalc.ClassicalPeriods.SymbolicPortLabelSeparationTarget.portLabelSeparationTargetOfSlots
    (Classical.choice assumption)

def comparisonSlotSeparationTarget
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        TraceCalc.ClassicalPeriods.StructuredComparisonSlotData}
    (assumption : GeometricPortLabelSeparationAssumption slotData) :
    TraceCalc.ClassicalPeriods.ComparisonSlotSeparationTarget slotData :=
  TraceCalc.ClassicalPeriods.ComparisonSlotSeparationTarget.ofSymbolicPortLabelSeparation
    (Classical.choice assumption)

end GeometricPortLabelSeparationAssumption

/-- Legacy aggregate wrapper for the missing port-label separation burden on the
comparison-to-boundary side.

The honest smallest remaining input is
`GeometricPortLabelSeparationAssumption`; this wrapper remains the current
manuscript-facing `Prop` shell consumed by the recovery package. -/
structure PortLabelSeparationTarget where
  theoremTarget : Prop

namespace PortLabelSeparationTarget

def ofGeometricPortLabelSeparationAssumption
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        TraceCalc.ClassicalPeriods.StructuredComparisonSlotData}
    (assumption : GeometricPortLabelSeparationAssumption slotData) :
    PortLabelSeparationTarget where
  theoremTarget := GeometricPortLabelSeparationAssumption.reducedPortLabelSeparationTarget slotData

def ofGeneratorTableAssumption
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {assignmentTable : GeneratorRealizationAssignmentTable ctx}
    {slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        TraceCalc.ClassicalPeriods.StructuredComparisonSlotData}
    (assumption : GeneratorTablePortLabelSeparationAssumption assignmentTable slotData) :
    PortLabelSeparationTarget :=
  ofGeometricPortLabelSeparationAssumption
    (GeometricPortLabelSeparationAssumption.ofGeneratorTableAssumption assumption)

def ofGeneratorTableData
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {assignmentTable : GeneratorRealizationAssignmentTable ctx}
    {slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        TraceCalc.ClassicalPeriods.StructuredComparisonSlotData}
    (rowWiseData : TraceCalc.ClassicalPeriods.GeneratorRowSlotSeparationData assignmentTable)
    (recoveredAssignmentData :
      TraceCalc.ClassicalPeriods.RecoveredSlotAssignmentData assignmentTable slotData) :
    PortLabelSeparationTarget :=
  ofGeneratorTableAssumption
    (GeneratorTablePortLabelSeparationAssumption.ofData rowWiseData recoveredAssignmentData)

@[simp] theorem ofGeometricPortLabelSeparationAssumption_theoremTarget
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        TraceCalc.ClassicalPeriods.StructuredComparisonSlotData}
    (assumption : GeometricPortLabelSeparationAssumption slotData) :
    (ofGeometricPortLabelSeparationAssumption assumption).theoremTarget =
      GeometricPortLabelSeparationAssumption.reducedPortLabelSeparationTarget slotData := rfl

@[simp] theorem ofGeneratorTableAssumption_theoremTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {assignmentTable : GeneratorRealizationAssignmentTable ctx}
    {slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        TraceCalc.ClassicalPeriods.StructuredComparisonSlotData}
    (assumption : GeneratorTablePortLabelSeparationAssumption assignmentTable slotData) :
    (ofGeneratorTableAssumption assumption).theoremTarget =
      GeometricPortLabelSeparationAssumption.reducedPortLabelSeparationTarget slotData := rfl

end PortLabelSeparationTarget

/-- Precise target for the remaining nondegeneracy burden on the comparison
pairing used by period extraction. -/
structure NondegenerateComparisonPairingTarget where
  theoremTarget : Prop

/-- Manuscript-facing package for the exact comparison-side assumptions still
needed before structured comparison data can be promoted to visible-boundary
reconstruction.

This deliberately does not assert that scalar periods alone determine the
boundary. The data here sit strictly above the scalar shadow: slot separation,
slot injectivity, recovery of boundary ports from those slots, and final
visible-boundary reconstruction. The last six fields record the concrete hard
assumption families that remain open in the manuscript wording.

The `chosenBasesTarget` field is optional presentation data only. The current
basis-free tomography package does not consume chosen bases on the main
comparison-side recovery path. -/
structure StructuredComparisonVisibleBoundaryRecoveryTarget
    (ctx : ClassicalComparisonContext.{u, v})
    (structuredEq : StructuredComparisonEquality ctx) where
  tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq
  comparisonSlotSeparationTarget : Prop
  comparisonSlotInjectivityTarget : Prop
  boundaryPortRecoveryFromComparisonSlotsTarget : Prop
  visibleBoundaryReconstructionTarget : Prop
  finiteDimensionalityTarget : Prop
  chosenBasesTarget : Prop
  faithfulFramedProbesTarget : Prop
  portLabelSeparationTarget : Prop
  comparisonNaturalityTarget : Prop
  nondegeneratePairingTarget : Prop

namespace StructuredComparisonVisibleBoundaryRecoveryTarget

def encodedFiniteDimensionalityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (finiteDimensionality : FiniteDimensionalProbeSeparation ctx) : Prop :=
  finiteDimensionality.finiteDimensionalityTarget

def encodedFaithfulFramedProbesTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq) : Prop :=
  GeometricRealizationTomographySoundness.faithfulFramedProbeTarget tomographySoundness

def encodedComparisonNaturalityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq) : Prop :=
  GeometricRealizationTomographySoundness.comparisonNaturalityTarget tomographySoundness

def encodedNondegenerateComparisonPairingTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq) : Prop :=
  TraceCalc.ClassicalPeriods.ComparisonPairingNondegeneracyTarget
    structuredEq
    tomographySoundness.concreteFramedDatum

@[simp] theorem encodedFiniteDimensionalityTarget_eq
    {ctx : ClassicalComparisonContext.{u, v}}
    (finiteDimensionality : FiniteDimensionalProbeSeparation ctx) :
    encodedFiniteDimensionalityTarget finiteDimensionality =
      finiteDimensionality.finiteDimensionalityTarget := rfl

@[simp] theorem encodedFaithfulFramedProbesTarget_eq
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq) :
    encodedFaithfulFramedProbesTarget tomographySoundness =
      GeometricRealizationTomographySoundness.faithfulFramedProbeTarget tomographySoundness := rfl

@[simp] theorem encodedComparisonNaturalityTarget_eq
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq) :
    encodedComparisonNaturalityTarget tomographySoundness =
      GeometricRealizationTomographySoundness.comparisonNaturalityTarget tomographySoundness := rfl

theorem encodedNondegenerateComparisonPairingTarget_of_tomography
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq) :
    encodedNondegenerateComparisonPairingTarget tomographySoundness := by
  intro left right hPairing
  have hProbe :
      ProbeEquality
        (concreteFramedProbeFamily tomographySoundness.concreteFramedDatum).toScalarProbeFamily
        left
        right := by
    simpa [TraceCalc.ClassicalPeriods.ComparisonPairingEquality,
      TraceCalc.ClassicalPeriods.ComparisonPairingProbeFamily.toScalarProbeFamily,
      concreteFramedProbeFamily, FramedProbeFamily.toScalarProbeFamily, framedScalarShadow]
      using hPairing
  have hBasis := tomographySoundness.probeExtensionality.theoremTarget left right hProbe
  exact tomographySoundness.packedReconstruction.theoremTarget left right hBasis

def ofTomographySoundness
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq)
    (comparisonSlotSeparationTarget comparisonSlotInjectivityTarget
      boundaryPortRecoveryFromComparisonSlotsTarget
      visibleBoundaryReconstructionTarget
      finiteDimensionalityTarget chosenBasesTarget faithfulFramedProbesTarget
      portLabelSeparationTarget comparisonNaturalityTarget
      nondegeneratePairingTarget : Prop) :
    StructuredComparisonVisibleBoundaryRecoveryTarget ctx structuredEq where
  tomographySoundness := tomographySoundness
  comparisonSlotSeparationTarget := comparisonSlotSeparationTarget
  comparisonSlotInjectivityTarget := comparisonSlotInjectivityTarget
  boundaryPortRecoveryFromComparisonSlotsTarget :=
    boundaryPortRecoveryFromComparisonSlotsTarget
  visibleBoundaryReconstructionTarget := visibleBoundaryReconstructionTarget
  finiteDimensionalityTarget := finiteDimensionalityTarget
  chosenBasesTarget := chosenBasesTarget
  faithfulFramedProbesTarget := faithfulFramedProbesTarget
  portLabelSeparationTarget := portLabelSeparationTarget
  comparisonNaturalityTarget := comparisonNaturalityTarget
  nondegeneratePairingTarget := nondegeneratePairingTarget

@[simp] theorem ofTomographySoundness_tomographySoundness
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq)
    (comparisonSlotSeparationTarget comparisonSlotInjectivityTarget
      boundaryPortRecoveryFromComparisonSlotsTarget
      visibleBoundaryReconstructionTarget
      finiteDimensionalityTarget chosenBasesTarget faithfulFramedProbesTarget
      portLabelSeparationTarget comparisonNaturalityTarget
      nondegeneratePairingTarget : Prop) :
    (ofTomographySoundness tomographySoundness comparisonSlotSeparationTarget
      comparisonSlotInjectivityTarget boundaryPortRecoveryFromComparisonSlotsTarget
      visibleBoundaryReconstructionTarget finiteDimensionalityTarget chosenBasesTarget
      faithfulFramedProbesTarget portLabelSeparationTarget comparisonNaturalityTarget
      nondegeneratePairingTarget).tomographySoundness = tomographySoundness := rfl

/-- Constructor helper exposing the assumptions already encoded by the current
tomography stack.

What becomes immediate here:
- finite-dimensionality, once supplied as the existing point-separation package,
- faithful framed probes, via the geometric-to-concrete tomography package,
- comparison naturality, via `GeometricComparisonNaturality`.

What remains explicit:
- chosen bases,
- geometric port-label separation via existence of a symbolic slot witness,
- nondegenerate pairing,
- and the four comparison-to-boundary reconstruction steps. -/
def ofTomographySoundnessAndExposedAssumptions
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq)
    (finiteDimensionality : FiniteDimensionalProbeSeparation ctx)
    (comparisonSlotSeparationTarget comparisonSlotInjectivityTarget
      boundaryPortRecoveryFromComparisonSlotsTarget
      visibleBoundaryReconstructionTarget chosenBasesTarget : Prop)
    (portLabelSeparationTarget : PortLabelSeparationTarget) :
    StructuredComparisonVisibleBoundaryRecoveryTarget ctx structuredEq where
  tomographySoundness := tomographySoundness
  comparisonSlotSeparationTarget := comparisonSlotSeparationTarget
  comparisonSlotInjectivityTarget := comparisonSlotInjectivityTarget
  boundaryPortRecoveryFromComparisonSlotsTarget :=
    boundaryPortRecoveryFromComparisonSlotsTarget
  visibleBoundaryReconstructionTarget := visibleBoundaryReconstructionTarget
  finiteDimensionalityTarget := encodedFiniteDimensionalityTarget finiteDimensionality
  chosenBasesTarget := chosenBasesTarget
  faithfulFramedProbesTarget := encodedFaithfulFramedProbesTarget tomographySoundness
  portLabelSeparationTarget := portLabelSeparationTarget.theoremTarget
  comparisonNaturalityTarget := encodedComparisonNaturalityTarget tomographySoundness
  nondegeneratePairingTarget := encodedNondegenerateComparisonPairingTarget tomographySoundness

@[simp] theorem ofTomographySoundnessAndExposedAssumptions_finiteDimensionalityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq)
    (finiteDimensionality : FiniteDimensionalProbeSeparation ctx)
    (comparisonSlotSeparationTarget comparisonSlotInjectivityTarget
      boundaryPortRecoveryFromComparisonSlotsTarget
      visibleBoundaryReconstructionTarget chosenBasesTarget : Prop)
    (portLabelSeparationTarget : PortLabelSeparationTarget) :
    let target : StructuredComparisonVisibleBoundaryRecoveryTarget ctx structuredEq :=
      ofTomographySoundnessAndExposedAssumptions tomographySoundness finiteDimensionality
        comparisonSlotSeparationTarget comparisonSlotInjectivityTarget
        boundaryPortRecoveryFromComparisonSlotsTarget
        visibleBoundaryReconstructionTarget chosenBasesTarget portLabelSeparationTarget
    target.finiteDimensionalityTarget =
      encodedFiniteDimensionalityTarget finiteDimensionality := rfl

@[simp] theorem ofTomographySoundnessAndExposedAssumptions_faithfulFramedProbesTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq)
    (finiteDimensionality : FiniteDimensionalProbeSeparation ctx)
    (comparisonSlotSeparationTarget comparisonSlotInjectivityTarget
      boundaryPortRecoveryFromComparisonSlotsTarget
      visibleBoundaryReconstructionTarget chosenBasesTarget : Prop)
    (portLabelSeparationTarget : PortLabelSeparationTarget) :
    let target : StructuredComparisonVisibleBoundaryRecoveryTarget ctx structuredEq :=
      ofTomographySoundnessAndExposedAssumptions tomographySoundness finiteDimensionality
        comparisonSlotSeparationTarget comparisonSlotInjectivityTarget
        boundaryPortRecoveryFromComparisonSlotsTarget
        visibleBoundaryReconstructionTarget chosenBasesTarget portLabelSeparationTarget
    target.faithfulFramedProbesTarget =
      encodedFaithfulFramedProbesTarget tomographySoundness := rfl

@[simp] theorem ofTomographySoundnessAndExposedAssumptions_comparisonNaturalityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq)
    (finiteDimensionality : FiniteDimensionalProbeSeparation ctx)
    (comparisonSlotSeparationTarget comparisonSlotInjectivityTarget
      boundaryPortRecoveryFromComparisonSlotsTarget
      visibleBoundaryReconstructionTarget chosenBasesTarget : Prop)
    (portLabelSeparationTarget : PortLabelSeparationTarget) :
    let target : StructuredComparisonVisibleBoundaryRecoveryTarget ctx structuredEq :=
      ofTomographySoundnessAndExposedAssumptions tomographySoundness finiteDimensionality
        comparisonSlotSeparationTarget comparisonSlotInjectivityTarget
        boundaryPortRecoveryFromComparisonSlotsTarget
        visibleBoundaryReconstructionTarget chosenBasesTarget portLabelSeparationTarget
    target.comparisonNaturalityTarget =
      encodedComparisonNaturalityTarget tomographySoundness := rfl

@[simp] theorem ofTomographySoundnessAndExposedAssumptions_nondegeneratePairingTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq)
    (finiteDimensionality : FiniteDimensionalProbeSeparation ctx)
    (comparisonSlotSeparationTarget comparisonSlotInjectivityTarget
      boundaryPortRecoveryFromComparisonSlotsTarget
      visibleBoundaryReconstructionTarget chosenBasesTarget : Prop)
    (portLabelSeparationTarget : PortLabelSeparationTarget) :
    let target : StructuredComparisonVisibleBoundaryRecoveryTarget ctx structuredEq :=
      ofTomographySoundnessAndExposedAssumptions tomographySoundness finiteDimensionality
        comparisonSlotSeparationTarget comparisonSlotInjectivityTarget
        boundaryPortRecoveryFromComparisonSlotsTarget
        visibleBoundaryReconstructionTarget chosenBasesTarget portLabelSeparationTarget
    target.nondegeneratePairingTarget =
      encodedNondegenerateComparisonPairingTarget tomographySoundness := rfl

end StructuredComparisonVisibleBoundaryRecoveryTarget

structure ClassicalManuscriptSpineTarget
    (ctx : ClassicalComparisonContext.{u, v})
    (structuredEq : StructuredComparisonEquality ctx) where
  generatorPackage : GeometricGeneratorFamilyPackage ctx
  localizationPackage : GeometricLocalizationPackage ctx
  geometricPresentationTheorem : GeometricPresentationTheoremTarget ctx
  motIncPresentationRealizationEquivalence : MotIncPresentationRealizationEquivalenceTarget ctx
  scalarFramedExtraction : ScalarFramedExtractionFromGeometryTarget ctx structuredEq
  generatorToLocalizationTarget : generatorPackage.toGeometricLocalizationPackage = localizationPackage
  localizationToMotIncTarget :
    motIncPresentationRealizationEquivalence.localizationPackage = localizationPackage
  presentationCompatibilityTarget : Prop

namespace ClassicalManuscriptSpineTarget

def ofPackages
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (generatorPackage : GeometricGeneratorFamilyPackage ctx)
    (localizationPackage : GeometricLocalizationPackage ctx)
    (geometricPresentationTheorem : GeometricPresentationTheoremTarget ctx)
    (motIncPresentationRealizationEquivalence : MotIncPresentationRealizationEquivalenceTarget ctx)
    (scalarFramedExtraction : ScalarFramedExtractionFromGeometryTarget ctx structuredEq)
    (generatorToLocalizationTarget : generatorPackage.toGeometricLocalizationPackage = localizationPackage)
    (localizationToMotIncTarget :
      motIncPresentationRealizationEquivalence.localizationPackage = localizationPackage)
    (presentationCompatibilityTarget : Prop) :
    ClassicalManuscriptSpineTarget ctx structuredEq where
  generatorPackage := generatorPackage
  localizationPackage := localizationPackage
  geometricPresentationTheorem := geometricPresentationTheorem
  motIncPresentationRealizationEquivalence := motIncPresentationRealizationEquivalence
  scalarFramedExtraction := scalarFramedExtraction
  generatorToLocalizationTarget := generatorToLocalizationTarget
  localizationToMotIncTarget := localizationToMotIncTarget
  presentationCompatibilityTarget := presentationCompatibilityTarget

@[simp] theorem ofPackages_generatorPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (generatorPackage : GeometricGeneratorFamilyPackage ctx)
    (localizationPackage : GeometricLocalizationPackage ctx)
    (geometricPresentationTheorem : GeometricPresentationTheoremTarget ctx)
    (motIncPresentationRealizationEquivalence : MotIncPresentationRealizationEquivalenceTarget ctx)
    (scalarFramedExtraction : ScalarFramedExtractionFromGeometryTarget ctx structuredEq)
    (generatorToLocalizationTarget : generatorPackage.toGeometricLocalizationPackage = localizationPackage)
    (localizationToMotIncTarget :
      motIncPresentationRealizationEquivalence.localizationPackage = localizationPackage)
    (presentationCompatibilityTarget : Prop) :
    (ofPackages generatorPackage localizationPackage geometricPresentationTheorem
      motIncPresentationRealizationEquivalence scalarFramedExtraction generatorToLocalizationTarget
      localizationToMotIncTarget presentationCompatibilityTarget).generatorPackage = generatorPackage :=
  rfl

@[simp] theorem ofPackages_localizationPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (generatorPackage : GeometricGeneratorFamilyPackage ctx)
    (localizationPackage : GeometricLocalizationPackage ctx)
    (geometricPresentationTheorem : GeometricPresentationTheoremTarget ctx)
    (motIncPresentationRealizationEquivalence : MotIncPresentationRealizationEquivalenceTarget ctx)
    (scalarFramedExtraction : ScalarFramedExtractionFromGeometryTarget ctx structuredEq)
    (generatorToLocalizationTarget : generatorPackage.toGeometricLocalizationPackage = localizationPackage)
    (localizationToMotIncTarget :
      motIncPresentationRealizationEquivalence.localizationPackage = localizationPackage)
    (presentationCompatibilityTarget : Prop) :
    (ofPackages generatorPackage localizationPackage geometricPresentationTheorem
      motIncPresentationRealizationEquivalence scalarFramedExtraction generatorToLocalizationTarget
      localizationToMotIncTarget presentationCompatibilityTarget).localizationPackage = localizationPackage :=
  rfl

end ClassicalManuscriptSpineTarget

end ClassicalPeriods
end TraceCalc