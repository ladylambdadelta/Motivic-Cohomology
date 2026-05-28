import TraceCalc.ClassicalPeriods.GeneratorRealizationTable

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

/-- Narrow Corr-row soundness target backed directly by generator realization data. -/
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

/-- Narrow Loc-row period-compatibility target backed directly by generator realization data. -/
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

theorem locPacketSoundnessFromGeneratorRealization
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    LocPacketPeriodCompatibilityFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.locAssignment.triangleCompatibilityTarget := by
  exact ⟨locPacketPeriodCompatibilityFromGeneratorRealization assignmentTable,
    locTriangleCompatibility_from_certifiedReplay assignmentTable⟩

/-- Replay-native Nis-row target extracted directly from generator realization data. -/
def NisPacketComparisonFromGeneratorRealizationTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) : Prop :=
  ∀ gen : assignmentTable.nisAssignment.family.GeneratorIndex,
    (assignmentTable.nisAssignment.baseComparisonDatum gen).grothendieckComparisonTarget ∧
      (assignmentTable.nisAssignment.patchComparisonDatum gen).grothendieckComparisonTarget ∧
      (assignmentTable.nisAssignment.overlapComparisonDatum gen).grothendieckComparisonTarget

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

theorem nisPacketSoundnessFromGeneratorRealization
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    NisPacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.nisAssignment.descentSquareCompatibilityTarget := by
  exact ⟨nisOverlapAgreement_from_certifiedReplay assignmentTable,
    nisDescentSquareCompatibility_from_certifiedReplay assignmentTable⟩

/-- Replay-native A1-row target extracted directly from generator realization data. -/
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

theorem a1PacketSoundnessFromGeneratorRealization
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    A1PacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.a1Assignment.framedExtractionTarget := by
  exact ⟨a1EndpointAgreement_from_certifiedReplay assignmentTable,
    a1HomotopyInvariance_from_certifiedReplay assignmentTable⟩

/-- Replay-native Env-row target extracted directly from generator realization data. -/
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

theorem envPacketSoundnessFromGeneratorRealization
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    EnvPacketComparisonFromGeneratorRealizationTarget assignmentTable ∧
      assignmentTable.envAssignment.exactCompletionTarget := by
  exact ⟨envComparisonAgreement_from_certifiedReplay assignmentTable,
    envFormalClosureSoundness_from_certifiedReplay assignmentTable⟩

end ClassicalPeriods
end TraceCalc