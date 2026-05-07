import TraceCalc.ClassicalPeriods.ComparisonBoundaryRecovery

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

structure OperationalGeometricPresentationTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  source : GeometricPeriodObject ctx
  target : GeometricPeriodObject ctx
  finitePresentationTarget : Prop
  interfaceAdequacyTarget : Prop

namespace OperationalGeometricPresentationTarget

def ofEndpoints
    {ctx : ClassicalComparisonContext.{u, v}}
    (source target : GeometricPeriodObject ctx)
    (finitePresentationTarget interfaceAdequacyTarget : Prop) :
    OperationalGeometricPresentationTarget ctx where
  source := source
  target := target
  finitePresentationTarget := finitePresentationTarget
  interfaceAdequacyTarget := interfaceAdequacyTarget

@[simp] theorem ofEndpoints_source
    {ctx : ClassicalComparisonContext.{u, v}}
    (source target : GeometricPeriodObject ctx)
    (finitePresentationTarget interfaceAdequacyTarget : Prop) :
    (ofEndpoints source target finitePresentationTarget interfaceAdequacyTarget).source = source := rfl

@[simp] theorem ofEndpoints_target
    {ctx : ClassicalComparisonContext.{u, v}}
    (source target : GeometricPeriodObject ctx)
    (finitePresentationTarget interfaceAdequacyTarget : Prop) :
    (ofEndpoints source target finitePresentationTarget interfaceAdequacyTarget).target = target := rfl

end OperationalGeometricPresentationTarget

structure TraceToGeometricPacketEquivalenceTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  realization : GeometricRealizationFunctorData ctx
  traceToPacketEquivalenceTarget : Prop
  packetClassificationTarget : Prop

namespace TraceToGeometricPacketEquivalenceTarget

def ofRealization
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (traceToPacketEquivalenceTarget packetClassificationTarget : Prop) :
    TraceToGeometricPacketEquivalenceTarget ctx where
  realization := realization
  traceToPacketEquivalenceTarget := traceToPacketEquivalenceTarget
  packetClassificationTarget := packetClassificationTarget

@[simp] theorem ofRealization_realization
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (traceToPacketEquivalenceTarget packetClassificationTarget : Prop) :
    (ofRealization realization traceToPacketEquivalenceTarget packetClassificationTarget).realization =
      realization := rfl

end TraceToGeometricPacketEquivalenceTarget

structure GeometricPresentationTheoremTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  operationalPresentation : OperationalGeometricPresentationTarget ctx
  tracePacketEquivalence : TraceToGeometricPacketEquivalenceTarget ctx
  presentationCompletenessTarget : Prop

namespace GeometricPresentationTheoremTarget

def ofOperationalAndPacket
    {ctx : ClassicalComparisonContext.{u, v}}
    (operationalPresentation : OperationalGeometricPresentationTarget ctx)
    (tracePacketEquivalence : TraceToGeometricPacketEquivalenceTarget ctx)
    (presentationCompletenessTarget : Prop) :
    GeometricPresentationTheoremTarget ctx where
  operationalPresentation := operationalPresentation
  tracePacketEquivalence := tracePacketEquivalence
  presentationCompletenessTarget := presentationCompletenessTarget

end GeometricPresentationTheoremTarget

structure FiniteCorrespondenceUniversalityTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  realization : GeometricRealizationFunctorData ctx
  corrFamily : CorrGeneratorFamilyData ctx realization
  finiteCorrespondenceUniversalityTarget : Prop
  correspondenceCompositionTarget : Prop

namespace FiniteCorrespondenceUniversalityTarget

def ofCorrFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (corrFamily : CorrGeneratorFamilyData ctx realization)
    (finiteCorrespondenceUniversalityTarget correspondenceCompositionTarget : Prop) :
    FiniteCorrespondenceUniversalityTarget ctx where
  realization := realization
  corrFamily := corrFamily
  finiteCorrespondenceUniversalityTarget := finiteCorrespondenceUniversalityTarget
  correspondenceCompositionTarget := correspondenceCompositionTarget

end FiniteCorrespondenceUniversalityTarget

structure LocalizationTriangleUniversalityTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  realization : GeometricRealizationFunctorData ctx
  locFamily : LocGeneratorFamilyData ctx realization
  localizationTriangleUniversalityTarget : Prop
  localizationFunctorialityTarget : Prop

namespace LocalizationTriangleUniversalityTarget

def ofLocFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (locFamily : LocGeneratorFamilyData ctx realization)
    (localizationTriangleUniversalityTarget localizationFunctorialityTarget : Prop) :
    LocalizationTriangleUniversalityTarget ctx where
  realization := realization
  locFamily := locFamily
  localizationTriangleUniversalityTarget := localizationTriangleUniversalityTarget
  localizationFunctorialityTarget := localizationFunctorialityTarget

end LocalizationTriangleUniversalityTarget

structure DualityDataUniversalityTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  realization : GeometricRealizationFunctorData ctx
  envFamily : EnvGeneratorFamilyData ctx realization
  dualityDataUniversalityTarget : Prop
  envelopeStructureTarget : Prop

namespace DualityDataUniversalityTarget

def ofEnvFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (envFamily : EnvGeneratorFamilyData ctx realization)
    (dualityDataUniversalityTarget envelopeStructureTarget : Prop) :
    DualityDataUniversalityTarget ctx where
  realization := realization
  envFamily := envFamily
  dualityDataUniversalityTarget := dualityDataUniversalityTarget
  envelopeStructureTarget := envelopeStructureTarget

@[simp] theorem ofEnvFamily_envFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (envFamily : EnvGeneratorFamilyData ctx realization)
    (dualityDataUniversalityTarget envelopeStructureTarget : Prop) :
    (ofEnvFamily envFamily dualityDataUniversalityTarget envelopeStructureTarget).envFamily = envFamily :=
  rfl

end DualityDataUniversalityTarget

structure RealBettiDeRhamComparisonRealizationTarget
    (ctx : ClassicalComparisonContext.{u, v}) where
  realization : GeometricRealizationFunctorData ctx
  bettiAgreementTarget : Prop
  deRhamAgreementTarget : Prop
  comparisonNaturalityTarget : Prop

namespace RealBettiDeRhamComparisonRealizationTarget

def ofRealization
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx)
    (bettiAgreementTarget deRhamAgreementTarget comparisonNaturalityTarget : Prop) :
    RealBettiDeRhamComparisonRealizationTarget ctx where
  realization := realization
  bettiAgreementTarget := bettiAgreementTarget
  deRhamAgreementTarget := deRhamAgreementTarget
  comparisonNaturalityTarget := comparisonNaturalityTarget

end RealBettiDeRhamComparisonRealizationTarget

/-- The five-row generator table now supplies the symbolic label layer, but an
honest comparison-to-boundary discharge still needs two ingredients: a proof
that the chosen row-wise symbolic labels are separated, and a bridge showing
that each recovered comparison-slot bundle is one of those five symbolic row
bundles. -/
def GeneratorTableRowWiseSlotSeparationTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) : Prop :=
  Nonempty (TraceCalc.ClassicalPeriods.GeneratorRowSlotSeparationData assignmentTable)

def GeneratorTableRecoveredSlotAssignmentTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx)
    (slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        TraceCalc.ClassicalPeriods.StructuredComparisonSlotData) : Prop :=
  TraceCalc.ClassicalPeriods.RecoveredSlotAssignmentData assignmentTable slotData

/-- Honest lift obligation from symbolic table data to the real comparison
recovery path: the recovered slot bundle for each reconstruction record must
land in one of the five designated Corr/Loc/Nis/A1/Env table rows. -/
def RealGeneratorTablePortLabelLiftObligation
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx)
    (slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        TraceCalc.ClassicalPeriods.StructuredComparisonSlotData) : Prop :=
  GeneratorTableRecoveredSlotAssignmentTarget assignmentTable slotData

def GeneratorTablePortLabelSeparationAssumption
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx)
    (slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        TraceCalc.ClassicalPeriods.StructuredComparisonSlotData) : Prop :=
  GeneratorTableRowWiseSlotSeparationTarget assignmentTable ∧
    GeneratorTableRecoveredSlotAssignmentTarget assignmentTable slotData

@[simp] theorem GeneratorTablePortLabelSeparationAssumption_iff
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {assignmentTable : GeneratorRealizationAssignmentTable ctx}
    {slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        TraceCalc.ClassicalPeriods.StructuredComparisonSlotData} :
    GeneratorTablePortLabelSeparationAssumption assignmentTable slotData ↔
      GeneratorTableRowWiseSlotSeparationTarget assignmentTable ∧
        GeneratorTableRecoveredSlotAssignmentTarget assignmentTable slotData :=
  Iff.rfl

theorem GeneratorTablePortLabelSeparationAssumption.reducedPortLabelSeparationTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {assignmentTable : GeneratorRealizationAssignmentTable ctx}
    {slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        TraceCalc.ClassicalPeriods.StructuredComparisonSlotData}
    (assumption : GeneratorTablePortLabelSeparationAssumption assignmentTable slotData) :
    TraceCalc.ClassicalPeriods.PortLabelSeparationTargetOfSlots slotData := by
  rcases assumption with ⟨hSeparated, hAssignment⟩
  exact
    TraceCalc.ClassicalPeriods.GeometricBoundaryPortLabelAssignmentTarget.toPortLabelSeparationTargetOfSlots
      (Classical.choice hSeparated)
      hAssignment

theorem GeneratorTablePortLabelSeparationAssumption.comparisonSlotSeparationTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {assignmentTable : GeneratorRealizationAssignmentTable ctx}
    {slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        TraceCalc.ClassicalPeriods.StructuredComparisonSlotData}
    (assumption : GeneratorTablePortLabelSeparationAssumption assignmentTable slotData) :
    TraceCalc.ClassicalPeriods.ComparisonSlotSeparationTarget slotData := by
  rcases assumption with ⟨hSeparated, hAssignment⟩
  exact
    TraceCalc.ClassicalPeriods.ComparisonSlotSeparationTarget.ofSymbolicPortLabelSeparation
      (TraceCalc.ClassicalPeriods.GeometricBoundaryPortLabelAssignmentTarget.toSymbolicPortLabelSeparationTarget
        (Classical.choice hSeparated)
        hAssignment)

def GeneratorTablePortLabelSeparationAssumption.structuredComparisonDeterminesVisibleBoundaryTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {α : Type v} {β : Sort _}
    {assignmentTable : GeneratorRealizationAssignmentTable ctx}
    (comparison :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α)
    (slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        TraceCalc.ClassicalPeriods.StructuredComparisonSlotData)
    (boundaryPorts :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        TraceCalc.ClassicalPeriods.VisibleBoundaryPortData)
    (visibleBoundary :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → β)
    (assumption : GeneratorTablePortLabelSeparationAssumption assignmentTable slotData)
    (slotInjectivity :
      TraceCalc.ClassicalPeriods.ComparisonSlotInjectivityTarget comparison slotData)
    (boundaryPortRecovery :
      TraceCalc.ClassicalPeriods.BoundaryPortRecoveryFromComparisonSlotsTarget
        slotData boundaryPorts)
    (visibleBoundaryReconstruction :
      TraceCalc.ClassicalPeriods.VisibleBoundaryReconstructionFromPortsTarget
        boundaryPorts visibleBoundary) :
    TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.StructuredComparisonDeterminesVisibleBoundaryTarget
      (setup := setup)
      comparison
      visibleBoundary :=
  TraceCalc.ClassicalPeriods.structuredComparisonDeterminesVisibleBoundaryTarget_of_slotRecovery
    comparison
    slotData
    boundaryPorts
    visibleBoundary
    (GeneratorTablePortLabelSeparationAssumption.comparisonSlotSeparationTarget assumption)
    slotInjectivity
    boundaryPortRecovery
    visibleBoundaryReconstruction

theorem GeneratorTablePortLabelSeparationAssumption.ofData
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {assignmentTable : GeneratorRealizationAssignmentTable ctx}
    {slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        TraceCalc.ClassicalPeriods.StructuredComparisonSlotData}
    (rowWiseData : TraceCalc.ClassicalPeriods.GeneratorRowSlotSeparationData assignmentTable)
    (recoveredAssignmentData :
      TraceCalc.ClassicalPeriods.RecoveredSlotAssignmentData assignmentTable slotData) :
    GeneratorTablePortLabelSeparationAssumption assignmentTable slotData :=
  ⟨⟨rowWiseData⟩, recoveredAssignmentData⟩

end ClassicalPeriods
end TraceCalc