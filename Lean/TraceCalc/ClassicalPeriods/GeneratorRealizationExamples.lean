import TraceCalc.ClassicalPeriods.GeometricLocalizationExamples
import TraceCalc.ClassicalPeriods.GeneratorRealizationTable

universe u v

namespace TraceCalc
namespace ClassicalPeriods

/-- Trivial `Corr` generator family for the unit sanity model. -/
def unitCorrGeneratorFamilyData
    (ctx : ClassicalComparisonContext.{u, v}) :
    CorrGeneratorFamilyData ctx (unitGeometricRealizationFunctorData ctx) where
  GeneratorIndex := PUnit
  sourceIndex := fun _ => PUnit.unit
  targetIndex := fun _ => PUnit.unit
  sourceObject := fun _ => UnitGeometricPeriodObject ctx
  targetObject := fun _ => UnitGeometricPeriodObject ctx
  generatorCorrespondence := fun _ => UnitGeometricCorrespondence ctx
  sourceObjectData := fun _ => unitGeometricComparisonObjectData ctx
  targetObjectData := fun _ => unitGeometricComparisonObjectData ctx
  sourceObjectCompatibilityTarget := by
    intro gen
    rfl
  targetObjectCompatibilityTarget := by
    intro gen
    rfl
  sourceObjectDataCompatibilityTarget := by
    intro gen
    rfl
  targetObjectDataCompatibilityTarget := by
    intro gen
    rfl
  theoremTarget := by
    intro gen
    exact ⟨True.intro, True.intro, True.intro⟩

/-- Trivial `Loc` generator family for the unit sanity model. -/
def unitLocGeneratorFamilyData
    (ctx : ClassicalComparisonContext.{u, v}) :
    LocGeneratorFamilyData ctx (unitGeometricRealizationFunctorData ctx) where
  GeneratorIndex := PUnit
  ambientIndex := fun _ => PUnit.unit
  openIndex := fun _ => PUnit.unit
  closedIndex := fun _ => PUnit.unit
  ambientObject := fun _ => UnitGeometricPeriodObject ctx
  openObject := fun _ => UnitGeometricPeriodObject ctx
  closedObject := fun _ => UnitGeometricPeriodObject ctx
  ambientData := fun _ => unitGeometricComparisonObjectData ctx
  openData := fun _ => unitGeometricComparisonObjectData ctx
  closedData := fun _ => unitGeometricComparisonObjectData ctx
  ambientObjectCompatibilityTarget := by
    intro gen
    rfl
  openObjectCompatibilityTarget := by
    intro gen
    rfl
  closedObjectCompatibilityTarget := by
    intro gen
    rfl
  ambientDataCompatibilityTarget := by
    intro gen
    rfl
  openDataCompatibilityTarget := by
    intro gen
    rfl
  closedDataCompatibilityTarget := by
    intro gen
    rfl
  theoremTarget := by
    intro gen
    exact ⟨True.intro, True.intro, True.intro⟩

/-- Trivial `Nis` generator family for the unit sanity model. -/
def unitNisGeneratorFamilyData
    (ctx : ClassicalComparisonContext.{u, v}) :
    NisGeneratorFamilyData ctx (unitGeometricRealizationFunctorData ctx) where
  GeneratorIndex := PUnit
  baseIndex := fun _ => PUnit.unit
  patchIndex := fun _ => PUnit.unit
  overlapIndex := fun _ => PUnit.unit
  baseObject := fun _ => UnitGeometricPeriodObject ctx
  patchObject := fun _ => UnitGeometricPeriodObject ctx
  overlapObject := fun _ => UnitGeometricPeriodObject ctx
  baseData := fun _ => unitGeometricComparisonObjectData ctx
  patchData := fun _ => unitGeometricComparisonObjectData ctx
  overlapData := fun _ => unitGeometricComparisonObjectData ctx
  baseObjectCompatibilityTarget := by
    intro gen
    rfl
  patchObjectCompatibilityTarget := by
    intro gen
    rfl
  overlapObjectCompatibilityTarget := by
    intro gen
    rfl
  baseDataCompatibilityTarget := by
    intro gen
    rfl
  patchDataCompatibilityTarget := by
    intro gen
    rfl
  overlapDataCompatibilityTarget := by
    intro gen
    rfl
  theoremTarget := by
    intro gen
    exact ⟨True.intro, True.intro, True.intro⟩

/-- Trivial `A1` generator family for the unit sanity model. -/
def unitA1GeneratorFamilyData
    (ctx : ClassicalComparisonContext.{u, v}) :
    A1GeneratorFamilyData ctx (unitGeometricRealizationFunctorData ctx) where
  GeneratorIndex := PUnit
  baseIndex := fun _ => PUnit.unit
  cylinderIndex := fun _ => PUnit.unit
  baseObject := fun _ => UnitGeometricPeriodObject ctx
  cylinderObject := fun _ => UnitGeometricPeriodObject ctx
  baseData := fun _ => unitGeometricComparisonObjectData ctx
  cylinderData := fun _ => unitGeometricComparisonObjectData ctx
  baseObjectCompatibilityTarget := by
    intro gen
    rfl
  cylinderObjectCompatibilityTarget := by
    intro gen
    rfl
  baseDataCompatibilityTarget := by
    intro gen
    rfl
  cylinderDataCompatibilityTarget := by
    intro gen
    rfl
  theoremTarget := by
    intro gen
    exact ⟨True.intro, True.intro, True.intro, True.intro⟩

/-- Trivial `Env` generator family for the unit sanity model. -/
def unitEnvGeneratorFamilyData
    (ctx : ClassicalComparisonContext.{u, v}) :
    EnvGeneratorFamilyData ctx (unitGeometricRealizationFunctorData ctx) where
  GeneratorIndex := PUnit
  ambientIndex := fun _ => PUnit.unit
  envelopeIndex := fun _ => PUnit.unit
  ambientObject := fun _ => UnitGeometricPeriodObject ctx
  envelopeObject := fun _ => UnitGeometricPeriodObject ctx
  envelopeCorrespondence := fun _ => UnitGeometricCorrespondence ctx
  ambientData := fun _ => unitGeometricComparisonObjectData ctx
  envelopeData := fun _ => unitGeometricComparisonObjectData ctx
  ambientObjectCompatibilityTarget := by
    intro gen
    rfl
  envelopeObjectCompatibilityTarget := by
    intro gen
    rfl
  ambientDataCompatibilityTarget := by
    intro gen
    rfl
  envelopeDataCompatibilityTarget := by
    intro gen
    rfl
  theoremTarget := by
    intro gen
    exact ⟨True.intro, True.intro, True.intro, True.intro, True.intro⟩

/-- Trivial realization assignment for the `Corr` row. -/
def unitCorrGeneratorRealizationAssignment
    (ctx : ClassicalComparisonContext.{u, v}) :
    CorrGeneratorRealizationAssignment ctx (unitGeometricRealizationFunctorData ctx) where
  family := unitCorrGeneratorFamilyData ctx
  sourceSlotName := "source"
  targetSlotName := "target"
  correspondenceSlotName := "corr"
  bettiSlotName := "betti"
  deRhamSlotName := "deRham"
  comparisonSlotName := "comparison"
  framedSlotName := "framed"
  scalarSlotName := "scalar"
  sourceProjection := fun _ => UnitGeometricPeriodObject ctx
  targetProjection := fun _ => UnitGeometricPeriodObject ctx
  sourceBettiPlaceholder := fun _ => unitGeometricBettiRealizationData ctx
  targetBettiPlaceholder := fun _ => unitGeometricBettiRealizationData ctx
  sourceDeRhamPlaceholder := fun _ => unitGeometricDeRhamRealizationData ctx
  targetDeRhamPlaceholder := fun _ => unitGeometricDeRhamRealizationData ctx
  sourceComparisonDatum := fun _ => unitGrothendieckComparisonData ctx
  targetComparisonDatum := fun _ => unitGrothendieckComparisonData ctx
  sourceFramedPlaceholder := fun _ => unitGeometricFramedObject ctx
  targetFramedPlaceholder := fun _ => unitGeometricFramedObject ctx
  sourceComparisonCompatibilityTarget := by
    intro gen
    rfl
  targetComparisonCompatibilityTarget := by
    intro gen
    rfl
  scalarExtractionTarget := True
  framedExtractionTarget := True
  theoremTarget := by
    intro gen
    constructor
    · exact True.intro
    · exact True.intro

/-- Trivial realization assignment for the `Loc` row. -/
def unitLocGeneratorRealizationAssignment
    (ctx : ClassicalComparisonContext.{u, v}) :
    LocGeneratorRealizationAssignment ctx (unitGeometricRealizationFunctorData ctx) where
  family := unitLocGeneratorFamilyData ctx
  ambientSlotName := "ambient"
  openSlotName := "open"
  closedSlotName := "closed"
  connectingMorphismSlotName := "connecting"
  bettiSlotName := "betti"
  deRhamSlotName := "deRham"
  comparisonSlotName := "comparison"
  framedSlotName := "framed"
  scalarSlotName := "scalar"
  ambientProjection := fun _ => UnitGeometricPeriodObject ctx
  openProjection := fun _ => UnitGeometricPeriodObject ctx
  closedProjection := fun _ => UnitGeometricPeriodObject ctx
  ambientBettiPlaceholder := fun _ => unitGeometricBettiRealizationData ctx
  openBettiPlaceholder := fun _ => unitGeometricBettiRealizationData ctx
  closedBettiPlaceholder := fun _ => unitGeometricBettiRealizationData ctx
  ambientDeRhamPlaceholder := fun _ => unitGeometricDeRhamRealizationData ctx
  openDeRhamPlaceholder := fun _ => unitGeometricDeRhamRealizationData ctx
  closedDeRhamPlaceholder := fun _ => unitGeometricDeRhamRealizationData ctx
  ambientComparisonDatum := fun _ => unitGrothendieckComparisonData ctx
  openComparisonDatum := fun _ => unitGrothendieckComparisonData ctx
  closedComparisonDatum := fun _ => unitGrothendieckComparisonData ctx
  ambientFramedPlaceholder := fun _ => unitGeometricFramedObject ctx
  openFramedPlaceholder := fun _ => unitGeometricFramedObject ctx
  closedFramedPlaceholder := fun _ => unitGeometricFramedObject ctx
  ambientComparisonCompatibilityTarget := by
    intro gen
    rfl
  openComparisonCompatibilityTarget := by
    intro gen
    rfl
  closedComparisonCompatibilityTarget := by
    intro gen
    rfl
  scalarExtractionTarget := True
  framedExtractionTarget := True
  coneNaturalityData :=
    { leftSquareCommutes := True
      middleSquareCommutes := True
      coneInducedMapEqOpenComparison := True
      coneTriangleFunctorialityData :=
        { sourceArrow :=
            { Closed := PUnit
              Ambient := PUnit
              closedToAmbient := fun _ => PUnit.unit }
          targetArrow :=
            { Closed := PUnit
              Ambient := PUnit
              closedToAmbient := fun _ => PUnit.unit }
          arrowMorphism :=
            { left := fun _ => PUnit.unit
              right := fun _ => PUnit.unit
              squareCommutes := rfl } }
      traceNativeReplayData :=
        { sinkPeelReplayTarget :=
            { ReplayWitness := PUnit
              replayWitness := PUnit.unit
              ambientPacketTarget := True
              openComplementPacketTarget := True
              closedSupportPacketTarget := True
              canonicalSinkTarget := True
              peelResultTarget := True
              exposedBoundaryDefectTarget := True
              defectMatchesShiftedClosedTarget := True
              replayReconstructsAmbientTarget := True }
          bettiReplayTarget := True
          deRhamReplayTarget := True
          ambientComparisonNaturalityTarget := True
          openComparisonNaturalityTarget := True
          closedComparisonNaturalityTarget := True
          connectingPacketComparisonNaturality_holds := by
            intro point
            cases point <;>
              rfl }
      leftSquareCommutes_holds := True.intro
      middleSquareCommutes_holds := True.intro
      coneInducedMapEqOpenComparison_holds := True.intro }
  theoremTarget := by
    intro gen
    constructor
    · exact True.intro
    · constructor
      · exact True.intro
      · exact True.intro

/-- Trivial realization assignment for the `Nis` row. -/
def unitNisGeneratorRealizationAssignment
    (ctx : ClassicalComparisonContext.{u, v}) :
    NisGeneratorRealizationAssignment ctx (unitGeometricRealizationFunctorData ctx) where
  family := unitNisGeneratorFamilyData ctx
  baseSlotName := "base"
  patchSlotName := "patch"
  overlapSlotName := "overlap"
  squareSlotName := "square"
  bettiSlotName := "betti"
  deRhamSlotName := "deRham"
  comparisonSlotName := "comparison"
  framedSlotName := "framed"
  scalarSlotName := "scalar"
  baseProjection := fun _ => UnitGeometricPeriodObject ctx
  patchProjection := fun _ => UnitGeometricPeriodObject ctx
  overlapProjection := fun _ => UnitGeometricPeriodObject ctx
  baseBettiPlaceholder := fun _ => unitGeometricBettiRealizationData ctx
  patchBettiPlaceholder := fun _ => unitGeometricBettiRealizationData ctx
  overlapBettiPlaceholder := fun _ => unitGeometricBettiRealizationData ctx
  baseDeRhamPlaceholder := fun _ => unitGeometricDeRhamRealizationData ctx
  patchDeRhamPlaceholder := fun _ => unitGeometricDeRhamRealizationData ctx
  overlapDeRhamPlaceholder := fun _ => unitGeometricDeRhamRealizationData ctx
  baseComparisonDatum := fun _ => unitGrothendieckComparisonData ctx
  patchComparisonDatum := fun _ => unitGrothendieckComparisonData ctx
  overlapComparisonDatum := fun _ => unitGrothendieckComparisonData ctx
  baseFramedPlaceholder := fun _ => unitGeometricFramedObject ctx
  patchFramedPlaceholder := fun _ => unitGeometricFramedObject ctx
  overlapFramedPlaceholder := fun _ => unitGeometricFramedObject ctx
  baseComparisonCompatibilityTarget := by
    intro gen
    rfl
  patchComparisonCompatibilityTarget := by
    intro gen
    rfl
  overlapComparisonCompatibilityTarget := by
    intro gen
    rfl
  scalarExtractionTarget := True
  framedExtractionTarget := True
  theoremTarget := by
    intro gen
    constructor
    · exact True.intro
    · constructor
      · exact True.intro
      · exact True.intro
  descentSquareCompatibilityTarget := True
  traceNativePatchReplayData :=
    { overlapGluingTarget :=
        { ReplayWitness := PUnit
          replayWitness := PUnit.unit
          basePacketTarget := True
          patchPacketTarget := True
          overlapPacketTarget := True
          basePatchAgreementOnOverlapTarget := True
          gluedReplayTarget := True
          gluedReplayRestrictsToBaseTarget := True
          gluedReplayRestrictsToPatchTarget := True
          overlapComparisonNaturalityTarget := True }
      bettiPatchReplayTarget := True
      deRhamPatchReplayTarget := True
      baseComparisonNaturalityTarget := True
      patchComparisonNaturalityTarget := True
      overlapComparisonNaturalityTarget := True
      overlapAgreement_holds := by
        intro gen
        exact ⟨True.intro, True.intro, True.intro⟩
      descentSquareCompatibility_holds := True.intro }

/-- Trivial realization assignment for the `A1` row. -/
def unitA1GeneratorRealizationAssignment
    (ctx : ClassicalComparisonContext.{u, v}) :
    A1GeneratorRealizationAssignment ctx (unitGeometricRealizationFunctorData ctx) where
  family := unitA1GeneratorFamilyData ctx
  baseSlotName := "base"
  cylinderSlotName := "cylinder"
  projectionZeroSlotName := "proj0"
  projectionOneSlotName := "proj1"
  bettiSlotName := "betti"
  deRhamSlotName := "deRham"
  comparisonSlotName := "comparison"
  framedSlotName := "framed"
  scalarSlotName := "scalar"
  baseProjection := fun _ => UnitGeometricPeriodObject ctx
  cylinderProjection := fun _ => UnitGeometricPeriodObject ctx
  baseBettiPlaceholder := fun _ => unitGeometricBettiRealizationData ctx
  cylinderBettiPlaceholder := fun _ => unitGeometricBettiRealizationData ctx
  baseDeRhamPlaceholder := fun _ => unitGeometricDeRhamRealizationData ctx
  cylinderDeRhamPlaceholder := fun _ => unitGeometricDeRhamRealizationData ctx
  baseComparisonDatum := fun _ => unitGrothendieckComparisonData ctx
  cylinderComparisonDatum := fun _ => unitGrothendieckComparisonData ctx
  baseFramedPlaceholder := fun _ => unitGeometricFramedObject ctx
  cylinderFramedPlaceholder := fun _ => unitGeometricFramedObject ctx
  baseComparisonCompatibilityTarget := by
    intro gen
    rfl
  cylinderComparisonCompatibilityTarget := by
    intro gen
    rfl
  scalarExtractionTarget := True
  framedExtractionTarget := True
  theoremTarget := by
    intro gen
    constructor
    · exact True.intro
    · constructor
      · exact True.intro
      · constructor
        · exact True.intro
        · exact True.intro
  traceNativeHomotopyReplayData :=
    { cylinderEndpointReplayTarget :=
        { ReplayWitness := PUnit
          replayWitness := PUnit.unit
          basePacketTarget := True
          cylinderPacketTarget := True
          endpointZeroPacketTarget := True
          endpointOnePacketTarget := True
          cylinderReplayTarget := True
          endpointZeroReplayTarget := True
          endpointOneReplayTarget := True
          endpointAgreementTarget := True
          endpointComparisonNaturalityTarget := True }
      baseBettiReplayTarget := True
      cylinderBettiReplayTarget := True
      baseDeRhamReplayTarget := True
      cylinderDeRhamReplayTarget := True
      projectionZeroComparisonNaturalityTarget := True
      projectionOneComparisonNaturalityTarget := True
      endpointAgreement_holds := by
        intro gen
        exact ⟨True.intro, True.intro, True.intro, True.intro⟩
      homotopyInvariance_holds := True.intro }

/-- Trivial realization assignment for the `Env` row. -/
def unitEnvGeneratorRealizationAssignment
    (ctx : ClassicalComparisonContext.{u, v}) :
    EnvGeneratorRealizationAssignment ctx (unitGeometricRealizationFunctorData ctx) where
  family := unitEnvGeneratorFamilyData ctx
  ambientSlotName := "ambient"
  envelopeSlotName := "envelope"
  exactCompletionSlotName := "exactCompletion"
  bettiSlotName := "betti"
  deRhamSlotName := "deRham"
  comparisonSlotName := "comparison"
  framedSlotName := "framed"
  scalarSlotName := "scalar"
  ambientProjection := fun _ => UnitGeometricPeriodObject ctx
  envelopeProjection := fun _ => UnitGeometricPeriodObject ctx
  ambientBettiPlaceholder := fun _ => unitGeometricBettiRealizationData ctx
  envelopeBettiPlaceholder := fun _ => unitGeometricBettiRealizationData ctx
  ambientDeRhamPlaceholder := fun _ => unitGeometricDeRhamRealizationData ctx
  envelopeDeRhamPlaceholder := fun _ => unitGeometricDeRhamRealizationData ctx
  ambientComparisonDatum := fun _ => unitGrothendieckComparisonData ctx
  envelopeComparisonDatum := fun _ => unitGrothendieckComparisonData ctx
  ambientFramedPlaceholder := fun _ => unitGeometricFramedObject ctx
  envelopeFramedPlaceholder := fun _ => unitGeometricFramedObject ctx
  ambientComparisonCompatibilityTarget := by
    intro gen
    rfl
  envelopeComparisonCompatibilityTarget := by
    intro gen
    rfl
  scalarExtractionTarget := True
  framedExtractionTarget := True
  exactCompletionTarget := True
  theoremTarget := by
    intro gen
    constructor
    · exact True.intro
    · constructor
      · exact True.intro
      · constructor
        · exact True.intro
        · exact True.intro
  traceNativeEnvReplayData :=
    { replayTransformerTarget :=
        { ReplayWitness := PUnit
          replayWitness := PUnit.unit
          operation := .structuralAdmin
          certifiedInputPacketTarget := True
          transformedPacketTarget := True
          boundaryTransportTarget := True
          dependencyTransportTarget := True
          replayTransformerTarget := True
          normalizationTarget := True }
      ambientBettiReplayTarget := True
      envelopeBettiReplayTarget := True
      ambientDeRhamReplayTarget := True
      envelopeDeRhamReplayTarget := True
      boundaryComparisonNaturalityTarget := True
      dependencyComparisonNaturalityTarget := True
      comparisonAgreement_holds := by
        intro gen
        exact ⟨True.intro, True.intro, True.intro, True.intro⟩
      formalClosure_holds := True.intro }

/-- Trivial realization-assignment table for the unit sanity model. -/
def unitGeneratorRealizationAssignmentTable
    (ctx : ClassicalComparisonContext.{u, v}) : GeneratorRealizationAssignmentTable ctx :=
  GeneratorRealizationAssignmentTable.ofAssignments
    (unitGeometricRealizationFunctorData ctx)
    (unitCorrGeneratorRealizationAssignment ctx)
    (unitLocGeneratorRealizationAssignment ctx)
    (unitNisGeneratorRealizationAssignment ctx)
    (unitA1GeneratorRealizationAssignment ctx)
    (unitEnvGeneratorRealizationAssignment ctx)
    (unitGeometricCorrespondenceFunctorialityTarget ctx)
    (unitGeometricOpenClosedLocalizationTarget ctx)
    (unitGeometricNisnevichDescentTarget ctx)
    (unitGeometricA1InvarianceTarget ctx)
    (unitGeometricEnvelopeExactnessTarget ctx)
    True
    True
    True

/-- The unit assignment table forgets to the named generator-family package. -/
def unitGeometricGeneratorFamilyPackage
    (ctx : ClassicalComparisonContext.{u, v}) : GeometricGeneratorFamilyPackage ctx where
  realization := unitGeometricRealizationFunctorData ctx
  corrFamily := unitCorrGeneratorFamilyData ctx
  locFamily := unitLocGeneratorFamilyData ctx
  nisFamily := unitNisGeneratorFamilyData ctx
  a1Family := unitA1GeneratorFamilyData ctx
  envFamily := unitEnvGeneratorFamilyData ctx
  corrTarget := unitGeometricCorrespondenceFunctorialityTarget ctx
  locTarget := unitGeometricOpenClosedLocalizationTarget ctx
  nisTarget := unitGeometricNisnevichDescentTarget ctx
  a1Target := unitGeometricA1InvarianceTarget ctx
  envTarget := unitGeometricEnvelopeExactnessTarget ctx
  generatorCoverageTarget := True
  realizationCompatibilityTarget := True
  motivicRecognitionInterfaceTarget := True

/-- The unit assignment table forgets to the localization/descent package. -/
def unitGeometricLocalizationPackageFromAssignmentTable
    (ctx : ClassicalComparisonContext.{u, v}) : GeometricLocalizationPackage ctx where
  realization := unitGeometricRealizationFunctorData ctx
  a1Invariance := unitGeometricA1InvarianceTarget ctx
  nisnevichDescent := unitGeometricNisnevichDescentTarget ctx
  openClosedLocalization := unitGeometricOpenClosedLocalizationTarget ctx
  correspondenceFunctoriality := unitGeometricCorrespondenceFunctorialityTarget ctx
  envelopeExactness := unitGeometricEnvelopeExactnessTarget ctx
  realizationCompatibilityTarget := True
  motivicRecognitionInterfaceTarget := True

/-- The unit sanity model inhabits the assignment-table-based readiness interface as well. -/
def unitAssignmentTableClassicalMotivicRealizationReadiness
    (ctx : ClassicalComparisonContext.{u, v}) :
    ClassicalMotivicRealizationReadiness ctx (unitStructuredComparisonEquality ctx) :=
  {
    localizationPackage := unitGeometricLocalizationPackageFromAssignmentTable ctx
    tomographySoundness := unitGeometricRealizationTomographySoundness ctx
    sharedRealizationTarget := rfl
    localizationFeedsTomographyTarget := True
    localizationFeedsMotivicRecognitionTarget := True
  }

/-! ### Example-specific projection lemmas for the unit sanity model. -/

@[simp] theorem unitGeneratorRealizationAssignmentTable_realization
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitGeneratorRealizationAssignmentTable ctx).realization = unitGeometricRealizationFunctorData ctx :=
  rfl

@[simp] theorem unitGeneratorRealizationAssignmentTable_corrAssignment
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitGeneratorRealizationAssignmentTable ctx).corrAssignment =
      unitCorrGeneratorRealizationAssignment ctx := rfl

@[simp] theorem unitGeneratorRealizationAssignmentTable_locAssignment
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitGeneratorRealizationAssignmentTable ctx).locAssignment =
      unitLocGeneratorRealizationAssignment ctx := rfl

@[simp] theorem unitGeneratorRealizationAssignmentTable_nisAssignment
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitGeneratorRealizationAssignmentTable ctx).nisAssignment =
      unitNisGeneratorRealizationAssignment ctx := rfl

@[simp] theorem unitGeneratorRealizationAssignmentTable_a1Assignment
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitGeneratorRealizationAssignmentTable ctx).a1Assignment =
      unitA1GeneratorRealizationAssignment ctx := rfl

@[simp] theorem unitGeneratorRealizationAssignmentTable_envAssignment
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitGeneratorRealizationAssignmentTable ctx).envAssignment =
      unitEnvGeneratorRealizationAssignment ctx := rfl

@[simp] theorem unitGeometricGeneratorFamilyPackage_realization
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitGeometricGeneratorFamilyPackage ctx).realization = unitGeometricRealizationFunctorData ctx := rfl

@[simp] theorem unitGeometricGeneratorFamilyPackage_corrFamily
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitGeometricGeneratorFamilyPackage ctx).corrFamily = unitCorrGeneratorFamilyData ctx := rfl

@[simp] theorem unitGeometricGeneratorFamilyPackage_locFamily
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitGeometricGeneratorFamilyPackage ctx).locFamily = unitLocGeneratorFamilyData ctx := rfl

@[simp] theorem unitGeometricGeneratorFamilyPackage_nisFamily
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitGeometricGeneratorFamilyPackage ctx).nisFamily = unitNisGeneratorFamilyData ctx := rfl

@[simp] theorem unitGeometricGeneratorFamilyPackage_a1Family
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitGeometricGeneratorFamilyPackage ctx).a1Family = unitA1GeneratorFamilyData ctx := rfl

@[simp] theorem unitGeometricGeneratorFamilyPackage_envFamily
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitGeometricGeneratorFamilyPackage ctx).envFamily = unitEnvGeneratorFamilyData ctx := rfl

@[simp] theorem unitGeometricLocalizationPackageFromAssignmentTable_realization
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitGeometricLocalizationPackageFromAssignmentTable ctx).realization =
      unitGeometricRealizationFunctorData ctx := rfl

@[simp] theorem unitGeometricLocalizationPackageFromAssignmentTable_a1Invariance
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitGeometricLocalizationPackageFromAssignmentTable ctx).a1Invariance =
      unitGeometricA1InvarianceTarget ctx := rfl

@[simp] theorem unitGeometricLocalizationPackageFromAssignmentTable_nisnevichDescent
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitGeometricLocalizationPackageFromAssignmentTable ctx).nisnevichDescent =
      unitGeometricNisnevichDescentTarget ctx := rfl

@[simp] theorem unitGeometricLocalizationPackageFromAssignmentTable_openClosedLocalization
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitGeometricLocalizationPackageFromAssignmentTable ctx).openClosedLocalization =
      unitGeometricOpenClosedLocalizationTarget ctx := rfl

@[simp] theorem unitGeometricLocalizationPackageFromAssignmentTable_correspondenceFunctoriality
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitGeometricLocalizationPackageFromAssignmentTable ctx).correspondenceFunctoriality =
      unitGeometricCorrespondenceFunctorialityTarget ctx := rfl

@[simp] theorem unitGeometricLocalizationPackageFromAssignmentTable_envelopeExactness
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitGeometricLocalizationPackageFromAssignmentTable ctx).envelopeExactness =
      unitGeometricEnvelopeExactnessTarget ctx := rfl

@[simp] theorem unitAssignmentTableClassicalMotivicRealizationReadiness_localizationPackage
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitAssignmentTableClassicalMotivicRealizationReadiness ctx).localizationPackage =
      unitGeometricLocalizationPackageFromAssignmentTable ctx := rfl

@[simp] theorem unitAssignmentTableClassicalMotivicRealizationReadiness_tomographySoundness
    (ctx : ClassicalComparisonContext.{u, v}) :
    (unitAssignmentTableClassicalMotivicRealizationReadiness ctx).tomographySoundness =
      unitGeometricRealizationTomographySoundness ctx := rfl

end ClassicalPeriods
end TraceCalc