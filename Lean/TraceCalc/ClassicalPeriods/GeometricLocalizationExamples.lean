import TraceCalc.ClassicalPeriods.GeometricLocalization

universe u v

namespace TraceCalc
namespace ClassicalPeriods

/-- Single-object geometric source used for the first localization/descent sanity model. -/
def UnitGeometricPeriodObject
    (ctx : ClassicalComparisonContext.{u, v}) : GeometricPeriodObject ctx where
  Carrier := PUnit
  object := PUnit.unit
  geometricAdmissibilityTarget := True
  realizationDefinedTarget := True

/-- Identity-only correspondence on the unit geometric source. -/
def UnitGeometricCorrespondence
    (ctx : ClassicalComparisonContext.{u, v}) :
    GeometricCorrespondence (UnitGeometricPeriodObject ctx) (UnitGeometricPeriodObject ctx) where
  correspondenceTarget := True
  compositionTarget := True
  identityTarget := True

/-- Trivial framed source/target data for the unit geometric object. -/
def unitGeometricFramedObject
    (ctx : ClassicalComparisonContext.{u, v}) :
    GeometricFramedObject (UnitGeometricPeriodObject ctx) where
  FrameCarrier := PUnit
  CycleCarrier := PUnit
  frame := PUnit.unit
  cycle := PUnit.unit
  framingAdmissibilityTarget := True
  framingFunctorialityTarget := True

/-- Tautological Betti carrier for the unit sanity model. -/
def unitBettiRealizationCarrier
    (ctx : ClassicalComparisonContext.{u, v}) : BettiRealizationCarrier ctx where
  Carrier := ctx.BaseField

/-- Tautological de Rham carrier for the unit sanity model. -/
def unitDeRhamRealizationCarrier
    (ctx : ClassicalComparisonContext.{u, v}) : DeRhamRealizationCarrier ctx where
  Carrier := ctx.BaseField

noncomputable section

/-- Tautological scalar-extension and comparison isomorphism for the unit sanity model. -/
def unitTensorScalarExtensionData
    (ctx : ClassicalComparisonContext.{u, v}) :
    ComparisonTensorScalarExtensionData
      (ctx := ctx)
      ctx.BaseField
      ctx.BaseField
      ctx.ScalarField
      ctx.ScalarField
      (Algebra.linearMap ctx.BaseField ctx.ScalarField)
      (Algebra.linearMap ctx.BaseField ctx.ScalarField) where
  bettiTensorModel :=
    (TensorProduct.AlgebraTensorModule.rid
      ctx.BaseField
      ctx.ScalarField
      ctx.ScalarField).restrictScalars ctx.BaseField
  deRhamTensorModel :=
    (TensorProduct.AlgebraTensorModule.rid
      ctx.BaseField
      ctx.ScalarField
      ctx.ScalarField).restrictScalars ctx.BaseField
  extendBetti_eq_tensorScalarExtension := by
    ext x
    simp [canonicalTensorScalarExtensionMap]
  extendDeRham_eq_tensorScalarExtension := by
    ext x
    simp [canonicalTensorScalarExtensionMap]

def unitComparisonIsomorphismData
    (ctx : ClassicalComparisonContext.{u, v}) :
    ComparisonIsomorphismData ctx (unitBettiRealizationCarrier ctx) (unitDeRhamRealizationCarrier ctx) where
  BettiOverScalar := ctx.ScalarField
  DeRhamOverScalar := ctx.ScalarField
  extendBetti := Algebra.linearMap ctx.BaseField ctx.ScalarField
  extendDeRham := Algebra.linearMap ctx.BaseField ctx.ScalarField
  comparisonIso := LinearEquiv.refl _ _
  tensorScalarExtensionData := unitTensorScalarExtensionData ctx
  ScalarExtensionWitness := PUnit
  scalarExtensionWitness := PUnit.unit
  comparisonNaturalityTarget := True
  comparisonBaseChangeCompatibility := True

/-- Tautological geometric Betti realization data on the unit source. -/
def unitGeometricBettiRealizationData
    (ctx : ClassicalComparisonContext.{u, v}) : GeometricBettiRealizationData ctx where
  geometricObject := UnitGeometricPeriodObject ctx
  carrier := unitBettiRealizationCarrier ctx
  geometricOriginTarget := True
  realizationFunctorialityTarget := True

/-- Tautological geometric de Rham realization data on the unit source. -/
def unitGeometricDeRhamRealizationData
    (ctx : ClassicalComparisonContext.{u, v}) : GeometricDeRhamRealizationData ctx where
  geometricObject := UnitGeometricPeriodObject ctx
  carrier := unitDeRhamRealizationCarrier ctx
  geometricOriginTarget := True
  realizationFunctorialityTarget := True

/-- Tautological Grothendieck comparison data on the unit source. -/
def unitGrothendieckComparisonData
    (ctx : ClassicalComparisonContext.{u, v}) :
    GrothendieckComparisonData
      ctx
      (unitGeometricBettiRealizationData ctx)
      (unitGeometricDeRhamRealizationData ctx) where
  comparison := unitComparisonIsomorphismData ctx
  sameUnderlyingObject := rfl
  grothendieckComparisonTarget := True
  periodCompatibilityTarget := True

/-- Sigma-packaged geometric comparison object for the unit sanity model. -/
def unitGeometricComparisonObjectData
    (ctx : ClassicalComparisonContext.{u, v}) : GeometricComparisonObjectData ctx :=
  ⟨
    unitGeometricBettiRealizationData ctx,
    unitGeometricDeRhamRealizationData ctx,
    unitGrothendieckComparisonData ctx
  ⟩

/-- Single-object realization functor data used by the localization sanity model. -/
def unitGeometricRealizationFunctorData
    (ctx : ClassicalComparisonContext.{u, v}) : GeometricRealizationFunctorData ctx where
  ObjectIndex := PUnit
  geometricObject := fun _ => UnitGeometricPeriodObject ctx
  CorrespondenceIndex := PUnit
  sourceIndex := fun _ => PUnit.unit
  targetIndex := fun _ => PUnit.unit
  correspondence := fun _ => UnitGeometricCorrespondence ctx
  bettiRealization := fun _ => unitGeometricBettiRealizationData ctx
  deRhamRealization := fun _ => unitGeometricDeRhamRealizationData ctx
  comparisonData := fun _ => unitGrothendieckComparisonData ctx
  objectFunctorialityTarget := True

/-- Concrete comparison object below the structured comparison API for the unit sanity model. -/
def unitConcreteComparisonObjectData
    (ctx : ClassicalComparisonContext.{u, v}) : ConcreteComparisonObjectData ctx where
  betti := unitBettiRealizationCarrier ctx
  deRham := unitDeRhamRealizationCarrier ctx
  comparison := unitComparisonIsomorphismData ctx

/-- Structured comparison object induced by the unit realization data. -/
def unitStructuredComparisonObject
    (ctx : ClassicalComparisonContext.{u, v}) : ClassicalStructuredComparisonObject ctx :=
  (unitConcreteComparisonObjectData ctx).toStructuredComparisonObject

/-- Identity structured comparison morphism on the unit structured comparison object. -/
def unitStructuredComparisonMorphism
    (ctx : ClassicalComparisonContext.{u, v}) :
    ClassicalStructuredComparisonMorphism
      (unitStructuredComparisonObject ctx)
      (unitStructuredComparisonObject ctx) where
  bettiMap := LinearMap.id
  deRhamMap := LinearMap.id
  bettiMapOverScalar := LinearMap.id
  deRhamMapOverScalar := LinearMap.id
  bettiExtensionCompatibility := fun _ => rfl
  deRhamExtensionCompatibility := fun _ => rfl
  comparisonSquareCommutes := by
    ext x
    rfl

/-- Sigma-packaged structured comparison morphism for the unit sanity model. -/
def unitSomeStructuredComparisonMorphism
    (ctx : ClassicalComparisonContext.{u, v}) : SomeStructuredComparisonMorphism ctx :=
  ⟨
    unitStructuredComparisonObject ctx,
    unitStructuredComparisonObject ctx,
    unitStructuredComparisonMorphism ctx
  ⟩

/-- Concrete framed-period witness on the unit structured comparison morphism. -/
def unitConcreteFramedPeriodData
    (ctx : ClassicalComparisonContext.{u, v}) :
    ConcreteFramedPeriodData (unitStructuredComparisonMorphism ctx) where
  deRhamVector := 0
  bettiImage := 0
  bettiCovector := 0
  bettiCycle := 0
  scalarPeriod := 0
  comparisonCompatibility := by
    simp [unitStructuredComparisonMorphism, unitStructuredComparisonObject]
  scalarPeriod_eq_evaluation := by
    simp

/-- Geometric framed-period witness used by the unit sanity model. -/
def unitGeometricFramedPeriodData
    (ctx : ClassicalComparisonContext.{u, v}) :
    @GeometricFramedPeriodData
      ctx
      (unitGeometricComparisonObjectData ctx)
      (unitGeometricComparisonObjectData ctx)
      (unitStructuredComparisonMorphism ctx) where
  geometricCorrespondence := UnitGeometricCorrespondence ctx
  deRhamClass := 0
  bettiClass := 0
  bettiCoframe := 0
  geometricScalarPeriod := 0
  concreteDeRhamVector := 0
  concreteBettiImage := 0
  concreteBettiCycle := 0
  concreteComparisonCompatibility := by
    simp [unitStructuredComparisonMorphism, unitStructuredComparisonObject]
  concreteScalarPeriod_eq_evaluation := by
    simp
  deRhamClassRealizesFrameTarget := True
  bettiClassRealizesCycleTarget := True
  grothendieckPeriodEvaluationTarget := True

/-- Sigma-packaged geometric framed-period witness for the unit sanity model. -/
def unitSomeGeometricFramedPeriodData
    (ctx : ClassicalComparisonContext.{u, v}) : SomeGeometricFramedPeriodData ctx :=
  ⟨
    unitGeometricComparisonObjectData ctx,
    unitGeometricComparisonObjectData ctx,
    unitStructuredComparisonMorphism ctx,
    unitGeometricFramedPeriodData ctx
  ⟩

/-- PUnit-indexed geometric framed datum used by the unit sanity model. -/
def unitGeometricFramedDatum
    (ctx : ClassicalComparisonContext.{u, v}) :
    PUnit → SomeStructuredComparisonMorphism ctx → SomeGeometricFramedPeriodData ctx :=
  fun _ _ => unitSomeGeometricFramedPeriodData ctx

/-- Sigma-packaged concrete framed-period witness for the unit sanity model. -/
def unitSomeConcreteFramedPeriodData
    (ctx : ClassicalComparisonContext.{u, v}) : SomeConcreteFramedPeriodData ctx :=
  ⟨
    unitStructuredComparisonObject ctx,
    unitStructuredComparisonObject ctx,
    unitStructuredComparisonMorphism ctx,
    unitConcreteFramedPeriodData ctx
  ⟩

/-- PUnit-indexed concrete framed datum used by the unit sanity model. -/
def unitConcreteFramedDatum
    (ctx : ClassicalComparisonContext.{u, v}) :
    PUnit → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx :=
  fun _ _ => unitSomeConcreteFramedPeriodData ctx

/-- Tautological soundness of the geometric-to-concrete framed datum for the unit model. -/
def unitGeometricPeriodsRealizeConcreteFramedData
    (ctx : ClassicalComparisonContext.{u, v}) :
    GeometricPeriodsRealizeConcreteFramedData
      ctx
      (unitGeometricFramedDatum ctx) where
  theoremTarget := by
    intro probe morphism
    rfl

/-- Tautological framed-period functoriality target for the unit realization model. -/
def unitGeometricFramedPeriodFunctoriality
    (ctx : ClassicalComparisonContext.{u, v}) :
    GeometricFramedPeriodFunctoriality ctx (unitGeometricRealizationFunctorData ctx) where
  sourceFraming := fun _ => unitGeometricFramedObject ctx
  targetFraming := fun _ => unitGeometricFramedObject ctx
  theoremTarget := by
    intro corr
    refine ⟨unitStructuredComparisonMorphism ctx, ?_⟩
    exact ⟨unitGeometricFramedPeriodData ctx⟩
  framedPeriodFunctorialityTarget := True
  framedExtractionCompatibilityTarget := True

/-- Tautological comparison naturality target for the unit realization model. -/
def unitGeometricComparisonNaturality
    (ctx : ClassicalComparisonContext.{u, v}) :
    GeometricComparisonNaturality ctx (unitGeometricRealizationFunctorData ctx) where
  theoremTarget := by
    intro corr
    simp [unitGeometricRealizationFunctorData, unitGrothendieckComparisonData,
      unitComparisonIsomorphismData]
  baseChangeNaturalityTarget := True

/-- Trivial structured-comparison equality used only for the unit sanity model. -/
def unitStructuredComparisonEquality
    (ctx : ClassicalComparisonContext.{u, v}) : StructuredComparisonEquality ctx where
  relates := fun _ _ => True
  reflexiveTarget := True
  symmetricTarget := True
  transitiveTarget := True

/-- Trivial basis-free equality used only for the unit sanity model. -/
def unitBasisFreePeriodMapEquality
    (ctx : ClassicalComparisonContext.{u, v}) : BasisFreePeriodMapEquality ctx where
  relates := fun _ _ => True
  reflexiveTarget := True
  symmetricTarget := True
  transitiveTarget := True

/-- Trivial probe extensionality used only for the unit sanity model. -/
def unitProbeExtensionality
    (ctx : ClassicalComparisonContext.{u, v}) :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily (fun probe morphism =>
        ((unitGeometricFramedDatum ctx) probe morphism).toSomeConcreteFramedPeriodData)).toScalarProbeFamily
      (unitBasisFreePeriodMapEquality ctx) where
  theoremTarget := by
    intro left right hProbe
    trivial

/-- Trivial packed reconstruction used only for the unit sanity model. -/
def unitPackedComparisonReconstruction
    (ctx : ClassicalComparisonContext.{u, v}) :
    BasisFreePeriodMapDeterminesPackedComparison
      ctx
      (unitBasisFreePeriodMapEquality ctx)
      (unitStructuredComparisonEquality ctx) where
  theoremTarget := by
    intro left right hBasis
    trivial

/-- Tautological geometric-realization/tomography package for the unit sanity model. -/
def unitGeometricRealizationTomographySoundness
    (ctx : ClassicalComparisonContext.{u, v}) :
    GeometricRealizationTomographySoundness ctx (unitStructuredComparisonEquality ctx) where
  geometricRealizationFunctor := unitGeometricRealizationFunctorData ctx
  geometricFramedFunctoriality := unitGeometricFramedPeriodFunctoriality ctx
  geometricComparisonNaturality := unitGeometricComparisonNaturality ctx
  geometricObjectData := fun _ => unitGeometricComparisonObjectData ctx
  objectDataCompatibilityTarget := by
    intro idx
    rfl
  ProbeIndex := PUnit
  geometricFramedDatum := fun _ _ => unitSomeGeometricFramedPeriodData ctx
  geometricToConcreteFramed := unitGeometricPeriodsRealizeConcreteFramedData ctx
  basisFreePeriodMapEquality := unitBasisFreePeriodMapEquality ctx
  probeExtensionality := unitProbeExtensionality ctx
  packedReconstruction := unitPackedComparisonReconstruction ctx

/-- Tautological A1-invariance target for the unit localization model. -/
def unitGeometricA1InvarianceTarget
    (ctx : ClassicalComparisonContext.{u, v}) :
    GeometricA1InvarianceTarget ctx (unitGeometricRealizationFunctorData ctx) where
  affineLineIndex := fun _ => PUnit.unit
  objectAssignmentTarget := by
    intro idx
    exact ⟨True.intro, True.intro⟩
  comparisonInvarianceTarget := True
  framedExtractionInvarianceTarget := True
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
        exact True.intro
      homotopyInvariance_holds := True.intro }

/-- Tautological Nisnevich descent target for the unit localization model. -/
def unitGeometricNisnevichDescentTarget
    (ctx : ClassicalComparisonContext.{u, v}) :
    GeometricNisnevichDescentTarget ctx (unitGeometricRealizationFunctorData ctx) where
  CoverIndex := PUnit
  baseIndex := fun _ => PUnit.unit
  patchIndex := fun _ => PUnit.unit
  overlapIndex := fun _ => PUnit.unit
  coverCompatibilityTarget := by
    intro cover
    exact ⟨True.intro, True.intro, True.intro⟩
  comparisonDescentTarget := by
    intro cover
    exact ⟨True.intro, True.intro, True.intro⟩
  gluingTheoremTarget := True
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
        intro cover
        exact ⟨True.intro, True.intro, True.intro⟩
      descentSquareCompatibility_holds := True.intro }

/-- Tautological open/closed localization target for the unit localization model. -/
def unitGeometricOpenClosedLocalizationTarget
    (ctx : ClassicalComparisonContext.{u, v}) :
    GeometricOpenClosedLocalizationTarget ctx (unitGeometricRealizationFunctorData ctx) where
  LocalizationIndex := PUnit
  ambientIndex := fun _ => PUnit.unit
  openIndex := fun _ => PUnit.unit
  closedIndex := fun _ => PUnit.unit
  openImmersionTarget := by
    intro loc
    exact ⟨True.intro, True.intro⟩
  closedImmersionTarget := by
    intro loc
    exact ⟨True.intro, True.intro⟩
  comparisonLocalizationTarget := by
    intro loc
    exact ⟨True.intro, True.intro, True.intro⟩
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

/-- Tautological correspondence functoriality target for the unit localization model. -/
def unitGeometricCorrespondenceFunctorialityTarget
    (ctx : ClassicalComparisonContext.{u, v}) :
    GeometricCorrespondenceFunctorialityTarget ctx (unitGeometricRealizationFunctorData ctx) where
  theoremTarget := by
    intro corr
    exact ⟨True.intro, True.intro, True.intro, True.intro, True.intro⟩
  compositionFunctorialityTarget := True
  identityFunctorialityTarget := True

/-- Tautological envelope exactness target for the unit localization model. -/
def unitGeometricEnvelopeExactnessTarget
    (ctx : ClassicalComparisonContext.{u, v}) :
    GeometricEnvelopeExactnessTarget ctx (unitGeometricRealizationFunctorData ctx) where
  EnvelopeIndex := PUnit
  ambientIndex := fun _ => PUnit.unit
  envelopeIndex := fun _ => PUnit.unit
  envelopeCorrespondence := fun _ => UnitGeometricCorrespondence ctx
  exactnessInputTarget := by
    intro env
    exact ⟨True.intro, True.intro, True.intro⟩
  comparisonExactnessTarget := by
    intro env
    exact ⟨True.intro, True.intro⟩
  formalClosureTarget := True
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
        intro env
        exact ⟨True.intro, True.intro, True.intro, True.intro, True.intro⟩
      formalClosure_holds := True.intro }

/-- The first concrete sanity localization package for the geometric localization/descent layer. -/
def unitGeometricLocalizationPackage
    (ctx : ClassicalComparisonContext.{u, v}) : GeometricLocalizationPackage ctx where
  realization := unitGeometricRealizationFunctorData ctx
  a1Invariance := unitGeometricA1InvarianceTarget ctx
  nisnevichDescent := unitGeometricNisnevichDescentTarget ctx
  openClosedLocalization := unitGeometricOpenClosedLocalizationTarget ctx
  correspondenceFunctoriality := unitGeometricCorrespondenceFunctorialityTarget ctx
  envelopeExactness := unitGeometricEnvelopeExactnessTarget ctx
  realizationCompatibilityTarget := True
  motivicRecognitionInterfaceTarget := True

/-- The unit sanity model inhabits the first motivic-realization readiness interface as well. -/
def unitClassicalMotivicRealizationReadiness
    (ctx : ClassicalComparisonContext.{u, v}) :
    ClassicalMotivicRealizationReadiness ctx (unitStructuredComparisonEquality ctx) :=
  (unitGeometricLocalizationPackage ctx).toClassicalMotivicRealizationReadiness
    (unitGeometricRealizationTomographySoundness ctx)
    rfl

end

end ClassicalPeriods
end TraceCalc
