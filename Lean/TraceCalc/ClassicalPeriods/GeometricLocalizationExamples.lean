import TraceCalc.ClassicalPeriods.GeometricLocalization

universe u v

namespace TraceCalc
namespace ClassicalPeriods

/-- Single-object geometric source used for the first localization/descent sanity model. -/
def UnitGeometricPeriodObject
    (ctx : ClassicalComparisonContext.{u, v}) : GeometricPeriodObject ctx where
  Carrier := PUnit.{1}
  object := PUnit.unit
  geometricAdmissibilityTarget := Nonempty PUnit.{1}
  realizationDefinedTarget := ∀ x : PUnit.{1}, x = PUnit.unit

/-- Identity-only correspondence on the unit geometric source. -/
def UnitGeometricCorrespondence
    (ctx : ClassicalComparisonContext.{u, v}) :
    GeometricCorrespondence (UnitGeometricPeriodObject ctx) (UnitGeometricPeriodObject ctx) where
  correspondenceTarget := Nonempty PUnit.{1}
  compositionTarget := ∀ x : PUnit.{1}, x = PUnit.unit
  identityTarget := (PUnit.unit : PUnit.{1}) = PUnit.unit

/-- Trivial framed source/target data for the unit geometric object. -/
def unitGeometricFramedObject
    (ctx : ClassicalComparisonContext.{u, v}) :
    GeometricFramedObject (UnitGeometricPeriodObject ctx) where
  FrameCarrier := PUnit.{1}
  CycleCarrier := PUnit.{1}
  frame := PUnit.unit
  cycle := PUnit.unit
  framingAdmissibilityTarget :=
    (∃ frame : PUnit.{1}, frame = PUnit.unit) ∧
      (∃ cycle : PUnit.{1}, cycle = PUnit.unit)
  framingFunctorialityTarget :=
    (∀ frame : PUnit.{1}, frame = PUnit.unit) ∧
      (∀ cycle : PUnit.{1}, cycle = PUnit.unit)

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
  ScalarExtensionWitness := PUnit.{1}
  scalarExtensionWitness := (PUnit.unit : PUnit.{1})
  comparisonNaturalityTarget :=
    ∀ a : ctx.ScalarField,
      (LinearEquiv.refl ctx.ScalarField ctx.ScalarField) a = a
  comparisonBaseChangeCompatibility :=
    (∀ a : ctx.BaseField,
      (Algebra.linearMap ctx.BaseField ctx.ScalarField) a =
        (Algebra.linearMap ctx.BaseField ctx.ScalarField) a) ∧
    (∀ a : ctx.BaseField,
      (Algebra.linearMap ctx.BaseField ctx.ScalarField) a =
        (Algebra.linearMap ctx.BaseField ctx.ScalarField) a)

/-- Tautological geometric Betti realization data on the unit source. -/
def unitGeometricBettiRealizationData
    (ctx : ClassicalComparisonContext.{u, v}) : GeometricBettiRealizationData ctx where
  geometricObject := UnitGeometricPeriodObject ctx
  carrier := unitBettiRealizationCarrier ctx
  geometricOriginTarget := (UnitGeometricPeriodObject ctx).object = PUnit.unit
  realizationFunctorialityTarget := (unitBettiRealizationCarrier ctx).Carrier = ctx.BaseField

/-- Tautological geometric de Rham realization data on the unit source. -/
def unitGeometricDeRhamRealizationData
    (ctx : ClassicalComparisonContext.{u, v}) : GeometricDeRhamRealizationData ctx where
  geometricObject := UnitGeometricPeriodObject ctx
  carrier := unitDeRhamRealizationCarrier ctx
  geometricOriginTarget := (UnitGeometricPeriodObject ctx).object = PUnit.unit
  realizationFunctorialityTarget := (unitDeRhamRealizationCarrier ctx).Carrier = ctx.BaseField

/-- Tautological Grothendieck comparison data on the unit source. -/
def unitGrothendieckComparisonData
    (ctx : ClassicalComparisonContext.{u, v}) :
    GrothendieckComparisonData
      ctx
      (unitGeometricBettiRealizationData ctx)
      (unitGeometricDeRhamRealizationData ctx) where
  comparison := unitComparisonIsomorphismData ctx
  sameUnderlyingObject := rfl
  grothendieckComparisonTarget :=
    (unitGeometricBettiRealizationData ctx).geometricObject =
      (unitGeometricDeRhamRealizationData ctx).geometricObject
  periodCompatibilityTarget :=
    ∀ a : ctx.BaseField,
      (unitComparisonIsomorphismData ctx).extendBetti a =
        (unitComparisonIsomorphismData ctx).extendDeRham a

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
  ObjectIndex := PUnit.{1}
  geometricObject := fun _ => UnitGeometricPeriodObject ctx
  CorrespondenceIndex := PUnit.{1}
  sourceIndex := fun _ => PUnit.unit
  targetIndex := fun _ => PUnit.unit
  correspondence := fun _ => UnitGeometricCorrespondence ctx
  bettiRealization := fun _ => unitGeometricBettiRealizationData ctx
  deRhamRealization := fun _ => unitGeometricDeRhamRealizationData ctx
  comparisonData := fun _ => unitGrothendieckComparisonData ctx
  objectFunctorialityTarget :=
    ∀ idx : PUnit.{1}, (UnitGeometricPeriodObject ctx).object = PUnit.unit

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
  PUnit.{1} → SomeStructuredComparisonMorphism ctx → SomeGeometricFramedPeriodData ctx :=
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
  PUnit.{1} → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx :=
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
  framedPeriodFunctorialityTarget := (unitGeometricFramedObject ctx).framingFunctorialityTarget
  framedExtractionCompatibilityTarget := (unitGeometricFramedObject ctx).framingAdmissibilityTarget

/-- Tautological comparison naturality target for the unit realization model. -/
def unitGeometricComparisonNaturality
    (ctx : ClassicalComparisonContext.{u, v}) :
    GeometricComparisonNaturality ctx (unitGeometricRealizationFunctorData ctx) where
  theoremTarget := by
    intro corr
    simp [unitGeometricRealizationFunctorData, unitGrothendieckComparisonData,
      unitComparisonIsomorphismData]
  baseChangeNaturalityTarget := True

/-- Probe-induced equality relation used by the unit sanity model. -/
def unitProbeEqualityRelation
    (ctx : ClassicalComparisonContext.{u, v}) :
    SomeStructuredComparisonMorphism ctx → SomeStructuredComparisonMorphism ctx → Prop :=
  fun _ _ => True

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
    exact True.intro

/-- Trivial packed reconstruction used only for the unit sanity model. -/
def unitPackedComparisonReconstruction
    (ctx : ClassicalComparisonContext.{u, v}) :
    BasisFreePeriodMapDeterminesPackedComparison
      ctx
      (unitBasisFreePeriodMapEquality ctx)
      (unitStructuredComparisonEquality ctx) where
  theoremTarget := by
    intro left right hBasis
    exact True.intro

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
  ProbeIndex := PUnit.{1}
  geometricFramedDatum := fun _ _ => unitSomeGeometricFramedPeriodData ctx
  geometricToConcreteFramed := unitGeometricPeriodsRealizeConcreteFramedData ctx
  basisFreePeriodMapEquality := unitBasisFreePeriodMapEquality ctx
  probeExtensionality := unitProbeExtensionality ctx
  packedReconstruction := unitPackedComparisonReconstruction ctx

/-- Tautological A1-invariance target for the unit localization model. -/
def unitGeometricA1InvarianceTarget
    (ctx : ClassicalComparisonContext.{u, v}) :
    GeometricA1InvarianceTarget ctx (unitGeometricRealizationFunctorData ctx) where
  affineLineIndex := fun _ => (PUnit.unit : PUnit.{1})
  objectAssignmentTarget := by
    intro idx
    exact ⟨⟨PUnit.unit⟩, ⟨PUnit.unit⟩⟩
  comparisonInvarianceTarget := True
  framedExtractionInvarianceTarget := (unitGeometricFramedObject ctx).framingFunctorialityTarget
  traceNativeHomotopyReplayData :=
    { cylinderEndpointReplayTarget :=
        { ReplayWitness := PUnit.{1}
          replayWitness := (PUnit.unit : PUnit.{1})
          basePacketTarget := (UnitGeometricPeriodObject ctx).object = (PUnit.unit : PUnit.{1})
          cylinderPacketTarget := (UnitGeometricPeriodObject ctx).object = (PUnit.unit : PUnit.{1})
          endpointZeroPacketTarget := (PUnit.unit : PUnit.{1}) = PUnit.unit
          endpointOnePacketTarget := (PUnit.unit : PUnit.{1}) = PUnit.unit
          cylinderReplayTarget := ∀ x : PUnit.{1}, x = PUnit.unit
          endpointZeroReplayTarget := ∀ x : PUnit.{1}, x = PUnit.unit
          endpointOneReplayTarget := ∀ x : PUnit.{1}, x = PUnit.unit
          endpointAgreementTarget := True
          endpointComparisonNaturalityTarget := True }
      baseBettiReplayTarget := (unitGeometricBettiRealizationData ctx).carrier.Carrier = ctx.BaseField
      cylinderBettiReplayTarget := (unitGeometricBettiRealizationData ctx).carrier.Carrier = ctx.BaseField
      baseDeRhamReplayTarget := (unitGeometricDeRhamRealizationData ctx).carrier.Carrier = ctx.BaseField
      cylinderDeRhamReplayTarget := (unitGeometricDeRhamRealizationData ctx).carrier.Carrier = ctx.BaseField
      projectionZeroComparisonNaturalityTarget := True
      projectionOneComparisonNaturalityTarget := True
      endpointAgreement_holds := True.intro
      homotopyInvariance_holds := by
        constructor <;> intro x <;> cases x <;> rfl }

/-- Tautological Nisnevich descent target for the unit localization model. -/
def unitGeometricNisnevichDescentTarget
    (ctx : ClassicalComparisonContext.{u, v}) :
    GeometricNisnevichDescentTarget ctx (unitGeometricRealizationFunctorData ctx) where
  CoverIndex := PUnit.{1}
  baseIndex := fun _ => (PUnit.unit : PUnit.{1})
  patchIndex := fun _ => (PUnit.unit : PUnit.{1})
  overlapIndex := fun _ => (PUnit.unit : PUnit.{1})
  coverCompatibilityTarget := by
    intro cover
    exact ⟨(by intro x; cases x; rfl), (by intro x; cases x; rfl), (by intro x; cases x; rfl)⟩
  comparisonDescentTarget := by
    intro cover
    exact ⟨rfl, rfl, rfl⟩
  gluingTheoremTarget := True
  traceNativePatchReplayData :=
    { overlapGluingTarget :=
        { ReplayWitness := PUnit.{1}
          replayWitness := PUnit.unit
          basePacketTarget := (UnitGeometricPeriodObject ctx).object = (PUnit.unit : PUnit.{1})
          patchPacketTarget := (UnitGeometricPeriodObject ctx).object = (PUnit.unit : PUnit.{1})
          overlapPacketTarget := (UnitGeometricPeriodObject ctx).object = (PUnit.unit : PUnit.{1})
          basePatchAgreementOnOverlapTarget := (PUnit.unit : PUnit.{1}) = PUnit.unit
          gluedReplayTarget := ∀ x : PUnit.{1}, x = PUnit.unit
          gluedReplayRestrictsToBaseTarget := ∀ x : PUnit.{1}, x = PUnit.unit
          gluedReplayRestrictsToPatchTarget := ∀ x : PUnit.{1}, x = PUnit.unit
          overlapComparisonNaturalityTarget := True }
      bettiPatchReplayTarget := (unitGeometricBettiRealizationData ctx).carrier.Carrier = ctx.BaseField
      deRhamPatchReplayTarget := (unitGeometricDeRhamRealizationData ctx).carrier.Carrier = ctx.BaseField
      baseComparisonNaturalityTarget := True
      patchComparisonNaturalityTarget := True
      overlapComparisonNaturalityTarget := True
      overlapAgreement_holds := by
        intro cover
        exact ⟨rfl, rfl, rfl⟩
      descentSquareCompatibility_holds := True.intro }

/-- Tautological open/closed localization target for the unit localization model. -/
def unitGeometricOpenClosedLocalizationTarget
    (ctx : ClassicalComparisonContext.{u, v}) :
    GeometricOpenClosedLocalizationTarget ctx (unitGeometricRealizationFunctorData ctx) where
  LocalizationIndex := PUnit.{1}
  ambientIndex := fun _ => (PUnit.unit : PUnit.{1})
  openIndex := fun _ => (PUnit.unit : PUnit.{1})
  closedIndex := fun _ => (PUnit.unit : PUnit.{1})
  openImmersionTarget := by
    intro loc
    exact ⟨⟨PUnit.unit⟩, ⟨PUnit.unit⟩⟩
  closedImmersionTarget := by
    intro loc
    exact ⟨⟨PUnit.unit⟩, ⟨PUnit.unit⟩⟩
  comparisonLocalizationTarget := by
    intro loc
    exact ⟨(by intro a; rfl), (by intro a; rfl), (by intro a; rfl)⟩
  coneNaturalityData :=
    { leftSquareCommutes := True
      middleSquareCommutes := True
      coneInducedMapEqOpenComparison := True
      coneTriangleFunctorialityData :=
        { sourceArrow :=
            { Closed := PUnit.{1}
              Ambient := PUnit.{1}
              closedToAmbient := fun _ => (PUnit.unit : PUnit.{1}) }
          targetArrow :=
            { Closed := PUnit.{1}
              Ambient := PUnit.{1}
              closedToAmbient := fun _ => (PUnit.unit : PUnit.{1}) }
          arrowMorphism :=
            { left := fun _ => (PUnit.unit : PUnit.{1})
              right := fun _ => (PUnit.unit : PUnit.{1})
              squareCommutes := rfl } }
      traceNativeReplayData :=
        { sinkPeelReplayTarget :=
            { ReplayWitness := PUnit.{1}
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
    exact ⟨⟨PUnit.unit⟩, (by intro x; cases x; rfl), (by intro x; cases x; rfl), rfl, rfl⟩
  compositionFunctorialityTarget := True
  identityFunctorialityTarget := True

/-- Tautological Tate/`P1` stabilization target for the unit localization model. -/
def unitGeometricTateStabilizationTarget
    (ctx : ClassicalComparisonContext.{u, v}) :
    GeometricTateStabilizationTarget ctx (unitGeometricRealizationFunctorData ctx) where
  TateWitness := PUnit.{1}
  tateWitness := PUnit.unit
  tateIndex := fun _ => (PUnit.unit : PUnit.{1})
  p1Index := fun _ => (PUnit.unit : PUnit.{1})
  stabilizeWithTate := fun _ _ => (PUnit.unit : PUnit.{1})
  stabilizeWithP1 := fun _ _ => (PUnit.unit : PUnit.{1})
  tateObjectTarget := by
    intro witness
    exact ⟨rfl, by intro a; rfl⟩
  p1ObjectTarget := by
    intro witness
    exact ⟨rfl, by intro a; rfl⟩
  stabilizationComparisonTarget := by
    intro witness idx
    exact ⟨rfl, rfl, (by intro a; rfl), (by intro a; rfl)⟩
  localizationRespectsStabilizationTarget := True
  localizationRespectsStabilizationTarget_holds := True.intro

/-- Tautological envelope exactness target for the unit localization model. -/
def unitGeometricEnvelopeExactnessTarget
    (ctx : ClassicalComparisonContext.{u, v}) :
    GeometricEnvelopeExactnessTarget ctx (unitGeometricRealizationFunctorData ctx) where
  EnvelopeIndex := PUnit.{1}
  ambientIndex := fun _ => (PUnit.unit : PUnit.{1})
  envelopeIndex := fun _ => (PUnit.unit : PUnit.{1})
  envelopeCorrespondence := fun _ => UnitGeometricCorrespondence ctx
  exactnessInputTarget := by
    intro env
    exact ⟨⟨PUnit.unit⟩, rfl, rfl⟩
  comparisonExactnessTarget := by
    intro env
    exact ⟨(by intro a; rfl), (by intro a; rfl)⟩
  formalClosureTarget := True
  traceNativeEnvReplayData :=
    { replayTransformerTarget :=
        { ReplayWitness := PUnit.{1}
          replayWitness := (PUnit.unit : PUnit.{1})
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
        exact ⟨⟨PUnit.unit⟩, rfl, rfl, (by intro a; rfl), (by intro a; rfl)⟩
      formalClosure_holds := True.intro }

/-- The first concrete sanity localization package for the geometric localization/descent layer. -/
def unitGeometricLocalizationPackage
    (ctx : ClassicalComparisonContext.{u, v}) : GeometricLocalizationPackage ctx where
  realization := unitGeometricRealizationFunctorData ctx
  a1Invariance := unitGeometricA1InvarianceTarget ctx
  nisnevichDescent := unitGeometricNisnevichDescentTarget ctx
  openClosedLocalization := unitGeometricOpenClosedLocalizationTarget ctx
  tateStabilization := unitGeometricTateStabilizationTarget ctx
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
