import TraceCalc.ClassicalPeriods.ComparisonBoundaryRecovery
import TraceCalc.ClassicalPeriods.ManuscriptTargetSupport

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

/-- Trivial framed placeholder used when a symbolic generator row needs named framed slots without
committing to any geometric cycle theory yet. -/
def symbolicPlaceholderFramedObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (object : GeometricPeriodObject ctx) : GeometricFramedObject object where
  FrameCarrier := PUnit
  CycleCarrier := PUnit
  frame := PUnit.unit
  cycle := PUnit.unit
  framingAdmissibilityTarget := True
  framingFunctorialityTarget := True

/-- Symbolic datum for the manuscript's `Corr` row.

This packages an arbitrary source object, target object, correspondence, and their attached
comparison-object data, together with only the compatibility targets needed to feed the theorem-
target layer. No finite-correspondence functoriality is proved here. -/
structure SymbolicCorrCanonicalRawPayloadSource
    {ctx : ClassicalComparisonContext.{u, v}}
    {sourceObject targetObject : GeometricPeriodObject ctx}
    (sourceObjectData targetObjectData : GeometricComparisonObjectData ctx)
    (correspondence : GeometricCorrespondence sourceObject targetObject) where
  structuredMorphism :
    ClassicalStructuredComparisonMorphism
      sourceObjectData.toStructuredComparisonObject
      targetObjectData.toStructuredComparisonObject
  geometricCorrespondence :
    GeometricCorrespondence sourceObjectData.deRhamData.geometricObject
      targetObjectData.bettiData.geometricObject
  deRhamClass : sourceObjectData.DeRhamCarrier
  bettiClass : targetObjectData.BettiCarrier
  bettiCoframe :
    targetObjectData.toStructuredComparisonObject.BettiOverScalar →ₗ[ctx.ScalarField]
      ctx.ScalarField
  geometricScalarPeriod : ctx.ScalarField
  concreteDeRhamVector : sourceObjectData.toStructuredComparisonObject.DeRhamOverScalar
  concreteBettiImage : targetObjectData.toStructuredComparisonObject.BettiOverScalar
  concreteBettiCycle : targetObjectData.toStructuredComparisonObject.BettiOverScalar
  concreteComparisonCompatibility :
    concreteBettiImage = targetObjectData.toStructuredComparisonObject.comparisonIso
      (structuredMorphism.deRhamMapOverScalar concreteDeRhamVector)
  concreteScalarPeriod_eq_evaluation :
    geometricScalarPeriod = bettiCoframe concreteBettiImage
  correspondenceRealizesGeometryTarget : correspondence.correspondenceTarget
  sourceComparisonNaturalityTarget :
    sourceObjectData.comparisonData.comparison.comparisonNaturalityTarget
  targetComparisonNaturalityTarget :
    targetObjectData.comparisonData.comparison.comparisonNaturalityTarget
  deRhamClassRealizesFrameTarget : Prop
  bettiClassRealizesCycleTarget : Prop
  grothendieckPeriodEvaluationTarget : Prop

structure SymbolicCorrDatum
    (ctx : ClassicalComparisonContext.{u, v}) where
  source : GeometricPeriodObject ctx
  target : GeometricPeriodObject ctx
  correspondence : GeometricCorrespondence source target
  correspondenceCompatibilityTarget : correspondence.correspondenceTarget
  sourceObjectData : GeometricComparisonObjectData ctx
  targetObjectData : GeometricComparisonObjectData ctx
  canonicalRawPayloadSource :
    SymbolicCorrCanonicalRawPayloadSource sourceObjectData targetObjectData correspondence
  sourceBettiCompatibilityTarget : source = sourceObjectData.bettiData.geometricObject
  sourceDeRhamCompatibilityTarget : source = sourceObjectData.deRhamData.geometricObject
  targetBettiCompatibilityTarget : target = targetObjectData.bettiData.geometricObject
  targetDeRhamCompatibilityTarget : target = targetObjectData.deRhamData.geometricObject
  sourceComparisonCompatibilityTarget : sourceObjectData.comparisonData.grothendieckComparisonTarget
  targetComparisonCompatibilityTarget : targetObjectData.comparisonData.grothendieckComparisonTarget
  sourcePeriodCompatibilityTarget : sourceObjectData.comparisonData.periodCompatibilityTarget
  targetPeriodCompatibilityTarget : targetObjectData.comparisonData.periodCompatibilityTarget

/-- Named object slots for the symbolic `Corr` example. -/
inductive SymbolicCorrObjectSlot
  | source
  | target
deriving DecidableEq, Repr

/-- Named correspondence slot for the symbolic `Corr` example. -/
inductive SymbolicCorrCorrespondenceSlot
  | corr
deriving DecidableEq, Repr

/-- Realization-functor surface for a single symbolic `Corr` generator. -/
def symbolicCorrRealizationFunctorData
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicCorrDatum ctx) : GeometricRealizationFunctorData ctx where
  ObjectIndex := SymbolicCorrObjectSlot
  geometricObject
    | .source => datum.source
    | .target => datum.target
  CorrespondenceIndex := SymbolicCorrCorrespondenceSlot
  sourceIndex := fun _ => .source
  targetIndex := fun _ => .target
  correspondence := fun _ => datum.correspondence
  bettiRealization
    | .source => datum.sourceObjectData.bettiData
    | .target => datum.targetObjectData.bettiData
  deRhamRealization
    | .source => datum.sourceObjectData.deRhamData
    | .target => datum.targetObjectData.deRhamData
  comparisonData
    | .source => datum.sourceObjectData.comparisonData
    | .target => datum.targetObjectData.comparisonData
  objectFunctorialityTarget :=
    datum.sourceObjectData.comparisonData.grothendieckComparisonTarget ∧
      datum.targetObjectData.comparisonData.grothendieckComparisonTarget

/-- Package a single symbolic correspondence datum as a one-generator `Corr` family. -/
def symbolicCorrGeneratorFamilyData
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicCorrDatum ctx) :
    CorrGeneratorFamilyData ctx (symbolicCorrRealizationFunctorData datum) where
  GeneratorIndex := PUnit
  sourceIndex := fun _ => .source
  targetIndex := fun _ => .target
  sourceObject := fun _ => datum.source
  targetObject := fun _ => datum.target
  generatorCorrespondence := fun _ => datum.correspondence
  sourceObjectData := fun _ => datum.sourceObjectData
  targetObjectData := fun _ => datum.targetObjectData
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
    exact ⟨
      datum.correspondenceCompatibilityTarget,
      datum.sourceComparisonCompatibilityTarget,
      datum.targetComparisonCompatibilityTarget
    ⟩

/-- Typed realization assignment for the single symbolic `Corr` generator. -/
def symbolicCorrGeneratorRealizationAssignment
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicCorrDatum ctx) :
    CorrGeneratorRealizationAssignment ctx (symbolicCorrRealizationFunctorData datum) where
  family := symbolicCorrGeneratorFamilyData datum
  sourceSlotName := "source"
  targetSlotName := "target"
  correspondenceSlotName := "corr"
  bettiSlotName := "betti"
  deRhamSlotName := "deRham"
  comparisonSlotName := "comparison"
  framedSlotName := "framed"
  scalarSlotName := "scalar"
  sourceProjection := fun _ => datum.source
  targetProjection := fun _ => datum.target
  sourceBettiPlaceholder := fun _ => datum.sourceObjectData.bettiData
  targetBettiPlaceholder := fun _ => datum.targetObjectData.bettiData
  sourceDeRhamPlaceholder := fun _ => datum.sourceObjectData.deRhamData
  targetDeRhamPlaceholder := fun _ => datum.targetObjectData.deRhamData
  sourceComparisonDatum := fun _ => datum.sourceObjectData.comparisonData
  targetComparisonDatum := fun _ => datum.targetObjectData.comparisonData
  sourceFramedPlaceholder := fun _ => symbolicPlaceholderFramedObject datum.source
  targetFramedPlaceholder := fun _ => symbolicPlaceholderFramedObject datum.target
  sourceComparisonCompatibilityTarget := by
    intro gen
    rfl
  targetComparisonCompatibilityTarget := by
    intro gen
    rfl
  scalarExtractionTarget :=
    datum.sourceObjectData.comparisonData.periodCompatibilityTarget ∧
      datum.targetObjectData.comparisonData.periodCompatibilityTarget
  framedExtractionTarget := True
  theoremTarget := by
    intro gen
    exact ⟨datum.sourceComparisonCompatibilityTarget, datum.targetComparisonCompatibilityTarget⟩

@[simp] theorem symbolicCorrRealizationFunctorData_geometricObject_source
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicCorrDatum ctx) :
    (symbolicCorrRealizationFunctorData datum).geometricObject .source = datum.source := rfl

@[simp] theorem symbolicCorrRealizationFunctorData_geometricObject_target
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicCorrDatum ctx) :
    (symbolicCorrRealizationFunctorData datum).geometricObject .target = datum.target := rfl

@[simp] theorem symbolicCorrGeneratorFamilyData_sourceObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicCorrDatum ctx) :
    (symbolicCorrGeneratorFamilyData datum).sourceObject PUnit.unit = datum.source := rfl

@[simp] theorem symbolicCorrGeneratorFamilyData_targetObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicCorrDatum ctx) :
    (symbolicCorrGeneratorFamilyData datum).targetObject PUnit.unit = datum.target := rfl

@[simp] theorem symbolicCorrGeneratorRealizationAssignment_sourceComparisonDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicCorrDatum ctx) :
    (symbolicCorrGeneratorRealizationAssignment datum).sourceComparisonDatum PUnit.unit =
      datum.sourceObjectData.comparisonData := rfl

@[simp] theorem symbolicCorrGeneratorRealizationAssignment_targetComparisonDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicCorrDatum ctx) :
    (symbolicCorrGeneratorRealizationAssignment datum).targetComparisonDatum PUnit.unit =
      datum.targetObjectData.comparisonData := rfl

inductive SymbolicCorrCanonicalProbe
  | canonical
deriving DecidableEq, Repr

def symbolicCorrCanonicalStructuredMorphism
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicCorrDatum ctx) :
    ClassicalStructuredComparisonMorphism
      datum.sourceObjectData.toStructuredComparisonObject
      datum.targetObjectData.toStructuredComparisonObject :=
  datum.canonicalRawPayloadSource.structuredMorphism

def symbolicCorrCanonicalGeometricRawPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicCorrDatum ctx) :
    GeometricFramedPeriodRawPayload (symbolicCorrCanonicalStructuredMorphism datum) :=
  { geometricCorrespondence := datum.canonicalRawPayloadSource.geometricCorrespondence
    deRhamClass := datum.canonicalRawPayloadSource.deRhamClass
    bettiClass := datum.canonicalRawPayloadSource.bettiClass
    bettiCoframe := datum.canonicalRawPayloadSource.bettiCoframe
    geometricScalarPeriod := datum.canonicalRawPayloadSource.geometricScalarPeriod
    concreteDeRhamVector := datum.canonicalRawPayloadSource.concreteDeRhamVector
    concreteBettiImage := datum.canonicalRawPayloadSource.concreteBettiImage
    concreteBettiCycle := datum.canonicalRawPayloadSource.concreteBettiCycle
    concreteComparisonCompatibility :=
      datum.canonicalRawPayloadSource.concreteComparisonCompatibility
    concreteScalarPeriod_eq_evaluation :=
      datum.canonicalRawPayloadSource.concreteScalarPeriod_eq_evaluation
    deRhamClassRealizesFrameTarget :=
      datum.canonicalRawPayloadSource.deRhamClassRealizesFrameTarget
    bettiClassRealizesCycleTarget :=
      datum.canonicalRawPayloadSource.bettiClassRealizesCycleTarget
    grothendieckPeriodEvaluationTarget :=
      datum.canonicalRawPayloadSource.grothendieckPeriodEvaluationTarget }

def symbolicCorrCanonicalConcreteFramedDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicCorrDatum ctx) :
    SymbolicCorrCanonicalProbe → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx :=
  fun _ _ =>
    (SomeGeometricFramedPeriodData.ofRawPayload
      datum.sourceObjectData
      datum.targetObjectData
      datum.canonicalRawPayloadSource.structuredMorphism
      (symbolicCorrCanonicalGeometricRawPayload datum)).toSomeConcreteFramedPeriodData

def symbolicCorrCanonicalFramedProbeFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicCorrDatum ctx) :
    FramedProbeFamily ctx :=
  concreteFramedProbeFamily
    (ProbeIndex := SymbolicCorrCanonicalProbe)
    (symbolicCorrCanonicalConcreteFramedDatum datum)

def symbolicCorrProbeExtensionalityOfFaithfulFramedProbes
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (datum : SymbolicCorrDatum ctx)
    (faithful :
      FaithfulFramedProbeTarget
        ctx
        (symbolicCorrCanonicalFramedProbeFamily datum)
        structuredEq) :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily
        (ProbeIndex := SymbolicCorrCanonicalProbe)
        (symbolicCorrCanonicalConcreteFramedDatum datum)).toScalarProbeFamily
      (tautologicalBasisFreePeriodMapEquality ctx structuredEq) :=
  let family :=
    concreteFramedProbeFamily
      (ProbeIndex := SymbolicCorrCanonicalProbe)
      (symbolicCorrCanonicalConcreteFramedDatum datum)
  let faithful' : FaithfulFramedProbeTarget ctx family structuredEq := faithful
  ProbeExtensionalityForBasisFreePeriodMap.ofFaithfulFramedProbeTarget
    (family := family)
    (structuredEq := structuredEq)
    (tautologicalFramedPeriodsInduceProbeEquality family)
    faithful'

structure SymbolicCorrRawFramedPeriodPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx) where
  symbolicDatum : SymbolicCorrDatum ctx
  ProbeIndex : Type w
  sourceObjectData :
    ProbeIndex → SomeStructuredComparisonMorphism ctx → GeometricComparisonObjectData ctx
  targetObjectData :
    ProbeIndex → SomeStructuredComparisonMorphism ctx → GeometricComparisonObjectData ctx
  structuredMorphism :
    (probe : ProbeIndex) →
      (morphism : SomeStructuredComparisonMorphism ctx) →
        ClassicalStructuredComparisonMorphism
          (sourceObjectData probe morphism).toStructuredComparisonObject
          (targetObjectData probe morphism).toStructuredComparisonObject
  framedPayload :
    (probe : ProbeIndex) →
      (morphism : SomeStructuredComparisonMorphism ctx) →
        GeometricFramedPeriodRawPayload (structuredMorphism probe morphism)
  probeExtensionality :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily
        (fun probe morphism =>
          (SomeGeometricFramedPeriodData.ofRawPayload
            (sourceObjectData probe morphism)
            (targetObjectData probe morphism)
            (structuredMorphism probe morphism)
            (framedPayload probe morphism)).toSomeConcreteFramedPeriodData)).toScalarProbeFamily
      (tautologicalBasisFreePeriodMapEquality ctx structuredEq)

def symbolicCorrRawFramedPeriodPayloadOfCanonicalSource
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (datum : SymbolicCorrDatum ctx)
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (ProbeIndex := SymbolicCorrCanonicalProbe)
          (symbolicCorrCanonicalConcreteFramedDatum datum)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq)) :
    SymbolicCorrRawFramedPeriodPayload structuredEq where
  symbolicDatum := datum
  ProbeIndex := SymbolicCorrCanonicalProbe
  sourceObjectData := fun _ _ => datum.sourceObjectData
  targetObjectData := fun _ _ => datum.targetObjectData
  structuredMorphism := fun _ _ => datum.canonicalRawPayloadSource.structuredMorphism
  framedPayload := fun _ _ => symbolicCorrCanonicalGeometricRawPayload datum
  probeExtensionality := probeExtensionality

namespace SymbolicCorrRawFramedPeriodPayload

def geometricFramedPeriodData
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicCorrRawFramedPeriodPayload structuredEq) :
    data.ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeGeometricFramedPeriodData ctx :=
  fun probe morphism =>
    SomeGeometricFramedPeriodData.ofRawPayload
      (data.sourceObjectData probe morphism)
      (data.targetObjectData probe morphism)
      (data.structuredMorphism probe morphism)
      (data.framedPayload probe morphism)

end SymbolicCorrRawFramedPeriodPayload

structure SymbolicCorrFramedPeriodDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx) where
  symbolicDatum : SymbolicCorrDatum ctx
  ProbeIndex : Type w
  geometricFramedPeriodData :
    ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeGeometricFramedPeriodData ctx
  probeExtensionality :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily
        (fun probe morphism =>
          (geometricFramedPeriodData probe morphism).toSomeConcreteFramedPeriodData)).toScalarProbeFamily
      (tautologicalBasisFreePeriodMapEquality ctx structuredEq)

def symbolicCorrFramedPeriodDatumOfRawPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (payload : SymbolicCorrRawFramedPeriodPayload structuredEq) :
    SymbolicCorrFramedPeriodDatum structuredEq where
  symbolicDatum := payload.symbolicDatum
  ProbeIndex := payload.ProbeIndex
  geometricFramedPeriodData := payload.geometricFramedPeriodData
  probeExtensionality := payload.probeExtensionality

def symbolicCorrFramedPeriodDatumOfCanonicalSource
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (datum : SymbolicCorrDatum ctx)
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (ProbeIndex := SymbolicCorrCanonicalProbe)
          (symbolicCorrCanonicalConcreteFramedDatum datum)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq)) :
    SymbolicCorrFramedPeriodDatum structuredEq :=
  symbolicCorrFramedPeriodDatumOfRawPayload
    (symbolicCorrRawFramedPeriodPayloadOfCanonicalSource datum probeExtensionality)

/-- Symbolic datum for the manuscript's `Loc` row. -/
structure SymbolicLocDatum
    (ctx : ClassicalComparisonContext.{u, v}) where
  ambient : GeometricPeriodObject ctx
  openPart : GeometricPeriodObject ctx
  closedPart : GeometricPeriodObject ctx
  ambientObjectData : GeometricComparisonObjectData ctx
  openObjectData : GeometricComparisonObjectData ctx
  closedObjectData : GeometricComparisonObjectData ctx
  ambientBettiCompatibilityTarget : ambient = ambientObjectData.bettiData.geometricObject
  ambientDeRhamCompatibilityTarget : ambient = ambientObjectData.deRhamData.geometricObject
  openBettiCompatibilityTarget : openPart = openObjectData.bettiData.geometricObject
  openDeRhamCompatibilityTarget : openPart = openObjectData.deRhamData.geometricObject
  closedBettiCompatibilityTarget : closedPart = closedObjectData.bettiData.geometricObject
  closedDeRhamCompatibilityTarget : closedPart = closedObjectData.deRhamData.geometricObject
  ambientPeriodCompatibilityTarget : ambientObjectData.comparisonData.periodCompatibilityTarget
  openPeriodCompatibilityTarget : openObjectData.comparisonData.periodCompatibilityTarget
  closedPeriodCompatibilityTarget : closedObjectData.comparisonData.periodCompatibilityTarget

inductive SymbolicLocObjectSlot
  | ambient
  | open
  | closed
deriving DecidableEq, Repr

def symbolicLocRealizationFunctorData
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicLocDatum ctx) : GeometricRealizationFunctorData ctx where
  ObjectIndex := SymbolicLocObjectSlot
  geometricObject
    | .ambient => datum.ambient
    | .open => datum.openPart
    | .closed => datum.closedPart
  CorrespondenceIndex := PEmpty
  sourceIndex := fun corr => nomatch corr
  targetIndex := fun corr => nomatch corr
  correspondence := fun corr => nomatch corr
  bettiRealization
    | .ambient => datum.ambientObjectData.bettiData
    | .open => datum.openObjectData.bettiData
    | .closed => datum.closedObjectData.bettiData
  deRhamRealization
    | .ambient => datum.ambientObjectData.deRhamData
    | .open => datum.openObjectData.deRhamData
    | .closed => datum.closedObjectData.deRhamData
  comparisonData
    | .ambient => datum.ambientObjectData.comparisonData
    | .open => datum.openObjectData.comparisonData
    | .closed => datum.closedObjectData.comparisonData
  objectFunctorialityTarget :=
    datum.ambientObjectData.comparisonData.periodCompatibilityTarget ∧
      datum.openObjectData.comparisonData.periodCompatibilityTarget ∧
      datum.closedObjectData.comparisonData.periodCompatibilityTarget

inductive SymbolicLocCanonicalProbe
  | ambientToOpen
deriving DecidableEq, Repr

def symbolicLocCanonicalSourceObjectData
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicLocDatum ctx) :
    SymbolicLocCanonicalProbe → GeometricComparisonObjectData ctx
  | .ambientToOpen => datum.ambientObjectData

def symbolicLocCanonicalTargetObjectData
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicLocDatum ctx) :
    SymbolicLocCanonicalProbe → GeometricComparisonObjectData ctx
  | .ambientToOpen => datum.openObjectData

structure SymbolicLocCanonicalRawPayloadSource
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicLocDatum ctx) where
  structuredMorphism :
    (probe : SymbolicLocCanonicalProbe) →
      ClassicalStructuredComparisonMorphism
        (symbolicLocCanonicalSourceObjectData datum probe).toStructuredComparisonObject
        (symbolicLocCanonicalTargetObjectData datum probe).toStructuredComparisonObject
  geometricCorrespondence :
    (probe : SymbolicLocCanonicalProbe) →
      GeometricCorrespondence
        (symbolicLocCanonicalSourceObjectData datum probe).deRhamData.geometricObject
        (symbolicLocCanonicalTargetObjectData datum probe).bettiData.geometricObject
  deRhamClass :
    (probe : SymbolicLocCanonicalProbe) →
      (symbolicLocCanonicalSourceObjectData datum probe).DeRhamCarrier
  bettiClass :
    (probe : SymbolicLocCanonicalProbe) →
      (symbolicLocCanonicalTargetObjectData datum probe).BettiCarrier
  bettiCoframe :
    (probe : SymbolicLocCanonicalProbe) →
      (symbolicLocCanonicalTargetObjectData datum probe).toStructuredComparisonObject.BettiOverScalar →ₗ[ctx.ScalarField]
        ctx.ScalarField
  geometricScalarPeriod : SymbolicLocCanonicalProbe → ctx.ScalarField
  concreteDeRhamVector :
    (probe : SymbolicLocCanonicalProbe) →
      (symbolicLocCanonicalSourceObjectData datum probe).toStructuredComparisonObject.DeRhamOverScalar
  concreteBettiImage :
    (probe : SymbolicLocCanonicalProbe) →
      (symbolicLocCanonicalTargetObjectData datum probe).toStructuredComparisonObject.BettiOverScalar
  concreteBettiCycle :
    (probe : SymbolicLocCanonicalProbe) →
      (symbolicLocCanonicalTargetObjectData datum probe).toStructuredComparisonObject.BettiOverScalar
  concreteComparisonCompatibility :
    (probe : SymbolicLocCanonicalProbe) →
      concreteBettiImage probe =
        (symbolicLocCanonicalTargetObjectData datum probe).toStructuredComparisonObject.comparisonIso
          ((structuredMorphism probe).deRhamMapOverScalar (concreteDeRhamVector probe))
  concreteScalarPeriod_eq_evaluation :
    (probe : SymbolicLocCanonicalProbe) →
      geometricScalarPeriod probe = bettiCoframe probe (concreteBettiImage probe)
  deRhamClassRealizesFrameTarget : SymbolicLocCanonicalProbe → Prop
  bettiClassRealizesCycleTarget : SymbolicLocCanonicalProbe → Prop
  grothendieckPeriodEvaluationTarget : SymbolicLocCanonicalProbe → Prop
  ambientComparisonNaturalityTarget :
    datum.ambientObjectData.comparisonData.comparison.comparisonNaturalityTarget
  openComparisonNaturalityTarget :
    datum.openObjectData.comparisonData.comparison.comparisonNaturalityTarget
  closedComparisonNaturalityTarget :
    datum.closedObjectData.comparisonData.comparison.comparisonNaturalityTarget
  localizationConeNaturalityData :
    LocalizationConeNaturalityData
      (symbolicLocRealizationFunctorData datum)
      SymbolicLocCanonicalProbe
      (fun _ => SymbolicLocObjectSlot.ambient)
      (fun _ => SymbolicLocObjectSlot.open)
      (fun _ => SymbolicLocObjectSlot.closed)

def SymbolicLocDatum.canonicalRawPayloadSource
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicLocDatum ctx)
    (source : SymbolicLocCanonicalRawPayloadSource datum) := source

def symbolicLocGeneratorFamilyData
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicLocDatum ctx) :
    LocGeneratorFamilyData ctx (symbolicLocRealizationFunctorData datum) where
  GeneratorIndex := PUnit
  ambientIndex := fun _ => .ambient
  openIndex := fun _ => .open
  closedIndex := fun _ => .closed
  ambientObject := fun _ => datum.ambient
  openObject := fun _ => datum.openPart
  closedObject := fun _ => datum.closedPart
  ambientData := fun _ => datum.ambientObjectData
  openData := fun _ => datum.openObjectData
  closedData := fun _ => datum.closedObjectData
  ambientObjectCompatibilityTarget := by intro gen; rfl
  openObjectCompatibilityTarget := by intro gen; rfl
  closedObjectCompatibilityTarget := by intro gen; rfl
  ambientDataCompatibilityTarget := by intro gen; rfl
  openDataCompatibilityTarget := by intro gen; rfl
  closedDataCompatibilityTarget := by intro gen; rfl
  theoremTarget := by
    intro gen
    exact ⟨datum.ambientPeriodCompatibilityTarget, datum.openPeriodCompatibilityTarget,
      datum.closedPeriodCompatibilityTarget⟩

def symbolicLocGeneratorRealizationAssignment
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicLocDatum ctx) :
    LocGeneratorRealizationAssignment ctx (symbolicLocRealizationFunctorData datum) where
  family := symbolicLocGeneratorFamilyData datum
  ambientSlotName := "ambient"
  openSlotName := "open"
  closedSlotName := "closed"
  connectingMorphismSlotName := "connecting"
  bettiSlotName := "betti"
  deRhamSlotName := "deRham"
  comparisonSlotName := "comparison"
  framedSlotName := "framed"
  scalarSlotName := "scalar"
  ambientProjection := fun _ => datum.ambient
  openProjection := fun _ => datum.openPart
  closedProjection := fun _ => datum.closedPart
  ambientBettiPlaceholder := fun _ => datum.ambientObjectData.bettiData
  openBettiPlaceholder := fun _ => datum.openObjectData.bettiData
  closedBettiPlaceholder := fun _ => datum.closedObjectData.bettiData
  ambientDeRhamPlaceholder := fun _ => datum.ambientObjectData.deRhamData
  openDeRhamPlaceholder := fun _ => datum.openObjectData.deRhamData
  closedDeRhamPlaceholder := fun _ => datum.closedObjectData.deRhamData
  ambientComparisonDatum := fun _ => datum.ambientObjectData.comparisonData
  openComparisonDatum := fun _ => datum.openObjectData.comparisonData
  closedComparisonDatum := fun _ => datum.closedObjectData.comparisonData
  ambientFramedPlaceholder := fun _ => symbolicPlaceholderFramedObject datum.ambient
  openFramedPlaceholder := fun _ => symbolicPlaceholderFramedObject datum.openPart
  closedFramedPlaceholder := fun _ => symbolicPlaceholderFramedObject datum.closedPart
  ambientComparisonCompatibilityTarget := by intro gen; rfl
  openComparisonCompatibilityTarget := by intro gen; rfl
  closedComparisonCompatibilityTarget := by intro gen; rfl
  scalarExtractionTarget :=
    datum.ambientObjectData.comparisonData.periodCompatibilityTarget ∧
      datum.openObjectData.comparisonData.periodCompatibilityTarget ∧
      datum.closedObjectData.comparisonData.periodCompatibilityTarget
  framedExtractionTarget := True
  coneNaturalityData :=
    { leftSquareCommutes := datum.closedObjectData.comparisonData.periodCompatibilityTarget
      middleSquareCommutes := datum.ambientObjectData.comparisonData.periodCompatibilityTarget
      coneInducedMapEqOpenComparison := datum.openObjectData.comparisonData.periodCompatibilityTarget
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
              ambientPacketTarget := datum.ambientObjectData.comparisonData.periodCompatibilityTarget
              openComplementPacketTarget := datum.openObjectData.comparisonData.periodCompatibilityTarget
              closedSupportPacketTarget := datum.closedObjectData.comparisonData.periodCompatibilityTarget
              canonicalSinkTarget := True
              peelResultTarget := True
              exposedBoundaryDefectTarget := True
              defectMatchesShiftedClosedTarget := True
              replayReconstructsAmbientTarget := True }
          bettiReplayTarget := datum.ambientObjectData.comparisonData.periodCompatibilityTarget
          deRhamReplayTarget := datum.openObjectData.comparisonData.periodCompatibilityTarget
          ambientComparisonNaturalityTarget := datum.ambientObjectData.comparisonData.periodCompatibilityTarget
          openComparisonNaturalityTarget := datum.openObjectData.comparisonData.periodCompatibilityTarget
          closedComparisonNaturalityTarget := datum.closedObjectData.comparisonData.periodCompatibilityTarget
          connectingPacketComparisonNaturality_holds := by
            intro point
            cases point <;>
              rfl }
      leftSquareCommutes_holds := datum.closedPeriodCompatibilityTarget
      middleSquareCommutes_holds := datum.ambientPeriodCompatibilityTarget
      coneInducedMapEqOpenComparison_holds := datum.openPeriodCompatibilityTarget }
  theoremTarget := by
    intro gen
    exact ⟨datum.ambientPeriodCompatibilityTarget, datum.openPeriodCompatibilityTarget,
      datum.closedPeriodCompatibilityTarget⟩

@[simp] theorem symbolicLocGeneratorFamilyData_ambientObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicLocDatum ctx) :
    (symbolicLocGeneratorFamilyData datum).ambientObject PUnit.unit = datum.ambient := rfl

@[simp] theorem symbolicLocGeneratorFamilyData_openObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicLocDatum ctx) :
    (symbolicLocGeneratorFamilyData datum).openObject PUnit.unit = datum.openPart := rfl

@[simp] theorem symbolicLocGeneratorFamilyData_closedObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicLocDatum ctx) :
    (symbolicLocGeneratorFamilyData datum).closedObject PUnit.unit = datum.closedPart := rfl

@[simp] theorem symbolicLocGeneratorRealizationAssignment_ambientComparisonDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicLocDatum ctx) :
    (symbolicLocGeneratorRealizationAssignment datum).ambientComparisonDatum PUnit.unit =
      datum.ambientObjectData.comparisonData := rfl

@[simp] theorem symbolicLocGeneratorRealizationAssignment_openComparisonDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicLocDatum ctx) :
    (symbolicLocGeneratorRealizationAssignment datum).openComparisonDatum PUnit.unit =
      datum.openObjectData.comparisonData := rfl

@[simp] theorem symbolicLocGeneratorRealizationAssignment_closedComparisonDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicLocDatum ctx) :
    (symbolicLocGeneratorRealizationAssignment datum).closedComparisonDatum PUnit.unit =
      datum.closedObjectData.comparisonData := rfl

def symbolicLocCanonicalStructuredMorphism
    {ctx : ClassicalComparisonContext.{u, v}}
    {datum : SymbolicLocDatum ctx}
    (source : SymbolicLocCanonicalRawPayloadSource datum)
    (probe : SymbolicLocCanonicalProbe) :
    ClassicalStructuredComparisonMorphism
      (symbolicLocCanonicalSourceObjectData datum probe).toStructuredComparisonObject
      (symbolicLocCanonicalTargetObjectData datum probe).toStructuredComparisonObject :=
  source.structuredMorphism probe

def symbolicLocCanonicalGeometricRawPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    {datum : SymbolicLocDatum ctx}
    (source : SymbolicLocCanonicalRawPayloadSource datum)
    (probe : SymbolicLocCanonicalProbe) :
    GeometricFramedPeriodRawPayload (symbolicLocCanonicalStructuredMorphism source probe) :=
  { geometricCorrespondence := source.geometricCorrespondence probe
    deRhamClass := source.deRhamClass probe
    bettiClass := source.bettiClass probe
    bettiCoframe := source.bettiCoframe probe
    geometricScalarPeriod := source.geometricScalarPeriod probe
    concreteDeRhamVector := source.concreteDeRhamVector probe
    concreteBettiImage := source.concreteBettiImage probe
    concreteBettiCycle := source.concreteBettiCycle probe
    concreteComparisonCompatibility := source.concreteComparisonCompatibility probe
    concreteScalarPeriod_eq_evaluation := source.concreteScalarPeriod_eq_evaluation probe
    deRhamClassRealizesFrameTarget := source.deRhamClassRealizesFrameTarget probe
    bettiClassRealizesCycleTarget := source.bettiClassRealizesCycleTarget probe
    grothendieckPeriodEvaluationTarget := source.grothendieckPeriodEvaluationTarget probe }

def symbolicLocCanonicalConcreteFramedDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    {datum : SymbolicLocDatum ctx}
    (source : SymbolicLocCanonicalRawPayloadSource datum) :
    SymbolicLocCanonicalProbe → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx :=
  fun probe _ =>
    (SomeGeometricFramedPeriodData.ofRawPayload
      (symbolicLocCanonicalSourceObjectData datum probe)
      (symbolicLocCanonicalTargetObjectData datum probe)
      (source.structuredMorphism probe)
      (symbolicLocCanonicalGeometricRawPayload source probe)).toSomeConcreteFramedPeriodData

def symbolicLocCanonicalFramedProbeFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    {datum : SymbolicLocDatum ctx}
    (source : SymbolicLocCanonicalRawPayloadSource datum) :
    FramedProbeFamily ctx :=
  concreteFramedProbeFamily
    (ProbeIndex := SymbolicLocCanonicalProbe)
    (symbolicLocCanonicalConcreteFramedDatum source)

def symbolicLocProbeExtensionalityOfFaithfulFramedProbes
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {datum : SymbolicLocDatum ctx}
    (source : SymbolicLocCanonicalRawPayloadSource datum)
    (faithful :
      FaithfulFramedProbeTarget
        ctx
        (symbolicLocCanonicalFramedProbeFamily source)
        structuredEq) :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily
        (ProbeIndex := SymbolicLocCanonicalProbe)
        (symbolicLocCanonicalConcreteFramedDatum source)).toScalarProbeFamily
      (tautologicalBasisFreePeriodMapEquality ctx structuredEq) :=
  let family :=
    concreteFramedProbeFamily
      (ProbeIndex := SymbolicLocCanonicalProbe)
      (symbolicLocCanonicalConcreteFramedDatum source)
  let faithful' : FaithfulFramedProbeTarget ctx family structuredEq := faithful
  ProbeExtensionalityForBasisFreePeriodMap.ofFaithfulFramedProbeTarget
    (family := family)
    (structuredEq := structuredEq)
    (tautologicalFramedPeriodsInduceProbeEquality family)
    faithful'

structure SymbolicLocRawFramedPeriodPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx) where
  symbolicDatum : SymbolicLocDatum ctx
  canonicalRawPayloadSource : SymbolicLocCanonicalRawPayloadSource symbolicDatum
  ProbeIndex : Type w
  sourceObjectData :
    ProbeIndex → SomeStructuredComparisonMorphism ctx → GeometricComparisonObjectData ctx
  targetObjectData :
    ProbeIndex → SomeStructuredComparisonMorphism ctx → GeometricComparisonObjectData ctx
  structuredMorphism :
    (probe : ProbeIndex) →
      (morphism : SomeStructuredComparisonMorphism ctx) →
        ClassicalStructuredComparisonMorphism
          (sourceObjectData probe morphism).toStructuredComparisonObject
          (targetObjectData probe morphism).toStructuredComparisonObject
  framedPayload :
    (probe : ProbeIndex) →
      (morphism : SomeStructuredComparisonMorphism ctx) →
        GeometricFramedPeriodRawPayload (structuredMorphism probe morphism)
  localizationConeNaturalityData :
    LocalizationConeNaturalityData
      (symbolicLocRealizationFunctorData symbolicDatum)
      SymbolicLocCanonicalProbe
      (fun _ => SymbolicLocObjectSlot.ambient)
      (fun _ => SymbolicLocObjectSlot.open)
      (fun _ => SymbolicLocObjectSlot.closed)
  probeExtensionality :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily
        (fun probe morphism =>
          (SomeGeometricFramedPeriodData.ofRawPayload
            (sourceObjectData probe morphism)
            (targetObjectData probe morphism)
            (structuredMorphism probe morphism)
            (framedPayload probe morphism)).toSomeConcreteFramedPeriodData)).toScalarProbeFamily
      (tautologicalBasisFreePeriodMapEquality ctx structuredEq)

def symbolicLocRawFramedPeriodPayloadOfCanonicalSource
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {datum : SymbolicLocDatum ctx}
    (source : SymbolicLocCanonicalRawPayloadSource datum)
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (ProbeIndex := SymbolicLocCanonicalProbe)
          (symbolicLocCanonicalConcreteFramedDatum source)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq)) :
    SymbolicLocRawFramedPeriodPayload structuredEq where
  symbolicDatum := datum
  canonicalRawPayloadSource := source
  ProbeIndex := SymbolicLocCanonicalProbe
  sourceObjectData := fun probe _ => symbolicLocCanonicalSourceObjectData datum probe
  targetObjectData := fun probe _ => symbolicLocCanonicalTargetObjectData datum probe
  structuredMorphism := fun probe _ => source.structuredMorphism probe
  framedPayload := fun probe _ => symbolicLocCanonicalGeometricRawPayload source probe
  localizationConeNaturalityData := source.localizationConeNaturalityData
  probeExtensionality := probeExtensionality

namespace SymbolicLocRawFramedPeriodPayload

def geometricFramedPeriodData
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicLocRawFramedPeriodPayload structuredEq) :
    data.ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeGeometricFramedPeriodData ctx :=
  fun probe morphism =>
    SomeGeometricFramedPeriodData.ofRawPayload
      (data.sourceObjectData probe morphism)
      (data.targetObjectData probe morphism)
      (data.structuredMorphism probe morphism)
      (data.framedPayload probe morphism)

end SymbolicLocRawFramedPeriodPayload

structure SymbolicLocFramedPeriodDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx) where
  symbolicDatum : SymbolicLocDatum ctx
  canonicalRawPayloadSource : SymbolicLocCanonicalRawPayloadSource symbolicDatum
  ProbeIndex : Type w
  geometricFramedPeriodData :
    ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeGeometricFramedPeriodData ctx
  localizationConeNaturalityData :
    LocalizationConeNaturalityData
      (symbolicLocRealizationFunctorData symbolicDatum)
      SymbolicLocCanonicalProbe
      (fun _ => SymbolicLocObjectSlot.ambient)
      (fun _ => SymbolicLocObjectSlot.open)
      (fun _ => SymbolicLocObjectSlot.closed)
  probeExtensionality :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily
        (fun probe morphism =>
          (geometricFramedPeriodData probe morphism).toSomeConcreteFramedPeriodData)).toScalarProbeFamily
      (tautologicalBasisFreePeriodMapEquality ctx structuredEq)

def symbolicLocFramedPeriodDatumOfRawPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (payload : SymbolicLocRawFramedPeriodPayload structuredEq) :
    SymbolicLocFramedPeriodDatum structuredEq where
  symbolicDatum := payload.symbolicDatum
  canonicalRawPayloadSource := payload.canonicalRawPayloadSource
  ProbeIndex := payload.ProbeIndex
  geometricFramedPeriodData := payload.geometricFramedPeriodData
  localizationConeNaturalityData := payload.localizationConeNaturalityData
  probeExtensionality := payload.probeExtensionality

def symbolicLocFramedPeriodDatumOfCanonicalSource
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {datum : SymbolicLocDatum ctx}
    (source : SymbolicLocCanonicalRawPayloadSource datum)
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (ProbeIndex := SymbolicLocCanonicalProbe)
          (symbolicLocCanonicalConcreteFramedDatum source)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq)) :
    SymbolicLocFramedPeriodDatum structuredEq :=
  symbolicLocFramedPeriodDatumOfRawPayload
    (symbolicLocRawFramedPeriodPayloadOfCanonicalSource source probeExtensionality)

/-- Symbolic datum for the manuscript's `Nis` row. -/
structure SymbolicNisDatum
    (ctx : ClassicalComparisonContext.{u, v}) where
  base : GeometricPeriodObject ctx
  patch : GeometricPeriodObject ctx
  overlap : GeometricPeriodObject ctx
  baseObjectData : GeometricComparisonObjectData ctx
  patchObjectData : GeometricComparisonObjectData ctx
  overlapObjectData : GeometricComparisonObjectData ctx
  baseBettiCompatibilityTarget : base = baseObjectData.bettiData.geometricObject
  baseDeRhamCompatibilityTarget : base = baseObjectData.deRhamData.geometricObject
  patchBettiCompatibilityTarget : patch = patchObjectData.bettiData.geometricObject
  patchDeRhamCompatibilityTarget : patch = patchObjectData.deRhamData.geometricObject
  overlapBettiCompatibilityTarget : overlap = overlapObjectData.bettiData.geometricObject
  overlapDeRhamCompatibilityTarget : overlap = overlapObjectData.deRhamData.geometricObject
  baseComparisonCompatibilityTarget : baseObjectData.comparisonData.grothendieckComparisonTarget
  patchComparisonCompatibilityTarget : patchObjectData.comparisonData.grothendieckComparisonTarget
  overlapComparisonCompatibilityTarget : overlapObjectData.comparisonData.grothendieckComparisonTarget

inductive SymbolicNisObjectSlot
  | base
  | patch
  | overlap
deriving DecidableEq, Repr

def symbolicNisRealizationFunctorData
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicNisDatum ctx) : GeometricRealizationFunctorData ctx where
  ObjectIndex := SymbolicNisObjectSlot
  geometricObject
    | .base => datum.base
    | .patch => datum.patch
    | .overlap => datum.overlap
  CorrespondenceIndex := PEmpty
  sourceIndex := fun corr => nomatch corr
  targetIndex := fun corr => nomatch corr
  correspondence := fun corr => nomatch corr
  bettiRealization
    | .base => datum.baseObjectData.bettiData
    | .patch => datum.patchObjectData.bettiData
    | .overlap => datum.overlapObjectData.bettiData
  deRhamRealization
    | .base => datum.baseObjectData.deRhamData
    | .patch => datum.patchObjectData.deRhamData
    | .overlap => datum.overlapObjectData.deRhamData
  comparisonData
    | .base => datum.baseObjectData.comparisonData
    | .patch => datum.patchObjectData.comparisonData
    | .overlap => datum.overlapObjectData.comparisonData
  objectFunctorialityTarget :=
    datum.baseObjectData.comparisonData.grothendieckComparisonTarget ∧
      datum.patchObjectData.comparisonData.grothendieckComparisonTarget ∧
      datum.overlapObjectData.comparisonData.grothendieckComparisonTarget

def symbolicNisGeneratorFamilyData
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicNisDatum ctx) :
    NisGeneratorFamilyData ctx (symbolicNisRealizationFunctorData datum) where
  GeneratorIndex := PUnit
  baseIndex := fun _ => .base
  patchIndex := fun _ => .patch
  overlapIndex := fun _ => .overlap
  baseObject := fun _ => datum.base
  patchObject := fun _ => datum.patch
  overlapObject := fun _ => datum.overlap
  baseData := fun _ => datum.baseObjectData
  patchData := fun _ => datum.patchObjectData
  overlapData := fun _ => datum.overlapObjectData
  baseObjectCompatibilityTarget := by intro gen; rfl
  patchObjectCompatibilityTarget := by intro gen; rfl
  overlapObjectCompatibilityTarget := by intro gen; rfl
  baseDataCompatibilityTarget := by intro gen; rfl
  patchDataCompatibilityTarget := by intro gen; rfl
  overlapDataCompatibilityTarget := by intro gen; rfl
  theoremTarget := by
    intro gen
    exact ⟨datum.baseComparisonCompatibilityTarget, datum.patchComparisonCompatibilityTarget,
      datum.overlapComparisonCompatibilityTarget⟩

def symbolicNisGeneratorRealizationAssignment
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicNisDatum ctx) :
    NisGeneratorRealizationAssignment ctx (symbolicNisRealizationFunctorData datum) where
  family := symbolicNisGeneratorFamilyData datum
  baseSlotName := "base"
  patchSlotName := "patch"
  overlapSlotName := "overlap"
  squareSlotName := "square"
  bettiSlotName := "betti"
  deRhamSlotName := "deRham"
  comparisonSlotName := "comparison"
  framedSlotName := "framed"
  scalarSlotName := "scalar"
  baseProjection := fun _ => datum.base
  patchProjection := fun _ => datum.patch
  overlapProjection := fun _ => datum.overlap
  baseBettiPlaceholder := fun _ => datum.baseObjectData.bettiData
  patchBettiPlaceholder := fun _ => datum.patchObjectData.bettiData
  overlapBettiPlaceholder := fun _ => datum.overlapObjectData.bettiData
  baseDeRhamPlaceholder := fun _ => datum.baseObjectData.deRhamData
  patchDeRhamPlaceholder := fun _ => datum.patchObjectData.deRhamData
  overlapDeRhamPlaceholder := fun _ => datum.overlapObjectData.deRhamData
  baseComparisonDatum := fun _ => datum.baseObjectData.comparisonData
  patchComparisonDatum := fun _ => datum.patchObjectData.comparisonData
  overlapComparisonDatum := fun _ => datum.overlapObjectData.comparisonData
  baseFramedPlaceholder := fun _ => symbolicPlaceholderFramedObject datum.base
  patchFramedPlaceholder := fun _ => symbolicPlaceholderFramedObject datum.patch
  overlapFramedPlaceholder := fun _ => symbolicPlaceholderFramedObject datum.overlap
  baseComparisonCompatibilityTarget := by intro gen; rfl
  patchComparisonCompatibilityTarget := by intro gen; rfl
  overlapComparisonCompatibilityTarget := by intro gen; rfl
  scalarExtractionTarget := True
  framedExtractionTarget := True
  theoremTarget := by
    intro gen
    exact ⟨datum.baseComparisonCompatibilityTarget, datum.patchComparisonCompatibilityTarget,
      datum.overlapComparisonCompatibilityTarget⟩
  descentSquareCompatibilityTarget := True
  traceNativePatchReplayData :=
    { overlapGluingTarget :=
        { ReplayWitness := PUnit
          replayWitness := PUnit.unit
          basePacketTarget := datum.baseObjectData.comparisonData.grothendieckComparisonTarget
          patchPacketTarget := datum.patchObjectData.comparisonData.grothendieckComparisonTarget
          overlapPacketTarget := datum.overlapObjectData.comparisonData.grothendieckComparisonTarget
          basePatchAgreementOnOverlapTarget :=
            datum.overlapObjectData.comparisonData.grothendieckComparisonTarget
          gluedReplayTarget := True
          gluedReplayRestrictsToBaseTarget := True
          gluedReplayRestrictsToPatchTarget := True
          overlapComparisonNaturalityTarget :=
            datum.overlapObjectData.comparisonData.grothendieckComparisonTarget }
      bettiPatchReplayTarget := datum.baseObjectData.comparisonData.grothendieckComparisonTarget
      deRhamPatchReplayTarget := datum.patchObjectData.comparisonData.grothendieckComparisonTarget
      baseComparisonNaturalityTarget :=
        datum.baseObjectData.comparisonData.grothendieckComparisonTarget
      patchComparisonNaturalityTarget :=
        datum.patchObjectData.comparisonData.grothendieckComparisonTarget
      overlapComparisonNaturalityTarget :=
        datum.overlapObjectData.comparisonData.grothendieckComparisonTarget
      overlapAgreement_holds := by
        intro gen
        exact ⟨datum.baseComparisonCompatibilityTarget, datum.patchComparisonCompatibilityTarget,
          datum.overlapComparisonCompatibilityTarget⟩
      descentSquareCompatibility_holds := True.intro }

@[simp] theorem symbolicNisGeneratorFamilyData_baseObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicNisDatum ctx) :
    (symbolicNisGeneratorFamilyData datum).baseObject PUnit.unit = datum.base := rfl

@[simp] theorem symbolicNisGeneratorFamilyData_patchObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicNisDatum ctx) :
    (symbolicNisGeneratorFamilyData datum).patchObject PUnit.unit = datum.patch := rfl

@[simp] theorem symbolicNisGeneratorFamilyData_overlapObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicNisDatum ctx) :
    (symbolicNisGeneratorFamilyData datum).overlapObject PUnit.unit = datum.overlap := rfl

@[simp] theorem symbolicNisGeneratorRealizationAssignment_baseComparisonDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicNisDatum ctx) :
    (symbolicNisGeneratorRealizationAssignment datum).baseComparisonDatum PUnit.unit =
      datum.baseObjectData.comparisonData := rfl

@[simp] theorem symbolicNisGeneratorRealizationAssignment_patchComparisonDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicNisDatum ctx) :
    (symbolicNisGeneratorRealizationAssignment datum).patchComparisonDatum PUnit.unit =
      datum.patchObjectData.comparisonData := rfl

@[simp] theorem symbolicNisGeneratorRealizationAssignment_overlapComparisonDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicNisDatum ctx) :
    (symbolicNisGeneratorRealizationAssignment datum).overlapComparisonDatum PUnit.unit =
      datum.overlapObjectData.comparisonData := rfl

/-- Symbolic datum for the manuscript's `A1` row. -/
structure SymbolicA1CanonicalRawPayloadSource
    {ctx : ClassicalComparisonContext.{u, v}}
    (baseObjectData cylinderObjectData : GeometricComparisonObjectData ctx) where
  structuredMorphism :
    ClassicalStructuredComparisonMorphism
      baseObjectData.toStructuredComparisonObject
      cylinderObjectData.toStructuredComparisonObject
  preservation :
    A1PeriodPreservationCertificate
      baseObjectData
      cylinderObjectData
      structuredMorphism

structure SymbolicA1Datum
    (ctx : ClassicalComparisonContext.{u, v}) where
  base : GeometricPeriodObject ctx
  cylinder : GeometricPeriodObject ctx
  baseObjectData : GeometricComparisonObjectData ctx
  cylinderObjectData : GeometricComparisonObjectData ctx
  canonicalRawPayloadSource :
    SymbolicA1CanonicalRawPayloadSource baseObjectData cylinderObjectData
  baseBettiCompatibilityTarget : base = baseObjectData.bettiData.geometricObject
  baseDeRhamCompatibilityTarget : base = baseObjectData.deRhamData.geometricObject
  cylinderBettiCompatibilityTarget : cylinder = cylinderObjectData.bettiData.geometricObject
  cylinderDeRhamCompatibilityTarget : cylinder = cylinderObjectData.deRhamData.geometricObject
  baseComparisonCompatibilityTarget : baseObjectData.comparisonData.grothendieckComparisonTarget
  cylinderComparisonCompatibilityTarget : cylinderObjectData.comparisonData.grothendieckComparisonTarget
  basePeriodCompatibilityTarget : baseObjectData.comparisonData.periodCompatibilityTarget
  cylinderPeriodCompatibilityTarget : cylinderObjectData.comparisonData.periodCompatibilityTarget

inductive SymbolicA1ObjectSlot
  | base
  | cylinder
deriving DecidableEq, Repr

def symbolicA1RealizationFunctorData
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicA1Datum ctx) : GeometricRealizationFunctorData ctx where
  ObjectIndex := SymbolicA1ObjectSlot
  geometricObject
    | .base => datum.base
    | .cylinder => datum.cylinder
  CorrespondenceIndex := PEmpty
  sourceIndex := fun corr => nomatch corr
  targetIndex := fun corr => nomatch corr
  correspondence := fun corr => nomatch corr
  bettiRealization
    | .base => datum.baseObjectData.bettiData
    | .cylinder => datum.cylinderObjectData.bettiData
  deRhamRealization
    | .base => datum.baseObjectData.deRhamData
    | .cylinder => datum.cylinderObjectData.deRhamData
  comparisonData
    | .base => datum.baseObjectData.comparisonData
    | .cylinder => datum.cylinderObjectData.comparisonData
  objectFunctorialityTarget :=
    datum.baseObjectData.comparisonData.grothendieckComparisonTarget ∧
      datum.cylinderObjectData.comparisonData.grothendieckComparisonTarget ∧
      datum.baseObjectData.comparisonData.periodCompatibilityTarget ∧
      datum.cylinderObjectData.comparisonData.periodCompatibilityTarget

def symbolicA1GeneratorFamilyData
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicA1Datum ctx) :
    A1GeneratorFamilyData ctx (symbolicA1RealizationFunctorData datum) where
  GeneratorIndex := PUnit
  baseIndex := fun _ => .base
  cylinderIndex := fun _ => .cylinder
  baseObject := fun _ => datum.base
  cylinderObject := fun _ => datum.cylinder
  baseData := fun _ => datum.baseObjectData
  cylinderData := fun _ => datum.cylinderObjectData
  baseObjectCompatibilityTarget := by intro gen; rfl
  cylinderObjectCompatibilityTarget := by intro gen; rfl
  baseDataCompatibilityTarget := by intro gen; rfl
  cylinderDataCompatibilityTarget := by intro gen; rfl
  theoremTarget := by
    intro gen
    exact ⟨datum.baseComparisonCompatibilityTarget, datum.cylinderComparisonCompatibilityTarget,
      datum.basePeriodCompatibilityTarget, datum.cylinderPeriodCompatibilityTarget⟩

def symbolicA1GeneratorRealizationAssignment
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicA1Datum ctx) :
    A1GeneratorRealizationAssignment ctx (symbolicA1RealizationFunctorData datum) where
  family := symbolicA1GeneratorFamilyData datum
  baseSlotName := "base"
  cylinderSlotName := "cylinder"
  projectionZeroSlotName := "proj0"
  projectionOneSlotName := "proj1"
  bettiSlotName := "betti"
  deRhamSlotName := "deRham"
  comparisonSlotName := "comparison"
  framedSlotName := "framed"
  scalarSlotName := "scalar"
  baseProjection := fun _ => datum.base
  cylinderProjection := fun _ => datum.cylinder
  baseBettiPlaceholder := fun _ => datum.baseObjectData.bettiData
  cylinderBettiPlaceholder := fun _ => datum.cylinderObjectData.bettiData
  baseDeRhamPlaceholder := fun _ => datum.baseObjectData.deRhamData
  cylinderDeRhamPlaceholder := fun _ => datum.cylinderObjectData.deRhamData
  baseComparisonDatum := fun _ => datum.baseObjectData.comparisonData
  cylinderComparisonDatum := fun _ => datum.cylinderObjectData.comparisonData
  baseFramedPlaceholder := fun _ => symbolicPlaceholderFramedObject datum.base
  cylinderFramedPlaceholder := fun _ => symbolicPlaceholderFramedObject datum.cylinder
  baseComparisonCompatibilityTarget := by intro gen; rfl
  cylinderComparisonCompatibilityTarget := by intro gen; rfl
  scalarExtractionTarget :=
    datum.baseObjectData.comparisonData.periodCompatibilityTarget ∧
      datum.cylinderObjectData.comparisonData.periodCompatibilityTarget
  framedExtractionTarget := True
  theoremTarget := by
    intro gen
    exact ⟨datum.baseComparisonCompatibilityTarget, datum.cylinderComparisonCompatibilityTarget,
      datum.basePeriodCompatibilityTarget, datum.cylinderPeriodCompatibilityTarget⟩
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
        exact ⟨datum.baseComparisonCompatibilityTarget, datum.cylinderComparisonCompatibilityTarget,
          datum.basePeriodCompatibilityTarget, datum.cylinderPeriodCompatibilityTarget⟩
      homotopyInvariance_holds := True.intro }

@[simp] theorem symbolicA1GeneratorFamilyData_baseObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicA1Datum ctx) :
    (symbolicA1GeneratorFamilyData datum).baseObject PUnit.unit = datum.base := rfl

@[simp] theorem symbolicA1GeneratorFamilyData_cylinderObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicA1Datum ctx) :
    (symbolicA1GeneratorFamilyData datum).cylinderObject PUnit.unit = datum.cylinder := rfl

@[simp] theorem symbolicA1GeneratorRealizationAssignment_baseComparisonDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicA1Datum ctx) :
    (symbolicA1GeneratorRealizationAssignment datum).baseComparisonDatum PUnit.unit =
      datum.baseObjectData.comparisonData := rfl

@[simp] theorem symbolicA1GeneratorRealizationAssignment_cylinderComparisonDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicA1Datum ctx) :
    (symbolicA1GeneratorRealizationAssignment datum).cylinderComparisonDatum PUnit.unit =
      datum.cylinderObjectData.comparisonData := rfl

inductive SymbolicA1CanonicalProbe
  | canonical
deriving DecidableEq, Repr

def symbolicA1CanonicalStructuredMorphism
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicA1Datum ctx) :
    ClassicalStructuredComparisonMorphism
      datum.baseObjectData.toStructuredComparisonObject
      datum.cylinderObjectData.toStructuredComparisonObject :=
  datum.canonicalRawPayloadSource.structuredMorphism

def symbolicA1CanonicalGeometricRawPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicA1Datum ctx) :
    GeometricFramedPeriodRawPayload (symbolicA1CanonicalStructuredMorphism datum) :=
  GeometricFramedPeriodRawPayload.ofA1Preservation
    datum.canonicalRawPayloadSource.preservation

@[simp] theorem symbolicA1CanonicalGeometricRawPayload_geometricCorrespondence
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicA1Datum ctx) :
    (symbolicA1CanonicalGeometricRawPayload datum).geometricCorrespondence =
      datum.canonicalRawPayloadSource.preservation.sectionCorrespondence := rfl

/-- Explicit framed-period layer for the symbolic `A1` row.

Unlike `SymbolicA1Datum`, this structure carries a genuine probe-indexed family of geometric
framed-period witnesses together with the separation statement needed by tomography. -/
structure SymbolicA1RawFramedPeriodPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx) where
  symbolicDatum : SymbolicA1Datum ctx
  ProbeIndex : Type w
  sourceObjectData :
    ProbeIndex → SomeStructuredComparisonMorphism ctx → GeometricComparisonObjectData ctx
  targetObjectData :
    ProbeIndex → SomeStructuredComparisonMorphism ctx → GeometricComparisonObjectData ctx
  structuredMorphism :
    (probe : ProbeIndex) →
      (morphism : SomeStructuredComparisonMorphism ctx) →
        ClassicalStructuredComparisonMorphism
          (sourceObjectData probe morphism).toStructuredComparisonObject
          (targetObjectData probe morphism).toStructuredComparisonObject
  framedPayload :
    (probe : ProbeIndex) →
      (morphism : SomeStructuredComparisonMorphism ctx) →
        GeometricFramedPeriodRawPayload (structuredMorphism probe morphism)
  probeExtensionality :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily
        (fun probe morphism =>
          (SomeGeometricFramedPeriodData.ofRawPayload
            (sourceObjectData probe morphism)
            (targetObjectData probe morphism)
            (structuredMorphism probe morphism)
            (framedPayload probe morphism)).toSomeConcreteFramedPeriodData)).toScalarProbeFamily
      (tautologicalBasisFreePeriodMapEquality ctx structuredEq)

def symbolicA1CanonicalConcreteFramedDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicA1Datum ctx) :
    SymbolicA1CanonicalProbe → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx :=
  fun _ _ =>
    (SomeGeometricFramedPeriodData.ofRawPayload
      datum.baseObjectData
      datum.cylinderObjectData
      datum.canonicalRawPayloadSource.structuredMorphism
      (symbolicA1CanonicalGeometricRawPayload datum)).toSomeConcreteFramedPeriodData

def symbolicA1CanonicalFramedProbeFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicA1Datum ctx) :
    FramedProbeFamily ctx :=
  concreteFramedProbeFamily
    (ProbeIndex := SymbolicA1CanonicalProbe)
    (symbolicA1CanonicalConcreteFramedDatum datum)

/-- Derive the canonical symbolic `A1` probe-extensionality witness from faithful framed probes.

This is the lower-level constructor. When faithful probes are available, prefer the canonical
family and tomography packages below so downstream code consumes projections instead of rebuilding
the family expression manually. -/
def symbolicA1ProbeExtensionalityOfFaithfulFramedProbes
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (datum : SymbolicA1Datum ctx)
    (faithful :
      FaithfulFramedProbeTarget
        ctx
        (symbolicA1CanonicalFramedProbeFamily datum)
        structuredEq) :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily
        (ProbeIndex := SymbolicA1CanonicalProbe)
        (symbolicA1CanonicalConcreteFramedDatum datum)).toScalarProbeFamily
      (tautologicalBasisFreePeriodMapEquality ctx structuredEq) :=
  let family :=
    concreteFramedProbeFamily
      (ProbeIndex := SymbolicA1CanonicalProbe)
      (symbolicA1CanonicalConcreteFramedDatum datum)
  let faithful' : FaithfulFramedProbeTarget ctx family structuredEq := faithful
  ProbeExtensionalityForBasisFreePeriodMap.ofFaithfulFramedProbeTarget
    (family := family)
    (structuredEq := structuredEq)
    (tautologicalFramedPeriodsInduceProbeEquality family)
    faithful'

/-- Lower-level canonical symbolic `A1` raw-payload constructor from an explicit extensionality
witness. Prefer the canonical package path when the witness comes from faithful framed probes. -/
def symbolicA1RawFramedPeriodPayloadOfCanonicalSource
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (datum : SymbolicA1Datum ctx)
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (ProbeIndex := SymbolicA1CanonicalProbe)
          (symbolicA1CanonicalConcreteFramedDatum datum)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq)) :
    SymbolicA1RawFramedPeriodPayload structuredEq where
  symbolicDatum := datum
  ProbeIndex := SymbolicA1CanonicalProbe
  sourceObjectData := fun _ _ => datum.baseObjectData
  targetObjectData := fun _ _ => datum.cylinderObjectData
  structuredMorphism := fun _ _ => datum.canonicalRawPayloadSource.structuredMorphism
  framedPayload := fun _ _ => symbolicA1CanonicalGeometricRawPayload datum
  probeExtensionality := probeExtensionality

namespace SymbolicA1RawFramedPeriodPayload

/-- Build the explicit raw symbolic `A1` framed-period payload from a probe-indexed family of
`A1` projection/section preservation certificates. -/
def ofA1Preservation
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (symbolicDatum : SymbolicA1Datum ctx)
    (ProbeIndex : Type w)
    (sourceObjectData :
      ProbeIndex → SomeStructuredComparisonMorphism ctx → GeometricComparisonObjectData ctx)
    (targetObjectData :
      ProbeIndex → SomeStructuredComparisonMorphism ctx → GeometricComparisonObjectData ctx)
    (structuredMorphism :
      (probe : ProbeIndex) →
        (morphism : SomeStructuredComparisonMorphism ctx) →
          ClassicalStructuredComparisonMorphism
            (sourceObjectData probe morphism).toStructuredComparisonObject
            (targetObjectData probe morphism).toStructuredComparisonObject)
    (preservation :
      (probe : ProbeIndex) →
        (morphism : SomeStructuredComparisonMorphism ctx) →
          A1PeriodPreservationCertificate
            (sourceObjectData probe morphism)
            (targetObjectData probe morphism)
            (structuredMorphism probe morphism))
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (fun probe morphism =>
            (SomeGeometricFramedPeriodData.ofRawPayload
              (sourceObjectData probe morphism)
              (targetObjectData probe morphism)
              (structuredMorphism probe morphism)
              (GeometricFramedPeriodRawPayload.ofA1Preservation
                (preservation probe morphism))).toSomeConcreteFramedPeriodData)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq)) :
    SymbolicA1RawFramedPeriodPayload structuredEq where
  symbolicDatum := symbolicDatum
  ProbeIndex := ProbeIndex
  sourceObjectData := sourceObjectData
  targetObjectData := targetObjectData
  structuredMorphism := structuredMorphism
  framedPayload := fun probe morphism =>
    GeometricFramedPeriodRawPayload.ofA1Preservation (preservation probe morphism)
  probeExtensionality := probeExtensionality

/-- Assemble the probe-indexed geometric framed witnesses determined by the raw symbolic `A1`
payload. -/
def geometricFramedPeriodData
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicA1RawFramedPeriodPayload structuredEq) :
    data.ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeGeometricFramedPeriodData ctx :=
  fun probe morphism =>
    SomeGeometricFramedPeriodData.ofRawPayload
      (data.sourceObjectData probe morphism)
      (data.targetObjectData probe morphism)
      (data.structuredMorphism probe morphism)
      (data.framedPayload probe morphism)

@[simp] theorem geometricFramedPeriodData_apply
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicA1RawFramedPeriodPayload structuredEq)
    (probe : data.ProbeIndex)
    (morphism : SomeStructuredComparisonMorphism ctx) :
    data.geometricFramedPeriodData probe morphism =
      SomeGeometricFramedPeriodData.ofRawPayload
        (data.sourceObjectData probe morphism)
        (data.targetObjectData probe morphism)
        (data.structuredMorphism probe morphism)
        (data.framedPayload probe morphism) := rfl

end SymbolicA1RawFramedPeriodPayload

structure SymbolicA1FramedPeriodDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx) where
  symbolicDatum : SymbolicA1Datum ctx
  ProbeIndex : Type w
  geometricFramedPeriodData :
    ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeGeometricFramedPeriodData ctx
  probeExtensionality :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily
        (fun probe morphism =>
          (geometricFramedPeriodData probe morphism).toSomeConcreteFramedPeriodData)).toScalarProbeFamily
      (tautologicalBasisFreePeriodMapEquality ctx structuredEq)

namespace SymbolicA1FramedPeriodDatum

def sourceObjectData
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicA1FramedPeriodDatum structuredEq)
    (probe : data.ProbeIndex)
    (morphism : SomeStructuredComparisonMorphism ctx) :
    GeometricComparisonObjectData ctx :=
  (data.geometricFramedPeriodData probe morphism).1

def targetObjectData
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicA1FramedPeriodDatum structuredEq)
    (probe : data.ProbeIndex)
    (morphism : SomeStructuredComparisonMorphism ctx) :
    GeometricComparisonObjectData ctx :=
  (data.geometricFramedPeriodData probe morphism).2.1

def structuredMorphism
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicA1FramedPeriodDatum structuredEq)
    (probe : data.ProbeIndex)
    (morphism : SomeStructuredComparisonMorphism ctx) :
    ClassicalStructuredComparisonMorphism
      (data.sourceObjectData probe morphism).toStructuredComparisonObject
      (data.targetObjectData probe morphism).toStructuredComparisonObject :=
  (data.geometricFramedPeriodData probe morphism).2.2.1

def framedPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicA1FramedPeriodDatum structuredEq)
    (probe : data.ProbeIndex)
    (morphism : SomeStructuredComparisonMorphism ctx) :
    GeometricFramedPeriodData (data.structuredMorphism probe morphism) :=
  (data.geometricFramedPeriodData probe morphism).2.2.2

@[simp] theorem sourceObjectData_eq
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicA1FramedPeriodDatum structuredEq)
    (probe : data.ProbeIndex)
    (morphism : SomeStructuredComparisonMorphism ctx) :
    data.sourceObjectData probe morphism =
      (data.geometricFramedPeriodData probe morphism).1 := rfl

@[simp] theorem targetObjectData_eq
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicA1FramedPeriodDatum structuredEq)
    (probe : data.ProbeIndex)
    (morphism : SomeStructuredComparisonMorphism ctx) :
    data.targetObjectData probe morphism =
      (data.geometricFramedPeriodData probe morphism).2.1 := rfl

@[simp] theorem structuredMorphism_eq
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicA1FramedPeriodDatum structuredEq)
    (probe : data.ProbeIndex)
    (morphism : SomeStructuredComparisonMorphism ctx) :
    data.structuredMorphism probe morphism =
      (data.geometricFramedPeriodData probe morphism).2.2.1 := rfl

@[simp] theorem framedPayload_eq
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicA1FramedPeriodDatum structuredEq)
    (probe : data.ProbeIndex)
    (morphism : SomeStructuredComparisonMorphism ctx) :
    data.framedPayload probe morphism =
      (data.geometricFramedPeriodData probe morphism).2.2.2 := rfl

/-- Promote an explicit raw symbolic `A1` framed-period payload into the existing framed-period
socket.  This is the first non-hidden step in the theorem ladder from A1 period data to
tomography. -/
def ofRawFramedPeriodPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (payload : SymbolicA1RawFramedPeriodPayload structuredEq) :
    SymbolicA1FramedPeriodDatum structuredEq where
  symbolicDatum := payload.symbolicDatum
  ProbeIndex := payload.ProbeIndex
  geometricFramedPeriodData := payload.geometricFramedPeriodData
  probeExtensionality := payload.probeExtensionality

/-- Compose the symbolic `A1` preservation certificate family directly into the framed-period
datum layer. -/
def ofA1Preservation
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (symbolicDatum : SymbolicA1Datum ctx)
    (ProbeIndex : Type w)
    (sourceObjectData :
      ProbeIndex → SomeStructuredComparisonMorphism ctx → GeometricComparisonObjectData ctx)
    (targetObjectData :
      ProbeIndex → SomeStructuredComparisonMorphism ctx → GeometricComparisonObjectData ctx)
    (structuredMorphism :
      (probe : ProbeIndex) →
        (morphism : SomeStructuredComparisonMorphism ctx) →
          ClassicalStructuredComparisonMorphism
            (sourceObjectData probe morphism).toStructuredComparisonObject
            (targetObjectData probe morphism).toStructuredComparisonObject)
    (preservation :
      (probe : ProbeIndex) →
        (morphism : SomeStructuredComparisonMorphism ctx) →
          A1PeriodPreservationCertificate
            (sourceObjectData probe morphism)
            (targetObjectData probe morphism)
            (structuredMorphism probe morphism))
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (fun probe morphism =>
            (SomeGeometricFramedPeriodData.ofRawPayload
              (sourceObjectData probe morphism)
              (targetObjectData probe morphism)
              (structuredMorphism probe morphism)
              (GeometricFramedPeriodRawPayload.ofA1Preservation
                (preservation probe morphism))).toSomeConcreteFramedPeriodData)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq)) :
    SymbolicA1FramedPeriodDatum structuredEq :=
  ofRawFramedPeriodPayload
    (SymbolicA1RawFramedPeriodPayload.ofA1Preservation
      symbolicDatum
      ProbeIndex
      sourceObjectData
      targetObjectData
      structuredMorphism
      preservation
      probeExtensionality)

end SymbolicA1FramedPeriodDatum

/-- Named constructor exposing the symbolic `A1` framed-period datum determined by an explicit
raw payload. -/
def symbolicA1FramedPeriodDatumOfRawPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (payload : SymbolicA1RawFramedPeriodPayload structuredEq) :
    SymbolicA1FramedPeriodDatum structuredEq :=
  SymbolicA1FramedPeriodDatum.ofRawFramedPeriodPayload payload

/-- Named symbolic `A1` constructor from projection/section preservation certificates. -/
def symbolicA1FramedPeriodDatumOfA1Preservation
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (symbolicDatum : SymbolicA1Datum ctx)
    (ProbeIndex : Type w)
    (sourceObjectData :
      ProbeIndex → SomeStructuredComparisonMorphism ctx → GeometricComparisonObjectData ctx)
    (targetObjectData :
      ProbeIndex → SomeStructuredComparisonMorphism ctx → GeometricComparisonObjectData ctx)
    (structuredMorphism :
      (probe : ProbeIndex) →
        (morphism : SomeStructuredComparisonMorphism ctx) →
          ClassicalStructuredComparisonMorphism
            (sourceObjectData probe morphism).toStructuredComparisonObject
            (targetObjectData probe morphism).toStructuredComparisonObject)
    (preservation :
      (probe : ProbeIndex) →
        (morphism : SomeStructuredComparisonMorphism ctx) →
          A1PeriodPreservationCertificate
            (sourceObjectData probe morphism)
            (targetObjectData probe morphism)
            (structuredMorphism probe morphism))
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (fun probe morphism =>
            (SomeGeometricFramedPeriodData.ofRawPayload
              (sourceObjectData probe morphism)
              (targetObjectData probe morphism)
              (structuredMorphism probe morphism)
              (GeometricFramedPeriodRawPayload.ofA1Preservation
                (preservation probe morphism))).toSomeConcreteFramedPeriodData)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq)) :
    SymbolicA1FramedPeriodDatum structuredEq :=
  SymbolicA1FramedPeriodDatum.ofA1Preservation
    symbolicDatum
    ProbeIndex
    sourceObjectData
    targetObjectData
    structuredMorphism
    preservation
    probeExtensionality

/-- Lower-level canonical symbolic `A1` framed-datum constructor from an explicit extensionality
witness. Prefer the package path when faithful framed probes are the source of extensionality. -/
def symbolicA1FramedPeriodDatumOfCanonicalSource
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (datum : SymbolicA1Datum ctx)
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (ProbeIndex := SymbolicA1CanonicalProbe)
          (symbolicA1CanonicalConcreteFramedDatum datum)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq)) :
    SymbolicA1FramedPeriodDatum structuredEq :=
  symbolicA1FramedPeriodDatumOfRawPayload
    (symbolicA1RawFramedPeriodPayloadOfCanonicalSource datum probeExtensionality)

/-- Symbolic datum for the manuscript's `Env` row. -/
structure SymbolicEnvDatum
    (ctx : ClassicalComparisonContext.{u, v}) where
  ambient : GeometricPeriodObject ctx
  envelope : GeometricPeriodObject ctx
  envelopeCorrespondence : GeometricCorrespondence envelope ambient
  envelopeCorrespondenceCompatibilityTarget : envelopeCorrespondence.correspondenceTarget
  ambientObjectData : GeometricComparisonObjectData ctx
  envelopeObjectData : GeometricComparisonObjectData ctx
  ambientBettiCompatibilityTarget : ambient = ambientObjectData.bettiData.geometricObject
  ambientDeRhamCompatibilityTarget : ambient = ambientObjectData.deRhamData.geometricObject
  envelopeBettiCompatibilityTarget : envelope = envelopeObjectData.bettiData.geometricObject
  envelopeDeRhamCompatibilityTarget : envelope = envelopeObjectData.deRhamData.geometricObject
  ambientComparisonCompatibilityTarget : ambientObjectData.comparisonData.grothendieckComparisonTarget
  envelopeComparisonCompatibilityTarget : envelopeObjectData.comparisonData.grothendieckComparisonTarget
  ambientPeriodCompatibilityTarget : ambientObjectData.comparisonData.periodCompatibilityTarget
  envelopePeriodCompatibilityTarget : envelopeObjectData.comparisonData.periodCompatibilityTarget

inductive SymbolicEnvObjectSlot
  | ambient
  | envelope
deriving DecidableEq, Repr

def symbolicEnvRealizationFunctorData
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicEnvDatum ctx) : GeometricRealizationFunctorData ctx where
  ObjectIndex := SymbolicEnvObjectSlot
  geometricObject
    | .ambient => datum.ambient
    | .envelope => datum.envelope
  CorrespondenceIndex := PEmpty
  sourceIndex := fun corr => nomatch corr
  targetIndex := fun corr => nomatch corr
  correspondence := fun corr => nomatch corr
  bettiRealization
    | .ambient => datum.ambientObjectData.bettiData
    | .envelope => datum.envelopeObjectData.bettiData
  deRhamRealization
    | .ambient => datum.ambientObjectData.deRhamData
    | .envelope => datum.envelopeObjectData.deRhamData
  comparisonData
    | .ambient => datum.ambientObjectData.comparisonData
    | .envelope => datum.envelopeObjectData.comparisonData
  objectFunctorialityTarget :=
    datum.ambientObjectData.comparisonData.grothendieckComparisonTarget ∧
      datum.envelopeObjectData.comparisonData.grothendieckComparisonTarget ∧
      datum.ambientObjectData.comparisonData.periodCompatibilityTarget ∧
      datum.envelopeObjectData.comparisonData.periodCompatibilityTarget

def symbolicEnvGeneratorFamilyData
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicEnvDatum ctx) :
    EnvGeneratorFamilyData ctx (symbolicEnvRealizationFunctorData datum) where
  GeneratorIndex := PUnit
  ambientIndex := fun _ => .ambient
  envelopeIndex := fun _ => .envelope
  ambientObject := fun _ => datum.ambient
  envelopeObject := fun _ => datum.envelope
  envelopeCorrespondence := fun _ => datum.envelopeCorrespondence
  ambientData := fun _ => datum.ambientObjectData
  envelopeData := fun _ => datum.envelopeObjectData
  ambientObjectCompatibilityTarget := by intro gen; rfl
  envelopeObjectCompatibilityTarget := by intro gen; rfl
  ambientDataCompatibilityTarget := by intro gen; rfl
  envelopeDataCompatibilityTarget := by intro gen; rfl
  theoremTarget := by
    intro gen
    exact ⟨datum.envelopeCorrespondenceCompatibilityTarget, datum.ambientComparisonCompatibilityTarget,
      datum.envelopeComparisonCompatibilityTarget, datum.ambientPeriodCompatibilityTarget,
      datum.envelopePeriodCompatibilityTarget⟩

def symbolicEnvGeneratorRealizationAssignment
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicEnvDatum ctx) :
    EnvGeneratorRealizationAssignment ctx (symbolicEnvRealizationFunctorData datum) where
  family := symbolicEnvGeneratorFamilyData datum
  ambientSlotName := "ambient"
  envelopeSlotName := "envelope"
  exactCompletionSlotName := "exactCompletion"
  bettiSlotName := "betti"
  deRhamSlotName := "deRham"
  comparisonSlotName := "comparison"
  framedSlotName := "framed"
  scalarSlotName := "scalar"
  ambientProjection := fun _ => datum.ambient
  envelopeProjection := fun _ => datum.envelope
  ambientBettiPlaceholder := fun _ => datum.ambientObjectData.bettiData
  envelopeBettiPlaceholder := fun _ => datum.envelopeObjectData.bettiData
  ambientDeRhamPlaceholder := fun _ => datum.ambientObjectData.deRhamData
  envelopeDeRhamPlaceholder := fun _ => datum.envelopeObjectData.deRhamData
  ambientComparisonDatum := fun _ => datum.ambientObjectData.comparisonData
  envelopeComparisonDatum := fun _ => datum.envelopeObjectData.comparisonData
  ambientFramedPlaceholder := fun _ => symbolicPlaceholderFramedObject datum.ambient
  envelopeFramedPlaceholder := fun _ => symbolicPlaceholderFramedObject datum.envelope
  ambientComparisonCompatibilityTarget := by intro gen; rfl
  envelopeComparisonCompatibilityTarget := by intro gen; rfl
  scalarExtractionTarget :=
    datum.ambientObjectData.comparisonData.periodCompatibilityTarget ∧
      datum.envelopeObjectData.comparisonData.periodCompatibilityTarget
  framedExtractionTarget := True
  exactCompletionTarget := True
  theoremTarget := by
    intro gen
    exact ⟨datum.ambientComparisonCompatibilityTarget, datum.envelopeComparisonCompatibilityTarget,
      datum.ambientPeriodCompatibilityTarget, datum.envelopePeriodCompatibilityTarget⟩
  traceNativeEnvReplayData :=
    { replayTransformerTarget :=
        { ReplayWitness := PUnit
          replayWitness := PUnit.unit
          operation := .structuralAdmin
          certifiedInputPacketTarget :=
            datum.ambientObjectData.comparisonData.grothendieckComparisonTarget ∧
              datum.envelopeObjectData.comparisonData.grothendieckComparisonTarget
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
        exact ⟨datum.ambientComparisonCompatibilityTarget, datum.envelopeComparisonCompatibilityTarget,
          datum.ambientPeriodCompatibilityTarget, datum.envelopePeriodCompatibilityTarget⟩
      formalClosure_holds := True.intro }

@[simp] theorem symbolicEnvGeneratorFamilyData_ambientObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicEnvDatum ctx) :
    (symbolicEnvGeneratorFamilyData datum).ambientObject PUnit.unit = datum.ambient := rfl

@[simp] theorem symbolicEnvGeneratorFamilyData_envelopeObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicEnvDatum ctx) :
    (symbolicEnvGeneratorFamilyData datum).envelopeObject PUnit.unit = datum.envelope := rfl

@[simp] theorem symbolicEnvGeneratorFamilyData_envelopeCorrespondence
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicEnvDatum ctx) :
    (symbolicEnvGeneratorFamilyData datum).envelopeCorrespondence PUnit.unit =
      datum.envelopeCorrespondence := rfl

@[simp] theorem symbolicEnvGeneratorRealizationAssignment_ambientComparisonDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicEnvDatum ctx) :
    (symbolicEnvGeneratorRealizationAssignment datum).ambientComparisonDatum PUnit.unit =
      datum.ambientObjectData.comparisonData := rfl

@[simp] theorem symbolicEnvGeneratorRealizationAssignment_envelopeComparisonDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicEnvDatum ctx) :
    (symbolicEnvGeneratorRealizationAssignment datum).envelopeComparisonDatum PUnit.unit =
      datum.envelopeObjectData.comparisonData := rfl

inductive SymbolicEnvCanonicalProbe
  | envelopeToAmbient
deriving DecidableEq, Repr

def symbolicEnvCanonicalSourceObjectData
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicEnvDatum ctx) :
    SymbolicEnvCanonicalProbe → GeometricComparisonObjectData ctx
  | .envelopeToAmbient => datum.envelopeObjectData

def symbolicEnvCanonicalTargetObjectData
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicEnvDatum ctx) :
    SymbolicEnvCanonicalProbe → GeometricComparisonObjectData ctx
  | .envelopeToAmbient => datum.ambientObjectData

structure SymbolicEnvCanonicalRawPayloadSource
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicEnvDatum ctx) where
  structuredMorphism :
    (probe : SymbolicEnvCanonicalProbe) →
      ClassicalStructuredComparisonMorphism
        (symbolicEnvCanonicalSourceObjectData datum probe).toStructuredComparisonObject
        (symbolicEnvCanonicalTargetObjectData datum probe).toStructuredComparisonObject
  geometricCorrespondence :
    (probe : SymbolicEnvCanonicalProbe) →
      GeometricCorrespondence
        (symbolicEnvCanonicalSourceObjectData datum probe).deRhamData.geometricObject
        (symbolicEnvCanonicalTargetObjectData datum probe).bettiData.geometricObject
  deRhamClass :
    (probe : SymbolicEnvCanonicalProbe) →
      (symbolicEnvCanonicalSourceObjectData datum probe).DeRhamCarrier
  bettiClass :
    (probe : SymbolicEnvCanonicalProbe) →
      (symbolicEnvCanonicalTargetObjectData datum probe).BettiCarrier
  bettiCoframe :
    (probe : SymbolicEnvCanonicalProbe) →
      (symbolicEnvCanonicalTargetObjectData datum probe).toStructuredComparisonObject.BettiOverScalar →ₗ[ctx.ScalarField]
        ctx.ScalarField
  geometricScalarPeriod : SymbolicEnvCanonicalProbe → ctx.ScalarField
  concreteDeRhamVector :
    (probe : SymbolicEnvCanonicalProbe) →
      (symbolicEnvCanonicalSourceObjectData datum probe).toStructuredComparisonObject.DeRhamOverScalar
  concreteBettiImage :
    (probe : SymbolicEnvCanonicalProbe) →
      (symbolicEnvCanonicalTargetObjectData datum probe).toStructuredComparisonObject.BettiOverScalar
  concreteBettiCycle :
    (probe : SymbolicEnvCanonicalProbe) →
      (symbolicEnvCanonicalTargetObjectData datum probe).toStructuredComparisonObject.BettiOverScalar
  concreteComparisonCompatibility :
    (probe : SymbolicEnvCanonicalProbe) →
      concreteBettiImage probe =
        (symbolicEnvCanonicalTargetObjectData datum probe).toStructuredComparisonObject.comparisonIso
          ((structuredMorphism probe).deRhamMapOverScalar (concreteDeRhamVector probe))
  concreteScalarPeriod_eq_evaluation :
    (probe : SymbolicEnvCanonicalProbe) →
      geometricScalarPeriod probe = bettiCoframe probe (concreteBettiImage probe)
  deRhamClassRealizesFrameTarget : SymbolicEnvCanonicalProbe → Prop
  bettiClassRealizesCycleTarget : SymbolicEnvCanonicalProbe → Prop
  grothendieckPeriodEvaluationTarget : SymbolicEnvCanonicalProbe → Prop
  ambientComparisonNaturalityTarget :
    datum.ambientObjectData.comparisonData.comparison.comparisonNaturalityTarget
  envelopeComparisonNaturalityTarget :
    datum.envelopeObjectData.comparisonData.comparison.comparisonNaturalityTarget
  traceNativeEnvReplayData :
    CertifiedEnvReplayData ctx
      (∀ _ : SymbolicEnvCanonicalProbe,
        datum.envelopeCorrespondence.correspondenceTarget ∧
          datum.ambientObjectData.comparisonData.grothendieckComparisonTarget ∧
          datum.envelopeObjectData.comparisonData.grothendieckComparisonTarget ∧
          datum.ambientObjectData.comparisonData.periodCompatibilityTarget ∧
          datum.envelopeObjectData.comparisonData.periodCompatibilityTarget)
      datum.envelopeObjectData.comparisonData.periodCompatibilityTarget

def SymbolicEnvDatum.canonicalRawPayloadSource
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicEnvDatum ctx)
    (source : SymbolicEnvCanonicalRawPayloadSource datum) := source

def symbolicEnvCanonicalStructuredMorphism
    {ctx : ClassicalComparisonContext.{u, v}}
    {datum : SymbolicEnvDatum ctx}
    (source : SymbolicEnvCanonicalRawPayloadSource datum)
    (probe : SymbolicEnvCanonicalProbe) :
    ClassicalStructuredComparisonMorphism
      (symbolicEnvCanonicalSourceObjectData datum probe).toStructuredComparisonObject
      (symbolicEnvCanonicalTargetObjectData datum probe).toStructuredComparisonObject :=
  source.structuredMorphism probe

def symbolicEnvCanonicalGeometricRawPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    {datum : SymbolicEnvDatum ctx}
    (source : SymbolicEnvCanonicalRawPayloadSource datum)
    (probe : SymbolicEnvCanonicalProbe) :
    GeometricFramedPeriodRawPayload (symbolicEnvCanonicalStructuredMorphism source probe) :=
  { geometricCorrespondence := source.geometricCorrespondence probe
    deRhamClass := source.deRhamClass probe
    bettiClass := source.bettiClass probe
    bettiCoframe := source.bettiCoframe probe
    geometricScalarPeriod := source.geometricScalarPeriod probe
    concreteDeRhamVector := source.concreteDeRhamVector probe
    concreteBettiImage := source.concreteBettiImage probe
    concreteBettiCycle := source.concreteBettiCycle probe
    concreteComparisonCompatibility := source.concreteComparisonCompatibility probe
    concreteScalarPeriod_eq_evaluation := source.concreteScalarPeriod_eq_evaluation probe
    deRhamClassRealizesFrameTarget := source.deRhamClassRealizesFrameTarget probe
    bettiClassRealizesCycleTarget := source.bettiClassRealizesCycleTarget probe
    grothendieckPeriodEvaluationTarget := source.grothendieckPeriodEvaluationTarget probe }

def symbolicEnvCanonicalConcreteFramedDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    {datum : SymbolicEnvDatum ctx}
    (source : SymbolicEnvCanonicalRawPayloadSource datum) :
    SymbolicEnvCanonicalProbe → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx :=
  fun probe _ =>
    (SomeGeometricFramedPeriodData.ofRawPayload
      (symbolicEnvCanonicalSourceObjectData datum probe)
      (symbolicEnvCanonicalTargetObjectData datum probe)
      (source.structuredMorphism probe)
      (symbolicEnvCanonicalGeometricRawPayload source probe)).toSomeConcreteFramedPeriodData

def symbolicEnvCanonicalFramedProbeFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    {datum : SymbolicEnvDatum ctx}
    (source : SymbolicEnvCanonicalRawPayloadSource datum) :
    FramedProbeFamily ctx :=
  concreteFramedProbeFamily
    (ProbeIndex := SymbolicEnvCanonicalProbe)
    (symbolicEnvCanonicalConcreteFramedDatum source)

def symbolicEnvProbeExtensionalityOfFaithfulFramedProbes
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {datum : SymbolicEnvDatum ctx}
    (source : SymbolicEnvCanonicalRawPayloadSource datum)
    (faithful :
      FaithfulFramedProbeTarget
        ctx
        (symbolicEnvCanonicalFramedProbeFamily source)
        structuredEq) :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily
        (ProbeIndex := SymbolicEnvCanonicalProbe)
        (symbolicEnvCanonicalConcreteFramedDatum source)).toScalarProbeFamily
      (tautologicalBasisFreePeriodMapEquality ctx structuredEq) :=
  let family :=
    concreteFramedProbeFamily
      (ProbeIndex := SymbolicEnvCanonicalProbe)
      (symbolicEnvCanonicalConcreteFramedDatum source)
  let faithful' : FaithfulFramedProbeTarget ctx family structuredEq := faithful
  ProbeExtensionalityForBasisFreePeriodMap.ofFaithfulFramedProbeTarget
    (family := family)
    (structuredEq := structuredEq)
    (tautologicalFramedPeriodsInduceProbeEquality family)
    faithful'

structure SymbolicEnvRawFramedPeriodPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx) where
  symbolicDatum : SymbolicEnvDatum ctx
  canonicalRawPayloadSource : SymbolicEnvCanonicalRawPayloadSource symbolicDatum
  ProbeIndex : Type w
  sourceObjectData :
    ProbeIndex → SomeStructuredComparisonMorphism ctx → GeometricComparisonObjectData ctx
  targetObjectData :
    ProbeIndex → SomeStructuredComparisonMorphism ctx → GeometricComparisonObjectData ctx
  structuredMorphism :
    (probe : ProbeIndex) →
      (morphism : SomeStructuredComparisonMorphism ctx) →
        ClassicalStructuredComparisonMorphism
          (sourceObjectData probe morphism).toStructuredComparisonObject
          (targetObjectData probe morphism).toStructuredComparisonObject
  framedPayload :
    (probe : ProbeIndex) →
      (morphism : SomeStructuredComparisonMorphism ctx) →
        GeometricFramedPeriodRawPayload (structuredMorphism probe morphism)
  traceNativeEnvReplayData :
    CertifiedEnvReplayData ctx
      (∀ _ : SymbolicEnvCanonicalProbe,
        symbolicDatum.envelopeCorrespondence.correspondenceTarget ∧
          symbolicDatum.ambientObjectData.comparisonData.grothendieckComparisonTarget ∧
          symbolicDatum.envelopeObjectData.comparisonData.grothendieckComparisonTarget ∧
          symbolicDatum.ambientObjectData.comparisonData.periodCompatibilityTarget ∧
          symbolicDatum.envelopeObjectData.comparisonData.periodCompatibilityTarget)
      symbolicDatum.envelopeObjectData.comparisonData.periodCompatibilityTarget
  probeExtensionality :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily
        (fun probe morphism =>
          (SomeGeometricFramedPeriodData.ofRawPayload
            (sourceObjectData probe morphism)
            (targetObjectData probe morphism)
            (structuredMorphism probe morphism)
            (framedPayload probe morphism)).toSomeConcreteFramedPeriodData)).toScalarProbeFamily
      (tautologicalBasisFreePeriodMapEquality ctx structuredEq)

def symbolicEnvRawFramedPeriodPayloadOfCanonicalSource
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {datum : SymbolicEnvDatum ctx}
    (source : SymbolicEnvCanonicalRawPayloadSource datum)
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (ProbeIndex := SymbolicEnvCanonicalProbe)
          (symbolicEnvCanonicalConcreteFramedDatum source)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq)) :
    SymbolicEnvRawFramedPeriodPayload structuredEq where
  symbolicDatum := datum
  canonicalRawPayloadSource := source
  ProbeIndex := SymbolicEnvCanonicalProbe
  sourceObjectData := fun probe _ => symbolicEnvCanonicalSourceObjectData datum probe
  targetObjectData := fun probe _ => symbolicEnvCanonicalTargetObjectData datum probe
  structuredMorphism := fun probe _ => source.structuredMorphism probe
  framedPayload := fun probe _ => symbolicEnvCanonicalGeometricRawPayload source probe
  traceNativeEnvReplayData := source.traceNativeEnvReplayData
  probeExtensionality := probeExtensionality

def SymbolicEnvRawFramedPeriodPayload.geometricFramedPeriodData
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicEnvRawFramedPeriodPayload structuredEq) :
    data.ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeGeometricFramedPeriodData ctx :=
  fun probe morphism =>
    SomeGeometricFramedPeriodData.ofRawPayload
      (data.sourceObjectData probe morphism)
      (data.targetObjectData probe morphism)
      (data.structuredMorphism probe morphism)
      (data.framedPayload probe morphism)

structure SymbolicEnvFramedPeriodDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx) where
  symbolicDatum : SymbolicEnvDatum ctx
  canonicalRawPayloadSource : SymbolicEnvCanonicalRawPayloadSource symbolicDatum
  ProbeIndex : Type w
  geometricFramedPeriodData :
    ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeGeometricFramedPeriodData ctx
  traceNativeEnvReplayData :
    CertifiedEnvReplayData ctx
      (∀ _ : SymbolicEnvCanonicalProbe,
        symbolicDatum.envelopeCorrespondence.correspondenceTarget ∧
          symbolicDatum.ambientObjectData.comparisonData.grothendieckComparisonTarget ∧
          symbolicDatum.envelopeObjectData.comparisonData.grothendieckComparisonTarget ∧
          symbolicDatum.ambientObjectData.comparisonData.periodCompatibilityTarget ∧
          symbolicDatum.envelopeObjectData.comparisonData.periodCompatibilityTarget)
      symbolicDatum.envelopeObjectData.comparisonData.periodCompatibilityTarget
  probeExtensionality :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily
        (fun probe morphism =>
          (geometricFramedPeriodData probe morphism).toSomeConcreteFramedPeriodData)).toScalarProbeFamily
      (tautologicalBasisFreePeriodMapEquality ctx structuredEq)

def symbolicEnvFramedPeriodDatumOfRawPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (payload : SymbolicEnvRawFramedPeriodPayload structuredEq) :
    SymbolicEnvFramedPeriodDatum structuredEq where
  symbolicDatum := payload.symbolicDatum
  canonicalRawPayloadSource := payload.canonicalRawPayloadSource
  ProbeIndex := payload.ProbeIndex
  geometricFramedPeriodData := payload.geometricFramedPeriodData
  traceNativeEnvReplayData := payload.traceNativeEnvReplayData
  probeExtensionality := payload.probeExtensionality

def symbolicEnvFramedPeriodDatumOfCanonicalSource
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {datum : SymbolicEnvDatum ctx}
    (source : SymbolicEnvCanonicalRawPayloadSource datum)
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (ProbeIndex := SymbolicEnvCanonicalProbe)
          (symbolicEnvCanonicalConcreteFramedDatum source)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq)) :
    SymbolicEnvFramedPeriodDatum structuredEq :=
  symbolicEnvFramedPeriodDatumOfRawPayload
    (symbolicEnvRawFramedPeriodPayloadOfCanonicalSource source probeExtensionality)

def symbolicGeneratorTableSlotLabelAssignment
  {ctx : ClassicalComparisonContext.{u, v}} :
    GeneratorTableSlotLabelAssignment ctx where
  corr := {
    sourceSlot := "source"
    targetSlot := "target"
    bettiSlot := "betti"
    deRhamSlot := "deRham"
    comparisonSlot := "comparison"
  }
  loc := {
    sourceSlot := "ambient"
    targetSlot := "open"
    bettiSlot := "betti"
    deRhamSlot := "deRham"
    comparisonSlot := "comparison"
  }
  nis := {
    sourceSlot := "base"
    targetSlot := "patch"
    bettiSlot := "betti"
    deRhamSlot := "deRham"
    comparisonSlot := "comparison"
  }
  a1 := {
    sourceSlot := "base"
    targetSlot := "cylinder"
    bettiSlot := "betti"
    deRhamSlot := "deRham"
    comparisonSlot := "comparison"
  }
  env := {
    sourceSlot := "ambient"
    targetSlot := "envelope"
    bettiSlot := "betti"
    deRhamSlot := "deRham"
    comparisonSlot := "comparison"
  }

@[simp] theorem symbolicGeneratorTableSlotLabelAssignment_slotLabel_corr_source
  {ctx : ClassicalComparisonContext.{u, v}} :
  (symbolicGeneratorTableSlotLabelAssignment (ctx := ctx)).slotLabel
      (.corr .source) = "source" := rfl

@[simp] theorem symbolicGeneratorTableSlotLabelAssignment_slotLabel_nis_target
  {ctx : ClassicalComparisonContext.{u, v}} :
  (symbolicGeneratorTableSlotLabelAssignment (ctx := ctx)).slotLabel
      (.nis .target) = "patch" := rfl

@[simp] theorem symbolicGeneratorTableSlotLabelAssignment_slotLabel_env_comparison
    {ctx : ClassicalComparisonContext.{u, v}} :
    (symbolicGeneratorTableSlotLabelAssignment (ctx := ctx)).slotLabel
      (.env .comparison) = "comparison" := rfl

def symbolicGeneratorTableSlotLabelSeparationData
    {ctx : ClassicalComparisonContext.{u, v}} :
    GeneratorTableSlotLabelSeparationData
      (symbolicGeneratorTableSlotLabelAssignment (ctx := ctx)) where
  corrSeparated := by
    show "source" ≠ "target" ∧ "betti" ≠ "deRham" ∧ "comparison" ≠ "source" ∧ "comparison" ≠ "target"
    decide
  locSeparated := by
    show "ambient" ≠ "open" ∧ "betti" ≠ "deRham" ∧ "comparison" ≠ "ambient" ∧ "comparison" ≠ "open"
    decide
  nisSeparated := by
    show "base" ≠ "patch" ∧ "betti" ≠ "deRham" ∧ "comparison" ≠ "base" ∧ "comparison" ≠ "patch"
    decide
  a1Separated := by
    show "base" ≠ "cylinder" ∧ "betti" ≠ "deRham" ∧ "comparison" ≠ "base" ∧ "comparison" ≠ "cylinder"
    decide
  envSeparated := by
    show "ambient" ≠ "envelope" ∧ "betti" ≠ "deRham" ∧ "comparison" ≠ "ambient" ∧ "comparison" ≠ "envelope"
    decide

inductive SymbolicNisCanonicalProbe
  | baseToPatch
deriving DecidableEq, Repr

def symbolicNisCanonicalSourceObjectData
      {ctx : ClassicalComparisonContext.{u, v}}
      (datum : SymbolicNisDatum ctx) :
      SymbolicNisCanonicalProbe → GeometricComparisonObjectData ctx
    | .baseToPatch => datum.baseObjectData

  def symbolicNisCanonicalTargetObjectData
      {ctx : ClassicalComparisonContext.{u, v}}
      (datum : SymbolicNisDatum ctx) :
      SymbolicNisCanonicalProbe → GeometricComparisonObjectData ctx
    | .baseToPatch => datum.patchObjectData

  structure SymbolicNisCanonicalRawPayloadSource
      {ctx : ClassicalComparisonContext.{u, v}}
      (datum : SymbolicNisDatum ctx) where
    structuredMorphism :
      (probe : SymbolicNisCanonicalProbe) →
        ClassicalStructuredComparisonMorphism
          (symbolicNisCanonicalSourceObjectData datum probe).toStructuredComparisonObject
          (symbolicNisCanonicalTargetObjectData datum probe).toStructuredComparisonObject
    geometricCorrespondence :
      (probe : SymbolicNisCanonicalProbe) →
        GeometricCorrespondence
          (symbolicNisCanonicalSourceObjectData datum probe).deRhamData.geometricObject
          (symbolicNisCanonicalTargetObjectData datum probe).bettiData.geometricObject
    deRhamClass :
      (probe : SymbolicNisCanonicalProbe) →
        (symbolicNisCanonicalSourceObjectData datum probe).DeRhamCarrier
    bettiClass :
      (probe : SymbolicNisCanonicalProbe) →
        (symbolicNisCanonicalTargetObjectData datum probe).BettiCarrier
    bettiCoframe :
      (probe : SymbolicNisCanonicalProbe) →
        (symbolicNisCanonicalTargetObjectData datum probe).toStructuredComparisonObject.BettiOverScalar →ₗ[ctx.ScalarField]
          ctx.ScalarField
    geometricScalarPeriod : SymbolicNisCanonicalProbe → ctx.ScalarField
    concreteDeRhamVector :
      (probe : SymbolicNisCanonicalProbe) →
        (symbolicNisCanonicalSourceObjectData datum probe).toStructuredComparisonObject.DeRhamOverScalar
    concreteBettiImage :
      (probe : SymbolicNisCanonicalProbe) →
        (symbolicNisCanonicalTargetObjectData datum probe).toStructuredComparisonObject.BettiOverScalar
    concreteBettiCycle :
      (probe : SymbolicNisCanonicalProbe) →
        (symbolicNisCanonicalTargetObjectData datum probe).toStructuredComparisonObject.BettiOverScalar
    concreteComparisonCompatibility :
      (probe : SymbolicNisCanonicalProbe) →
        concreteBettiImage probe =
          (symbolicNisCanonicalTargetObjectData datum probe).toStructuredComparisonObject.comparisonIso
            ((structuredMorphism probe).deRhamMapOverScalar (concreteDeRhamVector probe))
    concreteScalarPeriod_eq_evaluation :
      (probe : SymbolicNisCanonicalProbe) →
        geometricScalarPeriod probe = bettiCoframe probe (concreteBettiImage probe)
    deRhamClassRealizesFrameTarget : SymbolicNisCanonicalProbe → Prop
    bettiClassRealizesCycleTarget : SymbolicNisCanonicalProbe → Prop
    grothendieckPeriodEvaluationTarget : SymbolicNisCanonicalProbe → Prop
    baseComparisonNaturalityTarget :
      datum.baseObjectData.comparisonData.comparison.comparisonNaturalityTarget
    patchComparisonNaturalityTarget :
      datum.patchObjectData.comparisonData.comparison.comparisonNaturalityTarget
    overlapComparisonNaturalityTarget :
      datum.overlapObjectData.comparisonData.comparison.comparisonNaturalityTarget
    traceNativePatchReplayData :
      CertifiedNisPatchReplayData ctx
        (∀ _ : SymbolicNisCanonicalProbe,
          datum.baseObjectData.comparisonData.grothendieckComparisonTarget ∧
            datum.patchObjectData.comparisonData.grothendieckComparisonTarget ∧
            datum.overlapObjectData.comparisonData.grothendieckComparisonTarget)
        datum.overlapObjectData.comparisonData.grothendieckComparisonTarget

def SymbolicNisDatum.canonicalRawPayloadSource
      {ctx : ClassicalComparisonContext.{u, v}}
      (datum : SymbolicNisDatum ctx)
      (source : SymbolicNisCanonicalRawPayloadSource datum) := source

def symbolicNisCanonicalStructuredMorphism
      {ctx : ClassicalComparisonContext.{u, v}}
      {datum : SymbolicNisDatum ctx}
      (source : SymbolicNisCanonicalRawPayloadSource datum)
      (probe : SymbolicNisCanonicalProbe) :
      ClassicalStructuredComparisonMorphism
        (symbolicNisCanonicalSourceObjectData datum probe).toStructuredComparisonObject
        (symbolicNisCanonicalTargetObjectData datum probe).toStructuredComparisonObject :=
    source.structuredMorphism probe

def symbolicNisCanonicalGeometricRawPayload
      {ctx : ClassicalComparisonContext.{u, v}}
      {datum : SymbolicNisDatum ctx}
      (source : SymbolicNisCanonicalRawPayloadSource datum)
      (probe : SymbolicNisCanonicalProbe) :
      GeometricFramedPeriodRawPayload (symbolicNisCanonicalStructuredMorphism source probe) :=
    { geometricCorrespondence := source.geometricCorrespondence probe
      deRhamClass := source.deRhamClass probe
      bettiClass := source.bettiClass probe
      bettiCoframe := source.bettiCoframe probe
      geometricScalarPeriod := source.geometricScalarPeriod probe
      concreteDeRhamVector := source.concreteDeRhamVector probe
      concreteBettiImage := source.concreteBettiImage probe
      concreteBettiCycle := source.concreteBettiCycle probe
      concreteComparisonCompatibility := source.concreteComparisonCompatibility probe
      concreteScalarPeriod_eq_evaluation := source.concreteScalarPeriod_eq_evaluation probe
      deRhamClassRealizesFrameTarget := source.deRhamClassRealizesFrameTarget probe
      bettiClassRealizesCycleTarget := source.bettiClassRealizesCycleTarget probe
      grothendieckPeriodEvaluationTarget := source.grothendieckPeriodEvaluationTarget probe }

def symbolicNisCanonicalConcreteFramedDatum
      {ctx : ClassicalComparisonContext.{u, v}}
      {datum : SymbolicNisDatum ctx}
      (source : SymbolicNisCanonicalRawPayloadSource datum) :
      SymbolicNisCanonicalProbe → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx :=
    fun probe _ =>
      (SomeGeometricFramedPeriodData.ofRawPayload
        (symbolicNisCanonicalSourceObjectData datum probe)
        (symbolicNisCanonicalTargetObjectData datum probe)
        (source.structuredMorphism probe)
        (symbolicNisCanonicalGeometricRawPayload source probe)).toSomeConcreteFramedPeriodData

def symbolicNisCanonicalFramedProbeFamily
      {ctx : ClassicalComparisonContext.{u, v}}
      {datum : SymbolicNisDatum ctx}
      (source : SymbolicNisCanonicalRawPayloadSource datum) :
      FramedProbeFamily ctx :=
    concreteFramedProbeFamily
      (ProbeIndex := SymbolicNisCanonicalProbe)
      (symbolicNisCanonicalConcreteFramedDatum source)

def symbolicNisProbeExtensionalityOfFaithfulFramedProbes
      {ctx : ClassicalComparisonContext.{u, v}}
      {structuredEq : StructuredComparisonEquality ctx}
      {datum : SymbolicNisDatum ctx}
      (source : SymbolicNisCanonicalRawPayloadSource datum)
      (faithful :
        FaithfulFramedProbeTarget
          ctx
          (symbolicNisCanonicalFramedProbeFamily source)
          structuredEq) :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (ProbeIndex := SymbolicNisCanonicalProbe)
          (symbolicNisCanonicalConcreteFramedDatum source)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq) :=
    let family :=
      concreteFramedProbeFamily
        (ProbeIndex := SymbolicNisCanonicalProbe)
        (symbolicNisCanonicalConcreteFramedDatum source)
    let faithful' : FaithfulFramedProbeTarget ctx family structuredEq := faithful
    ProbeExtensionalityForBasisFreePeriodMap.ofFaithfulFramedProbeTarget
      (family := family)
      (structuredEq := structuredEq)
      (tautologicalFramedPeriodsInduceProbeEquality family)
      faithful'

structure SymbolicNisRawFramedPeriodPayload
      {ctx : ClassicalComparisonContext.{u, v}}
      (structuredEq : StructuredComparisonEquality ctx) where
    symbolicDatum : SymbolicNisDatum ctx
    canonicalRawPayloadSource : SymbolicNisCanonicalRawPayloadSource symbolicDatum
    ProbeIndex : Type w
    sourceObjectData :
      ProbeIndex → SomeStructuredComparisonMorphism ctx → GeometricComparisonObjectData ctx
    targetObjectData :
      ProbeIndex → SomeStructuredComparisonMorphism ctx → GeometricComparisonObjectData ctx
    structuredMorphism :
      (probe : ProbeIndex) →
        (morphism : SomeStructuredComparisonMorphism ctx) →
          ClassicalStructuredComparisonMorphism
            (sourceObjectData probe morphism).toStructuredComparisonObject
            (targetObjectData probe morphism).toStructuredComparisonObject
    framedPayload :
      (probe : ProbeIndex) →
        (morphism : SomeStructuredComparisonMorphism ctx) →
          GeometricFramedPeriodRawPayload (structuredMorphism probe morphism)
    traceNativePatchReplayData :
      CertifiedNisPatchReplayData ctx
        (∀ _ : SymbolicNisCanonicalProbe,
          symbolicDatum.baseObjectData.comparisonData.grothendieckComparisonTarget ∧
            symbolicDatum.patchObjectData.comparisonData.grothendieckComparisonTarget ∧
            symbolicDatum.overlapObjectData.comparisonData.grothendieckComparisonTarget)
        symbolicDatum.overlapObjectData.comparisonData.grothendieckComparisonTarget
    probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (fun probe morphism =>
            (SomeGeometricFramedPeriodData.ofRawPayload
              (sourceObjectData probe morphism)
              (targetObjectData probe morphism)
              (structuredMorphism probe morphism)
              (framedPayload probe morphism)).toSomeConcreteFramedPeriodData)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq)

def symbolicNisRawFramedPeriodPayloadOfCanonicalSource
      {ctx : ClassicalComparisonContext.{u, v}}
      {structuredEq : StructuredComparisonEquality ctx}
      {datum : SymbolicNisDatum ctx}
      (source : SymbolicNisCanonicalRawPayloadSource datum)
      (probeExtensionality :
        ProbeExtensionalityForBasisFreePeriodMap
          ctx
          (concreteFramedProbeFamily
            (ProbeIndex := SymbolicNisCanonicalProbe)
            (symbolicNisCanonicalConcreteFramedDatum source)).toScalarProbeFamily
          (tautologicalBasisFreePeriodMapEquality ctx structuredEq)) :
      SymbolicNisRawFramedPeriodPayload structuredEq where
    symbolicDatum := datum
    canonicalRawPayloadSource := source
    ProbeIndex := SymbolicNisCanonicalProbe
    sourceObjectData := fun probe _ => symbolicNisCanonicalSourceObjectData datum probe
    targetObjectData := fun probe _ => symbolicNisCanonicalTargetObjectData datum probe
    structuredMorphism := fun probe _ => source.structuredMorphism probe
    framedPayload := fun probe _ => symbolicNisCanonicalGeometricRawPayload source probe
    traceNativePatchReplayData := source.traceNativePatchReplayData
    probeExtensionality := probeExtensionality

def SymbolicNisRawFramedPeriodPayload.geometricFramedPeriodData
      {ctx : ClassicalComparisonContext.{u, v}}
      {structuredEq : StructuredComparisonEquality ctx}
      (data : SymbolicNisRawFramedPeriodPayload structuredEq) :
      data.ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeGeometricFramedPeriodData ctx :=
    fun probe morphism =>
      SomeGeometricFramedPeriodData.ofRawPayload
        (data.sourceObjectData probe morphism)
        (data.targetObjectData probe morphism)
        (data.structuredMorphism probe morphism)
        (data.framedPayload probe morphism)

structure SymbolicNisFramedPeriodDatum
      {ctx : ClassicalComparisonContext.{u, v}}
      (structuredEq : StructuredComparisonEquality ctx) where
    symbolicDatum : SymbolicNisDatum ctx
    canonicalRawPayloadSource : SymbolicNisCanonicalRawPayloadSource symbolicDatum
    ProbeIndex : Type w
    geometricFramedPeriodData :
      ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeGeometricFramedPeriodData ctx
    traceNativePatchReplayData :
      CertifiedNisPatchReplayData ctx
        (∀ _ : SymbolicNisCanonicalProbe,
          symbolicDatum.baseObjectData.comparisonData.grothendieckComparisonTarget ∧
            symbolicDatum.patchObjectData.comparisonData.grothendieckComparisonTarget ∧
            symbolicDatum.overlapObjectData.comparisonData.grothendieckComparisonTarget)
        symbolicDatum.overlapObjectData.comparisonData.grothendieckComparisonTarget
    probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (fun probe morphism =>
            (geometricFramedPeriodData probe morphism).toSomeConcreteFramedPeriodData)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq)

def symbolicNisFramedPeriodDatumOfRawPayload
      {ctx : ClassicalComparisonContext.{u, v}}
      {structuredEq : StructuredComparisonEquality ctx}
      (payload : SymbolicNisRawFramedPeriodPayload structuredEq) :
      SymbolicNisFramedPeriodDatum structuredEq where
    symbolicDatum := payload.symbolicDatum
    canonicalRawPayloadSource := payload.canonicalRawPayloadSource
    ProbeIndex := payload.ProbeIndex
    geometricFramedPeriodData := payload.geometricFramedPeriodData
    traceNativePatchReplayData := payload.traceNativePatchReplayData
    probeExtensionality := payload.probeExtensionality

def symbolicNisFramedPeriodDatumOfCanonicalSource
      {ctx : ClassicalComparisonContext.{u, v}}
      {structuredEq : StructuredComparisonEquality ctx}
      {datum : SymbolicNisDatum ctx}
      (source : SymbolicNisCanonicalRawPayloadSource datum)
      (probeExtensionality :
        ProbeExtensionalityForBasisFreePeriodMap
          ctx
          (concreteFramedProbeFamily
            (ProbeIndex := SymbolicNisCanonicalProbe)
            (symbolicNisCanonicalConcreteFramedDatum source)).toScalarProbeFamily
          (tautologicalBasisFreePeriodMapEquality ctx structuredEq)) :
      SymbolicNisFramedPeriodDatum structuredEq :=
    symbolicNisFramedPeriodDatumOfRawPayload
      (symbolicNisRawFramedPeriodPayloadOfCanonicalSource source probeExtensionality)


structure SymbolicSlotRecoveryData
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    (assignment : GeneratorTableSlotLabelAssignment ctx)
    (slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        StructuredComparisonSlotData) where
  separationData : GeneratorTableSlotLabelSeparationData assignment
  recoveredAssignmentMap : SymbolicRecoveredSlotAssignmentMap assignment slotData

theorem SymbolicSlotRecoveryData.toGeneratorTablePortLabelSeparationAssumption
    {ctx : ClassicalComparisonContext.{u, v}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {table : GeneratorRealizationAssignmentTable ctx}
    {slotData :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
        StructuredComparisonSlotData}
    (data :
      SymbolicSlotRecoveryData
        (GeneratorRealizationAssignmentTable.toGeneratorTableSlotLabelAssignment table)
        slotData) :
    GeneratorTablePortLabelSeparationAssumption table slotData :=
  GeneratorTablePortLabelSeparationAssumption.ofData
    data.separationData.toGeneratorRowSlotSeparationData
    data.recoveredAssignmentMap.toRecoveredSlotAssignmentData

def symbolicCorrFiniteCorrespondenceUniversalityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicCorrDatum ctx) :
    FiniteCorrespondenceUniversalityTarget ctx :=
  FiniteCorrespondenceUniversalityTarget.ofCorrFamily
    (symbolicCorrGeneratorFamilyData datum)
    datum.correspondence.correspondenceTarget
    datum.sourceObjectData.comparisonData.grothendieckComparisonTarget

def symbolicLocLocalizationTriangleUniversalityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicLocDatum ctx) :
    LocalizationTriangleUniversalityTarget ctx :=
  LocalizationTriangleUniversalityTarget.ofLocFamily
    (symbolicLocGeneratorFamilyData datum)
    datum.ambientObjectData.comparisonData.periodCompatibilityTarget
    datum.openObjectData.comparisonData.periodCompatibilityTarget

def symbolicNisOperationalGeometricPresentationTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicNisDatum ctx) :
    OperationalGeometricPresentationTarget ctx :=
  OperationalGeometricPresentationTarget.ofEndpoints
    datum.base
    datum.patch
    datum.baseObjectData.comparisonData.grothendieckComparisonTarget
    datum.overlapObjectData.comparisonData.grothendieckComparisonTarget

def symbolicNisTraceToGeometricPacketEquivalenceTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicNisDatum ctx) :
    TraceToGeometricPacketEquivalenceTarget ctx :=
  TraceToGeometricPacketEquivalenceTarget.ofRealization
    (symbolicNisRealizationFunctorData datum)
    datum.patchObjectData.comparisonData.grothendieckComparisonTarget
    (datum.baseObjectData.comparisonData.grothendieckComparisonTarget ∧
      datum.patchObjectData.comparisonData.grothendieckComparisonTarget ∧
      datum.overlapObjectData.comparisonData.grothendieckComparisonTarget)

def symbolicNisGeometricPresentationTheoremTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicNisDatum ctx) :
    GeometricPresentationTheoremTarget ctx :=
  GeometricPresentationTheoremTarget.ofOperationalAndPacket
    (symbolicNisOperationalGeometricPresentationTarget datum)
    (symbolicNisTraceToGeometricPacketEquivalenceTarget datum)
    datum.baseObjectData.comparisonData.grothendieckComparisonTarget

def symbolicA1TraceToGeometricPacketEquivalenceTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicA1Datum ctx) :
    TraceToGeometricPacketEquivalenceTarget ctx :=
  TraceToGeometricPacketEquivalenceTarget.ofRealization
    (symbolicA1RealizationFunctorData datum)
    datum.baseObjectData.comparisonData.periodCompatibilityTarget
    (datum.baseObjectData.comparisonData.grothendieckComparisonTarget ∧
      datum.cylinderObjectData.comparisonData.grothendieckComparisonTarget ∧
      datum.baseObjectData.comparisonData.periodCompatibilityTarget ∧
      datum.cylinderObjectData.comparisonData.periodCompatibilityTarget)

def symbolicA1RealBettiDeRhamComparisonRealizationTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicA1Datum ctx) :
    RealBettiDeRhamComparisonRealizationTarget ctx :=
  RealBettiDeRhamComparisonRealizationTarget.ofRealization
    (symbolicA1RealizationFunctorData datum)
    datum.baseObjectData.comparisonData.grothendieckComparisonTarget
    datum.cylinderObjectData.comparisonData.grothendieckComparisonTarget
    (datum.baseObjectData.comparisonData.periodCompatibilityTarget ∧
      datum.cylinderObjectData.comparisonData.periodCompatibilityTarget)

/-- The symbolic `A1` example has no correspondence indices, so the functoriality theorem field is
vacuous. This packages the already available realization-side data without inventing new framed
period witnesses. -/
def symbolicA1GeometricFramedPeriodFunctoriality
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicA1Datum ctx) :
    GeometricFramedPeriodFunctoriality ctx (symbolicA1RealizationFunctorData datum) where
  sourceFraming := fun corr => nomatch corr
  targetFraming := fun corr => nomatch corr
  theoremTarget := by
    intro corr
    nomatch corr
  framedPeriodFunctorialityTarget :=
    datum.baseObjectData.comparisonData.grothendieckComparisonTarget ∧
      datum.cylinderObjectData.comparisonData.grothendieckComparisonTarget ∧
      datum.baseObjectData.comparisonData.periodCompatibilityTarget ∧
      datum.cylinderObjectData.comparisonData.periodCompatibilityTarget
  framedExtractionCompatibilityTarget :=
    datum.baseObjectData.comparisonData.periodCompatibilityTarget ∧
      datum.cylinderObjectData.comparisonData.periodCompatibilityTarget

/-- The symbolic `A1` example likewise has vacuous correspondence-indexed naturality data; the
stored comparison-compatibility target remains the non-vacuous part exposed here. -/
def symbolicA1GeometricComparisonNaturality
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicA1Datum ctx) :
    GeometricComparisonNaturality ctx (symbolicA1RealizationFunctorData datum) where
  theoremTarget := by
    intro corr
    nomatch corr
  baseChangeNaturalityTarget :=
    datum.baseObjectData.comparisonData.periodCompatibilityTarget ∧
      datum.cylinderObjectData.comparisonData.periodCompatibilityTarget

/-- Concrete object-data package already present in the symbolic `A1` example. -/
def symbolicA1GeometricObjectData
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicA1Datum ctx) :
    (symbolicA1RealizationFunctorData datum).ObjectIndex → GeometricComparisonObjectData ctx
  | .base => datum.baseObjectData
  | .cylinder => datum.cylinderObjectData

@[simp] theorem symbolicA1GeometricObjectData_compatibilityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicA1Datum ctx)
    (idx : (symbolicA1RealizationFunctorData datum).ObjectIndex) :
    symbolicA1GeometricObjectData datum idx =
      (symbolicA1RealizationFunctorData datum).geometricComparisonObjectData idx := by
  cases idx <;> rfl

/-- Thin projection: any symbolic `A1` geometric framed-datum family already descends to concrete
framed data by forgetting the geometric witness. -/
def symbolicA1GeometricToConcreteFramed
    {ctx : ClassicalComparisonContext.{u, v}}
    {ProbeIndex : Type _}
    (geometricFramedDatum :
      ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeGeometricFramedPeriodData ctx) :
    GeometricPeriodsRealizeConcreteFramedData ctx geometricFramedDatum where
  theoremTarget := by
    intro probe morphism
    rfl

/-- The probe index carried by the explicit symbolic `A1` framed-period layer. -/
abbrev symbolicA1ProbeIndex
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicA1FramedPeriodDatum structuredEq) : Type _ :=
  data.ProbeIndex

/-- Honest constructor for the sigma-packaged geometric framed witness family carried by the
explicit symbolic `A1` framed-period layer. -/
def symbolicA1GeometricFramedDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicA1FramedPeriodDatum structuredEq) :
    data.ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeGeometricFramedPeriodData ctx :=
  data.geometricFramedPeriodData

@[simp] theorem symbolicA1GeometricFramedDatum_apply
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicA1FramedPeriodDatum structuredEq)
    (probe : data.ProbeIndex)
    (morphism : SomeStructuredComparisonMorphism ctx) :
    symbolicA1GeometricFramedDatum data probe morphism =
      data.geometricFramedPeriodData probe morphism := rfl

/-- Concrete framed witnesses obtained by forgetting the geometric component of the symbolic `A1`
framed-period layer. -/
def symbolicA1ConcreteFramedDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicA1FramedPeriodDatum structuredEq) :
    data.ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx :=
  fun probe morphism => (symbolicA1GeometricFramedDatum data probe morphism).toSomeConcreteFramedPeriodData

@[simp] theorem symbolicA1ConcreteFramedDatum_apply
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicA1FramedPeriodDatum structuredEq)
    (probe : data.ProbeIndex)
    (morphism : SomeStructuredComparisonMorphism ctx) :
    symbolicA1ConcreteFramedDatum data probe morphism =
      (symbolicA1GeometricFramedDatum data probe morphism).toSomeConcreteFramedPeriodData := rfl

/-- The symbolic `A1` lane can reuse the existing tautological basis-free equality once a
structured comparison equality has been chosen. -/
def symbolicA1BasisFreePeriodMapEquality
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx) :
    BasisFreePeriodMapEquality ctx :=
  tautologicalBasisFreePeriodMapEquality ctx structuredEq

/-- With the tautological basis-free equality in place, packed reconstruction is the identity step
already provided by the existing tomography core. -/
def symbolicA1PackedReconstruction
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx) :
    BasisFreePeriodMapDeterminesPackedComparison
      ctx
      (symbolicA1BasisFreePeriodMapEquality structuredEq)
      structuredEq :=
  { theoremTarget := by
      intro left right hBasis
      exact hBasis }

  /-- Probe extensionality supplied by the explicit symbolic `A1` framed-period layer. -/
  def symbolicA1ProbeExtensionality
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicA1FramedPeriodDatum structuredEq) :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily (symbolicA1ConcreteFramedDatum data)).toScalarProbeFamily
        (symbolicA1BasisFreePeriodMapEquality structuredEq) :=
    data.probeExtensionality

namespace GeometricRealizationTomographySoundness

def symbolicLocGeometricFramedPeriodFunctoriality
    {ctx : ClassicalComparisonContext.{u, v}}
    {datum : SymbolicLocDatum ctx}
  (_source : SymbolicLocCanonicalRawPayloadSource datum) :
    GeometricFramedPeriodFunctoriality ctx (symbolicLocRealizationFunctorData datum) where
  sourceFraming := fun corr => nomatch corr
  targetFraming := fun corr => nomatch corr
  theoremTarget := by
    intro corr
    nomatch corr
  framedPeriodFunctorialityTarget :=
    datum.ambientObjectData.comparisonData.grothendieckComparisonTarget ∧
      datum.openObjectData.comparisonData.grothendieckComparisonTarget ∧
      datum.closedObjectData.comparisonData.grothendieckComparisonTarget
  framedExtractionCompatibilityTarget :=
    datum.ambientObjectData.comparisonData.periodCompatibilityTarget ∧
      datum.openObjectData.comparisonData.periodCompatibilityTarget ∧
      datum.closedObjectData.comparisonData.periodCompatibilityTarget

def symbolicLocGeometricComparisonNaturality
    {ctx : ClassicalComparisonContext.{u, v}}
    {datum : SymbolicLocDatum ctx}
  (_source : SymbolicLocCanonicalRawPayloadSource datum) :
    GeometricComparisonNaturality ctx (symbolicLocRealizationFunctorData datum) where
  theoremTarget := by
    intro corr
    nomatch corr
  baseChangeNaturalityTarget :=
    datum.ambientObjectData.comparisonData.comparison.comparisonNaturalityTarget ∧
      datum.openObjectData.comparisonData.comparison.comparisonNaturalityTarget ∧
      datum.closedObjectData.comparisonData.comparison.comparisonNaturalityTarget

def ofSymbolicLocFramedData
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicLocFramedPeriodDatum structuredEq) :
    GeometricRealizationTomographySoundness ctx structuredEq :=
  ofFunctorialityAndFramedData
    (symbolicLocRealizationFunctorData data.symbolicDatum)
    (symbolicLocGeometricFramedPeriodFunctoriality data.canonicalRawPayloadSource)
    (symbolicLocGeometricComparisonNaturality data.canonicalRawPayloadSource)
    (fun idx =>
      match idx with
      | .ambient => data.symbolicDatum.ambientObjectData
      | .open => data.symbolicDatum.openObjectData
      | .closed => data.symbolicDatum.closedObjectData)
    (by intro idx; cases idx <;> rfl)
    data.ProbeIndex
    data.geometricFramedPeriodData
    (symbolicA1GeometricToConcreteFramed data.geometricFramedPeriodData)
    (tautologicalBasisFreePeriodMapEquality ctx structuredEq)
    data.probeExtensionality
    (symbolicA1PackedReconstruction structuredEq)

def ofSymbolicLocRawFramedPeriodPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (payload : SymbolicLocRawFramedPeriodPayload structuredEq) :
    GeometricRealizationTomographySoundness ctx structuredEq :=
  ofSymbolicLocFramedData (symbolicLocFramedPeriodDatumOfRawPayload payload)

def ofSymbolicLocCanonicalSource
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {datum : SymbolicLocDatum ctx}
    (source : SymbolicLocCanonicalRawPayloadSource datum)
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (ProbeIndex := SymbolicLocCanonicalProbe)
          (symbolicLocCanonicalConcreteFramedDatum source)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq)) :
    GeometricRealizationTomographySoundness ctx structuredEq :=
  ofSymbolicLocRawFramedPeriodPayload
    (symbolicLocRawFramedPeriodPayloadOfCanonicalSource source probeExtensionality)

structure SymbolicLocCanonicalFramedFamilyPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx)
    {datum : SymbolicLocDatum ctx}
    (source : SymbolicLocCanonicalRawPayloadSource datum) where
  concreteFramedDatum :
    SymbolicLocCanonicalProbe → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx
  concreteFramedDatum_eq : concreteFramedDatum = symbolicLocCanonicalConcreteFramedDatum source
  framedFamily : FramedProbeFamily ctx
  framedFamily_eq : framedFamily = symbolicLocCanonicalFramedProbeFamily source
  scalarFamily : ScalarProbeFamily ctx
  scalarFamily_eq : scalarFamily = framedFamily.toScalarProbeFamily
  basisEq : BasisFreePeriodMapEquality ctx
  basisEq_eq : basisEq = tautologicalBasisFreePeriodMapEquality ctx structuredEq
  faithful : FaithfulFramedProbeTarget ctx framedFamily structuredEq
  probeExtensionality : ProbeExtensionalityForBasisFreePeriodMap ctx scalarFamily basisEq
  canonicalProbeExtensionality :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily
        (ProbeIndex := SymbolicLocCanonicalProbe)
        (symbolicLocCanonicalConcreteFramedDatum source)).toScalarProbeFamily
      (tautologicalBasisFreePeriodMapEquality ctx structuredEq)

namespace SymbolicLocCanonicalFramedFamilyPackage

def ofFaithfulFramedProbes
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {datum : SymbolicLocDatum ctx}
    (source : SymbolicLocCanonicalRawPayloadSource datum)
    (faithful :
      FaithfulFramedProbeTarget
        ctx
        (symbolicLocCanonicalFramedProbeFamily source)
        structuredEq) :
    SymbolicLocCanonicalFramedFamilyPackage structuredEq source := by
  let concreteFramedDatum := symbolicLocCanonicalConcreteFramedDatum source
  let framedFamily := symbolicLocCanonicalFramedProbeFamily source
  let scalarFamily := framedFamily.toScalarProbeFamily
  let basisEq := tautologicalBasisFreePeriodMapEquality ctx structuredEq
  refine
    { concreteFramedDatum := concreteFramedDatum
      concreteFramedDatum_eq := rfl
      framedFamily := framedFamily
      framedFamily_eq := rfl
      scalarFamily := scalarFamily
      scalarFamily_eq := rfl
      basisEq := basisEq
      basisEq_eq := rfl
      faithful := ?_
      probeExtensionality := ?_
      canonicalProbeExtensionality := ?_ }
  · exact faithful
  · simpa [symbolicLocCanonicalFramedProbeFamily] using
      (symbolicLocProbeExtensionalityOfFaithfulFramedProbes
        (ctx := ctx)
        (structuredEq := structuredEq)
        source
        faithful)
  · exact symbolicLocProbeExtensionalityOfFaithfulFramedProbes
      (ctx := ctx)
      (structuredEq := structuredEq)
      source
      faithful

end SymbolicLocCanonicalFramedFamilyPackage

structure SymbolicLocCanonicalTomographyPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx)
    {datum : SymbolicLocDatum ctx}
    (source : SymbolicLocCanonicalRawPayloadSource datum) where
  familyPackage : SymbolicLocCanonicalFramedFamilyPackage structuredEq source
  rawPayload : SymbolicLocRawFramedPeriodPayload structuredEq
  framedDatum : SymbolicLocFramedPeriodDatum structuredEq
  localizationConeNaturalityData :
    LocalizationConeNaturalityData
      (symbolicLocRealizationFunctorData datum)
      SymbolicLocCanonicalProbe
      (fun _ => SymbolicLocObjectSlot.ambient)
      (fun _ => SymbolicLocObjectSlot.open)
      (fun _ => SymbolicLocObjectSlot.closed)
  tomography : GeometricRealizationTomographySoundness ctx structuredEq

namespace SymbolicLocCanonicalTomographyPackage

def ofFaithfulFramedProbes
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {datum : SymbolicLocDatum ctx}
    (source : SymbolicLocCanonicalRawPayloadSource datum)
    (faithful :
      FaithfulFramedProbeTarget
        ctx
        (symbolicLocCanonicalFramedProbeFamily source)
        structuredEq) :
    SymbolicLocCanonicalTomographyPackage structuredEq source := by
  let familyPackage :=
    SymbolicLocCanonicalFramedFamilyPackage.ofFaithfulFramedProbes
      (structuredEq := structuredEq)
      source
      faithful
  refine
    { familyPackage := familyPackage
      rawPayload := symbolicLocRawFramedPeriodPayloadOfCanonicalSource
        source
        familyPackage.canonicalProbeExtensionality
      framedDatum := symbolicLocFramedPeriodDatumOfCanonicalSource
        source
        familyPackage.canonicalProbeExtensionality
      localizationConeNaturalityData := source.localizationConeNaturalityData
      tomography := GeometricRealizationTomographySoundness.ofSymbolicLocCanonicalSource
        (structuredEq := structuredEq)
        source
        familyPackage.canonicalProbeExtensionality }

end SymbolicLocCanonicalTomographyPackage

def symbolicNisGeometricFramedPeriodFunctoriality
    {ctx : ClassicalComparisonContext.{u, v}}
    {datum : SymbolicNisDatum ctx}
  (_source : SymbolicNisCanonicalRawPayloadSource datum) :
    GeometricFramedPeriodFunctoriality ctx (symbolicNisRealizationFunctorData datum) where
  sourceFraming := fun corr => nomatch corr
  targetFraming := fun corr => nomatch corr
  theoremTarget := by
    intro corr
    nomatch corr
  framedPeriodFunctorialityTarget :=
    datum.baseObjectData.comparisonData.grothendieckComparisonTarget ∧
      datum.patchObjectData.comparisonData.grothendieckComparisonTarget ∧
      datum.overlapObjectData.comparisonData.grothendieckComparisonTarget
  framedExtractionCompatibilityTarget :=
    datum.baseObjectData.comparisonData.periodCompatibilityTarget ∧
      datum.patchObjectData.comparisonData.periodCompatibilityTarget ∧
      datum.overlapObjectData.comparisonData.periodCompatibilityTarget

def symbolicNisGeometricComparisonNaturality
    {ctx : ClassicalComparisonContext.{u, v}}
    {datum : SymbolicNisDatum ctx}
  (_source : SymbolicNisCanonicalRawPayloadSource datum) :
    GeometricComparisonNaturality ctx (symbolicNisRealizationFunctorData datum) where
  theoremTarget := by
    intro corr
    nomatch corr
  baseChangeNaturalityTarget :=
    datum.baseObjectData.comparisonData.comparison.comparisonNaturalityTarget ∧
      datum.patchObjectData.comparisonData.comparison.comparisonNaturalityTarget ∧
      datum.overlapObjectData.comparisonData.comparison.comparisonNaturalityTarget

def ofSymbolicNisFramedData
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicNisFramedPeriodDatum structuredEq) :
    GeometricRealizationTomographySoundness ctx structuredEq :=
  ofFunctorialityAndFramedData
    (symbolicNisRealizationFunctorData data.symbolicDatum)
    (symbolicNisGeometricFramedPeriodFunctoriality data.canonicalRawPayloadSource)
    (symbolicNisGeometricComparisonNaturality data.canonicalRawPayloadSource)
    (fun idx =>
      match idx with
      | .base => data.symbolicDatum.baseObjectData
      | .patch => data.symbolicDatum.patchObjectData
      | .overlap => data.symbolicDatum.overlapObjectData)
    (by intro idx; cases idx <;> rfl)
    data.ProbeIndex
    data.geometricFramedPeriodData
    (symbolicA1GeometricToConcreteFramed data.geometricFramedPeriodData)
    (tautologicalBasisFreePeriodMapEquality ctx structuredEq)
    data.probeExtensionality
    (symbolicA1PackedReconstruction structuredEq)

def ofSymbolicNisRawFramedPeriodPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (payload : SymbolicNisRawFramedPeriodPayload structuredEq) :
    GeometricRealizationTomographySoundness ctx structuredEq :=
  ofSymbolicNisFramedData (symbolicNisFramedPeriodDatumOfRawPayload payload)

def ofSymbolicNisCanonicalSource
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {datum : SymbolicNisDatum ctx}
    (source : SymbolicNisCanonicalRawPayloadSource datum)
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (ProbeIndex := SymbolicNisCanonicalProbe)
          (symbolicNisCanonicalConcreteFramedDatum source)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq)) :
    GeometricRealizationTomographySoundness ctx structuredEq :=
  ofSymbolicNisRawFramedPeriodPayload
    (symbolicNisRawFramedPeriodPayloadOfCanonicalSource source probeExtensionality)

structure SymbolicNisCanonicalFramedFamilyPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx)
    {datum : SymbolicNisDatum ctx}
    (source : SymbolicNisCanonicalRawPayloadSource datum) where
  concreteFramedDatum :
    SymbolicNisCanonicalProbe → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx
  concreteFramedDatum_eq : concreteFramedDatum = symbolicNisCanonicalConcreteFramedDatum source
  framedFamily : FramedProbeFamily ctx
  framedFamily_eq : framedFamily = symbolicNisCanonicalFramedProbeFamily source
  scalarFamily : ScalarProbeFamily ctx
  scalarFamily_eq : scalarFamily = framedFamily.toScalarProbeFamily
  basisEq : BasisFreePeriodMapEquality ctx
  basisEq_eq : basisEq = tautologicalBasisFreePeriodMapEquality ctx structuredEq
  faithful : FaithfulFramedProbeTarget ctx framedFamily structuredEq
  probeExtensionality : ProbeExtensionalityForBasisFreePeriodMap ctx scalarFamily basisEq
  canonicalProbeExtensionality :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily
        (ProbeIndex := SymbolicNisCanonicalProbe)
        (symbolicNisCanonicalConcreteFramedDatum source)).toScalarProbeFamily
      (tautologicalBasisFreePeriodMapEquality ctx structuredEq)

namespace SymbolicNisCanonicalFramedFamilyPackage

def ofFaithfulFramedProbes
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {datum : SymbolicNisDatum ctx}
    (source : SymbolicNisCanonicalRawPayloadSource datum)
    (faithful :
      FaithfulFramedProbeTarget
        ctx
        (symbolicNisCanonicalFramedProbeFamily source)
        structuredEq) :
    SymbolicNisCanonicalFramedFamilyPackage structuredEq source := by
  let concreteFramedDatum := symbolicNisCanonicalConcreteFramedDatum source
  let framedFamily := symbolicNisCanonicalFramedProbeFamily source
  let scalarFamily := framedFamily.toScalarProbeFamily
  let basisEq := tautologicalBasisFreePeriodMapEquality ctx structuredEq
  refine
    { concreteFramedDatum := concreteFramedDatum
      concreteFramedDatum_eq := rfl
      framedFamily := framedFamily
      framedFamily_eq := rfl
      scalarFamily := scalarFamily
      scalarFamily_eq := rfl
      basisEq := basisEq
      basisEq_eq := rfl
      faithful := ?_
      probeExtensionality := ?_
      canonicalProbeExtensionality := ?_ }
  · exact faithful
  · simpa [symbolicNisCanonicalFramedProbeFamily] using
      (symbolicNisProbeExtensionalityOfFaithfulFramedProbes
        (ctx := ctx)
        (structuredEq := structuredEq)
        source
        faithful)
  · exact symbolicNisProbeExtensionalityOfFaithfulFramedProbes
      (ctx := ctx)
      (structuredEq := structuredEq)
      source
      faithful

end SymbolicNisCanonicalFramedFamilyPackage

structure SymbolicNisCanonicalTomographyPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx)
    {datum : SymbolicNisDatum ctx}
    (source : SymbolicNisCanonicalRawPayloadSource datum) where
  familyPackage : SymbolicNisCanonicalFramedFamilyPackage structuredEq source
  rawPayload : SymbolicNisRawFramedPeriodPayload structuredEq
  framedDatum : SymbolicNisFramedPeriodDatum structuredEq
  traceNativePatchReplayData :
    CertifiedNisPatchReplayData ctx
      (∀ _ : SymbolicNisCanonicalProbe,
        datum.baseObjectData.comparisonData.grothendieckComparisonTarget ∧
          datum.patchObjectData.comparisonData.grothendieckComparisonTarget ∧
          datum.overlapObjectData.comparisonData.grothendieckComparisonTarget)
      datum.overlapObjectData.comparisonData.grothendieckComparisonTarget
  tomography : GeometricRealizationTomographySoundness ctx structuredEq

namespace SymbolicNisCanonicalTomographyPackage

def ofFaithfulFramedProbes
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {datum : SymbolicNisDatum ctx}
    (source : SymbolicNisCanonicalRawPayloadSource datum)
    (faithful :
      FaithfulFramedProbeTarget
        ctx
        (symbolicNisCanonicalFramedProbeFamily source)
        structuredEq) :
    SymbolicNisCanonicalTomographyPackage structuredEq source := by
  let familyPackage :=
    SymbolicNisCanonicalFramedFamilyPackage.ofFaithfulFramedProbes
      (structuredEq := structuredEq)
      source
      faithful
  refine
    { familyPackage := familyPackage
      rawPayload := symbolicNisRawFramedPeriodPayloadOfCanonicalSource
        source
        familyPackage.canonicalProbeExtensionality
      framedDatum := symbolicNisFramedPeriodDatumOfCanonicalSource
        source
        familyPackage.canonicalProbeExtensionality
      traceNativePatchReplayData := source.traceNativePatchReplayData
      tomography := GeometricRealizationTomographySoundness.ofSymbolicNisCanonicalSource
        (structuredEq := structuredEq)
        source
        familyPackage.canonicalProbeExtensionality }

end SymbolicNisCanonicalTomographyPackage

def symbolicEnvGeometricFramedPeriodFunctoriality
    {ctx : ClassicalComparisonContext.{u, v}}
    {datum : SymbolicEnvDatum ctx}
    (_source : SymbolicEnvCanonicalRawPayloadSource datum) :
    GeometricFramedPeriodFunctoriality ctx (symbolicEnvRealizationFunctorData datum) where
  sourceFraming := fun corr => nomatch corr
  targetFraming := fun corr => nomatch corr
  theoremTarget := by
    intro corr
    nomatch corr
  framedPeriodFunctorialityTarget :=
    datum.envelopeCorrespondence.correspondenceTarget ∧
      datum.ambientObjectData.comparisonData.grothendieckComparisonTarget ∧
      datum.envelopeObjectData.comparisonData.grothendieckComparisonTarget
  framedExtractionCompatibilityTarget :=
    datum.ambientObjectData.comparisonData.periodCompatibilityTarget ∧
      datum.envelopeObjectData.comparisonData.periodCompatibilityTarget

def symbolicEnvGeometricComparisonNaturality
    {ctx : ClassicalComparisonContext.{u, v}}
    {datum : SymbolicEnvDatum ctx}
    (_source : SymbolicEnvCanonicalRawPayloadSource datum) :
    GeometricComparisonNaturality ctx (symbolicEnvRealizationFunctorData datum) where
  theoremTarget := by
    intro corr
    nomatch corr
  baseChangeNaturalityTarget :=
    datum.ambientObjectData.comparisonData.comparison.comparisonNaturalityTarget ∧
      datum.envelopeObjectData.comparisonData.comparison.comparisonNaturalityTarget

def ofSymbolicEnvFramedData
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicEnvFramedPeriodDatum structuredEq) :
    GeometricRealizationTomographySoundness ctx structuredEq :=
  ofFunctorialityAndFramedData
    (symbolicEnvRealizationFunctorData data.symbolicDatum)
    (symbolicEnvGeometricFramedPeriodFunctoriality data.canonicalRawPayloadSource)
    (symbolicEnvGeometricComparisonNaturality data.canonicalRawPayloadSource)
    (fun idx =>
      match idx with
      | .ambient => data.symbolicDatum.ambientObjectData
      | .envelope => data.symbolicDatum.envelopeObjectData)
    (by intro idx; cases idx <;> rfl)
    data.ProbeIndex
    data.geometricFramedPeriodData
    (symbolicA1GeometricToConcreteFramed data.geometricFramedPeriodData)
    (tautologicalBasisFreePeriodMapEquality ctx structuredEq)
    data.probeExtensionality
    (symbolicA1PackedReconstruction structuredEq)

def ofSymbolicEnvRawFramedPeriodPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (payload : SymbolicEnvRawFramedPeriodPayload structuredEq) :
    GeometricRealizationTomographySoundness ctx structuredEq :=
  ofSymbolicEnvFramedData (symbolicEnvFramedPeriodDatumOfRawPayload payload)

def ofSymbolicEnvCanonicalSource
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {datum : SymbolicEnvDatum ctx}
    (source : SymbolicEnvCanonicalRawPayloadSource datum)
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (ProbeIndex := SymbolicEnvCanonicalProbe)
          (symbolicEnvCanonicalConcreteFramedDatum source)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq)) :
    GeometricRealizationTomographySoundness ctx structuredEq :=
  ofSymbolicEnvRawFramedPeriodPayload
    (symbolicEnvRawFramedPeriodPayloadOfCanonicalSource source probeExtensionality)

structure SymbolicEnvCanonicalFramedFamilyPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx)
    {datum : SymbolicEnvDatum ctx}
    (source : SymbolicEnvCanonicalRawPayloadSource datum) where
  concreteFramedDatum :
    SymbolicEnvCanonicalProbe → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx
  concreteFramedDatum_eq : concreteFramedDatum = symbolicEnvCanonicalConcreteFramedDatum source
  framedFamily : FramedProbeFamily ctx
  framedFamily_eq : framedFamily = symbolicEnvCanonicalFramedProbeFamily source
  scalarFamily : ScalarProbeFamily ctx
  scalarFamily_eq : scalarFamily = framedFamily.toScalarProbeFamily
  basisEq : BasisFreePeriodMapEquality ctx
  basisEq_eq : basisEq = tautologicalBasisFreePeriodMapEquality ctx structuredEq
  faithful : FaithfulFramedProbeTarget ctx framedFamily structuredEq
  probeExtensionality : ProbeExtensionalityForBasisFreePeriodMap ctx scalarFamily basisEq
  canonicalProbeExtensionality :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily
        (ProbeIndex := SymbolicEnvCanonicalProbe)
        (symbolicEnvCanonicalConcreteFramedDatum source)).toScalarProbeFamily
      (tautologicalBasisFreePeriodMapEquality ctx structuredEq)

namespace SymbolicEnvCanonicalFramedFamilyPackage

def ofFaithfulFramedProbes
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {datum : SymbolicEnvDatum ctx}
    (source : SymbolicEnvCanonicalRawPayloadSource datum)
    (faithful :
      FaithfulFramedProbeTarget
        ctx
        (symbolicEnvCanonicalFramedProbeFamily source)
        structuredEq) :
    SymbolicEnvCanonicalFramedFamilyPackage structuredEq source := by
  let concreteFramedDatum := symbolicEnvCanonicalConcreteFramedDatum source
  let framedFamily := symbolicEnvCanonicalFramedProbeFamily source
  let scalarFamily := framedFamily.toScalarProbeFamily
  let basisEq := tautologicalBasisFreePeriodMapEquality ctx structuredEq
  refine
    { concreteFramedDatum := concreteFramedDatum
      concreteFramedDatum_eq := rfl
      framedFamily := framedFamily
      framedFamily_eq := rfl
      scalarFamily := scalarFamily
      scalarFamily_eq := rfl
      basisEq := basisEq
      basisEq_eq := rfl
      faithful := ?_
      probeExtensionality := ?_
      canonicalProbeExtensionality := ?_ }
  · exact faithful
  · simpa [symbolicEnvCanonicalFramedProbeFamily] using
      (symbolicEnvProbeExtensionalityOfFaithfulFramedProbes
        (ctx := ctx)
        (structuredEq := structuredEq)
        source
        faithful)
  · exact symbolicEnvProbeExtensionalityOfFaithfulFramedProbes
      (ctx := ctx)
      (structuredEq := structuredEq)
      source
      faithful

end SymbolicEnvCanonicalFramedFamilyPackage

structure SymbolicEnvCanonicalTomographyPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx)
    {datum : SymbolicEnvDatum ctx}
    (source : SymbolicEnvCanonicalRawPayloadSource datum) where
  familyPackage : SymbolicEnvCanonicalFramedFamilyPackage structuredEq source
  rawPayload : SymbolicEnvRawFramedPeriodPayload structuredEq
  framedDatum : SymbolicEnvFramedPeriodDatum structuredEq
  traceNativeEnvReplayData :
    CertifiedEnvReplayData ctx
      (∀ _ : SymbolicEnvCanonicalProbe,
        datum.envelopeCorrespondence.correspondenceTarget ∧
          datum.ambientObjectData.comparisonData.grothendieckComparisonTarget ∧
          datum.envelopeObjectData.comparisonData.grothendieckComparisonTarget ∧
          datum.ambientObjectData.comparisonData.periodCompatibilityTarget ∧
          datum.envelopeObjectData.comparisonData.periodCompatibilityTarget)
      datum.envelopeObjectData.comparisonData.periodCompatibilityTarget
  tomography : GeometricRealizationTomographySoundness ctx structuredEq

namespace SymbolicEnvCanonicalTomographyPackage

def ofFaithfulFramedProbes
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {datum : SymbolicEnvDatum ctx}
    (source : SymbolicEnvCanonicalRawPayloadSource datum)
    (faithful :
      FaithfulFramedProbeTarget
        ctx
        (symbolicEnvCanonicalFramedProbeFamily source)
        structuredEq) :
    SymbolicEnvCanonicalTomographyPackage structuredEq source := by
  let familyPackage :=
    SymbolicEnvCanonicalFramedFamilyPackage.ofFaithfulFramedProbes
      (structuredEq := structuredEq)
      source
      faithful
  refine
    { familyPackage := familyPackage
      rawPayload := symbolicEnvRawFramedPeriodPayloadOfCanonicalSource
        source
        familyPackage.canonicalProbeExtensionality
      framedDatum := symbolicEnvFramedPeriodDatumOfCanonicalSource
        source
        familyPackage.canonicalProbeExtensionality
      traceNativeEnvReplayData := source.traceNativeEnvReplayData
      tomography := GeometricRealizationTomographySoundness.ofSymbolicEnvCanonicalSource
        (structuredEq := structuredEq)
        source
        familyPackage.canonicalProbeExtensionality }

end SymbolicEnvCanonicalTomographyPackage

def symbolicCorrGeometricFramedPeriodFunctoriality
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicCorrDatum ctx) :
    GeometricFramedPeriodFunctoriality ctx (symbolicCorrRealizationFunctorData datum) where
  sourceFraming := fun _ => symbolicPlaceholderFramedObject datum.source
  targetFraming := fun _ => symbolicPlaceholderFramedObject datum.target
  theoremTarget := by
    intro corrIdx
    cases corrIdx
    exact ⟨datum.canonicalRawPayloadSource.structuredMorphism,
      ⟨GeometricFramedPeriodData.ofRawPayload
        (symbolicCorrCanonicalGeometricRawPayload datum)⟩⟩
  framedPeriodFunctorialityTarget :=
    datum.sourceObjectData.comparisonData.grothendieckComparisonTarget ∧
      datum.targetObjectData.comparisonData.grothendieckComparisonTarget
  framedExtractionCompatibilityTarget :=
    datum.sourceObjectData.comparisonData.periodCompatibilityTarget ∧
      datum.targetObjectData.comparisonData.periodCompatibilityTarget

def symbolicCorrGeometricComparisonNaturality
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicCorrDatum ctx) :
    GeometricComparisonNaturality ctx (symbolicCorrRealizationFunctorData datum) where
  theoremTarget := by
    intro corrIdx
    cases corrIdx
    exact ⟨datum.canonicalRawPayloadSource.sourceComparisonNaturalityTarget,
      datum.canonicalRawPayloadSource.targetComparisonNaturalityTarget⟩
  baseChangeNaturalityTarget :=
    datum.sourceObjectData.comparisonData.comparison.comparisonNaturalityTarget ∧
      datum.targetObjectData.comparisonData.comparison.comparisonNaturalityTarget

def ofSymbolicCorrFramedData
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicCorrFramedPeriodDatum structuredEq) :
    GeometricRealizationTomographySoundness ctx structuredEq :=
  ofFunctorialityAndFramedData
    (symbolicCorrRealizationFunctorData data.symbolicDatum)
    (symbolicCorrGeometricFramedPeriodFunctoriality data.symbolicDatum)
    (symbolicCorrGeometricComparisonNaturality data.symbolicDatum)
    (fun idx =>
      match idx with
      | .source => data.symbolicDatum.sourceObjectData
      | .target => data.symbolicDatum.targetObjectData)
    (by intro idx; cases idx <;> rfl)
    data.ProbeIndex
    data.geometricFramedPeriodData
    (symbolicA1GeometricToConcreteFramed data.geometricFramedPeriodData)
    (tautologicalBasisFreePeriodMapEquality ctx structuredEq)
    data.probeExtensionality
    (symbolicA1PackedReconstruction structuredEq)

def ofSymbolicCorrRawFramedPeriodPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (payload : SymbolicCorrRawFramedPeriodPayload structuredEq) :
    GeometricRealizationTomographySoundness ctx structuredEq :=
  ofSymbolicCorrFramedData (symbolicCorrFramedPeriodDatumOfRawPayload payload)

def ofSymbolicCorrCanonicalSource
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (datum : SymbolicCorrDatum ctx)
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (ProbeIndex := SymbolicCorrCanonicalProbe)
          (symbolicCorrCanonicalConcreteFramedDatum datum)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq)) :
    GeometricRealizationTomographySoundness ctx structuredEq :=
  ofSymbolicCorrRawFramedPeriodPayload
    (symbolicCorrRawFramedPeriodPayloadOfCanonicalSource datum probeExtensionality)

structure SymbolicCorrCanonicalFramedFamilyPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx)
    (datum : SymbolicCorrDatum ctx) where
  concreteFramedDatum :
    SymbolicCorrCanonicalProbe → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx
  concreteFramedDatum_eq : concreteFramedDatum = symbolicCorrCanonicalConcreteFramedDatum datum
  framedFamily : FramedProbeFamily ctx
  framedFamily_eq : framedFamily = symbolicCorrCanonicalFramedProbeFamily datum
  scalarFamily : ScalarProbeFamily ctx
  scalarFamily_eq : scalarFamily = framedFamily.toScalarProbeFamily
  basisEq : BasisFreePeriodMapEquality ctx
  basisEq_eq : basisEq = tautologicalBasisFreePeriodMapEquality ctx structuredEq
  faithful : FaithfulFramedProbeTarget ctx framedFamily structuredEq
  probeExtensionality : ProbeExtensionalityForBasisFreePeriodMap ctx scalarFamily basisEq
  canonicalProbeExtensionality :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily
        (ProbeIndex := SymbolicCorrCanonicalProbe)
        (symbolicCorrCanonicalConcreteFramedDatum datum)).toScalarProbeFamily
      (tautologicalBasisFreePeriodMapEquality ctx structuredEq)

namespace SymbolicCorrCanonicalFramedFamilyPackage

def ofFaithfulFramedProbes
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (datum : SymbolicCorrDatum ctx)
    (faithful :
      FaithfulFramedProbeTarget
        ctx
        (symbolicCorrCanonicalFramedProbeFamily datum)
        structuredEq) :
    SymbolicCorrCanonicalFramedFamilyPackage structuredEq datum := by
  let concreteFramedDatum := symbolicCorrCanonicalConcreteFramedDatum datum
  let framedFamily := symbolicCorrCanonicalFramedProbeFamily datum
  let scalarFamily := framedFamily.toScalarProbeFamily
  let basisEq := tautologicalBasisFreePeriodMapEquality ctx structuredEq
  refine
    { concreteFramedDatum := concreteFramedDatum
      concreteFramedDatum_eq := rfl
      framedFamily := framedFamily
      framedFamily_eq := rfl
      scalarFamily := scalarFamily
      scalarFamily_eq := rfl
      basisEq := basisEq
      basisEq_eq := rfl
      faithful := ?_
      probeExtensionality := ?_
      canonicalProbeExtensionality := ?_ }
  · exact faithful
  · simpa [symbolicCorrCanonicalFramedProbeFamily] using
      (symbolicCorrProbeExtensionalityOfFaithfulFramedProbes
        (ctx := ctx)
        (structuredEq := structuredEq)
        datum
        faithful)
  · exact symbolicCorrProbeExtensionalityOfFaithfulFramedProbes
      (ctx := ctx)
      (structuredEq := structuredEq)
      datum
      faithful

end SymbolicCorrCanonicalFramedFamilyPackage

structure SymbolicCorrCanonicalTomographyPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx)
    (datum : SymbolicCorrDatum ctx) where
  familyPackage : SymbolicCorrCanonicalFramedFamilyPackage structuredEq datum
  rawPayload : SymbolicCorrRawFramedPeriodPayload structuredEq
  framedDatum : SymbolicCorrFramedPeriodDatum structuredEq
  tomography : GeometricRealizationTomographySoundness ctx structuredEq

namespace SymbolicCorrCanonicalTomographyPackage

def ofFaithfulFramedProbes
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (datum : SymbolicCorrDatum ctx)
    (faithful :
      FaithfulFramedProbeTarget
        ctx
        (symbolicCorrCanonicalFramedProbeFamily datum)
        structuredEq) :
    SymbolicCorrCanonicalTomographyPackage structuredEq datum := by
  let familyPackage :=
    SymbolicCorrCanonicalFramedFamilyPackage.ofFaithfulFramedProbes
      (structuredEq := structuredEq)
      datum
      faithful
  refine
    { familyPackage := familyPackage
      rawPayload := symbolicCorrRawFramedPeriodPayloadOfCanonicalSource
        datum
        familyPackage.canonicalProbeExtensionality
      framedDatum := symbolicCorrFramedPeriodDatumOfCanonicalSource
        datum
        familyPackage.canonicalProbeExtensionality
      tomography := GeometricRealizationTomographySoundness.ofSymbolicCorrCanonicalSource
        (structuredEq := structuredEq)
        datum
        familyPackage.canonicalProbeExtensionality }

end SymbolicCorrCanonicalTomographyPackage

/-- Assemble a tomography package from the symbolic `A1` realization data plus the genuinely
missing tomography witnesses. This isolates exactly what the current symbolic example already
supplies and leaves the geometric framed-datum layer explicit. -/
def ofSymbolicA1Data
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (datum : SymbolicA1Datum ctx)
  (ProbeIndex : Type _)
    (geometricFramedDatum :
      ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeGeometricFramedPeriodData ctx)
    (geometricToConcreteFramed :
      GeometricPeriodsRealizeConcreteFramedData ctx geometricFramedDatum)
    (basisFreePeriodMapEquality : BasisFreePeriodMapEquality ctx)
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (fun probe morphism =>
            (geometricFramedDatum probe morphism).toSomeConcreteFramedPeriodData)).toScalarProbeFamily
        basisFreePeriodMapEquality)
    (packedReconstruction :
      BasisFreePeriodMapDeterminesPackedComparison
        ctx
        basisFreePeriodMapEquality
        structuredEq) :
    GeometricRealizationTomographySoundness ctx structuredEq :=
  ofFunctorialityAndFramedData
    (symbolicA1RealizationFunctorData datum)
    (symbolicA1GeometricFramedPeriodFunctoriality datum)
    (symbolicA1GeometricComparisonNaturality datum)
    (symbolicA1GeometricObjectData datum)
    (symbolicA1GeometricObjectData_compatibilityTarget datum)
    ProbeIndex
    geometricFramedDatum
    geometricToConcreteFramed
    basisFreePeriodMapEquality
    probeExtensionality
    packedReconstruction

/-- Assemble the actual symbolic `A1` tomography package from the explicit proof-relevant framed
period layer. The old bare `SymbolicA1Datum` contributes only realization/object data; the framed
datum carries the missing probe-relevant period payload. -/
def ofSymbolicA1FramedData
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (data : SymbolicA1FramedPeriodDatum structuredEq) :
    GeometricRealizationTomographySoundness ctx structuredEq :=
  ofFunctorialityAndFramedData
    (symbolicA1RealizationFunctorData data.symbolicDatum)
    (symbolicA1GeometricFramedPeriodFunctoriality data.symbolicDatum)
    (symbolicA1GeometricComparisonNaturality data.symbolicDatum)
    (symbolicA1GeometricObjectData data.symbolicDatum)
    (symbolicA1GeometricObjectData_compatibilityTarget data.symbolicDatum)
    (symbolicA1ProbeIndex data)
    (symbolicA1GeometricFramedDatum data)
    (symbolicA1GeometricToConcreteFramed (symbolicA1GeometricFramedDatum data))
    (symbolicA1BasisFreePeriodMapEquality structuredEq)
    (symbolicA1ProbeExtensionality data)
    (symbolicA1PackedReconstruction structuredEq)

/-- Compose the raw symbolic `A1` framed-period payload directly into the existing tomography
constructor. -/
def ofSymbolicA1RawFramedPeriodPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (payload : SymbolicA1RawFramedPeriodPayload structuredEq) :
    GeometricRealizationTomographySoundness ctx structuredEq :=
  ofSymbolicA1FramedData (symbolicA1FramedPeriodDatumOfRawPayload payload)

/-- Compose an `A1` projection/section preservation certificate family directly into the
symbolic `A1` tomography package. -/
def ofSymbolicA1Preservation
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (symbolicDatum : SymbolicA1Datum ctx)
    (ProbeIndex : Type w)
    (sourceObjectData :
      ProbeIndex → SomeStructuredComparisonMorphism ctx → GeometricComparisonObjectData ctx)
    (targetObjectData :
      ProbeIndex → SomeStructuredComparisonMorphism ctx → GeometricComparisonObjectData ctx)
    (structuredMorphism :
      (probe : ProbeIndex) →
        (morphism : SomeStructuredComparisonMorphism ctx) →
          ClassicalStructuredComparisonMorphism
            (sourceObjectData probe morphism).toStructuredComparisonObject
            (targetObjectData probe morphism).toStructuredComparisonObject)
    (preservation :
      (probe : ProbeIndex) →
        (morphism : SomeStructuredComparisonMorphism ctx) →
          A1PeriodPreservationCertificate
            (sourceObjectData probe morphism)
            (targetObjectData probe morphism)
            (structuredMorphism probe morphism))
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (fun probe morphism =>
            (SomeGeometricFramedPeriodData.ofRawPayload
              (sourceObjectData probe morphism)
              (targetObjectData probe morphism)
              (structuredMorphism probe morphism)
              (GeometricFramedPeriodRawPayload.ofA1Preservation
                (preservation probe morphism))).toSomeConcreteFramedPeriodData)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq)) :
    GeometricRealizationTomographySoundness ctx structuredEq :=
  ofSymbolicA1FramedData
    (symbolicA1FramedPeriodDatumOfA1Preservation
      symbolicDatum
      ProbeIndex
      sourceObjectData
      targetObjectData
      structuredMorphism
      preservation
      probeExtensionality)

/-- Lower-level canonical symbolic `A1` tomography constructor from an explicit extensionality
witness. Prefer `SymbolicA1CanonicalTomographyPackage.ofFaithfulFramedProbes` when faithful framed
probes are available. -/
def ofSymbolicA1CanonicalSource
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (datum : SymbolicA1Datum ctx)
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (concreteFramedProbeFamily
          (ProbeIndex := SymbolicA1CanonicalProbe)
          (symbolicA1CanonicalConcreteFramedDatum datum)).toScalarProbeFamily
        (tautologicalBasisFreePeriodMapEquality ctx structuredEq)) :
    GeometricRealizationTomographySoundness ctx structuredEq :=
  ofSymbolicA1RawFramedPeriodPayload
    (symbolicA1RawFramedPeriodPayloadOfCanonicalSource datum probeExtensionality)

/-- Preferred symbolic `A1` family package for the faithful-probe route.

It names the canonical framed family, its scalar shadow family, the tautological basis equality,
and the derived probe-extensionality witness once so downstream code can reuse projections. -/
structure SymbolicA1CanonicalFramedFamilyPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx)
    (datum : SymbolicA1Datum ctx) where
  concreteFramedDatum :
    SymbolicA1CanonicalProbe → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx
  concreteFramedDatum_eq : concreteFramedDatum = symbolicA1CanonicalConcreteFramedDatum datum
  framedFamily : FramedProbeFamily ctx
  framedFamily_eq : framedFamily = symbolicA1CanonicalFramedProbeFamily datum
  scalarFamily : ScalarProbeFamily ctx
  scalarFamily_eq : scalarFamily = framedFamily.toScalarProbeFamily
  basisEq : BasisFreePeriodMapEquality ctx
  basisEq_eq : basisEq = tautologicalBasisFreePeriodMapEquality ctx structuredEq
  faithful : FaithfulFramedProbeTarget ctx framedFamily structuredEq
  probeExtensionality : ProbeExtensionalityForBasisFreePeriodMap ctx scalarFamily basisEq
  canonicalProbeExtensionality :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily
        (ProbeIndex := SymbolicA1CanonicalProbe)
        (symbolicA1CanonicalConcreteFramedDatum datum)).toScalarProbeFamily
      (tautologicalBasisFreePeriodMapEquality ctx structuredEq)

namespace SymbolicA1CanonicalFramedFamilyPackage

/-- Build the preferred canonical symbolic `A1` family package from faithful framed probes.

This packages the derived extensionality witness without requiring downstream code to restate the
canonical family expression. -/
def ofFaithfulFramedProbes
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (datum : SymbolicA1Datum ctx)
    (faithful :
      FaithfulFramedProbeTarget
        ctx
        (symbolicA1CanonicalFramedProbeFamily datum)
        structuredEq) :
    SymbolicA1CanonicalFramedFamilyPackage structuredEq datum := by
  let concreteFramedDatum := symbolicA1CanonicalConcreteFramedDatum datum
  let framedFamily := symbolicA1CanonicalFramedProbeFamily datum
  let scalarFamily := framedFamily.toScalarProbeFamily
  let basisEq := tautologicalBasisFreePeriodMapEquality ctx structuredEq
  refine
    { concreteFramedDatum := concreteFramedDatum
      concreteFramedDatum_eq := rfl
      framedFamily := framedFamily
      framedFamily_eq := rfl
      scalarFamily := scalarFamily
      scalarFamily_eq := rfl
      basisEq := basisEq
      basisEq_eq := rfl
      faithful := ?_
      probeExtensionality := ?_
      canonicalProbeExtensionality := ?_ }
  · exact faithful
  · simpa [symbolicA1CanonicalFramedProbeFamily] using
      (symbolicA1ProbeExtensionalityOfFaithfulFramedProbes
        (ctx := ctx)
        (structuredEq := structuredEq)
        datum
        faithful)
  · exact symbolicA1ProbeExtensionalityOfFaithfulFramedProbes
      (ctx := ctx)
      (structuredEq := structuredEq)
      datum
      faithful

end SymbolicA1CanonicalFramedFamilyPackage

/-- Preferred symbolic `A1` tomography package for the faithful-probe route.

This extends the canonical family package with the raw payload, framed datum, and tomography
result so downstream code can consume projections such as `pkg.tomography`. -/
structure SymbolicA1CanonicalTomographyPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx)
    (datum : SymbolicA1Datum ctx) where
  familyPackage : SymbolicA1CanonicalFramedFamilyPackage structuredEq datum
  rawPayload : SymbolicA1RawFramedPeriodPayload structuredEq
  framedDatum : SymbolicA1FramedPeriodDatum structuredEq
  tomography : GeometricRealizationTomographySoundness ctx structuredEq

namespace SymbolicA1CanonicalTomographyPackage

/-- Build the preferred symbolic `A1` tomography package from faithful framed probes. -/
def ofFaithfulFramedProbes
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (datum : SymbolicA1Datum ctx)
    (faithful :
      FaithfulFramedProbeTarget
        ctx
        (symbolicA1CanonicalFramedProbeFamily datum)
        structuredEq) :
    SymbolicA1CanonicalTomographyPackage structuredEq datum := by
  let familyPackage :=
    SymbolicA1CanonicalFramedFamilyPackage.ofFaithfulFramedProbes
      (structuredEq := structuredEq)
      datum
      faithful
  refine
    { familyPackage := familyPackage
      rawPayload := symbolicA1RawFramedPeriodPayloadOfCanonicalSource
        datum
        familyPackage.canonicalProbeExtensionality
      framedDatum := symbolicA1FramedPeriodDatumOfCanonicalSource
        datum
        familyPackage.canonicalProbeExtensionality
      tomography := GeometricRealizationTomographySoundness.ofSymbolicA1CanonicalSource
        (structuredEq := structuredEq)
        datum
        familyPackage.canonicalProbeExtensionality }

end SymbolicA1CanonicalTomographyPackage

end GeometricRealizationTomographySoundness

structure PrimitiveFamilyPeriodTomographyPartialTable
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx) where
  CorrDatum : Type w
  LocDatum : Type x
  NisDatum : Type y
  A1Datum : Type z
  corrDatum : CorrDatum → SymbolicCorrDatum ctx
  locDatum : LocDatum → SymbolicLocDatum ctx
  nisDatum : NisDatum → SymbolicNisDatum ctx
  a1Datum : A1Datum → SymbolicA1Datum ctx
  corrPackage :
    (idx : CorrDatum) →
      GeometricRealizationTomographySoundness.SymbolicCorrCanonicalTomographyPackage
        structuredEq (corrDatum idx)
  locRawPayloadSource :
    (idx : LocDatum) → SymbolicLocCanonicalRawPayloadSource (locDatum idx)
  locPackage :
    (idx : LocDatum) →
      GeometricRealizationTomographySoundness.SymbolicLocCanonicalTomographyPackage
        structuredEq (locRawPayloadSource idx)
  nisCanonicalPackageTarget : Prop
  nisCanonicalPackageTarget_holds : nisCanonicalPackageTarget
  a1Package :
    (idx : A1Datum) →
      GeometricRealizationTomographySoundness.SymbolicA1CanonicalTomographyPackage
        structuredEq (a1Datum idx)

structure PrimitiveFamilyPeriodTomographyTableShape
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx) where
  CorrDatum : Type w
  LocDatum : Type x
  NisDatum : Type y
  A1Datum : Type z
  EnvDatum : Type (max u v w x y z)
  corrDatum : CorrDatum → SymbolicCorrDatum ctx
  locDatum : LocDatum → SymbolicLocDatum ctx
  nisDatum : NisDatum → SymbolicNisDatum ctx
  a1Datum : A1Datum → SymbolicA1Datum ctx
  envDatum : EnvDatum → SymbolicEnvDatum ctx
  corrPackage :
    (idx : CorrDatum) →
      GeometricRealizationTomographySoundness.SymbolicCorrCanonicalTomographyPackage
        structuredEq (corrDatum idx)
  a1Package :
    (idx : A1Datum) →
      GeometricRealizationTomographySoundness.SymbolicA1CanonicalTomographyPackage
        structuredEq (a1Datum idx)
  locPackageTarget : Prop
  nisPackageTarget : Prop
  envPackageTarget : Prop

structure PrimitiveFamilyPeriodTomographyTable
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx) where
  CorrDatum : Type w
  LocDatum : Type x
  NisDatum : Type y
  A1Datum : Type z
  EnvDatum : Type (max u v w x y z)
  corrDatum : CorrDatum → SymbolicCorrDatum ctx
  locDatum : LocDatum → SymbolicLocDatum ctx
  nisDatum : NisDatum → SymbolicNisDatum ctx
  a1Datum : A1Datum → SymbolicA1Datum ctx
  envDatum : EnvDatum → SymbolicEnvDatum ctx
  corrPackage :
    (idx : CorrDatum) →
      GeometricRealizationTomographySoundness.SymbolicCorrCanonicalTomographyPackage
        structuredEq (corrDatum idx)
  locCanonicalPackageTarget : Prop
  locCanonicalPackageTarget_holds : locCanonicalPackageTarget
  nisCanonicalPackageTarget : Prop
  nisCanonicalPackageTarget_holds : nisCanonicalPackageTarget
  a1Package :
    (idx : A1Datum) →
      GeometricRealizationTomographySoundness.SymbolicA1CanonicalTomographyPackage
        structuredEq (a1Datum idx)
  envCanonicalPackageTarget : Prop
  envCanonicalPackageTarget_holds : envCanonicalPackageTarget

structure CertifiedTracePeriodTomographyTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx)
    (primitiveTable : PrimitiveFamilyPeriodTomographyTable structuredEq)
    (TraceInput : Type w) where
  traceInput : TraceInput
  primitiveTomographyTarget : Prop
  primitiveTomography_holds : primitiveTomographyTarget
  traceSoundnessTarget : Prop
  traceSoundness_holds : traceSoundnessTarget
  replayOrderCompatibilityTarget : Prop
  packetCutCompatibilityTarget : Prop
  canNFNormalizationCompatibilityTarget : Prop
  boundaryReconstructionCompatibilityTarget : Prop
  coherenceWitnessCompatibilityTarget : Prop
  closureTransportTarget : Prop
  closureTransport_holds : closureTransportTarget
  structuredComparisonEquality : StructuredComparisonEquality ctx
  structuredComparisonEquality_eq : structuredComparisonEquality = structuredEq
  tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq

namespace CertifiedTracePeriodTomographyTarget

def fromClosureTransport
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (primitiveTable : PrimitiveFamilyPeriodTomographyTable structuredEq)
    (TraceInput : Type w)
    (traceInput : TraceInput)
    (primitiveTomographyTarget : Prop)
    (primitiveTomography_holds : primitiveTomographyTarget)
    (traceSoundnessTarget : Prop)
    (traceSoundness_holds : traceSoundnessTarget)
    (replayOrderCompatibilityTarget packetCutCompatibilityTarget
      canNFNormalizationCompatibilityTarget boundaryReconstructionCompatibilityTarget
      coherenceWitnessCompatibilityTarget closureTransportTarget : Prop)
    (closureTransport_holds : closureTransportTarget)
    (tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq) :
    CertifiedTracePeriodTomographyTarget structuredEq primitiveTable TraceInput where
  traceInput := traceInput
  primitiveTomographyTarget := primitiveTomographyTarget
  primitiveTomography_holds := primitiveTomography_holds
  traceSoundnessTarget := traceSoundnessTarget
  traceSoundness_holds := traceSoundness_holds
  replayOrderCompatibilityTarget := replayOrderCompatibilityTarget
  packetCutCompatibilityTarget := packetCutCompatibilityTarget
  canNFNormalizationCompatibilityTarget := canNFNormalizationCompatibilityTarget
  boundaryReconstructionCompatibilityTarget := boundaryReconstructionCompatibilityTarget
  coherenceWitnessCompatibilityTarget := coherenceWitnessCompatibilityTarget
  closureTransportTarget := closureTransportTarget
  closureTransport_holds := closureTransport_holds
  structuredComparisonEquality := structuredEq
  structuredComparisonEquality_eq := rfl
  tomographySoundness := tomographySoundness

end CertifiedTracePeriodTomographyTarget

structure TracePeriodTomographyFromPrimitiveFamilies
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx) where
  primitiveTable : PrimitiveFamilyPeriodTomographyTable structuredEq
  TraceInput : Type w
  traceInput : TraceInput
  primitiveTomographyTarget : Prop
  primitiveTomography_holds : primitiveTomographyTarget
  traceSoundnessTarget : Prop
  traceSoundness_holds : traceSoundnessTarget
  replayOrderCompatibilityTarget : Prop
  packetCutCompatibilityTarget : Prop
  canNFNormalizationCompatibilityTarget : Prop
  boundaryReconstructionCompatibilityTarget : Prop
  coherenceWitnessCompatibilityTarget : Prop
  closureTransportTarget : Prop
  closureTransport_holds : closureTransportTarget
  structuredComparisonEquality : StructuredComparisonEquality ctx
  structuredComparisonEquality_eq : structuredComparisonEquality = structuredEq
  tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq
  targetPackage :
    CertifiedTracePeriodTomographyTarget structuredEq primitiveTable TraceInput

namespace TracePeriodTomographyFromPrimitiveFamilies

def ofPrimitiveFamilyTable
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (primitiveTable : PrimitiveFamilyPeriodTomographyTable structuredEq)
    (TraceInput : Type w)
    (traceInput : TraceInput)
    (primitiveTomographyTarget : Prop)
    (primitiveTomography_holds : primitiveTomographyTarget)
    (traceSoundnessTarget : Prop)
    (traceSoundness_holds : traceSoundnessTarget)
    (replayOrderCompatibilityTarget packetCutCompatibilityTarget
      canNFNormalizationCompatibilityTarget boundaryReconstructionCompatibilityTarget
      coherenceWitnessCompatibilityTarget closureTransportTarget : Prop)
    (closureTransport_holds : closureTransportTarget)
    (tomographySoundness : GeometricRealizationTomographySoundness ctx structuredEq) :
    TracePeriodTomographyFromPrimitiveFamilies structuredEq where
  primitiveTable := primitiveTable
  TraceInput := TraceInput
  traceInput := traceInput
  primitiveTomographyTarget := primitiveTomographyTarget
  primitiveTomography_holds := primitiveTomography_holds
  traceSoundnessTarget := traceSoundnessTarget
  traceSoundness_holds := traceSoundness_holds
  replayOrderCompatibilityTarget := replayOrderCompatibilityTarget
  packetCutCompatibilityTarget := packetCutCompatibilityTarget
  canNFNormalizationCompatibilityTarget := canNFNormalizationCompatibilityTarget
  boundaryReconstructionCompatibilityTarget := boundaryReconstructionCompatibilityTarget
  coherenceWitnessCompatibilityTarget := coherenceWitnessCompatibilityTarget
  closureTransportTarget := closureTransportTarget
  closureTransport_holds := closureTransport_holds
  structuredComparisonEquality := structuredEq
  structuredComparisonEquality_eq := rfl
  tomographySoundness := tomographySoundness
  targetPackage :=
    CertifiedTracePeriodTomographyTarget.fromClosureTransport
      primitiveTable
      TraceInput
      traceInput
      primitiveTomographyTarget
      primitiveTomography_holds
      traceSoundnessTarget
      traceSoundness_holds
      replayOrderCompatibilityTarget
      packetCutCompatibilityTarget
      canNFNormalizationCompatibilityTarget
      boundaryReconstructionCompatibilityTarget
      coherenceWitnessCompatibilityTarget
      closureTransportTarget
      closureTransport_holds
      tomographySoundness

end TracePeriodTomographyFromPrimitiveFamilies

def symbolicEnvDualityDataUniversalityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicEnvDatum ctx) :
    DualityDataUniversalityTarget ctx :=
  DualityDataUniversalityTarget.ofEnvFamily
    (symbolicEnvGeneratorFamilyData datum)
    datum.envelopeCorrespondence.correspondenceTarget
    datum.ambientObjectData.comparisonData.periodCompatibilityTarget

@[simp] theorem symbolicCorrFiniteCorrespondenceUniversalityTarget_corrFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicCorrDatum ctx) :
    (symbolicCorrFiniteCorrespondenceUniversalityTarget datum).corrFamily =
      symbolicCorrGeneratorFamilyData datum := rfl

@[simp] theorem symbolicLocLocalizationTriangleUniversalityTarget_locFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicLocDatum ctx) :
    (symbolicLocLocalizationTriangleUniversalityTarget datum).locFamily =
      symbolicLocGeneratorFamilyData datum := rfl

@[simp] theorem symbolicNisGeometricPresentationTheoremTarget_operationalPresentation
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicNisDatum ctx) :
    (symbolicNisGeometricPresentationTheoremTarget datum).operationalPresentation =
      symbolicNisOperationalGeometricPresentationTarget datum := rfl

@[simp] theorem symbolicA1RealBettiDeRhamComparisonRealizationTarget_realization
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicA1Datum ctx) :
    (symbolicA1RealBettiDeRhamComparisonRealizationTarget datum).realization =
      symbolicA1RealizationFunctorData datum := rfl

@[simp] theorem symbolicEnvDualityDataUniversalityTarget_envFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SymbolicEnvDatum ctx) :
    (symbolicEnvDualityDataUniversalityTarget datum).envFamily =
      symbolicEnvGeneratorFamilyData datum := rfl

end ClassicalPeriods
end TraceCalc