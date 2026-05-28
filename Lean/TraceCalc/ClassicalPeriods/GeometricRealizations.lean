import TraceCalc.ClassicalPeriods.FramedPeriodsConcrete
import TraceCalc.ClassicalPeriods.GeometricObjects

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

/-- Interface-level geometric Betti realization data.

This remains deliberately lightweight: it names the carrier used for the Betti side together with
the theorem targets asserting that the carrier comes from the intended geometric realization. -/
structure GeometricBettiRealizationData
    (ctx : ClassicalComparisonContext.{u, v}) where
  geometricObject : GeometricPeriodObject ctx
  carrier : BettiRealizationCarrier ctx
  geometricOriginTarget : Prop
  realizationFunctorialityTarget : Prop

/-- Interface-level geometric de Rham realization data. -/
structure GeometricDeRhamRealizationData
    (ctx : ClassicalComparisonContext.{u, v}) where
  geometricObject : GeometricPeriodObject ctx
  carrier : DeRhamRealizationCarrier ctx
  geometricOriginTarget : Prop
  realizationFunctorialityTarget : Prop

/-- Grothendieck comparison data sitting above the lightweight concrete comparison interface. -/
structure GrothendieckComparisonData
    (ctx : ClassicalComparisonContext.{u, v})
    (betti : GeometricBettiRealizationData ctx)
    (deRham : GeometricDeRhamRealizationData ctx) where
  comparison : ComparisonIsomorphismData ctx betti.carrier deRham.carrier
  sameUnderlyingObject : betti.geometricObject = deRham.geometricObject
  grothendieckComparisonTarget : Prop
  periodCompatibilityTarget : Prop

/-- Sigma-packaged geometric comparison-object data. -/
abbrev GeometricComparisonObjectData (ctx : ClassicalComparisonContext.{u, v}) :=
  Σ betti : GeometricBettiRealizationData ctx,
    Σ deRham : GeometricDeRhamRealizationData ctx,
      GrothendieckComparisonData ctx betti deRham

namespace GeometricComparisonObjectData

/-- Underlying geometric Betti realization package. -/
def bettiData
    {ctx : ClassicalComparisonContext.{u, v}}
    (data : GeometricComparisonObjectData ctx) : GeometricBettiRealizationData ctx :=
  data.1

/-- Underlying geometric de Rham realization package. -/
def deRhamData
    {ctx : ClassicalComparisonContext.{u, v}}
    (data : GeometricComparisonObjectData ctx) : GeometricDeRhamRealizationData ctx :=
  data.2.1

/-- Underlying Grothendieck comparison package. -/
def comparisonData
    {ctx : ClassicalComparisonContext.{u, v}}
    (data : GeometricComparisonObjectData ctx) :
    GrothendieckComparisonData ctx data.bettiData data.deRhamData :=
  data.2.2

/-- Geometric Betti carrier attached to an object datum. -/
abbrev BettiCarrier
    {ctx : ClassicalComparisonContext.{u, v}}
    (data : GeometricComparisonObjectData ctx) : Type _ :=
  data.bettiData.carrier.Carrier

/-- Geometric de Rham carrier attached to an object datum. -/
abbrev DeRhamCarrier
    {ctx : ClassicalComparisonContext.{u, v}}
    (data : GeometricComparisonObjectData ctx) : Type _ :=
  data.deRhamData.carrier.Carrier

/-- Forget the geometric comparison-object package to the existing concrete object layer. -/
def toConcreteComparisonObjectData
    {ctx : ClassicalComparisonContext.{u, v}}
    (data : GeometricComparisonObjectData ctx) : ConcreteComparisonObjectData ctx where
  betti := data.bettiData.carrier
  deRham := data.deRhamData.carrier
  comparison := data.comparisonData.comparison

@[simp] theorem toConcreteComparisonObjectData_betti
    {ctx : ClassicalComparisonContext.{u, v}}
    (data : GeometricComparisonObjectData ctx) :
    data.toConcreteComparisonObjectData.betti = data.bettiData.carrier := rfl

@[simp] theorem toConcreteComparisonObjectData_deRham
    {ctx : ClassicalComparisonContext.{u, v}}
    (data : GeometricComparisonObjectData ctx) :
    data.toConcreteComparisonObjectData.deRham = data.deRhamData.carrier := rfl

@[simp] theorem toConcreteComparisonObjectData_comparison
    {ctx : ClassicalComparisonContext.{u, v}}
    (data : GeometricComparisonObjectData ctx) :
    data.toConcreteComparisonObjectData.comparison = data.comparisonData.comparison := rfl

/-- Forget further to the structured comparison-object surface used by tomography. -/
def toStructuredComparisonObject
    {ctx : ClassicalComparisonContext.{u, v}}
    (data : GeometricComparisonObjectData ctx) : ClassicalStructuredComparisonObject ctx :=
  data.toConcreteComparisonObjectData.toStructuredComparisonObject

@[simp] theorem toStructuredComparisonObject_eq
    {ctx : ClassicalComparisonContext.{u, v}}
    (data : GeometricComparisonObjectData ctx) :
    data.toStructuredComparisonObject = data.toConcreteComparisonObjectData.toStructuredComparisonObject := rfl

end GeometricComparisonObjectData

/-- Interface-level geometric framed period data.

This layer names the geometric classes and the scalar period they are meant to realize, while the
actual descent to the existing concrete framed-period datum is carried by
`realizedConcreteDatum`. -/
structure GeometricFramedPeriodRawPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : GeometricComparisonObjectData ctx}
    (morphism :
      ClassicalStructuredComparisonMorphism
        source.toStructuredComparisonObject
        target.toStructuredComparisonObject) where
  geometricCorrespondence :
    GeometricCorrespondence source.deRhamData.geometricObject target.bettiData.geometricObject
  deRhamClass : source.DeRhamCarrier
  bettiClass : target.BettiCarrier
  bettiCoframe : target.toStructuredComparisonObject.BettiOverScalar →ₗ[ctx.ScalarField] ctx.ScalarField
  geometricScalarPeriod : ctx.ScalarField
  concreteDeRhamVector : source.toStructuredComparisonObject.DeRhamOverScalar
  concreteBettiImage : target.toStructuredComparisonObject.BettiOverScalar
  concreteBettiCycle : target.toStructuredComparisonObject.BettiOverScalar
  concreteComparisonCompatibility :
    concreteBettiImage = target.toStructuredComparisonObject.comparisonIso
      (morphism.deRhamMapOverScalar concreteDeRhamVector)
  concreteScalarPeriod_eq_evaluation :
    geometricScalarPeriod = bettiCoframe concreteBettiImage
  deRhamClassRealizesFrameTarget : Prop
  bettiClassRealizesCycleTarget : Prop
  grothendieckPeriodEvaluationTarget : Prop

/-- Structured `A1` period-preservation certificate.

This packages the projection/section geometry together with the pullback/pushforward compatibility
needed to manufacture a framed-period payload without asking callers to populate the raw record
field-by-field. The equalities encode the internal form of
`∫_γ ω = ∫_{s_* γ} p^*ω`. -/
structure A1PeriodPreservationCertificate
    {ctx : ClassicalComparisonContext.{u, v}}
    (source target : GeometricComparisonObjectData ctx)
    (morphism :
      ClassicalStructuredComparisonMorphism
        source.toStructuredComparisonObject
        target.toStructuredComparisonObject) where
  projectionCorrespondence :
    GeometricCorrespondence target.deRhamData.geometricObject source.deRhamData.geometricObject
  sectionCorrespondence :
    GeometricCorrespondence source.deRhamData.geometricObject target.bettiData.geometricObject
  projectionSectionIdentityTarget : Prop
  sourceDeRhamClass : source.DeRhamCarrier
  pushedForwardBettiClass : target.BettiCarrier
  bettiCoframe : target.toStructuredComparisonObject.BettiOverScalar →ₗ[ctx.ScalarField] ctx.ScalarField
  preservedScalarPeriod : ctx.ScalarField
  sourceDeRhamVector : source.toStructuredComparisonObject.DeRhamOverScalar
  pulledBackDeRhamVector : target.toStructuredComparisonObject.DeRhamOverScalar
  pushedForwardBettiImage : target.toStructuredComparisonObject.BettiOverScalar
  pushedForwardBettiCycle : target.toStructuredComparisonObject.BettiOverScalar
  pullbackOnDeRhamVectors :
    morphism.deRhamMapOverScalar sourceDeRhamVector = pulledBackDeRhamVector
  comparisonEvaluationCompatibility :
    pushedForwardBettiImage = target.toStructuredComparisonObject.comparisonIso pulledBackDeRhamVector
  scalarPeriodPreserved :
    preservedScalarPeriod = bettiCoframe pushedForwardBettiImage
  pullbackOnDeRhamClassesTarget : Prop
  pushforwardOnBettiCyclesTarget : Prop
  deRhamClassRealizesFrameTarget : Prop
  bettiClassRealizesCycleTarget : Prop
  grothendieckPeriodEvaluationTarget : Prop

structure GeometricFramedPeriodData
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : GeometricComparisonObjectData ctx}
    (morphism :
      ClassicalStructuredComparisonMorphism
        source.toStructuredComparisonObject
        target.toStructuredComparisonObject) where
  geometricCorrespondence :
    GeometricCorrespondence source.deRhamData.geometricObject target.bettiData.geometricObject
  deRhamClass : source.DeRhamCarrier
  bettiClass : target.BettiCarrier
  bettiCoframe : target.toStructuredComparisonObject.BettiOverScalar →ₗ[ctx.ScalarField] ctx.ScalarField
  geometricScalarPeriod : ctx.ScalarField
  concreteDeRhamVector : source.toStructuredComparisonObject.DeRhamOverScalar
  concreteBettiImage : target.toStructuredComparisonObject.BettiOverScalar
  concreteBettiCycle : target.toStructuredComparisonObject.BettiOverScalar
  concreteComparisonCompatibility :
    concreteBettiImage = target.toStructuredComparisonObject.comparisonIso
      (morphism.deRhamMapOverScalar concreteDeRhamVector)
  concreteScalarPeriod_eq_evaluation :
    geometricScalarPeriod = bettiCoframe concreteBettiImage
  deRhamClassRealizesFrameTarget : Prop
  bettiClassRealizesCycleTarget : Prop
  grothendieckPeriodEvaluationTarget : Prop

namespace GeometricFramedPeriodData

/-- Structural constructor exposing the exact data needed to build a geometric framed-period
witness.  This keeps the framed-period payload first-class rather than hiding it behind theorem
targets or placeholder slots. -/
def ofRawPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : GeometricComparisonObjectData ctx}
    {morphism :
      ClassicalStructuredComparisonMorphism
        source.toStructuredComparisonObject
        target.toStructuredComparisonObject}
    (payload : GeometricFramedPeriodRawPayload morphism) :
    GeometricFramedPeriodData morphism :=
  { geometricCorrespondence := payload.geometricCorrespondence
    deRhamClass := payload.deRhamClass
    bettiClass := payload.bettiClass
    bettiCoframe := payload.bettiCoframe
    geometricScalarPeriod := payload.geometricScalarPeriod
    concreteDeRhamVector := payload.concreteDeRhamVector
    concreteBettiImage := payload.concreteBettiImage
    concreteBettiCycle := payload.concreteBettiCycle
    concreteComparisonCompatibility := payload.concreteComparisonCompatibility
    concreteScalarPeriod_eq_evaluation := payload.concreteScalarPeriod_eq_evaluation
    deRhamClassRealizesFrameTarget := payload.deRhamClassRealizesFrameTarget
    bettiClassRealizesCycleTarget := payload.bettiClassRealizesCycleTarget
    grothendieckPeriodEvaluationTarget := payload.grothendieckPeriodEvaluationTarget }

/-- Forget a geometric framed period witness to the concrete framed-period layer. -/
def toConcreteFramedPeriodData
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : GeometricComparisonObjectData ctx}
    {morphism :
      ClassicalStructuredComparisonMorphism
        source.toStructuredComparisonObject
        target.toStructuredComparisonObject}
    (datum : GeometricFramedPeriodData morphism) :
    ConcreteFramedPeriodData morphism :=
  { deRhamVector := datum.concreteDeRhamVector
    bettiImage := datum.concreteBettiImage
    bettiCovector := datum.bettiCoframe
    bettiCycle := datum.concreteBettiCycle
    scalarPeriod := datum.geometricScalarPeriod
    comparisonCompatibility := datum.concreteComparisonCompatibility
    scalarPeriod_eq_evaluation := datum.concreteScalarPeriod_eq_evaluation }

@[simp] theorem toConcreteFramedPeriodData_eq
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : GeometricComparisonObjectData ctx}
    {morphism :
      ClassicalStructuredComparisonMorphism
        source.toStructuredComparisonObject
        target.toStructuredComparisonObject}
    (datum : GeometricFramedPeriodData morphism) :
    datum.toConcreteFramedPeriodData.scalarPeriod = datum.geometricScalarPeriod := rfl

end GeometricFramedPeriodData

namespace GeometricFramedPeriodRawPayload

/-- Build a framed-period raw payload from explicit `A1` projection/section preservation data. -/
def ofA1Preservation
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : GeometricComparisonObjectData ctx}
    {morphism :
      ClassicalStructuredComparisonMorphism
        source.toStructuredComparisonObject
        target.toStructuredComparisonObject}
    (certificate : A1PeriodPreservationCertificate source target morphism) :
    GeometricFramedPeriodRawPayload morphism :=
  { geometricCorrespondence := certificate.sectionCorrespondence
    deRhamClass := certificate.sourceDeRhamClass
    bettiClass := certificate.pushedForwardBettiClass
    bettiCoframe := certificate.bettiCoframe
    geometricScalarPeriod := certificate.preservedScalarPeriod
    concreteDeRhamVector := certificate.sourceDeRhamVector
    concreteBettiImage := certificate.pushedForwardBettiImage
    concreteBettiCycle := certificate.pushedForwardBettiCycle
    concreteComparisonCompatibility := by
      rw [certificate.pullbackOnDeRhamVectors]
      exact certificate.comparisonEvaluationCompatibility
    concreteScalarPeriod_eq_evaluation := certificate.scalarPeriodPreserved
    deRhamClassRealizesFrameTarget := certificate.deRhamClassRealizesFrameTarget
    bettiClassRealizesCycleTarget := certificate.bettiClassRealizesCycleTarget
    grothendieckPeriodEvaluationTarget := certificate.grothendieckPeriodEvaluationTarget }

end GeometricFramedPeriodRawPayload

/-- Sigma-packaged geometric framed period data. -/
abbrev SomeGeometricFramedPeriodData (ctx : ClassicalComparisonContext.{u, v}) :=
  Σ source : GeometricComparisonObjectData ctx,
    Σ target : GeometricComparisonObjectData ctx,
      Σ morphism :
          ClassicalStructuredComparisonMorphism
            source.toStructuredComparisonObject
            target.toStructuredComparisonObject,
        GeometricFramedPeriodData morphism

namespace SomeGeometricFramedPeriodData

/-- Sigma-pack a raw framed-period payload into the existing geometric framed-period surface. -/
def ofRawPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    (source target : GeometricComparisonObjectData ctx)
    (morphism :
      ClassicalStructuredComparisonMorphism
        source.toStructuredComparisonObject
        target.toStructuredComparisonObject)
    (payload : GeometricFramedPeriodRawPayload morphism) :
    SomeGeometricFramedPeriodData ctx :=
  ⟨source, target, morphism, GeometricFramedPeriodData.ofRawPayload payload⟩

/-- The scalar period claimed by the geometric framed witness. -/
def geometricScalarPeriod
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SomeGeometricFramedPeriodData ctx) : ctx.ScalarField :=
  datum.2.2.2.geometricScalarPeriod

/-- Forget a sigma-packaged geometric framed witness to the concrete framed-period layer. -/
def toSomeConcreteFramedPeriodData
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SomeGeometricFramedPeriodData ctx) : SomeConcreteFramedPeriodData ctx :=
  let source := datum.1.toStructuredComparisonObject
  let target := datum.2.1.toStructuredComparisonObject
  let morphism := datum.2.2.1
  let geometric := datum.2.2.2
  ⟨source, target, morphism, geometric.toConcreteFramedPeriodData⟩

@[simp] theorem toSomeConcreteFramedPeriodData_scalarPeriod
    {ctx : ClassicalComparisonContext.{u, v}}
    (datum : SomeGeometricFramedPeriodData ctx) :
    datum.toSomeConcreteFramedPeriodData.scalarPeriod = datum.2.2.2.geometricScalarPeriod := rfl

end SomeGeometricFramedPeriodData

/-- Soundness target asserting that geometric framed-period data really descends to the concrete
framed-period witnesses used by tomography. -/
structure GeometricPeriodsRealizeConcreteFramedData
    (ctx : ClassicalComparisonContext.{u, v})
    {ProbeIndex : Type w}
    (geometricDatum :
      ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeGeometricFramedPeriodData ctx) where
  theoremTarget :
    ∀ (probe : ProbeIndex) (morphism : SomeStructuredComparisonMorphism ctx),
      (geometricDatum probe morphism).toSomeConcreteFramedPeriodData.scalarPeriod =
        (geometricDatum probe morphism).geometricScalarPeriod

namespace GeometricPeriodsRealizeConcreteFramedData

theorem scalarPeriod_eq_geometricScalarPeriod
    {ctx : ClassicalComparisonContext.{u, v}}
    {ProbeIndex : Type w}
    {geometricDatum :
      ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeGeometricFramedPeriodData ctx}
    (soundness : GeometricPeriodsRealizeConcreteFramedData ctx geometricDatum)
    (probe : ProbeIndex)
    (morphism : SomeStructuredComparisonMorphism ctx) :
    (geometricDatum probe morphism).toSomeConcreteFramedPeriodData.scalarPeriod =
      (geometricDatum probe morphism).geometricScalarPeriod :=
  soundness.theoremTarget probe morphism

end GeometricPeriodsRealizeConcreteFramedData

/-- Object/correspondence-level realization data connecting the geometric source layer to the
Betti/de Rham/comparison packages. -/
structure GeometricRealizationFunctorData
    (ctx : ClassicalComparisonContext.{u, v}) where
  ObjectIndex : Type w
  geometricObject : ObjectIndex → GeometricPeriodObject ctx
  CorrespondenceIndex : Type x
  sourceIndex : CorrespondenceIndex → ObjectIndex
  targetIndex : CorrespondenceIndex → ObjectIndex
  correspondence :
    (corr : CorrespondenceIndex) →
      GeometricCorrespondence
        (geometricObject (sourceIndex corr))
        (geometricObject (targetIndex corr))
  bettiRealization : ObjectIndex → GeometricBettiRealizationData ctx
  deRhamRealization : ObjectIndex → GeometricDeRhamRealizationData ctx
  comparisonData :
    ∀ idx : ObjectIndex,
      GrothendieckComparisonData ctx (bettiRealization idx) (deRhamRealization idx)
  objectFunctorialityTarget : Prop

namespace GeometricRealizationFunctorData

/-- The geometric comparison-object datum attached to a source object index. -/
def geometricComparisonObjectData
    {ctx : ClassicalComparisonContext.{u, v}}
    (data : GeometricRealizationFunctorData ctx)
    (idx : data.ObjectIndex) : GeometricComparisonObjectData ctx :=
  ⟨data.bettiRealization idx, data.deRhamRealization idx, data.comparisonData idx⟩

@[simp] theorem geometricComparisonObjectData_bettiData
  {ctx : ClassicalComparisonContext.{u, v}}
  (data : GeometricRealizationFunctorData ctx)
  (idx : data.ObjectIndex) :
  (data.geometricComparisonObjectData idx).bettiData = data.bettiRealization idx := rfl

@[simp] theorem geometricComparisonObjectData_deRhamData
  {ctx : ClassicalComparisonContext.{u, v}}
  (data : GeometricRealizationFunctorData ctx)
  (idx : data.ObjectIndex) :
  (data.geometricComparisonObjectData idx).deRhamData = data.deRhamRealization idx := rfl

@[simp] theorem geometricComparisonObjectData_comparisonData
  {ctx : ClassicalComparisonContext.{u, v}}
  (data : GeometricRealizationFunctorData ctx)
  (idx : data.ObjectIndex) :
  (data.geometricComparisonObjectData idx).comparisonData = data.comparisonData idx := rfl

end GeometricRealizationFunctorData

/-- Smooth-scheme realization data attached to every object index of a geometric realization
functor. -/
structure GeometricSmoothRealizationFunctorData
    {ctx : ClassicalComparisonContext.{u, v}}
    (realization : GeometricRealizationFunctorData ctx) where
  objectRealization :
    (idx : realization.ObjectIndex) →
      GeometricObjectSmoothRealization (realization.geometricObject idx)

namespace GeometricSmoothRealizationFunctorData

def scheme
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (data : GeometricSmoothRealizationFunctorData realization)
    (idx : realization.ObjectIndex) :
    Wall10A.SchemeOverQ :=
  (data.objectRealization idx).scheme

def smoothScheme
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (data : GeometricSmoothRealizationFunctorData realization)
    (idx : realization.ObjectIndex) :
    Wall10A.SchemeOverQ.SmoothSchemeOverQ (data.scheme idx) :=
  (data.objectRealization idx).smoothScheme

theorem geometricAdmissibility
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (data : GeometricSmoothRealizationFunctorData realization)
    (idx : realization.ObjectIndex) :
    (realization.geometricObject idx).geometricAdmissibilityTarget :=
  (data.objectRealization idx).geometricAdmissibility

theorem realizationDefined
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (data : GeometricSmoothRealizationFunctorData realization)
    (idx : realization.ObjectIndex) :
    (realization.geometricObject idx).realizationDefinedTarget :=
  (data.objectRealization idx).realizationDefined

end GeometricSmoothRealizationFunctorData

/-- Functoriality target for framed-period extraction from geometric correspondences. -/
structure GeometricFramedPeriodFunctoriality
    (ctx : ClassicalComparisonContext.{u, v})
    (realization : GeometricRealizationFunctorData ctx) where
  sourceFraming :
    (corr : realization.CorrespondenceIndex) →
      GeometricFramedObject
        (realization.geometricObject (realization.sourceIndex corr))
  targetFraming :
    (corr : realization.CorrespondenceIndex) →
      GeometricFramedObject
        (realization.geometricObject (realization.targetIndex corr))
  theoremTarget :
    ∀ corr : realization.CorrespondenceIndex,
      let sourceData :=
        realization.geometricComparisonObjectData (realization.sourceIndex corr)
      let targetData :=
        realization.geometricComparisonObjectData (realization.targetIndex corr)
      ∃ morphism :
          ClassicalStructuredComparisonMorphism
            sourceData.toStructuredComparisonObject
            targetData.toStructuredComparisonObject,
        Nonempty (GeometricFramedPeriodData morphism)
  framedPeriodFunctorialityTarget : Prop
  framedExtractionCompatibilityTarget : Prop

namespace GeometricFramedPeriodFunctoriality

def soundnessTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (functoriality : GeometricFramedPeriodFunctoriality ctx realization) : Prop :=
  functoriality.framedPeriodFunctorialityTarget

/-- Full framed-period payload for a fixed geometric source/target package and structured
comparison morphism.  The geometric source and target packages are explicit indices, so every
universe used by `GeometricFramedPeriodData` is determined before the morphism is mentioned. -/
def FullFramedPeriodPayload
    {ctx : ClassicalComparisonContext.{u, v}}
    {source target : GeometricComparisonObjectData ctx}
    (morphism : ClassicalStructuredComparisonMorphism
      source.toStructuredComparisonObject target.toStructuredComparisonObject) : Prop :=
  Nonempty (GeometricFramedPeriodData morphism)

/-- Full framed-period matrix agreement for a geometric framed-period functoriality package.

Unlike `morphismExists`, this statement retains the actual `GeometricFramedPeriodData` payload. -/
def FullPeriodMatrixAgreementStatement
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (_func : GeometricFramedPeriodFunctoriality ctx realization) : Prop :=
  ∀ corr : realization.CorrespondenceIndex,
    let sourceData := realization.geometricComparisonObjectData (realization.sourceIndex corr)
    let targetData := realization.geometricComparisonObjectData (realization.targetIndex corr)
    ∃ morphism : ClassicalStructuredComparisonMorphism
        sourceData.toStructuredComparisonObject
        targetData.toStructuredComparisonObject,
      FullFramedPeriodPayload morphism

/-- The full framed-period matrix agreement is exactly the stored theorem target. -/
theorem fullPeriodMatrixAgreement_holds
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (func : GeometricFramedPeriodFunctoriality ctx realization) :
    func.FullPeriodMatrixAgreementStatement := by
  intro corr
  exact func.theoremTarget corr

/-- Extract the morphism-existence component of the framed period theorem target.

For each correspondence index `corr`, the `theoremTarget` field asserts the existence of a
`ClassicalStructuredComparisonMorphism` (together with a geometric framed period witness).
This function forgets the framed witness and returns only the universe-safe morphism-existence
guarantee `Nonempty (ClassicalStructuredComparisonMorphism src tgt)`.

Defined here (where all universe parameters of `GeometricFramedPeriodData` are in scope)
so that external files can call it without needing to declare the internal universe params. -/
def morphismExists
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (func : GeometricFramedPeriodFunctoriality ctx realization)
    (corr : realization.CorrespondenceIndex) :
    Nonempty (ClassicalStructuredComparisonMorphism
      (realization.geometricComparisonObjectData (realization.sourceIndex corr)).toStructuredComparisonObject
      (realization.geometricComparisonObjectData (realization.targetIndex corr)).toStructuredComparisonObject) :=
  let ⟨m, _⟩ := func.theoremTarget corr
  ⟨m⟩

end GeometricFramedPeriodFunctoriality

/-- Naturality target for the Grothendieck comparison package with respect to geometric
correspondences. -/
structure GeometricComparisonNaturality
    (ctx : ClassicalComparisonContext.{u, v})
    (realization : GeometricRealizationFunctorData ctx) where
  theoremTarget :
    ∀ corr : realization.CorrespondenceIndex,
      let sourceData := realization.comparisonData (realization.sourceIndex corr)
      let targetData := realization.comparisonData (realization.targetIndex corr)
      sourceData.comparison.comparisonNaturalityTarget ∧
        targetData.comparison.comparisonNaturalityTarget
  baseChangeNaturalityTarget : Prop

namespace GeometricComparisonNaturality

def comparisonNaturalityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (naturality : GeometricComparisonNaturality ctx realization) : Prop :=
  naturality.baseChangeNaturalityTarget

theorem source_comparisonNaturalityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (naturality : GeometricComparisonNaturality ctx realization)
    (corr : realization.CorrespondenceIndex) :
    (realization.comparisonData (realization.sourceIndex corr)).comparison.comparisonNaturalityTarget :=
  (naturality.theoremTarget corr).1

theorem target_comparisonNaturalityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {realization : GeometricRealizationFunctorData ctx}
    (naturality : GeometricComparisonNaturality ctx realization)
    (corr : realization.CorrespondenceIndex) :
    (realization.comparisonData (realization.targetIndex corr)).comparison.comparisonNaturalityTarget :=
  (naturality.theoremTarget corr).2

end GeometricComparisonNaturality

/-- The geometric theorem-target layer feeding real Betti/de Rham comparison data into the
existing concrete tomography package. -/
structure GeometricRealizationTomographySoundness
    (ctx : ClassicalComparisonContext.{u, v})
    (structuredEq : StructuredComparisonEquality ctx) where
  geometricRealizationFunctor : GeometricRealizationFunctorData ctx
  geometricFramedFunctoriality :
    GeometricFramedPeriodFunctoriality ctx geometricRealizationFunctor
  geometricComparisonNaturality :
    GeometricComparisonNaturality ctx geometricRealizationFunctor
  geometricObjectData :
    geometricRealizationFunctor.ObjectIndex → GeometricComparisonObjectData ctx
  objectDataCompatibilityTarget :
    ∀ idx : geometricRealizationFunctor.ObjectIndex,
      geometricObjectData idx =
        geometricRealizationFunctor.geometricComparisonObjectData idx
  ProbeIndex : Type y
  geometricFramedDatum :
    ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeGeometricFramedPeriodData ctx
  geometricToConcreteFramed :
    GeometricPeriodsRealizeConcreteFramedData ctx geometricFramedDatum
  basisFreePeriodMapEquality : BasisFreePeriodMapEquality ctx
  probeExtensionality :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      (concreteFramedProbeFamily
        (fun probe morphism =>
          (geometricFramedDatum probe morphism).toSomeConcreteFramedPeriodData)).toScalarProbeFamily
      basisFreePeriodMapEquality
  packedReconstruction :
    BasisFreePeriodMapDeterminesPackedComparison
      ctx
      basisFreePeriodMapEquality
      structuredEq

namespace GeometricRealizationTomographySoundness

/-- Forget the geometric object package to the existing concrete comparison-object layer. -/
def concreteComparisonObjectData
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (package : GeometricRealizationTomographySoundness ctx structuredEq) :
    package.geometricRealizationFunctor.ObjectIndex → ConcreteComparisonObjectData ctx :=
  fun idx => (package.geometricObjectData idx).toConcreteComparisonObjectData

@[simp] theorem concreteComparisonObjectData_apply
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (package : GeometricRealizationTomographySoundness ctx structuredEq)
    (idx : package.geometricRealizationFunctor.ObjectIndex) :
    package.concreteComparisonObjectData idx =
      (package.geometricObjectData idx).toConcreteComparisonObjectData := rfl

/-- Concrete framed-period data extracted from the geometric theorem-target family. -/
def concreteFramedDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (package : GeometricRealizationTomographySoundness ctx structuredEq) :
    package.ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx :=
  fun probe morphism =>
    (package.geometricFramedDatum probe morphism).toSomeConcreteFramedPeriodData

@[simp] theorem concreteFramedDatum_apply
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (package : GeometricRealizationTomographySoundness ctx structuredEq)
    (probe : package.ProbeIndex)
    (morphism : SomeStructuredComparisonMorphism ctx) :
    package.concreteFramedDatum probe morphism =
      (package.geometricFramedDatum probe morphism).toSomeConcreteFramedPeriodData := rfl

/-- Helper constructor for the geometric tomography soundness package. -/
def ofFunctorialityAndFramedData
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (geometricRealizationFunctor : GeometricRealizationFunctorData ctx)
    (geometricFramedFunctoriality :
      GeometricFramedPeriodFunctoriality ctx geometricRealizationFunctor)
    (geometricComparisonNaturality :
      GeometricComparisonNaturality ctx geometricRealizationFunctor)
    (geometricObjectData :
      geometricRealizationFunctor.ObjectIndex → GeometricComparisonObjectData ctx)
    (objectDataCompatibilityTarget :
      ∀ idx : geometricRealizationFunctor.ObjectIndex,
        geometricObjectData idx =
          geometricRealizationFunctor.geometricComparisonObjectData idx)
    (ProbeIndex : Type y)
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
    GeometricRealizationTomographySoundness ctx structuredEq where
  geometricRealizationFunctor := geometricRealizationFunctor
  geometricFramedFunctoriality := geometricFramedFunctoriality
  geometricComparisonNaturality := geometricComparisonNaturality
  geometricObjectData := geometricObjectData
  objectDataCompatibilityTarget := objectDataCompatibilityTarget
  ProbeIndex := ProbeIndex
  geometricFramedDatum := geometricFramedDatum
  geometricToConcreteFramed := geometricToConcreteFramed
  basisFreePeriodMapEquality := basisFreePeriodMapEquality
  probeExtensionality := probeExtensionality
  packedReconstruction := packedReconstruction

/-- The geometric theorem-target layer feeds directly into the concrete tomography package. -/
def toConcreteRealizationTomographyPackage
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (package : GeometricRealizationTomographySoundness ctx structuredEq) :
    ConcreteRealizationTomographyPackage ctx structuredEq where
  ObjectIndex := package.geometricRealizationFunctor.ObjectIndex
  comparisonObjectData := package.concreteComparisonObjectData
  ProbeIndex := package.ProbeIndex
  concreteFramedDatum := package.concreteFramedDatum
  framedSoundness := concreteFramedPeriodDataSoundness ctx
  scalarShadowExtraction := concreteScalarShadowFromFramedPeriods ctx
  basisFreePeriodMapEquality := package.basisFreePeriodMapEquality
  probeExtensionality := package.probeExtensionality
  packedReconstruction := package.packedReconstruction
  framedToProbeEquality :=
    concreteFramedPeriodsInduceFramedProbeEquality package.concreteFramedDatum
  framedProbeToTomographyProbeEquality :=
    tautologicalFramedProbeEquality_to_TomographyProbeEquality
      (concreteFramedProbeFamily package.concreteFramedDatum)

@[simp] theorem toConcreteRealizationTomographyPackage_comparisonObjectData
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (package : GeometricRealizationTomographySoundness ctx structuredEq) :
    package.toConcreteRealizationTomographyPackage.comparisonObjectData = package.concreteComparisonObjectData := rfl

@[simp] theorem toConcreteRealizationTomographyPackage_concreteFramedDatum
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (package : GeometricRealizationTomographySoundness ctx structuredEq) :
    package.toConcreteRealizationTomographyPackage.concreteFramedDatum = package.concreteFramedDatum := rfl

@[simp] theorem toConcreteRealizationTomographyPackage_basisFreePeriodMapEquality
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (package : GeometricRealizationTomographySoundness ctx structuredEq) :
    package.toConcreteRealizationTomographyPackage.basisFreePeriodMapEquality = package.basisFreePeriodMapEquality := rfl

def comparisonNaturalityTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (package : GeometricRealizationTomographySoundness ctx structuredEq) : Prop :=
  package.geometricComparisonNaturality.comparisonNaturalityTarget

def soundnessTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (package : GeometricRealizationTomographySoundness ctx structuredEq) : Prop :=
  package.geometricFramedFunctoriality.soundnessTarget

theorem scalarPeriod_eq_geometricScalarPeriod
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (package : GeometricRealizationTomographySoundness ctx structuredEq)
    (probe : package.ProbeIndex)
    (morphism : SomeStructuredComparisonMorphism ctx) :
    (package.geometricFramedDatum probe morphism).toSomeConcreteFramedPeriodData.scalarPeriod =
      (package.geometricFramedDatum probe morphism).geometricScalarPeriod :=
  package.geometricToConcreteFramed.scalarPeriod_eq_geometricScalarPeriod probe morphism

def FaithfulConcreteFramedProbeTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    (structuredEq : StructuredComparisonEquality ctx)
    {ProbeIndex : Type y}
    (concreteDatum : ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeConcreteFramedPeriodData ctx) : Prop :=
  ∀ left right : SomeStructuredComparisonMorphism ctx,
    ConcreteFramedProbeEquality concreteDatum left right →
      structuredEq.relates left right

def faithfulFramedProbeTarget
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (package : GeometricRealizationTomographySoundness ctx structuredEq) : Prop :=
  FaithfulConcreteFramedProbeTarget structuredEq package.concreteFramedDatum

end GeometricRealizationTomographySoundness

end ClassicalPeriods
end TraceCalc