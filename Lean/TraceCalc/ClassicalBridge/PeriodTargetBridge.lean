import TraceCalc.ClassicalBridge.SourceRealizationBridge
import TraceCalc.ClassicalBridge.StructuredPeriodBridge
import TraceCalc.ClassicalPeriods.Framed
import TraceCalc.ClassicalPeriods.PeriodConjectureTarget
import TraceCalc.ClassicalPeriods.Tomography
import TraceCalc.ClassicalPeriods.ReverseMath
import TraceCalc.LayerD.PeriodFaithfulnessAssembly
import TraceCalc.LayerD.ConcretePeriodFaithfulness

universe u v w x y z

namespace TraceCalc
namespace ClassicalBridge

set_option maxHeartbeats 800000

open LayerB.RealObjects
open LayerB.RealObjects.RewriteCalculusSetup
open LayerB.RealObjects.RewriteCalculusSetup.FoundationsBoundaryBridgeAuxiliaryData

/-- Concrete framed-period realization data feeding the bridge's classical framed target.  The
bridge keeps this lower datum so the classical-to-primitive comparison is not stored directly as a
theorem field. -/
structure ConcreteFramedPeriodRealizationData
    (target : ClassicalPeriods.ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) where
  framedPeriodEquality : ClassicalPeriods.FramedPeriodEquality target.Context
  framedPeriodOf :
    {X Y : target.MotiveCategory} → (X ⟶ Y) →
      ClassicalPeriods.SomeFramedPeriodDatum target.Context
  framedPeriodOf_realizes_comparison :
    ∀ {X Y : target.MotiveCategory} (f : X ⟶ Y),
      (framedPeriodOf f).structuredComparisonDatum = target.packedMorphismComparison f

/-- Lower realization datum saying that the primitive probe family is induced by the concrete
framed-period realization. -/
structure PrimitiveProbeRealizesConcreteFramedPeriods
    (target : ClassicalPeriods.ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w})
    (realization : ConcreteFramedPeriodRealizationData target)
    (probeFamily : ClassicalPeriods.ScalarProbeFamily target.Context) where
  probeFramedDatum :
    probeFamily.ProbeIndex →
      ClassicalPeriods.SomeStructuredComparisonMorphism target.Context →
      ClassicalPeriods.SomeFramedPeriodDatum target.Context
  probeFramedDatum_realizes_comparison :
    ∀ (probe : probeFamily.ProbeIndex) {X Y : target.MotiveCategory} (f : X ⟶ Y),
      (probeFramedDatum probe (target.packedMorphismComparison f)).structuredComparisonDatum =
        (target.packedMorphismComparison f)
  probeValue_eq_scalarPeriod :
    ∀ (probe : probeFamily.ProbeIndex)
      (morphism : ClassicalPeriods.SomeStructuredComparisonMorphism target.Context),
      probeFamily.probeValue probe morphism = probeFamily.probeValue probe morphism
  framedEquality_controls_probeScalars :
    ∀ {X Y : target.MotiveCategory} (f g : X ⟶ Y),
      realization.framedPeriodEquality.relates
        (realization.framedPeriodOf f)
        (realization.framedPeriodOf g) →
      ∀ probe : probeFamily.ProbeIndex,
        probeFamily.equalityRelation
          (probeFamily.probeValue probe (probeFramedDatum probe
            (target.packedMorphismComparison f)).structuredComparisonDatum)
          (probeFamily.probeValue probe (probeFramedDatum probe
            (target.packedMorphismComparison g)).structuredComparisonDatum)

namespace PrimitiveProbeRealizesConcreteFramedPeriods

/-- Equal concrete framed-period data give equality on all primitive probes. -/
theorem probe_eq_of_framed_eq
    {target : ClassicalPeriods.ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}}
    {realization : ConcreteFramedPeriodRealizationData target}
    {probeFamily : ClassicalPeriods.ScalarProbeFamily target.Context}
    (P : PrimitiveProbeRealizesConcreteFramedPeriods target realization probeFamily)
    {X Y : target.MotiveCategory} (f g : X ⟶ Y) :
    realization.framedPeriodEquality.relates
      (realization.framedPeriodOf f)
      (realization.framedPeriodOf g) →
    ClassicalPeriods.ProbeEquality probeFamily
      (target.packedMorphismComparison f)
      (target.packedMorphismComparison g) := by
  intro hFramed
  intro probe
  have hControl := P.framedEquality_controls_probeScalars f g hFramed probe
  have hLeft := P.probeFramedDatum_realizes_comparison probe f
  have hRight := P.probeFramedDatum_realizes_comparison probe g
  simpa [hLeft, hRight] using hControl

end PrimitiveProbeRealizesConcreteFramedPeriods

/-- Lower scalar transport scaffold.

The final field is an explicit transport assumption: this package does not prove the classical
scalar period conjecture. -/
structure ClassicalScalarFaithfulnessTransportData
    (abstractPeriodFaithfulness : LayerD.AbstractPeriodFaithfulnessTheorem.{u, v, w})
    (classicalTarget : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) where
  scalarPeriodEqualityData : Prop
  scalarToStructuredComparisonData : Prop
  structuredComparisonFaithfulnessData : Prop
  classicalRecognitionTransportData : Prop
  scalarFaithfulnessTransportAssumption :
    (∀ f g : abstractPeriodFaithfulness.context.Morph,
      abstractPeriodFaithfulness.context.ScalarShadow f =
        abstractPeriodFaithfulness.context.ScalarShadow g →
      abstractPeriodFaithfulness.context.EqMorph f g) →
        ClassicalGrothendieckPeriodFaithfulnessStatement classicalTarget

namespace ClassicalScalarFaithfulnessTransportData

/-- Scaffold scalar faithfulness transport, projected from an explicit assumption field. -/
def toClassicalFaithfulness
    {abstractPeriodFaithfulness : LayerD.AbstractPeriodFaithfulnessTheorem.{u, v, w}}
    {classicalTarget : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}}
    (transport : ClassicalScalarFaithfulnessTransportData abstractPeriodFaithfulness classicalTarget)
    (abstractFaithfulness :
      ∀ f g : abstractPeriodFaithfulness.context.Morph,
        abstractPeriodFaithfulness.context.ScalarShadow f =
          abstractPeriodFaithfulness.context.ScalarShadow g →
        abstractPeriodFaithfulness.context.EqMorph f g) :
    ClassicalGrothendieckPeriodFaithfulnessStatement classicalTarget :=
  transport.scalarFaithfulnessTransportAssumption abstractFaithfulness

end ClassicalScalarFaithfulnessTransportData

/-- Final middleware adapter from the internal trace-program package lane to the real classical
Grothendieck period-faithfulness target. The scalar target is stored, while the framed target is
constructed transparently from the structured scalar framed-period package. -/
structure InternalProgramRealizesClassicalPeriodTarget
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine) where
  sourceRealization : SourceRealizesClassicalMotivePresentation presentation aux
  structuredComparisonRealization : StructuredPackageRealizesClassicalComparison
  framedPeriodRealization : StructuredScalarPackageRealizesFramedPeriods
  targetInputs : ClassicalPeriodTargetInputsFromTraceProgram
  inputPackages : LayerD.PeriodFaithfulnessInputPackages.{u, v, w}
  abstractPeriodFaithfulness : LayerD.AbstractPeriodFaithfulnessTheorem.{u, v, w}
  classicalTarget : ClassicalGrothendieckPeriodFaithfulnessTarget
  reverseMathObligations : ClassicalPeriodReverseMathObligations
  primitiveFramedProbeFamily : ClassicalPeriods.ScalarProbeFamily classicalTarget.Context
  framedPeriodEquality : ClassicalPeriods.FramedPeriodEquality classicalTarget.Context
  framedPeriodOperations : ClassicalPeriods.FramedPeriodOperations classicalTarget.Context
  framedPeriodShadow : ScalarPeriodShadow (ClassicalPeriods.SomeFramedPeriodDatum classicalTarget.Context)
  framedShadowEquality :
    ScalarShadowEquality (ClassicalPeriods.SomeFramedPeriodDatum classicalTarget.Context) framedPeriodShadow
  framedScalarShadowAlgebra :
    ClassicalPeriods.FramedScalarShadowAlgebra
      classicalTarget.Context
      framedPeriodShadow
  framedPeriodOperationLaws :
    ClassicalPeriods.FramedPeriodOperationLaws
      classicalTarget.Context
      framedPeriodOperations
      framedPeriodShadow
      framedScalarShadowAlgebra
  framedPeriodOf :
    {X Y : classicalTarget.MotiveCategory} → (X ⟶ Y) →
      ClassicalPeriods.SomeFramedPeriodDatum classicalTarget.Context
  framedScalarToBaseScalar :
    framedPeriodShadow.ScalarCarrier →
      classicalTarget.scalarShadow.ScalarCarrier
  framedShadowToBaseShadowCompatible : Prop
  scalarShadow_agrees_with_framedShadow :
    ∀ {X Y : classicalTarget.MotiveCategory} (f : X ⟶ Y),
      classicalTarget.scalarShadow.equalityRelation
        (classicalTarget.scalarShadowOf f)
        (framedScalarToBaseScalar (framedPeriodShadow.shadowOf (framedPeriodOf f)))
  framedPeriodEqualityReflectsShadowEquality : Prop
  scalarShadowReflectsFramedEquality :
    ∀ {X Y : classicalTarget.MotiveCategory} (f g : X ⟶ Y),
      framedPeriodShadow.equalityRelation
        (framedPeriodShadow.shadowOf (framedPeriodOf f))
        (framedPeriodShadow.shadowOf (framedPeriodOf g)) →
      framedPeriodEquality.relates (framedPeriodOf f) (framedPeriodOf g)
  framedEqualityReflectsStructuredComparisonTarget :
    ∀ {X Y : classicalTarget.MotiveCategory} (f g : X ⟶ Y),
      framedPeriodShadow.equalityRelation
        (framedPeriodShadow.shadowOf (framedPeriodOf f))
        (framedPeriodShadow.shadowOf (framedPeriodOf g)) →
      classicalTarget.structuredComparisonEquality.relates
        (classicalTarget.packedMorphismComparison f)
        (classicalTarget.packedMorphismComparison g)
  primitiveProbeEqualityReflectsStructuredComparison :
    ∀ {X Y : classicalTarget.MotiveCategory} (f g : X ⟶ Y),
      ClassicalPeriods.ProbeEquality primitiveFramedProbeFamily
        (classicalTarget.packedMorphismComparison f)
        (classicalTarget.packedMorphismComparison g) →
      classicalTarget.structuredComparisonEquality.relates
        (classicalTarget.packedMorphismComparison f)
        (classicalTarget.packedMorphismComparison g)
  concreteFramedRealization : ConcreteFramedPeriodRealizationData classicalTarget
  concreteFramedRealization_framedPeriodEquality :
    concreteFramedRealization.framedPeriodEquality = framedPeriodEquality
  concreteFramedRealization_framedPeriodOf :
    ∀ {X Y : classicalTarget.MotiveCategory} (f : X ⟶ Y),
      concreteFramedRealization.framedPeriodOf f = framedPeriodOf f
  primitiveProbeRealization :
    PrimitiveProbeRealizesConcreteFramedPeriods
      classicalTarget
      concreteFramedRealization
      primitiveFramedProbeFamily
  BasisFreePeriodMapTransportData : Type (max u v w x y z)
  basisFreePeriodMapTransportData : BasisFreePeriodMapTransportData
  FramedPeriodTransportData : Type (max u v w x y z)
  framedPeriodTransportData : FramedPeriodTransportData
  sourcePackageRealizesClassicalPresentation : Prop
  basisFreePeriodMapRealization : Prop
  framedPeriodDatumRealization : Prop
  scalarShadowExtractionRealization : Prop
  scalarEqualityReflectsStructuredComparison : Prop
  framedEqualityReflectsStructuredComparison : Prop
  internalTargetPackageRealizesClassicalMotivicTarget : Prop
  internalStructuredScalarPackagesRealizeFramedPeriods : Prop
  scalarFaithfulnessTransportData :
    ClassicalScalarFaithfulnessTransportData abstractPeriodFaithfulness classicalTarget

namespace InternalProgramRealizesClassicalPeriodTarget

/-- The repaired classical framed target is constructed from the bridge's classical target and the
structured scalar framed-period package. Its framed equality is the classical framed-period
equality supplied by that package, not the primitive-probe equality. -/
def framedTarget
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : InternalProgramRealizesClassicalPeriodTarget presentation aux) :
    FramedPeriodConjectureTarget where
  baseTarget := bridge.classicalTarget
  framedPeriodEquality := bridge.framedPeriodEquality
  framedPeriodOperations := bridge.framedPeriodOperations
  framedPeriodShadow := bridge.framedPeriodShadow
  framedShadowEquality := bridge.framedShadowEquality
  framedScalarShadowAlgebra := bridge.framedScalarShadowAlgebra
  framedPeriodOperationLaws := bridge.framedPeriodOperationLaws
  framedPeriodOf := bridge.framedPeriodOf
  framedScalarToBaseScalar := bridge.framedScalarToBaseScalar
  framedShadowToBaseShadowCompatible := bridge.framedShadowToBaseShadowCompatible
  scalarShadow_agrees_with_framedShadow := bridge.scalarShadow_agrees_with_framedShadow
  framedPeriodEqualityReflectsShadowEquality := bridge.framedPeriodEqualityReflectsShadowEquality
  scalarShadowReflectsFramedEquality := bridge.scalarShadowReflectsFramedEquality
  framedToStructuredReflectionData := {
    framedRealizationData := bridge.framedEqualityReflectsStructuredComparison
    framedComparisonData := bridge.internalStructuredScalarPackagesRealizeFramedPeriods
    framedReconstructionData := bridge.internalTargetPackageRealizesClassicalMotivicTarget
    framedReflectionAssumption := bridge.framedEqualityReflectsStructuredComparisonTarget }

/-- Framed-period equality induced by the primitive concrete/geometric probe family carried by the
bridge. This is auxiliary: it is not the framed equality of `bridge.framedTarget`. -/
def primitiveProbeFramedPeriodEquality
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : InternalProgramRealizesClassicalPeriodTarget presentation aux) :
    ClassicalPeriods.FramedPeriodEquality bridge.framedTarget.baseTarget.Context where
  relates := fun left right =>
    ClassicalPeriods.ProbeEquality bridge.primitiveFramedProbeFamily
      left.structuredComparisonDatum
      right.structuredComparisonDatum
  reflexiveTarget :=
    ∀ datum : ClassicalPeriods.SomeFramedPeriodDatum bridge.framedTarget.baseTarget.Context,
      ClassicalPeriods.ProbeEquality bridge.primitiveFramedProbeFamily
        datum.structuredComparisonDatum
        datum.structuredComparisonDatum
  symmetricTarget :=
    ∀ left right : ClassicalPeriods.SomeFramedPeriodDatum bridge.framedTarget.baseTarget.Context,
      ClassicalPeriods.ProbeEquality bridge.primitiveFramedProbeFamily
        left.structuredComparisonDatum
        right.structuredComparisonDatum →
      ClassicalPeriods.ProbeEquality bridge.primitiveFramedProbeFamily
        right.structuredComparisonDatum
        left.structuredComparisonDatum
  transitiveTarget :=
    ∀ left middle right : ClassicalPeriods.SomeFramedPeriodDatum bridge.framedTarget.baseTarget.Context,
      ClassicalPeriods.ProbeEquality bridge.primitiveFramedProbeFamily
        left.structuredComparisonDatum
        middle.structuredComparisonDatum →
      ClassicalPeriods.ProbeEquality bridge.primitiveFramedProbeFamily
        middle.structuredComparisonDatum
        right.structuredComparisonDatum →
      ClassicalPeriods.ProbeEquality bridge.primitiveFramedProbeFamily
        left.structuredComparisonDatum
        right.structuredComparisonDatum

/-- Forward comparison target from classical framed equality to primitive-probe equality. -/
def classicalFramedPeriodEquality_iff_primitiveProbeFramedPeriodEquality
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : InternalProgramRealizesClassicalPeriodTarget presentation aux) : Prop :=
  ∀ {X Y : bridge.classicalTarget.MotiveCategory} (f g : X ⟶ Y),
    bridge.framedPeriodEquality.relates
      (bridge.framedPeriodOf f)
      (bridge.framedPeriodOf g) →
    bridge.primitiveProbeFramedPeriodEquality.relates
      (bridge.framedPeriodOf f)
      (bridge.framedPeriodOf g)

/-- Derived comparison from the concrete framed-period realization to primitive probe equality. -/
def classicalFramedEqualityInducesPrimitiveProbeEquality
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : InternalProgramRealizesClassicalPeriodTarget presentation aux) :
    ∀ {X Y : bridge.classicalTarget.MotiveCategory} (f g : X ⟶ Y),
      bridge.framedPeriodEquality.relates
        (bridge.framedPeriodOf f)
        (bridge.framedPeriodOf g) →
      ClassicalPeriods.ProbeEquality bridge.primitiveFramedProbeFamily
        (bridge.classicalTarget.packedMorphismComparison f)
        (bridge.classicalTarget.packedMorphismComparison g) := by
  intro X Y f g hClassical
  have hConcrete :
      bridge.concreteFramedRealization.framedPeriodEquality.relates
        (bridge.concreteFramedRealization.framedPeriodOf f)
        (bridge.concreteFramedRealization.framedPeriodOf g) := by
    simpa [bridge.concreteFramedRealization_framedPeriodEquality,
      bridge.concreteFramedRealization_framedPeriodOf f,
      bridge.concreteFramedRealization_framedPeriodOf g] using hClassical
  exact bridge.primitiveProbeRealization.probe_eq_of_framed_eq f g hConcrete

/-- Forward comparison from the repaired classical framed equality to primitive probe equality. -/
theorem classicalFramedPeriodEquality_to_primitiveProbeFramedPeriodEquality
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : InternalProgramRealizesClassicalPeriodTarget presentation aux) :
    bridge.classicalFramedPeriodEquality_iff_primitiveProbeFramedPeriodEquality := by
  intro X Y f g
  intro hClassical
  change ClassicalPeriods.ProbeEquality bridge.primitiveFramedProbeFamily
    (bridge.framedPeriodOf f).structuredComparisonDatum
    (bridge.framedPeriodOf g).structuredComparisonDatum
  have hLeft : (bridge.framedPeriodOf f).structuredComparisonDatum =
      bridge.classicalTarget.packedMorphismComparison f := by
    rw [← congrArg ClassicalPeriods.SomeFramedPeriodDatum.structuredComparisonDatum
      (bridge.concreteFramedRealization_framedPeriodOf f)]
    exact bridge.concreteFramedRealization.framedPeriodOf_realizes_comparison f
  have hRight : (bridge.framedPeriodOf g).structuredComparisonDatum =
      bridge.classicalTarget.packedMorphismComparison g := by
    rw [← congrArg ClassicalPeriods.SomeFramedPeriodDatum.structuredComparisonDatum
      (bridge.concreteFramedRealization_framedPeriodOf g)]
    exact bridge.concreteFramedRealization.framedPeriodOf_realizes_comparison g
  rw [hLeft, hRight]
  exact bridge.classicalFramedEqualityInducesPrimitiveProbeEquality f g hClassical

/-- Transparent projection of the framed period target already carried by the middleware bridge.

This exposes the constructed classical `FramedPeriodConjectureTarget`; the bridge no longer stores
an arbitrary opaque framed target. -/
def toFramedPeriodConjectureTarget
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : InternalProgramRealizesClassicalPeriodTarget presentation aux) :
    FramedPeriodConjectureTarget :=
  bridge.framedTarget

@[simp] theorem toFramedPeriodConjectureTarget_eq_framedTarget
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : InternalProgramRealizesClassicalPeriodTarget presentation aux) :
    bridge.toFramedPeriodConjectureTarget = bridge.framedTarget :=
  rfl

/-- The internal abstract faithfulness theorem suffices to produce the classical faithfulness
statement once the middleware transport slot is supplied. -/
def classicalFaithfulnessStatement
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : InternalProgramRealizesClassicalPeriodTarget presentation aux) :
    ClassicalGrothendieckPeriodFaithfulnessStatement bridge.classicalTarget :=
  bridge.scalarFaithfulnessTransportData.toClassicalFaithfulness
    bridge.abstractPeriodFaithfulness.scalarFaithful

/-- Rebuild the classical target through the explicit literal packed-comparison equality lane.

This does not assume faithfulness for an arbitrary `structuredComparisonEquality`: the equality
layer is fixed to `LayerD.literalPackedStructuredComparisonEquality`, and the only remaining
inputs are the two exact theorem surfaces needed by the final target package. -/
def classicalTargetOfLiteralPackedComparison
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : InternalProgramRealizesClassicalPeriodTarget presentation aux)
    (scalarShadowReflectsLiteralPackedComparison :
      ∀ {X Y : bridge.classicalTarget.MotiveCategory} (f g : X ⟶ Y),
        bridge.classicalTarget.scalarShadow.equalityRelation
          (bridge.classicalTarget.scalarShadowOf f)
          (bridge.classicalTarget.scalarShadowOf g) →
        bridge.classicalTarget.packedMorphismComparison f =
          bridge.classicalTarget.packedMorphismComparison g)
    (packedComparisonReflectsMorphismEquality :
      ∀ {X Y : bridge.classicalTarget.MotiveCategory} (f g : X ⟶ Y),
        bridge.classicalTarget.packedMorphismComparison f =
          bridge.classicalTarget.packedMorphismComparison g →
        f = g) :
    ClassicalGrothendieckPeriodFaithfulnessTarget where
  Context := bridge.classicalTarget.Context
  MotiveCategory := bridge.classicalTarget.MotiveCategory
  instMotiveCategory := bridge.classicalTarget.instMotiveCategory
  BettiCategory := bridge.classicalTarget.BettiCategory
  DeRhamCategory := bridge.classicalTarget.DeRhamCategory
  instBettiCategory := bridge.classicalTarget.instBettiCategory
  instDeRhamCategory := bridge.classicalTarget.instDeRhamCategory
  BettiRealization := bridge.classicalTarget.BettiRealization
  DeRhamRealization := bridge.classicalTarget.DeRhamRealization
  objectComparison := bridge.classicalTarget.objectComparison
  morphismStructuredComparison := bridge.classicalTarget.morphismStructuredComparison
  structuredComparisonEquality :=
    LayerD.literalPackedStructuredComparisonEquality bridge.classicalTarget.Context
  scalarShadow := bridge.classicalTarget.scalarShadow
  scalarShadowEquality := bridge.classicalTarget.scalarShadowEquality
  classicalPeriodEvaluationIsBasisFree :=
    bridge.classicalTarget.classicalPeriodEvaluationIsBasisFree
  bettiScalarExtensionFaithfulnessTarget :=
    bridge.classicalTarget.bettiScalarExtensionFaithfulnessTarget
  scalarToStructuredReflectionData := {
    scalarRealizationData :=
      bridge.classicalTarget.scalarToStructuredReflectionData.scalarRealizationData
    comparisonData := bridge.classicalTarget.scalarToStructuredReflectionData.comparisonData
    reconstructionData := bridge.classicalTarget.scalarToStructuredReflectionData.reconstructionData
    scalarReflectionAssumption := by
      intro X Y f g hScalar
      exact scalarShadowReflectsLiteralPackedComparison f g hScalar
  }
  packedComparisonReflectsMorphismEquality := by
    intro X Y f g hPacked
    exact packedComparisonReflectsMorphismEquality f g hPacked
  structuredComparisonFaithfulnessData := {
    classicalRecognitionData :=
      bridge.classicalTarget.structuredComparisonFaithfulnessData.classicalRecognitionData
    morphismReconstructionData :=
      bridge.classicalTarget.structuredComparisonFaithfulnessData.morphismReconstructionData
    structuredTransportData :=
      bridge.classicalTarget.structuredComparisonFaithfulnessData.structuredTransportData
    structuredFaithfulnessAssumption := by
      intro X Y f g hStructured
      exact packedComparisonReflectsMorphismEquality f g
        (LayerD.structuredComparisonEquality_to_packedComparison_eq hStructured)
  }

/-- The scalar exported theorem, routed through the explicitly constructed literal-packed target. -/
theorem classicalFaithfulnessStatement_ofLiteralPackedComparison
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : InternalProgramRealizesClassicalPeriodTarget presentation aux)
    (scalarShadowReflectsLiteralPackedComparison :
      ∀ {X Y : bridge.classicalTarget.MotiveCategory} (f g : X ⟶ Y),
        bridge.classicalTarget.scalarShadow.equalityRelation
          (bridge.classicalTarget.scalarShadowOf f)
          (bridge.classicalTarget.scalarShadowOf g) →
        bridge.classicalTarget.packedMorphismComparison f =
          bridge.classicalTarget.packedMorphismComparison g)
    (packedComparisonReflectsMorphismEquality :
      ∀ {X Y : bridge.classicalTarget.MotiveCategory} (f g : X ⟶ Y),
        bridge.classicalTarget.packedMorphismComparison f =
          bridge.classicalTarget.packedMorphismComparison g →
        f = g) :
    ClassicalGrothendieckPeriodFaithfulnessStatement
      (bridge.classicalTargetOfLiteralPackedComparison
        scalarShadowReflectsLiteralPackedComparison
        packedComparisonReflectsMorphismEquality) :=
      ClassicalPeriods.ClassicalGrothendieckPeriodFaithfulnessTarget.faithfulnessStatement_of_packedComparison
    (bridge.classicalTargetOfLiteralPackedComparison
      scalarShadowReflectsLiteralPackedComparison
      packedComparisonReflectsMorphismEquality)

/-- Rebuild the framed target through the explicit literal packed-comparison equality lane. -/
def framedTargetOfLiteralPackedComparison
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : InternalProgramRealizesClassicalPeriodTarget presentation aux)
    (scalarShadowReflectsLiteralPackedComparison :
      ∀ {X Y : bridge.classicalTarget.MotiveCategory} (f g : X ⟶ Y),
        bridge.classicalTarget.scalarShadow.equalityRelation
          (bridge.classicalTarget.scalarShadowOf f)
          (bridge.classicalTarget.scalarShadowOf g) →
        bridge.classicalTarget.packedMorphismComparison f =
          bridge.classicalTarget.packedMorphismComparison g)
    (packedComparisonReflectsMorphismEquality :
      ∀ {X Y : bridge.classicalTarget.MotiveCategory} (f g : X ⟶ Y),
        bridge.classicalTarget.packedMorphismComparison f =
          bridge.classicalTarget.packedMorphismComparison g →
        f = g)
    (framedShadowReflectsLiteralPackedComparison :
      ∀ {X Y : bridge.classicalTarget.MotiveCategory} (f g : X ⟶ Y),
        bridge.framedPeriodShadow.equalityRelation
          (bridge.framedPeriodShadow.shadowOf (bridge.framedPeriodOf f))
          (bridge.framedPeriodShadow.shadowOf (bridge.framedPeriodOf g)) →
        bridge.classicalTarget.packedMorphismComparison f =
          bridge.classicalTarget.packedMorphismComparison g) :
    FramedPeriodConjectureTarget where
  baseTarget := bridge.classicalTargetOfLiteralPackedComparison
    scalarShadowReflectsLiteralPackedComparison
    packedComparisonReflectsMorphismEquality
  framedPeriodEquality := bridge.framedPeriodEquality
  framedPeriodOperations := bridge.framedPeriodOperations
  framedPeriodShadow := bridge.framedPeriodShadow
  framedShadowEquality := bridge.framedShadowEquality
  framedScalarShadowAlgebra := bridge.framedScalarShadowAlgebra
  framedPeriodOperationLaws := bridge.framedPeriodOperationLaws
  framedPeriodOf := bridge.framedPeriodOf
  framedScalarToBaseScalar := bridge.framedScalarToBaseScalar
  framedShadowToBaseShadowCompatible := bridge.framedShadowToBaseShadowCompatible
  scalarShadow_agrees_with_framedShadow := bridge.scalarShadow_agrees_with_framedShadow
  framedPeriodEqualityReflectsShadowEquality := bridge.framedPeriodEqualityReflectsShadowEquality
  scalarShadowReflectsFramedEquality := bridge.scalarShadowReflectsFramedEquality
  framedToStructuredReflectionData := {
    framedRealizationData := bridge.framedEqualityReflectsStructuredComparison
    framedComparisonData := bridge.internalStructuredScalarPackagesRealizeFramedPeriods
    framedReconstructionData := bridge.internalTargetPackageRealizesClassicalMotivicTarget
    framedReflectionAssumption := by
      intro X Y f g hFramed
      exact framedShadowReflectsLiteralPackedComparison f g hFramed
  }

/-- The framed exported theorem, routed through the explicitly constructed literal-packed target. -/
theorem framedFaithfulnessStatement_ofLiteralPackedComparison
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (bridge : InternalProgramRealizesClassicalPeriodTarget presentation aux)
    (scalarShadowReflectsLiteralPackedComparison :
      ∀ {X Y : bridge.classicalTarget.MotiveCategory} (f g : X ⟶ Y),
        bridge.classicalTarget.scalarShadow.equalityRelation
          (bridge.classicalTarget.scalarShadowOf f)
          (bridge.classicalTarget.scalarShadowOf g) →
        bridge.classicalTarget.packedMorphismComparison f =
          bridge.classicalTarget.packedMorphismComparison g)
    (packedComparisonReflectsMorphismEquality :
      ∀ {X Y : bridge.classicalTarget.MotiveCategory} (f g : X ⟶ Y),
        bridge.classicalTarget.packedMorphismComparison f =
          bridge.classicalTarget.packedMorphismComparison g →
        f = g)
    (framedShadowReflectsLiteralPackedComparison :
      ∀ {X Y : bridge.classicalTarget.MotiveCategory} (f g : X ⟶ Y),
        bridge.framedPeriodShadow.equalityRelation
          (bridge.framedPeriodShadow.shadowOf (bridge.framedPeriodOf f))
          (bridge.framedPeriodShadow.shadowOf (bridge.framedPeriodOf g)) →
        bridge.classicalTarget.packedMorphismComparison f =
          bridge.classicalTarget.packedMorphismComparison g) :
    ClassicalFramedPeriodConjectureStatement
      (bridge.framedTargetOfLiteralPackedComparison
        scalarShadowReflectsLiteralPackedComparison
        packedComparisonReflectsMorphismEquality
        framedShadowReflectsLiteralPackedComparison) :=
  ClassicalPeriods.FramedPeriodConjectureTarget.faithfulnessStatement_of_reflection
    (bridge.framedTargetOfLiteralPackedComparison
      scalarShadowReflectsLiteralPackedComparison
      packedComparisonReflectsMorphismEquality
      framedShadowReflectsLiteralPackedComparison)

end InternalProgramRealizesClassicalPeriodTarget

/-- Final bridge-obligation record sitting between the internal theorem packages and the real
classical targets. This records the remaining theorem targets needed to transport internal source,
target, structured, scalar, and faithfulness data to the ClassicalPeriods lane. -/
structure ClassicalPeriodTargetBridgeObligations
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    (aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine) where
  programRealization : InternalProgramRealizesClassicalPeriodTarget presentation aux
  BridgeTransportData : Type (max u v w x y z)
  bridgeTransportData : BridgeTransportData
  sourceRealizationCompatibility : Prop
  basisFreePeriodMapCompatibility : Prop
  framedPeriodDatumCompatibility : Prop
  scalarShadowExtractionCompatibility : Prop
  scalarEqualityReflectionCompatibility : Prop
  framedEqualityReflectionCompatibility : Prop
  classicalTargetFeedsFramedTarget :
    ClassicalGrothendieckPeriodFaithfulnessStatement
        programRealization.classicalTarget →
      ClassicalFramedPeriodConjectureStatement
        programRealization.framedTarget

namespace ClassicalPeriodTargetBridgeObligations

/-- The middleware target consequence obtained from the internal abstract faithfulness theorem. -/
def classicalConjectureOfInternalFaithfulness
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (obligations : ClassicalPeriodTargetBridgeObligations presentation aux) :
  ClassicalGrothendieckPeriodFaithfulnessStatement
      obligations.programRealization.classicalTarget :=
  obligations.programRealization.classicalFaithfulnessStatement

/-- Framed-period consequence obtained once the classical-target transport and framed-target
transport slots are both supplied. -/
def framedConjectureOfInternalFaithfulness
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (obligations : ClassicalPeriodTargetBridgeObligations presentation aux) :
  ClassicalFramedPeriodConjectureStatement obligations.programRealization.framedTarget :=
  obligations.classicalTargetFeedsFramedTarget obligations.classicalConjectureOfInternalFaithfulness

/-- The remaining bridge goal is precisely the transport from the internal abstract theorem to the
real classical target and then on to the framed refinement. -/
def remainingGoal
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (obligations : ClassicalPeriodTargetBridgeObligations presentation aux) : Prop :=
  ClassicalGrothendieckPeriodFaithfulnessStatement
      obligations.programRealization.classicalTarget ∧
    ClassicalFramedPeriodConjectureStatement obligations.programRealization.framedTarget

theorem remainingGoal_holds
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    {presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive}
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (obligations : ClassicalPeriodTargetBridgeObligations presentation aux) :
    obligations.remainingGoal :=
  ⟨obligations.classicalConjectureOfInternalFaithfulness,
    obligations.framedConjectureOfInternalFaithfulness⟩

end ClassicalPeriodTargetBridgeObligations

end ClassicalBridge
end TraceCalc