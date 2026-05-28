import TraceCalc.ClassicalBridge.RecognizedMMQFramedPeriodSystem
import TraceCalc.ClassicalPeriods.Reflection

universe u v w x y z

namespace TraceCalc
namespace ClassicalBridge

open ClassicalPeriods
open MotivicRecognition
open LayerB.RealObjects

/-- Assumption-free recognized-`MM(Q)` period target skeleton.

This layer contains only canonical data already supplied by the recognized `MM(Q)` realization
system and the recognized framed-period system. Any remaining period-conjecture work is exposed
below as explicit theorem-obligation targets rather than as hidden assumptions on the data bundle.
-/
structure RecognizedMMQPeriodTargetSkeleton
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : LayerB.RealObjects.RewriteCalculusSetup.SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α}
    {C : LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (normalization : NormalizationPackageTarget internal)
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence)
    (transportedNormalization :
      TransportedNormalizationIsMotivicTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence normalizationTransport)
    (normTStructure : NormTStructureTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalization)
    (heartRecognition : HeartRecognitionTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalization normTStructure) where
  framedSystem :
    RecognizedMMQFramedPeriodSystem spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition
  probeIndex : Type z
  frameIndexOf :
    {M N : framedSystem.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ} →
      framedSystem.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom
        M N →
        Type z
  frameOfProbe :
    {M N : framedSystem.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ} →
      (f : framedSystem.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom
        M N) →
        probeIndex → frameIndexOf f
  framedPeriodOf :
    {M N : framedSystem.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ} →
      (f : framedSystem.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom
        M N) →
        frameIndexOf f →
          FramedPeriodDatum ctx (framedSystem.realizationSystem.pairingDataOf f)

namespace RecognizedMMQPeriodTargetSkeleton

/-- Canonical constructor of the recognized period target skeleton from an
explicit recognized framed-period system. -/
def ofFramedSystem
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : LayerB.RealObjects.RewriteCalculusSetup.SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α}
    {C : LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {normalization : NormalizationPackageTarget internal}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    {comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical}
    {canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence}
    {normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence}
    {transportedNormalization :
      TransportedNormalizationIsMotivicTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence normalizationTransport}
    {normTStructure : NormTStructureTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalization}
    {heartRecognition : HeartRecognitionTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalization normTStructure}
    (framedSystem :
      RecognizedMMQFramedPeriodSystem spine internal normalization classical
        comparisonEquivalence canonicalEquivalence normalizationTransport
        transportedNormalization normTStructure heartRecognition) :
    RecognizedMMQPeriodTargetSkeleton spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition := by
  cases framedSystem with
  | mk realizationSystem probeIndex frameIndexOf frameOfProbe framedPeriodOf =>
      exact
        { framedSystem :=
            { realizationSystem := realizationSystem
              ProbeIndex := probeIndex
              FrameIndexOf := frameIndexOf
              frameOfProbe := frameOfProbe
              framedPeriodOf := framedPeriodOf }
          probeIndex := probeIndex
          frameIndexOf := frameIndexOf
          frameOfProbe := frameOfProbe
          framedPeriodOf := framedPeriodOf }

variable
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : LayerB.RealObjects.RewriteCalculusSetup.SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α}
    {C : LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {normalization : NormalizationPackageTarget internal}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    {comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical}
    {canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence}
    {normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence}
    {transportedNormalization :
      TransportedNormalizationIsMotivicTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence normalizationTransport}
    {normTStructure : NormTStructureTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalization}
    {heartRecognition : HeartRecognitionTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalization normTStructure}

def realizationSystem
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :
    RecognizedMMQRealizationSystem spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition :=
  target.framedSystem.realizationSystem

def mmqIdentification
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :=
  target.realizationSystem.mmqIdentification

abbrev MixedMotivesQ
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) : Type y :=
  target.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ

abbrev MixedMotivesQHom
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (M N : target.MixedMotivesQ) : Type z :=
  target.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N

/-- Canonical replacement for the old `scalarRealizationData` scaffold field. -/
def scalarRealizationData
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :
    PeriodRealizationPackage ctx :=
  target.realizationSystem.structuredComparisonPackage.periodPackage

/-- Canonical replacement for the old `comparisonData` scaffold field. -/
def comparisonData
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :
    StructuredComparisonPackage ctx :=
  target.realizationSystem.structuredComparisonPackage

/-- Canonical replacement for the old `classicalRecognitionData` scaffold field. -/
def classicalRecognitionData
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :=
  target.mmqIdentification

/-- Canonical replacement for the old `structuredTransportData` scaffold field. -/
def structuredTransportData
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :
    RecognizedMMQRealizationSystem spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition :=
  target.realizationSystem

/-- Canonical framed-period data source for the recognized `MM(Q)` lane. -/
def framedPeriodData
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :
    RecognizedMMQFramedPeriodSystem spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition :=
  target.framedSystem

def objectComparisonOf
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (M : target.MixedMotivesQ) :
    ClassicalStructuredComparisonObject ctx :=
  target.realizationSystem.objectComparisonOf M

def morphismComparisonOf
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    {M N : target.MixedMotivesQ}
    (f : target.MixedMotivesQHom M N) :
    ClassicalStructuredComparisonMorphism ctx (target.objectComparisonOf M)
      (target.objectComparisonOf N) :=
  target.realizationSystem.morphismComparisonOf f

def packedMorphismComparisonOf
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    {M N : target.MixedMotivesQ}
    (f : target.MixedMotivesQHom M N) :
    SomeStructuredComparisonMorphism ctx :=
  packStructuredComparisonMorphism
    (target.objectComparisonOf M)
    (target.objectComparisonOf N)
    (target.morphismComparisonOf f)

def pairingDataOf
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    {M N : target.MixedMotivesQ}
    (f : target.MixedMotivesQHom M N) :
    PeriodPairingData ctx (target.morphismComparisonOf f) :=
  target.realizationSystem.pairingDataOf f

abbrev FrameIndexOf
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    {M N : target.MixedMotivesQ}
    (f : target.MixedMotivesQHom M N) : Type z :=
  target.frameIndexOf f

abbrev ProbeIndex
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) : Type z :=
  target.probeIndex

def someFramedPeriodOf
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    {M N : target.MixedMotivesQ}
    (f : target.MixedMotivesQHom M N)
    (frame : target.FrameIndexOf f) :
    SomeFramedPeriodDatum ctx :=
  ⟨target.objectComparisonOf M, target.objectComparisonOf N,
    target.morphismComparisonOf f, target.pairingDataOf f, target.framedPeriodOf f frame⟩

def framedPeriodShadow
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :
    ScalarPeriodShadow (SomeFramedPeriodDatum ctx) :=
  RecognizedMMQFramedPeriodSystem.framedPeriodShadow target.framedSystem

def framedShadowEquality
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :
    ScalarShadowEquality (SomeFramedPeriodDatum ctx) target.framedPeriodShadow :=
  RecognizedMMQFramedPeriodSystem.framedShadowEquality target.framedSystem

def framedShadowAlgebra
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :
    FramedScalarShadowAlgebra ctx target.framedPeriodShadow :=
  RecognizedMMQFramedPeriodSystem.framedShadowAlgebra target.framedSystem

def framedShadowOf
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    {M N : target.MixedMotivesQ}
    (f : target.MixedMotivesQHom M N)
    (frame : target.FrameIndexOf f) :
    ctx.ScalarField :=
  (target.framedPeriodOf f frame).scalarValue

def framedCoordinateFamilyOf
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    {M N : target.MixedMotivesQ}
    (f : target.MixedMotivesQHom M N) : target.ProbeIndex → ctx.ScalarField :=
  fun probe => (target.framedPeriodOf f (target.frameOfProbe f probe)).scalarValue

/-- Remaining reconstruction target replacing the old `reconstructionData` scaffold field. -/
def reconstructionDataTarget
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) : Prop :=
  ∀ {M N : target.MixedMotivesQ} (f g : target.MixedMotivesQHom M N),
    (target.morphismComparisonOf f).basisFreePeriodMap =
        (target.morphismComparisonOf g).basisFreePeriodMap →
      target.packedMorphismComparisonOf f = target.packedMorphismComparisonOf g

/-- Remaining reconstruction target replacing the old `morphismReconstructionData` scaffold field.
-/
def morphismReconstructionDataTarget
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) : Prop :=
  ∀ {M N : target.MixedMotivesQ} (f g : target.MixedMotivesQHom M N),
    target.packedMorphismComparisonOf f = target.packedMorphismComparisonOf g →
      f = g

/-- Remaining faithfulness target replacing the old `structuredFaithfulnessAssumption` field. -/
def structuredFaithfulnessTarget
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) : Prop :=
  ∀ {M N : target.MixedMotivesQ} (f g : target.MixedMotivesQHom M N),
    structuredEq.relates
      (target.packedMorphismComparisonOf f)
      (target.packedMorphismComparisonOf g) →
      f = g

/-- Remaining framed-reflection target replacing the old `framedReflectionAssumption` field. -/
def framedReflectionTarget
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) : Prop :=
  ∀ {M N : target.MixedMotivesQ}
    (f g : target.MixedMotivesQHom M N),
      (∀ probe : target.ProbeIndex,
          target.framedCoordinateFamilyOf f probe = target.framedCoordinateFamilyOf g probe) →
      structuredEq.relates
        (target.packedMorphismComparisonOf f)
        (target.packedMorphismComparisonOf g)

/-- Exact theorem target for the remaining basis-free evaluation obligation. -/
def classicalPeriodEvaluationIsBasisFreeTarget
    (periodEvaluation : SomeStructuredComparisonMorphism ctx → ctx.ScalarField)
    (basisFreeEquality : BasisFreePeriodMapEquality ctx) : Prop :=
  ∀ left right : SomeStructuredComparisonMorphism ctx,
    basisFreeEquality.relates left right →
      periodEvaluation left = periodEvaluation right

/-- Exact theorem target for the remaining scalar-extension faithfulness obligation. -/
def bettiScalarExtensionFaithfulnessTarget
    (scalarShadow : ScalarPeriodShadow (SomeStructuredComparisonMorphism ctx)) : Prop :=
  ∀ left right : SomeStructuredComparisonMorphism ctx,
    scalarShadow.equalityRelation (scalarShadow.shadowOf left) (scalarShadow.shadowOf right) →
      left = right

/-- Exact theorem target replacing the old `scalarReflectionAssumption` field. -/
def scalarReflectionTarget
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (scalarShadow : ScalarPeriodShadow (SomeStructuredComparisonMorphism ctx)) : Prop :=
  ∀ {M N : target.MixedMotivesQ} (f g : target.MixedMotivesQHom M N),
    scalarShadow.equalityRelation
      (scalarShadow.shadowOf (target.packedMorphismComparisonOf f))
      (scalarShadow.shadowOf (target.packedMorphismComparisonOf g)) →
    structuredEq.relates
      (target.packedMorphismComparisonOf f)
      (target.packedMorphismComparisonOf g)

/-- Named obligation for the remaining basis-free evaluation theorem. -/
structure RecognizedMMQBasisFreeEvaluationObligation where
  periodEvaluation : SomeStructuredComparisonMorphism ctx → ctx.ScalarField
  basisFreeEquality : BasisFreePeriodMapEquality ctx
  theoremTarget :
    classicalPeriodEvaluationIsBasisFreeTarget periodEvaluation basisFreeEquality

/-- Named obligation for the remaining scalar-extension faithfulness theorem. -/
structure RecognizedMMQBettiScalarExtensionFaithfulnessObligation where
  scalarShadow : ScalarPeriodShadow (SomeStructuredComparisonMorphism ctx)
  theoremTarget : bettiScalarExtensionFaithfulnessTarget scalarShadow

/-- Named obligation for the remaining reconstruction theorem below structured equality. -/
structure RecognizedMMQReconstructionObligation
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  theoremTarget : target.reconstructionDataTarget

/-- Named obligation for the remaining morphism-reconstruction theorem. -/
structure RecognizedMMQMorphismReconstructionObligation
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  theoremTarget : target.morphismReconstructionDataTarget

/-- Named obligation for the remaining scalar-reflection theorem. -/
structure RecognizedMMQScalarReflectionObligation
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  scalarShadow : ScalarPeriodShadow (SomeStructuredComparisonMorphism ctx)
  scalarShadowEquality : ScalarShadowEquality (SomeStructuredComparisonMorphism ctx) scalarShadow
  theoremTarget : target.scalarReflectionTarget scalarShadow

/-- Named obligation for the remaining structured-faithfulness theorem. -/
structure RecognizedMMQStructuredFaithfulnessObligation
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  theoremTarget : target.structuredFaithfulnessTarget

/-- Named obligation for the remaining framed-reflection theorem. -/
structure RecognizedMMQFramedReflectionObligation
    (target : RecognizedMMQPeriodTargetSkeleton spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  theoremTarget : target.framedReflectionTarget

end RecognizedMMQPeriodTargetSkeleton

end ClassicalBridge
end TraceCalc