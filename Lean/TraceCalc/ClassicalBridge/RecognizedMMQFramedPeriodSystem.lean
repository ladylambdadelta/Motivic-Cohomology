import TraceCalc.ClassicalBridge.RecognizedMMQRealizationSystem
import TraceCalc.ClassicalPeriods.Tomography
import TraceCalc.LayerD.ConcretePeriodFaithfulness

universe u v w x y z

namespace TraceCalc
namespace ClassicalBridge

open ClassicalPeriods
open MotivicRecognition
open LayerB.RealObjects

/-- Pure framed-period data specialized to the recognized manuscript-facing `MM(Q)` endpoint.

This stays strictly below any reflection or faithfulness theorem target. It assigns framed period
data to recognized `MM(Q)` morphisms, packages that data into the existing sigma-based framed
period surface, and exposes the canonical scalar shadow induced by framed periods. -/
structure RecognizedMMQFramedPeriodSystem
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
  realizationSystem :
    RecognizedMMQRealizationSystem spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition
  ProbeIndex : Type z
  FrameIndexOf :
    {M N : realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ} →
      realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N →
        Type z
  frameOfProbe :
    {M N : realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ} →
      (f : realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N) →
        ProbeIndex → FrameIndexOf f
  framedPeriodOf :
    {M N : realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ} →
      (f : realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N) →
        FrameIndexOf f → FramedPeriodDatum ctx (realizationSystem.pairingDataOf f)

namespace RecognizedMMQFramedPeriodSystem

/-- Canonical constructor input for the recognized framed-period system.

This records the additional frame-indexed data needed on top of a concrete
recognized realization system. -/
structure CanonicalInput
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
  realizationSystem :
    RecognizedMMQRealizationSystem spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition
  ProbeIndex : Type z
  FrameIndexOf :
    {M N : realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ} →
      realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N →
        Type z
  frameOfProbe :
    {M N : realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ} →
      (f : realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N) →
        ProbeIndex → FrameIndexOf f
  framedPeriodOf :
    {M N : realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ} →
      (f : realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N) →
        FrameIndexOf f → FramedPeriodDatum ctx (realizationSystem.pairingDataOf f)

/-- Build the recognized framed-period system from explicit canonical input
data. -/
def ofCanonicalInput
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
    (input : CanonicalInput spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition) :
    RecognizedMMQFramedPeriodSystem spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition where
  realizationSystem := input.realizationSystem
  ProbeIndex := input.ProbeIndex
  FrameIndexOf := input.FrameIndexOf
  frameOfProbe := input.frameOfProbe
  framedPeriodOf := input.framedPeriodOf

 /-- The full framed-coordinate family attached to one recognized `MM(Q)`
morphism. This is the period table indexed by the canonical admissible frame
family for that morphism. -/
def FramedCoordinateFamily
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    {M N : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
    (f : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N) :=
  system.ProbeIndex → ctx.ScalarField

/-- The canonical framed-coordinate family extracted from the recognized
framed-period system. -/
def framedCoordinateFamilyOf
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    {M N : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
    (f : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N) :
    FramedCoordinateFamily system f :=
  fun probe => (system.framedPeriodOf f (system.frameOfProbe f probe)).scalarValue

/-- Exact scalar-encoding completeness target for the recognized
framed/period-coordinate system: equality of the chosen scalar shadow on packed
comparison morphisms forces agreement of the full canonical framed coordinate
family.

This is intentionally stronger than the canonical framed shadow of a single
`SomeFramedPeriodDatum`, which only extracts one scalar coordinate
`datum.framedDatum.scalarValue`. Therefore this target should be read as a
codec/completeness theorem for the selected structured-comparison scalar shadow,
unless that shadow is itself defined to encode the whole framed family. It
isolates the first implication in the period-conjecture normal form. -/
def framedCoordinateFamilyAgreementTarget
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) : Prop :=
  ∀ {M N : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
    (f g : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N),
      ∀ probe : system.ProbeIndex,
        framedCoordinateFamilyOf system f probe = framedCoordinateFamilyOf system g probe

def scalarEncodingCompletenessTarget
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (scalarShadow : ScalarPeriodShadow (SomeStructuredComparisonMorphism ctx)) : Prop :=
  ∀ {M N : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
    (f g : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N),
      scalarShadow.equalityRelation
        (scalarShadow.shadowOf (system.realizationSystem.packedMorphismComparisonOf f))
        (scalarShadow.shadowOf (system.realizationSystem.packedMorphismComparisonOf g)) →
      ∀ probe : system.ProbeIndex,
        framedCoordinateFamilyOf system f probe = framedCoordinateFamilyOf system g probe

/-- A scalar codec for the full framed-coordinate family on the recognized
image.

This is the canonical scalar-period abstraction for the recognized bridge: the
shadow is attached to packed comparison morphisms, but it is intended to encode
the entire framed matrix-coefficient family, not one bare scalar sample. The
`encodingComplete` field is the exact codec injectivity/completeness theorem
that turns equality of shadow codes back into agreement of all framed
coordinates. -/
structure ScalarShadowCodec
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
      transportedNormalization normTStructure)
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  scalarShadow : ScalarPeriodShadow (SomeStructuredComparisonMorphism ctx)
  scalarShadowEquality :
    ScalarShadowEquality (SomeStructuredComparisonMorphism ctx) scalarShadow
  decodeFamily :
    {M N : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ} →
      (f : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N) →
        scalarShadow.ScalarCarrier → FramedCoordinateFamily system f
  decodeFamily_of_shadow :
    ∀ {M N : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
      (f : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N),
        decodeFamily f
            (scalarShadow.shadowOf (system.realizationSystem.packedMorphismComparisonOf f)) =
          framedCoordinateFamilyOf system f
  encodingComplete : scalarEncodingCompletenessTarget system scalarShadow

/-- The framed coordinate family factors through packed comparison on the
recognized image. This is the exact coherence theorem needed to build a scalar
codec from packed comparison data alone: any two recognized morphisms with the
same packed comparison have the same full probe-indexed family. -/
def framedCoordinateFactorsThroughPackedComparisonTarget
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) : Prop :=
  ∀ {M N : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
      (f : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N)
      {M' N' : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
      (g : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M' N'),
      system.realizationSystem.packedMorphismComparisonOf f =
          system.realizationSystem.packedMorphismComparisonOf g →
        ∀ probe : system.ProbeIndex,
          framedCoordinateFamilyOf system f probe = framedCoordinateFamilyOf system g probe

/-- Mathematical name for the first remaining input: framed coordinates are
coordinates of the packed comparison morphism, so the full probe family factors
through packed comparison on the recognized image. -/
abbrev recognizedFramedCoordinateFactorization
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :=
  framedCoordinateFactorsThroughPackedComparisonTarget system

/-- Witness that a packed comparison morphism lies in the recognized image of
the framed-period system. -/
def PackedComparisonWitness
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (packed : SomeStructuredComparisonMorphism ctx) :=
  Σ (M : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ),
    Σ (N : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ),
      {f : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N //
        system.realizationSystem.packedMorphismComparisonOf f = packed}

/-- Canonical family code of a packed comparison morphism, defined whenever the
packed morphism lies in the recognized image. Off the recognized image the code
is `none`. -/
noncomputable def familyCodeOfPackedComparison
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (packed : SomeStructuredComparisonMorphism ctx) : Option (system.ProbeIndex → ctx.ScalarField) := by
  classical
  by_cases h : Nonempty (PackedComparisonWitness system packed)
  · let witness := Classical.choice h
    exact some (framedCoordinateFamilyOf system witness.2.2.1)
  · exact none

set_option maxHeartbeats 800000

/-- Build the scalar codec directly from the theorem that the full framed
coordinate family factors through packed comparison. This is the canonical
recognized-image codec: the shadow stores an optional serialized family code,
present exactly on packed comparisons coming from recognized morphisms. -/
noncomputable def ScalarShadowCodec.ofFramedCoordinateFactorization
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (factorization : framedCoordinateFactorsThroughPackedComparisonTarget system) :
    ScalarShadowCodec spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition system := by
  set_option maxHeartbeats 800000 in
  classical
  let scalarShadow : ScalarPeriodShadow (SomeStructuredComparisonMorphism ctx) :=
    { ScalarCarrier := Option (system.ProbeIndex → ctx.ScalarField)
      shadowOf := familyCodeOfPackedComparison system
      equalityRelation := fun left right => left = right
      ShadowTransportData := PUnit
      shadowTransportData := PUnit.unit
      scalarExtractionSound := ∀ code : Option (system.ProbeIndex → ctx.ScalarField), code = code
      equalityCompatibleWithExtraction :=
        ∀ codeLeft codeRight : Option (system.ProbeIndex → ctx.ScalarField),
          codeLeft = codeRight ↔ codeLeft = codeRight }
  let decodeFamily :
      {M N : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ} →
        (f : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N) →
          scalarShadow.ScalarCarrier → FramedCoordinateFamily system f := by
    intro M N f code
    exact Option.getD code (framedCoordinateFamilyOf system f)
  refine
    { scalarShadow := scalarShadow
      scalarShadowEquality :=
        { reflexiveTarget := ∀ code : Option (system.ProbeIndex → ctx.ScalarField), code = code
          symmetricTarget :=
            ∀ codeLeft codeRight : Option (system.ProbeIndex → ctx.ScalarField),
              codeLeft = codeRight → codeRight = codeLeft
          transitiveTarget :=
            ∀ codeLeft codeMiddle codeRight : Option (system.ProbeIndex → ctx.ScalarField),
              codeLeft = codeMiddle → codeMiddle = codeRight → codeLeft = codeRight }
      decodeFamily := decodeFamily
      decodeFamily_of_shadow := ?_
      encodingComplete := ?_ }
  · intro M N f
    let packed := system.realizationSystem.packedMorphismComparisonOf f
    let witness : PackedComparisonWitness system packed := ⟨M, ⟨N, ⟨f, rfl⟩⟩⟩
    have hWitness : Nonempty (PackedComparisonWitness system packed) := ⟨witness⟩
    simp [decodeFamily, scalarShadow, familyCodeOfPackedComparison, hWitness, Option.getD]
    change framedCoordinateFamilyOf system (Classical.choice hWitness).2.2.1 =
        framedCoordinateFamilyOf system f
    exact funext
      (factorization (Classical.choice hWitness).2.2.1 f
        ((Classical.choice hWitness).2.2.2.trans rfl))
  · intro M N f g hCode probe
    have hf :=
      (show decodeFamily f (scalarShadow.shadowOf (system.realizationSystem.packedMorphismComparisonOf f)) =
          framedCoordinateFamilyOf system f from by
        unfold decodeFamily scalarShadow familyCodeOfPackedComparison
        let witness : PackedComparisonWitness system
            (system.realizationSystem.packedMorphismComparisonOf f) := ⟨M, ⟨N, ⟨f, rfl⟩⟩⟩
        have hWitness : Nonempty
            (PackedComparisonWitness system (system.realizationSystem.packedMorphismComparisonOf f)) :=
          ⟨witness⟩
        simp [hWitness, Option.getD]
        let chosen : PackedComparisonWitness system (system.realizationSystem.packedMorphismComparisonOf f) :=
          Classical.choice hWitness
        funext p
        exact factorization chosen.2.2.1 f (chosen.2.2.2.trans rfl) p)
    have hg :=
      (show decodeFamily g (scalarShadow.shadowOf (system.realizationSystem.packedMorphismComparisonOf g)) =
          framedCoordinateFamilyOf system g from by
        let witness : PackedComparisonWitness system
            (system.realizationSystem.packedMorphismComparisonOf g) := ⟨M, ⟨N, ⟨g, rfl⟩⟩⟩
        have hWitness : Nonempty
            (PackedComparisonWitness system (system.realizationSystem.packedMorphismComparisonOf g)) :=
          ⟨witness⟩
        simp [decodeFamily, scalarShadow, familyCodeOfPackedComparison, hWitness, Option.getD]
        let chosen : PackedComparisonWitness system (system.realizationSystem.packedMorphismComparisonOf g) :=
          Classical.choice hWitness
        funext p
        exact factorization chosen.2.2.1 g (chosen.2.2.2.trans rfl) p)
    let codeF := scalarShadow.shadowOf (system.realizationSystem.packedMorphismComparisonOf f)
    have hCodeSome : ∃ family : system.ProbeIndex → ctx.ScalarField, codeF = some family := by
      let witness : PackedComparisonWitness system
          (system.realizationSystem.packedMorphismComparisonOf f) := ⟨M, ⟨N, ⟨f, rfl⟩⟩⟩
      have hWitness : Nonempty
          (PackedComparisonWitness system (system.realizationSystem.packedMorphismComparisonOf f)) :=
        ⟨witness⟩
      refine ⟨framedCoordinateFamilyOf system witness.2.2.1, ?_⟩
      simp [codeF, scalarShadow, familyCodeOfPackedComparison, hWitness]
      change framedCoordinateFamilyOf system (Classical.choice hWitness).2.2.1 =
          framedCoordinateFamilyOf system f
      exact funext
        (factorization (Classical.choice hWitness).2.2.1 f
          ((Classical.choice hWitness).2.2.2.trans rfl))
    rcases hCodeSome with ⟨family, hFamily⟩
    have hFamilyG :
        scalarShadow.shadowOf (system.realizationSystem.packedMorphismComparisonOf g) = some family := by
      exact hCode.symm.trans hFamily
    have hf' : family = framedCoordinateFamilyOf system f := by
      calc
        family = decodeFamily f (some family) := by simp [decodeFamily]
        _ = decodeFamily f (scalarShadow.shadowOf (system.realizationSystem.packedMorphismComparisonOf f)) := by
          simpa [codeF] using congrArg (decodeFamily f) hFamily.symm
        _ = framedCoordinateFamilyOf system f := hf
    have hg' : family = framedCoordinateFamilyOf system g := by
      calc
        family = decodeFamily g (some family) := by simp [decodeFamily]
        _ = decodeFamily g (scalarShadow.shadowOf (system.realizationSystem.packedMorphismComparisonOf g)) := by
          simpa using congrArg (decodeFamily g) hFamilyG.symm
        _ = framedCoordinateFamilyOf system g := hg
    calc
      framedCoordinateFamilyOf system f probe = family probe := by
        exact (congrFun hf'.symm probe)
      _ = framedCoordinateFamilyOf system g probe := by
        exact (congrFun hg' probe)

set_option maxHeartbeats 200000

/-- Exact scalar-separation target for the recognized framed/period-coordinate
system: equality of scalar shadows on packed comparison morphisms determines
literal packed comparison equality on the recognized image. -/
def scalarSeparationTarget
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (scalarShadow : ScalarPeriodShadow (SomeStructuredComparisonMorphism ctx)) : Prop :=
  ∀ {M N : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
    (f g : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N),
      scalarShadow.equalityRelation
        (scalarShadow.shadowOf (system.realizationSystem.packedMorphismComparisonOf f))
        (scalarShadow.shadowOf (system.realizationSystem.packedMorphismComparisonOf g)) →
      system.realizationSystem.packedMorphismComparisonOf f =
        system.realizationSystem.packedMorphismComparisonOf g

/-- Scalar separation is derived from scalar-encoding completeness plus framed
matrix-coefficient separation. -/
def scalarSeparationTarget_of_scalarEncodingCompleteness
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (scalarCodec : ScalarShadowCodec spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition system)
    (framedSeparation :
      ∀ {M N : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
        (f g : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N),
          (∀ probe : system.ProbeIndex,
            framedCoordinateFamilyOf system f probe = framedCoordinateFamilyOf system g probe) →
          system.realizationSystem.packedMorphismComparisonOf f =
            system.realizationSystem.packedMorphismComparisonOf g) :
    scalarSeparationTarget system scalarCodec.scalarShadow := by
  intro M N f g hScalar
  exact framedSeparation f g (scalarCodec.encodingComplete f g hScalar)

/-- Exact framed matrix-coefficient separation target for the recognized
framed/period-coordinate system. Pointwise agreement across the full canonical
probe family determines literal packed comparison equality on the recognized
image. -/
def framedSeparationTarget
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) : Prop :=
  ∀ {M N : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
    (f g : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N),
      (∀ probe : system.ProbeIndex,
          framedCoordinateFamilyOf system f probe = framedCoordinateFamilyOf system g probe) →
      system.realizationSystem.packedMorphismComparisonOf f =
        system.realizationSystem.packedMorphismComparisonOf g

/-- Mathematical name for the second remaining input: shared-probe matrix
coefficients separate packed comparison morphisms on the recognized image. -/
abbrev recognizedMatrixCoefficientSeparation
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :=
  framedSeparationTarget system

/-- Scalar probe family induced by a shared packed-comparison coordinate evaluator on the
recognized image. -/
def sharedProbeFamily
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (coord : system.ProbeIndex → SomeStructuredComparisonMorphism ctx → ctx.ScalarField) :
    ScalarProbeFamily ctx where
  ProbeIndex := system.ProbeIndex
  ScalarCarrier := ctx.ScalarField
  probeValue := coord
  equalityRelation := fun left right => left = right
  probeNaturalityTarget := ∀ (a : ctx.ScalarField), a = a
  probeExtractionTarget := ∀ (a : ctx.ScalarField), a = a

/-- Discharge framed-coordinate factorization once the coordinates are explicitly presented as
functions of the packed comparison morphism. -/
theorem recognizedFramedCoordinateFactorization_of_coordEval
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (coord : system.ProbeIndex → SomeStructuredComparisonMorphism ctx → ctx.ScalarField)
    (coord_agrees :
      ∀ {M N : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
        (f : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N)
        (probe : system.ProbeIndex),
          coord probe (system.realizationSystem.packedMorphismComparisonOf f) =
            framedCoordinateFamilyOf system f probe) :
    recognizedFramedCoordinateFactorization system := by
  intro M N f M' N' g hPacked probe
  rw [← coord_agrees f probe, ← coord_agrees g probe, hPacked]

/-- Discharge matrix-coefficient separation from a shared packed-comparison coordinate evaluator
and the existing tomography reconstruction chain. -/
theorem recognizedMatrixCoefficientSeparation_of_tomography
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (coord : system.ProbeIndex → SomeStructuredComparisonMorphism ctx → ctx.ScalarField)
    (coord_agrees :
      ∀ {M N : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
        (f : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N)
        (probe : system.ProbeIndex),
          coord probe (system.realizationSystem.packedMorphismComparisonOf f) =
            framedCoordinateFamilyOf system f probe)
    (basisEq : BasisFreePeriodMapEquality ctx)
    (probeExtensionality :
      ProbeExtensionalityForBasisFreePeriodMap
        ctx
        (sharedProbeFamily system coord)
        basisEq)
    (packedReconstruction :
      BasisFreePeriodMapDeterminesPackedComparison
        ctx
        basisEq
        (LayerD.literalPackedStructuredComparisonEquality ctx)) :
    recognizedMatrixCoefficientSeparation system := by
  intro M N f g hFamily
  have hProbe :
      ProbeEquality
        (sharedProbeFamily system coord)
        (system.realizationSystem.packedMorphismComparisonOf f)
        (system.realizationSystem.packedMorphismComparisonOf g) := by
    intro probe
    change coord probe (system.realizationSystem.packedMorphismComparisonOf f) =
        coord probe (system.realizationSystem.packedMorphismComparisonOf g)
    rw [coord_agrees f probe, coord_agrees g probe]
    exact hFamily probe
  exact packedReconstruction.theoremTarget
    (system.realizationSystem.packedMorphismComparisonOf f)
    (system.realizationSystem.packedMorphismComparisonOf g)
    (probeExtensionality.theoremTarget
      (system.realizationSystem.packedMorphismComparisonOf f)
      (system.realizationSystem.packedMorphismComparisonOf g)
      hProbe)

/-- The missing bridge object at the realized period-coordinate layer: a
recognized framed-period system together with Hom-faithfulness for the
comparison realization, scalar-encoding completeness, and framed separation on
its image.

The package deliberately does not treat scalar separation as primitive. The
scalar route factors through:

1. scalar-shadow equality,
2. recovery of the full framed coordinate family,
3. framed/matrix-coordinate separation,
4. Hom-faithfulness of the comparison realization. -/
structure ComparisonPeriodCoordinatePackage
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
  system :
    RecognizedMMQFramedPeriodSystem spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition
  scalarCodec :
    ScalarShadowCodec spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition system
  homFaithfulnessTarget :
    RecognizedMMQRealizationSystem.homFaithfulnessTarget system.realizationSystem
  framedSeparation : framedSeparationTarget system

/-- Build the realized period-coordinate package from explicit canonical framed
input and proofs of the three exact theorem targets it exposes. -/
def ComparisonPeriodCoordinatePackage.ofCanonicalInput
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
    (input : CanonicalInput spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition)
    (scalarCodec :
      ScalarShadowCodec spine internal normalization classical comparisonEquivalence
        canonicalEquivalence normalizationTransport transportedNormalization normTStructure
        heartRecognition (RecognizedMMQFramedPeriodSystem.ofCanonicalInput input))
    (homFaithfulnessTarget :
      RecognizedMMQRealizationSystem.homFaithfulnessTarget input.realizationSystem)
    (framedSeparation :
      framedSeparationTarget (RecognizedMMQFramedPeriodSystem.ofCanonicalInput input)) :
    ComparisonPeriodCoordinatePackage spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition where
  system := RecognizedMMQFramedPeriodSystem.ofCanonicalInput input
  scalarCodec := scalarCodec
  homFaithfulnessTarget := homFaithfulnessTarget
  framedSeparation := framedSeparation

/-- Mathematical name for the third remaining input: the recognized comparison
realization is faithful on Hom-sets. -/
abbrev recognizedHomFaithfulness
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :=
  RecognizedMMQRealizationSystem.homFaithfulnessTarget system.realizationSystem

/-- The framed theorem ladder on the recognized image.

Pointwise agreement of the shared-probe coordinate family implies equality of
packed comparison morphisms by matrix-coefficient separation, and then equality
of motivic morphisms by Hom-faithfulness of the recognized comparison
realization. -/
theorem framed_morphism_eq_of_probe_family_eq
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (framedSeparation : framedSeparationTarget system)
    (homFaithfulness :
      RecognizedMMQRealizationSystem.homFaithfulnessTarget system.realizationSystem)
    {M N : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
    (f g : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N)
    (hFamily : ∀ probe : system.ProbeIndex,
      framedCoordinateFamilyOf system f probe = framedCoordinateFamilyOf system g probe) :
    f = g := by
  exact homFaithfulness f g (framedSeparation f g hFamily)

/-- The full scalar period-conjecture package is inhabited once the three
remaining theorem ingredients are given. -/
noncomputable def comparisonPeriodPackage_of_three_facts
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
    (input : CanonicalInput spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition)
    (factorization :
      framedCoordinateFactorsThroughPackedComparisonTarget (ofCanonicalInput input))
    (framedSeparation : framedSeparationTarget (ofCanonicalInput input))
    (homFaithfulness :
      RecognizedMMQRealizationSystem.homFaithfulnessTarget input.realizationSystem) :
    ComparisonPeriodCoordinatePackage spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition :=
  ComparisonPeriodCoordinatePackage.ofCanonicalInput
    input
    (ScalarShadowCodec.ofFramedCoordinateFactorization (ofCanonicalInput input) factorization)
    homFaithfulness
    framedSeparation

/-- The full scalar period-conjecture package is also inhabited from the stronger holographic
inputs: framed-coordinate factorization, framed separation, certified transcript completeness on
packed comparisons, and trace-presentation reflection back to recognized `MM(Q)` morphisms. -/
noncomputable def comparisonPeriodPackage_of_holographic_facts
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
    (input : CanonicalInput spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition)
    (factorization :
      framedCoordinateFactorsThroughPackedComparisonTarget (ofCanonicalInput input))
    (framedSeparation : framedSeparationTarget (ofCanonicalInput input))
    (transcripts :
      RecognizedMMQRealizationSystem.CertifiedBoundaryTranscriptSystem input.realizationSystem)
    (packedComparisonDeterminesTranscript :
      RecognizedMMQRealizationSystem.packedComparisonDeterminesTranscriptTarget transcripts)
    (semantic :
      RecognizedMMQRealizationSystem.CertifiedBoundaryTranscriptSemanticInterpretation
        transcripts) :
    ComparisonPeriodCoordinatePackage spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition :=
  comparisonPeriodPackage_of_three_facts
    input
    factorization
    framedSeparation
    (fun {M} {N} f g hPacked => by
      have hTranscript : transcripts.transcriptOf f = transcripts.transcriptOf g :=
        packedComparisonDeterminesTranscript f g hPacked
      have hFrontier :
          TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FrontierWord.Equiv
            (C.assignment.assign (transcripts.transcriptOf f).completedTrace).frontier
            (C.assignment.assign (transcripts.transcriptOf g).completedTrace).frontier := by
        simpa [hTranscript] using
          (TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FrontierWord.Equiv.refl
            (C.assignment.assign (transcripts.transcriptOf f).completedTrace).frontier)
      have hTransported :
          semantic.transport.traceMorphismToMixedMotivesQ
              ((semantic.realizationOf M N).morphismOfCompletedTrace
                (transcripts.transcriptOf f).completedTrace) =
            semantic.transport.traceMorphismToMixedMotivesQ
              ((semantic.realizationOf M N).morphismOfCompletedTrace
                (transcripts.transcriptOf g).completedTrace) := by
        exact RealObjectsTraceHeartMorphismRealization.mixedMotivesQHom_eq_of_frontierEquiv
          (C := C)
          semantic.transport
          (semantic.realizationOf M N)
          hFrontier
      have hfg_heq : HEq f g :=
        HEq.trans
          (HEq.symm (semantic.morphism_spec f))
          (HEq.trans (heq_of_eq hTransported) (semantic.morphism_spec g))
      exact eq_of_heq hfg_heq)

/-- The full scalar period-conjecture package from the exact final obstruction: canonical replay
normal forms are complete for recognized `MM(Q)` morphisms on the RealObjects carrier. -/
noncomputable def comparisonPeriodPackage_of_cannf_completeness
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
    (input : CanonicalInput spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition)
    (factorization :
      framedCoordinateFactorsThroughPackedComparisonTarget (ofCanonicalInput input))
    (framedSeparation : framedSeparationTarget (ofCanonicalInput input))
    (transcripts :
      RecognizedMMQRealizationSystem.CertifiedBoundaryTranscriptSystem input.realizationSystem)
    (packedComparisonDeterminesTranscript :
      RecognizedMMQRealizationSystem.packedComparisonDeterminesTranscriptTarget transcripts)
    (cannfCompleteness :
      RecognizedMMQRealizationSystem.recognizedCanNFCompleteForMorphismsTarget transcripts) :
    ComparisonPeriodCoordinatePackage spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition :=
  comparisonPeriodPackage_of_three_facts
    input
    factorization
    framedSeparation
    (fun f g hPacked =>
      (cannfCompleteness f g).1 <|
        by
          have hTranscript : transcripts.transcriptOf f = transcripts.transcriptOf g :=
            packedComparisonDeterminesTranscript f g hPacked
          simp [hTranscript])

def structuredComparisonPackage
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :
    StructuredComparisonPackage ctx :=
  system.realizationSystem.structuredComparisonPackage

def someFramedPeriodOf
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    {M N : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
    (f : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N)
    (frame : system.FrameIndexOf f) :
    SomeFramedPeriodDatum ctx :=
  ⟨system.realizationSystem.objectComparisonOf M,
    ⟨system.realizationSystem.objectComparisonOf N,
      ⟨system.realizationSystem.morphismComparisonOf f,
        ⟨system.realizationSystem.pairingDataOf f,
          system.framedPeriodOf f frame⟩⟩⟩⟩

def scalarValueOf
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    {M N : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
    (f : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N)
    (frame : system.FrameIndexOf f) :
    ctx.ScalarField :=
  (system.framedPeriodOf f frame).scalarValue

def framedPeriodShadow
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
    (_system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :
    ScalarPeriodShadow (SomeFramedPeriodDatum ctx) :=
  framedScalarShadow ctx

def framedShadowEquality
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
    (_system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :
    ScalarShadowEquality (SomeFramedPeriodDatum ctx) (framedPeriodShadow (_system := _system)) :=
  framedScalarShadowEquality ctx

def framedShadowAlgebra
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
    (_system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :
    FramedScalarShadowAlgebra ctx (framedPeriodShadow (_system := _system)) :=
  canonicalFramedScalarShadowAlgebra ctx

@[simp] theorem structuredComparisonPackage_eq
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :
    system.structuredComparisonPackage = system.realizationSystem.structuredComparisonPackage := rfl

@[simp] theorem pairingData_someFramedPeriodOf
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    {M N : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
    (f : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N)
    (frame : system.FrameIndexOf f) :
    (someFramedPeriodOf system f frame).pairingData = system.realizationSystem.pairingDataOf f := rfl

@[simp] theorem framedDatum_someFramedPeriodOf
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    {M N : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
    (f : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N)
    (frame : system.FrameIndexOf f) :
    (someFramedPeriodOf system f frame).framedDatum = system.framedPeriodOf f frame := rfl

@[simp] theorem structuredComparisonDatum_someFramedPeriodOf
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    {M N : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
    (f : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N)
    (frame : system.FrameIndexOf f) :
    (someFramedPeriodOf system f frame).structuredComparisonDatum =
      packStructuredComparisonMorphism
        (system.realizationSystem.objectComparisonOf M)
        (system.realizationSystem.objectComparisonOf N)
        (system.realizationSystem.morphismComparisonOf f) := rfl

@[simp] theorem framedPeriodShadow_someFramedPeriodOf
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
    (system : RecognizedMMQFramedPeriodSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    {M N : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
    (f : system.realizationSystem.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N)
    (frame : system.FrameIndexOf f) :
    (RecognizedMMQFramedPeriodSystem.framedPeriodShadow system).shadowOf
        (someFramedPeriodOf system f frame) =
      scalarValueOf system f frame := rfl

end RecognizedMMQFramedPeriodSystem

end ClassicalBridge
end TraceCalc