import TraceCalc.ClassicalBridge.ClassicalBridgeAnchors
import TraceCalc.LayerE.MotivicRecognition.ManuscriptSpineTargets
import TraceCalc.ClassicalPeriods.StructuredComparison
import TraceCalc.ClassicalPeriods.Framed

universe u v w x y z

namespace TraceCalc
namespace ClassicalBridge

open ClassicalPeriods
open MotivicRecognition
open LayerB.RealObjects

/-- Pure bridge data from the recognized manuscript-facing `MM(Q)` endpoint to
the existing realization, structured-comparison, and period-pairing lane.

This structure is intentionally below any period-faithfulness target. It
contains no scalar-reflection assumption, no structured-faithfulness
assumption, and no final period-conjecture theorem packaging. -/
structure RecognizedMMQRealizationSystem
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
  mmqIdentification :
    MMQIdentificationTarget spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition
  structuredComparisonPackage : StructuredComparisonPackage ctx
  generatorOf :
    mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ →
      FormalPeriodGenerator ctx
  objectComparisonOf :
    mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ →
      ClassicalStructuredComparisonObject ctx
  morphismComparisonOf :
    {M N : mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ} →
      mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N →
        ClassicalStructuredComparisonMorphism ctx (objectComparisonOf M) (objectComparisonOf N)
  pairingDataOf :
    {M N : mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ} →
      (f : mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N) →
        PeriodPairingData ctx (morphismComparisonOf f)

namespace RecognizedMMQRealizationSystem

/-- Canonical constructor input for the recognized `MM(Q)` realization system.

This packages the exact concrete data needed to instantiate the bridge-level
realization system without hiding any fields behind anonymous `where` blocks.
It does not assert that such data already exists canonically in the current
codebase; it only records the precise constructor interface once that upstream
recognition-to-realization bridge is discharged. -/
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
  mmqIdentification :
    MMQIdentificationTarget spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition
  structuredComparisonPackage : StructuredComparisonPackage ctx
  generatorOf :
    mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ →
      FormalPeriodGenerator ctx
  objectComparisonOf :
    mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ →
      ClassicalStructuredComparisonObject ctx
  morphismComparisonOf :
    {M N : mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ} →
      mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N →
        ClassicalStructuredComparisonMorphism ctx (objectComparisonOf M) (objectComparisonOf N)
  pairingDataOf :
    {M N : mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ} →
      (f : mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N) →
        PeriodPairingData ctx (morphismComparisonOf f)

/-- Build the recognized `MM(Q)` realization system from explicit canonical
input data. -/
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
    RecognizedMMQRealizationSystem spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition where
  mmqIdentification := input.mmqIdentification
  structuredComparisonPackage := input.structuredComparisonPackage
  generatorOf := input.generatorOf
  objectComparisonOf := input.objectComparisonOf
  morphismComparisonOf := input.morphismComparisonOf
  pairingDataOf := input.pairingDataOf

/-- Sigma-packaged structured comparison morphism attached to a recognized
`MM(Q)` morphism by the comparison realization system. -/
def packedMorphismComparisonOf
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
    (system : RecognizedMMQRealizationSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    {M N : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
    (f : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N) :
    SomeStructuredComparisonMorphism ctx :=
  packStructuredComparisonMorphism
    (system.objectComparisonOf M)
    (system.objectComparisonOf N)
    (system.morphismComparisonOf f)

/-- Exact faithfulness target for the canonical comparison realization functor on
recognized `MM(Q)`: literal equality of packed comparison morphisms determines
motivic morphism equality. -/
def homFaithfulnessTarget
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
    (system : RecognizedMMQRealizationSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) : Prop :=
  ∀ {M N : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
    (f g : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N),
      system.packedMorphismComparisonOf f = system.packedMorphismComparisonOf g →
        f = g

/-- Complete certified boundary transcript attached to a recognized `MM(Q)` morphism.

This is the holographic object needed for the final motivic proof step. It is intentionally
strictly richer than the bare Betti/de Rham comparison image: besides the comparison table, it
stores the certified completed trace record, its canonical normal form, and the replay/coherence
witness slots needed to reconstruct the trace-side morphism in the presented geometric category. -/
structure CertifiedBoundaryTranscript
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
    (system : RecognizedMMQRealizationSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    {M N : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
    where
  sourceGenerator : FormalPeriodGenerator ctx
  targetGenerator : FormalPeriodGenerator ctx
  sourceGenerator_spec : sourceGenerator = system.generatorOf M
  targetGenerator_spec : targetGenerator = system.generatorOf N
  completedTrace : LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup
  normalizedTrace : C.normalizer.NF
  normalizationWitness : C.normalize completedTrace = normalizedTrace
  replayWitness : Prop
  coherenceWitness : Prop
  comparisonTable : SomeStructuredComparisonMorphism ctx

/-- A certified-boundary-transcript provider for the recognized `MM(Q)` realization system.

This is the owning abstraction for the holographic step. The period/comparison side must supply a
full replayable transcript, not only numerical period values, and must certify that its comparison
table agrees with the packed comparison image. -/
structure CertifiedBoundaryTranscriptSystem
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
    (system : RecognizedMMQRealizationSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  transcriptOf :
    ∀ {M N : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ},
      system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N →
        RecognizedMMQRealizationSystem.CertifiedBoundaryTranscript
          (system := system) (M := M) (N := N)
  comparisonTable_spec :
    ∀ {M N : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
      (f : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N),
      (transcriptOf (M := M) (N := N) f).comparisonTable = system.packedMorphismComparisonOf f

/-- Explicit trace-presentation input for constructing certified boundary transcripts on the
recognized `MM(Q)` image.

This is the actual provider surface expected from the trace-presentation layer: for each
recognized morphism it supplies the completed trace record and the replay/coherence certificates.
The comparison table and canonical normal form are then filled canonically by the bridge data
already present in `RecognizedMMQRealizationSystem`. -/
structure CertifiedBoundaryTranscriptInput
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
    (system : RecognizedMMQRealizationSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) where
  completedTraceOf :
    ∀ {M N : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ},
      system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N →
        LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup
  replayWitnessOf :
    ∀ {M N : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
      (f : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N),
      Prop
  coherenceWitnessOf :
    ∀ {M N : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
      (f : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N),
      Prop

namespace CertifiedBoundaryTranscriptSystem

/-- Build the certified boundary transcript system from explicit trace-presentation data.

This is the concrete provider constructor for the holographic boundary transcript: the trace layer
supplies replayable completed records and witness slots, while the bridge layer computes the normal
form and comparison table canonically. -/
def ofTracePresentationData
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
    (system : RecognizedMMQRealizationSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (input : CertifiedBoundaryTranscriptInput system) :
    CertifiedBoundaryTranscriptSystem system where
  transcriptOf := by
    intro M N f
    refine
      { sourceGenerator := system.generatorOf M
        targetGenerator := system.generatorOf N
        sourceGenerator_spec := rfl
        targetGenerator_spec := rfl
        completedTrace := input.completedTraceOf f
        normalizedTrace := C.normalize (input.completedTraceOf f)
        normalizationWitness := rfl
        replayWitness := input.replayWitnessOf f
        coherenceWitness := input.coherenceWitnessOf f
        comparisonTable := system.packedMorphismComparisonOf f }
  comparisonTable_spec := by
    intro M N f
    rfl

end CertifiedBoundaryTranscriptSystem

/-- Explicit input surface for constructing a concrete semantic interpretation
package on top of a certified boundary transcript system. -/
structure CertifiedBoundaryTranscriptSemanticInput
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
    (system : RecognizedMMQRealizationSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition)
    (transcripts : CertifiedBoundaryTranscriptSystem system) where
  transport :
    ClassicalMMQHeartMorphismTransport
      system.mmqIdentification.classicalHeartIdentification.classicalMMQHeartTheorems
  traceHeartObjectOf :
    system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ →
      system.mmqIdentification.classicalHeartIdentification.traceHeart.heartObject
  traceHeartObject_spec :
    ∀ M,
      HEq (transport.traceObjectToMixedMotivesQ (traceHeartObjectOf M)) M
  realizationOf :
    ∀ M N : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ,
      RealObjectsTraceHeartMorphismRealization (C := C)
        system.mmqIdentification.classicalHeartIdentification.traceHeart
        (traceHeartObjectOf M)
        (traceHeartObjectOf N)
  morphism_spec :
    ∀ {M N : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
      (f : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N),
      HEq
        (transport.traceMorphismToMixedMotivesQ
          ((realizationOf M N).morphismOfCompletedTrace
            (transcripts.transcriptOf f).completedTrace))
        f

/-- Proof-relevant semantic interpretation of certified replay transcripts into
fixed trace-heart morphisms for the recognized `MM(Q)` realization system.

This is the exact missing mathematical object for the final replay-reflection
step: a choice of trace-heart representatives for `MM(Q)` objects, a fixed
completed-trace-to-heart realization for each object pair, and the proof that
transporting the realized morphism recovers the original `MM(Q)` morphism. -/
structure CertifiedBoundaryTranscriptSemanticInterpretation
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
    {system : RecognizedMMQRealizationSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition}
    (transcripts : CertifiedBoundaryTranscriptSystem system) where
  transport :
    ClassicalMMQHeartMorphismTransport
      system.mmqIdentification.classicalHeartIdentification.classicalMMQHeartTheorems
  traceHeartObjectOf :
    system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ →
      system.mmqIdentification.classicalHeartIdentification.traceHeart.heartObject
  traceHeartObject_spec :
    ∀ M,
      HEq (transport.traceObjectToMixedMotivesQ (traceHeartObjectOf M)) M
  realizationOf :
    ∀ M N : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ,
      RealObjectsTraceHeartMorphismRealization (C := C)
        system.mmqIdentification.classicalHeartIdentification.traceHeart
        (traceHeartObjectOf M)
        (traceHeartObjectOf N)
  morphism_spec :
    ∀ {M N : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
      (f : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N),
      HEq
        (transport.traceMorphismToMixedMotivesQ
          ((realizationOf M N).morphismOfCompletedTrace
            (transcripts.transcriptOf f).completedTrace))
        f

/-- Frontier-equivalent certified replay records determine the same recognized morphism. -/
def tracePresentationReflectsMorphismTarget
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
    {system : RecognizedMMQRealizationSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition}
    (transcripts : CertifiedBoundaryTranscriptSystem system) : Prop :=
  ∀ {M N : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
    (f g : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N),
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FrontierWord.Equiv
        (C.assignment.assign (transcripts.transcriptOf f).completedTrace).frontier
        (C.assignment.assign (transcripts.transcriptOf g).completedTrace).frontier →
          f = g

/-- Equality of certified normal forms determines equality of recognized morphisms. -/
def normalFormDeterminesMorphismTarget
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
    {system : RecognizedMMQRealizationSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition}
    (transcripts : CertifiedBoundaryTranscriptSystem system) : Prop :=
  ∀ {M N : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
    (f g : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N),
      (transcripts.transcriptOf f).normalizedTrace =
        (transcripts.transcriptOf g).normalizedTrace →
          f = g

/-- Canonical normal forms are complete for recognized motivic morphisms. -/
def recognizedCanNFCompleteForMorphismsTarget
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
    {system : RecognizedMMQRealizationSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition}
    (transcripts : CertifiedBoundaryTranscriptSystem system) : Prop :=
  ∀ {M N : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
    (f g : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N),
      (transcripts.transcriptOf f).normalizedTrace =
        (transcripts.transcriptOf g).normalizedTrace ↔
          f = g

/-- Equality of packed comparison morphisms determines equality of full certified transcripts. -/
def packedComparisonDeterminesTranscriptTarget
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
    {system : RecognizedMMQRealizationSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition}
    (transcripts : CertifiedBoundaryTranscriptSystem system) : Prop :=
  ∀ {M N : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQ}
    (f g : system.mmqIdentification.finalMotivicInfrastructure.mixedMotivesQHom M N),
      system.packedMorphismComparisonOf f = system.packedMorphismComparisonOf g →
        transcripts.transcriptOf f = transcripts.transcriptOf g

/-- Stable alias for the certified transcript carrier used in the late theorem block. -/
abbrev CertifiedTranscriptSystem
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
    (system : RecognizedMMQRealizationSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition) :=
  CertifiedBoundaryTranscriptSystem system

namespace CertifiedBoundaryTranscriptSemanticInterpretation

open RecognizedMMQRealizationSystem

/-- Build the semantic interpretation package from explicit concrete input. -/
def ofInput
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
    {system : RecognizedMMQRealizationSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition}
    {transcripts : CertifiedTranscriptSystem system}
    (input : CertifiedBoundaryTranscriptSemanticInput system transcripts) :
    CertifiedBoundaryTranscriptSemanticInterpretation transcripts where
  transport := input.transport
  traceHeartObjectOf := input.traceHeartObjectOf
  traceHeartObject_spec := input.traceHeartObject_spec
  realizationOf := input.realizationOf
  morphism_spec := input.morphism_spec

/-- Frontier-equivalent certified replay records determine the same recognized
`MM(Q)` morphism once the semantic interpretation map has been fixed. -/
theorem tracePresentationReflectsMorphismTarget_of_semanticInterpretation
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
    {system : RecognizedMMQRealizationSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition}
    {transcripts : CertifiedTranscriptSystem system}
    (semantic : CertifiedBoundaryTranscriptSemanticInterpretation transcripts) :
    tracePresentationReflectsMorphismTarget transcripts := by
  intro M N f g hFrontier
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
  exact eq_of_heq hfg_heq

/-- The semantic interpretation map closes the normal-form reflection theorem on
the recognized `MM(Q)` image. -/
theorem normalFormDeterminesMorphismTarget_of_semanticInterpretation
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
    {system : RecognizedMMQRealizationSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition}
    {transcripts : CertifiedTranscriptSystem system}
    (semantic : CertifiedBoundaryTranscriptSemanticInterpretation transcripts) :
    normalFormDeterminesMorphismTarget transcripts := by
  intro M N f g hNormalForm
  apply tracePresentationReflectsMorphismTarget_of_semanticInterpretation semantic f g
  have hCompletedNormalize :
      C.normalize (transcripts.transcriptOf f).completedTrace =
        C.normalize (transcripts.transcriptOf g).completedTrace := by
    calc
      C.normalize (transcripts.transcriptOf f).completedTrace =
          (transcripts.transcriptOf f).normalizedTrace :=
        (transcripts.transcriptOf f).normalizationWitness
      _ = (transcripts.transcriptOf g).normalizedTrace := hNormalForm
      _ = C.normalize (transcripts.transcriptOf g).completedTrace := by
        symm
        exact (transcripts.transcriptOf g).normalizationWitness
  exact (C.CanNF_complete hCompletedNormalize)

/-- The semantic interpretation map yields the full CanNF completeness theorem
for recognized `MM(Q)` morphisms. -/
theorem recognizedCanNFCompleteForMorphisms_of_semanticInterpretation
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
    {system : RecognizedMMQRealizationSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition}
    {transcripts}
    (semantic : CertifiedBoundaryTranscriptSemanticInterpretation
      (system := system) transcripts) :
    recognizedCanNFCompleteForMorphismsTarget (system := system) transcripts := by
  intro M N f g
  constructor
  · intro hNormalForm
    exact normalFormDeterminesMorphismTarget_of_semanticInterpretation semantic f g hNormalForm
  · intro hEq
    cases hEq
    rfl

/-- Packed comparison faithfulness follows from the concrete semantic
interpretation package and transcript completeness. -/
theorem homFaithfulnessTarget_of_semanticInterpretation
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
    {system : RecognizedMMQRealizationSystem spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure heartRecognition}
    {transcripts}
    (packedComparisonDeterminesTranscript :
      packedComparisonDeterminesTranscriptTarget (system := system) transcripts)
    (semantic : CertifiedBoundaryTranscriptSemanticInterpretation
      (system := system) transcripts) :
    homFaithfulnessTarget system := by
  intro M N f g hPacked
  have hTranscript : transcripts.transcriptOf f = transcripts.transcriptOf g :=
    packedComparisonDeterminesTranscript f g hPacked
  have hFrontier :
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FrontierWord.Equiv
        (C.assignment.assign (transcripts.transcriptOf f).completedTrace).frontier
        (C.assignment.assign (transcripts.transcriptOf g).completedTrace).frontier := by
    simpa [hTranscript] using
      (TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FrontierWord.Equiv.refl
        (C.assignment.assign (transcripts.transcriptOf f).completedTrace).frontier)
  exact CertifiedBoundaryTranscriptSemanticInterpretation.tracePresentationReflectsMorphismTarget_of_semanticInterpretation
    semantic
    f g
    hFrontier

end CertifiedBoundaryTranscriptSemanticInterpretation

/-- The missing bridge object at the recognized `MM(Q)` realization layer:
an actual comparison-realization system together with its Hom-faithfulness
theorem target. -/
structure ComparisonRealizationPackage
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
    RecognizedMMQRealizationSystem spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition
  theoremTarget : homFaithfulnessTarget system

/-- Build the comparison-realization package directly from explicit canonical
input and a proof of Hom-faithfulness for the resulting realized system. -/
def ComparisonRealizationPackage.ofCanonicalInput
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
    (theoremTarget : homFaithfulnessTarget
      (RecognizedMMQRealizationSystem.ofCanonicalInput input)) :
    ComparisonRealizationPackage spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition where
  system := RecognizedMMQRealizationSystem.ofCanonicalInput input
  theoremTarget := theoremTarget

/-- Build the comparison-realization package from canonical input and the full
holographic data, including the concrete semantic interpretation package on the
certified transcript carrier. -/
def ComparisonRealizationPackage.ofCanonicalInputAndHolography
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
    (transcripts : CertifiedBoundaryTranscriptSystem
      (RecognizedMMQRealizationSystem.ofCanonicalInput input))
    (packedComparisonDeterminesTranscript :
      packedComparisonDeterminesTranscriptTarget
        (system := RecognizedMMQRealizationSystem.ofCanonicalInput input) transcripts)
    (semantic : CertifiedBoundaryTranscriptSemanticInterpretation
      (system := RecognizedMMQRealizationSystem.ofCanonicalInput input) transcripts) :
    ComparisonRealizationPackage spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition :=
  ComparisonRealizationPackage.ofCanonicalInput
    input
    (CertifiedBoundaryTranscriptSemanticInterpretation.homFaithfulnessTarget_of_semanticInterpretation
      packedComparisonDeterminesTranscript
      semantic)

end RecognizedMMQRealizationSystem

end ClassicalBridge
end TraceCalc