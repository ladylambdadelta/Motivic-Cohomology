import TraceCalc.MotivicRecognition.ManuscriptSpineTargets
import TraceCalc.MotivicRecognition.SyntacticDMgmClassicalBridge

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

open LayerB.RealObjects
open ClassicalPeriods

/-!
Package 7: MM(Q) / abelian-heart assembly.

The target fields in `TraceMotivicTStructureData` are theorem statements.
This file therefore seals the assembly by projecting from the existing
`NormTStructureTheoremPackage` and `ClassicalMMQHeartTheorems` data, then
feeding those proof packages into the manuscript P7 targets.  It does not
construct a trace-native stand-in for the classical heart.
-/

theorem normTStructureTheoremPackage_from_target
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
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
    (normTStructure : NormTStructureTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalization) :
    NormTStructureTheoremPackage normTStructure.traceMotivicTStructure
      normTStructure.normalizationPacketCut :=
  normTStructure.normTStructureTheoremPackage

theorem normalizationInducesWeightCompatibleTStructure_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {packetCut : NormalizationPacketCutData structuralRecognition}
    (pkg : NormTStructureTheoremPackage tStructure packetCut) :
    tStructure.normalizationPacketCutTarget ∧
      packetCut.canonicalReconstructionCompatibilityTarget :=
  pkg.normalizationInducesWeightCompatibleTStructure

theorem transportedTStructureIsMotivic_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {packetCut : NormalizationPacketCutData structuralRecognition}
    (pkg : NormTStructureTheoremPackage tStructure packetCut) :
    tStructure.normalizationCompatibilityTarget ∧
      tStructure.campaign11WeightDevissageInputTarget :=
  pkg.transportedTStructureIsMotivic

theorem truncationTriangleRepresentability_holds
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {packetCut : NormalizationPacketCutData structuralRecognition}
    (pkg : NormTStructureTheoremPackage tStructure packetCut) :
    tStructure.truncationTriangleTarget ∧
      tStructure.truncationFunctorialityTarget :=
  pkg.truncationTriangleRepresentability

namespace HeartRecognitionTarget

def ofNormTStructure
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
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
      transportedNormalization) :
    HeartRecognitionTarget spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure where

theorem pureHeartRecognitionTarget_holds
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
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
    (pkg : NormTStructureTheoremPackage normTStructure.traceMotivicTStructure
      normTStructure.normalizationPacketCut) :
    (ofNormTStructure spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure)
        |>.pureHeartRecognitionTarget :=
  pkg.transportedTStructureIsMotivic.1

theorem lefschetzClosureTarget_holds
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
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
    (hTensor : transportedNormalization.tensorCompatibilityTarget)
    (hRealization : transportedNormalization.realizationCompatibilityTarget) :
    (ofNormTStructure spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure)
        |>.lefschetzClosureTarget :=
  ⟨hTensor, hRealization⟩

end HeartRecognitionTarget

theorem classicalMMQHeartTheorems_from_target
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
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
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure}
    (classicalHeartIdentification :
      ClassicalHeartIdentificationTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
        normTStructure heartRecognition) :
    ClassicalMMQHeartTheorems normTStructure.traceMotivicTStructure
      classicalHeartIdentification.traceHeart :=
  classicalHeartIdentification.classicalMMQHeartTheorems

namespace ClassicalHeartIdentificationTarget

def ofTraceMotivicTStructureData
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
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
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure)
    (components :
      TraceMotivicTStructureComponentTheorems normTStructure.traceMotivicTStructure) :
    ClassicalHeartIdentificationTarget spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition where
  traceHeart := TraceMotivicHeart.ofTStructure normTStructure.traceMotivicTStructure
  classicalMMQHeartTheorems :=
    ClassicalMMQHeartTheorems.ofTraceMotivicTStructureData
      normTStructure.traceMotivicTStructure components

def ofTransportedTStructureComponents
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
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
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure)
    (transportedHeartIdentifiesClassicalGeometricMotivesHeart :
      normTStructure.traceMotivicTStructure.recognitionCompatibilityTarget)
    (classicalAbelianHeartIsMixedMotivesQ :
      normTStructure.traceMotivicTStructure.normalizationCompatibilityTarget ∧
        normTStructure.traceMotivicTStructure.canonicalReconstructionCompatibilityTarget)
    (mixedMotiveHeartOverQTarget :
      normTStructure.traceMotivicTStructure.normalizationCompatibilityTarget ∧
        normTStructure.traceMotivicTStructure.orthogonalityFromSeparatedDegreesTarget)
    (compatibilityWithTransportedTStructureIsExact :
      normTStructure.traceMotivicTStructure.shiftClosureNonposTarget ∧
        normTStructure.traceMotivicTStructure.shiftClosureNonnegTarget ∧
        normTStructure.traceMotivicTStructure.orthogonalityTarget)
    (compatibilityWithHeartRecognitionIsNatural :
      normTStructure.traceMotivicTStructure.normalizationCompatibilityTarget ∧
        normTStructure.traceMotivicTStructure.normalizationPacketCutTarget) :
    ClassicalHeartIdentificationTarget spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition :=
  ClassicalHeartIdentificationTarget.ofTraceMotivicTStructureData spine internal normalization
    classical comparisonEquivalence canonicalEquivalence normalizationTransport
    transportedNormalization normTStructure heartRecognition
    (TraceMotivicTStructureComponentTheorems.ofComponents
      normTStructure.traceMotivicTStructure
      transportedHeartIdentifiesClassicalGeometricMotivesHeart
      classicalAbelianHeartIsMixedMotivesQ
      mixedMotiveHeartOverQTarget
      compatibilityWithTransportedTStructureIsExact
      compatibilityWithHeartRecognitionIsNatural)

def ofCanonicalPacketCutWithCertifiedStructuralPackage
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
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
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure)
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        spine.structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        spine.structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        spine.structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        spine.structuralRecognition.recognition.recognitionInput.tracePresentation
        spine.structuralRecognition.recognition.recognitionInput.classicalPresentation
        spine.structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (certified : CertifiedDMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (hCertified : certified.structuralRecognition = spine.structuralRecognition)
    (traceNative :
      TraceNativeWeightDevissageData spine.structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (threshold : Nat)
    (hThreshold : threshold ≤ traceNative.reconstructionLength)
    (hTStructure :
      normTStructure.traceMotivicTStructure =
        TraceMotivicTStructureData.ofCanonicalPacketCut traceNative threshold hThreshold) :
    ClassicalHeartIdentificationTarget spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition :=
  let normalizationPacketCut_holds :
      (TraceMotivicTStructureData.ofCanonicalPacketCut traceNative threshold
        hThreshold).normalizationPacketCutTarget :=
    hTStructure ▸
      (normalizationInducesWeightCompatibleTStructure_holds
        normTStructure.normTStructureTheoremPackage).1
  ClassicalHeartIdentificationTarget.ofTraceMotivicTStructureData spine internal normalization
    classical comparisonEquivalence canonicalEquivalence normalizationTransport
    transportedNormalization normTStructure heartRecognition
    (hTStructure ▸
      TraceMotivicTStructureComponentTheorems.ofCanonicalPacketCutWithCertifiedStructuralPackage
        certified hCertified traceNative threshold hThreshold normalizationPacketCut_holds)

abbrev ofCanonicalPacketCutWithStructuralTransport
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z}) :=
  @ofCanonicalPacketCutWithCertifiedStructuralPackage spine

/-- Legacy compatibility constructor.

This route accepts a preassembled `ClassicalMMQHeartTheorems` package and is
not the production certified closeout path. The repository-level certified route
goes through `ofCanonicalPacketCutWithCertifiedStructuralPackage`. -/
def ofClassicalMMQHeartTheorems
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
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
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure)
    (traceHeart : TraceMotivicHeart normTStructure.traceMotivicTStructure)
    (heartTheorems :
      ClassicalMMQHeartTheorems normTStructure.traceMotivicTStructure traceHeart) :
    ClassicalHeartIdentificationTarget spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition where
  traceHeart := traceHeart
  classicalMMQHeartTheorems := heartTheorems

end ClassicalHeartIdentificationTarget

/-- Explicit audit-stable alias for the canonical Package 7 route. -/
def classicalHeartIdentificationOfTraceMotivicTStructureData
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
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
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure)
    (components :
      TraceMotivicTStructureComponentTheorems normTStructure.traceMotivicTStructure) :
    ClassicalHeartIdentificationTarget spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition :=
  ClassicalHeartIdentificationTarget.ofTraceMotivicTStructureData spine internal normalization
    classical comparisonEquivalence canonicalEquivalence normalizationTransport
    transportedNormalization normTStructure heartRecognition components

namespace MMQIdentificationTarget

def ofClassicalHeartIdentification
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
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
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure)
    (classicalHeartIdentification :
      ClassicalHeartIdentificationTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
        normTStructure heartRecognition) :
    MMQIdentificationTarget spine internal normalization classical comparisonEquivalence
      canonicalEquivalence normalizationTransport transportedNormalization normTStructure
      heartRecognition where
  classicalHeartIdentification := classicalHeartIdentification
  mmqHeartIdentification :=
    classicalHeartIdentification.classicalMMQHeartTheorems.traceHeart_recognizes_classical_MMQ
  mmqPureHeartCompatibility :=
    classicalHeartIdentification.classicalMMQHeartTheorems
      |>.compatibilityWithHeartRecognitionIsNatural

theorem mmqHeartIdentification_holds
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup → α}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
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
      comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
      normTStructure}
    (mmqIdentification :
      MMQIdentificationTarget spine internal normalization classical comparisonEquivalence
        canonicalEquivalence normalizationTransport transportedNormalization normTStructure
        heartRecognition) :
    RecognizesClassicalMMQ normTStructure.traceMotivicTStructure
      mmqIdentification.classicalHeartIdentification.traceHeart :=
  mmqIdentification.mmqHeartIdentification

end MMQIdentificationTarget

end MotivicRecognition
end TraceCalc
